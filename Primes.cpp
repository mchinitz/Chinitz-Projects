#include <iostream>
using namespace std;
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdbool.h>
#include <sys/time.h>
#include <assert.h>
#include <thread>
#include <atomic>
atomic<bool> lock(false);
#define IS_MULTITHREADED 1
#define N 1000000 //nice and large to minimize prints, but not to large so bad locality
#define lower_lim 0
#define upper_lim 100000000 //10^8

/*
 * Task: find all primes between lower_lim and upper_lim, and print them in a text file
 *
 * (1) Compute primes <= sqrt(upper lim)
 * (2) Iterate over subintervals of length N. For each such interval,
 * (2a) Iterate over every multiple of the primes <= sqrt(N) contained in the interval.
 * Mark those values as composite. The primes are what is left ever
 * (2b) Find the primes, and add them to the ith list of primes within strings_to_print
 * When done with an interval, claim the next unclaimed subinterval (by some other thread).
 * (3) Sort the array of strings of primes in each interval by the values of the first elements in each.
 * (4) Print each string in the array of strings
 *
 * Advantages of design: (1) this algorithm uses substantially fewer computations than testing whether every odd number is prime using division
 * (2) We get better cache locality by using intervals than by letting each thread process different composite numbers.
 * This is because we are writing to a confined region of the composites array, rather than writing to elements increasingly far away
 * from each other.
 * (3) We use strings to minimize the number of I/O operations (instead preferring to print large buffers at a time)
 */



//Critical sections
void *update_curr_prime_to_test(void *args);
void *malloc_funct_under_lock(void *args);

double curr_time(void)
{
        struct timeval tv;
        /* struct timezone tz; */
        gettimeofday(&tv, 0 /* &tz */);
        return tv.tv_sec + tv.tv_usec*1.0e-6;
}

template<typename TYPE>
TYPE sum_array(int len, TYPE A[])
{
	TYPE sum = 0;
	for (int i=0; i<len; i++)
		sum += A[i];
	return sum;
}

//This does the work of sprintf for the particular format of an integer + a newline.
//This function is substantially faster than calling sprintf
int convert_to_string(unsigned int x, char A[], int num_digits)
{
	for (register int i= num_digits - 1; i >= 0; i--)
	{
		register unsigned int quotient = x / 10;
		A[i] = (x - 10 * quotient) + '0';
		x = quotient;
	}
	A[num_digits] = '\n';
	return num_digits + 1;
}

bool linear_search(int ele, int A[], int nrow)
{
	for (int i=0; i<nrow; i++)
		if (A[i] == ele)
			return true;
	return false;
}

int num_digits(int x)
{
	if (x == 0)
		return 1;
	x = abs(x);
	return log10(x) + 1;
}


//This function is intended only to be used sequentially. It returns whether a given number is prime.
//Note that it assumes that all primes less than this integer have already been stored in the array "prev_primes"
//so that we only need to check dividing by primes.
bool is_prime(int prev_primes[], int num_prev_primes, int x)
{
	if (x <= 1)
		return false;
	int sqrtX = sqrt(x);
	for (int i=0; i<num_prev_primes; i++)
	{
		if (prev_primes[i] > sqrtX)
			break;
		if (x % prev_primes[i] == 0)
			return false;
	}

	return true;
}

//Adds an element to an array, doubling the length if the array is currently at capacity.
//Args is a pointer to an array with four elements.
//The third argument is a pointer to an integer array we want to insert an element into.
//The first argument is the actual size of the array.
//The second argument is the number of slots in the array already used up.
//The fourth argument is the element to be inserted.
void *insert_ele_dynamic_arr(void *args)
{
	void *(*arr_args)[4] = (void *((*)[4]))(args);
	int *curr_len = (int *)((*arr_args)[0]);
	int *len = (int *)((*arr_args)[1]);
	int (*A)[] = (int ((*) []))((*arr_args)[2]);
	int ele = *(int *)((*arr_args)[3]);
	if (*curr_len == *len)
	{
		(*curr_len) *= 2;
		A = (int ((*) [] )) realloc(A, (*curr_len) * sizeof(int));
	}
	(*A)[*len] = ele;
	(*len) ++;
	return A;
}

int compare_str_by_first(const void *x, const void *y)
{
	char *first = *(char **)(x);
	if (first[0] == '\0')
		return -1;
	char *second = *(char **)(y);
	if (second[0] == '\0')
		return 1;
	return (int)(strtod(first, NULL)) - (int)(strtod(second, NULL));
}



//Given a function pointer and arguments, the method "lock_perform_unlock" (1) locks a spinlock
//(2) calls the critical section function and (3) unlocks.
class Generic_Thread_Lock_Routine
{
	void *args;
	void *(*fptr)(void *args);
public:
	void set_args(void *args)
	{
		this -> args = args;
	}
	void set_fptr(void *fptr(void *))
	{
		this -> fptr = fptr;
	}
	//[1]
	void *lock_perform_unlock()
	{
		while (atomic_exchange_explicit(&lock, true, memory_order_acquire));
		void *return_value = fptr(args);
		atomic_store_explicit(&lock, false, std::memory_order_release);
		return return_value;
	}
};

//This class performs the bulk of the work. Call get_primes() to generate the result.
class Test_Primes
{
	int (*prev_primes)[]; //stores primes from zero to sqrt(upper_lim), calculated regardless of the value of lower_lim
	int num_prev_primes = 0; //number of primes in the above range

	int curr_len = 1; //capacity of prev_primes, which in the constructor will initially be one
	int *composites;
	int array_len;

public:
#if IS_MULTITHREADED
	int num_threads = 4;
#else
	int num_threads = 1;
#endif


	//These three variables are made public because they are needed by the critical sections, which are not class methods.
	FILE *fp;
	//These two variables are used to mark progress in the thread routines
	int left_endpt = -1 * N; //since will immediately add N
	int num_printing_contenders = 0;
	int sqrtUpp;
	//NEW
	int *init_primes;
	char *strings_to_print[(int) ceil((upper_lim + 1) * 1.0 / N)];

	int *num_primes;

	Test_Primes(FILE *fp)
	{

		this -> fp = fp;
		sqrtUpp = sqrt(upper_lim);
		prev_primes = (int ((*) []))(malloc(sizeof(int)));
		initialize_small_prev_primes();
		array_len = upper_lim / 32 + 1;

		composites = (int *)(calloc(array_len, sizeof(int)));
		if (composites == NULL)
		{
			printf("Error, out of memory\n");
			exit(EXIT_FAILURE);
		}

		composites[0] |= 0x00000003; //neither zero nor one is prime.

		//Initialization of init_primes and composites
		init_primes = (int *)(malloc(num_prev_primes * sizeof(int)));
		memcpy(init_primes, *prev_primes, num_prev_primes * sizeof(int));

		for (int i=0; i<sqrtUpp; i++)
			if (!linear_search(i, init_primes, num_prev_primes)) //if not prime
			{
				int int_index = i / 32;
				int bit_index = i % 32;
				composites[int_index] |= (1 << bit_index);
			}
		for (int i=1; i<num_prev_primes; i++)
			init_primes[i] *= 2; //since really want to be adding 2 * primes (we don't need to mark composites[even indices] = true)

	int num_intervals = ceil((upper_lim + 1) * 1.0 / N);
	for (int i=0; i<num_intervals; i++)
		strings_to_print[i] = NULL;
	num_primes = (int *)(calloc(num_threads, sizeof(int)));
	}

	~Test_Primes()
	{
		free(prev_primes);
		free(composites);
		free(init_primes);
		int num_intervals = ceil(upper_lim * 1.0 / N);
		for (int i=0; i<num_intervals; i++)
			free(strings_to_print[i]);
		free(num_primes);
	}


	void initialize_small_prev_primes()
	{
		(*prev_primes)[0] = 2;
		num_prev_primes = 1;
		for (int i=3; i<=sqrtUpp; i+= 2)
		{
			if (is_prime(*prev_primes, num_prev_primes, i))
			{
				void *args[4] = {&curr_len, &num_prev_primes, prev_primes, &i};
				prev_primes = (int ((*) []))(insert_ele_dynamic_arr(args));
			}
		}

	}


	//Computes all the composites as indicated above. This is a thread routine. Calls the function store_primes
	//within each interval to find the primes and add them to the strings to print
	void collect_all_composites(int *thread_index)
	{
		thread_local Generic_Thread_Lock_Routine instance = Generic_Thread_Lock_Routine();

		instance.set_fptr(&update_curr_prime_to_test);

		int local_cpy_left_endpt;

		void *args[2] = {this, &local_cpy_left_endpt};

		while (1)
		{
			instance.set_args(&args);
			instance.lock_perform_unlock(); //updates the interval
			if (local_cpy_left_endpt > upper_lim)
				return;

			int max_interval = fmin(local_cpy_left_endpt + N, upper_lim + 1);

			//no reason to mark the evens!
			for (int primeIndex = 1; primeIndex < num_prev_primes; primeIndex ++)
			{

				int remainder = local_cpy_left_endpt % (*prev_primes)[primeIndex];
				register int loc = (remainder == 0) ? local_cpy_left_endpt : \
						local_cpy_left_endpt + ((*prev_primes)[primeIndex] - remainder);
				if (loc % 2 == 0)
					loc += (*prev_primes)[primeIndex];
				loc = fmax(loc, (*prev_primes)[primeIndex] * (*prev_primes)[primeIndex]);
				//loc initially denotes the smallest multiple of the current prime contained in the interval that is at least prime ^ 2

				while (loc < max_interval)
				{
					int int_index = loc / 32;
					int bit_index = loc % 32; //Written this way because expects compiler to repleace with bit operations
					composites[int_index] |= (1 << bit_index); //marks off the number as composite
					loc += init_primes[primeIndex];
				}
			}

			//find primes in interval and store them
			this -> store_primes(local_cpy_left_endpt, *thread_index);



		}
	}

	void store_primes(int local_cpy_left_endpt, int thread_index)
	{
		//add one to the factor multiplied by N for the new line character, and add one for null-termination

		const int interval_index = local_cpy_left_endpt / N;
		thread_local Generic_Thread_Lock_Routine instance = Generic_Thread_Lock_Routine();
		instance.set_fptr(&malloc_funct_under_lock);
		instance.set_args(&local_cpy_left_endpt);
		strings_to_print[interval_index] = (char *)(instance.lock_perform_unlock());
		//allocates under the lock to ensure that the strings don't overlap

		int end_loop = fmin(local_cpy_left_endpt + N, upper_lim + 1);
		int Num_Digits = num_digits(local_cpy_left_endpt);
		int next_digit_changer = pow(10, Num_Digits);
		int stringlen_buffer = 0;

		//skips all evens
		for (int i = local_cpy_left_endpt; i < end_loop; i+= 32)
		{
			int ele = composites[i / 32];
			for (int bit_index = 1; bit_index < 32; bit_index += 2)
			{
				if (!(ele & (1 << bit_index))) //if is prime
				{
					int num = i + bit_index;
					if (num > upper_lim)
						break;
					//determine whether the number of digits has changed
					while (num >= next_digit_changer)
					{
						next_digit_changer *= 10;
						Num_Digits ++;
					}
					num_primes[thread_index] ++;
					stringlen_buffer += convert_to_string(num, strings_to_print[interval_index] + stringlen_buffer, Num_Digits);

				}

			}

		}

		//condenses
		strings_to_print[interval_index] = (char *)(realloc(strings_to_print[interval_index], \
				stringlen_buffer + 1));

	}


	//Gathers composites and prints the primes to the text file.
	void get_primes()
	{
		assert(N % 32 == 0);

		if (lower_lim <= 2)
			fprintf(fp, "%d\n", 2);

		thread thread_array[num_threads];

		for (int i=0; i<num_threads; i++)
		{
			int *thread_index = (int *)(malloc(sizeof(int)));
			*thread_index = i;
			thread_array[i] = thread([=] {this -> collect_all_composites(thread_index);}); //[2]


		}
		for (int i=0; i<num_threads; i++)
			thread_array[i].join();


		int len = ceil(1.0 * upper_lim / N);
#if IS_MULTITHREADED
		qsort(strings_to_print, len, sizeof(char *), compare_str_by_first);
#endif

		for (int i=0; i<len; i++)
			fprintf(fp, "%s", strings_to_print[i]);

	}


	//computes the number of primes in the range. This method is used to check correctness.

	int get_num_primes()
	{
		return sum_array(num_threads, num_primes) + (lower_lim <= 2);
	}

};

//Claims a new list of primes to expand multiples of in the thread routine "collect_all_primes." This function
//is done under a lock
void *update_curr_prime_to_test(void *args)
{
	void *(*arr_arg)[2] = (void *((*)[2]))(args);
	Test_Primes *instance = (Test_Primes *)((*arr_arg)[0]);
	(instance -> left_endpt) += N;
	*(int *)((*arr_arg)[1]) = instance -> left_endpt;
	return NULL;
}

void *malloc_funct_under_lock(void *args)
{
	return calloc(N * (num_digits(*(int *)(args) + N) + 1) + 1, sizeof(char));
}

bool is_valid_user_input(int argc, char *argv[])
{
	if (argc <= 2 || argv[1] == NULL || argv[2] == NULL)
		return false;
	else if (strlen(argv[1]) < 16)
		return false;
	else if (strcmp(argv[1], "--createDataFile"))
		if (strlen(argv[1]) < 17 || strcmp(argv[1],  "--processDataFile"))
			return false;
	return true;
}

int main(int argc, char *argv[])
{

	if (!is_valid_user_input(argc, argv))
	{
		cout << "Error, must provide command line arguments of the form --createDataFile file or --processDataFile file" << endl;
		exit(EXIT_FAILURE);
	}

	//if the command is "--createDataFile," the third character is 'c'. Else it is not 'c'.
	//In the first case, create a file and return. Otherwise, run the program.
	const char *filename = (argv[1][2] == 'c') ? argv[1] + 17 : argv[1] + 18;
	if (argv[1][2] == 'c')
	{
		FILE *fp = fopen(filename, "w");
		fclose(fp);
		return 0;
	}

	FILE *fp = fopen(filename, "w");
	if (fp == NULL)
	{
		cout << "Error, file not read\n";
		exit(EXIT_FAILURE);
	}
	Test_Primes instance = Test_Primes(fp);
	double initial_time, final_time;
	initial_time = curr_time();
	instance.get_primes();

	int num_primes = instance.get_num_primes();
	final_time = curr_time();
	cout << "time_taken (seconds) = " << final_time - initial_time << endl;
	fclose(fp);
	cout << "number of primes = " << num_primes << endl;
}

/* 									REFERENCES
 *
 * [1] (2014). Atomic operations library [Online]. Available http://en.cppreference.com/w/cpp/atomic.
 * [2] (2013). c++11 Thread class how to use a class member function [Online].
 * Available http://www.cplusplusdevelop.com/721_21076003/.
 *
 *
 *
 *
 */
