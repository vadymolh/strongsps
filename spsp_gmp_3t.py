from multiprocessing import Pool, freeze_support
import math
import gmpy2
from gmpy2 import mpz 
import time
import itertools
import os, gc

import signal


def binary_gcd(a, b):
    r = 0    
    if (a < b):
        a, b = b, a
    if (b==0): 
        return a;
    r = a % b
    a, b = b, r
    if (b==0):
        return a;
    k = 0
    while (not((a|b)&1)): 
        k += 1
        a >>= 1
        b >>= 1
    while ( not(a&1) ):
        a >>= 1
    while ( not(b&1) ):
        b >>= 1
    while True:
        if (a==b): 
            return a << k
        if (a<b): 
            a, b = b, a
        t = (a-b) 
        t >>= 1       #t>0 
        while (not(t&1)): 
            t >>= 1
        a = t;
    
def binary_lcm(a, b):
    return  (a/binary_gcd(a, b)) * b;    

def _binary_lcm(numbers):
    return reduce(binary_lcm, numbers)    
   
def howlong(f):
    def tmp(*args, **kwargs):
        t = time.time()
        res = f(*args, **kwargs)
        print "time:%f" % (time.time()-t)
        return res
    return tmp
   

def available_cpu_count():
    ''' Number of available virtual or physical CPUs on this system'''
    try: 
        import multiprocessing 
        return multiprocessing.cpu_count()
    except (ImportError, NotImplementedError):
        pass    



def mul_mod (a, b , m):
    x = y = r = 0
    x = a * b 
    y = m * int(a*b/m+1/2)
    r = x - y 
    if (r < 0):
        r += m
    return r


def num_for_check2qt(num_for_check):
    '''Set q, t so that num_for_check==q*2^t+1'''
    q = num_for_check - 1 
    t = 0 
    while ((q & 1) == 0):
        q >>= 1
        t+= 1 
    return (q, t)



def prime_factors(x):
    """Returns list of prime factors of number __x__"""
    factorlist = []
    while x % 2 == 0:
        factorlist.append(2)
        x /= 2
    limit = 1 + int(gmpy2.isqrt(x))
    for factor in range (3, limit, 2):
        if x % factor == 0:
            factorlist.append(factor)
            x /= factor
    if x > 1: 
        factorlist.append(x)
    """Part2"""
    cc = factorlist
    facindex=[]
    for c in cc:
        z=cc.count(c)
        if [c,z] not in facindex:
            facindex.append([c,z])
    return facindex
    

def find_all_factors(n):
    factors = list(prime_factors(n))
    nfactors = len(factors)
    f = [0] * nfactors
    while True:
        yield reduce(lambda x, y: x*y, [factors[x][0]**f[x] for x in range(nfactors)], 1)
        i = 0
        while True:
            f[i] += 1
            if f[i] <= factors[i][1]:
                break
            f[i] = 0
            i += 1
            if i >= nfactors:
                return


def l_p(a_base, p):
    '''valuation of l(p)'''
    t = 1
    length = len(a_base)
    flag =[0]*length
    index = [n for n in range(0, length)]
    la_p = [0]*length
    list_factors = find_all_factors(p - 1)
    for t in list_factors:  
        if (not 0 in flag): 
            break        
        for i in index:
            if (flag[i]==1):
                continue
            if (int(gmpy2.powmod(a_base[i], t, p)) == 1):
                la_p[i] = t
                flag[i] = 1
            if (not 0 in flag): 
                break
    return la_p         	


def funcLoop(p_num, search_range, a_bases):
    
    itern = 0
    k = 1
    num_for_check = 0
    a_base = 0
    la_p = []
    lambda_p = 0
    down_limit = 3000000000
    mul = mul_tuple(p_num)
    check_flag = None
    checked = []
    lgndr = []
    if (p_num[0]%4 == 3):
        if (p_num[1]%4 == 3):
            for p in p_num:
                lgndr.append(legendre_symbol(a_bases, p))
            if (cmp(lgndr[0], lgndr[1])!= 0):
                return checked
            else:
                for p in p_num:
                    itern += 1
                    la_p.append(l_p(a_bases, p))
                    if (itern >= 2):
                        if (cmp(signature(la_p[itern-1]),signature(la_p[itern-2])) != 0): #copmparing signatures
                            return checked   
        elif (p_num[1]%4 == 1):
            for p in p_num:
                lgndr.append(legendre_symbol(a_bases, p))
            if (cmp(lgndr, [lgndr[0], [1]*len(lgndr[1])])!= 0):
                return checked            
            else:
                for p in p_num:
                    itern += 1
                    la_p.append(l_p(a_bases, p))
                    if (itern >= 2):
                        if (cmp(signature(la_p[itern-1]),signature(la_p[itern-2])) != 0): #copmparing signatures
                            return checked
    else:   
        for p in p_num:
            itern += 1
            la_p.append(l_p(a_bases, p))
            if (itern >= 2):
                if (cmp(signature(la_p[itern-1]),signature(la_p[itern-2])) != 0): #copmparing signatures
                    return checked   
    try:
        lambda_p = int(binary_lcm(la_p[0][0], la_p[1][0]))
    except TypeError:
        return checked
     
    gcommond = int(binary_gcd(lambda_p, p_num[0]))
    if int(binary_gcd(gcommond, p_num[1]))>1:
        return checked
    else:
        try:
            c = int(gmpy2.invert(mul, lambda_p))
        except ZeroDivisionError:
            return checked
        
        pt = int(gmpy2.next_prime(p_num[len(p_num)-1])) # first factor to check
              
        while pt < (search_range/mul):
            check_flag = True
            if (gmpy2.f_mod(pt, lambda_p) == gmpy2.f_mod(c, lambda_p)):
                num_for_check = mul*pt
                if (num_for_check < search_range):
                    q, t = num_for_check2qt(num_for_check)
                    for a_base in a_bases:
                        if not isStrongPsp(num_for_check, a_base, q, t):
                            check_flag = False
                    if check_flag == True:
                        checked.append([num_for_check, p_num[0], p_num[1], pt])
                        print 'p1--> %8s   p2-->%8s   p3-->%8s   base->: %s   spsp: %16s' % (p_num[0], p_num[1], pt, a_bases, num_for_check )
                        
            pt = int(gmpy2.next_prime(pt))
        return checked


def write_output_data(result_list, search_range, a_bases, start_time):
    '''Formating results for output'''
    i = 0
    x = []
    if len(result_list) == 1:
        x = result_list[0]
        open_file_wr(x,search_range, a_bases, start_time)
    else:    
        result_list = [x for x in result_list if x is not None]
        result_list.sort()
        x = []
        for i in range(0,len(result_list)):
            x.append(result_list[i])
        open_file_wr(x,search_range, a_bases, start_time)
    
    
    
def open_file_wr(x, search_range, a_bases, start_time):
    '''Writes result in file: output_psps.txt from the from the current directory''' 
    f = open('output_async_spsp3t.txt', 'w')
    f.write('Tested with bases: ')
    for a_base in a_bases:
        f.write('%s  ' % a_base)
    f.write('in range  -  %s' % int(search_range))
    f.write('\n')
    """Formatting, and printing time"""
    end_time = time.time() 
    end_time = end_time - start_time
    if (end_time > 86400):
        t = time.strftime('%j days %H:%M:%S', time.gmtime(end_time)) 
    else:
        t = time.strftime('%H:%M:%S', time.gmtime(end_time))
    print  t
    f.write('Time of execution:  %s  \n' % (t))
    f.write('spsp number:                        factor p1:               factor p2:               factor p3:\n')
    l=[]
    n=[]
    k1,k2 = 0, 0
    for l in x:
        if isinstance(l, list):
            for num in l:
                f.write('     %16s    ' % (num))
            if ((int(l[3])-1)%(int(l[1])-1) == 0):    
                k1, k2= (int(l[3])-1)/(int(l[1])-1), (int(l[2])-1)/(int(l[1])-1)
                f.write(' (k+1)(%dk+1)(%dk+1)' % (k2, k1))       
            f.write('\n')
        else:
            f.write('     %16s        ' % (l))
              
    f.close()

    
def read_input_data():
    '''Reading input values from file input_data_psps.txt 
    from curent directory'''
    f = open("input_data_spsp3t.txt")              
    for line in f:                       # loop over the file directly
        line = line.rstrip()             # remove the trailing newline
        if line.startswith('SEARCH_RANGE:'):
            s = line[len('SEARCH_RANGE:'):]
            if '*10^' in s:
                s0 = s[:s.index('*10^')]
                power = s[s.index('*10^')+4:]
                search_range = round(int(float(s0)*math.pow(int(10),int(power))))
            else:
                search_range = int(line[len('SEARCH_RANGE:'):])
        elif line.startswith('A_BASE:'):
            a_bases = map(int, (line[len('A_BASE:'):]).split())
        else:
            raise ValueError('Unknown attribute: %r' % line)
    f.close()
    return a_bases, search_range
    
def isStrongPsp(num_for_check, a_base, q, t):
    '''Checks for strong pseudoprime numbers
    q and t must be set so that num_for_check==q*2^t+1'''
    b = int(gmpy2.powmod(a_base, q, num_for_check))
    e = 1 

    if (b == 1):
        return True
    while ((b!=1) and (b!=(num_for_check-1)) and e<t):
        b = mul_mod(b, b, num_for_check)
        e+= 1
    if (b!=(num_for_check-1)): 
        return False
    return True

    
def signature(lap):
    length = len(lap)
    l_p = lap
    sign = [0]*length
    for index in range(0, length):
        if (l_p[index]%2 != 0):
            continue
        while (l_p[index]%2==0):
            l_p[index] >>= 1
            sign[index] += 1
    return sign
            
def legendre_symbol(a_bases, p):
    ''' Returns the list of Legendre symbols (a_bases | p). "p" is assumed to be an odd prime.'''
    legndr_list = []
    for base in a_bases:
        legndr_list.append(gmpy2.legendre(base, p))
    return legndr_list  


result_list = []
def log_result(result):
    num = []
    if (result != []):
        [result_list.append(num) for num in result]	
     	
		
def mul_tuple(p_num):
    mul = 1
    for p in p_num:
        mul = int(gmpy2.mul(mul,p))
    return mul


def init_worker():
    signal.signal(signal.SIGINT, signal.SIG_IGN)

@howlong
def main():
    start_time = time.time()
    #Reading input values
    a_bases, search_range = read_input_data()
    
    
    print "Start searching for spsp numbers by bases -> %s in range from 3 to %s" % (a_bases, int(search_range))    
    
        
    #defining number of available cpu cores, and creating threads
    nCPU = available_cpu_count()
    global pool
    
    
    p_num = []
    p_inner = [gmpy2.next_prime(max(a_bases)), gmpy2.next_prime(max(a_bases)+1)]
    factor_range = int(gmpy2.iroot_rem(mpz(search_range), mpz(3))[0])
    pool = Pool(nCPU, init_worker)
    delta_time = time.time()
    try:
        print "Press Ctrl+C to exit"
        while (p_inner[0] < factor_range):
            while (p_inner[1] < factor_range):
                p_inner[1] = int(gmpy2.next_prime(p_inner[1]))
                pool.apply_async(funcLoop, args = ([int(p_inner[0]), p_inner[1]], search_range, a_bases,), callback = log_result)
            pool.close()
            pool.join()
            pool = Pool(nCPU, init_worker)#processes=nCPU
            p_inner[0] = int(gmpy2.next_prime((p_inner[0])))
            p_inner[1] = int(gmpy2.next_prime((p_inner[0])))
        print "end"
    except KeyboardInterrupt:
        print "Terminate the process"
        pool.terminate()
        pool.join()
        
            
    write_output_data(result_list, search_range, a_bases, start_time)
    	
if __name__ =="__main__":
    freeze_support()
    main()    
