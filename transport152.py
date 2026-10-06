#!/usr/bin/env python3
from itertools import count

def keep(p, state, size):
    if size == 1: return bool(p)
    half = size >> 1
    return keep(min(p, half) if state & 1 else max(0, p - half), state >> 1, half)

def tick(p, state, size):
    state = (state + 1) & (size - 1)
    while not keep(p, state, size): state = (state + 1) & (size - 1)
    return state

def run(limit):
    if limit < 5: return
    primes, clocks, previous, centers, level = [], {}, 0, [], 2
    for x in count(2):
        prime = True
        for p, (state, size) in clocks.items():
            state = tick(p, state, size); clocks[p] = (state, size)
            if state == (0 if p == 2 else 1): prime = False
        if not prime: continue
        primes.append(x); clocks[x] = (0 if x == 2 else 1, 1 << (x - 1).bit_length())
        if x - previous == 2 and x > 5:
            center = x - 1; centers.append(center)
            if len(centers) == primes[level]:
                print(primes[level], tuple(centers))
                level += 1
                if level >= len(primes) or primes[level] > limit: return
                centers = [center]
        previous = x

if __name__ == '__main__':
    import sys
    run(int(sys.argv[1]) if len(sys.argv) > 1 else int(input('Prime ceiling: ')))
