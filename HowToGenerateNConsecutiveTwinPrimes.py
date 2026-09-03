from math import comb, gcd
from itertools import combinations
from functools import cache


# --------------------------------------------------
# OPTIONS
# --------------------------------------------------
#gives extra details
SHOW_DETAILS = False

# True:
#   Solve crossover directly with modular arithmetic.
#  It's best to keep optimization on, otherwise even level 31 requires 8 seconds to compute.
#  But using the optimizer doesnt change how the program fundamentally works.
# False:
#   Use the original step-by-step crossover search.
OPTIMIZE_CROSSOVER = True


# Simplex depths currently required.
SIMPLEX_ORDERS = (
    2,
    3
)


# Last prime level to generate.
MAX_STAGE = 60


# --------------------------------------------------
# PRIME STAGES
# --------------------------------------------------
# These Primes are manually entered by hand to make it crystal clear that the program
# does not do any independent prime certification such as calling isprime()

#To increase range, simply set max stage higher and add the primes in the list you wan to add
#  --again, I could make this part recursive but that is just regular trivial sieve mechanics.
# --------------------------------------------------

PRIMES = [
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    19,
    23,
    29,
    31,
    37,
    41,
    43,
    47,
    53,
    59
]


# --------------------------------------------------
# CROSS
# --------------------------------------------------

def cross(step, a, b):

    return (
        (step * a) % b
        ==
        (step * b) % a
    )


# --------------------------------------------------
# FIRST CROSSOVER ROW
# --------------------------------------------------

def first_cross_step(a, b):

    # The operation is symmetric.
    if a > b:
        a, b = b, a

    return _first_cross_step(
        a,
        b,
        OPTIMIZE_CROSSOVER
    )


@cache
def _first_cross_step(a, b, optimized):

    if a == b:
        return 1


    # ----------------------------------------------
    # ORIGINAL SEARCH
    # ----------------------------------------------

    if not optimized:

        step = 1

        while not cross(
            step,
            a,
            b
        ):

            step += 1

        return step


    # ----------------------------------------------
    # OPTIMIZED SEARCH
    # ----------------------------------------------

    common = gcd(
        a,
        b
    )

    left = a // common
    right = b // common


    if left == 1:
        return right


    period = (
        left
        * right
    )


    inverse_left = pow(
        left,
        -1,
        right
    )

    inverse_right = pow(
        right,
        -1,
        left
    )


    base = (

        inverse_left

        + right
        * (
            (
                inverse_right
                - inverse_left
            )

            * inverse_right

            % left
        )

    ) % period


    best = period


    for remainder in range(
        1,
        left
    ):

        step = (
            remainder
            * base
        ) % period


        if (
            step != 0
            and step < best
        ):

            best = step


    return best


# --------------------------------------------------
# RECURSIVE SIMPLEX CROSS
# --------------------------------------------------
# The simplex crosses allow us to understand the structure of the crosses we get,
# it allows us to know the prime addresses without knowing the prime addresses.


@cache
def simplex_cross(states):

    # C(p,1)
    if len(states) == 1:
        return states[0]


    # Two overlapping lower-dimensional faces.
    left = simplex_cross(
        states[:-1]
    )

    right = simplex_cross(
        states[1:]
    )


    if left == right:
        return left


    return first_cross_step(
        left,
        right
    )


# --------------------------------------------------
# SIMPLEX CROSSOVER LAYERS
# --------------------------------------------------

#In higher numebrs further crosses are required, could call it crosses of crosses.
#  This is what allows our list to be complete.

def simplex_crossovers(previous_level):

    p = len(
        previous_level
    )


    print()
    print("-----------------------------------------")
    print("COMPLETED LEVEL", p)
    print("-----------------------------------------")


    all_rows = set()


    # ==================================================
    # C(p,2), C(p,3), ...
    # ==================================================

    for order in SIMPLEX_ORDERS:

        rows = set()

        sources = []

        count = 0


        expected = comb(
            p,
            order
        )


        for group in combinations(
            previous_level,
            order
        ):

            count += 1

            group = tuple(
                group
            )


            row = simplex_cross(
                group
            )


            rows.add(
                row
            )


            if SHOW_DETAILS:

                sources.append(
                    (
                        group,
                        row
                    )
                )


        assert count == expected


        print(
            "C("
            + str(p)
            + ","
            + str(order)
            + ") =",
            expected,
            "| combinations =",
            count,
            "| unique crossover rows =",
            len(rows)
        )


        all_rows.update(
            rows
        )


        # ----------------------------------------------
        # OPTIONAL SOURCE TRACING
        # ----------------------------------------------

        if SHOW_DETAILS:

            print()

            print(
                "Crossover sources from C("
                + str(p)
                + ","
                + str(order)
                + "):"
            )


            for group, row in sources:

                print(
                    group,
                    "->",
                    row
                )


    # ==================================================
    # CROSSOVER CLOCKS
    # ==================================================
    #
    # No primality recognition is performed here.
    #
    # Every crossover row generated by the simplex
    # becomes a clock.
    # ==================================================

    generated_clocks = sorted(

        row

        for row in all_rows

        if row >= 5
    )


    return generated_clocks


# --------------------------------------------------
# PRIME CLOCK TEST
# --------------------------------------------------
# By simply testing if a number is on a +1 -1 Boundary we know it is
# not a Twin prime center.  Twin prime centers cannot fall on +1 or -1 of a modular cycle

def clock_ok(center, primes):

    for p in primes:

        phase = center % p


        if (
            phase == 1
            or phase == p - 1
        ):

            # Do not reject the clock itself
            # when it appears as a neighbor.

            if (
                center - 1 != p
                and center + 1 != p
            ):

                return False


    return True


# --------------------------------------------------
# GENERATE ONE PRIME LEVEL
# --------------------------------------------------
# Each prime given in the above list creates its own level, that is
# it creates everything it needs to generate p consecutive twin primes.


def level(
    start,
    primes,
    amount
):

    output = []

    center = start


    while len(output) < amount:


        if clock_ok(
            center,
            primes
        ):

            output.append(
                center
            )


        center += 6


    return output


# ==================================================
# PRIME STAGES
# ==================================================
#
# The explicit PRIMES list is used ONLY here
# to determine which levels are constructed.
# This could easily be made into a recursive function.
# ==================================================


prime_stages = [

    p

    for p in PRIMES

    if (
        5 <= p <= MAX_STAGE
    )
]


print(
    "prime stages:",
    prime_stages
)


# ==================================================
# INITIAL LEVEL: 5
# ==================================================
# The original Layer 5 and 7 are special and different because they are setting up the machinery.
#


level5 = level(

    start=6,

    primes=[
        5
    ],

    amount=5
)


print()
print("=========================================")
print("LEVEL 5")
print("=========================================")

print(
    "clocks:",
    [5]
)

print(
    "centers:",
    level5
)


# ==================================================
# INITIAL LEVEL: 7
# ==================================================

level7 = level(

    start=level5[-1],

    primes=[
        5,
        7
    ],

    amount=7
)


print()
print("=========================================")
print("LEVEL 7")
print("=========================================")

print(
    "clocks:",
    [5, 7]
)

print(
    "centers:",
    level7
)


# ==================================================
# RECURSIVE STATE
# ==================================================

previous_level = level7


# ==================================================
# ALL LATER LEVELS
#
# This puts it all together and prints all the levels in your list
# Try it out! Expand the range to what your computer can handle!
# Or if you are a wizard, optimize it further!
# ==================================================

for p in prime_stages[2:]:


    # --------------------------------------------------
    # Build the entire clock state from the simplex
    # crossover structure of the immediately previous
    # completed level.
    #
    # ALL generated crossover rows are used.
    # No primality recognition is performed.
    # --------------------------------------------------

    generated_clocks = simplex_crossovers(
        previous_level
    )


    print()
    print("=========================================")
    print("LEVEL", p)
    print("=========================================")


    # --------------------------------------------------
    # Generate exactly p consecutive centers.
    # --------------------------------------------------

    current_level = level(

        start=previous_level[-1],

        primes=generated_clocks,

        amount=p
    )


    print(
        "centers:",
        current_level
    )


    # --------------------------------------------------
    # Completed level becomes the entire state
    # for the next recursion.
    # --------------------------------------------------

    previous_level = current_level
