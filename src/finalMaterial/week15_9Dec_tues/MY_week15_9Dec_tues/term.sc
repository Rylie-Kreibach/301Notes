// #Sireum #Logika

import org.sireum._

def mult(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )

    var sum: Z = 0
    var count: Z = 0

    //measure of work? (how many more iterations left?)
    //initially?
        //y
    //after 1 iteration?
        //y-1 or y-count

    //in general?

    while (count < y) {
        Invariant(
            Modifies(sum, count),
            count <= y,
            sum == x*count
        )

        //measure: y-count
        sum = sum + x
        count = count + 1
        //measure: y-count
            //still works bc count++


        //measure should decrease with each iteration
            //does it?
                //Yes

        //when I have no work left, then my loop should be done
            //is it?
                //y == count: false, so you leave the loop
    }

    return sum
}

def multRec(x: Z, y: Z): Z = {
    Contract(
        Requires(y >= 0),
        Ensures(Res[Z] == x*y)
    )
    //termination measure: 
        //for all non-neg y
        //Base case: 0
            //MultRec(x, 0): terminates
                //Doesn't infinitely recurse
        //Inductive step: 
            //Assume inductive hypothesis: that MultRec(x, k) for some non-neg integer k
            //Prove: MultRec(x, k+1)
                //is at least 1, so enter else and make recursive call MultRec(x, k+1-1) which terminates
                    //Thus, we know MultRec(x, k+1) will also terminate
    var answer: Z = 0

    if (y == 0) {
        answer = 0
    } else {
        var temp: Z = mult(x, y-1)
        answer = x + temp
    }

    return answer
}

def collatz(n: Z): Z = {
    Contract(
        Requires(n > 0),
        Ensures(Res[Z] == 1)
    )

    //what if n is 52?
    //cur = 52, 26, 13, 40, 20, 10, 5, 16, 8, 4, 2, 1

    var cur: Z = n
    while (cur > 1) {
        Invariant(
            Modifies(cur),
            cur >= 1        //what else could we say?
        )

        if (cur % 2 == 0) {
            cur = cur / 2
        } else {
            cur = 3 * cur + 1
        }
    }

    return cur
}