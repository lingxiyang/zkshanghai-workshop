# 第 2 课 课后作业

## 第 1 题 转换为 bit 位 Num2Bits

    pragma circom 2.1.4;

    template Num2Bits (nBits) {
        signal input in;
        signal output b[nBits];
        var y=0;
        var incr =1;
        for(var i = 0; i < nBits; i++){
            b[i] <-- (in >> i) &1;
            b[i] * (b[i]-1) ===0;
            y += b[i]*incr;
            incr= incr  + incr;
        }
        y === in;
    }

    component main = Num2Bits(3);

    /* INPUT = {
        "in": "5"
    } */

## 第 2 题判零 IsZero

    pragma circom 2.1.4;

    template IsZero () {
        signal input in;
        signal output out;
        signal inv;
        inv <-- in ==0?1:1/in;
        out <== -inv*in +1;
        in*out === 0;
    }

    component main = IsZero();

    /* INPUT = {
        "in": "1"
    } */

## 第 3 题 相等 IsEqual

    pragma circom 2.1.4;
    template IsZero () {
        signal input in;
        signal output out;
        signal inv;
        inv <-- in ==0?1:1/in;
        out <== -inv*in +1;
        in*out === 0;
    }
    template IsEqual () {
        signal input in[2];
        signal output out;
        component zero = IsZero();
        zero.in <== in[0] - in[1];
        out <== zero.out;
    }

        component main = IsEqual();

        /* INPUT = {
            "in": ["0","0"]
        } */

## 第 4 题 选择器 Selector

    pragma circom 2.1.4;
    template Num2Bits (nBits) {
            signal input in;
            signal output out[nBits];
            var y=0;
            var incr =1;
            for(var i = 0; i < nBits; i++){
                out[i] <-- (in >> i) &1;
                out[i] * (out[i]-1) ===0;
                y += out[i]*incr;
                incr= incr  + incr;
            }
            y === in;
    }
    template IsZero () {
            signal input in;
            signal output out;
            signal inv;
            inv <-- in ==0?1:1/in;
            out <== -inv*in +1;
            in*out === 0;
        }
        template IsEqual () {
            signal input in[2];
            signal output out;
            component zero = IsZero();
            zero.in <== in[0] - in[1];
            out <== zero.out;
        }
    template LessThan(n) {
        assert(n <= 252);
        signal input in[2];
        signal output out;

        component n2b = Num2Bits(n+1);
        n2b.in <== in[0]+ (1<<n) - in[1];

        out <== 1-n2b.out[n];
    }
    template CalculateTotal(n) {
        signal input in[n];
        signal output out;

        signal sums[n];

        sums[0] <== in[0];

        for (var i = 1; i < n; i++) {
            sums[i] <== sums[i-1] + in[i];
        }

        out <== sums[n-1];
    }

    template Selector(nChoices) {
        signal input in[nChoices];
        signal input index;
        signal output out;


        component lessThan = LessThan(4);
        lessThan.in[0] <== index;
        lessThan.in[1] <== nChoices;
        lessThan.out === 1;

        component calcTotal = CalculateTotal(nChoices);
        component eqs[nChoices];

        for (var i = 0; i < nChoices; i ++) {
            eqs[i] = IsEqual();
            eqs[i].in[0] <== i;
            eqs[i].in[1] <== index;

            calcTotal.in[i] <== eqs[i].out * in[i];
        }

        out <== calcTotal.out;
    }
    component main = Selector(4);
    /* INPUT = {
            "in": ["3","2","4","5"],
            "index":"1"
        } */

## 第 5 题 判负 IsNegative

    pragma circom 2.1.4;
    include "circomlib/compconstant.circom";
        template IsNegative () {
            signal input in;
            signal output out;
            component comp = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
            component num2bits = Num2Bits(254);
            num2bits.in <==in;
            var i;
            for (i=0; i<254; i++) {
                comp.in[i] <== num2bits.out[i];
            }
            out <== comp.out;
        }

        component main = IsNegative();

        /* INPUT = {
            "in": "21888242871839275222246405745257275088548364400416034343698204186575808495616"
        } */

## 第 6 题 少于 LessThan

    pragma circom 2.1.4;

    template Num2Bits (nBits) {
    signal input in;
    signal output out[nBits];
    var y=0;
    var incr =1;
    for(var i = 0; i < nBits; i++){
        out[i] <-- (in >> i) &1;
        out[i] * (out[i]-1) ===0;
        y += out[i]*incr;
        incr= incr  + incr;
    }
    y === in;
    }
    template LessThan() {
    signal input in[2];
    signal output out;
    component n2b = Num2Bits(253);
    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
    }


    component main = LessThan();

    /* INPUT = {
    "in": ["2","3"]
    } */

## 第 6.1 题 lessThen 扩展参数

    pragma circom 2.1.4;

    template Num2Bits (nBits) {
    signal input in;
    signal output out[nBits];
    var y=0;
    var incr =1;
    for(var i = 0; i < nBits; i++){
        out[i] <-- (in >> i) &1;
        out[i] * (out[i]-1) ===0;
        y += out[i]*incr;
        incr= incr  + incr;
    }
    y === in;
    }
    template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);
    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];
    }
    component main = LessThan(250);

    /* INPUT = {
    "in": ["2","3"]
    } */

## 第 6.2 题 LessEqThan 等

    pragma circom 2.1.4;

        template Num2Bits (nBits) {
            signal input in;
            signal output out[nBits];
            var y=0;
            var incr =1;
            for(var i = 0; i < nBits; i++){
                out[i] <-- (in >> i) &1;
                out[i] * (out[i]-1) ===0;
                y += out[i]*incr;
                incr= incr  + incr;
            }
            y === in;
            }
            template LessThan(n) {
            assert(n <= 252);
            signal input in[2];
            signal output out;

            component n2b = Num2Bits(n+1);
            n2b.in <== in[0]+ (1<<n) - in[1];

            out <== 1-n2b.out[n];
        }
        template LessEqThan(n) {
            signal input in[2];
            signal output out;

            component lessThen = LessThan(n);
            lessThen.in[0] <== in[0];
            lessThen.in[1] <== in[1]+1;
            out <== lessThen.out;
        }
        template GreaterThan(n){
            signal input in[2];
            signal output out;

            component lessThen = LessThan(n);
            lessThen.in[0] <== in[1];
            lessThen.in[1] <== in[0];
            out <== lessThen.out;
        }
        template GreaterEqThan(n){
            signal input in[2];
            signal output out;

            component greaterThen = GreaterThan(n);
            greaterThen.in[0] <== in[0]+1;
            greaterThen.in[1] <== in[1];
            out <== greaterThen.out;
        }
        // component main = LessEqThan(250);
        //  component main = GreaterThan(250);
        component main = GreaterEqThan(250);

        /* INPUT = {
        "in": ["3","3"]
        } */

## 第 7 题 整数除法 IntegerDivide
