import { comment, execute, tellraw } from "sandstone/commands";
import { _ } from "sandstone/core";
import { PlayerScore, Selector, Variable } from "sandstone/variables";

var neginf = Variable(-2147483648);

function po2(num: number) {
    return Math.pow(2, num);
}

function compare(a: PlayerScore, b: PlayerScore) : PlayerScore {
    var out = Variable(0);
    _.if(a.lowerThan(b), () => {out.set(-1)});
    _.if(a.greaterThan(b), () => {out.set(1)});
    return out;
}

function ucompare(a: PlayerScore, b: PlayerScore) : PlayerScore {
    return compare(a.plus(neginf), b.plus(neginf));
}


function ushr(num: PlayerScore, shiftBy: number): PlayerScore {
    var shifted = Variable();
    if (shiftBy == 31) {
        execute.store.result.score(shifted).if(num.lowerThan(0))
    } else {
        shifted.set(num);
        _.if(num.lowerOrEqualThan(-1), () => {
            shifted.add(neginf);
            shifted.divide(po2(shiftBy)|0);
            shifted.add(po2(31 - shiftBy)|0);
        }).else(
            () => {
                shifted.divide(po2(shiftBy)|0);
            }
        )
    }
    return shifted;
}


class Long {
    top: PlayerScore;
    bottom: PlayerScore;

    constructor(low?: PlayerScore | number, high?: PlayerScore | number) {
        if (!low && !high) {
            this.top = Variable(0);
            this.bottom = Variable(0);
        } else if (!high) {
            this.top = Variable(0);
            this.bottom = Variable();
            this.bottom.set(low as any);
            if (typeof low == 'number') {
                if (low < 0) this.top.set(-1);
            } else {
                _.if(low.lowerThan(0), () => { this.top.set(-1) });
            }
        } else {
            this.top = Variable();
            this.top.set(high as any);
            this.bottom = Variable();
            this.bottom.set(low as any);
        }
    }

    multiplyC(multiplyBy: number | bigint): Long {
        multiplyBy = BigInt(multiplyBy)
        var l2h = multiplyBy >> BigInt(32);
        var l2l = multiplyBy & BigInt(0xFFFFFFFF);
        comment('mul start ' + l2h + ' ' + l2l + ' ' + multiplyBy);
        var bl = Number(l2l & BigInt(0xFFFF));
        var bh = Number(l2l) >>> 16;
        var al = this.bottom.moduloBy(0x10000);
        var ah = ushr(this.bottom, 16);
        var p10 = ah.multipliedBy(bl);
        var p01 = al.multipliedBy(bh);
        var p11 = ah.multipliedBy(bh);
        var high = ushr(p01, 16);
        high.add(p11);
        high.add(ushr(p10, 16));
        var low = al.multipliedBy(bl);
        p10.multiply(1 << 16);
        low.add(p10);
        execute.if(low.plus(neginf).lowerThan(p10.plus(neginf))).run(() => high.add(1));

        p01.multiply(1 << 16);
        low.add(p01);
        execute.if(low.plus(neginf).lowerThan(p01.plus(neginf))).run(() => high.add(1));

        high.add(this.bottom.multipliedBy((Number(l2h) | 0)));
        high.add(this.top.multipliedBy((Number(l2l) | 0)));
        return new Long(low, high);
    }

    multiplyL(multiplyBy: Long): Long {
        var l2h = multiplyBy.top;
        var l2l = multiplyBy.bottom;
        var bl = l2l.moduloBy(0x10000);
        var bh = ushr(l2l, 16);
        var al = this.bottom.moduloBy(0x10000);
        var ah = ushr(this.bottom, 16);
        var p10 = ah.multipliedBy(bl);
        var p01 = al.multipliedBy(bh);
        var p11 = ah.multipliedBy(bh);
        var high = ushr(p01, 16);
        high.add(p11);
        high.add(ushr(p10, 16));
        var low = al.multipliedBy(bl);
        p10.multiply(1 << 16);
        low.add(p10);
        execute.if(low.plus(neginf).lowerThan(p10.plus(neginf))).run(() => high.add(1));
        p01.multiply(1 << 16);
        low.add(p01);
        execute.if(low.plus(neginf).lowerThan(p01.plus(neginf))).run(() => high.add(1));
        high.add(this.bottom.multipliedBy(l2h));
        high.add(this.top.multipliedBy(l2l));
        return new Long(low, high);
    }

    divideL(divisor: Long): Long {
        comment('div start;')
        var divSign = Variable(0);
        execute.if(divisor.top.lowerThan(0)).if(this.top.greaterOrEqualThan(0)).run(() => {divSign.set(1)});
        execute.if(divisor.top.greaterOrEqualThan(0)).if(this.top.lowerThan(0)).run(() => {divSign.set(1)});
        var modulus = this.copy();
        divisor = divisor.copy();

        _.if(this.top.lowerThan(0), () => {
            modulus.negate();
        });

        _.if(divisor.top.lowerThan(0), () => {
            divisor.negate();
        });

        var quotient = new Long(0);
        var mask = new Long(1);
        var beak = Variable(0);
        _.while(_.and(divisor.top.greaterOrEqualThan(0), beak.equalTo(0)), () => {
            var cmp = divisor.ucompare(modulus);
            divisor._inplace_shl(1);
            mask._inplace_shl(1);
            _.if(cmp.greaterOrEqualThan(0), () => {
                beak.set(1);
            })
        });

        _.while(_.not(_.and(mask.top.equalTo(0), mask.bottom.equalTo(0))), () => {
            var cmp = modulus.ucompare(divisor);
            _.if(cmp.greaterOrEqualThan(0), () => {
                quotient._inplace_add(mask);
                modulus._inplace_subl(divisor);
            });
            mask._inplace_ushr(1);
            divisor._inplace_ushr(1);
        })

        return quotient;
    }

    multiply(multipliedBy: Long | number): Long {
        if (typeof multipliedBy == 'number') {
            return this.multiplyC(multipliedBy);
        }
        return this.multiplyL(multipliedBy);
    }

    ucompare(b: Long): PlayerScore {
        var v = ucompare(this.top, b.top);
        _.if(v.equalTo(0), () => {v.set(ucompare(this.bottom, b.bottom))});
        return v;
    }

    negate() {
        this.top.multiply(-1).remove(1);
        this.bottom.multiply(-1);
        _.if(this.bottom.equalTo(0), () => { this.top.add(1) });
    }

    addL(add: Long): Long {
        comment('add start');
        var high = this.top.plus(add.top);
        var low = this.bottom.plus(add.bottom);
        execute.if(low.plus(neginf).lowerThan(this.bottom.plus(neginf))).run(() => high.add(1));
        return new Long(low, high);
    }

    _inplace_add(add: Long) : Long {
        var low = this.bottom.plus(add.bottom);
        execute.if(low.plus(neginf).lowerThan(this.bottom.plus(neginf))).run(() => this.top.add(1));
        this.top.add(add.top);
        this.bottom.set(low);
        return this;
    }

    addC(add: number | bigint): Long {
        add = BigInt(add);
        var tadd = Number(add & BigInt(0xFFFFFFFF));
        comment('addC start ' + add + ' ' + tadd);
        if (tadd < 2147483648) {
            var low = this.bottom.plus(tadd);
        } else {
            comment('neg');
            var low = this.bottom.minus(4294967296 - tadd);
        }
        var high = this.top.plus(Number(add >> BigInt(32)));
        execute.if(low.plus(neginf).lowerThan(this.bottom.plus(neginf))).run(() => high.add(1));
        return new Long(low, high);
    }

    add(add: number | Long): Long {
        if (typeof add == 'number') {
            return this.addC(add);
        }
        return this.addL(add);
    }

    _inplace_subl(b: Long) {
        this.top.remove(b.top);
        execute.if(this.bottom.plus(neginf).lowerThan(b.bottom.plus(neginf))).run(() => this.top.remove(1));
        this.bottom.remove(b.bottom);
    }

    subL(b: Long): Long {
        var high = this.top.minus(b.top);
        var low = this.bottom.minus(b.bottom);
        execute.if(this.bottom.plus(neginf).lowerThan(b.bottom.plus(neginf))).run(() => high.remove(1));
        return new Long(low, high);
    }

    subC(b: bigint): Long {
        var tadd = Number(b & BigInt(0xFFFFFFFF));
        comment('subC start ' + b + ' ' + tadd);
        if (tadd < 2147483648) {
            var low = this.bottom.minus(tadd);
        } else {
            comment('neg');
            var low = this.bottom.plus(4294967296 - tadd);
        }
        var high = this.top.minus(Number(b >> BigInt(32)));
        execute.if(this.bottom.plus(neginf).lowerThan(0 | (tadd - 2147483648))).run(() => high.remove(1));
        return new Long(low, high);
    }

    sub(add: number | Long): Long {
        if (typeof add == 'number') {
            return this.subC(BigInt(add));
        }
        return this.subL(add);
    }

    ushr(shift: number): Long {
        comment('shift start');
        var low = ushr(this.bottom, shift);
        var high = ushr(this.top, shift);
        low.add(this.top.multipliedBy(po2((32 - shift))|0))
        comment('shift end unsigned');
        return new Long(low, high);
    }

    _inplace_ushr(shift: number) {
        comment('shift start');
        this.bottom.set(ushr(this.bottom, shift));
        this.bottom.add(this.top.multipliedBy(po2((32 - shift))|0))
        this.top.set(ushr(this.top, shift));
        comment('shift end unsigned');
    }

    _inplace_shl(shift: number) {
        comment('shift start');
        this.top.multiply(po2(shift));
        var tmep = ushr(this.bottom, 32-shift);
        this.top.add(tmep);
        this.bottom.multiply(po2(shift));
    }

    set(value: Long) {
        this.bottom.set(value.bottom);
        this.top.set(value.top);
    }

    copy(): Long {
        return new Long(this.bottom, this.top);
    }
}


class Fixed32 {
    value: PlayerScore

    constructor(int_value: PlayerScore | number, scaled?: boolean) {
        if (scaled) {
            this.value = Variable();
            this.value.set(int_value as any);
        } else {
            if (typeof int_value == 'number') {
                this.value = Variable(int_value * 1024);
            } else {
                this.value = int_value.multipliedBy(1024);
            }
        }
    }

    add(value2: Fixed32) :Fixed32 {
        return this.clone()._inplace_add(value2);
    }

    sub(value2: Fixed32) : Fixed32 {
        return this.clone()._inplace_sub(value2);
    }

    mul(value2: Fixed32) : Fixed32 {
        var res = new Long(this.value).multiply(new Long(value2.value));
        res._inplace_ushr(10);
        _.if(_.not(res.top.equalTo(0)), () => {
            tellraw(Selector('@a'), 'Overflow in fixed32 multiplication');
        })
        return new Fixed32(res.bottom, true);
    }

    div(value2: Fixed32) : Fixed32 {
        var res = new Long(this.value);
        res._inplace_shl(10);
        res = res.divideL(new Long(value2.value));
        _.if(_.not(res.top.equalTo(0)), () => {
            tellraw(Selector('@a'), 'Overflow in fixed32 division');
        })
        return new Fixed32(res.bottom, true);
    }

    idiv(value2: PlayerScore | number) : Fixed32 {
        var res = this.clone();
        res.value.divide(value2 as any);
        return res;
    }

    clone(): Fixed32 {
        return new Fixed32(this.value, true);
    }

    _inplace_add(value2: Fixed32) :Fixed32 {
        this.value.add(value2.value);
        return this;
    }

    _inplace_sub(value2: Fixed32):Fixed32 {
        this.value.remove(value2.value);
        return this;
    }

    set(other: Fixed32) {
        this.value.set(other.value);
    }
}


export { Long, Fixed32, ushr, compare, ucompare};