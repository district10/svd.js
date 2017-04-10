// Pure JavaScript SVD algorithm.
// Input: 2-D list (m by n) with m >= n
// Output: U,W V so that A = U*W*VT
//
// -   Translated from python code by TANG ZhiXiong
// -   GitHub: https://github.com/district10/svd.js
// -   Origin: http://stitchpanorama.sourceforge.net/Python/svd.py
// -   FYI: http://stackoverflow.com/questions/960060/singular-value-decomposition-svd-in-php
//
// Usage:
//        var a = [
//            [22.,10., 2.,  3., 7.],
//            [14., 7.,10.,  0., 8.],
//            [-1.,13.,-1.,-11., 3.],
//            [-3.,-2.,13., -2., 4.],
//            [ 9., 8., 1., -2., 4.],
//            [ 9., 1.,-7.,  5.,-1.],
//            [ 2.,-6., 6.,  5., 1.],
//            [ 4., 5., 0., -2., 2.]
//        ];
//        var ret = svd(a);
//        var u, w, v;
//        if (ret) {
//            u = ret[0];
//            w = ret[1];
//            v = ret[2];
//            _print(a);
//            _print(_mult(_mult(u,_diag(w)), _trans(v)));
//        }

//
var _zeros = function(m, n) {
    var arr = [];
    for (var i = 0; i < m; ++i) {
        if (n === undefined) {
            arr.push(0.0);
        } else {
            var row = [];
            for (var j = 0; j < n; ++j) {
                row.push(0.0);
            }
            arr.push(row);
        }
    }
    return arr;
};

//
var _clone = function (a) {
    var m = a.length,
        n = a[0].length;
    var b = [];
    for (var i = 0; i < m; ++i) {
        var row = [];
        for (var j = 0; j < n; ++j) {
            row.push(a[i][j]);
        }
        b.push(row);
    }
    return b;
};

var _trans = function (a) {
    var m = a.length,
        n = a[0].length;
    var b = [];
    for (var i = 0; i < n; ++i) {
        var row = [];
        for (var j = 0; j < m; ++j) {
            row.push(a[j][i]);
        }
        b.push(row);
    }
    return b;
};

//
var _mult = function (a, b) {
    // Multiply two matrices
    // a must be two dimensional
    // b can be one or two dimensional
    var am = a.length,
        bm = b.length,
        an = a[0].length,
        bn;
    if (Array.isArray(b[0])) {
        bn = b[0].length;
    } else {
        bn = 1;
    }
    if (an !== bm) {
        // raise ValueError, 'matrixmultiply error: array sizes do not match.'
        return;
    }
    var cm = am,
        cn = bn;
    var c;
    if (bn === 1) {
        c = _zeros(cm);
    } else {
        c = _zeros(cm,cn);
    }
    for (var i = 0; i < cm; ++i) {
        for (var j = 0; j < cn; ++j) {
            for (var k = 0; k < an; ++k) {
                if (bn === 1) {
                    c[i] += a[i][k]*b[k];
                } else {
                    c[i][j] += a[i][k]*b[k][j];
                }
            }
        }
    }
    return c;
};

//
var _diag = function(arr) {
    var n = arr.length;
    var ret = _zeros(n,n);
    for (var i = 0; i < n; ++i) {
        ret[i][i] = arr[i];
    }
    return ret;
};

//
var _toStr = function(a, before, after) {
    var before = before || "",
        after  = after || "";
    return before + a.map(function(r){
            if (Array.isArray(r)) {
                return r.map(function(e){ return (e).toFixed(4); }).join(", ");
            } else {
                return (r).toFixed(4);
            }
        }).join("\n") + after;
};

//
var _print = function(a, before, after) {
    var str;
    if (Array.isArray(a)) {
        str = _toStr(a,before,after);
    } else {
        str = a;
    }
    console.log(str);
    if (_writeDoc === true && _document !== undefined) {
        _document += (str+"\n");
    }
};

//
var _pythag = function(a, b) {
    var absa = Math.abs(a),
        absb = Math.abs(b);
    if (absa > absb) {
        return absa*Math.sqrt(1.0+(absb/absa)*(absb/absa));
    } else {
        if (absb === 0.0) {
            return 0.0;
        }  else {
            return absb*Math.sqrt(1.0+(absa/absb)*(absa/absb));
        }
    }
};

var svd = function (a, options) {
    // a is m by n, and m >= n

    // Golub and Reinsch state that eps should not be smaller than the
    // machine precision, ie the smallest number
    // for which 1+e>1.  tol should be beta/e where beta is the smallest
    // positive number representable in the computer.
    var options = options || {};
    var eps = options.eps || Number.EPSILON,
        tol = options.tol || Number.MIN_VALUE/eps;
    if (1.0+eps<=1.0 || tol <= 0.0) {
        return null;
    }
    var itmax = options.itmax || 50;
    var u = _clone(a);
    var m = a.length,
        n = a[0].length;

    var e = _zeros(n),
        q = _zeros(n),
        v = _zeros(n,n);

    // Householder's reduction to bidiagonal form
    var g = 0.0,
        x = 0.0;

    for (var i = 0; i < n; ++i) {
        e[i] = g;
        var s = 0.0,
            l = i+1;
        for (var j = i; j < m; ++j) {
            s += u[j][i]*u[j][i];
        }
        if (s <= tol) {
            g = 0.0;
        } else {
            var f = u[i][i];
            if (f < 0.0) {
                g =  Math.sqrt(s);
            } else {
                g = -Math.sqrt(s);
            }
            var h = f*g-s;
            u[i][i] = f-g;
            for (var j = l; j < n; ++j) {
                s = 0.0;
                for (var k = i; k < m; ++k) {
                    s += u[k][i]*u[k][j];
                }
                f = s / h;
                for (var k = i; k < m; ++k) {
                    u[k][j] += f*u[k][i];
                }
            }
        }
        q[i] = g;
        s = 0.0;
        for (var j = l; j < n; ++j) {
            s += u[i][j]*u[i][j];
        }
        if (s <= tol) {
            g = 0.0;
        } else {
            f = u[i][i+1];
            if (f < 0.0) {
                g =  Math.sqrt(s)
            } else {
                g = -Math.sqrt(s);
            }
            h = f*g-s;
            u[i][i+1] = f-g;
            for (var j = l; j < n; ++j) {
                e[j] = u[i][j]/h;
            }
            s = 0.0;
            for (var k = l; k < n; ++k) {
                s += u[j][k]*u[i][k];
            }
            for (var k = l; k < n; ++k) {
                u[j][k] += s*e[k];
            }
        }
        var y = Math.abs(q[i])+Math.abs(e[i]);
        if (y > x) { x = y; }
    }

    // accumulation of right hand gtransformations
    for (var i = n-1; i >= 0; --i) {
        if (g != 0.0) {
            h = g*u[i][i+1]
            for (var j = l; j < n; ++j) {
                v[j][i] = u[i][j]/h;
            }
            for (var j = l; j < n; ++j) {
                s = 0.0;
                for (var k = l; k < n; ++k) {
                    s += (u[i][k]*v[k][j]);
                }
                for (var k = l; k < n; ++k) {
                    v[k][j] += s*v[k][i];
                }
            }
        }
        for (var j = l; j < n; ++j) {
            v[i][j] = 0.0;
            v[j][i] = 0.0;
        }
        v[i][i] = 1.0;
        g = e[i];
        l = i;
    }

    // accumulation of left hand transformations
    for (var i = n-1; i >= 0; --i) {
        l = i+1;
        g = q[i];
        for (var j = l; j < n; ++j) {
            u[i][j] = 0.0;
        }
        if (g != 0.0) {
            h = u[i][i]*g;
            for (var j = l; j < n; ++j) {
                s = 0.0;
                for (var k = l; k < m; ++k) {
                    s += u[k][i]*u[k][j];
                }
                f = s/h;
                for (var k = i; k < m; ++k) {
                    u[k][j] += f*u[k][i];
                }
            }
            for (var j = i; j < m; ++j) {
                u[j][i] /= g;
            }
        } else {
            for (var j = i; j < m; ++j) {
                u[j][i] = 0.0;
            }
        }
        u[i][i] += 1.0;
    }

    // diagonalization of the bidiagonal form
    eps *= x;
    for (var k = n-1; k >= 0; --k) {
        for (var iteration = 0; iteration < itmax; ++iteration) {
            var goto_test_f_convergence = true;
            // test f splitting
            for (var l = k; l >= 0; --l) {
                goto_test_f_convergence = false;
                if (Math.abs(e[l]) <= eps) {
                    // goto test f convergence
                    goto_test_f_convergence = true;
                    break; // break out of l loop
                }
                if (Math.abs(q[l-1]) <= eps) {
                    // goto cancellation
                    break; // break out of l loop
                }
            }
            if (!goto_test_f_convergence) {
                // cancellation of e[l] if l>0
                var c = 0.0,
                    s = 1.0,
                    l1 = l-1;
                for (var i = l; i <= k; ++i) {
                    f = s*e[i];
                    e[i] = c*e[i];
                    if (Math.abs(f) <= eps) {
                        // goto test f convergence
                        break;
                    }
                    g = q[i];
                    h = _pythag(f,g);
                    q[i] = h;
                    c =  g/h;
                    s = -f/h;
                    for (var j = 0; j < m; ++j) {
                        y = u[j][l1];
                        var z = u[j][i];
                        u[j][l1] = y*c+z*s;
                        u[j][i] = -y*s+z*c;
                    }
                }
            }
            // test f convergence
            z = q[k];
            if (l === k) {
                // convergence
                if (z < 0.0) {
                    // q[k] is made non-negative
                    q[k] = -z;
                    for (var j = 0; j < n; ++j) {
                        v[j][k] *= -1;
                    }
                }
                break; // break out of iteration loop and move on to next k value
            }
            if (iteration >= itmax-1) {
                // if __debug__: print 'Error: no convergence.'
                // should this move on the the next k or exit with error??
                // raise ValueError,'SVD Error: No convergence.'  # exit the program with error
                break; // break out of iteration loop and move on to next k
            }
            // shift from bottom 2x2 minor
            x = q[l];
            y = q[k-1];
            g = e[k-1];
            h = e[k];
            f = ((y-z)*(y+z)+(g-h)*(g+h))/(2.0*h*y);
            g = _pythag(f,1.0);
            if (f < 0) {
                f = ((x-z)*(x+z)+h*(y/(f-g)-h))/x;
            } else {
                f = ((x-z)*(x+z)+h*(y/(f+g)-h))/x;
            }
            // next QR transformation
            c = 1.0;
            s = 1.0;
            for (var i = l+1; i <= k; ++i) {
                g = e[i];
                y = q[i];
                h = s*g;
                g = c*g;
                z = _pythag(f,h);
                e[i-1] = z;
                c = f/z;
                s = h/z;
                f = x*c+g*s;
                g = -x*s+g*c;
                h = y*s;
                y = y*c;
                for (var j = 0; j < n; ++j) {
                    x = v[j][i-1];
                    z = v[j][i];
                    v[j][i-1] = x*c+z*s;
                    v[j][i] = -x*s+z*c;
                }
                z = _pythag(f,h);
                q[i-1] = z;
                c = f/z;
                s = h/z;
                f = c*g+s*y;
                x = -s*g+c*y;
                for (var j = 0; j < m; ++j) {
                    y = u[j][i-1];
                    z = u[j][i];
                    u[j][i-1] = y*c+z*s;
                    u[j][i] = -y*s+z*c;
                }
            }
            e[l] = 0.0;
            e[k] = f;
            q[k] = x;
            // goto test f splitting
        }
    }

    // satisfy: a = u*w*vt, with w = _diag(q), vt = _trans(v), notice that u is not square
    return [u,q,v];
};
