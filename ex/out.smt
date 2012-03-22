(benchmark VERIMAG
:category { random }
:status unknown
:source { VERIMAG, Synchrone } 

:extrapreds ((entry))
:extrapreds ((if.then))
:extrapreds ((do.end))
:extrapreds ((if.then14))
:extrapreds ((do.end16))

:extrafuns ((x Int))
:extrafuns ((y Int))

:extrapreds ((x_0))
:extrapreds ((x_1))
:extrapreds ((x_2))
:extrapreds ((x_3))
:extrapreds ((x_4))
:extrapreds ((x_5))
:extrapreds ((x_6))
:extrafuns ((x_7 Int))
:extrafuns ((x_8 Int))
:extrapreds ((x_9))

:extrapreds ((stop_0))
:extrapreds ((warn_0))


:formula
(and
(= entry (or  (true)))
(or (not entry)
(and
(= x_0 (> x 4294967295))
(= x_1 (> y 4294967295))
(= x_2 (and x_0 x_1))
(= x_3 (< x 4))
(= x_4 (and x_2 x_3))
(= x_5 (< y 5))
(= x_6 (and x_4 x_5))
(ite x_6 do.end if.then)
))

(= if.then (or  ((and entry (not x_6)))))
(or (not if.then)
(and
(= stop_0 true)
(do.end)))

(= do.end (or  ((and entry x_6)) (if.then)))
(or (not do.end)
(and
(= x_7 (* y x))
(= x_8 (+ x_7 2))
(= x_9 (< x_8 100))
(ite x_9 do.end16 if.then14)
))

(= if.then14 (or  ((and do.end (not x_9)))))
(or (not if.then14)
(and
(= warn_0 true)
))

(= do.end16 (or  ((and do.end x_9))))
(or (not do.end16)
true)

(or (and (not stop_0) warn_0))))
