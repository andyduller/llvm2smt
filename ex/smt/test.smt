(benchmark a
:category { random }
:status unknown
:source {
Benchmarks from Miquel Bofill <mbofill@ima.udg.edu>
coming from a wastewater treatment scheduling problem
}
:extrafuns ((x1 Int))
:extrafuns ((x2 Int))
:extrafuns ((x3 Int))
:formula
(and
(= x1 50)
(= x2 60)
(= x3 (- x2 x1))
(> x3 20)
)
)
