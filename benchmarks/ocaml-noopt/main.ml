open Core
open Core_bench

let () =
  Command_unix.run (Bench.make_command [
    Bench.Test.create ~name:"demo0"
      (fun () -> ignore(Demo0.demo0 Tt));
    Bench.Test.create ~name:"demo1"
      (fun () -> ignore(Demo1.demo1 Tt));
    Bench.Test.create ~name:"demo2"
      (fun () -> ignore (Demo2.demo2 Tt));
    Bench.Test.create ~name:"list_sum"
      (fun () -> ignore (List_sum.list_sum Tt));
    Bench.Test.create ~name:"vs_easy"
      (fun () -> ignore ( Vs_easy.vs_easy Tt));
    Bench.Test.create ~name:"vs_hard"
      (fun () -> ignore ( Vs_hard.vs_hard Tt));
    Bench.Test.create ~name:"binom"
      (fun () -> ignore ( Binom.binom Tt));
    (* Bench.Test.create ~name:"color" *)
    (*   (fun () -> ignore (Color.color Tt)); *)
    Bench.Test.create ~name:"sha_fast"
      (fun () -> ignore ( Sha_fast.sha_fast Tt));
])
