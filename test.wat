(module
    (func (export "main") (result i32)
      (local i32 i32 i32)
        (local.set 1 (i32.const 100000))
        (loop 
          (local.set 2 (i32.add (local.get 2) (local.get 1)))
          (local.set 1 (i32.sub (local.get 1) (i32.const 1)))
          (i32.gt_u (local.get 1) (i32.const 0))
          (br_if 0)
        )
        (local.get 2)
    )
)