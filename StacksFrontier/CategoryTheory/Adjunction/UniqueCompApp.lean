module

public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Components of the comparison of two composite left adjoints

Let `adjE : Ef ⊣ Ei` and `adjB : B ⊣ V` be adjunctions, and let `adjF : Fu ⊣ U` and
`adjS : Sf ⊣ Si` be two more, arranged so that the two composite left adjoints `Ef ⋙ B` and
`Fu ⋙ Sf` have the same target.  A natural isomorphism `δ : Si ⋙ U ≅ V ⋙ Ei` between the
composites of the right adjoints then makes both of them left adjoint to `V ⋙ Ei`, so
`CategoryTheory.Adjunction.leftAdjointUniq` compares them.

This file gives the components of that comparison explicitly, in both directions.

## Main results

* `CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_inv_app`: the inverse component
  of the comparison, as a composite of the two units and the two counits with `δ.inv`.
* `CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app`: the same for the
  forward component, with the roles of the two pairs of adjunctions exchanged.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₁' C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₁'] [Category* C₂]
  {Ef : C₀ ⥤ C₁'} {Ei : C₁' ⥤ C₀} {B : C₁' ⥤ C₂} {V : C₂ ⥤ C₁'}
  {Fu : C₀ ⥤ C₁} {U : C₁ ⥤ C₀} {Sf : C₁ ⥤ C₂} {Si : C₂ ⥤ C₁}

/-- **The inverse component of the comparison of two composite left adjoints.**

`Ef ⋙ B` is left adjoint to `V ⋙ Ei`, and `Fu ⋙ Sf` is left adjoint to `Si ⋙ U`, hence to
`V ⋙ Ei` through `δ`; the component at `K` of the inverse of the comparison given by uniqueness
of a left adjoint is the composite displayed on the right, built from the two units of the first
pair, `δ.inv`, and the two counits of the second pair. -/
theorem leftAdjointUniq_comp_ofNatIsoRight_inv_app
    (adjE : Ef ⊣ Ei) (adjB : B ⊣ V) (adjF : Fu ⊣ U) (adjS : Sf ⊣ Si)
    (δ : Si ⋙ U ≅ V ⋙ Ei) (K : C₀) :
    ((adjE.comp adjB).leftAdjointUniq ((adjF.comp adjS).ofNatIsoRight δ)).inv.app K =
      Sf.map (Fu.map (adjE.unit.app K ≫ Ei.map (adjB.unit.app (Ef.obj K)))) ≫
        Sf.map (Fu.map (δ.inv.app (B.obj (Ef.obj K)))) ≫
          Sf.map (adjF.counit.app (Si.obj (B.obj (Ef.obj K)))) ≫
            adjS.counit.app (B.obj (Ef.obj K)) := by
  rw [leftAdjointUniq_inv_app, leftAdjointUniq_ofNatIsoRight_comp,
    leftAdjointCompIso_hom_app, comp_unit_app]
  rfl

/-- **The forward component of the comparison of two composite left adjoints.**

With `Ef ⋙ B` and `Fu ⋙ Sf` left adjoint to `V ⋙ Ei` as in
`CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_inv_app`, the component at `K` of
the comparison given by uniqueness of a left adjoint is the composite displayed on the right,
built from the two units of the *second* pair of adjunctions, `δ.hom`, and the two counits of the
*first* pair. -/
theorem leftAdjointUniq_comp_ofNatIsoRight_hom_app
    (adjE : Ef ⊣ Ei) (adjB : B ⊣ V) (adjF : Fu ⊣ U) (adjS : Sf ⊣ Si)
    (δ : Si ⋙ U ≅ V ⋙ Ei) (K : C₀) :
    ((adjE.comp adjB).leftAdjointUniq ((adjF.comp adjS).ofNatIsoRight δ)).hom.app K =
      B.map (Ef.map (adjF.unit.app K)) ≫
        B.map (Ef.map (U.map (adjS.unit.app (Fu.obj K)))) ≫
          B.map (Ef.map (δ.hom.app (Sf.obj (Fu.obj K)))) ≫
            B.map (adjE.counit.app (V.obj (Sf.obj (Fu.obj K)))) ≫
              adjB.counit.app (Sf.obj (Fu.obj K)) := by
  rw [← leftAdjointUniq_inv_app, leftAdjointUniq_ofNatIsoRight_comp,
    leftAdjointCompIso_inv_app, comp_counit_app]
  rfl

end CategoryTheory.Adjunction

end
