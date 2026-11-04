module

public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange

/-!
# The counit of `b^* ⊣ b_*` over the locus where `b` is an isomorphism

Let `b : X ⟶ Y` be quasi-compact and quasi-separated and `U ⊆ Y` an open over which `b` is an
isomorphism. If a quasi-coherent `𝒪_X`-module `L` is trivial over `b⁻¹(U)`, then the counit
`b^* b_* L ⟶ L` is invertible on the stalks at the points of `b⁻¹(U)`: by flat base change in
degree zero along the open immersion `U ⟶ Y` ([Stacks, Tag 02KH]) its restriction to `b⁻¹(U)`
is the counit of the isomorphism `b ∣_ U` at `L|_{b⁻¹(U)} ≅ 𝒪`, which is invertible.

## Main results

* `AlgebraicGeometry.DualizingDivisor.isIso_stalk_counit_of_isIso_morphismRestrict`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.DualizingDivisor

open VectorBundleCodimensionOne

/-- **The counit of `b^* ⊣ b_*` is invertible on stalks over the locus where `b` is an
isomorphism**, at a quasi-coherent module trivial over that locus. -/
theorem isIso_stalk_counit_of_isIso_morphismRestrict {X Y : Scheme.{u}} (b : X ⟶ Y)
    [QuasiCompact b] [QuasiSeparated b] (U : Y.Opens) [IsIso (b ∣_ U)] (L : X.Modules)
    [L.IsQuasicoherent]
    (eU : (Scheme.Modules.pullback (b ⁻¹ᵁ U).ι).obj L ≅ SheafOfModules.unit _)
    (x : X) (hx : x ∈ b ⁻¹ᵁ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((Scheme.Modules.pullbackPushforwardAdjunction b).counit.app L).val)) := by
  have H : IsPullback (b ⁻¹ᵁ U).ι (b ∣_ U) b U.ι := (isPullback_morphismRestrict b U).flip
  have hc : IsIso (b ∣_ U).toLRSHom.toHom.c := inferInstance
  have hu := isIso_unit_app_unit_of_isIso_c (b ∣_ U) hc
  have h1 := isIso_counit_app_of_iso_free (b ∣_ U) hu
    ((Scheme.Modules.pullback (b ⁻¹ᵁ U).ι).obj L) PUnit
    (eU ≪≫ (coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit _)).symm)
  have h2 := isIso_pullback_map_counit_of_isPullback H L h1
  exact isIso_stalk_of_isIso_pullback_map (b ⁻¹ᵁ U).ι _ h2 ⟨x, hx⟩

end AlgebraicGeometry.DualizingDivisor
