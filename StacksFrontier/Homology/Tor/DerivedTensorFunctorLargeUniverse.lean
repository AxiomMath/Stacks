module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

set_option maxRecDepth 4096

/-!
# The derived tensor product with a fixed object, above the ring universe

Let `R` be a commutative ring whose modules are allowed to inhabit a universe `max u v`
independent of the universe `u` of `R`. Tensoring with a K-flat complex inverts
quasi-isomorphisms, so the tensor-total functor attached to a K-flat resolution of any
representative of an object of the derived category descends through the localization. The
resulting endofunctor of the derived category is independent of the resolution chosen, commutes
with the shifts, and is exact.

## Main results

* `CochainComplex.DerivedTensor.derivedTensorProduct`: the derived tensor product with a fixed
  object, built from a K-flat resolution of any representative.
* `CochainComplex.DerivedTensor.derivedTensorProduct_commShift` and
  `CochainComplex.DerivedTensor.derivedTensorProduct_isTriangulated`: it commutes with the shifts
  and is an exact functor of triangulated categories.
* `CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution`: every K-flat
  resolution of every representative computes it, by a comparison uniquely determined by its
  pullback to the homotopy category.

## References

* [The Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

open CategoryTheory

universe u v w

namespace CochainComplex.DerivedTensor

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

section DerivedTensorFunctor

open CategoryTheory.MonoidalCategory

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
/-- The derived tensor product with `M`, computed by a K-flat resolution of a representative of
`M`. -/
@[stacks 064M, sga "4 XVII 4.1.7" "(i), modules over ring"]
public noncomputable def derivedTensorProduct
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R) :=
  let K := (CochainComplex.KFlat.exists_kFlat_resolution
    ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as).choose
  let hK := (CochainComplex.KFlat.exists_kFlat_resolution
    ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as).choose_spec.choose_spec.1
  Localization.lift (Tright K ⋙ DerivedCategory.Qh)
    (fun _ _ f hf ↦
      Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) _
        (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK f hf))
    DerivedCategory.Qh

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
/-- The derived tensor product commutes with the shift functors. -/
@[stacks 064M]
public noncomputable instance derivedTensorProduct_commShift
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedTensorProduct M).CommShift ℤ := by
  let K := (CochainComplex.KFlat.exists_kFlat_resolution
    ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as).choose
  let hK := (CochainComplex.KFlat.exists_kFlat_resolution
    ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as).choose_spec.choose_spec.1
  let h :
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).IsInvertedBy
        (Tright K ⋙ DerivedCategory.Qh) := fun _ _ f hf ↦
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) _
      (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK f hf)
  letI : (Tright K).CommShift ℤ := (TotalTensorComplex.tright_isTriangulated K).choose
  exact Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) ℤ
    (Tright K ⋙ DerivedCategory.Qh)
    (Localization.lift (Tright K ⋙ DerivedCategory.Qh) h DerivedCategory.Qh)

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
/-- The derived tensor product is an exact functor of triangulated categories. -/
@[stacks 064M]
public noncomputable instance derivedTensorProduct_isTriangulated
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedTensorProduct M).IsTriangulated := by
  let K := (CochainComplex.KFlat.exists_kFlat_resolution
    ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as).choose
  let hK := (CochainComplex.KFlat.exists_kFlat_resolution
    ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as).choose_spec.choose_spec.1
  let h :
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).IsInvertedBy
        (Tright K ⋙ DerivedCategory.Qh) := fun _ _ f hf ↦
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) _
      (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK f hf)
  let _ : (Tright K).CommShift ℤ := (TotalTensorComplex.tright_isTriangulated K).choose
  let _ : (Tright K).IsTriangulated := (TotalTensorComplex.tright_isTriangulated K).choose_spec
  let _ : (derivedTensorProduct M).CommShift ℤ := derivedTensorProduct_commShift M
  exact Functor.isTriangulated_of_localization DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    (Tright K ⋙ DerivedCategory.Qh)
    (Localization.lift (Tright K ⋙ DerivedCategory.Qh) h DerivedCategory.Qh)

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
/-- The natural transformation `Tright K ⟶ Tright K'` induced by a morphism `a : K ⟶ K'`. -/
public noncomputable def trightMap
    {K K' : CochainComplex (ModuleCat.{max u v} R) ℤ} (a : K ⟶ K') :
    Tright K ⟶ Tright K' where
  app X := (HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).map
    (((curriedTensor (ModuleCat.{max u v} R)).map₂CochainComplex.flip.map a).app X.as)
  naturality := by
    intro X Y f
    obtain ⟨f, rfl⟩ :=
      (HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).map_surjective f
    exact (HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).congr_map
      (((curriedTensor (ModuleCat.{max u v} R)).map₂CochainComplex.flip.map a).naturality f)

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
omit [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] in
private lemma trightMap_app
    {K K' : CochainComplex (ModuleCat.{max u v} R) ℤ} (a : K ⟶ K')
    (L : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (trightMap a).app
      ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj L) =
      (HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).map
        ((TleftCochain L).map a) := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
/-- The isomorphism in the derived category induced by a quasi-isomorphism of complexes. -/
private noncomputable def qhIsoOfQuasiIso
    {K L : CochainComplex (ModuleCat.{max u v} R) ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    (DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj L) :=
  Localization.isoOfHom DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).map f)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
private noncomputable def trightIsoOfQuasiIso
    {K K' : CochainComplex (ModuleCat.{max u v} R) ℤ} (a : K ⟶ K') [QuasiIso a]
    (hK : K.KFlat) (hK' : K'.KFlat) :
    Tright K ⋙ DerivedCategory.Qh ≅ Tright K' ⋙ DerivedCategory.Qh :=
  NatIso.ofComponents
    (fun X ↦ qhIsoOfQuasiIso ((TleftCochain X.as).map a) (quasiIso_tleftCochain_map a hK hK' X.as))
    (fun f ↦ by
      change DerivedCategory.Qh.map ((Tright K).map f) ≫
          DerivedCategory.Qh.map ((trightMap a).app _) =
        DerivedCategory.Qh.map ((trightMap a).app _) ≫
          DerivedCategory.Qh.map ((Tright K').map f)
      rw [← Functor.map_comp, ← Functor.map_comp, (trightMap a).naturality])

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
private lemma exists_kFlat_common_source
    (K K' : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (e : (DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj K')) :
    ∃ (A : CochainComplex (ModuleCat.{max u v} R) ℤ) (a : A ⟶ K) (b : A ⟶ K'),
      A.KFlat ∧ QuasiIso a ∧ QuasiIso b := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (DerivedCategory.Qh (C := ModuleCat.{max u v} R)) W e.hom
  have : IsIso (φ.map DerivedCategory.Qh (Localization.inverts DerivedCategory.Qh W)) := by
    rw [← hφ]
    infer_instance
  have : IsIso (DerivedCategory.Qh.map φ.s) :=
    Localization.inverts DerivedCategory.Qh W φ.s φ.hs
  have : IsIso (DerivedCategory.Qh.map φ.f) := by
    rw [← φ.map_s_comp_map DerivedCategory.Qh (Localization.inverts DerivedCategory.Qh W)]
    infer_instance
  have hf : W φ.f := (DerivedCategory.isIso_Qh_map_iff φ.f).1 inferInstance
  obtain ⟨s, hs⟩ := Q.map_surjective φ.s
  obtain ⟨g, hg⟩ := Q.map_surjective φ.f
  obtain ⟨A, r, hA, -, hr, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution φ.X'.as
  have key : ∀ {Y : CochainComplex (ModuleCat.{max u v} R) ℤ} (x : φ.X'.as ⟶ Y),
      W (Q.map x) → QuasiIso (r ≫ x) := fun x hx ↦ by
    rw [← HomologicalComplex.mem_quasiIso_iff,
      ← HomotopyCategory.quotient_map_mem_quasiIso_iff, Q.map_comp]
    exact W.comp_mem _ _ ((HomotopyCategory.quotient_map_mem_quasiIso_iff r).2 hr) hx
  refine ⟨A, r ≫ s, r ≫ g, hA, ?_, ?_⟩
  · exact key s (by rw [hs]; exact φ.hs)
  · exact key g (by rw [hg]; exact hf)

set_option synthInstance.maxHeartbeats 200000 in
-- formerly file-wide: instance search over `ModuleCat.{max u v} R` and its derived category
set_option maxHeartbeats 16000000 in
-- The comparison of the two resolutions is expensive to elaborate.
/-- A K-flat resolution of any representative of `M` computes the derived tensor product.
The comparison is a natural isomorphism, uniquely determined by its pullback to the homotopy
category. -/
@[stacks 064M]
public theorem derivedTensorProduct_iso_lift_of_kFlat_resolution
    (M : DerivedCategory (ModuleCat.{max u v} R))
    (P K : CochainComplex (ModuleCat.{max u v} R) ℤ) (f : K ⟶ P) [QuasiIso f]
    (hK : K.KFlat)
    (_eP : (DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
      ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj P) ≅ M) :
    let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
    let F := Tright K ⋙ DerivedCategory.Qh
    let hF : W.IsInvertedBy F := fun _ _ g hg ↦
      Localization.inverts DerivedCategory.Qh W _
        (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK g hg)
    let F' := Localization.lift F hF DerivedCategory.Qh
    Nonempty (DerivedCategory.Qh ⋙ derivedTensorProduct M ≅ F) ∧
      ∀ α : DerivedCategory.Qh ⋙ derivedTensorProduct M ≅ F,
        ∃! e : derivedTensorProduct M ≅ F',
          Functor.isoWhiskerLeft DerivedCategory.Qh e =
            α ≪≫ (Localization.fac F hF DerivedCategory.Qh).symm := by
  dsimp only
  let P₀ := ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).objPreimage M).as
  let K₀ := (CochainComplex.KFlat.exists_kFlat_resolution P₀).choose
  let f₀ := (CochainComplex.KFlat.exists_kFlat_resolution P₀).choose_spec.choose
  have hK₀ : K₀.KFlat :=
    (CochainComplex.KFlat.exists_kFlat_resolution P₀).choose_spec.choose_spec.1
  have hf₀ : QuasiIso f₀ :=
    (CochainComplex.KFlat.exists_kFlat_resolution P₀).choose_spec.choose_spec.2.2.1
  let Q := HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  let W := HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  have hinv : ∀ (L : CochainComplex (ModuleCat.{max u v} R) ℤ), L.KFlat →
      W.IsInvertedBy (Tright L ⋙ DerivedCategory.Qh) := fun L hL _ _ g hg ↦
    Localization.inverts DerivedCategory.Qh W _
      (CochainComplex.KFlat.kFlat_tright_preserves_quasiIso L hL g hg)
  let i₀ := qhIsoOfQuasiIso f₀ hf₀ ≪≫ DerivedCategory.Qh.objObjPreimageIso M
  let i := qhIsoOfQuasiIso f ‹_› ≪≫ _eP
  obtain ⟨A, a, b, hA, _, _⟩ := exists_kFlat_common_source K₀ K (i₀ ≪≫ i.symm)
  let β : Tright K₀ ⋙ DerivedCategory.Qh ≅ Tright K ⋙ DerivedCategory.Qh :=
    (trightIsoOfQuasiIso a hA hK₀).symm ≪≫ trightIsoOfQuasiIso b hA hK
  constructor
  · exact ⟨(Localization.fac (Tright K₀ ⋙ DerivedCategory.Qh)
      (hinv K₀ hK₀) DerivedCategory.Qh) ≪≫ β⟩
  · intro α
    let F := Tright K ⋙ DerivedCategory.Qh
    let hF := hinv K hK
    let F' := Localization.lift F hF DerivedCategory.Qh
    let e : derivedTensorProduct M ≅ F' :=
      Localization.liftNatIso DerivedCategory.Qh W
        (DerivedCategory.Qh ⋙ derivedTensorProduct M) F
        (derivedTensorProduct M) F' α
    have he : Functor.isoWhiskerLeft DerivedCategory.Qh e =
        α ≪≫ (Localization.fac F hF DerivedCategory.Qh).symm := by
      ext X
      simp [e, F, F']
      rfl
    refine ⟨e, he, fun e' he' ↦ Iso.ext <| Localization.natTrans_ext DerivedCategory.Qh W
      fun X ↦ (congr_app (congrArg Iso.hom he') X).trans (congr_app (congrArg Iso.hom he) X).symm⟩

end DerivedTensorFunctor

end CochainComplex.DerivedTensor

end
