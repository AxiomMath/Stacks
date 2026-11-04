module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.PurelyInseparable.Tower
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting
public import StacksFrontier.RingTheory.Length.RingEquiv
public import StacksFrontier.RingTheory.Length.SemiLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical weighting of a flat locally quasi-finite morphism

For a flat, locally quasi-finite morphism locally of finite presentation the length of the local
fibre ring at a point times the inseparable degree of its residue-field extension is a positive
weighting.

## Main definitions

* `AlgebraicGeometry.flatQuasiFiniteWeight` is that length–inseparable-degree function.

## Main results

* `AlgebraicGeometry.flatQuasiFiniteWeight_pos`: the function is strictly positive.
* `AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting`: the function is a weighting.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_flatQuasiFiniteWeight`: for a finite flat
  morphism the separable-degree weighted fibre sum of the function is the rank of the morphism.
* `AlgebraicGeometry.finInsepDegree_residueField_eq_of_etale_square`: the inseparable degree of
  the residue-field extension at a point is unchanged along an étale base change square.

## Implementation notes

The local fibre ring at `x` is the quotient of the stalk at `x` by the extension of the maximal
ideal of the stalk at `f x`; its length is converted to a natural number, which is legitimate
because the hypotheses make that length finite. The residue-field extension is the one induced
by the morphism.

Positivity is the positivity of both factors. That the function is a weighting is checked on a
finite open piece of an étale base change: there the weighted fibre sum is the rank of the global
sections of the piece as a module over the base, by additivity of length over the points of the
fibre and multiplicativity of the residue degree, and that rank is locally constant because a
finite flat morphism locally of finite presentation is finite locally free. Both factors of the
weight are unchanged by an étale base change, which is what makes the comparison possible.

## References

* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The residue field of the scheme-theoretic fibre at `f.asFiber x` is isomorphic, as an
algebra over the residue field of `f x`, to the residue field of `X` at `x`. -/
private noncomputable def fiberResidueFieldAlgEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    let : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    let : Algebra (Y.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (Y.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    ((f.fiber (f x)).residueField (f.asFiber x) : Type u) ≃ₐ[Y.residueField (f x)]
      (X.residueField x : Type u) := by
  let k := Y.residueField (f x)
  let F := f.fiber (f x)
  let _ : Algebra k (F.residueField (f.asFiber x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f.fiberToSpecResidueField (f x)).appTop ≫
      F.Γevaluation (f.asFiber x)).hom.toAlgebra
  let _ : Algebra k (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  refine AlgEquiv.symm (AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (f.fiberResidueFieldHom x).hom
      (f.bijective_fiberResidueFieldHom x)) ?_)
  intro a
  have h := congrArg CommRingCat.Hom.hom (f.fiberResidueFieldHom_algebraMap x)
  exact (DFunLike.congr_fun h a).symm

private lemma length_tensor_eq_of_map_maximalIdeal_eq
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [AddCommGroup M] [Module R M]
    (h : (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S) :
    Module.length S (S ⊗[R] M) = Module.length R M := by
  have hlen : Module.length S (S ⧸ IsLocalRing.maximalIdeal S) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
    exact ⟨IsLocalRing.maximalIdeal S, IsLocalRing.maximalIdeal.isMaximal S,
      ⟨LinearEquiv.refl _ _⟩⟩
  rw [IsLocalRing.length_baseChange, h, hlen, mul_one]

private lemma length_quotient_baseChange
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B] [IsLocalHom (algebraMap A B)]
    (hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B) (I : Ideal A) :
    Module.length B (B ⧸ Ideal.map (algebraMap A B) I) =
      Module.length A (A ⧸ I) := by
  have he := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq
  rw [show Module.length B (B ⧸ Ideal.map (algebraMap A B) I) =
    Module.length B (B ⊗[A] (A ⧸ I)) by simpa using he]
  exact length_tensor_eq_of_map_maximalIdeal_eq hmax

private lemma finInsepDegree_eq_of_separable_square
    {K K' L L' : Type*} [Field K] [Field K'] [Field L] [Field L']
    [Algebra K K'] [Algebra K L] [Algebra K L'] [Algebra K' L'] [Algebra L L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K' L']
    [Algebra.IsSeparable K K'] [Algebra.IsSeparable L L'] :
    Field.finInsepDegree K L = Field.finInsepDegree K' L' := by
  have h₁ := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K L L'
  have h₂ := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic K K' L'
  rw [Algebra.IsSeparable.finInsepDegree_eq K K', one_mul] at h₂
  rw [Algebra.IsSeparable.finInsepDegree_eq L L', mul_one] at h₁
  exact h₁.trans h₂.symm

private noncomputable def fiberGlobalSectionsMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    Y.residueField y →+* Γ(f.fiber y, ⊤) :=
  (((Scheme.ΓSpecIso (.of (Y.residueField y))).inv ≫
    (f.fiberToSpecResidueField y).appTop).hom)

private lemma fiberGlobalSectionsMap_finite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y) :
    (fiberGlobalSectionsMap f y).Finite := by
  let α := f.fiberToSpecResidueField y
  have : IsFinite α := by
    dsimp [α, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  have hα := α.finite_appTop
  have hΓ : ((Scheme.ΓSpecIso (.of (Y.residueField y))).inv.hom).Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of (Y.residueField y))).inv).surjective
  show (α.appTop.hom.comp _).Finite
  exact RingHom.Finite.comp hα hΓ

/-- The global sections of the fibre form a finite module over the residue field. -/
private lemma fiberGlobalSectionsMap_moduleFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y) :
    letI := (fiberGlobalSectionsMap f y).toAlgebra
    Module.Finite (Y.residueField y) Γ(f.fiber y, ⊤) := by
  let := (fiberGlobalSectionsMap f y).toAlgebra
  exact RingHom.finite_algebraMap.mp (fiberGlobalSectionsMap_finite f y)

private lemma fiberGlobalSectionsMap_flat {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [IsFinite f] (y : Y) :
    (fiberGlobalSectionsMap f y).Flat := by
  let α := f.fiberToSpecResidueField y
  have : Flat α := by
    dsimp [α, Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  have hα := α.flat_appTop
  have hΓ : ((Scheme.ΓSpecIso (.of (Y.residueField y))).inv.hom).Flat :=
    RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Y.residueField y))).inv)
  show (α.appTop.hom.comp _).Flat
  exact RingHom.Flat.comp hΓ hα

private lemma fiber_isoSpec_comp_SpecMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y) :
    let F := f.fiber y
    F.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (fiberGlobalSectionsMap f y)) =
      f.fiberToSpecResidueField y := by
  let F := f.fiber y
  let α := f.fiberToSpecResidueField y
  show F.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (fiberGlobalSectionsMap f y)) = α
  dsimp [fiberGlobalSectionsMap]
  rw [Spec.map_comp]
  have hn := Scheme.isoSpec_hom_naturality α
  show (f.fiber y).isoSpec.hom ≫ Spec.map α.appTop ≫
    Spec.map (Scheme.ΓSpecIso (.of (Y.residueField y))).inv = α
  calc
    _ = (α ≫ (Spec (Y.residueField y)).isoSpec.hom) ≫
        Spec.map (Scheme.ΓSpecIso (.of (Y.residueField y))).inv := by
      rw [← Category.assoc, hn]
    _ = α := by
      have ht : (Spec (Y.residueField y)).isoSpec.hom ≫
          Spec.map (Scheme.ΓSpecIso (.of (Y.residueField y))).inv = 𝟙 _ := by
        rw [← Scheme.isoSpec_Spec_inv]
        exact (Spec (Y.residueField y)).isoSpec.hom_inv_id
      rw [Category.assoc, ht, Category.comp_id]

private noncomputable def residueFieldAlgEquivOfIsoOverSpec
    {K : Type u} [Field K] {Z W : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (q : W ⟶ Spec (.of K)) (e : Z ≅ W)
    (h : e.hom ≫ q = p) (z : Z) :
    let : Algebra K (Z.residueField z) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    let : Algebra K (W.residueField (e.hom z)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ W.Γevaluation (e.hom z)).hom.toAlgebra
    (W.residueField (e.hom z) : Type u) ≃ₐ[K] (Z.residueField z : Type u) := by
  let : Algebra K (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  let : Algebra K (W.residueField (e.hom z)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ W.Γevaluation (e.hom z)).hom.toAlgebra
  let r : (W.residueField (e.hom z) : Type u) ≃+* (Z.residueField z : Type u) :=
    (asIso (e.hom.residueFieldMap z)).commRingCatIsoToRingEquiv
  have hsource : CommRingCat.ofHom (algebraMap K (Z.residueField z)) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z) := rfl
  have htarget : CommRingCat.ofHom (algebraMap K (W.residueField (e.hom z))) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ W.Γevaluation (e.hom z)) := rfl
  have hmap : (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫
      W.Γevaluation (e.hom z) ≫ e.hom.residueFieldMap z =
      (Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z := by
    calc
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫
          (e.hom.appTop ≫ Z.Γevaluation z) := by rw [Scheme.Γevaluation_naturality]
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z := by
        have happ := congrArg (fun m : Z ⟶ Spec (.of K) => m.appTop) h
        have happ' : q.appTop ≫ e.hom.appTop = p.appTop := by
          simpa only [Scheme.Hom.comp_appTop] using happ
        simpa only [Category.assoc] using
          congrArg (fun a => (Scheme.ΓSpecIso (.of K)).inv ≫ a ≫ Z.Γevaluation z) happ'
  have hr : CommRingCat.ofHom (r.toRingHom.comp
      (algebraMap K (W.residueField (e.hom z)))) =
      CommRingCat.ofHom (algebraMap K (Z.residueField z)) := by
    rw [CommRingCat.ofHom_comp, htarget, hsource]
    change _ ≫ e.hom.residueFieldMap z = _
    exact hmap
  exact AlgEquiv.ofRingEquiv (f := r) (by
    intro a
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) a)

private noncomputable def specResidueFieldAlgEquiv
    {B : Type u} [CommRing B] (r : PrimeSpectrum B) :
    let : Algebra B ((Spec (.of B)).residueField r) :=
      ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation r).hom.toAlgebra
    let : Algebra B r.asIdeal.ResidueField := (algebraMap B r.asIdeal.ResidueField).toAlgebra
    ((Spec (.of B)).residueField r : Type u) ≃ₐ[B] r.asIdeal.ResidueField := by
  let : Algebra B ((Spec (.of B)).residueField r) :=
    ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation r).hom.toAlgebra
  let : Algebra B r.asIdeal.ResidueField := (algebraMap B r.asIdeal.ResidueField).toAlgebra
  let i := Scheme.Spec.residueFieldIso (.of B) r
  let e := i.commRingCatIsoToRingEquiv
  apply AlgEquiv.ofRingEquiv (f := e)
  intro b
  have hsource : i.inv (algebraMap B r.asIdeal.ResidueField b) =
      ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation r) b := by
    have hh := congrArg (fun m => m b)
      (Scheme.Spec.algebraMap_residueFieldIso_inv (.of B) r)
    convert hh using 1 <;> rfl
  calc
    e (algebraMap B ((Spec (.of B)).residueField r) b) =
        e (i.inv (algebraMap B r.asIdeal.ResidueField b)) := by
          congr 1
          exact hsource.symm
    _ = algebraMap B r.asIdeal.ResidueField b := by
      change i.hom (i.inv _) = _
      simp

private lemma field_algebra_rank_sum
    {k B : Type*} [Field k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [Module.Flat k B] [IsArtinianRing B]
    [Algebra.QuasiFinite k B] [Fintype ((⊥ : Ideal k).primesOver B)] :
    ∑ q : (⊥ : Ideal k).primesOver B, q.1.ramificationIdx k * q.1.inertiaDeg k =
      Module.finrank k B := by
  rw [Ideal.sum_ramification_inertia_eq_finrank_fiber]
  exact Ideal.finrank_fiber_eq_finrank (R := k) (M := B) (p := ⊥)
@[instance_reducible] private noncomputable def fiberPrimeResidueFieldAlgebra
    {k B : Type*} [Field k] [CommRing B] [Algebra k B]
    (q : (⊥ : Ideal k).primesOver B) : Algebra k q.1.ResidueField := by
  let p : Ideal k := ⊥
  let : p.IsMaximal := Ideal.bot_isMaximal
  let hq : q.1.LiesOver p := Ideal.primesOver.liesOver p q
  let epk : p.ResidueField ≃+* k := p.algEquivResidueFieldOfField.toRingEquiv.symm
  let ψ := Ideal.ResidueField.map p q.1 (algebraMap k B) hq.over
  exact (ψ.comp epk.symm.toRingHom).toAlgebra

private theorem fiberPrimeResidueField_isScalarTower
    {k B : Type*} [Field k] [CommRing B] [Algebra k B]
    (q : (⊥ : Ideal k).primesOver B) :
    let : Algebra B q.1.ResidueField := (algebraMap B q.1.ResidueField).toAlgebra
    let : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q
    IsScalarTower k B q.1.ResidueField := by
  let p : Ideal k := ⊥
  let : p.IsMaximal := Ideal.bot_isMaximal
  let hq : q.1.LiesOver p := Ideal.primesOver.liesOver p q
  let epk : p.ResidueField ≃+* k := p.algEquivResidueFieldOfField.toRingEquiv.symm
  let ψ := Ideal.ResidueField.map p q.1 (algebraMap k B) hq.over
  let : Algebra B q.1.ResidueField := (algebraMap B q.1.ResidueField).toAlgebra
  let : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q
  apply IsScalarTower.of_algebraMap_eq
  intro a
  have he : epk.symm a = algebraMap k p.ResidueField a := by simp [epk]
  calc
    algebraMap k q.1.ResidueField a = ψ (epk.symm a) := rfl
    _ = ψ (algebraMap k p.ResidueField a) := by rw [he]
    _ = algebraMap B q.1.ResidueField (algebraMap k B a) :=
      Ideal.ResidueField.map_algebraMap p q.1 (algebraMap k B) hq.over a

private lemma weightedFiberSum_eq_fiber_sum
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (y : Y) [Finite (f.fiber y)] :
    separableDegreeWeightedFiberSum f w y =
      ∑ᶠ z : f.fiber y,
        let _i := ((Scheme.ΓSpecIso (.of (Y.residueField y))).inv ≫
          (f.fiberToSpecResidueField y).appTop ≫
          (f.fiber y).Γevaluation z).hom.toAlgebra
        w (f.fiberι y z) *
          (Field.finSepDegree (Y.residueField y) ((f.fiber y).residueField z) : ℤ) := by
  classical
  let p : X → Prop := fun x ↦ x ∈ f ⁻¹' {y}
  let s : Set X := f ⁻¹' {y}
  have hs : s.Finite := Set.finite_coe_iff.mp
    ((f.fiberHomeo y).finite_iff.mp (inferInstance : Finite (f.fiber y)))
  let : Fintype (f.fiber y) := Fintype.ofFinite _
  let : Finite {x : X // p x} := by
    show Finite (↑s)
    exact hs
  let : Fintype {x : X // p x} := Fintype.ofFinite _
  let e : {x : X // p x} ≃ f.fiber y := (f.fiberHomeo y).toEquiv.symm
  let g : f.fiber y → ℤ := fun z ↦
    let _i := ((Scheme.ΓSpecIso (.of (Y.residueField y))).inv ≫
      (f.fiberToSpecResidueField y).appTop ≫
      (f.fiber y).Γevaluation z).hom.toAlgebra
    w (f.fiberι y z) *
      (Field.finSepDegree (Y.residueField y) ((f.fiber y).residueField z) : ℤ)
  let F : X → ℤ := fun x ↦ if hx : p x then
    let _i := (f.residueFieldMap x).hom.toAlgebra
    w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)
    else 0
  have hsupport : Function.support F ⊆ hs.toFinset := by
    intro x hx
    have hFx : F x ≠ 0 := hx
    by_contra hn
    have hnot : ¬ p x := fun hp ↦ hn (hs.mem_toFinset.mpr hp)
    simp [F, hnot] at hFx
  have hsum := finsum_eq_sum_of_support_subset F hsupport
  have hsub : (∑ x ∈ hs.toFinset, F x) =
      ∑ x : {x : X // p x}, F x.1 := by
    apply Finset.sum_subtype hs.toFinset
    intro x
    rw [hs.mem_toFinset]
  have hpoint (x : {x : X // p x}) : F x.1 = g (e x) := by
    rcases x with ⟨x, hx⟩
    change f x ∈ ({y} : Set Y) at hx
    simp only [Set.mem_singleton_iff] at hx
    cases hx
    have hι : f.fiberι (f x) ((f.fiberHomeo (f x)).symm ⟨x, rfl⟩) = x := by
      have hh := congrArg Subtype.val
        ((f.fiberHomeo (f x)).apply_symm_apply ⟨x, rfl⟩)
      simpa only [Scheme.Hom.fiberHomeo_apply] using hh
    let : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    have he : e ⟨x, hx⟩ = f.asFiber x := by rfl
    let : Algebra (Y.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (.of (Y.residueField (f x)))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    have hdeg := Field.finSepDegree_eq_of_equiv _ _ _ (fiberResidueFieldAlgEquiv f x)
    have hp : p x := by simp [p]
    simp only [F, dite_eq_left hp]
    rw [he]
    dsimp [g]
    rw [Scheme.Hom.fiberι_asFiber, ← hdeg]
  have htransport : (∑ᶠ x : {x : X // p x}, F x.1) = ∑ᶠ z : f.fiber y, g z := by
    apply finsum_eq_of_bijective e e.bijective
    exact hpoint
  have hsub_finsum : (∑ x : {x : X // p x}, F x.1) =
      ∑ᶠ x : {x : X // p x}, F x.1 := by rw [finsum_eq_sum_of_fintype]
  have hfiber_finsum : (∑ z : f.fiber y, g z) = ∑ᶠ z : f.fiber y, g z := by
    rw [finsum_eq_sum_of_fintype]
  have htransport' : (∑ x : {x : X // p x}, F x.1) = ∑ z : f.fiber y, g z := by
    calc
      _ = ∑ᶠ x : {x : X // p x}, F x.1 := hsub_finsum
      _ = ∑ᶠ z : f.fiber y, g z := htransport
      _ = _ := hfiber_finsum.symm
  unfold separableDegreeWeightedFiberSum
  calc
    (∑ᶠ x : X, if f x = y then
        let _i := (f.residueFieldMap x).hom.toAlgebra
        w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)
      else 0) = ∑ᶠ x : X, F x := by
        apply finsum_congr
        intro x
        by_cases hx : p x
        · simp [F, p]
        · simp [F, p]
    _ = ∑ x ∈ hs.toFinset, F x := hsum
    _ = ∑ z : f.fiber y, g z := hsub.trans htransport'
    _ = ∑ᶠ z : f.fiber y, g z := hfiber_finsum

private alias length_ringEquiv_self := Module.length_eq_of_ringEquiv

lemma localFiberLength_eq_fiberStalkLength {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) =
      Module.length ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  let Q := (X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
  rw [Module.length_eq_of_surjective (S := X.presheaf.stalk x)
    (Ideal.Quotient.mk_surjective (I := Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))))]
  exact length_ringEquiv_self (quotientStalkEquivFiberStalk f x)

/-- The point of `Spec Γ(fibre)` corresponding to a point of the fibre lies over the zero
ideal of the residue field. -/
private lemma under_isoSpec_eq_bot {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y) (z : f.fiber y) :
    letI := (fiberGlobalSectionsMap f y).toAlgebra
    Ideal.under (Y.residueField y) ((f.fiber y).isoSpec.hom z).asIdeal = ⊥ :=
  (Ideal.eq_bot_or_top _).resolve_right
    (Ideal.comap_ne_top _ ((f.fiber y).isoSpec.hom z).2.ne_top)

private noncomputable def fiberPrimeOver {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y) (z : f.fiber y) :
    (let k := Y.residueField y
     let B := Γ(f.fiber y, ⊤)
     let : Algebra k B := (fiberGlobalSectionsMap f y).toAlgebra
     (⊥ : Ideal k).primesOver B) := by
  let k := Y.residueField y
  let B := Γ(f.fiber y, ⊤)
  let : Algebra k B := (fiberGlobalSectionsMap f y).toAlgebra
  let r : PrimeSpectrum B := (f.fiber y).isoSpec.hom z
  have hbot : Ideal.under k r.asIdeal = ⊥ := under_isoSpec_eq_bot f y z
  let : r.asIdeal.LiesOver (⊥ : Ideal k) := Ideal.LiesOver.mk hbot.symm
  exact Ideal.primesOver.mk (⊥ : Ideal k) r.asIdeal

private noncomputable def fiberPrimeResidueFieldAlgEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y) (z : f.fiber y) :
    let k := Y.residueField y
    let F := f.fiber y
    let B := Γ(F, ⊤)
    let : Algebra k B := (fiberGlobalSectionsMap f y).toAlgebra
    let : Module.Finite k B := fiberGlobalSectionsMap_moduleFinite f y
    let : Algebra k (F.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f.fiberToSpecResidueField y).appTop ≫
        F.Γevaluation z).hom.toAlgebra
    let q := fiberPrimeOver f y z
    let : Algebra B q.1.ResidueField := (algebraMap B q.1.ResidueField).toAlgebra
    let : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q
    q.1.ResidueField ≃ₐ[k] F.residueField z := by
  let k := Y.residueField y
  let F := f.fiber y
  let B := Γ(F, ⊤)
  let : Algebra k B := (fiberGlobalSectionsMap f y).toAlgebra
  let : Module.Finite k B := fiberGlobalSectionsMap_moduleFinite f y
  let : Algebra k (F.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f.fiberToSpecResidueField y).appTop ≫
      F.Γevaluation z).hom.toAlgebra
  let q := fiberPrimeOver f y z
  let : Algebra B q.1.ResidueField := (algebraMap B q.1.ResidueField).toAlgebra
  let : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q
  let : IsScalarTower k B q.1.ResidueField := fiberPrimeResidueField_isScalarTower q
  let r : PrimeSpectrum B := F.isoSpec.hom z
  let : r.asIdeal.IsPrime := r.2
  let : q.1.IsPrime := q.2.1
  let : Algebra B ((Spec (.of B)).residueField r) :=
    ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation r).hom.toAlgebra
  let : Algebra B r.asIdeal.ResidueField := (algebraMap B r.asIdeal.ResidueField).toAlgebra
  let β : Spec (.of B) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (fiberGlobalSectionsMap f y))
  let : Algebra k ((Spec (.of B)).residueField r) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ β.appTop ≫
      (Spec (.of B)).Γevaluation r).hom.toAlgebra
  let : IsScalarTower k B ((Spec (.of B)).residueField r) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    have hbase : (Scheme.ΓSpecIso (.of k)).inv ≫ β.appTop =
        CommRingCat.ofHom (fiberGlobalSectionsMap f y) ≫
          (Scheme.ΓSpecIso (.of B)).inv := by
      rw [← Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (fiberGlobalSectionsMap f y))]
    have hcat : ((Scheme.ΓSpecIso (.of k)).inv ≫ β.appTop) ≫
        (Spec (.of B)).Γevaluation r =
      CommRingCat.ofHom (fiberGlobalSectionsMap f y) ≫
        ((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation r) := by
      calc
        _ = (CommRingCat.ofHom (fiberGlobalSectionsMap f y) ≫
            (Scheme.ΓSpecIso (.of B)).inv) ≫ (Spec (.of B)).Γevaluation r := by
              rw [hbase]
        _ = _ := by rw [Category.assoc]
    have hcat_apply := congrArg (fun m => m.hom a) hcat
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ β.appTop ≫
      (Spec (.of B)).Γevaluation r).hom) a =
      (((Scheme.ΓSpecIso (.of B)).inv ≫ (Spec (.of B)).Γevaluation r).hom)
        ((fiberGlobalSectionsMap f y) a)
    exact hcat_apply
  let e₁ : (Spec (.of B)).residueField r ≃ₐ[k] F.residueField z :=
    residueFieldAlgEquivOfIsoOverSpec (f.fiberToSpecResidueField y) β F.isoSpec
      (fiber_isoSpec_comp_SpecMap f y) z
  let e₂ : (Spec (.of B)).residueField r ≃ₐ[B] r.asIdeal.ResidueField :=
    specResidueFieldAlgEquiv r
  let e₂' : (Spec (.of B)).residueField r ≃ₐ[B] q.1.ResidueField := e₂
  let : IsScalarTower k B q.1.ResidueField := by
    exact fiberPrimeResidueField_isScalarTower q
  exact e₂'.symm.restrictScalars k |>.trans e₁

private lemma fiberStalkLength_eq_ramificationIdx {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [IsFinite f] (y : Y) (z : f.fiber y) :
    (let k := Y.residueField y
     let B := Γ(f.fiber y, ⊤)
     let : Algebra k B := (fiberGlobalSectionsMap f y).toAlgebra
     Module.length ((f.fiber y).presheaf.stalk z)
       ((f.fiber y).presheaf.stalk z) = (fiberPrimeOver f y z).1.ramificationIdx k) := by
  let F := f.fiber y
  let k := Y.residueField y
  let B := Γ(F, ⊤)
  let : Algebra k B := (fiberGlobalSectionsMap f y).toAlgebra
  let : Module.Finite k B := fiberGlobalSectionsMap_moduleFinite f y
  have : IsArtinianRing B := inferInstance
  let r : PrimeSpectrum B := F.isoSpec.hom z
  have hbot : Ideal.under k r.asIdeal = ⊥ := under_isoSpec_eq_bot f y z
  let : r.asIdeal.LiesOver (⊥ : Ideal k) := Ideal.LiesOver.mk hbot.symm
  have : IsIso (F.isoSpec.hom.stalkMap z) := inferInstance
  let e₁ : F.presheaf.stalk z ≃+* (Spec (.of B)).presheaf.stalk r :=
    (asIso (F.isoSpec.hom.stalkMap z)).commRingCatIsoToRingEquiv.symm
  let e₂ : (Spec (.of B)).presheaf.stalk r ≃+* Localization.AtPrime r.asIdeal :=
    (Spec.stalkIso (.of B) r).commRingCatIsoToRingEquiv
  have : IsArtinianRing (Localization.AtPrime r.asIdeal) :=
    IsArtinianRing.localization_artinian r.asIdeal.primeCompl _
  show Module.length (F.presheaf.stalk z) (F.presheaf.stalk z) =
    r.asIdeal.ramificationIdx k
  rw [length_ringEquiv_self (e₁.trans e₂)]
  rw [Ideal.ramificationIdx_eq (p := (⊥ : Ideal k)) r.asIdeal, Ideal.map_bot]
  rw [(AlgEquiv.quotientBot (Localization.AtPrime r.asIdeal)
    (Localization.AtPrime r.asIdeal)).toLinearEquiv.length_eq]
  exact (ENat.natCast_toNat (Module.length_ne_top :
    Module.length (Localization.AtPrime r.asIdeal) (Localization.AtPrime r.asIdeal) ≠ ⊤)).symm

private lemma fiberι_cast_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) {y : Y} (hxy : f x = y) :
    f.fiberι y (hxy ▸ f.asFiber x) = x := by
  cases hxy
  exact f.fiberι_asFiber x

private lemma fiber_point_eq_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (z : f.fiber y) :
    let x := f.fiberι y z
    ∃ hxy : f x = y, z = hxy ▸ f.asFiber x := by
  let x := f.fiberι y z
  have hxy : f x = y := by
    have hh := congrArg (fun a : f.fiber y ⟶ Y => a z) (f.fiber_fac y)
    show f x = y
    simpa [x] using hh
  refine ⟨hxy, ?_⟩
  apply (f.fiberHomeo y).injective
  apply Subtype.ext
  show f.fiberι y z = f.fiberι y (hxy ▸ f.asFiber x)
  rw [fiberι_cast_asFiber]

private noncomputable def residueFieldMap_equiv_of_closedImmersion {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsClosedImmersion g] (x : X) :
    Y.residueField (g x) ≃+* X.residueField x := by
  let φ := (g.residueFieldMap x).hom
  have hsurj : Function.Surjective φ := by
    change Function.Surjective
      (IsLocalRing.ResidueField.map (g.stalkMap x).hom)
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk x) a
    obtain ⟨c, hc⟩ := g.stalkMap_surjective x b
    refine ⟨IsLocalRing.residue (Y.presheaf.stalk (g x)) c, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue, hc]
  exact RingEquiv.ofBijective φ ⟨RingHom.injective φ, hsurj⟩

/-- The fibre of a locally quasi-finite morphism is locally artinian. -/
private lemma isLocallyArtinian_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y) : IsLocallyArtinian (f.fiber y) := by
  have : LocallyQuasiFinite (f.fiberToSpecResidueField y) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  exact IsLocallyArtinian.of_locallyQuasiFinite (f.fiberToSpecResidueField y)

private noncomputable def fiberResidueFieldEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) :
    (f.fiber (f x)).residueField (f.asFiber x) ≃+* X.residueField x := by
  let F := f.fiber (f x)
  let g := f.asFiberHom x
  let c := IsLocalRing.closedPoint (X.residueField x)
  have : IsLocallyArtinian F := isLocallyArtinian_fiber f (f x)
  have hclosed : IsClosed ({f.asFiber x} : Set F) := isClosed_discrete _
  let : IsClosedImmersion g := by
    apply IsClosedImmersion.of_isPreimmersion g
    simp [g, Scheme.Hom.range_asFiberHom]
  have e₀ : F.residueField (g c) ≃+* (Spec (X.residueField x)).residueField c :=
    residueFieldMap_equiv_of_closedImmersion g c
  have e₁ : (Spec (X.residueField x)).residueField c ≃+* X.residueField x :=
    (Scheme.Spec.residueFieldIso (.of (X.residueField x)) c).commRingCatIsoToRingEquiv.trans
      c.asIdeal.algEquivResidueFieldOfField.toRingEquiv.symm
  have hc : g c = f.asFiber x := Scheme.Hom.asFiberHom_apply f x c
  have e₀' : F.residueField (f.asFiber x) ≃+* (Spec (X.residueField x)).residueField c := by
    exact hc ▸ e₀
  simpa [F] using e₀'.trans e₁

private lemma inertiaDeg_eq_finSepDegree_mul_finInsepDegree
    {k B : Type*} [Field k] [CommRing B] [Algebra k B] [Module.Finite k B]
    (q : (⊥ : Ideal k).primesOver B) :
    (letI : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q;
     q.1.inertiaDeg k =
      Field.finSepDegree k q.1.ResidueField * Field.finInsepDegree k q.1.ResidueField) := by
  let p : Ideal k := ⊥
  let : p.IsMaximal := Ideal.bot_isMaximal
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.1) :=
    Localization.AtPrime.algebraOfLiesOver p q.1
  let : Localization.AtPrime.IsLiesOverAlgebra p q.1 := inferInstance
  let : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q
  let epk : p.ResidueField ≃+* k :=
    p.algEquivResidueFieldOfField.toRingEquiv.symm
  let hq : q.1.LiesOver p := Ideal.primesOver.liesOver p q
  let ψ := Ideal.ResidueField.map p q.1 (algebraMap k B) hq.over
  let : Module k q.1.ResidueField := (fiberPrimeResidueFieldAlgebra q).toModule
  have hcompat : (algebraMap k q.1.ResidueField).comp epk.toRingHom =
      algebraMap p.ResidueField q.1.ResidueField := by
    apply RingHom.ext
    intro a
    show ψ (epk.symm (epk a)) = ψ a
    simp
  have hfin := Algebra.finrank_eq_of_equiv_equiv epk (RingEquiv.refl _)
    hcompat
  rw [Ideal.inertiaDeg_eq (p := p) q.1]
  calc
    Module.finrank p.ResidueField q.1.ResidueField = Module.finrank k q.1.ResidueField := by
      convert hfin using 1
    _ = Field.finSepDegree k q.1.ResidueField * Field.finInsepDegree k q.1.ResidueField :=
      (Field.finSepDegree_mul_finInsepDegree k q.1.ResidueField).symm

private lemma flatWeightTerm_eq_ramificationInertia
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f] (y : Y)
    (x : X) (hxy : f x = y) :
    (letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
       (f.residueFieldMap x).hom.toAlgebra
     let : Algebra (Y.residueField y) (Γ(f.fiber y, ⊤)) :=
       (fiberGlobalSectionsMap f y).toAlgebra
     let : Algebra (Y.residueField y) ((f.fiber y).residueField (hxy ▸ f.asFiber x)) :=
       ((Scheme.ΓSpecIso (.of (Y.residueField y))).inv ≫
         (f.fiberToSpecResidueField y).appTop ≫
         (f.fiber y).Γevaluation (hxy ▸ f.asFiber x)).hom.toAlgebra
    ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))))).toNat : ℤ) *
      (Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) *
        (Field.finSepDegree (Y.residueField y)
          ((f.fiber y).residueField (hxy ▸ f.asFiber x)) : ℤ) =
      (fiberPrimeOver f y (hxy ▸ f.asFiber x)).1.ramificationIdx (Y.residueField y) *
      (fiberPrimeOver f y (hxy ▸ f.asFiber x)).1.inertiaDeg (Y.residueField y)) := by
  classical
  cases hxy
  let k := Y.residueField (f x)
  let F := f.fiber (f x)
  let z := f.asFiber x
  let q := fiberPrimeOver f (f x) z
  let : Algebra k (Γ(F, ⊤)) := (fiberGlobalSectionsMap f (f x)).toAlgebra
  let : Module.Finite k (Γ(F, ⊤)) := fiberGlobalSectionsMap_moduleFinite f (f x)
  let : Algebra (Γ(F, ⊤)) q.1.ResidueField :=
    (algebraMap (Γ(F, ⊤)) q.1.ResidueField).toAlgebra
  let : Algebra k q.1.ResidueField := fiberPrimeResidueFieldAlgebra q
  let : IsScalarTower k (Γ(F, ⊤)) q.1.ResidueField :=
    fiberPrimeResidueField_isScalarTower q
  let : Algebra k (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra k (F.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f.fiberToSpecResidueField (f x)).appTop ≫
      F.Γevaluation z).hom.toAlgebra
  let e₁ : q.1.ResidueField ≃ₐ[k] F.residueField z :=
    fiberPrimeResidueFieldAlgEquiv f (f x) z
  let e₂ : F.residueField z ≃ₐ[k] X.residueField x :=
    fiberResidueFieldAlgEquiv f x
  have hsep : Field.finSepDegree k q.1.ResidueField =
      Field.finSepDegree k (F.residueField z) :=
    Field.finSepDegree_eq_of_equiv _ _ _ e₁
  have hinsep : Field.finInsepDegree k q.1.ResidueField =
      Field.finInsepDegree k (X.residueField x) :=
    Field.finInsepDegree_eq_of_equiv _ _ _ (e₁.trans e₂)
  have hlen : Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) =
      q.1.ramificationIdx k := by
    rw [localFiberLength_eq_fiberStalkLength f x]
    exact fiberStalkLength_eq_ramificationIdx f (f x) z
  have hlenNat : (Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))))).toNat =
      q.1.ramificationIdx k := by
    rw [hlen]
    simp
  have hInertia := inertiaDeg_eq_finSepDegree_mul_finInsepDegree q
  show ((Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))))).toNat : ℤ) *
      (Field.finInsepDegree k (X.residueField x) : ℤ) *
        (Field.finSepDegree k (F.residueField z) : ℤ) = _
  rw [hInertia, ← hlenNat, ← hinsep, ← hsep]
  push_cast
  ring

/-- The stalk map of an étale morphism is a formally unramified, essentially finite type local
homomorphism. -/
private lemma stalkMap_etale_props {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g] (x : X) :
    letI := (g.stalkMap x).hom.toAlgebra
    Algebra.FormallyUnramified (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) ∧
      IsLocalHom (algebraMap (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)) := by
  let := (g.stalkMap x).hom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap g x
  · rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap g x
  · exact (inferInstance : IsLocalHom (g.stalkMap x).hom)

/-- An étale morphism sends the maximal ideal of a stalk to that of the source stalk. -/
private lemma map_maximalIdeal_stalkMap_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g] (x : X) :
    Ideal.map (g.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let := (g.stalkMap x).hom.toAlgebra
  obtain ⟨_, _, _⟩ := stalkMap_etale_props g x
  exact Algebra.FormallyUnramified.map_maximalIdeal

private lemma localFiberLength_eq_of_etale_square {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y)
    (comm : h ≫ f = π ≫ g) [Etale h] [Etale g] (u : U) :
    Module.length (U.presheaf.stalk u)
        ((U.presheaf.stalk u) ⧸ Ideal.map (π.stalkMap u).hom
          (IsLocalRing.maximalIdeal (V.presheaf.stalk (π u)))) =
      Module.length (X.presheaf.stalk (h u))
        ((X.presheaf.stalk (h u)) ⧸ Ideal.map (f.stalkMap (h u)).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u))))) := by
  have hxy : f (h u) = g (π u) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : U ⟶ Y => q u) comm
  have hpoint : (h ≫ f) u = (π ≫ g) u := by
    show f (h u) = g (π u)
    exact hxy
  let eY : Y.presheaf.stalk (f (h u)) ≅ Y.presheaf.stalk (g (π u)) :=
    Y.presheaf.stalkCongr (.of_eq hxy)
  have heY : eY.hom = (Y.presheaf.stalkCongr (.of_eq hpoint)).hom := by
    apply congrArg Iso.hom
    congr 1
  let A := X.presheaf.stalk (h u)
  let B := U.presheaf.stalk u
  let : Algebra A B := (h.stalkMap u).hom.toAlgebra
  have hflat : Module.Flat A B := Flat.stalkMap h u
  let : Module.Flat A B := hflat
  let : IsLocalHom (algebraMap A B) := by
    show IsLocalHom (h.stalkMap u).hom
    infer_instance
  have hmax : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B := map_maximalIdeal_stalkMap_eq h u
  have hcompCat : f.stalkMap (h u) ≫ h.stalkMap u =
      eY.hom ≫ g.stalkMap (π u) ≫ π.stalkMap u := by
    rw [← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom (h ≫ f) (π ≫ g) comm u,
      Scheme.Hom.stalkMap_comp, ← heY]
    rfl
  have hcomp : (h.stalkMap u).hom.comp (f.stalkMap (h u)).hom =
      (π.stalkMap u).hom.comp ((g.stalkMap (π u)).hom.comp eY.hom.hom) := by
    have hc' := congrArg CommRingCat.Hom.hom hcompCat
    simpa only [CommRingCat.hom_comp, RingHom.comp_assoc] using hc'
  have hbase : Ideal.map ((g.stalkMap (π u)).hom.comp eY.hom.hom)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))) =
      IsLocalRing.maximalIdeal (V.presheaf.stalk (π u)) := by
    have hiso : Ideal.map eY.hom.hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))) =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (g (π u))) := by
      have hh := IsLocalRing.map_ringEquiv_maximalIdeal eY.commRingCatIsoToRingEquiv
      change Ideal.map eY.commRingCatIsoToRingEquiv.toRingHom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))) = _ at hh
      show Ideal.map eY.commRingCatIsoToRingEquiv.toRingHom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))) = _
      exact hh
    rw [← Ideal.map_map, hiso]
    exact map_maximalIdeal_stalkMap_eq g (π u)
  have hideal : Ideal.map (algebraMap A B)
        (Ideal.map (f.stalkMap (h u)).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u))))) =
      Ideal.map (π.stalkMap u).hom
      (IsLocalRing.maximalIdeal (V.presheaf.stalk (π u))) := by
    show Ideal.map (h.stalkMap u).hom
        (Ideal.map (f.stalkMap (h u)).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u))))) = _
    calc
      _ = Ideal.map ((h.stalkMap u).hom.comp (f.stalkMap (h u)).hom)
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))) := by rw [Ideal.map_map]
      _ = Ideal.map ((π.stalkMap u).hom.comp ((g.stalkMap (π u)).hom.comp eY.hom.hom))
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))) := by rw [hcomp]
      _ = Ideal.map (π.stalkMap u).hom
          (Ideal.map ((g.stalkMap (π u)).hom.comp eY.hom.hom)
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u))))) := by rw [Ideal.map_map]
      _ = Ideal.map (π.stalkMap u).hom
          (IsLocalRing.maximalIdeal (V.presheaf.stalk (π u))) := by rw [hbase]
  show Module.length B (B ⧸ Ideal.map (π.stalkMap u).hom
      (IsLocalRing.maximalIdeal (V.presheaf.stalk (π u)))) =
    Module.length A (A ⧸ Ideal.map (f.stalkMap (h u)).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (h u)))))
  rw [← hideal]
  exact length_quotient_baseChange hmax _

/-- The residue field of a point of a locally quasi-finite morphism is finite over that of its
image. -/
private lemma finite_residueField_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f x)) (X.residueField x) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have hBE : (X.residue x).hom.QuasiFinite := RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective (X.residue x).hom (X.residue_surjective x))
  have hAE := hBE.comp (f.quasiFiniteAt x)
  let : Algebra A (Y.residueField (f x)) := (Y.residue (f x)).hom.toAlgebra
  let : Algebra A (X.residueField x) := ((X.residue x).hom.comp (f.stalkMap x).hom).toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower A (Y.residueField (f x)) (X.residueField x) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    have hh := congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x)
    exact congrArg (fun φ : A →+* X.residueField x => φ a) hh.symm
  have : Algebra.QuasiFinite A (X.residueField x) := hAE
  have : Algebra.QuasiFinite (Y.residueField (f x)) (X.residueField x) :=
    Algebra.QuasiFinite.of_restrictScalars A _ _
  exact Module.Finite.of_quasiFinite

/-- The inseparable degree of the residue-field extension at a point is unchanged along an
étale base change square.

Given a commutative square `h ≫ f = π ≫ g` with `h` and `g` étale and `f` and `π` locally
quasi-finite, and a point `u` of `U`, the residue-field extension `κ(f (h u)) ⊆ κ(h u)` cut out
by `f` and the residue-field extension `κ(π u) ⊆ κ(u)` cut out by `π` have the same finite
inseparable degree. Indeed the two extensions sit in a tower over `κ(f (h u))` whose two étale
steps `κ(f (h u)) ⊆ κ(π u)` and `κ(h u) ⊆ κ(u)` are separable, so they contribute nothing to
the inseparable degree. -/
lemma finInsepDegree_residueField_eq_of_etale_square
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (h : U ⟶ X) (π : U ⟶ V) (g : V ⟶ Y)
    (comm : h ≫ f = π ≫ g) [Etale h] [Etale g] [LocallyQuasiFinite f]
    [LocallyQuasiFinite π] (u : U) :
    (letI := (f.residueFieldMap (h u)).hom.toAlgebra;
      Field.finInsepDegree (Y.residueField (f (h u))) (X.residueField (h u))) =
    (letI := (π.residueFieldMap u).hom.toAlgebra;
      Field.finInsepDegree (V.residueField (π u)) (U.residueField u)) := by
  let K := Y.residueField (f (h u))
  let K' := V.residueField (π u)
  let L := X.residueField (h u)
  let L' := U.residueField u
  have hxyRaw := congrArg (fun q : U ⟶ Y => q u) comm
  have hxy : f (h u) = g (π u) := by
    simpa only [Scheme.Hom.comp_apply] using hxyRaw
  let eK : Y.residueField (f (h u)) ≅ Y.residueField (g (π u)) :=
    Y.residueFieldCongr hxy
  let : Algebra K K' :=
    ((g.residueFieldMap (π u)).hom.comp eK.hom.hom).toAlgebra
  let : Algebra K L := (f.residueFieldMap (h u)).hom.toAlgebra
  let : Algebra K' L' := (π.residueFieldMap u).hom.toAlgebra
  let : Algebra L L' := (h.residueFieldMap u).hom.toAlgebra
  have hsep : Algebra.IsSeparable K K' := by
    let C := Y.presheaf.stalk (g (π u))
    let D := V.presheaf.stalk (π u)
    let : Algebra C D := (g.stalkMap (π u)).hom.toAlgebra
    obtain ⟨_, _, _⟩ := stalkMap_etale_props g (π u)
    let a₀ : Algebra (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField D) :=
      IsLocalRing.ResidueField.instAlgebra (R := C) (S := D)
    let a₁ : Algebra (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField D) :=
      (g.residueFieldMap (π u)).hom.toAlgebra
    have ha : a₀ = a₁ := by
      apply Algebra.algebra_ext
      intro a
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := C) a
      show IsLocalRing.residue D ((g.stalkMap (π u)).hom r) =
        IsLocalRing.ResidueField.map (g.stalkMap (π u)).hom (IsLocalRing.residue C r)
      rw [IsLocalRing.ResidueField.map_residue]
    let : Algebra (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField D) := a₀
    have hsepCD : Algebra.IsSeparable (IsLocalRing.ResidueField C)
        (IsLocalRing.ResidueField D) := by
      infer_instance
    let e₁ : IsLocalRing.ResidueField C ≃+* K :=
      eK.commRingCatIsoToRingEquiv.symm
    let e₂ : IsLocalRing.ResidueField D ≃+* K' := RingEquiv.refl _
    have hmap : algebraMap (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField D) =
        (g.residueFieldMap (π u)).hom := by
      have hh := congrArg (fun a : Algebra (IsLocalRing.ResidueField C)
          (IsLocalRing.ResidueField D) => a.algebraMap) ha
      exact hh
    have he : RingHom.comp (algebraMap K K') e₁ =
        RingHom.comp e₂ (algebraMap (IsLocalRing.ResidueField C)
          (IsLocalRing.ResidueField D)) := by
      ext a
      show (g.residueFieldMap (π u)).hom (eK.hom (e₁ a)) =
        algebraMap (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField D) a
      rw [hmap]
      have hk : eK.hom (e₁ a) = a := by
        show eK.commRingCatIsoToRingEquiv (e₁ a) = a
        exact eK.commRingCatIsoToRingEquiv.apply_symm_apply a
      rw [hk]
      rfl
    exact (Algebra.IsSeparable.iff_of_equiv_equiv e₁ e₂ he).mp hsepCD
  have hcomp : (h.residueFieldMap u).hom.comp (f.residueFieldMap (h u)).hom =
      (π.residueFieldMap u).hom.comp
        ((g.residueFieldMap (π u)).hom.comp eK.hom.hom) := by
    have hc := Scheme.Hom.residueFieldMap_congr comm u
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hc
    have hc' := congrArg CommRingCat.Hom.hom hc
    have heK : eK.hom = (Y.residueFieldCongr hxyRaw).hom := by
      congr 1
    rw [← heK] at hc'
    convert hc' using 1
    all_goals
      ext a
      rfl
  let : Algebra K L' :=
    ((h.residueFieldMap u).hom.comp (f.residueFieldMap (h u)).hom).toAlgebra
  have hT₁ : IsScalarTower K K' L' := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact congrArg (fun φ : K →+* L' => φ a) hcomp
  have hT₂ : IsScalarTower K L L' := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  let _i := hT₁
  let _i := hT₂
  have : Module.Finite K L := finite_residueField_of_locallyQuasiFinite f (h u)
  have : Module.Finite K' L' := finite_residueField_of_locallyQuasiFinite π u
  have halg₁ : Algebra.IsAlgebraic K L := .of_finite K L
  have halg₂ : Algebra.IsAlgebraic K' L' := .of_finite K' L'
  exact finInsepDegree_eq_of_separable_square (K := K) (K' := K') (L := L) (L' := L')



private lemma isArtinianRing_stalk_of_isLocallyArtinian {Z : Scheme.{u}}
    [IsLocallyArtinian Z] (z : Z) : IsArtinianRing (Z.presheaf.stalk z) := by
  obtain ⟨W, hW, hz, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) (by simp)
  let p := hW.primeIdealOf ⟨z, hz⟩
  let : Algebra Γ(Z, W) (Z.presheaf.stalk z) :=
    (Z.presheaf.germ W z hz).hom.toAlgebra
  have hloc := hW.isLocalization_stalk ⟨z, hz⟩
  let : IsLocalization p.asIdeal.primeCompl (Z.presheaf.stalk z) := hloc
  have hArt : IsArtinianRing Γ(Z, W) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨W, hW⟩
  exact IsArtinianRing.localization_artinian p.asIdeal.primeCompl _

private lemma localFiberLength_ne_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X) :
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) ≠ ⊤ := by
  have : IsLocallyArtinian (f.fiber (f x)) := isLocallyArtinian_fiber f (f x)
  have : IsArtinianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    isArtinianRing_stalk_of_isLocallyArtinian _
  rw [localFiberLength_eq_fiberStalkLength]
  exact Module.length_ne_top

/-- The local-fibre length times the inseparable degree of the residue-field
extension at a point of a scheme morphism. -/
@[stacks 0F3D "the formula"]
noncomputable def flatQuasiFiniteWeight {X Y : Scheme.{u}} (f : X ⟶ Y) : X → ℤ :=
  fun x ↦
    let _i := (f.residueFieldMap x).hom.toAlgebra
    ((Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸
        Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))))).toNat : ℤ) *
      (Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)

private lemma flatQuasiFiniteWeight_fiberSum_eq_finrank
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [Flat f] [IsFinite f] :
    separableDegreeWeightedFiberSum f (flatQuasiFiniteWeight f) =
      fun y ↦ (f.finrank y : ℤ) := by
  classical
  funext y
  let k := Y.residueField y
  let F := f.fiber y
  let B := Γ(F, ⊤)
  let φ := fiberGlobalSectionsMap f y
  let : Algebra k B := φ.toAlgebra
  have hfiniteφ : φ.Finite := fiberGlobalSectionsMap_finite f y
  have hflatφ : φ.Flat := fiberGlobalSectionsMap_flat f y
  let : Module.Finite k B := fiberGlobalSectionsMap_moduleFinite f y
  let : Module.Flat k B := (RingHom.flat_algebraMap_iff).mp (by
    rw [RingHom.algebraMap_toAlgebra]
    exact hflatφ)
  have hαfinite : IsFinite (f.fiberToSpecResidueField y) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  let : IsFinite (f.fiberToSpecResidueField y) := hαfinite
  let : IsLocallyArtinian F := isLocallyArtinian_fiber f y
  let : CompactSpace F := inferInstance
  let : IsArtinianScheme F := { toIsLocallyArtinian := inferInstance }
  let : Finite F := inferInstance
  let : Fintype F := Fintype.ofFinite F
  let Q := (⊥ : Ideal k).primesOver B
  let e : F ≃ Q := {
    toFun := fun z ↦ fiberPrimeOver f y z
    invFun := fun q ↦ F.isoSpec.inv ⟨q.1, q.2.1⟩
    left_inv := by
      intro z
      show F.isoSpec.inv (F.isoSpec.hom z) = z
      simp
    right_inv := by
      intro q
      apply Subtype.ext
      show (F.isoSpec.hom (F.isoSpec.inv ⟨q.1, q.2.1⟩)).asIdeal = q.1
      have hp := F.isoSpec.schemeIsoToHomeo.apply_symm_apply
        (⟨q.1, q.2.1⟩ : Spec (.of B))
      have hp' : F.isoSpec.hom (F.isoSpec.inv ⟨q.1, q.2.1⟩) =
          ⟨q.1, q.2.1⟩ := by
        show F.isoSpec.schemeIsoToHomeo
          (F.isoSpec.schemeIsoToHomeo.symm ⟨q.1, q.2.1⟩) = _
        exact hp
      exact congrArg PrimeSpectrum.asIdeal hp' }
  let : Fintype Q := Fintype.ofEquiv F e
  let : IsArtinianRing B := inferInstance
  let : Algebra.QuasiFinite k B := inferInstance
  have hsumN : ∑ q : Q, q.1.ramificationIdx k * q.1.inertiaDeg k =
      Module.finrank k B := field_algebra_rank_sum
  have hrank : Module.finrank k B = f.finrank y := by
    let β : Spec (.of B) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom φ)
    have : IsFinite β :=
      (IsFinite.SpecMap_iff (CommRingCat.ofHom φ)).mpr hfiniteφ
    have : Flat β :=
      (Flat.SpecMap_iff (f := CommRingCat.ofHom φ)).mpr hflatφ
    have hβ : (Spec.map (CommRingCat.ofHom φ)).finrank = φ.finrank :=
      Scheme.Hom.finrank_SpecMap_eq_finrank hfiniteφ hflatφ
    have hmodule : φ.finrank (IsLocalRing.closedPoint k) = Module.finrank k B := by
      show Module.rankAtStalk B (IsLocalRing.closedPoint k) = Module.finrank k B
      exact congrFun (Module.rankAtStalk_eq_finrank_of_free (R := k) (M := B))
        (IsLocalRing.closedPoint k)
    calc
      Module.finrank k B = (Spec.map (CommRingCat.ofHom φ)).finrank
          (IsLocalRing.closedPoint k) := by rw [hβ, hmodule]
      _ = (F.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ)).finrank
          (IsLocalRing.closedPoint k) := by
            rw [Scheme.Hom.finrank_comp_left_of_isIso]
      _ = (f.fiberToSpecResidueField y).finrank (IsLocalRing.closedPoint k) := by
            rw [fiber_isoSpec_comp_SpecMap]
      _ = f.finrank y := by
            have h := Scheme.Hom.finrank_pullback_snd f (Y.fromSpecResidueField y)
              (IsLocalRing.closedPoint k)
            rw [Scheme.fromSpecResidueField_apply y (IsLocalRing.closedPoint k)] at h
            simpa [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber] using h
  rw [weightedFiberSum_eq_fiber_sum f (flatQuasiFiniteWeight f) y]
  rw [finsum_eq_sum_of_fintype]
  calc
    (∑ z : F,
        let _i := ((Scheme.ΓSpecIso (.of k)).inv ≫
          (f.fiberToSpecResidueField y).appTop ≫ F.Γevaluation z).hom.toAlgebra
        flatQuasiFiniteWeight f (f.fiberι y z) *
          (Field.finSepDegree k (F.residueField z) : ℤ)) =
      ∑ q : Q, (q.1.ramificationIdx k : ℤ) * (q.1.inertiaDeg k : ℤ) := by
        apply Fintype.sum_equiv e
        intro z
        let x := f.fiberι y z
        obtain ⟨hxy, hz⟩ := fiber_point_eq_asFiber f y z
        rw [hz]
        have hpoint : f.fiberι y (hxy ▸ f.asFiber x) = x :=
          fiberι_cast_asFiber f x hxy
        rw [hpoint]
        exact flatWeightTerm_eq_ramificationInertia f y x hxy
    _ = (Module.finrank k B : ℤ) := by
      exact_mod_cast hsumN
    _ = (f.finrank y : ℤ) := by exact_mod_cast hrank

/-- The canonical local-fibre weighting is strictly positive. -/
@[stacks 0F3D "positivity"]
theorem flatQuasiFiniteWeight_pos {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f]
    (x : X) : 0 < flatQuasiFiniteWeight f x := by
  let Q := (X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
  have hlen_top : Module.length (X.presheaf.stalk x) Q ≠ ⊤ :=
    localFiberLength_ne_top f x
  have hquot : Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) < ⊤ :=
    IsLocalRing.map_maximalIdeal_lt_top (f.stalkMap x).hom
  have : Nontrivial Q :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_of_lt hquot)
  have hlen_pos : 0 < Module.length (X.presheaf.stalk x) Q := Module.length_pos
  have hlen_nat_pos : 0 < (Module.length (X.presheaf.stalk x) Q).toNat :=
    ENat.toNat_pos (ne_of_gt hlen_pos) hlen_top
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : FiniteDimensional (Y.residueField (f x)) (X.residueField x) :=
    finite_residueField_of_locallyQuasiFinite f x
  have hinsep_pos : 0 < Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) :=
    Nat.pos_iff_ne_zero.mpr (NeZero.ne _)
  show 0 < ((Module.length (X.presheaf.stalk x) Q).toNat : ℤ) *
    (Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℤ)
  exact_mod_cast mul_pos hlen_nat_pos hinsep_pos

/-- The canonical local-fibre function is a weighting. -/
@[stacks 0F3D "weighting"]
theorem flatQuasiFiniteWeight_isWeighting {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f] :
    IsWeighting f (flatQuasiFiniteWeight f) := by
  classical
  rw [isWeighting_iff]
  intro U V h π g comm hg hU hπ
  let q := pullback.lift h π comm
  have hh : h = q ≫ pullback.fst f g := (pullback.lift_fst h π comm).symm
  have hπ' : π = q ≫ pullback.snd f g := (pullback.lift_snd h π comm).symm
  have : Etale h := by
    rw [hh]
    infer_instance
  have : Flat π := by
    rw [hπ']
    infer_instance
  have : LocallyOfFinitePresentation π := by
    rw [hπ']
    infer_instance
  have : LocallyQuasiFinite π := by infer_instance
  have : Stacks.Morphisms.IsFiniteLocallyFree π :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation π).2
      ⟨hπ, inferInstance, inferInstance⟩
  have hweights : flatQuasiFiniteWeight f ∘ h = flatQuasiFiniteWeight π := by
    funext u
    simp only [Function.comp_apply, flatQuasiFiniteWeight]
    rw [localFiberLength_eq_of_etale_square f h π g comm u,
      finInsepDegree_residueField_eq_of_etale_square f h π g comm u]
  have hsum : separableDegreeWeightedFiberSum π (flatQuasiFiniteWeight π) =
      fun v ↦ (π.finrank v : ℤ) := by
    exact flatQuasiFiniteWeight_fiberSum_eq_finrank π
  rw [hweights, hsum]
  exact (π.isLocallyConstant_finrank).comp fun n => (n : ℤ)

/-- For a finite flat morphism the separable-degree weighted fibre sum of the canonical
local-fibre weighting is the rank of the morphism: summing the local fibre lengths over a fibre,
each weighted by the separable and the inseparable degree of its residue-field extension, gives
the dimension of the fibre over the residue field of its image.

This is the fibre-sum identity which `AlgebraicGeometry.flatQuasiFiniteWeight_isWeighting`
consumes internally to conclude local constancy; stated on its own it is the degree of a fibre
of a finite flat morphism, which is what the push-pull formula of Stacks 02RH needs. -/
alias separableDegreeWeightedFiberSum_flatQuasiFiniteWeight := flatQuasiFiniteWeight_fiberSum_eq_finrank

end AlgebraicGeometry
