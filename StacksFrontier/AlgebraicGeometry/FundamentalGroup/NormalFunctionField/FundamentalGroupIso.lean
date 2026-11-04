module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.FieldTheory.Galois.Infinite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalFunctionField.MaximalEtaleExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalGenericPointSurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale fundamental group of a normal integral scheme as a Galois group

Let `X` be an integral normal scheme, let `sbar` be an algebraic geometric point of `X` lying over
the generic point, and let `M` be the maximal subextension of `Ω = κ(sbar)` in which `X` is
unramified (`AlgebraicGeometry.maximalEtaleExtension`). This file constructs the action of
`Gal(Ω/K)` on the finite-étale fibre functor at `sbar` and identifies `π₁(X, sbar)` with the
Galois group `Gal(M/K)`.

## Main definitions

* `AlgebraicGeometry.absoluteGaloisToFundamentalGroup` — the action of `Gal(Ω/K)` on the
  finite-étale fibre functor at `sbar`, as a continuous homomorphism to `π₁(X, sbar)`.
* `AlgebraicGeometry.fundamentalGroupIsoGalMaximalEtaleExtension` — the identification
  `π₁(X, sbar) ≃ Gal(M/K)` of topological groups.

## Main results

* `AlgebraicGeometry.absoluteGaloisToFundamentalGroup_apply` — a field automorphism acts on a
  finite étale geometric fibre by precomposition, which pins the homomorphism down.
* `AlgebraicGeometry.fundamentalGroupIsoGalMaximalEtaleExtension_apply` — the identification
  carries that homomorphism to restriction of automorphisms to `M`, which pins the isomorphism
  down: it is not merely an abstract isomorphism of profinite groups.

## Implementation notes

The isomorphism of groups is built from the two surjections out of `Gal(Ω/K)` — the fibre-functor
action and restriction to `M` — which have the same kernel; surjectivity of the first is Stacks
0BQM, recorded in `StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalGenericPointSurjective`.

## References

* [Stacks Project, Tag 03VG](https://stacks.math.columbia.edu/tag/03VG)
* [Stacks Project, Tag 0BQM](https://stacks.math.columbia.edu/tag/0BQM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (sbar : GeometricPoint X)

attribute [local instance]
  instAlgebraCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatSpecOfResidueFieldHomTopCatBaseHomDefault

/-- The homomorphism `H →* J` through which `g` factors when `f` is surjective and its kernel is
contained in that of `g`. -/
private noncomputable def liftAlongSurjective
    {G H J : Type*} [Group G] [Group H] [Group J]
    (f : G →* H) (g : G →* J) (hf : Function.Surjective f) (hker : f.ker ≤ g.ker) :
    H →* J :=
  f.liftOfSurjective hf ⟨g, hker⟩

private theorem liftAlongSurjective_apply
    {G H J : Type*} [Group G] [Group H] [Group J]
    (f : G →* H) (g : G →* J) (hf : Function.Surjective f) (hker : f.ker ≤ g.ker) (x : G) :
    liftAlongSurjective f g hf hker (f x) = g x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

private theorem continuous_liftAlongSurjective
    {G H J : Type*} [Group G] [Group H] [Group J]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
    [CompactSpace G] [T2Space H]
    (f : G →ₜ* H) (g : G →ₜ* J) (hf : Function.Surjective f)
    (hker : f.toMonoidHom.ker ≤ g.toMonoidHom.ker) :
    Continuous (liftAlongSurjective f.toMonoidHom g.toMonoidHom hf hker) := by
  apply (Topology.IsQuotientMap.of_surjective_continuous hf f.continuous).continuous_iff.mpr
  have hcomp :
      (liftAlongSurjective f.toMonoidHom g.toMonoidHom hf hker : H → J) ∘ (f : G → H) =
        (g : G → J) :=
    funext (liftAlongSurjective_apply f.toMonoidHom g.toMonoidHom hf hker)
  rw [hcomp]
  exact g.continuous

/-- Two continuous surjections out of a compact group with the same kernel identify their targets
as topological groups. -/
private noncomputable def continuousMulEquivOfSurjectiveOfKerEq
    {G H J : Type*} [Group G] [Group H] [Group J]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
    [CompactSpace G] [T2Space H] [T2Space J]
    (f : G →ₜ* H) (g : G →ₜ* J)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.toMonoidHom.ker = g.toMonoidHom.ker) :
    H ≃ₜ* J :=
  ⟨{ liftAlongSurjective f.toMonoidHom g.toMonoidHom hf hker.le with
      invFun := liftAlongSurjective g.toMonoidHom f.toMonoidHom hg hker.ge
      left_inv := by
        intro y
        obtain ⟨x, rfl⟩ := hf y
        exact (congrArg (liftAlongSurjective g.toMonoidHom f.toMonoidHom hg hker.ge)
            (liftAlongSurjective_apply f.toMonoidHom g.toMonoidHom hf hker.le x)).trans
          (liftAlongSurjective_apply g.toMonoidHom f.toMonoidHom hg hker.ge x)
      right_inv := by
        intro y
        obtain ⟨x, rfl⟩ := hg y
        exact (congrArg (liftAlongSurjective f.toMonoidHom g.toMonoidHom hf hker.le)
            (liftAlongSurjective_apply g.toMonoidHom f.toMonoidHom hg hker.ge x)).trans
          (liftAlongSurjective_apply f.toMonoidHom g.toMonoidHom hf hker.le x) },
    continuous_liftAlongSurjective f g hf hker.le,
    continuous_liftAlongSurjective g f hg hker.ge⟩

private theorem continuousMulEquivOfSurjectiveOfKerEq_apply
    {G H J : Type*} [Group G] [Group H] [Group J]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
    [CompactSpace G] [T2Space H] [T2Space J]
    (f : G →ₜ* H) (g : G →ₜ* J)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : f.toMonoidHom.ker = g.toMonoidHom.ker) (x : G) :
    continuousMulEquivOfSurjectiveOfKerEq f g hf hg hker (f x) = g x :=
  liftAlongSurjective_apply f.toMonoidHom g.toMonoidHom hf hker.le x

private theorem restrictNormalHom_separableClosure_injective
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Function.Injective
      (AlgEquiv.restrictNormalHom (separableClosure K Ω) :
        Gal(Ω/K) →* Gal(separableClosure K Ω/K)) := by
  let L := separableClosure K Ω
  let : Algebra L Ω := L.val.toAlgebra
  let : IsScalarTower K L Ω := inferInstance
  have hpi : IsPurelyInseparable L Ω := separableClosure.isPurelyInseparable K Ω
  let : IsPurelyInseparable L Ω := hpi
  intro σ τ h
  have hcomp : σ.toRingHom.comp (algebraMap L Ω) =
      τ.toRingHom.comp (algebraMap L Ω) := by
    ext x
    show σ (x : Ω) = τ (x : Ω)
    simpa only [AlgEquiv.restrictNormalHom_apply] using
      congrArg (fun z : L => (z : Ω)) (AlgEquiv.ext_iff.mp h x)
  have hst : σ.toRingHom = τ.toRingHom :=
    IsPurelyInseparable.injective_comp_algebraMap L Ω Ω hcomp
  ext x
  exact congrArg (fun f : Ω →+* Ω => f x) hst

private theorem restrictNormalHom_separableClosure_surjective
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
  Function.Surjective
      (AlgEquiv.restrictNormalHom (separableClosure K Ω) :
        Gal(Ω/K) →* Gal(separableClosure K Ω/K)) := by
  intro σ
  exact AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := separableClosure K Ω) (E := Ω) σ

private noncomputable def restrictNormalHom_separableClosure_equiv
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Gal(Ω/K) ≃* Gal(separableClosure K Ω/K) :=
  MulEquiv.ofBijective
    (AlgEquiv.restrictNormalHom (separableClosure K Ω) : Gal(Ω/K) →* Gal(separableClosure K Ω/K))
    ⟨restrictNormalHom_separableClosure_injective K Ω,
      restrictNormalHom_separableClosure_surjective K Ω⟩

private theorem restrictNormalHom_separableClosure_continuous
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
  Continuous (AlgEquiv.restrictNormalHom (separableClosure K Ω) :
      Gal(Ω/K) → Gal(separableClosure K Ω/K)) :=
  InfiniteGalois.restrictNormalHom_continuous (separableClosure K Ω)

private theorem fixes_of_restrict_fixes_inf
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (E : IntermediateField K Ω) (σ : Gal(Ω/K))
    (h : ∀ y : Ω, y ∈ E ⊓ separableClosure K Ω → σ y = y) :
    ∀ x : Ω, x ∈ E → σ x = x := by
  let S := separableClosure K Ω
  let : Algebra S Ω := S.val.toAlgebra
  let : IsPurelyInseparable S Ω := separableClosure.isPurelyInseparable K Ω
  let q := ringExpChar S
  let : ExpChar Ω q := expChar_of_injective_ringHom (algebraMap S Ω).injective q
  intro x hx
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem S q x
  have hyS : x ^ (q ^ n) ∈ S := by
    change (y : Ω) = x ^ (q ^ n) at hy
    exact hy ▸ y.property
  have hyE : x ^ (q ^ n) ∈ E := E.toSubfield.pow_mem hx (q ^ n)
  have heq : σ (x ^ (q ^ n)) = x ^ (q ^ n) := h _ ⟨hyE, hyS⟩
  apply iterateFrobenius_inj Ω q n
  simpa only [iterateFrobenius_def, map_pow] using heq

private theorem fixes_of_restrict_fixes_inf'
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (σ : Gal(Ω/K))
    (h : (AlgEquiv.restrictNormalHom (separableClosure K Ω) σ) ∈
      (IntermediateField.restrict
        (show E ⊓ separableClosure K Ω ≤ separableClosure K Ω from inf_le_right)).fixingSubgroup) :
    ∀ x : Ω, x ∈ E → σ x = x := by
  let S := separableClosure K Ω
  let R := E ⊓ S
  let R' := IntermediateField.restrict (show R ≤ S from inf_le_right)
  have hfix : ∀ y : Ω, y ∈ R → σ y = y := by
    intro y hy
    have hyS : y ∈ S := hy.2
    let z : S := ⟨y, hyS⟩
    have hz : z ∈ R' :=
      (IntermediateField.mem_restrict (show R ≤ S from inf_le_right) z).2 hy
    have hσz := (IntermediateField.mem_fixingSubgroup_iff R'
      (AlgEquiv.restrictNormalHom S σ)).mp h z hz
    have hz' := congrArg (fun t : S => (t : Ω)) hσz
    simpa only [AlgEquiv.restrictNormalHom_apply] using hz'
  exact fixes_of_restrict_fixes_inf K Ω E σ hfix

private theorem finite_restrict_inf
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (E S : IntermediateField K Ω) [FiniteDimensional K E] :
    FiniteDimensional K
      (IntermediateField.restrict (show E ⊓ S ≤ S from inf_le_right)) := by
  let R := E ⊓ S
  let e : R →ₐ[K] E := IntermediateField.inclusion inf_le_left
  let : FiniteDimensional K R := FiniteDimensional.of_injective e.toLinearMap e.injective
  let R' := IntermediateField.restrict (show R ≤ S from inf_le_right)
  have : FiniteDimensional K R' :=
    Module.Finite.equiv
      (IntermediateField.restrictAlgEquiv (show R ≤ S from inf_le_right)).toLinearEquiv
  exact inferInstance

private theorem restrictNormalHom_separableClosure_symm_continuous
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Continuous (restrictNormalHom_separableClosure_equiv K Ω).symm := by
  let S := separableClosure K Ω
  let r : Gal(Ω/K) →* Gal(S/K) := AlgEquiv.restrictNormalHom S
  let e : Gal(Ω/K) ≃* Gal(S/K) := restrictNormalHom_separableClosure_equiv K Ω
  show Continuous e.symm
  apply continuous_of_continuousAt_one e.symm
  apply continuousAt_def.mpr
  intro U hU
  have hU' : U ∈ nhds (1 : Gal(Ω/K)) := by simpa only [map_one] using hU
  obtain ⟨E, hfin, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω U).mp hU'
  let : FiniteDimensional K E := hfin
  let R' : IntermediateField K S :=
    IntermediateField.restrict (show E ⊓ S ≤ S from inf_le_right)
  have : FiniteDimensional K R' := finite_restrict_inf K Ω E S
  apply (krullTopology_mem_nhds_one_iff K S (e.symm ⁻¹' U)).mpr
  refine ⟨R', inferInstance, ?_⟩
  intro τ hτ
  apply hsub
  apply (IntermediateField.mem_fixingSubgroup_iff E (e.symm τ)).mpr
  intro x hx
  apply fixes_of_restrict_fixes_inf' K Ω E (e.symm τ) ?_ x hx
  have heτ : r (e.symm τ) = τ := e.apply_symm_apply τ
  show r (e.symm τ) ∈ R'.fixingSubgroup
  rw [heτ]
  exact hτ

private theorem compactSpace_Gal_isAlgClosure
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    CompactSpace Gal(Ω/K) := by
  let S := separableClosure K Ω
  let e : Gal(Ω/K) ≃* Gal(S/K) := restrictNormalHom_separableClosure_equiv K Ω
  let eₜ : Gal(Ω/K) ≃ₜ* Gal(S/K) :=
    ⟨e, restrictNormalHom_separableClosure_continuous K Ω,
      restrictNormalHom_separableClosure_symm_continuous K Ω⟩
  exact eₜ.symm.toHomeomorph.compactSpace

private theorem finite_point_factorization
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f]
    (p : Spec (.of Ω) ⟶ Z)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    ∃ (E : IntermediateField K Ω), FiniteDimensional K E ∧
      ∃ q : Spec (.of E) ⟶ Z,
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ q = p := by
  let r : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  let : Algebra K Γ(Z, ⊤) := r.hom.toAlgebra
  have hr : r.hom.Finite := RingHom.Finite.comp f.finite_appTop
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of K)).inv).2)
  have : Module.Finite K Γ(Z, ⊤) := hr
  let a : Γ(Z, ⊤) ⟶ CommRingCat.of Ω := p.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom
  have hra : r ≫ a = CommRingCat.ofHom (algebraMap K Ω) := by
    dsimp [r, a]
    rw [← Category.assoc, Category.assoc (Scheme.ΓSpecIso (.of K)).inv,
      ← Scheme.Hom.comp_appTop, hp, ← Scheme.ΓSpecIso_inv_naturality]
    simp
  let g : Γ(Z, ⊤) →ₐ[K] Ω :=
    { a.hom with commutes' := fun k => congrArg (fun h : CommRingCat.of K ⟶ .of Ω => h.hom k) hra }
  have : Module.Finite K g.range := Module.Finite.of_surjective
    g.rangeRestrict.toLinearMap g.rangeRestrict_surjective
  let E := (Subalgebra.isAlgebraic_iff g.range).mpr
    (Algebra.IsAlgebraic.of_finite K g.range) |>.toIntermediateField
  have : FiniteDimensional K E := inferInstanceAs (FiniteDimensional K g.range)
  have : IsAffine Z := isAffine_of_isAffineHom f
  refine ⟨E, inferInstance, Spec.map (CommRingCat.ofHom g.rangeRestrict.toRingHom) ≫
    Z.isoSpec.inv, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  show Spec.map a ≫ Z.isoSpec.inv = p
  dsimp [a]
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_hom]
  rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem galois_comp_geometricPoint
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default))) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ sbar.hom = sbar.hom := by
  let r := CommRingCat.ofHom (GeometricPoint.residueFieldHom sbar)
  let γ := Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)
  have hfac := geometricPoint_factorization X sbar
  have hfix : r ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom = r := by
    ext a
    exact σ.commutes a
  calc
    γ ≫ sbar.hom = γ ≫ (Spec.map r ≫ X.fromSpecResidueField (sbar.hom default)) :=
      congrArg (fun f : Spec (.of sbar.residueField) ⟶ X => γ ≫ f) hfac.symm
    _ = (γ ≫ Spec.map r) ≫
        X.fromSpecResidueField (sbar.hom default) := by rw [Category.assoc]
    _ = Spec.map (r ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        X.fromSpecResidueField (sbar.hom default) := by rw [← Spec.map_comp]
    _ = Spec.map r ≫ X.fromSpecResidueField (sbar.hom default) := by rw [hfix]
    _ = sbar.hom := hfac

private theorem spec_map_galois_one {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] :
    Spec.map (CommRingCat.ofHom (1 : Gal(Ω/K)).toAlgHom.toRingHom) = 𝟙 _ := by
  rw [← Spec.map_id, ← CommRingCat.ofHom_id]
  rfl

private theorem spec_map_galois_mul {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (σ τ : Gal(Ω/K)) :
    Spec.map (CommRingCat.ofHom (σ * τ).toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private noncomputable def galoisActionOnFiber [ConnectedSpace X]
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (Y : FiniteEtaleOver X) :
    finiteEtaleFiber sbar Y ≃ finiteEtaleFiber sbar Y where
  toFun p := ⟨
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1,
    by rw [Category.assoc, p.2, galois_comp_geometricPoint X sbar σ]⟩
  invFun p := ⟨
    Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom) ≫ p.1,
    by rw [Category.assoc, p.2, galois_comp_geometricPoint X sbar σ.symm]⟩
  left_inv p := by
    apply Subtype.ext
    change (Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom)) ≫ p.1 = p.1
    rw [← spec_map_galois_mul, ← AlgEquiv.aut_inv, inv_mul_cancel, spec_map_galois_one,
      Category.id_comp]
  right_inv p := by
    apply Subtype.ext
    change (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom)) ≫ p.1 = p.1
    rw [← spec_map_galois_mul, ← AlgEquiv.aut_inv, mul_inv_cancel, spec_map_galois_one,
      Category.id_comp]

private noncomputable def galoisActionAut [ConnectedSpace X]
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default))) :
    AlgebraicGeometry.EtaleFundamentalGroup X sbar :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (galoisActionOnFiber X sbar σ Y))
    (by
      intro Y Z f
      ext p
      apply Subtype.ext
      simp [galoisActionOnFiber, finiteEtaleFiberFunctor])

/-- Two elements of the étale fundamental group agree if they agree on all fibre points. -/
private theorem etaleFundamentalGroup_ext [ConnectedSpace X] {a b : EtaleFundamentalGroup X sbar}
    (h : ∀ (Y : FiniteEtaleOver X) (p : finiteEtaleFiber sbar Y),
      ((a.app Y).hom p).1 = ((b.app Y).hom p).1) : a = b := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply ConcreteCategory.hom_ext
  intro p
  exact Subtype.ext (h Y p)

private noncomputable def galoisActionHom [ConnectedSpace X] :
    Gal(sbar.residueField / X.residueField (sbar.hom default)) →*
      AlgebraicGeometry.EtaleFundamentalGroup X sbar where
  toFun := galoisActionAut X sbar
  map_one' := by
    apply etaleFundamentalGroup_ext
    intro Y p
    change Spec.map (CommRingCat.ofHom
      (1 : Gal(sbar.residueField / X.residueField (sbar.hom default))).toAlgHom.toRingHom) ≫
        p.1 = p.1
    rw [spec_map_galois_one, Category.id_comp]
  map_mul' σ τ := by
    apply etaleFundamentalGroup_ext
    intro Y p
    simp only [galoisActionAut, galoisActionOnFiber, Equiv.toIso]
    change Spec.map (CommRingCat.ofHom (σ * τ).toAlgHom.toRingHom) ≫ p.1 =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) ≫ p.1)
    rw [← Category.assoc, ← spec_map_galois_mul]

/-- An automorphism fixes the points of an intermediate field `E` exactly when the induced
endomorphism of `Spec Ω` is compatible with `Spec E → Spec Ω`. -/
private theorem spec_map_galois_comp_eq_iff {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) (σ : Gal(Ω/K)) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom E.val.toRingHom) =
      Spec.map (CommRingCat.ofHom E.val.toRingHom) ↔ ∀ x : E, σ x = x := by
  rw [← Spec.map_comp, Spec.map_injective.eq_iff, CommRingCat.hom_ext_iff]
  exact ⟨fun h x => DFunLike.congr_fun h x, fun h => RingHom.ext h⟩

private theorem finiteEtaleFiber_factorization
    (Y : FiniteEtaleOver X) (p : finiteEtaleFiber sbar Y) :
    ∃ (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField),
      FiniteDimensional (X.residueField (sbar.hom default)) E ∧
      ∃ q : Spec (.of E) ⟶ Y.left,
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ q = p.1 := by
  let : IsFinite Y.hom := Y.prop.1
  let j := X.fromSpecResidueField (sbar.hom default)
  let t := Spec.map (CommRingCat.ofHom
    (algebraMap (X.residueField (sbar.hom default)) sbar.residueField))
  have ht : t ≫ j = sbar.hom := geometricPoint_factorization X sbar
  let z := Limits.pullback.lift p.1 t (p.2.trans ht.symm)
  obtain ⟨E, hE, q, hq⟩ := finite_point_factorization
    (K := X.residueField (sbar.hom default)) (Ω := sbar.residueField)
    (Limits.pullback.snd Y.hom j) z
      (Limits.pullback.lift_snd p.1 t (p.2.trans ht.symm))
  refine ⟨E, hE, q ≫ Limits.pullback.fst Y.hom j, ?_⟩
  rw [← Category.assoc, hq]
  exact Limits.pullback.lift_fst p.1 t (p.2.trans ht.symm)

private theorem galoisActionOnFiber_eq_of_mem_fixingSubgroup [ConnectedSpace X]
    (Y : FiniteEtaleOver X) (p : finiteEtaleFiber sbar Y) :
    ∃ E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField,
      FiniteDimensional (X.residueField (sbar.hom default)) E ∧
      ∀ σ ∈ E.fixingSubgroup, galoisActionOnFiber X sbar σ Y p = p := by
  obtain ⟨E, hE, q, hq⟩ := finiteEtaleFiber_factorization X sbar Y p
  refine ⟨E, hE, fun σ hσ => ?_⟩
  apply Subtype.ext
  show Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1 = p.1
  rw [← hq, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  exact (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ x x.2

private theorem galoisActionHom_continuous [ConnectedSpace X] :
    Continuous (galoisActionHom X sbar) := by
  apply continuous_of_continuousAt_one (galoisActionHom X sbar)
  let F := finiteEtaleFiberFunctor sbar
  let : TopologicalSpace (Aut F) := Stacks.FundamentalGroup.functorAutomorphismTopology F
  let (Y : FiniteEtaleOver X) : TopologicalSpace (F.obj Y) := ⊥
  let (Y : FiniteEtaleOver X) : DiscreteTopology (F.obj Y) := ⟨rfl⟩
  show @ContinuousAt _ _ _
    (TopologicalSpace.induced (Stacks.FundamentalGroup.componentEmbedding F)
      (Stacks.FundamentalGroup.automorphismProductTopology F)) _ 1
  apply (Topology.IsInducing.continuousAt_iff
    (show Topology.IsInducing _ from ⟨rfl⟩)).mpr
  apply continuousAt_pi.mpr
  intro Y
  show @ContinuousAt _ _ _ (autTopology (E := F.obj Y))
    (fun σ => galoisActionOnFiber X sbar σ Y) 1
  apply (Topology.IsInducing.continuousAt_iff
    (show Topology.IsInducing _ from ⟨rfl⟩)).mpr
  apply continuousAt_pi.mpr
  intro p
  rw [ContinuousAt, nhds_discrete (F.obj Y),
    Filter.tendsto_pure]
  obtain ⟨E, hE, hfix⟩ := galoisActionOnFiber_eq_of_mem_fixingSubgroup X sbar Y p
  apply (krullTopology_mem_nhds_one_iff _ _ _).mpr
  refine ⟨E, hE, fun σ hσ => ?_⟩
  show galoisActionOnFiber X sbar σ Y p = galoisActionOnFiber X sbar 1 Y p
  rw [hfix σ hσ, hfix 1 E.fixingSubgroup.one_mem]

/-- The residue-field Galois action on the geometric fibre functor at `sbar`.
Its action is specified below, independently of any isomorphism of groups. -/
@[stacks 03VG "canonical generic-point homomorphism", no_expose]
public noncomputable def absoluteGaloisToFundamentalGroup
    [ConnectedSpace X] :
    Gal(sbar.residueField / X.residueField (sbar.hom default)) →ₜ*
      AlgebraicGeometry.EtaleFundamentalGroup X sbar :=
  ⟨galoisActionHom X sbar, galoisActionHom_continuous X sbar⟩

private theorem absoluteGaloisToFundamentalGroup_spec [ConnectedSpace X]
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (Y : FiniteEtaleOver X) (p : finiteEtaleFiber sbar Y) :
    (((absoluteGaloisToFundamentalGroup X sbar σ).app Y).hom p).1 =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1 :=
  rfl

private theorem normalization_point_fixed_of_mem_ker
    [ConnectedSpace X]
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (hE : FiniteEtaleNormalization X sbar E)
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (hσ : absoluteGaloisToFundamentalGroup X sbar σ = 1) :
    let f : Spec (.of E) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (sbar.hom default)) E)) ≫
        X.fromSpecResidueField (sbar.hom default)
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ f.toNormalization =
      Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ f.toNormalization := by
  let f : Spec (.of E) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField (sbar.hom default)) E)) ≫
      X.fromSpecResidueField (sbar.hom default)
  let Y : FiniteEtaleOver X :=
    MorphismProperty.Over.mk ⊤ f.fromNormalization hE.2
  let p : finiteEtaleFiber sbar Y :=
    ⟨Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ f.toNormalization, by
      show (Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ f.toNormalization) ≫
        f.fromNormalization = sbar.hom
      rw [Category.assoc, f.toNormalization_fromNormalization]
      dsimp only [f]
      rw [← Spec.map_comp_assoc]
      exact geometricPoint_factorization X sbar⟩
  have hact := absoluteGaloisToFundamentalGroup_spec X sbar σ Y p
  rw [hσ] at hact
  exact hact.symm

private theorem finiteEtaleNormalization_fixed_of_action_eq_one
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X)
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (hE : FiniteEtaleNormalization X sbar E)
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (hσ : absoluteGaloisToFundamentalGroup X sbar σ = 1) :
    ∀ x : E, σ x = x := by
  let : FiniteDimensional (X.residueField (sbar.hom default)) E := hE.1
  let f : Spec (.of E) ⟶ X :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField (sbar.hom default)) E)) ≫
      X.fromSpecResidueField (sbar.hom default)
  have : Mono f.toNormalization :=
    finiteExtension_toNormalization_mono_at_generic X (sbar.hom default) hgeneric E
  have hp := normalization_point_fixed_of_mem_ker X sbar E hE σ hσ
  exact (spec_map_galois_comp_eq_iff E σ).mp ((cancel_mono f.toNormalization).mp hp)

private theorem fixes_sSup_iff
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (S : Set (IntermediateField K Ω)) (σ : Gal(Ω/K)) :
    (∀ x : Ω, x ∈ sSup S → σ x = x) ↔
      ∀ E ∈ S, ∀ x : E, σ x = x := by
  constructor
  · intro h E hE x
    exact h x (le_sSup hE x.property)
  · intro h x hx
    let H : Subgroup Gal(Ω/K) := Subgroup.closure {σ}
    have hle : sSup S ≤ IntermediateField.fixedField H := by
      apply sSup_le
      intro E hE
      apply (IntermediateField.le_iff_le H E).mpr
      apply (Subgroup.closure_le E.fixingSubgroup).2
      rintro _ rfl
      exact (IntermediateField.mem_fixingSubgroup_iff E _).2 fun y hy => h E hE ⟨y, hy⟩
    have hx' : x ∈ IntermediateField.fixedField H := hle hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.subset_closure (by simp))

private theorem maximalEtaleExtension_fixed_of_action_eq_one
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X)
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (hσ : absoluteGaloisToFundamentalGroup X sbar σ = 1) :
    ∀ x : sbar.residueField, x ∈ maximalEtaleExtension X sbar → σ x = x :=
  (fixes_sSup_iff
    {E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField |
      FiniteEtaleNormalization X sbar E} σ).2
    fun E hE => finiteEtaleNormalization_fixed_of_action_eq_one X sbar hgeneric E hE σ hσ

private theorem exists_galois_action_lift
    [IsIntegral X] [IsNormal X]
    (x : X) (hx : x = genericPoint X) (Ω : Type u) [Field Ω]
    [Algebra (X.residueField x) Ω] [IsAlgClosed Ω] [IsAlgClosure (X.residueField x) Ω] :
    ∀ a : AlgebraicGeometry.EtaleFundamentalGroup X
        ((algebraicClosureGeometricPoint (X.residueField x) Ω).map
          (X.fromSpecResidueField x)),
      ∃ σ : Gal(Ω / X.residueField x),
        ∀ (Y : FiniteEtaleOver X)
          (p : finiteEtaleFiber
            ((algebraicClosureGeometricPoint (X.residueField x) Ω).map
              (X.fromSpecResidueField x)) Y),
          ((a.app Y).hom p).1 =
            Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1 := by
  subst x
  let K := X.residueField (genericPoint X)
  let L := separableClosure K Ω
  let : Algebra L Ω := L.val.toAlgebra
  intro a
  obtain ⟨τ, hτ⟩ := surjective_galoisToFundamentalGroup X L Ω a
  obtain ⟨σ, hσ⟩ := restrictNormalHom_separableClosure_surjective K Ω τ
  have ha : AlgebraicGeometry.galoisToFundamentalGroup X L Ω
      (AlgEquiv.restrictNormalHom L σ) = a :=
    (congrArg (AlgebraicGeometry.galoisToFundamentalGroup X L Ω) hσ).trans hτ
  refine ⟨σ, fun Y p => ?_⟩
  simpa only [ha] using galoisToFundamentalGroup_restrict_apply X L Ω σ Y p
@[sga "4½ Arcata 2.4.1" "partial"]
private theorem absoluteGaloisToFundamentalGroup_surjective
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (hgeneric : sbar.hom default = genericPoint X) :
    Function.Surjective (absoluteGaloisToFundamentalGroup X sbar) := by
  let : IsAlgClosure (X.residueField (sbar.hom default)) sbar.residueField := hs
  have h := exists_galois_action_lift X (sbar.hom default) hgeneric sbar.residueField
  have hh : Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField (sbar.hom default)) sbar.residueField)) ≫
      X.fromSpecResidueField (sbar.hom default) = sbar.hom :=
    geometricPoint_factorization X sbar
  let P (j : Spec (.of sbar.residueField) ⟶ X) : Prop :=
    ∀ a : AlgebraicGeometry.EtaleFundamentalGroup X ⟨sbar.residueField, j⟩,
      ∃ σ : Gal(sbar.residueField / X.residueField (sbar.hom default)),
        ∀ (Y : FiniteEtaleOver X)
          (p : finiteEtaleFiber ⟨sbar.residueField, j⟩ Y),
          ((a.app Y).hom p).1 =
            Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1
  have h' : P (Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField (sbar.hom default)) sbar.residueField)) ≫
      X.fromSpecResidueField (sbar.hom default)) := h
  have h'' : P sbar.hom := hh ▸ h'
  intro a
  obtain ⟨σ, hσ⟩ := h'' a
  refine ⟨σ, etaleFundamentalGroup_ext X sbar fun Y p => ?_⟩
  exact (absoluteGaloisToFundamentalGroup_spec X sbar σ Y p).trans (hσ Y p).symm

private theorem absoluteGaloisToFundamentalGroup_eq_one_of_fixes_maximal
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X)
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (hσ : ∀ x : sbar.residueField,
      x ∈ maximalEtaleExtension X sbar → σ x = x) :
    absoluteGaloisToFundamentalGroup X sbar σ = 1 := by
  apply etaleFundamentalGroup_ext
  intro Y p
  let : IsFinite Y.hom := Y.prop.1
  let : Etale Y.hom := Y.prop.2
  obtain ⟨W, hW, i, q, himono, hq⟩ := exists_integral_finiteEtale_factor X Y p.1
  let : IsIntegral W.left := hW
  let : IsFinite W.hom := W.prop.1
  let : Etale W.hom := W.prop.2
  let w : W.left ⟶ X := W.hom
  have hi : i.left ≫ Y.hom = W.hom := by simpa using i.w
  have hp : q ≫ W.hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.residueField (sbar.hom default)) sbar.residueField)) ≫
        X.fromSpecResidueField (sbar.hom default) := by
    rw [← hi, ← Category.assoc, hq, p.2]
    exact (geometricPoint_factorization X sbar).symm
  obtain ⟨E, hfin, hfe, j, hjmono, hj⟩ :=
    exists_finiteEtale_intermediate_factor_at X (sbar.hom default)
      hgeneric sbar.residueField (Y := W.left) w q hp
  have hE : FiniteEtaleNormalization X sbar E := ⟨hfin, hfe⟩
  have hEM : E ≤ maximalEtaleExtension X sbar :=
    le_sSup (Set.mem_ofPred.mpr hE)
  have hfield := (spec_map_galois_comp_eq_iff E σ).mpr fun x => hσ x (hEM x.property)
  have hact := absoluteGaloisToFundamentalGroup_spec X sbar σ Y p
  show ((((absoluteGaloisToFundamentalGroup X sbar) σ).app Y).hom p).1 = p.1
  rw [hact]
  show Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1 = p.1
  rw [← hq, ← hj]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ j ≫ i.left) hfield

private theorem absoluteGaloisToFundamentalGroup_eq_one_iff_fixes_maximal
    [IsIntegral X] [IsNormal X]
    (hgeneric : sbar.hom default = genericPoint X)
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default))) :
    absoluteGaloisToFundamentalGroup X sbar σ = 1 ↔
      ∀ x : sbar.residueField,
        x ∈ maximalEtaleExtension X sbar → σ x = x :=
  ⟨maximalEtaleExtension_fixed_of_action_eq_one X sbar hgeneric σ,
    absoluteGaloisToFundamentalGroup_eq_one_of_fixes_maximal X sbar hgeneric σ⟩

/-- The étale fundamental group is the Galois group of the maximal extension
unramified over the scheme, with canonicality specified below. -/
@[stacks 03VG "fundamental group", no_expose]
public noncomputable def fundamentalGroupIsoGalMaximalEtaleExtension
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (hgeneric : sbar.hom default = genericPoint X) :
    AlgebraicGeometry.EtaleFundamentalGroup X sbar ≃ₜ*
      Gal(maximalEtaleExtension X sbar / X.residueField (sbar.hom default)) :=
  letI : IsAlgClosure (X.residueField (sbar.hom default)) sbar.residueField := hs
  letI : CompactSpace Gal(sbar.residueField / X.residueField (sbar.hom default)) :=
    compactSpace_Gal_isAlgClosure (X.residueField (sbar.hom default)) sbar.residueField
  letI : Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) :=
    normal_maximalEtaleExtension X sbar hs hgeneric
  continuousMulEquivOfSurjectiveOfKerEq
    (absoluteGaloisToFundamentalGroup X sbar)
    (ContinuousMonoidHom.mk (AlgEquiv.restrictNormalHom (maximalEtaleExtension X sbar))
      (InfiniteGalois.restrictNormalHom_continuous (maximalEtaleExtension X sbar)))
    (absoluteGaloisToFundamentalGroup_surjective X sbar hs hgeneric)
    (AlgEquiv.restrictNormalHom_surjective (F := X.residueField (sbar.hom default))
      (K₁ := maximalEtaleExtension X sbar) (E := sbar.residueField))
    (by
      ext σ
      simp only [MonoidHom.mem_ker]
      exact (absoluteGaloisToFundamentalGroup_eq_one_iff_fixes_maximal X sbar hgeneric σ).trans
        (AlgEquiv.restrictNormal_eq_one_iff (maximalEtaleExtension X sbar) σ).symm)

/-- The canonical identification sends the generic-point homomorphism to
restriction of absolute Galois automorphisms to the maximal étale extension. -/
@[stacks 03VG "compatibility with restriction"]
public theorem fundamentalGroupIsoGalMaximalEtaleExtension_apply
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (hgeneric : sbar.hom default = genericPoint X) :
    letI : Normal (X.residueField (sbar.hom default))
        (maximalEtaleExtension X sbar) :=
      normal_maximalEtaleExtension X sbar hs hgeneric
    ∀ σ : Gal(sbar.residueField / X.residueField (sbar.hom default)),
      fundamentalGroupIsoGalMaximalEtaleExtension X sbar hs hgeneric
          (absoluteGaloisToFundamentalGroup X sbar σ) =
        (AlgEquiv.restrictNormalHom (maximalEtaleExtension X sbar)) σ := by
  let : IsAlgClosure (X.residueField (sbar.hom default)) sbar.residueField := hs
  let : CompactSpace Gal(sbar.residueField / X.residueField (sbar.hom default)) :=
    compactSpace_Gal_isAlgClosure (X.residueField (sbar.hom default)) sbar.residueField
  let : Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) :=
    normal_maximalEtaleExtension X sbar hs hgeneric
  intro σ
  exact continuousMulEquivOfSurjectiveOfKerEq_apply _ _ _ _ _ σ

public theorem fiber_stabilizer_of_mono_factor
    [ConnectedSpace X]
    (Y : FiniteEtaleOver X) (p : finiteEtaleFiber sbar Y)
    (E : IntermediateField (X.residueField (sbar.hom default)) sbar.residueField)
    (j : Spec (.of E) ⟶ Y.left) [Mono j]
    (hj : Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ j = p.1)
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default))) :
    (((absoluteGaloisToFundamentalGroup X sbar σ).app Y).hom p = p) ↔
      σ ∈ E.fixingSubgroup := by
  have hact := absoluteGaloisToFundamentalGroup_spec X sbar σ Y p
  rw [Subtype.ext_iff, hact, ← hj, ← Category.assoc, cancel_mono]
  rw [spec_map_galois_comp_eq_iff, IntermediateField.mem_fixingSubgroup_iff, Subtype.forall]

/-- A generic-field automorphism acts on a finite étale geometric fibre by
precomposition with the induced automorphism of the geometric point. -/
@[stacks 03VG "canonical generic-point action"]
public theorem absoluteGaloisToFundamentalGroup_apply
    [ConnectedSpace X]
    (σ : Gal(sbar.residueField/X.residueField (sbar.hom default)))
    (Y : FiniteEtaleOver X)
    (p : finiteEtaleFiber sbar Y) :
    ((((absoluteGaloisToFundamentalGroup X sbar) σ).app Y).hom p).1 =
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ p.1 :=
  absoluteGaloisToFundamentalGroup_spec X sbar σ Y p

end AlgebraicGeometry
