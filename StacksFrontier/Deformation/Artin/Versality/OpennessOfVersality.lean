module

public import StacksFrontier.Deformation.Artin.Versality.OpennessTower
public import StacksFrontier.AlgebraicGeometry.Properties.MaximalPoints

/-!
# Openness of versality

This is Stacks 0CXU: a category fibred in groupoids `𝒳` over the big fppf site of a locally
Noetherian scheme `S`, whose diagonal is representable by algebraic spaces, which satisfies (RS*),
is limit preserving, and for which square-zero systems as in Stacks 0CXT are effective, satisfies
openness of versality.

## Main results

* `Deformation.Artin.false_of_failedLifts`: the core of the argument, over an affine chart.
* `Deformation.Artin.isOpenVersality_of_isSquareZeroEffective`: **Stacks 0CXU**.

## Implementation notes

The source argues by contradiction: a sequence `u n` of finite type points at which `x` is not
versal, accumulating at `u₀`, gives by Stacks 0G2S objects `x ⟶ x₁ ⟶ x₂ ⟶ ⋯` over first order
thickenings of `U` admitting no local retraction, whose limit (hypothesis (4)) descends by limit
preservation to an object `ξ'` over a finite type thickening `U'`; the algebraic space `Z`
representing `(Sch/U) ×_{x, 𝒳, ξ'} (Sch/U')` is smooth over `U'` near `u₀` by Stacks 0CXM, and
a section of `Z ⟶ U'` over the first order thickening `U ⊆ U'` (Stacks 04AM) gives a retraction.

Here the thickenings are glued directly from failed Artinian lifting problems
(`Deformation.Artin.exists_tower`), and no section over `U'` is needed: once some `u n` lies in the
open set of points of `U` which the canonical section sends into the smooth locus of `Z`, the
failed lifting problem at `u n` is solved by
`Deformation.Artin.exists_lift_of_smoothChart`, exactly as in the proof of Stacks 0G2K.

The conclusion is the body of `Deformation.Artin.IsOpenVersality`, written out; the predicate
itself takes an argument asserting that `𝒳 ⟶ Sch/S` is fibred in groupoids over all schemes over
`S`, which fails for the bounded site (compare
`Deformation.Artin.isOpenVersality_of_naiveObstructionTheory`).

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))

/-- **The limit object of the proof of Stacks 0CXU.** Glueing a sequence of failed lifting
problems `P n` for `x` over `Spec R₀` by (RS*) and passing to the limit by effectiveness of
square-zero systems gives an object `ξ` over the spectrum of the limit of the stages, with arrows
`x ⟶ ξ` and `z n ⟶ ξ` over the spectra of the projections, compatible with the lifting
problems. -/
theorem exists_limit_of_failedLifts
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (heff : IsSquareZeroEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (P : ℕ → FailedLift B S hS 𝒳 iΛ hR₀ x)
    (hRlim : B.Contains (Spec (.of (Stacks.CompatibleTuples.limit (towerφ P) (towerf P))))) :
    ∃ (ξ : 𝒳.val.obj) (_ : 𝒳.val.p.obj ξ = siteObject B S hS hRlim
        (Spec.map (CommRingCat.ofHom (algebraMap Λ
          (Stacks.CompatibleTuples.limit (towerφ P) (towerf P)))) ≫ iΛ))
      (κ : x ⟶ ξ) (ζ : ∀ n, (P n).z ⟶ ξ),
      𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ hRlim
        (Stacks.CompatibleTuples.limitFst (towerφ P) (towerf P))) κ ∧
      (∀ n, IsFailedLiftZArrow B S hS (P n) hRlim
        (Stacks.CompatibleTuples.limitEval (towerφ P) (towerf P) n) (ζ n)) ∧
      (∀ n, (P n).a ≫ κ = (P n).i ≫ ζ n) := by
  classical
  let p := 𝒳.val.p
  have hf : ∀ k, Function.Surjective (towerf P k) := fun k => (P k).surjective
  have hker : ∀ k, RingHom.ker (towerf P k).toRingHom ^ 2 = ⊥ := fun k => (P k).ker_sq
  have hRn : ∀ n, B.Contains (Spec (.of (Stacks.CompatibleTuples.stage (towerφ P) (towerf P) n))) :=
    fun n => contains_spec_of_surjective B
      (Stacks.CompatibleTuples.proj (towerφ P) (towerf P) n).toRingHom
      (Stacks.CompatibleTuples.surjective_proj hf n) hRlim
  obtain ⟨obj, hobj, step, toObj, sz, hstep, htoObj, htoObj_succ, hsz, hcompat⟩ :=
    exists_tower B S hS 𝒳 iΛ hR₀ x P hRS hx hRn
  obtain ⟨ξ, hξ, ι, hι, hιw⟩ := exists_limit_object B S hS 𝒳 iΛ (towerφ P) (towerf P) heff hf
    hker hRn hRlim obj hobj step hstep
  have hιtoObj : ∀ n, toObj n ≫ ι n = toObj 0 ≫ ι 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [htoObj_succ, Category.assoc, hιw, ih]
  refine ⟨ξ, hξ, toObj 0 ≫ ι 0, fun n => sz n ≫ ι (n + 1), ?_, fun n => ?_, fun n => ?_⟩
  · have h := isHomLift_specAlgSiteHom_comp B S hS p iΛ (htoObj 0) (hι 0)
    rw [Stacks.CompatibleTuples.stageFst_comp_proj] at h
    exact h
  · have h := isHomLift_specAlgSiteHom_comp B S hS p iΛ (hsz n) (hι (n + 1))
    rw [show (towerLast P n).comp (Stacks.CompatibleTuples.proj (towerφ P) (towerf P) (n + 1)) =
      Stacks.CompatibleTuples.limitEval (towerφ P) (towerf P) n from
        Stacks.CompatibleTuples.stageLast_comp_proj _ _ n] at h
    exact h
  · rw [← hιtoObj (n + 1), ← Category.assoc, hcompat n, Category.assoc]

/-- **The descended thickening of the proof of Stacks 0CXU.** Glueing a sequence of failed
lifting problems `P n` for `x` over `Spec R₀` by (RS*), passing to the limit by effectiveness of
square-zero systems and descending by limit preservation gives a finite type `Λ`-algebra `R'`
with a surjection `R' ⟶ R₀` and maps `R' ⟶ A' n` agreeing in `A n`, an object `x'` over
`Spec R'`, and arrows `x ⟶ x'`, `z n ⟶ x'` over their spectra, compatible with the lifting
problems. -/
theorem exists_descended_thickening
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    (heff : IsSquareZeroEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hΛ : B.Contains (Spec (.of Λ)))
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] [Algebra.FiniteType Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (P : ℕ → FailedLift B S hS 𝒳 iΛ hR₀ x) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra Λ R') (_ : Algebra.FiniteType Λ R')
      (hR' : B.Contains (Spec (.of R'))) (gU : R' →ₐ[Λ] R₀) (gZ : ∀ n, R' →ₐ[Λ] (P n).A')
      (_ : Function.Surjective gU) (_ : ∀ n, (P n).φ.comp gU = (P n).f.comp (gZ n))
      (x' : 𝒳.val.obj)
      (_ : 𝒳.val.p.obj x' =
        siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ))
      (κ : x ⟶ x') (ζ : ∀ n, (P n).z ⟶ x'),
      𝒳.val.p.IsHomLift (specAlgSiteHom B S hS iΛ hR₀ hR' gU) κ ∧
      (∀ n, IsFailedLiftZArrow B S hS (P n) hR' (gZ n) (ζ n)) ∧
      (∀ n, (P n).a ≫ κ = (P n).i ≫ ζ n) := by
  classical
  let p := 𝒳.val.p
  have hf : ∀ k, Function.Surjective (towerf P k) := fun k => (P k).surjective
  have hker : ∀ k, RingHom.ker (towerf P k).toRingHom ^ 2 = ⊥ := fun k => (P k).ker_sq
  have hRlim : B.Contains (Spec (.of (Stacks.CompatibleTuples.limit (towerφ P) (towerf P)))) :=
    contains_spec_compatibleTuples_limit B (towerφ P) (towerf P) hR₀ (fun n => (P n).memA')
  obtain ⟨ξ, hξ, κL, ζL, hκL, hζL, hcompatL⟩ :=
    exists_limit_of_failedLifts B S hS 𝒳 hRS heff iΛ hR₀ x hx P hRlim
  -- descent to a finite type thickening
  let I : Ideal (Stacks.CompatibleTuples.limit (towerφ P) (towerf P)) :=
    RingHom.ker (Stacks.CompatibleTuples.limitFst (towerφ P) (towerf P)).toRingHom
  have hI : I ^ 2 = ⊥ := Stacks.CompatibleTuples.ker_limitFst_sq hker
  have : Algebra.FiniteType Λ (Stacks.CompatibleTuples.limit (towerφ P) (towerf P) ⧸ I) :=
    Algebra.FiniteType.equiv inferInstance (Ideal.quotientKerAlgEquivOfSurjective
      (f := Stacks.CompatibleTuples.limitFst (towerφ P) (towerf P))
      (Stacks.CompatibleTuples.surjective_limitFst hf)).symm
  obtain ⟨Asub, x'f, δ, hδ, -⟩ := exists_finiteTypeCover_thickening_descent B S hS 𝒳 hlim iΛ hΛ
    hRlim I hI ⟨ξ, hξ⟩
  let : Algebra.FiniteType Λ Asub.1 := (Subalgebra.fg_iff_finiteType Asub.1).1 Asub.2.1
  have hR' : B.Contains (Spec (.of Asub.1)) := contains_stage B hΛ Asub.1 Asub.2.1
  have hx' : p.obj x'f.1 =
      siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ Asub.1)) ≫ iΛ) := x'f.2
  have hδ' : p.IsHomLift (specAlgSiteHom B S hS iΛ hRlim hR' Asub.1.val) δ := hδ
  let gU : Asub.1 →ₐ[Λ] R₀ :=
    (Stacks.CompatibleTuples.limitFst (towerφ P) (towerf P)).comp Asub.1.val
  let gZ : ∀ n, Asub.1 →ₐ[Λ] (P n).A' := fun n =>
    (Stacks.CompatibleTuples.limitEval (towerφ P) (towerf P) n).comp Asub.1.val
  have hgU : Function.Surjective gU := by
    intro r₀
    obtain ⟨t, ht⟩ := Stacks.CompatibleTuples.surjective_limitFst hf r₀
    obtain ⟨b, hb⟩ := Asub.2.2 (Ideal.Quotient.mk I t)
    refine ⟨b, ?_⟩
    have : (b : Stacks.CompatibleTuples.limit (towerφ P) (towerf P)) - t ∈ I :=
      Ideal.Quotient.eq.1 hb
    have h0 : Stacks.CompatibleTuples.limitFst (towerφ P) (towerf P)
        ((b : Stacks.CompatibleTuples.limit (towerφ P) (towerf P)) - t) = 0 := this
    rw [_root_.map_sub, sub_eq_zero] at h0
    change Stacks.CompatibleTuples.limitFst (towerφ P) (towerf P)
      (b : Stacks.CompatibleTuples.limit (towerφ P) (towerf P)) = r₀
    rw [h0, ht]
  have hcomm : ∀ n, (P n).φ.comp gU = (P n).f.comp (gZ n) := by
    intro n
    ext b
    exact congrArg (fun g : Stacks.CompatibleTuples.limit (towerφ P) (towerf P) →ₐ[Λ] (P n).A =>
      g (b : _)) (Stacks.CompatibleTuples.comp_limitEval (towerφ P) (towerf P) n)
  refine ⟨Asub.1, inferInstance, inferInstance, inferInstance, hR', gU, gZ, hgU, hcomm, x'f.1, hx',
    κL ≫ δ, fun n => ζL n ≫ δ, isHomLift_specAlgSiteHom_comp B S hS p iΛ hκL hδ',
    fun n => isHomLift_specAlgSiteHom_comp B S hS p iΛ (hζL n) hδ', fun n => ?_⟩
  rw [← Category.assoc, hcompatL n, Category.assoc]

open BaseChange in
/-- **The core of Stacks 0CXU.** Let `x` over `Spec R₀`, with `R₀` of finite type over `Λ` and
`Spec Λ ⊆ S` an affine open, be versal at a finite type point `u₀`, and let `P n` be lifting
problems for `x` without solution, at points `u n` such that every open neighbourhood of `u₀`
contains some `u n`. This is impossible. -/
theorem false_of_failedLifts [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    (heff : IsSquareZeroEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hΛ : B.Contains (Spec (.of Λ)))
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] [Algebra.FiniteType Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (u₀ : Spec (.of R₀)) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x (congrArg (Over.post B.inclusion).obj hx))
    (P : ℕ → FailedLift B S hS 𝒳 iΛ hR₀ x)
    (hdense : ∀ V : Set (Spec (.of R₀)), IsOpen V → u₀ ∈ V → ∃ n, (P n).point ∈ V) : False := by
  classical
  obtain ⟨R', _, _, _, hR', gU, gZ, hgU, hcomm, x', hx', κ, ζ, hκ, hζ, hcompatζ⟩ :=
    exists_descended_thickening B S hS 𝒳 hRS hlim heff iΛ hΛ hR₀ x hx P
  -- the smooth locus of the base change
  let UaS := siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)
  let U'S := siteObject B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ iΛ)
  have hlftAlg : ∀ (T : Type u) [CommRing T] [Algebra Λ T] [Algebra.FiniteType Λ T],
      LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ T)) ≫ iΛ) := by
    intro T _ _ _
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ T))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    infer_instance
  have : LocallyOfFiniteType (B.inclusion.map UaS.hom) := hlftAlg R₀
  have : LocallyOfFiniteType (B.inclusion.map U'S.hom) := hlftAlg R'
  let gS : UaS ⟶ U'S := specAlgSiteHom B S hS iΛ hR₀ hR' gU
  have hgmono : Mono (B.inclusion.map gS.left) := by
    have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom gU.toRingHom) hgU
    change Mono (Spec.map (CommRingCat.ofHom gU.toRingHom))
    infer_instance
  obtain ⟨F, hF, e, s₀, Z₀, hZ₀, hsmZ, hsec, V, hV, hu₀V, hfac⟩ :=
    exists_smooth_openSubspace_isOpen_of_isVersalAt B S hS 𝒳 hΔ hRS hlim gS hgmono hx hx' κ hκ
      u₀ hu₀ hversal
  obtain ⟨n, hn⟩ := hdense V hV hu₀V
  -- the failed lifting problem at `u n` has a solution
  obtain ⟨b, hb⟩ := exists_lift_of_smoothChart B S hS 𝒳 hRS iΛ hR₀ hR' (P n).f (P n).surjective
    (P n).ker_sq (P n).memA (P n).memA' (P n).φ gU (gZ n) (hcomm n)
    (mono_of_mono_inclusion_map B S hS gS hgmono) hx hx' (P n).hy (P n).hz (P n).i (P n).hi
    (P n).a (P n).ha κ hκ (ζ n) (hζ n) (hcompatζ n) F e s₀ Z₀ hZ₀ hsmZ hsec (P n).point
    (fun Y h hh => hfac Y h fun y => (hh y).symm ▸ hn) (P n).point_eq
  exact (P n).not_lift ⟨b, hb⟩

/-! ### A failed lifting problem at a point where `x` is not versal -/

/-- **A point where `x` is not versal carries a failed lifting problem.** If `x` over `Spec R₀`
is not versal at `t`, there is a small extension of Artinian local `Λ`-algebras with residue field
`κ(t)` and a lifting problem along it at `t` without solution. -/
theorem exists_failedLift_of_not_isVersalAt
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (t : Spec (.of R₀))
    (ht : ¬ IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) t x (congrArg (Over.post B.inclusion).obj hx)) :
    ∃ P : FailedLift B S hS 𝒳 iΛ hR₀ x, P.point = t := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let q := p ⋙ Over.post B.inclusion
  let U' : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ)
  have hx' : q.obj x = U' := congrArg (Over.post B.inclusion).obj hx
  have hH' : Set.range (U'.left.fromSpecResidueField t ≫ U'.hom).base ⊆ Set.range iΛ.base :=
    range_residuePoint_subset S U'.hom t iΛ ⟨_, rfl⟩
  let : Algebra Λ (U'.left.residueField t) := chartResidueAlgebra iΛ U' t hH'
  rw [isVersalAt_iff_liftsAtResiduePoint_chart iΛ U' t q x hx'
    (algebraMap_chartResidueAlgebra iΛ U' t hH')] at ht
  have hsmall : ¬ ∀ {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ (U'.left.residueField t)}
      (f : A' ⟶ A), InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      LiftsAlong (k := U'.left.residueField t) B S hS p iΛ U' x hx'
        (U'.left.fromSpecResidueField t) f :=
    fun H => ht (liftsAtResiduePoint_of_isSmallExtension (k := U'.left.residueField t) B S hS p hp
      iΛ U' x hx' _ H)
  simp only [not_forall] at hsmall
  obtain ⟨A, A', f, hf, hfail⟩ := hsmall
  simp only [not_exists] at hfail
  obtain ⟨y, z, hy, hz, i, hi, a, ha, hno⟩ := hfail
  have hcont : ∀ (w : 𝒳.val.obj) (X : Scheme), B.inclusion.obj (p.obj w).left = X →
      B.Contains X := fun w X h => h ▸ (p.obj w).left.2
  have hA : B.Contains (Spec (.of A)) := hcont y _ (congrArg Over.left hy)
  have hA' : B.Contains (Spec (.of A')) := hcont z _ (congrArg Over.left hz)
  have hyS := eq_siteObject_of_post B S hS hA _ (p.obj y) hy
  have hzS := eq_siteObject_of_post B S hS hA' _ (p.obj z) hz
  obtain ⟨φ, hφ⟩ := exists_algHom_of_specMap S iΛ (schemeMap q hy hx' a) (schemeMap_over q hy _ a)
  have ha' : p.IsHomLift (specAlgSiteHom B S hS iΛ hA hR₀ φ) a :=
    isHomLift_of_schemeMap B S hS p hyS hx _ a (by rw [toScheme_specSiteHom, hφ])
  have hi' : p.IsHomLift (specAlgSiteHom B S hS iΛ hA hA' f.hom) i :=
    isHomLift_of_schemeMap B S hS p hyS hzS _ i (by rw [toScheme_specSiteHom]; exact hi)
  have hsubA : ∀ c d : Spec (.of A), c = d := subsingleton_spec_of_isArtinianRing A
  have hpt : ∀ t', Spec.map (CommRingCat.ofHom φ.toRingHom) t' = t := by
    intro t'
    rw [hsubA t' ((Spec.map (CommRingCat.ofHom (residueMap A))) (IsLocalRing.closedPoint _))]
    have h := congrArg (fun m : Spec (.of (U'.left.residueField t)) ⟶ Spec (.of R₀) =>
      m (IsLocalRing.closedPoint _)) ha
    simp only at h
    rw [← hφ] at h
    exact h.trans (Scheme.fromSpecResidueField_apply _ _)
  have hfs : Function.Surjective f.hom := hf.2.2.2.2.1
  let P : FailedLift B S hS 𝒳 iΛ hR₀ x :=
    { A := A
      A' := A'
      f := f.hom
      surjective := hfs
      ker_sq := smallExtension_kernel_sq_zero f hf
      memA := hA
      memA' := hA'
      φ := φ
      point := t
      point_eq := hpt
      y := y
      z := z
      hy := hyS
      hz := hzS
      i := i
      hi := hi'
      a := a
      ha := ha'
      not_lift := fun ⟨b, hb⟩ => hno b hb }
  exact ⟨P, rfl⟩

/-! ### Accumulating sequences of points -/

/-- **A countable sequence accumulating at a point.** In the spectrum of a Noetherian ring, let
`w₀` lie in the closure of a set `E` none of whose points specializes to `w₀`. Then there is a
sequence of points of `E` meeting every open neighbourhood of `w₀`. This is where Stacks 0G2F
enters. -/
theorem exists_seq_mem_open_of_mem_closure {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : Set (PrimeSpectrum R)) (w₀ : PrimeSpectrum R) (hw : w₀ ∈ closure E)
    (hE : ∀ e ∈ E, ¬ e ⤳ w₀) :
    ∃ u : ℕ → PrimeSpectrum R, (∀ n, u n ∈ E) ∧
      ∀ V : Set (PrimeSpectrum R), IsOpen V → w₀ ∈ V → ∃ n, u n ∈ V := by
  classical
  let J := PrimeSpectrum.vanishingIdeal E
  let ι := PrimeSpectrum.comap (Ideal.Quotient.mk J)
  have hι : Topology.IsClosedEmbedding ι :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hrange : Set.range ι = closure E := by
    rw [range_comap_of_surjective (R := R) (S := R ⧸ J) _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hEι : E ⊆ Set.range ι := hrange ▸ subset_closure
  let T : Set (PrimeSpectrum (R ⧸ J)) := ι ⁻¹' E
  have hTE : ι '' T = E := Set.image_preimage_eq_of_subset hEι
  have hTdense : Dense T := by
    intro q
    have hq : ι q ∈ closure E := hrange ▸ ⟨q, rfl⟩
    rw [← hTE, hι.closure_image_eq] at hq
    obtain ⟨q', hq', hqq'⟩ := hq
    rwa [hι.injective hqq'] at hq'
  have hTinf : T.Infinite := by
    intro hfin
    have hEfin : E.Finite := hTE ▸ hfin.image ι
    have hcl : closure E = ⋃ e ∈ E, closure {e} := by
      conv_lhs => rw [← Set.biUnion_of_singleton E]
      exact hEfin.closure_biUnion _
    rw [hcl] at hw
    obtain ⟨e, he, hwe⟩ := Set.mem_iUnion₂.mp hw
    exact hE e he (specializes_iff_mem_closure.mpr hwe)
  obtain ⟨E'', hE''T, hE''c, hE''d⟩ := AlgebraicGeometry.exists_countable_dense_subset
    (Spec (.of (R ⧸ J))) T hTinf hTdense
  have hE''ne : E''.Nonempty := by
    obtain ⟨t, -⟩ := hTinf.nonempty
    have : Nonempty (Spec (.of (R ⧸ J))) := ⟨t⟩
    exact hE''d.nonempty
  obtain ⟨u, hu⟩ := (hE''c.image ι).exists_eq_range (hE''ne.image ι)
  refine ⟨u, fun n => ?_, fun V hV hwV => ?_⟩
  · obtain ⟨e, he, hee⟩ : u n ∈ ι '' E'' := hu ▸ ⟨n, rfl⟩
    rw [← hee]
    exact hE''T he
  · obtain ⟨q, hq⟩ : w₀ ∈ Set.range ι := hrange ▸ hw
    obtain ⟨e, heV, heE⟩ := hE''d.inter_open_nonempty (ι ⁻¹' V) (hV.preimage hι.continuous)
      ⟨q, show ι q ∈ V from hq ▸ hwV⟩
    obtain ⟨n, hn⟩ : ι e ∈ Set.range u := hu ▸ ⟨e, heE, rfl⟩
    exact ⟨n, hn ▸ heV⟩

/-! ### Openness of versality -/

/-- **Openness of versality over an affine chart.** Let `x` over `Spec R₀`, with `R₀` of finite
type over `Λ` and `Spec Λ ⊆ S` an affine open, be versal at a finite type point `u₀`. Then `x` is
versal at every finite type point of an open neighbourhood of `u₀`. -/
theorem exists_isOpen_isVersalAt_chart [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    (heff : IsSquareZeroEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hΛ : B.Contains (Spec (.of Λ)))
    {R₀ : Type u} [CommRing R₀] [Algebra Λ R₀] [Algebra.FiniteType Λ R₀]
    (hR₀ : B.Contains (Spec (.of R₀)))
    (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x =
      siteObject B S hS hR₀ (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
    (u₀ : Spec (.of R₀)) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x (congrArg (Over.post B.inclusion).obj hx)) :
    ∃ V : Set (Spec (.of R₀)), IsOpen V ∧ u₀ ∈ V ∧ ∀ t ∈ V, AlgebraicGeometry.IsFiniteTypePoint t →
      IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
        (𝒳.val.p ⋙ Over.post B.inclusion) t x (congrArg (Over.post B.inclusion).obj hx) := by
  classical
  by_contra hcon
  -- the finite type points where `x` is not versal accumulate at `u₀`
  let E : Set (Spec (.of R₀)) := {t | AlgebraicGeometry.IsFiniteTypePoint t ∧
    ¬ IsVersalAt (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ R₀)) ≫ iΛ))
      (𝒳.val.p ⋙ Over.post B.inclusion) t x (congrArg (Over.post B.inclusion).obj hx)}
  have hw : u₀ ∈ closure E := by
    rw [mem_closure_iff]
    intro o ho hu₀o
    by_contra h
    refine hcon ⟨o, ho, hu₀o, fun t ht hft => ?_⟩
    by_contra hnv
    exact h ⟨t, ht, hft, hnv⟩
  have hE : ∀ e ∈ E, ¬ e ⤳ u₀ := fun e he hspec =>
    he.2 (isVersalAt_of_specializes_chart B S hS 𝒳 hΔ hRS hlim iΛ hΛ hR₀ x hx u₀ hu₀ hversal e
      hspec)
  have : IsLocallyNoetherian (Spec (.of Λ)) := isLocallyNoetherian_of_isOpenImmersion iΛ
  have : IsNoetherianRing Λ := isLocallyNoetherian_Spec (R := .of Λ) |>.mp inferInstance
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing Λ R₀
  obtain ⟨u, huE, hu⟩ := exists_seq_mem_open_of_mem_closure (R := R₀) E u₀ hw hE
  -- a failed lifting problem at every `u n`
  choose P hPpt using fun n =>
    exists_failedLift_of_not_isVersalAt B S hS 𝒳 iΛ hR₀ x hx (u n) (huE n).2
  exact false_of_failedLifts B S hS 𝒳 hΔ hRS hlim heff iΛ hΛ hR₀ x hx u₀ hu₀ hversal P
    (fun V hV hu₀V => by
      obtain ⟨n, hn⟩ := hu V hV hu₀V
      exact ⟨n, (hPpt n).symm ▸ hn⟩)

/-- **Stacks 0CXU.** Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in
groupoids over the big fppf site of `S` such that

1. the diagonal of `𝒳` is representable by algebraic spaces,
2. `𝒳` has (RS*),
3. `𝒳` is limit preserving,
4. systems of objects as in Stacks 0CXT, over inverse systems of algebras whose transition maps
   are surjective with square-zero kernels, are effective.

Then `𝒳` satisfies openness of versality: if `x` is an object of `𝒳` over a scheme `U` locally of
finite type over `S`, versal at a finite type point `u₀` of `U`, then `x` is versal at every finite
type point of an open neighbourhood of `u₀`.

The conclusion is the body of `Deformation.Artin.IsOpenVersality` (Stacks 07XQ), written out; see
the implementation notes of this file. -/
@[stacks 0CXU]
public theorem isOpenVersality_of_isSquareZeroEffective [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    (heff : IsSquareZeroEffective B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (U : Over S) (hUft : LocallyOfFiniteType U.hom) (x : 𝒳.val.obj)
    (hx : (𝒳.val.p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x hx) :
    ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
      ∀ u ∈ V.1, AlgebraicGeometry.IsFiniteTypePoint u →
        IsVersalAt U (𝒳.val.p ⋙ Over.post B.inclusion) u x hx := by
  classical
  subst hx
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x).hom) := hUft
  obtain ⟨D, w₀, hw₀, -⟩ := exists_chartedData B S hS p x (p.obj x).left.2 u₀ hu₀
  obtain ⟨obj, ρ, hρ⟩ := exists_restrictedLift B S hS p x D.mem D.immersion hp
  let iΛ := D.chart.immersion
  have hΛ : B.Contains (Spec (.of D.chart.ring)) :=
    contains_of_isOpenImmersion B iΛ inferInstance hS
  have hxa : p.obj obj.1 = siteObject B S hS D.mem
      (Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring)) ≫ iΛ) := by
    refine obj.2.trans (eq_siteObject_of_post B S hS D.mem _ _ ?_)
    change Over.mk (restrictedSiteAlgebra B S hS p x D.mem D.immersion).toScheme = _
    rw [toScheme_restrictedSiteAlgebra, ← D.factorization]
    rfl
  let U' : Over S := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring)) ≫ iΛ)
  have hx' : (p ⋙ Over.post B.inclusion).obj obj.1 = U' := congrArg (Over.post B.inclusion).obj hxa
  have hρ' : schemeMap (p ⋙ Over.post B.inclusion) hx' rfl ρ = D.immersion := hρ
  have hrange : ∀ t : Spec (CommRingCat.of D.ring),
      (B.inclusion.map (p.obj x).hom).base (D.immersion.base t) ∈ Set.range iΛ.base := fun t =>
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap D.chart.ring D.ring))).base t,
      congrArg (fun m : Spec (CommRingCat.of D.ring) ⟶ S => m.base t) D.factorization⟩
  have hH : ∀ t : Spec (CommRingCat.of D.ring),
      Set.range (((p ⋙ Over.post B.inclusion).obj x).left.fromSpecResidueField
          (D.immersion.base t) ≫ ((p ⋙ Over.post B.inclusion).obj x).hom).base ⊆
        Set.range iΛ.base := fun t =>
    range_residuePoint_subset S _ _ iΛ (hrange t)
  have hH' : ∀ t : Spec (CommRingCat.of D.ring),
      Set.range (U'.left.fromSpecResidueField t ≫ U'.hom).base ⊆ Set.range iΛ.base := by
    intro t
    refine range_residuePoint_subset S U'.hom t iΛ ?_
    exact ⟨_, rfl⟩
  have hiff : ∀ t : Spec (CommRingCat.of D.ring),
      IsVersalAt U' (p ⋙ Over.post B.inclusion) t obj.1 hx' ↔
        IsVersalAt ((p ⋙ Over.post B.inclusion).obj x) (p ⋙ Over.post B.inclusion)
          (D.immersion.base t) x rfl := fun t =>
    isVersalAt_iff_restrict B S hS p hp iΛ rfl hx' ρ D.immersion D.isOpenImmersion hρ' t
      (hH t) (hH' t)
  have hw₀ft : AlgebraicGeometry.IsFiniteTypePoint w₀ :=
    isFiniteTypePoint_of_isOpenImmersion D.immersion w₀ (by rw [hw₀]; exact hu₀)
  have hversal' : IsVersalAt U' (p ⋙ Over.post B.inclusion) w₀ obj.1 hx' := by
    rw [hiff w₀, hw₀]
    exact hversal
  obtain ⟨V', hV'open, hw₀V', hV'⟩ := exists_isOpen_isVersalAt_chart B S hS 𝒳 hΔ hRS hlim heff
    iΛ hΛ D.mem obj.1 hxa w₀ hw₀ft hversal'
  refine ⟨⟨D.immersion.base '' V', D.immersion.isOpenEmbedding.isOpenMap V' hV'open⟩,
    ⟨w₀, hw₀V', hw₀⟩, ?_⟩
  rintro u ⟨t, htV', rfl⟩ hft
  exact (hiff t).mp (hV' t htV' (isFiniteTypePoint_of_isOpenImmersion D.immersion t hft))

end Deformation.Artin

end
