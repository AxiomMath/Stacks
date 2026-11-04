module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso

/-!
# `H⁰` and the genus of the fibres of a proper flat family of schemes

Let `f : X ⟶ S` be a proper, flat morphism of schemes of finite presentation and let
`E = Rf_*𝒪_X`, a perfect object of `D(𝒪_S)` (Stacks 0B91). At a field-valued point
`p : Spec K ⟶ S` with fibre `X_K = X ×_S Spec K`, the derived-fibre Betti numbers of `E` are the
dimensions of the cohomology of `𝒪_{X_K}` and the derived-fibre Euler characteristic of `E` is
`χ(X_K, 𝒪)` (cohomology and base change, Stacks 0B91 and 0BDN).

From the upper semicontinuity of the Betti numbers (Stacks 0BDI) and the openness of the image
of `f`, the points at which `K = H⁰(X_K, 𝒪_{X_K})` form an open subset of `S`; and from the local
constancy of the Euler characteristic (Stacks 0BDJ) together with `χ(𝒪) = 1 - g` for a proper
curve with `H⁰ = K`, the genus of the fibres is locally constant on the points whose fibres are
such curves. These are the scheme cases of Stacks 0E0R at `i = 0` and of the local constancy of
the genus used in Stacks 0E6V and 0E6K.

## Main results

* `AlgebraicGeometry.C1590Private.derivedFiberBetti_zero_eq_finrank_globalSections`: the zeroth
  derived-fibre Betti number of `Rf_*𝒪_X` at a field-valued point is `dim_K Γ(X_K, 𝒪)`.
* `AlgebraicGeometry.C1590Private.chiDerivedFibre_eq_one_sub_genus`: the derived-fibre Euler
  characteristic at a field-valued point whose fibre is a curve with `H⁰ = K` is `1 - g`.
* `AlgebraicGeometry.C1590Private.bijective_iff_derivedFiberBetti_zero_eq_one`: `K = H⁰(X_K, 𝒪)`
  exactly when the zeroth derived-fibre Betti number at the point is one.
* `AlgebraicGeometry.C1590Private.isOpen_setOf_derivedFiberBetti_zero_eq_one`: the locus where
  that Betti number is one is open.

## References

* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
* [Stacks Project, Tag 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

open ProperFlatFibreEulerCharacteristic

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] (hf : FinitePresentation f)

include hf

/-- `Rf_*𝒪_X` of a proper flat morphism of finite presentation is perfect (Stacks 0B91). -/
theorem isPerfect_derivedPushforwardModule_unit :
    RingedSpace.IsPerfect.{u, u + 1} (X := S.toRingedSpace)
      (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf)) :=
  perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hf inferInstance _
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X) (isFlatOver_unit_of_flat f)

/-- `Rf_*𝒪_X` of a proper flat morphism of finite presentation is pseudo-coherent. -/
theorem isPseudoCoherent_derivedPushforwardModule_unit :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf)) :=
  DerivedFibreBetti.isPseudoCoherent_of_isPerfect _ (isPerfect_derivedPushforwardModule_unit f hf)

omit hf in
/-- The cohomology over a field of the pullback of the structure sheaf along a morphism is that of
the structure sheaf. -/
theorem finrank_cohomologyOverField_pullback_unit (K : Type u) [Field K] {Y : Scheme.{u}}
    (q : Y ⟶ X) (g : Y ⟶ Spec (.of K)) (n : ℕ) :
    Module.finrank K (cohomologyOverField K g
        ((Scheme.Modules.pullback q).obj (SheafOfModules.unit X.ringCatSheaf)) n) =
      Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Y.ringCatSheaf) n) :=
  ((ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (((SheafOfModules.evaluation Y.ringCatSheaf
        (Opposite.op (⊤ : Y.Opens))).rightDerived n).mapIso
        (Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom))).toLinearEquiv.finrank_eq

/-- **Cohomology and base change in degree `n ≥ 0` at a field-valued point.** For a cartesian
square with `p : Spec K ⟶ S`, the `n`-th derived-fibre Betti number of `Rf_*𝒪_X` at the image of
the point of `Spec K` is `dim_K Hⁿ(Y, 𝒪_Y)` for the base change `Y = X ×_S Spec K`. -/
theorem derivedFiberBetti_eq_finrank_cohomologyOverField (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ X) (g : Y ⟶ Spec (.of K))
    (hsq : IsPullback q g f p) (pt : Spec (.of K)) (n : ℕ) :
    DerivedFibreBetti.derivedFiberBetti S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) n (p.base pt) =
      Module.finrank K (cohomologyOverField K g (SheafOfModules.unit Y.ringCatSheaf) n) := by
  have hF := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have hflat := isFlatOver_unit_of_flat f
  have hpc := isPseudoCoherent_derivedPushforwardModule_unit f hf
  obtain ⟨e⟩ := baseChangeDerivedPushforward f p g q hsq hf inferInstance _ hF hflat
  have hpc₁ := DerivedFibreBetti.isPseudoCoherent_derivedPullback p _ hpc
  let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} (Spec (.of K)).toRingedSpace) :=
    HasDerivedCategory.standard (Spec (.of K)).Modules
  have hpc₂ := RingedSpace.IsPseudoCoherent.of_iso.{u, u + 1} hpc₁ e
  have h1 := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback p _ hpc n) pt
  rw [Function.comp_apply] at h1
  rw [← h1, DerivedFibreBetti.derivedFiberBetti_congr _ hpc₁ hpc₂ e,
    DerivedFibreOverField.derivedFiberBetti_derivedPushforwardModule K g _ hpc₂ n pt,
    finrank_cohomologyOverField_pullback_unit]

/-- **The zeroth derived-fibre Betti number is the dimension of the global functions of the
fibre.** -/
theorem derivedFiberBetti_zero_eq_finrank_globalSections (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ X) (g : Y ⟶ Spec (.of K))
    (hsq : IsPullback q g f p) (pt : Spec (.of K)) :
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
    DerivedFibreBetti.derivedFiberBetti S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) 0 (p.base pt) =
      Module.finrank K Γ(Y, ⊤) := by
  have h := derivedFiberBetti_eq_finrank_cohomologyOverField f hf K p q g hsq pt 0
  rwa [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K g] at h

omit [IsProper f] [Flat f] hf in
/-- A morphism to the spectrum of a field is bijective on global functions exactly when the
global functions form a one-dimensional vector space over the field. -/
theorem bijective_appTop_iff_finrank_eq_one (K : Type u) [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of K)) :
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
    Function.Bijective g.appTop ↔ Module.finrank K Γ(Y, ⊤) = 1 := by
  let : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
  have hcomp : Function.Bijective (algebraMap K Γ(Y, ⊤)) ↔ Function.Bijective g.appTop := by
    change Function.Bijective (g.appTop ∘ (Scheme.ΓSpecIso (.of K)).inv) ↔ _
    exact Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)
  rw [← hcomp]
  refine ⟨fun hb =>
      (LinearEquiv.ofBijective (Algebra.linearMap K Γ(Y, ⊤)) hb).finrank_eq.symm.trans
        (Module.finrank_self K), fun h1 => ?_⟩
  have : Module.Finite K Γ(Y, ⊤) := Module.finite_of_finrank_eq_succ h1
  have : Nontrivial Γ(Y, ⊤) := Module.nontrivial_of_finrank_eq_succ h1
  have hinj : Function.Injective (Algebra.linearMap K Γ(Y, ⊤)) := (algebraMap K Γ(Y, ⊤)).injective
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [h1, Module.finrank_self])).1 hinj⟩

/-- **`K = H⁰(X_K, 𝒪)` is read on the zeroth derived-fibre Betti number.** At a field-valued
point `p : Spec K ⟶ S` with fibre `Y`, the map `K ⟶ Γ(Y, 𝒪_Y)` is bijective exactly when the
zeroth derived-fibre Betti number of `Rf_*𝒪_X` at the image of `p` is one. -/
theorem bijective_appTop_iff_derivedFiberBetti_zero_eq_one (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ X) (g : Y ⟶ Spec (.of K))
    (hsq : IsPullback q g f p) (pt : Spec (.of K)) :
    Function.Bijective g.appTop ↔
      DerivedFibreBetti.derivedFiberBetti S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) 0 (p.base pt) = 1 := by
  rw [derivedFiberBetti_zero_eq_finrank_globalSections f hf K p q g hsq pt]
  exact bijective_appTop_iff_finrank_eq_one K g

/-- The zeroth derived-fibre Betti number at `s : S` is the dimension of `H⁰` of the fibre over the
residue field. -/
private theorem derivedFiberBetti_zero_eq_finrank_fiber (s : S) :
    DerivedFibreBetti.derivedFiberBetti S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) 0 s =
      Module.finrank (IsLocalRing.ResidueField (S.presheaf.stalk s))
        (cohomologyOverField _ (f.fiberToSpecResidueField s)
        (SheafOfModules.unit (f.fiber s).ringCatSheaf) 0) := by
  obtain ⟨pt, hpt⟩ : ∃ pt, (S.fromSpecResidueField s).base pt = s :=
    ⟨IsLocalRing.closedPoint (S.residueField s), Scheme.fromSpecResidueField_apply _ _⟩
  have h := derivedFiberBetti_eq_finrank_cohomologyOverField f hf _ _ _ _
    (isPullback_fiberι_fiberToSpecResidueField f s) pt 0
  exact (congrArg (DerivedFibreBetti.derivedFiberBetti S _ _ 0) hpt.symm).trans h

/-- **The locus where `H⁰` of the fibre is the residue field is open** (the scheme case of
Stacks 0E0R at `i = 0`). The points of `S` at which the zeroth derived-fibre Betti number of
`Rf_*𝒪_X` is one form an open subset: it is the intersection of the open locus where that Betti
number is at most one (Stacks 0BDI) with the open image of `f`, on which it is at least one. -/
theorem isOpen_setOf_derivedFiberBetti_zero_eq_one [LocallyOfFinitePresentation f] :
    IsOpen {s : S | DerivedFibreBetti.derivedFiberBetti S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) 0 s = 1} := by
  set β := DerivedFibreBetti.derivedFiberBetti S
    (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
    (isPseudoCoherent_derivedPushforwardModule_unit f hf) 0
  have hβ : ∀ s, β s = _ := derivedFiberBetti_zero_eq_finrank_fiber f hf
  have hU : IsOpen (β ⁻¹' Set.Iio 2) :=
    (upperSemicontinuous_iff_isOpen_preimage.1
      (DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti S _ _ 0)) 2
  have hR : IsOpen (Set.range f.base) := (Scheme.Hom.isOpenMap f).isOpen_range
  have hpos : ∀ s ∈ Set.range f.base, 1 ≤ β s := by
    rintro s ⟨x, rfl⟩
    rw [hβ]
    set g := f.fiberToSpecResidueField (f.base x)
    have hgp : IsProper g := MorphismProperty.of_isPullback (P := @IsProper)
      (isPullback_fiberι_fiberToSpecResidueField f (f.base x)) inferInstance
    have := @forall_finiteDimensional_cohomologyOverField_unit_of_isProper _ _ _ g hgp 0
    have : Nonempty (f.fiber (f.base x)) := by
      have : x ∈ Set.range (f.fiberι (f.base x)).base := by
        rw [Scheme.Hom.range_fiberι]; rfl
      obtain ⟨y, -⟩ := this
      exact ⟨y⟩
    have : Nonempty (⊤ : (f.fiber (f.base x)).Opens) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
    have e := (cohomologyOverFieldZeroIsoSections _ g
      (SheafOfModules.unit (f.fiber (f.base x)).ringCatSheaf)).toLinearEquiv
    have hΓ : Nontrivial Γ(f.fiber (f.base x), ⊤) := inferInstance
    have : Nontrivial (cohomologyOverField _ g
        (SheafOfModules.unit (f.fiber (f.base x)).ringCatSheaf) 0) :=
      @Function.Injective.nontrivial _ _ hΓ _ e.symm.injective
    exact Module.finrank_pos
  have heq : {s : S | β s = 1} = β ⁻¹' Set.Iio 2 ∩ Set.range f.base := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
    constructor
    · intro h1
      refine ⟨by omega, ?_⟩
      by_contra hs
      have hmem : ∀ y, f.base ((f.fiberι s).base y) = s := fun y => by
        have : (f.fiberι s).base y ∈ Set.range (f.fiberι s).base := ⟨y, rfl⟩
        rwa [Scheme.Hom.range_fiberι] at this
      have : IsEmpty (f.fiber s) := ⟨fun y => hs ⟨_, hmem y⟩⟩
      have e := (cohomologyOverFieldZeroIsoSections _ (f.fiberToSpecResidueField s)
        (SheafOfModules.unit (f.fiber s).ringCatSheaf)).toLinearEquiv
      have : Subsingleton (cohomologyOverField _ (f.fiberToSpecResidueField s)
          (SheafOfModules.unit (f.fiber s).ringCatSheaf) 0) := by
        refine @Function.Injective.subsingleton _ _ _ e.injective ?_
        exact inferInstanceAs (Subsingleton Γ(f.fiber s, ⊤))
      rw [hβ, Module.finrank_zero_of_subsingleton] at h1
      exact zero_ne_one h1
    · rintro ⟨h2, hs⟩
      have := hpos s hs
      omega
  rw [heq]
  exact hU.inter hR

/-- **The derived-fibre Euler characteristic of `Rf_*𝒪_X` is locally constant** (Stacks 0BDJ). -/
theorem isLocallyConstant_chiDerivedFibre_unit :
    IsLocallyConstant (DerivedFibreBetti.chiDerivedFibre S
      (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
      (isPseudoCoherent_derivedPushforwardModule_unit f hf)) :=
  DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _
    (isPerfect_derivedPushforwardModule_unit f hf)

/-- **`χ = 1 - g` at a field-valued point whose fibre is a curve with `H⁰ = K`.** For a cartesian
square with `p : Spec K ⟶ S` whose base change `Y` has dimension at most one and `K = H⁰(Y, 𝒪_Y)`,
the derived-fibre Euler characteristic of `Rf_*𝒪_X` at the image of the point of `Spec K` is
`1 - g`, where `g` is the genus of `Y` over `K` (Stacks 0B9T and 0BY7). -/
theorem chiDerivedFibre_eq_one_sub_genus (K : Type u) [Field K]
    (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ X) (g : Y ⟶ Spec (.of K))
    (hsq : IsPullback q g f p) (pt : Spec (.of K)) (hdim : topologicalKrullDim Y ≤ 1)
    (hΓ : Function.Bijective g.appTop) :
    DerivedFibreBetti.chiDerivedFibre S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) (p.base pt) = 1 - genus g := by
  have hF := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have h₁ := chiDerivedFibre_eq_eulerSum f hf _ hF (isFlatOver_unit_of_flat f) K p q g hsq pt
  have i : (Scheme.Modules.pullback q).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    Stacks.PullbackAlgebra.pullbackUnitIso q.toLRSHom.toShHom
  rw [eulerSum_congr K g i] at h₁
  have hgp : IsProper g := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have e₁ := @one_sub_genus_eq_eulerCharacteristic_unit K _ Y g hgp hdim
    ((bijective_appTop_iff_finrank_eq_one K g).1 hΓ)
  exact h₁.trans e₁.symm

/-- **The genus of the fibres is locally constant where they are curves with `H⁰` the field.**
Two field-valued points of `S` with the same value of the derived-fibre Euler characteristic of
`Rf_*𝒪_X` — for instance two points of a connected open — whose fibres have dimension at most
one and `H⁰` the field have fibres of the same genus. -/
theorem genus_eq_of_chiDerivedFibre_eq {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    (p₁ : Spec (.of K₁) ⟶ S) (p₂ : Spec (.of K₂) ⟶ S) {Y₁ Y₂ : Scheme.{u}}
    (q₁ : Y₁ ⟶ X) (g₁ : Y₁ ⟶ Spec (.of K₁)) (hsq₁ : IsPullback q₁ g₁ f p₁)
    (q₂ : Y₂ ⟶ X) (g₂ : Y₂ ⟶ Spec (.of K₂)) (hsq₂ : IsPullback q₂ g₂ f p₂)
    (pt₁ : Spec (.of K₁)) (pt₂ : Spec (.of K₂))
    (hdim₁ : topologicalKrullDim Y₁ ≤ 1) (hdim₂ : topologicalKrullDim Y₂ ≤ 1)
    (hΓ₁ : Function.Bijective g₁.appTop) (hΓ₂ : Function.Bijective g₂.appTop)
    (hχ : DerivedFibreBetti.chiDerivedFibre S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) (p₁.base pt₁) =
      DerivedFibreBetti.chiDerivedFibre S
        (derivedPushforwardModule f (SheafOfModules.unit X.ringCatSheaf))
        (isPseudoCoherent_derivedPushforwardModule_unit f hf) (p₂.base pt₂)) :
    genus g₁ = genus g₂ := by
  rw [chiDerivedFibre_eq_one_sub_genus f hf K₁ p₁ q₁ g₁ hsq₁ pt₁ hdim₁ hΓ₁,
    chiDerivedFibre_eq_one_sub_genus f hf K₂ p₂ q₂ g₂ hsq₂ pt₂ hdim₂ hΓ₂] at hχ
  exact_mod_cast sub_right_injective hχ

end AlgebraicGeometry.C1590Private

end
