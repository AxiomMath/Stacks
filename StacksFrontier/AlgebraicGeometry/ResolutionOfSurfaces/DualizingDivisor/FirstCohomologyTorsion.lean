module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.OfModification
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ZeroDimensionalFibres
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The first cohomology of a modification of a surface is supported at the closed point

Let `A` be a Noetherian normal local domain of dimension two and `f : X ⟶ Spec(A)` a
modification. For a quasi-coherent `𝒪_X`-module `𝒢` the `A`-module `H¹(X, 𝒢)` is killed, element
by element, by an element outside every prime `𝔭 ≠ 𝔪`: over the punctured spectrum `f` is an
isomorphism, so the fibres there are single points and `R¹f_*𝒢` has zero stalk at `𝔭`
([Stacks, Tag 02V7] with zero-dimensional fibres); since `R¹f_*𝒢` is quasi-coherent its stalk at
`𝔭` is the localization of its global sections, which are `H¹(X, 𝒢)` ([Stacks, Tag 01XK]).
This is the statement "`H¹(X, 𝒢)` is supported at `𝔪`" used in the proof of [Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.topologicalKrullDim_fiber_le_zero`: the fibres of `f`
  away from the closed point are at most zero-dimensional.
* `AlgebraicGeometry.DualizingDivisor.exists_smul_eq_zero_rightDerived_one`: every element of
  `H¹(X, 𝒢)` is killed by an element outside a given prime `𝔭 ≠ 𝔪`.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]

/-- **The fibres of a modification of a surface away from the closed point are points.** Over
the punctured spectrum the modification is an isomorphism, so each fibre there has at most one
point, hence dimension at most zero. -/
theorem topologicalKrullDim_fiber_le_zero (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) (y : Spec (.of A))
    (hy : y ≠ IsLocalRing.closedPoint A) :
    topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  let V := VanishingSituation.ofModification A hdim f hf
  let U : (Spec (.of A)).Opens := V.puncturedSpectrumOpen
  have : IsIso (f ∣_ U) := V.isIso_morphismRestrict_puncturedSpectrumOpen
  have hmem : ∀ a : f ⁻¹' {y}, (a : X) ∈ f ⁻¹ᵁ U := fun a => by
    change f a ∈ ({IsLocalRing.closedPoint A}ᶜ : Set (Spec (.of A)))
    rw [show f a = y from a.2]
    exact hy
  have : Subsingleton (f ⁻¹' {y}) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    let a' : (f ⁻¹ᵁ U).toScheme := ⟨a, hmem a⟩
    let b' : (f ⁻¹ᵁ U).toScheme := ⟨b, hmem b⟩
    have h : a' = b' := (f ∣_ U).isOpenEmbedding.injective (Subtype.ext (by
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      exact (show f a = y from a.2).trans (show f b = y from b.2).symm))
    exact congrArg (fun z : f ⁻¹ᵁ U => (z : X)) h
  have : Subsingleton (f.fiber y) := (f.fiberHomeo y).injective.subsingleton
  simpa using topologicalKrullDim_zero_of_discreteTopology (f.fiber y)

/-- A property of objects invariant under isomorphism passes from the `ℤ`-indexed right derived
functors `rightDerivedPlus` (at any model of the derived categories) to Mathlib's `ℕ`-indexed
ones. The models are implicit arguments, so that they are read off the hypothesis. -/
theorem rightDerived_of_rightDerivedPlus {C D : Type*} [Category C] [Abelian C]
    [EnoughInjectives C] [Category D] [Abelian D] {_ : HasDerivedCategory C}
    {_ : HasDerivedCategory D} (F : C ⥤ D) [F.Additive] (n : ℕ) (Z : C) (P : D → Prop)
    (hP : ∀ {a b : D}, (a ≅ b) → P a → P b) (h : P ((F.rightDerivedPlus (n : ℤ)).obj Z)) :
    P ((F.rightDerived n).obj Z) :=
  hP ((Stacks.DerivedIndexing.rightDerivedIso F n).app Z).symm h

/-- **Sections of `R¹f_*𝒢` are killed off the closed point.** For a quasi-coherent `𝒢` on a
modification `X` of `Spec(A)` and a prime `𝔭 ≠ 𝔪`, every global section of `R¹f_*𝒢` is killed by
(the image in `Γ(Spec A, 𝒪)` of) an element of `A` outside `𝔭`: the stalk of the quasi-coherent
module `R¹f_*𝒢` at `𝔭` vanishes and is the localization at `𝔭` of its global sections. -/
theorem exists_smul_eq_zero_sections_rightDerivedPlus (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f) (G : X.Modules)
    [G.IsQuasicoherent] (p : Ideal A) [p.IsPrime] (hp : p ≠ IsLocalRing.maximalIdeal A)
    (s : (Stacks.Cohomology.sectionsFunctor (Spec (.of A)) ⊤).obj
      (((Scheme.Modules.pushforward f).rightDerived 1).obj G)) :
    ∃ a : A, a ∉ p ∧ (Scheme.ΓSpecIso (.of A)).inv a • s = 0 := by
  have : IsProper f := hf.isProper
  let y : Spec (.of A) := ⟨p, inferInstance⟩
  have hy : y ≠ IsLocalRing.closedPoint A := fun h => hp (congrArg PrimeSpectrum.asIdeal h)
  let R := ((Scheme.Modules.pushforward f).rightDerived 1).obj G
  have : R.IsQuasicoherent :=
    rightDerived_of_rightDerivedPlus (Scheme.Modules.pushforward f) 1 G
      (fun M : (Spec (.of A)).Modules => M.IsQuasicoherent)
      (fun e h => (SheafOfModules.isQuasicoherent (Spec (.of A)).ringCatSheaf).prop_of_iso e h)
      (ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus f G inferInstance 1)
  have hzero : IsZero (R.presheaf.stalk y) :=
    rightDerived_of_rightDerivedPlus (Scheme.Modules.pushforward f) 1 G
      (fun M : (Spec (.of A)).Modules => IsZero (M.presheaf.stalk y))
      (fun e h => h.of_iso ((TopCat.Presheaf.stalkFunctor _ y).mapIso
        ((Scheme.Modules.toPresheaf _).mapIso e.symm)))
      (isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_zero
        f y (topologicalKrullDim_fiber_le_zero hdim f hf y hy) G 1 one_pos)
  have hU := isAffineOpen_top (Spec (.of A))
  have hyU : y ∈ (⊤ : (Spec (.of A)).Opens) := trivial
  have := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ R hU hyU
  have hgerm : Stacks.ModuleStalkSpecialization.germₗ R hyU s =
      Stacks.ModuleStalkSpecialization.germₗ R hyU 0 :=
    (AddCommGrpCat.subsingleton_of_isZero hzero).elim _ _
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl) hgerm
  refine ⟨(Scheme.ΓSpecIso (.of A)).hom c, ?_, ?_⟩
  · have hcp : (c : Γ(Spec (.of A), ⊤)) ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := c.2
    rwa [← mem_basicOpen_iff_notMem_primeIdealOf hU, basicOpen_eq_of_affine'] at hcp
  · rw [Iso.hom_inv_id_apply]
    rwa [smul_zero] at hc

/-- **`H¹(X, 𝒢)` is supported at the closed point.** For a modification `f : X ⟶ Spec(A)` of a
two-dimensional Noetherian normal local domain, a quasi-coherent `𝒪_X`-module `𝒢` and a prime
`𝔭 ≠ 𝔪`, every element of the `A`-module `H¹(X, 𝒢)` (the first right derived functor of
`A`-linear global sections) is killed by an element of `A` outside `𝔭`. It is
`exists_smul_eq_zero_sections_rightDerivedPlus` read through [Stacks, Tag 01XK]. -/
theorem exists_smul_eq_zero_rightDerived_one (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) (G : X.Modules) [G.IsQuasicoherent]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ IsLocalRing.maximalIdeal A)
    (x : ((globalSectionsOver f).rightDerived 1).obj G) : ∃ a : A, a ∉ p ∧ a • x = 0 := by
  have : IsProper f := hf.isProper
  let ψ := (Scheme.ΓSpecIso (.of A)).inv.hom
  let φ := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
  let e₁ := ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    (Stacks.Cohomology.sectionsFunctor X ⊤) (ModuleCat.restrictScalars φ)
    (globalSectionsOver f) (Iso.refl _) 1).app G).symm
  let e₂ := ModuleCat.restrictScalarsComp'App ψ f.appTop.hom φ rfl
    (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 1).obj G)
  let e₃ := (ModuleCat.restrictScalars ψ).mapIso
    ((Stacks.Cohomology.AffineBase.sectionsRightDerivedPushforwardIso f 1).app
      ⟨G, inferInstance⟩)
  let e := (e₁ ≪≫ e₂ ≪≫ e₃).toLinearEquiv
  obtain ⟨a, ha, has⟩ := exists_smul_eq_zero_sections_rightDerivedPlus hdim f hf G p hp (e x)
  refine ⟨a, ha, e.injective ?_⟩
  rwa [map_smul, map_zero]

end AlgebraicGeometry.DualizingDivisor

end
