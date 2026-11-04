module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineHomToStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DetectingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GeometricPointwiseBaseChangeTensorSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompFlat
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTorAmplitudeDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude

/-!
# Stacks 0DKI (3) is false without a Tor-dimension condition on `g`

Stacks 0DKI considers a cartesian square of algebraic spaces `g' ≫ f = f' ≫ g` over `S`,
`K ∈ D_QCoh(𝒪_X)` and `L(g')^*K ⟶ K'` in `D_QCoh(𝒪_{X'})` satisfying the equivalent conditions
of Stacks 0DKG. Part (3) asserts that if `K` is bounded below and `E` is pseudo-coherent, these
conditions hold for `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`. This is false.

Take `S = X = Y = Spec A` with `A = ℤ/4`, `f = 𝟙`, `g = g' : S' = X' = Spec ℤ/2 ⟶ S` the closed
point, `K = 𝒪_X[0]`, `K' = L(g')^*K` with `φ = 𝟙`, and `E = (ℤ/2)^~[0]`. All hypotheses hold:
`f = 𝟙` is flat, so the conditions of Stacks 0DKG hold for `(K, K', φ)`; `K` is bounded below;
`E` is pseudo-coherent, `ℤ/4` being Noetherian. But the conclusion fails. `A` is self-injective,
so `R𝓗om(E, K)` lies in degrees `≤ 0` and `RΓ(X, R𝓗om(E, K)) ⊗ᴸ_A ℤ/2` has no `H¹`. On the other
side, `H¹(R𝓗om(L(g')^*E, K'))` receives the nonzero class of `0 ⟶ ℤ/2 ⟶ ℤ/4 ⟶ ℤ/2 ⟶ 0` in
`Ext¹_A(ℤ/2, ℤ/2)`. So condition (2) of Stacks 0DKG fails on the identity chart.

The proof in the Stacks Project breaks at the computation for a bounded above complex of finite
free modules `E_x`. The infinite products in `Hom^•(E_x, K_x)` commute with `⊗ᴸ R'` only
when `R'` has finite Tor dimension, and `ℤ/2` has infinite Tor dimension over `ℤ/4`. With `g`
of finite Tor dimension the statement holds:
`AlgebraicGeometry.Space.geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent`.

## Main results

In the namespace `Stacks.Examples.PseudoCoherentSheafHomBaseChange`:

* `not_geometricPointwiseBaseChange_sheafHom_residueObj`: the conclusion of Stacks 0DKI (3)
  fails for the data above.
* `not_forall_geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent`: Stacks 0DKI (3) as
  written is false.

## References

* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0DKG](https://stacks.math.columbia.edu/tag/0DKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

universe u

namespace Stacks.Examples.PseudoCoherentSheafHomBaseChange

/-! ### Two rings: `ℤ/4` and its residue field -/

section Algebra

variable {A : Type u} [CommRing A]

/-- **Baer's criterion for a ring with four elements `0, 1, 2, 3` and `4 = 0 ≠ 2`** (such as
`ℤ/4`): every `A`-linear map from an ideal to `A` extends to `A`. -/
theorem baer_self_of_four (h4 : (4 : A) = 0) (h2 : (2 : A) ≠ 0)
    (hA : ∀ x : A, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : Module.Baer A A := by
  intro I g
  by_cases h1 : (1 : A) ∈ I
  · refine ⟨LinearMap.toSpanSingleton A A (g ⟨1, h1⟩), fun x hx => ?_⟩
    have : (⟨x, hx⟩ : I) = x • ⟨1, h1⟩ := by ext; simp
    rw [this, map_smul]
    simp
  · have h3 : (3 : A) ∉ I := fun h3 => h1 (by
      have : (1 : A) = 3 * 3 - 2 * 4 := by ring
      rw [this, h4, mul_zero, sub_zero]
      exact I.mul_mem_left 3 h3)
    by_cases h2I : (2 : A) ∈ I
    · set c := g ⟨2, h2I⟩ with hc
      have h2c : 2 * c = 0 := by
        have : (2 : A) • (⟨2, h2I⟩ : I) = 0 := by
          ext
          simp only [Submodule.coe_smul, smul_eq_mul, Submodule.coe_zero]
          linear_combination h4
        have := congrArg g this
        rwa [map_smul, map_zero, smul_eq_mul] at this
      obtain ⟨r, hr⟩ : ∃ r : A, 2 * r = c := by
        rcases hA c with h | h | h | h
        · exact ⟨0, by rw [h]; ring⟩
        · exact absurd (by simpa [h] using h2c) h2
        · exact ⟨1, by rw [h]; ring⟩
        · exact absurd (by linear_combination h2c - h4 - 2 * h) h2
      refine ⟨LinearMap.toSpanSingleton A A r, fun x hx => ?_⟩
      rcases hA x with h | h | h | h
      · subst h
        simp only [LinearMap.toSpanSingleton_apply, zero_smul]
        exact (congrArg g (Subtype.ext rfl : (⟨0, hx⟩ : I) = 0)).trans (map_zero g) |>.symm
      · exact absurd (h ▸ hx) h1
      · subst h
        simp only [LinearMap.toSpanSingleton_apply, smul_eq_mul]
        rw [hr]
      · exact absurd (h ▸ hx) h3
    · refine ⟨0, fun x hx => ?_⟩
      rcases hA x with h | h | h | h
      · subst h
        exact ((congrArg g (Subtype.ext rfl : (⟨0, hx⟩ : I) = 0)).trans (map_zero g)).symm
      · exact absurd (h ▸ hx) h1
      · exact absurd (h ▸ hx) h2I
      · exact absurd (h ▸ hx) h3

/-- A ring with four elements `0, 1, 2, 3` and `4 = 0 ≠ 2` is self-injective. -/
theorem injective_self_of_four (h4 : (4 : A) = 0) (h2 : (2 : A) ≠ 0)
    (hA : ∀ x : A, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3) : Injective (ModuleCat.of A A) := by
  have := (baer_self_of_four h4 h2 hA).injective
  exact Module.injective_object_of_injective_module A A



variable {A' : Type u} [CommRing A'] (φ : A →+* A')

/-- `A'` as an `A`-module. -/
noncomputable abbrev resMod : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of A' A')

/-- The hypotheses: `A` has the four elements `0, 1, 2, 3` with `4 = 0 ≠ 2`, and `A'` the two
elements `0 ≠ 1` with `2 = 0`. -/
structure FourTwoRings (φ : A →+* A') : Prop where
  h4 : (4 : A) = 0
  h2 : (2 : A) ≠ 0
  hA : ∀ x : A, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3
  hA' : ∀ y : A', y = 0 ∨ y = 1
  h1' : (1 : A') ≠ 0
  h2' : (2 : A') = 0

variable {φ}

/-- `φ a = 0` exactly when `2 a = 0`. -/
theorem FourTwoRings.φ_eq_zero_iff (H : FourTwoRings φ) (a : A) : φ a = 0 ↔ 2 * a = 0 := by
  have e2 : φ 2 = 0 := by rw [map_ofNat, H.h2']
  have e3 : φ 3 = 1 := by
    rw [show (3 : A) = 1 + 2 by norm_num, map_add, map_one, e2, add_zero]
  rcases H.hA a with h | h | h | h <;> subst h
  · simp
  · simp only [map_one, mul_one]
    exact ⟨fun h => absurd h H.h1', fun h => absurd h H.h2⟩
  · simp only [e2, true_iff]
    linear_combination H.h4
  · rw [e3]
    exact ⟨fun h => absurd h H.h1', fun h => absurd (by linear_combination h - H.h4) H.h2⟩

open Classical in
/-- `0 ↦ 0`, `y ↦ 2` otherwise. -/
noncomputable def twiceFun (y : A') : A := if y = 0 then 0 else 2

/-- `twiceFun` is additive. -/
theorem twiceFun_add (H : FourTwoRings φ) (y y' : A') :
    twiceFun (y + y') = (twiceFun y : A) + twiceFun y' := by
  rcases H.hA' y with rfl | rfl <;> rcases H.hA' y' with rfl | rfl
  · simp [twiceFun]
  · simp [twiceFun, H.h1']
  · simp [twiceFun, H.h1']
  · have : (1 : A') + 1 = 0 := by linear_combination H.h2'
    simp only [twiceFun, this, ite_true, ite_eq_right H.h1']
    linear_combination -H.h4

/-- `twiceFun` is `A`-linear for the `A`-module structure of `A'` through `φ`. -/
theorem twiceFun_mul (H : FourTwoRings φ) (a : A) (y : A') :
    twiceFun (φ a * y) = a * (twiceFun y : A) := by
  rcases H.hA' y with rfl | rfl
  · simp [twiceFun]
  · rw [mul_one]
    simp only [twiceFun, ite_eq_right H.h1']
    by_cases ha : φ a = 0
    · rw [ite_eq_left ha, mul_comm, (H.φ_eq_zero_iff a).1 ha]
    · rw [ite_eq_right ha]
      have h2a : 2 * a ≠ 0 := fun h => ha ((H.φ_eq_zero_iff a).2 h)
      rcases H.hA a with rfl | rfl | rfl | rfl
      · simp at h2a
      · ring
      · exact absurd (by linear_combination H.h4) h2a
      · linear_combination (-1 : A) * H.h4

/-- The `A`-linear map `A' ⟶ A`, `0 ↦ 0`, `1 ↦ 2`. -/
noncomputable def twiceLift (H : FourTwoRings φ) : resMod φ ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (X := ↑(resMod φ)) (Y := A)
  { toFun := fun y => twiceFun (A := A) (A' := A') y
    map_add' := fun y y' => twiceFun_add H y y'
    map_smul' := fun a y => twiceFun_mul H a y }

/-- The reduction `A ⟶ A'` as a map of `A`-modules. -/
noncomputable def reductionHom (φ : A →+* A') : ModuleCat.of A A ⟶ resMod φ :=
  ModuleCat.ofHom (X := A) (Y := ↑(resMod φ))
  { toFun := fun a => (φ a : A')
    map_add' := fun a b => map_add φ a b
    map_smul' := fun a b => by
      change φ (a * b) = φ a * φ b
      exact map_mul φ a b }


/-- The composite `A' ⟶ A ⟶ A'` vanishes. -/
theorem reductionHom_twiceLift (H : FourTwoRings φ) : twiceLift H ≫ reductionHom φ = 0 := by
  ext y
  change A' at y
  show φ (twiceFun (A := A) (A' := A') y) = 0
  rcases H.hA' y with rfl | rfl
  · simp [twiceFun]
  · simp only [twiceFun, ite_eq_right H.h1', map_ofNat]
    exact H.h2'

/-- The short exact sequence `0 ⟶ A' ⟶ A ⟶ A' ⟶ 0` of `A`-modules. -/
noncomputable def twiceSeq (H : FourTwoRings φ) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (twiceLift H) (reductionHom φ) (reductionHom_twiceLift H)

/-- The sequence `0 ⟶ A' ⟶ A ⟶ A' ⟶ 0` is short exact. -/
theorem twiceSeq_shortExact (H : FourTwoRings φ) : (twiceSeq H).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    change A at a
    change φ a = 0 at ha
    have h2a := (H.φ_eq_zero_iff a).1 ha
    rcases H.hA a with rfl | rfl | rfl | rfl
    · exact ⟨(0 : A'), by change twiceFun (A := A) (A' := A') 0 = 0; simp [twiceFun]⟩
    · exact absurd (by simpa using h2a) H.h2
    · exact ⟨(1 : A'), by change twiceFun (A := A) (A' := A') 1 = 2; simp [twiceFun, H.h1']⟩
    · exact absurd (by linear_combination h2a - H.h4) H.h2
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro y y' hyy
    change A' at y y'
    change twiceFun (A := A) (A' := A') y = twiceFun (A := A) (A' := A') y' at hyy
    rcases H.hA' y with h | h <;> rcases H.hA' y' with h' | h'
    · exact h.trans h'.symm
    · rw [h, h'] at hyy
      simp [twiceFun, H.h1'] at hyy
      exact absurd hyy.symm H.h2
    · rw [h, h'] at hyy
      exact absurd (by simpa [twiceFun, H.h1'] using hyy) H.h2
    · exact h.trans h'.symm
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro y
    change A' at y
    rcases H.hA' y with h | h
    · exact ⟨(0 : A), by change φ 0 = y; rw [h, map_zero]⟩
    · exact ⟨(1 : A), by change φ 1 = y; rw [h, map_one]⟩

/-- **`Ext¹_A(A', A') ≠ 0`**: the sequence `0 ⟶ A' ⟶ A ⟶ A' ⟶ 0` does not split. -/
theorem not_subsingleton_ext_one (H : FourTwoRings φ) :
    ¬ Subsingleton (Abelian.Ext (resMod φ) (resMod φ) 1) := by
  intro hsub
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (resMod φ) (twiceSeq_shortExact H)
    (Abelian.Ext.mk₀ (𝟙 (resMod φ))) (n₁ := 1) rfl (@Subsingleton.elim _ hsub _ _)
  obtain ⟨s, rfl⟩ := Abelian.Ext.mk₀_bijective (resMod φ) (twiceSeq H).X₂ |>.2 x₂
  rw [Abelian.Ext.mk₀_comp_mk₀] at hx₂
  have hs : s ≫ reductionHom φ = 𝟙 _ := (Abelian.Ext.mk₀_bijective _ _).1 hx₂
  set a : A := s.hom (1 : A')
  have ha1 : φ a = 1 := congrArg (fun t => t.hom (1 : A')) hs
  have ha2 : 2 * a = 0 := by
    have h0 : (2 : A) • (show ↑(resMod φ) from (1 : A')) = 0 := by
      show φ 2 * 1 = (0 : A')
      rw [mul_one, map_ofNat, H.h2']
    have := congrArg s.hom h0
    rwa [map_smul, map_zero] at this
  exact H.h1' (ha1.symm.trans ((H.φ_eq_zero_iff a).2 ha2))
end Algebra



/-- The reduction `ℤ/4 ⟶ ℤ/2`. -/
noncomputable def reduction : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

/-- The closed point `Spec ℤ/2 ⟶ Spec ℤ/4`. -/
noncomputable abbrev specReduction : Spec (.of (ZMod 2)) ⟶ Spec (.of (ZMod 4)) :=
  Spec.map (CommRingCat.ofHom reduction)

/-- `Spec ℤ/2 ⟶ Spec ℤ/4` is a closed immersion. -/
instance : IsClosedImmersion specReduction :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)

/-- `Spec ℤ/2 ⟶ Spec ℤ/4` is a monomorphism. -/
instance : Mono specReduction := inferInstance

/-- A big fppf site containing `Spec ℤ/4`. -/
noncomputable def zmodFourSite : BigFppfSite.{0} :=
  (BigFppfSite.exists_contains (Spec (.of (ZMod 4)))).choose

/-- The chosen site contains `Spec ℤ/4`. -/
theorem zmodFourSite_contains : zmodFourSite.Contains (Spec (.of (ZMod 4))) :=
  (BigFppfSite.exists_contains (Spec (.of (ZMod 4)))).choose_spec

/-- The chosen site contains `Spec ℤ/2`, a closed subscheme of `Spec ℤ/4`. -/
theorem zmodFourSite_contains_zmodTwo : zmodFourSite.Contains (Spec (.of (ZMod 2))) :=
  zmodFourSite.contains_of_mono specReduction zmodFourSite_contains

/-- The base scheme `S = Spec ℤ/4`. -/
noncomputable abbrev specZModFour : Scheme.{0} := Spec (.of (ZMod 4))

/-- `S` as an object of the big fppf site over itself. -/
noncomputable abbrev baseObj : BigFppfOver zmodFourSite specZModFour zmodFourSite_contains :=
  siteObject zmodFourSite specZModFour zmodFourSite_contains zmodFourSite_contains (𝟙 _)
/-- The closed point `Spec ℤ/2 ⟶ S` as an object of the big fppf site over `S`. -/
noncomputable abbrev pointObj : BigFppfOver zmodFourSite specZModFour zmodFourSite_contains :=
  siteObject zmodFourSite specZModFour zmodFourSite_contains zmodFourSite_contains_zmodTwo
    specReduction

/-- The closed point `Spec ℤ/2 ⟶ Spec ℤ/4`, over `S`. -/
noncomputable def pointToBase : pointObj ⟶ baseObj :=
  Over.homMk (ObjectProperty.homMk specReduction) (by ext1; exact Category.comp_id _)

/-- `S` is affine. -/
instance : IsAffine
    ((BigFppfOver.toScheme zmodFourSite specZModFour zmodFourSite_contains).obj baseObj) :=
  inferInstanceAs (IsAffine (Spec _))
/-- `Spec ℤ/2` is affine. -/
instance : IsAffine
    ((BigFppfOver.toScheme zmodFourSite specZModFour zmodFourSite_contains).obj pointObj) :=
  inferInstanceAs (IsAffine (Spec _))



attribute [local instance] HasDerivedCategory.standard

/-- `X = Y = S`, as an algebraic space over `S`. -/
abbrev baseSpace : AlgebraicSpaces zmodFourSite specZModFour zmodFourSite_contains :=
  ⟨yoneda.obj baseObj, isAlgebraicSpace_yoneda _ _ _ baseObj⟩
/-- `X' = S' = Spec ℤ/2`, as an algebraic space over `S`. -/
abbrev pointSpace : AlgebraicSpaces zmodFourSite specZModFour zmodFourSite_contains :=
  ⟨yoneda.obj pointObj, isAlgebraicSpace_yoneda _ _ _ pointObj⟩
/-- `g = g' : S' ⟶ S`, the closed point. -/
noncomputable abbrev pointMap : pointSpace ⟶ baseSpace :=
  representedSpaceMap zmodFourSite specZModFour zmodFourSite_contains pointToBase

/-- The square with `f = 𝟙_X`, `f' = 𝟙_{X'}` and `g = g'` is cartesian. -/
theorem isPullback_pointMap : IsPullback pointMap (𝟙 pointSpace) (𝟙 baseSpace) pointMap :=
  IsPullback.of_vert_isIso ⟨by simp⟩

/-- `K = 𝒪_X[0]`. -/
noncomputable abbrev structureObj :
    DerivedCategory (SheafOfModules.{0}
      (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains baseSpace)) :=
  (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- `A = Γ(X, 𝒪_X) ≅ ℤ/4`. -/
noncomputable abbrev baseRing : CommRingCat.{0} :=
  Γ((BigFppfOver.toScheme zmodFourSite specZModFour zmodFourSite_contains).obj baseObj, ⊤)
/-- `A' = Γ(X', 𝒪_{X'}) ≅ ℤ/2`. -/
noncomputable abbrev pointRing : CommRingCat.{0} :=
  Γ((BigFppfOver.toScheme zmodFourSite specZModFour zmodFourSite_contains).obj pointObj, ⊤)
/-- The map `A ⟶ A'` of global functions of `g`. -/
noncomputable abbrev baseToPointRingHom : baseRing →+* pointRing :=
  (representedAffineCommRingCatHom zmodFourSite specZModFour zmodFourSite_contains pointToBase).hom
/-- The residue field `A'` of `A`, as an `A`-module. -/
noncomputable abbrev residueModule : ModuleCat.{0} baseRing :=
  (ModuleCat.restrictScalars baseToPointRingHom).obj (ModuleCat.of pointRing pointRing)

/-- `E`, the residue field of `S` placed in degree zero, as an object of `D_QCoh(𝒪_X)`. -/
noncomputable abbrev residueObj :
    DerivedCategory (SheafOfModules.{0}
      (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains baseSpace)) :=
  (representedAffineToposDerivedAssociated zmodFourSite specZModFour zmodFourSite_contains
    baseObj).obj
    ((@DerivedCategory.singleFunctor (ModuleCat.{0} baseRing) _ _
      (HasDerivedCategory.standard _) 0).obj residueModule)

/-- `𝒪_X`. -/
abbrev baseStructureModule :=
  structureSheafModule zmodFourSite specZModFour zmodFourSite_contains baseSpace

/-- `𝒪_X` as a complex concentrated in degree zero. -/
abbrev structureComplex : CochainComplex (SheafOfModules.{0}
    (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains baseSpace)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj baseStructureModule

/-- A property of the terms of `𝒪_X[0]` holds in every degree if it holds for zero objects and in
degree `0`. -/
private theorem forall_structureComplex_X
    {P : SheafOfModules.{0}
      (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains baseSpace) →
        Prop}
    (hz : ∀ M, IsZero M → P M) (h₀ : P (structureComplex.X 0)) (n : ℤ) :
    P (structureComplex.X n) := by
  by_cases hn : n = 0
  · subst hn
    exact h₀
  · exact hz _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- The terms of `𝒪_X[0]` are quasi-coherent. -/
theorem isQuasicoherentOnSite_structureComplex_X (n : ℤ) :
    (structureComplex.X n).IsQuasicoherentOnSite :=
  forall_structureComplex_X (P := SheafOfModules.IsQuasicoherentOnSite)
    (fun _ => SheafOfModules.IsQuasicoherentOnSite.of_isZero)
    (SheafOfModules.IsQuasicoherentOnSite.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm
      (_root_.SheafOfModules.isQuasicoherentOnSite_unit _)) n

/-- `𝒪_X[0]` is strictly bounded above by `0`. -/
instance : CochainComplex.IsStrictlyLE structureComplex 0 :=
  (CochainComplex.isStrictlyLE_iff structureComplex 0).2 fun i hi =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- `L(g')^*𝒪_X[0] ⟶ (g')^*𝒪_X[0]` is invertible: `𝒪_X[0]` is K-flat. -/
theorem isIso_pullbackQComparison_structureComplex :
    IsIso (smallEtaleDerivedPullbackQComparison pointMap structureComplex) := by
  have hflat :=
    forall_structureComplex_X
      (P := AlgebraicGeometry.SheafOfModules.IsFlat.{0, 1, 0, 0}
        (O := (smallEtaleRingedTopos zmodFourSite specZModFour zmodFourSite_contains
          baseSpace).O))
      (fun _ => isFlat_of_isZero zmodFourSite specZModFour zmodFourSite_contains)
      (Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
        (HomologicalComplex.singleObjXSelf _ _ _).symm
        (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
          (Y := smallEtaleRingedSite zmodFourSite specZModFour zmodFourSite_contains
            baseSpace.1 baseSpace.2)))
  have := isIso_smallEtaleDerivedModulePullbackComparison_app zmodFourSite specZModFour
    zmodFourSite_contains pointMap
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj structureComplex)
    (smallEtaleModuleKFlat_of_isStrictlyLE zmodFourSite specZModFour zmodFourSite_contains
      baseSpace structureComplex 0 hflat)
  rw [smallEtaleDerivedPullbackQComparison.eq_1]
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' inferInstance
    (Iso.isIso_hom ((DerivedCategory.quotientCompQhIso _).app _)))

/-- `K = 𝒪_X[0]` lies in `D_QCoh(𝒪_X)`. -/
theorem qcohDerived_structureObj :
    QcohDerived zmodFourSite specZModFour zmodFourSite_contains baseSpace structureObj :=
  qcohDerived_singleFunctor_structureModule (X := baseSpace.1) (hX := baseSpace.2)

/-- **The hypothesis of Stacks 0DKI holds for `K = 𝒪_X`, `K' = L(g')^*K` and `φ = 𝟙`**: the
conditions of Stacks 0DKG, as `f = 𝟙_X` is flat (Stacks 0A1K for `𝒢^• = 𝒪_X[0]`). -/
theorem geometricPointwiseBaseChange_structureObj :
    GeometricPointwiseBaseChange zmodFourSite specZModFour zmodFourSite_contains (𝟙 baseSpace)
      pointMap (𝟙 pointSpace) pointMap isPullback_pointMap.w structureObj
      ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
        pointMap).obj structureObj) (𝟙 _) := by
  have hA := affineChartwiseBaseChange_pullbackQComparison zmodFourSite specZModFour
    zmodFourSite_contains isPullback_pointMap structureComplex 0
    isQuasicoherentOnSite_structureComplex_X
    (forall_structureComplex_X
      (fun _ => isFlatOver_of_isZero zmodFourSite specZModFour zmodFourSite_contains (𝟙 baseSpace))
      (IsFlatOver.of_iso zmodFourSite specZModFour zmodFourSite_contains baseSpace.2
        (HomologicalComplex.singleObjXSelf _ _ _).symm
        (isFlatOver_structureSheafModule zmodFourSite specZModFour zmodFourSite_contains
          (𝟙 baseSpace)
          (isFlat_of_isEtale zmodFourSite specZModFour zmodFourSite_contains
            (isEtale_of_isIso zmodFourSite specZModFour zmodFourSite_contains _)))))
  have := isIso_pullbackQComparison_structureComplex
  let e : DerivedCategory.Q.obj structureComplex ≅ structureObj :=
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{0}
      (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains baseSpace))
        0).app baseStructureModule).symm
  let e' := (asIso (smallEtaleDerivedPullbackQComparison pointMap structureComplex)).symm ≪≫
    (smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
      pointMap).mapIso e
  have hA' := AffineChartwiseBaseChange.of_iso (f := 𝟙 baseSpace) (g := pointMap)
    (f' := 𝟙 pointSpace) (g' := pointMap) (w := isPullback_pointMap.w) e e'
    (smallEtaleDerivedPullbackQComparison pointMap structureComplex) (𝟙 _) (by simp [e']) hA
  exact (geometricPointwiseBaseChange_iff_affineChartwiseBaseChange isPullback_pointMap
    structureObj qcohDerived_structureObj _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ pointMap structureObj
      qcohDerived_structureObj) _).2 hA'


/-! ### The rings -/

/-- `A ≅ ℤ/4` and `A' ≅ ℤ/2` satisfy `FourTwoRings`. -/
theorem fourTwoRings_baseToPointRingHom : FourTwoRings baseToPointRingHom := by
  let eA : baseRing ≃+* ZMod 4 :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZMod 4))).commRingCatIsoToRingEquiv
  let eA' : pointRing ≃+* ZMod 2 :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).commRingCatIsoToRingEquiv
  have h4 : ∀ z : ZMod 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by decide
  have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  refine ⟨eA.injective ?_, fun h => ?_, fun x => ?_, fun y => ?_, fun h => ?_, eA'.injective ?_⟩
  · rw [map_ofNat, map_zero]; decide
  · have := congrArg eA h; rw [map_ofNat, map_zero] at this; exact absurd this (by decide)
  · rcases h4 (eA x) with h | h | h | h
    · exact Or.inl (eA.injective (h.trans (map_zero eA).symm))
    · exact Or.inr (Or.inl (eA.injective (h.trans (map_one eA).symm)))
    · exact Or.inr (Or.inr (Or.inl (eA.injective (h.trans (map_ofNat eA 2).symm))))
    · exact Or.inr (Or.inr (Or.inr (eA.injective (h.trans (map_ofNat eA 3).symm))))
  · rcases h2 (eA' y) with h | h
    · exact Or.inl (eA'.injective (h.trans (map_zero eA').symm))
    · exact Or.inr (eA'.injective (h.trans (map_one eA').symm))
  · have := congrArg eA' h; rw [map_one, map_zero] at this; exact absurd this (by decide)
  · rw [map_ofNat, map_zero]; decide

/-- `A ≅ ℤ/4` is self-injective. -/
theorem injective_baseRing : Injective (ModuleCat.of baseRing baseRing) :=
  injective_self_of_four fourTwoRings_baseToPointRingHom.h4 fourTwoRings_baseToPointRingHom.h2
    fourTwoRings_baseToPointRingHom.hA

/-! ### Morphisms out of `E` -/

/-- `Hom(E, K[n]) = Ext^n_A(A', A) = 0` for `n ≥ 1`, as `A` is self-injective. -/
theorem subsingleton_hom_residueObj_shift (n : ℕ) :
    Subsingleton (residueObj ⟶ structureObj⟦((n + 1 : ℕ) : ℤ)⟧) := by
  let : HasDerivedCategory (ModuleCat.{0} baseRing) := HasDerivedCategory.standard _
  have := injective_baseRing
  let Φ :=
    representedAffineDerivedAssociated zmodFourSite specZModFour zmodFourSite_contains baseObj
  let ι := representedAffineDerivedAssociatedSingleUnitIso zmodFourSite specZModFour
    zmodFourSite_contains baseObj 0
  have h₀ : Subsingleton (Abelian.Ext residueModule (ModuleCat.of baseRing baseRing) (n + 1)) :=
    ⟨fun a b =>
      (Abelian.Ext.eq_zero_of_injective a).trans (Abelian.Ext.eq_zero_of_injective b).symm⟩
  have h₁ := (Abelian.Ext.homEquiv (X := residueModule) (Y := ModuleCat.of baseRing baseRing)
    (n := n + 1)).subsingleton_congr.1 h₀
  have h₂ := ((representedAffineDerivedAssociatedFullyFaithful zmodFourSite specZModFour
    zmodFourSite_contains baseObj).homEquiv
    (X := (DerivedCategory.singleFunctor _ 0).obj residueModule)
    (Y := ((DerivedCategory.singleFunctor _ 0).obj
      (ModuleCat.of baseRing baseRing))⟦((n + 1 : ℕ) : ℤ)⟧)).subsingleton_congr.1 h₁
  refine (Iso.homCongr (Iso.refl _) ((Φ.commShiftIso ((n + 1 : ℕ) : ℤ)).app _ ≪≫
    (shiftFunctor _ ((n + 1 : ℕ) : ℤ)).mapIso ι)).subsingleton_congr.1 h₂

/-- `E` lies in `D_QCoh(𝒪_X)`. -/
theorem qcohDerived_residueObj :
    QcohDerived zmodFourSite specZModFour zmodFourSite_contains baseSpace residueObj :=
  qcohDerived_representedAffineDerivedAssociated_obj zmodFourSite specZModFour
    zmodFourSite_contains baseObj _

/-- `K = 𝒪_X[0]` is bounded below. -/
theorem isBoundedBelow_structureObj : DerivedCategoryB.IsBoundedBelow structureObj :=
  ⟨0, fun n hn => by
    have : structureObj.IsGE 0 := inferInstance
    exact (DerivedCategory.isGE_iff structureObj 0).1 this n hn⟩

/-- `A ≅ ℤ/4` is Noetherian. -/
instance : IsNoetherianRing baseRing :=
  isNoetherianRing_of_ringEquiv (ZMod 4)
    (Scheme.ΓSpecIso (CommRingCat.of (ZMod 4))).commRingCatIsoToRingEquiv.symm

/-- `A' ≅ ℤ/2` is finite. -/
instance : Finite pointRing :=
  Finite.of_equiv (ZMod 2)
    (Scheme.ΓSpecIso (CommRingCat.of (ZMod 2))).commRingCatIsoToRingEquiv.symm.toEquiv

/-- The finite `A`-module `A'` in degree zero is `m`-pseudo-coherent for every `m`. -/
theorem isPseudoCoherentFrom_single_residueModule (m : ℤ) :
    @StacksDraft.PseudoCoherence.IsPseudoCoherentFrom _ _ (_)
      ((@DerivedCategory.singleFunctor (ModuleCat.{0} baseRing) _ _
        (HasDerivedCategory.standard _) 0).obj residueModule) m := by
  let : HasDerivedCategory (ModuleCat.{0} baseRing) := HasDerivedCategory.standard _
  refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((DerivedCategory.singleFunctor _ 0).obj residueModule) m residueModule).1.2
    ⟨⟨0, fun i hi => ?_⟩, fun i _ => ?_⟩
  · exact (DerivedCategory.isLE_iff _ 0).1 inferInstance i hi
  · by_cases hi : i = 0
    · subst hi
      have : Finite ((𝟭 (ModuleCat.{0} baseRing)).obj residueModule) :=
        inferInstanceAs (Finite pointRing)
      have : Module.Finite baseRing ((𝟭 (ModuleCat.{0} baseRing)).obj residueModule) :=
        Module.Finite.of_finite
      exact Module.Finite.equiv
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app
          residueModule).toLinearEquiv.symm
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{0} baseRing) i).obj
          ((DerivedCategory.singleFunctor _ 0).obj residueModule)) := by
        rcases lt_or_gt_of_ne hi with h | h
        · exact (DerivedCategory.isGE_iff _ 0).1 inferInstance i h
        · exact (DerivedCategory.isLE_iff _ 0).1 inferInstance i h
      have := ModuleCat.subsingleton_of_isZero hz
      exact Module.Finite.of_finite

/-- `E` is pseudo-coherent. -/
theorem isPseudoCoherent_residueObj :
    RingedSite.IsPseudoCoherent (smallEtaleRingedSite zmodFourSite specZModFour
      zmodFourSite_contains baseSpace.1 baseSpace.2) residueObj := by
  let : HasDerivedCategory (ModuleCat.{0} baseRing) := HasDerivedCategory.standard _
  have h : ∀ m : ℤ, (smallEtaleRingedSite zmodFourSite specZModFour zmodFourSite_contains
      baseSpace.1 baseSpace.2).IsPseudoCoherentFrom residueObj m :=
    fun m => (isPseudoCoherentFrom_iff_representedAffineDerivedSections zmodFourSite specZModFour
      zmodFourSite_contains baseObj residueObj
      qcohDerived_residueObj m).2 ((isPseudoCoherentFrom_single_residueModule m).ofIso
        ((asIso (representedAffineDerivedAdjunction zmodFourSite specZModFour
          zmodFourSite_contains baseObj).unit).app _))
  obtain ⟨P, -, ⟨e⟩⟩ := h 0
  exact ⟨P, fun n => RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ residueObj n (h n)
    P e, ⟨e⟩⟩

/-- `R𝓗om(E, K)` lies in `D_QCoh(𝒪_X)` (Stacks 0A8A). -/
theorem qcohDerived_sheafHom_residueObj :
    QcohDerived zmodFourSite specZModFour zmodFourSite_contains baseSpace
      (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains baseSpace).obj
        (op residueObj)).obj structureObj) :=
  qcohDerived_smallEtaleDerivedSheafHom baseSpace residueObj structureObj
    (Or.inl ⟨isPseudoCoherent_residueObj, isBoundedBelow_structureObj, qcohDerived_structureObj⟩)

/-- `H^n(R𝓗om(E, K)) = 0` for `n ≥ 1`. -/
theorem isZero_homology_sheafHom_residueObj (n : ℕ) :
    IsZero ((DerivedCategory.homologyFunctor (AlgebraicGeometry.Space.Modules.{0, 0} zmodFourSite
      specZModFour zmodFourSite_contains baseSpace.1 baseSpace.2) ((n + 1 : ℕ) : ℤ)).obj
        (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains
          baseSpace).obj (op residueObj)).obj structureObj)) :=
  isZero_homology_of_forall_homFromUnit_eq_zero
    (representedAffineFinalChart zmodFourSite specZModFour zmodFourSite_contains baseObj)
    (isTerminalChartOfIso baseObj (Iso.refl _))
    (isAffineChart_representedAffineFinalChart zmodFourSite specZModFour zmodFourSite_contains
      baseObj)
    _ qcohDerived_sheafHom_residueObj _ fun x =>
      ((homUnitShiftSmallEtaleDerivedSheafHomEquiv baseSpace residueObj structureObj
        _).subsingleton_congr.2 (subsingleton_hom_residueObj_shift n)).elim x 0


/-! ### Generic t-structure facts -/

section TStructure

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- A left adjoint between derived categories whose right adjoint preserves `D^{≥ n+1}`
preserves `D^{≤ n}`. -/
theorem isLE_obj_of_adjunction {F : DerivedCategory C ⥤ DerivedCategory D}
    {G : DerivedCategory D ⥤ DerivedCategory C} (adj : F ⊣ G) [F.PreservesZeroMorphisms] (n : ℤ)
    (hG : ∀ Y : DerivedCategory D, Y.IsGE (n + 1) → (G.obj Y).IsGE (n + 1))
    (X : DerivedCategory C) (hX : X.IsLE n) : (F.obj X).IsLE n := by
  show DerivedCategory.TStructure.t.IsLE (F.obj X) n
  rw [DerivedCategory.TStructure.t.isLE_iff_orthogonal n (n + 1) rfl]
  intro Y f hY
  have := hG Y hY
  have := hX
  have h0 : adj.homEquiv _ _ f = 0 := DerivedCategory.TStructure.t.zero _ n (n + 1) (by omega)
  rw [← (adj.homEquiv _ _).symm_apply_apply f, h0, Adjunction.homEquiv_counit, Functor.map_zero,
    Limits.zero_comp]

/-- Under the same hypotheses, `F` kills `H^{n+1}` of objects of `D^{≤ n}`. -/
theorem isZero_homology_obj_of_adjunction {F : DerivedCategory C ⥤ DerivedCategory D}
    {G : DerivedCategory D ⥤ DerivedCategory C} (adj : F ⊣ G) [F.PreservesZeroMorphisms] (n : ℤ)
    (hG : ∀ Y : DerivedCategory D, Y.IsGE (n + 1) → (G.obj Y).IsGE (n + 1))
    (X : DerivedCategory C) (hX : X.IsLE n) (m : ℤ) (hm : n < m) :
    IsZero ((DerivedCategory.homologyFunctor D m).obj (F.obj X)) :=
  (DerivedCategory.isLE_iff _ n).1 (isLE_obj_of_adjunction adj n hG X hX) m hm

/-- An isomorphism carries a vanishing cohomology object to a vanishing one. -/
theorem isZero_homology_of_isIso {P Q : DerivedCategory C} (β : P ⟶ Q) (hβ : IsIso β) (m : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor C m).obj P)) :
    IsZero ((DerivedCategory.homologyFunctor C m).obj Q) :=
  h.of_iso ((DerivedCategory.homologyFunctor C m).mapIso (asIso β)).symm

end TStructure

/-! ### The target -/

/-- `L(g')^*𝒪_X[0] ≅ 𝒪_{X'}[0]`. -/
def pullbackStructureObjIso :
    (smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains pointMap).obj
      structureObj ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit (ringedToposStructureRingSheaf zmodFourSite specZModFour
        zmodFourSite_contains pointSpace)) :=
  (smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains pointMap).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{0}
        (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains baseSpace))
          0).app (SheafOfModules.unit _)) ≪≫
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
      (smallEtaleRingedToposHom zmodFourSite specZModFour zmodFourSite_contains pointMap) 0 ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{0}
      (ringedToposStructureRingSheaf zmodFourSite specZModFour zmodFourSite_contains pointSpace))
        0).app (SheafOfModules.unit _)).symm

/-- `Hom(L(g')^*E, L(g')^*K[1]) = Ext^1_A(A', A') ≠ 0`. -/
theorem not_subsingleton_hom_pullback_residueObj_shift :
    ¬ Subsingleton ((smallEtaleDerivedModulePullback zmodFourSite specZModFour
      zmodFourSite_contains pointMap).obj residueObj ⟶
        ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
          pointMap).obj structureObj)⟦(1 : ℤ)⟧) := by
  let : HasDerivedCategory (ModuleCat.{0} baseRing) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{0} pointRing) := HasDerivedCategory.standard _
  intro hsub
  apply not_subsingleton_ext_one fourTwoRings_baseToPointRingHom
  let Φ' :=
    representedAffineDerivedAssociated zmodFourSite specZModFour zmodFourSite_contains pointObj
  let ext :=
    representedAffineDerivedExtension zmodFourSite specZModFour zmodFourSite_contains pointToBase
  let adj := RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction baseToPointRingHom
  let Rs := (ModuleCat.restrictScalars baseToPointRingHom).mapDerivedCategory
  let N1 := (DerivedCategory.singleFunctor (ModuleCat.{0} baseRing) 0).obj residueModule
  let A1 := (DerivedCategory.singleFunctor (ModuleCat.{0} pointRing) 0).obj
    (ModuleCat.of pointRing pointRing)
  let a₁ : (smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
      pointMap).obj residueObj ≅ Φ'.obj (ext.functor.obj N1) :=
    (representedAffineToposDerivedBaseChangeIso zmodFourSite specZModFour zmodFourSite_contains
      pointToBase).app N1
  let b : ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
      pointMap).obj structureObj)⟦(1 : ℤ)⟧ ≅ Φ'.obj (A1⟦(1 : ℤ)⟧) :=
    (shiftFunctor _ (1 : ℤ)).mapIso (pullbackStructureObjIso ≪≫
      (representedAffineDerivedAssociatedSingleUnitIso zmodFourSite specZModFour
        zmodFourSite_contains pointObj 0).symm) ≪≫
      ((Φ'.commShiftIso (1 : ℤ)).app A1).symm
  have h₁ := (Iso.homCongr a₁ b).subsingleton_congr.1 hsub
  have h₂ := ((representedAffineDerivedAssociatedFullyFaithful zmodFourSite specZModFour
    zmodFourSite_contains pointObj).homEquiv
    (X := ext.functor.obj N1) (Y := A1⟦(1 : ℤ)⟧)).subsingleton_congr.2 h₁
  have h₃ := (adj.homEquiv N1 (A1⟦(1 : ℤ)⟧)).subsingleton_congr.1 h₂
  let c : Rs.obj (A1⟦(1 : ℤ)⟧) ≅ N1⟦((1 : ℕ) : ℤ)⟧ :=
    (Rs.commShiftIso (1 : ℤ)).app A1 ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso
      (((ModuleCat.restrictScalars baseToPointRingHom).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of pointRing pointRing))
  have h₄ := (Iso.homCongr (Iso.refl N1) c).subsingleton_congr.1 h₃
  exact (Abelian.Ext.homEquiv (X := residueModule) (Y := residueModule)
    (n := 1)).subsingleton_congr.2 h₄


/-! ### The internal Hom on `X'` -/

/-- `R𝓗om(L(g')^*E, K')` with `K' = L(g')^*K`. -/
abbrev pullbackSheafHom :=
  ((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains pointSpace).obj
    (op ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
      pointMap).obj residueObj))).obj
    ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
      pointMap).obj structureObj)

/-- `K' = L(g')^*K` is bounded below. -/
theorem isBoundedBelow_pullback_structureObj :
    DerivedCategoryB.IsBoundedBelow ((smallEtaleDerivedModulePullback zmodFourSite specZModFour
      zmodFourSite_contains pointMap).obj structureObj) :=
  ⟨0, fun n hn => ((DerivedCategory.isGE_iff _ 0).1 inferInstance n hn).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso pullbackStructureObjIso)⟩

/-- `R𝓗om(L(g')^*E, K')` lies in `D_QCoh(𝒪_{X'})`. -/
theorem qcohDerived_pullbackSheafHom :
    QcohDerived zmodFourSite specZModFour zmodFourSite_contains pointSpace pullbackSheafHom :=
  qcohDerived_smallEtaleDerivedSheafHom pointSpace _ _
    (Or.inl ⟨isPseudoCoherent_smallEtaleDerivedModulePullback pointMap residueObj
        isPseudoCoherent_residueObj,
      isBoundedBelow_pullback_structureObj,
      derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ pointMap structureObj
        qcohDerived_structureObj⟩)

/-- If `H^1(R𝓗om(L(g')^*E, K')) = 0` then `Hom(L(g')^*E, K'[1]) = 0`. -/
theorem subsingleton_hom_pullback_residueObj_shift_of_isZero
    (hz : IsZero ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Space.Modules.{0, 0} zmodFourSite specZModFour zmodFourSite_contains
        pointSpace.1 pointSpace.2) 1).obj pullbackSheafHom)) :
    Subsingleton ((smallEtaleDerivedModulePullback zmodFourSite specZModFour
      zmodFourSite_contains pointMap).obj residueObj ⟶
        ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
          pointMap).obj structureObj)⟦(1 : ℤ)⟧) := by
  refine (homUnitShiftSmallEtaleDerivedSheafHomEquiv pointSpace _ _ 1).subsingleton_congr.1
    ⟨fun a b => ?_⟩
  have hbij := bijective_homologyFunctor_map_fromUnit
    (representedAffineFinalChart zmodFourSite specZModFour zmodFourSite_contains pointObj)
    (isTerminalChartOfIso pointObj (Iso.refl _))
    (isAffineChart_representedAffineFinalChart zmodFourSite specZModFour zmodFourSite_contains
      pointObj) (pullbackSheafHom⟦(1 : ℤ)⟧)
    (qcohDerived_shift pullbackSheafHom 1 qcohDerived_pullbackSheafHom)
  have hz' : IsZero ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Space.Modules.{0, 0} zmodFourSite specZModFour zmodFourSite_contains
        pointSpace.1 pointSpace.2) 0).obj (pullbackSheafHom⟦(1 : ℤ)⟧)) :=
    hz.of_iso (((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Space.Modules.{0, 0} zmodFourSite specZModFour zmodFourSite_contains
        pointSpace.1 pointSpace.2) 0).shiftIso
        (1 : ℤ) (0 : ℤ) (1 : ℤ) (by norm_num)).app pullbackSheafHom)
  exact hbij.1 (hz'.eq_of_tgt _ _)

/-! ### The comparison on the identity chart -/

/-- The algebraic-space map of an identity is the identity. -/
theorem representedSpaceMap_id (T : BigFppfOver zmodFourSite specZModFour zmodFourSite_contains) :
    representedSpaceMap zmodFourSite specZModFour zmodFourSite_contains (𝟙 T) = 𝟙 _ :=
  (schemeSpaceFunctor zmodFourSite specZModFour zmodFourSite_contains).map_id T

/-- **If the conclusion of Stacks 0DKI (3) held here, `H^1(R𝓗om(L(g')^*E, K'))` would
vanish.** Condition (2) of Stacks 0DKG on the identity chart makes
`RΓ(X, R𝓗om(E, K)) ⊗ᴸ_A A' ⟶ RΓ(X', R𝓗om(L(g')^*E, K'))` invertible, and its source has no
`H^1`: `RΓ(X, R𝓗om(E, K))` lies in degrees `≤ 0`. -/
theorem isZero_homology_one_pullbackSheafHom
    (hG : GeometricPointwiseBaseChange zmodFourSite specZModFour zmodFourSite_contains
      (𝟙 baseSpace) pointMap (𝟙 pointSpace) pointMap isPullback_pointMap.w
      (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains baseSpace).obj
        (op residueObj)).obj structureObj) pullbackSheafHom
      (smallEtaleDerivedPullbackSheafHomMap pointMap residueObj structureObj ≫
        ((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains pointSpace).obj
          (op ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
            pointMap).obj residueObj))).map (𝟙 _))) :
    IsZero ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Space.Modules.{0, 0} zmodFourSite specZModFour zmodFourSite_contains
        pointSpace.1 pointSpace.2) 1).obj pullbackSheafHom) := by
  let : HasDerivedCategory (ModuleCat.{0} baseRing) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{0} pointRing) := HasDerivedCategory.standard _
  have hA := (geometricPointwiseBaseChange_iff_affineChartwiseBaseChange isPullback_pointMap _
    qcohDerived_sheafHom_residueObj _ qcohDerived_pullbackSheafHom _).1 hG
  have hI := hA.isIso baseObj baseObj pointObj pointObj (𝟙 baseSpace) (𝟙 baseSpace) (𝟙 pointSpace)
    (𝟙 pointSpace) (𝟙 baseObj) pointToBase (𝟙 pointObj) pointToBase (by simp)
    (isEtale_of_isIso _ _ _ _) (isEtale_of_isIso _ _ _ _) (isEtale_of_isIso _ _ _ _)
    (IsPullback.of_vert_isIso ⟨by simp⟩) (by simp [representedSpaceMap_id]) (by simp)
    (by simp [representedSpaceMap_id]) (by simp)
  -- the derived sections of `M` lie in degrees `≤ 0`
  have hq₄ := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (𝟙 baseSpace) _
    qcohDerived_sheafHom_residueObj
  have hX₀ : ((representedAffineDerivedSections zmodFourSite specZModFour zmodFourSite_contains
      baseObj).obj
        ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
          (𝟙 baseSpace)).obj
          (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains
            baseSpace).obj (op residueObj)).obj structureObj))).IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = ((n + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
    refine IsZero.of_iso ?_ (representedAffineDerivedSectionsHomologyIso zmodFourSite
      specZModFour zmodFourSite_contains baseObj _ hq₄ _)
    refine (representedAffineSections zmodFourSite specZModFour zmodFourSite_contains
      baseObj).map_isZero ?_
    exact (isZero_homology_sheafHom_residueObj n).of_iso
      ((DerivedCategory.homologyFunctor _ _).mapIso
        ((smallEtaleDerivedModulePullbackIdentityIso zmodFourSite specZModFour
          zmodFourSite_contains baseSpace).app _))
  have := hX₀
  have hX₁' := Stacks.Homology.isLE_mapDerivedCategory_obj (ModuleCat.restrictScalars
    (representedAffineCommRingCatHom zmodFourSite specZModFour zmodFourSite_contains
      (𝟙 baseObj)).hom)
    ((representedAffineDerivedSections zmodFourSite specZModFour zmodFourSite_contains baseObj).obj
      ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
        (𝟙 baseSpace)).obj
        (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains baseSpace).obj
          (op residueObj)).obj structureObj))) 0
  have h1 := isZero_homology_obj_of_adjunction
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
      (representedAffineCommRingCatHom zmodFourSite specZModFour zmodFourSite_contains
        pointToBase).hom) 0
    (fun Y hY => Stacks.Cohomology.DerivedInternalHomPullback.isGE_mapDerivedCategory_obj
      (ModuleCat.restrictScalars _) Y 1 hY) _ hX₁' 1 (by norm_num)
  have h2 := isZero_homology_of_isIso _ hI 1 h1
  -- back to the sheaf on `X'`
  have hq₂ := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (𝟙 pointSpace) _
    qcohDerived_pullbackSheafHom
  have h3 : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{0} pointRing) 1).obj
      ((representedAffineDerivedSections zmodFourSite specZModFour zmodFourSite_contains
        pointObj).obj
          ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
            (𝟙 pointSpace)).obj pullbackSheafHom))) :=
    Dualizing.isZero_of_isZero_restrictScalars
      (representedAffineCommRingCatHom zmodFourSite specZModFour zmodFourSite_contains
        (𝟙 pointObj)).hom
      (h2.of_iso (((ModuleCat.restrictScalars _).mapDerivedCategoryHomologyIso 1).app _).symm)
  have := isIso_representedAffineDerivedAdjunction_counit_app zmodFourSite specZModFour
    zmodFourSite_contains pointObj _ hq₂
  let c := asIso ((representedAffineDerivedAdjunction zmodFourSite specZModFour
    zmodFourSite_contains pointObj).counit.app
      ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
        (𝟙 pointSpace)).obj pullbackSheafHom))
  have h4 : IsZero ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Space.Modules.{0, 0} zmodFourSite specZModFour zmodFourSite_contains
        pointSpace.1 pointSpace.2) 1).obj
          ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
            (𝟙 pointSpace)).obj pullbackSheafHom)) :=
    ((representedAffineAssociated zmodFourSite specZModFour zmodFourSite_contains
      pointObj).map_isZero h3).of_iso
        ((DerivedCategory.homologyFunctor _ 1).mapIso c.symm ≪≫
          ((representedAffineAssociated zmodFourSite specZModFour zmodFourSite_contains
            pointObj).mapDerivedCategoryHomologyIso 1).app _)
  exact h4.of_iso ((DerivedCategory.homologyFunctor _ 1).mapIso
    ((smallEtaleDerivedModulePullbackIdentityIso zmodFourSite specZModFour zmodFourSite_contains
      pointSpace).app pullbackSheafHom).symm)


/-! ### The counterexample -/

/-- **The conclusion of Stacks 0DKI (3) fails for `A = ℤ/4`.** For the cartesian square with
`X = Y = S = Spec ℤ/4`, `f = f' = 𝟙` and `g = g' : Spec ℤ/2 ⟶ S`, `K = 𝒪_X[0]`, `K' = L(g')^*K`,
`φ = 𝟙` and `E = (ℤ/2)^~[0]`, the conditions of Stacks 0DKG fail for
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, although they hold for `φ`
(`geometricPointwiseBaseChange_structureObj`), `K` is bounded below
(`isBoundedBelow_structureObj`) and `E` is pseudo-coherent (`isPseudoCoherent_residueObj`).
The map of Equation 0DKF fails to be invertible in degree `1`. -/
theorem not_geometricPointwiseBaseChange_sheafHom_residueObj :
    ¬ GeometricPointwiseBaseChange zmodFourSite specZModFour zmodFourSite_contains (𝟙 baseSpace)
      pointMap (𝟙 pointSpace) pointMap isPullback_pointMap.w
      (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains baseSpace).obj
        (op residueObj)).obj structureObj)
      (((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains pointSpace).obj
        (op ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
          pointMap).obj residueObj))).obj
          ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
            pointMap).obj structureObj))
      (smallEtaleDerivedPullbackSheafHomMap pointMap residueObj structureObj ≫
        ((smallEtaleDerivedSheafHom zmodFourSite specZModFour zmodFourSite_contains pointSpace).obj
          (op ((smallEtaleDerivedModulePullback zmodFourSite specZModFour zmodFourSite_contains
            pointMap).obj residueObj))).map (𝟙 _)) :=
  fun hG => not_subsingleton_hom_pullback_residueObj_shift
    (subsingleton_hom_pullback_residueObj_shift_of_isZero (isZero_homology_one_pullbackSheafHom hG))

/-- **Stacks 0DKI (3) is false as written.** It is not true that
for every cartesian square `g' ≫ f = f' ≫ g` of algebraic spaces, `K ∈ D_QCoh(𝒪_X)` bounded below
and `φ : L(g')^*K ⟶ K'` in `D_QCoh(𝒪_{X'})` satisfying the conditions of Stacks 0DKG, and every
pseudo-coherent `E`, the conditions of Stacks 0DKG hold for
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` (Stacks 08JF followed by `R𝓗om(L(g')^*E, φ)`). The
counterexample has `Y = S = Spec ℤ/4` and `g : Spec ℤ/2 ⟶ S`, which has infinite Tor dimension:
`not_geometricPointwiseBaseChange_sheafHom_residueObj`. The corrected statement, with `g` of finite
Tor dimension, is
`AlgebraicGeometry.Space.geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent`. -/
@[stacks 0DKI
    "(3) as written is false: the erratum's counterexample, A = Z/4, g : Spec Z/2 → Spec A"]
theorem not_forall_geometricPointwiseBaseChange_sheafHom_of_isPseudoCoherent :
    ¬ ∀ (B : BigFppfSite.{0}) (S : Scheme.{0}) (hS : B.Contains S)
      (X Y X' Y' : AlgebraicSpaces B S hS) (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : IsPullback g' f' f g)
      (K : DerivedCategory (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X))),
      QcohDerived B S hS X K →
      ∀ (K' : DerivedCategory (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X'))),
      QcohDerived B S hS X' K' →
      ∀ (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K'),
      GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ →
      DerivedCategoryB.IsBoundedBelow K →
      ∀ (E : DerivedCategory (SheafOfModules.{0} (ringedToposStructureRingSheaf B S hS X))),
      RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E →
      GeometricPointwiseBaseChange B S hS f g f' g' sq.w
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K)
        (((smallEtaleDerivedSheafHom B S hS X').obj
          (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).obj K')
        (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
          ((smallEtaleDerivedSheafHom B S hS X').obj
            (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ) := fun H =>
  not_geometricPointwiseBaseChange_sheafHom_residueObj
    (H zmodFourSite specZModFour zmodFourSite_contains baseSpace baseSpace pointSpace pointSpace
      (𝟙 baseSpace) pointMap (𝟙 pointSpace) pointMap isPullback_pointMap structureObj
      qcohDerived_structureObj _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ pointMap structureObj
        qcohDerived_structureObj)
      (𝟙 _) geometricPointwiseBaseChange_structureObj isBoundedBelow_structureObj residueObj
      isPseudoCoherent_residueObj)

end Stacks.Examples.PseudoCoherentSheafHomBaseChange

end
