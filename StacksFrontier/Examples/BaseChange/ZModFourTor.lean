module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.Injective
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# Self-injectivity of `ℤ/4` and `Tor₁^{ℤ/4}(ℤ/2, ℤ/2) ≠ 0`

This file proves the facts about `ℤ/4` underlying the counterexample to case (2) of
[Stacks, Tag 08IE] for `S = X = Spec ℤ/4`, `f = id`, `E = (ℤ/2)~`, `𝒢^• = 𝒪_X` and
`g : Spec ℤ/2 ⟶ Spec ℤ/4`.

## Main results

* `Stacks.Examples.ZModFour.baer_zmodFour`: `ℤ/4` is self-injective (Baer's criterion).
* `Stacks.Examples.ZModFour.derivedHomTwoFourIso`: `RHom_{ℤ/4}(ℤ/2, ℤ/4) ≅ ℤ/2[0]`.
* `Stacks.Examples.ZModFour.not_isZero_homology_neg_one_derivedExtension`: the derived base
  change `ℤ/2 ⊗ᴸ_{ℤ/4} ℤ/2` has nonzero cohomology in degree `-1`, i.e.
  `Tor₁^{ℤ/4}(ℤ/2, ℤ/2) ≠ 0`, computed on the `2`-periodic free resolution
  `⋯ ⟶ ℤ/4 ⟶ ℤ/4 ⟶ ℤ/4 ⟶ ℤ/2` (`Stacks.Examples.ZModFour.resolution`).

## References

* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Examples.ZModFour

/-- The reduction `ℤ/4 → ℤ/2`. -/
abbrev toTwo : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : (2 : ℕ) ∣ 4) (ZMod 2)

/-- `ℤ/2` as a `ℤ/4`-module. -/
@[instance_reducible]
def moduleTwo : Module (ZMod 4) (ZMod 2) := Module.compHom (ZMod 2) toTwo

attribute [local instance] moduleTwo

/-- `ℤ/2` as an object of `Mod(ℤ/4)`. -/
abbrev two : ModuleCat.{0} (ZMod 4) := ModuleCat.of (ZMod 4) (ZMod 2)

/-- The free module of rank one. -/
abbrev four : ModuleCat.{0} (ZMod 4) := ModuleCat.of (ZMod 4) (ZMod 4)

/-- The `2`-periodic complex `⋯ ⟶ ℤ/4 ⟶ ℤ/4 ⟶ ℤ/4`, the differential being `2 = 1 + 1`. -/
def periodic : ChainComplex (ModuleCat.{0} (ZMod 4)) ℕ :=
  ChainComplex.of (fun _ => four) (fun _ => 𝟙 four + 𝟙 four) (fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun x => by
      change (x + x) + (x + x) = 0
      rw [← two_mul, ← two_mul, ← mul_assoc,
        show ((2 : ZMod 4) * 2) = 0 by decide, zero_mul]))

/-- The reduction `ℤ/4 ⟶ ℤ/2`, as a map of `ℤ/4`-modules. -/
def reduce : four ⟶ two :=
  ModuleCat.ofHom
    { toFun := fun x => toTwo x
      map_add' := fun x y => map_add toTwo x y
      map_smul' := fun r x => map_mul toTwo r x }

/-- Each differential of `periodic` is multiplication by `2`, i.e. `𝟙 + 𝟙`. -/
theorem periodic_d (n : ℕ) : periodic.d (n + 1) n = 𝟙 four + 𝟙 four := by
  simp [periodic]

/-- The augmentation of the periodic complex. -/
def augmentation : periodic ⟶ (ChainComplex.single₀ (ModuleCat.{0} (ZMod 4))).obj two :=
  (ChainComplex.toSingle₀Equiv periodic two).symm ⟨reduce, by
    rw [periodic_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x =>
      (by decide : ∀ x : ZMod 4, toTwo (x + x) = 0) x)⟩

/-- The degree-zero component of `augmentation` is `reduce`. -/
theorem augmentation_f_zero : augmentation.f 0 = reduce :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The periodic complex is exact in every positive degree. -/
theorem periodic_exactAt_succ (m : ℕ) : periodic.ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff' periodic (m + 2) (m + 1) m (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (periodic.d (m + 1) m).hom x = 0 at hx
  rw [periodic_d] at hx
  change x + x = 0 at hx
  obtain ⟨y, hy⟩ := (by decide : ∀ x : ZMod 4, x + x = 0 → ∃ y : ZMod 4, y + y = x) x hx
  refine ⟨y, ?_⟩
  show (periodic.d (m + 2) (m + 1)).hom y = x
  rwa [periodic_d]

/-- The augmentation `periodic ⟶ ℤ/2[0]` is a quasi-isomorphism. -/
instance quasiIso_augmentation : QuasiIso augmentation := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        change (augmentation.f 0).hom x = 0 at hx
        rw [augmentation_f_zero] at hx
        change toTwo x = 0 at hx
        obtain ⟨y, hy⟩ :=
          (by decide : ∀ x : ZMod 4, toTwo x = 0 → ∃ y : ZMod 4, y + y = x) x hx
        refine ⟨y, ?_⟩
        change (periodic.d 1 0).hom y = x
        rwa [periodic_d]
      · change Epi (augmentation.f 0)
        rw [augmentation_f_zero]
        have hs : ∀ y : ZMod 2, ∃ x : ZMod 4, toTwo x = y := by decide
        exact (ModuleCat.epi_iff_surjective reduce).2 fun y => hs y
    all_goals rfl
  | succ m =>
    rw [quasiIsoAt_iff_exactAt']
    · exact periodic_exactAt_succ m
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The periodic projective resolution of `ℤ/2` over `ℤ/4`. -/
def resolution : ProjectiveResolution two where
  complex := periodic
  projective := fun _ => inferInstanceAs (Projective (ModuleCat.of (ZMod 4) (ZMod 4)))
  π := augmentation

/-- The periodic complex after extension of scalars along `ℤ/4 → ℤ/2`. -/
abbrev reducedPeriodic : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  ((ModuleCat.extendScalars.{0, 0, 0} toTwo).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    periodic

/-- In a `ℤ/2`-module, `𝟙 + 𝟙 = 0`. -/
theorem id_add_id_eq_zero (M : ModuleCat.{0} (ZMod 2)) : 𝟙 M + 𝟙 M = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun x => by
    show x + x = 0
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul])

/-- The differentials of the reduced periodic complex vanish. -/
theorem reducedPeriodic_d (n : ℕ) : reducedPeriodic.d (n + 1) n = 0 := by
  have h : (ModuleCat.extendScalars.{0, 0, 0} toTwo).map (𝟙 four + 𝟙 four) = 0 := by
    rw [Functor.map_add, CategoryTheory.Functor.map_id, id_add_id_eq_zero]
  show (ModuleCat.extendScalars.{0, 0, 0} toTwo).map (periodic.d (n + 1) n) = 0
  rw [periodic_d]
  exact h

/-- The terms of the reduced periodic complex are nonzero: `ℤ/2 ⊗_{ℤ/4} ℤ/4 ≅ ℤ/2`. -/
theorem nontrivial_reducedPeriodic_X (n : ℕ) : Nontrivial (reducedPeriodic.X n) := by
  show Nontrivial (TensorProduct (ZMod 4)
    ((ModuleCat.restrictScalars toTwo).obj (ModuleCat.of (ZMod 2) (ZMod 2))) (ZMod 4))
  have : Nontrivial ((ModuleCat.restrictScalars toTwo).obj (ModuleCat.of (ZMod 2) (ZMod 2))) :=
    inferInstanceAs (Nontrivial (ZMod 2))
  exact (TensorProduct.rid (ZMod 4)
    ((ModuleCat.restrictScalars toTwo).obj (ModuleCat.of (ZMod 2) (ZMod 2)))).toEquiv.nontrivial

/-- `H_1` of the reduced periodic complex is nonzero. -/
theorem not_isZero_reducedPeriodic_homology_one : ¬ IsZero (reducedPeriodic.homology 1) := by
  intro hz
  have hex : reducedPeriodic.ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_isZero_homology reducedPeriodic 1).2 hz
  rw [HomologicalComplex.exactAt_iff' reducedPeriodic 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at hex
  have := nontrivial_reducedPeriodic_X 1
  obtain ⟨x, hx⟩ := exists_ne (0 : reducedPeriodic.X 1)
  obtain ⟨y, hy⟩ := hex x (by
    show (reducedPeriodic.d 1 0).hom x = 0
    rw [reducedPeriodic_d]
    rfl)
  apply hx
  rw [← hy]
  show (reducedPeriodic.d 2 1).hom y = 0
  rw [reducedPeriodic_d]
  rfl

/-- **`Tor₁^{ℤ/4}(ℤ/2, ℤ/2) ≠ 0`**, as the first left derived functor of extension of scalars
along `ℤ/4 → ℤ/2` at `ℤ/2`. -/
theorem not_isZero_leftDerived_one :
    ¬ IsZero (((ModuleCat.extendScalars.{0, 0, 0} toTwo).leftDerived 1).obj two) := fun h =>
  not_isZero_reducedPeriodic_homology_one
    (h.of_iso (RingTheory.TorIndependence.isoLeftDerivedObjHomology toTwo resolution 1))

attribute [local instance] HasDerivedCategory.standard

/-- **`Tor₁^{ℤ/4}(ℤ/2, ℤ/2) ≠ 0`, derivedly**: the cohomology in degree `-1` of the derived
base change `ℤ/2 ⊗ᴸ_{ℤ/4} ℤ/2` is nonzero. -/
theorem not_isZero_homology_neg_one_derivedExtension :
    ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{0} (ZMod 2)) (-1)).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{0, 0, 0}
          toTwo).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{0} (ZMod 4)) 0).obj two))) := fun h =>
  not_isZero_leftDerived_one
    (h.of_iso (RingTheory.TorIndependence.singleDerivedExtensionIsoLeftDerivedOfResolution
      toTwo resolution 1).symm)

/-- **`ℤ/4` is self-injective**: it satisfies Baer's criterion as a module over itself. -/
theorem baer_zmodFour : Module.Baer (ZMod 4) (ZMod 4) := by
  intro I g
  by_cases h1 : (1 : ZMod 4) ∈ I
  · refine ⟨LinearMap.smulRight LinearMap.id (g ⟨1, h1⟩), fun x hx => ?_⟩
    rw [LinearMap.smulRight_apply, LinearMap.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (mul_one x)
  have h3 : (3 : ZMod 4) ∉ I := fun h3 => h1 (by
    have := I.mul_mem_left 3 h3
    rwa [show (3 : ZMod 4) * 3 = 1 by decide] at this)
  by_cases h2 : (2 : ZMod 4) ∈ I
  · have hy : (2 : ZMod 4) * g ⟨2, h2⟩ = 0 := by
      rw [← smul_eq_mul, ← map_smul, show (2 : ZMod 4) • (⟨2, h2⟩ : I) = 0 from
        Subtype.ext (show (2 : ZMod 4) * 2 = 0 by decide), map_zero]
    obtain ⟨c, hc⟩ := (by decide : ∀ y : ZMod 4, 2 * y = 0 → ∃ c : ZMod 4, 2 * c = y) _ hy
    refine ⟨LinearMap.smulRight LinearMap.id c, fun x hx => ?_⟩
    rw [LinearMap.smulRight_apply, LinearMap.id_apply, smul_eq_mul]
    fin_cases x
    · exact (zero_mul c).trans ((map_zero g).symm.trans (congrArg g (Subtype.ext rfl)))
    · exact absurd hx h1
    · exact hc.trans (congrArg g (Subtype.ext rfl))
    · exact absurd hx h3
  · refine ⟨0, fun x hx => ?_⟩
    fin_cases x
    · exact (map_zero g).symm.trans (congrArg g (Subtype.ext rfl))
    · exact absurd hx h1
    · exact absurd hx h2
    · exact absurd hx h3


/-! ### `RHom_{ℤ/4}(ℤ/2, ℤ/4) = ℤ/2[0]` -/

section RHom

open CochainComplex.HomComplex

/-- `ℤ/2` in degree zero. -/
abbrev twoComplex : CochainComplex (ModuleCat.{0} (ZMod 4)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj two

/-- `ℤ/4` in degree zero. -/
abbrev fourComplex : CochainComplex (ModuleCat.{0} (ZMod 4)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj four

/-- Every term of `fourComplex` is an injective `ℤ/4`-module. -/
instance injective_fourComplex_X (n : ℤ) : Injective (fourComplex.X n) := by
  by_cases hn : n = 0
  · subst hn
    have : Module.Injective (ZMod 4) (ZMod 4) := baer_zmodFour.injective
    exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 four).symm
      (Module.injective_object_of_injective_module (ZMod 4) (ZMod 4))
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 four n hn).injective

/-- The complex `ℤ/4[0]` is K-injective. -/
instance isKInjective_fourComplex : fourComplex.IsKInjective :=
  CochainComplex.isKInjective_of_injective fourComplex 0

/-- The Hom complex `𝓗om^•(ℤ/2[0], ℤ/4[0])`. -/
abbrev homComplex : CochainComplex (ModuleCat.{0} (ZMod 4)) ℤ :=
  CochainComplex.HomComplexR (ZMod 4) twoComplex fourComplex

/-- The Hom complex `𝓗om^•(ℤ/2[0], ℤ/4[0])` vanishes in every nonzero degree. -/
theorem isZero_homComplex_X (n : ℤ) (hn : n ≠ 0) : IsZero (homComplex.X n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y => Cochain.ext _ _ fun p q hpq => ?_⟩
  by_cases hp : p = 0
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 four q
      (by omega)).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 two p hp).eq_of_src _ _

/-- The inclusion `ℤ/2 ⟶ ℤ/4`, `x ↦ 2x`. -/
def twoToFour : ZMod 2 →ₗ[ZMod 4] ZMod 4 where
  toFun x := 2 * ((ZMod.val x : ℕ) : ZMod 4)
  map_add' := by decide
  map_smul' := by decide

/-- `{0, 2} ⊆ ℤ/4` read back in `ℤ/2`. -/
def halve (x : ZMod 4) : ZMod 2 := if x = 2 then 1 else 0

/-- The value at `1` of the degree-zero component of a cochain `ℤ/2[0] ⟶ ℤ/4[0]`. -/
def evalOne (z : Cochain twoComplex fourComplex 0) : ZMod 4 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 four).hom.hom
    ((z.v 0 0 (add_zero 0)).hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 two).inv.hom (1 : ZMod 2)))

/-- `evalOne` is additive. -/
theorem evalOne_add (z w : Cochain twoComplex fourComplex 0) :
    evalOne (z + w) = evalOne z + evalOne w := by
  simp [evalOne, Cochain.add_v]

/-- The value `evalOne z` is killed by `2`. -/
theorem two_mul_evalOne (z : Cochain twoComplex fourComplex 0) : 2 * evalOne z = 0 := by
  have h2 : (2 : ZMod 4) • (1 : ZMod 2) = 0 := by decide
  rw [evalOne, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_smul, h2]
  simp only [map_zero]

/-- The cochain `ℤ/2[0] ⟶ ℤ/4[0]` given in degree zero by `c • (x ↦ 2x)`. -/
def cochainOf (c : ZMod 2) : Cochain twoComplex fourComplex 0 :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 two).hom ≫
    ModuleCat.ofHom (((ZMod.val c : ℕ) : ZMod 4) • twoToFour) ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 four).inv) 0

/-- The value at `1` of `cochainOf c` is `2c`. -/
theorem evalOne_cochainOf (c : ZMod 2) :
    evalOne (cochainOf c) = 2 * ((ZMod.val c : ℕ) : ZMod 4) := by
  simp only [evalOne, cochainOf, Cochain.single_v]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearMap.smul_apply,
    smul_eq_mul]
  show ((ZMod.val c : ℕ) : ZMod 4) * twoToFour 1 = _
  simp only [twoToFour, LinearMap.coe_mk, AddHom.coe_mk]
  revert c
  decide

/-- **`Hom^0(ℤ/2[0], ℤ/4[0]) ≅ ℤ/2`**, additively. -/
def cochainZeroAddEquiv : Cochain twoComplex fourComplex 0 ≃+ ZMod 2 where
  toFun z := halve (evalOne z)
  invFun := cochainOf
  left_inv z := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 0 := by omega
      simp only [cochainOf, Cochain.single_v]
      have e : z.v 0 0 hpq = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 two).hom ≫
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 two).inv ≫ z.v 0 0 hpq ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 four).hom) ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 four).inv := by simp
      rw [e]
      congr 2
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      have key : ∀ a : ZMod 4, 2 * a = 0 →
          (((ZMod.val (halve a) : ℕ) : ZMod 4) * 2) = a := by decide
      rcases hx x with rfl | rfl
      · simp only [map_zero]
      · have := key _ (two_mul_evalOne z)
        simp only [evalOne] at this
        simp only [ModuleCat.hom_ofHom, LinearMap.smul_apply, ModuleCat.hom_comp,
          LinearMap.comp_apply, smul_eq_mul]
        rw [← this]
        simp only [twoToFour, LinearMap.coe_mk, AddHom.coe_mk]
        rw [show ((ZMod.val (1 : ZMod 2) : ℕ) : ZMod 4) = 1 by decide, mul_one]
        rfl
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 two p hp).eq_of_src _ _
  right_inv c := by
    simp only [evalOne_cochainOf]
    exact (by decide : ∀ c : ZMod 2, halve (2 * ((ZMod.val c : ℕ) : ZMod 4)) = c) c
  map_add' z w := by
    simp only [evalOne_add]
    exact (by decide : ∀ a b : ZMod 4, 2 * a = 0 → 2 * b = 0 →
      halve (a + b) = halve a + halve b) _ _ (two_mul_evalOne z) (two_mul_evalOne w)

/-- **`Hom^0(ℤ/2[0], ℤ/4[0]) ≅ ℤ/2`** in `Mod(ℤ/4)`. -/
def homComplexXZeroIso : homComplex.X 0 ≅ two :=
  LinearEquiv.toModuleIso
    { AddMonoidHom.toZModLinearMap 4 cochainZeroAddEquiv.toAddMonoidHom with
      invFun := cochainZeroAddEquiv.symm
      left_inv := cochainZeroAddEquiv.left_inv
      right_inv := cochainZeroAddEquiv.right_inv }

attribute [local instance] HasDerivedCategory.standard

/-- **`RHom_{ℤ/4}(ℤ/2, ℤ/4) ≅ ℤ/2[0]`**. -/
def derivedHomTwoFourIso :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := ZMod 4)).hom.obj
        (Opposite.op (DerivedCategory.Q.obj twoComplex), DerivedCategory.Q.obj fourComplex) ≅
      DerivedCategory.Q.obj twoComplex :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := ZMod 4)).homIso twoComplex fourComplex ≪≫
    DerivedCategory.Q.mapIso
      (CategoryTheory.Functor.isoSingleFunctorObj homComplex 0 isZero_homComplex_X ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso homComplexXZeroIso)

end RHom

end Stacks.Examples.ZModFour
