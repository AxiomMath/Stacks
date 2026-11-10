module

public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonTwistProbes
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.StructureSheafPushforward
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The twists `𝒪, 𝒪(-1), …, 𝒪(-n)` form a semi-orthogonal family of exceptional objects

Let `k` be a field and `X = ℙⁿ_k`. This file proves, for the twists `𝒪(-a)[0]`, `0 ≤ a ≤ n`,
read as the probes `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.twistProbe`, the
hypotheses of `Stacks.Triangulated.ProbeKilling.mem_of_probes` that concern the twists alone:

* every nonzero endomorphism of `𝒪(-a)[0]` is invertible, and `𝒪(-a)[0] ≠ 0`, global functions
  on `ℙⁿ_k` being the field `k`;
* `Hom(𝒪(-a)[0], 𝒪(-a)[0][m]) = 0` for `m ≠ 0`;
* `Hom(𝒪(-b)[0], 𝒪(-a)[0][m]) = 0` for every `m` when `b < a`.

Each statement is moved by the twisting autoequivalence to a statement about morphisms out of
`𝒪_X[0]`, that is about the cohomology `H^m(X, 𝒪(e))` (Stacks 01XT): morphisms out of the
structure sheaf in the derived category are sheaf cohomology
(`Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology`), and the cohomology of a
twist `𝒪(e)` with `-n ≤ e` vanishes outside degree `0`, and in degree `0` too when `e < 0`.

## Main results

All names are in the namespace `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization`.

* `subsingleton_unitObject_hom_twistSingle`: `Hom(𝒪_X[0], 𝒪(e)[0][m]) = 0` for `m < 0`, and for
  `-n ≤ e` whenever `e < 0` or `m ≠ 0`.
* `isIso_of_ne_zero_unitObject`: every nonzero endomorphism of `𝒪_X[0]` is invertible.
* `twistProbe_isIso_of_ne_zero`, `twistProbe_not_isZero`, `twistProbe_self_shift`,
  `twistProbe_orth`: the hypotheses of `Stacks.Triangulated.ProbeKilling.mem_of_probes` about the
  twists.

## References

* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.Triangulated.ProbeKilling

namespace Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

universe u

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] opensSheafTensorAdditive opensSheafTensorObjAdditive
  opensHasMapBifunctorSheafTensor

variable (k : Type u) [Field k] (n : ℕ)

/-! ### The cohomology of the twists -/

/-- **`H^q(ℙⁿ_k, 𝒪(e)) = 0` for `-n ≤ e`, whenever `e < 0` or `q ≠ 0`** ([Stacks, Tag 01XT]):
the only nonzero cohomology of such a twist is `H^0(ℙⁿ_k, 𝒪(e)) = k[T₀, …, Tₙ]_e` for `e ≥ 0`, the
top-degree cohomology of a twist `-n ≤ e < 0` being free on an empty set of Laurent monomials. -/
theorem isZero_rightDerived_twistOver (e : ℤ) (q : ℕ) (he : -(n : ℤ) ≤ e) (hq : e < 0 ∨ q ≠ 0) :
    IsZero (((moduleGlobalSections (projectiveSpaceOverRing n (CommRingCat.of k))).rightDerived
      q).obj (twistOver n (Spec (CommRingCat.of k)) e)) := by
  open Stacks.ProjectiveSpace.Cohomology in
  have hsub : Subsingleton (twistCohomology Γ(Spec (CommRingCat.of k), ⊤) n e q) := by
    by_cases hqn : q = n ∧ e < 0
    · obtain ⟨rfl, hneg⟩ := hqn
      have hs : Subsingleton (negativeTwistPart Γ(Spec (CommRingCat.of k), ⊤) q e) := by
        refine ⟨fun x y => Subtype.ext ?_⟩
        have hx := x.2
        have hy := y.2
        change _ ∈ Finsupp.supported _ _ _ at hx hy
        rw [(negativeLaurentMonomials_eq_empty_iff q e).2 he, Finsupp.supported_empty,
          Submodule.mem_bot] at hx hy
        rw [hx, hy]
      exact ((twistCohomologyMonomial Γ(Spec (CommRingCat.of k), ⊤) q e).degreeTop
        hneg).toLinearEquiv.toEquiv.subsingleton
    · exact ModuleCat.isZero_iff_subsingleton.mp
        ((twistCohomologyMonomial Γ(Spec (CommRingCat.of k), ⊤) n e).vanishing q (by
          rintro (⟨rfl, h⟩ | h)
          · omega
          · exact hqn h))
  have : Subsingleton ↥(((moduleGlobalSections
      (projectiveSpaceOver n (Spec (CommRingCat.of k)))).rightDerived q).obj
        (twistOver n (Spec (CommRingCat.of k)) e)) :=
    @Equiv.subsingleton _ _ (ProjectiveSpaceHigherDirectImage.twistCohomologyIsoRestrictScalars
      n (Spec (CommRingCat.of k)) e q).toLinearEquiv.toEquiv.symm hsub
  exact ModuleCat.isZero_of_subsingleton _

/-- **`Hom(𝒪_X[0], 𝒪(e)[0][m]) = 0`** for `m < 0`, and for `-n ≤ e` whenever `e < 0` or `m ≠ 0`.
In negative degrees this is the t-structure: `𝒪_X[0]` lies in degrees `≤ 0` and `𝒪(e)[0][m]` in
degrees `≥ -m > 0`. In degrees `m ≥ 0` the group is `H^m(X, 𝒪(e))`, by
`Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology`, and that vanishes by
`isZero_rightDerived_twistOver`. -/
theorem subsingleton_unitObject_hom_twistSingle (e m : ℤ)
    (h : m < 0 ∨ (-(n : ℤ) ≤ e ∧ (e < 0 ∨ m ≠ 0))) :
    Subsingleton (Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n) ⟶
      (twistSingle k n e)⟦m⟧) := by
  rcases lt_or_ge m 0 with hm | hm
  · refine ((twistSingleZeroIso k n).homFromEquiv.subsingleton_congr).1 ?_
    change Subsingleton (twistSingle k n 0 ⟶ (shiftFunctor (DerivedCategory
      (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) m).obj (twistSingle k n e))
    have := (DerivedCategory.TStructure.t).isGE_shift (twistSingle k n e) 0 m (-m) (by omega)
    refine ⟨fun f g => ?_⟩
    rw [DerivedCategory.TStructure.t.zero f 0 (-m) (by omega),
      DerivedCategory.TStructure.t.zero g 0 (-m) (by omega)]
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    obtain ⟨he, hq⟩ := h.resolve_left (by omega)
    have : Subsingleton ↥(((_root_.SheafOfModules.evaluation
        (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf (op ⊤)).rightDerived q).obj
          (twistOver n (Spec (CommRingCat.of k)) e)) :=
      ModuleCat.subsingleton_of_isZero (isZero_rightDerived_twistOver k n e q he (by omega))
    exact (Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology
      (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf
      (twistOver n (Spec (CommRingCat.of k)) e) q).toEquiv.subsingleton

/-! ### Endomorphisms of the structure sheaf -/

/-- **Global functions on `ℙⁿ_k` form a field**: the structure morphism identifies them with the
global functions on `Spec k`, that is with `k`. -/
theorem isField_globalSections :
    IsField Γ(projectiveSpaceOverRing n (CommRingCat.of k), ⊤) := by
  have := ProjectiveSpaceHigherDirectImage.isIso_c_structureMorphism_projectiveSpaceOver
    n (Spec (CommRingCat.of k))
  have hiso : IsIso ((projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)).appTop) :=
    NatIso.isIso_app_of_isIso _ _
  let e₁ : Γ(Spec (CommRingCat.of k), ⊤) ≃+* Γ(projectiveSpaceOverRing n (CommRingCat.of k), ⊤) :=
    (asIso ((projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)).appTop)).commRingCatIsoToRingEquiv
  let e₂ : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  exact ((e₂.trans e₁).symm.toMulEquiv).isField (Field.toIsField k)

section Endomorphisms

variable {R : Sheaf (Opens.grothendieckTopology (projectiveSpaceOverRing n (CommRingCat.of k)))
  RingCat.{u}}

/-- The value of an endomorphism of the unit module at an open, as a map of rings of sections. -/
def unitApp (f : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)
    (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ) (x : R.obj.obj U) :
    R.obj.obj U :=
  (f.val.app U).hom x

/-- An endomorphism of the unit module is, at every open, multiplication by its value at `1`. -/
theorem unitApp_eq_mul (f : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)
    (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ) (x : R.obj.obj U) :
    unitApp k n f U x = x * unitApp k n f U 1 := by
  unfold unitApp
  calc (f.val.app U).hom x = (f.val.app U).hom (x • (1 : R.obj.obj U)) :=
        congrArg _ (mul_one x).symm
    _ = x • (f.val.app U).hom (1 : R.obj.obj U) := (f.val.app U).hom.map_smul x _
    _ = _ := rfl

/-- The value at an open of an endomorphism of the unit module at `1` is the restriction of its
value on global functions at `1`. -/
theorem unitApp_one (f : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)
    (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ) :
    unitApp k n f U 1 = R.obj.map (homOfLE le_top).op (unitApp k n f (op ⊤) 1) := by
  have h := PresheafOfModules.naturality_apply f.val ((homOfLE (le_top : U.unop ≤ ⊤)).op)
    (1 : R.obj.obj (op ⊤))
  change (f.val.app U).hom (R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op (1 : R.obj.obj (op ⊤))) =
    R.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op ((f.val.app (op ⊤)).hom (1 : R.obj.obj (op ⊤)))
      at h
  rwa [map_one] at h

/-- The value of a composite of endomorphisms of the unit module is the composite of values. -/
theorem unitApp_comp (f g : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)
    (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ) (x : R.obj.obj U) :
    unitApp k n (f ≫ g) U x = unitApp k n g U (unitApp k n f U x) := rfl

/-- The value of the identity endomorphism of the unit module is the identity. -/
theorem unitApp_id (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ)
    (x : R.obj.obj U) : unitApp k n (𝟙 (_root_.SheafOfModules.unit R)) U x = x := rfl

/-- The value of the zero endomorphism of the unit module is zero. -/
theorem unitApp_zero (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ)
    (x : R.obj.obj U) :
    unitApp k n (0 : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R) U x = 0 := rfl

/-- Two endomorphisms of the unit module agree as soon as they agree at `1` on every open. -/
theorem unit_endo_ext {f g : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R}
    (h : ∀ U, unitApp k n f U 1 = unitApp k n g U 1) : f = g := by
  apply (_root_.SheafOfModules.unitHomEquiv (_root_.SheafOfModules.unit R)).injective
  ext U
  exact h U

/-- The endomorphism of the unit module given by multiplication by a global function. -/
def unitMul (t : R.obj.obj (op ⊤)) : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R :=
  (_root_.SheafOfModules.unitHomEquiv (_root_.SheafOfModules.unit R)).symm
    (PresheafOfModules.sectionsMk (fun U => (R.obj.map (homOfLE le_top).op t : R.obj.obj U))
      (fun U V f => by
        change R.obj.map f (R.obj.map (homOfLE le_top).op t) = R.obj.map (homOfLE le_top).op t
        rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
        rfl))

/-- The value at `1` on an open of multiplication by a global function `t` is the restriction of
`t`. -/
theorem unitApp_unitMul (t : R.obj.obj (op ⊤))
    (U : (Opens (projectiveSpaceOverRing n (CommRingCat.of k)))ᵒᵖ) :
    unitApp k n (unitMul k n t) U 1 = R.obj.map (homOfLE le_top).op t :=
  congrArg (fun σ => σ.val U)
    ((_root_.SheafOfModules.unitHomEquiv (_root_.SheafOfModules.unit R)).apply_symm_apply _)

end Endomorphisms

/-- **Every nonzero endomorphism of the structure sheaf of `ℙⁿ_k` is invertible.** An
endomorphism of `𝒪_X` is multiplication by its value at `1`, a global function, and global
functions form a field. -/
theorem isIso_of_ne_zero_unit
    (e : _root_.SheafOfModules.unit (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf ⟶
      _root_.SheafOfModules.unit (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf)
    (he : e ≠ 0) : IsIso e := by
  set R := (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf
  have hF : IsField (R.obj.obj (op ⊤)) := isField_globalSections k n
  set s0 : R.obj.obj (op ⊤) := unitApp k n e (op ⊤) 1 with hs
  have hs0 : s0 ≠ 0 := by
    intro h0
    apply he
    refine unit_endo_ext k n fun U => ?_
    rw [unitApp_one k n e U, ← hs, h0, map_zero, unitApp_zero]
  obtain ⟨t, ht⟩ := hF.mul_inv_cancel hs0
  have ht' : t * s0 = 1 := (hF.mul_comm t s0).trans ht
  refine ⟨unitMul k n t, ?_, ?_⟩
  · refine unit_endo_ext k n fun U => ?_
    rw [unitApp_comp, unitApp_eq_mul k n (unitMul k n t), unitApp_unitMul, unitApp_one k n e U,
      ← hs, ← map_mul, ht, map_one, unitApp_id]
  · refine unit_endo_ext k n fun U => ?_
    rw [unitApp_comp, unitApp_eq_mul k n e, unitApp_unitMul, unitApp_one k n e U, ← hs,
      ← map_mul, ht', map_one, unitApp_id]

/-- **The structure sheaf of `ℙⁿ_k` is not zero**: its global functions form a field. -/
theorem not_isZero_unit :
    ¬ IsZero (_root_.SheafOfModules.unit
      (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf) := by
  intro h
  set R := (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf
  have hF : IsField (R.obj.obj (op ⊤)) := isField_globalSections k n
  have h1 := congrArg (fun φ => unitApp k n φ (op ⊤) 1) ((IsZero.iff_id_eq_zero _).1 h)
  simp only [unitApp_id, unitApp_zero] at h1
  obtain ⟨x, y, hxy⟩ := hF.exists_pair_ne
  apply hxy
  rw [← mul_one x, ← mul_one y, h1, mul_zero, mul_zero]

/-- **Every nonzero endomorphism of `𝒪_X[0]` in `D(𝒪_X)` is invertible**: the functor placing a
module in degree zero is fully faithful. -/
theorem isIso_of_ne_zero_unitObject
    (e : Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n) ⟶
      Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n)) (he : e ≠ 0) : IsIso e := by
  let F := DerivedCategory.singleFunctor (projectiveSpaceOverRing n (CommRingCat.of k)).Modules 0
  obtain ⟨e₀, rfl⟩ := F.map_surjective e
  have : IsIso e₀ := isIso_of_ne_zero_unit k n e₀ (fun h => he (h ▸ F.map_zero _ _))
  exact Functor.map_isIso F e₀

/-- **`𝒪_X[0] ≠ 0` in `D(𝒪_X)`.** -/
theorem not_isZero_unitObject :
    ¬ IsZero (Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n)) := by
  intro h
  let F := DerivedCategory.singleFunctor (projectiveSpaceOverRing n (CommRingCat.of k)).Modules 0
  exact not_isZero_unit k n ((IsZero.iff_id_eq_zero _).2
    (F.map_injective ((F.map_id _).trans (((IsZero.iff_id_eq_zero _).1 h).trans
      (F.map_zero _ _).symm))))

/-! ### The probe hypotheses -/

/-- The morphisms out of the probe of `𝒪(-b)` into a shift of `𝒪(-a)[0]` are the
morphisms out of `𝒪_X[0]` into the same shift of `𝒪(b - a)[0]`. -/
def twistProbeHomEquiv (a b m : ℤ) :
    ((twistProbe k n b).U ⟶ ((twistProbe k n b).G.obj (twistSingle k n (-a)))⟦m⟧) ≃
      (Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n) ⟶
        (twistSingle k n (b - a))⟦m⟧) :=
  ((shiftFunctor _ m).mapIso (twistSingleTensorIso k n (-a) b ≪≫
    twistSingleCongr k n (by ring))).homToEquiv

/-- **The probe objects are not zero.** -/
theorem twistProbe_not_isZero (a : ℤ) : ¬ IsZero (twistProbe k n a).P := fun h =>
  not_isZero_unitObject k n (((twistProbe k n a).G.map_isZero h).of_iso (twistProbe k n a).ι.symm)

/-- **Every nonzero endomorphism of a probe object is invertible.** The twisting
autoequivalence carries the endomorphisms of `𝒪(-a)[0]` to those of `𝒪_X[0]`. -/
theorem twistProbe_isIso_of_ne_zero (a : ℤ) (e : (twistProbe k n a).P ⟶ (twistProbe k n a).P)
    (he : e ≠ 0) : IsIso e := by
  let p := twistProbe k n a
  have h1 : p.ι.inv ≫ p.G.map e ≫ p.ι.hom ≠ 0 := by
    intro h0
    apply he
    apply p.ff.map_injective
    rw [p.G.map_zero]
    simpa using p.ι.hom ≫= h0 =≫ p.ι.inv
  have hX : IsIso (p.ι.inv ≫ p.G.map e ≫ p.ι.hom) := isIso_of_ne_zero_unitObject k n _ h1
  have : IsIso (p.G.map e) := by
    rw [show p.G.map e = p.ι.hom ≫ (p.ι.inv ≫ p.G.map e ≫ p.ι.hom) ≫ p.ι.inv by simp]
    exact IsIso.comp_isIso
  exact p.ff.isIso_of_isIso_map e

/-- Morphisms from the probe object of `𝒪(-b)` to a shift of `𝒪(-a)[0]` vanish as soon as the
corresponding cohomology of `𝒪(b - a)` does. -/
private theorem subsingleton_twistProbe_hom (a b m : ℤ)
    (h : m < 0 ∨ (-(n : ℤ) ≤ b - a ∧ (b - a < 0 ∨ m ≠ 0))) :
    Subsingleton ((twistProbe k n b).P ⟶ (twistProbe k n a).P⟦m⟧) :=
  ((twistProbe k n b).subsingleton_iff _ m).2
    ((twistProbeHomEquiv k n a b m).subsingleton_congr.2
      (subsingleton_unitObject_hom_twistSingle k n _ m h))

/-- **A probe object has no self-morphisms in nonzero degrees**: `H^m(X, 𝒪) = 0` for `m ≠ 0`. -/
theorem twistProbe_self_shift (a m : ℤ) (hm : m ≠ 0) :
    Subsingleton ((twistProbe k n a).P ⟶ (twistProbe k n a).P⟦m⟧) :=
  subsingleton_twistProbe_hom k n a a m (Or.inr ⟨by simp, Or.inr hm⟩)

/-- **Semi-orthogonality**: for `0 ≤ b < a ≤ n`, every morphism from `𝒪(-b)[0]` to a shift of
`𝒪(-a)[0]` vanishes, since `H^m(X, 𝒪(b - a)) = 0` for `-n ≤ b - a ≤ -1`. -/
theorem twistProbe_orth (a b : ℤ) (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ n) :
    (twistProbe k n b).Orth (twistProbe k n a).P := fun m =>
  subsingleton_twistProbe_hom k n a b m (Or.inr ⟨by omega, Or.inl (by omega)⟩)

end Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

end
