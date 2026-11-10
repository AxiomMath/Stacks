module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientShortExact
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningVanishingAboveDegree

/-!
# Twisting down on the blowup

Let `A` be a commutative ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec(A)`
in `I`, with twists `𝒪_X(t)`, `t ∈ ℤ`.

This file builds the general theory of *twisting down* that the proof of [Stacks, Tag 0GAC]
("A bit of uniformity, III") runs on: the canonical maps `𝒪_X(t) ⟶ 𝒪_X(t')` for `t' ≤ t`, the
fact that twisting down by `c` kills every module annihilated by `Iᶜ` ([Stacks, Tag 0GA9], in
the direction that proof uses), and the exactness, additivity and quasi-coherence of twisting.

The twists are indexed by **integers**, as the consumer of these results indexes them; at a
natural number `q` the twist `blowupTwistInt I q` is `blowupTwist I q` on the nose, and the
one-step map is `ambientTwistMap I q` (`blowupTwistLE_natCast_succ`), so the existing statements
about `ambientSections` and `thickeningSections` apply.

## The vanishing

Locally on `X` the image of `𝒪_X(t+1) ⟶ 𝒪_X(t)` is `I·𝒪_X(t)`: near any point it lies in
`D₊(b⁽¹⁾)` for some `b ∈ I`, and there the image of a section is `b` times a section
(`Stacks.Blowup.exists_restrict_appTwistShift_eq_smul`). The maps are `𝒪_X`-linear, so after `c`
steps the image of a section is, near any point, `a` times a section for some `a ∈ Iᶜ`
(`exists_restrict_blowupTwistLE_eq_globalSmulCenter`). On a local pure tensor `e ⊗ s` the map
`E ⊗ 𝒪_X(t'+c) ⟶ E ⊗ 𝒪_X(t')` is then `e ⊗ a·z = a·e ⊗ z = 0`, and a local pure tensor vanishing
near every point vanishes (`whiskerLeft_eq_zero_of_locally`).

## Implementation notes

The map `blowupTwistLE` is `descendMap`, a composite defined by `Int.leInduction` for an arbitrary
`ℤ`-indexed descending sequence, so its one-step unfolding is a statement about a variable index
and never compares two spellings of an index of `twistingSheaf` by unfolding the sheaf. Where an
index is only *equal* to `s + 1` (as `t' + ((k + 1 : ℕ) : ℤ)` in the induction) the comparison is
an `eqToHom` (`blowupTwistLE_eq_eqToHom_comp`), which costs nothing on sections.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupTwistInt`: the twist `𝒪_X(t)`, `t ∈ ℤ`.
* `Stacks.LocalCohomology.UniformityIII.blowupTwistLE`: the canonical map `𝒪_X(t) ⟶ 𝒪_X(t')`
  for `t' ≤ t`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.blowupTwistLE_refl`, `blowupTwistLE_trans`,
  `blowupTwistLE_succ`, `blowupTwistLE_natCast_succ`: the maps form a functor from `(ℤ, ≥)`.
* `Stacks.LocalCohomology.UniformityIII.whiskerLeft_blowupTwistLE_eq_zero`: **[Stacks, Tag 0GA9]**
  — if `Iᶜ` kills `E` then `E ⊗ 𝒪_X(t) ⟶ E ⊗ 𝒪_X(t')` is zero for `t' + c ≤ t`.
* `Stacks.LocalCohomology.UniformityIII.blowupΓMap_blowupTwistLE_ambientSections`,
  `blowupΓMap_whiskerLeft_blowupTwistLE_thickeningSections`: on the canonical sections the maps
  are the inclusions `Iᑫ ⊆ Iᑫ'`.
* `Stacks.LocalCohomology.UniformityIII.shortExact_whiskerRight_blowupTwistInt`,
  `isQuasicoherent_tensor_blowupTwistInt`, `additive_tensorRight_blowupTwistInt`,
  `isZero_tensor_blowupTwistInt`: twisting is exact, preserves quasi-coherence and is additive.
* `Stacks.LocalCohomology.UniformityIII.globalSmulCenter_app_whiskerRight`,
  `globalSmulCenter_app_tensor_eq_zero`: multiplication by a global function on `E ⊗ F` is the one
  on `E` tensored with `F`, so a function killing `E` kills `E ⊗ F`.

## References

* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0GA9](https://stacks.math.columbia.edu/tag/0GA9)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.RegularSequence (globalSmulCenter)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul whiskerLeft_tmul whiskerRight_tmul
  tensorObjTmul_smul_right tensorObjTmul_zero_left tensorObjTmul_eq_zero_of_locally)
open Stacks.SheafOfModules.TensorStalkRingedSpace (sheafifyUnit)
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal'

/-! ### Descending maps along a sequence indexed by the integers -/

section Descend

variable {C : Type*} [Category C] (F : ℤ → C) (f : ∀ t, F (t + 1) ⟶ F t)

/-- **The composite of a descending sequence of maps**: for `t' ≤ t`, the composite
`F t ⟶ F (t - 1) ⟶ ⋯ ⟶ F t'` of the given maps `f s : F (s + 1) ⟶ F s`. -/
def descendMap {t t' : ℤ} (h : t' ≤ t) : F t ⟶ F t' :=
  Int.leInduction (m := t') (motive := fun n _ => F n ⟶ F t') (𝟙 (F t'))
    (fun n _ φ => f n ≫ φ) t h

/-- The empty composite is the identity. -/
theorem descendMap_refl (t : ℤ) : descendMap F f (le_refl t) = 𝟙 (F t) :=
  Int.leInduction_base (motive := fun n _ => F n ⟶ F t) _ _

/-- One more step at the top of a descending composite. -/
theorem descendMap_succ_left {t t' : ℤ} (h : t' ≤ t) (h' : t' ≤ t + 1) :
    descendMap F f h' = f t ≫ descendMap F f h :=
  Int.leInduction_add_one (motive := fun n _ => F n ⟶ F t') _ _ t h

/-- Descending composites compose. -/
theorem descendMap_trans {t t' t'' : ℤ} (h : t' ≤ t) (h' : t'' ≤ t') :
    descendMap F f h ≫ descendMap F f h' = descendMap F f (h'.trans h) := by
  induction t, h using Int.leInduction with
  | base => rw [descendMap_refl, Category.id_comp]
  | succ n hn ih =>
    rw [descendMap_succ_left F f hn, descendMap_succ_left F f (h'.trans hn), Category.assoc, ih]

/-- The one-step descending composite is the given map. -/
theorem descendMap_succ (t : ℤ) (h : t ≤ t + 1) : descendMap F f h = f t := by
  rw [descendMap_succ_left F f (le_refl t), descendMap_refl, Category.comp_id]

/-- A descending composite between equal indices is the canonical identification. -/
theorem descendMap_eq_eqToHom {t t' : ℤ} (hts : t = t') (h : t' ≤ t) :
    descendMap F f h = eqToHom (congrArg F hts) := by
  subst hts
  exact descendMap_refl F f t

/-- One more step at the top of a descending composite, with the top index written as `s + 1`
only up to an equality. -/
theorem descendMap_eq_eqToHom_comp {t t' s : ℤ} (hts : t = s + 1) (h : t' ≤ t) (h' : t' ≤ s) :
    descendMap F f h = eqToHom (congrArg F hts) ≫ f s ≫ descendMap F f h' := by
  subst hts
  rw [eqToHom_refl, Category.id_comp]
  exact descendMap_succ_left F f h' h

end Descend

/-! ### Multiplication by a global function and the tensor product -/

section Smul

variable {X : Scheme.{u}}

/-- `Stacks.RegularSequence.globalSmulCenter` on sections over an open, at the spelling
`Γ(M, V)` that carries the scalar action. -/
theorem globalSmulCenter_app_val_app (r : Γ(X, ⊤)) (M : X.Modules) (V : X.Opens)
    (m : Γ(M, V)) :
    (((globalSmulCenter X r).app M).val.app (op V)).hom m = X.presheaf.map V.leTop.op r • m :=
  rfl

/-- Multiplication by the global function `1` is the identity on sections. -/
theorem globalSmulCenter_one_app_val_app (M : X.Modules) (V : X.Opens) (m : Γ(M, V)) :
    (((globalSmulCenter X 1).app M).val.app (op V)).hom m = m := by
  rw [globalSmulCenter_app_val_app, map_one, one_smul]

/-- Multiplication by a product of global functions is the composite of the two
multiplications, on sections. -/
theorem globalSmulCenter_mul_app_val_app (r r' : Γ(X, ⊤)) (M : X.Modules) (V : X.Opens)
    (m : Γ(M, V)) :
    (((globalSmulCenter X (r * r')).app M).val.app (op V)).hom m =
      (((globalSmulCenter X r).app M).val.app (op V)).hom
        ((((globalSmulCenter X r').app M).val.app (op V)).hom m) := by
  rw [globalSmulCenter_app_val_app, globalSmulCenter_app_val_app, globalSmulCenter_app_val_app,
    map_mul, mul_smul]

/-- A zero morphism of sheaves of modules is zero on sections. -/
theorem zero_val_app_apply {M N : X.Modules} (V : X.Opensᵒᵖ) (m : M.val.obj V) :
    (((0 : M ⟶ N).val.app V).hom m) = 0 := by
  change ((0 : M.val ⟶ N.val).app V).hom m = 0
  simp

/-- Equal morphisms of sheaves of modules agree on sections. -/
private theorem val_app_hom_congr {M N : X.Modules} {f g : M ⟶ N} (h : f = g) (V : X.Opensᵒᵖ)
    (m : M.val.obj V) : (f.val.app V).hom m = (g.val.app V).hom m := by
  rw [h]

/-- **A scalar moves out of the left factor of a local pure tensor.** The canonical map into the
sheafified tensor product is linear. -/
theorem smul_tensorObjTmul (Y : RingedSpace.{u, u})
    (M N : SheafOfModules.{u} (structureSheafRing Y))
    (U : (Opens Y.carrier)ᵒᵖ) (r : Y.presheaf.obj U) (a : M.val.obj U) (b : N.val.obj U) :
    r • tensorObjTmul Y M N U a b = tensorObjTmul Y M N U (r • a) b :=
  (((sheafifyUnit Y (PresheafOfModules.tensorObj (O := Y.presheaf) M.val N.val)).app U).hom.map_smul
    r (a ⊗ₜ[Y.presheaf.obj U] b)).symm.trans
    (congrArg (Stacks.SheafOfModules.OnSpace.tensorObjSection Y M N U)
      (TensorProduct.smul_tmul' r a b))

/-- **Multiplication by a global function commutes with tensoring on the right**: on `E ⊗ F` it
is multiplication on `E` tensored with `F`. The module structure of a tensor product is the one
of its first factor. -/
theorem globalSmulCenter_app_whiskerRight (E F : X.Modules) (r : Γ(X, ⊤)) :
    (globalSmulCenter X r).app E ▷ F = (globalSmulCenter X r).app (E ⊗ F) := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace
    (f := (globalSmulCenter X r).app E ▷ F) (g := (globalSmulCenter X r).app (E ⊗ F))
    fun U e s => ?_
  refine (whiskerRight_tmul X.toRingedSpace ((globalSmulCenter X r).app E) F U e s).trans ?_
  exact (smul_tensorObjTmul X.toRingedSpace E F U (X.presheaf.map U.unop.leTop.op r) e s).symm

/-- **A global function killing `E` kills `E ⊗ F`.** -/
theorem globalSmulCenter_app_tensor_eq_zero (E F : X.Modules) (r : Γ(X, ⊤))
    (h : (globalSmulCenter X r).app E = 0) : (globalSmulCenter X r).app (E ⊗ F) = 0 := by
  rw [← globalSmulCenter_app_whiskerRight, h]
  exact ((MonoidalCategory.tensorHom_id _ F).symm.trans
    (Stacks.SheafOfModules.OnSpace.tensorHom_eq _ 0 (𝟙 F))).trans
    (AlgebraicGeometry.SheafOfModules.tensorSheafMap_zero_left _ (𝟙 F))

/-- **A whiskering `E ◁ φ` vanishes as soon as `φ` is locally divisible by functions killing
`E`.** If near every point the restriction of the image of every local section under `φ` is a
multiple of a section by a global function `r` with `r · E = 0`, then `E ◁ φ = 0`: on a local
pure tensor `e ⊗ s` it is `e ⊗ φ(s)`, which near every point is `e ⊗ r·z = r·e ⊗ z = 0`. -/
theorem whiskerLeft_eq_zero_of_locally (E : X.Modules) {F G : X.Modules} (φ : F ⟶ G)
    (hφ : ∀ (U : X.Opens) (s : F.val.obj (op U)) (x : X), x ∈ U →
      ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ r : Γ(X, ⊤),
        (globalSmulCenter X r).app E = 0 ∧ ∃ z : G.val.obj (op V),
          (G.val.map (homOfLE hVU).op).hom ((φ.val.app (op U)).hom s) =
            (((globalSmulCenter X r).app G).val.app (op V)).hom z) :
    E ◁ φ = 0 := by
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace
    (f := E ◁ φ) (g := (0 : (E ⊗ F : X.Modules) ⟶ E ⊗ G)) fun U e s => ?_
  refine Eq.trans ?_ (zero_val_app_apply U _).symm
  refine (whiskerLeft_tmul X.toRingedSpace E φ U e s).trans ?_
  refine tensorObjTmul_eq_zero_of_locally X.toRingedSpace E G U.unop e _ fun x hx => ?_
  obtain ⟨V, hVU, hxV, r, hr, z, hz⟩ := hφ U.unop s x hx
  refine ⟨V, hVU, hxV, ?_⟩
  refine (congrArg (tensorObjTmul X.toRingedSpace E G (op V)
    ((E.val.map (homOfLE hVU).op).hom e)) hz).trans ?_
  refine (tensorObjTmul_smul_right X.toRingedSpace E G (op V)
    (X.presheaf.map V.leTop.op r) _ z).trans ?_
  refine (congrArg (fun w => tensorObjTmul X.toRingedSpace E G (op V) w z) ?_).trans
    (tensorObjTmul_zero_left X.toRingedSpace E G (op V) z)
  exact (val_app_hom_congr hr _ _).trans (zero_val_app_apply _ _)

end Smul

/-! ### The integer twists and the maps between them -/

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **The twist `𝒪_X(t)` for an integer `t`.** At a natural number `q` it is `blowupTwist I q`
on the nose. -/
abbrev blowupTwistInt (t : ℤ) : (blowupScheme I).Modules :=
  twistingSheaf (Stacks.Blowup.reesGrading I) t

/-- **The canonical map `𝒪_X(t) ⟶ 𝒪_X(t')` for `t' ≤ t`**: the composite of the maps
`Stacks.Blowup.twistShiftMap I s : 𝒪_X(s + 1) ⟶ 𝒪_X(s)` for `t' ≤ s < t`. -/
def blowupTwistLE {t t' : ℤ} (h : t' ≤ t) : blowupTwistInt I t ⟶ blowupTwistInt I t' :=
  descendMap (blowupTwistInt I) (Stacks.Blowup.twistShiftMap I) h

/-- `blowupTwistLE` at equal indices is the identity. -/
theorem blowupTwistLE_refl (t : ℤ) : blowupTwistLE I (le_refl t) = 𝟙 _ :=
  descendMap_refl _ _ t

/-- The maps `blowupTwistLE` compose. -/
theorem blowupTwistLE_trans {t t' t'' : ℤ} (h : t' ≤ t) (h' : t'' ≤ t') :
    blowupTwistLE I h ≫ blowupTwistLE I h' = blowupTwistLE I (h'.trans h) :=
  descendMap_trans _ _ h h'

/-- `blowupTwistLE` by one step is `Stacks.Blowup.twistShiftMap`. -/
theorem blowupTwistLE_succ (t : ℤ) :
    blowupTwistLE I (Int.le_add_one (le_refl t)) = Stacks.Blowup.twistShiftMap I t :=
  descendMap_succ _ _ t _

/-- `blowupTwistLE` by one step at natural indices is
`Stacks.LocalCohomology.UniformityIII.ambientTwistMap`; this is what lets the statements about
`ambientSections` and `thickeningSections` be applied. -/
theorem blowupTwistLE_natCast_succ (q : ℕ) :
    blowupTwistLE I (Nat.cast_le.mpr (Nat.le_succ q) : ((q : ℕ) : ℤ) ≤ ((q + 1 : ℕ) : ℤ)) =
      ambientTwistMap I q :=
  descendMap_succ _ _ (q : ℤ) _

/-- `blowupTwistLE` with its top index written as `s + 1` only up to an equality. -/
theorem blowupTwistLE_eq_eqToHom_comp {t t' s : ℤ} (hts : t = s + 1) (h : t' ≤ t)
    (h' : t' ≤ s) :
    blowupTwistLE I h = eqToHom (congrArg (blowupTwistInt I) hts) ≫
      Stacks.Blowup.twistShiftMap I s ≫ blowupTwistLE I h' :=
  descendMap_eq_eqToHom_comp _ _ hts h h'

/-! ### Global sections -/

/-- **`blowupTwistLE` on the canonical sections**: the composite
`Iᑫ → H⁰(X, 𝒪_X(q)) → H⁰(X, 𝒪_X(q'))` is the canonical map of `Iᑫ'` along `Iᑫ ⊆ Iᑫ'`. -/
theorem blowupΓMap_blowupTwistLE_ambientSections {q q' : ℕ} (h : (q' : ℤ) ≤ q)
    (x : (I ^ q : Ideal A)) :
    blowupΓMap I (blowupTwistLE I h) (ambientSections I q x) =
      ambientSections I q' ⟨x, Ideal.pow_le_pow_right (by exact_mod_cast h) x.2⟩ := by
  have hq : q' ≤ q := by exact_mod_cast h
  induction q, hq using Nat.le_induction with
  | base =>
    rw [blowupTwistLE_refl]
    rfl
  | succ n hn ih =>
    have h₁ : ((n : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := Nat.cast_le.mpr (Nat.le_succ n)
    have h₂ : (q' : ℤ) ≤ (n : ℤ) := Nat.cast_le.mpr hn
    rw [← blowupTwistLE_trans I h₁ h₂, blowupΓMap_comp, blowupTwistLE_natCast_succ,
      blowupΓMap_ambientTwistMap_ambientSections]
    exact ih h₂ _

/-- **`𝒪_{Yₙ} ⊗ blowupTwistLE` on the canonical sections**: the composite
`Iᑫ → H⁰(X, 𝒪_{Yₙ}(q)) → H⁰(X, 𝒪_{Yₙ}(q'))` is the canonical map of `Iᑫ'` along `Iᑫ ⊆ Iᑫ'`. -/
theorem blowupΓMap_whiskerLeft_blowupTwistLE_thickeningSections (n : ℕ) {q q' : ℕ}
    (h : (q' : ℤ) ≤ q) (x : (I ^ q : Ideal A)) :
    blowupΓMap I (thickeningSheaf I n ◁ blowupTwistLE I h) (thickeningSections I n q x) =
      thickeningSections I n q' ⟨x, Ideal.pow_le_pow_right (by exact_mod_cast h) x.2⟩ := by
  have hc := comp_leftUnitor_inv_whiskerRight (thickeningProj I n) (blowupTwistLE I h)
  refine (congrArg (fun φ => blowupΓMap I φ (ambientSections I q x)) hc.symm).trans ?_
  exact congrArg (blowupΓMap I (thickeningTwistProj I n q'))
    (blowupΓMap_blowupTwistLE_ambientSections I h x)

/-! ### Twisting down kills a module annihilated by a power of `I` -/

/-- The pullback of a product is the product of the pullbacks. -/
theorem pullbackCoeff_mul (a b : A) :
    pullbackCoeff I (a * b) = pullbackCoeff I a * pullbackCoeff I b := by
  simp only [pullbackCoeff, map_mul]

/-- The pullback of `1` is `1`. -/
theorem pullbackCoeff_one : pullbackCoeff I 1 = 1 := by
  simp only [pullbackCoeff, map_one]

section Local

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-- **One step down is locally divisible by an element of `I`.** Near every point the image of
a local section of `𝒪_X(t+1)` in `𝒪_X(t)` is `b` times a section, for some `b ∈ I`: this is
`Stacks.Blowup.exists_restrict_appTwistShift_eq_smul` at a degree-one standard open containing
the point (`Stacks.Blowup.exists_reesDegOne_mem_primeCompl`), with the scalar read as
multiplication by the global function `b` pulls back to. -/
theorem exists_restrict_twistShiftMap_eq_globalSmulCenter (t : ℤ) (U : (blowupScheme I).Opens)
    (s : (blowupTwistInt I (t + 1)).val.obj (op U)) (x : blowupScheme I) (hx : x ∈ U) :
    ∃ (V : (blowupScheme I).Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ b ∈ I,
      ∃ c : (blowupTwistInt I t).val.obj (op V),
        ((blowupTwistInt I t).val.map (homOfLE hVU).op).hom
            (((Stacks.Blowup.twistShiftMap I t).val.app (op U)).hom s) =
          (((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
            (blowupTwistInt I t)).val.app (op V)).hom c := by
  refine (Stacks.Blowup.exists_reesDegOne_mem_primeCompl I x).elim
    fun b h => h.elim fun hb hbx => ?_
  refine (Stacks.Blowup.exists_restrict_appTwistShift_eq_smul I t U s x hx hb hbx
      (((SheafOfModules.unit (blowupScheme I).ringCatSheaf).val.map
          (homOfLE (le_top : U ≤ ⊤)).op) (pullbackCoeff I b))
      (fun y => val_appTop_toSpec I b y.1)).elim fun V h => h.elim fun hVU h =>
    h.2.elim fun c hc => ⟨V, hVU, h.1, b, hb, c, ?_⟩
  refine Eq.trans (congrArg (fun w => ((blowupTwistInt I t).val.map (homOfLE hVU).op).hom w)
    (Stacks.Blowup.appTwistShift_eq I t (op U) s).symm) ?_
  exact hc.trans rfl

/-- **Twisting down by `k` is locally divisible by an element of `Iᵏ`.** Near every point the
image of a local section of `𝒪_X(t' + k)` in `𝒪_X(t')` is `a` times a section, for some
`a ∈ Iᵏ`. By induction on `k`, from `exists_restrict_twistShiftMap_eq_globalSmulCenter`: the
maps are `𝒪_X`-linear, so a multiple by `b` of a section stays a multiple by `b` after the
remaining `k` steps, and `b · Iᵏ ⊆ Iᵏ⁺¹`. -/
theorem exists_restrict_blowupTwistLE_eq_globalSmulCenter (t' : ℤ) (k : ℕ) (h : t' ≤ t' + k)
    (U : (blowupScheme I).Opens) (s : (blowupTwistInt I (t' + k)).val.obj (op U))
    (x : blowupScheme I) (hx : x ∈ U) :
    ∃ (V : (blowupScheme I).Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ a ∈ I ^ k,
      ∃ z : (blowupTwistInt I t').val.obj (op V),
        ((blowupTwistInt I t').val.map (homOfLE hVU).op).hom
            (((blowupTwistLE I h).val.app (op U)).hom s) =
          (((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app
            (blowupTwistInt I t')).val.app (op V)).hom z := by
  induction k generalizing U x with
  | zero =>
    refine ⟨U, le_rfl, hx, 1, by simp, ((blowupTwistInt I t').val.map (homOfLE le_rfl).op).hom
      (((blowupTwistLE I h).val.app (op U)).hom s), ?_⟩
    rw [pullbackCoeff_one]
    exact (globalSmulCenter_one_app_val_app (blowupTwistInt I t') U _).symm
  | succ k ih =>
    have hts : t' + ((k + 1 : ℕ) : ℤ) = (t' + k) + 1 := by push_cast; ring
    have hk : t' ≤ t' + k := by omega
    have happ : ((blowupTwistLE I h).val.app (op U)).hom s =
        ((blowupTwistLE I hk).val.app (op U)).hom
          (((Stacks.Blowup.twistShiftMap I (t' + k)).val.app (op U)).hom
            (((eqToHom (congrArg (blowupTwistInt I) hts)).val.app (op U)).hom s)) :=
      val_app_hom_congr (blowupTwistLE_eq_eqToHom_comp I hts h hk) _ s
    obtain ⟨V₁, hV₁U, hxV₁, b, hb, c, hc⟩ := exists_restrict_twistShiftMap_eq_globalSmulCenter I
      (t' + k) U (((eqToHom (congrArg (blowupTwistInt I) hts)).val.app (op U)).hom s) x hx
    obtain ⟨V, hVV₁, hxV, a, ha, z, hz⟩ := ih hk V₁ c x hxV₁
    refine ⟨V, hVV₁.trans hV₁U, hxV, b * a,
      by rw [pow_succ']; exact Ideal.mul_mem_mul hb ha, z, ?_⟩
    rw [happ]
    refine (PresheafOfModules.map_comp_apply (blowupTwistInt I t').val (homOfLE hV₁U).op
      (homOfLE hVV₁).op _).trans ?_
    refine (congrArg (fun w => ((blowupTwistInt I t').val.map (homOfLE hVV₁).op) w)
      (PresheafOfModules.naturality_apply (blowupTwistLE I hk).val (homOfLE hV₁U).op
        _).symm).trans ?_
    refine (congrArg (fun w => ((blowupTwistInt I t').val.map (homOfLE hVV₁).op)
      (((blowupTwistLE I hk).val.app (op V₁)).hom w)) hc).trans ?_
    refine (congrArg (fun w => ((blowupTwistInt I t').val.map (homOfLE hVV₁).op) w)
      (val_app_hom_congr ((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).naturality
        (blowupTwistLE I hk)) (op V₁) c).symm).trans ?_
    refine (PresheafOfModules.naturality_apply
      ((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app (blowupTwistInt I t')).val
      (homOfLE hVV₁).op _).symm.trans ?_
    refine (congrArg (fun w => (((globalSmulCenter (blowupScheme I) (pullbackCoeff I b)).app
      (blowupTwistInt I t')).val.app (op V)).hom w) hz).trans ?_
    rw [pullbackCoeff_mul]
    exact (globalSmulCenter_mul_app_val_app _ _ (blowupTwistInt I t') V z).symm

end Local

/-- **Twisting down by `c` kills a module annihilated by `Iᶜ`** ([Stacks, Tag 0GA9], the
direction used in the proof of [Stacks, Tag 0GAC]). If every `a ∈ Iᶜ` kills `E`, then
`E ⊗ 𝒪_X(t) ⟶ E ⊗ 𝒪_X(t')` is zero whenever `t' + c ≤ t`.

The map factors through `E ⊗ 𝒪_X(t' + c)`, and on that factor it vanishes by
`whiskerLeft_eq_zero_of_locally`: twisting down by `c` is locally divisible by elements of `Iᶜ`
(`exists_restrict_blowupTwistLE_eq_globalSmulCenter`), and these kill `E`. -/
theorem whiskerLeft_blowupTwistLE_eq_zero (E : (blowupScheme I).Modules) {c : ℕ} {t t' : ℤ}
    (hE : ∀ a ∈ I ^ c, (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app E = 0)
    (h : t' ≤ t) (hc : t' + c ≤ t) : E ◁ blowupTwistLE I h = 0 := by
  have h₁ : t' ≤ t' + c := by omega
  rw [← blowupTwistLE_trans I hc h₁, MonoidalCategory.whiskerLeft_comp,
    whiskerLeft_eq_zero_of_locally E (blowupTwistLE I h₁) (fun U s x hx => ?_), comp_zero]
  obtain ⟨V, hVU, hxV, a, ha, z, hz⟩ :=
    exists_restrict_blowupTwistLE_eq_globalSmulCenter I t' c h₁ U s x hx
  exact ⟨V, hVU, hxV, pullbackCoeff I a, hE a ha, z, hz⟩

/-! ### Twisting is exact, additive and preserves quasi-coherence -/

/-- **Every integer twist on the blowup is flat** ([Stacks, Tag 05P2]), at the spelling of the
ring sheaf that `mono_whiskerRight_blowupTwistInt` uses. -/
theorem isFlat_blowupTwistInt (t : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (blowupScheme I).sheaf) (blowupTwistInt I t) :=
  Stacks.Blowup.isFlat_twistingSheaf_reesGrading I t

/-- **Whiskering a monomorphism by an integer twist is a monomorphism**: the twist is flat. -/
theorem mono_whiskerRight_blowupTwistInt {F G : (blowupScheme I).Modules} (f : F ⟶ G)
    (hf : Mono f) (t : ℤ) : Mono (f ▷ blowupTwistInt I t) := by
  rw [whiskerRight_eq_tensorSheafMap]
  have hm : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (blowupScheme I).sheaf).flip.obj (blowupTwistInt I t)).PreservesMonomorphisms :=
    have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (blowupScheme I).sheaf).flip.obj (blowupTwistInt I t)) := (isFlat_blowupTwistInt I t).1
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  let tensor := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (blowupScheme I).sheaf
  have equation := (congrArg (((tensor.map f).app (blowupTwistInt I t)) ≫ ·)
    ((tensor.obj G).map_id (blowupTwistInt I t))).trans (Category.comp_id _)
  exact (congrArg Mono equation).mpr (@Functor.map_mono _ _ _ _ _ hm _ _ f hf)

/-- A whiskered complex is a complex. -/
theorem whiskerRight_comp_whiskerRight_eq_zero {E₁ E₂ E₃ : (blowupScheme I).Modules}
    (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (w : f ≫ g = 0) (H : (blowupScheme I).Modules) :
    f ▷ H ≫ g ▷ H = 0 :=
  (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
    ((congrArg (fun φ : E₁ ⟶ E₃ => φ ▷ H) w).trans (zero_whiskerRight_eq_zero I H))

/-- **Twisting is exact**: a short exact sequence of sheaves of modules on the blowup stays short
exact after tensoring with `𝒪_X(t)`. Exactness in the middle and on the right is
[Stacks, Tag 01CC]; on the left it is the flatness of the twist. -/
theorem shortExact_whiskerRight_blowupTwistInt {E₁ E₂ E₃ : (blowupScheme I).Modules}
    (f : E₁ ⟶ E₂) (g : E₂ ⟶ E₃) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (t : ℤ) :
    (ShortComplex.mk (f ▷ blowupTwistInt I t) (g ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I f g w _)).ShortExact := by
  have hepi : Epi g := hS.epi_g
  obtain ⟨_, hex⟩ := @AlgebraicGeometry.SheafOfModules.tensorSheafMap_exact
    (blowupScheme I).toRingedSpace (ShortComplex.mk f g w) (blowupTwistInt I t) hS.exact hepi
  exact ShortComplex.ShortExact.mk'
    (exact_mk_of_eq (whiskerRight_eq_tensorSheafMap I _ _).symm
      (whiskerRight_eq_tensorSheafMap I _ _).symm hex)
    (mono_whiskerRight_blowupTwistInt I f hS.mono_f t)
    (epi_whiskerRight_of_epi I g hepi _)

/-- **Twisting preserves quasi-coherence**: `E ⊗ 𝒪_X(t)` is quasi-coherent for quasi-coherent
`E` ([Stacks, Tag 01CE]), the twist being quasi-coherent. -/
instance isQuasicoherent_tensor_blowupTwistInt (E : (blowupScheme I).Modules)
    [E.IsQuasicoherent] (t : ℤ) :
    (E ⊗ blowupTwistInt I t : (blowupScheme I).Modules).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj (X := blowupScheme I)
    E (blowupTwistInt I t) inferInstance
    (Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf
      (Stacks.Blowup.reesGrading I) t)

/-- **Twisting is additive**: `- ⊗ 𝒪_X(t)` is an additive functor, the sheafified tensor product
being additive in its first variable. -/
instance additive_tensorRight_blowupTwistInt (t : ℤ) :
    (MonoidalCategory.tensorRight (blowupTwistInt I t)).Additive where
  map_add {F G f g} := by
    change (f + g) ▷ blowupTwistInt I t = f ▷ blowupTwistInt I t + g ▷ blowupTwistInt I t
    rw [whiskerRight_eq_tensorSheafMap, whiskerRight_eq_tensorSheafMap,
      whiskerRight_eq_tensorSheafMap]
    exact Stacks.AlgebraicGeometry.ProjTwistedSections.tensorSheafMap_add_left _ _ f g

/-- **Twisting a zero object gives a zero object.** -/
theorem isZero_tensor_blowupTwistInt {E : (blowupScheme I).Modules} (hE : IsZero E) (t : ℤ) :
    IsZero (E ⊗ blowupTwistInt I t : (blowupScheme I).Modules) :=
  (MonoidalCategory.tensorRight (blowupTwistInt I t)).map_isZero hE

end Stacks.LocalCohomology.UniformityIII

end
