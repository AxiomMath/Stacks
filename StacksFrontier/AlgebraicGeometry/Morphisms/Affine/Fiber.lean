module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Localization.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of an affine morphism

For an affine morphism of schemes `f : X ⟶ Y` and a point `y : Y`, this file identifies the
scheme-theoretic fibre `f.fiber y` with the spectrum of `κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y`.

Mathlib has this description only for a morphism of the form `Spec S ⟶ Spec R`
(`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso`); for a general affine morphism it records
only that the fibre is affine.  The missing ingredient, supplied here, is the ring-level
description of the stalk of the pushforward: over an affine open `V ∋ y` with preimage
`f⁻¹V` (affine, because `f` is), the stalk `(f_* 𝒪_X)_y` is the localization of `Γ(X, f⁻¹V)`
at the image of the prime complement of `y`.  Everything else is formal: that localization
statement makes the square

```
  Γ(Y, V) ⟶ Γ(X, f⁻¹V)
     ↓            ↓
  𝒪_{Y,y} ⟶ (f_* 𝒪_X)_y
```

a pushout of commutative rings, hence its spectrum a pullback of schemes, which pastes against
the affine square `Spec Γ(X, f⁻¹V) ⟶ X` over `Spec Γ(Y, V) ⟶ Y` to give
`Spec ((f_* 𝒪_X)_y) ≅ X ×_Y Spec 𝒪_{Y,y}`; one further base change along
`Spec κ(y) ⟶ Spec 𝒪_{Y,y}` is the fibre.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.pushforwardStalk`: the stalk `(f_* 𝒪_X)_y`.
* `AlgebraicGeometry.Scheme.Hom.pushforwardGerm`: the germ map `Γ(X, f⁻¹V) ⟶ (f_* 𝒪_X)_y`.
* `AlgebraicGeometry.Scheme.Hom.pushforwardStalkMap`: the canonical `𝒪_{Y,y} ⟶ (f_* 𝒪_X)_y`,
  which is the stalk at `y` of the comorphism of `f`, together with the induced
  `𝒪_{Y,y}`-algebra structure.
* `AlgebraicGeometry.Scheme.Hom.fiberIsoSpecResidueFieldTensorPushforwardStalk`: the fibre
  comparison isomorphism `f.fiber y ≅ Spec (κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y)`.
* `AlgebraicGeometry.Scheme.Hom.fiberHomeoPrimeSpectrum`: its underlying homeomorphism
  `f ⁻¹' {y} ≃ₜ PrimeSpectrum (κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isLocalization_pushforwardStalk_of_isCompact`: the stalk of the
  pushforward is the localization of the sections over the preimage, whenever that preimage is
  quasi-compact and quasi-separated.  This is the only step that is not formal, and affineness
  of `f` is not what it uses: the preimage enters only through the Qcqs lemma.
* `AlgebraicGeometry.Scheme.Hom.isLocalization_pushforwardStalk`: the same for an affine
  morphism, whose preimages of affine opens are affine.
* `AlgebraicGeometry.Scheme.Hom.isPullback_SpecMap_pushforwardStalkMap`:
  `Spec ((f_* 𝒪_X)_y) ≅ X ×_Y Spec 𝒪_{Y,y}`, as a pullback square.
* `AlgebraicGeometry.Scheme.Hom.exists_isPullback_fiberTensor` and
  `...fiberIsoSpecResidueFieldTensorPushforwardStalk_hom_fiberToSpecResidueField`: the fibre
  comparison, and the fact that it is an isomorphism of `κ(y)`-schemes.

## Implementation notes

The scheme universe `u` is the only universe here and it is forced: `Spec` and the tensor
product of `CommRingCat.{u}` objects both stay in `Type u`, and `Scheme.Hom.fiber` is a pullback
in `Scheme.{u}`.  Nothing is narrowed.

`pushforwardStalk` is a `def` and not an `abbrev` on purpose, so that the `𝒪_{Y,y}`-algebra
instance on it is found at one spelling only; the lemmas about `pushforwardGerm` are stated at
that pinned spelling for the same reason.

The `Algebra Γ(X, f⁻¹V) ((f_* 𝒪_X)_y)` structure used by
`isLocalization_pushforwardStalk` depends on the proof `y ∈ V`, so it cannot be a global
instance; it is supplied by a `letI` in the statement, exactly as Mathlib does for
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk'`.

The map `Spec ((f_* 𝒪_X)_y) ⟶ X` depends on a choice of affine open neighbourhood of `y`
(Mathlib's `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq` is the corresponding independence
statement for the structure sheaf, which has no analogue here yet), so
`exists_isPullback_fiberTensor` produces it existentially.  The leg to `Spec κ(y)` is canonical,
which is what makes the fibre comparison itself independent of all choices.

This module carries no Stacks tag.  The statement it proves is used by the Stacks Project
inside the proof of Tag 0C3B and in the fibre description of a normalization, but it is not
itself the content of a numbered Stacks result, and no tag was invented for it.

## References

* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8), affine morphisms.
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B), the stalk of the
  pushforward along a normalization, which is the intended consumer.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat
open scoped TensorProduct

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

section Helpers

variable {Z : Scheme.{u}}

/-- Any two restriction maps of the structure presheaf between the same pair of opens agree:
the morphisms of `Opens` form a thin category. -/
lemma Scheme.presheaf_map_eq_homOfLE {U W : Z.Opens} (i : op U ⟶ op W) (h : W ≤ U) :
    Z.presheaf.map i = Z.presheaf.map (homOfLE h).op :=
  congrArg Z.presheaf.map (Subsingleton.elim _ _)

/-- A point of an affine open lies in the basic open of a section iff the section avoids the
prime ideal corresponding to that point. -/
lemma IsAffineOpen.mem_basicOpen_iff_mem_primeCompl {U : Z.Opens} (hU : IsAffineOpen U)
    (x : U) (s : Γ(Z, U)) :
    (x : Z) ∈ Z.basicOpen s ↔ s ∈ (hU.primeIdealOf x).asIdeal.primeCompl := by
  let := hU.isLocalization_stalk x
  rw [Z.mem_basicOpen s x x.2,
    ← IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk x)
      (hU.primeIdealOf x).asIdeal s,
    TopCat.Presheaf.stalk_open_algebraMap Z.presheaf x]

/-- The restriction of a section to any open contained in its basic open is a unit. -/
lemma Scheme.isUnit_map_of_le_basicOpen {U W : Z.Opens} (s : Γ(Z, U)) (hWU : W ≤ U)
    (hW : W ≤ Z.basicOpen s) : IsUnit (Z.presheaf.map (homOfLE hWU).op s) := by
  have key : ∀ (x : Z) (hx : x ∈ W),
      IsUnit (Z.presheaf.germ W x hx (Z.presheaf.map (homOfLE hWU).op s)) := by
    intro x hx
    rw [Z.presheaf.germ_res_apply (homOfLE hWU) x hx]
    exact (Z.mem_basicOpen s x (hWU hx)).mp (hW hx)
  exact Z.toRingedSpace.isUnit_of_isUnit_germ W _ key

/-- An open that *equals* the basic open of a section of an affine open is the corresponding
localization.  The open is kept abstract so that this applies to an open presented in another
way, such as the preimage of a basic open under a morphism. -/
lemma IsAffineOpen.isLocalization_away_of_eq {U W : Z.Opens} (hU : IsAffineOpen U) (r : Γ(Z, U))
    (hWU : W ≤ U) (hW : W = Z.basicOpen r) :
    letI : Algebra Γ(Z, U) Γ(Z, W) := (Z.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    IsLocalization.Away r Γ(Z, W) := by
  subst hW
  exact hU.isLocalization_basicOpen r

/-- The same statement for a quasi-compact quasi-separated open in place of an affine one: this
is the **Qcqs lemma** `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs` with the open kept
abstract in the same way.  An affine open is quasi-compact and quasi-separated, so this subsumes
`IsAffineOpen.isLocalization_away_of_eq`; that form is kept because it needs no topological
hypotheses at its call sites. -/
lemma isLocalization_away_of_eq_of_isCompact {U W : Z.Opens} (hc : IsCompact (U : Set Z))
    (hq : IsQuasiSeparated (U : Set Z)) (r : Γ(Z, U)) (hWU : W ≤ U) (hW : W = Z.basicOpen r) :
    letI : Algebra Γ(Z, U) Γ(Z, W) := (Z.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    IsLocalization.Away r Γ(Z, W) := by
  subst hW
  exact isLocalization_basicOpen_of_qcqs hc hq r

end Helpers

namespace Scheme.Hom

/-! ### The stalk of the pushforward of the structure sheaf -/

/-- The stalk at `y` of the pushforward `f_* 𝒪_X` of the structure sheaf of `X`. -/
def pushforwardStalk (f : X ⟶ Y) (y : Y) : CommRingCat.{u} :=
  (f.base _* X.presheaf).stalk y

/-- The germ map `Γ(X, f⁻¹V) ⟶ (f_* 𝒪_X)_y`. -/
def pushforwardGerm (f : X ⟶ Y) (V : Y.Opens) (y : Y) (hy : y ∈ V) :
    Γ(X, f ⁻¹ᵁ V) ⟶ f.pushforwardStalk y :=
  (f.base _* X.presheaf).germ V y hy

/-- The canonical map `𝒪_{Y,y} ⟶ (f_* 𝒪_X)_y`, the stalk at `y` of the comorphism of `f`. -/
def pushforwardStalkMap (f : X ⟶ Y) (y : Y) :
    Y.presheaf.stalk y ⟶ f.pushforwardStalk y :=
  (TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c

/-- The pushforward stalk as an algebra over the local ring of `Y` at `y`. -/
instance algebra_stalk_pushforwardStalk (f : X ⟶ Y) (y : Y) :
    Algebra (Y.presheaf.stalk y) (f.pushforwardStalk y) :=
  (f.pushforwardStalkMap y).hom.toAlgebra

/-- The residue field at `y` as an algebra over the local ring at `y`. -/
instance _root_.AlgebraicGeometry.Scheme.algebra_stalk_residueField (y : Y) :
    Algebra (Y.presheaf.stalk y) (Y.residueField y) :=
  (Y.residue y).hom.toAlgebra

/-- The structure map of the algebra `(f_* 𝒪_X)_y` over `𝒪_{Y,y}` is `pushforwardStalkMap`. -/
@[simp]
lemma algebraMap_pushforwardStalk (f : X ⟶ Y) (y : Y) :
    algebraMap (Y.presheaf.stalk y) (f.pushforwardStalk y) = (f.pushforwardStalkMap y).hom :=
  rfl

variable (f : X ⟶ Y)

/-- Restriction compatibility of the germ into the pushforward stalk. -/
lemma pushforwardGerm_res {V W : Y.Opens} (hWV : W ≤ V) (y : Y) (hy : y ∈ W)
    (a : Γ(X, f ⁻¹ᵁ V)) :
    f.pushforwardGerm W y hy (X.presheaf.map (homOfLE (f.preimage_mono hWV)).op a) =
      f.pushforwardGerm V y (hWV hy) a :=
  (f.base _* X.presheaf).germ_res_apply (homOfLE hWV) y hy a

/-- Every element of the pushforward stalk is the germ of a section of `𝒪_X` over the preimage
of an arbitrarily small neighbourhood of `y`. -/
lemma exists_pushforwardGerm_eq {V : Y.Opens} {y : Y} (hy : y ∈ V) (z : f.pushforwardStalk y) :
    ∃ W ≤ V, ∃ (hyW : y ∈ W) (t : Γ(X, f ⁻¹ᵁ W)), f.pushforwardGerm W y hyW t = z :=
  (f.base _* X.presheaf).exists_le_germ_eq z hy

/-- Two sections with the same germ in the pushforward stalk already agree over the preimage of
some neighbourhood of `y`. -/
lemma exists_res_eq_of_pushforwardGerm_eq {V : Y.Opens} {y : Y} (hy : y ∈ V)
    {a b : Γ(X, f ⁻¹ᵁ V)} (h : f.pushforwardGerm V y hy a = f.pushforwardGerm V y hy b) :
    ∃ W, ∃ (_ : y ∈ W) (hWV : W ≤ V),
      X.presheaf.map (homOfLE (f.preimage_mono hWV)).op a =
        X.presheaf.map (homOfLE (f.preimage_mono hWV)).op b := by
  obtain ⟨W, hyW, iU, iV, e⟩ := (f.base _* X.presheaf).germ_eq y hy hy a b h
  exact ⟨W, hyW, iU.le, e⟩

/-- **The ring-level description of the stalk of `f_* 𝒪_X` over a quasi-compact
quasi-separated preimage.**

If `V` is an affine open of `Y` containing `y` whose preimage is quasi-compact and
quasi-separated, then `(f_* 𝒪_X)_y` is the localization of `Γ(X, f⁻¹V)` at the image of the prime
complement of `y`.  This is the statement that the stalk of the pushforward is the localization
of the sections over the preimage.

Affineness of `f` is not what the argument uses: the preimage enters only through the Qcqs
lemma, which identifies the sections over the part of `f⁻¹V` lying over a basic open of `V` with
a localization of `Γ(X, f⁻¹V)`.  An affine morphism gives an affine, hence quasi-compact
quasi-separated, preimage, which is `isLocalization_pushforwardStalk` below. -/
theorem isLocalization_pushforwardStalk_of_isCompact
    {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V)
    (hc : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X))
    (hq : IsQuasiSeparated ((f ⁻¹ᵁ V : X.Opens) : Set X)) :
    letI : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) :=
      (f.pushforwardGerm V y hy).hom.toAlgebra
    IsLocalization ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk y) := by
  let : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) :=
    (f.pushforwardGerm V y hy).hom.toAlgebra
  have halg : ∀ a : Γ(X, f ⁻¹ᵁ V),
      algebraMap Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) a = f.pushforwardGerm V y hy a :=
    fun _ ↦ rfl
  have hex : ∀ {W : Y.Opens}, y ∈ W → ∃ s ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl,
      ∃ _ : y ∈ Y.basicOpen s, Y.basicOpen s ≤ W := fun {W} hyW ↦ by
    obtain ⟨s, hsW, hys⟩ := hV.exists_basicOpen_le ⟨y, hyW⟩ hy
    exact ⟨s, (hV.mem_basicOpen_iff_mem_primeCompl ⟨y, hy⟩ s).mp hys, hys, hsW⟩
  let : ∀ s : Γ(Y, V), Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen s) := fun s ↦
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le s))).op).hom.toAlgebra
  have hloc : ∀ s : Γ(Y, V),
      IsLocalization.Away ((f.app V).hom s) Γ(X, f ⁻¹ᵁ Y.basicOpen s) := fun s ↦
    isLocalization_away_of_eq_of_isCompact hc hq ((f.app V).hom s)
      (f.preimage_mono (Y.basicOpen_le s)) (Scheme.preimage_basicOpen f s)
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨-, s, hs, rfl⟩
    have hys : y ∈ Y.basicOpen s := (hV.mem_basicOpen_iff_mem_primeCompl ⟨y, hy⟩ s).mpr hs
    have hunit : IsUnit (X.presheaf.map
        (homOfLE (f.preimage_mono (Y.basicOpen_le s))).op ((f.app V).hom s)) :=
      Scheme.isUnit_map_of_le_basicOpen _ _ (Scheme.preimage_basicOpen f s).le
    have hu : IsUnit (f.pushforwardGerm V y hy ((f.app V).hom s)) := by
      rw [← f.pushforwardGerm_res (Y.basicOpen_le s) y hys]
      exact hunit.map _
    rw [halg]
    exact hu
  · intro z
    obtain ⟨W, hWV, hyW, t, ht⟩ := f.exists_pushforwardGerm_eq hy z
    obtain ⟨s, hs, hys, hsW⟩ := hex hyW
    have hloc := hloc s
    have hres : ∀ a : Γ(X, f ⁻¹ᵁ V),
        f.pushforwardGerm (Y.basicOpen s) y hys
            (algebraMap Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen s) a) =
          algebraMap Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) a := fun a ↦
      f.pushforwardGerm_res (Y.basicOpen_le s) y hys a
    obtain ⟨t', ht'⟩ : ∃ t' : Γ(X, f ⁻¹ᵁ Y.basicOpen s),
        f.pushforwardGerm (Y.basicOpen s) y hys t' = z :=
      ⟨X.presheaf.map (homOfLE (f.preimage_mono hsW)).op t,
        (f.pushforwardGerm_res hsW y hys t).trans ht⟩
    obtain ⟨⟨b, c, n, hn⟩, hbc⟩ :=
      IsLocalization.surj (Submonoid.powers ((f.app V).hom s)) t'
    subst hn
    have hfin : z * algebraMap Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) ((f.app V).hom (s ^ n)) =
        algebraMap Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) b := by
      have hg := DFunLike.congr_arg
        (ConcreteCategory.hom (f.pushforwardGerm (Y.basicOpen s) y hys)) hbc
      rw [map_mul, ht', hres, hres] at hg
      simpa [map_pow] using hg
    exact ⟨⟨b, ⟨(f.app V).hom (s ^ n), s ^ n, pow_mem hs n, rfl⟩⟩, hfin⟩
  · intro a b hab
    rw [halg, halg] at hab
    obtain ⟨W, hyW, hWV, e⟩ := f.exists_res_eq_of_pushforwardGerm_eq hy hab
    obtain ⟨s, hs, hys, hsW⟩ := hex hyW
    have hloc := hloc s
    have key : algebraMap Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen s) a =
        algebraMap Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ Y.basicOpen s) b := by
      have hg := DFunLike.congr_arg
        (ConcreteCategory.hom (X.presheaf.map (homOfLE (f.preimage_mono hsW)).op)) e
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp] at hg
      rw [Scheme.presheaf_map_eq_homOfLE (Z := X) _ (f.preimage_mono (Y.basicOpen_le s)),
        Scheme.presheaf_map_eq_homOfLE (Z := X) _ (f.preimage_mono (Y.basicOpen_le s))] at hg
      exact hg
    obtain ⟨⟨c, n, hn⟩, hc⟩ :=
      IsLocalization.exists_of_eq (M := Submonoid.powers ((f.app V).hom s)) key
    subst hn
    exact ⟨⟨(f.app V).hom (s ^ n), s ^ n, pow_mem hs n, rfl⟩, by simpa [map_pow] using hc⟩

/-- **The ring-level description of the stalk of `f_* 𝒪_X` for an affine morphism `f`.**

If `V` is an affine open of `Y` containing `y`, then `(f_* 𝒪_X)_y` is the localization of
`Γ(X, f⁻¹V)` at the image of the prime complement of `y`.  The preimage of `V` is affine, hence
quasi-compact and quasi-separated, so this is `isLocalization_pushforwardStalk_of_isCompact`. -/
theorem isLocalization_pushforwardStalk [IsAffineHom f]
    {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V) :
    letI : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) :=
      (f.pushforwardGerm V y hy).hom.toAlgebra
    IsLocalization ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk y) :=
  f.isLocalization_pushforwardStalk_of_isCompact hV hy (hV.preimage f).isCompact
    (hV.preimage f).isQuasiSeparated

/-! ### `Spec` of the pushforward stalk as a base change -/

/-- **`Spec ((f_* 𝒪_X)_y) ≅ X ×_Y Spec 𝒪_{Y,y}` for an affine morphism `f`.**

Stated as a pullback square, with the map to `X` written using an affine open `V ∋ y`. -/
theorem isPullback_SpecMap_pushforwardStalkMap [IsAffineHom f]
    {V : Y.Opens} (hV : IsAffineOpen V) {y : Y} (hy : y ∈ V) :
    IsPullback (Spec.map (f.pushforwardGerm V y hy) ≫ (hV.preimage f).fromSpec)
      (Spec.map (f.pushforwardStalkMap y)) f (Y.fromSpecStalk y) := by
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  let : Algebra Γ(Y, V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  let : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) :=
    (f.pushforwardGerm V y hy).hom.toAlgebra
  have h1 : IsLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) :=
    hV.isLocalization_stalk ⟨y, hy⟩
  have h2 : IsLocalization ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk y) := f.isLocalization_pushforwardStalk hV hy
  have hpush : IsPushout (f.app V) (Y.presheaf.germ V y hy) (f.pushforwardGerm V y hy)
      (f.pushforwardStalkMap y) :=
    CommRingCat.isPushout_of_isLocalization (f.app V).hom (f.pushforwardStalkMap y).hom
      (congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkFunctor_map_germ V y hy f.c))
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  have t : IsPullback hU.fromSpec (Spec.map (f.app V)) f hV.fromSpec := by
    refine (IsOpenImmersion.isPullback (Spec.map (f.app V)) hU.fromSpec hV.fromSpec f ?_ ?_).flip
    · simpa only [Scheme.Hom.appLE_eq_app] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl).symm
    · rw [hV.opensRange_fromSpec, hU.opensRange_fromSpec]
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).paste_horiz t
  rwa [← IsAffineOpen.fromSpecStalk, hV.fromSpecStalk_eq_fromSpecStalk hy] at h

/-! ### The fibre -/

/-- The fibre of an affine morphism, as a pullback square over `Spec κ(y)` with apex
`Spec (κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y)`.  The leg to `X` depends on a choice of affine open
neighbourhood of `y`, so it is produced existentially; the leg to `Spec κ(y)` does not. -/
@[ega "II 1.5.4" "more general"]
theorem exists_isPullback_fiberTensor [IsAffineHom f] (y : Y) :
    ∃ g : Spec (.of (↑(Y.residueField y) ⊗[↑(Y.presheaf.stalk y)]
          ↑(f.pushforwardStalk y))) ⟶ X,
      IsPullback g (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := ↑(Y.presheaf.stalk y))
          (A := ↑(Y.residueField y)) (B := ↑(f.pushforwardStalk y)))))
        f (Y.fromSpecResidueField y) := by
  obtain ⟨V, hV, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have hres : Spec.map (CommRingCat.ofHom
      (algebraMap ↑(Y.presheaf.stalk y) ↑(Y.residueField y))) ≫ Y.fromSpecStalk y =
      Y.fromSpecResidueField y := rfl
  have hT : Spec.map (CommRingCat.ofHom
      (algebraMap ↑(Y.presheaf.stalk y) ↑(f.pushforwardStalk y))) =
      Spec.map (f.pushforwardStalkMap y) := rfl
  have h := ((isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct
    ↑(Y.presheaf.stalk y) ↑(Y.residueField y) ↑(f.pushforwardStalk y))).flip).paste_horiz
      (hT ▸ f.isPullback_SpecMap_pushforwardStalkMap hV hy)
  rw [hres] at h
  exact ⟨_, h⟩

/-- **The ring-level description of the fibre of an affine morphism.**

For an affine morphism `f : X ⟶ Y` and `y : Y`, the scheme-theoretic fibre of `f` at `y` is the
spectrum of `κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y`. -/
@[ega "II 1.5.4" "more general"]
def fiberIsoSpecResidueFieldTensorPushforwardStalk [IsAffineHom f] (y : Y) :
    f.fiber y ≅
      Spec (.of (↑(Y.residueField y) ⊗[↑(Y.presheaf.stalk y)] ↑(f.pushforwardStalk y))) :=
  (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).isoIsPullback _ _
    (f.exists_isPullback_fiberTensor y).choose_spec

/-- The fibre comparison isomorphism is an isomorphism of `κ(y)`-schemes. -/
@[reassoc (attr := simp)]
lemma fiberIsoSpecResidueFieldTensorPushforwardStalk_hom_fiberToSpecResidueField
    [IsAffineHom f] (y : Y) :
    (f.fiberIsoSpecResidueFieldTensorPushforwardStalk y).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := ↑(Y.presheaf.stalk y)) (A := ↑(Y.residueField y))
          (B := ↑(f.pushforwardStalk y)))) =
      f.fiberToSpecResidueField y :=
  (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).isoIsPullback_hom_snd _ _
    (f.exists_isPullback_fiberTensor y).choose_spec

/-- **The set-level description of the fibre of an affine morphism.**  The points of `X` lying
over `y` are homeomorphic to the prime spectrum of `κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y`. -/
def fiberHomeoPrimeSpectrum [IsAffineHom f] (y : Y) :
    f ⁻¹' {y} ≃ₜ PrimeSpectrum (↑(Y.residueField y) ⊗[↑(Y.presheaf.stalk y)]
      ↑(f.pushforwardStalk y)) :=
  (f.fiberHomeo y).symm.trans
    (Scheme.homeoOfIso (f.fiberIsoSpecResidueFieldTensorPushforwardStalk y))

end Scheme.Hom

end AlgebraicGeometry
