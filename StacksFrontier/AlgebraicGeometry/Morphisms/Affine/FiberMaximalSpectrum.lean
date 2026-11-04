module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Integral

/-!
# The fibre of an integral morphism and the maximal spectrum of the pushforward stalk

For an integral morphism of schemes `f : X ⟶ Y` and a point `y : Y`, this file identifies the
set-theoretic fibre `f ⁻¹' {y}` with the *maximal* spectrum of the stalk `(f_* 𝒪_X)_y`,
compatibly with residue fields: the residue field of a point of the fibre is the quotient of
`(f_* 𝒪_X)_y` by the corresponding maximal ideal.

The companion file `StacksFrontier/AlgebraicGeometry/Morphisms/Affine/Fiber.lean` describes the
fibre of a general *affine* morphism as `Spec (κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y)`.  Integrality
sharpens that description twice over: the primes of the fibre ring are all maximal, and the
residue field at such a point needs no further localization.  Both sharpenings come from the
same source, namely that `(f_* 𝒪_X)_y` is integral over the local ring `𝒪_{Y,y}`, so a prime
of `(f_* 𝒪_X)_y` is maximal exactly when it lies over the maximal ideal.

The route taken here is direct and does not pass through the tensor-product description.  The
bijection is given by sending a point `x` of the fibre to the kernel of the evaluation map
`(f_* 𝒪_X)_y ⟶ κ(x)`; everything else is then forced, because that kernel determines (and is
determined by) the prime of `Γ(X, f⁻¹V)` cut out by `x`, for `V` an affine open neighbourhood
of `y`.  Surjectivity of the evaluation map — which is what makes the residue field a *quotient*
rather than a localization of a quotient — is where maximality of the kernel is used.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.stalkPushforward`: the canonical `(f_* 𝒪_X)_{f x} ⟶ 𝒪_{X,x}`.
* `AlgebraicGeometry.Scheme.Hom.fiberResidue`: the evaluation `(f_* 𝒪_X)_{f x} ⟶ κ(x)`, and
  `AlgebraicGeometry.Scheme.Hom.fiberResidueOfEq`, the same map written at a point `y` of `Y`
  presented together with a proof that `f x = y`.
* `AlgebraicGeometry.Scheme.Hom.fiberMaximalIdeal`: the maximal ideal of `(f_* 𝒪_X)_y` cut out
  by a point of the fibre, and `AlgebraicGeometry.Scheme.Hom.fiberEquivMaximalSpectrum`, the
  resulting bijection `f ⁻¹' {y} ≃ MaximalSpectrum ((f_* 𝒪_X)_y)`.
* `AlgebraicGeometry.Scheme.Hom.residueFieldEquivQuotient`: the residue field of a point of the
  fibre as the quotient of `(f_* 𝒪_X)_y` by the corresponding maximal ideal.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIntegral_pushforwardStalk`: for an integral morphism the
  stalk `(f_* 𝒪_X)_y` is integral over `𝒪_{Y,y}`.  This is `isLocalization_pushforwardStalk`
  transported along `IsLocalization.isIntegral_localization`.
* `AlgebraicGeometry.Scheme.Hom.surjective_fiberResidue`: the evaluation map into the residue
  field of a point of the fibre is surjective.
* `AlgebraicGeometry.Scheme.Hom.bijective_fiberMaximalIdeal`: the fibre is in bijection with
  the maximal spectrum.
* `AlgebraicGeometry.Scheme.Hom.residueFieldEquivQuotient_comp_residueFieldMap`: the bijection
  is compatible with residue fields, over the residue field of the base point.  The square over
  the stalk of the pushforward is `RingHom.quotientKerEquivOfSurjective_symm_comp`, since
  `residueFieldEquivQuotient` is the inverse of `RingHom.quotientKerEquivOfSurjective`.

## Implementation notes

`fiberResidue` is stated at `f x` for a point `x : X`, which is the form in which it is proved
about; `fiberResidueOfEq` is the form in which it is used, where the base point `y : Y` is
fixed and the fibre is the subtype `{x : X // f x = y}`.  The transport between the two is by
`eqToHom`, and every lemma about `fiberResidueOfEq` is proved by substituting the equality
away, so no transport survives in a proof.

The three auxiliary lemmas about `IsAffineOpen.primeIdealOf` (that the maximal ideal of the
stalk pulls back to it along the germ map, and that it is injective and surjective) are
general facts about affine opens with no bearing on integrality; they are stated here because
Mathlib has `IsAffineOpen.fromSpec_primeIdealOf` but neither direction of the bijection.

This module carries no Stacks tag.  The statement it proves is the fibre description used by
the Stacks Project inside the proof of Tag 0C3B, and it is the set-level content of the
normalization fibre, but it is not itself a numbered Stacks result and no tag was invented
for it.

## References

* [Stacks Project, Tag 01WG](https://stacks.math.columbia.edu/tag/01WG), integral morphisms.
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B), the stalk of the
  pushforward along a normalization, which is the intended consumer.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

/-- The maximal ideal of the stalk at a point of an affine open pulls back along the germ map
to the prime ideal of the sections corresponding to that point. -/
lemma IsAffineOpen.comap_maximalIdeal_germ {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U)
    (z : U) :
    (maximalIdeal (Z.presheaf.stalk z)).comap (Z.presheaf.germ U z z.2).hom =
      (hU.primeIdealOf z).asIdeal := by
  let : Algebra Γ(Z, U) (Z.presheaf.stalk z) := TopCat.Presheaf.algebra_section_stalk Z.presheaf z
  have : IsLocalization.AtPrime (Z.presheaf.stalk z) (hU.primeIdealOf z).asIdeal :=
    hU.isLocalization_stalk z
  have h := IsLocalization.AtPrime.under_maximalIdeal (R := Γ(Z, U))
    (Z.presheaf.stalk z) (hU.primeIdealOf z).asIdeal
  rwa [Ideal.under, TopCat.Presheaf.stalk_open_algebraMap] at h

/-- A point of an affine open is determined by the prime ideal of the sections it cuts out. -/
lemma IsAffineOpen.primeIdealOf_injective {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun z z' h ↦
  Subtype.ext (((hU.fromSpec_primeIdealOf z).symm.trans (congrArg hU.fromSpec h)).trans
    (hU.fromSpec_primeIdealOf z'))

/-- Every prime ideal of the sections over an affine open is cut out by a point of it. -/
lemma IsAffineOpen.primeIdealOf_surjective {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U) :
    Function.Surjective hU.primeIdealOf :=
  (Scheme.homeoOfIso hU.isoSpec).surjective

/-- Every point of a scheme lies in some affine open. -/
private lemma exists_isAffineOpen_mem {Z : Scheme.{u}} (z : Z) :
    ∃ V : Z.Opens, IsAffineOpen V ∧ z ∈ V :=
  let ⟨V, hV, hz, _⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤) (x := z) trivial
  ⟨V, hV, hz⟩

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The stalk of the pushforward and the stalk upstairs -/

/-- The canonical map `(f_* 𝒪_X)_{f x} ⟶ 𝒪_{X,x}`, that is, `TopCat.Presheaf.stalkPushforward`
for the structure sheaf of `X` along the underlying continuous map of `f`. -/
def stalkPushforward (x : X) : f.pushforwardStalk (f x) ⟶ X.presheaf.stalk x :=
  X.presheaf.stalkPushforward CommRingCat f.base x

/-- The stalk map of `f` factors through the stalk of the pushforward. -/
@[reassoc]
lemma pushforwardStalkMap_stalkPushforward (x : X) :
    f.pushforwardStalkMap (f x) ≫ f.stalkPushforward x = f.stalkMap x := rfl

/-! ### The evaluation map at a point of a fibre -/

/-- The evaluation of the stalk of `f_* 𝒪_X` at `f x` in the residue field of `x`. -/
def fiberResidue (x : X) : f.pushforwardStalk (f x) ⟶ X.residueField x :=
  f.stalkPushforward x ≫ X.residue x

/-- The kernel of the evaluation at `x` is the preimage of the maximal ideal of the local ring
of `x`. -/
lemma ker_fiberResidue (x : X) :
    RingHom.ker (f.fiberResidue x).hom =
      (maximalIdeal (X.presheaf.stalk x)).comap (f.stalkPushforward x).hom := by
  rw [← IsLocalRing.ker_residue (R := X.presheaf.stalk x), RingHom.ker_eq_comap_bot,
    RingHom.ker_eq_comap_bot, Ideal.comap_comap]
  rfl

/-- The kernel of the evaluation at a point of the fibre is a prime ideal. -/
instance isPrime_ker_fiberResidue (x : X) : (RingHom.ker (f.fiberResidue x).hom).IsPrime := by
  rw [ker_fiberResidue]
  infer_instance

/-- The kernel of the evaluation at a point of the fibre lies over the maximal ideal of the
local ring of the base point. -/
lemma comap_ker_fiberResidue (x : X) :
    (RingHom.ker (f.fiberResidue x).hom).comap
        (algebraMap (Y.presheaf.stalk (f x)) (f.pushforwardStalk (f x))) =
      maximalIdeal (Y.presheaf.stalk (f x)) := by
  rw [ker_fiberResidue, Ideal.comap_comap, algebraMap_pushforwardStalk, ← CommRingCat.hom_comp,
    pushforwardStalkMap_stalkPushforward]
  exact IsLocalRing.maximalIdeal_comap (f.stalkMap x).hom

/-- The residue-field square of `f` at `x`, rewritten through the stalk of the pushforward. -/
@[reassoc]
lemma residue_residueFieldMap_eq_fiberResidue (x : X) :
    Y.residue (f x) ≫ f.residueFieldMap x =
      f.pushforwardStalkMap (f x) ≫ f.fiberResidue x := by
  rw [Scheme.residue_residueFieldMap, fiberResidue, ← pushforwardStalkMap_stalkPushforward,
    Category.assoc]

/-! ### Integrality of the pushforward stalk -/

/-- **The stalk of the pushforward along an integral morphism is integral over the local ring
of the base.**  This is `isLocalization_pushforwardStalk` transported along
`IsLocalization.isIntegral_localization`. -/
instance isIntegral_pushforwardStalk [IsIntegralHom f] (y : Y) :
    Algebra.IsIntegral (Y.presheaf.stalk y) (f.pushforwardStalk y) := by
  obtain ⟨V, hV, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  let : Algebra Γ(Y, V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  let : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) :=
    (f.pushforwardGerm V y hy).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  have : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  have h1 : IsLocalization (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) :=
    hV.isLocalization_stalk ⟨y, hy⟩
  have h2 : IsLocalization (Submonoid.map (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) (f.pushforwardStalk y) :=
    f.isLocalization_pushforwardStalk hV hy
  have h3 : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ V)
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) (f.pushforwardStalk y) := h2
  have key := isIntegral_localization (R := Γ(Y, V)) (S := Γ(X, f ⁻¹ᵁ V))
    (M := (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl) (Rₘ := Y.presheaf.stalk y)
    (Sₘ := f.pushforwardStalk y)
  have hmap : IsLocalization.map (M := (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
      (f.pushforwardStalk y) (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V))
      (Submonoid.le_comap_map _) =
      algebraMap (Y.presheaf.stalk y) (f.pushforwardStalk y) := by
    refine IsLocalization.ringHom_ext (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl ?_
    rw [IsLocalization.map_comp]
    change (f.app V ≫ f.pushforwardGerm V y hy).hom =
      (Y.presheaf.germ V y hy ≫ f.pushforwardStalkMap y).hom
    exact (congrArg CommRingCat.Hom.hom (TopCat.Presheaf.stalkFunctor_map_germ V y hy f.c)).symm
  refine ⟨fun z ↦ ?_⟩
  change (algebraMap (Y.presheaf.stalk y) (f.pushforwardStalk y)).IsIntegralElem z
  rw [← hmap]
  exact key z

/-! ### Surjectivity of the evaluation map -/

/-- The kernel of the evaluation at a point of the fibre of an integral morphism is maximal. -/
private lemma isMaximal_ker_fiberResidue [IsIntegralHom f] (x : X) :
    (RingHom.ker (f.fiberResidue x).hom).IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
    ((f.comap_ker_fiberResidue x) ▸ IsLocalRing.maximalIdeal.isMaximal _)

/-- **The evaluation of the pushforward stalk in the residue field of a point of the fibre is
surjective.**  Its kernel is a maximal ideal, because the pushforward stalk is integral over the
local ring of the base point; the residue field is therefore generated as a field by the image,
and the image is already a field. -/
lemma surjective_fiberResidue [IsIntegralHom f] (x : X) :
    Function.Surjective (f.fiberResidue x).hom := by
  intro t
  obtain ⟨V, hV, hx⟩ := exists_isAffineOpen_mem (f x)
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  obtain ⟨u, hu⟩ := X.residue_surjective x t
  let : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (X.presheaf.stalk x) :=
    hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨b, s, hs⟩, hbs⟩ :=
    IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl u
  have hres : ∀ a : Γ(X, f ⁻¹ᵁ V), f.fiberResidue x (f.pushforwardGerm V (f x) hx a) =
      X.residue x (X.presheaf.germ (f ⁻¹ᵁ V) x hx a) := by
    intro a
    rw [show f.fiberResidue x (f.pushforwardGerm V (f x) hx a) =
      X.residue x (f.stalkPushforward x (f.pushforwardGerm V (f x) hx a)) from rfl]
    exact congrArg (X.residue x) (congrArg (fun g : Γ(X, f ⁻¹ᵁ V) ⟶ X.presheaf.stalk x ↦
      (ConcreteCategory.hom g) a)
        (TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base X.presheaf V x hx))
  set β := f.pushforwardGerm V (f x) hx b
  set σ := f.pushforwardGerm V (f x) hx s
  have key : t * f.fiberResidue x σ = f.fiberResidue x β := by
    rw [hres, hres, ← hu, ← map_mul]
    exact congrArg (X.residue x) hbs
  have hσ0 : σ ∉ RingHom.ker (f.fiberResidue x).hom := by
    intro hmem
    have hc : X.residue x (X.presheaf.germ (f ⁻¹ᵁ V) x hx s) = 0 := by
      rw [← hres]
      exact hmem
    exact hs ((hU.comap_maximalIdeal_germ ⟨x, hx⟩) ▸
      Ideal.mem_comap.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hc))
  obtain ⟨c, i, hi, hci⟩ := (f.isMaximal_ker_fiberResidue x).exists_inv hσ0
  refine ⟨β * c, ?_⟩
  have hi0 : f.fiberResidue x i = 0 := hi
  have h1 : f.fiberResidue x c * f.fiberResidue x σ = 1 := by
    have h := congrArg (f.fiberResidue x) hci
    rwa [map_add, map_mul, hi0, add_zero, map_one] at h
  rw [map_mul, ← key, mul_assoc, mul_comm (f.fiberResidue x σ), h1, mul_one]

/-! ### The fibre as the maximal spectrum of the pushforward stalk -/

/-- The evaluation of `(f_* 𝒪_X)_y` in the residue field of a point `x` of the fibre of `f`
over `y`, written with the base point `y` and the proof `f x = y` kept apart. -/
def fiberResidueOfEq {y : Y} (x : X) (hx : f x = y) :
    f.pushforwardStalk y ⟶ X.residueField x :=
  eqToHom (congrArg f.pushforwardStalk hx.symm) ≫ f.fiberResidue x

/-- For the proof `rfl`, `fiberResidueOfEq` is `fiberResidue`. -/
@[simp]
lemma fiberResidueOfEq_rfl (x : X) : f.fiberResidueOfEq x rfl = f.fiberResidue x := by
  simp [fiberResidueOfEq]

/-- The evaluation of `(f_* 𝒪_X)_y` in the residue field of a point of the fibre over `y` is
surjective. -/
lemma surjective_fiberResidueOfEq [IsIntegralHom f] {y : Y} (x : X) (hx : f x = y) :
    Function.Surjective (f.fiberResidueOfEq x hx).hom := by
  subst hx
  exact f.surjective_fiberResidue x

/-- The kernel of the evaluation of `(f_* 𝒪_X)_y` at a point of the fibre over `y` is a maximal
ideal. -/
lemma isMaximal_ker_fiberResidueOfEq [IsIntegralHom f] {y : Y} (x : X) (hx : f x = y) :
    (RingHom.ker (f.fiberResidueOfEq x hx).hom).IsMaximal := by
  subst hx
  exact f.isMaximal_ker_fiberResidue x

/-- The maximal ideal of `(f_* 𝒪_X)_y` cut out by a point of the fibre of `f` over `y`. -/
def fiberMaximalIdeal [IsIntegralHom f] {y : Y} (x : {x : X // f x = y}) :
    MaximalSpectrum (f.pushforwardStalk y) :=
  ⟨RingHom.ker (f.fiberResidueOfEq x.1 x.2).hom, f.isMaximal_ker_fiberResidueOfEq x.1 x.2⟩

/-- The maximal ideal cut out by a point of the fibre pulls back, along the germ into the
pushforward stalk over an affine open `V ∋ y`, to the prime of `Γ(X, f⁻¹V)` cut out by that
point. -/
lemma comap_ker_fiberResidueOfEq [IsIntegralHom f] {V : Y.Opens} (hV : IsAffineOpen V) {y : Y}
    (hy : y ∈ V) (x : X) (hx : f x = y) (hxU : x ∈ f ⁻¹ᵁ V) :
    (RingHom.ker (f.fiberResidueOfEq x hx).hom).comap (f.pushforwardGerm V y hy).hom =
      ((hV.preimage f).primeIdealOf ⟨x, hxU⟩).asIdeal := by
  subst hx
  rw [fiberResidueOfEq_rfl, ker_fiberResidue, Ideal.comap_comap, ← CommRingCat.hom_comp,
    show f.pushforwardGerm V (f x) hy ≫ f.stalkPushforward x = _ from
      TopCat.Presheaf.stalkPushforward_germ CommRingCat f.base X.presheaf V x hy]
  exact (hV.preimage f).comap_maximalIdeal_germ ⟨x, hxU⟩

/-- **The points of the fibre of an integral morphism are exactly the maximal ideals of the
stalk of the pushforward.** -/
lemma bijective_fiberMaximalIdeal [IsIntegralHom f] (y : Y) :
    Function.Bijective (f.fiberMaximalIdeal (y := y)) := by
  obtain ⟨V, hV, hy⟩ := exists_isAffineOpen_mem y
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  let : Algebra Γ(X, f ⁻¹ᵁ V) (f.pushforwardStalk y) :=
    (f.pushforwardGerm V y hy).hom.toAlgebra
  have hloc : IsLocalization ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk y) := f.isLocalization_pushforwardStalk hV hy
  constructor
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
    have hxU : x ∈ f ⁻¹ᵁ V := show f x ∈ V by rwa [hx]
    have hx'U : x' ∈ f ⁻¹ᵁ V := show f x' ∈ V by rwa [hx']
    have e : hU.primeIdealOf ⟨x, hxU⟩ = hU.primeIdealOf ⟨x', hx'U⟩ := by
      apply PrimeSpectrum.ext
      rw [← f.comap_ker_fiberResidueOfEq hV hy x hx hxU,
        ← f.comap_ker_fiberResidueOfEq hV hy x' hx' hx'U]
      exact congrArg (fun q : MaximalSpectrum (f.pushforwardStalk y) ↦
        q.asIdeal.comap (f.pushforwardGerm V y hy).hom) h
    have hxx' : x = x' := congrArg Subtype.val (hU.primeIdealOf_injective e)
    exact Subtype.ext hxx'
  · intro q
    have : q.asIdeal.IsPrime := q.isMaximal.isPrime
    have hcomap : q.asIdeal.comap (algebraMap (Y.presheaf.stalk y) (f.pushforwardStalk y)) =
        maximalIdeal (Y.presheaf.stalk y) :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal)
    have hq₀comap : (q.asIdeal.comap (f.pushforwardGerm V y hy).hom).comap (f.app V).hom =
        (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
      rw [Ideal.comap_comap, ← CommRingCat.hom_comp,
        ← show Y.presheaf.germ V y hy ≫ f.pushforwardStalkMap y =
          f.app V ≫ f.pushforwardGerm V y hy from TopCat.Presheaf.stalkFunctor_map_germ V y hy f.c,
        CommRingCat.hom_comp, ← Ideal.comap_comap, ← algebraMap_pushforwardStalk, hcomap]
      exact hV.comap_maximalIdeal_germ ⟨y, hy⟩
    obtain ⟨z, hz⟩ := hU.primeIdealOf_surjective
      ⟨q.asIdeal.comap (f.pushforwardGerm V y hy).hom, Ideal.comap_isPrime _ _⟩
    have h2 : hV.primeIdealOf ⟨f z.1, z.2⟩ = hV.primeIdealOf ⟨y, hy⟩ := by
      rw [← IsAffineOpen.comap_primeIdealOf_appLE (f := f) V hV (f ⁻¹ᵁ V) hU le_rfl z.2]
      apply PrimeSpectrum.ext
      rw [Scheme.Hom.appLE_eq_app]
      show (hU.primeIdealOf z).asIdeal.comap (f.app V).hom = _
      rw [hz]
      exact hq₀comap
    have hfz : f z.1 = y := congrArg Subtype.val (hV.primeIdealOf_injective h2)
    refine ⟨⟨z.1, hfz⟩, ?_⟩
    have hcc : (RingHom.ker (f.fiberResidueOfEq z.1 hfz).hom).comap
        (f.pushforwardGerm V y hy).hom = q.asIdeal.comap (f.pushforwardGerm V y hy).hom := by
      rw [f.comap_ker_fiberResidueOfEq hV hy z.1 hfz z.2]
      exact congrArg PrimeSpectrum.asIdeal hz
    have hone := (IsLocalization.orderIsoOfPrime
      ((hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl.map (f.app V).hom)
      (f.pushforwardStalk y)).injective
      (a₁ := ⟨RingHom.ker (f.fiberResidueOfEq z.1 hfz).hom,
        (f.isMaximal_ker_fiberResidueOfEq z.1 hfz).isPrime⟩)
      (a₂ := ⟨q.asIdeal, inferInstance⟩) (Subtype.ext hcc)
    exact MaximalSpectrum.ext (congrArg Subtype.val hone)

/-- **The fibre of an integral morphism is the maximal spectrum of the stalk of the
pushforward.**  A point of the fibre is sent to the kernel of the evaluation of that stalk in
its residue field. -/
def fiberEquivMaximalSpectrum [IsIntegralHom f] (y : Y) :
    {x : X // f x = y} ≃ MaximalSpectrum (f.pushforwardStalk y) :=
  Equiv.ofBijective _ (f.bijective_fiberMaximalIdeal y)

/-- The maximal ideal attached to a point of the fibre is the kernel of the evaluation in its
residue field. -/
@[simp]
lemma fiberEquivMaximalSpectrum_asIdeal [IsIntegralHom f] {y : Y} (x : {x : X // f x = y}) :
    (f.fiberEquivMaximalSpectrum y x).asIdeal =
      RingHom.ker (f.fiberResidueOfEq x.1 x.2).hom := rfl

/-- The residue field of a point of the fibre is the quotient of the stalk of the pushforward
by the corresponding maximal ideal. -/
def residueFieldEquivQuotient [IsIntegralHom f] {y : Y} (x : {x : X // f x = y}) :
    X.residueField x.1 ≃+* (f.pushforwardStalk y ⧸ (f.fiberEquivMaximalSpectrum y x).asIdeal) :=
  (RingHom.quotientKerEquivOfSurjective (f.surjective_fiberResidueOfEq x.1 x.2)).symm

/-- The identification of the residue field of a point of the fibre with the quotient of the
pushforward stalk is compatible with the residue field of the base point: both ways round the
square from `𝒪_{Y,y}` agree. -/
lemma residueFieldEquivQuotient_comp_residueFieldMap [IsIntegralHom f] {y : Y}
    (x : {x : X // f x = y}) :
    (((f.residueFieldEquivQuotient x).toRingHom.comp
          ((f.residueFieldMap x.1).hom.comp (Y.residueFieldCongr x.2.symm).hom.hom)).comp
        (Y.residue y).hom) =
      (Ideal.Quotient.mk (f.fiberEquivMaximalSpectrum y x).asIdeal).comp
        (algebraMap (Y.presheaf.stalk y) (f.pushforwardStalk y)) := by
  obtain ⟨x, rfl⟩ := x
  have hsq : (f.residueFieldMap x).hom.comp (Y.residue (f x)).hom =
      (f.fiberResidue x).hom.comp (f.pushforwardStalkMap (f x)).hom :=
    congrArg CommRingCat.Hom.hom (f.residue_residueFieldMap_eq_fiberResidue x)
  have hres : (f.residueFieldEquivQuotient ⟨x, rfl⟩).toRingHom.comp (f.fiberResidue x).hom =
      Ideal.Quotient.mk (f.fiberEquivMaximalSpectrum (f x) ⟨x, rfl⟩).asIdeal := by
    rw [← fiberResidueOfEq_rfl]
    exact RingHom.quotientKerEquivOfSurjective_symm_comp _
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, CommRingCat.hom_id, RingHom.comp_id,
    algebraMap_pushforwardStalk]
  rw [RingHom.comp_assoc, hsq, ← RingHom.comp_assoc, hres]

end Scheme.Hom

end AlgebraicGeometry

end
