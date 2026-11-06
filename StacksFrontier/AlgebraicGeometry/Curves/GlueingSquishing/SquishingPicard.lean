module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.Minpoly.Field
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingTangentVector
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic

/-!
# Picard groups and the squishing of a tangent vector

Let `k` be an algebraically closed field and let `f : X' ⟶ X` be the squishing of a tangent
vector `ϑ` of an algebraic `k`-scheme `X'`, in the sense of [Stacks, Tag 0C1K]: `ϑ` is a closed
immersion of the dual numbers which `f` contracts to a rational point `x` of `X`, the morphism
`f` is finite and an isomorphism away from `x`, and the coefficient of `ε` along `ϑ` exhibits the
additive skyscraper `(k, +)_x` as the quotient of `f_*𝒪_{X'}` by `𝒪_X`. [Stacks, Tag 0C1N]
records an exact sequence

`(k, +) ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`,

whose second map is pullback along `f` and whose first map is the connecting homomorphism of the
short exact sequence of sheaves of units on `X` with middle term `f_*𝒪_{X'}^*`; the first map is
injective when `X'` is proper and reduced. Three of its clauses are proved here.

**The pullback is a homomorphism.** The Picard group used is `Stacks.Picard.ofScheme` and the
pullback map is the *bundled* homomorphism `Stacks.Picard.schemePullbackClassHom`, so this clause
is `map_zero` and `map_add` of that homomorphism.

**Surjectivity of pullback.** Every invertible `𝒪_{X'}`-module is the pullback of an invertible
`𝒪_X`-module. The squishing is finite and is an isomorphism over an open `U` of `X` whose
complement is the single point `x`, hence discrete, so this is exactly the descent statement of
[Stacks, Tag 0C0T]. Transporting it to Picard classes uses that pullback computes the class of
`L` from the class of `f^*L` for *any* representative `L`, so the representative chosen by the
skeleton underlying `Pic(X')` may be fed to Tag 0C0T directly.

**Injectivity of the first map when `X'` is proper and reduced.** The first map is the connecting
homomorphism of the units sequence, so it is injective exactly when the map `Γ(X', 𝒪_{X'})^* → k`
sending a unit to its logarithmic `ε`-derivative along `ϑ` is zero. That is what is proved, in
the stronger form that the `ε`-coefficient along `ϑ` of *every* global section vanishes. The
global functions of a scheme proper over `k` are integral over `k` and those of a reduced scheme
form a reduced ring, so the minimal polynomial over `k` of a global section `a` is squarefree.
The minimal polynomial of the image of `a` in `k[ε]` divides it and is therefore squarefree too,
while a nonzero `ε`-coefficient would force that image to be a double root of a linear
polynomial.

## Main results

* `Stacks.SquishPicard.picardPullback_zero_and_add` — pullback on Picard groups preserves `0`
  and addition.
* `Stacks.SquishPicard.surjective_schemePullbackClassHom` — pullback `Pic(X) → Pic(X')` along the
  squishing of a tangent vector is surjective.
* `Stacks.SquishPicard.epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced` and
  `Stacks.SquishPicard.epsilonCoefficientAt_unit_eq_zero_of_isProper_of_isReduced` — on a proper
  reduced `X'` the `ε`-coefficient along `ϑ` of a global section, in particular of a global unit,
  vanishes; equivalently the first map of the sequence of Tag 0C1N is injective.

## Implementation notes

The squishing predicate used is `AlgebraicGeometry.IsSquishingTangentVector`, whose last clause
is an honest `CategoryTheory.ShortComplex.ShortExact` for the sheaf sequence.

The `ε`-coefficient is `AlgebraicGeometry.epsilonCoefficientAt`. The restriction of global
sections along `ϑ` is packaged as the ring homomorphism `globalSectionsToDualNumber`, whose
`ε`-coefficient it is by definition; that `ϑ` is defined over `k` is used exactly once, to see
that this homomorphism carries constants to constants, and it is phrased as an identity of
morphisms of `CommRingCat` so that the equation `ϑ ≫ (X' ↘ Spec k) = dualNumberToBase k` can be
rewritten under the germ without a dependent-type obstruction.

The injectivity clause is recorded here as the lifting criterion that the connecting
homomorphism consumes. The tangent homomorphism `(k, +) →+ Pic(X)` itself is
`Stacks.SquishSheafSequence.picardTangentHom`, built from the short exact sequence of sheaves of
units `1 → 𝒪_X^* → f_*𝒪_{X'}^* → (k, +)_x → 1` of the squishing, and its injectivity is
`Stacks.SquishSheafSequence.injective_picardTangentHom_of_isProper_of_isReduced`.

## References

* [Stacks Project, Tag 0C1N](https://stacks.math.columbia.edu/tag/0C1N)
* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
* [Stacks Project, Tag 0C0T](https://stacks.math.columbia.edu/tag/0C0T)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.SquishPicard

open Stacks.RingedSpace (structureIsSheaf)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

/-- Pullback of Picard classes is a homomorphism of abelian groups. -/
@[stacks 0C1N "the Picard pullback homomorphism"]
theorem picardPullback_zero_and_add {X' X : Scheme.{u}} (f : X' ⟶ X) :
    Stacks.Picard.schemePullbackClassHom f 0 = 0 ∧
      ∀ x y : Stacks.Picard.ofScheme X,
        Stacks.Picard.schemePullbackClassHom f (x + y) =
          Stacks.Picard.schemePullbackClassHom f x +
            Stacks.Picard.schemePullbackClassHom f y :=
  ⟨map_zero _, fun x y => map_add _ x y⟩

/-- Pullback along the squishing of a tangent vector is surjective on Picard groups. -/
@[stacks 0C1N "surjectivity"]
theorem surjective_schemePullbackClassHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ) :
    Function.Surjective (Stacks.Picard.schemePullbackClassHom f) := by
  obtain ⟨-, -, -, -, -, -, -, x, -, -, hfin, ⟨U, hU, hUiso⟩, -⟩ := h
  have : IsFinite f := hfin
  have : IsIso (f ∣_ U) := hUiso
  have : DiscreteTopology ((U : Set X)ᶜ : Set X) := by
    rw [hU, compl_compl]
    have : Subsingleton ({(θ ≫ f).base (IsLocalRing.closedPoint (DualNumber k))} : Set X) :=
      Set.subsingleton_singleton.coe_sort
    infer_instance
  intro y
  obtain ⟨M, hM, ⟨e⟩⟩ := Stacks.PicFinite.exists_isInvertible_modulePullback_iso f U
    (Stacks.Picard.picardRepresentative X'.toSheafedSpace y).obj
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _
      (structureIsSheaf X'.toSheafedSpace) _).mp
      (Stacks.Picard.picardRepresentative X'.toSheafedSpace y).property)
  let M₀ : SheafOfModules.{u} (structureSheaf X.toSheafedSpace.presheaf
    (structureIsSheaf X.toSheafedSpace)) := M
  have hM' : Stacks.SheafOfModules.IsInvertible X.toSheafedSpace.presheaf
      (structureIsSheaf X.toSheafedSpace) M₀ :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _
      (structureIsSheaf X.toSheafedSpace) M₀).mpr hM
  refine ⟨Stacks.SheafOfModules.picardClass X.toSheafedSpace.presheaf
      (structureIsSheaf X.toSheafedSpace) M₀ hM',
    (Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom M₀ hM').trans
      (((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩).trans
        (Stacks.Picard.classOf_picardRepresentative X'.toSheafedSpace y))⟩

/-! ### The lifting criterion for injectivity of the first map -/

/-- **A dual-number-valued point of a reduced algebra integral over a field is constant.** -/
private theorem snd_eq_zero_of_isIntegralElem {k A : Type u} [Field k] [CommRing A]
    [IsReduced A] (σ : k →+* A) (ρ : A →+* DualNumber k)
    (hσρ : ∀ c, ρ (σ c) = algebraMap k (DualNumber k) c) {a : A}
    (ha : σ.IsIntegralElem a) : (ρ a).snd = 0 := by
  let alg : Algebra k A := σ.toAlgebra
  have halg : ∀ c : k, algebraMap k A c = σ c := fun _ => rfl
  let φ : A →ₐ[k] DualNumber k :=
    { ρ with commutes' := fun c => (congrArg ρ (halg c)).trans (hσρ c) }
  have hφ : ∀ x : A, φ x = ρ x := fun _ => rfl
  have hint : IsIntegral k a := by
    show (algebraMap k A).IsIntegralElem a
    rwa [RingHom.algebraMap_toAlgebra]
  have hq : Squarefree (minpoly k a) :=
    (minpoly.isRadical k a).squarefree (minpoly.ne_zero hint)
  have hdvd1 : minpoly k (φ a) ∣ minpoly k a :=
    minpoly.dvd k (φ a) (by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero])
  have hsq : Squarefree (minpoly k (φ a)) := Squarefree.squarefree_of_dvd hdvd1 hq
  have hfst : (φ a - algebraMap k (DualNumber k) (ρ a).fst).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, hφ,
      sub_self]
  have hsq2 : (φ a - algebraMap k (DualNumber k) (ρ a).fst) ^ 2 = 0 := by
    rw [pow_two]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, hfst, mul_zero, TrivSqZeroExt.fst_zero]
    · rw [TrivSqZeroExt.snd_mul, hfst]
      simp
  have hdvd3 : minpoly k (φ a) ∣ Polynomial.X - Polynomial.C (ρ a).fst := by
    refine (hsq.dvd_pow_iff_dvd two_ne_zero).1 (minpoly.dvd k (φ a) ?_)
    rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hsq2
  have hroot := minpoly.dvd_iff.mp hdvd3
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hroot
  have hsnd := congrArg TrivSqZeroExt.snd hroot
  rwa [TrivSqZeroExt.snd_sub, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_zero, sub_zero, hφ] at hsnd

/-- Restriction of a global section along a dual-number-valued point, as a ring homomorphism to
the dual numbers. Its `ε`-coefficient is `AlgebraicGeometry.epsilonCoefficientAt`. -/
private def globalSectionsToDualNumber {k : Type u} [Field k] {X' : Scheme.{u}}
    (θ : Spec (.of (DualNumber k)) ⟶ X') : Γ(X', ⊤) →+* DualNumber k :=
  (X'.presheaf.germ ⊤ _ trivial ≫ Scheme.stalkClosedPointTo θ).hom

/-- A tangent vector defined over `k` restricts the constant global sections to the constant
dual numbers. -/
private theorem comp_globalSectionsToDualNumber {k : Type u} [Field k] {X' : Scheme.{u}}
    [X'.Over (Spec (.of k))] (θ : Spec (.of (DualNumber k)) ⟶ X')
    (hθ : θ ≫ (X' ↘ Spec (.of k)) = dualNumberToBase k) (c : k) :
    globalSectionsToDualNumber θ
        (((Scheme.ΓSpecIso (.of k)).inv ≫ (X' ↘ Spec (.of k)).appTop).hom c) =
      algebraMap k (DualNumber k) c := by
  have hθ' : θ ≫ (X' ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) := hθ
  have hgerm : (X' ↘ Spec (.of k)).appTop ≫
      X'.presheaf.germ ⊤ (θ.base (IsLocalRing.closedPoint (DualNumber k))) trivial =
      (Spec (.of k)).presheaf.germ ⊤
          ((θ ≫ (X' ↘ Spec (.of k))).base (IsLocalRing.closedPoint (DualNumber k))) trivial ≫
        (X' ↘ Spec (.of k)).stalkMap (θ.base (IsLocalRing.closedPoint (DualNumber k))) :=
    (Scheme.Hom.germ_stalkMap (X' ↘ Spec (.of k)) ⊤
      (θ.base (IsLocalRing.closedPoint (DualNumber k))) trivial).symm
  have step : (X' ↘ Spec (.of k)).appTop ≫
      X'.presheaf.germ ⊤ (θ.base (IsLocalRing.closedPoint (DualNumber k))) trivial ≫
        Scheme.stalkClosedPointTo θ =
      (Spec (.of k)).presheaf.germ ⊤
          ((θ ≫ (X' ↘ Spec (.of k))).base (IsLocalRing.closedPoint (DualNumber k))) trivial ≫
        Scheme.stalkClosedPointTo (θ ≫ (X' ↘ Spec (.of k))) :=
    (Category.assoc _ _ _).symm.trans
      (((congrArg (· ≫ Scheme.stalkClosedPointTo θ) hgerm).trans
        (Category.assoc _ _ _)).trans
        (congrArg (fun m => (Spec (.of k)).presheaf.germ ⊤
            ((θ ≫ (X' ↘ Spec (.of k))).base (IsLocalRing.closedPoint (DualNumber k)))
            trivial ≫ m)
          (Scheme.stalkClosedPointTo_comp θ (X' ↘ Spec (.of k))).symm))
  have key : (Spec (.of k)).presheaf.germ ⊤
        ((θ ≫ (X' ↘ Spec (.of k))).base (IsLocalRing.closedPoint (DualNumber k))) trivial ≫
      Scheme.stalkClosedPointTo (θ ≫ (X' ↘ Spec (.of k))) =
      (Scheme.ΓSpecIso (.of k)).hom ≫
        CommRingCat.ofHom (algebraMap k (DualNumber k)) := by
    rw [hθ']
    exact Scheme.germ_stalkClosedPointTo_Spec _
  have main : (Scheme.ΓSpecIso (.of k)).inv ≫ (X' ↘ Spec (.of k)).appTop ≫
      X'.presheaf.germ ⊤ (θ.base (IsLocalRing.closedPoint (DualNumber k))) trivial ≫
        Scheme.stalkClosedPointTo θ =
      CommRingCat.ofHom (algebraMap k (DualNumber k)) := by
    rw [step, key, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  show ((Scheme.ΓSpecIso (.of k)).inv ≫ (X' ↘ Spec (.of k)).appTop ≫
    X'.presheaf.germ ⊤ (θ.base (IsLocalRing.closedPoint (DualNumber k))) trivial ≫
      Scheme.stalkClosedPointTo θ).hom c = _
  rw [main]
  rfl

/-- **The first map of the sequence of Stacks Tag 0C1N is injective when `X'` is proper and
reduced**, in the form that the connecting homomorphism consumes: the `ε`-coefficient along the
squished tangent vector of every global section of `𝒪_{X'}` vanishes.

The global functions of a scheme proper over `k` are integral over `k`, and those of a reduced
scheme are a reduced ring, so the minimal polynomial over `k` of a global section is squarefree.
Its image in `k[ε]` therefore cannot be a double root of a linear polynomial, which is what a
nonzero `ε`-coefficient would make it. -/
@[stacks 0C1N "the lifting criterion for injectivity on a proper reduced scheme"]
theorem epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X' ↘ Spec (.of k))] [IsReduced X'] (s : Γ(X', ⊤)) :
    AlgebraicGeometry.epsilonCoefficientAt θ ⊤ trivial s = 0 := by
  obtain ⟨-, -, -, -, -, -, hθ, -⟩ := h
  have hint := Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap
    (k := k) (X' ↘ Spec (.of k))
  show (globalSectionsToDualNumber θ s).snd = 0
  exact snd_eq_zero_of_isIntegralElem _ (globalSectionsToDualNumber θ)
    (comp_globalSectionsToDualNumber θ hθ) (hint s)

/-- The criterion of `Stacks.SquishPicard.epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced`
for a global unit: the logarithmic `ε`-derivative of a unit on a proper reduced `X'` vanishes, so
no nonzero scalar is hit by the units sequence and the first map of Tag 0C1N is injective. -/
@[stacks 0C1N "the lifting criterion for injectivity on a proper reduced scheme"]
theorem epsilonCoefficientAt_unit_eq_zero_of_isProper_of_isReduced
    {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X' ↘ Spec (.of k))] [IsReduced X'] (s : Γ(X', ⊤)ˣ) :
    AlgebraicGeometry.epsilonCoefficientAt θ ⊤ trivial (s : Γ(X', ⊤)) = 0 :=
  epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced f θ h _

end Stacks.SquishPicard

end
