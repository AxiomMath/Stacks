module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeTheoreticImage

/-!
# Existence of the scheme theoretic image of a morphism of algebraic stacks (Stacks 0CPU)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0CPU** says that the
scheme theoretic image of `f` in the sense of **Stacks 0CMI** exists: there is a smallest closed
substack of `𝒴` through which `f` factors. It is the intersection of all closed substacks of `𝒴`
through which `f` factors, here `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate f`.

## Main definitions

* `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate`: the intersection of all closed
  substacks of `𝒴` through which `f` factors, as a property of the objects of `𝒴`.

## Main results

* `AlgebraicGeometry.Stack.hasSchemeTheoreticImage`: **Stacks 0CPU**, the scheme theoretic image
  of every 1-morphism of algebraic stacks exists.
* `AlgebraicGeometry.Stack.isSchemeTheoreticImage_schemeTheoreticImageCandidate`: the
  intersection is the scheme theoretic image, and
  `AlgebraicGeometry.Stack.isClosedSubstack_schemeTheoreticImageCandidate` the closedness clause
  on its own.
* `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_le` and
  `AlgebraicGeometry.Stack.le_schemeTheoreticImageCandidate`: the two halves of the universal
  property of the intersection.
* `AlgebraicGeometry.Stack.factorsThroughSubstack_schemeTheoreticImageCandidate`: `f` factors
  through the candidate.
* `AlgebraicGeometry.Stack.eq_schemeTheoreticImageCandidate`: a scheme theoretic image of `f` is
  the candidate.
* `AlgebraicGeometry.Stack.hasSchemeTheoreticImage_iff_isClosedSubstack`: the scheme theoretic
  image of `f` exists if and only if the candidate is a closed substack of `𝒴`.
* `AlgebraicGeometry.Stack.isSchemeTheoreticImage_fullSubcategoryInclusion`: a closed substack
  is the scheme theoretic image of its own inclusion.
* `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate_comp`: the candidate is unchanged by
  precomposition with a surjective, flat 1-morphism locally of finite presentation, which
  strengthens **Stacks 0CMJ** to an unconditional equality of candidates.

## The proof

Being the scheme theoretic image of `f` consists of three clauses: cutting out a closed substack
of `𝒴`, factoring `f`, and being contained in every closed substack of `𝒴` through which `f`
factors. For the intersection the last two are the two halves of the universal property of an
infimum, and the first is `AlgebraicGeometry.Stack.isClosedSubstack_sInf`: an arbitrary
intersection of closed substacks is a closed substack.

The source argues on a presentation `𝒴 = [U/R]`, through the correspondence of Stacks 0507
between closed substacks of `𝒴` and `R`-invariant closed subspaces of `U`, and takes the sum of
the quasi-coherent ideals of the candidates. The route here avoids both the correspondence and
quasi-coherent ideals: the base change of the inclusion of an intersection of closed substacks
along a scheme-valued point of `𝒴` is the intersection of the base changes of the members, which
are closed subspaces of the scheme, and an intersection of closed subspaces is a closed subspace
(`AlgebraicGeometry.Space.isClosedSubspace_sInf`, the input the source's sum of ideals provides
on the presentation).

## Implementation notes

A closed substack is a property of the objects of `𝒴` satisfying
`AlgebraicGeometry.Stack.IsClosedSubstack`, so the intersection is the `sInf` of the complete
lattice `CategoryTheory.ObjectProperty 𝒴.val.val.obj` and the two halves of its universal
property are `sInf_le` and `le_sInf`. All the statements below are phrased through those two,
so none of them unfolds the `sInf`.

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CMJ](https://stacks.math.columbia.edu/tag/0CMJ)
* [Stacks Project, Tag 0CPU](https://stacks.math.columbia.edu/tag/0CPU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The intersection of all the closed substacks of `𝒴` through which a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks factors, as a property of the objects of `𝒴`. -/
def schemeTheoreticImageCandidate {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    ObjectProperty 𝒴.val.val.obj :=
  sInf {Q : ObjectProperty 𝒴.val.val.obj | IsClosedSubstack 𝒴 Q ∧ FactorsThroughSubstack f Q}

/-- Minimality of the candidate image: the intersection of the closed substacks through which `f`
factors is contained in each of them. -/
@[stacks 0CPU "minimality of the candidate image"]
theorem schemeTheoreticImageCandidate_le {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {Q : ObjectProperty 𝒴.val.val.obj} (hQ : IsClosedSubstack 𝒴 Q)
    (hfac : FactorsThroughSubstack f Q) : schemeTheoreticImageCandidate f ≤ Q :=
  sInf_le ⟨hQ, hfac⟩

/-- A property of the objects of `𝒴` contained in every closed substack through which `f`
factors is contained in the candidate image. -/
theorem le_schemeTheoreticImageCandidate {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {R : ObjectProperty 𝒴.val.val.obj}
    (h : ∀ Q : ObjectProperty 𝒴.val.val.obj, IsClosedSubstack 𝒴 Q →
      FactorsThroughSubstack f Q → R ≤ Q) :
    R ≤ schemeTheoreticImageCandidate f :=
  le_sInf fun Q hQ => h Q hQ.1 hQ.2

/-- An object of `𝒴` lies in the candidate image of `f` exactly when it lies in every closed
substack of `𝒴` through which `f` factors. -/
theorem schemeTheoreticImageCandidate_apply_iff {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (Y : 𝒴.val.val.obj) :
    schemeTheoreticImageCandidate f Y ↔
      ∀ Q : ObjectProperty 𝒴.val.val.obj, IsClosedSubstack 𝒴 Q →
        FactorsThroughSubstack f Q → Q Y :=
  ⟨fun h _ hQ hfac => schemeTheoreticImageCandidate_le f hQ hfac Y h,
    fun h => le_schemeTheoreticImageCandidate f
      (R := fun Z => ∀ Q : ObjectProperty 𝒴.val.val.obj, IsClosedSubstack 𝒴 Q →
        FactorsThroughSubstack f Q → Q Z)
      (fun Q hQ hfac _ hZ => hZ Q hQ hfac) Y h⟩

/-- The candidate image is strictly full, each closed substack through which `f` factors
being so. -/
instance isClosedUnderIsomorphisms_schemeTheoreticImageCandidate
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    (schemeTheoreticImageCandidate f).IsClosedUnderIsomorphisms where
  of_iso e hY := by
    rw [schemeTheoreticImageCandidate_apply_iff] at hY ⊢
    intro Q hQ hfac
    have := hQ.1
    exact Q.prop_of_iso e (hY Q hQ hfac)

/-- Factoring through a closed substack is a condition on the objects in the image of `f`. -/
private theorem factorsThroughSubstack_iff_forall_of_isClosedSubstack
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) {Q : ObjectProperty 𝒴.val.val.obj}
    (hQ : IsClosedSubstack 𝒴 Q) :
    FactorsThroughSubstack f Q ↔ ∀ X : 𝒳.val.val.obj, Q (f.hom.hom.obj X) :=
  have := hQ.1
  factorsThroughSubstack_iff_forall f

/-- The factorization through the candidate image: `f` factors through the intersection of the
closed substacks of `𝒴` through which it factors, because factoring through a strictly full
subcategory is a condition on the objects in the image of `f`. -/
@[stacks 0CPU "the candidate image factors f"]
theorem factorsThroughSubstack_schemeTheoreticImageCandidate
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    FactorsThroughSubstack f (schemeTheoreticImageCandidate f) := by
  rw [factorsThroughSubstack_iff_forall]
  intro X
  rw [schemeTheoreticImageCandidate_apply_iff]
  intro Q hQ hfac
  exact (factorsThroughSubstack_iff_forall_of_isClosedSubstack f hQ).1 hfac X

/-- The scheme theoretic image of `f`, if there is one, is the candidate image: it is contained
in the candidate by its own minimality and contains it by the minimality of the candidate. -/
theorem eq_schemeTheoreticImageCandidate {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {P : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    P = schemeTheoreticImageCandidate f :=
  le_antisymm (le_schemeTheoreticImageCandidate f fun Q hQ hfac => hP.2.2 Q hQ hfac)
    (schemeTheoreticImageCandidate_le f hP.1 hP.2.1)

/-- The candidate image is the scheme theoretic image of `f` exactly when it cuts out a closed
substack of `𝒴`, the other two clauses of **Stacks 0CMI** holding for it outright. -/
theorem isSchemeTheoreticImage_schemeTheoreticImageCandidate_iff
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsSchemeTheoreticImage f (schemeTheoreticImageCandidate f) ↔
      IsClosedSubstack 𝒴 (schemeTheoreticImageCandidate f) :=
  ⟨fun h => h.1, fun h => ⟨h, factorsThroughSubstack_schemeTheoreticImageCandidate f,
    fun _ hQ hfac => schemeTheoreticImageCandidate_le f hQ hfac⟩⟩

/-- The scheme theoretic image of `f` exists if and only if the candidate image cuts out a
closed substack of `𝒴`: a scheme theoretic image is the candidate, and the candidate is one as
soon as it is a closed substack. -/
theorem hasSchemeTheoreticImage_iff_isClosedSubstack {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) :
    HasSchemeTheoreticImage f ↔ IsClosedSubstack 𝒴 (schemeTheoreticImageCandidate f) := by
  refine ⟨fun ⟨P, hP⟩ => ?_, fun h => ⟨_,
    (isSchemeTheoreticImage_schemeTheoreticImageCandidate_iff f).2 h⟩⟩
  rw [← eq_schemeTheoreticImageCandidate hP]
  exact hP.1

/-- The candidate image of `f` is a closed substack of `𝒴`: it is an intersection of closed
substacks, and those are closed substacks by
`AlgebraicGeometry.Stack.isClosedSubstack_sInf`. -/
theorem isClosedSubstack_schemeTheoreticImageCandidate {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) : IsClosedSubstack 𝒴 (schemeTheoreticImageCandidate f) :=
  isClosedSubstack_sInf 𝒴 _ fun _ hQ => hQ.1

/-- The candidate image of `f` is the scheme theoretic image of `f` (**Stacks 0CMI**): it is a
closed substack of `𝒴`, `f` factors through it, and it is contained in every closed substack of
`𝒴` through which `f` factors. -/
theorem isSchemeTheoreticImage_schemeTheoreticImageCandidate
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsSchemeTheoreticImage f (schemeTheoreticImageCandidate f) :=
  (isSchemeTheoreticImage_schemeTheoreticImageCandidate_iff f).2
    (isClosedSubstack_schemeTheoreticImageCandidate f)

/-- **Stacks 0CPU.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Then the
scheme theoretic image of `f` exists: there is a smallest closed substack of `𝒴` through which
`f` factors, namely `AlgebraicGeometry.Stack.schemeTheoreticImageCandidate f`. -/
@[stacks 0CPU]
theorem hasSchemeTheoreticImage {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    HasSchemeTheoreticImage f :=
  ⟨_, isSchemeTheoreticImage_schemeTheoreticImageCandidate f⟩

/-- A closed substack of `𝒴` is the scheme theoretic image of its own inclusion: the inclusion
factors through it, and a closed substack the inclusion factors through contains every object of
it. -/
theorem isSchemeTheoreticImage_fullSubcategoryInclusion {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (P : ObjectProperty 𝒴.val.val.obj)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hP : IsClosedSubstack 𝒴 P) :
    IsSchemeTheoreticImage (fullSubcategoryInclusion 𝒴 P hPalg) P := by
  refine ⟨hP, ?_, fun _ hQ hfac => ?_⟩
  · rw [factorsThroughSubstack_iff_forall_of_isClosedSubstack _ hP]
    exact fun X => X.property
  · exact fun Y hY => (factorsThroughSubstack_iff_forall_of_isClosedSubstack _ hQ).1 hfac ⟨Y, hY⟩

/-- The inclusion of a closed substack has a scheme theoretic image, namely that substack. -/
theorem hasSchemeTheoreticImage_fullSubcategoryInclusion {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (P : ObjectProperty 𝒴.val.val.obj)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hP : IsClosedSubstack 𝒴 P) :
    HasSchemeTheoreticImage (fullSubcategoryInclusion 𝒴 P hPalg) :=
  ⟨P, isSchemeTheoreticImage_fullSubcategoryInclusion P hPalg hP⟩

/-- The candidate image of the inclusion of a closed substack is that substack. -/
theorem schemeTheoreticImageCandidate_fullSubcategoryInclusion
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (P : ObjectProperty 𝒴.val.val.obj)
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hP : IsClosedSubstack 𝒴 P) :
    schemeTheoreticImageCandidate (fullSubcategoryInclusion 𝒴 P hPalg) = P :=
  (eq_schemeTheoreticImageCandidate
    (isSchemeTheoreticImage_fullSubcategoryInclusion P hPalg hP)).symm

/-- The candidate image is unchanged by precomposition with a surjective, flat 1-morphism
locally of finite presentation: the two intersections are over the same closed substacks, by
`AlgebraicGeometry.Stack.factorsThroughSubstack_comp_iff`. -/
theorem schemeTheoreticImageCandidate_comp {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS g)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g) :
    schemeTheoreticImageCandidate (g ≫ f) = schemeTheoreticImageCandidate f :=
  le_antisymm
    (le_schemeTheoreticImageCandidate f fun _ hQ hfac =>
      schemeTheoreticImageCandidate_le (g ≫ f) hQ
        ((factorsThroughSubstack_comp_iff f g hsurj hflat hlfp hQ).1 hfac))
    (le_schemeTheoreticImageCandidate (g ≫ f) fun _ hQ hfac =>
      schemeTheoreticImageCandidate_le f hQ
        ((factorsThroughSubstack_comp_iff f g hsurj hflat hlfp hQ).2 hfac))

end AlgebraicGeometry.Stack

end
