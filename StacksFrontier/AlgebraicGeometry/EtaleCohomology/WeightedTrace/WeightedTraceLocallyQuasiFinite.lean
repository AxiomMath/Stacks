module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GenericSeparableDegree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.UniversallyOpen

/-!
# The weighting of a locally quasi-finite morphism over a geometrically unibranch base

Let `Y` be a geometrically unibranch and locally Noetherian scheme and let `f : X ⟶ Y` be
locally quasi-finite. The generic-separable-degree function of
`AlgebraicGeometry.exists_weighting_genericSeparableDegree` is then a weighting of `f`, and this
file assembles the first assertion of Stacks 0GKJ out of it: an integer-valued weighting, whose
value at each point is that generic separable degree, which is nonnegative, and which restricts
along an arbitrary base change of `f` to a weighting there, with no hypothesis whatsoever on the
new base.

The other assertion of Stacks 0GKJ — the trace maps `Tr_{f, w, K} : f_! f^{-1}K ⟶ K` that the
example reads off Lemmas 0GKG and 0GKH for this `f` and `w` — is not part of this file. Those two
lemmas are statements about an arbitrary weighting of an arbitrary locally quasi-finite morphism,
so nothing about them is special to this example's hypotheses; the trace map is
`AlgebraicGeometry.SmallEtale.weightedTrace`, and that assertion, instantiated at the weighting
below, is `AlgebraicGeometry.SmallEtale.exists_weighting_weightedTrace_of_isGeometricallyUnibranch`.

## Main results

* `AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch` — the
  weighting of Stacks 0GKJ: a locally quasi-finite morphism locally of finite type onto a
  geometrically unibranch locally Noetherian scheme carries a nonnegative integer-valued
  weighting whose value at a point is the generic separable degree of the strict henselizations
  there, and whose restriction along every base change of `f` is a weighting of that base change.
* `AlgebraicGeometry.exists_nonneg_weighting_of_isGeometricallyUnibranch` — the bare existence
  statement, without the description of the weight or its base changes.
* `AlgebraicGeometry.exists_nonneg_weighting_of_isNormal` — the same for a normal locally
  Noetherian base, which is the case of a normal variety that Stacks 0GKJ offers as its example.
* `AlgebraicGeometry.exists_nonneg_weighting_of_isPullback` — an arbitrary base change of such a
  morphism carries a nonnegative weighting too, namely the restriction of the weighting upstairs.
* `AlgebraicGeometry.not_exists_positive_weighting_of_not_universallyOpen` — a locally
  quasi-finite morphism which is not universally open carries no everywhere positive weighting,
  which is why the statements above are nonnegative and not positive.

## Implementation notes

**Nonnegative, not positive.** Stacks 0GKJ calls the weighting it produces *positive*, and in
Stacks a positive weighting is one with values in the strictly positive integers: More on
Morphisms, Section 37.75 introduces the term with the gloss "i.e., `w : X → Z_{>0}`", and Stacks
0F3C is stated for a weighting with `w x > 0` for all `x`. The weighting of Stacks 0F3E, which
0GKJ cites for the weighting it produces, has target `Z_{≥0}`, and nonnegative is all that is
true:
for the closed immersion of the closed fibre of a discrete valuation ring into its spectrum —
locally quasi-finite, with a normal Noetherian target — the generic fibre of the strict
henselization upstairs is empty over the generic point downstairs, so the generic separable
degree is `0`. (Independently: a nonzero morphism from the pushforward of the constant sheaf on
the closed point to the constant sheaf on the spectrum would have to be nonzero on global
sections while restricting to `0` on the open point, which the constant sheaf on an irreducible
scheme forbids. So the only weighting for which the trace of Stacks 0GKG can exist there is
`0`.) The statements below therefore carry `0 ≤ w x`, and nothing claims `0 < w x`. The word
*positive* is the one place where Stacks 0GKJ asks for more than the lemma it cites gives.

The obstruction to `0 < w x` is recorded as a theorem rather than left to prose:
`AlgebraicGeometry.not_exists_positive_weighting_of_not_universallyOpen` says that a locally
quasi-finite morphism which is not universally open carries no everywhere positive weighting at
all, whatever its base. This is Stacks 0F3C read backwards, and it shows that the word
*positive* in Stacks 0GKJ cannot be obtained from any argument: the closed immersion of a closed
point of a one-dimensional normal Noetherian scheme is locally quasi-finite over a base which is
normal, Noetherian and hence geometrically unibranch, and it is not open, so for it a positive
weighting does not exist. For the closed immersion of the closed point `(2)` into `Spec ℤ`,
`AlgebraicGeometry.exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting` exhibits a
locally quasi-finite morphism locally of finite type onto a normal, geometrically unibranch and
locally Noetherian scheme which carries a nonnegative weighting and no positive one.

**The trace maps.** The construction of `Tr_{f, w}` in Stacks 0GKG goes through the
finite-support direct image *presheaf* `f_{p!}` of Stacks 0F6E: a section of `f_{p!}Z(V)` is a
locally constant integer-valued section supported on a locally closed `Z ⊂ X_V` finite over `V`,
one decomposes it into the open-and-closed level sets `U_n` where it takes the value `n`, and
sends it to the sum over nonzero `n` of `n` times the fibre integral `∫_{U_n → V} w|_{U_n}`; it
is the defining property of a weighting that each such fibre integral is locally constant on
`V`, so the sum lands in `Z(V)`. Sheafifying gives `f_!Z ⟶ Z`, and tensoring with `F` through
the canonical isomorphism `f_! f^{-1}F = f_!Z ⊗ F` of Stacks 0GKF gives the trace.

**Why the étale case does not generalise.** For an étale `j`, `j_!` is a left adjoint of `j^{-1}`,
and the trace is the counit of that adjunction; that is how it is defined in
`AlgebraicGeometry.etaleCanonicalTrace`. The counit does not mention a weighting at all, and the
fact that reconciles it with Stacks 0GKG is the separate computation that the canonical weighting
of an étale morphism is the constant function `1`
(`AlgebraicGeometry.flatQuasiFiniteWeight_eq_one_of_etale`). For a locally quasi-finite `f` that
is not étale there is no such adjunction: the adjoint that `f_!` does have is a *right* adjoint
`f^!` (`AlgebraicGeometry.SmallEtale.fShriekAdjunction`, Stacks 0F59), whose counit is
`f_! f^! ⟶ 𝟭`, not `f_! f^{-1} ⟶ 𝟭`. A morphism `f_! f^{-1}F ⟶ F` genuinely depends on the
weighting — for the weighting `0` it is the zero morphism — so no counit can produce it. The
étale construction therefore has no generalisation to a locally quasi-finite morphism: the trace
maps of Stacks 0GKJ need the fibre-integral construction of Stacks 0GKG.

**Relation to Stacks 0F3E.** The weighting and the generic-separable-degree formula for its
values are 0F3E; what is added here is the coercion into the integer-valued
interface that a weighting has by definition, the nonnegativity that coercion makes visible, the
restriction of that one weighting along an arbitrary base change, and the normal case that
Stacks 0GKJ names as its example.

## References

* [Stacks Project, Tag 0GKJ](https://stacks.math.columbia.edu/tag/0GKJ)
* [Stacks Project, Tag 0F3E](https://stacks.math.columbia.edu/tag/0F3E)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
* [Stacks Project, Tag 0BQ3](https://stacks.math.columbia.edu/tag/0BQ3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A locally quasi-finite morphism locally of finite type onto a geometrically unibranch
locally Noetherian scheme carries an integer-valued weighting `w` which is nonnegative, whose
restriction along an arbitrary base change of `f` is a weighting of that base change, and whose
value at a point `x` is the generic separable degree of the strict henselization of the local
ring at `x` over the strict henselization of the local ring at `f x` — the number of geometric
points of the generic fibre of `Spec O_{X, x}^{sh} ⟶ Spec O_{Y, f(x)}^{sh}`, which is how
Stacks 0GKJ describes it.

The last conjunct is the description quantified over all compatible choices of strict
henselizations, of the minimal prime of the one downstairs and of an algebraic closure of its
residue field, exactly as in `AlgebraicGeometry.exists_weighting_genericSeparableDegree`, so no
choice of henselization is built into the statement.

`0 ≤ w x` is all the sign information there is, and the source's word *positive* cannot be
taken literally: see the implementation notes and
`AlgebraicGeometry.not_exists_positive_weighting_of_not_universallyOpen`. -/
@[stacks 0GKJ "the weighting of the example, with the sign the cited lemma gives: a locally \
quasi-finite morphism locally of finite type onto a geometrically unibranch locally Noetherian \
base carries a weighting w, nonnegative, equal at each point to the generic separable degree of \
the strict henselizations, and restricting along every base change of f to a weighting there. \
Nonnegative and not positive is what the source's own citation 0F3E gives, and 0F3C forbids \
more for an f that is not universally open. The trace maps Tr_{f, w, K} that the example then \
reads off 0GKG and 0GKH for this f and w are not asserted here; they come from \
`AlgebraicGeometry.SmallEtale.weightedTrace` and 0GKH, both of which are about an arbitrary \
weighting and not about this example's hypotheses. The whole example, this weighting together \
with its trace maps on abelian sheaves and on D(Y_étale, Λ), is the theorem \
`exists_weighting_derivedWeightedTraceMod_of_isGeometricallyUnibranch` of the namespace \
`AlgebraicGeometry.SmallEtale`"]
public theorem exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsLocallyNoetherian Y] (hY : IsGeometricallyUnibranch Y) :
    ∃ w : X → ℤ,
      IsWeighting f w ∧
      (∀ x : X, 0 ≤ w x) ∧
      (∀ (X' Y' : Scheme.{u}) (q : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
        IsPullback q f' f g → IsWeighting f' (w ∘ q)) ∧
      ∀ (x : X)
        (κY : Type u) [Field κY]
        [Algebra (maximalIdeal (Y.presheaf.stalk (f x))).ResidueField κY]
        [IsSepClosure (maximalIdeal (Y.presheaf.stalk (f x))).ResidueField κY]
        (Rsh : Type u) [CommRing Rsh] [IsLocalRing Rsh]
        [Algebra (Y.presheaf.stalk (f x)) Rsh]
        (_hRsh : Stacks.StrictHenselization.IsStrictHenselization
          (Y.presheaf.stalk (f x)) κY Rsh)
        (κX : Type u) [Field κX]
        [Algebra (maximalIdeal (X.presheaf.stalk x)).ResidueField κX]
        [IsSepClosure (maximalIdeal (X.presheaf.stalk x)).ResidueField κX]
        (Ssh : Type u) [CommRing Ssh] [IsLocalRing Ssh]
        [Algebra (X.presheaf.stalk x) Ssh] [Algebra Rsh Ssh]
        [Algebra (Y.presheaf.stalk (f x)) Ssh]
        [IsScalarTower (Y.presheaf.stalk (f x)) Rsh Ssh]
        (_hSsh : Stacks.StrictHenselization.IsStrictHenselization
          (X.presheaf.stalk x) κX Ssh)
        (_hcomp : (algebraMap (Y.presheaf.stalk (f x)) Ssh) =
          (algebraMap (X.presheaf.stalk x) Ssh).comp (f.stalkMap x).hom)
        (p : Ideal Rsh) [p.IsPrime] (_hp : p ∈ minimalPrimes Rsh)
        (Kbar : Type u) [Field Kbar]
        [Algebra p.ResidueField Kbar] [IsAlgClosure p.ResidueField Kbar],
        w x = (Nat.card (AlgHom p.ResidueField
          (TensorProduct Rsh p.ResidueField Ssh) Kbar) : ℤ) := by
  obtain ⟨w, hw, hdescription⟩ := exists_weighting_genericSeparableDegree f hY
  refine ⟨fun x => (w x : ℤ), hw, fun x => Int.natCast_nonneg (w x),
    fun _ _ _ _ _ sq => hw.comp_of_isPullback sq, ?_⟩
  intro x κY _ _ _ Rsh _ _ _ hRsh κX _ _ _ Ssh _ _ _ _ _ _ hSsh hcomp p _ hp Kbar _ _ _
  exact congrArg (fun n : ℕ => (n : ℤ))
    (hdescription x κY Rsh hRsh κX Ssh hSsh hcomp p hp Kbar)

/-- A locally quasi-finite morphism locally of finite type onto a geometrically unibranch
locally Noetherian scheme carries a nonnegative integer-valued weighting, namely the
generic-separable-degree weighting of Stacks 0F3E read as a function to `ℤ`.

This is the bare existence statement, without the description of the weighting or its behaviour
under base change; the full first assertion of Stacks 0GKJ is
`AlgebraicGeometry.exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch`. Note
that `0 ≤ w x` is all the sign information there is: the weight vanishes at a point of the
source whose strict henselization has empty generic fibre over the generic point below it. -/
public theorem exists_nonneg_weighting_of_isGeometricallyUnibranch
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsLocallyNoetherian Y] (hY : IsGeometricallyUnibranch Y) :
    ∃ w : X → ℤ, IsWeighting f w ∧ ∀ x : X, 0 ≤ w x := by
  obtain ⟨w, hw, hnonneg, -, -⟩ :=
    exists_weighting_genericSeparableDegree_of_isGeometricallyUnibranch f hY
  exact ⟨w, hw, hnonneg⟩

/-- A locally quasi-finite morphism locally of finite type onto a normal locally Noetherian
scheme carries a nonnegative integer-valued weighting: a normal scheme is geometrically
unibranch. This is the example Stacks 0GKJ names, a normal variety as the base. -/
public theorem exists_nonneg_weighting_of_isNormal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsLocallyNoetherian Y] [IsNormal Y] :
    ∃ w : X → ℤ, IsWeighting f w ∧ ∀ x : X, 0 ≤ w x :=
  exists_nonneg_weighting_of_isGeometricallyUnibranch f isGeometricallyUnibranch_of_isNormal

/-- An arbitrary base change of a locally quasi-finite morphism locally of finite type onto a
geometrically unibranch locally Noetherian scheme carries a nonnegative integer-valued weighting,
obtained by restricting the weighting upstairs along the projection.

No hypothesis is placed on the new base: that is the point of the closing remark of Stacks 0GKJ,
which observes that the restricted weighting is a weighting of the base change while in general
having no description in terms of the base change itself. -/
public theorem exists_nonneg_weighting_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y]
    (hY : IsGeometricallyUnibranch Y) (sq : IsPullback p f' f g) :
    ∃ w' : X' → ℤ, IsWeighting f' w' ∧ ∀ x' : X', 0 ≤ w' x' := by
  obtain ⟨w, hw, hnonneg⟩ := exists_nonneg_weighting_of_isGeometricallyUnibranch f hY
  exact ⟨w ∘ p, hw.comp_of_isPullback sq, fun x' => hnonneg (p x')⟩

/-- A locally quasi-finite morphism locally of finite type which is not universally open carries
no everywhere positive weighting.

This is Stacks 0F3C read backwards, and it is the precise reason the existence statements above
give `0 ≤ w x` rather than the `0 < w x` that the word *positive* in Stacks 0GKJ asks for: a
positive weighting is not available for an arbitrary locally quasi-finite morphism onto a
geometrically unibranch locally Noetherian base, because such a morphism need not be open. The
morphism witnessing that is the closed immersion of the closed point `(2)` into `Spec ℤ`; see
`AlgebraicGeometry.exists_locallyQuasiFinite_isNormal_not_exists_positive_weighting` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.NoPositiveWeighting`, which puts
this theorem together with that witness and so needs no hypothesis. -/
public theorem not_exists_positive_weighting_of_not_universallyOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hf : ¬ UniversallyOpen f) :
    ¬ ∃ w : X → ℤ, IsWeighting f w ∧ ∀ x : X, 0 < w x := fun ⟨_, hw, hpos⟩ =>
  hf (universallyOpen_of_positive_weighting hw hpos)

end AlgebraicGeometry

end
