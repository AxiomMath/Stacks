module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The assertions for torsion sheaves on curves pass to a finite direct image

Let `k` be an algebraically closed field, let `f : X ⟶ Y` be a finite morphism of separated
schemes of finite type over `k` whose underlying spaces have dimension at most one, and let `F`
be a torsion abelian sheaf on the small étale site of `X`. Stacks Project Tag 0A5D asserts that
each of the eight statements of Situation 0A52 holds for the direct image `f_* F` as soon as it
holds for `F`. The eight statements are the vanishing of `H^q(X, F)` above degree two, its
vanishing above degree one when `X` is affine and when `F` is torsion of characteristic-primary
exponent, the finiteness of `H^q(X, F)` for constructible `F` of torsion prime to the
characteristic and for constructible `F` on a proper `X`, the bijectivity of the restriction map
`H^q(X, F) → H^q(X_{k'}, F|_{X_{k'}})` along an extension `k'/k` of algebraically closed fields
in those same two cases, and the surjectivity of `H²(X, F) → H²(U, F|_U)` for an open `U ⊆ X`.

The source proves all eight at once from a single input: because `f` is finite its higher direct
images vanish (Tag 03QP), so the Leray spectral sequence (Tag 0733) collapses to an
identification `H^q(X, F) = H^q(Y, f_* F)`, and every one of the eight statements is an assertion
about those groups. That identification is the hypothesis carried here, as
`Stacks.EtaleCohomology.DirectImageCohomologyComparison`; what is proved is that it transfers all
eight statements from `F` to `f_* F`, which is a different sheaf on a different scheme.

## Main definitions

* `Stacks.EtaleCohomology.CurveCohomologyStatements` is the conjunction of the eight statements of
  Situation 0A52 for one abelian sheaf, one field per numbered statement.
* `Stacks.EtaleCohomology.DirectImageCohomologyComparison` is the Leray identification of the
  cohomology of a sheaf with that of its direct image, together with its compatibility with the
  restriction map the last three statements are about.

## Main results

* `Stacks.EtaleCohomology.curveCohomologyStatements_smallEtaleDirectImageAb` is Tag 0A5D: the
  eight statements for `F` give the eight statements for `f_* F`.
* `Stacks.EtaleCohomology.bijective_of_comparisonSquare` and
  `Stacks.EtaleCohomology.surjective_of_comparisonSquare` are the transfer of bijectivity and of
  surjectivity of a map across a commuting square whose vertical maps are bijections.

## Implementation notes

**What the finiteness of `f` is used for.** Two of the eight statements have a side condition on
the scheme rather than on the coefficient sheaf, and for those two the transfer is not formal:
statement (2) is conditional on the base being affine and statement (7) on it being proper, and
both conditions have to be moved from `Y` to `X` against the direction of the comparison. A
finite morphism is affine, so an affine `Y` forces an affine `X` by
`AlgebraicGeometry.isAffine_of_isAffineHom`; and a finite morphism is proper, so a proper
structure morphism `π : Y ⟶ Spec k` forces the proper structure morphism `f ≫ π` of `X`. These
are the only places where `IsFinite f` enters, and they are why it is an assumption of the
theorem rather than of the comparison.

**What is carried as a hypothesis and why.** Three transfers of a side condition from `f_* F`
back to `F` are hypotheses of the theorem:

* statement (3) is conditional on the coefficient sheaf being `l`-power torsion and statement (6)
  on its being torsion prime to `p`, so the conclusion for `f_* F` assumes that of `f_* F` and
  must supply it for `F`. For a finite morphism the two are equivalent, because the stalk of
  `f_* F` at a point of `Y` is the sum of the stalks of `F` over the points of the fibre, but that
  stalk computation (Tag 03QP again, in its sheaf-theoretic form) is not available in this
  library, so `hprimePower` and `hprimeToChar` carry the direction the proof needs.
* statements (4) and (5) are conditional on the coefficient sheaf being constructible, and
  likewise need constructibility of `f_* F` to give constructibility of `F`. This library's
  constructibility predicate for abelian sheaves,
  `AlgebraicGeometry.IsConstructibleAbelianSheaf`, is stated for the small étale site of an
  object of a `BigEtaleSite`, which is not the site `Scheme.smallEtaleTopology` that the other six
  statements and Mathlib's `CategoryTheory.Sheaf.H` are about. Rather than drop the two
  statements, `CurveCohomologyStatements` takes the constructibility condition as a predicate
  parameter, so each of (4) and (5) is stated and transferred for an arbitrary such condition and
  in particular for the intended one; `hconstructible` is the transfer.

None of the three is the conclusion of the theorem, and none of them is about the same sheaf on
both sides.

**Hypotheses of Situation 0A52 that are absent.** The transfer uses neither the base field being
algebraically closed, nor the separatedness, the finite type or the dimension bound on `X` and
`Y`, nor the standing assumption that `F` is torsion in the sense of
`Stacks.Torsion.torsionSheafProperty`. None of those hypotheses therefore appears, which makes
the statement below stronger than the one Tag 0A5D makes and so implies it. Where a torsion
condition is part of a numbered statement, as in (3) and (6), it is
`Stacks.Torsion.IsPrimePowerTorsion` and `Stacks.Torsion.IsPrimeToCharacteristicTorsion`.

**The restriction map.** Statements (6), (7) and (8) are about
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` along an arbitrary morphism of schemes,
which is the morphism `i : Y' ⟶ Y` for `f_* F` and the morphism `j : X' ⟶ X` for `F`. Keeping
those two morphisms abstract rather than quantifying over extensions `k'/k` inside the statement
covers both uses the source makes of them — the projection of a scalar extension in (6) and (7)
and the inclusion of an open subscheme in (8) — and matches the transfer of the same eight
statements along a short exact sequence for Tag 0A5C. The comparison square relating the two
restriction maps is what Tag 0A5D gets from the compatibility of a finite direct image with
arbitrary base change (Tag 0959).

Vanishing is spelled `Subsingleton`, matching Mathlib's `CategoryTheory.Sheaf.H`, which is an
`Ext`-group from the constant sheaf `ℤ` and so has no canonical zero element to compare against.
The coefficient universe is `AddCommGrpCat.{max (u + 1) v}` for schemes in `Scheme.{u}`, the
family of universes in which étale cohomology of such a scheme is computed.

## References

* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section Transfer

/-- Bijectivity of a map transfers across a commuting square whose two vertical maps are
bijective: if `e' ∘ g = g' ∘ e` with `e` and `e'` bijective, then `g` is bijective as soon as
`g'` is. -/
theorem bijective_of_comparisonSquare {A B A' B' : Type*}
    {e : A → B} {e' : A' → B'} {g : A → A'} {g' : B → B'}
    (he : Function.Bijective e) (he' : Function.Bijective e')
    (hcomm : ∀ x, e' (g x) = g' (e x)) (hg' : Function.Bijective g') :
    Function.Bijective g := by
  rw [← he'.of_comp_iff' g]
  exact (funext hcomm : e' ∘ g = g' ∘ e) ▸ hg'.comp he

/-- Surjectivity of a map transfers across a commuting square `e' ∘ g = g' ∘ e` whose left-hand
vertical map is surjective and whose right-hand vertical map is injective. -/
theorem surjective_of_comparisonSquare {A B A' B' : Type*}
    {e : A → B} {e' : A' → B'} {g : A → A'} {g' : B → B'}
    (he : Function.Surjective e) (he' : Function.Injective e')
    (hcomm : ∀ x, e' (g x) = g' (e x)) (hg' : Function.Surjective g') :
    Function.Surjective g := fun y ↦ by
  obtain ⟨x, hx⟩ := hg' (e' y)
  obtain ⟨a, ha⟩ := he x
  exact ⟨a, he' (by rw [hcomm, ha, hx])⟩

end Transfer

section Statements

variable {Z Z' : Scheme.{u}} (i : Z' ⟶ Z)

/-- **The eight statements of Situation 0A52 for one abelian sheaf.** For a sheaf `G` on the small
étale site of a scheme `Z` with structure morphism `π` to the spectrum of a field, together with a
morphism `i : Z' ⟶ Z` along which cohomology is restricted, two integers `l` and `p` playing the
role of the characteristic and the exponential characteristic of that field, and a predicate
`constructible` playing the role of constructibility of a coefficient sheaf.

Stacks Project Tag 0A52 states the eight in the presence of an algebraically closed base field
and a separated finite-type `Z` of dimension at most one, and quantifies statements (6) and (7)
over extensions `k'/k` of algebraically closed fields rather than over a morphism `i`. Neither
restriction is imposed here, so this conjunction is stronger than the one the source makes. -/
structure CurveCohomologyStatements {k : Type u} [Field k] (π : Z ⟶ Spec (.of k)) (l p : ℕ)
    (constructible : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] : Prop where
  /-- **Statement (1), Tag 0A53.** The étale cohomology of `G` vanishes above degree two. -/
  vanishing : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{w} G q)
  /-- **Statement (2), Tag 0A54.** If `Z` is affine then the étale cohomology of `G` vanishes
  above degree one. -/
  vanishing_of_isAffine : IsAffine Z → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} G q)
  /-- **Statement (3), Tag 0A55.** If `G` is `l`-power torsion, `l` being the characteristic of
  the base field, then its étale cohomology vanishes above degree one. -/
  vanishing_of_isPrimePowerTorsion :
    Stacks.Torsion.IsPrimePowerTorsion Z.smallEtaleTopology l G →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} G q)
  /-- **Statement (4), Tag 0A56.** If `G` is constructible and torsion prime to `p`, the
  characteristic of the base field, then its étale cohomology is finite in every degree. -/
  finite_of_isPrimeToCharacteristicTorsion :
    constructible G → Stacks.Torsion.IsPrimeToCharacteristicTorsion Z.smallEtaleTopology p G →
      ∀ q : ℕ, Finite (Sheaf.H.{w} G q)
  /-- **Statement (5), Tag 0A57.** If `Z` is proper over the base field and `G` is constructible
  then the étale cohomology of `G` is finite in every degree. -/
  finite_of_isProper : constructible G → IsProper π → ∀ q : ℕ, Finite (Sheaf.H.{w} G q)
  /-- **Statement (6), Tag 0A58.** If `G` is torsion prime to `p`, the characteristic of the base
  field, then restriction along `i` is bijective on étale cohomology in every degree. In the
  source `i` is the projection of the scalar extension of `Z` along an extension of algebraically
  closed fields. -/
  bijective_restriction_of_isPrimeToCharacteristicTorsion :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion Z.smallEtaleTopology p G →
      ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i G q)
  /-- **Statement (7), Tag 0A59.** If `Z` is proper over the base field then restriction along `i`
  is bijective on étale cohomology in every degree, with no condition on `G`. In the source `i` is
  again the projection of a scalar extension. -/
  bijective_restriction_of_isProper :
    IsProper π → ∀ q : ℕ, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i G q)
  /-- **Statement (8), Tag 0A5A.** Restriction along `i` is surjective on étale cohomology in
  degree two. In the source `i` is the inclusion of an open subscheme of `Z`. -/
  surjective_restriction :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i G 2)

end Statements

section Comparison

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (i : Y' ⟶ Y) (j : X' ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The cohomological comparison a finite direct image supplies.** For a morphism `f : X ⟶ Y`
and an abelian sheaf `F` on the small étale site of `X`, an identification of the étale cohomology
of `F` with that of `f_* F` in every degree, a second such identification after restriction along
morphisms `j : X' ⟶ X` and `i : Y' ⟶ Y`, and the commutation of the two with the restriction
maps.

For a finite `f` this is what the source constructs: the higher direct images of `f` vanish (Tag
03QP), so the Leray spectral sequence (Tag 0733) degenerates to the first identification, the
compatibility of a finite direct image with arbitrary base change (Tag 0959) gives the second, and
the two are induced by the same morphism of spectral sequences, whence the square. -/
structure DirectImageCohomologyComparison
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) where
  /-- The Leray identification `H^q(Y, f_* F) ≃ H^q(X, F)` of the étale cohomology of the direct
  image with that of `F`. -/
  base (q : ℕ) : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q ≃+ Sheaf.H.{w} F q
  /-- The same identification after restriction, between the étale cohomology of the inverse image
  of `f_* F` along `i` and that of the inverse image of `F` along `j`. -/
  restriction (q : ℕ) :
    Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} i).obj
        ((smallEtaleDirectImageAb f).obj F)) q ≃+
      Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} j).obj F) q
  /-- The two identifications commute with restriction: restricting a class of the direct image
  along `i` and then comparing is the same as comparing and then restricting along `j`. -/
  restriction_comm (q : ℕ) (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    restriction q (etaleCohomologyRestrictionMap.{u, v, w} i
        ((smallEtaleDirectImageAb f).obj F) q x) =
      etaleCohomologyRestrictionMap.{u, v, w} j F q (base q x)

end Comparison

section DirectImage

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (i : Y' ⟶ Y) (j : X' ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}

/-- Vanishing of the étale cohomology of `F` in a degree gives vanishing of that of `f_* F` in
the same degree, by the comparison. -/
private theorem subsingleton_smallEtaleDirectImageAb
    (c : DirectImageCohomologyComparison.{u, v, w} f i j F) (q : ℕ)
    (hq : Subsingleton (Sheaf.H.{w} F q)) :
    Subsingleton (Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) := by
  have := hq
  exact (c.base q).injective.subsingleton

/-- Finiteness of the étale cohomology of `F` in a degree gives finiteness of that of `f_* F` in
the same degree, by the comparison. -/
private theorem finite_smallEtaleDirectImageAb
    (c : DirectImageCohomologyComparison.{u, v, w} f i j F) (q : ℕ)
    (hq : Finite (Sheaf.H.{w} F q)) :
    Finite (Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) := by
  have := hq
  exact Finite.of_injective (c.base q) (c.base q).injective

/-- Bijectivity of restriction along `j` for `F` gives bijectivity of restriction along `i` for
`f_* F`, by the comparison square. -/
private theorem bijective_restriction_smallEtaleDirectImageAb
    (c : DirectImageCohomologyComparison.{u, v, w} f i j F) (q : ℕ)
    (hq : Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} j F q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i
      ((smallEtaleDirectImageAb f).obj F) q) :=
  bijective_of_comparisonSquare (c.base q).bijective (c.restriction q).bijective
    (c.restriction_comm q) hq

/-- Surjectivity of restriction along `j` for `F` in degree two gives surjectivity of restriction
along `i` for `f_* F` in degree two, by the comparison square. -/
private theorem surjective_restriction_smallEtaleDirectImageAb
    (c : DirectImageCohomologyComparison.{u, v, w} f i j F)
    (hq : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} j F 2)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i
      ((smallEtaleDirectImageAb f).obj F) 2) :=
  surjective_of_comparisonSquare (c.base 2).surjective (c.restriction 2).injective
    (c.restriction_comm 2) hq

/-- Let `f : X ⟶ Y` be a finite morphism of schemes and let `F` be an abelian sheaf on the small
étale site of `X`. If the eight statements of Situation 0A52 hold for `F`, relative to the
structure morphism `f ≫ π` of `X` and to restriction along `j`, then they hold for the direct
image `f_* F`, relative to the structure morphism `π` of `Y` and to restriction along `i`.

The input is the comparison `c` of the étale cohomology of `F` with that of `f_* F`, which for a
finite morphism comes from the vanishing of the higher direct images and the Leray spectral
sequence. Beyond it the proof needs that the side conditions of the eight statements move between
the two sheaves. The two conditions on the scheme move by finiteness of `f`: an affine `Y` forces
an affine `X`, and a proper `π` forces a proper `f ≫ π`. The three conditions on the coefficient
sheaf are carried: `hprimePower` and `hprimeToChar` for the two torsion conditions and
`hconstructible` for constructibility, each in the direction from `f_* F` to `F`, which for a
finite morphism holds because the stalks of `f_* F` are the sums of the stalks of `F` over the
fibres. -/
@[stacks 0A5D "the eight statements of Situation 0A52 pass to a finite direct image, over the
Leray comparison and over the transfer of the torsion and constructibility side conditions"]
theorem curveCohomologyStatements_smallEtaleDirectImageAb {k : Type u} [Field k]
    (π : Y ⟶ Spec (.of k)) (l p : ℕ) [IsFinite f]
    {constructibleSource : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    {constructibleTarget : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
    (c : DirectImageCohomologyComparison.{u, v, w} f i j F)
    (hprimePower : Stacks.Torsion.IsPrimePowerTorsion Y.smallEtaleTopology l
        ((smallEtaleDirectImageAb f).obj F) →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l F)
    (hprimeToChar : Stacks.Torsion.IsPrimeToCharacteristicTorsion Y.smallEtaleTopology p
        ((smallEtaleDirectImageAb f).obj F) →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p F)
    (hconstructible : constructibleTarget ((smallEtaleDirectImageAb f).obj F) →
      constructibleSource F)
    (h : CurveCohomologyStatements.{u, v, w} j (f ≫ π) l p constructibleSource F) :
    CurveCohomologyStatements.{u, v, w} i π l p constructibleTarget
      ((smallEtaleDirectImageAb f).obj F) where
  vanishing q hq :=
    subsingleton_smallEtaleDirectImageAb f i j c q (h.vanishing q hq)
  vanishing_of_isAffine hY q hq := by
    have : IsAffine Y := hY
    exact subsingleton_smallEtaleDirectImageAb f i j c q
      (h.vanishing_of_isAffine (isAffine_of_isAffineHom f) q hq)
  vanishing_of_isPrimePowerTorsion htorsion q hq :=
    subsingleton_smallEtaleDirectImageAb f i j c q
      (h.vanishing_of_isPrimePowerTorsion (hprimePower htorsion) q hq)
  finite_of_isPrimeToCharacteristicTorsion hconstr htorsion q :=
    finite_smallEtaleDirectImageAb f i j c q
      (h.finite_of_isPrimeToCharacteristicTorsion (hconstructible hconstr)
        (hprimeToChar htorsion) q)
  finite_of_isProper hconstr hproper q := by
    have : IsProper π := hproper
    exact finite_smallEtaleDirectImageAb f i j c q
      (h.finite_of_isProper (hconstructible hconstr) inferInstance q)
  bijective_restriction_of_isPrimeToCharacteristicTorsion htorsion q :=
    bijective_restriction_smallEtaleDirectImageAb f i j c q
      (h.bijective_restriction_of_isPrimeToCharacteristicTorsion (hprimeToChar htorsion) q)
  bijective_restriction_of_isProper hproper q := by
    have : IsProper π := hproper
    exact bijective_restriction_smallEtaleDirectImageAb f i j c q
      (h.bijective_restriction_of_isProper inferInstance q)
  surjective_restriction :=
    surjective_restriction_smallEtaleDirectImageAb f i j c h.surjective_restriction

end DirectImage

end Stacks.EtaleCohomology

end
