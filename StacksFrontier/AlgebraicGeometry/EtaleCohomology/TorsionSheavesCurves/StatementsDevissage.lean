module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.RestrictToDenseOpen
import StacksCore.Tactic.StacksAttribute

/-!
# Dévissage of the assertions for torsion sheaves on curves along direct sums

Let `k` be an algebraically closed field, let `X` be a separated finite type scheme over `k` of
dimension at most one and let `F` be a torsion abelian sheaf on `X_étale`.  Stacks Project Tag
03SC asserts that the eight statements of Situation 0A52 hold for `F`.  Its proof is a dévissage
with four steps, and this file supplies the two of them that move the eight statements across a
direct sum.

## Main results

* `Stacks.EtaleCohomology.curveCohomologyStatements_of_iso`: the eight statements depend only on
  the isomorphism class of the coefficient sheaf.
* `Stacks.EtaleCohomology.curveCohomologyStatements_biproduct`: the eight statements are closed
  under a finite direct sum of abelian sheaves.
* `Stacks.EtaleCohomology.curveCohomologyStatements_of_biproduct_extensionByZero`: the last two
  steps of the proof of Tag 03SC, from the base case of Tag 03SD for the summands to the eight
  statements for `F`.
* `Stacks.EtaleCohomology.curveCohomologyStatements_of_biproduct_extensionByZero_of_closedPoints`:
  the same, with the positive-degree vanishing on the closed part discharged.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03SD](https://stacks.math.columbia.edu/tag/03SD)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 0GJA](https://stacks.math.columbia.edu/tag/0GJA)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open ZeroObject

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

section Devissage

variable {X Y : Scheme.{u}} (i : Y ⟶ X) {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (l p : ℕ)
  {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The eight statements of Situation 0A52 depend only on the isomorphism class of the
coefficient sheaf.**  An isomorphism `e : F ≅ G` makes `0 ⟶ F ⟶ G ⟶ 0 ⟶ 0` a split short exact
sequence, so this is Tag 0A5C applied to that sequence, with the eight statements for the zero
sheaf supplied by `Stacks.EtaleCohomology.curveCohomologyStatements_of_isZero`.

`hconstructible` is the descent of the abstract constructibility predicate along a short exact
sequence, which is what Tag 0A5C consumes; the source gets it from Proposition 09BH. -/
theorem curveCohomologyStatements_of_iso
    (hconstructible :
      ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        S.ShortExact → constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (e : F ≅ G)
    (h : CurveCohomologyStatements.{u, v, w} i π l p constructible F) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible G := by
  have hS : (ShortComplex.mk e.hom (0 : G ⟶ 0) (by simp)).ShortExact :=
    ShortComplex.Splitting.shortExact
      { r := e.inv
        s := 0
        f_r := by simp
        s_g := (isZero_zero _).eq_of_tgt _ _
        id := by simp }
  exact curveCohomologyStatements_X₂_of_shortExact_of_constructible_and.{u, v, w} i π l p hS
    (hconstructible _ hS) h
    (curveCohomologyStatements_of_isZero.{u, v, w} i π l p (isZero_zero _))

/-- **The eight statements of Situation 0A52 are closed under finite direct sums.**  If each
member of a finite family `G` of abelian sheaves on the small étale site of `X` satisfies the
eight statements, so does its direct sum.

The induction is on the number of summands, over the split short exact sequence
`0 ⟶ G 0 ⟶ ⨁ G ⟶ ⨁ (G ∘ Fin.succ) ⟶ 0` and Tag 0A5C; the empty direct sum is a zero object.

In the proof of Tag 03SC this step is used twice: to split a constructible torsion sheaf into its
`ℓ`-primary parts, and to split `j_!G` into the contributions `j_{a!}(G|_{U_a})` of the
irreducible components of the dense open on which `G` is finite locally constant. -/
theorem curveCohomologyStatements_biproduct
    (hconstructible :
      ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        S.ShortExact → constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    (n : ℕ) (G : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h : ∀ a, CurveCohomologyStatements.{u, v, w} i π l p constructible (G a)) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible (⨁ G) := by
  induction n with
  | zero =>
    refine curveCohomologyStatements_of_isZero.{u, v, w} i π l p ?_
    rw [IsZero.iff_id_eq_zero, ← biproduct.total]
    simp
  | succ n ih =>
    have hz : biproduct.ι G 0 ≫ (biproduct.lift fun a : Fin n => biproduct.π G a.succ) = 0 :=
      biproduct.hom_ext _ _ fun a => by
        simp [biproduct.ι_π_ne G (Fin.succ_ne_zero a).symm]
    have hS : (ShortComplex.mk (biproduct.ι G 0)
        (biproduct.lift fun a : Fin n => biproduct.π G a.succ) hz).ShortExact :=
      ShortComplex.Splitting.shortExact
        { r := biproduct.π G 0
          s := biproduct.desc fun a : Fin n => biproduct.ι G a.succ
          f_r := biproduct.ι_π_self G 0
          s_g := by
            refine biproduct.hom_ext' _ _ fun b => biproduct.hom_ext _ _ fun a => ?_
            by_cases hab : b = a
            · subst hab; simp
            · simp [biproduct.ι_π_ne _ hab,
                biproduct.ι_π_ne G fun hh => hab (Fin.succ_injective _ hh)]
          id := by rw [biproduct.lift_desc, ← biproduct.total, Fin.sum_univ_succ] }
    exact curveCohomologyStatements_X₂_of_shortExact_of_constructible_and.{u, v, w} i π l p hS
      (hconstructible _ hS)
      (h 0) (ih _ fun a => h a.succ)

end Devissage

/-! ### Tag 03SC: the dévissage to the base case over a dense open -/

section Reduction

variable {X Z X' Y : Scheme.{u}} (i' : Z ⟶ X) (j : X' ⟶ X) (i : Y ⟶ X)
  [IsClosedImmersion i'] [IsOpenImmersion j]
  {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (l p : ℕ)
  {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} → Prop}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks Project, Tag 03SC, its final dévissage.** Let `j : X' ⟶ X` be an open immersion and
`i' : Z ⟶ X` a closed immersion onto the complement of its image. Let `F` be an abelian sheaf on
the small étale site of `X`, and suppose the extension by zero `j_! j^{-1} F` is the direct sum of
a finite family `G` of abelian sheaves for each of which the eight statements of Situation 0A52
hold. Then the eight statements hold for `F`.

This is the last two paragraphs of the source's proof of Tag 03SC. There `X` is a separated finite
type scheme of dimension at most one over an algebraically closed field `k`, `F` is a constructible
sheaf of `𝔽_ℓ`-vector spaces, `X'` is a dense open on which `F` is finite locally constant and
decomposed as `X' = U₁ ⨿ … ⨿ Uₙ` into irreducible components, and `G a = j_{a!}(F|_{U_a})`, so that
the family is the decomposition `j_!j^{-1}F = ⨁ⱼ j_{a!}(F|_{U_a})` and the eight statements for
each `G a` are Tag 03SD. The proof assembles three results: the direct-sum dévissage
`Stacks.EtaleCohomology.curveCohomologyStatements_biproduct` of this file, the transport along `e`
of `Stacks.EtaleCohomology.curveCohomologyStatements_of_iso`, and the extension step of Tag 0A5C
over the localization sequence of Tag 095L, which is the backward implication of Tag 0GJA.

## What is carried, and why

* `hG` is the base case, Tag 03SD, which this library does not have, and carrying it is the point
  of this statement. The obstruction is **not** the three inputs of the source's proof of that
  base case, all of which are registered here: the trace of Proposition 03SE, on
  `AlgebraicGeometry.abelianTrace` and `AlgebraicGeometry.moduleTrace` of
  `ExtensionByZeroBaseChange/Trace.lean`; Zariski's main theorem in the form the proof uses, the
  separated quasi-finite factorization through a finite morphism of Tag 05K0, on
  `Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization` of
  `FiniteFactorization/Basic.lean`; and the normalization of a curve, Tag 0BXR, on
  `AlgebraicGeometry.exists_iso_normalizationSchemeOverField_coproduct_normal_irreducible` and
  `AlgebraicGeometry.isVariety_normalizationOverField` of
  `Variety/OneDimensional/NormalizationOverField.lean`, with the local rings of a smooth curve
  described by Tag 0B8Y on
  `AlgebraicGeometry.smoothAt_closedPoint_tfae_of_isCurve_of_isSeparable` of
  `CurveLocalRing/Smooth.lean`. What is absent is the chain 0A5B → 03SG → 0A3Q → 03SD itself: no
  declaration in this library carries any of those four tags. At the foot of the chain, Tag 0A5B,
  the `ℓ = char k` half is no longer an absence of mathematics — it rests on Tags 0A3K, 0A3N and
  0A3P, all three registered in `ArtinSchreierSequence/`, and
  `ArtinSchreierSequence/ConstantSequenceDatum.lean` registers forms of all three in which the
  Artin–Schreier sequence of Tag 0A3J is supplied rather than assumed. The two obligations that
  remain at 0A5B are its coefficient-universe design and, for the `ℓ ≠ char k` half, the
  Picard-scheme representability of Tag 0B9Z, which this library does not have.
* `e` is the geometric input of the source's third and fourth paragraphs: the choice of the dense
  open, the shrinking that makes its components disjoint, and the resulting decomposition of the
  extension by zero. Only the decomposition is used, so it is what is assumed.
* `hvanish`, `hfinite` and `hrestr` are the cohomology of the closed part, exactly as in Tag 0GJA:
  `Z` is a finite set of `k`-rational points, so that cohomology is concentrated in degree zero,
  finite there, and insensitive to an extension of the algebraically closed ground field. Of these
  three, `hvanish` is the one this library can prove, as
  `Stacks.EtaleCohomology.subsingleton_etaleCohomology_directImage_of_closed_points`.
* `hconstructible` is the descent of the abstract constructibility predicate along a short exact
  sequence, which is Proposition 09BH; it is the hypothesis Tag 0A5C already carries.

**Hypotheses of Situation 0A52 that are absent.** None of the standing hypotheses of Tag 03SC is
used: not the base field being algebraically closed, not the separatedness, the finite type or the
dimension bound on `X`, not the constructibility of `F`, not its being torsion, and not the density
of the open `X'`. The density and the dimension bound act only through `hvanish`, `hfinite` and
`hrestr`, which are assumed. The statement below is therefore stronger than the step of Tag 03SC it
formalizes, and so implies it. Where a torsion or constructibility condition is part of one of the
eight statements, it is the one carried by
`Stacks.EtaleCohomology.CurveCohomologyStatements` itself.

The source's first two paragraphs are *not* covered: the reduction of `X` to its reduction
(Proposition 03SI), the presentation of a torsion sheaf as a filtered colimit of constructible
sheaves (Lemma 03SA) together with the commutation of cohomology with filtered colimits (Lemma
03Q5), and the `ℓ`-primary dévissage of a constructible torsion sheaf. The last of those is an
application of `Stacks.EtaleCohomology.curveCohomologyStatements_biproduct` and of Tag 0A5C once
the primary decomposition of a torsion abelian sheaf is available, which it is not.

This is a step of [Stacks, Tag 03SC], which is registered unconditionally on
`Stacks.EtaleCohomology.torsionCurveAssertions`; scope of this step: the final dévissage only: from
Tag 03SD for the summands (hG) and the decomposition of j_! j^{-1} F over the irreducible
components of the dense open (e), across the localization sequence of Tag 095L. Carried: Tag 03SD
(hG), the decomposition (e), the degree-zero cohomology and the restriction bijectivity of the
closed part (hfinite, hrestr), and the Proposition 09BH descent of constructibility
(hconstructible). Not covered: the reduction to a reduced X (Proposition 03SI) and to a
constructible sheaf (Lemmas 03SA and 03Q5), and the l-primary dévissage. -/
theorem curveCohomologyStatements_of_biproduct_extensionByZero
    (hij : Set.range j.base = (Set.range i'.base)ᶜ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hvanish : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H.{w}
      ((etaleAbelianDirectImage.{u, v} i').obj ((etaleAbelianInverseImage.{u, v} i').obj F)) q))
    (hfinite : Finite (Sheaf.H.{w}
      ((etaleAbelianDirectImage.{u, v} i').obj ((etaleAbelianInverseImage.{u, v} i').obj F)) 0))
    (hrestr : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} i
      ((etaleAbelianDirectImage.{u, v} i').obj ((etaleAbelianInverseImage.{u, v} i').obj F)) q))
    (hconstructible :
      ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}),
        S.ShortExact → constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    (n : ℕ) (G : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (e : (⨁ G) ≅ (extensionByZero.{u, v} j).obj ((etaleRestriction.{u, v} j).obj F))
    (hG : ∀ a, CurveCohomologyStatements.{u, v, w} i π l p constructible (G a)) :
    CurveCohomologyStatements.{u, v, w} i π l p constructible F := by
  have hS := openClosedShortComplex_shortExact.{u, v} i' j hij F
  exact curveCohomologyStatements_X₂_of_shortExact_of_constructible_and.{u, v, w} i π l p hS
    (hconstructible _ hS)
    (curveCohomologyStatements_of_iso.{u, v, w} i π l p hconstructible e
      (curveCohomologyStatements_biproduct.{u, v, w} i π l p hconstructible n G hG))
    (curveCohomologyStatements_of_cohomology_concentrated.{u, v, w} i π l p hvanish hfinite hrestr)

/-- **Stacks Project, Tag 03SC, its final dévissage, with the vanishing on the closed part
discharged.** This is
`Stacks.EtaleCohomology.curveCohomologyStatements_of_biproduct_extensionByZero` with the
positive-degree cohomology of the closed part replaced by the geometric hypotheses it follows
from: `Z` is affine, each of its points is closed, and each of its residue fields is separably
closed. In the source `Z` is the complement of a dense open in a scheme of dimension at most one
over an algebraically closed field, hence a finite set of `k`-rational points, which satisfies all
three.

The input is `Stacks.EtaleCohomology.subsingleton_etaleCohomology_directImage_of_closed_points`,
which is stated at the coefficient universe `AddCommGrpCat.{u + 1}`; that is why the coefficient
and `Ext` universes are specialized here, whereas the theorem above leaves them free. Two of the
three cohomological hypotheses on the closed part remain, `hfinite` and `hrestr`, because this
library does not have them.

This is a step of [Stacks, Tag 03SC], which is registered unconditionally on
`Stacks.EtaleCohomology.torsionCurveAssertions`; scope of this step: the final dévissage again, at
the coefficient universe u + 1, with the positive-degree vanishing on the closed part discharged
from Tags 03QP and 09AY and replaced by its geometric hypotheses (hclosed, hsep). Still
carried: Tag 03SD (hG), the decomposition (e), the degree-zero cohomology and the restriction
bijectivity of the closed part (hfinite, hrestr), and the Proposition 09BH descent of
constructibility (hconstructible). Not covered: the reduction to a reduced X (Proposition 03SI) and
to a constructible sheaf (Lemmas 03SA and 03Q5), and the l-primary dévissage. -/
theorem curveCohomologyStatements_of_biproduct_extensionByZero_of_closedPoints
    {X Z X' Y : Scheme.{u}} (i' : Z ⟶ X) (j : X' ⟶ X) (i : Y ⟶ X)
    [IsClosedImmersion i'] [IsOpenImmersion j] [IsAffine Z]
    {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (l p : ℕ)
    {constructible : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} → Prop}
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hij : Set.range j.base = (Set.range i'.base)ᶜ)
    (hclosed : ∀ z : Z, IsClosed ({z} : Set Z))
    (hsep : ∀ z : Z, IsSepClosed (Z.residueField z))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : Finite (Sheaf.H.{u + 1}
      ((etaleAbelianDirectImage.{u, u + 1} i').obj
        ((etaleAbelianInverseImage.{u, u + 1} i').obj F)) 0))
    (hrestr : ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} i
      ((etaleAbelianDirectImage.{u, u + 1} i').obj
        ((etaleAbelianInverseImage.{u, u + 1} i').obj F)) q))
    (hconstructible :
      ∀ S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        S.ShortExact → constructible S.X₂ → constructible S.X₁ ∧ constructible S.X₃)
    (n : ℕ) (G : Fin n → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : (⨁ G) ≅ (extensionByZero.{u, u + 1} j).obj ((etaleRestriction.{u, u + 1} j).obj F))
    (hG : ∀ a, CurveCohomologyStatements.{u, u + 1, u + 1} i π l p constructible (G a)) :
    CurveCohomologyStatements.{u, u + 1, u + 1} i π l p constructible F :=
  curveCohomologyStatements_of_biproduct_extensionByZero.{u, u + 1, u + 1} i' j i π l p hij F
    (fun q hq => subsingleton_etaleCohomology_directImage_of_closed_points.{u} i' hclosed hsep
      ((etaleAbelianInverseImage.{u, u + 1} i').obj F) q hq)
    hfinite hrestr hconstructible n G e hG

end Reduction

end Stacks.EtaleCohomology

end
