module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.ConnectedNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Stein factorization of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The *Stein factorization*
of `f` is the factorization `X ⟶ Y' ⟶ Y` through the normalization `Y'` of `Y` in `X`, which by
Stacks 0A0Q is the relative spectrum `\underline{Spec}_Y(f_* 𝒪_X)`.  Stacks 0A19 lists five
properties of that factorization for a universally closed, quasi-separated `f`, and Stacks 0A1B
sharpens them when `f` is proper and `Y` is locally Noetherian.

Both tags are stated here for the factorization that
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` constructs:
`AlgebraicGeometry.Space.normalizationIn` is `Y'`, its structure morphism is `π`, and
`AlgebraicGeometry.Space.toNormalizationIn` is `f'`.  Clause (5) of each tag — that `Y'` is the
normalization of `Y` in `X` — therefore holds by construction, and is recorded in the form the
library gives that notion, `AlgebraicGeometry.Space.IsRelativeNormalization`.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_toNormalizationIn`,
  `AlgebraicGeometry.Space.isQuasiCompact_toNormalizationIn` and
  `AlgebraicGeometry.Space.isQuasiSeparated_toNormalizationIn`: three of the four assertions of
  clause (1) of Stacks 0A19 — `f'` is universally closed, quasi-compact and quasi-separated.
* `AlgebraicGeometry.Space.isSurjective_of_isRelativeNormalization` and
  `AlgebraicGeometry.Space.isSurjective_toNormalizationIn`: the fourth assertion of clause (1)
  of Stacks 0A19 — `f'` is surjective — for any factorization with the characterizing property
  of Stacks 0823, and for the factorization of Stacks 0822.
* `AlgebraicGeometry.Space.isIntegralHom_normalizationIn`: clause (2) of Stacks 0A19, that `π`
  is integral.
* `AlgebraicGeometry.Space.isRelativeNormalization_steinFactorization`: clause (5) of
  Stacks 0A19, that `Y'` is the normalization of `Y` in `X`.
* `AlgebraicGeometry.Space.steinFactorization_universallyClosed`: the conjunction of all five
  clauses of Stacks 0A19, for consumers wanting them in one place.  Clauses (3) and (4) are not
  proved in this library and appear in it as named hypotheses, so it records no tag; the clauses
  that are proved are stated in the results listed above.
* `AlgebraicGeometry.Space.isProper_toNormalizationIn`: the properness half of clause (1) of
  Stacks 0A1B.
* All five clauses of Stacks 0A1B are proved for the normalization
  `AlgebraicGeometry.Space.normalizationInQcqs` instead, beginning with
  `AlgebraicGeometry.Space.isProper_and_connectedPullback_toNormalizationInQcqs`.

## Implementation notes

**What is proved, and from what.**  The three permanence assertions about `f'` are the source's
own argument, read off the cancellation lemmas.  The structure morphism `π` of the
normalization is affine by the typing of `AlgebraicGeometry.Space.normalizationIn`, which lands
in `AlgebraicGeometry.Space.AffineOver`; hence `π` is separated (Stacks 03KM, proved as
`AlgebraicGeometry.Space.isSeparated_of_isAffineHom`) and so quasi-separated (Stacks 03KK).
With `f = f' ≫ π` that gives

* `f'` universally closed, by Stacks 04NX part (1), because `f` is and `π` is separated;
* `f'` quasi-compact, by Stacks 03KS, because `f` is quasi-compact — which is Stacks 04XW
  applied to the universally closed `f`, the step with which the source opens — and `π` is
  quasi-separated;
* `f'` quasi-separated, by Stacks 03KR, because `f` is; no hypothesis on `π` is needed;
* `f'` proper, by Stacks 04NX part (2), because `f` is and `π` is separated.  This is the
  properness half of clause (1) of Stacks 0A1B.

Integrality of `π` is clause (2), and it is clause (1) of Stacks 0823 for the same
factorization, proved as
`AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn`; the same theorem
supplies clause (5).  Clause (4) is the second assertion of Stacks 0A0Q, proved as
`AlgebraicGeometry.Space.isIso_relativeSpecDirectImageToNormalizationIn`, which carries the
integrality of `f_* 𝒪_X` — the *first* assertion of that tag — as a hypothesis.

Surjectivity of `f'` is the remaining assertion of clause (1), and it is proved from the
characterization of Stacks 0823 rather than by the source's computation on an affine chart.
Let `Z ⊂ Y'` be the scheme-theoretic image of `f'` (Stacks 082X).  It is a closed subspace, so
`Z ⟶ Y'` is integral (Stacks 081Y) and hence so is `Z ⟶ Y`, and `f` factors through it; the
universal property therefore produces a morphism `Y' ⟶ Z` which, by the uniqueness clause
applied at `Y'` itself, is a section of the inclusion.  A subfunctor inclusion is a
monomorphism, so the inclusion is an isomorphism, and the points of `Z` are the closure of the
image of `|f'|` by Stacks 082Z part (4), `f'` being quasi-compact.  That image is closed
because `f'` is universally closed, so it is all of `|Y'|`.

**What is carried, clause by clause.**  Beyond the structures that the normalization needs in
order to exist at all (`E` and `C` of Stacks 081V, `hqc` of Stacks 03M9, `hqc'` of Stacks 0820,
`hid` of Stacks 03G8) and the inputs of Stacks 0823 (`P`, `D`, `hloc`), the following are
hypotheses rather than conclusions:

* `hint`, the integrality of `f_* 𝒪_X`.  This is the first assertion of Stacks 0A0Q, whose
  proof is not in this library; see the section "What is not proved" of
  `StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral`.  It is what
  clause (4) rests on.
* `hstr`, clause (3), invertibility of the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` of Stacks 03G8.
  The source deduces it on an affine `Y = Spec(R)` from `Y' = Spec(A)` with `A = Γ(X, 𝒪_X)`,
  which needs the identification of the sections of `f_* 𝒪_X` over an affine étale chart of `Y`
  with the global regular functions on the base change of `X` to that chart; the implementation
  notes of `StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStructureSheafIntegral` record that
  identification as the missing bridge on exactly this path.

**What is not addressed at all.**  The closing sentence of Stacks 0A19, that formation of the
factorization commutes with flat base change, is not stated here.

## References

* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (E : AffineAlgebraAntiEquivalence B S hS) (C : BaseChangeCompatibility B S hS E)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqc' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS X).obj ≅ unitAlgebra B S hS X)

/-! ### The structure morphism of the normalization -/

/-- The structure morphism `π : Y' ⟶ Y` of the normalization of `Y` in `X` is separated: it is
affine by the typing of `AlgebraicGeometry.Space.normalizationIn`, and an affine morphism of
algebraic spaces is separated (**Stacks 03KM**). -/
theorem isSeparated_normalizationIn :
    IsSeparated B S hS (normalizationIn B S hS E f hqc').obj.hom.hom :=
  isSeparated_of_isAffineHom B S hS _ (normalizationIn B S hS E f hqc').obj.left.2 Y.2
    (normalizationIn B S hS E f hqc').property

/-- The structure morphism `π : Y' ⟶ Y` of the normalization of `Y` in `X` is quasi-separated,
being separated (**Stacks 03KK**). -/
theorem isQuasiSeparated_normalizationIn :
    IsQuasiSeparated B S hS (normalizationIn B S hS E f hqc').obj.hom.hom :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_normalizationIn B S hS E f hqc')

/-- The factorization `f = f' ≫ π` of Stacks 0822, read on the underlying morphisms of
presheaves. -/
theorem toNormalizationIn_comp_hom :
    (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom ≫
        (normalizationIn B S hS E f hqc').obj.hom.hom = f.hom :=
  congrArg (fun k => k.hom) (toNormalizationIn_factorization B S hS E C f hqc hqc' hid)

/-! ### Clause (1) of Stacks 0A19 -/

/-- **Stacks 0A19, clause (1): `f'` is universally closed.**  By Stacks 04NX part (1), since the
composite `f = f' ≫ π` is universally closed and `π` is separated. -/
@[stacks 0A19 "part (1): the morphism to the normalization is universally closed"]
theorem universallyClosed_toNormalizationIn
    (hfuc : UniversallyClosed B S hS f.hom) :
    UniversallyClosed B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom := by
  refine universallyClosed_of_comp_of_isSeparated B S hS X.2
    (normalizationIn B S hS E f hqc').obj.left.2 Y.2 _ _ ?_
    (isSeparated_normalizationIn B S hS E f hqc')
  rwa [toNormalizationIn_comp_hom B S hS E C f hqc hqc' hid]

/-- **Stacks 0A19, clause (1): `f'` is quasi-compact.**  By Stacks 03KS, since the composite
`f = f' ≫ π` is quasi-compact — a universally closed morphism is quasi-compact by
Stacks 04XW — and `π` is quasi-separated. -/
@[stacks 0A19 "part (1): the morphism to the normalization is quasi-compact"]
theorem isQuasiCompact_toNormalizationIn
    (hfuc : UniversallyClosed B S hS f.hom) :
    IsQuasiCompact B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom := by
  refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS _ _ X.2 Y.2 ?_
    (isQuasiSeparated_normalizationIn B S hS E f hqc')
  rw [toNormalizationIn_comp_hom B S hS E C f hqc hqc' hid]
  exact isQuasiCompact_of_universallyClosed B S hS X.2 Y.2 f.hom hfuc

/-- **Stacks 0A19, clause (1): `f'` is quasi-separated.**  By Stacks 03KR, since the composite
`f = f' ≫ π` is quasi-separated.  Nothing is required of `π`. -/
@[stacks 0A19 "part (1): the morphism to the normalization is quasi-separated"]
theorem isQuasiSeparated_toNormalizationIn
    (hfqs : IsQuasiSeparated B S hS f.hom) :
    IsQuasiSeparated B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom := by
  refine isQuasiSeparated_of_comp B S hS
    (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom
    (normalizationIn B S hS E f hqc').obj.hom.hom ?_
  rwa [toNormalizationIn_comp_hom B S hS E C f hqc hqc' hid]

attribute [local instance] pointTopology

/-- A quasi-compact and universally closed morphism to the normalization of `V` in `U` is
surjective: its scheme-theoretic image is a closed subspace through which `U ⟶ V` factors
integrally, so the characterization of Stacks 0823 retracts the normalization onto that image,
whose points are therefore all of it and are the closure of the image of the point map. -/
theorem isSurjective_of_isRelativeNormalization
    {U V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : U ⟶ V} {ν : V' ⟶ V} {g' : U ⟶ V'}
    (h : IsRelativeNormalization B S hS g ν g') (hU : IsAlgebraicSpace B S hS U)
    (hV' : IsAlgebraicSpace B S hS V') (hqcg : IsQuasiCompact B S hS g')
    (hucg : UniversallyClosed B S hS g') :
    IsSurjective B S hS g' := by
  set Z := schemeTheoreticImageSubfunctor B S hS g'
  have hZcl : IsClosedSubspace B S hS Z :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS g' hV'
  have hfac : toSchemeTheoreticImage B S hS g' ≫ Z.ι = g' :=
    toSchemeTheoreticImage_ι B S hS g'
  -- the image is a closed subspace, so an integral factorization of `g`
  have hZint : IsIntegralHom B S hS (Z.ι ≫ ν) :=
    isIntegralHom_comp B S hS
      (isIntegralHom_of_isClosedImmersion B S hS Z.ι hZcl.2) h.isIntegralHom
  obtain ⟨k, ⟨hkg, hkν⟩, -⟩ := h.existsUnique_lift hZcl.1 (Z.ι ≫ ν) hZint
    (toSchemeTheoreticImage B S hS g') (by rw [← Category.assoc, hfac, h.fac])
  -- the comparison morphism is a section of the inclusion, by uniqueness at `V'` itself
  have hsection : k ≫ Z.ι = 𝟙 V' := by
    refine (h.existsUnique_lift hV' ν h.isIntegralHom g' h.fac).unique ⟨?_, ?_⟩
      ⟨Category.comp_id g', Category.id_comp ν⟩
    · rw [← Category.assoc, hkg, hfac]
    · rw [Category.assoc]; exact hkν
  have hretract : Z.ι ≫ k = 𝟙 Z.toFunctor := by
    refine (cancel_mono Z.ι).1 ?_
    rw [Category.assoc, hsection, Category.comp_id, Category.id_comp]
  have : IsIso Z.ι := ⟨k, hretract, hsection⟩
  -- hence the image of the point map is dense, and it is closed because `g'` is closed
  have hdense : closure (Set.range (pointsMap B S hS U g')) = Set.univ := by
    rw [← range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS g' hU hV'
      hqcg]
    exact Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS Z.ι)
  have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS U g')) :=
    (isClosed_of_universallyClosed B S hS hV' g' hucg).isClosed_range
  exact Set.range_eq_univ.1 (by rw [← hclosed.closure_eq, hdense])

include hqc hid in
/-- **Stacks 0A19, clause (1): `f'` is surjective.**  The scheme-theoretic image of `f'` inside
the normalization `Y'` of `Y` in `X` is a closed subspace, hence integral over `Y`, through
which `f` factors; the characterization of Stacks 0823 therefore retracts `Y'` onto it, and
`f'` has closed image because it is universally closed. -/
@[stacks 0A19 "part (1): the morphism to the normalization is surjective"]
theorem isSurjective_toNormalizationIn
    (P : RelativeSpecUniversalProperty B S hS E C) (D : IntegralAlgebraDictionary B S hS E)
    (hloc : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegralLocalOnAffineCharts)
    (hfuc : UniversallyClosed B S hS f.hom) :
    IsSurjective B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom :=
  isSurjective_of_isRelativeNormalization B S hS
    (isRelativeNormalization_toNormalizationIn P D f hqc hqc' hid hloc) X.2
    (normalizationIn B S hS E f hqc').obj.left.2
    (isQuasiCompact_toNormalizationIn B S hS E C f hqc hqc' hid hfuc)
    (universallyClosed_toNormalizationIn B S hS E C f hqc hqc' hid hfuc)

/-! ### Clause (2) of Stacks 0A19 -/

include hqc hid in
/-- **Stacks 0A19, clause (2): `π` is integral.**  This is clause (1) of Stacks 0823 for the
same factorization, proved as
`AlgebraicGeometry.Space.isRelativeNormalization_toNormalizationIn`, and it carries that
theorem's inputs: the universal property `P` of the relative spectrum, the dictionary `D` of
Stacks 03ZP between integral morphisms affine over `Y` and integral algebras, and the clause
`hloc` of Stacks 0820 that a locally integral section over an affine chart is integral. -/
@[stacks 0A19 "part (2): the normalization morphism is integral"]
theorem isIntegralHom_normalizationIn
    (P : RelativeSpecUniversalProperty B S hS E C) (D : IntegralAlgebraDictionary B S hS E)
    (hloc : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegralLocalOnAffineCharts) :
    IsIntegralHom B S hS (normalizationIn B S hS E f hqc').obj.hom.hom :=
  (isRelativeNormalization_toNormalizationIn P D f hqc hqc' hid hloc).isIntegralHom

/-! ### Clause (5) of Stacks 0A19 -/

include hqc hid in
/-- **Stacks 0A19, clause (5): `Y'` is the normalization of `Y` in `X`.**  The factorization
`f = f' ≫ π` has the two properties of Stacks 0823 which characterize the normalization:
`π` is integral, and every factorization of `f` through an integral morphism of algebraic
spaces to `Y` receives a unique compatible morphism from `Y'`. -/
@[stacks 0A19 "part (5): the intermediate space is the normalization of Y in X"]
theorem isRelativeNormalization_steinFactorization
    (P : RelativeSpecUniversalProperty B S hS E C) (D : IntegralAlgebraDictionary B S hS E)
    (hloc : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegralLocalOnAffineCharts) :
    IsRelativeNormalization B S hS f.hom
      (normalizationIn B S hS E f hqc').obj.hom.hom
      (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom :=
  isRelativeNormalization_toNormalizationIn P D f hqc hqc' hid hloc

/-! ### All five clauses of Stacks 0A19 -/

/-- **Stacks 0A19.**  Let `f : X ⟶ Y` be a universally closed and quasi-separated morphism of
algebraic spaces over `S`.  Take `Y'` to be the normalization of `Y` in `X` and
`f = f' ≫ π` the factorization of Stacks 0822.  Then, in the order of the source:

1. `f'` is universally closed, quasi-compact, quasi-separated and surjective;
2. `π : Y' ⟶ Y` is integral;
3. the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` of Stacks 03G8 is invertible;
4. `Y' = \underline{Spec}_Y(f_* 𝒪_X)`, in the form that the morphism of relative spectra
   induced by the inclusion `𝒪' ⊂ f_* 𝒪_X` is invertible;
5. `Y'` is the normalization of `Y` in `X`, in the sense of
   `AlgebraicGeometry.Space.IsRelativeNormalization`.

The conclusion also records the factorization equation itself.

**Two of the five clauses are hypotheses rather than conclusions**, namely the surjectivity
`hsurj` in clause (1) and clause (3) as `hstr`; and clause (4) rests on the hypothesis `hint`,
the first assertion of Stacks 0A0Q.  The module documentation says for each what its proof
needs and why it is not available here.  Everything else is proved: clause (2) and clause (5)
from Stacks 0823, and the three permanence assertions of clause (1) from Stacks 04NX part (1),
Stacks 03KS and Stacks 03KR with Stacks 04XW.

The closing sentence of the source, that formation of the factorization commutes with flat base
change, is not part of this statement.

The hypothesis `hsurj` has since become redundant: surjectivity of `f'` is
`AlgebraicGeometry.Space.isSurjective_toNormalizationIn`, which is where clause (1) of the tag
is recorded.  This conjunction is retained for the convenience of its consumers and records no
tag of its own. -/
theorem steinFactorization_universallyClosed
    (P : RelativeSpecUniversalProperty B S hS E C) (D : IntegralAlgebraDictionary B S hS E)
    (hloc : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegralLocalOnAffineCharts)
    (hfuc : UniversallyClosed B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hint : (pushforwardAlgebra B S hS (Over.mk f)).IsIntegral)
    (hsurj : IsSurjective B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom)
    (hstr : IsIso (smallEtaleRingedToposHom B S hS
      (toNormalizationIn B S hS E C f hqc hqc' hid).left).fSharp) :
    (toNormalizationIn B S hS E C f hqc hqc' hid).left ≫
          (normalizationIn B S hS E f hqc').obj.hom = f ∧
      UniversallyClosed B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom ∧
      IsQuasiCompact B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom ∧
      IsQuasiSeparated B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom ∧
      IsSurjective B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom ∧
      IsIntegralHom B S hS (normalizationIn B S hS E f hqc').obj.hom.hom ∧
      IsIso (smallEtaleRingedToposHom B S hS
        (toNormalizationIn B S hS E C f hqc hqc' hid).left).fSharp ∧
      IsIso (relativeSpecDirectImageToNormalizationIn B S hS E f hqc hqc') ∧
      IsRelativeNormalization B S hS f.hom
        (normalizationIn B S hS E f hqc').obj.hom.hom
        (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom :=
  ⟨toNormalizationIn_factorization B S hS E C f hqc hqc' hid,
    universallyClosed_toNormalizationIn B S hS E C f hqc hqc' hid hfuc,
    isQuasiCompact_toNormalizationIn B S hS E C f hqc hqc' hid hfuc,
    isQuasiSeparated_toNormalizationIn B S hS E C f hqc hqc' hid hfqs,
    hsurj,
    isIntegralHom_normalizationIn B S hS E C f hqc hqc' hid P D hloc,
    hstr,
    isIso_relativeSpecDirectImageToNormalizationIn B S hS E f hqc hqc' hint,
    isRelativeNormalization_toNormalizationIn P D f hqc hqc' hid hloc⟩

/-! ### Clause (1) of Stacks 0A1B: properness -/

/-- **Stacks 0A1B, clause (1): `f'` is proper.**  By Stacks 04NX part (2), since the composite
`f = f' ≫ π` is proper and `π` is separated. -/
@[stacks 0A1B "part (1): the morphism to the normalization is proper"]
theorem isProper_toNormalizationIn (hf : IsProper B S hS f.hom) :
    IsProper B S hS (toNormalizationIn B S hS E C f hqc hqc' hid).left.hom := by
  refine isProper_of_comp_of_isSeparated B S hS X.2
    (normalizationIn B S hS E f hqc').obj.left.2 Y.2 _ _ ?_
    (isSeparated_normalizationIn B S hS E f hqc')
  rwa [toNormalizationIn_comp_hom B S hS E C f hqc hqc' hid]

end AlgebraicGeometry.Space

end
