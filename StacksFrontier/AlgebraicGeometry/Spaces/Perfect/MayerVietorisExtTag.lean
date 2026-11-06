module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExt
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag

/-!
# Stacks 08H9, with nothing assumed: the registration of the tag

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V` be its intersection.  Write `(-)|_Y` for restriction of modules
along `j_Y : Y ⟶ X` and `j_{Y!}` for a left adjoint of it, extension by zero.  Then for all
objects `E` and `F` of `D(𝒪_X)` the Mayer–Vietoris sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

is exact.  This is **Stacks 08H9**.

The maps of that sequence are not arbitrary, and the statement registered here does not leave
them arbitrary: the first is restriction along `j_U` and along `j_V`, the second the difference of
the two restrictions to `P`, and the third the connecting homomorphism of the Mayer–Vietoris
distinguished triangle of part (2) of Stacks 08GV.  They are constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisExtRestriction`.

## Main results

* `AlgebraicGeometry.Space.mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek` is
  **Stacks 08H9** with nothing at all assumed beyond the square and with every map of the
  sequence named.  The restriction map is the pair of the actions
  `CategoryTheory.ShiftedHom.map` of the two derived restrictions; the second map is
  `AlgebraicGeometry.Space.edsDerivedHomRestrictionOpen` minus
  `AlgebraicGeometry.Space.edsDerivedHomRestrictionEtale`, and the statement records that each of
  those two carries the restriction of a morphism of `D(𝒪_X)` to the restriction of that morphism
  to `P`; the connecting map is `AlgebraicGeometry.Space.edsDerivedHomBoundary` at the connecting
  morphism `δ` of the Mayer–Vietoris triangle, which the statement binds together with the
  triangle it completes.  **This is the one library registration of Tag 08H9.**
* `AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek`
  has the same three terms but quantifies over the three maps without describing them.  It is
  **untagged**: an exact sequence of those groups whose maps are arbitrary additive maps is not
  the Mayer–Vietoris sequence, so the statement is strictly weaker than the tag.  Nothing in the
  library uses it; it is kept as a true weakening of the carrier.
* `AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_eds` is that same
  weaker conclusion for an arbitrary choice of extension-by-zero data, and is **untagged** as
  well.

## Implementation notes

The two maps out of the intersection cannot be left arbitrary, and are not: they are induced by
`AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison`, the comparisons attached to the two
factorizations of the morphism from the intersection.  Their alternating composite with the two
counits vanishes by `AlgebraicGeometry.Space.zero_edsShriekMayerVietoris`, and the short complex
built from them is `CategoryTheory.ShortComplex.mayerVietoris`, which is by definition the short
complex part (1) of Stacks 08GV speaks about; the compatibility
`AlgebraicGeometry.Space.edsShriekOpenComparison_comp_counit` of each comparison with the counits
is what makes the map it induces on homomorphism groups a restriction map.

The carrier has the elementary distinguished square as its only binder.  The extension-by-zero
data is not quantified over but is `AlgebraicGeometry.Space.etaleModuleLowerShriek` with its
adjunctions `AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`; its exactness, Stacks
03DJ, is the theorem `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` with
its two companions rather than an instance argument, and the two sheafification hypotheses of the
ambient site are discharged by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat`.

### Where `@[stacks 08H9]` sits

Exactly one declaration of the library carries the tag: the carrier here.

## References

* [Stacks Project, Tag 08H9](https://stacks.math.columbia.edu/tag/08H9)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section Data

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

include adjU adjV adjP in
/-- **The Mayer–Vietoris sequence of Tag 08H9, for a quantified extension by zero.**  Let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, let `P = U ×_X V`, write `(-)|_Y` for restriction of modules along `j_Y : Y ⟶ X` and let
`j_{Y!}` be a left adjoint of it, extension by zero, with counit `j_{Y!}(F|_Y) ⟶ F`.  Then for
all objects `E` and `F` of `D(𝒪_X)` there are restriction, difference and connecting
homomorphisms making the Mayer–Vietoris sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

exact at each of its three kinds of spot and in every integer degree, the homomorphism groups of
the restrictions being taken in the derived categories of `U`, of `V` and of `P`.

The short exact sequence of part (1) of Stacks 08GV, which
`AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_square` takes as an
input, is supplied by `AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris` at the two
comparisons of the square.

This is **not** the registration of Tag 08H9: it quantifies over the three extension-by-zero
functors with their adjunctions and their exactness instances, and takes the ambient site's two
sheafification hypotheses as instance arguments, none of which the source assumes.  The
registered carrier is
`AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek`
below, which has the very same conclusion with none of that data and no instance argument at all.
This form is kept because it is the shape every consumer inside the development uses, and because
it says the sequence does not depend on the choice of extension by zero. -/
theorem exists_mayerVietoris_derivedHom_longExactSequence_of_eds
    (E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (restriction : ∀ n : ℤ, (E ⟶ F⟦n⟧) →+
          (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)))
      (difference : ∀ n : ℤ,
        (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)) →+
          ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧))
      (boundary : ∀ n : ℤ,
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) →+
          (E ⟶ F⟦n + 1⟧)),
      ∀ n : ℤ, Function.Exact (restriction n) (difference n) ∧
        Function.Exact (difference n) (boundary n) ∧
        Function.Exact (boundary n) (restriction (n + 1)) :=
  exists_mayerVietoris_derivedHom_longExactSequence_of_square B S hS hsq adjU adjV adjP
    (edsShriekOpenComparison B S hS hsq adjU adjP)
    (edsShriekEtaleComparison B S hS hsq adjV adjP)
    (zero_edsShriekMayerVietoris B S hS hsq adjU adjV adjP)
    (shortExact_edsShriekMayerVietoris B S hS hsq adjU adjV adjP) E F

end Data

section LowerShriek

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The Mayer–Vietoris sequence of Stacks 08H9 with its three maps quantified over.**  Let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V` and write `(-)|_Y`
for restriction of modules along `j_Y : Y ⟶ X`.  Then for all objects `E` and `F` of `D(𝒪_X)`
there are restriction, difference and connecting homomorphisms making the Mayer–Vietoris
sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

exact at each of its three kinds of spot and in every integer degree, the homomorphism groups of
the restrictions being taken in the derived categories of `U`, of `V` and of `P`.

This is `AlgebraicGeometry.Space.exists_mayerVietoris_derivedHom_longExactSequence_of_eds` at
the extensions by zero the library constructs,
`AlgebraicGeometry.Space.etaleModuleLowerShriek` with its adjunctions
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`.  Nothing beyond the square is
assumed: the extension-by-zero data is no longer quantified over, its exactness is the theorem
`AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` (Stacks 03DJ) with its
two companions, and the two sheafification hypotheses of the ambient site are discharged by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat`.

**This is not the registration of Tag 08H9**, and it is deliberately untagged: its three maps
are quantified over without being described, so it is satisfied by exact sequences of these
groups that are not the Mayer–Vietoris sequence, which is strictly weaker than the tag.  The
registered carrier is
`AlgebraicGeometry.Space.mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek` below,
whose first map is the pair of the two derived restrictions, whose second is the difference of
the two restrictions to the intersection and whose connecting map is that of the Mayer–Vietoris
triangle.  Nothing in the library uses the statement here; it is kept because it is a true
weakening of the carrier and records the shape in which the sequence was first obtained. -/
theorem exists_mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek
    (E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ (restriction : ∀ n : ℤ, (E ⟶ F⟦n⟧) →+
          (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)))
      (difference : ∀ n : ℤ,
        (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
            ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
              ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)) →+
          ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧))
      (boundary : ∀ n : ℤ,
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
            ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) →+
          (E ⟶ F⟦n + 1⟧)),
      ∀ n : ℤ, Function.Exact (restriction n) (difference n) ∧
        Function.Exact (difference n) (boundary n) ∧
        Function.Exact (boundary n) (restriction (n + 1)) :=
  exists_mayerVietoris_derivedHom_longExactSequence_of_eds B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)) E F

/-- **Stacks 08H9, with nothing assumed and with every map of the sequence named.**  Let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, let `P = U ×_X V` and write `(-)|_Y` for restriction of modules along `j_Y : Y ⟶ X`.  Then
for all objects `E` and `F` of `D(𝒪_X)` the Mayer–Vietoris sequence

`⋯ ⟶ Ext⁻¹(E|_P, F|_P) ⟶ Hom(E, F) ⟶ Hom(E|_U, F|_U) ⊕ Hom(E|_V, F|_V) ⟶ Hom(E|_P, F|_P) ⟶ ⋯`

is exact at each of its three kinds of spot and in every integer degree, the homomorphism groups
of the restrictions being taken in the derived categories of `U`, of `V` and of `P`.

Every map of the sequence is named; none of the three is quantified over.

* **The restriction map is the restriction map.**  In degree `n` it carries `x : E ⟶ F⟦n⟧` to the
  pair of the actions `CategoryTheory.ShiftedHom.map` of the two derived restrictions on it, so
  neither a choice nor an extension by zero enters it.
* **The second map is the difference of the two restrictions to the intersection.**  It is
  `AlgebraicGeometry.Space.edsDerivedHomRestrictionOpen` on the first summand minus
  `AlgebraicGeometry.Space.edsDerivedHomRestrictionEtale` on the second; each of those is the map
  induced by the comparison of the square attached to the corresponding factorization of `j_P`,
  and the two clauses below record that each carries the restriction of a morphism of `D(𝒪_X)` to
  the restriction of that morphism to `P`.
* **The connecting homomorphism is the one of the Mayer–Vietoris triangle.**  The morphism `δ` is
  bound as the third map of the distinguished triangle of part (2) of Stacks 08GV, read at the
  composites of the derived functors, and `AlgebraicGeometry.Space.edsDerivedHomBoundary` is
  composition with that same `δ`, as the third clause below records.

Nothing beyond the square is assumed: the extension-by-zero data is not quantified over but is
`AlgebraicGeometry.Space.etaleModuleLowerShriek` with its adjunctions
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`, its exactness is the theorem
`AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` (Stacks 03DJ) with its two
companions, and the two sheafification hypotheses of the ambient site are discharged by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat`.

This is the one library registration of Tag 08H9, and the elementary distinguished square is its
only binder. -/
@[stacks 08H9 "the whole tag, and its one library registration: the Mayer-Vietoris sequence of \
an elementary distinguished square is exact at each of its three kinds of spot and in every \
integer degree, its first map being the pair of the two derived restrictions of a shifted \
morphism, its second the difference of the two restrictions to the intersection, and its \
connecting map that of the triangle of 08GV part (2); the square is the only binder"]
theorem mayerVietoris_derivedHom_longExactSequence_of_eds_lowerShriek
    (E F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ : E ⟶ ((etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))⟦(1 : ℤ)⟧,
      Triangle.mk
          (biprod.lift
            ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq))
                      (etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
                        (isEtale_edsInterHom B S hS hsq))).inv.app E ≫
              (NatTrans.mapDerivedCategory
                (edsShriekOpenComparison B S hS hsq
                    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
                      (isEtale_edsOpenHom B S hS hsq))
                          (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                            (isEtale_edsInterHom B S hS hsq)))).app E ≫
              (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq))
                    (etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
                      (isEtale_edsOpenHom B S hS hsq))).hom.app E)
            (-((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq))
                      (etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
                        (isEtale_edsInterHom B S hS hsq))).inv.app E ≫
              (NatTrans.mapDerivedCategory
                (edsShriekEtaleComparison B S hS hsq
                    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
                      (isEtale_edsEtaleHom B S hS hsq))
                          (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                            (isEtale_edsInterHom B S hS hsq)))).app E ≫
              (Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
                    (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
                      (isEtale_edsEtaleHom B S hS hsq))).hom.app E)))
          (biprod.desc
            ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq))
                      (etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
                        (isEtale_edsOpenHom B S hS hsq))).inv.app E ≫
              (NatTrans.mapDerivedCategory
                  (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
                    (isEtale_edsOpenHom B S hS hsq)).counit).app E ≫
              (Functor.mapDerivedCategoryIdIso _).hom.app E)
            ((Functor.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS
                  (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq))
                      (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
                        (isEtale_edsEtaleHom B S hS hsq))).inv.app E ≫
              (NatTrans.mapDerivedCategory
                  (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
                    (isEtale_edsEtaleHom B S hS hsq)).counit).app E ≫
              (Functor.mapDerivedCategoryIdIso _).hom.app E)) δ ∈
        distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) ∧
      (∀ (n : ℤ) (x : E ⟶ F⟦n⟧),
        edsDerivedHomRestrictionOpen B S hS hsq E F n
            (ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
              (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory) =
          ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory) ∧
      (∀ (n : ℤ) (x : E ⟶ F⟦n⟧),
        edsDerivedHomRestrictionEtale B S hS hsq E F n
            (ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory) =
          ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
            (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory) ∧
      (∀ (n : ℤ) (z : ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E ⟶
          ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧)),
        edsDerivedHomBoundary B S hS hsq E F δ n z =
          δ ≫ (((etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
                  (isEtale_edsInterHom B S hS hsq)).shiftedHomMapDerivedCategoryEquiv
                ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
                  (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E) F n).symm
              z)⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' (DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
              n 1 (n + 1) rfl).inv.app F) ∧
      ∀ n : ℤ,
        Function.Exact
            (fun x : E ⟶ F⟦n⟧ =>
              (ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory,
                ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                  (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory))
            (fun w => edsDerivedHomRestrictionOpen B S hS hsq E F n w.1 -
              edsDerivedHomRestrictionEtale B S hS hsq E F n w.2) ∧
          Function.Exact
            (fun w : ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E ⟶
                ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                    (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) ×
                ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                    (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E ⟶
                    ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)⟦n⟧) =>
              edsDerivedHomRestrictionOpen B S hS hsq E F n w.1 -
                edsDerivedHomRestrictionEtale B S hS hsq E F n w.2)
            (edsDerivedHomBoundary B S hS hsq E F δ n) ∧
          Function.Exact (edsDerivedHomBoundary B S hS hsq E F δ n)
            (fun x : E ⟶ F⟦n + 1⟧ =>
              (ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
                (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory,
                ShiftedHom.map x (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
                  (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory)) := by
  have h := exists_mem_distTriang_edsDerivedShriekMayerVietoris B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)) E
  obtain ⟨δ, hδ⟩ := h
  refine ⟨δ, hδ, fun n x => edsDerivedHomRestrictionOpen_map B S hS hsq E F n x,
    fun n x => edsDerivedHomRestrictionEtale_map B S hS hsq E F n x,
    fun n z => edsDerivedHomBoundary_apply B S hS hsq E F δ n z,
    fun n => ?_⟩
  refine mayerVietoris_shiftedHom_longExactSequence_restrictions _ _ _ _ _ ?_ ?_ E F δ hδ n
  exacts [edsShriekOpenComparison_comp_counit B S hS hsq _ _,
    edsShriekEtaleComparison_comp_counit B S hS hsq _ _]

end LowerShriek

end AlgebraicGeometry.Space

end
