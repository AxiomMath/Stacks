module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.InitialObjectDerivedColimitLargeSite
public import StacksFrontier.Cotangent.ResolutionPointCriterionPolynomialSite
public import StacksFrontier.Cotangent.ThreefoldPolynomialOnTop
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08QV at the sites themselves: `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ`

Let `A → B → C` be ring maps with `C = B[E]` a polynomial algebra over `B`, let `C_{C/B/A}` be
the threefold site of Tag 08QT -- `CommAlgCat.polynomialTowerSite` -- and let `C_{C/B}` be the
site of Tag 08PR for `B → C`, which is `CommAlgCat.polynomialSite B (towerRelativeAlgebra B C)`.
Tag 08QV asserts

`Lπ_!(g₃^{-1}ℱ) = Lπ_{3, !}ℱ = π_{3, !}ℱ`

for every abelian sheaf `ℱ` on `C_{C/B}`. This file proves it **at those two sites themselves**,
rather than at the small models of the restricted sites where
`CommAlgCat.standardLeftDerivedColimitThirdChainIso` reads it.

What was previously available was the same chain read at the small models of the
footnote-restricted sites. Those are statements about different coefficients: the footnote cuts
`C_{C/B/A}` down to the full subcategory of the towers whose two layers of variables have
cardinality at most `κ` and `μ`, and `C_{C/B}` to the augmentations bounded by `μ`, and both the
abelian sheaves and `Lπ_!` change when one passes to a full subcategory. The obstruction to
stating the tag at the sites themselves was not mathematical but a size mismatch -- the degreewise
form of the criterion of Tag 08Q9 was available only for a small site, while the objects of these
sites live in `Type (u + 1)` and their morphisms in `Type u` -- and it is removed by
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge`, the derived-category
form of that criterion, which has no smallness hypothesis.

## Main results

* `CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`: **Tag 08QV, the first
  equality** -- `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ` in `D(Ab)`, at `CommAlgCat.polynomialTowerSite` and
  `CommAlgCat.polynomialSite B (towerRelativeAlgebra B C)`.
* `CommAlgCat.polynomialSiteDerivedColimitThirdIso`: **Tag 08QV, the second equality** --
  `Lπ_{3,!}ℱ = π_{3,!}ℱ` in `D(Ab)`, at `C_{C/B}` itself.
* `CommAlgCat.isPointResolution_towerCosimplicialObject`: the cosimplicial object `U_•` of the
  towers `(P_n → B, P_n[E] → C)` of a resolution `ε` is a point resolution of `C_{C/B/A}`.
* `CommAlgCat.towerThirdCosimplicialConstIso`: `u₃(U_•)` is the constant cosimplicial object of
  `C_{C/B}` with value the identity augmentation `C → C`.
* `CommAlgCat.isInitial_towerIdentityObj`: that identity augmentation is an initial object of
  `C_{C/B}`.

## Implementation notes

**Where the mathematics is.** Nothing is reproved. The hypothesis of Tag 08Q9 is
`CommAlgCat.exists_homotopyEquivalences_towerMor`, which is already proved at `C_{C/B/A}` itself
for every object of that site: it is literally `Stacks.ChaoticSite.IsPointResolution` of `U_•`,
the condition mentioning only the simplicial sets of morphisms and so being available at a site
of any size. Likewise `u₃(U_n)` is identified with the identity augmentation at the unrestricted
site already, by `CommAlgCat.towerThirdObjIso`.

**The coefficient universe.** The objects of both sites live in `Type (u + 1)` and their
morphisms in `Type u`, so abelian presheaves are read at `AddCommGrpCat.{u + 1}`, the smallest
universe in which the index category of a presheaf has colimits of abelian groups. This is the
universe at which `CommAlgCat.polynomialAbelianLowerShriekEvaluationIso` names `π_!` for the
site of Tag 08PR.

**No resolution appears in either statement.** The source's lemma has no resolution in it: `P_•`
is chosen inside its proof. Neither does either statement here -- the type of `Lπ_!(g₃^{-1}ℱ)`
does not mention one -- and the choice is made in the proof of the first equality, where `P_•` is
the standard resolution of Tag 08PM and the two things the criterion asks of it, that its terms
be polynomial algebras and that its augmentation be a trivial Kan fibration, are the two fields
of `CommAlgCat.standardResolution_isResolution`, Tag 08QI.

**Both equalities come from one criterion.** The source says `Lπ_!(g₃^{-1}ℱ)` is computed by the
constant simplicial abelian group `ℱ(C → C)`, which is `Lπ_{3,!}ℱ = π_{3,!}ℱ` by Tag 08QG. That
is the shape here: the criterion of Tag 08Q9 is applied twice, to `U_•` on `C_{C/B/A}` and to the
constant cosimplicial object at the identity augmentation on `C_{C/B}`, and the two Moore
complexes agree because `u₃(U_•)` *is* that constant object. The second equality is then the
underivedness of a lower shriek at a site with an initial object,
`Stacks.ChaoticSite.AbelianValued.totalDerivedColimitSingleIsoOfIsInitial`.

## References

* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QG](https://stacks.math.columbia.edu/tag/08QG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-! ### Enough projectives on the threefold site -/

section Projectives

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- **Abelian presheaves on the threefold site `C_{C/B/A}` have enough projectives**, at the
coefficient universe `u + 1`. The site is not small -- its objects live in `Type (u + 1)` and its
morphisms in `Type u` -- so `Stacks.CategoryHomology.presheafEnoughProjectives` does not apply;
the free diagrams on the objects still exist at `u + 1`, which is what
`Stacks.CategoryHomology.diagramsEnoughProjectives'` needs. -/
instance enoughProjectives_polynomialTowerSitePresheaf :
    EnoughProjectives ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  diagramsEnoughProjectives' _ _

end Projectives

/-! ### The hypothesis of Tag 08Q9 at the threefold site -/

section PointResolution

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)
  (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))

/-- **The cosimplicial object of the towers of a resolution is a point resolution of the site
`C_{C/B/A}`.** Let `ε : P_• ⟶ B` be a resolution of `B` over `A` and let `C = B[E]`. Then every
simplicial set `Mor_{C_{C/B/A}}(U_•, W)` is homotopy equivalent to a singleton, which is the
hypothesis of the criterion of Tag 08Q9.

This is `CommAlgCat.exists_homotopyEquivalences_towerMor` read as
`Stacks.ChaoticSite.IsPointResolution`: the two statements are the same, the condition mentioning
only the simplicial sets of morphisms of the site and so being stated for a category whose
objects and morphisms live in unrelated universes. -/
theorem isPointResolution_towerCosimplicialObject
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.IsPointResolution (towerCosimplicialObject ε eqv hP) :=
  exists_homotopyEquivalences_towerMor ε eqv hP hε

end PointResolution

/-! ### `u₃` of the cosimplicial object is constant at the identity augmentation -/

section Third

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)
  (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))

include eqv in
/-- The identity augmentation `C → C`, as an object of the site `C_{C/B}` -- the opposite of the
category of polynomial `B`-algebras augmented to `C`. -/
def towerIdentityObj : polynomialSite B (towerRelativeAlgebra B C) :=
  op (towerIdentityAugmentation eqv)

include eqv in
/-- **The identity augmentation `C → C` is an initial object of the site `C_{C/B}`.** It is
terminal among polynomial `B`-algebras augmented to `C`, by
`CommAlgCat.polynomialIdentityAugmentation_isTerminal`, and the site is the opposite of that
category. -/
def isInitial_towerIdentityObj : IsInitial (towerIdentityObj eqv) :=
  initialOpOfTerminal (polynomialIdentityAugmentation_isTerminal B (towerRelativeAlgebra B C)
    (isPolynomialAlgebra_towerRelativeAlgebra eqv))

/-- `u₃` of the tower of a degree of a resolution is terminal among polynomial `B`-algebras
augmented to `C`: it is the identity augmentation `C → C` by
`CommAlgCat.towerThirdObjIso`. -/
def isTerminal_towerThirdObj (m : SimplexCategoryᵒᵖ) :
    IsTerminal ((polynomialTowerThirdAugmentations A B C).obj
      ((towerSimplicialOfResolution ε eqv hP).obj m)) :=
  IsTerminal.ofIso
    (polynomialIdentityAugmentation_isTerminal B (towerRelativeAlgebra B C)
      (isPolynomialAlgebra_towerRelativeAlgebra eqv))
    (towerThirdObjIso ε eqv hP m).symm

/-- `u₃` of the cosimplicial object of the towers of a resolution is, in each degree, an initial
object of the site `C_{C/B}`. -/
def isInitial_towerThirdObj (m : SimplexCategory) :
    IsInitial ((towerCosimplicialObject ε eqv hP ⋙ polynomialTowerThird A B C).obj m) :=
  initialOpOfTerminal (isTerminal_towerThirdObj ε eqv hP (op m))

/-- **`u₃(U_•)` is the constant cosimplicial object of `C_{C/B}` with value the identity
augmentation `C → C`.** In each degree it is an initial object there, so the comparison is the
unique morphism out of an initial object and its naturality is automatic. -/
def towerThirdCosimplicialConstIso :
    towerCosimplicialObject ε eqv hP ⋙ polynomialTowerThird A B C ≅
      (Functor.const SimplexCategory).obj (towerIdentityObj eqv) :=
  NatIso.ofComponents
    (fun m => (isInitial_towerThirdObj ε eqv hP m).uniqueUpToIso
      (isInitial_towerIdentityObj eqv))
    fun _ => (isInitial_towerThirdObj ε eqv hP _).hom_ext _ _

end Third

/-! ### Tag 08QV at the sites themselves -/

section Chain

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)

/-- `g₃^{-1}` on abelian presheaves, for the sites themselves: restriction along `u₃`, which is
the inverse image of the morphism of topoi `g₃` of Tag 08QT by
`CommAlgCat.polynomialTowerThirdTopos_inverseImage`. -/
abbrev towerThirdInverseImage (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    ((polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (polynomialTowerThird A B C).op

section Resolution

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))

/-- **The Moore complex of `(g₃^{-1}ℱ)(U_•)` is the Moore complex of `ℱ` on the constant
cosimplicial object at the identity augmentation `C → C`.** Evaluating `g₃^{-1}ℱ` on `U_•` is
evaluating `ℱ` on `u₃(U_•)`, which is that constant cosimplicial object by
`CommAlgCat.towerThirdCosimplicialConstIso`. -/
def cosimplicialMooreComplexTowerThirdIso
    (F : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex' AddCommGrpCat.{u + 1}
          (towerCosimplicialObject ε eqv hP)).obj
        ((towerThirdInverseImage A B C).obj F) ≅
      (Stacks.ChaoticSite.GeneralValued.cosimplicialMooreComplex' AddCommGrpCat.{u + 1}
        ((Functor.const SimplexCategory).obj (towerIdentityObj eqv))).obj F :=
  (alternatingFaceMapComplex AddCommGrpCat.{u + 1}).mapIso
    (Functor.isoWhiskerRight
      (NatIso.op (towerThirdCosimplicialConstIso ε eqv hP)).symm F)


/-- The extended Moore complex version of
`CommAlgCat.cosimplicialMooreComplexTowerThirdIso`: the reindexing to a cochain complex over
`ℤ` is a functor, so it carries the comparison. -/
def mooreCochainComplexTowerThirdIso
    (F : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
          (towerCosimplicialObject ε eqv hP) AddCommGrpCat.{u + 1}).obj
        ((towerThirdInverseImage A B C).obj F) ≅
      (Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
        ((Functor.const SimplexCategory).obj (towerIdentityObj eqv))
        AddCommGrpCat.{u + 1}).obj F :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor AddCommGrpCat.{u + 1}).mapIso
    (cosimplicialMooreComplexTowerThirdIso eqv ε hP F)

end Resolution

/-- **Stacks 08QV, the first equality `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ`, at the sites themselves.**
With notation as in Tag 08QT, suppose `C = B[E]` is a polynomial algebra over `B`. Then

`Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ`

in `D(Ab)`, for every abelian sheaf `ℱ` on `C_{C/B}` -- the abelian presheaves being the abelian
sheaves, the topology being chaotic.

Both sides are the extended Moore complex of `ℱ(u₃(U_•))` for the cosimplicial object `U_•` of the
towers `(P_n → B, P_n[E] → C)`: on the left by the criterion of Tag 08Q9 applied to `U_•` on
`C_{C/B/A}`, on the right by that criterion applied to the constant cosimplicial object at the
identity augmentation `C → C` on `C_{C/B}`, which `u₃(U_•)` is. No hypothesis on a resolution
survives: the resolution of `B` over `A` is the standard one of Tag 08PM, whose terms are
polynomial algebras and whose augmentation is a trivial Kan fibration by Tag 08QI. -/
@[stacks 08QV "the first equality `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ` in `D(Ab)`, at the sites of \
    Tag 08QT and Tag 08PR themselves -- `CommAlgCat.polynomialTowerSite` and \
    `CommAlgCat.polynomialSite B (towerRelativeAlgebra B C)`, not restrictions of them -- with \
    `Lπ_!` and `Lπ_{3,!}` the total left derived functors of the colimits over the index \
    categories of Tag 08PF and the coefficients at the universe `u + 1` of the sites' objects. The \
    second equality `Lπ_{3,!}ℱ = π_{3,!}ℱ` is \
    `CommAlgCat.polynomialSiteDerivedColimitThirdIso`"]
def polynomialTowerDerivedColimitThirdInverseImageIso
    (F : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (totalDerivedColimit' (polynomialTowerSite A B C) AddCommGrpCat.{u + 1}).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single ((polynomialTowerSite A B C)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
            (ComplexShape.up ℤ) 0).obj ((towerThirdInverseImage A B C).obj F))) ≅
      (totalDerivedColimit' (polynomialSite B (towerRelativeAlgebra B C))
          AddCommGrpCat.{u + 1}).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            ((polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
            (ComplexShape.up ℤ) 0).obj F)) :=
  ((Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge
        (towerCosimplicialObject (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom eqv
          (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).isPolynomialAlgebra)
        (isPointResolution_towerCosimplicialObject _ eqv _
          (standardResolution_isResolution.{u, u} A
            (towerBaseAlgebra A B)).trivialKanFibration)).app _).symm ≪≫
    DerivedCategory.Q.mapIso (mooreCochainComplexTowerThirdIso eqv _ _ F) ≪≫
    (Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge
      ((Functor.const SimplexCategory).obj (towerIdentityObj eqv))
      (Stacks.ChaoticSite.isPointResolution_const_of_isInitial
        (isInitial_towerIdentityObj eqv))).app F

/-- **Stacks 08QV, the second equality `Lπ_{3,!}ℱ = π_{3,!}ℱ`, at the site `C_{C/B}` itself.**
With notation as in Tag 08QT, suppose `C = B[E]` is a polynomial algebra over `B`. Then

`Lπ_{3,!}ℱ = π_{3,!}ℱ`

in `D(Ab)`, for every abelian sheaf `ℱ` on `C_{C/B}`: the left side is the complex concentrated in
degree zero on `π_{3,!}ℱ`, the colimit of `ℱ` over the index category of Tag 08PF.

This is where `C = B[E]` is used on `C_{C/B}` itself: it makes the identity augmentation `C → C`
an object of that site, and that object is initial there, so `π_{3,!}` is an evaluation and hence
exact. -/
@[stacks 08QV "the second equality `Lπ_{3,!}ℱ = π_{3,!}ℱ` in `D(Ab)`, at the site `C_{C/B}` of \
    Tag 08PR itself -- `CommAlgCat.polynomialSite B (towerRelativeAlgebra B C)`, not a restriction \
    of it -- with `Lπ_{3,!}` the total left derived functor of the colimit over its index category \
    and `π_{3,!}ℱ` that colimit, as in Tag 08PF. The first equality \
    `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ` is \
    `CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`"]
def polynomialSiteDerivedColimitThirdIso
    (F : (polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (totalDerivedColimit' (polynomialSite B (towerRelativeAlgebra B C))
          AddCommGrpCat.{u + 1}).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            ((polynomialSite B (towerRelativeAlgebra B C))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) 0).obj
          (colimit F)) :=
  Stacks.ChaoticSite.AbelianValued.totalDerivedColimitSingleIsoOfIsInitial
    (isInitial_towerIdentityObj eqv) F

end Chain

end CommAlgCat

end
