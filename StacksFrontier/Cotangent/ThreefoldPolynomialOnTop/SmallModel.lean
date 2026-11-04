module

public import StacksFrontier.Cotangent.ThreefoldPolynomialOnTop.TowerMor
import StacksCore.Tactic.StacksAttribute

/-!
# The chain `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ` at the small models

This file applies the criterion of Tag 08Q9 to the cosimplicial object `U_•` of towers of a
resolution, at the small model of the footnote-restricted threefold site of Tag 08QT, and reads
off the chain `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ` there: first for an arbitrary resolution
whose augmentation is a trivial Kan fibration, then unconditionally for the standard resolution
of Tag 08PM, through Tag 08QI.

## Main definitions

* `CommAlgCat.boundedTowerCosimplicialObject` and `CommAlgCat.smallTowerCosimplicialObject`:
  `U_•` in the footnote-restricted site and in its small model.
* `CommAlgCat.boundedTowerIdentityAugmentation` and `CommAlgCat.smallTowerIdentityObj`: the
  identity augmentation `C → C`, as an object of the restricted site `C_{C/B}` and of its
  small model.

## Main results

* `CommAlgCat.isPointResolution_smallTowerCosimplicialObject` and
  `CommAlgCat.smallTowerLeftDerivedColimitNatIso`: the criterion of Tag 08Q9 applies to `U_•`.
* `CommAlgCat.smallTowerThirdConstIso` and `CommAlgCat.colimitSmallTowerIdentityIso`.
* `CommAlgCat.leftDerivedColimitThirdInverseImageZeroIso`,
  `CommAlgCat.isZero_leftDerivedColimitThirdInverseImage_succ`,
  `CommAlgCat.leftDerivedColimitThirdZeroIso` and
  `CommAlgCat.isZero_leftDerivedColimitThird_succ`: the chain for an arbitrary resolution.
* `CommAlgCat.standardLeftDerivedColimitThirdInverseImageZeroIso`,
  `CommAlgCat.isZero_standardLeftDerivedColimitThirdInverseImage_succ` and
  `CommAlgCat.standardLeftDerivedColimitThirdChainIso`: the chain for the standard resolution.

## References

* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QG](https://stacks.math.columbia.edu/tag/08QG)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CommAlgCat

/-! ### The criterion of Tag 08Q9 at the small model of the restricted tower site -/

section Small

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C) (κ μ : Cardinal.{u})
  (hPκ : ∀ m, IsPolynomialAlgebraBelow A κ (P.obj m)) (hμ : Cardinal.mk E ≤ μ)

include ε eqv hPκ hμ in
/-- **The towers of a bounded resolution lie in the restricted category of polynomial
towers**: `P_n` has at most `κ` variables over `A` by hypothesis, and `P_n[E]` has at most `μ`
variables over `P_n` because `E` has at most `μ` elements. -/
lemma isPolynomialTowerBelow_towerCommaOfResolution (m : SimplexCategoryᵒᵖ) :
    IsPolynomialTowerBelow A B C κ μ
      (towerCommaOfResolution ε eqv (fun m => (hPκ m).isPolynomialAlgebra) m) :=
  ⟨hPκ m, ⟨E, hμ, ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) fun _ => rfl⟩⟩,
    (isPolynomialTower_towerCommaOfResolution ε eqv
      (fun m => (hPκ m).isPolynomialAlgebra) m).2⟩

include ε eqv hPκ hμ in
/-- The towers of a bounded resolution, as a simplicial object of the restricted category of
polynomial towers. -/
def boundedTowerSimplicialOfResolution :
    SimplicialObject (BoundedPolynomialTower A B C κ μ) :=
  (IsPolynomialTowerBelow A B C κ μ).lift
    (towerCommaSimplicialOfResolution ε eqv (fun m => (hPκ m).isPolynomialAlgebra))
    (isPolynomialTowerBelow_towerCommaOfResolution ε eqv κ μ hPκ hμ)

include ε eqv hPκ hμ in
/-- The towers of a bounded resolution, as a cosimplicial object of the restricted site
`C_{C/B/A}`. -/
def boundedTowerCosimplicialObject :
    CosimplicialObject (boundedPolynomialTowerSite A B C κ μ) :=
  (boundedTowerSimplicialOfResolution ε eqv κ μ hPκ hμ).rightOp

include ε eqv hPκ hμ in
/-- Read in the unrestricted site, the cosimplicial object of the bounded towers of a resolution
is the cosimplicial object of those towers: the restriction only cuts down the ambient
category. -/
def boundedTowerCosimplicialObjectι :
    boundedTowerCosimplicialObject ε eqv κ μ hPκ hμ ⋙
        boundedPolynomialTowerSiteι A B C κ μ ≅
      towerCosimplicialObject ε eqv (fun m => (hPκ m).isPolynomialAlgebra) :=
  Iso.refl _

include ε eqv hPκ hμ in
/-- The cosimplicial object of the towers of a bounded resolution, transported to the genuinely
small model of the restricted site. -/
def smallTowerCosimplicialObject :
    CosimplicialObject (smallBoundedPolynomialTowerSite A B C κ μ) :=
  boundedTowerCosimplicialObject ε eqv κ μ hPκ hμ ⋙
    (boundedPolynomialTowerSiteEquiv A B C κ μ).inverse

include ε eqv hPκ hμ in
/-- Read in the unrestricted site, the cosimplicial object of the small model is the
cosimplicial object of the towers of the resolution. -/
def smallTowerCosimplicialObjectι :
    smallTowerCosimplicialObject ε eqv κ μ hPκ hμ ⋙
        smallBoundedPolynomialTowerSiteToPolynomialTowerSite A B C κ μ ≅
      towerCosimplicialObject ε eqv (fun m => (hPκ m).isPolynomialAlgebra) :=
  Functor.isoWhiskerLeft (boundedTowerCosimplicialObject ε eqv κ μ hPκ hμ)
      (Functor.isoWhiskerRight (boundedPolynomialTowerSiteEquiv A B C κ μ).counitIso
        (boundedPolynomialTowerSiteι A B C κ μ)) ≪≫
    boundedTowerCosimplicialObjectι ε eqv κ μ hPκ hμ

include ε eqv hPκ hμ in
/-- **The hypothesis of the criterion of Tag 08Q9, for the small model of the restricted site
`C_{C/B/A}`.** Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial
algebras on at most `κ` variables, and let `C = B[E]` with `E` of cardinality at most `μ`. Then
the cosimplicial object `U_•` of the towers `(P_n → B, P_n[E] → C)` in the small model of the
restricted site is a point resolution: every simplicial set of morphisms from it into an object
of the model is homotopy equivalent to a singleton.

Nothing is reproved: the homotopy equivalences are those of
`CommAlgCat.exists_homotopyEquivalences_towerMor`, supplied in the unrestricted site, and they
descend because the model embeds fully faithfully in it. -/
theorem isPointResolution_smallTowerCosimplicialObject
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.IsPointResolution
      (smallTowerCosimplicialObject ε eqv κ μ hPκ hμ) :=
  Stacks.ChaoticSite.isPointResolution_of_fullyFaithful
    (fullyFaithfulSmallBoundedPolynomialTowerSiteToPolynomialTowerSite A B C κ μ) _
    (smallTowerCosimplicialObjectι ε eqv κ μ hPκ hμ)
    (exists_homotopyEquivalences_towerMor ε eqv
      (fun m => (hPκ m).isPolynomialAlgebra) hε)

include ε eqv hPκ hμ in
/-- **The criterion of Tag 08Q9 at the small model of the restricted site `C_{C/B/A}`.** For
every abelian presheaf `𝒢` on the small model, the left derived functors of the colimit over the
index category are the homology of the Moore complex of `𝒢(U_•)`, naturally in `𝒢`. -/
def smallTowerLeftDerivedColimitNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (n : ℕ) :
    (colim : ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        AddCommGrpCat.{u}).leftDerived n ≅
      Stacks.ChaoticSite.cosimplicialMooreComplex
          (smallTowerCosimplicialObject ε eqv κ μ hPκ hμ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  Stacks.ChaoticSite.leftDerivedColimitNatIso _
    (isPointResolution_smallTowerCosimplicialObject ε eqv κ μ hPκ hμ hε) n

end Small

/-! ### `u₃` of the cosimplicial object is constant at the identity augmentation -/

section Conclusion

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C) (κ μ : Cardinal.{u})
  (hPκ : ∀ m, IsPolynomialAlgebraBelow A κ (P.obj m)) (hμ : Cardinal.mk E ≤ μ)

include eqv hμ in
/-- `C` is a polynomial algebra over `B` on at most `μ` variables, by a presentation
`C = B[E]` with `E` of cardinality at most `μ`. -/
lemma isPolynomialAlgebraBelow_towerRelativeAlgebra :
    IsPolynomialAlgebraBelow B μ (towerRelativeAlgebra B C) :=
  ⟨E, hμ, ⟨eqv⟩⟩

include eqv hμ in
/-- The identity augmentation `C → C`, as an object of the restricted category of polynomial
`B`-algebras augmented to `C`. -/
def boundedTowerIdentityAugmentation :
    BoundedPolynomialAugmentation B (towerRelativeAlgebra B C) μ :=
  ⟨Over.mk (𝟙 (towerRelativeAlgebra B C)),
    isPolynomialAlgebraBelow_towerRelativeAlgebra eqv μ hμ⟩

include eqv hμ in
/-- The identity augmentation `C → C` is terminal in the restricted category of polynomial
`B`-algebras augmented to `C`: an augmentation `α : Q → C` has exactly one map to it over `C`,
namely `α` itself. -/
def boundedTowerIdentityAugmentation_isTerminal :
    IsTerminal (boundedTowerIdentityAugmentation eqv μ hμ) :=
  IsTerminal.ofUniqueHom
    (fun X => ObjectProperty.homMk (Over.mkIdTerminal.from X.obj))
    fun _ f => by
      apply ObjectProperty.hom_ext
      exact Over.mkIdTerminal.hom_ext f.hom _

include ε eqv hPκ hμ in
/-- `u₃` of a tower of a bounded resolution is the identity augmentation `C → C`, read in the
restricted category of polynomial `B`-algebras augmented to `C`. -/
def boundedTowerThirdObjIso (m : SimplexCategoryᵒᵖ) :
    (boundedPolynomialTowerThirdAugmentations A B C κ μ).obj
        ((boundedTowerSimplicialOfResolution ε eqv κ μ hPκ hμ).obj m) ≅
      boundedTowerIdentityAugmentation eqv μ hμ :=
  ObjectProperty.isoMk _
    (Over.isoMk (CommAlgCat.isoMk
        (towerBaseChangeAlgEquiv ε eqv (fun m => (hPκ m).isPolynomialAlgebra) m)) (by
      apply CommAlgCat.hom_ext
      refine AlgHom.ext fun z => ?_
      exact (towerBaseChangeAugmentation_eq_algEquiv ε eqv
        (fun m => (hPκ m).isPolynomialAlgebra) m z).symm))

include ε eqv hPκ hμ in
/-- `u₃` of a tower of a bounded resolution is terminal in the restricted category of
polynomial `B`-algebras augmented to `C`. -/
def isTerminal_boundedTowerThirdObj (m : SimplexCategoryᵒᵖ) :
    IsTerminal ((boundedPolynomialTowerThirdAugmentations A B C κ μ).obj
      ((boundedTowerSimplicialOfResolution ε eqv κ μ hPκ hμ).obj m)) :=
  IsTerminal.ofIso (boundedTowerIdentityAugmentation_isTerminal eqv μ hμ)
    (boundedTowerThirdObjIso ε eqv κ μ hPκ hμ m).symm

include eqv hμ in
/-- The identity augmentation `C → C`, as an object of the small model of the restricted site
`C_{C/B}`. -/
def smallTowerIdentityObj : smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ :=
  (boundedPolynomialSiteEquiv B (towerRelativeAlgebra B C) μ).inverse.obj
    (op (boundedTowerIdentityAugmentation eqv μ hμ))

include eqv hμ in
/-- The identity augmentation `C → C` is an initial object of the small model of the restricted
site `C_{C/B}`, the site being the opposite of the category of augmentations. -/
def isInitial_smallTowerIdentityObj : IsInitial (smallTowerIdentityObj eqv μ hμ) :=
  IsInitial.isInitialObj _ _
    (initialOpOfTerminal (boundedTowerIdentityAugmentation_isTerminal eqv μ hμ))

include ε eqv hPκ hμ in
/-- `u₃` of the cosimplicial object of the towers of a bounded resolution is, in each degree, an
initial object of the small model of the restricted site `C_{C/B}`. -/
def isInitial_smallTowerThirdObj (m : SimplexCategory) :
    IsInitial ((smallTowerCosimplicialObject ε eqv κ μ hPκ hμ ⋙
      smallBoundedPolynomialTowerThird A B C κ μ).obj m) :=
  IsInitial.ofIso
    (IsInitial.isInitialObj
      (boundedPolynomialSiteEquiv B (towerRelativeAlgebra B C) μ).inverse _
      (initialOpOfTerminal (isTerminal_boundedTowerThirdObj ε eqv κ μ hPκ hμ (op m))))
    ((boundedPolynomialSiteEquiv B (towerRelativeAlgebra B C) μ).inverse.mapIso
      ((boundedPolynomialTowerThird A B C κ μ).mapIso
        ((boundedPolynomialTowerSiteEquiv A B C κ μ).counitIso.app _).symm))

include ε eqv hPκ hμ in
/-- **`u₃(U_•)` is the constant cosimplicial object with value the identity augmentation
`C → C`**, read in the small model of the restricted site `C_{C/B}`: in each degree it is an
initial object there, and the comparison is the unique morphism out of an initial object. -/
def smallTowerThirdConstIso :
    smallTowerCosimplicialObject ε eqv κ μ hPκ hμ ⋙
        smallBoundedPolynomialTowerThird A B C κ μ ≅
      (Functor.const SimplexCategory).obj (smallTowerIdentityObj eqv μ hμ) :=
  NatIso.ofComponents
    (fun m => (isInitial_smallTowerThirdObj ε eqv κ μ hPκ hμ m).uniqueUpToIso
      (isInitial_smallTowerIdentityObj eqv μ hμ))
    fun _ => (isInitial_smallTowerThirdObj ε eqv κ μ hPκ hμ _).hom_ext _ _

include eqv hμ in
/-- **Tag 08QG at the small model of the restricted site `C_{C/B}`**: `π_{3,!}ℱ = ℱ(C → C)`.
The lower shriek of Tag 08PF is the colimit over the index category, and the identity
augmentation `C → C` is a terminal object of it. -/
def colimitSmallTowerIdentityIso
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    colimit F ≅ F.obj (op (smallTowerIdentityObj eqv μ hμ)) :=
  colimit.isoColimitCocone ⟨_, colimitOfDiagramTerminal
    (terminalOpOfInitial (isInitial_smallTowerIdentityObj eqv μ hμ)) F⟩

/-- `g₃^{-1}` on abelian presheaves, for the small models of the restricted sites: restriction
along `u₃`, which is the inverse image of the morphism of topoi `g₃` by
`CommAlgCat.smallBoundedPolynomialTowerThirdTopos_inverseImage`. -/
abbrev smallTowerThirdInverseImage (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra A B] (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (κ μ : Cardinal.{u}) :
    ((smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
    (smallBoundedPolynomialTowerThird A B C κ μ).op

include ε eqv hPκ hμ in
/-- **The Moore complex of `(g₃^{-1}ℱ)(U_•)` is the alternating constant complex on
`ℱ(C → C)`**: `u₃(U_•)` is the constant cosimplicial object with value the identity
augmentation. -/
def cosimplicialMooreComplexThirdInverseImageIso
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (Stacks.ChaoticSite.cosimplicialMooreComplex
          (smallTowerCosimplicialObject ε eqv κ μ hPκ hμ)).obj
        ((smallTowerThirdInverseImage A B C κ μ).obj F) ≅
      ChainComplex.alternatingConst.obj (F.obj (op (smallTowerIdentityObj eqv μ hμ))) :=
  (AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}).mapIso
      (Functor.isoWhiskerRight
          (NatIso.op (smallTowerThirdConstIso ε eqv κ μ hPκ hμ)).symm F ≪≫
        Functor.constComp SimplexCategoryᵒᵖ (op (smallTowerIdentityObj eqv μ hμ)) F) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app
      (F.obj (op (smallTowerIdentityObj eqv μ hμ)))

include ε eqv hPκ hμ in
/-- **Stacks 08QV, in degree zero.** With notation as in Tag 08QT, suppose `C = B[E]` is a
polynomial algebra over `B`. Then `π_!(g₃^{-1}ℱ) = π_{3,!}ℱ` for every abelian presheaf `ℱ` on
the small model of the restricted site `C_{C/B}`: both sides are the sections of `ℱ` at the
identity augmentation `C → C`. -/
@[stacks 08QV "the degree-zero half of `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ`, read at the \
  small models of the footnote-restricted sites of Tag 08QT, with `π_!` the colimit over the \
  index category of Tag 08PF and `κ`, `μ` the bounds on the two layers of variables; the \
  vanishing in positive degrees is \
  `CommAlgCat.isZero_leftDerivedColimitThirdInverseImage_succ`"]
def leftDerivedColimitThirdInverseImageZeroIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((colim : ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          AddCommGrpCat.{u}).leftDerived 0).obj
        ((smallTowerThirdInverseImage A B C κ μ).obj F) ≅
      colimit F :=
  (smallTowerLeftDerivedColimitNatIso ε eqv κ μ hPκ hμ hε 0).app _ ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) 0).mapIso
      (cosimplicialMooreComplexThirdInverseImageIso ε eqv κ μ hPκ hμ F) ≪≫
    ChainComplex.alternatingConstHomologyZero _ ≪≫
    (colimitSmallTowerIdentityIso eqv μ hμ F).symm

include ε eqv hPκ hμ in
/-- **Stacks 08QV, in positive degrees.** With notation as in Tag 08QT, suppose `C = B[E]` is a
polynomial algebra over `B`. Then `L_nπ_!(g₃^{-1}ℱ) = 0` for `n > 0`: the simplicial abelian
group `(g₃^{-1}ℱ)(U_•)` is constant. -/
@[stacks 08QV "the positive-degree half of `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ`, read at \
  the small models of the footnote-restricted sites of Tag 08QT: `Lπ_!(g₃^{-1}ℱ)` is \
  concentrated in degree zero, where it is `π_{3,!}ℱ` by \
  `CommAlgCat.leftDerivedColimitThirdInverseImageZeroIso`"]
theorem isZero_leftDerivedColimitThirdInverseImage_succ
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) :
    IsZero (((colim : ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        AddCommGrpCat.{u}).leftDerived (n + 1)).obj
      ((smallTowerThirdInverseImage A B C κ μ).obj F)) := by
  refine IsZero.of_iso ?_
    ((smallTowerLeftDerivedColimitNatIso ε eqv κ μ hPκ hμ hε (n + 1)).app _ ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ)
          (n + 1)).mapIso
        (cosimplicialMooreComplexThirdInverseImageIso ε eqv κ μ hPκ hμ F))
  exact (ChainComplex.alternatingConst_exactAt
    (F.obj (op (smallTowerIdentityObj eqv μ hμ))) (n + 1) (Nat.succ_ne_zero n)).isZero_homology

/-! ### The middle term `Lπ_{3, !}ℱ` -/

/-- **Stacks 08QV, the middle term in degree zero**: `π_{3,!}` is right exact, so
`L_0π_{3,!}ℱ = π_{3,!}ℱ` for every abelian presheaf `ℱ` on the small model of the restricted
site `C_{C/B}`. No hypothesis on `C` is used here; the content of the second equality of the tag
is the vanishing in positive degrees, which is
`CommAlgCat.isZero_leftDerivedColimitThird_succ`.
**Not Tag 08QV.** This is read at the small model of the footnote-restricted site `C_{C/B}`, not
at `C_{C/B}` itself: the footnote cuts that site down to the full subcategory of the augmentations
whose set of variables has cardinality at most `μ`, and both the abelian sheaves and `Lπ_{3,!}`
change when one passes to a full subcategory, so this is a statement about different
coefficients. The tag at the sites themselves is
`CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`, the first equality, together with
`CommAlgCat.polynomialSiteDerivedColimitThirdIso`, the second. -/
def leftDerivedColimitThirdZeroIso
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((colim : ((smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤
          AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived 0).obj F ≅
      colimit F :=
  Stacks.ChaoticSite.leftDerivedColimitZeroIsoColimit F

include eqv hμ in
/-- **Stacks 08QV, the middle term in positive degrees.** Suppose `C = B[E]` is a polynomial
algebra over `B`. Then `L_nπ_{3,!}ℱ = 0` for `n > 0` and every abelian presheaf `ℱ` on the small
model of the restricted site `C_{C/B}`.

This is the second equality `Lπ_{3,!}ℱ = π_{3,!}ℱ` of the tag: the identity augmentation
`C → C` is an initial object of `C_{C/B}`, so `π_{3,!}` is evaluation there and hence exact.
**Not Tag 08QV.** This is read at the small model of the footnote-restricted site `C_{C/B}`, not
at `C_{C/B}` itself: the footnote cuts that site down to the full subcategory of the augmentations
whose set of variables has cardinality at most `μ`, and both the abelian sheaves and `Lπ_{3,!}`
change when one passes to a full subcategory, so this is a statement about different
coefficients. The tag at the sites themselves is
`CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`, the first equality, together with
`CommAlgCat.polynomialSiteDerivedColimitThirdIso`, the second. -/
theorem isZero_leftDerivedColimitThird_succ
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) :
    IsZero (((colim : ((smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤
        AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived (n + 1)).obj F) :=
  Stacks.ChaoticSite.isZero_leftDerivedColimit_succ_of_isInitial
    (isInitial_smallTowerIdentityObj eqv μ hμ) F n

end Conclusion

/-! ### Stacks 08QV: the chain `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ`, unconditionally -/

section Standard

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C) (κ μ : Cardinal.{u})
  (hκ : standardResolutionVarCardinal A (towerBaseAlgebra A B) ≤ κ)
  (hμ : Cardinal.mk E ≤ μ)

include hκ in
/-- Every term of the standard resolution of `B` over `A` is a polynomial algebra over `A` on at
most `κ` variables, as soon as `κ` is at least the bound
`CommAlgCat.standardResolutionVarCardinal A B` of Tag 08PM's resolution. -/
theorem standardTowerResolution_isPolynomialAlgebraBelow (m : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A κ
      ((standardResolution.{u, u} A (towerBaseAlgebra A B)).left.obj m) :=
  (standardResolution_isPolynomialAlgebraBelow A (towerBaseAlgebra A B) m).imp
    fun _ h => ⟨h.1.trans hκ, h.2⟩

include eqv hκ hμ in
/-- **Stacks 08QV, in degree zero, unconditionally.** With notation as in Tag 08QT, suppose
`C = B[E]` is a polynomial algebra over `B`. Then `π_!(g₃^{-1}ℱ) = π_{3,!}ℱ` for every abelian
presheaf `ℱ` on the small model of the restricted site `C_{C/B}`.

No hypothesis on a resolution survives: the resolution of `B` over `A` whose towers compute
`Lπ_!` is the standard one of Tag 08PM, and the trivial Kan fibration condition that
`CommAlgCat.leftDerivedColimitThirdInverseImageZeroIso` carries is supplied by Tag 08QI,
`CommAlgCat.standardResolution_isResolution`.
**Not Tag 08QV.** This is read at the small models of the footnote-restricted sites, not at
`C_{C/B/A}` and `C_{C/B}` themselves: the footnote cuts those sites down to the full subcategories
of the towers whose two layers of variables have cardinality at most `κ` and `μ`, and both the
abelian sheaves and `Lπ_!` change when one passes to a full subcategory, so this is a statement
about different coefficients. The tag at the sites themselves is
`CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`, the first equality, together with
`CommAlgCat.polynomialSiteDerivedColimitThirdIso`, the second. -/
def standardLeftDerivedColimitThirdInverseImageZeroIso
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((colim : ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          AddCommGrpCat.{u}).leftDerived 0).obj
        ((smallTowerThirdInverseImage A B C κ μ).obj F) ≅
      colimit F :=
  leftDerivedColimitThirdInverseImageZeroIso (B := B)
    (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom eqv κ μ
    (standardTowerResolution_isPolynomialAlgebraBelow κ hκ) hμ
    (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).trivialKanFibration F

include eqv hκ hμ in
/-- **Stacks 08QV, in positive degrees, unconditionally.** With notation as in Tag 08QT, suppose
`C = B[E]` is a polynomial algebra over `B`. Then `L_nπ_!(g₃^{-1}ℱ) = 0` for `n > 0`, the
resolution being the standard one of Tag 08PM and the trivial Kan fibration condition being
supplied by Tag 08QI.
**Not Tag 08QV.** This is read at the small models of the footnote-restricted sites, not at
`C_{C/B/A}` and `C_{C/B}` themselves: the footnote cuts those sites down to the full subcategories
of the towers whose two layers of variables have cardinality at most `κ` and `μ`, and both the
abelian sheaves and `Lπ_!` change when one passes to a full subcategory, so this is a statement
about different coefficients. The tag at the sites themselves is
`CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`, the first equality, together with
`CommAlgCat.polynomialSiteDerivedColimitThirdIso`, the second. -/
theorem isZero_standardLeftDerivedColimitThirdInverseImage_succ
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) :
    IsZero (((colim : ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        AddCommGrpCat.{u}).leftDerived (n + 1)).obj
      ((smallTowerThirdInverseImage A B C κ μ).obj F)) :=
  isZero_leftDerivedColimitThirdInverseImage_succ (B := B)
    (standardResolution.{u, u} A (towerBaseAlgebra A B)).hom eqv κ μ
    (standardTowerResolution_isPolynomialAlgebraBelow κ hκ) hμ
    (standardResolution_isResolution.{u, u} A (towerBaseAlgebra A B)).trivialKanFibration F n

include eqv hκ hμ in
/-- **Stacks 08QV, the first equality, in every degree.** With notation as in Tag 08QT, suppose
`C = B[E]` is a polynomial algebra over `B`. Then `L_nπ_!(g₃^{-1}ℱ) = L_nπ_{3,!}ℱ` for every `n`
and every abelian presheaf `ℱ` on the small model of the restricted site `C_{C/B}`: in degree
zero both are `π_{3,!}ℱ` and in positive degrees both vanish.

Together with `CommAlgCat.leftDerivedColimitThirdZeroIso` and
`CommAlgCat.isZero_leftDerivedColimitThird_succ`, which say that `Lπ_{3,!}ℱ` is `π_{3,!}ℱ`, this
is the full chain `Lπ_!(g₃^{-1}ℱ) = Lπ_{3,!}ℱ = π_{3,!}ℱ` of the tag.
**Not Tag 08QV.** This is read at the small models of the footnote-restricted sites, not at
`C_{C/B/A}` and `C_{C/B}` themselves: the footnote cuts those sites down to the full subcategories
of the towers whose two layers of variables have cardinality at most `κ` and `μ`, and both the
abelian sheaves and `Lπ_!` change when one passes to a full subcategory, so this is a statement
about different coefficients. The tag at the sites themselves is
`CommAlgCat.polynomialTowerDerivedColimitThirdInverseImageIso`, the first equality, together with
`CommAlgCat.polynomialSiteDerivedColimitThirdIso`, the second. -/
def standardLeftDerivedColimitThirdChainIso
    (F : (smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (n : ℕ) :
    ((colim : ((smallBoundedPolynomialTowerSite A B C κ μ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          AddCommGrpCat.{u}).leftDerived n).obj
        ((smallTowerThirdInverseImage A B C κ μ).obj F) ≅
      ((colim : ((smallBoundedPolynomialSite B (towerRelativeAlgebra B C) μ)ᵒᵖ ⥤
          AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n).obj F := by
  match n with
  | 0 =>
    exact standardLeftDerivedColimitThirdInverseImageZeroIso eqv κ μ hκ hμ F ≪≫
      (leftDerivedColimitThirdZeroIso μ F).symm
  | m + 1 =>
    exact (isZero_standardLeftDerivedColimitThirdInverseImage_succ eqv κ μ hκ hμ F m).iso
      (isZero_leftDerivedColimitThird_succ eqv μ hμ F m)

end Standard

end CommAlgCat

end
