module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesPushforwardCompAnyCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBridgePseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.CategoryTheory.Bicategory.LeftAdjointStrongTrans

/-!
# The base change map of a square of represented algebraic spaces is the scheme one

Let
```
W' --n'--> W
|m'        |m
v          v
V' --n---> V
```
be a commutative square of the big fppf site of `S`. The spaces-étale base change map of the
square of represented algebraic spaces, `AlgebraicGeometry.Space.spacesToposBaseChangeSquare`,
and the base change map of sheaves of sets on the bounded small étale sites of the underlying
schemes, `AlgebraicGeometry.smallEtaleBaseChangeNatTrans`, are both mates of the comparison of the
two composite direct images around the square. The restrictions along the chart functors
(`AlgebraicGeometry.Space.representedRestriction`) identify the four spaces-étale topoi with the
four bounded small étale topoi, compatibly with direct images
(`AlgebraicGeometry.Space.representedPushforwardIso`), and that compatibility respects composition
(`AlgebraicGeometry.Space.representedPushforwardSquare_comp`). This file proves that the two
comparisons of composite direct images correspond under these identifications, for sheaves with
values in an arbitrary category `A`. Taking mates then identifies the invertibility of the two
base change maps.

## Main results

* `AlgebraicGeometry.Space.representedPushforwardIso_comp_app`: the composition compatibility of
  the comparison of direct images, read at one sheaf on the sheaf categories, with values in any
  category; on sections it is `AlgebraicGeometry.Space.representedChartBaseChangeIso_comp_app`.
* `AlgebraicGeometry.Space.representedPushforwardCompSquare_app`: **the comparison of the two
  composite direct images around a commutative square corresponds under the chart restrictions**,
  at every sheaf of sets.
* `AlgebraicGeometry.Space.representedPushforwardCube`: the same correspondence as an equation of
  2-squares, with the bounded comparison through the diagonal of the square,
  `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`. This is the cube identity whose mate is
  the comparison of the two base change maps.
* `AlgebraicGeometry.Space.isIso_spacesToposBaseChangeSquare_iff`: **the spaces-étale base change
  map of a square of represented algebraic spaces is invertible if and only if the base change
  map of sheaves of sets on the bounded small étale sites of the underlying schemes is.**

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TwoSquare

universe u

/-! ### Components of 2-squares and of the bounded comparisons -/

/-- The component of a 2-square given by a natural transformation is the component of that
transformation. -/
theorem CategoryTheory.TwoSquare.mk_natTrans_app {C₁ C₂ C₃ C₄ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Category* C₄] {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {Bo : C₃ ⥤ C₄} (α : T ⋙ R ⟶ L ⋙ Bo) (X : C₁) :
    (TwoSquare.mk T L R Bo α).natTrans.app X = α.app X := rfl

namespace AlgebraicGeometry

/-- At sheaves of sets of the site's universe, the component of the composition comparison of
direct images `AlgebraicGeometry.smallEtaleSheafPushforwardCompIso` is that of
`AlgebraicGeometry.smallEtaleMorphism_comp_pushforwardIso`. -/
theorem smallEtaleSheafPushforwardCompIso_hom_app_type (B : BigEtaleSite.{u}) (X Y Z : B.Scheme)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    (smallEtaleSheafPushforwardCompIso B X Y Z f g (Type (u + 1))).hom.app M =
      (smallEtaleMorphism_comp_pushforwardIso B X Y Z f g).hom.app M := rfl

/-- The inverse of `AlgebraicGeometry.smallEtaleSheafPushforwardCompIso_hom_app_type`. -/
theorem smallEtaleSheafPushforwardCompIso_inv_app_type (B : BigEtaleSite.{u}) (X Y Z : B.Scheme)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))) :
    (smallEtaleSheafPushforwardCompIso B X Y Z f g (Type (u + 1))).inv.app M =
      (smallEtaleMorphism_comp_pushforwardIso B X Y Z f g).inv.app M := rfl

namespace SmallEtale

universe u' v'

variable (A : Type u') [Category.{v'} A] (B : BigEtaleSite.{u})

/-- The comparison of direct images along a factorised composite, at one sheaf: the comparison
along the written-out composite followed by the transport along the factorisation. -/
theorem boundedPushforwardCompIso_hom_app {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V)
    (Q : Z ⟶ V) (hQ : k ≫ l = Q) (F : Sheaf (SmallEtale.topology B Z.1 Z.property) A) :
    (boundedPushforwardCompIso B A k l Q hQ).hom.app F =
      (smallEtaleSheafPushforwardCompIso B Z W V k l A).hom.app F ≫
        (eqToHom (congrArg (fun m : Z ⟶ V => B.smallPushforward m A) hQ)).app F := by
  subst hQ
  simp [boundedPushforwardCompIso, smallEtaleBaseChange_factoredCompIso,
    smallEtaleSheafPushforwardCompIso]

/-- The inverse of `AlgebraicGeometry.SmallEtale.boundedPushforwardCompIso_hom_app`. -/
theorem boundedPushforwardCompIso_inv_app {Z W V : B.Scheme} (k : Z ⟶ W) (l : W ⟶ V)
    (Q : Z ⟶ V) (hQ : k ≫ l = Q) (F : Sheaf (SmallEtale.topology B Z.1 Z.property) A) :
    (boundedPushforwardCompIso B A k l Q hQ).inv.app F =
      (eqToHom (congrArg (fun m : Z ⟶ V => B.smallPushforward m A) hQ.symm)).app F ≫
        (smallEtaleSheafPushforwardCompIso B Z W V k l A).inv.app F := by
  subst hQ
  simp [boundedPushforwardCompIso, smallEtaleBaseChange_factoredCompIso,
    smallEtaleSheafPushforwardCompIso]

variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)

/-- The component of `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate` at a sheaf. -/
theorem boundedBaseChangeMate_natTrans_app
    (F : Sheaf (SmallEtale.topology B X'.1 X'.property) A) :
    (boundedBaseChangeMate B A f g g' f' P hP₁ hP₂).natTrans.app F =
      (boundedPushforwardCompIso B A g' f P hP₁).hom.app F ≫
        (boundedPushforwardCompIso B A f' g P hP₂).inv.app F := rfl

/-- **The base change map of sheaves of sets on the bounded small étale sites is the mate of the
comparison through the diagonal.** `AlgebraicGeometry.smallEtaleBaseChangeNatTrans` is invertible
if and only if the mate of `AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`, at the
coefficient universe `u + 1`, is. -/
theorem isIso_smallEtaleBaseChangeNatTrans_iff_boundedBaseChangeMate (h : g' ≫ f = f' ≫ g) :
    IsIso (smallEtaleBaseChangeNatTrans.{u} B g' f' f g h) ↔
      IsIso ((mateEquiv (B.smallPullbackAdjunction g' (Type (u + 1)))
        (B.smallPullbackAdjunction g (Type (u + 1)))).symm
        (boundedBaseChangeMate B (Type (u + 1)) f g g' f' P hP₁ hP₂)).natTrans := by
  rw [smallEtaleBaseChangeNatTrans_eq_mateEquiv_symm,
    smallEtaleBaseChangeMate_eq_boundedBaseChangeMate B f g g' f' h P hP₁ hP₂]

end SmallEtale

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

universe u' v'

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (A : Type u') [Category.{v'} A]

/-- The comparison of direct images along a morphism of the site acts on sections by restriction
along the base-change comparison of the chart functors. -/
theorem representedPushforwardIso_hom_app_hom_app {V W : BigFppfOver B S hS} (f : W ⟶ V)
    (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) A)
    (U : (representedSchemeSmallEtale B S hS V)ᵒᵖ) :
    ((representedPushforwardIso f A).hom.app M).hom.app U =
      M.obj.map ((representedChartBaseChangeIso f).hom.app U.unop).op :=
  (Category.id_comp _).trans (Category.comp_id _)

/-- The comparison of direct images along a morphism of the site depends on the morphism only
through equality: transported along `p₁ = p₂` on both sides it is the comparison along `p₂`. -/
theorem representedPushforwardIso_eqToHom_app {V W : BigFppfOver B S hS} {p₁ p₂ : W ⟶ V}
    (h : p₁ = p₂) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) A) :
    (representedPushforwardIso p₁ A).hom.app M ≫
        (eqToHom (congrArg (fun k : W ⟶ V =>
          (smallEtaleBaseChange (associatedBigEtaleSite B) k.left).sheafPushforwardContinuous
            A (representedSchemeTopology B S hS V)
            (representedSchemeTopology B S hS W)) h)).app ((representedRestriction W A).obj M) =
      (representedRestriction V A).map ((eqToHom (congrArg (fun k : W ⟶ V =>
          (spacesBaseChange B S hS (yonedaSpaceHom k)).functor.sheafPushforwardContinuous
            A (SpacesEtale.topology B S hS (yonedaSpace B S hS V))
            (SpacesEtale.topology B S hS (yonedaSpace B S hS W))) h)).app M) ≫
        (representedPushforwardIso p₂ A).hom.app M := by
  subst h
  simp

/-- The spaces-étale direct images along `h_(q ≫ p)` and along `h_q ≫ h_p` agree. -/
theorem spacesPushforward_yonedaSpaceHom_comp {X Y Z : BigFppfOver B S hS} (p : Y ⟶ X)
    (q : Z ⟶ Y) :
    (spacesBaseChange B S hS (yonedaSpaceHom (q ≫ p))).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) =
      (spacesBaseChange B S hS
          (yonedaSpaceHom q ≫ yonedaSpaceHom p)).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) :=
  congrArg (fun k : yonedaSpace B S hS Z ⟶ yonedaSpace B S hS X =>
    (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
      A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
      (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))) (yonedaSpaceHom_comp q p)

/-- The transport of `AlgebraicGeometry.Space.spacesPushforward_yonedaSpaceHom_comp` is the
identity at every sheaf: `h_(q ≫ p)` and `h_q ≫ h_p` are definitionally equal. -/
theorem eqToHom_spacesPushforward_yonedaSpaceHom_comp_app {X Y Z : BigFppfOver B S hS}
    (p : Y ⟶ X) (q : Z ⟶ Y) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A) :
    (eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q)).app M = 𝟙 _ :=
  rfl

/-- `AlgebraicGeometry.Space.eqToHom_spacesPushforward_yonedaSpaceHom_comp_app`, followed by a
morphism. -/
theorem eqToHom_spacesPushforward_yonedaSpaceHom_comp_app_comp {X Y Z : BigFppfOver B S hS}
    (p : Y ⟶ X) (q : Z ⟶ Y) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A)
    {N : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS X)) A}
    (k : ((spacesBaseChange B S hS
        (yonedaSpaceHom q ≫ yonedaSpaceHom p)).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M ⟶ N) :
    (eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q)).app M ≫ k = k :=
  Category.id_comp k

/-- **The composition compatibility of the comparison of direct images, at one sheaf**, on the
sheaf categories: the comparison along `q ≫ p`, followed by the composition isomorphism of
bounded direct images, is the composition isomorphism of spaces-étale direct images followed by
the comparisons along `p` and along `q`. -/
theorem representedPushforwardIso_comp_app {X Y Z : BigFppfOver B S hS} (p : Y ⟶ X)
    (q : Z ⟶ Y) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A) :
    (representedPushforwardIso (q ≫ p) A).hom.app M ≫
        (smallEtaleSheafPushforwardCompIso (associatedBigEtaleSite B) _ _ _
          q.left p.left A).inv.app ((representedRestriction Z A).obj M) =
      (representedRestriction X A).map
          ((eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q)).app M ≫
          (spacesBaseChange_pushforward_comp_anyCoefficients B S hS
          (yonedaSpaceHom q) (yonedaSpaceHom p) A).inv.app M) ≫
        (representedPushforwardIso p A).hom.app (((spacesBaseChange B S hS
            (yonedaSpaceHom q)).functor.sheafPushforwardContinuous
          A (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
          (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M) ≫
        ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS X)
          (representedSchemeTopology B S hS Y)).map ((representedPushforwardIso q
              A).hom.app M) := by
  rewrite [eqToHom_spacesPushforward_yonedaSpaceHom_comp_app_comp]
  apply ObjectProperty.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  show (𝟙 _ ≫ M.obj.map ((representedChartBaseChangeIso (q ≫ p)).hom.app U.unop).op ≫ 𝟙 _) ≫
      (M.obj.map ((representedSchemeChartFunctor Z).map
        ((smallEtaleBaseChange_compIso (associatedBigEtaleSite B) _ _ _ q.left p.left).val.hom.app
          U.unop)).op ≫ 𝟙 _) =
    (M.obj.map ((spacesBaseChange_comp B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)).hom.app
        ((representedSchemeChartFunctor X).obj U.unop)).op ≫ 𝟙 _) ≫
      ((𝟙 _ ≫ M.obj.map ((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.map
          ((representedChartBaseChangeIso p).hom.app U.unop)).op ≫ 𝟙 _) ≫
        (𝟙 _ ≫ M.obj.map ((representedChartBaseChangeIso q).hom.app
          ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).obj U.unop)).op ≫ 𝟙 _))
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun k => M.obj.map k.op) (representedChartBaseChangeIso_comp_app p q U.unop)

/-- `AlgebraicGeometry.Space.representedPushforwardIso_comp_app`, followed by a morphism. -/
theorem representedPushforwardIso_comp_app_assoc {X Y Z : BigFppfOver B S hS} (p : Y ⟶ X)
    (q : Z ⟶ Y) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS X)
          (representedSchemeTopology B S hS Y)).obj
          (((smallEtaleBaseChange (associatedBigEtaleSite B) q.left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS Y)
          (representedSchemeTopology B S hS Z)).obj ((representedRestriction Z
              A).obj M)) ⟶ N) :
    (representedPushforwardIso (q ≫ p) A).hom.app M ≫
        (smallEtaleSheafPushforwardCompIso (associatedBigEtaleSite B) _ _ _
          q.left p.left A).inv.app ((representedRestriction Z A).obj M) ≫ k =
      (representedRestriction X A).map
          ((eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q)).app M ≫
          (spacesBaseChange_pushforward_comp_anyCoefficients B S hS
          (yonedaSpaceHom q) (yonedaSpaceHom p) A).inv.app M) ≫
        (representedPushforwardIso p A).hom.app (((spacesBaseChange B S hS
            (yonedaSpaceHom q)).functor.sheafPushforwardContinuous
          A (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
          (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M) ≫
        ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS X)
          (representedSchemeTopology B S hS Y)).map ((representedPushforwardIso q
              A).hom.app M) ≫ k := by
  rw [← Category.assoc, representedPushforwardIso_comp_app A p q M]
  simp only [Category.assoc]

/-- `AlgebraicGeometry.Space.representedPushforwardIso_comp_app`, solved for the comparisons
along `p` and `q`, followed by a morphism. -/
theorem representedPushforwardIso_comp_app'_assoc {X Y Z : BigFppfOver B S hS} (p : Y ⟶ X)
    (q : Z ⟶ Y) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : ((smallEtaleBaseChange (associatedBigEtaleSite B) (q ≫ p).left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS X)
          (representedSchemeTopology B S hS Z)).obj ((representedRestriction Z
              A).obj M) ⟶ N) :
    (representedPushforwardIso p A).hom.app (((spacesBaseChange B S hS
        (yonedaSpaceHom q)).functor.sheafPushforwardContinuous
          A (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
          (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M) ≫
        ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).sheafPushforwardContinuous
          A (representedSchemeTopology B S hS X)
          (representedSchemeTopology B S hS Y)).map ((representedPushforwardIso q
              A).hom.app M) ≫
        (smallEtaleSheafPushforwardCompIso (associatedBigEtaleSite B) _ _ _
          q.left p.left A).hom.app ((representedRestriction Z A).obj M) ≫ k =
      (representedRestriction X A).map ((spacesBaseChange_pushforward_comp_anyCoefficients B S hS
          (yonedaSpaceHom q) (yonedaSpaceHom p) A).hom.app M ≫
          (eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q).symm).app M) ≫
        (representedPushforwardIso (q ≫ p) A).hom.app M ≫ k := by
  rw [← Iso.inv_hom_id_app_assoc (smallEtaleSheafPushforwardCompIso
      (associatedBigEtaleSite B) _ _ _ q.left p.left A) ((representedRestriction Z
          A).obj M) k,
    representedPushforwardIso_comp_app_assoc A p q M, ← Functor.map_comp_assoc]
  simp

/-- `AlgebraicGeometry.Space.representedPushforwardIso_eqToHom_app`, followed by a morphism. -/
theorem representedPushforwardIso_eqToHom_app_assoc {V W : BigFppfOver B S hS} {p₁ p₂ : W ⟶ V}
    (h : p₁ = p₂) (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS W)) A)
    {N : Sheaf (representedSchemeTopology B S hS V) A}
    (k : ((smallEtaleBaseChange (associatedBigEtaleSite B) p₂.left).sheafPushforwardContinuous
            A (representedSchemeTopology B S hS V)
            (representedSchemeTopology B S hS W)).obj ((representedRestriction W
                A).obj M) ⟶ N) :
    (representedPushforwardIso p₁ A).hom.app M ≫
        (eqToHom (congrArg (fun k : W ⟶ V =>
          (smallEtaleBaseChange (associatedBigEtaleSite B) k.left).sheafPushforwardContinuous
            A (representedSchemeTopology B S hS V)
            (representedSchemeTopology B S hS W)) h)).app ((representedRestriction W
                A).obj M) ≫ k =
      (representedRestriction V A).map ((eqToHom (congrArg (fun k : W ⟶ V =>
          (spacesBaseChange B S hS (yonedaSpaceHom k)).functor.sheafPushforwardContinuous
            A (SpacesEtale.topology B S hS (yonedaSpace B S hS V))
            (SpacesEtale.topology B S hS (yonedaSpace B S hS W))) h)).app M) ≫
        (representedPushforwardIso p₂ A).hom.app M ≫ k := by
  rw [← Category.assoc, representedPushforwardIso_eqToHom_app A h M, Category.assoc]

section Square

variable {V W V' W' : BigFppfOver B S hS} (m : W ⟶ V) (n : V' ⟶ V) (n' : W' ⟶ W)
  (m' : W' ⟶ V')

/-- **The comparison of the two composite direct images corresponds under the chart
restrictions**, at one sheaf `M` on the spaces-étale site of `h_{W'}`: going around the square on
the bounded small étale side after restricting is restricting after going around it on the
spaces-étale side. -/
theorem representedPushforwardCompSquare_app (h : n' ≫ m = m' ≫ n)
    (w : yonedaSpaceHom n' ≫ yonedaSpaceHom m = yonedaSpaceHom m' ≫ yonedaSpaceHom n)
    (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS W')) (Type (u + 1))) :
    (representedPushforwardIso m (Type (u + 1))).hom.app
          (((spacesBaseChange B S hS (yonedaSpaceHom n')).functor.sheafPushforwardContinuous
            (Type (u + 1)) (SpacesEtale.topology B S hS (yonedaSpace B S hS W))
            (SpacesEtale.topology B S hS (yonedaSpace B S hS W'))).obj M) ≫
        ((smallEtaleBaseChange (associatedBigEtaleSite B) m.left).sheafPushforwardContinuous
          (Type (u + 1)) (representedSchemeTopology B S hS V)
          (representedSchemeTopology B S hS W)).map ((representedPushforwardIso n'
              (Type (u + 1))).hom.app M) ≫
        (smallEtaleMorphism_comp_pushforwardIso (associatedBigEtaleSite B) _ _ _
          n'.left m.left).hom.app ((representedRestriction W' (Type (u + 1))).obj M) ≫
        (eqToHom (congrArg (fun k : W' ⟶ V =>
          (smallEtaleBaseChange (associatedBigEtaleSite B) k.left).sheafPushforwardContinuous
            (Type (u + 1)) (representedSchemeTopology B S hS V)
            (representedSchemeTopology B S hS W')) h)).app ((representedRestriction W'
                (Type (u + 1))).obj M) ≫
        (smallEtaleMorphism_comp_pushforwardIso (associatedBigEtaleSite B) _ _ _
          m'.left n.left).inv.app ((representedRestriction W' (Type (u + 1))).obj M) ≫
        ((smallEtaleBaseChange (associatedBigEtaleSite B) n.left).sheafPushforwardContinuous
          (Type (u + 1)) (representedSchemeTopology B S hS V)
          (representedSchemeTopology B S hS V')).map ((representedPushforwardIso m'
              (Type (u + 1))).inv.app M) =
      (representedRestriction V (Type (u + 1))).map
          ((spacesPushforwardCompSquare_anyCoefficients B S hS (yonedaSpaceHom n')
            (yonedaSpaceHom m') (yonedaSpaceHom m) (yonedaSpaceHom n) w (Type (u + 1))).app M) ≫
        (representedPushforwardIso n (Type (u + 1))).hom.app
          (((spacesBaseChange B S hS (yonedaSpaceHom m')).functor.sheafPushforwardContinuous
            (Type (u + 1)) (SpacesEtale.topology B S hS (yonedaSpace B S hS V'))
            (SpacesEtale.topology B S hS (yonedaSpace B S hS W'))).obj M) := by
  have k : ((smallEtaleBaseChange (associatedBigEtaleSite B) n.left).sheafPushforwardContinuous
        (Type (u + 1)) (representedSchemeTopology B S hS V)
        (representedSchemeTopology B S hS V')).map ((representedPushforwardIso m'
            (Type (u + 1))).hom.app M) ≫
      ((smallEtaleBaseChange (associatedBigEtaleSite B) n.left).sheafPushforwardContinuous
        (Type (u + 1)) (representedSchemeTopology B S hS V)
        (representedSchemeTopology B S hS V')).map ((representedPushforwardIso m'
            (Type (u + 1))).inv.app M) =
        𝟙 ((representedRestriction V' (Type (u + 1)) ⋙
          (smallEtaleBaseChange (associatedBigEtaleSite B) n.left).sheafPushforwardContinuous
          (Type (u + 1)) (representedSchemeTopology B S hS V)
          (representedSchemeTopology B S hS V')).obj
          (((spacesBaseChange B S hS (yonedaSpaceHom m')).functor.sheafPushforwardContinuous
            (Type (u + 1)) (SpacesEtale.topology B S hS (yonedaSpace B S hS V'))
            (SpacesEtale.topology B S hS (yonedaSpace B S hS W'))).obj M)) := by
    simp
  rewrite [← smallEtaleSheafPushforwardCompIso_hom_app_type,
    ← smallEtaleSheafPushforwardCompIso_inv_app_type]
  rw [representedPushforwardIso_comp_app'_assoc (Type (u + 1)) m n' M,
    representedPushforwardIso_eqToHom_app_assoc (Type (u + 1)) h M,
    representedPushforwardIso_comp_app_assoc (Type (u + 1)) n m' M, k, Category.comp_id]
  simp only [← Functor.map_comp_assoc]
  refine congrArg (fun t => (representedRestriction V (Type (u + 1))).map t ≫ _) ?_
  simp only [spacesPushforwardCompSquare_anyCoefficients, NatTrans.comp_app, eqToHom_app,
    Category.assoc, eqToHom_trans_assoc]

end Square

/-! ### The comparison through a factorisation -/

section Factored

variable {X Y Z : BigFppfOver B S hS}

/-- The bounded direct image along a morphism of the site is restriction along base change of
the represented schemes, on morphisms. -/
theorem smallPushforward_map_eq_sheafPushforwardContinuous_map (p : Y ⟶ X)
    {M N : Sheaf (representedSchemeTopology B S hS Y) A} (f : M ⟶ N) :
    ((associatedBigEtaleSite B).smallPushforward p.left A).map f =
      ((smallEtaleBaseChange (associatedBigEtaleSite B) p.left).sheafPushforwardContinuous
        A (representedSchemeTopology B S hS X)
        (representedSchemeTopology B S hS Y)).map f := rfl

/-- The transport of the bounded direct image along `q.left ≫ p.left = (q ≫ p).left`, an
equality of definitionally equal morphisms, is the identity. -/
theorem eqToHom_smallPushforward_comp_left_app_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    (hQ : q.left ≫ p.left = (q ≫ p).left)
    (M : Sheaf (representedSchemeTopology B S hS Z) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : ((associatedBigEtaleSite B).smallPushforward (q ≫ p).left A).obj M ⟶ N) :
    (eqToHom (congrArg (fun m : Z.left ⟶ X.left =>
      (associatedBigEtaleSite B).smallPushforward m A) hQ)).app M ≫ k = k :=
  Category.id_comp k

/-- The inverse transport of
`AlgebraicGeometry.Space.eqToHom_smallPushforward_comp_left_app_comp`. -/
theorem eqToHom_smallPushforward_comp_left_symm_app_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    (hQ : q.left ≫ p.left = (q ≫ p).left)
    (M : Sheaf (representedSchemeTopology B S hS Z) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : ((associatedBigEtaleSite B).smallPushforward (q.left ≫ p.left) A).obj M ⟶
      N) :
    (eqToHom (congrArg (fun m : Z.left ⟶ X.left =>
      (associatedBigEtaleSite B).smallPushforward m A) hQ.symm)).app M ≫ k = k :=
  Category.id_comp k

/-- The comparison of the composite of the spaces-étale direct images along `h_q` and `h_p` with
the direct image along `h_Q`, for a factorisation `q ≫ p = Q` in the site. -/
def spacesPushforwardFactoredComp (p : Y ⟶ X) (q : Z ⟶ Y) (Q : Z ⟶ X) (e : q ≫ p = Q) :
    (spacesBaseChange B S hS (yonedaSpaceHom q)).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) ⋙
      (spacesBaseChange B S hS (yonedaSpaceHom p)).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Y)) ⟶
    (spacesBaseChange B S hS (yonedaSpaceHom Q)).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) :=
  (spacesBaseChange_pushforward_comp_anyCoefficients B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)
      A).hom ≫
    eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q).symm ≫
    eqToHom (congrArg (fun k : Z ⟶ X =>
      (spacesBaseChange B S hS (yonedaSpaceHom k)).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))) e)

/-- The inverse comparison of `AlgebraicGeometry.Space.spacesPushforwardFactoredComp`. -/
def spacesPushforwardFactoredCompInv (p : Y ⟶ X) (q : Z ⟶ Y) (Q : Z ⟶ X) (e : q ≫ p = Q) :
    (spacesBaseChange B S hS (yonedaSpaceHom Q)).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) ⟶
    (spacesBaseChange B S hS (yonedaSpaceHom q)).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) ⋙
      (spacesBaseChange B S hS (yonedaSpaceHom p)).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Y)) :=
  eqToHom (congrArg (fun k : Z ⟶ X =>
      (spacesBaseChange B S hS (yonedaSpaceHom k)).functor.sheafPushforwardContinuous
        A (SpacesEtale.topology B S hS (yonedaSpace B S hS X))
        (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))) e.symm) ≫
    eqToHom (spacesPushforward_yonedaSpaceHom_comp A p q) ≫
    (spacesBaseChange_pushforward_comp_anyCoefficients B S hS (yonedaSpaceHom q) (yonedaSpaceHom p)
        A).inv

/-- **The comparison of direct images along a factorised composite, at one sheaf.** For a
factorisation `q ≫ p = Q` of the site, the comparisons along `p` and along `q`, followed by the
bounded composition comparison through `Q`, are the spaces-étale comparison through `Q`
followed by the comparison along `Q`. -/
theorem representedPushforwardIso_factoredComp_app_assoc (p : Y ⟶ X) (q : Z ⟶ Y) (Q : Z ⟶ X)
    (e : q ≫ p = Q) (hQ : q.left ≫ p.left = Q.left)
    (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : ((associatedBigEtaleSite B).smallPushforward Q.left A).obj
      ((representedRestriction Z A).obj M) ⟶ N) :
    (representedPushforwardIso p A).hom.app
        (((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.sheafPushforwardContinuous
          A (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
          (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M) ≫
      ((associatedBigEtaleSite B).smallPushforward p.left A).map
        ((representedPushforwardIso q A).hom.app M) ≫
      (SmallEtale.boundedPushforwardCompIso (associatedBigEtaleSite B) A q.left
        p.left Q.left hQ).hom.app ((representedRestriction Z A).obj M) ≫ k =
    (representedRestriction X A).map ((spacesPushforwardFactoredComp A p q Q e).app M) ≫
      (representedPushforwardIso Q A).hom.app M ≫ k := by
  subst e
  rewrite [SmallEtale.boundedPushforwardCompIso_hom_app, Category.assoc,
    eqToHom_smallPushforward_comp_left_app_comp A p q hQ,
    smallPushforward_map_eq_sheafPushforwardContinuous_map,
    representedPushforwardIso_comp_app'_assoc A p q M, spacesPushforwardFactoredComp, eqToHom_refl,
    Category.comp_id, NatTrans.comp_app]
  rfl

/-- **The inverse comparison of direct images along a factorised composite, at one sheaf.** -/
theorem representedPushforwardIso_factoredCompInv_app_assoc (p : Y ⟶ X) (q : Z ⟶ Y)
    (Q : Z ⟶ X) (e : q ≫ p = Q) (hQ : q.left ≫ p.left = Q.left)
    (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : ((associatedBigEtaleSite B).smallPushforward p.left A).obj
      (((associatedBigEtaleSite B).smallPushforward q.left A).obj
        ((representedRestriction Z A).obj M)) ⟶ N) :
    (representedPushforwardIso Q A).hom.app M ≫
      (SmallEtale.boundedPushforwardCompIso (associatedBigEtaleSite B) A q.left
        p.left Q.left hQ).inv.app ((representedRestriction Z A).obj M) ≫ k =
    (representedRestriction X A).map
        ((spacesPushforwardFactoredCompInv A p q Q e).app M) ≫
      (representedPushforwardIso p A).hom.app
        (((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.sheafPushforwardContinuous
          A (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
          (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M) ≫
      ((associatedBigEtaleSite B).smallPushforward p.left A).map
        ((representedPushforwardIso q A).hom.app M) ≫ k := by
  subst e
  rewrite [SmallEtale.boundedPushforwardCompIso_inv_app, Category.assoc,
    eqToHom_smallPushforward_comp_left_symm_app_comp A p q hQ,
    representedPushforwardIso_comp_app_assoc A p q M,
    smallPushforward_map_eq_sheafPushforwardContinuous_map, spacesPushforwardFactoredCompInv,
    eqToHom_refl, Category.id_comp, NatTrans.comp_app]
  rfl

/-- The bounded direct image of the comparison along `q`, followed by that of its inverse, is
the identity, after any morphism. -/
theorem representedPushforwardIso_map_hom_map_inv (p : Y ⟶ X) (q : Z ⟶ Y)
    (M : Sheaf (SpacesEtale.topology B S hS (yonedaSpace B S hS Z)) A)
    {N : Sheaf (representedSchemeTopology B S hS X) A}
    (k : N ⟶ ((associatedBigEtaleSite B).smallPushforward p.left A).obj
      ((representedRestriction Y A).obj
        (((spacesBaseChange B S hS (yonedaSpaceHom q)).functor.sheafPushforwardContinuous
          A (SpacesEtale.topology B S hS (yonedaSpace B S hS Y))
          (SpacesEtale.topology B S hS (yonedaSpace B S hS Z))).obj M))) :
    k ≫ ((associatedBigEtaleSite B).smallPushforward p.left A).map
        ((representedPushforwardIso q A).hom.app M) ≫
      ((associatedBigEtaleSite B).smallPushforward p.left A).map
        ((representedPushforwardIso q A).inv.app M) = k := by
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  exact (congrArg (k ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id k)

end Factored

/-! ### The base change maps -/

section BaseChange

variable {V W V' W' : BigFppfOver B S hS} (m : W ⟶ V) (n : V' ⟶ V) (n' : W' ⟶ W)
  (m' : W' ⟶ V')

/-- The comparison of the two composite spaces-étale direct images around a commutative square
is the composite of the two comparisons through a common diagonal `Q`. -/
theorem spacesPushforwardCompSquare_eq_factoredComp (Q : W' ⟶ V) (e₁ : n' ≫ m = Q)
    (e₂ : m' ≫ n = Q)
    (w : yonedaSpaceHom n' ≫ yonedaSpaceHom m = yonedaSpaceHom m' ≫ yonedaSpaceHom n) :
    spacesPushforwardCompSquare_anyCoefficients B S hS (yonedaSpaceHom n') (yonedaSpaceHom m')
        (yonedaSpaceHom m) (yonedaSpaceHom n) w A =
      spacesPushforwardFactoredComp A m n' Q e₁ ≫ spacesPushforwardFactoredCompInv A n m' Q e₂ := by
  rewrite [spacesPushforwardCompSquare_anyCoefficients, spacesPushforwardFactoredComp,
    spacesPushforwardFactoredCompInv, Category.assoc, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans_assoc, eqToHom_trans_assoc]
  rfl

/-- **The comparison of the two composite direct images corresponds under the chart
restrictions**, as an equation of 2-squares: the bounded comparison through a diagonal `Q` of the
square, pasted with the comparisons of direct images along `n'`, `m` and `m'`, is the
spaces-étale comparison pasted with the comparison along `n`. This is the cube identity of
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq` for the two base change maps. -/
theorem representedPushforwardCube (Q : W' ⟶ V) (e₁ : n' ≫ m = Q) (e₂ : m' ≫ n = Q)
    (hQ₁ : n'.left ≫ m.left = Q.left) (hQ₂ : m'.left ≫ n.left = Q.left)
    (w : yonedaSpaceHom n' ≫ yonedaSpaceHom m = yonedaSpaceHom m' ≫ yonedaSpaceHom n) :
    ((TwoSquare.mk _ _ _ _ (representedPushforwardIso n' A).hom ≫ᵥ
        SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite B) A m.left n.left
          n'.left m'.left Q.left hQ₁ hQ₂).whiskerRight
        (representedPushforwardIso m A).hom).whiskerLeft (representedPushforwardIso m'
            A).inv =
      TwoSquare.mk _ _ _ _ (spacesPushforwardCompSquare_anyCoefficients B S hS (yonedaSpaceHom n')
        (yonedaSpaceHom m') (yonedaSpaceHom m) (yonedaSpaceHom n) w A) ≫ᵥ
        TwoSquare.mk _ _ _ _ (representedPushforwardIso n A).hom := by
  refine TwoSquare.ext _ _ fun M => ?_
  rewrite [SmallEtale.ts_whiskerLeft_app, SmallEtale.ts_whiskerRight_app, SmallEtale.ts_vComp_app,
    SmallEtale.ts_vComp_app, TwoSquare.mk_natTrans_app, TwoSquare.mk_natTrans_app,
    TwoSquare.mk_natTrans_app, TwoSquare.mk_natTrans_app,
    SmallEtale.boundedBaseChangeMate_natTrans_app, Category.assoc, Category.assoc, Category.assoc,
    representedPushforwardIso_factoredComp_app_assoc A m n' Q e₁ hQ₁ M,
    representedPushforwardIso_factoredCompInv_app_assoc A n m' Q e₂ hQ₂ M,
    representedPushforwardIso_map_hom_map_inv, ← Functor.map_comp_assoc, ← NatTrans.comp_app,
    ← spacesPushforwardCompSquare_eq_factoredComp A m n n' m' Q e₁ e₂ w]
  rfl

/-- **The base change map of a square of represented algebraic spaces is the scheme one.** For
a commutative square `n' ≫ m = m' ≫ n` of the big fppf site whose image under the Yoneda embedding
is cartesian, the spaces-étale base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of the square of represented
algebraic spaces is invertible if and only if the base change map of sheaves of sets on the
bounded small étale sites of the underlying schemes is. -/
theorem isIso_spacesToposBaseChangeSquare_iff (h : n' ≫ m = m' ≫ n)
    (sq : IsPullback (yonedaSpaceHom n') (yonedaSpaceHom m') (yonedaSpaceHom m)
      (yonedaSpaceHom n)) :
    IsIso (spacesToposBaseChangeSquare B S hS (yonedaSpaceHom n') (yonedaSpaceHom m')
        (yonedaSpaceHom m) (yonedaSpaceHom n) sq) ↔
      IsIso (smallEtaleBaseChangeNatTrans.{u} (associatedBigEtaleSite B) n'.left m'.left
        m.left n.left (congrArg (fun k : W' ⟶ V => k.left) h)) := by
  have hQ₁ : n'.left ≫ m.left = (n' ≫ m).left := (Over.comp_left _ _ _ n' m).symm
  have hQ₂ : m'.left ≫ n.left = (n' ≫ m).left :=
    (Over.comp_left _ _ _ m' n).symm.trans (congrArg (fun k : W' ⟶ V => k.left) h.symm)
  rw [SmallEtale.isIso_smallEtaleBaseChangeNatTrans_iff_boundedBaseChangeMate
    (associatedBigEtaleSite B) m.left n.left n'.left m'.left _ hQ₁ hQ₂]
  let adj₁ := spacesToposAdjunction B S hS (yonedaSpaceHom n')
  let adj₂ := spacesToposAdjunction B S hS (yonedaSpaceHom n)
  let adj₁' := (associatedBigEtaleSite B).smallPullbackAdjunction n'.left (Type (u + 1))
  let adj₂' := (associatedBigEtaleSite B).smallPullbackAdjunction n.left (Type (u + 1))
  let τ₁ := (mateEquiv adj₁ adj₁').symm (TwoSquare.mk _ _ _ _ (representedPushforwardIso n'
      (Type (u + 1))).hom)
  let τ₂ := (mateEquiv adj₂ adj₂').symm (TwoSquare.mk _ _ _ _ (representedPushforwardIso n
      (Type (u + 1))).hom)
  have hτ : ∀ {V W : BigFppfOver B S hS} (p : W ⟶ V),
      IsIso ((mateEquiv (spacesToposAdjunction B S hS (yonedaSpaceHom p))
        ((associatedBigEtaleSite B).smallPullbackAdjunction p.left (Type (u + 1)))).symm
        (TwoSquare.mk _ _ _ _ (representedPushforwardIso p (Type (u + 1))).hom)).natTrans :=
    fun p => @CategoryTheory.isIso_mateEquiv_symm_of_isEquivalence
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (representedRestriction_isEquivalence _ _)
      (representedRestriction_isEquivalence _ _) _ (representedPushforwardIso p _).isIso_hom
  have : IsIso τ₁.natTrans := hτ n'
  have : IsIso τ₂.natTrans := hτ n
  have hcube : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ
      SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite B) (Type (u + 1)) m.left n.left
          n'.left m'.left (n' ≫ m).left hQ₁ hQ₂).whiskerRight
        (representedPushforwardIso m (Type (u + 1))).hom).whiskerLeft (representedPushforwardIso m'
            (Type (u + 1))).inv =
      TwoSquare.mk _ _ _ _ (spacesPushforwardCompSquare_anyCoefficients B S hS (yonedaSpaceHom n')
        (yonedaSpaceHom m') (yonedaSpaceHom m) (yonedaSpaceHom n) sq.w (Type (u + 1))) ≫ᵥ
        mateEquiv adj₂ adj₂' τ₂ := by
    rewrite [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact representedPushforwardCube (Type (u + 1)) m n n' m' (n' ≫ m) rfl h.symm hQ₁ hQ₂ sq.w
  constructor
  · intro hfront
    have hfront' : IsIso ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _
        (spacesPushforwardCompSquare_anyCoefficients B S hS (yonedaSpaceHom n') (yonedaSpaceHom m')
          (yonedaSpaceHom m) (yonedaSpaceHom n) sq.w (Type (u + 1))))).natTrans := hfront
    have := representedRestriction_isEquivalence W (Type (u + 1))
    have key : ∀ {C D E F C' D' E' F' : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
          [Category.{u + 1} E] [Category.{u + 1} F] [Category.{u + 1} C'] [Category.{u + 1} D']
          [Category.{u + 1} E'] [Category.{u + 1} F']
          {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
          {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
          {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
          {ΦC : C ⥤ C'} {ΦD : D ⥤ D'} {ΦE : E ⥤ E'} {ΦF : F ⥤ F'}
          (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
          (τ₁ : TwoSquare ΦC L₁ L₁' ΦD) (τ₂ : TwoSquare ΦE L₂ L₂' ΦF)
          (σG : G ⋙ ΦE ⟶ ΦC ⋙ G') (σH : ΦD ⋙ H' ⟶ H ⋙ ΦF)
          (β : TwoSquare R₁ H G R₂) (β' : TwoSquare R₁' H' G' R₂') (hΦ : ΦC.EssSurj)
          (hτ₁ : IsIso τ₁.natTrans) (hτ₂ : IsIso τ₂.natTrans) (hσG : IsIso σG) (hσH : IsIso σH)
          (hβ : IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans)
          (_ : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
            β ≫ᵥ mateEquiv adj₂ adj₂' τ₂),
          IsIso ((mateEquiv adj₁' adj₂').symm β').natTrans := by
        intro C D E F C' D' E' F' _ _ _ _ _ _ _ _ L₁ R₁ L₂ R₂ L₁' R₁' L₂' R₂' G H G' H' ΦC ΦD ΦE ΦF
          adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' hΦ hτ₁ hτ₂ hσG hσH hβ h
        have := hΦ; have := hτ₁; have := hτ₂; have := hσG; have := hσH
        have hl : IsIso ((mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂).natTrans := by
          rw [NatTrans.isIso_iff_isIso_app]
          intro c
          have e : ((mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂).natTrans.app c =
              τ₂.natTrans.app (G.obj c) ≫
                ΦF.map (((mateEquiv adj₁ adj₂).symm β).natTrans.app c) := by
            simp [TwoSquare.hComp]
          rw [e]
          infer_instance
        rw [Stacks.CategoryTheory.mateEquiv_symm_hComp_eq adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h]
          at hl
        have hw : IsIso (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans := by
          generalize τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β' = w at hl ⊢
          have : IsIso ((Functor.whiskerRight σG L₂' ≫ w.natTrans) ≫ Functor.whiskerLeft L₁ σH) :=
            hl
          have : IsIso (Functor.whiskerRight σG L₂' ≫ w.natTrans) :=
            IsIso.of_isIso_comp_right _ (Functor.whiskerLeft L₁ σH)
          exact IsIso.of_isIso_comp_left (Functor.whiskerRight σG L₂') w.natTrans
        rw [NatTrans.isIso_iff_isIso_app]
        intro d
        obtain ⟨c, ⟨e⟩⟩ : ∃ c, Nonempty (ΦC.obj c ≅ d) :=
          ⟨ΦC.objPreimage d, ⟨ΦC.objObjPreimageIso d⟩⟩
        have hc : IsIso (((mateEquiv adj₁' adj₂').symm β').natTrans.app (ΦC.obj c)) := by
          have := NatIso.isIso_app_of_isIso (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans c
          have e' : (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans.app c =
              ((mateEquiv adj₁' adj₂').symm β').natTrans.app (ΦC.obj c) ≫
                H'.map (τ₁.natTrans.app c) := by
            simp [TwoSquare.hComp]
          rw [e'] at this
          exact IsIso.of_isIso_comp_right _ (H'.map (τ₁.natTrans.app c))
        have nat := ((mateEquiv adj₁' adj₂').symm β').natTrans.naturality e.hom
        have h₂ : ((mateEquiv adj₁' adj₂').symm β').natTrans.app d =
            inv ((G' ⋙ L₂').map e.hom) ≫ ((mateEquiv adj₁' adj₂').symm β').natTrans.app (ΦC.obj c) ≫
              (L₁' ⋙ H').map e.hom := by
          rw [← nat]
          simp
        rw [h₂]
        infer_instance
    exact key adj₁ adj₂ adj₁' adj₂' τ₁ τ₂
      (representedPushforwardIso m (Type (u + 1))).hom (representedPushforwardIso m'
          (Type (u + 1))).inv _ _ inferInstance ‹_› ‹_› inferInstance inferInstance hfront' hcube
  · intro hback
    have := representedRestriction_isEquivalence V' (Type (u + 1))
    exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms adj₁ adj₂ adj₁' adj₂'
      τ₁ τ₂ (representedPushforwardIso m (Type (u + 1))).hom (representedPushforwardIso m'
          (Type (u + 1))).inv _ _ hcube

end BaseChange

end AlgebraicGeometry.Space

end
