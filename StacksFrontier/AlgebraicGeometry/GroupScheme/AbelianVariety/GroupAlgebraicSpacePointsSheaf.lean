module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.GroupAlgebraicSpace

/-!
# The sheaf of points of a constant group algebraic space on the site of an object

Let `k` be a field, let `A` be a commutative group scheme over `Spec k` lying in a big fppf site,
and let `G` be the commutative group algebraic space over `Spec k` attached to it (Stacks 043I,
`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupScheme`). For an object `U` of the big fppf
site of `Spec k` with scheme `W`, the restriction of the abelian sheaf of points of `G` to the
big fppf site of `W` (`AlgebraicGeometry.Space.pointsSheafOnObjScheme`) is the abelian sheaf of
points of the base change `A_W = A ×_{Spec k} W` (`AlgebraicGeometry.pointsSheaf`): a point of
`G` over `V → W` is a morphism `V ⟶ A` over `Spec k`, that is, a morphism `V ⟶ A_W` over `W`.

## Main definitions

* `CategoryTheory.Over.mapPullbackAdjGrpObjHomMulEquiv`: the adjunction between `Over.map f` and
  `Over.pullback f` on morphisms into a group object, as an isomorphism of groups.
* `Stacks.Cohomology.Torsors.AbelianTorsor.transportIso`: a torsor under an abelian sheaf, read
  under an isomorphic abelian sheaf.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsBaseChangeMulEquiv`: the sections of `G`
  over an object `V` of the site of `W` are the points of `A_W` over `V`.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsSheafOnObjSchemeIso`: **the restriction of
  the sheaf of points of `G` to the site of `W` is the sheaf of points of `A_W`**.
* `AlgebraicGeometry.Space.TorsorObj.baseChangeTorsor`: the torsor of an fppf `G`-torsor over
  `U`, read as a torsor under the sheaf of points of `A_W`.

## Main results

* `Stacks.Cohomology.Torsors.hMap_torsorIsoClassesEquivH1_transportIso`: the map on `H¹` of an
  isomorphism of abelian sheaves carries the class of a torsor to the class of the transported
  torsor (from Stacks 03AJ, naturality in the coefficients).
* `AlgebraicGeometry.Space.TorsorObj.hMap_pointsSheafOnObjSchemeIso_objSchemeTorsor`: the
  isomorphism of coefficient sheaves carries the class of the torsor carried to the site of
  `W` to the class of `AlgebraicGeometry.Space.TorsorObj.baseChangeTorsor`.
* `AlgebraicGeometry.Space.TorsorObj.hMap_hAddEquiv_h1Class`: the class in `H¹(U, G)` of an
  fppf `G`-torsor over `U`, read in `H¹(W, A_W)`, is the class of
  `AlgebraicGeometry.Space.TorsorObj.baseChangeTorsor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj CategoryTheory.Obj

universe w t v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

attribute [local instance] cartesianMonoidalCategory

/-- **The adjunction `Over.map f ⊣ Over.pullback f` on points of a group object.** For
`f : X ⟶ Y`, an object `Z` over `X` and a group object `A` over `Y`, the morphisms
`Z ⟶ f^* A` over `X` are the morphisms `f_! Z ⟶ A` over `Y`, as groups: the pullback functor
preserves finite products, so it carries the group law of `A` to that of `f^* A`. This is
the form for a group structure given as an instance on `A`; for a bundled `Grp (Over Y)` see
`CategoryTheory.Over.mapPullbackAdjHomMulEquiv`. -/
def mapPullbackAdjGrpObjHomMulEquiv {X Y : C} (f : X ⟶ Y) (Z : Over X) (A : Over Y) [GrpObj A] :
    ((Over.map f).obj Z ⟶ A) ≃* (Z ⟶ (Over.pullback f).obj A) where
  toEquiv := (Over.mapPullbackAdj f).homEquiv Z A
  map_mul' g h := by
    change (Over.mapPullbackAdj f).homEquiv Z A (g * h) =
      (Over.mapPullbackAdj f).homEquiv Z A g * (Over.mapPullbackAdj f).homEquiv Z A h
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]

theorem mapPullbackAdjGrpObjHomMulEquiv_apply {X Y : C} (f : X ⟶ Y) (Z : Over X) (A : Over Y)
    [GrpObj A] (g : (Over.map f).obj Z ⟶ A) :
    mapPullbackAdjGrpObjHomMulEquiv f Z A g = (Over.mapPullbackAdj f).homEquiv Z A g :=
  rfl

end CategoryTheory.Over

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An isomorphism of abelian sheaves identifies the sections of the two sheaves read as
sheaves of multiplicatively written groups. -/
def sectionEquivOfIso {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ≅ H') :
    SheafOfGroups.SectionEquiv (abelianSheafAsGroupSheaf H) (abelianSheafAsGroupSheaf H') where
  equiv V := ((sheafToPresheaf J _).mapIso φ).app V |>.addCommGroupIsoToAddEquiv
    |>.toMultiplicative |>.toEquiv
  map_mul V g h := map_mul (((sheafToPresheaf J _).mapIso φ).app V
    |>.addCommGroupIsoToAddEquiv |>.toMultiplicative) g h
  naturality f g := NatTrans.naturality_apply φ.hom.hom f g

/-- **A torsor under an abelian sheaf, read under an isomorphic abelian sheaf.** For an
isomorphism `φ : H ≅ H'`, a section of `H'` acts on a torsor under `H` as the section of `H` it
is identified with. -/
def AbelianTorsor.transportIso {H H' : Sheaf J AddCommGrpCat.{t}} (φ : H ≅ H')
    (F : AbelianTorsor H) : AbelianTorsor H' :=
  ⟨F.1.transport (sectionEquivOfIso φ).symm,
    PseudoTorsor.transport_isTorsor _ _ F.2⟩

variable [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- **The class of a transported torsor.** The map on first cohomology induced by an
isomorphism `φ : H ≅ H'` of abelian sheaves carries the class of a torsor under `H` to the
class of the same torsor read under `H'`. -/
theorem hMap_torsorIsoClassesEquivH1_transportIso {H H' : Sheaf J AddCommGrpCat.{t}}
    (φ : H ≅ H') (F : AbelianTorsor H) :
    Sheaf.H.map φ.hom 1 (torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) F)) =
      torsorIsoClassesEquivH1 H' (Quotient.mk (torsorSetoid H') (F.transportIso φ)) :=
  torsorIsoClassesEquivH1_naturality φ.hom F (F.transportIso φ) (𝟙 _) fun U h s => by
    change F.1.act U (Multiplicative.ofAdd h) s =
      F.1.act U (Multiplicative.ofAdd (φ.inv.hom.app U (φ.hom.hom.app U h))) s
    rw [show φ.inv.hom.app U (φ.hom.hom.app U h) = h from
      congrArg (fun m : H ⟶ H => m.hom.app U h) φ.hom_inv_id]

end Stacks.Cohomology.Torsors

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {k : Type u} [Field k] {hk : 𝒞.Contains (Spec (.of k))}

namespace GroupAlgebraicSpace

variable (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] (hA : 𝒞.Contains A.left)
  (U : BigFppfOver 𝒞 (Spec (.of k)) hk)

/-- **The sections of `G` over an object of the site of `W` are the points of `A_W`.** For an
object `V` of the big fppf site of the scheme `W` of `U`, the sections of the group algebraic
space `G` of `A` over `V`, read over `Spec k`, are the morphisms `V ⟶ A` over `Spec k`, that is,
the morphisms `V ⟶ A_W` over `W`. -/
def pointsBaseChangeMulEquiv
    (V : BigFppfOver 𝒞 (BigFppfOver.objScheme 𝒞 _ hk U)
      (BigFppfOver.contains_objScheme 𝒞 _ hk U)) :
    (ofGroupScheme (hS := hk) A hA).Sections
        ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj V).left ≃*
      ((Over.post 𝒞.inclusion).obj V ⟶
        groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk U)) :=
  ((sectionsMulEquiv _ _).trans (pointsMulEquiv 𝒞 _ hk (baseS 𝒞 _ hk) _ _ _)).trans
    (Over.mapPullbackAdjGrpObjHomMulEquiv (BigFppfOver.objHom 𝒞 _ hk U)
      ((Over.post 𝒞.inclusion).obj V) A)

/-- `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsBaseChangeMulEquiv` takes a section to
the point of `A_W` adjoint to its component in `A`. -/
theorem pointsBaseChangeMulEquiv_apply
    (V : BigFppfOver 𝒞 (BigFppfOver.objScheme 𝒞 _ hk U)
      (BigFppfOver.contains_objScheme 𝒞 _ hk U))
    (s : (ofGroupScheme (hS := hk) A hA).Sections
      ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj V).left) :
    pointsBaseChangeMulEquiv A hA U V s =
      (Over.mapPullbackAdj (BigFppfOver.objHom 𝒞 _ hk U)).homEquiv
        ((Over.post 𝒞.inclusion).obj V) A
        ((prod.snd : baseS 𝒞 _ hk ⨯ (pointsOnSite 𝒞 _ hk (groupSchemeObj 𝒞 _ hk A hA)
          (inferInstanceAs (GrpObj A)) ⋙ forget GrpCat) ⟶ _).app _ s) := by
  change (Over.mapPullbackAdj (BigFppfOver.objHom 𝒞 _ hk U)).homEquiv
        ((Over.post 𝒞.inclusion).obj V) A
    (yonedaEquiv (yonedaEquiv.symm s ≫ prod.snd)) = _
  exact congrArg _ ((yonedaEquiv_comp _ _).trans (congrArg _ (Equiv.apply_symm_apply _ _)))

/-- `AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsBaseChangeMulEquiv` is natural: restricting
a section along a morphism `g` of the site of `W` restricts the point of `A_W` along `g`. -/
theorem pointsBaseChangeMulEquiv_naturality
    {V₁ V₂ : BigFppfOver 𝒞 (BigFppfOver.objScheme 𝒞 _ hk U)
      (BigFppfOver.contains_objScheme 𝒞 _ hk U)} (g : V₂ ⟶ V₁)
    (s : (ofGroupScheme (hS := hk) A hA).Sections
      ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.obj V₁).left) :
    pointsBaseChangeMulEquiv A hA U V₂
        ((ofGroupScheme (hS := hk) A hA).obj.X.left.map
          ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.map g).left.op s) =
      (Over.post 𝒞.inclusion).map g ≫ pointsBaseChangeMulEquiv A hA U V₁ s := by
  have key : (Over.map (BigFppfOver.objHom 𝒞 _ hk U)).map ((Over.post 𝒞.inclusion).map g) =
      (toSchemeOver 𝒞 _ hk).map ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.map g).left :=
    rfl
  refine ((pointsBaseChangeMulEquiv_apply A hA U V₂ _).trans ?_).trans
    (congrArg _ (pointsBaseChangeMulEquiv_apply A hA U V₁ s)).symm
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_left
    (Over.mapPullbackAdj (BigFppfOver.objHom 𝒞 _ hk U)) ((Over.post 𝒞.inclusion).map g) _)
  rw [key]
  exact congrArg _ (NatTrans.naturality_apply (prod.snd : baseS 𝒞 _ hk ⨯
    (pointsOnSite 𝒞 _ hk (groupSchemeObj 𝒞 _ hk A hA) (inferInstanceAs (GrpObj A)) ⋙
      forget GrpCat) ⟶ _) ((BigFppfOver.objEquiv 𝒞 _ hk U).functor.map g).left.op s)

/-- **The restriction of the sheaf of points of `G` to the site of `W` is the sheaf of points of
`A_W`.** For an object `U` of the big fppf site of `Spec k` with scheme `W`, the abelian sheaf of
points of the group algebraic space `G` of `A`, restricted to the big fppf site of `W`, is the
abelian sheaf of points of the base change `A_W` of `A` to `W`, sectionwise by
`AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsBaseChangeMulEquiv`. -/
def pointsSheafOnObjSchemeIso
    (hAW : 𝒞.Contains (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk U)).left) :
    pointsSheafOnObjScheme (ofGroupScheme (hS := hk) A hA) U ≅
      AlgebraicGeometry.pointsSheaf 𝒞 (BigFppfOver.objScheme 𝒞 _ hk U)
        (BigFppfOver.contains_objScheme 𝒞 _ hk U)
        (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk U)) hAW :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun V => (pointsBaseChangeMulEquiv A hA U V.unop).toAdditive.toAddCommGrpIso)
      (by
        intro V₁ V₂ φ
        ext s
        exact pointsBaseChangeMulEquiv_naturality A hA U φ.unop s))

end GroupAlgebraicSpace

namespace TorsorObj

open Stacks.Cohomology.Torsors

variable {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] {hA : 𝒞.Contains A.left}
  (T : TorsorObj (isAlgebraicSpace_baseS 𝒞 _ hk) (GroupAlgebraicSpace.ofGroupScheme A hA))
  (hAW : 𝒞.Contains (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk T.U)).left)

/-- **The torsor of an fppf `G`-torsor over `U`, under the sheaf of points of `A_W`**: the torsor
`AlgebraicGeometry.Space.TorsorObj.objSchemeTorsor` on the big fppf site of the scheme `W` of
`U`, read under the sheaf of points of the base change `A_W` through
`AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsSheafOnObjSchemeIso`. -/
def baseChangeTorsor :
    AbelianTorsor (AlgebraicGeometry.pointsSheaf 𝒞 (BigFppfOver.objScheme 𝒞 _ hk T.U)
      (BigFppfOver.contains_objScheme 𝒞 _ hk T.U)
      (groupSchemeBaseChange A (BigFppfOver.objHom 𝒞 _ hk T.U)) hAW) :=
  T.objSchemeTorsor.transportIso (GroupAlgebraicSpace.pointsSheafOnObjSchemeIso A hA T.U hAW)

variable [HasSheafify (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk T.U)
    (BigFppfOver.contains_objScheme 𝒞 _ hk T.U)) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk T.U)
    (BigFppfOver.contains_objScheme 𝒞 _ hk T.U)) AddCommGrpCat.{u})]

/-- The isomorphism of coefficient sheaves
`AlgebraicGeometry.Space.GroupAlgebraicSpace.pointsSheafOnObjSchemeIso` carries the class of the
torsor carried to the site of `W` to the class of the torsor under the sheaf of points of
`A_W`. -/
theorem hMap_pointsSheafOnObjSchemeIso_objSchemeTorsor :
    Sheaf.H.map (GroupAlgebraicSpace.pointsSheafOnObjSchemeIso A hA T.U hAW).hom 1
        (torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) T.objSchemeTorsor)) =
      torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) (T.baseChangeTorsor hAW)) :=
  hMap_torsorIsoClassesEquivH1_transportIso _ _

variable [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasSheafify ((BigFppfOver.topology 𝒞 _ hk).over U) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 (Spec (.of k)) hk,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 _ hk).over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞 (BigFppfOver.objScheme 𝒞 _ hk T.U)
    (BigFppfOver.contains_objScheme 𝒞 _ hk T.U)) AddCommGrpCat.{u})]

/-- **The class of an fppf `G`-torsor over `U`, read in `H¹(W, A_W)`.** The comparison of
cohomology along the equivalence of sites `(Sch/W)_fppf ≌ (Sch/Spec k)_fppf / U` (Stacks 00XU),
followed by the isomorphism of the sheaf of points of `G` restricted to `(Sch/W)_fppf` with the
sheaf of points of `A_W`, carries the class of the torsor to the class of
`AlgebraicGeometry.Space.TorsorObj.baseChangeTorsor`. -/
theorem hMap_hAddEquiv_h1Class :
    Sheaf.H.map (GroupAlgebraicSpace.pointsSheafOnObjSchemeIso A hA T.U hAW).hom 1
        (Stacks.Cohomology.DenseSubsite.hAddEquiv _ _ (BigFppfOver.objEquiv 𝒞 _ hk T.U).functor
          ((GroupAlgebraicSpace.pointsSheaf (GroupAlgebraicSpace.ofGroupScheme A hA)).over T.U)
          1 T.h1Class) =
      torsorIsoClassesEquivH1 _ (Quotient.mk (torsorSetoid _) (T.baseChangeTorsor hAW)) := by
  rw [hAddEquiv_h1Class, hMap_pointsSheafOnObjSchemeIso_objSchemeTorsor]

end TorsorObj

end AlgebraicGeometry.Space
