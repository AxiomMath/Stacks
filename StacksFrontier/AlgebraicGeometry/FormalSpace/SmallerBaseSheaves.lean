module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseCharts
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Large-valued sheaves over a smaller base, as sheaves over a representable sheaf

Let `g : V ⟶ S` be a morphism of a big fppf site `B`.
`AlgebraicGeometry.FormalSpace.smallerBaseSheafEquivalence` identifies the fppf sheaves with
values in `Type (u + 1)` on the big fppf site of `V` with the presheaves on the big fppf site of
`S` over the universe-lifted representable presheaf of `g` whose underlying presheaf is a sheaf.
This file rephrases that as an equivalence with the slice of the category of fppf sheaves on the
big fppf site of `S` over the representable sheaf of `g`, and records what the resulting functor
to fppf sheaves on the big fppf site of `S` preserves.

## Main definitions

* `AlgebraicGeometry.FormalSpace.smallerBaseTarget`: the representable sheaf of `g`.
* `AlgebraicGeometry.FormalSpace.smallerBaseOverEquivalence`: fppf sheaves on the big fppf site
  of `V` are fppf sheaves on the big fppf site of `S` over the representable sheaf of `g`.
* `AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor`: the resulting functor to fppf sheaves
  on the big fppf site of `S`.
* `AlgebraicGeometry.FormalSpace.smallerBaseYonedaIso`: on representable sheaves the
  equivalence is the slice of the Yoneda embedding.

## Main results

* The functor `AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor` preserves colimits and
  fibre products, and preserves and reflects epimorphisms.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

attribute [local instance] bigFppfOver_subcanonical

/-- The universe-lifted representable sheaf of `g : V ⟶ S`, an fppf sheaf on the big fppf site
of `S`, the big fppf topology being subcanonical. -/
abbrev smallerBaseTarget : FppfSheaf B S hS :=
  (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (Over.mk g)

/-- The presheaves over the universe-lifted representable presheaf of `g` whose underlying
presheaf is a sheaf are the fppf sheaves over the representable sheaf of `g`. -/
def sheavesOverSmallerBaseEquivalence :
    SheavesOverSmallerBase B V S hV hS g ≌ Over (smallerBaseTarget B V S hV hS g) where
  functor :=
    { obj X := Over.mk (ObjectProperty.homMk X.obj.hom :
        (⟨X.obj.left, X.property⟩ : FppfSheaf B S hS) ⟶ smallerBaseTarget B V S hV hS g)
      map f := Over.homMk (ObjectProperty.homMk f.hom.left)
        (ObjectProperty.hom_ext _ (Over.w f.hom)) }
  inverse :=
    { obj Y := ⟨Over.mk Y.hom.hom, Y.left.property⟩
      map f := ObjectProperty.homMk (Over.homMk f.left.hom
        (congrArg (fun k => k.hom) (Over.w f))) }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- **Large-valued sheaves over a smaller base, as sheaves over a representable sheaf.** Fppf
sheaves with values in `Type (u + 1)` on the big fppf site of `V` are the same thing as such
sheaves on the big fppf site of `S` over the representable sheaf of `g : V ⟶ S`. -/
def smallerBaseOverEquivalence : FppfSheaf B V hV ≌ Over (smallerBaseTarget B V S hV hS g) :=
  (smallerBaseSheafEquivalence B V S hV hS g).trans
    (sheavesOverSmallerBaseEquivalence B V S hV hS g)

/-- The fppf sheaf on the big fppf site of `S` attached to an fppf sheaf on the big fppf site of
`V`: its sections over `T` are the factorizations `φ : T ⟶ (V ⟶ S)` together with a section over
`T →φ V`. -/
abbrev smallerBaseSheafFunctor : FppfSheaf B V hV ⥤ FppfSheaf B S hS :=
  (smallerBaseOverEquivalence B V S hV hS g).functor ⋙ Over.forget _

/-- The structural morphism of the attached sheaf to the representable sheaf of `g`. -/
abbrev smallerBaseStr (G : FppfSheaf B V hV) :
    (smallerBaseSheafFunctor B V S hV hS g).obj G ⟶ smallerBaseTarget B V S hV hS g :=
  ((smallerBaseOverEquivalence B V S hV hS g).functor.obj G).hom

/-- The attached sheaf has the attached presheaf as underlying presheaf. -/
theorem smallerBaseSheafFunctor_obj_obj (G : FppfSheaf B V hV) :
    ((smallerBaseSheafFunctor B V S hV hS g).obj G).obj = smallerBaseULift B V S hV hS g G.obj :=
  rfl

/-- The attached morphism of sheaves has the attached morphism of presheaves as underlying
morphism. -/
theorem smallerBaseSheafFunctor_map_hom {G G' : FppfSheaf B V hV} (f : G ⟶ G') :
    ((smallerBaseSheafFunctor B V S hV hS g).map f).hom =
      smallerBaseULiftMap B V S hV hS g f.hom :=
  rfl

/-- The structural morphism of the attached sheaf has the structural morphism of the attached
presheaf as underlying morphism. -/
theorem smallerBaseStr_hom (G : FppfSheaf B V hV) :
    (smallerBaseStr B V S hV hS g G).hom = smallerBaseULiftHom B V S hV hS g G.obj :=
  rfl

/-- Attached morphisms are compatible with the structural morphisms. -/
@[reassoc (attr := simp)]
theorem smallerBaseSheafFunctor_map_comp_str {G G' : FppfSheaf B V hV} (f : G ⟶ G') :
    (smallerBaseSheafFunctor B V S hV hS g).map f ≫ smallerBaseStr B V S hV hS g G' =
      smallerBaseStr B V S hV hS g G :=
  Over.w ((smallerBaseOverEquivalence B V S hV hS g).functor.map f)

/-! ### Lifting morphisms and objects -/

/-- A morphism of attached sheaves compatible with the structural morphisms comes from a unique
morphism of sheaves on the big fppf site of `V`. -/
def smallerBaseLift {G G' : FppfSheaf B V hV}
    (f : (smallerBaseSheafFunctor B V S hV hS g).obj G ⟶
      (smallerBaseSheafFunctor B V S hV hS g).obj G')
    (hf : f ≫ smallerBaseStr B V S hV hS g G' = smallerBaseStr B V S hV hS g G) : G ⟶ G' :=
  (smallerBaseOverEquivalence B V S hV hS g).fullyFaithfulFunctor.preimage (Over.homMk f hf)

/-- The morphism of attached sheaves induced by `smallerBaseLift f hf` is `f`. -/
@[simp]
theorem smallerBaseSheafFunctor_map_smallerBaseLift {G G' : FppfSheaf B V hV}
    (f : (smallerBaseSheafFunctor B V S hV hS g).obj G ⟶
      (smallerBaseSheafFunctor B V S hV hS g).obj G')
    (hf : f ≫ smallerBaseStr B V S hV hS g G' = smallerBaseStr B V S hV hS g G) :
    (smallerBaseSheafFunctor B V S hV hS g).map (smallerBaseLift B V S hV hS g f hf) = f := by
  simp [smallerBaseLift]

/-- The functor `smallerBaseSheafFunctor` is faithful. -/
instance : (smallerBaseSheafFunctor B V S hV hS g).Faithful := by
  dsimp only [smallerBaseSheafFunctor]
  infer_instance

/-- The sheaf on the big fppf site of `V` attached to an fppf sheaf on the big fppf site of `S`
with a morphism to the representable sheaf of `g`. -/
abbrev smallerBaseSheafOf (X : FppfSheaf B S hS) (p : X ⟶ smallerBaseTarget B V S hV hS g) :
    FppfSheaf B V hV :=
  (smallerBaseOverEquivalence B V S hV hS g).inverse.obj (Over.mk p)

/-- The sheaf attached to `smallerBaseSheafOf X p` is `X`. -/
def smallerBaseSheafOfIso (X : FppfSheaf B S hS) (p : X ⟶ smallerBaseTarget B V S hV hS g) :
    (smallerBaseSheafFunctor B V S hV hS g).obj (smallerBaseSheafOf B V S hV hS g X p) ≅ X :=
  (Over.forget _).mapIso ((smallerBaseOverEquivalence B V S hV hS g).counitIso.app (Over.mk p))

/-- The isomorphism `smallerBaseSheafOfIso X p` carries the structural morphism of the attached
sheaf to `p`. -/
@[reassoc (attr := simp)]
theorem smallerBaseSheafOfIso_hom_comp (X : FppfSheaf B S hS)
    (p : X ⟶ smallerBaseTarget B V S hV hS g) :
    (smallerBaseSheafOfIso B V S hV hS g X p).hom ≫ p =
      smallerBaseStr B V S hV hS g (smallerBaseSheafOf B V S hV hS g X p) :=
  Over.w ((smallerBaseOverEquivalence B V S hV hS g).counitIso.app (Over.mk p)).hom

/-- An isomorphism of attached sheaves compatible with the structural morphisms comes from a
unique isomorphism of sheaves on the big fppf site of `V`. -/
def smallerBaseLiftIso {G G' : FppfSheaf B V hV}
    (e : (smallerBaseSheafFunctor B V S hV hS g).obj G ≅
      (smallerBaseSheafFunctor B V S hV hS g).obj G')
    (he : e.hom ≫ smallerBaseStr B V S hV hS g G' = smallerBaseStr B V S hV hS g G) : G ≅ G' :=
  (smallerBaseOverEquivalence B V S hV hS g).fullyFaithfulFunctor.preimageIso (Over.isoMk e he)

/-! ### Exactness -/

/-- The functor `smallerBaseSheafFunctor` preserves colimits. -/
instance : PreservesColimitsOfSize.{w, w'} (smallerBaseSheafFunctor B V S hV hS g) := by
  dsimp only [smallerBaseSheafFunctor]
  infer_instance

/-- The functor `smallerBaseSheafFunctor` preserves fibre products. -/
instance : PreservesLimitsOfShape WalkingCospan (smallerBaseSheafFunctor B V S hV hS g) := by
  dsimp only [smallerBaseSheafFunctor]
  infer_instance

/-- **Epimorphisms do not see the change of base.** -/
theorem epi_smallerBaseSheafFunctor_map_iff {G G' : FppfSheaf B V hV} (f : G ⟶ G') :
    Epi ((smallerBaseSheafFunctor B V S hV hS g).map f) ↔ Epi f := by
  constructor
  · intro h
    exact (smallerBaseSheafFunctor B V S hV hS g).epi_of_epi_map h
  · intro h
    infer_instance

/-! ### Representable sheaves -/

/-- The sections of the presheaf attached to the representable presheaf of `U` viewed over `V`
through a factorization `ψ : U ⟶ (V ⟶ S)` are the morphisms into `U`. -/
def smallerBaseULiftYonedaOverEquiv {U : BigFppfOver B S hS} (ψ : U ⟶ Over.mk g)
    (T : BigFppfOver B S hS) :
    (smallerBaseULift B V S hV hS g
        (uliftYoneda.{u + 1}.obj (Over.mk ψ.left : BigFppfOver B V hV))).obj (op T) ≃
      (uliftYoneda.{u + 1}.obj U).obj (op T) where
  toFun p := ULift.up (Over.homMk p.2.down.left (by
    have h1 : p.2.down.left ≫ ψ.left = p.1.left := Over.w p.2.down
    have h2 : p.1.left ≫ g = T.hom := Over.w p.1
    have h3 : ψ.left ≫ g = U.hom := Over.w ψ
    exact (congrArg (_ ≫ ·) h3).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) h1).trans h2))))
  invFun m := smallerBaseULiftMk B V S hV hS g _ (m.down ≫ ψ)
    (ULift.up (Over.homMk m.down.left rfl))
  left_inv p := smallerBaseULiftMk_uliftYoneda_ext B V S hV hS g _ _ rfl
  right_inv _ := rfl

/-- The presheaf attached to the representable presheaf of `U` viewed over `V` through a
factorization `ψ : U ⟶ (V ⟶ S)` is the representable presheaf of `U`. -/
def smallerBaseULiftYonedaOverIso {U : BigFppfOver B S hS} (ψ : U ⟶ Over.mk g) :
    smallerBaseULift B V S hV hS g
        (uliftYoneda.{u + 1}.obj (Over.mk ψ.left : BigFppfOver B V hV)) ≅
      uliftYoneda.{u + 1}.obj U :=
  NatIso.ofComponents (fun T => (smallerBaseULiftYonedaOverEquiv B V S hV hS g ψ (unop T)).toIso)
    (fun _ => by ext; exact ULift.ext (Over.OverMorphism.ext rfl))

/-- The fppf sheaf `h_U` over `V`, through a factorization `ψ : U ⟶ (V ⟶ S)`, is attached to the
representable sheaf of `U`. -/
def smallerBaseYonedaIso {U : BigFppfOver B S hS} (ψ : U ⟶ Over.mk g) :
    (smallerBaseSheafFunctor B V S hV hS g).obj
        ((BigFppfOver.topology B V hV).uliftYoneda.{u + 1}.obj
          (Over.mk ψ.left : BigFppfOver B V hV)) ≅
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (smallerBaseULiftYonedaOverIso B V S hV hS g ψ)

/-- The isomorphism `smallerBaseYonedaIso ψ` carries the structural morphism of the attached sheaf
to the morphism of representable sheaves induced by `ψ`. -/
@[reassoc (attr := simp)]
theorem smallerBaseYonedaIso_hom_comp {U : BigFppfOver B S hS} (ψ : U ⟶ Over.mk g) :
    (smallerBaseYonedaIso B V S hV hS g ψ).hom ≫
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map ψ =
      smallerBaseStr B V S hV hS g _ := by
  ext T p
  exact ULift.ext (Over.OverMorphism.ext (Over.w p.2.down))

/-- The isomorphisms `smallerBaseYonedaIso` are natural in a morphism `a : U ⟶ U'` together with a
morphism `k` over `V` lying over it. -/
theorem smallerBaseYonedaIso_hom_naturality {U U' : BigFppfOver B S hS} (ψ : U ⟶ Over.mk g)
    (ψ' : U' ⟶ Over.mk g) (a : U ⟶ U')
    (k : (Over.mk ψ.left : BigFppfOver B V hV) ⟶ Over.mk ψ'.left) (hk : k.left = a.left) :
    (smallerBaseSheafFunctor B V S hV hS g).map
        ((BigFppfOver.topology B V hV).uliftYoneda.{u + 1}.map k) ≫
        (smallerBaseYonedaIso B V S hV hS g ψ').hom =
      (smallerBaseYonedaIso B V S hV hS g ψ).hom ≫
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map a := by
  ext T p
  exact ULift.ext (Over.OverMorphism.ext (by
    change p.2.down.left ≫ k.left = p.2.down.left ≫ a.left
    rw [hk]))

/-- On representable sheaves the attached sheaf is the representable sheaf of the object viewed
over `S`. -/
def smallerBaseSheafFunctorYonedaIso :
    (BigFppfOver.topology B V hV).uliftYoneda.{u + 1} ⋙ smallerBaseSheafFunctor B V S hV hS g ≅
      Over.map g ⋙ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} :=
  NatIso.ofComponents
    (fun X => (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (smallerBaseULiftYonedaIso B V S hV hS g X))
    (fun {X X'} m => by
      ext T p
      exact ULift.ext (Over.OverMorphism.ext rfl))

/-- On sheafified representable sheaves the attached sheaf is the sheafified representable sheaf
of the object viewed over `S`. -/
def smallerBaseSheafifiedYonedaIso :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B V hV) ⋙
        smallerBaseSheafFunctor B V S hV hS g ≅
      Over.map g ⋙ Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) :=
  Functor.isoWhiskerRight
      (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B V hV)).symm _ ≪≫
    smallerBaseSheafFunctorYonedaIso B V S hV hS g ≪≫
    Functor.isoWhiskerLeft _ (Sheaf.uliftYonedaIsoSheafifiedYoneda (BigFppfOver.topology B S hS))

end AlgebraicGeometry.FormalSpace

end
