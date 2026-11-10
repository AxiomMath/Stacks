module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of morphisms of ringed topoi

A morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is a morphism of the
underlying topoi together with `f♯ : O_D ⟶ f_*O_C`. Composing two of them is
`AlgebraicGeometry.RingedToposHom.comp`: the underlying morphisms of topoi compose, and the
structure map of the composite is
`O_E ⟶ g_*O_D ⟶ g_*f_*O_C ≅ (g ∘ f)_*O_C`, where the last step is the canonical comparison of
successive direct images with the direct image of the composite. That comparison is the identity
on sections.

## Main definitions

* `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso`: the comparison of iterated inverse
  images of a sheaf of rings with the inverse image along the composite.
* `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafCompIso`: the same for sheaves of
  commutative rings.
* `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso`: the comparison of successive
  direct images of a sheaf of commutative rings along morphisms of topoi with the direct image
  along their composite.
* `AlgebraicGeometry.RingedToposHom.comp`: composition of morphisms of ringed topoi.

## Main results

* `CategoryTheory.Functor.map_binaryOp_of_prodComparison`,
  `.map_unaryOp_of_eq` and `.map_constOp_of_terminalComparison`: a transported binary, unary or
  constant operation is computed by the operation it is transported from, for a
  finite-product-preserving functor to types.
* `Stacks.Sheaves.ToposPullback.pullbackRingSheafCompIso_hom_ringSheafMap` and
  `.pullbackRingSheafCompIso_inv_ringSheafMap`: the comparison of iterated inverse images of a
  sheaf of rings, and its inverse, are the identity on underlying sheaves of sets.
* `Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso_hom_forget`: the comparison of
  direct images is the identity on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.comp_toToposHom`: the underlying morphism of topoi of a
  composite is the composite of the underlying morphisms of topoi.
* `AlgebraicGeometry.RingedToposHom.comp_fSharp_forget`: on underlying sheaves of sets, the
  structure map of a composite is the composite of the structure maps.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe t u₁ u₂ v₁ v₂

variable {A : Type u₁} [Category.{v₁} A] [HasFiniteProducts A]
  {B : Type u₂} [Category.{v₂} B] [HasFiniteProducts B]
  (Ψ : A ⥤ B) [PreservesFiniteProducts Ψ]
  (P : B ⥤ Type t) [PreservesFiniteProducts P]

/-- A binary operation transported along `Ψ` and then along `P` is the operation transported
along `Ψ ⋙ P`, given the factorization of `Ψ.map` through the binary product comparison of
`Ψ`. -/
lemma map_binaryOp_of_prodComparison {X : A} (m : X ⨯ X ⟶ X)
    (n : Ψ.obj X ⨯ Ψ.obj X ⟶ Ψ.obj X) (h : Ψ.map m = prodComparison Ψ X X ≫ n)
    (x y : P.obj (Ψ.obj X)) :
    P.map n (prodObjMk x y) = (Ψ ⋙ P).map m (prodObjMk x y) := by
  rw [Functor.comp_map, h, P.map_comp_apply, map_prodComparison_apply, map_fst_prodObjMk,
    map_snd_prodObjMk]

omit [HasFiniteProducts A] [HasFiniteProducts B] [PreservesFiniteProducts Ψ]
  [PreservesFiniteProducts P] in
/-- A unary operation transported along `Ψ` and then along `P` is the operation transported
along `Ψ ⋙ P`. -/
lemma map_unaryOp_of_eq {X : A} (m : X ⟶ X) (n : Ψ.obj X ⟶ Ψ.obj X)
    (h : Ψ.map m = 𝟙 (Ψ.obj X) ≫ n ≫ 𝟙 (Ψ.obj X)) (x : P.obj (Ψ.obj X)) :
    P.map n x = (Ψ ⋙ P).map m x := by
  rw [Functor.comp_map, h, Category.id_comp, Category.comp_id]

/-- A constant transported along `Ψ` and then along `P` is the constant transported along
`Ψ ⋙ P`, given the factorization of `Ψ.map` through the terminal comparison of `Ψ`. -/
lemma map_constOp_of_terminalComparison {X : A} (m : ⊤_ A ⟶ X) (n : ⊤_ B ⟶ Ψ.obj X)
    (h : Ψ.map m = terminalComparison Ψ ≫ n ≫ 𝟙 (Ψ.obj X)) :
    P.map n default = (Ψ ⋙ P).map m default := by
  rw [Functor.comp_map, h, Category.comp_id, P.map_comp_apply]
  exact congrArg (P.map n) (Subsingleton.elim _ _)

end CategoryTheory.Functor

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory.Sheaf CategoryTheory.Functor

universe ww ww' ww'' vv uu vv' uu' vv'' uu''

section RingComp

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [L.HasSheafCompose (forget RingCat.{ww''})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf L (Type ww'') ⥤ Sheaf K (Type ww')) [PreservesFiniteProducts Ψ]
  (R : Sheaf L RingCat.{ww''})

/-- The comparison of iterated inverse images with the inverse image along the composite, over
one object of the site: the identity on sections, read as a ring homomorphism. -/
noncomputable def pullbackRingSheafCompHomApp (X : Cᵒᵖ) :
    (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)).obj.obj X ⟶
      (pullbackRingSheaf J (Ψ ⋙ Φ) R).obj.obj X :=
  letI := Sheaf.ringObjRing (pullbackRingSheaf K Ψ R) (Φ ⋙ sectionsFunctor J X)
  letI := Sheaf.ringObjRing R ((Ψ ⋙ Φ) ⋙ sectionsFunctor J X)
  RingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦ map_binaryOp_of_prodComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringAddHom R) (Sheaf.ringAddHom (pullbackRingSheaf K Ψ R))
        (ringAdd_map_aux' K Ψ R) x y
      map_mul' := fun x y ↦ map_binaryOp_of_prodComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringMulHom R) (Sheaf.ringMulHom (pullbackRingSheaf K Ψ R))
        (ringMul_map_aux' K Ψ R) x y
      map_zero' := map_constOp_of_terminalComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringZeroHom R) (Sheaf.ringZeroHom (pullbackRingSheaf K Ψ R))
        (ringZero_map_aux K Ψ R)
      map_one' := map_constOp_of_terminalComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringOneHom R) (Sheaf.ringOneHom (pullbackRingSheaf K Ψ R))
        (ringOne_map_aux K Ψ R) }

/-- The comparison of the inverse image along the composite with iterated inverse images, over
one object of the site: the identity on sections, read as a ring homomorphism. -/
noncomputable def pullbackRingSheafCompInvApp (X : Cᵒᵖ) :
    (pullbackRingSheaf J (Ψ ⋙ Φ) R).obj.obj X ⟶
      (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)).obj.obj X :=
  letI := Sheaf.ringObjRing (pullbackRingSheaf K Ψ R) (Φ ⋙ sectionsFunctor J X)
  letI := Sheaf.ringObjRing R ((Ψ ⋙ Φ) ⋙ sectionsFunctor J X)
  RingCat.ofHom
    { toFun := id
      map_add' := fun x y ↦ (map_binaryOp_of_prodComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringAddHom R) (Sheaf.ringAddHom (pullbackRingSheaf K Ψ R))
        (ringAdd_map_aux' K Ψ R) x y).symm
      map_mul' := fun x y ↦ (map_binaryOp_of_prodComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringMulHom R) (Sheaf.ringMulHom (pullbackRingSheaf K Ψ R))
        (ringMul_map_aux' K Ψ R) x y).symm
      map_zero' := (map_constOp_of_terminalComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringZeroHom R) (Sheaf.ringZeroHom (pullbackRingSheaf K Ψ R))
        (ringZero_map_aux K Ψ R)).symm
      map_one' := (map_constOp_of_terminalComparison Ψ (Φ ⋙ sectionsFunctor J X)
        (Sheaf.ringOneHom R) (Sheaf.ringOneHom (pullbackRingSheaf K Ψ R))
        (ringOne_map_aux K Ψ R)).symm }

/-- Taking the inverse image of a sheaf of rings along `Ψ` and then along `Φ` is taking it along
`Ψ ⋙ Φ`. The comparison is the identity on underlying sheaves of sets. -/
noncomputable def pullbackRingSheafCompIso :
    pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R) ≅ pullbackRingSheaf J (Ψ ⋙ Φ) R where
  hom :=
    { hom :=
        { app := fun X ↦ pullbackRingSheafCompHomApp J K Φ Ψ R X
          naturality := fun _ _ _ ↦ rfl } }
  inv :=
    { hom :=
        { app := fun X ↦ pullbackRingSheafCompInvApp J K Φ Ψ R X
          naturality := fun _ _ _ ↦ rfl } }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The comparison of iterated inverse images with the inverse image along the composite is the
identity on underlying sheaves of sets. -/
@[simp]
lemma pullbackRingSheafCompIso_hom_ringSheafMap :
    (sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafCompIso J K Φ Ψ R).hom =
      𝟙 (Φ.obj (Ψ.obj (Sheaf.ringSheaf R))) :=
  rfl

/-- The inverse comparison is also the identity on underlying sheaves of sets. -/
@[simp]
lemma pullbackRingSheafCompIso_inv_ringSheafMap :
    (sheafCompose J (forget RingCat.{ww})).map (pullbackRingSheafCompIso J K Φ Ψ R).inv =
      𝟙 (Φ.obj (Ψ.obj (Sheaf.ringSheaf R))) :=
  rfl

end RingComp

section CommRingComp

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [L.HasSheafCompose (forget RingCat.{ww''})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [L.HasSheafCompose (forget₂ CommRingCat.{ww''} RingCat.{ww''})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf L (Type ww'') ⥤ Sheaf K (Type ww')) [PreservesFiniteProducts Ψ]
  (O : Sheaf L CommRingCat.{ww''})

/-- Taking the inverse image of a sheaf of commutative rings along `Ψ` and then along `Φ` is
taking it along `Ψ ⋙ Φ`. -/
noncomputable def pullbackCommRingSheafCompIso :
    pullbackCommRingSheaf J Φ (pullbackCommRingSheaf K Ψ O) ≅
      pullbackCommRingSheaf J (Ψ ⋙ Φ) O :=
  (fullyFaithfulForgetCommRingSheaf J).preimageIso
    (pullbackRingSheafCompIso J K Φ Ψ (SheafOfModules.Tensor.ringSheaf O))

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [L.HasSheafCompose (forget₂ CommRingCat.{ww''} RingCat.{ww''})] in
/-- Forgetting commutativity carries the comparison of iterated inverse images to the
ring-valued comparison. -/
lemma forgetCommRingSheaf_map_pullbackCommRingSheafCompIso_hom :
    (Stacks.forgetCommRingSheaf J).map (pullbackCommRingSheafCompIso J K Φ Ψ O).hom =
      (pullbackRingSheafCompIso J K Φ Ψ (SheafOfModules.Tensor.ringSheaf O)).hom :=
  (fullyFaithfulForgetCommRingSheaf J).map_preimage _

/-- Forgetting to sets from commutative rings factors through forgetting to rings. -/
private lemma sheafCompose_forget_map_eq_forgetCommRingSheaf_map
    {A B : Sheaf J CommRingCat.{ww}} (φ : A ⟶ B) :
    (sheafCompose J (forget CommRingCat.{ww})).map φ =
      (sheafCompose J (forget RingCat.{ww})).map ((Stacks.forgetCommRingSheaf J).map φ) := rfl

omit [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [L.HasSheafCompose (forget₂ CommRingCat.{ww''} RingCat.{ww''})] in
/-- The comparison of iterated inverse images with the inverse image along the composite is the
identity on underlying sheaves of sets. -/
@[simp]
lemma pullbackCommRingSheafCompIso_hom_forget :
    (sheafCompose J (forget CommRingCat.{ww})).map
        (pullbackCommRingSheafCompIso J K Φ Ψ O).hom =
      𝟙 (Φ.obj (Ψ.obj ((sheafCompose L (forget CommRingCat.{ww''})).obj O))) := by
  rw [sheafCompose_forget_map_eq_forgetCommRingSheaf_map,
    forgetCommRingSheaf_map_pullbackCommRingSheafCompIso_hom]
  rfl

end CommRingComp

end Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' ww'' vv uu vv' uu' vv'' uu''

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [L.HasSheafCompose (forget RingCat.{ww''})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [L.HasSheafCompose (forget₂ CommRingCat.{ww''} RingCat.{ww''})]
  (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
  (g : MorphismOfTopoi (Sheaf K (Type ww')) (Sheaf L (Type ww'')))
  (O : Sheaf J CommRingCat.{ww})

/-- The direct image of a sheaf of commutative rings along `f` and then along `g` is its direct
image along `g ∘ f`. -/
noncomputable def pushforwardCommRingCompIso :
    (pushforwardCommRingFunctor g).obj ((pushforwardCommRingFunctor f).obj O) ≅
      (pushforwardCommRingFunctor (g.comp f)).obj O :=
  pullbackCommRingSheafCompIso L K g.pushforward f.pushforward O

/-- The comparison of successive direct images with the direct image of the composite is the
identity on underlying sheaves of sets. -/
@[simp]
lemma pushforwardCommRingCompIso_hom_forget :
    (sheafCompose L (forget CommRingCat.{ww''})).map (pushforwardCommRingCompIso f g O).hom =
      𝟙 (g.pushforward.obj
        (f.pushforward.obj ((sheafCompose J (forget CommRingCat.{ww})).obj O))) :=
  pullbackCommRingSheafCompIso_hom_forget L K g.pushforward f.pushforward O

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry

namespace RingedToposHom

open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w' v'' u'' w''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- The composition of two morphisms of ringed topoi: the underlying morphisms of topoi compose,
and the structure map of the composite is
`O_Z ⟶ g_*O_Y ⟶ g_*f_*O_X ≅ (g ∘ f)_*O_X`, the last step being the canonical comparison of
successive direct images with the direct image of the composite. -/
@[stacks 01D3 "part (3): composition"]
noncomputable def comp (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    RingedToposHom X Z where
  toToposHom := g.toToposHom.comp f.toToposHom
  fSharp := g.fSharp ≫ (pushforwardCommRingFunctor g.toToposHom).map f.fSharp ≫
    (pushforwardCommRingCompIso f.toToposHom g.toToposHom X.O).hom

/-- The underlying morphism of topoi of a composite of morphisms of ringed topoi is the
composite of the underlying morphisms of topoi. -/
@[simp]
theorem comp_toToposHom (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    (comp g f).toToposHom = g.toToposHom.comp f.toToposHom := rfl

/-- On underlying sheaves of sets, the structure map of a composite of morphisms of ringed topoi
is the composite `O_Z ⟶ g_*O_Y ⟶ g_*f_*O_X` of the structure maps. -/
lemma comp_fSharp_forget (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    Z.forgetRing.map (g.comp f).fSharp =
      Z.forgetRing.map g.fSharp ≫
        g.toToposHom.pushforward.map (Y.forgetRing.map f.fSharp) := by
  have h1 : Z.forgetRing.map (g.comp f).fSharp =
      Z.forgetRing.map g.fSharp ≫
        Z.forgetRing.map ((pushforwardCommRingFunctor g.toToposHom).map f.fSharp) ≫
          Z.forgetRing.map (pushforwardCommRingCompIso f.toToposHom g.toToposHom X.O).hom := by
    change Z.forgetRing.map (g.fSharp ≫
      (pushforwardCommRingFunctor g.toToposHom).map f.fSharp ≫
        (pushforwardCommRingCompIso f.toToposHom g.toToposHom X.O).hom) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  have h2 : Z.forgetRing.map ((pushforwardCommRingFunctor g.toToposHom).map f.fSharp) =
      g.toToposHom.pushforward.map (Y.forgetRing.map f.fSharp) := by
    have e : (Stacks.forgetCommRingSheaf Z.J).map
          ((pushforwardCommRingFunctor g.toToposHom).map f.fSharp) =
        pullbackRingSheafMap Z.J g.toToposHom.pushforward
          ((Stacks.forgetCommRingSheaf Y.J).map f.fSharp) :=
      forgetCommRingSheaf_map_pullbackCommRingSheafMap Z.J g.toToposHom.pushforward f.fSharp
    change (sheafCompose Z.J (forget CommRingCat.{w''})).map _ = _
    rw [sheafCompose_forget_map_eq_forgetCommRingSheaf_map, e]
    exact ringSheafMap_pullbackRingSheafMap Z.J g.toToposHom.pushforward _
  have h3 : Z.forgetRing.map (pushforwardCommRingCompIso f.toToposHom g.toToposHom X.O).hom =
      𝟙 (g.toToposHom.pushforward.obj
        (Y.forgetRing.obj ((pushforwardCommRingFunctor f.toToposHom).obj X.O))) :=
    pushforwardCommRingCompIso_hom_forget f.toToposHom g.toToposHom X.O
  rw [h1, h2, h3]
  exact congrArg (fun m ↦ Z.forgetRing.map g.fSharp ≫ m)
    (Category.comp_id (g.toToposHom.pushforward.map (Y.forgetRing.map f.fSharp)))

end RingedToposHom

end AlgebraicGeometry
