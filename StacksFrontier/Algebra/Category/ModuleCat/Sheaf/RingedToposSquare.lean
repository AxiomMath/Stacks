module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposCoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.StacksAttribute

/-!
# Commuting squares of morphisms of ringed topoi

A square of morphisms of ringed topoi
```
X --f--> Y
|        |
p        q
v        v
S --g--> T
```
with `S = T` on the nose commutes when an isomorphism `e : (p ∘ f)⁻¹ ≅ (q ∘ g)⁻¹` of the two
inverse images is given *and* the two structure maps agree after transport along the adjoint
mate of `e`. This file provides what is needed to verify such a square:

* the structure map of a morphism of ringed topoi in inverse-image form on underlying sheaves of
  sets, and its behaviour under composition;
* the translation between "the structure maps agree along the mate of `e`" and an equation
  between the two inverse-image structure maps, which is the form in which such an equation can
  actually be checked;
* the observation that a morphism which is `eqToHom` of an equality of objects — a *transport* —
  is determined by its source and target, so that a square all of whose edges are transports
  commutes for free.

## Main definitions

* `Stacks.IsTransport`: a morphism is `eqToHom` of an equality of its source and target.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget`: the structure map `f⁻¹O_Y ⟶ O_X`
  on underlying sheaves of sets.

## Main results

* `CategoryTheory.Adjunction.comp_rightAdjointUniq_hom_app_eq_iff`: an equation involving the
  adjoint mate of an isomorphism of left adjoints is equivalent to an equation between the
  adjuncts.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageForget_comp`: the inverse-image structure
  map of a composite is the composite of the inverse-image structure maps, and
  `AlgebraicGeometry.RingedToposHom.isTransport_fSharpInverseImageForget_comp`: it is a transport
  as soon as both factors' are.
* `AlgebraicGeometry.RingedToposHom.ringedSquare_of_isTransport`: a square of morphisms of
  ringed topoi whose two inverse-image structure maps and whose comparison isomorphism are all
  transports commutes.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_eq_of_isTransport`: the same square in
  inverse-image form, as an equation between morphisms of sheaves of commutative rings.
* `AlgebraicGeometry.RingedToposHom.coefficientMorphism_fSharpInverseImageForget`: the
  inverse-image structure map of a change of coefficient rings is the given map of structure
  sheaves.

## Implementation notes

`Stacks.IsTransport` is a predicate on a morphism rather than a structure on a pair of objects
because that is how it composes: `IsTransport` is closed under composition, under the action of a
functor, under taking a component of a natural transformation, and under inversion, and
`Stacks.IsTransport.eq` says any two transports with the same source and target are equal. Those
five facts are the whole calculus.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks

/-- A morphism is a **transport** when its source and target are equal and it is the canonical
morphism `eqToHom` of that equality. A transport carries no information beyond its source and
target: `Stacks.IsTransport.eq` says two transports between the same objects are equal. -/
def IsTransport {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ h : X = Y, f = eqToHom h

namespace IsTransport

variable {C : Type*} [Category* C]

/-- `eqToHom` of an equality is a transport. -/
theorem eqToHom {X Y : C} (h : X = Y) : IsTransport (CategoryTheory.eqToHom h) := ⟨h, rfl⟩

/-- The identity is a transport. -/
theorem id (X : C) : IsTransport (𝟙 X) := ⟨rfl, rfl⟩

/-- A composite of transports is a transport. -/
theorem comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsTransport f) (hg : IsTransport g) :
    IsTransport (f ≫ g) := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨h', rfl⟩ := hg
  exact ⟨h.trans h', eqToHom_trans h h'⟩

/-- The image of a transport under a functor is a transport. -/
theorem map {D : Type*} [Category* D] (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} (hf : IsTransport f) :
    IsTransport (F.map f) := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨congrArg F.obj h, eqToHom_map F h⟩

/-- Every component of a transport between functors is a transport. -/
theorem app {D : Type*} [Category* D] {F G : C ⥤ D} {f : F ⟶ G} (hf : IsTransport f) (X : C) :
    IsTransport (f.app X) := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨congrArg (fun F : C ⥤ D => F.obj X) h, eqToHom_app h X⟩

/-- If the forward direction of an isomorphism is a transport then so is its inverse. -/
theorem inv {X Y : C} (e : X ≅ Y) (h : IsTransport e.hom) : IsTransport e.inv := by
  obtain ⟨rfl, he⟩ := h
  obtain rfl : e = Iso.refl X := Iso.ext he
  exact ⟨rfl, rfl⟩

/-- Two transports with the same source and target are equal: a transport is determined by its
source and target. -/
theorem eq {X Y : C} {f g : X ⟶ Y} (hf : IsTransport f) (hg : IsTransport g) : f = g := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨h', rfl⟩ := hg
  rfl

end IsTransport

end Stacks

namespace CategoryTheory.Adjunction

universe v₁ u₁ v₂ u₂ v₃ u₃

/-- An equation whose left-hand side ends in the adjoint mate of an isomorphism `e : L ≅ L'` of
left adjoints is equivalent to an equation between the adjuncts, with `e` inserted on the left. -/
theorem comp_rightAdjointUniq_hom_app_eq_iff {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R') (e : L ≅ L')
    {X : C} {Y : D} (f : X ⟶ R.obj Y) (g : X ⟶ R'.obj Y) :
    f ≫ ((a.ofNatIsoLeft e).rightAdjointUniq a').hom.app Y = g ↔
      (a.homEquiv X Y).symm f = e.hom.app X ≫ (a'.homEquiv X Y).symm g := by
  have key : (a'.homEquiv X Y).symm (f ≫ ((a.ofNatIsoLeft e).rightAdjointUniq a').hom.app Y) =
      e.inv.app X ≫ (a.homEquiv X Y).symm f := by
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app,
      ← Adjunction.homEquiv_counit (adj := a.ofNatIsoLeft e),
      Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  rw [← (a'.homEquiv X Y).symm.injective.eq_iff, key]
  exact (e.app X).inv_comp_eq

/-- The adjunct of `a ≫ b ≫ G.map c`, a morphism factored with a pre- and a post-composition,
is `F.map a ≫ (adjunct of b) ≫ c`. -/
theorem homEquiv_symm_comp_comp_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X X' : C} {Y Y' : D}
    (a : X' ⟶ X) (b : X ⟶ G.obj Y) (c : Y ⟶ Y') :
    (adj.homEquiv X' Y').symm (a ≫ b ≫ G.map c) = F.map a ≫ (adj.homEquiv X Y).symm b ≫ c := by
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

universe w₀ v₀ u₀ v₁ u₁ v₂ u₂

/-- The canonical comparison of a composite of pushforwards of sheaves with the pushforward
along the composite is a transport, when the isomorphism it is built from is `eqToIso` of an
equality of the two composites: restriction along `f` and then along `g` *is* restriction along
`f ⋙ g`, and the comparison is the identity on sections. -/
theorem isTransport_sheafPushforwardContinuousComp'_hom
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D] {E : Type u₂}
    [Category.{v₂} E] {f : C ⥤ D} {g : D ⥤ E} {fg : C ⥤ E} (h : f ⋙ g = fg)
    (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) [f.IsContinuous J K] [g.IsContinuous K L]
    [fg.IsContinuous J L] :
    Stacks.IsTransport (sheafPushforwardContinuousComp' (eqToIso h) A J K L).hom := by
  subst fg
  have hiso : (sheafPushforwardContinuousIso (Iso.refl (f ⋙ g)) A J L).hom =
      𝟙 (sheafPushforwardContinuous (f ⋙ g) A J L) := by
    ext M X
    simp only [sheafPushforwardContinuousIso_hom, Iso.refl_inv,
      sheafPushforwardContinuousNatTrans_app_hom, NatTrans.op_id, ObjectProperty.ι_obj,
      Functor.whiskerRight_id', NatTrans.id_app, Functor.comp_obj, Functor.op_obj,
      ObjectProperty.FullSubcategory.id_hom]
    exact rfl
  have h₀ : sheafPushforwardContinuous g A K L ⋙ sheafPushforwardContinuous f A J K =
      sheafPushforwardContinuous (f ⋙ g) A J L := rfl
  exact ⟨h₀, ((congrArg Iso.hom (Iso.refl_trans _)).trans hiso).trans
    (eqToHom_refl _ h₀).symm⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w' v'' u'' w''

section Forget

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The structure map of a morphism of ringed topoi in inverse-image form, read on underlying
sheaves of sets: the adjunct of `f♯ : O_Y ⟶ f_*O_X` under `f⁻¹ ⊣ f_*`. -/
noncomputable def fSharpInverseImageForget (f : RingedToposHom X Y) :
    f.toToposHom.inverseImage.obj (Y.forgetRing.obj Y.O) ⟶ X.forgetRing.obj X.O :=
  (f.toToposHom.adj.homEquiv _ _).symm (Y.forgetRing.map f.fSharp)

/-- Forgetting the ring operations of the inverse-image form of the structure map gives the
inverse-image form of the forgotten structure map; the two readings of `f⁻¹O_Y ⟶ O_X` agree.

Not to be confused with
`AlgebraicGeometry.RingedToposHom.forgetRing_map_fSharpInverseImage` in
`RingedToposPullbackLowerShriek`, which compares the same left-hand side against the `RingCat`
form `fSharpInverseImageRing` rather than against `fSharpInverseImageForget`. -/
lemma forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget (f : RingedToposHom X Y)
    [X.J.HasSheafCompose (forget CommRingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})] :
    X.forgetRing.map f.fSharpInverseImage = f.fSharpInverseImageForget :=
  MorphismOfTopoi.ringAdjunction_homEquiv_symm_forget f.toToposHom Y.O X.O f.fSharp

/-- A morphism of ringed topoi with its two structure sheaves replaced by isomorphic ones: the
underlying geometric morphism is unchanged and the structure map is conjugated by the two
isomorphisms. -/
noncomputable def ofStructureIso (f : RingedToposHom X Y) {OX : Sheaf X.J CommRingCat.{w}}
    {OY : Sheaf Y.J CommRingCat.{w}} (eX : X.O ≅ OX) (eY : Y.O ≅ OY) :
    RingedToposHom (X := { X with O := OX }) (Y := { Y with O := OY }) where
  toToposHom := f.toToposHom
  fSharp := eY.inv ≫ f.fSharp ≫ f.toToposHom.pushforwardRing.map eX.hom

/-- Changing the structure sheaves conjugates the inverse-image structure map by the two
isomorphisms. In particular it keeps it a transport when the two isomorphisms are. -/
lemma ofStructureIso_fSharpInverseImageForget (f : RingedToposHom X Y)
    {OX : Sheaf X.J CommRingCat.{w}} {OY : Sheaf Y.J CommRingCat.{w}}
    (eX : X.O ≅ OX) (eY : Y.O ≅ OY) :
    (f.ofStructureIso eX eY).fSharpInverseImageForget =
      f.toToposHom.inverseImage.map ((sheafCompose Y.J (forget CommRingCat.{w})).map eY.inv) ≫
        f.fSharpInverseImageForget ≫
          (sheafCompose X.J (forget CommRingCat.{w})).map eX.hom :=
  have h := ((sheafCompose Y.J (forget CommRingCat.{w})).map_comp eY.inv
      (f.fSharp ≫ f.toToposHom.pushforwardRing.map eX.hom)).trans
    (congrArg (fun m ↦ (sheafCompose Y.J (forget CommRingCat.{w})).map eY.inv ≫ m)
      (((sheafCompose Y.J (forget CommRingCat.{w})).map_comp f.fSharp
            (f.toToposHom.pushforwardRing.map eX.hom)).trans
        (congrArg (fun m ↦ (sheafCompose Y.J (forget CommRingCat.{w})).map f.fSharp ≫ m)
          (MorphismOfTopoi.pushforwardRing_map_forget f.toToposHom eX.hom))))
  (congrArg (f.toToposHom.adj.homEquiv _ _).symm h).trans
    (Adjunction.homEquiv_symm_comp_comp_map f.toToposHom.adj _ _ _)

/-- A morphism of ringed topoi read on isomorphic structure sheaves has a transport for its
inverse-image structure map as soon as the original does and the two comparisons do. -/
lemma isTransport_ofStructureIso_fSharpInverseImageForget (f : RingedToposHom X Y)
    {OX : Sheaf X.J CommRingCat.{w}} {OY : Sheaf Y.J CommRingCat.{w}}
    (eX : X.O ≅ OX) (eY : Y.O ≅ OY)
    (hf : Stacks.IsTransport f.fSharpInverseImageForget)
    (hX : Stacks.IsTransport ((sheafCompose X.J (forget CommRingCat.{w})).map eX.hom))
    (hY : Stacks.IsTransport ((sheafCompose Y.J (forget CommRingCat.{w})).map eY.hom)) :
    Stacks.IsTransport (f.ofStructureIso eX eY).fSharpInverseImageForget := by
  rw [ofStructureIso_fSharpInverseImageForget]
  exact ((Stacks.IsTransport.inv
    ((sheafCompose Y.J (forget CommRingCat.{w})).mapIso eY) hY).map _).comp (hf.comp hX)

end Forget

section Comp

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The inverse-image structure map of a composite of morphisms of ringed topoi is the composite
`f⁻¹g⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X` of the inverse-image structure maps. -/
lemma fSharpInverseImageForget_comp (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    (g.comp f).fSharpInverseImageForget =
      f.toToposHom.inverseImage.map g.fSharpInverseImageForget ≫ f.fSharpInverseImageForget :=
  (congrArg ((g.comp f).toToposHom.adj.homEquiv _ _).symm (comp_fSharp_forget g f)).trans
    (Adjunction.comp_homEquiv_symm_comp g.toToposHom.adj f.toToposHom.adj _ _)

/-- The inverse-image structure map of a composite of morphisms of ringed topoi is a transport as
soon as those of the two factors are. -/
theorem isTransport_fSharpInverseImageForget_comp (g : RingedToposHom Y Z)
    (f : RingedToposHom X Y) (hg : Stacks.IsTransport g.fSharpInverseImageForget)
    (hf : Stacks.IsTransport f.fSharpInverseImageForget) :
    Stacks.IsTransport (g.comp f).fSharpInverseImageForget := by
  rw [fSharpInverseImageForget_comp]
  exact (hg.map _).comp hf

end Comp

section Square

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **A square of ringed topoi all of whose edges are transports commutes.** If two morphisms of
ringed topoi `F, G : X ⟶ Y` have inverse-image structure maps that are transports, and an
isomorphism `e : F⁻¹ ≅ G⁻¹` whose forward direction is a transport, then the structure map of `F`
transported along the adjoint mate of `e` is the structure map of `G`. -/
theorem ringedSquare_of_isTransport (F G : RingedToposHom X Y)
    (e : F.toToposHom.inverseImage ≅ G.toToposHom.inverseImage)
    (hF : Stacks.IsTransport F.fSharpInverseImageForget)
    (hG : Stacks.IsTransport G.fSharpInverseImageForget)
    (he : Stacks.IsTransport e.hom) :
    Y.forgetRing.map F.fSharp ≫
      ((F.toToposHom.adj.ofNatIsoLeft e).rightAdjointUniq G.toToposHom.adj).hom.app
        (X.forgetRing.obj X.O) = Y.forgetRing.map G.fSharp :=
  (Adjunction.comp_rightAdjointUniq_hom_app_eq_iff
    F.toToposHom.adj G.toToposHom.adj e _ _).mpr (hF.eq ((he.app _).comp hG))

/-- **The same square, read on sheaves of commutative rings.** Under the hypotheses of
`AlgebraicGeometry.RingedToposHom.ringedSquare_of_isTransport`, the inverse-image structure map
of `F` is the ring-valued comparison induced by `e` followed by that of `G`. This is the
inverse-image form of the square, and it is an equation between morphisms of sheaves of
*commutative rings*: the comparison of the two inverse images of the structure sheaf of the
target is `Stacks.Sheaves.ToposPullback.pullbackCommRingSheafIsoOfNatIso` of `e`, the transport
of the ring operations along `e`. -/
theorem fSharpInverseImage_eq_of_isTransport [X.J.HasSheafCompose (forget CommRingCat.{w})]
    [Y.J.HasSheafCompose (forget CommRingCat.{w})] (F G : RingedToposHom X Y)
    (e : F.toToposHom.inverseImage ≅ G.toToposHom.inverseImage)
    (hF : Stacks.IsTransport F.fSharpInverseImageForget)
    (hG : Stacks.IsTransport G.fSharpInverseImageForget)
    (he : Stacks.IsTransport e.hom) :
    F.fSharpInverseImage =
      (pullbackCommRingSheafIsoOfNatIso X.J e Y.O).hom ≫ G.fSharpInverseImage := by
  have hT : ∀ H : RingedToposHom X Y, Stacks.IsTransport H.fSharpInverseImageForget →
      Stacks.IsTransport (X.forgetRing.map H.fSharpInverseImage) := fun H hH => by
    rwa [forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget]
  refine X.forgetRing.map_injective (Stacks.IsTransport.eq (hT F hF) ?_)
  exact Eq.mp (congrArg Stacks.IsTransport (X.forgetRing.map_comp _ _).symm)
    ((he.app _).comp (hT G hG))

end Square

section Coefficient

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  {O O' : Sheaf J CommRingCat.{w}}

/-- The inverse-image structure map of a change of coefficient rings is the given map of
structure sheaves: on underlying sheaves of sets the identification of the inverse image along
the identity with the identity contributes nothing. -/
lemma coefficientMorphism_fSharpInverseImageForget (α : O ⟶ O') :
    (coefficientMorphism J α).fSharpInverseImageForget =
      (sheafCompose J (forget CommRingCat.{w})).map α := by
  refine (forgetRing_map_fSharpInverseImage_eq_fSharpInverseImageForget
      (coefficientMorphism J α)).symm.trans
    ((congrArg (sheafCompose J (forget CommRingCat.{w})).map
      (coefficientMorphism_fSharpInverseImage J α)).trans ?_)
  erw [Functor.map_comp, forget_map_pullbackCommRingSheafFunctorId_hom_app, Category.id_comp]

end Coefficient

end AlgebraicGeometry.RingedToposHom

end
