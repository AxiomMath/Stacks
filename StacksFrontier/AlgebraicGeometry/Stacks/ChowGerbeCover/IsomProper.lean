module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeOfEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceOverAlgebraicSpaceRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedIsomPullback

/-!
# The isomorphism sheaf over a separated morphism to an algebraic space is proper

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space over `S`, let `Z` be
an algebraic space over `S` and let `x₁, x₂ : Z ⟶ 𝒳` be two 1-morphisms with `x₁ ≫ f = x₂ ≫ f`.
The proof of Stacks 0CQ7 uses that the algebraic space `Isom_𝒳(x₁, x₂)` of Stacks 06PP is proper
over `Z` when `f` is separated: this is Stacks 0CPL (2), which makes
`Isom_𝒳(x₁, x₂) ⟶ Isom_Y(f x₁, f x₂)` proper, read over an algebraic space, where the target is
`Z` itself.

The library has the isomorphism sheaf twice: as a presheaf of sets with its structure morphism to
`Z` (`AlgebraicGeometry.Stack.isomSpaceOverSpace`,
`AlgebraicGeometry.Stack.isomSpaceOverSpaceProj`, whose algebraicity is Stacks 06PP) and as a
category fibred in groupoids (`AlgebraicGeometry.Stack.HigherDiagonal.isomStack`, the setting of
the library's Stacks 0CPL and 0CPR). This file identifies the two
(`AlgebraicGeometry.Stack.isomStackOfSpace` is an equivalence), transports the condition of Stacks
03YK along the identification (Stacks 0457), and uses that the fibres of the algebraic stack of an
algebraic space are discrete.

## Main definitions

* `AlgebraicGeometry.Stack.isomStackOfSpace`: the based functor from the category attached to the
  presheaf `Isom_𝒳(x₁, x₂)` to `Isom_𝒳(x₁, x₂)` as a category fibred in groupoids.
* `AlgebraicGeometry.Stack.RelativePropertyHolds`: the condition of Stacks 03YK at a property,
  without the instance arguments of `AlgebraicGeometry.Stack.HasRelativeProperty`.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_isomStackOfSpace`: the two readings of the isomorphism
  sheaf agree.
* `AlgebraicGeometry.Stack.relativePropertyHolds_isomSpaceOverSpaceMap`: a property of
  `AlgebraicGeometry.Stack.HigherDiagonal.isomMap` is one of the map of isomorphism sheaves.
* `AlgebraicGeometry.Stack.relativePropertyHolds_isomSpaceOverSpaceProj`: over an algebraic space,
  it is one of the structure morphism `Isom_𝒳(x₁, x₂) ⟶ Z`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_isomSpaceOverSpaceProj_of_isSeparated`:
  **Stacks 0CPL (2)** for the isomorphism sheaf over an algebraic space: `Isom_𝒳(x₁, x₂)` is
  proper over `Z` when `f` is separated.

## References

* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor.Fiber

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

attribute [local implicit_reducible] pointFiber

/-! ### Morphisms of the category attached to a presheaf of sets -/

/-- **Two morphisms of the category attached to a presheaf of sets lying over one morphism of
the site are equal**: a morphism of that category is determined by its base. -/
theorem fibredCategory_hom_eq_of_isHomLift {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : (fibredCategory B S hS F).val.obj} {U V : BigFppfOver B S hS} (c : U ⟶ V)
    (m m' : a ⟶ b) (hm : (fibredCategory B S hS F).val.p.IsHomLift c m)
    (hm' : (fibredCategory B S hS F).val.p.IsHomLift c m') : m = m' := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ (by apply Discrete.hom_eq)
  show (fibredCategory B S hS F).val.p.map m = (fibredCategory B S hS F).val.p.map m'
  rw [IsHomLift.fac' (fibredCategory B S hS F).val.p c m,
    IsHomLift.fac' (fibredCategory B S hS F).val.p c m']

/-- The base of a morphism of the category attached to a presheaf of sets lying over `c` is `c`. -/
theorem fibredCategory_hom_base_eq_of_isHomLift {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : (fibredCategory B S hS F).val.obj} (c : a.base ⟶ b.base) (m : a ⟶ b)
    (hm : (fibredCategory B S hS F).val.p.IsHomLift c m) : m.base = c :=
  (IsHomLift.fac' (fibredCategory B S hS F).val.p c m).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-! ### The isomorphism sheaf as a category fibred in groupoids -/

/-- The object of `Isom_𝒳(x₁, x₂)`, read as the category fibred in groupoids
`AlgebraicGeometry.Stack.HigherDiagonal.isomStack`, named by a section of the isomorphism sheaf
`AlgebraicGeometry.Stack.isomSpaceOverSpace`: the point `z` of `Z` on both factors and the
isomorphism `x₁(z) ≅ x₂(z)` the section carries. -/
noncomputable def isomStackObjOfSection (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (W : BigFppfOver B S hS) (s : isomSection B S hS Z hZ x₁ x₂ (Opposite.op W)) :
    (HigherDiagonal.isomStack B S hS Z hZ x₁ x₂).val.obj :=
  ⟨{ base := W
     x := spacePoint.{u, w} B S hS Z hZ W s.1
     y := spacePoint.{u, w} B S hS Z hZ W s.1
     hx := rfl
     hy := rfl
     iso := fiberInclusion.mapIso (@asIso _ _ _ _ s.2.1 s.2.2)
     vertical := s.2.1.2 }, rfl⟩

/-- The comparison square of a morphism of the category attached to the isomorphism sheaf: it is
the equation defining the restriction of a section, `AlgebraicGeometry.Stack.pointRestrict_fac`. -/
theorem isomStackObjOfSection_w (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W₁ W₂ : (BigFppfOver B S hS)ᵒᵖ} (g : W₁ ⟶ W₂) (s : isomSection B S hS Z hZ x₁ x₂ W₁)
    (s' : isomSection B S hS Z hZ x₁ x₂ W₂)
    (hs : s' = (isomSpaceOverSpace B S hS Z hZ x₁ x₂).map g s) :
    x₁.hom.hom.toFunctor.map
        (spacePointHom.{u, w} B S hS Z hZ g s.1 s'.1 (congrArg Sigma.fst hs)) ≫
        fiberInclusion.map s.2.1 =
      fiberInclusion.map s'.2.1 ≫ x₂.hom.hom.toFunctor.map
        (spacePointHom.{u, w} B S hS Z hZ g s.1 s'.1 (congrArg Sigma.fst hs)) := by
  subst hs
  exact (pointRestrict_fac B S hS Z hZ x₁ x₂ g s.1 _ rfl s.2.1).symm

/-- **The isomorphism sheaf, read as a category fibred in groupoids.** The based functor from the
category attached to the presheaf `Isom_𝒳(x₁, x₂)` of Stacks 06PP to the category fibred in
groupoids `AlgebraicGeometry.Stack.HigherDiagonal.isomStack` of the vertical isomorphisms
`x₁(z) ≅ x₂(z)` at a single point of `Z`: a section is sent to the isomorphism it carries, and a
morphism over `g` to the pair of morphisms of the category of elements of `Z` over `g`. -/
noncomputable def isomStackOfSpace (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x₁ x₂)).val ⥤ᵇ
      (HigherDiagonal.isomStack B S hS Z hZ x₁ x₂).val where
  obj P := isomStackObjOfSection B S hS Z hZ x₁ x₂ P.base P.fiber.as
  map {P Q} g := ObjectProperty.homMk
    { hbase := g.base
      a := spacePointHom.{u, w} B S hS Z hZ g.base.op Q.fiber.as.1 P.fiber.as.1
        (congrArg Sigma.fst (Discrete.eq_of_hom g.fiber))
      b := spacePointHom.{u, w} B S hS Z hZ g.base.op Q.fiber.as.1 P.fiber.as.1
        (congrArg Sigma.fst (Discrete.eq_of_hom g.fiber))
      ha := spacePointHom_isHomLift.{u, w} B S hS Z hZ g.base.op _ _ _
      hb := spacePointHom_isHomLift.{u, w} B S hS Z hZ g.base.op _ _ _
      w := isomStackObjOfSection_w B S hS Z hZ x₁ x₂ g.base.op Q.fiber.as P.fiber.as
        (Discrete.eq_of_hom g.fiber) }
  map_id P := by
    refine ObjectProperty.hom_ext _ (TwoFibreProductOver.Hom.ext' ?_ ?_) <;>
      exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl (by apply Discrete.hom_eq)
  map_comp f g := by
    refine ObjectProperty.hom_ext _ (TwoFibreProductOver.Hom.ext' ?_ ?_) <;>
      exact Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl (by apply Discrete.hom_eq)
  w := rfl

/-- `AlgebraicGeometry.Stack.isomStackOfSpace` is faithful: a morphism of the category attached to
a presheaf of sets is determined by its base. -/
instance faithful_isomStackOfSpace (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomStackOfSpace B S hS Z hZ x₁ x₂).toFunctor.Faithful where
  map_injective {P Q} g g' h :=
    Pseudofunctor.CoGrothendieck.Hom.ext _ _
      (congrArg (fun k => k.hom.hbase) h) (by apply Discrete.hom_eq)

/-- `AlgebraicGeometry.Stack.isomStackOfSpace` is full: the two components of a morphism between
two sections are the morphism of the category of elements of `Z` over its base, and its comparison
square says that the source section is the restriction of the target one
(`AlgebraicGeometry.Stack.pointRestrict_uniq`). -/
instance full_isomStackOfSpace (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomStackOfSpace B S hS Z hZ x₁ x₂).toFunctor.Full where
  map_surjective {P Q} k := by
    have hbase : k.hom.a.base = k.hom.hbase :=
      fibredCategory_hom_base_eq_of_isHomLift B S hS _ _ k.hom.ha
    have hz : P.fiber.as.1 = Z.map k.hom.hbase.op Q.fiber.as.1 := by
      have h1 : P.fiber.as.1 = Z.map k.hom.a.base.op Q.fiber.as.1 :=
        Discrete.eq_of_hom k.hom.a.fiber
      rwa [hbase] at h1
    have ha : k.hom.a = spacePointHom.{u, w} B S hS Z hZ k.hom.hbase.op Q.fiber.as.1
        P.fiber.as.1 hz :=
      fibredCategory_hom_eq_of_isHomLift B S hS k.hom.hbase _ _ k.hom.ha
        (spacePointHom_isHomLift.{u, w} B S hS Z hZ k.hom.hbase.op _ _ _)
    have hb : k.hom.b = spacePointHom.{u, w} B S hS Z hZ k.hom.hbase.op Q.fiber.as.1
        P.fiber.as.1 hz :=
      fibredCategory_hom_eq_of_isHomLift B S hS k.hom.hbase _ _ k.hom.hb
        (spacePointHom_isHomLift.{u, w} B S hS Z hZ k.hom.hbase.op _ _ _)
    have hs : P.fiber.as =
        (isomSpaceOverSpace B S hS Z hZ x₁ x₂).map k.hom.hbase.op Q.fiber.as := by
      refine isomSection_eq_of_pointHomCongr B S hS Z hZ x₁ x₂ _ _ P.fiber.as.1 rfl hz.symm ?_
      change P.fiber.as.2.1 = pointHomCongr B S hS Z hZ x₁ x₂ hz.symm
        (pointRestrict B S hS Z hZ x₁ x₂ k.hom.hbase.op Q.fiber.as.1 _ rfl Q.fiber.as.2.1)
      refine Eq.trans ?_
        (pointHomCongr_pointRestrict B S hS Z hZ x₁ x₂ _ _ rfl hz hz.symm _).symm
      refine pointRestrict_uniq B S hS Z hZ x₁ x₂ _ _ _ hz _ _ ?_
      have hw := k.hom.w
      rw [ha, hb] at hw
      exact hw.symm
    refine ⟨⟨k.hom.hbase, Discrete.eqToHom hs⟩, ?_⟩
    exact ObjectProperty.hom_ext _ (TwoFibreProductOver.Hom.ext' ha.symm hb.symm)

/-- `AlgebraicGeometry.Stack.isomStackOfSpace` is essentially surjective: an object of
`Isom_𝒳(x₁, x₂)` is a point `z` of `Z` over `W` on both factors together with a vertical
isomorphism `x₁(z) ≅ x₂(z)`, which is a section of the isomorphism sheaf over `W`. -/
instance essSurj_isomStackOfSpace (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomStackOfSpace B S hS Z hZ x₁ x₂).toFunctor.EssSurj where
  mem_essImage A := by
    obtain ⟨⟨W, t, t', ht, ht', e, he⟩, htt'⟩ := A
    change t = t' at htt'
    subst htt'
    obtain ⟨W₀, ⟨z⟩⟩ := t
    change W₀ = W at ht
    subst ht
    refine ⟨⟨W₀, ⟨⟨z, ⟨⟨e.hom, he⟩, isIso_fiberHom B S hS 𝒳 _⟩⟩⟩⟩, ⟨eqToIso ?_⟩⟩
    have : fiberInclusion.mapIso (@asIso _ _ _ _ (⟨e.hom, he⟩ :
        pointFiber B S hS Z hZ x₁ W₀ z ⟶ pointFiber B S hS Z hZ x₂ W₀ z)
        (isIso_fiberHom B S hS 𝒳 _)) = e := Iso.ext rfl
    refine ObjectProperty.FullSubcategory.ext ?_
    change TwoFibreProductOver.mk W₀ _ _ rfl rfl _ _ = TwoFibreProductOver.mk W₀ _ _ rfl ht' e he
    simp only [this]
    rfl

/-- **Stacks 06PP: the isomorphism sheaf is the category fibred in groupoids of isomorphisms
between the two points.** `AlgebraicGeometry.Stack.isomStackOfSpace` is an equivalence. -/
instance isEquivalence_isomStackOfSpace (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomStackOfSpace B S hS Z hZ x₁ x₂).toFunctor.IsEquivalence where

/-! ### Transport of the relative property to the isomorphism sheaves -/

/-- **The condition of Stacks 03YK at `P`**, for a 1-morphism of categories fibred in groupoids
over the big fppf site of `S`, written without the instance and representability arguments of
`AlgebraicGeometry.Stack.HasRelativeProperty`, which it agrees with definitionally: every
algebraic space representing the base change of `f` along a scheme-valued point of its target has
structural morphism with `P`. `AlgebraicGeometry.Stack.IsProper` is this at properness. -/
abbrev RelativePropertyHolds (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (c : 𝒜 ⟶ 𝒞) :
    Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒞.val.obj)
    (_hy : y ⋙ 𝒞.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒜.val.p 𝒞.val.p y
          (CatFiberedInGroupoids.homFunctor c))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- An isomorphism of two objects of `Isom_𝒵(z₁, z₂)` over the same point whose comparison
isomorphisms have the same underlying morphism; its components are identities. -/
def isomStackIsoOfHomEq {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (z₁ z₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒵) (W : BigFppfOver B S hS)
    (t : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj)
    (ht : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj t = W)
    (e e' : z₁.hom.hom.toFunctor.obj t ≅ z₂.hom.hom.toFunctor.obj t)
    (he : 𝒵.val.val.p.IsHomLift (𝟙 W) e.hom) (he' : 𝒵.val.val.p.IsHomLift (𝟙 W) e'.hom)
    (h : e.hom = e'.hom) :
    (⟨⟨W, t, t, ht, ht, e, he⟩, rfl⟩ : (HigherDiagonal.isomStack B S hS Z hZ z₁ z₂).val.obj) ≅
      ⟨⟨W, t, t, ht, ht, e', he'⟩, rfl⟩ where
  hom := ObjectProperty.homMk
    ⟨𝟙 W, 𝟙 t, 𝟙 t, IsHomLift.id ht, IsHomLift.id ht, by simp [h]⟩
  inv := ObjectProperty.homMk
    ⟨𝟙 W, 𝟙 t, 𝟙 t, IsHomLift.id ht, IsHomLift.id ht, by simp [h]⟩
  hom_inv_id := ObjectProperty.hom_ext _
    (TwoFibreProductOver.Hom.ext' (Category.id_comp _) (Category.id_comp _))
  inv_hom_id := ObjectProperty.hom_ext _
    (TwoFibreProductOver.Hom.ext' (Category.id_comp _) (Category.id_comp _))

/-- **The square comparing the two readings of the map on isomorphism sheaves.** Read through
`AlgebraicGeometry.Stack.isomStackOfSpace`, the map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(f x₁, f x₂)` of
Stacks 0CPK (3) on presheaves is the map `AlgebraicGeometry.Stack.HigherDiagonal.isomMap` of
categories fibred in groupoids: both apply `f` to an isomorphism and keep the point of `Z`. -/
noncomputable def isomStackOfSpaceCompIsomMapIso (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    BasedFunctor.comp (isomStackOfSpace B S hS Z hZ x₁ x₂)
        (HigherDiagonal.isomMap B S hS f Z hZ x₁ x₂).hom ≅
      BasedFunctor.comp
        (algebraicSpaceStackMap.{u, w} B S hS
          (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂)
          (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f))
          (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)).hom.hom
        (isomStackOfSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f)) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun P => isomStackIsoOfHomEq B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) P.base
        (spacePoint.{u, w} B S hS Z hZ P.base P.fiber.as.1) rfl _ _ _ _ rfl)
      (fun {P Q} g => ObjectProperty.hom_ext _ (TwoFibreProductOver.Hom.ext'
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm))))
    (fun _ => IsHomLift.of_fac' _ _ _ rfl rfl (by
      simp only [Category.id_comp]
      rfl))

/-- **Stacks 0CPL (2) read for the isomorphism sheaves.** A property of the map
`AlgebraicGeometry.Stack.HigherDiagonal.isomMap` of categories fibred in groupoids, in the sense
of Stacks 03YK, is a property of the map of isomorphism sheaves
`AlgebraicGeometry.Stack.isomSpaceOverSpaceMap` of Stacks 0CPK (3): the two are related by the
equivalences `AlgebraicGeometry.Stack.isomStackOfSpace`, and Stacks 0457 applies. -/
theorem relativePropertyHolds_isomSpaceOverSpaceMap (P : MorphismProperty (AlgebraicSpaces B S hS))
    (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (h : RelativePropertyHolds B S hS P (HigherDiagonal.isomMap B S hS f Z hZ x₁ x₂)) :
    RelativePropertyHolds B S hS P
      (algebraicSpaceStackMap.{u, w} B S hS
        (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂)
        (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f))
        (isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂)).hom :=
  relativeProperty_of_equivalences B S hS P _ _ (isomStackOfSpace B S hS Z hZ x₁ x₂)
    (isomStackOfSpace B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f))
    (isomStackOfSpaceCompIsomMapIso B S hS Z hZ f x₁ x₂) h

/-- **Stacks 0457 for the 1-morphisms induced by morphisms of algebraic spaces.** The condition of
Stacks 03YK at `P` passes from the 1-morphism induced by `φ : X ⟶ Y` to the one induced by
`ψ : X' ⟶ Y'` whenever the two are related by isomorphisms `X' ≅ X` and `Y' ≅ Y`: these induce
equivalences of algebraic stacks, and the square of induced 1-morphisms commutes strictly. -/
theorem relativePropertyHolds_algebraicSpaceStackMap_of_iso
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y') (φ : X ⟶ Y) (ψ : X' ⟶ Y') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (hw : eX.hom ≫ φ = ψ ≫ eY.hom)
    (h : RelativePropertyHolds B S hS P (algebraicSpaceStackMap.{u, w} B S hS hX hY φ).hom) :
    RelativePropertyHolds B S hS P (algebraicSpaceStackMap.{u, w} B S hS hX' hY' ψ).hom := by
  have := AlgebraicStacks.isEquivalence_homFunctor_algebraicSpaceStackMap.{u, w} B S hS hX' hX eX
  have := AlgebraicStacks.isEquivalence_homFunctor_algebraicSpaceStackMap.{u, w} B S hS hY' hY eY
  have h₁ := congrArg (fun k => k.hom.hom)
    (AlgebraicStacks.algebraicSpaceStackMap_comp.{u, w} B S hS hX' hX hY eX.hom φ)
  have h₂ := congrArg (fun k => k.hom.hom)
    (AlgebraicStacks.algebraicSpaceStackMap_comp.{u, w} B S hS hX' hY' hY ψ eY.hom)
  have h₃ := congrArg (fun k => (algebraicSpaceStackMap.{u, w} B S hS hX' hY k).hom.hom) hw
  exact relativeProperty_of_equivalences B S hS P _ _
    (algebraicSpaceStackMap.{u, w} B S hS hX' hX eX.hom).hom.hom
    (algebraicSpaceStackMap.{u, w} B S hS hY' hY eY.hom).hom.hom
    (eqToIso (h₁.symm.trans (h₃.trans h₂))) h

/-- **The fibres of the algebraic stack of an algebraic space are discrete**: two morphisms of a
fibre with the same source and target are equal. -/
theorem algebraicSpaceStack_fiber_hom_eq {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {W : BigFppfOver B S hS}
    {a b : (algebraicSpaceStack.{u, w} B S hS Y hY).val.val.p.Fiber W} (φ ψ : a ⟶ b) : φ = ψ :=
  Subtype.ext (fibredCategory_hom_eq_of_isHomLift B S hS (𝟙 W) _ _ φ.2 ψ.2)

section SpaceTarget

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
  (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)

/-- **Over an algebraic space every section of the isomorphism sheaf is the one a 2-morphism
names.** If the target of `f` is an algebraic space then the fibres of its algebraic stack are
discrete, so the structure morphism of `Isom_Y(f x₁, f x₂)` to `Z` is inverse to the section
determined by any 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f`. -/
theorem isomSpaceOverSpaceProj_comp_twistedSection (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    isomSpaceOverSpaceProj B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) ≫
        twistedSection B S hS Z hZ f x₁ x₂ α = 𝟙 _ :=
  Functor.presheafHom_ext fun _ s =>
    (isomSection_mk_eq_iff B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) s.1 _ s.2.2).mpr
      (algebraicSpaceStack_fiber_hom_eq.{u, w} B S hS hY _ _)

/-- Over an algebraic space, the section of the isomorphism sheaf named by a 2-morphism
`α : x₁ ≫ f ⟶ x₂ ≫ f` is an isomorphism. -/
instance isIso_twistedSection (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsIso (twistedSection B S hS Z hZ f x₁ x₂ α) :=
  ⟨⟨isomSpaceOverSpaceProj B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f),
    twistedSection_comp_proj B S hS Z hZ f x₁ x₂ α,
    isomSpaceOverSpaceProj_comp_twistedSection B S hS Z hZ hY f x₁ x₂ α⟩⟩

/-- Over an algebraic space, the map on isomorphism sheaves induced by `f` is the structure
morphism to `Z` followed by the section named by a 2-morphism. -/
theorem isomSpaceOverSpaceMap_eq_proj_comp_twistedSection (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    isomSpaceOverSpaceMap B S hS Z hZ f x₁ x₂ =
      isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂ ≫ twistedSection B S hS Z hZ f x₁ x₂ α :=
  Functor.presheafHom_ext fun _ s =>
    (isomSection_mk_eq_iff B S hS Z hZ (x₁ ≫ f) (x₂ ≫ f) s.1 _ _).mpr
      (algebraicSpaceStack_fiber_hom_eq.{u, w} B S hS hY _ _)

/-- **Stacks 0CPL (2) over an algebraic space, for any property.** Let `f : 𝒳 ⟶ Y` be a
1-morphism to an algebraic space and `x₁, x₂ : Z ⟶ 𝒳` with `x₁ ≫ f = x₂ ≫ f`. If the map
`Isom_𝒳(x₁, x₂) ⟶ Isom_Y(f x₁, f x₂)` of categories fibred in groupoids has the property `P` of
Stacks 03YK, so has the 1-morphism induced by the structure morphism `Isom_𝒳(x₁, x₂) ⟶ Z`:
`Isom_Y(f x₁, f x₂) ⟶ Z` is an isomorphism, the fibres of `Y` being discrete. -/
theorem relativePropertyHolds_isomSpaceOverSpaceProj (P : MorphismProperty (AlgebraicSpaces B S hS))
    (h : x₁ ≫ f = x₂ ≫ f)
    (hP : RelativePropertyHolds B S hS P (HigherDiagonal.isomMap B S hS f Z hZ x₁ x₂)) :
    RelativePropertyHolds B S hS P
      (algebraicSpaceStackMap.{u, w} B S hS
        (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂) hZ
        (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂)).hom :=
  relativePropertyHolds_algebraicSpaceStackMap_of_iso B S hS P _ _ _ hZ _ _ (Iso.refl _)
    (asIso (twistedSection B S hS Z hZ f x₁ x₂ (eqToHom h)))
    ((Category.id_comp _).trans
      (isomSpaceOverSpaceMap_eq_proj_comp_twistedSection B S hS Z hZ hY f x₁ x₂ (eqToHom h)))
    (relativePropertyHolds_isomSpaceOverSpaceMap B S hS Z hZ P f x₁ x₂ hP)

end SpaceTarget

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CPL (2), for the isomorphism sheaf over an algebraic space.** Let
`f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space over `S`,
let `Z` be an algebraic space over `S` and let `x₁, x₂ : Z ⟶ 𝒳` with `x₁ ≫ f = x₂ ≫ f`. Then the
algebraic space `Isom_𝒳(x₁, x₂)` of Stacks 06PP is proper over `Z`.

Stacks 0CPL (2) makes `Isom_𝒳(x₁, x₂) ⟶ Isom_Y(f x₁, f x₂)` proper; over an algebraic space the
target is `Z` itself, its fibres being discrete. -/
theorem isProper_isomSpaceOverSpaceProj_of_isSeparated {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hf : IsSeparated B S hS f)
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (h : x₁ ≫ f = x₂ ≫ f) :
    Space.IsProper B S hS (isomSpaceOverSpaceProj B S hS Z hZ x₁ x₂) :=
  (isProper_algebraicSpaceStackMap_hom_iff.{u, w} B S hS
    (isAlgebraicSpace_isomSpaceOverSpace.{u, w} B S hS Z hZ x₁ x₂) hZ _).1
    (relativePropertyHolds_isomSpaceOverSpaceProj B S hS Z hZ hY f x₁ x₂
      (fun _ _ m => Space.IsProper B S hS m.hom) h
      (HigherDiagonal.isProper_isomMap_of_isSeparated B S hS f Z hZ x₁ x₂ hf))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
