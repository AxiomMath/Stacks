module

public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Adjoint pairs on sheaves of algebraic structures compatible with the underlying sheaves of sets

Let `f = (f⁻¹, f_*)` be a morphism of topoi `Sh(C) → Sh(D)` and let `s : A ⥤ Type w` be the
forgetful functor of a type of algebraic structure. Stacks 00YV asserts, for seven such types,
that `f` gives an adjoint pair `(f⁻¹, f_*)` on sheaves with values in `A`, *compatible with taking
the underlying sheaves of sets*. This file packages what that assertion consists of, for one `A`:

* two functors `f⁻¹ : Sh(D, A) ⥤ Sh(C, A)` and `f_* : Sh(C, A) ⥤ Sh(D, A)`;
* an adjunction `f⁻¹ ⊣ f_*` between them;
* natural isomorphisms identifying the underlying sheaf of sets of `f⁻¹ F`, resp. `f_* G`, with
  `f⁻¹` of the underlying sheaf of sets of `F`, resp. `f_*` of that of `G`;
* compatibility of the adjunctions: forgetting the structure carries the unit of `f⁻¹ ⊣ f_*` on
  `A`-valued sheaves to the unit of `f⁻¹ ⊣ f_*` on sheaves of sets, read through the two
  isomorphisms. Since an adjunction is determined by its unit, this says that the hom-set
  bijection on `A`-valued sheaves is the restriction of the one on sheaves of sets, which is how
  the source proves adjointness.

## Main definitions

* `Stacks.Topos.StructureAdjunction`: the data above, for a morphism of topoi `f` and a functor
  `s : A ⥤ Type w`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Topos

universe w v u v' u' a b

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- For a morphism of topoi `f : Sh(C) → Sh(D)` and a functor `s : A ⥤ Type w` (the underlying
set of an algebraic structure), an adjoint pair `f⁻¹ ⊣ f_*` on sheaves with values in `A`
compatible with taking the underlying sheaves of sets: the underlying sheaf of sets of `f⁻¹ F`,
resp. `f_* G`, is `f⁻¹`, resp. `f_*`, of the underlying sheaf of sets, naturally, and under
these identifications the unit of the adjunction on `A`-valued sheaves is the unit of `f⁻¹ ⊣ f_*`
on sheaves of sets. -/
structure StructureAdjunction (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))
    {A : Type a} [Category.{b} A] (s : A ⥤ Type w) [J.HasSheafCompose s]
    [K.HasSheafCompose s] where
  /-- The inverse image `f⁻¹ : Sh(D, A) ⥤ Sh(C, A)`. -/
  inverseImage : Sheaf K A ⥤ Sheaf J A
  /-- The direct image `f_* : Sh(C, A) ⥤ Sh(D, A)`. -/
  pushforward : Sheaf J A ⥤ Sheaf K A
  /-- The inverse image is left adjoint to the direct image. -/
  adj : inverseImage ⊣ pushforward
  /-- The underlying sheaf of sets of `f⁻¹ F` is `f⁻¹` of the underlying sheaf of sets of `F`. -/
  inverseImageForgetIso :
    inverseImage ⋙ sheafCompose J s ≅ sheafCompose K s ⋙ f.inverseImage
  /-- The underlying sheaf of sets of `f_* G` is `f_*` of the underlying sheaf of sets of `G`. -/
  pushforwardForgetIso :
    pushforward ⋙ sheafCompose K s ≅ sheafCompose J s ⋙ f.pushforward
  /-- Forgetting the structure carries the unit of `adj` to the unit of `f⁻¹ ⊣ f_*` on sheaves
  of sets. -/
  forget_map_unit_app (F : Sheaf K A) :
    (sheafCompose K s).map (adj.unit.app F) ≫ pushforwardForgetIso.hom.app (inverseImage.obj F) ≫
        f.pushforward.map (inverseImageForgetIso.hom.app F) =
      f.adj.unit.app ((sheafCompose K s).obj F)

end Stacks.Topos
