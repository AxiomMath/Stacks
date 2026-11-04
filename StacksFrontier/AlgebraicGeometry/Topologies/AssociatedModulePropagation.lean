module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFaithful

/-!
# Propagating agreement of maps of associated modules off the affine objects of a site

Tag 03DU attaches to a quasi-coherent module `M` on a scheme `S` a presheaf of modules `Mᵃ` on a
site `C` of schemes over `S`, and Descent, Lemma 0GN7 asserts that `M ↦ Mᵃ` is fully faithful on
quasi-coherent modules. This file shows that if the arrows of `C` factoring through an object of a
class `P` cover every object, and `Nᵃ` is a sheaf, then a map `Mᵃ ⟶ Nᵃ` is determined by its
components at the objects of `P`; in particular at the affine objects. So the fullness clause of
Lemma 0GN7 follows from its restriction to the affine objects of the site.

## Main results

* `CategoryTheory.Presheaf.hom_ext_of_coverByImage`: two maps of presheaves into a sheaf which
  agree on the objects in the image of a functor whose `CategoryTheory.Sieve.coverByImage` sieves
  are covering are equal.
* `Stacks.Sites.hom_ext_associatedModulePresheaf_of_property`: two maps `Mᵃ ⟶ Nᵃ` which agree
  over a covering class of objects are equal.
* `Stacks.Sites.hom_ext_associatedModulePresheaf_of_isAffine`: two maps `Mᵃ ⟶ Nᵃ` which agree
  over the affine objects are equal, if the arrows factoring through an affine object cover.
* `Stacks.Sites.coverByImage_isAffine_mem`: on a site all of whose objects have affine underlying
  scheme that covering hypothesis holds, for every topology.
* `Stacks.Sites.surjective_associatedModuleMap_of_property` and
  `Stacks.Sites.surjective_associatedModuleMap_of_isAffine`: the fullness clause of Descent,
  Lemma 0GN7 follows from its restriction to a covering class of objects, respectively to the
  affine objects.
* `Stacks.Sites.bijective_associatedModuleMap_of_isAffine`: over an affine base, `M ↦ Mᵃ` is
  bijective on morphisms, given its fullness at the affine objects.

## Implementation notes

The covering hypothesis is `CategoryTheory.Sieve.coverByImage` of the inclusion of the affine
objects — the arrows that *factor* through an affine object — and not
`CategoryTheory.Sieve.ofObjects` of the affine objects, the arrows whose *source* has some
morphism to an affine object. By `CategoryTheory.Sieve.pullback_ofObjects_eq_top`, on a site
whose terminal object is affine the latter is the maximal sieve, so it would hold for every
topology, including the trivial one.

`CategoryTheory.Presheaf.hom_ext_of_coverByImage` is proved on the components at objects of the
form `op X`: at `X : Cᵒᵖ` the arrows of the covering sieve are indexed by morphisms into
`X.unop`, and a rewrite with naturality fails its motive check although the two spellings are
definitionally equal.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.Presheaf

/-- Let `G : D ⥤ C` be a functor such that for every object `X` of `C` the arrows of `C`
factoring through an object in the image of `G` form a covering sieve, and let `P` be a sheaf.
Then two maps `Q ⟶ P` out of an arbitrary presheaf which agree at every `G.obj Y` are equal. -/
public theorem hom_ext_of_coverByImage {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {A : Type u₃} [Category.{v₃} A] (G : D ⥤ C)
    {J : GrothendieckTopology C} {Q P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (hcover : ∀ X : C, Sieve.coverByImage G X ∈ J X)
    {α β : Q ⟶ P} (h : ∀ Y : D, α.app (op (G.obj Y)) = β.app (op (G.obj Y))) :
    α = β := by
  have key : ∀ X : C, α.app (op X) = β.app (op X) := by
    intro X
    refine hP.hom_ext ⟨_, hcover X⟩ _ _ ?_
    rintro ⟨Z, f, ⟨⟨Y, lift, map, fac⟩⟩⟩
    dsimp only
    rw [← fac, op_comp, P.map_comp, ← Category.assoc, ← Category.assoc,
      ← α.naturality map.op, ← β.naturality map.op, h Y]
  exact NatTrans.ext (funext fun ⟨X⟩ => key X)

end CategoryTheory.Presheaf

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
    (J : GrothendieckTopology C)

/-! ### Propagation off a covering class of objects -/

/-- Let `C` be a site of schemes over `S`, let `P` be a property of its objects such that the
arrows factoring through an object with `P` cover every object, and let `M`, `N` be
quasi-coherent modules on `S` whose associated presheaf `Nᵃ` is a sheaf. Then two maps
`Mᵃ ⟶ Nᵃ` of associated presheaves of modules which agree over the objects with `P` are equal. -/
public theorem hom_ext_associatedModulePresheaf_of_property (P : ObjectProperty C)
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage (ObjectProperty.ι P) X ∈ J X)
    {a b : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver}
    (h : ∀ X : C, P X → a.app (op X) = b.app (op X)) :
    a = b := by
  have hN' : Presheaf.IsSheaf J
      ((PresheafOfModules.toPresheaf (structurePresheaf S toOver)).obj
        (associatedModulePresheaf S N toOver)) := hN
  refine (PresheafOfModules.toPresheaf (structurePresheaf S toOver)).map_injective
    (Presheaf.hom_ext_of_coverByImage _ hN' hcover fun Y => ?_)
  ext x
  exact congrArg (fun φ => φ x) (congrArg ModuleCat.Hom.hom (h Y.obj Y.property))

/-! ### Propagation off the affine objects -/

/-- Let `C` be a site of schemes over `S` in which the arrows factoring through an object with
affine underlying scheme cover every object, and let `M`, `N` be quasi-coherent modules on `S`
whose associated presheaf `Nᵃ` is a sheaf. Then two maps `Mᵃ ⟶ Nᵃ` of associated presheaves of
modules which agree over the affine objects of the site are equal. -/
public theorem hom_ext_associatedModulePresheaf_of_isAffine
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    {a b : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver}
    (h : ∀ X : C, IsAffine (toOver.obj X).left → a.app (op X) = b.app (op X)) :
    a = b :=
  hom_ext_associatedModulePresheaf_of_property S toOver J _ hN hcover h

/-- If every object of the site has affine underlying scheme, then for every topology the arrows
factoring through an object with affine underlying scheme form a covering sieve of each
object. -/
public theorem coverByImage_isAffine_mem (hC : ∀ X : C, IsAffine (toOver.obj X).left) (X : C) :
    Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X := by
  have h : Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X = ⊤ :=
    Sieve.id_mem_iff_eq_top.1 ⟨⟨⟨X, hC X⟩, 𝟙 _, 𝟙 _, by simp⟩⟩
  exact h ▸ J.top_mem X

/-! ### The fullness clause reduced to a covering class of objects -/

/-- Suppose that the arrows factoring through an object with `P` cover every object, and that
every map `Mᵃ ⟶ Nᵃ` of associated presheaves of modules agrees, over the objects with `P`, with
the map induced by some morphism `M ⟶ N`. Then, `Nᵃ` being a sheaf, every map `Mᵃ ⟶ Nᵃ` is
induced by a morphism `M ⟶ N`. -/
public theorem surjective_associatedModuleMap_of_property (P : ObjectProperty C)
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage (ObjectProperty.ι P) X ∈ J X)
    (hP : ∀ a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver,
      ∃ φ : M ⟶ N, ∀ X : C, P X →
        (associatedModuleMap S toOver φ).app (op X) = a.app (op X)) :
    Function.Surjective fun φ : M ⟶ N => associatedModuleMap S toOver φ := fun a =>
  (hP a).imp fun _ hφ => hom_ext_associatedModulePresheaf_of_property S toOver J P hN hcover hφ

/-! ### The fullness clause reduced to the affine objects -/

/-- Suppose that every map `Mᵃ ⟶ Nᵃ` of associated presheaves of modules agrees, over the
objects of the site with affine underlying scheme, with the map induced by some morphism `M ⟶ N`.
Then, `Nᵃ` being a sheaf and the arrows factoring through an affine object covering, every map
`Mᵃ ⟶ Nᵃ` is induced by a morphism `M ⟶ N`. -/
public theorem surjective_associatedModuleMap_of_isAffine
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (haff : ∀ a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver,
      ∃ φ : M ⟶ N, ∀ X : C, IsAffine (toOver.obj X).left →
        (associatedModuleMap S toOver φ).app (op X) = a.app (op X)) :
    Function.Surjective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  surjective_associatedModuleMap_of_property S toOver J _ hN hcover haff

/-- Over an affine base `S`, on a site which contains an object `X₀` with invertible structure
morphism and in which the arrows factoring through an affine object cover, and for
quasi-coherent `M`, `N` with `Nᵃ` a sheaf, the map
`φ ↦ Stacks.Sites.associatedModuleMap S toOver φ` is bijective as soon as every map `Mᵃ ⟶ Nᵃ`
agrees with some `φᵃ` over the affine objects. -/
public theorem bijective_associatedModuleMap_of_isAffine [IsAffine S]
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf J (associatedPresheaf S N toOver))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ J X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom]
    (haff : ∀ a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver,
      ∃ φ : M ⟶ N, ∀ X : C, IsAffine (toOver.obj X).left →
        (associatedModuleMap S toOver φ).app (op X) = a.app (op X)) :
    Function.Bijective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  ⟨associatedModuleMap_injective S toOver X₀,
    surjective_associatedModuleMap_of_isAffine S toOver J hN hcover haff⟩

end Stacks.Sites

end
