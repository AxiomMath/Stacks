module

public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.ProductSections
public import StacksFrontier.AlgebraicGeometry.GenericPointSheaf.StalkUnits

/-!
# The product of the local schemes at the generic points

The right-hand side of the generic-point decomposition of the sheaf of meromorphic functions is a
product of the pushed-forward structure sheaves of the local schemes `Spec 𝒪_{X, η}` at the
generic points. This file builds that product as a sheaf of commutative rings, with sections over
an open set equal, by definition, to the product of the sections of the factors, and records its
canonical structure-sheaf algebra map.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointProduct.stalkPresheaf`: one factor, the pushforward of the
  structure sheaf of `Spec 𝒪_{X, η}` along the canonical morphism to `X`.
* `Stacks.AlgebraicGeometry.GenericPointProduct.piStalkSheaf`: the product of the factors.
* `Stacks.AlgebraicGeometry.GenericPointProduct.toPiStalkSheaf`: the canonical morphism from the
  structure sheaf, whose component at an open set sends a section to its family of pullbacks.

## Implementation notes

The product is built by hand rather than as a categorical product, so that its sections are
definitionally the dependent function type; the categorical product of sheaves has only
isomorphic sections, and every later computation would have to carry that isomorphism. The sheaf
condition is checked componentwise through the unique-gluing formulation.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointProduct

variable (X : Scheme.{u})

/-- One factor of the generic-point product: the structure sheaf of `Spec 𝒪_{X, η}`, pushed
forward along the canonical morphism `Spec 𝒪_{X, η} ⟶ X`. Its sections over `U` are the sections
of `Spec 𝒪_{X, η}` over the preimage of `U`. -/
noncomputable abbrev stalkPresheaf (η : genericPoints X) : TopCat.Presheaf CommRingCat.{u} X :=
  (X.fromSpecStalk η.1).base _* (Spec (X.presheaf.stalk η.1)).presheaf

/-- Each factor of the generic-point product is a sheaf, being a pushforward of one. -/
theorem isSheaf_stalkPresheaf (η : genericPoints X) : (stalkPresheaf X η).IsSheaf :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf _ (Spec (X.presheaf.stalk η.1)).sheaf.property

/-- One factor of the generic-point product, as a sheaf. -/
noncomputable abbrev stalkSheaf (η : genericPoints X) : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨stalkPresheaf X η, isSheaf_stalkPresheaf X η⟩

/-- The presheaf of commutative rings whose sections over an open set are the product, over the
generic points of `X`, of the sections of the local scheme at that generic point. -/
noncomputable abbrev piStalkPresheaf : TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (∀ η : genericPoints X, (stalkPresheaf X η).obj U)
  map {_ _} i := CommRingCat.ofHom
    (RingHom.pi fun η ↦ ((stalkPresheaf X η).map i).hom.comp (Pi.evalRingHom _ η))
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun s ↦ funext fun η ↦ ?_)
    change ((stalkPresheaf X η).map (𝟙 U)).hom (s η) = s η
    rw [(stalkPresheaf X η).map_id]
    rfl
  map_comp {U V W} i j := by
    refine CommRingCat.hom_ext (RingHom.ext fun s ↦ funext fun η ↦ ?_)
    change ((stalkPresheaf X η).map (i ≫ j)).hom (s η) =
      ((stalkPresheaf X η).map j).hom (((stalkPresheaf X η).map i).hom (s η))
    rw [(stalkPresheaf X η).map_comp]
    rfl

/-- The restriction maps of the generic-point product act componentwise. -/
theorem piStalkPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (s : (piStalkPresheaf X).obj U) (η : genericPoints X) :
    (piStalkPresheaf X).map i s η = (stalkPresheaf X η).map i (s η) := rfl

/-- The generic-point product is a sheaf: a compatible family glues componentwise, and the
gluing is unique because it is unique in each factor. -/
theorem isSheaf_piStalkPresheaf : (piStalkPresheaf X).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  choose s hs huniq using fun η : genericPoints X ↦
    (stalkSheaf X η).existsUnique_gluing U (fun i ↦ sf i η) fun i j ↦ congrFun (hsf i j) η
  refine ⟨fun η ↦ s η, fun i ↦ funext fun η ↦ hs η i, fun t ht ↦ funext fun η ↦ ?_⟩
  exact huniq η (t η) fun i ↦ congrFun (ht i) η

/-- The product, over the generic points of `X`, of the structure sheaves of the local schemes
`Spec 𝒪_{X, η}` pushed forward to `X`. -/
noncomputable def piStalkSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨piStalkPresheaf X, isSheaf_piStalkPresheaf X⟩

/-- The underlying presheaf of `piStalkSheaf X` is `piStalkPresheaf X`. -/
@[simp]
theorem piStalkSheaf_presheaf : (piStalkSheaf X).presheaf = piStalkPresheaf X := rfl

/-- The canonical morphism from the structure sheaf of `X` to the generic-point product: a
section is sent to the family of its pullbacks to the local schemes at the generic points. -/
noncomputable abbrev toPiStalkPresheaf : X.presheaf ⟶ piStalkPresheaf X where
  app U := CommRingCat.ofHom (RingHom.pi fun η ↦ ((X.fromSpecStalk η.1).c.app U).hom)
  naturality {U V} i := by
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ funext fun η ↦ ?_)
    change ((X.fromSpecStalk η.1).c.app V).hom (X.presheaf.map i r) =
      ((stalkPresheaf X η).map i).hom (((X.fromSpecStalk η.1).c.app U).hom r)
    exact ConcreteCategory.congr_hom ((X.fromSpecStalk η.1).c.naturality i) r

/-- The component of `toPiStalkPresheaf X` at the generic point `η` is the pullback of sections
along the canonical morphism `Spec 𝒪_{X, η} ⟶ X`. -/
theorem toPiStalkPresheaf_app_apply (U : (Opens X)ᵒᵖ) (r : X.presheaf.obj U)
    (η : genericPoints X) :
    (toPiStalkPresheaf X).app U r η = (X.fromSpecStalk η.1).c.app U r := rfl

/-- The canonical morphism from the structure sheaf to the generic-point product, as a morphism
of sheaves of commutative rings. -/
noncomputable def toPiStalkSheaf : X.sheaf ⟶ piStalkSheaf X := ⟨toPiStalkPresheaf X⟩

end Stacks.AlgebraicGeometry.GenericPointProduct
