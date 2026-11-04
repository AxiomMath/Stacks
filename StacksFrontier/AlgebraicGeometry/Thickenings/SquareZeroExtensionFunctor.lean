module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension

/-!
# Functoriality of the realization of a square-zero extension

A relative square-zero extension `E` of the structure sheaf of a scheme `X` over `S` is
realized by a first-order thickening `X ⊆ X'` over `S`; the realizing data is recorded by
`Stacks.Thickenings.Realization`. This file upgrades that existence statement to a
construction which is functorial in the extension.

A morphism of square-zero extensions over `S` consists of a morphism `X₁ ⟶ X₂` of the
underlying schemes together with a morphism of the ringed spaces carrying the two extension
sheaves, compatible with the two inclusions of the structure sheaves and with the two algebra
structures over `S`. Such a morphism induces a morphism of the realizations, and the
assignment is compatible with identities and composition. As a consequence the realization is
unique up to a canonical isomorphism over `S` under `X`.

## Main definitions

* `Stacks.Thickenings.SquareZeroExtension.Hom`: a morphism of relative square-zero extensions
  over a fixed base.
* `Stacks.Thickenings.SquareZeroExtensionOver`: the category of relative square-zero
  extensions over a fixed base.
* `Stacks.Thickenings.realization`: the realization of a square-zero extension, as a
  construction rather than a mere existence statement.
* `Stacks.Thickenings.Realization.map`: the morphism of realizations induced by a morphism of
  square-zero extensions.
* `Stacks.Thickenings.realizationFunctor`: the realization, as a functor from square-zero
  extensions over `S` to schemes over `S`.

## Main results

* `Stacks.Thickenings.Realization.map_immersion` and
  `Stacks.Thickenings.Realization.map_toBase`: the induced morphism is a morphism of
  thickenings over `S`.
* `Stacks.Thickenings.Realization.map_id` and `Stacks.Thickenings.Realization.map_comp`: the
  identity and composition laws.
* `Stacks.Thickenings.Realization.uniqueIso`: any two realizations of the same extension are
  canonically isomorphic, compatibly with the immersions and with the morphisms to the base.

## Implementation notes

The only input used about a realization is the data recorded in `Realization`: the
isomorphism of sheafed spaces onto the ringed space carrying the extension sheaf, and the two
compatibilities `inclusion_eq` and `toBase_eq`. In particular the induced morphism is built
between arbitrary realizations, not only the chosen one. The nontrivial point is that the
morphism of sheafed spaces obtained by transport is a morphism of locally ringed spaces: its
stalk maps are local because, after composing with the (local) stalk maps of the immersion of
the first thickening, they factor through the stalk maps of two morphisms of schemes.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-- Two morphisms of schemes agree as soon as they agree as morphisms of sheafed spaces. -/
private theorem scheme_hom_ext_of_toShHom {X Y : Scheme.{u}} {a b : X ⟶ Y}
    (h : a.toLRSHom.toShHom = b.toLRSHom.toShHom) : a = b :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (congrArg InducedCategory.Hom.hom h))

/-- The first factor of a composite of ring maps is local as soon as the composite is. -/
private theorem isLocalHom_of_comp' {R T V : CommRingCat.{u}} (a : R ⟶ T) (b : T ⟶ V)
    (h : IsLocalHom (a ≫ b).hom) : IsLocalHom a.hom := by
  have : IsLocalHom (b.hom.comp a.hom) := by rwa [← CommRingCat.hom_comp]
  exact isLocalHom_of_comp a.hom b.hom

variable {S : Scheme.{u}}

/-- A morphism of relative square-zero extensions of structure sheaves over a common base
`S`: a morphism of the underlying schemes together with a morphism of the ringed spaces
carrying the two extension sheaves, compatible with the inclusions of the structure sheaves
and with the algebra structures over `S`. -/
public structure SquareZeroExtension.Hom {X₁ X₂ : Scheme.{u}} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    (E₁ : SquareZeroExtension f₁) (E₂ : SquareZeroExtension f₂) where
  /-- The morphism of the schemes carrying the two extensions. -/
  base : X₁ ⟶ X₂
  /-- The morphism of the ringed spaces carrying the two extension sheaves. -/
  sheafHom : thickenedSpace X₁ E₁.A ⟶ thickenedSpace X₂ E₂.A
  /-- Compatibility with the inclusions of the structure sheaves. -/
  inclusion_comm : E₁.inclusion ≫ sheafHom = base.toLRSHom.toShHom ≫ E₂.inclusion
  /-- Compatibility with the algebra structures over the base. -/
  toBase_comm : sheafHom ≫ E₂.toBase = E₁.toBase

namespace SquareZeroExtension.Hom

variable {X₁ X₂ X₃ : Scheme.{u}} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  {E₁ : SquareZeroExtension f₁} {E₂ : SquareZeroExtension f₂} {E₃ : SquareZeroExtension f₃}

/-- A morphism of square-zero extensions is determined by its two pieces of data. -/
@[ext]
public theorem ext {φ ψ : E₁.Hom E₂} (hbase : φ.base = ψ.base)
    (hsheaf : φ.sheafHom = ψ.sheafHom) : φ = ψ := by
  cases φ; cases ψ; subst hbase; subst hsheaf; rfl

/-- The underlying morphism of schemes of a morphism of square-zero extensions is a morphism
over the base. -/
public theorem base_comp_structureMorphism (φ : E₁.Hom E₂) : φ.base ≫ f₂ = f₁ := by
  apply scheme_hom_ext_of_toShHom
  rw [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom, ← E₂.over_base,
    ← Category.assoc, ← φ.inclusion_comm, Category.assoc, φ.toBase_comm, E₁.over_base]

/-- The identity morphism of a square-zero extension. -/
public def id (E : SquareZeroExtension f₁) : E.Hom E where
  base := 𝟙 X₁
  sheafHom := 𝟙 _
  inclusion_comm := by
    rw [Category.comp_id, show (𝟙 X₁ : X₁ ⟶ X₁).toLRSHom.toShHom = 𝟙 _ from rfl,
      Category.id_comp]
  toBase_comm := Category.id_comp _

/-- The composition of two morphisms of square-zero extensions. -/
public def comp (φ : E₁.Hom E₂) (ψ : E₂.Hom E₃) : E₁.Hom E₃ where
  base := φ.base ≫ ψ.base
  sheafHom := φ.sheafHom ≫ ψ.sheafHom
  inclusion_comm := by
    rw [← Category.assoc, φ.inclusion_comm, Category.assoc, ψ.inclusion_comm,
      Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom, Category.assoc]
  toBase_comm := by rw [Category.assoc, ψ.toBase_comm, φ.toBase_comm]

/-- The identity morphism has the identity as underlying morphism of schemes. -/
@[simp] public theorem id_base (E : SquareZeroExtension f₁) : (Hom.id E).base = 𝟙 X₁ := rfl

/-- The identity morphism has the identity as underlying morphism of ringed spaces. -/
@[simp] public theorem id_sheafHom (E : SquareZeroExtension f₁) :
    (Hom.id E).sheafHom = 𝟙 _ := rfl

/-- Composition composes the underlying morphisms of schemes. -/
@[simp] public theorem comp_base (φ : E₁.Hom E₂) (ψ : E₂.Hom E₃) :
    (φ.comp ψ).base = φ.base ≫ ψ.base := rfl

/-- Composition composes the underlying morphisms of ringed spaces. -/
@[simp] public theorem comp_sheafHom (φ : E₁.Hom E₂) (ψ : E₂.Hom E₃) :
    (φ.comp ψ).sheafHom = φ.sheafHom ≫ ψ.sheafHom := rfl

end SquareZeroExtension.Hom

/-- A relative square-zero extension of the structure sheaf of a scheme over `S`, with the
scheme and its structure morphism bundled in. -/
public structure SquareZeroExtensionOver (S : Scheme.{u}) where
  /-- The scheme carrying the extension. -/
  carrier : Scheme.{u}
  /-- Its structure morphism to the base. -/
  structureMorphism : carrier ⟶ S
  /-- The extension itself. -/
  extension : SquareZeroExtension structureMorphism

/-- Relative square-zero extensions over a fixed base form a category. -/
public instance : Category (SquareZeroExtensionOver S) where
  Hom E₁ E₂ := E₁.extension.Hom E₂.extension
  id E := SquareZeroExtension.Hom.id E.extension
  comp φ ψ := φ.comp ψ
  id_comp _ := SquareZeroExtension.Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := SquareZeroExtension.Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := SquareZeroExtension.Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

namespace SquareZeroExtensionOver

/-- The categorical identity has the identity as underlying morphism of schemes. -/
@[simp] public theorem id_base (E : SquareZeroExtensionOver S) :
    (𝟙 E : E ⟶ E).base = 𝟙 E.carrier := rfl

/-- Categorical composition composes the underlying morphisms of schemes. -/
@[simp] public theorem comp_base {E₁ E₂ E₃ : SquareZeroExtensionOver S} (φ : E₁ ⟶ E₂)
    (ψ : E₂ ⟶ E₃) : (φ ≫ ψ).base = φ.base ≫ ψ.base := rfl

/-- The categorical identity has the identity as underlying morphism of ringed spaces. -/
@[simp] public theorem id_sheafHom (E : SquareZeroExtensionOver S) :
    (𝟙 E : E ⟶ E).sheafHom = 𝟙 _ := rfl

/-- Categorical composition composes the underlying morphisms of ringed spaces. -/
@[simp] public theorem comp_sheafHom {E₁ E₂ E₃ : SquareZeroExtensionOver S} (φ : E₁ ⟶ E₂)
    (ψ : E₂ ⟶ E₃) : (φ ≫ ψ).sheafHom = φ.sheafHom ≫ ψ.sheafHom := rfl

end SquareZeroExtensionOver

/-- The realization of a square-zero extension, as a construction. -/
public def realization {X : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    Realization E :=
  (squareZeroExtension_realization E).some

namespace Realization

variable {X₁ X₂ X₃ : Scheme.{u}} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  {E₁ : SquareZeroExtension f₁} {E₂ : SquareZeroExtension f₂} {E₃ : SquareZeroExtension f₃}

/-- The underlying map of a realization is surjective: the thickening has the same points as
the scheme it thickens. -/
public theorem surjective_immersion (r : Realization E₁) : Function.Surjective r.immersion :=
  r.immersion_isFirstOrder.isThickening.2

/-- The morphism of sheafed spaces between two realizations induced by a morphism of
square-zero extensions. -/
public def mapShHom (r₁ : Realization E₁) (r₂ : Realization E₂) (φ : E₁.Hom E₂) :
    r₁.ambient.toSheafedSpace ⟶ r₂.ambient.toSheafedSpace :=
  r₁.sheafedIso.hom ≫ φ.sheafHom ≫ r₂.sheafedIso.inv

/-- The square expressing that `mapShHom` restricts to the given morphism of schemes on the
closed subschemes. -/
public theorem immersion_comp_mapShHom (r₁ : Realization E₁) (r₂ : Realization E₂)
    (φ : E₁.Hom E₂) :
    r₁.immersion.toLRSHom.toShHom ≫ r₁.mapShHom r₂ φ =
      φ.base.toLRSHom.toShHom ≫ r₂.immersion.toLRSHom.toShHom := by
  rw [mapShHom, ← Category.assoc, r₁.inclusion_eq, ← Category.assoc, φ.inclusion_comm,
    Category.assoc, ← r₂.inclusion_eq]
  simp

/-- The stalk maps of `mapShHom` are local: after composing with the stalk map of the first
immersion they factor as the stalk map of the second immersion followed by the stalk map of
the given morphism of schemes, all of which are local. -/
public theorem isLocalHom_mapShHom_stalkMap (r₁ : Realization E₁) (r₂ : Realization E₂)
    (φ : E₁.Hom E₂) (p : r₁.ambient) :
    IsLocalHom (((r₁.mapShHom r₂ φ).hom.stalkMap p).hom) := by
  obtain ⟨x, hx⟩ := r₁.surjective_immersion p
  have hx' : (r₁.immersion.toLRSHom.toShHom).hom.base x = p := hx
  subst hx'
  have hsq : (r₁.immersion.toLRSHom.toShHom).hom ≫ (r₁.mapShHom r₂ φ).hom =
      (φ.base.toLRSHom.toShHom).hom ≫ (r₂.immersion.toLRSHom.toShHom).hom :=
    congrArg InducedCategory.Hom.hom (r₁.immersion_comp_mapShHom r₂ φ)
  have hright : IsLocalHom ((((φ.base.toLRSHom.toShHom).hom ≫
      (r₂.immersion.toLRSHom.toShHom).hom).stalkMap x).hom) := by
    rw [PresheafedSpace.stalkMap.comp]
    have h₂ : IsLocalHom (((r₂.immersion.toLRSHom.toShHom).hom.stalkMap
        ((φ.base.toLRSHom.toShHom).hom.base x)).hom) :=
      r₂.immersion.toLRSHom.prop _
    have h₁ : IsLocalHom (((φ.base.toLRSHom.toShHom).hom.stalkMap x).hom) :=
      φ.base.toLRSHom.prop x
    exact @CommRingCat.isLocalHom_comp _ _ _ _ _ h₁ h₂
  have hleft : IsLocalHom ((((r₁.immersion.toLRSHom.toShHom).hom ≫
      (r₁.mapShHom r₂ φ).hom).stalkMap x).hom) := by
    rw [PresheafedSpace.stalkMap.congr_hom _ _ hsq x]
    exact @CommRingCat.isLocalHom_comp _ _ _ _ _ hright inferInstance
  have hsplit : ((r₁.immersion.toLRSHom.toShHom).hom ≫ (r₁.mapShHom r₂ φ).hom).stalkMap x =
      (r₁.mapShHom r₂ φ).hom.stalkMap ((r₁.immersion.toLRSHom.toShHom).hom.base x) ≫
        (r₁.immersion.toLRSHom.toShHom).hom.stalkMap x :=
    PresheafedSpace.stalkMap.comp _ _ x
  exact isLocalHom_of_comp' _ _ (hsplit ▸ hleft)

/-- The morphism of realizations induced by a morphism of square-zero extensions. -/
public def map (r₁ : Realization E₁) (r₂ : Realization E₂) (φ : E₁.Hom E₂) :
    r₁.ambient ⟶ r₂.ambient :=
  Scheme.Hom.mk (LocallyRingedSpace.homMk (r₁.mapShHom r₂ φ)
    (r₁.isLocalHom_mapShHom_stalkMap r₂ φ))

/-- The induced morphism of realizations is `mapShHom` as a morphism of sheafed spaces. -/
@[simp] public theorem map_toShHom (r₁ : Realization E₁) (r₂ : Realization E₂)
    (φ : E₁.Hom E₂) : (r₁.map r₂ φ).toLRSHom.toShHom = r₁.mapShHom r₂ φ := rfl

/-- The induced morphism of realizations restricts to the given morphism of schemes on the
closed subschemes. -/
public theorem map_immersion (r₁ : Realization E₁) (r₂ : Realization E₂) (φ : E₁.Hom E₂) :
    r₁.immersion ≫ r₁.map r₂ φ = φ.base ≫ r₂.immersion := by
  apply scheme_hom_ext_of_toShHom
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom, map_toShHom] using
    r₁.immersion_comp_mapShHom r₂ φ

/-- The induced morphism of realizations is a morphism over the base. -/
public theorem map_toBase (r₁ : Realization E₁) (r₂ : Realization E₂) (φ : E₁.Hom E₂) :
    r₁.map r₂ φ ≫ r₂.toBase = r₁.toBase := by
  apply scheme_hom_ext_of_toShHom
  rw [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom, map_toShHom, mapShHom,
    Category.assoc, Category.assoc, r₂.toBase_eq, φ.toBase_comm, ← r₁.toBase_eq,
    Iso.hom_inv_id_assoc]

/-- The identity morphism of extensions induces the identity of a realization. -/
@[simp] public theorem map_id (r : Realization E₁) :
    r.map r (SquareZeroExtension.Hom.id E₁) = 𝟙 r.ambient := by
  apply scheme_hom_ext_of_toShHom
  rw [map_toShHom, show (𝟙 r.ambient : r.ambient ⟶ r.ambient).toLRSHom.toShHom = 𝟙 _ from rfl,
    mapShHom, SquareZeroExtension.Hom.id_sheafHom, Category.id_comp, Iso.hom_inv_id]

/-- The induced morphisms of realizations compose. -/
public theorem map_comp (r₁ : Realization E₁) (r₂ : Realization E₂) (r₃ : Realization E₃)
    (φ : E₁.Hom E₂) (ψ : E₂.Hom E₃) :
    r₁.map r₃ (φ.comp ψ) = r₁.map r₂ φ ≫ r₂.map r₃ ψ := by
  apply scheme_hom_ext_of_toShHom
  simp only [map_toShHom, LocallyRingedSpace.comp_toShHom, Scheme.Hom.comp_toLRSHom,
    mapShHom, SquareZeroExtension.Hom.comp_sheafHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Any two realizations of the same square-zero extension are canonically isomorphic. -/
public def uniqueIso (r₁ r₂ : Realization E₁) : r₁.ambient ≅ r₂.ambient where
  hom := r₁.map r₂ (SquareZeroExtension.Hom.id E₁)
  inv := r₂.map r₁ (SquareZeroExtension.Hom.id E₁)
  hom_inv_id := by
    rw [← map_comp, show (SquareZeroExtension.Hom.id E₁).comp (SquareZeroExtension.Hom.id E₁) =
      SquareZeroExtension.Hom.id E₁ from
        SquareZeroExtension.Hom.ext (Category.id_comp _) (Category.id_comp _), map_id]
  inv_hom_id := by
    rw [← map_comp, show (SquareZeroExtension.Hom.id E₁).comp (SquareZeroExtension.Hom.id E₁) =
      SquareZeroExtension.Hom.id E₁ from
        SquareZeroExtension.Hom.ext (Category.id_comp _) (Category.id_comp _), map_id]

/-- The forward direction of the canonical isomorphism between two realizations. -/
@[simp] public theorem uniqueIso_hom (r₁ r₂ : Realization E₁) :
    (uniqueIso r₁ r₂).hom = r₁.map r₂ (SquareZeroExtension.Hom.id E₁) := rfl

/-- The backward direction of the canonical isomorphism between two realizations. -/
@[simp] public theorem uniqueIso_inv (r₁ r₂ : Realization E₁) :
    (uniqueIso r₁ r₂).inv = r₂.map r₁ (SquareZeroExtension.Hom.id E₁) := rfl

/-- The canonical isomorphism between two realizations is compatible with the immersions. -/
public theorem immersion_comp_uniqueIso (r₁ r₂ : Realization E₁) :
    r₁.immersion ≫ (uniqueIso r₁ r₂).hom = r₂.immersion := by
  rw [uniqueIso_hom, r₁.map_immersion r₂ (SquareZeroExtension.Hom.id E₁),
    SquareZeroExtension.Hom.id_base, Category.id_comp]

/-- The canonical isomorphism between two realizations is a morphism over the base. -/
public theorem uniqueIso_comp_toBase (r₁ r₂ : Realization E₁) :
    (uniqueIso r₁ r₂).hom ≫ r₂.toBase = r₁.toBase := by
  rw [uniqueIso_hom, r₁.map_toBase r₂ (SquareZeroExtension.Hom.id E₁)]

end Realization

/-- The realization of a square-zero extension over `S`, as a functor to schemes over `S`. -/
public def realizationFunctor (S : Scheme.{u}) : SquareZeroExtensionOver S ⥤ Over S where
  obj E := Over.mk (realization E.extension).toBase
  map {E₁ E₂} φ := Over.homMk
    ((realization E₁.extension).map (realization E₂.extension) φ)
    ((realization E₁.extension).map_toBase (realization E₂.extension) φ)
  map_id E := Over.OverMorphism.ext (Realization.map_id (realization E.extension))
  map_comp {E₁ E₂ E₃} φ ψ := Over.OverMorphism.ext
    ((realization E₁.extension).map_comp (realization E₂.extension)
      (realization E₃.extension) φ ψ)

/-- The scheme underlying the value of the realization functor. -/
@[simp] public theorem realizationFunctor_obj_left (E : SquareZeroExtensionOver S) :
    ((realizationFunctor S).obj E).left = (realization E.extension).ambient := rfl

/-- The structure morphism of the value of the realization functor. -/
@[simp] public theorem realizationFunctor_obj_hom (E : SquareZeroExtensionOver S) :
    ((realizationFunctor S).obj E).hom = (realization E.extension).toBase := rfl

/-- The morphism of schemes underlying the value of the realization functor on a morphism. -/
@[simp] public theorem realizationFunctor_map_left {E₁ E₂ : SquareZeroExtensionOver S}
    (φ : E₁ ⟶ E₂) : ((realizationFunctor S).map φ).left =
      (realization E₁.extension).map (realization E₂.extension) φ := rfl

/-- The realizations of a morphism of square-zero extensions commute with the immersions of
the thickened schemes. -/
public theorem realizationFunctor_map_immersion {E₁ E₂ : SquareZeroExtensionOver S}
    (φ : E₁ ⟶ E₂) :
    (realization E₁.extension).immersion ≫ ((realizationFunctor S).map φ).left =
      φ.base ≫ (realization E₂.extension).immersion :=
  (realization E₁.extension).map_immersion (realization E₂.extension) φ

end Stacks.Thickenings

end
