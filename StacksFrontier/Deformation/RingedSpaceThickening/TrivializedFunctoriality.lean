module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFunctoriality
public import StacksFrontier.Deformation.RingedSpaceThickening.TrivialExtension
import StacksCore.Tactic.StacksAttribute

/-!
# Extensions over a morphism of trivialized first order thickenings

Let `(X, 𝒪_X)` be a ringed space, let `i₁ : X ⟶ X'₁` and `i₂ : X ⟶ X'₂` be first order
thickenings with ideals `ℐ₁` and `ℐ₂`, and let `h : X'₁ ⟶ X'₂` be a morphism of thickenings of
`(X, 𝒪_X)`, so `i₁ ≫ h = i₂`. Assume both thickenings are trivialized, by retractions `π₁` and
`π₂`, and assume the trivializations are compatible: `π₁ = h ≫ π₂`, which is what it means for
`h` to be a morphism of *trivialized* first order thickenings.

Fix an `𝒪_X`-module `ℱ` and pairs `(𝒦₁, c₁)`, `(𝒦₂, c₂)` with `cᵢ : ℐᵢ ⊗_{𝒪_X} ℱ ⟶ 𝒦ᵢ`, and a
map `k : 𝒦₂ ⟶ 𝒦₁` making the square built from `c₁`, `c₂` and `ℐ₂ ⟶ ℐ₁` commute. Each
trivialization turns an extension as in Tag 08L4 into a class in `Ext¹_{𝒪_X}(ℱ, 𝒦ᵢ)`. This file
proves that the resulting square

    {ℱ'₂ with c₂ and 𝒦₂}  ⟶  Ext¹_{𝒪_X}(ℱ, 𝒦₂)
            |                        |
            |                        k
            v                        v
    {ℱ'₁ with c₁ and 𝒦₁}  ⟶  Ext¹_{𝒪_X}(ℱ, 𝒦₁)

commutes, the left vertical map being the pushout functoriality of Tag 08LC and the right
vertical map functoriality of `Ext` in its second argument.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.inducedTrivialization`: the trivialization of `i₁`
  obtained from one of `i₂` by composing with `h`; a trivialization of `i₁` is compatible with
  one of `i₂` exactly when it is this one.
* `AlgebraicGeometry.RingedSpaceThickening.thickeningPushforwardComp`: the comparison
  `(i₁)_* ⋙ h_* ≅ (i₂)_*` coming from `i₁ ≫ h = i₂`.
* `AlgebraicGeometry.RingedSpaceThickening.PushedExtension`: a map of extensions from `ℱ'₂` to
  `ℱ'₁`, read over `X'₂`, inducing `k` on kernel modules and the identity on `ℱ`. This is what
  it means for `ℱ'₁` to be the extension that Tag 08LC produces from `ℱ'₂`.
* `AlgebraicGeometry.RingedSpaceThickening.PushedExtension.ofPushoutMap`: that datum, built
  from the form Tag 08LC delivers — an `𝒪_{X'₁}`-module structure on the pushout
  `ℱ'₂ ⊔_{𝒦₂} 𝒦₁`, read over `X'₂` as a map out of
  `AlgebraicGeometry.RingedSpaceThickening.pushoutExtension`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass_eq_of_pushedExtension`: the
  square above commutes — the class of `ℱ'₁` is the image of the class of `ℱ'₂` under `k`.
* `AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass_eq_of_pushoutMap`: the same
  identity of classes with `ℱ'₁` presented as an `𝒪_{X'₁}`-module structure on the pushout,
  which is how Tag 08LC produces it.
* `AlgebraicGeometry.RingedSpaceThickening.splitExtensionHom`: the map of short exact sequences
  of `𝒪_X`-modules underlying the commutativity, with `k` on the kernels and `𝟙 ℱ` on the
  quotients.
* `AlgebraicGeometry.RingedSpaceThickening.underlyingExtensionClass_congr`: the class of an
  extension depends on the trivialization only through its retraction.

## Implementation notes

The underlying spaces of `X`, `X'₁` and `X'₂` are not identified, so an `𝒪_{X'₁}`-module is not
an `𝒪_{X'₂}`-module. An extension `ℱ'₁` over `X'₁` is compared with one over `X'₂` by
`h_*`, under which the compatibility `π₁ = h ≫ π₂` becomes the statement that the two readings
of `ℱ'₁` as an `𝒪_X`-module — along `π₁` directly, and along `π₂` after `h_*` — are the same
functor. That is why `PushedExtension` is phrased over `X'₂`: it is the only place both
extensions live.

Pushforward of sheaves of modules along a composite is definitionally the composite of the
pushforwards (`RingedSpaceModuleAdjunction.modulePushforwardComp_hom_app` is `rfl`), so
once the trivialization of `i₁` is literally `h ≫ π₂` and `i₂` is literally `i₁ ≫ h`, the two
readings are the same functor on the nose and only the identifications of the outer terms
remain. Those identifications are composites of `eqToHom`s and identity components, so they are
compared through `IsSectionIdentity`: a morphism of sheaves of modules between modules with
equal — but not syntactically equal — sections, which is the identity on every section.
Equality of two such morphisms is `eq_of_isSectionIdentity`.

## References

* [Stacks Project, Tag 08LD](https://stacks.math.columbia.edu/tag/08LD)
* [Stacks Project, Tag 08LC](https://stacks.math.columbia.edu/tag/08LC)
* [Stacks Project, Tag 08LB](https://stacks.math.columbia.edu/tag/08LB)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Thickenings

universe e u

namespace AlgebraicGeometry.RingedSpaceThickening

attribute [local implicit_reducible] RingedSpaceModuleAdjunction.modulePushforward
  splitExtension IsFirstOrderThickening IsThickening

variable {X X₁ X₂ : RingedSpace.{u, u}}

/-! ### Morphisms that are the identity on sections

The comparisons between the several readings of a direct image as an `𝒪_X`-module are composites
of `eqToHom`s and of identity components, so each of them leaves every section alone. Since the
modules they relate have equal but not syntactically equal sections, "leaves every section
alone" is a statement about heterogeneous equality.
-/

/-- A morphism of sheaves of modules is the *identity on sections* when it carries every section
to itself. The source and target have equal sections whenever this holds, but they need not be
syntactically equal, so the equation is heterogeneous. -/
def IsSectionIdentity {M N : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ N) : Prop :=
  ∀ U s, HEq ((φ.val.app U).hom s) s

/-- The identity is the identity on sections. -/
theorem isSectionIdentity_id (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity (𝟙 M) := fun _ _ => HEq.rfl

/-- A transport along an equality of modules is the identity on sections. -/
theorem isSectionIdentity_eqToHom {M N : SheafOfModules.{u} (structureSheafRing X)} (e : M = N) :
    IsSectionIdentity (eqToHom e) := by
  subst e; exact isSectionIdentity_id M

/-- A component of a transport along an equality of functors is the identity on sections. -/
theorem isSectionIdentity_eqToHom_app {C : Type*} [Category C]
    {G H : C ⥤ SheafOfModules.{u} (structureSheafRing X)} (e : G = H) (M : C) :
    IsSectionIdentity ((eqToHom e).app M) := by
  subst e; exact isSectionIdentity_id _

/-- Being the identity on sections is stable under composition. -/
theorem isSectionIdentity_comp {M N P : SheafOfModules.{u} (structureSheafRing X)}
    {φ : M ⟶ N} {ψ : N ⟶ P}
    (hφ : IsSectionIdentity φ) (hψ : IsSectionIdentity ψ) : IsSectionIdentity (φ ≫ ψ) :=
  fun U s => (hψ U ((φ.val.app U).hom s)).trans (hφ U s)

/-- Pushing a morphism that is the identity on sections forward keeps it so: pushforward only
reindexes the opens, it does not change the map on sections. -/
theorem isSectionIdentity_modulePushforward (f : X ⟶ X₁)
    {M N : SheafOfModules.{u} (structureSheafRing X)} {φ : M ⟶ N} (hφ : IsSectionIdentity φ) :
    IsSectionIdentity ((modulePushforward f).map φ) := fun _U s => hφ _ s

/-- The inverse of an isomorphism that is the identity on sections is again one. -/
theorem isSectionIdentity_inv {M N : SheafOfModules.{u} (structureSheafRing X)} (e : M ≅ N)
    (he : IsSectionIdentity e.hom) : IsSectionIdentity e.inv := by
  intro U s
  have h : (e.hom.val.app U).hom ((e.inv.val.app U).hom s) = s :=
    congrArg (fun φ : N ⟶ N => (φ.val.app U).hom s) e.inv_hom_id
  exact (he U ((e.inv.val.app U).hom s)).symm.trans (heq_of_eq h)

/-- Two morphisms of sheaves of modules that are both the identity on sections are equal. -/
theorem eq_of_isSectionIdentity {M N : SheafOfModules.{u} (structureSheafRing X)} {φ ψ : M ⟶ N}
    (hφ : IsSectionIdentity φ) (hψ : IsSectionIdentity ψ) : φ = ψ := by
  ext U s
  exact eq_of_heq ((hφ U s).trans (hψ U s).symm)

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` is the identity on sections. -/
theorem isSectionIdentity_modulePushforwardComp_hom {Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity ((RingedSpaceModuleAdjunction.modulePushforwardComp f g).hom.app M) :=
  fun _ _ => HEq.rfl

/-- The inverse comparison `(f ≫ g)_* ≅ f_* ⋙ g_*` is the identity on sections. -/
theorem isSectionIdentity_modulePushforwardComp_inv {Y Z : RingedSpace.{u, u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity ((RingedSpaceModuleAdjunction.modulePushforwardComp f g).inv.app M) :=
  fun _ _ => HEq.rfl

/-- The comparison `(𝟙 X)_* ≅ 𝟭` is the identity on sections. -/
theorem isSectionIdentity_modulePushforwardId_hom (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity ((RingedSpaceModuleAdjunction.modulePushforwardId X).hom.app M) :=
  fun _ _ => HEq.rfl

/-- Reading a direct image back along a trivialization returns the module itself, by an
isomorphism that is the identity on sections. -/
theorem isSectionIdentity_splitRestrictionIso_hom {i : X ⟶ X₁} (π : SplitMono i)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity (splitRestrictionIso i π M).hom := by
  show IsSectionIdentity ((splitRestrictionCompIso i π).hom.app M)
  simp only [splitRestrictionCompIso, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom]
  refine isSectionIdentity_comp (isSectionIdentity_modulePushforwardComp_hom _ _ M) ?_
  exact isSectionIdentity_comp
    (isSectionIdentity_eqToHom_app
      (congrArg (fun f : X ⟶ X => modulePushforward f) π.id) M)
    (isSectionIdentity_modulePushforwardId_hom M)

/-! ### Compatible trivializations -/

/-- The trivialization of `i₁` induced by a trivialization `π₂` of `i₂` and a morphism
`h : X'₁ ⟶ X'₂` of thickenings of `(X, 𝒪_X)`: the retraction is `h` followed by that of `π₂`.
A trivialization of `i₁` is compatible with `π₂` in the sense of the source exactly when its
retraction is this one. -/
def inducedTrivialization (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂)
    (π₂ : SplitMono i₂) : SplitMono i₁ where
  retraction := h ≫ π₂.retraction
  id := by rw [← Category.assoc, comm]; exact π₂.id

/-- The retraction of the induced trivialization, by definition. -/
@[simp]
theorem inducedTrivialization_retraction (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (π₂ : SplitMono i₂) :
    (inducedTrivialization i₁ i₂ h comm π₂).retraction = h ≫ π₂.retraction := rfl

/-- The class `ξ_{ℱ'}` of Tag 08LB depends on the trivialization only through its retraction: the
remaining datum of a `SplitMono` is a proof. -/
theorem underlyingExtensionClass_congr {i : X ⟶ X₁} (π π' : SplitMono i)
    (hπ : π.retraction = π'.retraction) (hb : IsIso i.hom.base)
    (F K : SheafOfModules.{u} (structureSheafRing X))
    [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))]
    (E : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i).obj F)
      ((modulePushforward i).obj K) 0) :
    underlyingExtensionClass i π hb F K E = underlyingExtensionClass i π' hb F K E := by
  obtain ⟨r, hr⟩ := π
  obtain ⟨r', hr'⟩ := π'
  cases hπ
  rfl

/-! ### The comparison of direct images along a morphism of thickenings -/

/-- The comparison `(i₁)_* ⋙ h_* ≅ (i₂)_*` for a morphism `h : X'₁ ⟶ X'₂` of thickenings of
`(X, 𝒪_X)`: pushforward is multiplicative, and `i₁ ≫ h = i₂`. -/
noncomputable def thickeningPushforwardComp (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) :
    modulePushforward i₁ ⋙ modulePushforward h ≅ modulePushforward i₂ :=
  RingedSpaceModuleAdjunction.modulePushforwardComp i₁ h ≪≫
    eqToIso (congrArg modulePushforward comm)

/-- The comparison of direct images along a morphism of thickenings is the identity on
sections. -/
theorem isSectionIdentity_thickeningPushforwardComp_inv (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂) (M : SheafOfModules.{u} (structureSheafRing X)) :
    IsSectionIdentity ((thickeningPushforwardComp i₁ i₂ h comm).inv.app M) := by
  simp only [thickeningPushforwardComp, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv]
  exact isSectionIdentity_comp
    (isSectionIdentity_eqToHom_app (congrArg modulePushforward comm).symm M)
    (isSectionIdentity_modulePushforwardComp_inv i₁ h M)

/-- Reading an `𝒪_{X'₁}`-module as an `𝒪_X`-module along the induced trivialization is reading it
over `X'₂` by `h_*` and then back along `π₂`: the retraction of the induced trivialization is
`h` followed by that of `π₂`, and pushforward is multiplicative. -/
noncomputable def inducedRestrictionComp (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (π₂ : SplitMono i₂) :
    modulePushforward h ⋙ splitRestriction i₂ π₂ ≅
      splitRestriction i₁ (inducedTrivialization i₁ i₂ h comm π₂) :=
  RingedSpaceModuleAdjunction.modulePushforwardComp h π₂.retraction

/-- The comparison of the two readings is the identity on sections. -/
theorem isSectionIdentity_inducedRestrictionComp_hom (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (π₂ : SplitMono i₂) (M : SheafOfModules.{u} (structureSheafRing X₁)) :
    IsSectionIdentity ((inducedRestrictionComp i₁ i₂ h comm π₂).hom.app M) :=
  fun _ _ => HEq.rfl

/-- With compatible trivializations the two readings of a direct image as an `𝒪_X`-module agree:
reading `(i₂)_* 𝒦` back along `π₂` is reading `h_* (i₁)_* 𝒦` back along `π₂`, which is reading
`(i₁)_* 𝒦` back along the induced trivialization of `i₁`. -/
theorem splitRestrictionIso_inducedTrivialization (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (π₂ : SplitMono i₂) (M : SheafOfModules.{u} (structureSheafRing X)) :
    (splitRestriction i₂ π₂).map ((thickeningPushforwardComp i₁ i₂ h comm).inv.app M) ≫
        (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app ((modulePushforward i₁).obj M) ≫
          (splitRestrictionIso i₁ (inducedTrivialization i₁ i₂ h comm π₂) M).hom =
      (splitRestrictionIso i₂ π₂ M).hom := by
  refine eq_of_isSectionIdentity (isSectionIdentity_comp ?_ (isSectionIdentity_comp ?_ ?_))
    (isSectionIdentity_splitRestrictionIso_hom π₂ M)
  · exact isSectionIdentity_modulePushforward π₂.retraction
      (isSectionIdentity_thickeningPushforwardComp_inv i₁ i₂ h comm M)
  · exact isSectionIdentity_inducedRestrictionComp_hom i₁ i₂ h comm π₂ _
  · exact isSectionIdentity_splitRestrictionIso_hom
      (inducedTrivialization i₁ i₂ h comm π₂) M

/-- `splitRestrictionIso_inducedTrivialization` with the inverse isomorphisms: the comparison of
the outer terms over `X'₁` is the comparison over `X'₂` followed by the change of readings. -/
@[reassoc]
theorem splitRestrictionIso_inducedTrivialization_inv (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (π₂ : SplitMono i₂) (M : SheafOfModules.{u} (structureSheafRing X)) :
    (splitRestrictionIso i₂ π₂ M).inv ≫
        (splitRestriction i₂ π₂).map ((thickeningPushforwardComp i₁ i₂ h comm).inv.app M) ≫
          (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app ((modulePushforward i₁).obj M) =
      (splitRestrictionIso i₁ (inducedTrivialization i₁ i₂ h comm π₂) M).inv := by
  rw [← cancel_mono (splitRestrictionIso i₁ (inducedTrivialization i₁ i₂ h comm π₂) M).hom,
    Iso.inv_hom_id, Category.assoc, Category.assoc,
    splitRestrictionIso_inducedTrivialization i₁ i₂ h comm π₂ M, Iso.inv_hom_id]

/-- Naturality of `AlgebraicGeometry.RingedSpaceThickening.splitRestrictionIso`, with the inverse
isomorphisms. -/
@[reassoc]
theorem splitRestrictionIso_inv_naturality {i : X ⟶ X₁} (π : SplitMono i)
    {M N : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ N) :
    (splitRestrictionIso i π M).inv ≫ (splitRestriction i π).map ((modulePushforward i).map φ) =
      φ ≫ (splitRestrictionIso i π N).inv := by
  rw [← cancel_mono (splitRestrictionIso i π N).hom, Category.assoc,
    splitRestrictionIso_naturality i π φ, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-! ### A map of extensions over the larger thickening -/

/-- A map of extensions as in Tag 08L4 from `ℱ'₂` over `X'₂` to `ℱ'₁` over `X'₁`, read over `X'₂`
by `h_*`: it induces `k` on the kernel modules and the identity on `ℱ`. This is exactly the data by
which Tag 08LC produces `ℱ'₁` from `ℱ'₂`, since such a map exhibits `h_* ℱ'₁` as the pushout of
`ℱ'₂` along `k`. -/
structure PushedExtension (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0) where
  /-- The map on middle terms, read over `X'₂`. -/
  hom : E₂.Z.left ⟶ (modulePushforward h).obj E₁.Z.left
  /-- On the kernel modules the map is `k`. -/
  kernel_commutes : E₂.f ≫ hom =
    (modulePushforward i₂).map k ≫ (thickeningPushforwardComp i₁ i₂ h comm).inv.app K₁ ≫
      (modulePushforward h).map E₁.f
  /-- On the quotient module the map is the identity of `ℱ`. -/
  quotient_commutes : hom ≫ (modulePushforward h).map E₁.g =
    E₂.g ≫ (thickeningPushforwardComp i₁ i₂ h comm).inv.app F

/-- The `PushedExtension` given by a map `φ` from the middle term of
`AlgebraicGeometry.RingedSpaceThickening.pushoutExtension` to `h_* ℱ'₁` carrying the inclusion of
`𝒦₁` to the inclusion of `𝒦₁` and the surjection onto `ℱ` to the surjection onto `ℱ`: its map on
middle terms is the pushout injection of `ℱ'₂` followed by `φ`. Such a `φ` is an `𝒪_{X'₁}`-module
structure on the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁` read over `X'₂`, the form in which Tag 08LC produces
`ℱ'₁`. -/
noncomputable def PushedExtension.ofPushoutMap (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    {E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0}
    {E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0}
    (φ : (pushoutExtension i₂ F K₁ K₂ k E₂).Z.left ⟶ (modulePushforward h).obj E₁.Z.left)
    (hf : (pushoutExtension i₂ F K₁ K₂ k E₂).f ≫ φ =
      (thickeningPushforwardComp i₁ i₂ h comm).inv.app K₁ ≫ (modulePushforward h).map E₁.f)
    (hg : φ ≫ (modulePushforward h).map E₁.g =
      (pushoutExtension i₂ F K₁ K₂ k E₂).g ≫
        (thickeningPushforwardComp i₁ i₂ h comm).inv.app F) :
    PushedExtension i₁ i₂ h comm F K₁ K₂ k E₂ E₁ where
  hom := pushoutExtensionInl i₂ F K₁ K₂ k E₂ ≫ φ
  kernel_commutes := by
    rw [← Category.assoc, f_comp_pushoutExtensionInl, Category.assoc, hf]
  quotient_commutes := by
    rw [Category.assoc, hg, ← Category.assoc, pushoutExtensionInl_comp_g]

/-! ### The commutative square of Stacks 08LD -/

variable [HasExt.{e} (SheafOfModules.{u} (structureSheafRing X))]

/-- The map of short exact sequences of `𝒪_X`-modules underlying Tag 08LD: the two extensions, read
as sequences of `𝒪_X`-modules along the two compatible trivializations, are related by `k` on the
kernels and by the identity on `ℱ`. The map on middle terms is the one of `PushedExtension`, read
back along `π₂`. -/
noncomputable def splitExtensionHom (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (π₂ : SplitMono i₂) (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X))
    (k : K₂ ⟶ K₁)
    {E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0}
    {E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0}
    (w : PushedExtension i₁ i₂ h comm F K₁ K₂ k E₂ E₁) :
    splitExtension i₂ π₂ F K₂ E₂ ⟶
      splitExtension i₁ (inducedTrivialization i₁ i₂ h comm π₂) F K₁ E₁ where
  τ₁ := k
  τ₂ := (splitRestriction i₂ π₂).map w.hom ≫
    (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app E₁.Z.left
  τ₃ := 𝟙 F
  comm₁₂ := by
    have hnat : (splitRestriction i₂ π₂).map ((modulePushforward h).map E₁.f) ≫
          (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app E₁.Z.left =
        (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app ((modulePushforward i₁).obj K₁) ≫
          (splitRestriction i₁ (inducedTrivialization i₁ i₂ h comm π₂)).map E₁.f :=
      (inducedRestrictionComp i₁ i₂ h comm π₂).hom.naturality E₁.f
    simp only [splitExtension_f, Category.assoc]
    rw [← Functor.map_comp_assoc, w.kernel_commutes]
    simp only [Functor.map_comp, Category.assoc]
    rw [hnat, ← Category.assoc ((splitRestrictionIso i₂ π₂ K₂).inv),
      splitRestrictionIso_inv_naturality π₂ k, Category.assoc,
      splitRestrictionIso_inducedTrivialization_inv_assoc i₁ i₂ h comm π₂ K₁]
  comm₂₃ := by
    have hnat : (splitRestriction i₂ π₂).map ((modulePushforward h).map E₁.g) ≫
          (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app ((modulePushforward i₁).obj F) =
        (inducedRestrictionComp i₁ i₂ h comm π₂).hom.app E₁.Z.left ≫
          (splitRestriction i₁ (inducedTrivialization i₁ i₂ h comm π₂)).map E₁.g :=
      (inducedRestrictionComp i₁ i₂ h comm π₂).hom.naturality E₁.g
    simp only [splitExtension_g, Category.assoc]
    rw [← reassoc_of% hnat, ← Functor.map_comp_assoc, w.quotient_commutes,
      Functor.map_comp_assoc, splitRestrictionIso_inducedTrivialization i₁ i₂ h comm π₂ F]
    exact (Category.comp_id _).symm

/-- For a morphism `h : X'₁ ⟶ X'₂` of trivialized first order thickenings of `(X, 𝒪_X)` the square
relating the extension classes commutes: if `ℱ'₁` is the extension that the functoriality of Tag
08LC produces from `ℱ'₂` and `k : 𝒦₂ ⟶ 𝒦₁`, then the class `ξ_{ℱ'₁}` of Tag 08LB is the image of
`ξ_{ℱ'₂}` under functoriality of `Ext¹_{𝒪_X}(ℱ, -)` along `k`.

The hypotheses `hc`, `hE₂` and `hE₁` say that the two extensions are members of the two sets the
square relates — that their canonical maps of Tag 08L4 are `c₂` and `c₁`, compatibly with `k`.
The identity of classes uses only the map of extensions `w`. -/
@[stacks 08LD "the commutative square relating the two extension classes"]
theorem underlyingExtensionClass_eq_of_pushedExtension (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂)
    (hi₁ : IsFirstOrderThickening i₁) (hi₂ : IsFirstOrderThickening i₂)
    (π₁ : SplitMono i₁) (π₂ : SplitMono i₂)
    (hπ : π₁.retraction = h ≫ π₂.retraction)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    (c₁ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i₁))).obj (F)) ⟶ K₁)
    (c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
      ((idealSheafPullback i₂))).obj (F)) ⟶ K₂)
    (_hc : c₂ ≫ k = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩)).map
        (((thickeningIdealMap i₁ i₂ h comm), (𝟙 F)) : (_, _) ⟶ (_, _))) ≫ c₁)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0)
    (_hE₂ : (firstOrderExtensionAction i₂ F K₂ hi₂ E₂).val = c₂)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0)
    (_hE₁ : (firstOrderExtensionAction i₁ F K₁ hi₁ E₁).val = c₁)
    (w : PushedExtension i₁ i₂ h comm F K₁ K₂ k E₂ E₁) :
    underlyingExtensionClass i₁ π₁ hi₁.1.1 F K₁ E₁ =
      (underlyingExtensionClass i₂ π₂ hi₂.1.1 F K₂ E₂).comp
        (CategoryTheory.Abelian.Ext.mk₀ k) (add_zero 1) := by
  rw [underlyingExtensionClass_congr π₁ (inducedTrivialization i₁ i₂ h comm π₂) hπ]
  have hnat := (splitExtension_shortExact i₂ π₂ hi₂.1.1 F K₂ E₂).extClass_naturality
    (splitExtension_shortExact i₁ (inducedTrivialization i₁ i₂ h comm π₂) hi₁.1.1 F K₁ E₁)
    (splitExtensionHom i₁ i₂ h comm π₂ F K₁ K₂ k w)
  dsimp only [splitExtensionHom] at hnat
  exact (hnat.trans (CategoryTheory.Abelian.Ext.mk₀_id_comp _)).symm

/-- The square of Tag 08LD, with the left vertical map presented the way Tag 08LC builds it: `ℱ'₁`
is an `𝒪_{X'₁}`-module structure on the pushout `ℱ'₂ ⊔_{𝒦₂} 𝒦₁`, recorded as a map `φ` from the
pushout to `h_* ℱ'₁` compatible with the inclusion of `𝒦₁` and with the surjection onto `ℱ`. Then
the class of `ℱ'₁` is the image of the class of `ℱ'₂` under `k`. -/
theorem underlyingExtensionClass_eq_of_pushoutMap (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂)
    (hi₁ : IsFirstOrderThickening i₁) (hi₂ : IsFirstOrderThickening i₂)
    (π₁ : SplitMono i₁) (π₂ : SplitMono i₂)
    (hπ : π₁.retraction = h ≫ π₂.retraction)
    (F K₁ K₂ : SheafOfModules.{u} (structureSheafRing X)) (k : K₂ ⟶ K₁)
    (c₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (idealSheafPullback i₁)).obj F ⟶ K₁)
    (c₂ : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
      (idealSheafPullback i₂)).obj F ⟶ K₂)
    (hc : c₂ ≫ k =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        ((thickeningIdealMap i₁ i₂ h comm, 𝟙 F) : (_, _) ⟶ (_, _)) ≫ c₁)
    (E₂ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₂).obj F)
      ((modulePushforward i₂).obj K₂) 0)
    (hE₂ : (firstOrderExtensionAction i₂ F K₂ hi₂ E₂).val = c₂)
    (E₁ : CategoryTheory.Abelian.YonedaExtension ((modulePushforward i₁).obj F)
      ((modulePushforward i₁).obj K₁) 0)
    (hE₁ : (firstOrderExtensionAction i₁ F K₁ hi₁ E₁).val = c₁)
    (φ : (pushoutExtension i₂ F K₁ K₂ k E₂).Z.left ⟶ (modulePushforward h).obj E₁.Z.left)
    (hf : (pushoutExtension i₂ F K₁ K₂ k E₂).f ≫ φ =
      (thickeningPushforwardComp i₁ i₂ h comm).inv.app K₁ ≫ (modulePushforward h).map E₁.f)
    (hg : φ ≫ (modulePushforward h).map E₁.g =
      (pushoutExtension i₂ F K₁ K₂ k E₂).g ≫
        (thickeningPushforwardComp i₁ i₂ h comm).inv.app F) :
    underlyingExtensionClass i₁ π₁ hi₁.1.1 F K₁ E₁ =
      (underlyingExtensionClass i₂ π₂ hi₂.1.1 F K₂ E₂).comp
        (CategoryTheory.Abelian.Ext.mk₀ k) (add_zero 1) :=
  underlyingExtensionClass_eq_of_pushedExtension i₁ i₂ h comm hi₁ hi₂ π₁ π₂ hπ F K₁ K₂ k c₁ c₂
    hc E₂ hE₂ E₁ hE₁ (PushedExtension.ofPushoutMap i₁ i₂ h comm F K₁ K₂ k φ hf hg)

end AlgebraicGeometry.RingedSpaceThickening

end
