module

public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Connected components of a locally connected scheme

On a scheme whose underlying space is locally connected — for instance any locally Noetherian
scheme — each connected component is open as well as closed, so it is an open subscheme, and
the scheme is the coproduct of its connected components. A morphism of such schemes carries
each component of the source into a unique component of the target, namely the one selected by
the induced map on connected components, and therefore restricts to a morphism between them.

This is the decomposition `X = ∐_{i ∈ I} X_i` that chapter 42 of the Stacks Project uses to cut
a bivariant class into its components.

## Main definitions

* `AlgebraicGeometry.Scheme.connectedComponentOpens` — a connected component, as an open
  subscheme.
* `AlgebraicGeometry.Scheme.connectedComponentsCoproductIso` — the identification of a scheme
  with the coproduct of its connected components.
* `AlgebraicGeometry.Scheme.Hom.resConnectedComponent` — the restriction of a morphism to a
  component of its source and the corresponding component of its target.

## Main results

* `AlgebraicGeometry.Scheme.isClosed_connectedComponentOpens` — the components are closed.
* `AlgebraicGeometry.Scheme.Hom.mapsTo_connectedComponentOpens` and
  `AlgebraicGeometry.Scheme.Hom.eq_connectedComponentsMap_of_mapsTo` — the target component a
  source component lands in exists and is unique.
* `AlgebraicGeometry.Scheme.Hom.resConnectedComponent_comp_ι` and
  `AlgebraicGeometry.Scheme.Hom.resConnectedComponent_comp_ι_comp` — the restriction is a
  restriction of the given morphism, and it is a morphism over any base the given morphism is
  a morphism over.

## Implementation notes

The index type is Mathlib's `ConnectedComponents` of the underlying space and a component is
the fibre of `ConnectedComponents.mk` over its index; the induced map on indices is Mathlib's
`Continuous.connectedComponentsMap`. Local connectedness enters only to make those fibres open;
`TopologicalSpace.IsLocallyNoetherianSpace.locallyConnectedSpace` supplies it on a locally
Noetherian scheme.

The coproduct isomorphism is obtained from the open-immersion inclusions by
`AlgebraicGeometry.nonempty_isColimit_cofanMk_of`, which needs exactly that the components
cover and are pairwise disjoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X Y : Scheme.{u})

section Opens

variable [LocallyConnectedSpace X]

/-- A connected component of a locally connected scheme, as an open subscheme. It is the fibre
of `ConnectedComponents.mk` over the given index, which is open because the space is locally
connected. -/
def connectedComponentOpens (i : ConnectedComponents X) : X.Opens where
  carrier := ConnectedComponents.mk ⁻¹' {i}
  is_open' := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent

/-- The underlying set of a connected component is the fibre of `ConnectedComponents.mk` over its
index. -/
@[simp]
theorem coe_connectedComponentOpens (i : ConnectedComponents X) :
    (X.connectedComponentOpens i : Set X) = ConnectedComponents.mk ⁻¹' {i} :=
  rfl

/-- A point lies in the connected component of index `i` exactly when its connected component is
`i`. -/
@[simp]
theorem mem_connectedComponentOpens {i : ConnectedComponents X} {x : X} :
    x ∈ X.connectedComponentOpens i ↔ ConnectedComponents.mk x = i :=
  Iff.rfl

/-- A connected component of a locally connected scheme is closed as well as open. -/
theorem isClosed_connectedComponentOpens (i : ConnectedComponents X) :
    IsClosed (X.connectedComponentOpens i : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [coe_connectedComponentOpens, connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

/-- The connected components cover the scheme. -/
theorem iSup_connectedComponentOpens : ⨆ i, X.connectedComponentOpens i = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨ConnectedComponents.mk x, rfl⟩

/-- Distinct connected components are disjoint. -/
theorem disjoint_connectedComponentOpens {i j : ConnectedComponents X} (h : i ≠ j) :
    Disjoint (X.connectedComponentOpens i) (X.connectedComponentOpens j) :=
  disjoint_iff.2 <| Opens.ext <| Set.eq_empty_iff_forall_notMem.2 fun _ hx ↦
    h (hx.1.symm.trans hx.2)

/-- The canonical map from the coproduct of the connected components to the scheme is an
isomorphism: the components are open, they cover, and they are pairwise disjoint. -/
instance isIso_sigmaDesc_connectedComponentOpens :
    IsIso (Sigma.desc fun i : ConnectedComponents X ↦ (X.connectedComponentOpens i).ι) := by
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk X fun i ↦ (X.connectedComponentOpens i).ι)).mp
      (nonempty_isColimit_cofanMk_of _ ?_ fun i j hij ↦ ?_)
  · simpa only [Scheme.Opens.opensRange_ι] using X.iSup_connectedComponentOpens
  · simpa only [Scheme.Opens.opensRange_ι] using X.disjoint_connectedComponentOpens hij

/-- **The decomposition of a locally connected scheme into its connected components**: the
coproduct of the components, with their open immersions, is the scheme itself. -/
noncomputable def connectedComponentsCoproductIso :
    (∐ fun i : ConnectedComponents X ↦ (X.connectedComponentOpens i : Scheme.{u})) ≅ X :=
  asIso (Sigma.desc fun i : ConnectedComponents X ↦ (X.connectedComponentOpens i).ι)

end Opens

namespace Hom

variable {X Y} [LocallyConnectedSpace X] [LocallyConnectedSpace Y] (f : X ⟶ Y)

/-- A morphism carries a connected component of its source into the connected component of its
target selected by the induced map on connected components. -/
theorem connectedComponentOpens_le_preimage (i : ConnectedComponents X) :
    X.connectedComponentOpens i ≤
      f ⁻¹ᵁ Y.connectedComponentOpens (f.continuous.connectedComponentsMap i) := by
  rintro x (hx : ConnectedComponents.mk x = i)
  exact hx ▸ (f.continuous.connectedComponentsMap_mk x).symm

/-- A morphism carries a connected component of its source into the connected component of its
target selected by the induced map on connected components. -/
theorem mapsTo_connectedComponentOpens (i : ConnectedComponents X) :
    Set.MapsTo f.base (X.connectedComponentOpens i : Set X)
      (Y.connectedComponentOpens (f.continuous.connectedComponentsMap i) : Set Y) :=
  f.connectedComponentOpens_le_preimage i

/-- The connected component of the target that a given connected component of the source maps
into is unique. -/
theorem eq_connectedComponentsMap_of_mapsTo {i : ConnectedComponents X}
    {j : ConnectedComponents Y}
    (h : Set.MapsTo f.base (X.connectedComponentOpens i : Set X)
      (Y.connectedComponentOpens j : Set Y)) :
    j = f.continuous.connectedComponentsMap i := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  exact ((h (rfl : ConnectedComponents.mk x = _)) :
    ConnectedComponents.mk (f.base x) = j).symm.trans (f.continuous.connectedComponentsMap_mk x)

/-- The restriction of a morphism to a connected component of its source and the connected
component of its target that component maps into. -/
noncomputable def resConnectedComponent (i : ConnectedComponents X) :
    (X.connectedComponentOpens i : Scheme.{u}) ⟶
      (Y.connectedComponentOpens (f.continuous.connectedComponentsMap i) : Scheme.{u}) :=
  f.resLE _ _ (f.connectedComponentOpens_le_preimage i)

/-- The restriction of `f` to a connected component, followed by the inclusion of the target
component, is the inclusion of the source component followed by `f`. -/
@[simp, reassoc]
theorem resConnectedComponent_comp_ι (i : ConnectedComponents X) :
    f.resConnectedComponent i ≫
        (Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)).ι =
      (X.connectedComponentOpens i).ι ≫ f :=
  f.resLE_comp_ι _

/-- Restricting a morphism over a base `S` to a connected component of its source and the
corresponding component of its target is again a morphism over `S`, for the structure
morphisms the component inclusions induce. -/
@[reassoc]
theorem resConnectedComponent_comp_ι_comp {S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    (hf : f ≫ sY = sX) (i : ConnectedComponents X) :
    f.resConnectedComponent i ≫
        ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap i)).ι ≫ sY) =
      (X.connectedComponentOpens i).ι ≫ sX := by
  rw [← Category.assoc, resConnectedComponent_comp_ι, Category.assoc, hf]

/-- The restriction of a morphism locally of finite type to connected components is locally of
finite type. -/
instance locallyOfFiniteType_resConnectedComponent [LocallyOfFiniteType f]
    (i : ConnectedComponents X) : LocallyOfFiniteType (f.resConnectedComponent i) :=
  inferInstanceAs (LocallyOfFiniteType (f.resLE _ _ _))

end Hom

/-- A locally Noetherian scheme is locally connected, so its connected components are open. -/
@[ega "I 6.1.9" "special case",
  sga "1 IX 5.1" "more general",
  sga "3 VIA 2.3" "partial",
  sga "3 X 5.11.0" "more general",
  sga "3 X 6.2" "partial"]
instance locallyConnectedSpace_of_isLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyConnectedSpace X :=
  IsLocallyNoetherianSpace.locallyConnectedSpace X
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X)

end AlgebraicGeometry.Scheme

end
