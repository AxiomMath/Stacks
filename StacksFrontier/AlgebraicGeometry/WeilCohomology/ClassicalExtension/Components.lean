module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalChowCycleData
import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Projective
import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The connected components of a smooth projective scheme

A smooth projective scheme `X` over a field `k` is the disjoint union of its connected
components, finitely many open and closed subschemes, and each of them is a smooth projective
variety: it is smooth and projective over `k`, being open and closed in `X`, and it is
irreducible, being connected and smooth over a field, hence integral. A morphism `f : X ⟶ Y`
carries each component of `X` into one component of `Y` and so restricts to a morphism of
smooth projective varieties between them. This is the decomposition along which a cohomology
theory defined on smooth projective varieties extends to all smooth projective schemes; Stacks
0FH2 uses it ("every smooth projective scheme is canonically a disjoint union of smooth
projective varieties").

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.Components`: the connected components of `X`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.comp`: the component `X_c`, as a smooth
  projective variety.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.compι`: its inclusion `X_c ⟶ X`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.compMap`: the map on components induced by a
  morphism.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.resComp`: the restriction `X_c ⟶ Y_{f(c)}` of
  a morphism `f : X ⟶ Y`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.finite_components`: there are finitely many
  components.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.resComp_compι`: `resComp f c` is a restriction
  of `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- The underlying scheme of a smooth projective scheme over `k` is locally Noetherian. -/
instance isLocallyNoetherian_left : IsLocallyNoetherian X.obj.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.obj.hom

/-- The underlying space of a smooth projective scheme over `k` is quasi-compact. -/
instance compactSpace_left : CompactSpace X.obj.left :=
  QuasiCompact.compactSpace_of_compactSpace X.obj.hom

/-- The connected components of a smooth projective scheme over `k`. -/
abbrev Components : Type u :=
  _root_.ConnectedComponents X.obj.left

/-- A smooth projective scheme has finitely many connected components: they are open, as the
scheme is locally Noetherian, and they cover the quasi-compact space. -/
@[sga "3 VIA 2.3" "special case", sga "3 X 5.11.0" "special case"]
instance finite_components : Finite (Components X) := by
  have : DiscreteTopology (Components X) :=
    _root_.ConnectedComponents.discreteTopology_iff.2 fun _ ↦
    isOpen_connectedComponent
  have : CompactSpace (Components X) := _root_.ConnectedComponents.surjective_coe.compactSpace
    _root_.ConnectedComponents.continuous_coe
  exact finite_of_compact_of_discrete

/-- The connected components of a smooth projective scheme form a finite type. -/
instance : Fintype (Components X) :=
  Fintype.ofFinite _

/-- The connected component `X_c`, as an open subscheme of `X`. -/
abbrev compOpens (c : Components X) : X.obj.left.Opens :=
  X.obj.left.connectedComponentOpens c

/-- The connected component `X_c` is closed in `X`. -/
theorem isClosed_compOpens (c : Components X) : IsClosed (compOpens X c : Set X.obj.left) :=
  X.obj.left.isClosed_connectedComponentOpens c

/-- The connected component `X_c` is connected. -/
instance connectedSpace_compOpens (c : Components X) : ConnectedSpace (compOpens X c) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  have h : (compOpens X (_root_.ConnectedComponents.mk x) : Set X.obj.left) =
      connectedComponent x := by
    rw [Scheme.coe_connectedComponentOpens, connectedComponents_preimage_singleton]
  exact Subtype.connectedSpace (h ▸ isConnected_connectedComponent)

/-- The inclusion of the connected component `X_c` into `X` is a closed immersion. -/
instance isClosedImmersion_compOpens_ι (c : Components X) : IsClosedImmersion (compOpens X c).ι :=
  .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact isClosed_compOpens X c)

/-- The inclusion of the connected component `X_c` into `X` is proper. -/
instance isProper_compOpens_ι (c : Components X) : IsProper (compOpens X c).ι :=
  inferInstance

/-- **A connected component of a smooth projective scheme over `k` is a smooth projective
variety.** -/
theorem smoothProjective_comp (c : Components X) :
    SmoothProjective k (Over.mk ((compOpens X c).ι ≫ X.obj.hom)) := by
  set U := compOpens X c
  have : Smooth ((compOpens X c).ι ≫ X.obj.hom) := inferInstance
  have : IsReduced U.toScheme := isReduced_of_smooth (U.ι ≫ X.obj.hom)
  have : CompactSpace U := isCompact_iff_compactSpace.1 (isClosed_compOpens X c).isCompact
  have : IrreducibleSpace U.toScheme :=
    irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace (U.ι ≫ X.obj.hom)
  have : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsVariety k (U.ι ≫ X.obj.hom) := by constructor
  refine ⟨(isSmoothVariety_iff k (U.ι ≫ X.obj.hom)).2 ⟨‹_›, ‹_›⟩, ?_⟩
  exact (isProjective_iff_isProjectiveMorphism_of_isAffine _).1
    (Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion _ _
      inferInstance X.property.2)

/-- **The connected component `X_c`**, as a smooth projective variety over `k`. -/
abbrev comp (c : Components X) : (SmoothProjective k).FullSubcategory :=
  ⟨Over.mk ((compOpens X c).ι ≫ X.obj.hom), smoothProjective_comp X c⟩

/-- The underlying scheme of `comp X c` is the open subscheme `compOpens X c`. -/
@[simp]
theorem comp_obj_left (c : Components X) : (comp X c).obj.left = (compOpens X c).toScheme :=
  rfl

/-- The structure morphism of `comp X c` is the restriction of that of `X`. -/
@[simp]
theorem comp_obj_hom (c : Components X) : (comp X c).obj.hom = (compOpens X c).ι ≫ X.obj.hom :=
  rfl

/-- The inclusion `X_c ⟶ X` of a connected component. -/
def compι (c : Components X) : (SmoothProjective.toSchemeCat k).obj (comp X c) ⟶ X :=
  ObjectProperty.homMk (Over.homMk (compOpens X c).ι rfl)

/-- The underlying morphism of `compι X c` is the open immersion of `compOpens X c`. -/
@[simp]
theorem compι_left (c : Components X) : (compι X c).hom.left = (compOpens X c).ι :=
  rfl

/-- The inclusion `X_c ⟶ X` of a connected component is an open immersion. -/
instance isOpenImmersion_compι_left (c : Components X) : IsOpenImmersion (compι X c).hom.left :=
  inferInstanceAs (IsOpenImmersion (compOpens X c).ι)

/-- The inclusion `X_c ⟶ X` of a connected component is a closed immersion. -/
instance isClosedImmersion_compι_left (c : Components X) : IsClosedImmersion (compι X c).hom.left :=
  inferInstanceAs (IsClosedImmersion (compOpens X c).ι)

/-- Morphisms between full subcategories of `Over S` are determined by their left components. -/
private theorem hom_ext_of_left_eq {S : Scheme.{u}} {P : ObjectProperty (Over S)}
    {A B : P.FullSubcategory} {f g : A ⟶ B} (h : f.hom.left = g.hom.left) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext h)

/-- Morphisms out of a component are determined by their underlying morphisms of schemes. -/
theorem comp_hom_ext {V : (SmoothProjective k).FullSubcategory} {c : Components X}
    {f g : V ⟶ comp X c} (h : f.hom.left = g.hom.left) : f = g :=
  hom_ext_of_left_eq h

/-- Morphisms into a component are determined after composing with its inclusion. -/
theorem comp_hom_ext' {V : (SmoothProjective k).FullSubcategory} {c : Components X}
    {f g : V ⟶ comp X c} (h : f.hom.left ≫ (compOpens X c).ι = g.hom.left ≫ (compOpens X c).ι) :
    f = g :=
  hom_ext_of_left_eq (by
    have : Mono (compOpens X c).ι := IsOpenImmersion.mono _
    exact Mono.right_cancellation _ _ h)

variable {X} {Y Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- The map on connected components induced by a morphism. -/
def compMap (f : X ⟶ Y) : Components X → Components Y :=
  f.hom.left.continuous.connectedComponentsMap

/-- The identity morphism induces the identity on connected components. -/
theorem compMap_id (c : Components X) : compMap (𝟙 X) c = c := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  exact Continuous.connectedComponentsMap_mk _ x

/-- The map on connected components induced by a composite is the composite of the maps. -/
theorem compMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (c : Components X) :
    compMap (f ≫ g) c = compMap g (compMap f c) := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
  simp only [compMap, Continuous.connectedComponentsMap_mk]
  rfl

/-- **The restriction `X_c ⟶ Y_{f(c)}` of a morphism `f : X ⟶ Y`** to a connected component of
its source and the component of its target it maps into. -/
def resComp (f : X ⟶ Y) (c : Components X) : comp X c ⟶ comp Y (compMap f c) :=
  ObjectProperty.homMk (Over.homMk (f.hom.left.resConnectedComponent c)
    (Scheme.Hom.resConnectedComponent_comp_ι_comp _ (Over.w f.hom) c))

/-- The restriction `X_c ⟶ Y_{f(c)}`, followed by the inclusion of `Y_{f(c)}`, is the inclusion
of `X_c` followed by `f`. -/
@[reassoc (attr := simp)]
theorem resComp_left_ι (f : X ⟶ Y) (c : Components X) :
    (resComp f c).hom.left ≫ (compOpens Y (compMap f c)).ι = (compOpens X c).ι ≫ f.hom.left :=
  Scheme.Hom.resConnectedComponent_comp_ι _ c

/-- `resComp f c` is a restriction of `f`. -/
@[reassoc]
theorem resComp_compι (f : X ⟶ Y) (c : Components X) :
    (SmoothProjective.toSchemeCat k).map (resComp f c) ≫ compι Y (compMap f c) =
      compι X c ≫ f :=
  hom_ext_of_left_eq (resComp_left_ι f c)

/-- The restriction `X_c ⟶ Y_d` of a morphism `f : X ⟶ Y`, for any name `d` of the component
`f` maps `X_c` into. -/
def resCompOf (f : X ⟶ Y) (c : Components X) (d : Components Y) (h : compMap f c = d) :
    comp X c ⟶ comp Y d :=
  h ▸ resComp f c

/-- The restriction `X_c ⟶ Y_d`, followed by the inclusion of `Y_d`, is the inclusion of `X_c`
followed by `f`. -/
@[reassoc (attr := simp)]
theorem resCompOf_left_ι (f : X ⟶ Y) (c : Components X) (d : Components Y)
    (h : compMap f c = d) :
    (resCompOf f c d h).hom.left ≫ (compOpens Y d).ι = (compOpens X c).ι ≫ f.hom.left := by
  subst h
  exact resComp_left_ι f c

/-! ### An enumeration of the components

The components of `X` form a type in the universe of `X`; an enumeration by `Fin n` lets
products over them stay in any universe. -/

variable (X) in
/-- The indices `0, …, n - 1` of the `n` connected components of `X`. -/
abbrev Idx : Type :=
  Fin (Fintype.card (Components X))

variable (X) in
/-- The enumeration of the connected components of `X`. -/
def idxEquiv : Idx X ≃ Components X :=
  (Fintype.equivFin _).symm

variable (X) in
/-- The connected component of `X` with index `i`, as a smooth projective variety. -/
abbrev compAt (i : Idx X) : (SmoothProjective k).FullSubcategory :=
  comp X (idxEquiv X i)

variable (X) in
/-- The inclusion of the connected component of `X` with index `i`. -/
abbrev compAtι (i : Idx X) : (SmoothProjective.toSchemeCat k).obj (compAt X i) ⟶ X :=
  compι X (idxEquiv X i)

/-- The map on indices of components induced by a morphism. -/
def idxMap (f : X ⟶ Y) (i : Idx X) : Idx Y :=
  (idxEquiv Y).symm (compMap f (idxEquiv X i))

/-- The component of `Y` with index `idxMap f i` is the image under `f` of the component of `X`
with index `i`. -/
theorem idxEquiv_idxMap (f : X ⟶ Y) (i : Idx X) :
    idxEquiv Y (idxMap f i) = compMap f (idxEquiv X i) :=
  (idxEquiv Y).apply_symm_apply _

/-- The identity morphism induces the identity on indices of components. -/
theorem idxMap_id (i : Idx X) : idxMap (𝟙 X) i = i := by
  simp [idxMap, compMap_id]

/-- The map on indices of components induced by a composite is the composite of the maps. -/
theorem idxMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (i : Idx X) :
    idxMap (f ≫ g) i = idxMap g (idxMap f i) := by
  simp [idxMap, compMap_comp]

/-- **The restriction of `f : X ⟶ Y` to the component of index `i`** and the component of `Y` it
maps into. -/
def resIdx (f : X ⟶ Y) (i : Idx X) : compAt X i ⟶ compAt Y (idxMap f i) :=
  resCompOf f _ _ (idxEquiv_idxMap f i).symm

/-- The restriction `resIdx f i`, followed by the inclusion of its target component, is the
inclusion of the component of index `i` followed by `f`. -/
@[reassoc (attr := simp)]
theorem resIdx_left_ι (f : X ⟶ Y) (i : Idx X) :
    (resIdx f i).hom.left ≫ (compOpens Y (idxEquiv Y (idxMap f i))).ι =
      (compOpens X (idxEquiv X i)).ι ≫ f.hom.left :=
  resCompOf_left_ι _ _ _ _

/-- `resIdx f i` is a restriction of `f`. -/
@[reassoc]
theorem resIdx_compAtι (f : X ⟶ Y) (i : Idx X) :
    (SmoothProjective.toSchemeCat k).map (resIdx f i) ≫ compAtι Y (idxMap f i) =
      compAtι X i ≫ f :=
  hom_ext_of_left_eq (resIdx_left_ι f i)

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
