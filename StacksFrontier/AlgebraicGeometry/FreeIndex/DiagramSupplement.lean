module

public import StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic
public import StacksFrontier.AlgebraicGeometry.FreeIndex.Diagram
public import StacksFrontier.AlgebraicGeometry.FreeIndex.Punctured
public import StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.BasicSupplement

/-!
# The system of punctured planes over a field of arbitrary universe

For a field `F` in universe `w`, this module constructs, at an arbitrary universe `u` of schemes,
the cofiltered system indexed by `(Finset F)ᵒᵖ` of affine planes over the rings `stageUniv F T`,
and its subsystem of punctured planes. Every scheme of the punctured system is quasi-compact,
quasi-separated and not affine, and every transition morphism is affine. When `F` is not
`u`-small, the limit of the punctured system is the empty scheme.

## Main definitions

* `planeDiagramUniv`: The system of affine planes over the rings `stageUniv F T`.
* `stageOpenUniv`: The punctured plane, as an open subscheme of the affine plane.
* `diagramUniv`: The system of punctured planes.
* `stageιUniv`: The open immersion of a punctured plane into the affine plane.
* `baseMapUniv`: The structure morphism of an affine plane over its base ring.
* `legMapUniv`: The morphism from a punctured plane to the spectrum of its base ring.
* `toSchemeDiagramConeUniv`: A cone over `diagramUniv F` as a cone over `schemeDiagramUniv F`.
* `emptyConeUniv`: The cone over `diagramUniv F` with the empty scheme as vertex.

## Main results

* `not_isAffine_diagram_obj_univ`: No scheme of the punctured system is affine.
* `isEmpty_cone_pt_univ`: If `F` is not `u`-small, every cone over `diagramUniv F` has an empty
  vertex.
* `isEmpty_cone_pt_of_mk_lt`: A cone over `diagramUniv K` whose vertex has fewer global sections
  than `K` has elements has an empty vertex.
* `isLimitEmptyConeUniv`: If `F` is not `u`-small, the empty cone is a limit cone.
-/

universe w u

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Stacks.Refute09ZM

variable (F : Type w) [Field F]

open Stacks.EmptyLimitCounterexample

/-- The transition map `stageMapUniv` along `T ≤ T` is the identity. -/
theorem stageMap_self_univ (T : Finset F) :
    stageMapUniv F (le_refl T) = RingHom.id (stageUniv F T) :=
  RingHom.ext fun x => by simp [stageMapUniv, RingEquiv.symm_apply_eq, Subtype.ext_iff]

/-- The transition maps `stageMapUniv` compose along `T₁ ≤ T₂ ≤ T₃`. -/
theorem stageMap_trans_univ {T₁ T₂ T₃ : Finset F} (h₁ : T₁ ≤ T₂) (h₂ : T₂ ≤ T₃) :
    stageMapUniv F (h₁.trans h₂) = (stageMapUniv F h₂).comp (stageMapUniv F h₁) :=
  RingHom.ext fun x => by simp [stageMapUniv, Subtype.ext_iff]

/-- The cofiltered system of **affine planes** over the rings `stageUniv F T`. -/
def planeDiagramUniv : (Finset F)ᵒᵖ ⥤ Scheme.{u} where
  obj T := affinePlane (stageUniv F T.unop)
  map {_ _} f := specPlaneMap (stageMapUniv F (leOfHom f.unop))
  map_id T := by
    rw [show stageMapUniv F (leOfHom (𝟙 T).unop) = RingHom.id _ from stageMap_self_univ F _,
      specPlaneMap_id]
  map_comp {T₁ T₂ T₃} f g := by
    rw [show stageMapUniv F (leOfHom (f ≫ g).unop)
        = (stageMapUniv F (leOfHom f.unop)).comp (stageMapUniv F (leOfHom g.unop)) from
      stageMap_trans_univ F _ _, specPlaneMap_comp]

/-- The plane system at `T` is the affine plane over `stageUniv F T`. -/
@[simp] theorem planeDiagram_obj_univ (T : Finset F) :
    (planeDiagramUniv F).obj (op T) = affinePlane (stageUniv F T) := rfl

/-- The transition morphisms of the plane system are induced by `stageMapUniv`. -/
@[simp] theorem planeDiagram_map_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (planeDiagramUniv F).map f = specPlaneMap (stageMapUniv F (leOfHom f.unop)) := rfl

/-- The open subscheme of the affine plane at `T`: the punctured plane over `stageUniv F T`. -/
abbrev stageOpenUniv (T : (Finset F)ᵒᵖ) : ((planeDiagramUniv F).obj T).Opens :=
  puncturedOpen (stageUniv F T.unop)

/-- The punctured plane at `T` is the preimage of the punctured plane at `T'` under a transition
morphism of the plane system. -/
theorem preimage_stageOpen_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    stageOpenUniv F T = (planeDiagramUniv F).map f ⁻¹ᵁ stageOpenUniv F T' :=
  (preimage_puncturedOpen _).symm

/-- **The system of punctured planes.** Every scheme of the system is quasi-compact,
quasi-separated and not affine, and every transition morphism is affine. -/
def diagramUniv : (Finset F)ᵒᵖ ⥤ Scheme.{u} where
  obj T := (stageOpenUniv F T).toScheme
  map {_ _} f := ((planeDiagramUniv F).map f).resLE _ _ (le_of_eq (preimage_stageOpen_univ F f))
  map_id T := by
    rw [← cancel_mono (stageOpenUniv F T).ι, Scheme.Hom.resLE_comp_ι, Category.id_comp,
      (planeDiagramUniv F).map_id, Category.comp_id]
  map_comp {T₁ T₂ T₃} f g := by
    rw [← cancel_mono (stageOpenUniv F T₃).ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, (planeDiagramUniv F).map_comp]

/-- The punctured system at `T` is the open subscheme `stageOpenUniv F T`. -/
@[simp] theorem diagram_obj_univ (T : (Finset F)ᵒᵖ) :
    (diagramUniv F).obj T = (stageOpenUniv F T).toScheme := rfl

/-- The open immersion of the punctured plane `(diagramUniv F).obj T` into the affine plane
`(planeDiagramUniv F).obj T`. -/
def stageιUniv (T : (Finset F)ᵒᵖ) : (diagramUniv F).obj T ⟶ (planeDiagramUniv F).obj T :=
  (stageOpenUniv F T).ι

/-- The open immersions `stageιUniv` form a natural transformation from the punctured system to
the plane system. -/
theorem diagram_map_comp_stageι_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (diagramUniv F).map f ≫ stageιUniv F T' = stageιUniv F T ≫ (planeDiagramUniv F).map f :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The transition morphisms of the plane system are affine. -/
instance isAffineHom_planeDiagram_map_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    IsAffineHom ((planeDiagramUniv F).map f) :=
  inferInstanceAs (IsAffineHom (specPlaneMap _))

/-- The transition morphisms of the punctured system are affine. -/
instance isAffineHom_diagram_map_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    IsAffineHom ((diagramUniv F).map f) :=
  isAffineHom_resLE_of_eq ((planeDiagramUniv F).map f) (preimage_stageOpen_univ F f)

/-- Every scheme of the punctured system is quasi-compact. -/
instance compactSpace_diagram_obj_univ (T : (Finset F)ᵒᵖ) : CompactSpace ((diagramUniv F).obj T) :=
  inferInstanceAs (CompactSpace (punctured (stageUniv F T.unop)))

/-- Every scheme of the punctured system is quasi-separated. -/
instance quasiSeparatedSpace_diagram_obj_univ (T : (Finset F)ᵒᵖ) :
    QuasiSeparatedSpace ((diagramUniv F).obj T) :=
  inferInstanceAs (QuasiSeparatedSpace (punctured (stageUniv F T.unop)))

/-- **No scheme of the punctured system is affine.** -/
theorem not_isAffine_diagram_obj_univ (T : (Finset F)ᵒᵖ) : ¬ IsAffine ((diagramUniv F).obj T) :=
  not_isAffine_punctured (stageUniv F T.unop)

section Limit

/-- The structure morphism from the affine plane `(planeDiagramUniv F).obj T` to the spectrum
`(schemeDiagramUniv F).obj T` of its base ring. -/
def baseMapUniv (T : (Finset F)ᵒᵖ) : (planeDiagramUniv F).obj T ⟶ (schemeDiagramUniv F).obj T :=
  specPlaneBase (stageUniv F T.unop)

/-- The structure morphisms `baseMapUniv` form a natural transformation from the plane system to
`schemeDiagramUniv F`. -/
theorem planeDiagram_map_comp_baseMap_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (planeDiagramUniv F).map f ≫ baseMapUniv F T' = baseMapUniv F T ≫ (schemeDiagramUniv F).map f :=
  specPlaneMap_comp_specPlaneBase _

/-- The morphism from the punctured plane `(diagramUniv F).obj T` to
`(schemeDiagramUniv F).obj T`: the open immersion `stageιUniv` followed by `baseMapUniv`. -/
def legMapUniv (T : (Finset F)ᵒᵖ) : (diagramUniv F).obj T ⟶ (schemeDiagramUniv F).obj T :=
  stageιUniv F T ≫ baseMapUniv F T

/-- The morphisms `legMapUniv` form a natural transformation from the punctured system to
`schemeDiagramUniv F`. -/
theorem legMap_naturality_univ {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (diagramUniv F).map f ≫ legMapUniv F T' = legMapUniv F T ≫ (schemeDiagramUniv F).map f := by
  rw [legMapUniv, legMapUniv, ← Category.assoc, diagram_map_comp_stageι_univ, Category.assoc,
    planeDiagram_map_comp_baseMap_univ, ← Category.assoc]

/-- A cone over the system of punctured planes, read as a cone over `schemeDiagramUniv F` by
composing with `legMapUniv`. -/
def toSchemeDiagramConeUniv (s : Cone (diagramUniv F)) : Cone (schemeDiagramUniv F) where
  pt := s.pt
  π :=
    { app := fun T => s.π.app T ≫ legMapUniv F T
      naturality := fun T T' f => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.id_comp, ← s.w f, Category.assoc, legMap_naturality_univ, Category.assoc] }

/-- **The limit of the system of punctured planes is the empty scheme**: if the ground field is not
`u`-small, every cone over the system has an empty vertex. -/
theorem isEmpty_cone_pt_univ (hF : ¬ Small.{u} F) (s : Cone (diagramUniv.{w, u} F)) :
    IsEmpty s.pt :=
  Stacks.EmptyLimitCounterexample.isEmpty_cone_pt_univ F hF (toSchemeDiagramConeUniv F s)

/-- **The limit of the system of punctured planes is empty, measured by cardinality.** A cone
over it whose vertex has fewer global sections than the ground field has elements has an empty
vertex. -/
theorem isEmpty_cone_pt_of_mk_lt {K : Type u} [Field K] (s : Cone (diagramUniv K))
    (hK : Cardinal.mk Γ(s.pt, ⊤) < Cardinal.mk K) : IsEmpty s.pt :=
  Stacks.EmptyLimitCounterexample.isEmpty_cone_pt_of_mk_lt (toSchemeDiagramConeUniv K s) hK

end Limit

/-- The cone over the system with the empty scheme as vertex. -/
def emptyConeUniv : Cone (diagramUniv F) where
  pt := ∅
  π :=
    { app := fun _ => emptyIsInitial.to _
      naturality := fun _ _ _ => emptyIsInitial.hom_ext _ _ }

/-- The vertex of `emptyConeUniv F` is the empty scheme. -/
@[simp] theorem emptyCone_pt_univ : (emptyConeUniv F).pt = ∅ := rfl

/-- **The empty cone is a limit cone.** -/
def isLimitEmptyConeUniv (hF : ¬ Small.{u} F) : IsLimit (emptyConeUniv.{w, u} F) where
  lift s := by
    have := isEmpty_cone_pt_univ F hF s
    exact isInitialOfIsEmpty.to _
  fac s j := by
    have := isEmpty_cone_pt_univ F hF s
    exact (isInitialOfIsEmpty (X := s.pt)).hom_ext _ _
  uniq s m _ := by
    have := isEmpty_cone_pt_univ F hF s
    exact (isInitialOfIsEmpty (X := s.pt)).hom_ext _ _

end Stacks.Refute09ZM

end

end
