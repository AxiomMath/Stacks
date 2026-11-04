module

public import StacksFrontier.AlgebraicGeometry.FreeIndex.Punctured
public import StacksFrontier.AlgebraicGeometry.EmptyLimitCounterexample.Basic

/-!
# A large cofiltered system of punctured planes whose limit is the empty scheme

This file carries the system that refutes [Stacks, Tag 09ZM] once the index category's universe
is freed from the scheme universe.  It is the system
`Stacks.EmptyLimitCounterexample.schemeDiagram`, which is a cofiltered system of nonempty affine
schemes in `Scheme.{u}` indexed by `Type (u+1)` whose limit in `Scheme.{u}` is empty, with every
stage replaced by the punctured plane over its coordinate ring.

Replacing the stages changes nothing about the limit — a cone over the new system still gives a
cone over the old one, by composing with the open immersion and with `Spec` of `MvPolynomial.C` —
and it changes everything about the stages: a punctured plane is quasi-compact, quasi-separated
and **not affine**, while the transition morphisms stay affine, being restrictions of affine
morphisms to an open and its exact inverse image.

## Main definitions

* `Stacks.Refute09ZM.planeDiagram`: the system of affine planes over the stage rings.
* `Stacks.Refute09ZM.diagram`: the system of punctured planes over the stage rings.
* `Stacks.Refute09ZM.emptyCone`: the cone over it with the empty scheme as vertex.

## Main results

* `Stacks.Refute09ZM.isAffineHom_diagram_map`: every transition morphism is affine.
* `Stacks.Refute09ZM.not_isAffine_diagram_obj`: no stage is affine.
* `Stacks.Refute09ZM.isLimitEmptyCone`: the empty cone is a limit cone, as soon as the ground
  field is not `u`-small.

## Implementation notes

The stages are open subschemes and the transition morphisms are `Scheme.Hom.resLE` of the
transition morphisms of affine planes.  Functoriality is `Scheme.Hom.resLE_comp_resLE`, and both
functor laws are checked after cancelling the open immersion, which is a monomorphism; that keeps
every proof obligation at the level of the ambient affine planes, where everything is `Spec` of a
ring homomorphism.

## References

* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
* [The Stacks Project, Tag 06AC](https://stacks.math.columbia.edu/tag/06AC)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Refute09ZM

section SpecPlane

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- `specPlaneMap` sends the identity ring homomorphism to the identity morphism. -/
theorem specPlaneMap_id : specPlaneMap (RingHom.id A) = 𝟙 (affinePlane A) := by
  rw [specPlaneMap, show (CommRingCat.ofHom (MvPolynomial.map (σ := Fin 2) (RingHom.id A)))
    = 𝟙 (CommRingCat.of (affinePlaneRing A)) from
    CommRingCat.hom_ext (RingHom.ext fun p => MvPolynomial.map_id p), Spec.map_id]

/-- `specPlaneMap` is contravariantly functorial: it sends a composite of ring homomorphisms to
the composite of the morphisms in the opposite order. -/
theorem specPlaneMap_comp (phi : B →+* A) (psi : C →+* B) :
    specPlaneMap (phi.comp psi) = specPlaneMap phi ≫ specPlaneMap psi := by
  have h : CommRingCat.ofHom (MvPolynomial.map (σ := Fin 2) (phi.comp psi))
      = CommRingCat.ofHom (MvPolynomial.map (σ := Fin 2) psi) ≫
        CommRingCat.ofHom (MvPolynomial.map (σ := Fin 2) phi) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (RingHom.ext fun p => (MvPolynomial.map_map _ _ p).symm)
  rw [specPlaneMap, specPlaneMap, specPlaneMap, h, Spec.map_comp]

/-- `Spec` of the inclusion of the base ring into the coordinate ring of the plane: the structure
morphism of the affine plane over its base. -/
def specPlaneBase (A : Type u) [CommRing A] :
    affinePlane A ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 2) (R := A)))

/-- The structure morphism `specPlaneBase` of the affine plane is natural in the base ring. -/
theorem specPlaneMap_comp_specPlaneBase (phi : B →+* A) :
    specPlaneMap phi ≫ specPlaneBase B
      = specPlaneBase A ≫ Spec.map (CommRingCat.ofHom phi) := by
  rw [specPlaneMap, specPlaneBase, specPlaneBase, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg Spec.map
    (congrArg CommRingCat.ofHom (RingHom.ext fun a => MvPolynomial.map_C _ a))

/-- The restriction `f.resLE U V` of an affine morphism `f : X ⟶ Y` to an open `U` of `Y` and an
open `V` of `X` equal to the inverse image `f ⁻¹ᵁ U` is affine. -/
theorem isAffineHom_resLE_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    {V : X.Opens} (h : V = f ⁻¹ᵁ U) : IsAffineHom (f.resLE U V (le_of_eq h)) := by
  have hiso : IsIso (X.homOfLE (le_of_eq h)) := by
    rw [show X.homOfLE (le_of_eq h) = (X.isoOfEq h).hom from rfl]
    infer_instance
  have hres : IsAffineHom (f ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict f U).flip ‹IsAffineHom f›
  delta Scheme.Hom.resLE
  infer_instance

end SpecPlane

variable (F : Type (u + 1)) [Field F]

open Stacks.EmptyLimitCounterexample

/-- The transition map of the stage rings along `T ≤ T` is the identity. -/
theorem stageMap_self (T : Finset F) : stageMap F (le_refl T) = RingHom.id (stage F T) :=
  RingHom.ext fun x => by simp [stageMap, RingEquiv.symm_apply_eq, Subtype.ext_iff]

/-- The transition maps of the stage rings compose: the map along `T₁ ≤ T₃` is the composite of
the maps along `T₁ ≤ T₂` and `T₂ ≤ T₃`. -/
theorem stageMap_trans {T₁ T₂ T₃ : Finset F} (h₁ : T₁ ≤ T₂) (h₂ : T₂ ≤ T₃) :
    stageMap F (h₁.trans h₂) = (stageMap F h₂).comp (stageMap F h₁) :=
  RingHom.ext fun x => by simp [stageMap, Subtype.ext_iff]

/-- The cofiltered system of **affine planes** over the stage rings `stage F T`, with transition
morphisms `specPlaneMap` of the transition maps `stageMap F`. -/
def planeDiagram : (Finset F)ᵒᵖ ⥤ Scheme.{u} where
  obj T := affinePlane (stage F T.unop)
  map {_ _} f := specPlaneMap (stageMap F (leOfHom f.unop))
  map_id T := by rw [show stageMap F (leOfHom (𝟙 T).unop) = RingHom.id _ from stageMap_self F _,
    specPlaneMap_id]
  map_comp {T₁ T₂ T₃} f g := by
    rw [show stageMap F (leOfHom (f ≫ g).unop)
        = (stageMap F (leOfHom f.unop)).comp (stageMap F (leOfHom g.unop)) from
      stageMap_trans F _ _, specPlaneMap_comp]

/-- The stage of `planeDiagram F` at `T` is the affine plane over `stage F T`. -/
@[simp] theorem planeDiagram_obj (T : Finset F) :
    (planeDiagram F).obj (op T) = affinePlane (stage F T) := rfl

/-- The transition morphism of `planeDiagram F` along `f` is `specPlaneMap` of the transition
map of the stage rings. -/
@[simp] theorem planeDiagram_map {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (planeDiagram F).map f = specPlaneMap (stageMap F (leOfHom f.unop)) := rfl

/-- The open subscheme of the stage at `T`: the punctured plane over the stage ring. -/
abbrev stageOpen (T : (Finset F)ᵒᵖ) : ((planeDiagram F).obj T).Opens :=
  puncturedOpen (stage F T.unop)

/-- The inverse image of the punctured plane under a transition morphism of `planeDiagram F` is
the punctured plane. -/
theorem preimage_stageOpen {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    stageOpen F T = (planeDiagram F).map f ⁻¹ᵁ stageOpen F T' :=
  (preimage_puncturedOpen _).symm

/-- **The system of punctured planes**: the stage at `T` is the open subscheme `stageOpen F T` of
the affine plane over `stage F T`, and the transition morphisms are the restrictions of those of
`planeDiagram F`. -/
def diagram : (Finset F)ᵒᵖ ⥤ Scheme.{u} where
  obj T := (stageOpen F T).toScheme
  map {_ _} f := ((planeDiagram F).map f).resLE _ _ (le_of_eq (preimage_stageOpen F f))
  map_id T := by
    rw [← cancel_mono (stageOpen F T).ι, Scheme.Hom.resLE_comp_ι, Category.id_comp,
      (planeDiagram F).map_id, Category.comp_id]
  map_comp {T₁ T₂ T₃} f g := by
    rw [← cancel_mono (stageOpen F T₃).ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, (planeDiagram F).map_comp]

/-- The stage of `diagram F` at `T` is the open subscheme `stageOpen F T`. -/
@[simp] theorem diagram_obj (T : (Finset F)ᵒᵖ) :
    (diagram F).obj T = (stageOpen F T).toScheme := rfl

/-- The open immersion of the stage of `diagram F` at `T` into the stage of `planeDiagram F`
at `T`. -/
def stageι (T : (Finset F)ᵒᵖ) : (diagram F).obj T ⟶ (planeDiagram F).obj T :=
  (stageOpen F T).ι

/-- The open immersions `stageι F` form a natural transformation from `diagram F` to
`planeDiagram F`. -/
theorem diagram_map_comp_stageι {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (diagram F).map f ≫ stageι F T' = stageι F T ≫ (planeDiagram F).map f :=
  Scheme.Hom.resLE_comp_ι _ _

/-- Every transition morphism of `planeDiagram F` is affine. -/
instance isAffineHom_planeDiagram_map {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    IsAffineHom ((planeDiagram F).map f) :=
  inferInstanceAs (IsAffineHom (specPlaneMap _))

/-- Every transition morphism of `diagram F` is affine. -/
instance isAffineHom_diagram_map {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    IsAffineHom ((diagram F).map f) :=
  isAffineHom_resLE_of_eq ((planeDiagram F).map f) (preimage_stageOpen F f)

/-- Every stage of `diagram F` is quasi-compact. -/
instance compactSpace_diagram_obj (T : (Finset F)ᵒᵖ) : CompactSpace ((diagram F).obj T) :=
  inferInstanceAs (CompactSpace (punctured (stage F T.unop)))

/-- Every stage of `diagram F` is quasi-separated. -/
instance quasiSeparatedSpace_diagram_obj (T : (Finset F)ᵒᵖ) :
    QuasiSeparatedSpace ((diagram F).obj T) :=
  inferInstanceAs (QuasiSeparatedSpace (punctured (stage F T.unop)))

/-- **No stage of the system is affine.** -/
theorem not_isAffine_diagram_obj (T : (Finset F)ᵒᵖ) : ¬ IsAffine ((diagram F).obj T) :=
  not_isAffine_punctured (stage F T.unop)

section Limit

/-- The structure morphism from the stage of `planeDiagram F` at `T`, the affine plane over
`stage F T`, to the stage of `schemeDiagram F` at `T`, the spectrum of `stage F T`. -/
def baseMap (T : (Finset F)ᵒᵖ) : (planeDiagram F).obj T ⟶ (schemeDiagram F).obj T :=
  specPlaneBase (stage F T.unop)

/-- The morphisms `baseMap F` form a natural transformation from `planeDiagram F` to
`schemeDiagram F`. -/
theorem planeDiagram_map_comp_baseMap {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (planeDiagram F).map f ≫ baseMap F T' = baseMap F T ≫ (schemeDiagram F).map f :=
  specPlaneMap_comp_specPlaneBase _

/-- The morphism from the stage of `diagram F` at `T` to the stage of `schemeDiagram F` at `T`:
the open immersion `stageι F T` followed by `baseMap F T`. -/
def legMap (T : (Finset F)ᵒᵖ) : (diagram F).obj T ⟶ (schemeDiagram F).obj T :=
  stageι F T ≫ baseMap F T

/-- The morphisms `legMap F` form a natural transformation from `diagram F` to
`schemeDiagram F`. -/
theorem legMap_naturality {T T' : (Finset F)ᵒᵖ} (f : T ⟶ T') :
    (diagram F).map f ≫ legMap F T' = legMap F T ≫ (schemeDiagram F).map f := by
  rw [legMap, legMap, ← Category.assoc, diagram_map_comp_stageι, Category.assoc,
    planeDiagram_map_comp_baseMap, ← Category.assoc]

/-- The cone over `schemeDiagram F` obtained from a cone over `diagram F` by composing its legs
with `legMap F`. -/
def toSchemeDiagramCone (s : Cone (diagram F)) : Cone (schemeDiagram F) where
  pt := s.pt
  π :=
    { app := fun T => s.π.app T ≫ legMap F T
      naturality := fun T T' f => by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.id_comp, ← s.w f, Category.assoc, legMap_naturality, Category.assoc] }

/-- **The limit of the system of punctured planes is the empty scheme**: if the field `F` is not
`u`-small, every cone over `diagram F` has an empty vertex. -/
theorem isEmpty_cone_pt (hF : ¬ Small.{u} F) (s : Cone (diagram F)) : IsEmpty s.pt :=
  Stacks.EmptyLimitCounterexample.isEmpty_cone_pt F hF (toSchemeDiagramCone F s)

end Limit

/-- The cone over the system with the empty scheme as vertex. -/
def emptyCone : Cone (diagram F) where
  pt := ∅
  π :=
    { app := fun _ => emptyIsInitial.to _
      naturality := fun _ _ _ => emptyIsInitial.hom_ext _ _ }

/-- The vertex of `emptyCone F` is the empty scheme. -/
@[simp] theorem emptyCone_pt : (emptyCone F).pt = ∅ := rfl

/-- **The empty cone is a limit cone** if the field `F` is not `u`-small. -/
def isLimitEmptyCone (hF : ¬ Small.{u} F) : IsLimit (emptyCone F) where
  lift s := by
    have := isEmpty_cone_pt F hF s
    exact isInitialOfIsEmpty.to _
  fac s j := by
    have := isEmpty_cone_pt F hF s
    exact (isInitialOfIsEmpty (X := s.pt)).hom_ext _ _
  uniq s m _ := by
    have := isEmpty_cone_pt F hF s
    exact (isInitialOfIsEmpty (X := s.pt)).hom_ext _ _

end Stacks.Refute09ZM

end

end
