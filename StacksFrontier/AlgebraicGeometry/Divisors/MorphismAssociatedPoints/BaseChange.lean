module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.Flat
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassin.TensorPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# The relative assassin under arbitrary base change

Let `f : X ⟶ S` be locally of finite type, let `g : S' ⟶ S` be arbitrary, and let `F` be a
quasi-coherent `𝒪_X`-module. A point `x'` of `X' = X ×_S S'` belongs to the relative assassin of
the pullback of `F` to `X'` exactly when its image `x` in `X` belongs to the relative assassin of
`F` and the point of `Spec (κ(x) ⊗_{κ(s)} κ(s'))` that `x'` determines is the generic point of an
irreducible component.

## Main results

* `AlgebraicGeometry.mem_relativeAssassin_pullback_iff` characterizes the relative assassin after
  arbitrary base change.

## Implementation notes

The proof reduces the statement to the fibres over the image `s'` of `x'` in `S'`. The fibre of
`pullback.snd f g` over `s'` maps to the fibre of `f` over `g s'`, and that map is flat, being a
base change of `Spec (κ(s') ⊗ -)` along a field extension. Bourbaki's lemma on the associated
points of a flat tensor product (Stacks 05DB,
`AlgebraicGeometry.associatedPoints_tensor_pullback_eq_relativeAssassin`)
applied to that map and to the structure sheaf of the fibre expresses the
associated points of the restriction of `F` to the fibre over `s'` as a union over the associated
points of the restriction of `F` to the fibre over `g s'`.

The remaining ingredient identifies the fibre of that map over a point `y` with
`Spec (κ(y) ⊗_{κ(g s')} κ(s'))` and the associated points of the structure sheaf of a Noetherian
Cohen-Macaulay affine scheme with the generic points of its irreducible components; the tensor
product of residue fields is Cohen-Macaulay because `f` is locally of finite type.

For `x' : X ×_S S'`, `Scheme.Pullback.Triplet.ofPoint x'` packages its images `x`, `s'` and `s`.
Its `tensor` is canonically `κ(x) ⊗[κ(s)] κ(s')`, and `Scheme.Pullback.SpecOfPoint x'` is the
point corresponding to `x'` under the fibre-product point classification.

## References

* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
-/

@[expose] public section

open CategoryTheory Limits RingedSpaceModuleAdjunction TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Fibres of a base-changed morphism -/

/-- The canonical morphism from a fibre of the base-changed morphism `pullback.snd f g` to the
corresponding fibre of `f`. -/
private noncomputable def fiberBaseChangeFiberMap {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (s' : S') : (pullback.snd f g).fiber s' ⟶ f.fiber (g s') :=
  pullback.map _ _ _ _ (pullback.fst f g)
    (Spec.map (g.residueFieldMap s')) g (by simp [pullback.condition]) (by simp)

/-- `AlgebraicGeometry.fiberPullbackIso` is compatible with `fiberBaseChangeFiberMap`. -/
private lemma fiberPullbackIso_hom_fst {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') :
    (fiberPullbackIso f g s').hom ≫
        pullback.fst (f.fiberToSpecResidueField (g s'))
          (Spec.map (g.residueFieldMap s')) = fiberBaseChangeFiberMap f g s' :=
  (isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) s').isoPullback_hom_fst

/-- The morphism between fibres is compatible with the fibre inclusions and the first
projection. -/
private lemma fiberBaseChangeFiberMap_fiberι {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') :
    fiberBaseChangeFiberMap f g s' ≫ f.fiberι (g s') =
      (pullback.snd f g).fiberι s' ≫ pullback.fst f g := by
  unfold fiberBaseChangeFiberMap Scheme.Hom.fiberι
  exact pullback.lift_fst _ _ _

/-- A point of a fibre of `pullback.snd f g` and its image in the fibre of `f` have the same image
in `X`. -/
private lemma apply_fiberι_fiberBaseChangeFiberMap {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (z : (pullback.snd f g).fiber s') :
    f.fiberι (g s') (fiberBaseChangeFiberMap f g s' z) =
      pullback.fst f g ((pullback.snd f g).fiberι s' z) :=
  congrArg (fun k : _ ⟶ X ↦ k z) (fiberBaseChangeFiberMap_fiberι f g s')

/-- The morphism between fibres is flat: it is a base change of a field extension. -/
private theorem fiberBaseChangeFiberMap_flat {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') :
    Flat (fiberBaseChangeFiberMap f g s') := by
  let q := Spec.map (g.residueFieldMap s')
  have hq : Flat q := by
    apply Flat.SpecMap_iff.mpr
    let : Algebra (S.residueField (g s')) (S'.residueField s') :=
      (g.residueFieldMap s').hom.toAlgebra
    show Module.Flat (S.residueField (g s')) (S'.residueField s')
    infer_instance
  have hp : Flat (pullback.fst (f.fiberToSpecResidueField (g s')) q) := by
    have : MorphismProperty.IsStableUnderBaseChangeAlong
        (P := @Flat) (f.fiberToSpecResidueField (g s')) :=
      ⟨fun pb h => Flat.isStableUnderBaseChange.of_isPullback pb h⟩
    exact MorphismProperty.pullback_fst (f.fiberToSpecResidueField (g s')) q hq
  rw [← fiberPullbackIso_hom_fst f g s']
  infer_instance

/-- Restricting a module to a fibre of the base-changed morphism agrees with restricting its
pullback to the corresponding fibre of the original morphism. -/
private noncomputable def fiberModuleComparisonIso {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (F : X.Modules) :
    ((Scheme.Modules.pullback ((pullback.snd f g).fiberι s')).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ≅
      ((Scheme.Modules.pullback (fiberBaseChangeFiberMap f g s')).obj
        ((Scheme.Modules.pullback (f.fiberι (g s'))).obj F)) :=
  (Scheme.Modules.pullbackComp ((pullback.snd f g).fiberι s')
      (pullback.fst f g)).app F ≪≫
    eqToIso (by rw [fiberBaseChangeFiberMap_fiberι]) ≪≫
      ((Scheme.Modules.pullbackComp (fiberBaseChangeFiberMap f g s')
        (f.fiberι (g s'))).app F).symm

/-! ### Residue fields at points of a fibre -/

/-- The inclusion of a fibre induces an isomorphism on residue fields at every point of the
fibre. -/
private lemma fiberι_residueFieldMap_isIso {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) : IsIso ((f.fiberι s).residueFieldMap y) := by
  let g := S.fromSpecResidueField s
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint y
  let q := Scheme.Pullback.SpecOfPoint y
  have hβ : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := by
    let : IsIso (g.residueFieldMap T.y) :=
      isIso_residueFieldMap_fromSpecResidueField S s T.y
    infer_instance
  have : IsIso T.tensorInl := by
    show IsIso (pushout.inl _ _)
    exact CategoryTheory.Limits.pushout_inl_iso_of_right_iso _ _
  have hT : IsIso (T.SpecTensorTo.residueFieldMap q) := by
    have h := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T q
    exact IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor q).hom
  have hcomp : IsIso ((T.SpecTensorTo ≫ pullback.fst f g).residueFieldMap q) := by
    rw [T.specTensorTo_fst, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (isIso_residueFieldMap_fromSpecResidueField X T.x _) inferInstance
  rw [Scheme.residueFieldMap_comp] at hcomp
  have hIso : IsIso ((pullback.fst f g).residueFieldMap (T.SpecTensorTo q)) := by
    have : IsIso ((pullback.fst f g).residueFieldMap (T.SpecTensorTo q) ≫
        T.SpecTensorTo.residueFieldMap q) := hcomp
    exact IsIso.of_isIso_comp_right
      (g := (pullback.fst f g).residueFieldMap (T.SpecTensorTo q))
      (f := T.SpecTensorTo.residueFieldMap q)
  rw [← Scheme.Pullback.SpecTensorTo_SpecOfPoint y]
  simpa [Scheme.Hom.fiberι, Scheme.Hom.fiber, g, T, q] using hIso

/-! ### Associated primes and associated points -/

/-- Being an associated prime in the exact-annihilator sense is invariant under a linear
equivalence: a linear equivalence preserves the annihilator of an element. -/
private alias isAssociatedPrimeStacks_congr_linearEquiv :=
    Stacks.Divisors.isAssociatedPrimeStacks_of_linearEquiv_iff

/-- Tensoring with the structure sheaf, regarded as a module over itself, does nothing. -/
private noncomputable def tensorSheafUnitIso (X : RingedSpace.{u, u})
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj
        ((SheafOfModules.unit (structureSheafRing X)))).obj (G)) ≅ G := by
  change (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X).obj
      ((PresheafOfModules.tensorObj (O := (X).presheaf) ((SheafOfModules.unit (structureSheafRing
          X)).val) (G.val))) ≅ G
  -- `PresheafOfModules.monoidalCategory` is keyed on `𝒪 ⋙ forget₂ CommRingCat RingCat`, and
  -- `(structureSheafRing X).obj` is a projection; `structureSheafRing` is
  -- `@[instance_reducible]` rather than `@[reducible]`, so the goal is not keyed to that
  -- instance and search does not retrieve it. The two presheaves of rings are equal by `rfl`.
  letI : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
    inferInstanceAs (MonoidalCategory
      (PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
  let e : PresheafOfModules.tensorObj (O := X.presheaf)
      (SheafOfModules.unit (structureSheafRing X)).val G.val ≅ G.val :=
    MonoidalCategoryStruct.leftUnitor G.val
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)
  haveI : IsIso adj.counit := by
    dsimp [adj]
    infer_instance
  exact (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyFunctor X).mapIso e ≪≫
    (asIso adj.counit).app G

/-! ### The tensor comparison at a point of a fibre -/

/-- The triplet of points of `X`, `S'` and `S` determined by a point `y` of the fibre of `f` over
`g s'`, together with `s'`. -/
private noncomputable abbrev fiberTriplet {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (s' : S') (y : f.fiber (g s')) : Scheme.Pullback.Triplet f g :=
  ⟨f.fiberι (g s') y, s', g s', f.apply_fiberι (g s') y, rfl⟩

/-- The structural morphism of the fibre of `f` over `g s'`, read on the residue field of a point
`y` of that fibre, factors through the residue field of the image of `y` in `X`. -/
private lemma fromSpecResidueField_fiberToSpecResidueField {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (y : f.fiber (g s')) :
    (f.fiber (g s')).fromSpecResidueField y ≫ f.fiberToSpecResidueField (g s') =
      Spec.map ((f.fiberι (g s')).residueFieldMap y) ≫
        Spec.map ((S.residueFieldCongr (fiberTriplet f g s' y).hx).inv ≫
          f.residueFieldMap (fiberTriplet f g s' y).x) := by
  have ha : Spec.map ((S.residueFieldCongr (fiberTriplet f g s' y).hx).inv ≫
        f.residueFieldMap (fiberTriplet f g s' y).x) ≫ S.fromSpecResidueField (g s') =
      X.fromSpecResidueField (f.fiberι (g s') y) ≫ f := by
    simp only [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_inv]
    rw [Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  apply (cancel_mono (S.fromSpecResidueField (g s'))).mp
  simp only [Category.assoc]
  rw [ha, ← Scheme.Hom.fiber_fac]
  simpa only [Category.assoc] using
    congrArg (fun k : Spec ((f.fiber (g s')).residueField y) ⟶ X ↦ k ≫ f)
      ((f.fiberι (g s')).SpecMap_residueFieldMap_fromSpecResidueField y).symm

/-- The fibre of `fiberBaseChangeFiberMap f g s'` over `y` sits in the pullback square whose
corners are the residue fields of `y`, of `s'` and of `g s'`. -/
private lemma isPullback_pointFiber {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (s' : S')
    (y : f.fiber (g s')) :
    IsPullback
      ((fiberBaseChangeFiberMap f g s').fiberToSpecResidueField y ≫
        Spec.map ((f.fiberι (g s')).residueFieldMap y))
      ((fiberBaseChangeFiberMap f g s').fiberι y ≫
        (pullback.snd f g).fiberToSpecResidueField s')
      (Spec.map ((S.residueFieldCongr (fiberTriplet f g s' y).hx).inv ≫
        f.residueFieldMap (fiberTriplet f g s' y).x))
      (Spec.map (g.residueFieldMap s')) := by
  have : IsIso ((f.fiberι (g s')).residueFieldMap y) :=
    fiberι_residueFieldMap_isIso f (g s') y
  have hinner := (IsPullback.of_hasPullback (fiberBaseChangeFiberMap f g s')
      ((f.fiber (g s')).fromSpecResidueField y)).flip.paste_vert
    (isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) s')
  have hright : IsPullback (Spec.map ((f.fiberι (g s')).residueFieldMap y))
      ((f.fiber (g s')).fromSpecResidueField y ≫ f.fiberToSpecResidueField (g s'))
      (Spec.map ((S.residueFieldCongr (fiberTriplet f g s' y).hx).inv ≫
        f.residueFieldMap (fiberTriplet f g s' y).x))
      (𝟙 (Spec (S.residueField (g s')))) :=
    IsPullback.of_horiz_isIso
      ⟨by simpa using (fromSpecResidueField_fiberToSpecResidueField f g s' y).symm⟩
  have hpaste := hinner.paste_horiz hright
  rwa [Category.comp_id] at hpaste

/-- The defining pullback square of the residue-field tensor product attached to `y`, with its
right-hand leg in the spelling `isPullback_pointFiber` uses. -/
private lemma isPullback_specMap_tensor_fiberTriplet {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (y : f.fiber (g s')) :
    IsPullback (Spec.map (fiberTriplet f g s' y).tensorInl)
      (Spec.map (fiberTriplet f g s' y).tensorInr)
      (Spec.map ((S.residueFieldCongr (fiberTriplet f g s' y).hx).inv ≫
        f.residueFieldMap (fiberTriplet f g s' y).x))
      (Spec.map (g.residueFieldMap s')) := by
  have h := (fiberTriplet f g s' y).isPullback_SpecMap_tensor
  rwa [show Spec.map ((S.residueFieldCongr (fiberTriplet f g s' y).hy).inv ≫
      g.residueFieldMap (fiberTriplet f g s' y).y) = Spec.map (g.residueFieldMap s') by
    simp] at h

/-- The fibre of `fiberBaseChangeFiberMap f g s'` over `y` is the spectrum of the tensor product
of residue fields attached to the corresponding triplet. -/
private noncomputable def pointFiberTensorIso {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (s' : S') (y : f.fiber (g s')) :
    (fiberBaseChangeFiberMap f g s').fiber y ≅ Spec (fiberTriplet f g s' y).tensor :=
  (isPullback_pointFiber f g s' y).isoIsPullback _ _
    (isPullback_specMap_tensor_fiberTriplet f g s' y)

/-- The comparison isomorphism is compatible with the first inclusion into the tensor
product. -/
private lemma pointFiberTensorIso_hom_inl {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (y : f.fiber (g s')) :
    (pointFiberTensorIso f g s' y).hom ≫ Spec.map (fiberTriplet f g s' y).tensorInl =
      (fiberBaseChangeFiberMap f g s').fiberToSpecResidueField y ≫
        Spec.map ((f.fiberι (g s')).residueFieldMap y) :=
  (isPullback_pointFiber f g s' y).isoIsPullback_hom_fst _ _
    (isPullback_specMap_tensor_fiberTriplet f g s' y)

/-- The comparison isomorphism is compatible with the second inclusion into the tensor
product. -/
private lemma pointFiberTensorIso_hom_inr {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (y : f.fiber (g s')) :
    (pointFiberTensorIso f g s' y).hom ≫ Spec.map (fiberTriplet f g s' y).tensorInr =
      (fiberBaseChangeFiberMap f g s').fiberι y ≫
        (pullback.snd f g).fiberToSpecResidueField s' :=
  (isPullback_pointFiber f g s' y).isoIsPullback_hom_snd _ _
    (isPullback_specMap_tensor_fiberTriplet f g s' y)

/-- The comparison isomorphism is compatible with the canonical morphism from the spectrum of the
tensor product into the fibre product. -/
private lemma pointFiberTensorIso_hom_SpecTensorTo {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') (y : f.fiber (g s')) :
    (pointFiberTensorIso f g s' y).hom ≫ (fiberTriplet f g s' y).SpecTensorTo =
      (fiberBaseChangeFiberMap f g s').fiberι y ≫ (pullback.snd f g).fiberι s' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Scheme.Pullback.Triplet.specTensorTo_fst,
      ← Category.assoc, pointFiberTensorIso_hom_inl]
    simp only [Category.assoc]
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Scheme.Hom.fiber_fac, Category.assoc, fiberBaseChangeFiberMap_fiberι]
  · rw [Category.assoc, Scheme.Pullback.Triplet.specTensorTo_snd,
      ← Category.assoc, pointFiberTensorIso_hom_inr]
    simp only [Category.assoc]
    rw [← Scheme.Hom.fiber_fac]

/-! ### Associated points of a Cohen-Macaulay affine scheme -/

/-- A point is associated to a scheme exactly when the maximal ideal of its local ring is an
associated prime of that local ring. -/
private lemma schemeAssociatedPoints_iff_stalk (X : Scheme.{u}) (x : X) :
    x ∈ Stacks.Divisors.schemeAssociatedPoints X ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk x) (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
  isAssociatedPrimeStacks_congr_linearEquiv (structureSheafStalkLinearEquiv X x) _

/-- The maximal ideal of a local ring being an associated prime of the ring itself transports
along a ring isomorphism. -/
private lemma isAssociatedPrimeStacks_maximalIdeal_of_ringEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (h : IsAssociatedPrimeStacks A A (IsLocalRing.maximalIdeal A)) :
    IsAssociatedPrimeStacks B B (IsLocalRing.maximalIdeal B) := by
  obtain ⟨hp, m, hm⟩ := h
  refine ⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime, e m, ?_⟩
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot]
  show e a * e m = 0 ↔ _
  rw [← map_mul, map_eq_zero_iff e e.injective]
  have h : a * m = 0 ↔ a ∈ IsLocalRing.maximalIdeal A := by
    rw [← hm, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    rfl
  rw [h, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  exact not_congr ⟨fun h ↦ h.map e.toMonoidHom,
    fun h ↦ by simpa using h.map e.symm.toMonoidHom⟩

/-- The two directions of the previous transport. -/
private lemma isAssociatedPrimeStacks_maximalIdeal_ringEquiv {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    IsAssociatedPrimeStacks R R (IsLocalRing.maximalIdeal R) ↔
      IsAssociatedPrimeStacks S S (IsLocalRing.maximalIdeal S) :=
  ⟨isAssociatedPrimeStacks_maximalIdeal_of_ringEquiv e,
    isAssociatedPrimeStacks_maximalIdeal_of_ringEquiv e.symm⟩

/-- The associated points of a scheme are preserved by an isomorphism of schemes. -/
private lemma schemeAssociatedPoints_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    x ∈ Stacks.Divisors.schemeAssociatedPoints X ↔
      e.hom x ∈ Stacks.Divisors.schemeAssociatedPoints Y := by
  rw [schemeAssociatedPoints_iff_stalk, schemeAssociatedPoints_iff_stalk]
  exact (isAssociatedPrimeStacks_maximalIdeal_ringEquiv
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv (asIso (e.hom.stalkMap x)))).symm

/-- For a Noetherian ring, the associated points of its spectrum are its associated primes. -/
private lemma schemeAssociatedPoints_spec (R : CommRingCat.{u}) [IsNoetherianRing R]
    (p : Spec R) : p ∈ Stacks.Divisors.schemeAssociatedPoints (Spec R) ↔
      p.asIdeal ∈ associatedPrimes R R := by
  have : p.asIdeal.IsPrime := p.isPrime
  rw [schemeAssociatedPoints_iff_stalk,
    isAssociatedPrimeStacks_maximalIdeal_ringEquiv
      (CategoryTheory.Iso.commRingCatIsoToRingEquiv (Spec.stalkIso R p)),
    isAssociatedPrimeStacks_iff_mem_associatedPrimes]
  rw [←
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal))]
  show (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).comap
    (algebraMap R (Localization.AtPrime p.asIdeal)) ∈ associatedPrimes R R ↔ _
  have hp : (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).comap
      (algebraMap R (Localization.AtPrime p.asIdeal)) = p.asIdeal := by
    ext r
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime p.asIdeal) p.asIdeal r
  rw [hp]

/-- Over a Noetherian Cohen-Macaulay ring the associated primes of the ring are exactly its
minimal primes. -/
private lemma associatedPrimes_eq_minimal_of_cohenMacaulay {R : Type*} [CommRing R]
    [IsNoetherianRing R] (hCM : Module.IsCohenMacaulay R R) (p : PrimeSpectrum R) :
    p.asIdeal ∈ associatedPrimes R R ↔ p.asIdeal ∈ minimalPrimes R := by
  have hmin : ∀ q ∈ associatedPrimes R R, Minimal (· ∈ associatedPrimes R R) q :=
    Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth.mpr
      (fun q ↦ by rw [hCM q (by simp [Module.support_self])]; exact min_le_right _ _)
  have hp := Set.ext_iff.mp
    (Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes (R := R) (M := R)) p
  simp only [Set.mem_ofPred_eq, Module.support_self] at hp
  rw [← PrimeSpectrum.isMin_iff]
  exact ⟨fun ha q hqp ↦ (hp.mpr ⟨ha, fun q hq hqp ↦ (hmin _ ha).2 hq hqp⟩).2 (Set.mem_univ _) hqp,
    fun hm ↦ (hp.mp ⟨Set.mem_univ _, fun q _ hqp ↦ hm hqp⟩).1⟩

/-- A prime of a commutative ring is the generic point of an irreducible component of its prime
spectrum exactly when it is minimal. -/
private lemma generic_primeSpectrum_iff_minimal {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) :
    (∃ Z ∈ irreducibleComponents (PrimeSpectrum R), IsGenericPoint p Z) ↔
      p.asIdeal ∈ minimalPrimes R := by
  have h : (∃ Z ∈ irreducibleComponents (PrimeSpectrum R), IsGenericPoint p Z) ↔
      closure {p} ∈ irreducibleComponents (PrimeSpectrum R) :=
    ⟨fun ⟨_, hZ, h⟩ ↦ h.symm ▸ hZ, fun h ↦ ⟨_, h, rfl⟩⟩
  rw [h, PrimeSpectrum.closure_singleton,
    PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, p.isPrime.isRadical.radical]

/-- The spectrum of a nontrivial commutative ring has a point which is the generic point of an
irreducible component, namely any minimal prime. -/
lemma exists_isGenericPoint_mem_irreducibleComponents (R : Type u) [CommRing R] [Nontrivial R] :
    ∃ p : PrimeSpectrum R, ∃ Z ∈ irreducibleComponents (PrimeSpectrum R), IsGenericPoint p Z := by
  obtain ⟨I, hI⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
  exact ⟨⟨I, hI.1.1⟩, (generic_primeSpectrum_iff_minimal _).2 hI⟩

/-- A point of an affine scheme is the generic point of an irreducible component exactly when the
corresponding prime is minimal. -/
private lemma generic_spec_iff_minimal (R : CommRingCat.{u}) (p : Spec R) :
    (∃ Z ∈ irreducibleComponents (Spec R), IsGenericPoint p Z) ↔
      p.asIdeal ∈ minimalPrimes R :=
  generic_primeSpectrum_iff_minimal (R := R) p

/-- Generic points of irreducible components are carried to generic points of irreducible
components by a homeomorphism. -/
private lemma generic_image_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (x : A)
    (h : ∃ Z ∈ irreducibleComponents A, IsGenericPoint x Z) :
    ∃ Z ∈ irreducibleComponents B, IsGenericPoint (e x) Z := by
  obtain ⟨Z, hZ, hx⟩ := h
  refine ⟨e '' Z, image_mem_irreducibleComponents_of_isPreirreducible_fiber e
    e.continuous e.isOpenMap (fun b ↦
      (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective hZ, ?_⟩
  show closure {e x} = e '' Z
  rw [← Set.image_singleton, ← e.image_closure, hx]

/-- Being the generic point of an irreducible component is invariant under a homeomorphism. -/
private lemma generic_homeomorph_iff {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (x : A) :
    (∃ Z ∈ irreducibleComponents A, IsGenericPoint x Z) ↔
      ∃ Z ∈ irreducibleComponents B, IsGenericPoint (e x) Z := by
  refine ⟨generic_image_homeomorph e x, fun h ↦ ?_⟩
  simpa using generic_image_homeomorph e.symm (e x) h

/-- A point of the spectrum of a tensor product of residue fields along a morphism locally of
finite type is associated exactly when it is the generic point of an irreducible component: the
tensor product is Noetherian and Cohen-Macaulay. -/
private lemma tensor_spec_associated_iff_generic {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    p ∈ Stacks.Divisors.schemeAssociatedPoints (Spec T.tensor) ↔
      ∃ Z ∈ irreducibleComponents (Spec T.tensor), IsGenericPoint p Z := by
  obtain ⟨x, y, s, rfl, hy⟩ := T
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (S.residueField (f x)) (S'.residueField y) :=
    ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap y).hom.toAlgebra
  have hCM := Algebra.TensorProduct.isNoetherianRing_and_isCohenMacaulay_of_essFiniteType
    (S.residueField (f x)) (X.residueField x) (S'.residueField y)
    (Or.inl (residueField_essFiniteType_of_locallyOfFiniteType f x))
  let R := CommRingCat.of (TensorProduct (S.residueField (f x))
    (X.residueField x) (S'.residueField y))
  have : IsNoetherianRing R := hCM.1
  let eR : R ≅ (Scheme.Pullback.Triplet.mk x y (f x) rfl hy).tensor := by
    simpa only [Scheme.Pullback.Triplet.tensor, Scheme.residueFieldCongr_refl,
      Iso.refl_inv, Category.id_comp, RingHom.algebraMap_toAlgebra,
      CommRingCat.ofHom_hom] using
      (CommRingCat.isPushout_tensorProduct (S.residueField (f x))
        (X.residueField x) (S'.residueField y)).isoPushout
  let e := Scheme.Spec.mapIso eR.op
  exact (schemeAssociatedPoints_iso e p).trans
    (((schemeAssociatedPoints_spec R (e.hom p)).trans
      ((associatedPrimes_eq_minimal_of_cohenMacaulay hCM.2 (e.hom p)).trans
        (generic_spec_iff_minimal R (e.hom p)).symm)).trans
          (generic_homeomorph_iff (Scheme.homeoOfIso e) p).symm)

/-! ### The main result -/

/-- The canonical morphism from the spectrum of the tensor product of residue fields into the
fibre product is injective on points. -/
private lemma specTensorTo_injective {X S S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} (T : Scheme.Pullback.Triplet f g) :
    Function.Injective T.SpecTensorTo := by
  intro a b h
  have h' : (⟨T, a⟩ : Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) = ⟨T, b⟩ :=
    (Scheme.Pullback.carrierEquiv (f := f) (g := g)).symm.injective h
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h'

/-- A point of the fibre of `fiberBaseChangeFiberMap f g s'` over `y` is associated to the
structure sheaf of the fibre over `s'` exactly when the corresponding point of the residue-field
tensor product is the generic point of an irreducible component. -/
private lemma associated_pointFiber_iff_generic {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (s' : S') (y : f.fiber (g s')) (w : (fiberBaseChangeFiberMap f g s').fiber y)
    (x' : pullback (C := Scheme.{u}) f g)
    (hw : (pullback.snd f g).fiberι s' ((fiberBaseChangeFiberMap f g s').fiberι y w) = x') :
    w ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback ((fiberBaseChangeFiberMap f g s').fiberι y)).obj
          (structureSheafModule ((pullback.snd f g).fiber s'))) ↔
      ∃ Z ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor),
        IsGenericPoint (Scheme.Pullback.SpecOfPoint x') Z := by
  let T := fiberTriplet f g s' y
  have hT : T = Scheme.Pullback.Triplet.ofPoint x' := by
    apply Scheme.Pullback.Triplet.ext
    · show f.fiberι (g s') y = pullback.fst f g x'
      rw [← hw, ← apply_fiberι_fiberBaseChangeFiberMap, Scheme.Hom.apply_fiberι]
    · show s' = pullback.snd f g x'
      rw [← hw, Scheme.Hom.apply_fiberι]
  let eT : Spec T.tensor ≅ Spec (Scheme.Pullback.Triplet.ofPoint x').tensor :=
    Scheme.Spec.mapIso (Scheme.Pullback.Triplet.tensorCongr hT).symm.op
  let e := pointFiberTensorIso f g s' y ≪≫ eT
  have he : e.hom w = Scheme.Pullback.SpecOfPoint x' := by
    apply specTensorTo_injective (Scheme.Pullback.Triplet.ofPoint x')
    rw [Scheme.Pullback.SpecTensorTo_SpecOfPoint]
    have hcomp : e.hom ≫ (Scheme.Pullback.Triplet.ofPoint x').SpecTensorTo =
        (fiberBaseChangeFiberMap f g s').fiberι y ≫ (pullback.snd f g).fiberι s' := by
      dsimp only [e, eT, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_inv]
      show (pointFiberTensorIso f g s' y).hom ≫
        Spec.map (Scheme.Pullback.Triplet.tensorCongr hT).inv ≫
          (Scheme.Pullback.Triplet.ofPoint x').SpecTensorTo = _
      rw [Scheme.Pullback.Triplet.tensorCongr_inv,
        Scheme.Pullback.tensorCongr_SpecTensorTo, pointFiberTensorIso_hom_SpecTensorTo]
    exact (congrArg (fun k : _ ⟶ pullback (C := Scheme.{u}) f g ↦ k w) hcomp).trans hw
  have hunit := associatedPoints_eq_of_moduleIso
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso ((fiberBaseChangeFiberMap f g s').fiberι y))
  simp only [Scheme.unitModule] at hunit
  rw [hunit]
  exact (schemeAssociatedPoints_iso e w).trans
    ((tensor_spec_associated_iff_generic f g _ (e.hom w)).trans (by rw [he]))

/-- **Stacks Project, Tag 05DC.** Under arbitrary base change, a point is in
the relative assassin of the pulled-back quasi-coherent module exactly when
its image is in the original relative assassin and its residue-field tensor
product point is generic in an irreducible component. -/
@[stacks 05DC]
theorem mem_relativeAssassin_pullback_iff
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [LocallyOfFiniteType f]
    (x' : pullback (C := Scheme.{u}) f g) :
    x' ∈ Stacks.Divisors.relativeAssassin (pullback.snd (C := Scheme.{u}) f g)
        ((Scheme.Modules.pullback (pullback.fst (C := Scheme.{u}) f g)).obj F) ↔
      (pullback.fst (C := Scheme.{u}) f g x' ∈ Stacks.Divisors.relativeAssassin f F ∧
        ∃ Z ∈ irreducibleComponents
            (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor),
          IsGenericPoint (Scheme.Pullback.SpecOfPoint x') Z) := by
  let s' : S' := pullback.snd (C := Scheme.{u}) f g x'
  let p := fiberBaseChangeFiberMap f g s'
  let source := (pullback.snd (C := Scheme.{u}) f g).fiber s'
  let target := f.fiber (g s')
  let G := (Scheme.Modules.pullback (f.fiberι (g s'))).obj F
  let Fbase := (Scheme.Modules.pullback (pullback.fst (C := Scheme.{u}) f g)).obj F
  let Funit := structureSheafModule source
  have : IsLocallyNoetherian target := isLocallyNoetherian_fiber_of_locallyOfFiniteType f (g s')
  have hFqc : F.IsQuasicoherent := inferInstance
  have : G.IsQuasicoherent := by
    show ((modulePullback (f.fiberι (g s')).toLRSHom.toShHom).obj F).IsQuasicoherent
    exact @SheafOfModules.modulePullback_isQuasicoherent _ _
      (f.fiberι (g s')).toLRSHom.toShHom F hFqc
  have : Funit.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit source
  have : Flat p := fiberBaseChangeFiberMap_flat f g s'
  have hFlatUnit : IsFlatOver p.toLRSHom.toShHom Funit :=
    isFlatOver_structureSheafModule p
  have hBourbaki := associatedPoints_tensor_pullback_eq_relativeAssassin
    p Funit G hFlatUnit
  have hFiberAss : Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback ((pullback.snd (C := Scheme.{u}) f g).fiberι s')).obj Fbase) =
      Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback p).obj G) :=
    associatedPoints_eq_of_moduleIso (fiberModuleComparisonIso f g s' F)
  let z' := (pullback.snd (C := Scheme.{u}) f g).asFiber x'
  have hOuter : x' ∈ Stacks.Divisors.relativeAssassin (pullback.snd f g) Fbase ↔
      z' ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback
          ((pullback.snd (C := Scheme.{u}) f g).fiberι s')).obj Fbase) := by
    simpa only [z', s', Scheme.Hom.fiberι_asFiber] using
      (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
        (pullback.snd (C := Scheme.{u}) f g) Fbase s' z').symm
  let y₀ : target := p z'
  have hy₀ : f.fiberι (g s') y₀ = pullback.fst f g x' := by
    rw [apply_fiberι_fiberBaseChangeFiberMap]
    simp [z', s']
  let w₀ : p.fiber y₀ := (p.fiberHomeo y₀).symm ⟨z', rfl⟩
  have hw₀ : p.fiberι y₀ w₀ = z' := Scheme.Hom.fiberι_fiberHomeo_symm p y₀ ⟨z', rfl⟩
  have hx' : (pullback.snd f g).fiberι s' z' = x' :=
    Scheme.Hom.fiberι_asFiber (pullback.snd f g) x'
  have hUnion : Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback ((pullback.snd (C := Scheme.{u}) f g).fiberι s')).obj Fbase) =
      ⋃ y ∈ Stacks.Divisors.associatedPoints G,
        (p.fiberι y) '' Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback (p.fiberι y)).obj Funit) :=
    hFiberAss.trans ((associatedPoints_eq_of_moduleIso (tensorSheafUnitIso
      source.toLocallyRingedSpace.toRingedSpace ((Scheme.Modules.pullback p).obj G))).symm.trans
        hBourbaki)
  rw [hOuter, hUnion]
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨y, hy, w, hw, hzw⟩
    have hyy₀ : y = y₀ := (p.apply_fiberι y w).symm.trans (congrArg p hzw)
    subst y
    refine ⟨?_, (associated_pointFiber_iff_generic f g s' y₀ w x' (by rwa [hzw])).mp hw⟩
    rw [← hy₀]
    exact (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
      f F (g s') y₀).mp hy
  · rintro ⟨hxrel, hgeneric⟩
    refine ⟨y₀, ?_, w₀,
      (associated_pointFiber_iff_generic f g s' y₀ w₀ x' (by rwa [hw₀])).mpr hgeneric, hw₀⟩
    exact (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin
      f F (g s') y₀).mpr (by simpa only [hy₀] using hxrel)

end AlgebraicGeometry
