module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyIrreducible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingHypotheses
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.CoveringFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometrically connected fibres near the generic point

Let `f : X ⟶ Y` be a finite type morphism with irreducible target. Stacks Tag 055G says that
if the fibre over the generic point of `Y` is geometrically connected, then the restriction of
`f` over some nonempty open subscheme of `Y` has geometrically connected fibres.

The proof needs Stacks Tag 0559 — the same statement with "irreducible" in place of
"connected" — which is not yet available in the library, so the results below take its
conclusion as a hypothesis, packaged as
`AlgebraicGeometry.GeometricallyIrreducibleAfterShrinking`.

## Main results

* `AlgebraicGeometry.exists_open_geometricallyConnected_restrict` is Stacks Tag 055G granted
  that hypothesis.
* `AlgebraicGeometry.geometricallyConnected_iff_numGeometricConnectedComponents_eq_one`
  identifies the locus of geometrically connected fibres with the level set at `1` of the
  number of geometric connected components of the fibres.

## Implementation notes

The open subscheme is represented by `V : Y.Opens` and the base change of `f` to it by
Mathlib's morphism restriction `f ∣_ V`; geometric connectedness of all of its fibres is
`GeometricallyConnected (f ∣_ V)`, using the fibrewise characterization of that morphism
property. Being of finite type is `LocallyOfFiniteType` together with `QuasiCompact`.

The argument follows the source: Tag 0551 provides a finite etale surjective cover of a
nonempty open of the base over which the components of the generic fibre are geometrically
irreducible, and Tag 055F transports the count of geometric connected components along that
cover and along the reduction of the base. Over such a base one takes the closures `X i` in
`X` of the components of the generic fibre; Tag 054Y makes them cover every nearby fibre, the
hypothesis above keeps each of them irreducible fibrewise, and generic flatness (Tag 052B)
makes the nonempty pairwise intersections surject onto a neighbourhood of the generic point.
On that neighbourhood the incidence pattern of the components of each fibre is the one of the
generic fibre, which is connected, so each fibre is connected.

## References

* [Stacks Project, Tag 055G](https://stacks.math.columbia.edu/tag/055G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The canonical comparison map from the fibre of `f ∣_ V` at a point of `V` to the fibre of
`f` at its image in `Y`, induced by the pullback square presenting the restriction. -/
private noncomputable def fiberAfterRestrictMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (yV : V.toScheme) :
    (f ∣_ V).fiber yV ⟶ f.fiber (V.ι yV) :=
  pullback.map (f ∣_ V) (V.toScheme.fromSpecResidueField yV)
    f (Y.fromSpecResidueField (V.ι yV)) (f ⁻¹ᵁ V).ι
    (Spec.map (V.ι.residueFieldMap yV)) V.ι
    (by simp)
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField V.ι yV).symm

/-- The comparison map of `fiberAfterRestrictMap` sits in a pullback square over the
isomorphism of residue fields at a point of an open subscheme. -/
private theorem isPullback_fiberAfterRestrictMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (yV : V.toScheme) :
    IsPullback (fiberAfterRestrictMap f V yV)
      ((f ∣_ V).fiberToSpecResidueField yV)
      (f.fiberToSpecResidueField (V.ι yV))
      (Spec.map (V.ι.residueFieldMap yV)) :=
  isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f V).flip yV

/-- Taking the spectrum of the residue field isomorphism at a point of an open subscheme gives
an isomorphism of schemes. -/
private instance isIso_specMap_residueFieldMap_ι
    {Y : Scheme.{u}} (V : Y.Opens) (yV : V.toScheme) :
    IsIso (Spec.map (V.ι.residueFieldMap yV)) :=
  (Scheme.Spec.mapIso (asIso (V.ι.residueFieldMap yV)).op).isIso_hom

private instance isIso_fiberAfterRestrictMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (yV : V.toScheme) :
    IsIso (fiberAfterRestrictMap f V yV) :=
  (isPullback_fiberAfterRestrictMap f V yV).isIso_fst_of_isIso inferInstance

/-- The arrow presenting the fibre of `f ∣_ V` over a point of `V` is isomorphic to the arrow
presenting the fibre of `f` over its image in `Y`. -/
private noncomputable def fiberAfterRestrictArrowIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (yV : V.toScheme) :
    Arrow.mk ((f ∣_ V).fiberToSpecResidueField yV) ≅
      Arrow.mk (f.fiberToSpecResidueField (V.ι yV)) :=
  Arrow.isoMk (asIso (fiberAfterRestrictMap f V yV))
    (asIso (Spec.map (V.ι.residueFieldMap yV)))
    (isPullback_fiberAfterRestrictMap f V yV).w

/-- Geometric irreducibility of all fibres of a restriction `f ∣_ V` gives geometric
irreducibility of the fibre of `f` over each point of `V`. -/
private theorem geometricallyIrreducible_fiber_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (y : Y) (hy : y ∈ V)
    [GeometricallyIrreducible (f ∣_ V)] :
    GeometricallyIrreducible (f.fiberToSpecResidueField (V.ι ⟨y, hy⟩)) := by
  have hV : GeometricallyIrreducible ((f ∣_ V).fiberToSpecResidueField ⟨y, hy⟩) :=
    (GeometricallyIrreducible.iff_geometricallyIrreducible_fiber
      (f := f ∣_ V)).mp inferInstance ⟨y, hy⟩
  rw [GeometricallyIrreducible.eq_geometrically] at hV ⊢
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (fun T : Scheme.{u} => IrreducibleSpace T))
    (fiberAfterRestrictArrowIso f V ⟨y, hy⟩)).mp hV

/-- The fibre of a restriction `f ∣_ V` over a point of `V` is geometrically connected exactly
when the fibre of `f` over its image in `Y` is. -/
private theorem geometricallyConnected_fiber_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (y : Y) (hy : y ∈ V) :
    GeometricallyConnected ((f ∣_ V).fiberToSpecResidueField ⟨y, hy⟩) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (V.ι ⟨y, hy⟩)) := by
  rw [GeometricallyConnected.eq_geometrically]
  exact MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (fun T : Scheme.{u} => ConnectedSpace T))
    (fiberAfterRestrictArrowIso f V ⟨y, hy⟩)

/-- A scheme over a field is geometrically connected exactly when its base change to a separable
closure of the field is connected. -/
private theorem geometricallyConnected_iff_connectedSpace_pullback_separableClosure
    {X : Scheme.{u}} (k : Type u) [Field k] (g : X ⟶ Spec (.of k)) :
    GeometricallyConnected g ↔
      ConnectedSpace (pullback (C := Scheme) g
        (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))) := by
  have : IsSepClosed (SeparableClosure k) := IsSepClosure.sep_closed (k := k)
  rw [geometricallyConnected_iff_baseChange_fieldExtension k (SeparableClosure k) g,
    geometricallyConnected_iff_connectedSpace]

/-- **Stacks Project, Tag 055F.** A fibre is geometrically connected exactly when its number of
geometric connected components is one: both say that the base change of the fibre to a separable
closure of the residue field is connected. -/
@[ega "IV 4.5.2" "partial"]
theorem geometricallyConnected_iff_numGeometricConnectedComponents_eq_one
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    GeometricallyConnected (f.fiberToSpecResidueField y) ↔
      numGeometricConnectedComponents f y = 1 := by
  let k := Y.residueField y
  let g := f.fiberToSpecResidueField y
  let Z := pullback g (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))))
  have hcard : ENat.card (ConnectedComponents Z) = 1 ↔ ConnectedSpace Z := by
    rw [ENat.card_eq_one_iff_unique]
    constructor
    · rintro ⟨u⟩
      let : Unique (ConnectedComponents Z) := u
      have : Subsingleton (ConnectedComponents Z) := inferInstance
      have : Nonempty Z := (ConnectedComponents.nonempty_iff_nonempty).mp inferInstance
      have : PreconnectedSpace Z := by
        rw [preconnectedSpace_iff_connectedComponent]
        intro x
        apply Set.eq_univ_iff_forall.mpr
        intro z
        exact ConnectedComponents.coe_eq_coe'.mp
          (Subsingleton.elim (z : ConnectedComponents Z) x)
      exact ⟨inferInstance⟩
    · intro h
      let : ConnectedSpace Z := h
      let : PreconnectedSpace Z := inferInstance
      let : Subsingleton (ConnectedComponents Z) := inferInstance
      let : Nonempty (ConnectedComponents Z) := inferInstance
      let u : Unique (ConnectedComponents Z) :=
        ⟨⟨Classical.choice ‹Nonempty (ConnectedComponents Z)›⟩,
          fun a => Subsingleton.elim a _⟩
      exact ⟨u⟩
  exact (geometricallyConnected_iff_connectedSpace_pullback_separableClosure k g).trans hcard.symm

private theorem irreducibleSpace_subscheme_of_support_eq
    {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I.support = J.support) :
    IrreducibleSpace I.subscheme → IrreducibleSpace J.subscheme := by
  let e (K : X.IdealSheafData) : K.subscheme ≃ₜ ↑(K.support : Set X) := by
    refine (Homeomorph.Set.univ K.subscheme).symm.trans
      (K.subschemeι.isEmbedding.homeomorphImage Set.univ) |>.trans
      (Homeomorph.setCongr ?_)
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι]
  intro hI
  exact ((e I).trans
    ((Homeomorph.setCongr (congrArg (fun s : Closeds X => (s : Set X)) h)).trans
      (e J).symm)).irreducibleSpace_iff.mp hI

private theorem support_comap_eq_of_support_eq
    {X Y : Scheme.{u}} (I J : Y.IdealSheafData) (f : X ⟶ Y)
    (h : I.support = J.support) : (I.comap f).support = (J.comap f).support := by
  simp only [Scheme.IdealSheafData.support_comap, h]

private theorem geomIrred_subscheme_of_support_eq
    {X : Scheme.{u}} (k : Type u) [Field k] (p : X ⟶ Spec (.of k))
    (I J : X.IdealSheafData) (h : I.support = J.support)
    (hI : GeometricallyIrreducible (I.subschemeι ≫ p)) :
    GeometricallyIrreducible (J.subschemeι ≫ p) := by
  rw [GeometricallyIrreducible.eq_geometrically]
  refine (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun T : Scheme.{u} => IrreducibleSpace T) (f := J.subschemeι ≫ p)).2 ?_
  intro K _ q
  let iso (K : X.IdealSheafData) : (K.comap (pullback.fst (C := Scheme) p q)).subscheme ≅
      pullback (C := Scheme) (K.subschemeι ≫ p) q :=
    K.comapIso (pullback.fst (C := Scheme) p q) ≪≫
      pullbackSymmetry (pullback.fst (C := Scheme) p q) K.subschemeι ≪≫
      pullbackRightPullbackFstIso p q K.subschemeι
  have hIext : IrreducibleSpace (I.comap (pullback.fst (C := Scheme) p q)).subscheme :=
    (ObjectProperty.prop_of_iso (P := fun T : Scheme.{u} => IrreducibleSpace T) (iso I).symm)
      (hI.geometrically_irreducibleSpace q (pullback.fst (C := Scheme) _ _)
        (pullback.snd (C := Scheme) _ _) (IsPullback.of_hasPullback (C := Scheme) _ _))
  exact (ObjectProperty.prop_of_iso (P := fun T : Scheme.{u} => IrreducibleSpace T) (iso J))
    (irreducibleSpace_subscheme_of_support_eq _ _
      (support_comap_eq_of_support_eq I J (pullback.fst (C := Scheme) p q) h) hIext)

private theorem geomIrred_comap_map_of_isEmbedding
    {A B : Scheme.{u}} (i : A ⟶ B) [QuasiCompact i] (hi : Topology.IsEmbedding i)
    (I : A.IdealSheafData) (k : Type u) [Field k] (p : A ⟶ Spec (.of k))
    (hI : GeometricallyIrreducible (I.subschemeι ≫ p)) :
    GeometricallyIrreducible (((I.map i).comap i).subschemeι ≫ p) := by
  apply geomIrred_subscheme_of_support_eq k p I ((I.map i).comap i) ?_ hI
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_map]
  ext x
  show x ∈ (I.support : Set A) ↔ x ∈ i ⁻¹' closure (i '' (I.support : Set A))
  rw [← hi.isInducing.closure_eq_preimage_closure_image]
  simp [I.support.isClosed.closure_eq]

/-- The inclusion of a fibre is quasi-compact. -/
private instance quasiCompact_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    QuasiCompact (f.fiberι y) := by
  dsimp [Scheme.Hom.fiberι, Scheme.Hom.fiber]
  infer_instance

/-- Base changing the closed subscheme cut out by `I` along `q` is geometrically irreducible over
the base change of `p` exactly when the base change of its structure map is. -/
private theorem geometricallyIrreducible_comap_subschemeι_iff
    {S T U : Scheme.{u}} (p : S ⟶ U) (q : T ⟶ U) (I : S.IdealSheafData) :
    GeometricallyIrreducible
        ((I.comap (pullback.fst p q)).subschemeι ≫ pullback.snd p q) ↔
      GeometricallyIrreducible (pullback.snd (I.subschemeι ≫ p) q) := by
  let i := pullback.fst p q
  let e : (I.comap i).subscheme ≅ pullback (I.subschemeι ≫ p) q :=
    I.comapIso i ≪≫ pullbackSymmetry i I.subschemeι ≪≫
      pullbackRightPullbackFstIso p q I.subschemeι
  have hcomm : e.hom ≫ pullback.snd (I.subschemeι ≫ p) q =
      (I.comap i).subschemeι ≫ pullback.snd p q := by
    simp [e, i]
  rw [GeometricallyIrreducible.eq_geometrically]
  exact MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (fun T : Scheme.{u} => IrreducibleSpace T))
    (Arrow.isoMk e (Iso.refl _) hcomm)

private theorem geomIrred_subscheme_fiber_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y) (I : X.IdealSheafData) :
    GeometricallyIrreducible
        ((I.comap (f.fiberι η)).subschemeι ≫ f.fiberToSpecResidueField η) ↔
      GeometricallyIrreducible ((I.subschemeι ≫ f).fiberToSpecResidueField η) :=
  geometricallyIrreducible_comap_subschemeι_iff f (Y.fromSpecResidueField η) I

private theorem geomIrred_subscheme_baseChange
    {S T U : Scheme.{u}} (p : S ⟶ U) (q : T ⟶ U) (I : S.IdealSheafData)
    (hI : GeometricallyIrreducible (I.subschemeι ≫ p)) :
    GeometricallyIrreducible
      ((I.comap (pullback.fst p q)).subschemeι ≫ pullback.snd p q) :=
  (geometricallyIrreducible_comap_subschemeι_iff p q I).mpr inferInstance

private theorem geomIrred_fiberSubscheme_geometricExtension
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (I : X.IdealSheafData)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K]
    (hQ : GeometricallyIrreducible ((I.subschemeι ≫ f).fiberToSpecResidueField y)) :
    GeometricallyIrreducible
      ((((I.comap (f.fiberι y)).comap
        (pullback.fst (f.fiberToSpecResidueField y)
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Y.residueField y) K))))).subschemeι) ≫
          pullback.snd (f.fiberToSpecResidueField y)
            (Spec.map (CommRingCat.ofHom
              (algebraMap (Y.residueField y) K)))) := by
  have hI := (geomIrred_subscheme_fiber_iff f y I).mpr hQ
  exact geomIrred_subscheme_baseChange (f.fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))
    (I.comap (f.fiberι y)) hI

private theorem geomIrred_closure_subscheme_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (I : (f.fiber η).IdealSheafData)
    (hI : GeometricallyIrreducible
      (I.subschemeι ≫ f.fiberToSpecResidueField η)) :
    GeometricallyIrreducible
      (((I.map (f.fiberι η)).subschemeι ≫ f).fiberToSpecResidueField η) := by
  let J := I.map (f.fiberι η)
  have hJ : GeometricallyIrreducible
      ((J.comap (f.fiberι η)).subschemeι ≫ f.fiberToSpecResidueField η) :=
    geomIrred_comap_map_of_isEmbedding (f.fiberι η)
      (f.fiberι η).isEmbedding I (Y.residueField η) (f.fiberToSpecResidueField η) hI
  exact (geomIrred_subscheme_fiber_iff f η J).mp hJ

private theorem intersection_path_of_finite_closed_cover
    {ι α : Type*} [TopologicalSpace α] [Finite ι] [ConnectedSpace α]
    (s : ι → Set α) (hclosed : ∀ i, IsClosed (s i))
    (hcover : (⋃ i, s i) = Set.univ) {i j : ι}
    (hi : (s i).Nonempty) (hj : (s j).Nonempty) :
    Relation.ReflTransGen (fun i j => (s i ∩ s j).Nonempty) i j := by
  classical
  let R : ι → ι → Prop := fun i j => (s i ∩ s j).Nonempty
  let reachable : Set ι := {j | Relation.ReflTransGen R i j}
  let U : Set α := ⋃ k ∈ reachable, s k
  let W : Set α := ⋃ k ∈ reachableᶜ, s k
  have hiReachable : i ∈ reachable := Relation.ReflTransGen.refl
  have hUclosed : IsClosed U :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hclosed k
  have hWclosed : IsClosed W :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hclosed k
  have hcompl : Uᶜ = W := by
    ext x
    constructor
    · intro hxU
      have hxcover : x ∈ ⋃ k, s k := by rw [hcover]; exact Set.mem_univ x
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxcover
      have hk : k ∉ reachable := by
        intro hk
        exact hxU (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hxk⟩⟩)
      exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hxk⟩⟩
    · intro hxW hxU
      obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxU
      obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.mp hxW
      have hpath : Relation.ReflTransGen R i k := Set.mem_ofPred.mp hk
      have hedge : R k l := ⟨x, hxk, hxl⟩
      have hlNot : l ∉ reachable := by simpa using hl
      exact hlNot (Set.mem_ofPred.mpr (hpath.tail hedge))
  have hUopen : IsOpen U := by
    have hEq : U = Wᶜ := by simpa using congrArg (fun A : Set α => Aᶜ) hcompl
    rw [hEq]
    exact hWclosed.isOpen_compl
  have hUclopen : IsClopen U := ⟨hUclosed, hUopen⟩
  have hUnonempty : U.Nonempty := by
    rcases hi with ⟨x, hx⟩
    exact ⟨x, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiReachable, hx⟩⟩⟩
  have hUeq : U = Set.univ :=
    ((connectedSpace_iff_clopen.mp inferInstance).2 U hUclopen).resolve_left hUnonempty.ne_empty
  rcases hj with ⟨x, hxj⟩
  have hxU : x ∈ U := by rw [hUeq]; exact Set.mem_univ x
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxU
  have hpath : Relation.ReflTransGen R i k := Set.mem_ofPred.mp hk
  exact hpath.tail ⟨x, hxk, hxj⟩

private theorem connected_of_intersection_paths
    {ι α : Type*} [TopologicalSpace α]
    (s : ι → Set α) (hpre : ∀ i, IsPreconnected (s i))
    (hcover : (⋃ i, s i) = Set.univ)
    (hpath : ∀ i j, Relation.ReflTransGen (fun i j => (s i ∩ s j).Nonempty) i j)
    (hne : ∃ i, (s i).Nonempty) : ConnectedSpace α := by
  have hpreUnion : IsPreconnected (⋃ i, s i) :=
    IsPreconnected.iUnion_of_reflTransGen hpre hpath
  have hpreUniv : IsPreconnected (Set.univ : Set α) := by
    simpa [hcover] using hpreUnion
  have hnonempty : Nonempty α := by
    obtain ⟨i, x, hx⟩ := hne
    exact ⟨x⟩
  exact ConnectedSpace.mk (toPreconnectedSpace := ⟨hpreUniv⟩) hnonempty

private theorem generic_fiber_irreducibleComponents_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (η : Y) :
    (irreducibleComponents (f.fiber η)).Finite := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
    infer_instance
  let : IsLocallyNoetherian (f.fiber η) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η)
  let : IsNoetherian (f.fiber η) := AlgebraicGeometry.IsNoetherian.mk
  exact finite_irreducibleComponents_of_isNoetherian

private theorem generic_component_intersection_path
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) [GeometricallyConnected (f.fiberToSpecResidueField η)]
    (C D : irreducibleComponents (f.fiber η)) :
    Relation.ReflTransGen (fun C D : irreducibleComponents (f.fiber η) =>
      (C.1 ∩ D.1).Nonempty) C D := by
  have hfin : (irreducibleComponents (f.fiber η)).Finite :=
    generic_fiber_irreducibleComponents_finite f η
  let : Finite (irreducibleComponents (f.fiber η)) := hfin.to_subtype
  have : ConnectedSpace (f.fiber η) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField η)
  apply intersection_path_of_finite_closed_cover
    (fun C : irreducibleComponents (f.fiber η) => C.1)
  · intro C
    exact isClosed_of_mem_irreducibleComponents C.1 C.2
  · ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hx : x ∈ ⋃₀ irreducibleComponents (f.fiber η) := by
        rw [sUnion_irreducibleComponents]
        exact Set.mem_univ x
      rcases Set.mem_sUnion.mp hx with ⟨S, hS, hxS⟩
      exact Set.mem_iUnion.mpr ⟨⟨S, hS⟩, hxS⟩
  · exact C.2.1.nonempty
  · exact D.2.1.nonempty

private noncomputable def genericComponentClosureIdeal
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : irreducibleComponents (f.fiber η)) : X.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩).map (f.fiberι η)

/-- A point of `X` lies in the support of the closure ideal of a component `C` exactly when it lies
in the closure of the image of `C`. -/
private theorem mem_support_genericComponentClosureIdeal_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y) (C : irreducibleComponents (f.fiber η)) (x : X) :
    x ∈ (genericComponentClosureIdeal f η C).support ↔
      x ∈ closure (f.fiberι η '' (C.1 : Set (f.fiber η))) := by
  rw [genericComponentClosureIdeal]
  show x ∈ ((Scheme.IdealSheafData.vanishingIdeal _).map (f.fiberι η)).support ↔ _
  rw [Scheme.IdealSheafData.support_map]
  simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact Iff.rfl

private theorem genericComponentClosure_fiber_geometricallyIrreducible
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : irreducibleComponents (f.fiber η))
    (hC : GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩).subschemeι ≫
        f.fiberToSpecResidueField η)) :
    GeometricallyIrreducible
      (((genericComponentClosureIdeal f η C).subschemeι ≫ f).fiberToSpecResidueField η) := by
  simpa [genericComponentClosureIdeal] using
    geomIrred_closure_subscheme_fiber f η
      (Scheme.IdealSheafData.vanishingIdeal
        ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩) hC

private theorem exists_open_genericComponentClosure_geometricallyIrreducible
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η Set.univ)
    (C : irreducibleComponents (f.fiber η))
    (hC : GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩).subschemeι ≫
        f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, Nonempty V ∧
      GeometricallyIrreducible
        (((genericComponentClosureIdeal f η C).subschemeι ≫ f) ∣_ V) := by
  let I := genericComponentClosureIdeal f η C
  let q := I.subschemeι ≫ f
  let : GeometricallyIrreducible (q.fiberToSpecResidueField η) :=
    genericComponentClosure_fiber_geometricallyIrreducible f η C hC
  simpa [I, q] using H q inferInstance inferInstance inferInstance η hη inferInstance

private theorem exists_open_fiber_covered_by_genericComponentClosures
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V → ∀ x : f.fiber y,
        ∃ C : irreducibleComponents (f.fiber η),
          f.fiberι y x ∈ (genericComponentClosureIdeal f η C).support := by
  let Z : irreducibleComponents (f.fiber η) → Set (f.fiber η) := fun C => C.1
  have hcover : ∀ x : f.fiber η, ∃ C, x ∈ Z C := by
    intro x
    have hx : x ∈ ⋃₀ irreducibleComponents (f.fiber η) := by
      rw [sUnion_irreducibleComponents]
      exact Set.mem_univ x
    obtain ⟨S, hS, hxS⟩ := Set.mem_sUnion.mp hx
    exact ⟨⟨S, hS⟩, hxS⟩
  obtain ⟨U, hUopen, hUnonempty, hnear⟩ :=
    exists_open_fiber_covered_by_closures f η hη Z hcover
  refine ⟨⟨U, hUopen⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hUnonempty
    exact ⟨⟨x, hx⟩⟩
  intro y hy x
  obtain ⟨C, hC⟩ := hnear y hy x
  exact ⟨C, (mem_support_genericComponentClosureIdeal_iff f η C _).2 hC⟩

/-- A generic point of the whole space lies in every nonempty open subset. -/
private theorem mem_opens_of_isGenericPoint_univ {Y : Type*} [TopologicalSpace Y] {η : Y}
    (hη : IsGenericPoint η Set.univ) (U : Opens Y) (hU : Nonempty U) : η ∈ U :=
  (hη.mem_open_set_iff U.2).2 (by obtain ⟨y, hy⟩ := hU; exact ⟨y, Set.mem_univ y, hy⟩)

private theorem exists_open_range_near_generic_point_of_nonempty_fiber
    {Z Y : Scheme.{u}} (q : Z ⟶ Y) [IsReduced Y]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hηq : Nonempty (q.fiber η)) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V → ∃ z : Z, q z = y := by
  let F : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z
  let : F.IsFiniteType := structureSheaf_isFiniteType Z
  obtain ⟨U, hUdense, hflat, hfp, _, _⟩ :=
    exists_dense_open_flat_finitePresentation q F
  let qU := q.resLE U (q ⁻¹ᵁ U) le_rfl
  have : Flat qU := hflat
  have : LocallyOfFinitePresentation qU := hfp.1
  have : QuasiCompact qU := hfp.2.1
  have : QuasiSeparated qU := hfp.2.2
  let : AlgebraicGeometry.UniversallyOpen qU :=
    AlgebraicGeometry.UniversallyOpen.of_flat qU
  have hopen : IsOpenMap qU.base := qU.isOpenMap
  have hUopen : IsOpen (U : Set Y) := U.2
  have : Nonempty Y := ⟨η⟩
  have hU : η ∈ U := mem_opens_of_isGenericPoint_univ hη U hUdense.nonempty.to_subtype
  obtain ⟨x⟩ := hηq
  let z := q.fiberι η x
  have hz : q z = η := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac]
    simp
  let xU : q ⁻¹ᵁ U := ⟨z, by change q z ∈ U; rw [hz]; exact hU⟩
  let yU : U := ⟨η, hU⟩
  have hyU : qU.base xU = yU := by
    apply Subtype.ext
    simpa [qU, xU, yU] using hz
  have hRange : IsOpen (Set.range qU.base) := hopen.isOpen_range
  let V : Y.Opens := ⟨U.ι.base '' Set.range qU.base, U.ι.isOpenMap _ hRange⟩
  refine ⟨V, ?_, ?_⟩
  · exact ⟨η, ⟨yU, ⟨xU, hyU⟩, rfl⟩⟩
  · intro y hy
    obtain ⟨yU, hyU', hy⟩ := hy
    obtain ⟨xU, hxU⟩ := hyU'
    refine ⟨xU.1, ?_⟩
    have hqU : qU.base xU = yU := hxU
    have hval : (qU xU).1 = q xU.1 := by
      simpa [qU] using
        (Scheme.Hom.coe_resLE_apply (f := q) (U := U)
          (V := q ⁻¹ᵁ U) (e := le_rfl) xU)
    exact hval.symm.trans ((congrArg Subtype.val hqU).trans hy)

private theorem exists_open_intersection_closure_fiber_nonempty
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (C D : irreducibleComponents (f.fiber η))
    (hCD : (C.1 ∩ D.1).Nonempty) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
      Nonempty ((((genericComponentClosureIdeal f η C ⊔
        genericComponentClosureIdeal f η D).subschemeι ≫ f).fiber y)) := by
  let K := genericComponentClosureIdeal f η C ⊔ genericComponentClosureIdeal f η D
  let q := K.subschemeι ≫ f
  have hmem (E : irreducibleComponents (f.fiber η)) (hE : Classical.choose hCD ∈ E.1) :
      f.fiberι η (Classical.choose hCD) ∈ (genericComponentClosureIdeal f η E).support :=
    (mem_support_genericComponentClosureIdeal_iff f η E _).2 (subset_closure ⟨_, hE, rfl⟩)
  have hw : f.fiberι η (Classical.choose hCD) ∈ K.support := by
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨hmem C (Classical.choose_spec hCD).1, hmem D (Classical.choose_spec hCD).2⟩
  have hrange : f.fiberι η (Classical.choose hCD) ∈ Set.range K.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hw
  obtain ⟨z, hz⟩ := Set.mem_range.mp hrange
  have hηz : q z = η := by
    show f (K.subschemeι z) = η
    rw [hz]
    exact (f.fiberHomeo η (Classical.choose hCD)).property
  have hgeneric : Nonempty (q.fiber η) := by
    exact ⟨(q.fiberHomeo η).symm ⟨z, hηz⟩⟩
  have : LocallyOfFiniteType q := inferInstance
  have : QuasiCompact q := inferInstance
  obtain ⟨V, hV, hrange⟩ :=
    exists_open_range_near_generic_point_of_nonempty_fiber q η hη hgeneric
  refine ⟨V, hV, ?_⟩
  intro y hy
  obtain ⟨z, hzy⟩ := hrange y hy
  exact ⟨(q.fiberHomeo y).symm ⟨z, hzy⟩⟩

private theorem exists_open_geometricallyConnected_restrict_of_geometricComponents
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y] [IsReduced Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η Set.univ)
    [GeometricallyConnected (f.fiberToSpecResidueField η)]
    (hcomponents : ∀ C : irreducibleComponents (f.fiber η),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩).subschemeι ≫
            f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyConnected (f ∣_ V) := by
  classical
  let Cs := irreducibleComponents (f.fiber η)
  have hCs : Cs.Finite := generic_fiber_irreducibleComponents_finite f η
  let : Finite Cs := hCs.to_subtype
  obtain ⟨Uc, hUcoverNe, hcovered⟩ :=
    exists_open_fiber_covered_by_genericComponentClosures f η hη
  have : ConnectedSpace (f.fiber η) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField η)
  obtain ⟨Ur, hUrangeNe, hrange⟩ :=
    exists_open_range_near_generic_point_of_nonempty_fiber f η hη
      (show Nonempty (f.fiber η) from inferInstance)
  have hGIexists (C : Cs) : ∃ W : Y.Opens, Nonempty W ∧
      GeometricallyIrreducible
        (((genericComponentClosureIdeal f η C).subschemeι ≫ f) ∣_ W) := by
    apply exists_open_genericComponentClosure_geometricallyIrreducible H f η hη C
    simpa [genericComponentClosureIdeal] using hcomponents C
  let WGI : Cs → Y.Opens := fun C => Classical.choose (hGIexists C)
  have hWGInet (C : Cs) : Nonempty (WGI C) := (Classical.choose_spec (hGIexists C)).1
  have hWGI (C : Cs) : GeometricallyIrreducible
      (((genericComponentClosureIdeal f η C).subschemeι ≫ f) ∣_ WGI C) :=
    (Classical.choose_spec (hGIexists C)).2
  have hEdgeExists (C D : Cs) (hCD : (C.1 ∩ D.1).Nonempty) :
      ∃ W : Y.Opens, Nonempty W ∧
        ∀ y : Y, y ∈ W →
          Nonempty ((((genericComponentClosureIdeal f η C ⊔
            genericComponentClosureIdeal f η D).subschemeι ≫ f).fiber y)) :=
    exists_open_intersection_closure_fiber_nonempty f η hη C D hCD
  let WEdge : Cs → Cs → Y.Opens := fun C D =>
    if hCD : (C.1 ∩ D.1).Nonempty then Classical.choose (hEdgeExists C D hCD) else ⊤
  have hWEdgenet (C D : Cs) : Nonempty (WEdge C D) := by
    by_cases hCD : (C.1 ∩ D.1).Nonempty
    · simpa [WEdge, hCD] using (Classical.choose_spec (hEdgeExists C D hCD)).1
    · simp [WEdge, hCD]
  have hWEdge (C D : Cs) (hCD : (C.1 ∩ D.1).Nonempty) (y : Y) (hy : y ∈ WEdge C D) :
      Nonempty ((((genericComponentClosureIdeal f η C ⊔
        genericComponentClosureIdeal f η D).subschemeι ≫ f).fiber y)) := by
    have hy' : y ∈ Classical.choose (hEdgeExists C D hCD) := by
      simpa [WEdge, hCD] using hy
    simpa [WEdge, hCD] using (Classical.choose_spec (hEdgeExists C D hCD)).2 y hy'
  let W : Y.Opens := Uc ⊓ Ur ⊓ (⨅ C : Cs, WGI C) ⊓ (⨅ C : Cs, ⨅ D : Cs, WEdge C D)
  have hmemW (z : Y) : z ∈ W ↔ z ∈ Uc ∧ z ∈ Ur ∧ (∀ C : Cs, z ∈ WGI C) ∧
      ∀ C D : Cs, z ∈ WEdge C D := by
    simp [W, ← SetLike.mem_coe, Opens.coe_iInf, and_assoc]
  have hηW : η ∈ W := (hmemW η).2 ⟨mem_opens_of_isGenericPoint_univ hη _ hUcoverNe,
    mem_opens_of_isGenericPoint_univ hη _ hUrangeNe,
    fun C => mem_opens_of_isGenericPoint_univ hη _ (hWGInet C),
    fun C D => mem_opens_of_isGenericPoint_univ hη _ (hWEdgenet C D)⟩
  refine ⟨W, ⟨⟨η, hηW⟩⟩, ?_⟩
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro yW
  let y : Y := W.ι yW
  have hy : y ∈ W := yW.property
  have hyParts := (hmemW y).1 hy
  have : Nonempty (f.fiber y) := by
    obtain ⟨x, hx⟩ := hrange y hyParts.2.1
    exact ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩
  let k := Y.residueField y
  let K := SeparableClosure k
  let g := f.fiberToSpecResidueField y
  let q := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Zg := pullback g q
  let J : Cs → Zg.IdealSheafData := fun C =>
    ((genericComponentClosureIdeal f η C).comap (f.fiberι y)).comap
      (pullback.fst g q)
  let s : Cs → Set Zg := fun C => (J C).support
  have : IsSepClosed K := IsSepClosure.sep_closed (k := k) (K := K)
  have hclosed (C : Cs) : IsClosed (s C) := (J C).support.isClosed
  have hs (C : Cs) (z : Zg) : z ∈ s C ↔
      f.fiberι y (pullback.fst g q z) ∈ (genericComponentClosureIdeal f η C).support := by
    simp only [s, J, Scheme.IdealSheafData.support_comap]
    rfl
  have hcover : (⋃ C : Cs, s C) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨C, hC⟩ := hcovered y hyParts.1 (pullback.fst g q z)
    exact Set.mem_iUnion.mpr ⟨C, (hs C z).2 hC⟩
  have hpre (C : Cs) : _root_.IsPreconnected (s C) := by
    have hGIy : GeometricallyIrreducible
        (((genericComponentClosureIdeal f η C).subschemeι ≫ f).fiberToSpecResidueField y) := by
      let qC := (genericComponentClosureIdeal f η C).subschemeι ≫ f
      let : GeometricallyIrreducible (qC ∣_ WGI C) := hWGI C
      simpa [qC] using geometricallyIrreducible_fiber_of_restrict
        qC (WGI C) y (hyParts.2.2.1 C)
    have hGIext := geomIrred_fiberSubscheme_geometricExtension f y
      (genericComponentClosureIdeal f η C) K hGIy
    let : GeometricallyIrreducible
        ((J C).subschemeι ≫ pullback.snd g q) := by
      exact hGIext
    have : Subsingleton (Spec (.of K)) := inferInstance
    have : Nonempty (Spec (.of K)) := inferInstance
    have : IrreducibleSpace (J C).subscheme :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton
        ((J C).subschemeι ≫ pullback.snd g q)
    have hirr : IsIrreducible (s C) := by
      have h := (IrreducibleSpace.isIrreducible_univ (J C).subscheme).image
        (J C).subschemeι.base (J C).subschemeι.continuous.continuousOn
      simpa [s, Scheme.IdealSheafData.range_subschemeι] using h
    exact hirr.2.isPreconnected
  have hEdgeLift (C D : Cs) (hCD : (C.1 ∩ D.1).Nonempty) :
      (s C ∩ s D).Nonempty := by
    obtain ⟨w⟩ := hWEdge C D hCD y (hyParts.2.2.2 C D)
    let KCD := genericComponentClosureIdeal f η C ⊔ genericComponentClosureIdeal f η D
    let qCD := KCD.subschemeι ≫ f
    let w' := qCD.fiberι y w
    have hw' : qCD w' = y := by
      exact (qCD.fiberHomeo y w).property
    let x : f.fiber y := (f.fiberHomeo y).symm ⟨KCD.subschemeι w', by
      show f (KCD.subschemeι w') = y
      exact hw'⟩
    have hx : f.fiberι y x = KCD.subschemeι w' := by
      simp [x]
    let : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
      exact (flat_and_surjective_SpecMap_iff
        (CommRingCat.ofHom (algebraMap k K))).mpr
          (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) |>.2
    obtain ⟨z, hz⟩ := (pullback.fst g q).surjective x
    have hK : KCD.subschemeι w' ∈ KCD.support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w', rfl⟩
    rw [Scheme.IdealSheafData.support_sup] at hK
    exact ⟨z, (hs C z).2 (by rw [hz, hx]; exact hK.1), (hs D z).2 (by rw [hz, hx]; exact hK.2)⟩
  have hpath : ∀ C D : Cs, Relation.ReflTransGen
      (fun C D : Cs => (s C ∩ s D).Nonempty) C D := by
    intro C D
    have hp := generic_component_intersection_path f η C D
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp hCD ih => exact ih.tail (hEdgeLift _ _ hCD)
  have hnonempty : ∃ C : Cs, (s C).Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hrange y hyParts.2.1
    let x : f.fiber y := (f.fiberHomeo y).symm ⟨x₀, hx₀⟩
    obtain ⟨z, hz⟩ := (pullback.fst g q).surjective x
    obtain ⟨C, hzC⟩ := Set.mem_iUnion.mp (by
      rw [hcover]
      exact Set.mem_univ z)
    exact ⟨C, ⟨z, hzC⟩⟩
  have hconnected : ConnectedSpace Zg :=
    connected_of_intersection_paths s hpre hcover hpath hnonempty
  have hfiberGC : GeometricallyConnected g :=
    (geometricallyConnected_iff_connectedSpace_pullback_separableClosure k g).mpr hconnected
  exact (geometricallyConnected_fiber_of_restrict f W y hy).mpr hfiberGC

private theorem etale_algebra_isReduced_of_isDomain
    {R B : Type u} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] : _root_.IsReduced B := by
  let K := FractionRing R
  have : Algebra.Etale K (TensorProduct R K B) := inferInstance
  have : _root_.IsReduced (TensorProduct R K B) := by
    let : Algebra.FormallyUnramified K (TensorProduct R K B) :=
      ((Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth).mp
        Algebra.Etale.formallyEtale).1
    let : Algebra.EssFiniteType K (TensorProduct R K B) := inferInstance
    exact Algebra.FormallyUnramified.isReduced_of_field K (TensorProduct R K B)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R K B) := by
    have hRK : Function.Injective (Algebra.linearMap R K) := IsFractionRing.injective R K
    have hrT : Function.Injective (LinearMap.rTensor B (Algebra.linearMap R K)) :=
      Module.Flat.rTensor_preserves_injective_linearMap (Algebra.linearMap R K) hRK
    intro b₁ b₂ hb
    have key : ∀ b : B, (Algebra.TensorProduct.includeRight : B →ₐ[R] _) b =
        LinearMap.rTensor B (Algebra.linearMap R K) (1 ⊗ₜ[R] b) := by
      intro b
      simp only [Algebra.TensorProduct.includeRight_apply, LinearMap.rTensor_tmul,
        Algebra.linearMap_apply, map_one]
    rw [key, key] at hb
    simpa using congrArg (TensorProduct.lid R B) (hrT hb)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[R] TensorProduct R K B) hinj

private theorem isReduced_of_finite_etale_over_integral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f]
    [IsReduced Y] [IrreducibleSpace Y] : IsReduced X := by
  let 𝒰 := Y.affineCover.pullback₁ f
  have : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
    intro i
    let U := Y.affineCover.X i
    let P := 𝒰.X i
    let p : P ⟶ U := pullback.snd f (Y.affineCover.f i)
    have : IsOpenImmersion (Y.affineCover.f i) := Y.affineCover.map_prop i
    have : IsReduced U := isReduced_of_isOpenImmersion (Y.affineCover.f i)
    have : Nonempty (Y.affineCover.X i) := by
      classical
      dsimp [Scheme.affineCover]
      let V := Classical.choose (Y.local_affine i)
      let e := Classical.choice
        (Classical.choose_spec (Classical.choose_spec (Y.local_affine i)))
      exact ⟨e.hom.base ⟨i, V.2⟩⟩
    have : IrreducibleSpace U := (Y.affineCover.f i).isOpenEmbedding.irreducibleSpace
    have : IsIntegral U := isIntegral_of_irreducibleSpace_of_isReduced U
    have : IsAffine U := Scheme.isAffine_affineCover Y i
    have : IsFinite p := (inferInstance : IsFinite (pullback.snd f (Y.affineCover.f i)))
    have : IsAffineHom p := IsFinite.toIsAffineHom
    have : IsAffine P := isAffine_of_isAffineHom p
    have : Etale p := (inferInstance : Etale (pullback.snd f (Y.affineCover.f i)))
    have hEtale : (p.appTop).hom.Etale :=
      HasRingHomProperty.appTop (P := @Etale) p ‹Etale p›
    let : Algebra Γ(U, ⊤) Γ(P, ⊤) := (p.appTop).hom.toAlgebra
    have : Algebra.Etale Γ(U, ⊤) Γ(P, ⊤) := hEtale.toAlgebra
    have : IsDomain Γ(U, ⊤) :=
      (affine_isIntegral_iff Γ(U, ⊤)).mp inferInstance
    have : _root_.IsReduced ↥Γ(P, ⊤) :=
      etale_algebra_isReduced_of_isDomain (R := ↥Γ(U, ⊤)) (B := ↥Γ(P, ⊤))
    exact isReduced_of_isAffine_isReduced P
  exact IsReduced.of_openCover X 𝒰

/-- **Stacks Project, Tag 055G**, granted Tag 0559. A finite type morphism whose fibre over
the generic point of an irreducible base is geometrically connected has geometrically connected
fibres over a nonempty open subscheme of the base.

No tag is attached: the statement carries the hypothesis `H`, which the Stacks statement does
not have. Discharging `H` turns this into Tag 055G. -/
public theorem exists_open_geometricallyConnected_restrict
    (H : GeometricallyIrreducibleAfterShrinking.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η Set.univ)
    [GeometricallyConnected (f.fiberToSpecResidueField η)] :
    ∃ V : Y.Opens, Nonempty V ∧ GeometricallyConnected (f ∣_ V) := by
  classical
  let Y₀ := Y.nilradical.subscheme
  let r : Y₀ ⟶ Y := Y.nilradical.subschemeι
  let : UniversalHomeomorphism r :=
    universalHomeomorphism_nilradical_subschemeι Y
  have hrHomeo : IsHomeomorph r :=
    (inferInstance : UniversalHomeomorphism r)
      |>.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  let eRed := hrHomeo.homeomorph r
  have : IsReduced Y₀ := isReduced_nilradical_subscheme Y
  have : IrreducibleSpace Y₀ := eRed.irreducibleSpace_iff.mpr inferInstance
  let η₀ : Y₀ := eRed.symm η
  have hη₀ : IsGenericPoint η₀ Set.univ := by
    show closure ({η₀} : Set Y₀) = Set.univ
    calc
      closure ({η₀} : Set Y₀) = eRed.symm '' closure ({η} : Set Y) := by
        rw [eRed.symm.image_closure]
        simp [η₀]
      _ = Set.univ := by rw [hη.def]; simp
  have hrη : r η₀ = η := by
    show eRed η₀ = η
    exact eRed.apply_symm_apply η
  let f₀ := pullback.snd f r
  have hpbRed : IsPullback (pullback.fst f r) f₀ f r :=
    IsPullback.of_hasPullback f r
  have hcountRed := congrFun
    (numGeometricConnectedComponents_eq_of_isPullback f f₀
      (pullback.fst f r) r hpbRed) η₀
  have hGCη : GeometricallyConnected (f.fiberToSpecResidueField η) := inferInstance
  have hcountOne : numGeometricConnectedComponents f η = 1 :=
    (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f η).mp hGCη
  have hGCη₀ : GeometricallyConnected (f₀.fiberToSpecResidueField η₀) := by
    apply (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f₀ η₀).mpr
    calc
      numGeometricConnectedComponents f₀ η₀ =
          numGeometricConnectedComponents f (r η₀) := hcountRed
      _ = 1 := by rw [hrη]; exact hcountOne
  let : LocallyOfFiniteType f₀ := inferInstance
  let : QuasiCompact f₀ := inferInstance
  obtain ⟨V₀, hV₀ne, Y', g, hgSurj, hgFinite, hgEtale, hYirr, hYaff,
      hpull, hg'Surj, hg'Finite, hg'Etale, hgeneric⟩ :=
    exists_nonemptyOpen_finiteEtale_cover_geometricallyIrreducible_genericFiber f₀
  let : IrreducibleSpace Y' := hYirr
  let : IsReduced V₀.toScheme := inferInstance
  have : Nonempty (V₀ : Set Y₀) := by
    obtain ⟨y, hy⟩ := hV₀ne
    exact ⟨⟨y, hy⟩⟩
  have : IrreducibleSpace V₀.toScheme := by
    show IrreducibleSpace (V₀ : Set Y₀)
    exact V₀.2.isOpenEmbedding_subtypeVal.irreducibleSpace
  let : IsFinite g := hgFinite
  let : Etale g := hgEtale
  let : IsReduced Y' := isReduced_of_finite_etale_over_integral g
  let k := g ≫ V₀.ι
  let f' := pullback.fst k f₀
  let : LocallyOfFiniteType f' := inferInstance
  let : QuasiCompact f' := inferInstance
  let η' : Y' := genericPoint Y'
  have hη' : IsGenericPoint η' Set.univ := genericPoint_spec Y'
  have hkrange : Set.range k.base = (V₀ : Set Y₀) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (g z).property
    · intro hy
      let : Surjective g := hgSurj
      obtain ⟨z, hz⟩ := g.surjective ⟨y, hy⟩
      refine ⟨z, ?_⟩
      show V₀.ι (g z) = y
      exact congrArg V₀.ι hz
  have hηV₀ : η₀ ∈ V₀ := mem_opens_of_isGenericPoint_univ hη₀ V₀ hV₀ne.to_subtype
  have hV₀dense : closure (V₀ : Set Y₀) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    have hsub : closure ({η₀} : Set Y₀) ⊆ closure (V₀ : Set Y₀) :=
      closure_minimal (Set.singleton_subset_iff.mpr (subset_closure hηV₀))
        isClosed_closure
    have hy : y ∈ closure ({η₀} : Set Y₀) := by rw [hη₀.def]; exact Set.mem_univ y
    exact hsub hy
  have hη'k : IsGenericPoint (k η') Set.univ := by
    have himage := hη'.image k.continuous
    have hclosure : closure (k '' (Set.univ : Set Y')) = Set.univ := by
      rw [Set.image_univ, hkrange, hV₀dense]
    rw [hclosure] at himage
    exact himage
  have hηeq : k η' = η₀ := hη'k.eq hη₀
  have hpbCover : IsPullback (pullback.snd k f₀) f' f₀ k :=
    (IsPullback.of_hasPullback k f₀).flip
  have hcountCover := congrFun
    (numGeometricConnectedComponents_eq_of_isPullback f₀ f'
      (pullback.snd k f₀) k hpbCover) η'
  have hGCη' : GeometricallyConnected (f'.fiberToSpecResidueField η') := by
    apply (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f' η').mpr
    calc
      numGeometricConnectedComponents f' η' =
          numGeometricConnectedComponents f₀ (k η') := hcountCover
      _ = 1 := by rw [hηeq]; exact
        (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f₀ η₀).mp hGCη₀
  have hcomponents : ∀ C : irreducibleComponents (f'.fiber η'),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨C.1, isClosed_of_mem_irreducibleComponents C.1 C.2⟩).subschemeι ≫
            f'.fiberToSpecResidueField η') := by
    intro C
    exact hgeneric η' hη' C
  let : GeometricallyConnected (f'.fiberToSpecResidueField η') := hGCη'
  obtain ⟨W, hWne, hWGC⟩ :=
    exists_open_geometricallyConnected_restrict_of_geometricComponents
      H f' η' hη' hcomponents
  have hkOpen : IsOpenMap k := by
    dsimp [k]
    let : Etale g := hgEtale
    exact IsOpenMap.comp (f := g) (g := V₀.ι)
      V₀.ι.isOpenMap (Scheme.Hom.isOpenMap g)
  let U₀ : Y₀.Opens := ⟨k.base '' (W : Set Y'), hkOpen _ W.2⟩
  have hU₀ne : Nonempty U₀ := by
    obtain ⟨z, hz⟩ := hWne
    exact ⟨⟨k z, ⟨z, hz, rfl⟩⟩⟩
  have hcountF₀ (y : Y₀) (hy : y ∈ U₀) :
      numGeometricConnectedComponents f₀ y = 1 := by
    obtain ⟨z, hzW, hzy⟩ := hy
    have hGCz : GeometricallyConnected (f'.fiberToSpecResidueField z) := by
      have hfib := (GeometricallyConnected.iff_geometricallyConnected_fiber
        (f := f' ∣_ W)).mp hWGC ⟨z, hzW⟩
      exact (geometricallyConnected_fiber_of_restrict f' W z hzW).mp hfib
    have hcntz := (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f' z).mp hGCz
    have hbase := congrFun
      (numGeometricConnectedComponents_eq_of_isPullback f₀ f'
        (pullback.snd k f₀) k hpbCover) z
    have hpoint : k z = y := hzy
    calc
      numGeometricConnectedComponents f₀ y =
          numGeometricConnectedComponents f₀ (k z) := by rw [hpoint]
      _ = numGeometricConnectedComponents f' z := hbase.symm
      _ = 1 := hcntz
  let V : Y.Opens := ⟨r.base '' (U₀ : Set Y₀), hrHomeo.isOpenMap _ U₀.2⟩
  refine ⟨V, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hU₀ne
    exact ⟨⟨r y, ⟨y, hy, rfl⟩⟩⟩
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro yV
  let y : Y := V.ι yV
  have hy : y ∈ V := yV.property
  change y ∈ r.base '' (U₀ : Set Y₀) at hy
  obtain ⟨y₀, hy₀, hry⟩ := hy
  have hcountf : numGeometricConnectedComponents f y = 1 := by
    have hbase := congrFun
      (numGeometricConnectedComponents_eq_of_isPullback f f₀
        (pullback.fst f r) r hpbRed) y₀
    rw [← hry]
    calc
      numGeometricConnectedComponents f (r y₀) =
          numGeometricConnectedComponents f₀ y₀ := hbase.symm
      _ = 1 := hcountF₀ y₀ hy₀
  have hrestrCount := congrFun
    (numGeometricConnectedComponents_eq_of_isPullback f
      (f ∣_ V) (f ⁻¹ᵁ V).ι V.ι (isPullback_morphismRestrict f V).flip) yV
  apply (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one (f ∣_ V) yV).mpr
  calc
    numGeometricConnectedComponents (f ∣_ V) yV =
        numGeometricConnectedComponents f (V.ι yV) := hrestrCount
    _ = 1 := hcountf

end AlgebraicGeometry
