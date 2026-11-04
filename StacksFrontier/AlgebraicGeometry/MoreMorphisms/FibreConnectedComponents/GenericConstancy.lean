module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LowerBound
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import
  StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.ConnectedComponents
public import StacksCore.Tactic.StacksAttribute

/-!
# Generic constancy of the number of geometric connected components

Let `f : X ⟶ Y` be a finite type morphism of schemes and let `y` be a point of `Y`. Stacks Tag
055H says that the number of geometrically connected components of the fibres of `f` is
constant on a nonempty open subset of the closure of `y`.

## Main results

* `AlgebraicGeometry.exists_open_numGeometricConnectedComponents_eq` is Stacks Tag 055H.

## Implementation notes

Being of finite type is expressed by `LocallyOfFiniteType` together with `QuasiCompact`, and
the number of geometric connected components is the `ℕ∞`-valued
`AlgebraicGeometry.numGeometricConnectedComponents` of Tag 055F. The open subset is bundled as
an open of the subspace `closure {y}`, so its points carry both the openness and the
containment asserted by the source.

Replacing `Y` by the reduced induced closed subscheme on `closure {y}`, whose underlying space
is homeomorphic to `closure {y}`, reduces the statement to an irreducible base with a chosen
dense generic point `η`, Tag 055F transporting the count along that base change. Over such a
base Tag 0551 provides a finite etale surjective cover of a nonempty open of the base over
which the irreducible components of the generic fibre are geometrically irreducible; Tag 054S
then makes each connected component of the generic fibre geometrically connected, Tag 055G
spreads that out to the fibres over a neighbourhood of `η`, and Tag 054Y makes the closures of
those components cover every nearby fibre. This bounds the number of geometric connected
components of a nearby fibre above by the number for the generic fibre, while Tag 055D bounds
the number of ordinary connected components below by it; a faithfully flat base change of a
fibre to a separably closed field is surjective, so the ordinary count is at most the geometric
one, and the two bounds meet.

## References

* [Stacks Project, Tag 055H](https://stacks.math.columbia.edu/tag/055H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

private lemma natCard_connectedComponents_le_of_finite_cover_connected
    {α ι : Type u} [TopologicalSpace α] [Finite ι]
    (S : ι → Set α) (hconn : ∀ i, IsConnected (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i) :
    Nat.card (_root_.ConnectedComponents α) ≤ Nat.card ι := by
  classical
  let := Fintype.ofFinite ι
  choose x hx using fun i => (hconn i).nonempty
  apply Nat.card_le_card_of_surjective (fun i => ConnectedComponents.mk (x i))
  intro c
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hzi⟩ := hcover z
  refine ⟨i, ?_⟩
  rw [ConnectedComponents.coe_eq_coe']
  have hzcomp := (hconn i).subset_connectedComponent (hx i) hzi
  rw [← connectedComponent_eq hzcomp]
  exact mem_connectedComponent

private lemma natCard_connectedComponents_le_of_surjective_continuous
    {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    [Finite (_root_.ConnectedComponents α)] [Finite (_root_.ConnectedComponents β)]
    (f : α → β) (hf : Continuous f) (hfsurj : Function.Surjective f) :
    Nat.card (_root_.ConnectedComponents β) ≤ Nat.card (_root_.ConnectedComponents α) :=
  Nat.card_le_card_of_surjective hf.connectedComponentsMap
    (hf.connectedComponentsMap_surjective hfsurj)

private lemma natCard_connectedComponents_fiber_le_geometricFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
    [Field K] [Algebra (Y.residueField y) K]
    [Finite (_root_.ConnectedComponents (f.fiber y))]
    [Finite (_root_.ConnectedComponents (geometricFiber f y K))] :
    Nat.card (_root_.ConnectedComponents (f.fiber y)) ≤
      Nat.card (_root_.ConnectedComponents (geometricFiber f y K)) := by
  let k := Y.residueField y
  let q := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Module.FaithfullyFlat k K := by
    apply Module.FaithfullyFlat.of_comap_surjective
    exact fun _ => ⟨default, Subsingleton.elim _ _⟩
  have hq : Flat q ∧ Surjective q :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).2
      ((RingHom.faithfullyFlat_algebraMap_iff (R := k) (S := K)).2 inferInstance)
  let g := f.fiberToSpecResidueField y
  let p := pullback.fst g q
  have : Surjective q := hq.2
  exact natCard_connectedComponents_le_of_surjective_continuous p.base
    p.continuous p.surjective

private theorem finiteConnectedComponents_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (y : Y) : Finite (_root_.ConnectedComponents (f.fiber y)) := by
  have : IsNoetherian (f.fiber y) := fiber_isNoetherian f y
  exact TopologicalSpace.NoetherianSpace.finite_connectedComponents (f.fiber y)

private theorem finiteConnectedComponents_geometricFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (y : Y) (K : Type u) [Field K] [Algebra (Y.residueField y) K] :
    Finite (_root_.ConnectedComponents (geometricFiber f y K)) := by
  let g := f.fiberToSpecResidueField y
  let h := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K))
  have : CompactSpace (Spec (.of K)) := inferInstance
  have : LocallyOfFiniteType g := by
    show LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y))
    exact AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹LocallyOfFiniteType f›
  have hlt : LocallyOfFiniteType (pullback.snd g h) :=
    AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g h) inferInstance
  let : QuasiCompact g := inferInstance
  let : QuasiCompact (pullback.snd g h) := inferInstance
  have hcompact : CompactSpace (geometricFiber f y K) := by
    show CompactSpace (Limits.pullback (C := Scheme) g h)
    infer_instance
  let : IsLocallyNoetherian (Spec (.of K)) := inferInstance
  have hlocal : IsLocallyNoetherian (geometricFiber f y K) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.snd g h) hlt inferInstance
  let : IsNoetherian (geometricFiber f y K) :=
    { toIsLocallyNoetherian := hlocal, toCompactSpace := hcompact }
  exact TopologicalSpace.finite_connectedComponents_of_finite_irreducibleComponents
    AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian

private noncomputable def homeomorph_of_embeddings_range_eq
    {A B X : Type v} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (f : A → X) (g : B → X) (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
    (h : Set.range f = Set.range g) : A ≃ₜ B := by
  have h' : f '' Set.univ = g '' Set.univ := by
    ext x
    constructor
    · rintro ⟨a, -, rfl⟩
      obtain ⟨b, hb⟩ := Set.mem_range.mp ((Set.ext_iff.mp h (f a)).mp ⟨a, rfl⟩)
      exact ⟨b, Set.mem_univ _, hb⟩
    · rintro ⟨b, -, rfl⟩
      obtain ⟨a, ha⟩ := Set.mem_range.mp ((Set.ext_iff.mp h (g b)).mpr ⟨b, rfl⟩)
      exact ⟨a, Set.mem_univ _, ha⟩
  exact ((Homeomorph.Set.univ A).symm.trans (hf.homeomorphImage Set.univ)).trans
    ((Homeomorph.setCongr h').trans ((hg.homeomorphImage Set.univ).symm.trans
      (Homeomorph.Set.univ B)))

/-- The subscheme of the base change of an ideal sheaf is the base change of its subscheme. -/
private noncomputable def comapSubschemeIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (I : X.IdealSheafData) :
    (I.comap (pullback.fst f g)).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
  I.comapIso (pullback.fst f g) ≪≫ pullbackSymmetry (pullback.fst f g) I.subschemeι ≪≫
    pullbackRightPullbackFstIso f g I.subschemeι

private lemma connectedSpace_comap_subscheme_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (I : X.IdealSheafData) :
    ConnectedSpace (I.comap (pullback.fst f g)).subscheme ↔
      ConnectedSpace (pullback (C := Scheme) (I.subschemeι ≫ f) g) :=
  ⟨ObjectProperty.prop_of_iso (P := fun T : Scheme.{u} => ConnectedSpace T)
      (comapSubschemeIso f g I),
    ObjectProperty.prop_of_iso (P := fun T : Scheme.{u} => ConnectedSpace T)
      (comapSubschemeIso f g I).symm⟩

private lemma geometricallyConnected_subscheme_iff_connectedSpace_comap
    {X : Scheme.{u}} (k : Type u) [Field k] (p : X ⟶ Spec (.of k)) (I : X.IdealSheafData) :
    GeometricallyConnected (I.subschemeι ≫ p) ↔
      ∀ (K : Type u) [Field K] (q : Spec (.of K) ⟶ Spec (.of k)),
        ConnectedSpace (I.comap (pullback.fst p q)).subscheme := by
  rw [GeometricallyConnected.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms (P := fun T : Scheme.{u} => ConnectedSpace T)]
  exact forall_congr' fun K => forall_congr' fun _ => forall_congr' fun q =>
    (connectedSpace_comap_subscheme_iff p q I).symm

private lemma geometricallyConnected_subscheme_of_support_eq
    {X : Scheme.{u}} (k : Type u) [Field k] (p : X ⟶ Spec (.of k))
    (I J : X.IdealSheafData) (h : I.support = J.support)
    (hI : GeometricallyConnected (I.subschemeι ≫ p)) :
    GeometricallyConnected (J.subschemeι ≫ p) := by
  rw [geometricallyConnected_subscheme_iff_connectedSpace_comap] at hI ⊢
  intro K _ q
  refine (homeomorph_of_embeddings_range_eq _ _ (I.comap (pullback.fst p q)).subschemeι.isEmbedding
    (J.comap (pullback.fst p q)).subschemeι.isEmbedding ?_).connectedSpace_iff.mp (hI K q)
  simp [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap, h]

private lemma geometricallyConnected_closedSubscheme_of_open_range
    {X : Scheme.{u}} (k : Type u) [Field k] (p : X ⟶ Spec (.of k))
    (U : X.Opens) (I : X.IdealSheafData)
    (himage : Set.range U.ι = (I.support : Set X))
    (hU : GeometricallyConnected (U.ι ≫ p)) :
    GeometricallyConnected (I.subschemeι ≫ p) := by
  rw [geometricallyConnected_subscheme_iff_connectedSpace_comap]
  intro K _ q
  let T := pullback (C := Scheme) p q
  let e := pullbackRightPullbackFstIso p q U.ι
  let uMap : pullback (C := Scheme) U.ι (pullback.fst (C := Scheme) p q) ⟶ T :=
    pullback.snd (C := Scheme) U.ι (pullback.fst (C := Scheme) p q)
  let I' := I.comap (pullback.fst (C := Scheme) p q)
  have hu : Topology.IsEmbedding uMap := by
    dsimp [uMap]
    exact (pullback.snd (C := Scheme) U.ι
      (pullback.fst (C := Scheme) p q)).isOpenEmbedding.isEmbedding
  have hI : Topology.IsEmbedding I'.subschemeι := I'.subschemeι.isEmbedding
  have hrange : Set.range uMap = Set.range I'.subschemeι := by
    show Set.range (pullback.snd (C := Scheme) U.ι
      (pullback.fst (C := Scheme) p q)) =
      Set.range I'.subschemeι.base
    rw [AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd,
      Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange,
      Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      ← Scheme.Opens.range_ι U]
    exact congrArg (fun s : Set X => (pullback.fst p q).base ⁻¹' s) himage
  let eHomeo := homeomorph_of_embeddings_range_eq uMap I'.subschemeι hu hI hrange
  have hbase' : ConnectedSpace (pullback (C := Scheme) (U.ι ≫ p) q) :=
    hU.geometrically_connectedSpace q
      (pullback.fst (C := Scheme) (U.ι ≫ p) q)
      (pullback.snd (C := Scheme) (U.ι ≫ p) q)
      (IsPullback.of_hasPullback (C := Scheme) _ _)
  have hbase : ConnectedSpace (pullback (C := Scheme) U.ι
      (pullback.fst (C := Scheme) p q)) :=
    (ObjectProperty.prop_of_iso (P := fun T : Scheme.{u} => ConnectedSpace T) e.symm) hbase'
  exact eHomeo.connectedSpace_iff.mp hbase

private lemma geometricallyConnected_comap_map_of_isEmbedding
    {A B : Scheme.{u}} (i : A ⟶ B) [QuasiCompact i] (hi : Topology.IsEmbedding i)
    (I : A.IdealSheafData) (k : Type u) [Field k] (p : A ⟶ Spec (.of k))
    (hI : GeometricallyConnected (I.subschemeι ≫ p)) :
    GeometricallyConnected (((I.map i).comap i).subschemeι ≫ p) := by
  apply geometricallyConnected_subscheme_of_support_eq k p I ((I.map i).comap i) ?_ hI
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_map]
  ext x
  show x ∈ (I.support : Set A) ↔
    x ∈ i ⁻¹' closure (i '' (I.support : Set A))
  rw [← hi.isInducing.closure_eq_preimage_closure_image]
  simp [I.support.isClosed.closure_eq]

private lemma geometricallyConnected_subscheme_baseChange_iff
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (I : X.IdealSheafData) :
    GeometricallyConnected
        ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) ↔
      GeometricallyConnected (pullback.snd (I.subschemeι ≫ f) g) := by
  let i := pullback.fst f g
  let p := pullback.snd f g
  let h := I.subschemeι ≫ f
  let a := (I.comap i).subschemeι ≫ p
  let b := pullback.snd h g
  let e := comapSubschemeIso f g I
  have hcomm : e.hom ≫ b = a := by
    show ((I.comapIso i).hom ≫
      ((pullbackSymmetry i I.subschemeι).hom ≫
        (pullbackRightPullbackFstIso f g I.subschemeι).hom)) ≫ b = a
    calc
      _ = (I.comapIso i).hom ≫
          ((pullbackSymmetry i I.subschemeι).hom ≫
            ((pullbackRightPullbackFstIso f g I.subschemeι).hom ≫ b)) := by
              simp [Category.assoc]
      _ = (I.comapIso i).hom ≫
          ((pullbackSymmetry i I.subschemeι).hom ≫ (pullback.snd I.subschemeι i ≫ p)) := by
              rw [pullbackRightPullbackFstIso_hom_snd]
      _ = (I.comapIso i).hom ≫
          (((pullbackSymmetry i I.subschemeι).hom ≫ pullback.snd I.subschemeι i) ≫ p) := by
              rw [Category.assoc]
      _ = (I.comapIso i).hom ≫ (pullback.fst i I.subschemeι ≫ p) := by
              rw [pullbackSymmetry_hom_comp_snd]
      _ = (I.comap i).subschemeι ≫ p := by
              rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  let eArrow : Arrow.mk a ≅ Arrow.mk b :=
    Arrow.isoMk (f := Arrow.mk a) (g := Arrow.mk b) e (Iso.refl _) hcomm
  rw [GeometricallyConnected.eq_geometrically]
  exact MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (fun T : Scheme.{u} => ConnectedSpace T)) eArrow

private lemma geometricallyConnected_subscheme_comap_baseChange
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (I : X.IdealSheafData)
    (hI : GeometricallyConnected (I.subschemeι ≫ f)) :
    GeometricallyConnected
      (((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g)) := by
  refine (geometricallyConnected_subscheme_baseChange_iff f g I).mpr ?_
  rw [GeometricallyConnected.eq_geometrically] at hI ⊢
  exact MorphismProperty.pullback_snd _ _ hI

private theorem natCard_connectedComponents_pullback_le_of_cover
    {A B Z : Scheme.{u}} (f : A ⟶ B) (g : Z ⟶ B)
    [Subsingleton Z] [Nonempty Z] {ι : Type u} [Finite ι]
    (I : ι → A.IdealSheafData)
    (hgeom : ∀ i, GeometricallyConnected ((I i).subschemeι ≫ f))
    (hcover : ∀ x : A, ∃ i, x ∈ (I i).support) :
    Nat.card (_root_.ConnectedComponents (Limits.pullback (C := Scheme) f g)) ≤ Nat.card ι := by
  classical
  let π := pullback.fst f g
  let pK := pullback.snd f g
  let S : ι → Set (Limits.pullback (C := Scheme) f g) := fun i =>
    ↑((I i).comap π).support
  have hconn : ∀ i, _root_.IsConnected (S i) := by
    intro i
    let I₂ := (I i).comap π
    have : GeometricallyConnected (I₂.subschemeι ≫ pK) :=
      geometricallyConnected_subscheme_comap_baseChange f g (I i) (hgeom i)
    let : Surjective (I₂.subschemeι ≫ pK) := inferInstance
    let : Nonempty I₂.subscheme := ⟨Classical.choose
      ((I₂.subschemeι ≫ pK).surjective (Classical.choice ‹Nonempty Z›))⟩
    let : ConnectedSpace I₂.subscheme :=
      GeometricallyConnected.connectedSpace_of_subsingleton (I₂.subschemeι ≫ pK)
    show _root_.IsConnected (↑I₂.support : Set (Limits.pullback (C := Scheme) f g))
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact isConnected_univ.image I₂.subschemeι.base
      I₂.subschemeι.continuous.continuousOn
  have hcover' : ∀ z : Limits.pullback (C := Scheme) f g, ∃ i, z ∈ S i := by
    intro z
    obtain ⟨i, hi⟩ := hcover (π.base z)
    refine ⟨i, ?_⟩
    show z ∈ (↑((I i).comap π).support : Set _)
    rw [Scheme.IdealSheafData.support_comap]
    exact hi
  exact natCard_connectedComponents_le_of_finite_cover_connected S hconn hcover'

private theorem natCard_connectedComponents_geometricFiber_le_of_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (y : Y) {ι : Type u} [Finite ι] (I : ι → (f.fiber y).IdealSheafData)
    (hgeom : ∀ i, GeometricallyConnected
      ((I i).subschemeι ≫ f.fiberToSpecResidueField y))
    (hcover : ∀ x : f.fiber y, ∃ i, x ∈ (I i).support) :
    Nat.card (_root_.ConnectedComponents (geometricFiber f y
      (SeparableClosure (Y.residueField y)))) ≤ Nat.card ι :=
  natCard_connectedComponents_pullback_le_of_cover
    (f.fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (SeparableClosure (Y.residueField y))))) I hgeom hcover

private noncomputable def connectedComponentSet
    {α : Type u} [TopologicalSpace α] (c : _root_.ConnectedComponents α) : Set α :=
  connectedComponent (Classical.choose (ConnectedComponents.surjective_coe c))

private theorem connectedComponentSet_eq_preimage
    {α : Type u} [TopologicalSpace α] (c : _root_.ConnectedComponents α) :
    connectedComponentSet c = ConnectedComponents.mk ⁻¹' {c} := by
  let x := Classical.choose (ConnectedComponents.surjective_coe c)
  have hx : ConnectedComponents.mk x = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  calc
    connectedComponentSet c = connectedComponent x := rfl
    _ = ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x} :=
      (connectedComponents_preimage_singleton (x := x)).symm
    _ = ConnectedComponents.mk ⁻¹' {c} := by rw [hx]

@[sga "3 VIA 2.1" "more general", sga "3 X 5.11.0" "more general"]
private theorem connectedComponentSet_isClosed
    {α : Type u} [TopologicalSpace α] (c : _root_.ConnectedComponents α) :
    IsClosed (connectedComponentSet c) := by
  rw [connectedComponentSet_eq_preimage]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

private lemma mem_connectedComponentSet_mk {α : Type u} [TopologicalSpace α] (x : α) :
    x ∈ connectedComponentSet (ConnectedComponents.mk x) := by
  rw [connectedComponentSet_eq_preimage]
  simp

private lemma mem_of_isGenericPoint_of_nonempty {α : Type*} [TopologicalSpace α] {η : α}
    (hη : IsGenericPoint η Set.univ) (U : Opens α) (hU : Nonempty U) : η ∈ U := by
  obtain ⟨z⟩ := hU
  exact (hη.mem_open_set_iff U.2).2 ⟨z.1, Set.mem_univ _, z.2⟩

private theorem geometricallyConnected_vanishingIdeal_connectedComponent
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (hfinite : (irreducibleComponents (f.fiber η)).Finite)
    (hgeom : ∀ Z : irreducibleComponents (f.fiber η),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal (X := f.fiber η)
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
          f.fiberToSpecResidueField η))
    (c : _root_.ConnectedComponents (f.fiber η)) :
    GeometricallyConnected
      ((Scheme.IdealSheafData.vanishingIdeal
        ⟨connectedComponentSet c, connectedComponentSet_isClosed c⟩).subschemeι ≫
        f.fiberToSpecResidueField η) := by
  obtain ⟨U, hU, hUconn⟩ := geometricallyConnected_connectedComponent
    (Y.residueField η) (f.fiber η) (f.fiberToSpecResidueField η) hfinite hgeom c
  have hUrange : Set.range U.ι = connectedComponentSet c := by
    rw [Scheme.Opens.range_ι, hU, ← connectedComponentSet_eq_preimage]
  exact geometricallyConnected_closedSubscheme_of_open_range
    (Y.residueField η) (f.fiberToSpecResidueField η) U _ hUrange hUconn

private theorem geometricallyConnected_fiber_of_geometricallyConnected_restrict
    {X Y : Scheme.{u}} (q : X ⟶ Y) (V : Y.Opens) (y : Y) (hy : y ∈ V)
    [GeometricallyConnected (q ∣_ V)] :
    GeometricallyConnected (q.fiberToSpecResidueField y) := by
  let y' : V.toScheme := ⟨y, hy⟩
  let hpb := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict q V).flip y'
  let : IsOpenImmersion V.ι := inferInstance
  let : IsIso (V.ι.stalkMap y') :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion V.ι)).2 y'
  let : IsIso (V.ι.residueFieldMap y') := inferInstance
  let eSpec := Scheme.Spec.mapIso (asIso (V.ι.residueFieldMap y')).op
  let : IsIso (Spec.map (V.ι.residueFieldMap y')) := eSpec.isIso_hom
  let p := pullback.map (q ∣_ V) (V.toScheme.fromSpecResidueField y') q
    (Y.fromSpecResidueField (V.ι y')) (q ⁻¹ᵁ V).ι
    (Spec.map (V.ι.residueFieldMap y')) V.ι
    (isPullback_morphismRestrict q V).flip.w.symm (by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField])
  let : IsIso p := hpb.isIso_fst_of_isIso
  let e : Arrow.mk ((q ∣_ V).fiberToSpecResidueField y') ≅
      Arrow.mk (q.fiberToSpecResidueField y) :=
    Arrow.isoMk (f := Arrow.mk ((q ∣_ V).fiberToSpecResidueField y'))
      (g := Arrow.mk (q.fiberToSpecResidueField y))
      (@asIso _ _ _ _ p hpb.isIso_fst_of_isIso)
      (@asIso _ _ _ _ (Spec.map (V.ι.residueFieldMap y')) eSpec.isIso_hom) hpb.w
  have hGeom : GeometricallyConnected ((q ∣_ V).fiberToSpecResidueField y') :=
    (GeometricallyConnected.iff_geometricallyConnected_fiber
      (f := q ∣_ V)).mp inferInstance y'
  rw [GeometricallyConnected.eq_geometrically] at hGeom ⊢
  exact (MorphismProperty.arrow_mk_iso_iff
    (P := geometrically (fun T : Scheme.{u} => ConnectedSpace T)) e).mp hGeom

private lemma geometricallyConnected_closure_subscheme_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (I : (f.fiber η).IdealSheafData) [QuasiCompact (f.fiberι η)]
    (hI : GeometricallyConnected (I.subschemeι ≫ f.fiberToSpecResidueField η)) :
    GeometricallyConnected
      (((I.map (f.fiberι η)).subschemeι ≫ f).fiberToSpecResidueField η) := by
  let J := I.map (f.fiberι η)
  have hJ : GeometricallyConnected
      ((J.comap (f.fiberι η)).subschemeι ≫ f.fiberToSpecResidueField η) :=
    geometricallyConnected_comap_map_of_isEmbedding (f.fiberι η)
      (f.fiberι η).isEmbedding I (Y.residueField η) (f.fiberToSpecResidueField η) hI
  exact (geometricallyConnected_subscheme_baseChange_iff f
    (Y.fromSpecResidueField η) J).mp hJ

private lemma quasiCompact_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (y : Y) :
    QuasiCompact (f.fiberι y) := by
  dsimp [Scheme.Hom.fiberι, Scheme.Hom.fiber]
  infer_instance

private noncomputable def genericClosedSubsetClosureIdeal
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (C : Set (f.fiber η)) (hC : IsClosed C) : X.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩).map (f.fiberι η)

private theorem exists_open_genericClosedSubsetClosure_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η Set.univ) (C : Set (f.fiber η)) (hC : IsClosed C)
    (hconn : GeometricallyConnected
      ((Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩).subschemeι ≫
        f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, Nonempty V ∧
      GeometricallyConnected
        (((genericClosedSubsetClosureIdeal f η C hC).subschemeι ≫ f) ∣_ V) := by
  let I := genericClosedSubsetClosureIdeal f η C hC
  let q := I.subschemeι ≫ f
  have := quasiCompact_fiberι f η
  have : LocallyOfFiniteType q := inferInstance
  have : QuasiCompact q := inferInstance
  let : GeometricallyConnected (q.fiberToSpecResidueField η) := by
    simpa [I, q, genericClosedSubsetClosureIdeal] using
      geometricallyConnected_closure_subscheme_fiber f η
        (Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩) hconn
  simpa [I, q] using geometricallyConnectedAfterShrinking q inferInstance
    inferInstance inferInstance η hη inferInstance

private theorem exists_open_fiber_covered_by_genericClosedSubsetClosures
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    {ι : Type u} (C : ι → Set (f.fiber η))
    (hcover : ∀ x : f.fiber η, ∃ i, x ∈ C i)
    (hclosed : ∀ i, IsClosed (C i)) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V → ∀ x : f.fiber y,
        ∃ i, f.fiberι y x ∈ (genericClosedSubsetClosureIdeal f η (C i)
          (hclosed i)).support := by
  obtain ⟨U, hUopen, hUnonempty, hnear⟩ :=
    exists_open_fiber_covered_by_closures f η hη C hcover
  have := quasiCompact_fiberι f η
  refine ⟨⟨U, hUopen⟩, hUnonempty.to_subtype, fun y hy x => ?_⟩
  obtain ⟨i, hi⟩ := hnear y hy x
  refine ⟨i, ?_⟩
  change f.fiberι y x ∈ closure (f.fiberι η '' C i) at hi
  show f.fiberι y x ∈
    ((Scheme.IdealSheafData.vanishingIdeal ⟨C i, hclosed i⟩).map
      (f.fiberι η)).support
  rw [Scheme.IdealSheafData.support_map]
  simpa using hi

private theorem exists_open_fiber_controlled_by_generic_components
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hgeom : ∀ Z : irreducibleComponents (f.fiber η),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal (X := f.fiber η)
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
          f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V →
        (∀ c : _root_.ConnectedComponents (f.fiber η),
          GeometricallyConnected
            (((genericClosedSubsetClosureIdeal f η
              (connectedComponentSet c) (connectedComponentSet_isClosed c)).subschemeι ≫
              f).fiberToSpecResidueField y)) ∧
        (∀ x : f.fiber y, ∃ c : _root_.ConnectedComponents (f.fiber η),
          f.fiberι y x ∈ (genericClosedSubsetClosureIdeal f η
            (connectedComponentSet c) (connectedComponentSet_isClosed c)).support) := by
  classical
  let C : _root_.ConnectedComponents (f.fiber η) → Set (f.fiber η) := connectedComponentSet
  have hclosed : ∀ c, IsClosed (C c) := connectedComponentSet_isClosed
  have hcover : ∀ x : f.fiber η, ∃ c, x ∈ C c :=
    fun x => ⟨ConnectedComponents.mk x, mem_connectedComponentSet_mk x⟩
  let : Finite (_root_.ConnectedComponents (f.fiber η)) := finiteConnectedComponents_fiber f η
  choose U hUne hUgeom using fun c =>
    exists_open_genericClosedSubsetClosure_geometricallyConnected f η hη (C c) (hclosed c)
      (geometricallyConnected_vanishingIdeal_connectedComponent f η
        (AlgebraicGeometry.finite_irreducibleComponents_fiber f η) hgeom c)
  obtain ⟨Ucover, hUcoverNe, hUcover⟩ :=
    exists_open_fiber_covered_by_genericClosedSubsetClosures f η hη C hcover hclosed
  have hηUcover : η ∈ Ucover := mem_of_isGenericPoint_of_nonempty hη Ucover hUcoverNe
  have hηU (c : _root_.ConnectedComponents (f.fiber η)) : η ∈ U c :=
    mem_of_isGenericPoint_of_nonempty hη (U c) (hUne c)
  let V : Y.Opens := Ucover ⊓ ⨅ c, U c
  have hηInf : η ∈ ((⨅ c, U c : Y.Opens) : Set Y) := by
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηU
  have hηV : η ∈ V := by
    show η ∈ (Ucover : Set Y) ∩ ((⨅ c, U c : Y.Opens) : Set Y)
    rw [Set.mem_inter_iff]
    exact ⟨hηUcover, hηInf⟩
  refine ⟨V, ⟨⟨η, hηV⟩⟩, ?_⟩
  intro y hy
  change y ∈ (Ucover : Set Y) ∩ ((⨅ c, U c : Y.Opens) : Set Y) at hy
  rw [Set.mem_inter_iff] at hy
  have hyInf : y ∈ ((⨅ c, U c : Y.Opens) : Set Y) := hy.2
  rw [TopologicalSpace.Opens.coe_iInf] at hyInf
  have hyU (c : _root_.ConnectedComponents (f.fiber η)) : y ∈ U c :=
    (Set.mem_iInter.mp hyInf) c
  refine ⟨fun c => ?_, hUcover y hy.1⟩
  have := hUgeom c
  exact geometricallyConnected_fiber_of_geometricallyConnected_restrict
    ((genericClosedSubsetClosureIdeal f η (C c) (hclosed c)).subschemeι ≫ f)
    (U c) y (hyU c)

private theorem natCard_connectedComponents_geometricFiber_generic_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hgeom : ∀ Z : irreducibleComponents (f.fiber η),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal (X := f.fiber η)
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
          f.fiberToSpecResidueField η))
    [Finite (_root_.ConnectedComponents (f.fiber η))]
    [Finite (_root_.ConnectedComponents
      (geometricFiber f η (SeparableClosure (Y.residueField η))))] :
    Nat.card (_root_.ConnectedComponents
        (geometricFiber f η (SeparableClosure (Y.residueField η)))) =
      Nat.card (_root_.ConnectedComponents (f.fiber η)) := by
  let Iη : _root_.ConnectedComponents (f.fiber η) → (f.fiber η).IdealSheafData := fun c =>
    Scheme.IdealSheafData.vanishingIdeal
      ⟨connectedComponentSet c, connectedComponentSet_isClosed c⟩
  have hupper := natCard_connectedComponents_pullback_le_of_cover
    (f.fiberToSpecResidueField η)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField η) (SeparableClosure (Y.residueField η))))) Iη
    (geometricallyConnected_vanishingIdeal_connectedComponent f η
      (AlgebraicGeometry.finite_irreducibleComponents_fiber f η) hgeom)
    (fun x => ⟨ConnectedComponents.mk x, mem_connectedComponentSet_mk x⟩)
  exact Nat.le_antisymm hupper (natCard_connectedComponents_fiber_le_geometricFiber f η _)

private theorem natCard_connectedComponents_geometricFiber_le_of_control
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (η y : Y)
    [Finite (_root_.ConnectedComponents (f.fiber η))]
    (hconn : ∀ c : _root_.ConnectedComponents (f.fiber η),
      GeometricallyConnected
        (((genericClosedSubsetClosureIdeal f η
          (connectedComponentSet c) (connectedComponentSet_isClosed c)).subschemeι ≫
          f).fiberToSpecResidueField y))
    (hcover : ∀ x : f.fiber y, ∃ c : _root_.ConnectedComponents (f.fiber η),
      f.fiberι y x ∈ (genericClosedSubsetClosureIdeal f η
        (connectedComponentSet c) (connectedComponentSet_isClosed c)).support) :
    Nat.card (_root_.ConnectedComponents (geometricFiber f y
      (SeparableClosure (Y.residueField y)))) ≤
      Nat.card (_root_.ConnectedComponents (f.fiber η)) := by
  let J : _root_.ConnectedComponents (f.fiber η) → X.IdealSheafData := fun c =>
    genericClosedSubsetClosureIdeal f η (connectedComponentSet c)
      (connectedComponentSet_isClosed c)
  have := quasiCompact_fiberι f y
  refine natCard_connectedComponents_geometricFiber_le_of_cover f y
    (fun c => (J c).comap (f.fiberι y))
    (fun c => (geometricallyConnected_subscheme_baseChange_iff f
      (Y.fromSpecResidueField y) (J c)).2 (hconn c)) fun x => ?_
  obtain ⟨c, hc⟩ := hcover x
  refine ⟨c, ?_⟩
  show x ∈ (((J c).comap (f.fiberι y)).support : Set (f.fiber y))
  rw [Scheme.IdealSheafData.support_comap]
  exact hc

private theorem exists_open_numGeometricConnectedComponents_eq_of_generic_components
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (η : Y) (hη : IsGenericPoint η Set.univ)
    (hgeom : ∀ Z : irreducibleComponents (f.fiber η),
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal (X := f.fiber η)
          ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
          f.fiberToSpecResidueField η)) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∃ n : ℕ∞, ∀ z : V, numGeometricConnectedComponents f z.1 = n := by
  classical
  let : Finite (_root_.ConnectedComponents (f.fiber η)) := finiteConnectedComponents_fiber f η
  let n := Nat.card (_root_.ConnectedComponents (f.fiber η))
  obtain ⟨U, hUne, hcontrol⟩ :=
    exists_open_fiber_controlled_by_generic_components f η hη hgeom
  obtain ⟨D, hDopen, hDne, hDlower⟩ :=
    exists_open_natCard_connectedComponents_fiber_ge f η hη n rfl
  have hηU : η ∈ U := mem_of_isGenericPoint_of_nonempty hη U hUne
  have hηD : η ∈ D :=
    mem_of_isGenericPoint_of_nonempty hη ⟨D, hDopen⟩ hDne.to_subtype
  let V : Y.Opens := ⟨(U : Set Y) ∩ D, U.2.inter hDopen⟩
  refine ⟨V, ⟨⟨η, hηU, hηD⟩⟩, numGeometricConnectedComponents f η, ?_⟩
  intro z
  let y := z.1
  have hctl := hcontrol y z.2.1
  let K := SeparableClosure (Y.residueField y)
  let : Finite (_root_.ConnectedComponents (f.fiber y)) := finiteConnectedComponents_fiber f y
  let : Finite (_root_.ConnectedComponents (geometricFiber f y K)) :=
    finiteConnectedComponents_geometricFiber f y K
  let Kη := SeparableClosure (Y.residueField η)
  let : Finite (_root_.ConnectedComponents (geometricFiber f η Kη)) :=
    finiteConnectedComponents_geometricFiber f η Kη
  have hnat : Nat.card (_root_.ConnectedComponents (geometricFiber f y K)) = n :=
    Nat.le_antisymm
      (natCard_connectedComponents_geometricFiber_le_of_control f η y hctl.1 hctl.2)
      ((hDlower y z.2.2).trans (natCard_connectedComponents_fiber_le_geometricFiber f y K))
  unfold numGeometricConnectedComponents
  rw [ENat.card_eq_coe_natCard, ENat.card_eq_coe_natCard]
  exact_mod_cast hnat.trans
    (natCard_connectedComponents_geometricFiber_generic_eq f η hgeom).symm

private theorem exists_open_numGeometricConnectedComponents_eq_of_irreducible_base
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ V : Y.Opens, Nonempty V ∧
      ∃ n : ℕ∞, ∀ z : V, numGeometricConnectedComponents f z.1 = n := by
  classical
  obtain ⟨V, hVne, Y', g, hgSurj, hgFinite, hgEtale, hY'irr, hY'affine, hrest⟩ :=
    exists_nonemptyOpen_finiteEtale_cover_geometricallyIrreducible_genericFiber f
  dsimp at hrest
  obtain ⟨hpb, hg'Surj, hg'Finite, hg'Etale, hgeom⟩ := hrest
  let X_V := pullback V.ι f
  let fV : X_V ⟶ V.toScheme := pullback.fst V.ι f
  let X' := pullback (g ≫ V.ι) f
  let f' : X' ⟶ Y' := pullback.fst (g ≫ V.ι) f
  let g' : X' ⟶ X_V := pullback.lift
    (pullback.fst (g ≫ V.ι) f ≫ g)
    (pullback.snd (g ≫ V.ι) f) (by
      rw [Category.assoc]
      exact pullback.condition)
  have : LocallyOfFiniteType fV := by infer_instance
  have : QuasiCompact fV := by infer_instance
  have : LocallyOfFiniteType f' := by infer_instance
  have : QuasiCompact f' := by infer_instance
  let η' : Y' := genericPoint Y'
  have hη' : IsGenericPoint η' Set.univ := genericPoint_spec Y'
  obtain ⟨V', hV'ne, n, hconst⟩ :=
    exists_open_numGeometricConnectedComponents_eq_of_generic_components f' η' hη'
      (hgeom η' hη')
  have hcountBase : numGeometricConnectedComponents f' =
      numGeometricConnectedComponents fV ∘ g :=
    numGeometricConnectedComponents_eq_of_isPullback
      fV f' g' g hpb
  have hcountRestrict : numGeometricConnectedComponents fV =
      numGeometricConnectedComponents f ∘ V.ι :=
    numGeometricConnectedComponents_eq_of_isPullback
      f fV (pullback.snd V.ι f) V.ι (IsPullback.of_hasPullback V.ι f).flip
  let Wset : Set Y := V.ι '' (g '' (V' : Set Y'))
  have hWopen : IsOpen Wset := V.ι.isOpenMap _ (g.isOpenMap _ V'.2)
  let W : Y.Opens := ⟨Wset, hWopen⟩
  have hWne : Nonempty W := by
    obtain ⟨z, hz⟩ := hV'ne
    exact ⟨⟨V.ι (g z), ⟨g z, ⟨z, hz, rfl⟩, rfl⟩⟩⟩
  refine ⟨W, hWne, n, ?_⟩
  intro z
  obtain ⟨v, hv, hVz⟩ := z.2
  obtain ⟨z', hz', hgv⟩ := hv
  calc
    numGeometricConnectedComponents f z.1 =
        numGeometricConnectedComponents f (V.ι (g z')) := by rw [← hVz, hgv]
    _ = numGeometricConnectedComponents fV (g z') := (congrFun hcountRestrict (g z')).symm
    _ = numGeometricConnectedComponents f' z' := (congrFun hcountBase z').symm
    _ = n := hconst ⟨z', hz'⟩

/-- **Stacks Project, Tag 055H.** For a finite type morphism of schemes, the number of
geometric connected components of the fibres is constant on some nonempty open subset of the
closure of any prescribed point of the base. -/
@[stacks 055H]
theorem exists_open_numGeometricConnectedComponents_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    ∃ V : TopologicalSpace.Opens (↑(closure ({y} : Set Y))), Nonempty V ∧
      ∃ n : ℕ∞, ∀ z : V, numGeometricConnectedComponents f z.1.1 = n := by
  classical
  let S := closure ({y} : Set Y)
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨S, isClosed_closure⟩ : Closeds Y)
  let Z := I.subscheme
  let i := I.subschemeι
  have hrange : Set.range i.base = S := by
    rw [I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let h : Z ≃ₜ S :=
    i.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : IrreducibleSpace S :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y)).closure
  have : IrreducibleSpace Z := h.irreducibleSpace_iff.mpr inferInstance
  let fZ := pullback.snd f i
  have : LocallyOfFiniteType fZ := inferInstance
  have : QuasiCompact fZ := inferInstance
  obtain ⟨U, hUne, n, hconst⟩ :=
    exists_open_numGeometricConnectedComponents_eq_of_irreducible_base fZ
  let V : TopologicalSpace.Opens S := h.opensCongr U
  refine ⟨V, ?_, n, ?_⟩
  · obtain ⟨z⟩ := hUne
    exact ⟨⟨h z.1, by simpa [V] using z.2⟩⟩
  intro z
  let zZ : Z := h.symm z.1
  have hzZ : zZ ∈ U := by simpa [V] using z.2
  have hzEq : i.base zZ = z.1.1 := by
    have hval : (h zZ).1 = i.base zZ := by
      simp [h, Topology.IsEmbedding.toHomeomorph, Homeomorph.setCongr]
    exact hval.symm.trans (congrArg Subtype.val (h.apply_symm_apply z.1))
  have hpull := congrFun (numGeometricConnectedComponents_eq_of_isPullback f fZ
    (pullback.fst f i) i (IsPullback.of_hasPullback f i)) zZ
  calc
    numGeometricConnectedComponents f z.1.1 =
        numGeometricConnectedComponents f (i.base zZ) := by rw [hzEq]
    _ = numGeometricConnectedComponents fZ zZ := by simpa using hpull.symm
    _ = n := hconst ⟨zZ, hzZ⟩

end AlgebraicGeometry

end
