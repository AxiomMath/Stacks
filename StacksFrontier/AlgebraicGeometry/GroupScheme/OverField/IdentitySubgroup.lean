module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Irreducible
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion

/-!
# The identity component of a group scheme over a field

A group scheme over a field has a canonical closed subgroup scheme supported on the connected
component of its identity.  Its inclusion is flat, and the subgroup is geometrically irreducible
and quasi-compact.

## Main definitions

* `AlgebraicGeometry.identityComponent`: the closed subgroup scheme of the identity component.

## Main results

* `AlgebraicGeometry.identityComponent_flat`: its inclusion is flat.
* `AlgebraicGeometry.identityComponent_range`: its underlying space is the identity component.
* `AlgebraicGeometry.identityComponent_geometricallyIrreducible`: it is geometrically
  irreducible.
* `AlgebraicGeometry.identityComponent_compactSpace`: it is quasi-compact.
* `AlgebraicGeometry.identityComponent_unique`: every flat closed subgroup scheme supported on
  the identity component is uniquely isomorphic to it over `G`.

## References

* [Stacks Project, Tag 0B7R](https://stacks.math.columbia.edu/tag/0B7R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u


private theorem flat_ker_subschemeι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hClosed : IsClosedImmersion f] [hFlat : Flat f] : Flat f.ker.subschemeι := by
  let A : MorphismProperty.Over @IsClosedImmersion ⊤ Y :=
    MorphismProperty.Over.mk ⊤ f hClosed
  let : Category (MorphismProperty.Over @IsClosedImmersion ⊤ Y) := by
    show Category (MorphismProperty.Comma (Functor.id Scheme)
      (Functor.fromPUnit.{0} Y) @IsClosedImmersion ⊤ ⊤)
    exact @MorphismProperty.Comma.instCategory Scheme inferInstance
      (Discrete PUnit.{1}) inferInstance Scheme inferInstance (Functor.id Scheme)
      (Functor.fromPUnit.{0} Y)
      @IsClosedImmersion ⊤ ⊤ inferInstance inferInstance
  let E := IsClosedImmersion.overEquivIdealSheafData Y
  let hunit := E.unitIso.app (Opposite.op A)
  let e := Iso.unop hunit
  let eOver := (MorphismProperty.Over.forget @IsClosedImmersion ⊤ Y).mapIso e
  let eScheme := (Over.forget Y).mapIso eOver
  have hfac : eScheme.hom ≫ f = f.ker.subschemeι := by
    show eOver.hom.left ≫ f = f.ker.subschemeι
    exact Over.w eOver.hom
  rw [← hfac]
  exact @Flat.comp _ _ _ eScheme.hom f inferInstance hFlat

private theorem ker_eq_of_flat_closedImmersion_range_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsClosedImmersion f] [IsClosedImmersion g]
    [Flat f] [Flat g] (h : Set.range f = Set.range g) : f.ker = g.ker := by
  refine (AlgebraicGeometry.support_bijOn_flat_closedImmersions Z).injOn (flat_ker_subschemeι f)
    (flat_ker_subschemeι g) (TopologicalSpace.Closeds.ext ?_)
  rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker, h]

private theorem grpHom_of_factor {C : Type u} [Category C]
    [CartesianMonoidalCategory C] {A B T : Grp C}
    (i : B ⟶ T) (j : A ⟶ T) [Mono i.hom.hom]
    (f : A.X ⟶ B.X) (hf : f ≫ i.hom.hom = j.hom.hom) :
    ∃ φ : A ⟶ B, φ.hom.hom = f ∧ φ ≫ i = j := by
  let φ : A ⟶ B := Grp.homMk'' f (one_f := by
    apply (cancel_mono i.hom.hom).mp
    calc
      (η[A.X] ≫ f) ≫ i.hom.hom = η[A.X] ≫ (f ≫ i.hom.hom) := by
        simp only [Category.assoc]
      _ = η[A.X] ≫ j.hom.hom := by rw [hf]
      _ = η[T.X] := IsMonHom.one_hom j.hom.hom
      _ = η[B.X] ≫ i.hom.hom := (IsMonHom.one_hom i.hom.hom).symm)
    (mul_f := by
      apply (cancel_mono i.hom.hom).mp
      calc
        (μ[A.X] ≫ f) ≫ i.hom.hom = μ[A.X] ≫ (f ≫ i.hom.hom) := by
          simp only [Category.assoc]
        _ = μ[A.X] ≫ j.hom.hom := by rw [hf]
        _ = (j.hom.hom ⊗ₘ j.hom.hom) ≫ μ[T.X] :=
          IsMonHom.mul_hom j.hom.hom
        _ = (f ≫ i.hom.hom ⊗ₘ f ≫ i.hom.hom) ≫ μ[T.X] := by rw [hf]
        _ = (f ⊗ₘ f) ≫ (i.hom.hom ⊗ₘ i.hom.hom) ≫ μ[T.X] := by
          rw [← tensorHom_comp_tensorHom]
          simp only [Category.assoc]
        _ = (f ⊗ₘ f) ≫ (μ[B.X] ≫ i.hom.hom) := by
          rw [← IsMonHom.mul_hom i.hom.hom]
        _ = ((f ⊗ₘ f) ≫ μ[B.X]) ≫ i.hom.hom := by
          simp only [Category.assoc])
  exact ⟨φ, rfl, Grp.hom_ext _ _ hf⟩

private lemma identityConnectedComponent_stableUnderGeneralization
    {X : Type u} [TopologicalSpace X] (x : X) :
    StableUnderGeneralization (connectedComponent x) := by
  intro y z hyz hz
  rw [← connectedComponent_eq_iff_mem.mpr hz, connectedComponent_eq_iff_mem.mpr
    (irreducibleComponent_subset_connectedComponent
      ((isClosed_irreducibleComponent (x := z)).closure_subset_iff.mpr
        (by simp [mem_irreducibleComponent]) hyz.mem_closure))]
  exact mem_connectedComponent

private theorem connectedSpace_of_range_connectedComponent {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Topology.IsClosedEmbedding f) (y : Y)
    (h : Set.range f = connectedComponent y) : ConnectedSpace X := by
  have hpre : _root_.IsPreconnected (Set.univ : Set X) := by
    apply hf.isInducing.isPreconnected_image.mp
    rw [Set.image_univ, h]
    exact isPreconnected_connectedComponent
  obtain ⟨x, -⟩ : y ∈ Set.range f := h ▸ mem_connectedComponent
  have : PreconnectedSpace X := ⟨hpre⟩
  exact ⟨⟨x⟩⟩

private theorem exists_flat_identityComponent_ideal (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    ∃ I : G.X.left.IdealSheafData,
      Flat I.subschemeι ∧
        I.support = ⟨connectedComponent (identityPoint k G),
          isClosed_connectedComponent⟩ := by
  let Z : TopologicalSpace.Closeds G.X.left :=
    ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩
  have hstable : StableUnderGeneralization (Z : Set G.X.left) :=
    identityConnectedComponent_stableUnderGeneralization (identityPoint k G)
  obtain ⟨I, hI, hIZ⟩ :=
    (AlgebraicGeometry.support_bijOn_flat_closedImmersions G.X.left).surjOn hstable
  exact ⟨I, hI, hIZ⟩

/-- A morphism in `Over (Spec k)` into `G` whose range lies in the support of a flat closed
subscheme factors through it. -/
private theorem exists_factor_of_range_subset_support (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hFlat : Flat I.subschemeι) (X : Over (Spec (.of k))) (f : X ⟶ G.X)
    (hf : Set.range f.left ⊆ I.support) :
    ∃ m : X ⟶ Over.mk (I.subschemeι ≫ G.X.hom), m ≫ Over.homMk I.subschemeι = f := by
  let := hFlat
  obtain ⟨m₀, hm₀, -⟩ := AlgebraicGeometry.existsUnique_lift_of_flat_closedImmersion I f.left hf
  have hw : m₀ ≫ (I.subschemeι ≫ G.X.hom) = X.hom := by
    rw [← Category.assoc, hm₀]
    exact f.w
  exact ⟨Over.homMk m₀ hw, Over.OverMorphism.ext hm₀⟩

private theorem exists_identityUnit_factor (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hFlat : Flat I.subschemeι)
    (hSupport : I.support =
      ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩) :
    ∃ e : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk (I.subschemeι ≫ G.X.hom),
      e ≫ Over.homMk I.subschemeι = η[G.X] := by
  have hrange : Set.range (η[G.X]).left ⊆ I.support := by
    rw [hSupport]
    rintro _ ⟨s, rfl⟩
    show (η[G.X]).left s ∈ connectedComponent
      (identityPoint k G)
    have : Subsingleton (↥((𝟙_ (Over (Spec (.of k)))).left)) := by
      show Subsingleton (PrimeSpectrum k)
      exact Ring.KrullDimLE.subsingleton_primeSpectrum k
    obtain rfl : s = (default : Spec (.of k)) := Subsingleton.elim _ _
    exact mem_connectedComponent
  exact exists_factor_of_range_subset_support k G I hFlat _ η[G.X] hrange

private theorem idealSubscheme_connected (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hSupport : I.support =
      ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩) :
    ConnectedSpace I.subscheme := by
  apply connectedSpace_of_range_connectedComponent I.subschemeι
    (IsClosedImmersion.isClosedEmbedding _) (identityPoint k G)
  rw [I.range_subschemeι, hSupport]
  rfl

@[sga "3 IX 5.5" "more general"]
private theorem idealSubscheme_geometricallyConnected (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hSupport : I.support =
      ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩)
    (e : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk (I.subschemeι ≫ G.X.hom)) :
    GeometricallyConnected (I.subschemeι ≫ G.X.hom) := by
  have := idealSubscheme_connected k G I hSupport
  exact geometricallyConnected_of_connectedSpace_of_section _ e.left e.w

private theorem identityProduct_connected (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hSupport : I.support =
      ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩)
    (e : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk (I.subschemeι ≫ G.X.hom)) :
    ConnectedSpace (MonoidalCategoryStruct.tensorObj
      (Over.mk (I.subschemeι ≫ G.X.hom)) (Over.mk (I.subschemeι ≫ G.X.hom))).left := by
  let p := I.subschemeι ≫ G.X.hom
  let : ConnectedSpace I.subscheme := idealSubscheme_connected k G I hSupport
  let : GeometricallyConnected p := idealSubscheme_geometricallyConnected k G I hSupport e
  let : UniversallyOpen p := by infer_instance
  let : GeometricallyConnected (pullback.fst p p) := inferInstance
  have : GeometricallyConnected
      (MonoidalCategoryStruct.tensorObj (Over.mk p) (Over.mk p)).hom := by
    simpa [Over.tensorObj_hom] using GeometricallyConnected.comp (pullback.fst p p) p
  exact GeometricallyConnected.connectedSpace_of_subsingleton
    (MonoidalCategoryStruct.tensorObj (Over.mk p) (Over.mk p)).hom

private theorem exists_identityInverse_factor (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hFlat : Flat I.subschemeι)
    (hSupport : I.support =
      ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩) :
    ∃ i : Over.mk (I.subschemeι ≫ G.X.hom) ⟶ Over.mk (I.subschemeι ≫ G.X.hom),
      i ≫ Over.homMk I.subschemeι = Over.homMk I.subschemeι ≫ ι[G.X] := by
  let j : Over.mk (I.subschemeι ≫ G.X.hom) ⟶ G.X := Over.homMk I.subschemeι
  have hinv : (ι[G.X]).left (identityPoint k G) = identityPoint k G := by
    have hp := congrArg (fun f => f.left (IsLocalRing.closedPoint k))
      (show η[G.X] ≫ ι[G.X] = η[G.X] by simp)
    change (ι[G.X]).left ((η[G.X]).left (IsLocalRing.closedPoint k)) =
      (η[G.X]).left (IsLocalRing.closedPoint k) at hp
    have hpoint : (default : Spec (.of k)) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    simpa [identityPoint, hpoint] using hp
  have himage := Continuous.image_connectedComponent_subset
    (ι[G.X]).left.continuous (identityPoint k G)
  have hrange : Set.range (j ≫ ι[G.X]).left ⊆ I.support := by
    rw [hSupport]
    rintro _ ⟨x, rfl⟩
    show (ι[G.X]).left (I.subschemeι x) ∈
      connectedComponent (identityPoint k G)
    have hxI : I.subschemeι x ∈ (I.support : Set G.X.left) := by
      rw [← I.range_subschemeι]
      exact ⟨x, rfl⟩
    have hx : I.subschemeι x ∈
        connectedComponent (identityPoint k G) := by
      simpa [hSupport] using hxI
    have hy' : (ι[G.X]).left (I.subschemeι x) ∈
        connectedComponent ((ι[G.X]).left (identityPoint k G)) :=
      himage ⟨I.subschemeι x, hx, rfl⟩
    simpa [hinv] using hy'
  exact exists_factor_of_range_subset_support k G I hFlat _ (j ≫ ι[G.X]) hrange

private theorem exists_identityMul_factor (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) (I : G.X.left.IdealSheafData)
    (hFlat : Flat I.subschemeι)
    (hSupport : I.support =
      ⟨connectedComponent (identityPoint k G), isClosed_connectedComponent⟩)
    (e : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk (I.subschemeι ≫ G.X.hom))
    (he : e ≫ Over.homMk I.subschemeι = η[G.X]) :
    ∃ m : MonoidalCategoryStruct.tensorObj
      (Over.mk (I.subschemeι ≫ G.X.hom)) (Over.mk (I.subschemeι ≫ G.X.hom)) ⟶
      Over.mk (I.subschemeι ≫ G.X.hom),
      m ≫ Over.homMk I.subschemeι =
        ((Over.homMk I.subschemeι) ⊗ₘ (Over.homMk I.subschemeι)) ≫ μ[G.X] := by
  let H : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ G.X.hom)
  let j : H ⟶ G.X := Over.homMk I.subschemeι
  let D := MonoidalCategoryStruct.tensorObj H H
  let g : D ⟶ G.X := (j ⊗ₘ j) ≫ μ[G.X]
  let u : Over.mk (𝟙 (Spec (.of k))) ⟶ D :=
    (MonoidalCategoryStruct.leftUnitor (Over.mk (𝟙 (Spec (.of k))))).inv ≫ (e ⊗ₘ e)
  let : ConnectedSpace D.left := identityProduct_connected k G I hSupport e
  have hcomp := tensorHom_comp_tensorHom e e j j
  have hu : u ≫ g = η[G.X] := by
    dsimp [u, g, D]
    simp only [Category.assoc]
    rw [← Category.assoc (e ⊗ₘ e) (j ⊗ₘ j) μ[G.X], hcomp, he, MonObj.one_mul_hom]
    simp
  have hpoint : identityPoint k G ∈ Set.range g.left := by
    let x : Spec (.of k) := default
    refine ⟨u.left x, ?_⟩
    have hp := congrArg (fun f => f.left x) hu
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hp
    simpa [identityPoint] using hp
  have hrange : Set.range g.left ⊆ I.support := by
    rw [hSupport]
    have hconn : _root_.IsConnected (Set.range g.left) := by
      rw [← Set.image_univ]
      exact isConnected_univ.image g.left g.left.continuous.continuousOn
    exact hconn.subset_connectedComponent hpoint
  exact exists_factor_of_range_subset_support k G I hFlat D g hrange

/-- A group scheme over a field has a flat closed subgroup scheme whose support is the
connected component of its identity. -/
@[sga "3 VIA 2.6.5" "(i), (i)(b)"]
theorem exists_identityComponent_subgroup (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    ∃ K : ClosedSubgroupScheme G,
      Set.range K.ι.hom.hom.left =
        connectedComponent (identityPoint k G) ∧
      Flat K.ι.hom.hom.left := by
  obtain ⟨I, hFlat, hSupport⟩ := exists_flat_identityComponent_ideal k G
  let H : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ G.X.hom)
  let j : H ⟶ G.X := Over.homMk I.subschemeι
  let : IsClosedImmersion j.left := by
    show IsClosedImmersion I.subschemeι
    infer_instance
  obtain ⟨e, he⟩ := exists_identityUnit_factor k G I hFlat hSupport
  have hm := exists_identityMul_factor k G I hFlat hSupport e he
  obtain ⟨i, hi⟩ := exists_identityInverse_factor k G I hFlat hSupport
  obtain ⟨K, eK, hfactor⟩ :=
    (isClosedSubgroupScheme_iff_factor G j).mpr ⟨⟨e, he⟩, hm, ⟨i, hi⟩⟩
  have hfactor' : j.left = eK.hom.left ≫ K.ι.hom.hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left hfactor
  let : IsIso eK.hom := inferInstance
  let : IsIso eK.hom.left := ⟨⟨eK.inv.left,
    by simp,
    by simp⟩⟩
  have hsurj : Function.Surjective eK.hom.left := by
    intro z
    refine ⟨eK.inv.left z, ?_⟩
    have hz := congrArg (fun f => f.left.base z) eK.inv_hom_id
    simpa only [Over.comp_left, Scheme.Hom.comp_base, TopCat.comp_app,
      Over.id_left, Scheme.Hom.id_base, CategoryTheory.id_apply] using hz
  have hrangeIso : Set.range K.ι.hom.hom.left = Set.range j.left := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj z
      refine ⟨y, ?_⟩
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
        congrArg (fun f => f.left y) hfactor
    · rintro ⟨y, rfl⟩
      refine ⟨eK.hom.left y, ?_⟩
      have h := congrArg (fun f => f.left y) hfactor
      simpa only [Over.comp_left, Scheme.Hom.comp_apply] using h.symm
  have hrangeJ : Set.range j.left = connectedComponent
      (identityPoint k G) := by
    show Set.range I.subschemeι = _
    rw [I.range_subschemeι, hSupport]
    rfl
  let : IsIso eK.inv.left := ⟨⟨eK.hom.left,
    by simp,
    by simp⟩⟩
  let : Flat eK.inv.left := inferInstance
  let : Flat j.left := hFlat
  have hflatK : Flat K.ι.hom.hom.left := by
    have heq : eK.inv.left ≫ j.left = K.ι.hom.hom.left := by
      rw [hfactor', ← Category.assoc]
      simp [← Over.comp_left]
    rw [← heq]
    infer_instance
  exact ⟨K, hrangeIso.trans hrangeJ, hflatK⟩

/-- The canonical closed subgroup scheme whose support is the connected component of
the identity of `G`. -/
@[stacks 0B7R "construction",
  sga "3 VIA 2.6.5" "(i) existence of G^0",
  sga "6 XIII 4.1" "G^0 over a field", ega "IV 15.6.10", sga "3 VIA 2.3"]
noncomputable def identityComponent (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) : ClosedSubgroupScheme G :=
  Classical.choose (exists_identityComponent_subgroup k G)

private theorem identityComponent_carrier_connected (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    ConnectedSpace (identityComponent k G).carrier.X.left := by
  let K := identityComponent k G
  let : IsClosedImmersion K.ι.hom.hom.left := K.isClosedImmersion
  apply connectedSpace_of_range_connectedComponent K.ι.hom.hom.left
    (IsClosedImmersion.isClosedEmbedding _) (identityPoint k G)
  exact (Classical.choose_spec (exists_identityComponent_subgroup k G)).1

@[ega "IV 4.5.14" "Rational-point case",
  sga "3 IX 5.5" "more general",
  sga "3 VIA 2.1.1" "special case",
  sga "3 VIB 10.9" "special case",
  sga "3 VIB 3.3"]
private theorem identityComponent_geometricallyConnected (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    GeometricallyConnected (identityComponent k G).carrier.X.hom := by
  let H := (identityComponent k G).carrier.X
  let p := H.hom
  let : ConnectedSpace H.left := identityComponent_carrier_connected k G
  exact geometricallyConnected_of_connectedSpace_of_section p (η[H]).left (by
    simpa only [Over.tensorUnit_hom] using Over.w (η[H]))

@[sga "3 VIA 2.4" "(i), special case"]
private theorem identityComponent_irreducibleSpace (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    IrreducibleSpace (identityComponent k G).carrier.X.left := by
  let : ConnectedSpace (identityComponent k G).carrier.X.left :=
    identityComponent_carrier_connected k G
  exact irreducibleSpace_of_connectedSpace
    (identityComponent k G).carrier.X

/-- The inclusion of the identity component is flat. -/
@[stacks 0B7R "part (1): flatness", sga "3 VIA 2.6.5" "(i)(b) flatness"]
theorem identityComponent_flat (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    Flat (identityComponent k G).ι.hom.hom.left :=
  (Classical.choose_spec (exists_identityComponent_subgroup k G)).2

/-- The underlying set of the identity subgroup is the connected component of the identity. -/
@[stacks 0B7R "part (2): support"]
theorem identityComponent_range (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    Set.range (identityComponent k G).ι.hom.hom.left =
      connectedComponent (identityPoint k G) :=
  (Classical.choose_spec (exists_identityComponent_subgroup k G)).1

/-- The identity component is geometrically irreducible over the field. -/
@[stacks 0B7R "part (3): geometric irreducibility",
  ega "IV 15.6.10" "partial",
  sga "3 VIA 2.4" "(i), special case",
  sga "3 VIA 2.6.2",
  sga "3 VIA 2.6.5"]
theorem identityComponent_geometricallyIrreducible (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    GeometricallyIrreducible (identityComponent k G).carrier.X.hom := by
  rw [GeometricallyIrreducible.eq_geometrically]
  apply (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme => IrreducibleSpace X)).2
  intro K inst y
  let H := (identityComponent k G).carrier.X
  let : GrpObj (Over.mk H.hom) := by
    show GrpObj H
    exact (identityComponent k G).carrier.grp
  let : GeometricallyConnected H.hom := identityComponent_geometricallyConnected k G
  let T := Limits.pullback H.hom y
  let q := Limits.pullback.snd H.hom y
  let : GeometricallyConnected q := inferInstance
  let : GrpObj (Over.mk q) := Over.grpObjMkPullbackSnd
  let : ConnectedSpace (Over.mk q).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton q
  exact irreducibleSpace_of_connectedSpace
    (Over.mk q)

/-- The identity component is quasi-compact. -/
@[stacks 0B7R "part (4): quasi-compactness",
  sga "3 VIA 2.6.2" "quasi-compactness",
  sga "3 VIA 2.6.5" "(ii) quasi-compact",
  sga "3 VIA 2.4" "(ii), base field",
  sga "3 VIB 3.9" "special case"]
theorem identityComponent_compactSpace (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) :
    CompactSpace (identityComponent k G).carrier.X.left := by
  let : IrreducibleSpace (identityComponent k G).carrier.X.left :=
    identityComponent_irreducibleSpace k G
  infer_instance

/-- Any flat closed subgroup scheme supported on the identity component is uniquely
isomorphic to the identity component over `G`. -/
@[stacks 0B7R "canonicality"]
theorem identityComponent_unique (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k))))
    (H : ClosedSubgroupScheme G)
    [Flat H.ι.hom.hom.left]
    (hH : Set.range H.ι.hom.hom.left =
      connectedComponent (identityPoint k G)) :
    ∃! φ : H.carrier ≅ (identityComponent k G).carrier,
      φ.hom ≫ (identityComponent k G).ι = H.ι := by
  let K := identityComponent k G
  let iH := H.ι.hom.hom.left
  let iK := K.ι.hom.hom.left
  let : IsClosedImmersion iH := H.isClosedImmersion
  let : IsClosedImmersion iK := K.isClosedImmersion
  let : Flat iH := inferInstance
  let : Flat iK := identityComponent_flat k G
  have hker : iH.ker = iK.ker :=
    ker_eq_of_flat_closedImmersion_range_eq iH iK
      (hH.trans (identityComponent_range k G).symm)
  have hfacS : IsClosedImmersion.lift iK iH hker.symm.le ≫ iK = iH :=
    IsClosedImmersion.lift_fac iK iH hker.symm.le
  let fS : H.carrier.X.left ⟶ K.carrier.X.left :=
    IsClosedImmersion.lift iK iH hker.symm.le
  let : IsIso fS := IsClosedImmersion.isIso_of_ker_eq iH iK fS hfacS hker
  have hfbase : fS ≫ K.carrier.X.hom = H.carrier.X.hom := by
    rw [← K.ι.hom.hom.w, ← Category.assoc, hfacS, H.ι.hom.hom.w]
  let f : H.carrier.X ⟶ K.carrier.X := Over.homMk fS hfbase
  have hf : f ≫ K.ι.hom.hom = H.ι.hom.hom := Over.OverMorphism.ext hfacS
  let : Mono iK :=
    (IsClosedImmersion.iff_isFinite_and_mono iK).mp K.isClosedImmersion |>.2
  let : Mono K.ι.hom.hom := Over.mono_of_mono_left K.ι.hom.hom
  let : Mono iH :=
    (IsClosedImmersion.iff_isFinite_and_mono iH).mp H.isClosedImmersion |>.2
  let : Mono H.ι.hom.hom := Over.mono_of_mono_left H.ι.hom.hom
  obtain ⟨φ, hφ, hφfac⟩ := grpHom_of_factor K.ι H.ι f hf
  let fInvS : K.carrier.X.left ⟶ H.carrier.X.left := inv fS
  have hfInvbase : fInvS ≫ H.carrier.X.hom = K.carrier.X.hom := by
    rw [← hfbase]
    simp [fInvS]
  let fInv : K.carrier.X ⟶ H.carrier.X := Over.homMk fInvS hfInvbase
  have hfInv : fInv ≫ H.ι.hom.hom = K.ι.hom.hom := by
    apply Over.OverMorphism.ext
    calc
      fInvS ≫ iH = fInvS ≫ (fS ≫ iK) := by rw [hfacS]
      _ = iK := by simp [fInvS]
  obtain ⟨ψ, hψ, hψfac⟩ := grpHom_of_factor H.ι K.ι fInv hfInv
  let e : H.carrier ≅ K.carrier := {
    hom := φ
    inv := ψ
    hom_inv_id := by
      apply Grp.hom_ext
      rw [Grp.comp_hom_hom, hφ, hψ, Grp.id_hom_hom]
      apply Over.OverMorphism.ext
      show fS ≫ fInvS = 𝟙 _
      exact IsIso.hom_inv_id fS
    inv_hom_id := by
      apply Grp.hom_ext
      rw [Grp.comp_hom_hom, hψ, hφ, Grp.id_hom_hom]
      apply Over.OverMorphism.ext
      show fInvS ≫ fS = 𝟙 _
      exact IsIso.inv_hom_id fS
  }
  refine ⟨e, hφfac, fun e' he' => ?_⟩
  apply Iso.ext
  apply Grp.hom_ext
  apply (cancel_mono K.ι.hom.hom).mp
  simpa only [Grp.comp_hom_hom] using
    congrArg (fun q : H.carrier ⟶ G => q.hom.hom) (he'.trans hφfac.symm)

end AlgebraicGeometry

end
