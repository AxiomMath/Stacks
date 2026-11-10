module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.SmoothBranches
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchConnected
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversallyOpen.Criteria
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchEtaleCriterion

/-!
# Universal openness from dominance of the irreducible components

A locally quasi-finite morphism to a geometrically unibranch, locally Noetherian scheme is
universally open as soon as every irreducible component of its source dominates an irreducible
component of its target.

## Main results

* `AlgebraicGeometry.universallyOpen_of_locallyQuasiFinite_of_dominant_components` is the
  criterion.

## Implementation notes

By the affine-space criterion for universal openness it suffices to see that every
`𝔸ⁿ × X ⟶ 𝔸ⁿ × Y` is open, and since that morphism is locally quasi-finite over a locally
Noetherian base it is enough that it lifts generalizations. Affine space over a geometrically
unibranch scheme is again geometrically unibranch because its structure morphism is smooth and
smooth morphisms preserve the number of geometric branches; and the components of affine space
over a scheme correspond to the components of the scheme, so the componentwise dominance
hypothesis is also inherited.

Lifting a generalization `y' ⤳ y` along such a morphism is done at a point `x` over `y` by
passing to an elementary étale neighbourhood `(V, v)` of `y` carrying an open `U` of the base
change which is finite over `V` with a single point `u` over `v` mapping to `x`. An irreducible
component of `U` through `u` maps onto an irreducible component of `V` through `v`, which is
unique by geometric unibranchness, and that component contains a generalization of `v` over `y'`;
its preimage in `U` provides the required generalization of `x`.

Dominance of a source component over a target component is expressed as the closure of its image
being that component.

## References

* [Stacks Project, Tag 0F32](https://stacks.math.columbia.edu/tag/0F32)
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The closure of the image of a set is the closure of the image of its generic point. -/
@[ega "I 6.5.5" "more general"]
private lemma closure_image_eq_closure_singleton_of_isGenericPoint
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Continuous f) (s : Set A) (η : A) (hη : IsGenericPoint η s) :
    closure (f '' s) = closure ({f η} : Set B) := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure)
    (closure_mono (Set.singleton_subset_iff.mpr ⟨η, hη.mem, rfl⟩))
  rintro y ⟨x, hx, rfl⟩
  exact specializes_iff_mem_closure.mp ((hη.specializes hx).map hf)

/-- In a sober space, two irreducible components whose generic points are comparable agree. -/
private theorem eq_of_genericPoints_specializes
    {T : Type*} [TopologicalSpace T] [QuasiSober T] (C D : irreducibleComponents T)
    (h : (genericPoints.ofComponent C).1 ⤳ (genericPoints.ofComponent D).1) : C = D := by
  have hsubset : (D : Set T) ⊆ (C : Set T) := by
    rw [← genericPoints.isGenericPoint_ofComponent D,
      ← genericPoints.isGenericPoint_ofComponent C]
    exact specializes_iff_closure_subset.mp h
  exact Subtype.ext (Set.Subset.antisymm (D.2.2 C.2.1 hsubset) hsubset)

/-- For a flat morphism, if a specialization of the generic point of an irreducible component lies
over the generic point of a component of the target, so does that generic point. -/
private theorem apply_genericPoint_eq_of_specializes {P Z : Scheme.{u}} (p : P ⟶ Z) [Flat p]
    (W : irreducibleComponents P) (D : irreducibleComponents Z) {z : P}
    (hz : (genericPoints.ofComponent W).1 ⤳ z) (hD : p z = (genericPoints.ofComponent D).1) :
    p (genericPoints.ofComponent W).1 = (genericPoints.ofComponent D).1 := by
  obtain ⟨D', hD'⟩ := Stacks.Chow.component_genericPoint_maps_to_component_genericPoint p W
  have hD'eq : p (genericPoints.ofComponent W).1 = (genericPoints.ofComponent D').1 := by
    rwa [(genericPoints.isGenericPoint_ofComponent W).eq
      (W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2))]
  rw [hD'eq, eq_of_genericPoints_specializes D' D (hD'eq ▸ hD ▸ hz.map p.continuous)]

/-- Two morphisms out of a common source into a common target that agree as morphisms agree at
every point. -/
private lemma apply_eq_of_comp_eq
    {P X Y Z : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : a ≫ f = b ≫ g) (z : P) : f (a z) = g (b z) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : P ⟶ Z => k z) h

/-- Two morphisms forming a commutative square send the ranges of the two legs out of the common
source to the same set. -/
private lemma image_range_eq_of_comp_eq
    {P X Y Z : Scheme.{u}} (a : P ⟶ X) (b : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : a ≫ f = b ≫ g) : f '' Set.range a = g '' Set.range b := by
  ext z
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨b w, ⟨w, rfl⟩, (apply_eq_of_comp_eq a b f g h w).symm⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨a w, ⟨w, rfl⟩, apply_eq_of_comp_eq a b f g h w⟩

/-- For a locally quasi-finite morphism, a specialization between two points of the same fibre is
trivial. -/
private theorem eq_of_specializes_of_apply_eq {V Y : Scheme.{u}} (p : V ⟶ Y) [LocallyOfFiniteType p]
    [LocallyQuasiFinite p] {a b : V} (h : a ⤳ b) (hab : p a = p b) : a = b := by
  obtain ⟨O, hO, hOeq⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mp inferInstance (p b)) b rfl
  exact Set.mem_singleton_iff.mp (hOeq.le
    ⟨(specializes_iff_forall_open.mp h) O hO (hOeq.symm.le (Set.mem_singleton b)).1, hab⟩)

/-- Over a geometrically unibranch scheme, every point of the source of an étale morphism lies on
exactly one irreducible component. -/
@[ega "IV 15.3.3" "special case"]
private theorem existsUnique_irreducibleComponent_of_etale
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] (hY : IsGeometricallyUnibranch Y) (x : X) :
    ∃! C : irreducibleComponents X, x ∈ (C : Set X) :=
  (isGeometricallyUnibranchAt_iff_existsUnique_irreducibleComponent Y (p x)).mp (hY (p x))
    (EtaleNeighborhood.ofEtale p x)

/-- Over a geometrically unibranch, locally Noetherian scheme, the irreducible components of the
source of an étale morphism are locally open. -/
@[ega "IV 18.10.7" "partial", sga "3 X 5.14.0" "partial"]
private theorem exists_isOpen_subset_irreducibleComponent_of_etale
    {V Y : Scheme.{u}} (p : V ⟶ Y) [Etale p] (hY : IsGeometricallyUnibranch Y)
    [IsLocallyNoetherian Y] (v : V) (W : irreducibleComponents V) (hv : v ∈ (W : Set V)) :
    ∃ O : Set V, IsOpen O ∧ v ∈ O ∧ O ⊆ (W : Set V) := by
  have : LocallyOfFiniteType p := inferInstance
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨O, hO, hvO, hNoeth⟩ := isLocallyNoetherianSpace_of_isLocallyNoetherian V v
  let T : Type u := {z : V // z ∈ O}
  let j : T → V := Subtype.val
  have hj : Topology.IsOpenEmbedding j := hO.isOpenEmbedding_subtypeVal
  have : NoetherianSpace T := hNoeth
  have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
  have hunique : ∀ z (C' D' : irreducibleComponents T),
      z ∈ (C' : Set T) → z ∈ (D' : Set T) → C' = D' := by
    intro z C' D' hzC hzD
    obtain ⟨F₀, -, hF₀⟩ := existsUnique_irreducibleComponent_of_etale p hY (j z)
    have key (A : irreducibleComponents T) (hzA : z ∈ (A : Set T)) :
        (A : Set T) = j ⁻¹' (F₀ : Set V) := by
      obtain ⟨F, hF, hFA⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
        (j '' (A : Set T)) (A.2.1.image j hj.continuous.continuousOn)
      obtain rfl : (⟨F, hF⟩ : irreducibleComponents V) = F₀ := hF₀ ⟨F, hF⟩ (hFA ⟨z, hzA, rfl⟩)
      have hA : (A : Set T) ⊆ j ⁻¹' F := fun t ht => hFA ⟨t, ht, rfl⟩
      exact hA.antisymm (A.2.2
        (preimage_mem_irreducibleComponents hF hj ⟨j z, hFA ⟨z, hzA, rfl⟩, z, rfl⟩).1 hA)
    exact Subtype.ext ((key C' hzC).trans (key D' hzD).symm)
  let C : irreducibleComponents T :=
    ⟨j ⁻¹' (W : Set V), preimage_mem_irreducibleComponents W.2 hj ⟨j ⟨v, hvO⟩, hv, ⟨v, hvO⟩, rfl⟩⟩
  exact ⟨j '' (C : Set T),
    hj.isOpenMap _ (isOpen_of_mem_irreducibleComponents_of_finite hfin hunique C),
    ⟨⟨v, hvO⟩, by simpa [C, j] using hv, rfl⟩, Set.image_preimage_subset j _⟩

/-- Over a geometrically unibranch, locally Noetherian scheme, a generalization of the image of a
point `v` under an étale morphism lifts to a generalization of `v` on any irreducible component
through `v`. -/
private theorem exists_specializes_mem_irreducibleComponent_of_etale {V Y : Scheme.{u}} (p : V ⟶ Y)
    [Etale p] (hY : IsGeometricallyUnibranch Y) [IsLocallyNoetherian Y] {v : V}
    {W : irreducibleComponents V} (hv : v ∈ (W : Set V)) {y : Y} (hy : y ⤳ p v) :
    ∃ v' ∈ (W : Set V), v' ⤳ v ∧ p v' = y := by
  obtain ⟨O, hO, hvO, hOW⟩ := exists_isOpen_subset_irreducibleComponent_of_etale p hY v W hv
  obtain ⟨v', hv'v, rfl⟩ := Flat.generalizingMap p (a := v) (b := y) hy
  exact ⟨v', hOW ((specializes_iff_forall_open.mp hv'v) O hO hvO), hv'v, rfl⟩

/-- Let `q : U ⟶ V` be universally closed and `p : V ⟶ Y` flat and locally quasi-finite. If the
generic point of an irreducible component `E` of `U` lies over the generic point of an irreducible
component of `Y`, then the image of `E` under `q` is an irreducible component of `V`. -/
private theorem exists_image_eq_irreducibleComponent_of_universallyClosed {U V Y : Scheme.{u}}
    (q : U ⟶ V) [UniversallyClosed q] (p : V ⟶ Y) [Flat p] [LocallyOfFiniteType p]
    [LocallyQuasiFinite p] (E : irreducibleComponents U) (D : irreducibleComponents Y)
    (hE : p (q (genericPoints.ofComponent E).1) = (genericPoints.ofComponent D).1) :
    ∃ W : irreducibleComponents V, q '' (E : Set U) = (W : Set V) := by
  have hηE := genericPoints.isGenericPoint_ofComponent E
  obtain ⟨Wset, hWset, hEW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (q '' (E : Set U)) (E.2.1.image q q.continuous.continuousOn)
  let W : irreducibleComponents V := ⟨Wset, hWset⟩
  have hηW : IsGenericPoint (genericPoints.ofComponent W).1 (W : Set V) :=
    genericPoints.isGenericPoint_ofComponent W
  have hηWz : (genericPoints.ofComponent W).1 ⤳ q (genericPoints.ofComponent E).1 :=
    hηW.specializes (hEW ⟨_, hηE.mem, rfl⟩)
  have hηWE : (genericPoints.ofComponent W).1 ∈ q '' (E : Set U) :=
    (eq_of_specializes_of_apply_eq p hηWz
      ((apply_genericPoint_eq_of_specializes p W D hηWz hE).trans hE.symm)) ▸
      ⟨(genericPoints.ofComponent E).1, hηE.mem, rfl⟩
  refine ⟨W, hEW.antisymm ?_⟩
  change (W : Set V) ⊆ _
  rw [← genericPoints.isGenericPoint_ofComponent W]
  exact closure_minimal (Set.singleton_subset_iff.mpr hηWE)
    (q.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ E.2))

/-- For a flat morphism `q : U ⟶ X` and a point `u` over `x`, some irreducible component of `U`
through `u` has its generic point over the generic point of the irreducible component of `x`. -/
private theorem exists_mem_irreducibleComponent_genericPoint_eq_of_flat {U X : Scheme.{u}}
    (q : U ⟶ X) [Flat q] {u : U} {x : X} (hu : q u = x) :
    ∃ E : irreducibleComponents U, u ∈ (E : Set U) ∧
      q (genericPoints.ofComponent E).1 = (genericPoints.ofComponent
        ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩).1 := by
  subst hu
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent (q u), irreducibleComponent_mem_irreducibleComponents (q u)⟩
  have hC : q u ∈ (C : Set X) := mem_irreducibleComponent
  obtain ⟨uη, huηu, hqη⟩ := Flat.generalizingMap q (a := u) (b := (genericPoints.ofComponent C).1)
    ((genericPoints.isGenericPoint_ofComponent C).specializes hC)
  let E : irreducibleComponents U :=
    ⟨irreducibleComponent uη, irreducibleComponent_mem_irreducibleComponents uη⟩
  have hEclosed : IsClosed (E : Set U) := isClosed_of_mem_irreducibleComponents _ E.2
  have hηE : IsGenericPoint (genericPoints.ofComponent E).1 (E : Set U) :=
    genericPoints.isGenericPoint_ofComponent E
  exact ⟨E, (specializes_iff_forall_closed.mp huηu) _ hEclosed mem_irreducibleComponent,
    apply_genericPoint_eq_of_specializes q E C (hηE.specializes mem_irreducibleComponent) hqη⟩

/-- The key lifting statement: a locally quasi-finite morphism to a geometrically unibranch,
locally Noetherian scheme whose source components dominate target components lifts
generalizations. -/
private theorem generalizingMap_of_locallyQuasiFinite_of_dominant_components
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsLocallyNoetherian Y] (hY : IsGeometricallyUnibranch Y)
    (hcomponents : ∀ C : irreducibleComponents X,
      ∃ D : irreducibleComponents Y, closure (f '' (C : Set X)) = (D : Set Y)) :
    GeneralizingMap f.base := by
  intro x y hy
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  obtain ⟨D, hD⟩ := hcomponents C
  let ξ : X := (genericPoints.ofComponent C).1
  have hξC : IsGenericPoint ξ (C : Set X) := genericPoints.isGenericPoint_ofComponent C
  have hfξD : IsGenericPoint (f ξ) (D : Set Y) := by
    change closure ({f ξ} : Set Y) = (D : Set Y)
    rw [← closure_image_eq_closure_singleton_of_isGenericPoint f.base f.continuous
      (C : Set X) ξ hξC]
    exact hD
  obtain ⟨N⟩ := Stacks.Flatness.exists_etaleNeighborhood_finiteAt f x
    (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (f.quasiFiniteAt x))
  obtain ⟨hfinite, ⟨u, hu, huunique⟩, hspec⟩ := N.spec
  let U := N.openSubscheme
  let qX : U.toScheme ⟶ X := U.ι ≫ pullback.fst f N.neighborhood.toBase
  let qY : U.toScheme ⟶ N.neighborhood.scheme := U.ι ≫ pullback.snd f N.neighborhood.toBase
  have hqXu : qX u = x := (hspec u hu).1
  have hcomm (w : U.toScheme) : N.neighborhood.toBase (qY w) = f (qX w) :=
    (apply_eq_of_comp_eq (pullback.fst f N.neighborhood.toBase)
      (pullback.snd f N.neighborhood.toBase) f N.neighborhood.toBase pullback.condition
      (U.ι w)).symm
  have : Etale qX := by
    dsimp [qX]
    infer_instance
  have : Flat qX := inferInstance
  obtain ⟨E, huE, hqXE⟩ := exists_mem_irreducibleComponent_genericPoint_eq_of_flat qX hqXu
  have hηED : N.neighborhood.toBase (qY (genericPoints.ofComponent E).1) =
      (genericPoints.ofComponent D).1 := by
    rw [hcomm, hqXE]
    exact hfξD.eq (genericPoints.isGenericPoint_ofComponent D)
  have : IsFinite qY := hfinite
  have : LocallyQuasiFinite N.neighborhood.toBase :=
    (locallyQuasiFinite_of_etale N.neighborhood.toBase).2
  obtain ⟨W, hEW⟩ := exists_image_eq_irreducibleComponent_of_universallyClosed qY
    N.neighborhood.toBase E D hηED
  have hvW : N.neighborhood.point ∈ (W : Set N.neighborhood.scheme) := by
    rw [← hEW]
    exact ⟨u, huE, hu⟩
  obtain ⟨v', hv'W, hv'v, hv'y⟩ := exists_specializes_mem_irreducibleComponent_of_etale
    N.neighborhood.toBase hY hvW (by simpa [N.neighborhood.map_point] using hy)
  rw [← hEW] at hv'W
  obtain ⟨u', hu'E, rfl⟩ := hv'W
  obtain ⟨u'', hu'u'', hu''v⟩ := qY.isClosedMap.specializingMap hv'v
  exact ⟨qX u', by simpa [huunique u'' hu''v, hqXu] using hu'u''.map qX.continuous,
    (hcomm u').symm.trans hv'y⟩

/-- Affine space over a geometrically unibranch scheme is geometrically unibranch. -/
@[ega "IV 14.4.1.1" "special case", sga "7 VIII 5.2" "special case"]
private theorem isGeometricallyUnibranch_affineSpace
    {Y : Scheme.{u}} (n : Type u) [Finite n] (hY : IsGeometricallyUnibranch Y) :
    IsGeometricallyUnibranch 𝔸(n; Y) := by
  have : Smooth (𝔸(n; Y) ↘ Y) := smooth_affineSpace_over n Y
  intro z
  rw [← numberOfGeometricBranches_eq_one_iff _ z,
    numberOfGeometricBranches_eq_of_smooth (𝔸(n; Y) ↘ Y) z]
  exact (numberOfGeometricBranches_eq_one_iff Y ((𝔸(n; Y) ↘ Y) z)).mpr
    (hY ((𝔸(n; Y) ↘ Y) z))

/-- A morphism from a reduced scheme factors through a closed subscheme whose support contains
its image. -/
@[sga "3 VIB 7.1" "partial"]
private theorem exists_lift_subscheme_of_range_subset_support {X Y : Scheme.{u}} [IsReduced Y]
    (I : X.IdealSheafData) (f : Y ⟶ X) (h : Set.range f ⊆ (I.support : Set X)) :
    ∃ g : Y ⟶ I.subscheme, g ≫ I.subschemeι = f := by
  have hker : I ≤ f.ker := by
    refine (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
      (Closeds.closure_le.mpr h)).trans ?_
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
      Scheme.IdealSheafData.map_bot, Closeds.coe_top, Set.image_univ] using
      (Scheme.IdealSheafData.map_vanishingIdeal f (⊤ : Closeds Y)).symm.le
  exact ⟨IsClosedImmersion.lift I.subschemeι f (by simpa [I.ker_subschemeι] using hker),
    IsClosedImmersion.lift_fac I.subschemeι f _⟩

/-- Affine space preserves dominance of a morphism. -/
private theorem isDominant_affineSpace_map {X Y : Scheme.{u}} (n : Type u) (f : X ⟶ Y)
    [IsDominant f] : IsDominant (AffineSpace.map n f) := by
  have H := (AffineSpace.isPullback_map (n := n) f).flip
  have : IsDominant (pullback.snd f (𝔸(n; Y) ↘ Y)) :=
    isDominant_pullback_snd_of_isOpenMap f (𝔸(n; Y) ↘ Y) (AffineSpace.isOpenMap_over Y)
  have hcomp : IsDominant (H.isoPullback.hom ≫ pullback.snd f (𝔸(n; Y) ↘ Y)) := inferInstance
  rwa [H.isoPullback_hom_snd] at hcomp

/-- The range of the map of affine spaces induced by a morphism is the preimage of its range. -/
private theorem range_affineSpace_map {X Y : Scheme.{u}} (n : Type u) (i : X ⟶ Y) :
    Set.range (AffineSpace.map n i) = (𝔸(n; Y) ↘ Y) ⁻¹' Set.range i := by
  have H := AffineSpace.isPullback_map (n := n) i
  calc
    Set.range (AffineSpace.map n i) =
        Set.range (H.isoPullback.hom ≫ pullback.fst (𝔸(n; Y) ↘ Y) i) :=
      congrArg (fun k : 𝔸(n; X) ⟶ 𝔸(n; Y) => Set.range k) H.isoPullback_hom_fst.symm
    _ = Set.range (pullback.fst (𝔸(n; Y) ↘ Y) i) := by
      change Set.range ((pullback.fst (𝔸(n; Y) ↘ Y) i) ∘ H.isoPullback.hom) = _
      rw [Set.range_comp, Set.range_eq_univ.mpr (Scheme.Hom.surjective H.isoPullback.hom),
        Set.image_univ]
    _ = (𝔸(n; Y) ↘ Y) ⁻¹' Set.range i := Scheme.Pullback.range_fst (𝔸(n; Y) ↘ Y) i

/-- The range of the map of affine spaces induced by the closed subscheme of an irreducible
component is the preimage of the component. -/
private theorem range_affineSpace_map_subschemeι_vanishingIdeal {Z : Scheme.{u}} (n : Type u)
    (C : irreducibleComponents Z) :
    Set.range (AffineSpace.map n (Scheme.IdealSheafData.vanishingIdeal
      ⟨(C : Set Z), isClosed_of_mem_irreducibleComponents _ C.2⟩).subschemeι) =
      (𝔸(n; Z) ↘ Z) ⁻¹' (C : Set Z) := by
  rw [range_affineSpace_map, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- If the closure of the image under `f` of the support of `I` is the support of `J`, and the
closed subscheme of `I` is reduced, then `f` restricts to a dominant morphism between the closed
subschemes of `I` and `J`. -/
private theorem exists_isDominant_comp_subschemeι_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : X.IdealSheafData) [IsReduced I.subscheme] (J : Y.IdealSheafData)
    (h : closure (f '' (I.support : Set X)) = J.support) :
    ∃ g : I.subscheme ⟶ J.subscheme, IsDominant g ∧ g ≫ J.subschemeι = I.subschemeι ≫ f := by
  obtain ⟨g, hg⟩ := exists_lift_subscheme_of_range_subset_support J (I.subschemeι ≫ f) (by
    rintro _ ⟨c, rfl⟩
    rw [← h]
    exact subset_closure ⟨I.subschemeι c, I.range_subschemeι ▸ ⟨c, rfl⟩, rfl⟩)
  refine ⟨g, ⟨denseRange_iff_closure_range.mpr ?_⟩, hg⟩
  rw [J.subschemeι.isEmbedding.closure_eq_preimage_closure_image,
    image_range_eq_of_comp_eq g I.subschemeι J.subschemeι f hg, I.range_subschemeι, h,
    ← J.range_subschemeι]
  simp

/-- Componentwise dominance is inherited by affine space. -/
private theorem affineSpace_dominant_components {X Y : Scheme.{u}} (n : Type u) (f : X ⟶ Y)
    (hcomponents : ∀ C : irreducibleComponents X,
      ∃ D : irreducibleComponents Y, closure (f '' (C : Set X)) = (D : Set Y)) :
    ∀ E : irreducibleComponents 𝔸(n; X),
      ∃ F : irreducibleComponents 𝔸(n; Y),
        closure (AffineSpace.map n f '' (E : Set 𝔸(n; X))) = (F : Set 𝔸(n; Y)) := by
  intro E
  let eX := (𝔸(n; X) ↘ X).irreducibleComponentsEquiv (AffineSpace.isOpenMap_over X)
  let eY := (𝔸(n; Y) ↘ Y).irreducibleComponentsEquiv (AffineSpace.isOpenMap_over Y)
  obtain ⟨C, rfl⟩ := eX.symm.surjective E
  obtain ⟨D, hCD⟩ := hcomponents C
  let F : irreducibleComponents 𝔸(n; Y) := eY.symm D
  let IC : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨(C : Set X), isClosed_of_mem_irreducibleComponents _ C.2⟩
  let ID : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨(D : Set Y), isClosed_of_mem_irreducibleComponents _ D.2⟩
  have hCsupport : (IC.support : Set X) = (C : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hDsupport : (ID.support : Set Y) = (D : Set Y) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsReduced IC.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  obtain ⟨g, _, hg⟩ := exists_isDominant_comp_subschemeι_eq f IC ID (by
    rwa [hCsupport, hDsupport])
  let cA : 𝔸(n; IC.subscheme) ⟶ 𝔸(n; X) := AffineSpace.map n IC.subschemeι
  let dA : 𝔸(n; ID.subscheme) ⟶ 𝔸(n; Y) := AffineSpace.map n ID.subschemeι
  let gA : 𝔸(n; IC.subscheme) ⟶ 𝔸(n; ID.subscheme) := AffineSpace.map n g
  have hcArange : Set.range cA = (eX.symm C : Set 𝔸(n; X)) :=
    (range_affineSpace_map_subschemeι_vanishingIdeal n C).trans
      (Scheme.Hom.irreducibleComponentsEquiv_symm_apply_coe (𝔸(n; X) ↘ X)
        (AffineSpace.isOpenMap_over X) C).symm
  have hdArange : Set.range dA = (F : Set 𝔸(n; Y)) :=
    (range_affineSpace_map_subschemeι_vanishingIdeal n D).trans
      (Scheme.Hom.irreducibleComponentsEquiv_symm_apply_coe (𝔸(n; Y) ↘ Y)
        (AffineSpace.isOpenMap_over Y) D).symm
  have hgA : IsDominant gA := isDominant_affineSpace_map n g
  have hcomp : cA ≫ AffineSpace.map n f = gA ≫ dA := by
    simpa only [AffineSpace.map_comp] using congrArg (AffineSpace.map n) hg.symm
  refine ⟨F, ?_⟩
  rw [← hcArange, image_range_eq_of_comp_eq cA gA (AffineSpace.map n f) dA hcomp, ← hdArange]
  refine Set.Subset.antisymm (closure_minimal (Set.image_subset_range dA _)
    (hdArange ▸ isClosed_of_mem_irreducibleComponents _ F.2)) fun y hy => ?_
  obtain ⟨z, rfl⟩ := hy
  exact (Set.mapsTo_image dA (Set.range gA)).closure dA.continuous
    (hgA.denseRange.closure_range ▸ Set.mem_univ z)

/-- **Stacks Project, Tag 0F32.** A locally quasi-finite morphism to a geometrically unibranch,
locally Noetherian scheme is universally open as soon as every irreducible component of its
source dominates an irreducible component of its target. -/
@[stacks 0F32,
  ega "IV 14.4.5" "quasi-finite case",
  ega "IV 14.4.2" "quasi-finite, b)=>a)",
  ega "IV 14.4.4" "loc. quasi-finite case",
  ega "IV 14.5.6" "(d) ⇒ (b)",
  ega "IV 14.5.9" "(d) ⇒ (a), special case",
  ega "IV 18.10.2" "special case", sga "3 VIB 5.6.0" "(i), (ii), special case"]
theorem universallyOpen_of_locallyQuasiFinite_of_dominant_components
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsLocallyNoetherian Y] (hY : IsGeometricallyUnibranch Y)
    (hcomponents : ∀ C : irreducibleComponents X,
      ∃ D : irreducibleComponents Y, closure (f '' (C : Set X)) = (D : Set Y)) :
    UniversallyOpen f := by
  rw [universallyOpen_iff_forall_isOpenMap_affineSpaceMap]
  intro n
  have : LocallyOfFiniteType (AffineSpace.map (ULift.{u} (Fin n)) f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AffineSpace.isPullback_map f).flip (show LocallyOfFiniteType f from inferInstance)
  have : LocallyQuasiFinite (AffineSpace.map (ULift.{u} (Fin n)) f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (AffineSpace.isPullback_map f).flip (show LocallyQuasiFinite f from inferInstance)
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin n); Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(ULift.{u} (Fin n); Y) ↘ Y)
  exact isOpenMap_of_generalizingMap _
    (generalizingMap_of_locallyQuasiFinite_of_dominant_components
      (f := AffineSpace.map (ULift.{u} (Fin n)) f)
      (isGeometricallyUnibranch_affineSpace _ hY)
      (affineSpace_dominant_components _ f hcomponents))

end AlgebraicGeometry

end
