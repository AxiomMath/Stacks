module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.AffineQuasiCompactImmersion
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FiniteGroupoidThickening
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantPrincipalOpenGenericOrbits
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOneQuasiAffine.InvariantCore

/-!
# A dense invariant open with flat structure maps

This file contains the second part of the proof of the quasi-affine case of [Stacks, Tag 0ABI],
whose main result is in `InvariantAffineOpenDimensionOneQuasiAffine.NoetherianQuasiAffine`:
generic points of orbits, and Steps 3 to 7 of the proof, which produce an invariant affine open
neighbourhood of a point once the structure maps are flat over a dense open.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_invariant_affineOpen_of_dense_flat_open`: Steps 3 to 7
  of the proof of [Stacks, Tag 0ABI].

## Implementation notes

* Steps 3 to 5, the easy case and the choice of `f`, are
  `exists_invariant_affineOpen_of_dense_flat_open`. The easy case is [Stacks, Tag 03JE] together
  with [Stacks, Tag 01ZY] in the form
  `Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine`.
* Steps 6 and 7, the reduced complement `Z` and the choice of `h`, are
  `exists_invariant_affineOpen_of_principal_finiteLocallyFree_locus` and
  `exists_affine_basicOpen_of_generic_orbits_in_closed_subscheme`.

## References

* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 0ABF](https://stacks.math.columbia.edu/tag/0ABF)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A point maximal for the specialization order is a generic point of an irreducible
component. -/
private lemma generic_of_isMax {X : Scheme.{u}} {x : X} (hmax : IsMax x) :
    ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z := by
  let _ : PartialOrder X := specializationOrder X
  let Z : Set X := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  let η : X := hZ.1.genericPoint
  have hη : IsGenericPoint η Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηx : η ⤳ x := hη.specializes mem_irreducibleComponent
  have hle : x ≤ η := hηx
  have hEq : x = η := hmax.eq_of_le hle
  refine ⟨Z, hZ, ?_⟩
  simpa [hEq.symm] using hη

/-- A point specializing nontrivially to a point with stalk of Krull dimension at most one is a
generic point of an irreducible component: the dimension bound forces its coheight to vanish. -/
private lemma generic_of_strict_generalization_of_local_dimension_le_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] {x y : X}
    (hyx : y ⤳ x) (hne : y ≠ x)
    (hdim : Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    ∃ Z ∈ irreducibleComponents X, IsGenericPoint y Z := by
  classical
  let _ : PartialOrder X := specializationOrder X
  have hxy : x < y :=
    ⟨hyx, fun hback => hne (inseparable_iff_specializes_and.mpr ⟨hback, hyx⟩).eq.symm⟩
  have hcy : Order.coheight y + 1 ≤ 1 :=
    calc
      Order.coheight y + 1 ≤ Order.coheight x := by
        conv_rhs => rw [Order.coheight_eq_iSup_gt_coheight]
        exact le_iSup_of_le y (le_iSup_of_le hxy le_rfl)
      _ ≤ 1 := by
        simpa [ringKrullDim_stalk_eq_coheight x] using Ring.krullDimLE_iff.mp hdim
  have hcy0 : Order.coheight y = 0 := by
    cases hc : Order.coheight y with
    | top => simp [hc] at hcy
    | coe n =>
      have hn : n = 0 := by
        simp only [hc] at hcy
        norm_cast at hcy
        omega
      simp [hn]
  have hmax : IsMax y := Order.coheight_eq_zero.mp hcy0
  exact generic_of_isMax hmax

/-- A point with no nontrivial generalization is maximal for the specialization order. -/
private lemma isMax_of_no_strict_generalization {X : Scheme.{u}} {x : X}
    (h : ∀ y : X, y ⤳ x → y = x) : IsMax x := by
  let _ : PartialOrder X := specializationOrder X
  intro y hy
  cases h y hy
  exact le_rfl

/-- In a sober space with finitely many irreducible components, a dense open contains the generic
point of every irreducible component. -/
@[ega "I 7.2.8.1" "partial"]
private lemma genericPoint_mem_dense_open
    {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (hcomponents : (irreducibleComponents X).Finite)
    (W : Opens X) (hWopen : IsOpen (W : Set X)) (hWdense : Dense (W : Set X))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    hZ.1.genericPoint ∈ W := by
  classical
  let η := hZ.1.genericPoint
  have hηZ : IsGenericPoint η Z :=
    hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  by_contra hηW
  have hdisj : ¬ (W.1 ∩ Z).Nonempty := fun h =>
    hηW ((hηZ.mem_open_set_iff hWopen).2 (by simpa [Set.inter_comm] using h))
  let C : Set (Set X) := {D | D ∈ irreducibleComponents X ∧ D ≠ Z}
  have hCfinite : C.Finite := hcomponents.subset fun D hD => hD.1
  have hWsubset : (W : Set X) ⊆ ⋃₀ C := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp (by
      rw [sUnion_irreducibleComponents (X := X)]
      exact Set.mem_univ x)
    by_cases hDZ : D = Z
    · subst D
      exact False.elim (hdisj ⟨x, hx, hxD⟩)
    · exact Set.mem_sUnion.mpr ⟨D, ⟨hD, hDZ⟩, hxD⟩
  have hCclosed : IsClosed (⋃₀ C) :=
    hCfinite.isClosed_sUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1
  have hηC : η ∈ ⋃₀ C := closure_minimal hWsubset hCclosed (by simp [hWdense.closure_eq])
  obtain ⟨D, hD, hηD⟩ := Set.mem_sUnion.mp hηC
  have hZsubD : Z ⊆ D := by
    rw [← hηZ]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηD)
      (isClosed_of_mem_irreducibleComponents D hD.1)
  exact hD.2 (Set.Subset.antisymm (hZ.2 hD.1.1 hZsubD) hZsubD)

/-- The image of an irreducible component under a closed generalizing map is an irreducible
component. -/
private lemma image_irreducibleComponent_of_closed_generalizing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hclosed : IsClosedMap f)
    (hgen : GeneralizingMap f) (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) :
    f.base '' Z ∈ irreducibleComponents Y := by
  let η : genericPoints X := genericPoints.ofComponent ⟨Z, hZ⟩
  have hη : IsGenericPoint η.1 Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  have hI : IsIrreducible (f.base '' Z) := hZ.1.image f.base f.continuous.continuousOn
  have hIc : IsClosed (f.base '' Z) :=
    hclosed Z (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηI : IsGenericPoint (f.base η.1) (f.base '' Z) := by
    simpa only [hIc.closure_eq] using hη.image f.continuous
  refine ⟨hI, fun V hV hIV => ?_⟩
  obtain ⟨W, hW, hVW⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible V hV
  have hIW : f.base '' Z ⊆ W := hIV.trans hVW
  let ξ : genericPoints Y := genericPoints.ofComponent ⟨W, hW⟩
  have hξ : IsGenericPoint ξ.1 W := genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩
  have hrel : ξ.1 ⤳ f.base η.1 := by
    rw [specializes_iff_mem_closure, hξ]
    have hηmem : η.1 ∈ Z := by rw [← hη]; exact subset_closure (by simp)
    exact hIW ⟨η.1, hηmem, rfl⟩
  obtain ⟨x, hx, hfx⟩ := hgen hrel
  have hZsub : Z ⊆ closure {x} := by
    rw [← hη]
    exact closure_minimal (Set.singleton_subset_iff.mpr hx.mem_closure) isClosed_closure
  have hxcl : closure {x} = Z :=
    subset_antisymm (hZ.2 isIrreducible_singleton.closure hZsub) hZsub
  have hxη : x = η.1 :=
    IsGenericPoint.eq (by simpa [hxcl] : IsGenericPoint x Z) hη
  have hξI : W = f.base '' Z := by
    rw [← hξ, ← hηI, ← hfx, hxη]
  rwa [hξI] at hVW

/-- Two points of the source of an integral morphism, one specializing to the other and with the
same image, are equal, since points of a fibre of an integral morphism are closed in it. -/
private lemma eq_of_specializes_same_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {x y : X} (hxy : x ⤳ y) (hfy : f.base x = f.base y) : x = y := by
  let yF : f.fiber (f.base x) := (f.fiberHomeo (f.base x)).symm ⟨y, hfy.symm⟩
  have hF : f.asFiber x ⤳ yF := by
    change (f.fiberHomeo (f.base x)).symm ⟨x, rfl⟩ ⤳ yF
    exact ((subtype_specializes_iff ..).2 hxy).map
      (f.fiberHomeo (f.base x)).symm.continuous
  have h := congrArg (f.fiberι (f.base x)) (Set.mem_singleton_iff.mp
    (specializes_iff_forall_closed.mp hF _
      (AlgebraicGeometry.isClosed_singleton_asFiber_of_isIntegral f x) (Set.mem_singleton _)))
  simpa [yF] using h.symm

/-- A bound on the Krull dimension of a stalk of the target passes to the corresponding stalk of
the source along a morphism surjective on stalks. -/
private lemma krullDimLE_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] {x : X} {n : ℕ}
    (h : Ring.KrullDimLE n (Y.presheaf.stalk (f.base x))) :
    Ring.KrullDimLE n (X.presheaf.stalk x) := by
  rw [Ring.krullDimLE_iff] at h ⊢
  exact (ringKrullDim_le_of_surjective (f.stalkMap x).hom (f.stalkMap_surjective x)).trans h

/-- The bound of one on the Krull dimension of the stalks along an orbit passes from the ambient
groupoid to a groupoid mapping to it by a morphism surjective on stalks, because the image of an
arrow out of the chosen point is an arrow out of its image. -/
lemma orbit_stalk_dimension_le_one_of_groupoidHom
    {S : Scheme.{u}} (H G : Stacks.Groupoids.GroupoidScheme S)
    (F : Stacks.Groupoids.GroupoidScheme.Hom H G) [SurjectiveOnStalks F.mapObjects.left]
    (x : H.objects.left)
    (hdim : ∀ y : G.objects.left,
      (∃ r : G.arrows.left, G.source.left.base r = F.mapObjects.left.base x ∧
        G.target.left.base r = y) → Ring.KrullDimLE 1 (G.objects.left.presheaf.stalk y)) :
    ∀ y : H.objects.left,
      (∃ r : H.arrows.left, H.source.left.base r = x ∧ H.target.left.base r = y) →
        Ring.KrullDimLE 1 (H.objects.left.presheaf.stalk y) := by
  rintro y ⟨r, hrs, hrt⟩
  have hs := congrArg (fun f => f.base r) (congrArg Over.Hom.left F.map_source)
  have ht := congrArg (fun f => f.base r) (congrArg Over.Hom.left F.map_target)
  have horbit : ∃ q : G.arrows.left,
      G.source.left.base q = F.mapObjects.left.base x ∧
        G.target.left.base q = F.mapObjects.left.base y := by
    refine ⟨F.mapArrows.left.base r, ?_, ?_⟩
    · exact (by simpa using hs : G.source.left.base (F.mapArrows.left.base r) =
        F.mapObjects.left.base (H.source.left.base r)).trans (congrArg _ hrs)
    · exact (by simpa using ht : G.target.left.base (F.mapArrows.left.base r) =
        F.mapObjects.left.base (H.target.left.base r)).trans (congrArg _ hrt)
  exact krullDimLE_of_surjectiveOnStalks F.mapObjects.left (hdim _ horbit)

/-- A point of the source of a finite flat morphism over a generic point of an irreducible
component is itself a generic point of an irreducible component. -/
private lemma generic_preimage_of_finite_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    {x : X} {y : Y} (hxy : f.base x = y)
    (hy : ∃ Z ∈ irreducibleComponents Y, IsGenericPoint y Z) :
    ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z := by
  classical
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp (by
    rw [sUnion_irreducibleComponents (X := X)]
    exact Set.mem_univ x)
  let η : X := hC.1.genericPoint
  have hηC : IsGenericPoint η C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hImageC : f.base '' C ∈ irreducibleComponents Y :=
    image_irreducibleComponent_of_closed_generalizing f f.isClosedMap
      (Flat.generalizingMap f) C hC
  have hImageClosed : IsClosed (f.base '' C) :=
    f.isClosedMap C (isClosed_of_mem_irreducibleComponents C hC)
  have hηImage : IsGenericPoint (f.base η) (f.base '' C) := by
    simpa only [hImageClosed.closure_eq] using hηC.image f.continuous
  obtain ⟨D, hD, hyD⟩ := hy
  have hyImage : y ∈ f.base '' C := ⟨x, hxC, hxy⟩
  have hDsub : D ⊆ f.base '' C := fun q hq =>
    (specializes_iff_forall_closed.mp (hyD.specializes hq)) _ hImageClosed hyImage
  have hEq : f.base '' C = D := Set.Subset.antisymm (hD.2 hImageC.1 hDsub) hDsub
  have hηD : IsGenericPoint (f.base η) D := hEq ▸ hηImage
  have hmap : f.base η = f.base x := (hηD.eq hyD).trans hxy.symm
  have hηx : η = x := eq_of_specializes_same_fiber f (hηC.specializes hxC) hmap
  exact ⟨C, hC, hηx ▸ hηC⟩

/-- The image of a generic point of an irreducible component under a finite flat morphism is a
generic point of an irreducible component. -/
private lemma generic_image_of_finite_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    {x : X}
    (hx : ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z) :
    ∃ Z ∈ irreducibleComponents Y, IsGenericPoint (f.base x) Z := by
  obtain ⟨D, hD, hxD⟩ := hx
  have hDc : IsClosed (f.base '' D) :=
    f.isClosedMap D (isClosed_of_mem_irreducibleComponents D hD)
  refine ⟨f.base '' D, image_irreducibleComponent_of_closed_generalizing f f.isClosedMap
    (Flat.generalizingMap f) D hD, ?_⟩
  simpa only [hDc.closure_eq] using hxD.image f.continuous

/-- The orbit of a generic point of an irreducible component of the object scheme of a groupoid
scheme with finite flat source and target consists of generic points of irreducible
components. -/
private lemma generic_orbit_of_generic_point
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [Flat G.source.left] [Flat G.target.left]
    {x : G.objects.left}
    (hx : ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint x Z)
    {y : G.objects.left}
    (hxy : ∃ r : G.arrows.left,
      G.source.left.base r = x ∧ G.target.left.base r = y) :
    ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z := by
  obtain ⟨r, hrs, hrt⟩ := hxy
  have hr : ∃ Z ∈ irreducibleComponents G.arrows.left, IsGenericPoint r Z :=
    generic_preimage_of_finite_flat G.source.left hrs hx
  simpa [hrt] using generic_image_of_finite_flat G.target.left hr

/-- The source of the inverse of an arrow is the target of the arrow. -/
private lemma source_base_inverse {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (r : G.arrows.left) : G.source.left.base (G.inverse.left.base r) = G.target.left.base r :=
  congrArg (fun f => f.base r) (congrArg Over.Hom.left G.source_inverse)

/-- The target of the inverse of an arrow is the source of the arrow. -/
private lemma target_base_inverse {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (r : G.arrows.left) : G.target.left.base (G.inverse.left.base r) = G.source.left.base r :=
  congrArg (fun f => f.base r) (congrArg Over.Hom.left G.target_inverse)

/-- If the saturation of the closure of an open is the whole object scheme, then every point has
a point of its orbit in that closure. -/
lemma exists_orbit_point_mem_closure_of_saturation
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (W : G.objects.left.Opens)
    (hsat : G.target.left.base ''
      (G.source.left.base ⁻¹' closure (W : Set G.objects.left)) = Set.univ)
    (x : G.objects.left) :
    ∃ y : G.objects.left,
      (∃ r : G.arrows.left, G.source.left.base r = x ∧ G.target.left.base r = y) ∧
        y ∈ closure (W : Set G.objects.left) := by
  have hmem : x ∈ G.target.left.base ''
      (G.source.left.base ⁻¹' closure (W : Set G.objects.left)) := by
    rw [hsat]
    exact Set.mem_univ x
  obtain ⟨r, hr, htarget⟩ := hmem
  refine ⟨G.source.left.base r, ?_, hr⟩
  exact ⟨G.inverse.left.base r, (source_base_inverse G r).trans htarget, target_base_inverse G r⟩

/-- If a point of the orbit of `x` lies in an invariant open, then so does `x`, by invariance
applied to the inverse of the connecting arrow. -/
lemma mem_of_mem_orbit_invariant_open
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    (W : G.objects.left.Opens) (hW : Stacks.Groupoids.IsInvariantOpen G W)
    {x y : G.objects.left}
    (horbit : ∃ r : G.arrows.left,
      G.source.left.base r = x ∧ G.target.left.base r = y)
    (hy : y ∈ W) : x ∈ W := by
  obtain ⟨r, hrs, hrt⟩ := horbit
  have hsource := (source_base_inverse G r).trans hrt
  have htarget := (target_base_inverse G r).trans hrs
  exact htarget ▸ hW (G.inverse.left.base r) (hsource ▸ hy)

/-- The zero locus of the vanishing ideal of the complement of the range of an open immersion into
an affine scheme is that complement. -/
private lemma zeroLocus_vanishingIdeal_compl_range {R : CommRingCat.{u}} {Z : Scheme.{u}}
    (j : Z ⟶ Spec R) [IsOpenImmersion j] :
    PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (Set.range j)ᶜ : Set R) =
      (Set.range j)ᶜ :=
  (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
    (IsOpenImmersion.isOpen_range j).isClosed_compl.closure_eq

/-- The nonvanishing locus of a function in the vanishing ideal of the complement of the range of
an open immersion into an affine scheme lies in the range. -/
private lemma basicOpen_le_opensRange_of_mem_vanishingIdeal {R : CommRingCat.{u}} {Z : Scheme.{u}}
    (j : Z ⟶ Spec R) [IsOpenImmersion j] {h : R}
    (hh : h ∈ PrimeSpectrum.vanishingIdeal (Set.range j)ᶜ) :
    PrimeSpectrum.basicOpen h ≤ j.opensRange := fun z hz => by
  by_contra hn
  exact hz (((zeroLocus_vanishingIdeal_compl_range j).ge hn) hh)

/-- **Step 7 of the source's proof of [Stacks, Tag 0ABI].** For a groupoid scheme whose object
scheme is closed in a quasi-affine scheme and whose orbit of a point consists of generic points
of irreducible components, some global function on the ambient scheme has affine nonvanishing
locus whose preimage is an invariant open containing that point. The ideal fed to
[Stacks, Tag 0ABF] is the one cutting out the complement of the image of the quasi-affine scheme
in its affine hull. -/
private lemma exists_affine_basicOpen_of_generic_orbits_in_closed_subscheme
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [IsLocallyNoetherian G.objects.left]
    {X : Scheme.{u}} [X.IsQuasiAffine]
    (i : G.objects.left ⟶ X) [IsClosedImmersion i]
    (x : G.objects.left)
    (hx : ∀ y, (∃ r : G.arrows.left,
      G.source.left r = x ∧ G.target.left r = y) →
      ∃ Z ∈ irreducibleComponents G.objects.left, IsGenericPoint y Z) :
    ∃ h : Γ(X, ⊤), IsAffineOpen (X.basicOpen h) ∧
      Stacks.Groupoids.IsInvariantOpen G (i ⁻¹ᵁ X.basicOpen h) ∧ i x ∈ X.basicOpen h := by
  classical
  let j := X.toSpecΓ
  let I := PrimeSpectrum.vanishingIdeal (Set.range j)ᶜ
  have hI := zeroLocus_vanishingIdeal_compl_range j
  have hclosed : IsClosed ((Set.range j)ᶜ ∪ Set.range (i ≫ j)) := by
    have heq : ((Set.range j)ᶜ ∪ Set.range (i ≫ j))ᶜ =
        j '' (Set.range i)ᶜ := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_union, not_or, not_not,
        Set.mem_range, Set.mem_image, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨⟨y, rfl⟩, hy⟩
        exact ⟨y, fun ⟨a, ha⟩ => hy ⟨a, congrArg j ha⟩, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, rfl⟩, fun ⟨a, ha⟩ => hy ⟨a, j.isEmbedding.injective ha⟩⟩
    rw [← isOpen_compl_iff, heq]
    exact j.isOpenMap _ i.isClosedEmbedding.isClosed_range.isOpen_compl
  obtain ⟨h, hhI, hinv, _, hmem⟩ :=
    AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen H06AD G
      (AlgebraicGeometry.finitePresentation_of_finiteType G.source.left)
      (AlgebraicGeometry.finitePresentation_of_finiteType G.target.left)
      (fun _ : Unit => x) (fun _ => hx) (i ≫ j) I
      (by
        rw [hI]
        exact Set.disjoint_left.mpr fun _ ⟨a, ha⟩ hn => hn ⟨i a, ha⟩)
      (by rwa [hI])
  have hle := basicOpen_le_opensRange_of_mem_vanishingIdeal j hhI
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [← X.toSpecΓ_preimage_basicOpen h]
    exact (IsAffineOpen.Spec_basicOpen h).preimage_of_isOpenImmersion j hle
  · intro r hr
    exact (X.toSpecΓ_preimage_basicOpen h).le
      (hinv r ((X.toSpecΓ_preimage_basicOpen h).ge hr))
  · exact (X.toSpecΓ_preimage_basicOpen h).le (hmem PUnit.unit)

/-- **Steps 6 to 10 of the source's proof of [Stacks, Tag 0ABI].** Let the nonvanishing locus of
`f` be an invariant affine open over which the source map is finite locally free, and let `x` be
a point outside it all of whose orbit's nontrivial generalizations lie inside it. Then `x` has
an invariant affine open neighbourhood: the reduced complement of the locus of `f` carries a
restricted groupoid whose orbit of `x` consists of generic points, which yields a function `h`
as in step 7, and the invariant core of the nonvanishing locus of `h` is the required open. -/
private lemma exists_invariant_affineOpen_of_principal_finiteLocallyFree_locus
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [IsNoetherian G.objects.left] [G.objects.left.IsQuasiAffine]
    (f : Γ(G.objects.left, ⊤)) (hf : IsAffineOpen (G.objects.left.basicOpen f))
    (hfinv : Stacks.Groupoids.IsInvariantOpen G (G.objects.left.basicOpen f))
    (N : Stacks.Norm.MorphismNormMap (G.source.left ∣_ G.objects.left.basicOpen f))
    (x : G.objects.left) (hxf : x ∉ G.objects.left.basicOpen f)
    (hstrict : ∀ y, (∃ r : G.arrows.left,
      G.source.left r = x ∧ G.target.left r = y) →
      ∀ z, z ≠ y → z ⤳ y → z ∈ G.objects.left.basicOpen f) :
    ∃ V : G.objects.left.Opens, Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧ x ∈ V := by
  classical
  let Z := Scheme.IdealSheafData.vanishingIdeal (X := G.objects.left)
    ⟨(G.objects.left.basicOpen f : Set G.objects.left)ᶜ,
      (G.objects.left.basicOpen f).isOpen.isClosed_compl⟩
  let g : Over.mk (Z.subschemeι ≫ G.objects.hom) ⟶ G.objects :=
    Over.homMk Z.subschemeι
  let R := AlgebraicGeometry.GroupoidScheme.restrict G g
  let i := R.hom.mapObjects.left
  have : IsClosedImmersion g.left := show IsClosedImmersion Z.subschemeι from inferInstance
  have hi : IsClosedImmersion i :=
    (restriction_mapObjects_property_iff G g R @IsClosedImmersion).2 inferInstance
  have : IsFinite g.left := show IsFinite Z.subschemeι from inferInstance
  have hfinite := finite_restriction_maps G g R
  have : IsFinite R.groupoid.source.left := hfinite.1
  have : IsFinite R.groupoid.target.left := hfinite.2
  have : IsLocallyNoetherian R.groupoid.objects.left :=
    LocallyOfFiniteType.isLocallyNoetherian i
  have hrange : Set.range i = (G.objects.left.basicOpen f : Set G.objects.left)ᶜ := by
    rw [range_restriction_mapObjects G g R]
    exact Z.range_subschemeι.trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  obtain ⟨xZ, hxZ⟩ := (show x ∈ Set.range i by rwa [hrange])
  have hgeneric : ∀ y, (∃ r : R.groupoid.arrows.left,
      R.groupoid.source.left r = xZ ∧ R.groupoid.target.left r = y) →
      ∃ C ∈ irreducibleComponents R.groupoid.objects.left, IsGenericPoint y C := by
    rintro y ⟨r, hrs, hrt⟩
    refine generic_of_isMax (isMax_of_no_strict_generalization fun z hz =>
      i.isEmbedding.injective ?_)
    by_contra hne
    have hs := congrArg (fun k => k.left r) R.hom.map_source
    have ht := congrArg (fun k => k.left r) R.hom.map_target
    have hy : ∃ q : G.arrows.left, G.source.left q = x ∧ G.target.left q = i y :=
      ⟨R.hom.mapArrows.left r, hs.trans ((congrArg i hrs).trans hxZ), ht.trans (congrArg i hrt)⟩
    exact (hrange ▸ Set.mem_range_self z) (hstrict (i y) hy (i z) hne (hz.map i.continuous))
  obtain ⟨h, hh, hinv, hx⟩ :=
    exists_affine_basicOpen_of_generic_orbits_in_closed_subscheme H06AD R.groupoid i xZ
      hgeneric
  have hres : ∀ r : G.arrows.left,
      G.source.left r ∈ G.objects.left.basicOpen h →
      G.source.left r ∉ G.objects.left.basicOpen f →
      G.target.left r ∈ G.objects.left.basicOpen h := by
    intro r hrh hrf
    have htf : G.target.left r ∉ G.objects.left.basicOpen f := by
      intro ht
      exact hrf ((target_base_inverse G r) ▸
        hfinv (G.inverse.left.base r) ((source_base_inverse G r).symm ▸ ht))
    obtain ⟨a, ha⟩ := (show G.source.left r ∈ Set.range i by rwa [hrange])
    obtain ⟨b, hb⟩ := (show G.target.left r ∈ Set.range i by rwa [hrange])
    obtain ⟨q, hqs, hqt⟩ := exists_restriction_arrow_of_mapObjects G g R a b r ha.symm hb.symm
    have hqmem := hinv q (show i (R.groupoid.source.left q) ∈ G.objects.left.basicOpen h by
      rwa [hqs, ha])
    change i (R.groupoid.target.left q) ∈ G.objects.left.basicOpen h at hqmem
    rwa [hqt, hb] at hqmem
  refine ⟨invariantCore G (G.objects.left.basicOpen h), invariantCore_invariant G _,
    isAffineOpen_invariantCore_of_norm_of_invariant_complement G f h hf hh N hres, ?_⟩
  apply (mem_invariantCore_iff G _ x).2
  intro r hr
  apply hres r
  · simpa [hr, hxZ] using hx
  · rwa [hr]

/-- An arrow of the ambient groupoid between the images of two generalized points lifts uniquely
along a morphism of groupoid schemes which is fully faithful on generalized points. -/
private lemma exists_arrow_lift_of_fullyFaithful
    {S : Scheme.{u}} {H G : Stacks.Groupoids.GroupoidScheme S}
    (F : Stacks.Groupoids.GroupoidScheme.Hom H G)
    (hF : ∀ T, Nonempty (F.evaluation T).FullyFaithful)
    {T : Over S} (a b : T ⟶ H.objects) (r : T ⟶ G.arrows)
    (hs : r ≫ G.source = a ≫ F.mapObjects)
    (ht : r ≫ G.target = b ≫ F.mapObjects) :
    ∃ q : T ⟶ H.arrows, q ≫ H.source = a ∧ q ≫ H.target = b ∧
      q ≫ F.mapArrows = r := by
  let ff := (hF T).some
  let r' : (F.evaluation T).obj a ⟶ (F.evaluation T).obj b := ⟨r, hs, ht⟩
  let q := ff.preimage r'
  exact ⟨q.arrow, q.source_eq, q.target_eq,
    congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow (ff.map_preimage r')⟩

/-- A morphism of groupoid schemes fully faithful on generalized points with monomorphic map on
objects has monomorphic map on arrows. -/
private lemma mono_mapArrows_of_fullyFaithful
    {S : Scheme.{u}} {H G : Stacks.Groupoids.GroupoidScheme S}
    (F : Stacks.Groupoids.GroupoidScheme.Hom H G)
    (hF : ∀ T, Nonempty (F.evaluation T).FullyFaithful) [Mono F.mapObjects] :
    Mono F.mapArrows := by
  constructor
  intro T a b hab
  have hs : a ≫ H.source = b ≫ H.source := by
    rw [← cancel_mono F.mapObjects]
    simpa only [Category.assoc, F.map_source] using
      congrArg (· ≫ G.source) hab
  have ht : a ≫ H.target = b ≫ H.target := by
    rw [← cancel_mono F.mapObjects]
    simpa only [Category.assoc, F.map_target] using
      congrArg (· ≫ G.target) hab
  let a' : H.EvaluationHom (a ≫ H.source) (a ≫ H.target) := ⟨a, rfl, rfl⟩
  let b' : H.EvaluationHom (a ≫ H.source) (a ≫ H.target) := ⟨b, hs.symm, ht.symm⟩
  have heq : (F.evaluation T).map a' = (F.evaluation T).map b' :=
    Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext hab
  exact congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow ((hF T).some.map_injective heq)

/-- If two subgroupoids of a groupoid scheme are related by an open immersion with invariant
image on objects, then the arrows of the smaller one are the base change of the arrows of the
larger one along the source map, compatibly with the target maps. -/
lemma source_isPullback_of_open_fullyFaithful_factor
    {S : Scheme.{u}} {K H G : Stacks.Groupoids.GroupoidScheme S}
    (E : Stacks.Groupoids.GroupoidScheme.Hom K G)
    (F : Stacks.Groupoids.GroupoidScheme.Hom H G)
    (hE : ∀ T, Nonempty (E.evaluation T).FullyFaithful)
    (hF : ∀ T, Nonempty (F.evaluation T).FullyFaithful)
    [Mono E.mapObjects] [Mono F.mapObjects]
    (k : K.objects ⟶ H.objects) [IsOpenImmersion k.left]
    (hk : k ≫ F.mapObjects = E.mapObjects)
    (hinv : Stacks.Groupoids.IsInvariantSet H (Set.range k.left)) :
    ∃ a : K.arrows ⟶ H.arrows, IsPullback a K.source H.source k ∧
      a ≫ H.target = K.target ≫ k ∧ a ≫ F.mapArrows = E.mapArrows := by
  classical
  have := mono_mapArrows_of_fullyFaithful E hE
  have := mono_mapArrows_of_fullyFaithful F hF
  obtain ⟨a, has, hat, ha⟩ := exists_arrow_lift_of_fullyFaithful F hF
    (K.source ≫ k) (K.target ≫ k) E.mapArrows
    (by rw [Category.assoc, hk, E.map_source])
    (by rw [Category.assoc, hk, E.map_target])
  refine ⟨a, ⟨⟨has⟩, ⟨?_⟩⟩, hat, ha⟩
  apply PullbackCone.isLimitAux'
  intro c
  apply Classical.choice
  suffices ∃ q, q ≫ a = c.fst ∧ q ≫ K.source = c.snd by
    obtain ⟨q, hqa, hqs⟩ := this
    have uniq : ∀ m : c.pt ⟶ K.arrows, m ≫ a = c.fst → m = q := by
      intro m hm
      have key : m ≫ E.mapArrows = q ≫ E.mapArrows := by
        rw [← ha, ← Category.assoc, hm, ← Category.assoc, hqa]
      exact (cancel_mono E.mapArrows).mp key
    refine ⟨⟨q, hqa, hqs, ?_⟩⟩
    intro m hm _
    exact uniq m hm
  have hrange : Set.range (c.fst ≫ H.target).left ⊆ Set.range k.left := by
    rintro z ⟨t, rfl⟩
    exact hinv (c.fst.left t) ⟨c.snd.left t, (congrArg (fun m => m.left t) c.condition).symm⟩
  let l := IsOpenImmersion.lift k.left (c.fst ≫ H.target).left hrange
  have hl : l ≫ k.left = (c.fst ≫ H.target).left := IsOpenImmersion.lift_fac ..
  let b : c.pt ⟶ K.objects := Over.homMk l (by
    rw [← k.w, ← Category.assoc, hl]
    exact (c.fst ≫ H.target).w)
  have hb : b ≫ k = c.fst ≫ H.target := Over.OverMorphism.ext hl
  obtain ⟨q, hqs, hqt, hq⟩ := exists_arrow_lift_of_fullyFaithful E hE
    c.snd b (c.fst ≫ F.mapArrows)
    (by rw [Category.assoc, F.map_source, ← Category.assoc, c.condition,
      Category.assoc, hk])
    (by rw [Category.assoc, F.map_target, ← Category.assoc, ← hb,
      Category.assoc, hk])
  have hqa : q ≫ a = c.fst := by
    rw [← cancel_mono F.mapArrows, Category.assoc, ha]
    exact hq
  exact ⟨q, hqa, hqs⟩

/-- The restriction of a morphism over an open contained in the image of an open immersion is
flat, as soon as the base change of the morphism along that open immersion is. -/
private lemma flat_restrict_of_pullback_of_subset_range
    {A B X Y : Scheme.{u}} (a : A ⟶ X) (s : A ⟶ B)
    (f : X ⟶ Y) (k : B ⟶ Y) [IsOpenImmersion k] [Flat s]
    (sq : IsPullback a s f k) (V : Y.Opens) (hV : (V : Set Y) ⊆ Set.range k) :
    Flat (f ∣_ V) := by
  let l := IsOpenImmersion.lift k V.ι (by simpa using hV)
  have hl : l ≫ k = V.ι := IsOpenImmersion.lift_fac ..
  have sq' := (IsPullback.of_hasPullback s l).paste_horiz sq
  rw [hl] at sq'
  have : Flat (pullback.snd s l) := inferInstance
  let e := sq'.isoIsPullback _ _ (isPullback_morphismRestrict f V).flip
  have he : e.hom ≫ (f ∣_ V) = pullback.snd s l := by simp [e]
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso (@Flat) e.hom _).mp
    (he.symm ▸ inferInstance)

/-- Two points with the same image in the base of a Cartesian square of schemes over a base have
a common preimage in its vertex. -/
private lemma exists_point_of_over_isPullback
    {S : Scheme.{u}} {P X Y Z : Over S}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback a b f g) (x : X.left) (y : Y.left)
    (h : f.left x = g.left y) :
    ∃ p : P.left, a.left p = x ∧ b.left p = y := by
  obtain ⟨p, hp, hq⟩ := exists_point_over_pullback f g x y h
  let l := sq.lift (pullback.fst f g) (pullback.snd f g) pullback.condition
  exact ⟨l.left p, (congrArg (fun m => m.left p) (sq.lift_fst ..)).trans hp,
    (congrArg (fun m => m.left p) (sq.lift_snd ..)).trans hq⟩

/-- The image of an invariant subset is invariant, for a morphism of groupoid schemes whose
arrows are the base change of the ambient arrows along the source map. -/
private lemma invariant_image_of_source_isPullback
    {S : Scheme.{u}} {H G : Stacks.Groupoids.GroupoidScheme S}
    (a : H.arrows ⟶ G.arrows) (k : H.objects ⟶ G.objects)
    (sq : IsPullback a H.source G.source k)
    (ht : a ≫ G.target = H.target ≫ k)
    (V : Set H.objects.left) (hV : Stacks.Groupoids.IsInvariantSet H V) :
    Stacks.Groupoids.IsInvariantSet G (k.left '' V) := by
  rintro r ⟨y, hy, hyr⟩
  obtain ⟨q, hqa, hqs⟩ := exists_point_of_over_isPullback sq r y hyr.symm
  refine ⟨H.target.left q, hV q (hqs.symm ▸ hy), ?_⟩
  exact (congrArg (fun m => m.left q) ht).symm.trans (congrArg G.target.left hqa)

/-- A generalization of a generic point of an irreducible component equals it. -/
private lemma eq_of_specializes_genericPoint
    {X : Type u} [TopologicalSpace X] [T0Space X] {x y : X}
    (hx : ∃ C ∈ irreducibleComponents X, IsGenericPoint x C)
    (hy : y ⤳ x) : y = x := by
  obtain ⟨C, hC, hx⟩ := hx
  have hsub : C ⊆ closure ({y} : Set X) := by
    rw [← hx]
    exact closure_minimal (Set.singleton_subset_iff.mpr hy.mem_closure) isClosed_closure
  have hyC : y ∈ C :=
    hC.2 isIrreducible_singleton.closure hsub (subset_closure (Set.mem_singleton y))
  exact (inseparable_iff_specializes_and.mpr ⟨hy, hx.specializes hyC⟩).eq

/-- A point of the source of an open immersion whose image is a generic point of an irreducible
component is itself a generic point of an irreducible component. -/
private lemma generic_of_generic_image_of_isOpenImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] {x : X}
    (hx : ∃ C ∈ irreducibleComponents Y, IsGenericPoint (i x) C) :
    ∃ C ∈ irreducibleComponents X, IsGenericPoint x C :=
  generic_of_isMax (isMax_of_no_strict_generalization fun _ hy =>
    i.isEmbedding.injective (eq_of_specializes_genericPoint hx (hy.map i.continuous)))

/-- **Steps 3 to 10 of the source's proof of [Stacks, Tag 0ABI].** Let `G` be a groupoid scheme
with finite source and target over a Noetherian quasi-affine object scheme, and let `H` be a
subgroupoid on a dense open with flat, finite source and target whose arrows are the base change
of those of `G`. Then every point whose orbit has stalks of Krull dimension at most one lies in
an invariant affine open. If the point lies in the dense open, [Stacks, Tag 03JE] applies
directly, using that finitely many points of a quasi-affine scheme lie in an affine open
([Stacks, Tag 01ZY]); otherwise [Stacks, Tag 0ABF] applied to the generic points of the
components of the dense open produces the function `f` of step 5, and the previous lemma
finishes. -/
lemma exists_invariant_affineOpen_of_dense_flat_open
    (H06AD : ∀ (Y Y' : Scheme.{u}) (j : Y ⟶ Y'), IsThickening j → IsAffine Y → IsAffine Y')
    {S : Scheme.{u}} (G H : Stacks.Groupoids.GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left]
    [IsNoetherian G.objects.left] [G.objects.left.IsQuasiAffine]
    [IsFinite H.source.left] [IsFinite H.target.left]
    [Flat H.source.left] [Flat H.target.left]
    (k : H.objects ⟶ G.objects) [IsOpenImmersion k.left]
    (a : H.arrows ⟶ G.arrows) (sq : IsPullback a H.source G.source k)
    (ht : a ≫ G.target = H.target ≫ k)
    (hdense : DenseRange k.left)
    (x : G.objects.left)
    (hdim : ∀ y, (∃ r : G.arrows.left, G.source.left r = x ∧ G.target.left r = y) →
      Ring.KrullDimLE 1 (G.objects.left.presheaf.stalk y)) :
    ∃ V : G.objects.left.Opens, Stacks.Groupoids.IsInvariantOpen G V ∧
      IsAffineOpen V ∧ x ∈ V := by
  classical
  have : IsLocallyNoetherian H.objects.left := LocallyOfFiniteType.isLocallyNoetherian k.left
  have : NoetherianSpace H.objects.left := k.left.isEmbedding.isInducing.noetherianSpace
  have : H.objects.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion k.left
  have : Stacks.Morphisms.IsFiniteLocallyFree H.source.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian _).2
      ⟨inferInstance, inferInstance⟩
  have : Stacks.Morphisms.IsFiniteLocallyFree H.target.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian _).2
      ⟨inferInstance, inferInstance⟩
  by_cases hxW : x ∈ Set.range k.left
  · obtain ⟨y, rfl⟩ := hxW
    obtain ⟨V, hV, hVO⟩ :=
      Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine (orbit_finite H y)
    obtain ⟨V, hV, hy, hVI⟩ :=
      AlgebraicGeometry.GroupoidScheme.exists_invariant_affine_open_of_orbit_subset_affine H y
        ⟨V, hV, fun r hr => hVO ⟨r, hr, rfl⟩⟩
    exact ⟨k.left ''ᵁ V, invariant_image_of_source_isPullback a k sq ht _ hVI,
      hV.image_of_isOpenImmersion k.left, ⟨y, hy, rfl⟩⟩
  let ι := {C : Set H.objects.left // C ∈ irreducibleComponents H.objects.left}
  have : Finite ι := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let η : ι → H.objects.left := fun C => C.2.1.genericPoint
  have hη (C : ι) : IsGenericPoint (η C) C.1 :=
    C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)
  let j := k.left ≫ G.objects.left.toSpecΓ
  let I := PrimeSpectrum.vanishingIdeal (Set.range j)ᶜ
  have hI := zeroLocus_vanishingIdeal_compl_range j
  obtain ⟨f, hfI, hfInv, hfAff, hfmem⟩ :=
    AlgebraicGeometry.exists_mem_ideal_invariant_affine_preimage_basicOpen H06AD H
      (AlgebraicGeometry.finitePresentation_of_finiteType H.source.left)
      (AlgebraicGeometry.finitePresentation_of_finiteType H.target.left) η
      (fun C y hy => generic_orbit_of_generic_point H ⟨C.1, C.2, hη C⟩ hy) j I
      (by rw [hI]; exact disjoint_compl_right)
      (by
        convert isClosed_univ using 1
        refine Set.eq_univ_of_forall fun z => ?_
        by_cases hz : z ∈ Set.range (j : H.objects.left → Spec Γ(G.objects.left, ⊤))
        · exact Or.inr hz
        · exact Or.inl (hI.ge hz))
  have hle := basicOpen_le_opensRange_of_mem_vanishingIdeal j hfI
  have hfW : (G.objects.left.basicOpen f : Set G.objects.left) ⊆ Set.range k.left := by
    intro z hz
    obtain ⟨y, hy⟩ := hle ((G.objects.left.toSpecΓ_preimage_basicOpen f).ge hz)
    exact ⟨y, G.objects.left.toSpecΓ.isEmbedding.injective hy⟩
  have himage : k.left ''ᵁ (j ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
      G.objects.left.basicOpen f := by
    change k.left ''ᵁ (k.left ⁻¹ᵁ G.objects.left.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen f) = _
    rw [G.objects.left.toSpecΓ_preimage_basicOpen]
    exact SetLike.coe_injective (Set.image_preimage_eq_of_subset hfW)
  have hfinv : Stacks.Groupoids.IsInvariantOpen G (G.objects.left.basicOpen f) := by
    rw [← himage]
    exact invariant_image_of_source_isPullback a k sq ht _ hfInv
  have hf : IsAffineOpen (G.objects.left.basicOpen f) := by
    rw [← himage]
    exact hfAff.image_of_isOpenImmersion k.left
  have hstrict : ∀ y, (∃ r : G.arrows.left,
      G.source.left r = x ∧ G.target.left r = y) →
      ∀ z, z ≠ y → z ⤳ y → z ∈ G.objects.left.basicOpen f := by
    intro y hy z hne hzy
    obtain ⟨C, hC, hzC⟩ :=
      generic_of_strict_generalization_of_local_dimension_le_one hzy hne (hdim y hy)
    have hzW : z ∈ Set.range k.left := by
      have hgen := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
      rw [hzC.eq hgen]
      exact genericPoint_mem_dense_open NoetherianSpace.finite_irreducibleComponents
        k.left.opensRange k.left.opensRange.isOpen hdense hC
    obtain ⟨w, rfl⟩ := hzW
    obtain ⟨D, hD, hw⟩ := generic_of_generic_image_of_isOpenImmersion k.left ⟨C, hC, hzC⟩
    have hwη : w = η ⟨D, hD⟩ := hw.eq (hη ⟨D, hD⟩)
    rw [hwη]
    exact (G.objects.left.toSpecΓ_preimage_basicOpen f).le (hfmem ⟨D, hD⟩)
  have : Flat (G.source.left ∣_ G.objects.left.basicOpen f) :=
    flat_restrict_of_pullback_of_subset_range a.left H.source.left G.source.left k.left
      (sq.map (Over.forget S)) _ hfW
  have : Stacks.Morphisms.IsFiniteLocallyFree (G.source.left ∣_ G.objects.left.basicOpen f) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian _).2
      ⟨inferInstance, inferInstance⟩
  exact exists_invariant_affineOpen_of_principal_finiteLocallyFree_locus H06AD G f hf hfinv
    (Stacks.Divisors.finiteLocallyFreeNorm _).toMorphismNormMap x (fun hx => hxW (hfW hx)) hstrict

end AlgebraicGeometry.GroupoidScheme

end
