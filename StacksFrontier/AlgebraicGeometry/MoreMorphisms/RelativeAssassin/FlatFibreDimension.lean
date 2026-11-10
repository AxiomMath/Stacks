module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedReduction
public import StacksFrontier.RingTheory.RelativeDimension.ValuationRing
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibre dimension at a generic point of the fibre of the closure of a relative associated point

Let `f : X ⟶ S` be locally of finite type, `F` a quasi-coherent `𝒪_X`-module of finite type and
`y` a point of `Ass_{X/S}(F)`. Let `Y` be the reduced closed subscheme supported on the closure
of `y` and let `g : Y ⟶ S` be the induced morphism. If `x` is a generic point of an irreducible
component of the fibre `Y_s` and `F` is flat over `S` at the image of `x` in `X`, then the local
dimension of `Y_s` at `x` equals the dimension of the whole fibre `Y_{f y}`.

## Main results

* `Stacks.RelativeAssassin.topologicalKrullDimAt_fiber_eq_fiber_of_flat`
* `Stacks.RelativeAssassin.topologicalKrullDim_eq_at_generic_component`

## Implementation notes

The configuration is transported to a valuation base by
`Stacks.RelativeAssassin.exists_valuation_base_change_associated_flat`, where the point `y`
becomes a relative associated point over the generic point of `Spec A` and `x` becomes a generic
point of a component of the closed fibre. Over a valuation ring the special fibre and the generic
fibre of an integral scheme of finite type have the same dimension, which is the content of
`valuation_fiber_dimension_bridge`; it is proved on an affine chart, where the two dimensions are
the Krull dimensions of the two fibre rings of a finite type domain over a valuation ring. Both
the original local dimension and the dimension of the target fibre are then recovered from the
valuation base by the invariance of fibre dimension under base change and by the fact that at a
generic point of a component the local dimension is the dimension of that component.

## References

* [Stacks Project, Tag 0GSI](https://stacks.math.columbia.edu/tag/0GSI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.RelativeAssassin

/-- The projection of a fibre to the spectrum of the residue field is locally of finite type
when the morphism is. -/
private theorem locallyOfFiniteType_fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s)))

attribute [local instance] locallyOfFiniteType_fiberToSpecResidueField

/-- The two fibres of a morphism over equal points are homeomorphic. -/
private def fiberHomeoOfEq {X S : Scheme.{u}} (f : X ⟶ S)
    (s t : S) (hst : s = t) : f.fiber s ≃ₜ f.fiber t := by
  let hset : f ⁻¹' {s} = f ⁻¹' {t} := by rw [hst]
  exact (f.fiberHomeo s).trans
    ((Homeomorph.setCongr hset).trans (f.fiberHomeo t).symm)

/-- The spectrum map of an algebra of finite type is locally of finite type. -/
private theorem locallyOfFiniteType_spec_map_algebraMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- For a finite type domain over a valuation ring, the local dimension of the fibre at a prime
over the closed point is the Krull dimension of the generic fibre ring. -/
private theorem affine_fiber_dimension_at_closedPoint_of_valuationRing
    {A B : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B]
    (b : PrimeSpectrum B) (hb : (Spec.map (CommRingCat.ofHom (algebraMap A B))) b =
      IsLocalRing.closedPoint A)
    (hfib : Nontrivial ((IsLocalRing.maximalIdeal A).Fiber B)) :
    topologicalKrullDimAt
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))) b))
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).asFiber b) =
      ringKrullDim ((⊥ : Ideal A).Fiber B) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let m : Ideal A := IsLocalRing.maximalIdeal A
  let ebase := fiberHomeoOfEq f (f b) _ hb
  let xb : f.fiber (IsLocalRing.closedPoint A) := ebase (f.asFiber b)
  let e := (Spec.fiberToSpecResidueFieldIso A B
    (IsLocalRing.closedPoint A)).hom.left.homeomorph
  let p : PrimeSpectrum (m.Fiber B) := e xb
  let q : Spec (.of (m.Fiber B)) ⟶ Spec (.of m.ResidueField) :=
    Spec.map (CommRingCat.ofHom (algebraMap m.ResidueField (m.Fiber B)))
  have : LocallyOfFiniteType q := locallyOfFiniteType_spec_map_algebraMap
  have h00QK :=
    ValuationRing.ringKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot_and_equidimensional
      (R := A) (S := B) hfib
  calc
    topologicalKrullDimAt (f.fiber (f b)) (f.asFiber b)
        = topologicalKrullDimAt (f.fiber (IsLocalRing.closedPoint A)) xb :=
          topologicalKrullDimAt_eq_of_homeomorph ebase (f.asFiber b)
    _ = topologicalKrullDimAt (PrimeSpectrum (m.Fiber B)) p :=
      topologicalKrullDimAt_eq_of_homeomorph e xb
    _ = topologicalKrullDim (Spec (.of (m.Fiber B))) :=
      topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional
        m.ResidueField (Spec (.of (m.Fiber B))) q h00QK.2 p
    _ = ringKrullDim (m.Fiber B) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (m.Fiber B)
    _ = ringKrullDim ((⊥ : Ideal A).Fiber B) := h00QK.1

/-- For a finite type domain over a valuation ring, the local dimension of the fibre at a prime
over the closed point is the dimension of the generic fibre. -/
private theorem affine_closed_fiber_point_dimension_eq_generic_fiber
    {A B : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B]
    (b : PrimeSpectrum B) (hb : (Spec.map (CommRingCat.ofHom (algebraMap A B))) b =
      IsLocalRing.closedPoint A)
    (hfib : Nontrivial ((IsLocalRing.maximalIdeal A).Fiber B)) :
    topologicalKrullDimAt
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))) b))
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).asFiber b) =
      topologicalKrullDim
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
          (genericPoint (Spec (.of A)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let eta : PrimeSpectrum A := ⊥
  have heta : genericPoint (Spec (.of A)) = eta := by
    simpa [eta] using genericPoint_eq_bot_of_affine (.of A)
  have : eta.asIdeal.IsPrime := eta.2
  calc
    topologicalKrullDimAt (f.fiber (f b)) (f.asFiber b) =
        ringKrullDim ((⊥ : Ideal A).Fiber B) :=
      affine_fiber_dimension_at_closedPoint_of_valuationRing b hb hfib
    _ = ringKrullDim (eta.asIdeal.Fiber B) := rfl
    _ = topologicalKrullDim
        (PrimeSpectrum (eta.asIdeal.Fiber B)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ = topologicalKrullDim (f.fiber eta) := (IsHomeomorph.topologicalKrullDim_eq _
      (Spec.fiberToSpecResidueFieldIso A B eta).hom.left.homeomorph.isHomeomorph).symm
    _ = topologicalKrullDim (f.fiber (genericPoint (Spec (.of A)))) := by
      rw [← heta]

/-- On a scheme locally of finite type over a field, the dimension of an irreducible component
is the local dimension at a generic point of that component. -/
theorem topologicalKrullDim_eq_at_generic_component
    (k : Type u) [Field k] (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] (x : X) (C : Set X)
    (hC : C ∈ irreducibleComponents X) (hx : IsGenericPoint x C) :
    topologicalKrullDim C = topologicalKrullDimAt X x := by
  obtain ⟨D, hD, hxD, hDdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X q x
  have hCD : C ⊆ D := by
    rw [← hx.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hxD)
      (isClosed_of_mem_irreducibleComponents D hD)
  rwa [Set.Subset.antisymm hCD (hC.2 hD.1 hCD)]

/-- A closed immersion of schemes locally of finite type over a field preserves the local
dimension at a generic point of a component whose image is again such a point. -/
private theorem localFiberDimAt_eq_of_closedImmersion_genericPoints
    (k : Type u) [Field k] {P Q : Scheme.{u}}
    (j : P ⟶ Q) [IsClosedImmersion j]
    (p : P ⟶ Spec (.of k)) (q : Q ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (x : P) (C : Set P) (hC : C ∈ irreducibleComponents P)
    (hx : IsGenericPoint x C)
    (D : Set Q) (hD : D ∈ irreducibleComponents Q)
    (hjx : IsGenericPoint (j x) D) :
    topologicalKrullDimAt P x = topologicalKrullDimAt Q (j x) := by
  have himage : j '' C = D := by
    rw [← hx.def, ← hjx.def]
    simpa only [Set.image_singleton] using
      (j.isClosedEmbedding.closure_image_eq ({x} : Set P)).symm
  calc
    topologicalKrullDimAt P x = topologicalKrullDim C :=
      (topologicalKrullDim_eq_at_generic_component k P p x C hC hx).symm
    _ = topologicalKrullDim D := by
      rw [← himage]
      exact IsHomeomorph.topologicalKrullDim_eq _
        (j.isEmbedding.homeomorphImage C).isHomeomorph
    _ = topologicalKrullDimAt Q (j x) :=
      topologicalKrullDim_eq_at_generic_component k Q q (j x) D hD hjx

/-- The dimension of the whole space agrees with the dimension of its universal subset. -/
private lemma topologicalKrullDim_univ_eq (X : Type u) [TopologicalSpace X] :
    topologicalKrullDim (Set.univ : Set X) = topologicalKrullDim X :=
  IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
    (Homeomorph.Set.univ X).isHomeomorph

/-- In a pullback square the dimension of the component of a fibre through a point agrees with
the dimension of the corresponding component upstairs. -/
private theorem fiber_component_dimension_eq_under_pullback
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (x' : X')
    (C : Set (f.fiber (f (g' x'))))
    (hC : C ∈ irreducibleComponents (f.fiber (f (g' x'))))
    (hxC : IsGenericPoint (f.asFiber (g' x')) C)
    (C' : Set (f'.fiber (f' x')))
    (hC' : C' ∈ irreducibleComponents (f'.fiber (f' x')))
    (hxC' : IsGenericPoint (f'.asFiber x') C') :
    topologicalKrullDim C = topologicalKrullDim C' := by
  have : LocallyOfFiniteType f' :=
    MorphismProperty.of_isPullback h (P := @LocallyOfFiniteType) inferInstance
  calc
    topologicalKrullDim C =
        topologicalKrullDimAt (f.fiber (f (g' x'))) (f.asFiber (g' x')) :=
      topologicalKrullDim_eq_at_generic_component
        (S.residueField (f (g' x'))) (f.fiber (f (g' x')))
        (f.fiberToSpecResidueField (f (g' x'))) (f.asFiber (g' x')) C hC hxC
    _ = topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') :=
      (AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback h x').symm
    _ = topologicalKrullDim C' :=
      (topologicalKrullDim_eq_at_generic_component
        (S'.residueField (f' x')) (f'.fiber (f' x'))
        (f'.fiberToSpecResidueField (f' x')) (f'.asFiber x') C' hC' hxC').symm

/-- A space with a generic point has itself as its unique irreducible component. -/
private lemma univ_mem_irreducibleComponents_of_genericPoint
    {T : Type u} [TopologicalSpace T] {t : T}
    (ht : IsGenericPoint t (Set.univ : Set T)) :
    (Set.univ : Set T) ∈ irreducibleComponents T :=
  ⟨ht.isIrreducible, fun Z _ _ => Set.subset_univ Z⟩

/-- A homeomorphism carries the closure of a point generating an irreducible component to the
closure of its image, again an irreducible component. -/
private lemma closure_mem_irreducibleComponents_homeomorph
    {P Q : Type u} [TopologicalSpace P] [TopologicalSpace Q]
    (e : P ≃ₜ Q) {x : P}
    (hC : closure ({x} : Set P) ∈ irreducibleComponents P) :
    closure ({e x} : Set Q) ∈ irreducibleComponents Q := by
  have hclosure : e.symm ⁻¹' closure ({x} : Set P) = closure ({e x} : Set Q) := by
    rw [← e.image_eq_preimage_symm, e.image_closure, Set.image_singleton]
  rw [← hclosure]
  exact preimage_mem_irreducibleComponents hC e.symm.isOpenEmbedding
    ⟨x, subset_closure rfl, e x, by simp⟩

/-- A homeomorphism carries a generic point of the whole space to a generic point of the whole
target. -/
private lemma isGenericPoint_univ_homeomorph {P Q : Type u} [TopologicalSpace P]
    [TopologicalSpace Q] (e : P ≃ₜ Q) {x : P} (hx : IsGenericPoint x (Set.univ : Set P)) :
    IsGenericPoint (e x) (Set.univ : Set Q) := by
  simpa [Set.image_univ_of_surjective e.surjective] using hx.image e.continuous

/-- The image in a fibre of a generic point of the source is a generic point of that fibre. -/
private lemma genericPoint_fiber_generic
    {T S : Scheme.{u}} (f : T ⟶ S) (t : T)
    (ht : IsGenericPoint t (Set.univ : Set T)) :
    IsGenericPoint (f.asFiber t) (Set.univ : Set (f.fiber (f t))) := by
  let V : Set T := f ⁻¹' {f t}
  have htV : IsGenericPoint (⟨t, rfl⟩ : V) (Set.univ : Set V) := by
    apply isGenericPoint_def.mpr
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Set.image_singleton, ht.def]
    simp [V]
  let e := f.fiberHomeo (f t)
  have he : e (f.asFiber t) = ⟨t, rfl⟩ := Subtype.ext (by simp [e])
  have he' : e.symm ⟨t, rfl⟩ = f.asFiber t := e.symm_apply_eq.mpr he.symm
  simpa [he'] using isGenericPoint_univ_homeomorph e.symm htV

/-- The homeomorphism between fibres over equal points commutes with the fibre inclusions. -/
private lemma fiberι_fiberHomeoOfEq {X S : Scheme.{u}} (f : X ⟶ S) (s t : S) (h : s = t)
    (ξ : f.fiber s) : f.fiberι t (fiberHomeoOfEq f s t h ξ) = f.fiberι s ξ :=
  calc
    f.fiberι t (fiberHomeoOfEq f s t h ξ) = (f.fiberHomeo t (fiberHomeoOfEq f s t h ξ)).1 :=
      (f.fiberHomeo_apply _ _).symm
    _ = (f.fiberHomeo s ξ).1 := by simp [fiberHomeoOfEq, Homeomorph.setCongr]
    _ = f.fiberι s ξ := f.fiberHomeo_apply _ _

/-- A point of a fibre is carried to the corresponding point of the fibre through its image. -/
private lemma fiberHomeoOfEq_apply_fiberι {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (ξ : f.fiber s) :
    fiberHomeoOfEq f s _ (f.apply_fiberι s ξ).symm ξ = f.asFiber (f.fiberι s ξ) := by
  apply (f.fiberι _).isEmbedding.injective
  rw [fiberι_fiberHomeoOfEq, Scheme.Hom.fiberι_asFiber]

/-- Equal points have equal fibre local dimensions. -/
private lemma fiberLocalDimAt_eq_of_point_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (x y : X) (hxy : x = y) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) := by
  subst hxy
  rfl

/-- Fibres over equal points have equal dimensions. -/
private lemma topologicalKrullDim_fiber_eq_of_eq {X S : Scheme.{u}} (f : X ⟶ S) {s t : S}
    (h : s = t) : topologicalKrullDim (f.fiber s) = topologicalKrullDim (f.fiber t) := by
  subst h
  rfl

/-- The local dimension of a fibre at a point is the local dimension, at the same point, of the
fibre through its image. -/
private lemma topologicalKrullDimAt_fiber_eq_asFiber_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (ξ : f.fiber s) :
    topologicalKrullDimAt (f.fiber s) ξ =
      topologicalKrullDimAt (f.fiber (f (f.fiberι s ξ))) (f.asFiber (f.fiberι s ξ)) := by
  rw [← fiberHomeoOfEq_apply_fiberι]
  exact topologicalKrullDimAt_eq_of_homeomorph _ ξ

/-- A point of a fibre generating an irreducible component still does so in the fibre through its
image. -/
private lemma closure_asFiber_fiberι_mem_irreducibleComponents {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (ξ : f.fiber s)
    (hξ : closure ({ξ} : Set (f.fiber s)) ∈ irreducibleComponents (f.fiber s)) :
    closure ({f.asFiber (f.fiberι s ξ)} : Set (f.fiber (f (f.fiberι s ξ)))) ∈
      irreducibleComponents (f.fiber (f (f.fiberι s ξ))) := by
  rw [← fiberHomeoOfEq_apply_fiberι]
  exact closure_mem_irreducibleComponents_homeomorph _ hξ

/-- For a morphism locally of finite type, the dimension of the fibre through a generic point of
the source is the local dimension of that fibre at the point. -/
private lemma topologicalKrullDim_fiber_eq_topologicalKrullDimAt_of_isGenericPoint
    {T S : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f] (t : T)
    (ht : IsGenericPoint t (Set.univ : Set T)) :
    topologicalKrullDim (f.fiber (f t)) = topologicalKrullDimAt (f.fiber (f t)) (f.asFiber t) := by
  have hgen := genericPoint_fiber_generic f t ht
  rw [← topologicalKrullDim_univ_eq]
  exact topologicalKrullDim_eq_at_generic_component (S.residueField (f t)) (f.fiber (f t))
    (f.fiberToSpecResidueField (f t)) (f.asFiber t) Set.univ
    (univ_mem_irreducibleComponents_of_genericPoint hgen) hgen

/-- Restricting along an open immersion does not change the local dimension of the fibres. -/
private lemma topologicalKrullDimAt_fiber_eq_of_isOpenImmersion {U T S : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (q : T ⟶ S) (q' : U ⟶ S) (hq : j ≫ q = q')
    (u : U) (t : T) (ht : j u = t) :
    topologicalKrullDimAt (q'.fiber (q' u)) (q'.asFiber u) =
      topologicalKrullDimAt (q.fiber (q t)) (q.asFiber t) := by
  subst hq ht
  exact AlgebraicGeometry.fiberDimensionAt_eq_of_open_square j q (j ≫ q) (𝟙 _) (by simp) u

/-- An open subscheme of a scheme with a generic point contains it, and the point over it is a
generic point of the open subscheme. -/
private lemma exists_isGenericPoint_of_isOpenImmersion {U T : Scheme.{u}} (ι : U ⟶ T)
    [IsOpenImmersion ι] {y : T} (hy : IsGenericPoint y (Set.univ : Set T)) (z : T)
    (hz : z ∈ ι.opensRange) : ∃ u : U, ι u = y ∧ IsGenericPoint u (Set.univ : Set U) := by
  have hyOpen : y ∈ ι.opensRange :=
    (specializes_iff_forall_open.mp (hy.specializes (Set.mem_univ z))) ι.opensRange
      ι.opensRange.isOpen hz
  change y ∈ Set.range (fun u : U => ι u) at hyOpen
  obtain ⟨u, hu⟩ := hyOpen
  refine ⟨u, hu, ?_⟩
  rw [isGenericPoint_def, Set.eq_univ_iff_forall]
  intro w
  have hspec : ι u ⤳ ι w := by simpa [hu] using hy.specializes (Set.mem_univ _)
  exact specializes_iff_mem_closure.mp (ι.isOpenEmbedding.isInducing.specializes_iff.mp hspec)

/-- The point of a closed subscheme supported on the closure of `y` lying over `y` is a generic
point of that subscheme. -/
private lemma exists_isGenericPoint_of_support_eq_closure {X : Scheme.{u}}
    (Y : X.IdealSheafData) (y : X) (hY : (Y.support : Set X) = closure ({y} : Set X)) :
    ∃ y₀ : Y.subscheme, Y.subschemeι y₀ = y ∧ IsGenericPoint y₀ (Set.univ : Set Y.subscheme) := by
  have hyY : y ∈ (Y.support : Set X) := by
    rw [hY]
    exact subset_closure rfl
  rw [← Y.range_subschemeι] at hyY
  obtain ⟨y₀, hy₀⟩ := hyY
  refine ⟨y₀, hy₀, isGenericPoint_def.mpr ?_⟩
  rw [Y.subschemeι.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, hy₀,
    ← hY, ← Y.range_subschemeι]
  simp

/-- The reduced closed subscheme supported on the closure of a point of a closed subscheme `Z`
is a closed subscheme of `Z`. -/
private lemma exists_closedImmersion_vanishingIdeal_closure {X : Scheme.{u}}
    (Z : X.IdealSheafData) (z : Z.subscheme) (y : X) (hzy : Z.subschemeι z = y) :
    ∃ n : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set X))).subscheme ⟶ Z.subscheme,
      IsClosedImmersion n ∧ n ≫ Z.subschemeι = (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set X))).subschemeι := by
  let Y' := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))
  have hyZ : Closeds.closure ({y} : Set X) ≤ Z.support := by
    change ((Closeds.closure ({y} : Set X) : Closeds X) : Set X) ≤ Z.support
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) Z.support.isClosed
    rw [← Z.range_subschemeι]
    exact ⟨z, hzy⟩
  have hle : Z ≤ Y'.map (𝟙 X) := by
    simpa using (Z.le_support_iff_le_vanishingIdeal).mp hyZ
  have hn : Scheme.IdealSheafData.subschemeMap Y' Z (𝟙 X) hle ≫ Z.subschemeι =
      Y'.subschemeι := by
    rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
    simp
  have : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap Y' Z (𝟙 X) hle ≫
      Z.subschemeι) := by
    rw [hn]
    infer_instance
  exact ⟨_, IsClosedImmersion.of_comp_isClosedImmersion _ Z.subschemeι, hn⟩

/-- The canonical morphism from the spectrum of the tensor product of residue fields attached to
a point of a pullback is a preimmersion. -/
private theorem triplet_specTensorTo_isPreimmersion
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (T : Scheme.Pullback.Triplet f g) :
    IsPreimmersion T.SpecTensorTo := by
  let a := X.fromSpecResidueField T.x
  let b := Y.fromSpecResidueField T.y
  let i := S.fromSpecResidueField T.s
  let u := Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
  let v := Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)
  have hu : u ≫ i = a ≫ f := by
    dsimp [u, i, a]
    rw [Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField T.hx.symm]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f T.x
  have hv : v ≫ i = b ≫ g := by
    dsimp [v, i, b]
    rw [Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField T.hy.symm]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g T.y
  have hD := T.isPullback_SpecMap_tensor
  have hS : IsPullback (Spec.map T.tensorInl) (Spec.map T.tensorInr)
      (a ≫ f) (b ≫ g) := by
    rw [← hu, ← hv]
    exact IsPullback.of_isLimit <|
      CategoryTheory.Limits.PullbackCone.isLimitOfCompMono u v i
        (CategoryTheory.Limits.PullbackCone.mk
          (Spec.map T.tensorInl) (Spec.map T.tensorInr) hD.w)
        hD.isLimit
  let m := Limits.pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 _) (by simp) (by simp)
  have hm : IsPreimmersion m := by
    let : MorphismProperty.IsStableUnderComposition @IsPreimmersion :=
      ⟨fun f g hf hg => IsPreimmersion.comp f g⟩
    exact MorphismProperty.pullbackMap (P := @IsPreimmersion)
      (inferInstance : IsPreimmersion a) (inferInstance : IsPreimmersion b)
      rfl rfl
  have hcomp : hS.isoPullback.hom ≫ m = T.SpecTensorTo := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · simp only [m, Limits.pullback.map]
      rw [Category.assoc, Limits.pullback.lift_fst, ← Category.assoc, hS.isoPullback_hom_fst]
      simp [a, T.specTensorTo_fst]
    · simp only [m, Limits.pullback.map]
      rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, hS.isoPullback_hom_snd]
      simp [b, T.specTensorTo_snd]
  rw [← hcomp]
  infer_instance

/-- A point of a pullback of schemes whose associated point in the spectrum of the tensor product
of residue fields is a generic point has no proper generalization with the same two images. -/
private lemma eq_of_specializes_of_triplet_isGenericPoint
    {X S S' : Scheme.{u}} (f : X ⟶ S) (gA : S' ⟶ S)
    (x' w : ↥(Limits.pullback f gA))
    (htrip : Scheme.Pullback.Triplet.ofPoint w = Scheme.Pullback.Triplet.ofPoint x')
    (hwx : w ⤳ x')
    (hgen : Scheme.Pullback.SpecOfPoint x' ∈
      genericPoints (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor)) :
    w = x' := by
  let T : Scheme.Pullback.Triplet f gA := Scheme.Pullback.Triplet.ofPoint x'
  let eT := Scheme.Pullback.Triplet.tensorCongr htrip
  let r : Spec T.tensor := Spec.map eT.inv (Scheme.Pullback.SpecOfPoint w)
  have hwrep : T.SpecTensorTo r = w := by
    calc
      T.SpecTensorTo r = (Scheme.Pullback.Triplet.ofPoint w).SpecTensorTo
          (Spec.map eT.hom r) := by
        simpa only [Scheme.Hom.comp_apply] using
          (congrArg (fun k : Spec T.tensor ⟶ Limits.pullback f gA => k r)
            (Scheme.Pullback.tensorCongr_SpecTensorTo htrip)).symm
      _ = (Scheme.Pullback.Triplet.ofPoint w).SpecTensorTo
          (Scheme.Pullback.SpecOfPoint w) := by
            congr 1
            change ((Spec.map eT.inv ≫ Spec.map eT.hom)
              (Scheme.Pullback.SpecOfPoint w)) = _
            rw [← Spec.map_comp]
            simp [eT]
      _ = w := Scheme.Pullback.SpecTensorTo_SpecOfPoint w
  have hxrep : T.SpecTensorTo (Scheme.Pullback.SpecOfPoint x') = x' := by
    simp [T]
  have hspecT : r ⤳ Scheme.Pullback.SpecOfPoint x' := by
    have : IsPreimmersion T.SpecTensorTo :=
      triplet_specTensorTo_isPreimmersion f gA T
    apply T.SpecTensorTo.isEmbedding.isInducing.specializes_iff.mp
    rwa [hwrep, hxrep]
  calc
    w = T.SpecTensorTo r := hwrep.symm
    _ = T.SpecTensorTo (Scheme.Pullback.SpecOfPoint x') :=
      congrArg T.SpecTensorTo
        ((mem_genericPoints_iff_forall_specializes_eq _).mp hgen r hspecT)
    _ = x' := hxrep

/-- A closed immersion over an affine base preserves the local dimension of a fibre at a generic
point of a component whose image is again such a point. -/
private lemma localFibreDim_eq_of_closedImmersion_over_affine
    {A : Type u} [CommRing A] {P Q : Scheme.{u}} (n : P ⟶ Q) [IsClosedImmersion n]
    (qP : P ⟶ Spec (.of A)) (qQ : Q ⟶ Spec (.of A))
    [LocallyOfFiniteType qP] [LocallyOfFiniteType qQ] (hn : n ≫ qQ = qP)
    (s : Spec (.of A)) (ξ : qP.fiber s) (ζ : qQ.fiber s)
    (hζ : n (qP.fiberι s ξ) = qQ.fiberι s ζ)
    (C : Set (qP.fiber s)) (hC : C ∈ irreducibleComponents (qP.fiber s))
    (hξC : IsGenericPoint ξ C)
    (D : Set (qQ.fiber s)) (hD : D ∈ irreducibleComponents (qQ.fiber s))
    (hζD : IsGenericPoint ζ D) :
    topologicalKrullDimAt (qP.fiber s) ξ = topologicalKrullDimAt (qQ.fiber s) ζ := by
  have : s.asIdeal.IsPrime := s.2
  let k := (Spec (.of A)).fromSpecResidueField s
  let nF : qP.fiber s ⟶ qQ.fiber s :=
    Limits.pullback.map qP k qQ k n (𝟙 _) (𝟙 _) (by simpa using hn.symm) (by simp)
  have hnF_fst : nF ≫ qQ.fiberι s = qP.fiberι s ≫ n := by
    change Limits.pullback.lift (Limits.pullback.fst qP k ≫ n)
        (Limits.pullback.snd qP k) _ ≫ Limits.pullback.fst qQ k =
        Limits.pullback.fst qP k ≫ n
    exact Limits.pullback.lift_fst _ _ _
  have hnFξ : nF ξ = ζ :=
    (qQ.fiberι s).isEmbedding.injective <|
      (congrArg (fun h : qP.fiber s ⟶ Q => h ξ) hnF_fst).trans hζ
  have hnF : IsClosedImmersion nF := by
    let : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
      ⟨fun f g hf hg => by
        have : IsClosedImmersion f := hf
        have : IsClosedImmersion g := hg
        infer_instance⟩
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion n) (inferInstance : IsClosedImmersion (𝟙 _))
      (by simpa using hn.symm) (by simp)
  let eₛ := Scheme.Spec.residueFieldIso (.of A) s
  let pP := qP.fiberToSpecResidueField s ≫ Spec.map eₛ.inv
  let pQ := qQ.fiberToSpecResidueField s ≫ Spec.map eₛ.inv
  have : LocallyOfFiniteType pP := locallyOfFiniteType_comp _ _
  have : LocallyOfFiniteType pQ := locallyOfFiniteType_comp _ _
  simpa only [hnFξ] using localFiberDimAt_eq_of_closedImmersion_genericPoints
    (k := s.asIdeal.ResidueField) nF pP pQ ξ C hC hξC D hD (by simpa only [hnFξ] using hζD)

/-- A point whose image in its fibre generates an irreducible component of that fibre has no
proper generalization in the fibre. -/
private lemma eq_of_specializes_of_closure_asFiber_mem {V S : Scheme.{u}} (g : V ⟶ S) (v w : V)
    (hgen : closure ({g.asFiber v} : Set (g.fiber (g v))) ∈ irreducibleComponents (g.fiber (g v)))
    (hwv : w ⤳ v) (hw : g w = g v) : w = v := by
  have hgen' : g.asFiber v ∈ genericPoints (g.fiber (g v)) := hgen
  have hw' : g.fiberι (g v) ((g.fiberHomeo (g v)).symm ⟨w, hw⟩) = w :=
    g.fiberι_fiberHomeo_symm _ _
  have hspec : (g.fiberHomeo (g v)).symm ⟨w, hw⟩ ⤳ g.asFiber v := by
    apply (g.fiberι (g v)).isEmbedding.isInducing.specializes_iff.mp
    rwa [hw', Scheme.Hom.fiberι_asFiber]
  rw [← hw', (mem_genericPoints_iff_forall_specializes_eq _).mp hgen' _ hspec,
    Scheme.Hom.fiberι_asFiber]

/-- Let `W` be a closed subscheme of a pullback `X ×_S S'` mapping to `V`, and `z` a point of `W`
whose image in `V` is generic in its fibre over `S` and whose point in the spectrum of the tensor
product of residue fields is generic. Then `z` is generic in its fibre over `S'`. -/
private lemma closure_asFiber_mem_irreducibleComponents_of_isGenericPoint_tensor
    {X S S' V W : Scheme.{u}} (f : X ⟶ S) (gA : S' ⟶ S) (g : V ⟶ S) (m : W ⟶ V)
    (j : W ⟶ Limits.pullback f gA) [IsClosedImmersion j] (ι : V ⟶ X) (qW : W ⟶ S')
    (hqW : j ≫ Limits.pullback.snd f gA = qW) (hw : j ≫ Limits.pullback.fst f gA = m ≫ ι)
    (hg : m ≫ g = qW ≫ gA) (z : W)
    (hgen : closure ({g.asFiber (m z)} : Set (g.fiber (g (m z)))) ∈
      irreducibleComponents (g.fiber (g (m z))))
    (htensor : Scheme.Pullback.SpecOfPoint (j z) ∈
      genericPoints (Spec (Scheme.Pullback.Triplet.ofPoint (j z)).tensor)) :
    closure ({qW.asFiber z} : Set (qW.fiber (qW z))) ∈ irreducibleComponents (qW.fiber (qW z)) := by
  change qW.asFiber z ∈ genericPoints (qW.fiber (qW z))
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun a ha => ?_
  have ha' : qW.fiberι (qW z) a ⤳ z := by
    simpa using ha.map (qW.fiberι (qW z)).continuous
  have hqa : qW (qW.fiberι (qW z) a) = qW z := qW.apply_fiberι _ a
  have h₁ := congrArg (fun k : W ⟶ S => k (qW.fiberι (qW z) a)) hg
  have h₂ := congrArg (fun k : W ⟶ S => k z) hg
  have h₃ := congrArg (fun k : W ⟶ X => k (qW.fiberι (qW z) a)) hw
  have h₄ := congrArg (fun k : W ⟶ X => k z) hw
  have h₅ := congrArg (fun k : W ⟶ S' => k (qW.fiberι (qW z) a)) hqW
  have h₆ := congrArg (fun k : W ⟶ S' => k z) hqW
  simp only [Scheme.Hom.comp_apply] at h₁ h₂ h₃ h₄ h₅ h₆
  have hma : m (qW.fiberι (qW z) a) = m z :=
    eq_of_specializes_of_closure_asFiber_mem g (m z) _ hgen (ha'.map m.continuous)
      (by rw [h₁, h₂, hqa])
  have hpw : Limits.pullback.fst f gA (j (qW.fiberι (qW z) a)) =
      Limits.pullback.fst f gA (j z) := by
    rw [h₃, h₄, hma]
  have hqw : Limits.pullback.snd f gA (j (qW.fiberι (qW z) a)) =
      Limits.pullback.snd f gA (j z) := by
    rw [h₅, h₆, hqa]
  apply (qW.fiberι (qW z)).isEmbedding.injective
  rw [Scheme.Hom.fiberι_asFiber]
  exact j.isEmbedding.injective <| eq_of_specializes_of_triplet_isGenericPoint f gA (j z)
    (j (qW.fiberι (qW z) a)) (Scheme.Pullback.Triplet.ext hpw hqw) (ha'.map j.continuous) htensor

/-- In the base change configuration of `topologicalKrullDimAt_fiber_eq_fiber_of_flat`, the local
dimension of the fibre of `g` at `x` equals the local dimension at `ξ` of the corresponding fibre
of the closed subscheme `U` of the base change. -/
private theorem topologicalKrullDimAt_fiber_eq_of_closedImmersion_baseChange
    {A : Type u} [CommRing A] {X S U V W : Scheme.{u}} (f : X ⟶ S)
    (gA : Spec (.of A) ⟶ S) (ι : V ⟶ X) (g : V ⟶ S) [LocallyOfFiniteType g] (m : W ⟶ V)
    (j : W ⟶ Limits.pullback f gA) [IsClosedImmersion j] (qZ : W ⟶ Spec (.of A))
    (hqZ : j ≫ Limits.pullback.snd f gA = qZ) (hw : j ≫ Limits.pullback.fst f gA = m ≫ ι)
    (hpb : IsPullback m qZ g gA) (n : U ⟶ W) [IsClosedImmersion n] (qY : U ⟶ Spec (.of A))
    [LocallyOfFiniteType qY] [LocallyOfFiniteType qZ] (hn : n ≫ qZ = qY)
    (s₀ : Spec (.of A)) (ξ : qY.fiber s₀)
    (hξ : closure ({ξ} : Set (qY.fiber s₀)) ∈ irreducibleComponents (qY.fiber s₀))
    (s : S) (x : g.fiber s)
    (hx : closure ({x} : Set (g.fiber s)) ∈ irreducibleComponents (g.fiber s))
    (hpoint : m (n (qY.fiberι s₀ ξ)) = g.fiberι s x) (x' : ↥(Limits.pullback f gA))
    (hjx : j (n (qY.fiberι s₀ ξ)) = x')
    (htensor : Scheme.Pullback.SpecOfPoint x' ∈
      genericPoints (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor)) :
    topologicalKrullDimAt (g.fiber s) x = topologicalKrullDimAt (qY.fiber s₀) ξ := by
  subst hjx
  have hqz : qZ (n (qY.fiberι s₀ ξ)) = s₀ :=
    (congrArg (fun k : U ⟶ Spec (.of A) => k (qY.fiberι s₀ ξ)) hn).trans (qY.apply_fiberι s₀ ξ)
  have hgen := closure_asFiber_fiberι_mem_irreducibleComponents g s x hx
  rw [← hpoint] at hgen
  have hzgen := closure_asFiber_mem_irreducibleComponents_of_isGenericPoint_tensor f gA g m j ι
    qZ hqZ hw hpb.w (n (qY.fiberι s₀ ξ)) hgen htensor
  have hez : qZ.fiberι s₀ (fiberHomeoOfEq qZ _ s₀ hqz (qZ.asFiber (n (qY.fiberι s₀ ξ)))) =
      n (qY.fiberι s₀ ξ) := by
    rw [fiberι_fiberHomeoOfEq, Scheme.Hom.fiberι_asFiber]
  calc
    topologicalKrullDimAt (g.fiber s) x =
        topologicalKrullDimAt (g.fiber (g (g.fiberι s x))) (g.asFiber (g.fiberι s x)) :=
      topologicalKrullDimAt_fiber_eq_asFiber_fiberι g s x
    _ = topologicalKrullDimAt (g.fiber (g (m (n (qY.fiberι s₀ ξ)))))
        (g.asFiber (m (n (qY.fiberι s₀ ξ)))) :=
      fiberLocalDimAt_eq_of_point_eq g _ _ hpoint.symm
    _ = topologicalKrullDimAt (qZ.fiber (qZ (n (qY.fiberι s₀ ξ))))
        (qZ.asFiber (n (qY.fiberι s₀ ξ))) :=
      (AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback hpb _).symm
    _ = topologicalKrullDimAt (qZ.fiber s₀)
        (fiberHomeoOfEq qZ _ s₀ hqz (qZ.asFiber (n (qY.fiberι s₀ ξ)))) :=
      topologicalKrullDimAt_eq_of_homeomorph _ _
    _ = topologicalKrullDimAt (qY.fiber s₀) ξ :=
      (localFibreDim_eq_of_closedImmersion_over_affine n qY qZ hn s₀ ξ _ hez.symm
        (closure {ξ}) hξ (isGenericPoint_closure (x := ξ)) _
        (closure_mem_irreducibleComponents_homeomorph (fiberHomeoOfEq qZ _ s₀ hqz)
          (x := qZ.asFiber (n (qY.fiberι s₀ ξ))) hzgen)
        isGenericPoint_closure).symm

/-- In the base change configuration of `topologicalKrullDimAt_fiber_eq_fiber_of_flat`, the
dimension of the fibre of the closed subscheme `U` through a generic point `y` equals the
dimension of the fibre of `g` through the image of `y`. -/
private theorem topologicalKrullDim_fiber_eq_of_closedImmersion_baseChange
    {A : Type u} [CommRing A] {S U V W : Scheme.{u}} (m : W ⟶ V) (qZ : W ⟶ Spec (.of A))
    (g : V ⟶ S) (gA : Spec (.of A) ⟶ S) [LocallyOfFiniteType g] (hpb : IsPullback m qZ g gA)
    (n : U ⟶ W) [IsClosedImmersion n] (qY : U ⟶ Spec (.of A)) [LocallyOfFiniteType qY]
    [LocallyOfFiniteType qZ] (hn : n ≫ qZ = qY) (y : U)
    (hy : IsGenericPoint y (Set.univ : Set U))
    (hmy : IsGenericPoint (m (n y)) (Set.univ : Set V)) (s₀ : Spec (.of A)) (η : qZ.fiber s₀)
    (hη : closure ({η} : Set (qZ.fiber s₀)) ∈ irreducibleComponents (qZ.fiber s₀))
    (hηy : qZ.fiberι s₀ η = n y) :
    topologicalKrullDim (qY.fiber (qY y)) = topologicalKrullDim (g.fiber (g (m (n y)))) := by
  have hqy : qY y = s₀ := by
    rw [← hn, Scheme.Hom.comp_apply, ← hηy, Scheme.Hom.apply_fiberι]
  have hηY : IsGenericPoint (fiberHomeoOfEq qY (qY y) s₀ hqy (qY.asFiber y))
      (Set.univ : Set (qY.fiber s₀)) :=
    isGenericPoint_univ_homeomorph _ (genericPoint_fiber_generic qY y hy)
  have hnη : n (qY.fiberι s₀ (fiberHomeoOfEq qY (qY y) s₀ hqy (qY.asFiber y))) =
      qZ.fiberι s₀ η := by
    rw [fiberι_fiberHomeoOfEq, Scheme.Hom.fiberι_asFiber, hηy]
  calc
    topologicalKrullDim (qY.fiber (qY y)) =
        topologicalKrullDimAt (qY.fiber (qY y)) (qY.asFiber y) :=
      topologicalKrullDim_fiber_eq_topologicalKrullDimAt_of_isGenericPoint qY y hy
    _ = topologicalKrullDimAt (qY.fiber s₀) (fiberHomeoOfEq qY (qY y) s₀ hqy (qY.asFiber y)) :=
      topologicalKrullDimAt_eq_of_homeomorph _ _
    _ = topologicalKrullDimAt (qZ.fiber s₀) η :=
      localFibreDim_eq_of_closedImmersion_over_affine n qY qZ hn s₀ _ η hnη Set.univ
        (univ_mem_irreducibleComponents_of_genericPoint hηY) hηY (closure {η}) hη
        (isGenericPoint_closure (x := η))
    _ = topologicalKrullDimAt (qZ.fiber (qZ (n y))) (qZ.asFiber (n y)) := by
      rw [topologicalKrullDimAt_fiber_eq_asFiber_fiberι qZ s₀ η, hηy]
    _ = topologicalKrullDimAt (g.fiber (g (m (n y)))) (g.asFiber (m (n y))) :=
      AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback hpb (n y)
    _ = topologicalKrullDim (g.fiber (g (m (n y)))) :=
      (topologicalKrullDim_fiber_eq_topologicalKrullDimAt_of_isGenericPoint g _ hmy).symm

/-- For a finite type domain over a valuation ring whose generic point lies over the generic point
of the base, the local dimension of the fibre at a point over the closed point equals the local
dimension of the generic fibre at the generic point. -/
private theorem affine_valuation_fiber_dimension_bridge
    {A B : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B]
    (b : PrimeSpectrum B) (hb : (Spec.map (CommRingCat.ofHom (algebraMap A B))) b =
      IsLocalRing.closedPoint A)
    (hgen : (Spec.map (CommRingCat.ofHom (algebraMap A B))) (genericPoint (Spec (.of B))) =
      genericPoint (Spec (.of A))) :
    topologicalKrullDimAt
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))) b))
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).asFiber b) =
      topologicalKrullDimAt
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).fiber
          ((Spec.map (CommRingCat.ofHom (algebraMap A B))) (genericPoint (Spec (.of B)))))
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).asFiber
          (genericPoint (Spec (.of B)))) := by
  let fb := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : FaithfulSMul A B := by
    apply (faithfulSMul_iff_algebraMap_injective A B).2
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine] at hgen
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot]
    exact congrArg PrimeSpectrum.asIdeal hgen
  have : Nontrivial ((IsLocalRing.maximalIdeal A).Fiber B) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp
      ⟨(Spec.fiberToSpecResidueFieldIso A B (IsLocalRing.closedPoint A)).hom.left.homeomorph
        (fiberHomeoOfEq fb _ _ hb (fb.asFiber b))⟩
  have : LocallyOfFiniteType fb := locallyOfFiniteType_spec_map_algebraMap
  rw [affine_closed_fiber_point_dimension_eq_generic_fiber b hb inferInstance, ← hgen]
  exact topologicalKrullDim_fiber_eq_topologicalKrullDimAt_of_isGenericPoint _ _
    (genericPoint_spec (Spec (.of B)))

/-- Over a valuation ring, the local dimension of the closed fibre of an integral scheme locally
of finite type whose generic point lies over the generic point of the base equals the dimension
of the generic fibre. -/
private theorem valuation_fiber_dimension_bridge
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {T : Scheme.{u}} [IsIntegral T]
    (q : T ⟶ Spec (.of A)) [LocallyOfFiniteType q]
    (y : T) (hy : IsGenericPoint y (Set.univ : Set T))
    (hyq : q y = genericPoint (Spec (.of A)))
    (ξ : q.fiber (IsLocalRing.closedPoint A)) :
    topologicalKrullDimAt (q.fiber (IsLocalRing.closedPoint A)) ξ =
      topologicalKrullDim (q.fiber (genericPoint (Spec (.of A)))) := by
  classical
  let z := q.fiberι (IsLocalRing.closedPoint A) ξ
  let i := T.affineCover.idx z
  let ι := T.affineCover.f i
  obtain ⟨t, ht⟩ := T.affineCover.covers z
  let T₀ := T.affineCover.X i
  have : Nonempty T₀ := ⟨t⟩
  have : IsIntegral T₀ := isIntegral_of_isOpenImmersion ι
  let q₀ : T₀ ⟶ Spec (.of A) := ι ≫ q
  have : LocallyOfFiniteType q₀ := inferInstanceAs (LocallyOfFiniteType (ι ≫ q))
  let B : Type u := Γ(T₀, ⊤)
  let qSpec : Spec (.of B) ⟶ Spec (.of A) := T₀.isoSpec.inv ≫ q₀
  have : LocallyOfFiniteType qSpec :=
    inferInstanceAs (LocallyOfFiniteType (T₀.isoSpec.inv ≫ q₀))
  let e := Spec.fullyFaithful.preimage qSpec
  let : Algebra A B := e.unop.hom.toAlgebra
  have hmap : qSpec = Spec.map (CommRingCat.ofHom (algebraMap A B)) :=
    (Spec.fullyFaithful.map_preimage qSpec).symm
  have : Algebra.FiniteType A B := by
    rw [← RingHom.finiteType_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (hmap ▸ inferInstance)
  have hcomp : (T₀.isoSpec.inv ≫ ι) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A B)) :=
    (Category.assoc _ _ _).trans hmap
  obtain ⟨ty, hty, htygen⟩ :=
    exists_isGenericPoint_of_isOpenImmersion ι hy z (T.affineCover.covers z)
  have hbη : T₀.isoSpec.hom ty = genericPoint (Spec (.of B)) := by
    simpa [htygen.eq (genericPoint_spec T₀)] using
      genericPoint_eq_of_isOpenImmersion T₀.isoSpec.hom
  have hη : (T₀.isoSpec.inv ≫ ι) (genericPoint (Spec (.of B))) = y := by
    rw [← hbη]
    simpa using hty
  have hb : (T₀.isoSpec.inv ≫ ι) (T₀.isoSpec.hom t) = z := by simpa using ht
  let fb := Spec.map (CommRingCat.ofHom (algebraMap A B))
  calc
    topologicalKrullDimAt (q.fiber (IsLocalRing.closedPoint A)) ξ =
        topologicalKrullDimAt (q.fiber (q z)) (q.asFiber z) :=
      topologicalKrullDimAt_fiber_eq_asFiber_fiberι q _ ξ
    _ = topologicalKrullDimAt (fb.fiber (fb (T₀.isoSpec.hom t)))
        (fb.asFiber (T₀.isoSpec.hom t)) :=
      (topologicalKrullDimAt_fiber_eq_of_isOpenImmersion _ q fb hcomp _ z hb).symm
    _ = topologicalKrullDimAt (fb.fiber (fb (genericPoint (Spec (.of B)))))
        (fb.asFiber (genericPoint (Spec (.of B)))) :=
      affine_valuation_fiber_dimension_bridge (T₀.isoSpec.hom t)
        (by
          rw [← hcomp]
          exact (congrArg q hb).trans (q.apply_fiberι _ ξ))
        (by
          rw [← hcomp]
          exact (congrArg q hη).trans hyq)
    _ = topologicalKrullDimAt (q.fiber (q y)) (q.asFiber y) :=
      topologicalKrullDimAt_fiber_eq_of_isOpenImmersion _ q fb hcomp _ y hη
    _ = topologicalKrullDim (q.fiber (q y)) :=
      (topologicalKrullDim_fiber_eq_topologicalKrullDimAt_of_isGenericPoint q y hy).symm
    _ = topologicalKrullDim (q.fiber (genericPoint (Spec (.of A)))) := by rw [hyq]

/-- In the base change configuration of `topologicalKrullDimAt_fiber_eq_fiber_of_flat` over a
valuation ring, the local dimension of the fibre of `g` at `x` equals the dimension of the fibre
of `g` through the image of the generic point `η` of the generic fibre. -/
private theorem topologicalKrullDimAt_fiber_eq_of_valuation_baseChange
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] {X S U V W : Scheme.{u}}
    (f : X ⟶ S) (gA : Spec (.of A) ⟶ S) (ι : V ⟶ X) [IsClosedImmersion ι] (g : V ⟶ S)
    [LocallyOfFiniteType g] (m : W ⟶ V) (j : W ⟶ Limits.pullback f gA) [IsClosedImmersion j]
    (qZ : W ⟶ Spec (.of A)) [LocallyOfFiniteType qZ]
    (hqZ : j ≫ Limits.pullback.snd f gA = qZ) (hw : j ≫ Limits.pullback.fst f gA = m ≫ ι)
    (hpb : IsPullback m qZ g gA) (n : U ⟶ W) [IsClosedImmersion n] [IsIntegral U]
    (qY : U ⟶ Spec (.of A)) [LocallyOfFiniteType qY] (hn : n ≫ qZ = qY)
    (η : qZ.fiber (genericPoint (Spec (.of A))))
    (hη : closure ({η} : Set (qZ.fiber (genericPoint (Spec (.of A))))) ∈
      irreducibleComponents (qZ.fiber (genericPoint (Spec (.of A)))))
    (hmη : IsGenericPoint (m (qZ.fiberι _ η)) (Set.univ : Set V))
    (y : U) (hy : n y = qZ.fiberι _ η) (hygen : IsGenericPoint y (Set.univ : Set U))
    (ξ : qY.fiber (IsLocalRing.closedPoint A))
    (hξ : closure ({ξ} : Set (qY.fiber (IsLocalRing.closedPoint A))) ∈
      irreducibleComponents (qY.fiber (IsLocalRing.closedPoint A)))
    (s : S) (x : g.fiber s)
    (hx : closure ({x} : Set (g.fiber s)) ∈ irreducibleComponents (g.fiber s))
    (x' : ↥(Limits.pullback f gA)) (hjx : j (n (qY.fiberι _ ξ)) = x')
    (hpx : Limits.pullback.fst f gA x' = ι (g.fiberι s x))
    (htensor : ∃ P ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor),
      IsGenericPoint (Scheme.Pullback.SpecOfPoint x') P) :
    topologicalKrullDimAt (g.fiber s) x =
      topologicalKrullDim (g.fiber (g (m (qZ.fiberι _ η)))) := by
  obtain ⟨P, hP, hxP⟩ := htensor
  have hqY : qY y = genericPoint (Spec (.of A)) := by
    rw [← hn, Scheme.Hom.comp_apply, hy, Scheme.Hom.apply_fiberι]
  calc
    topologicalKrullDimAt (g.fiber s) x =
        topologicalKrullDimAt (qY.fiber (IsLocalRing.closedPoint A)) ξ :=
      topologicalKrullDimAt_fiber_eq_of_closedImmersion_baseChange f gA ι g m j qZ hqZ hw hpb n
        qY hn _ ξ hξ s x hx (ι.isEmbedding.injective <| by
          simpa only [Scheme.Hom.comp_apply, hjx, hpx] using
            congrArg (fun k : W ⟶ X => k (n (qY.fiberι _ ξ))) hw.symm) x' hjx (by
          change closure ({Scheme.Pullback.SpecOfPoint x'} :
              Set (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor)) ∈
            irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor)
          rwa [hxP.def])
    _ = topologicalKrullDim (qY.fiber (genericPoint (Spec (.of A)))) :=
      valuation_fiber_dimension_bridge qY y hygen hqY ξ
    _ = topologicalKrullDim (qY.fiber (qY y)) := topologicalKrullDim_fiber_eq_of_eq qY hqY.symm
    _ = topologicalKrullDim (g.fiber (g (m (n y)))) :=
      topologicalKrullDim_fiber_eq_of_closedImmersion_baseChange m qZ g gA hpb n qY hn y hygen
        (by rwa [hy]) _ η hη hy.symm
    _ = topologicalKrullDim (g.fiber (g (m (qZ.fiberι _ η)))) := by rw [hy]

/-- In the configuration of `topologicalKrullDimAt_fiber_eq_fiber_of_flat` after a valuation ring
base change, the local dimension of the fibre of the closed subscheme `Y` at `x` equals the
dimension of the fibre of `Y` over the image of `y`. -/
private theorem topologicalKrullDimAt_fiber_eq_of_valuation_comap
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (gA : Spec (.of A) ⟶ S) (y : X)
    (Y : X.IdealSheafData) (hY : (Y.support : Set X) = closure ({y} : Set X))
    (s : S) (x : (Y.subschemeι ≫ f).fiber s)
    (hx : closure ({x} : Set ((Y.subschemeι ≫ f).fiber s)) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber s))
    (Z : (Limits.pullback f gA).IdealSheafData) (m : Z.subscheme ⟶ Y.subscheme)
    (hcomap : IsPullback Z.subschemeι m (Limits.pullback.fst f gA) Y.subschemeι)
    (η : (Z.subschemeι ≫ Limits.pullback.snd f gA).fiber (genericPoint (Spec (.of A))))
    (hη : closure ({η} : Set ((Z.subschemeι ≫ Limits.pullback.snd f gA).fiber
        (genericPoint (Spec (.of A))))) ∈
      irreducibleComponents ((Z.subschemeι ≫ Limits.pullback.snd f gA).fiber
        (genericPoint (Spec (.of A)))))
    (y' : ↥(Limits.pullback f gA))
    (hy' : Z.subschemeι ((Z.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ η) = y')
    (hpy : Limits.pullback.fst f gA y' = y) (Y' : (Limits.pullback f gA).IdealSheafData)
    (hY' : Y' = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y'} : Set ↥(Limits.pullback f gA))))
    [IsIntegral Y'.subscheme]
    (ξ : (Y'.subschemeι ≫ Limits.pullback.snd f gA).fiber (IsLocalRing.closedPoint A))
    (hξ : closure ({ξ} : Set ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiber
        (IsLocalRing.closedPoint A))) ∈
      irreducibleComponents ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiber
        (IsLocalRing.closedPoint A)))
    (hpx : Limits.pullback.fst f gA
        (Y'.subschemeι ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ ξ)) =
      Y.subschemeι ((Y.subschemeι ≫ f).fiberι s x))
    (htensor : ∃ P ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint
        (Y'.subschemeι ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ ξ))).tensor),
      IsGenericPoint (Scheme.Pullback.SpecOfPoint
        (Y'.subschemeι ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ ξ))) P) :
    topologicalKrullDimAt ((Y.subschemeι ≫ f).fiber s) x =
      topologicalKrullDim ((Y.subschemeι ≫ f).fiber (f y)) := by
  have hpb : IsPullback m (Z.subschemeι ≫ Limits.pullback.snd f gA) (Y.subschemeι ≫ f) gA := by
    simpa only [Category.assoc] using hcomap.flip.paste_vert (IsPullback.of_hasPullback f gA)
  obtain ⟨y₀, hy₀, hy₀gen⟩ := exists_isGenericPoint_of_support_eq_closure Y y hY
  let zη := (Z.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ η
  have hmyz : Y.subschemeι (m zη) = y := by
    rw [← hpy, ← hy']
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : Z.subscheme ⟶ X => k zη) hcomap.w.symm
  have hmygen : IsGenericPoint (m zη) (Set.univ : Set Y.subscheme) := by
    simpa only [Y.subschemeι.isEmbedding.injective (hmyz.trans hy₀.symm)] using hy₀gen
  obtain ⟨n, hn, hncomp⟩ : ∃ n : Y'.subscheme ⟶ Z.subscheme,
      IsClosedImmersion n ∧ n ≫ Z.subschemeι = Y'.subschemeι := by
    subst hY'
    exact exists_closedImmersion_vanishingIdeal_closure Z zη y' hy'
  obtain ⟨y₁, hy₁, hy₁gen⟩ := exists_isGenericPoint_of_support_eq_closure Y' y' (by
    subst hY'
    simp)
  have hncomm : n ≫ Z.subschemeι ≫ Limits.pullback.snd f gA =
      Y'.subschemeι ≫ Limits.pullback.snd f gA := by
    rw [← Category.assoc, hncomp]
  have hzξ : Z.subschemeι (n ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ ξ)) =
      Y'.subschemeι ((Y'.subschemeι ≫ Limits.pullback.snd f gA).fiberι _ ξ) :=
    congrArg (fun k : Y'.subscheme ⟶ _ => k _) hncomp
  have hny₁ : n y₁ = zη := Z.subschemeι.isEmbedding.injective
    ((congrArg (fun k : Y'.subscheme ⟶ _ => k y₁) hncomp).trans (hy₁.trans hy'.symm))
  calc
    _ = topologicalKrullDim ((Y.subschemeι ≫ f).fiber ((Y.subschemeι ≫ f) (m zη))) :=
      topologicalKrullDimAt_fiber_eq_of_valuation_baseChange f gA Y.subschemeι
        (Y.subschemeι ≫ f) m Z.subschemeι _ rfl hcomap.w hpb n _ hncomm η hη hmygen y₁ hny₁
        hy₁gen ξ hξ s x hx _ hzξ hpx htensor
    _ = _ := topologicalKrullDim_fiber_eq_of_eq _ (congrArg f hmyz :
      (Y.subschemeι ≫ f) (m zη) = f y)

/-- **Fibre dimension at a generic point of the fibre of a closure.** Let `f : X ⟶ S` be locally
of finite type, `F` a quasi-coherent finite type `𝒪_X`-module and `y` a point of `Ass_{X/S}(F)`.
Let `Y` be the reduced closed subscheme supported on the closure of `y`. At a generic point `x`
of an irreducible component of the fibre of `Y` over `s` at whose image `F` is flat over `S`, the
local dimension of that fibre equals the dimension of the fibre of `Y` over `f y`. -/
@[stacks 0GSI "the fibre dimension equality",
  ega "IV 12.1.1.4" "fibre dimension equality",
  ega "IV 12.1.1.5" "dim(Z'_y)=dim(Z'_{y'})"]
theorem topologicalKrullDimAt_fiber_eq_fiber_of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ Stacks.Divisors.relativeAssassin f F) (s : S) :
    let Y := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({y} : Set X), isClosed_closure⟩ : Closeds X)
    let g : Y.subscheme ⟶ S := Y.subschemeι ≫ f
    ∀ x : g.fiber s,
      (∃ Z : irreducibleComponents (g.fiber s), IsGenericPoint x (Z : Set (g.fiber s))) →
      AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F (Y.subschemeι (g.fiberι s x)) →
      topologicalKrullDimAt (g.fiber s) x = topologicalKrullDim (g.fiber (f y)) := by
  classical
  intro Y g x ⟨C, hC⟩ hflat
  have hCclosure : closure ({x} : Set (g.fiber s)) ∈ irreducibleComponents (g.fiber s) := by
    simpa only [isGenericPoint_def.mp hC] using C.property
  obtain ⟨A, hA, hAdom, hAval, gA, hgeneric, hclosed, hdata⟩ :=
    exists_valuation_base_change_associated_flat
      f F y hy Y rfl s (Y.subschemeι (g.fiberι s x)) x hCclosure rfl hflat
  let : CommRing A := hA
  let : IsDomain A := hAdom
  let : ValuationRing A := hAval
  let X' := Limits.pullback f gA
  let p : X' ⟶ X := Limits.pullback.fst f gA
  let q : X' ⟶ Spec (.of A) := Limits.pullback.snd f gA
  let Z : X'.IdealSheafData := Y.comap p
  let j : Z.subscheme ⟶ X' := Z.subschemeι
  rcases hdata with ⟨η, hηcomp, hpy, hrest⟩
  let y' : X' := j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)
  let Y' : X'.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({y'} : Set X'))
  rcases hrest with ⟨hYint, hy', ξ', hξcomp, hpx, hflat'⟩
  let x' : X' := Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι (IsLocalRing.closedPoint A) ξ')
  have : IsIntegral Y'.subscheme := hYint
  have hgeneric' : q y' = genericPoint (Spec (.of A)) := by
    dsimp [y']
    change (((j ≫ q).fiberι (genericPoint (Spec (.of A))) ≫ (j ≫ q)) η) = _
    rw [Scheme.Hom.fiber_fac]
    simp
    rfl
  let F' := (Scheme.Modules.pullback p).obj F
  have : F'.IsQuasicoherent := Stacks.Modules.isQuasicoherent_pullback p F inferInstance
  have : F'.IsFiniteType := Stacks.Modules.isFiniteType_pullback p F inferInstance
  have hx'assoc : x' ∈ Stacks.Divisors.relativeAssassin q F' :=
    mem_relativeAssassin_of_isGenericPoint_closedFibre
      q F' y' hy' hgeneric' Y' rfl ξ' hξcomp hflat'
  let m : Z.subscheme ⟶ Y.subscheme :=
    (Y.comapIso p).hom ≫ Limits.pullback.snd p Y.subschemeι
  have hcomap : IsPullback j m p Y.subschemeι := by
    dsimp only [j, m, Z]
    exact IsPullback.of_iso_pullback ⟨by simp⟩ (Y.comapIso p) (by simp) rfl
  exact topologicalKrullDimAt_fiber_eq_of_valuation_comap f gA y Y (by simp [Y]) s x hCclosure Z m
    hcomap η hηcomp y' rfl hpy Y' rfl ξ' hξcomp hpx
    ((AlgebraicGeometry.mem_relativeAssassin_pullback_iff f gA F x').mp hx'assoc).2

end Stacks.RelativeAssassin

end
