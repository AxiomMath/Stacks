module

public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.CompositeFibre
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Specialization.Defs
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
import StacksFrontier.RingTheory.Catenary.FormalFibresAssociatedDimension

/-!
# Fibrewise relative dimension of a flat morphism

A flat morphism locally of finite presentation decomposes, up to a fibrewise dense open, into
pieces of constant relative dimension.

## Main results

* `AlgebraicGeometry.exists_open_relativeDimension_fiberwise_dense` supplies the open pieces of
  each relative dimension and states their fibrewise density.
* `AlgebraicGeometry.cohenMacaulayAt_of_openImmersion_source`: Cohen–Macaulayness at a point is
  preserved by restricting the source of a morphism along an open immersion.

## Implementation notes

The open piece indexed by `d` is represented by `U d : X.Opens`, and its morphism to the base is
the composite of its canonical open immersion with `f`. Fibrewise density is expressed by
pulling the supremum of these opens back along the canonical morphism from each fibre, and the
points of the fibres corresponding to points of the source are represented by
`AlgebraicGeometry.Scheme.Hom.asFiber`.

The decomposition is obtained by restricting to the Cohen–Macaulay locus, which is open and
fibrewise dense, and applying the clopen decomposition of a flat finitely presented morphism
with Cohen–Macaulay fibres.

## References

* [Stacks Project, Tag 054T](https://stacks.math.columbia.edu/tag/054T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Applying a point map to a composite is applying the two maps in turn. -/
private theorem source_comp_apply_explicit {X Y S : Scheme.{u}}
    (j : X ⟶ Y) (f : Y ⟶ S) (x : X) : (j ≫ f) x = f (j x) :=
  rfl

/-- The morphism of fibres sends the canonical fibre point of `x` to that of `j x`. -/
private theorem fiberMapOfSourceHom_asFiber {X Y S : Scheme.{u}}
    (j : X ⟶ Y) (f : Y ⟶ S) (x : X) :
    fiberMapOfSourceHom j f (f (j x))
      ((fiberIsoOfEq (j ≫ f) (source_comp_apply_explicit j f x)).hom
        ((j ≫ f).asFiber x)) = f.asFiber (j x) := by
  apply (f.fiberι (f (j x))).isEmbedding.injective
  change (fiberMapOfSourceHom j f (f (j x)) ≫ f.fiberι (f (j x)))
      ((fiberIsoOfEq (j ≫ f) (source_comp_apply_explicit j f x)).hom
        ((j ≫ f).asFiber x)) = _
  have hfst : fiberMapOfSourceHom j f (f (j x)) ≫ f.fiberι (f (j x)) =
      (j ≫ f).fiberι (f (j x)) ≫ j := pullback.lift_fst _ _ _
  rw [hfst]
  have hpoint : (j ≫ f).fiberι (f (j x))
      ((fiberIsoOfEq (j ≫ f) (source_comp_apply_explicit j f x)).hom
        ((j ≫ f).asFiber x)) = x := by
    dsimp [fiberIsoOfEq]
    cases source_comp_apply_explicit j f x
    exact (j ≫ f).fiberι_asFiber x
  change j ((j ≫ f).fiberι (f (j x))
      ((fiberIsoOfEq (j ≫ f) (source_comp_apply_explicit j f x)).hom
        ((j ≫ f).asFiber x))) = _
  rw [hpoint]
  simp [Scheme.Hom.fiberι_asFiber]

/-- Cohen–Macaulayness of a stalk is invariant under an open immersion. -/
private theorem isCohenMacaulayLocalRing_stalk_iff_of_isOpenImmersion {A B : Scheme.{u}}
    [IsLocallyNoetherian A] [IsLocallyNoetherian B] (J : A ⟶ B) [IsOpenImmersion J] (z : A) :
    IsCohenMacaulayLocalRing ↑(B.presheaf.stalk (J z)) ↔
      IsCohenMacaulayLocalRing ↑(A.presheaf.stalk z) :=
  have : IsIso (J.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹_›).2 z
  isCohenMacaulayLocalRing_iff_of_ringEquiv (asIso (J.stalkMap z)).commRingCatIsoToRingEquiv

/-- Cohen–Macaulayness at a point is preserved by restricting the source along an open
immersion. -/
public theorem cohenMacaulayAt_of_openImmersion_source {X Y S : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (f : Y ⟶ S)
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y))
    (he : ∀ y : S, IsLocallyNoetherian ((j ≫ f).fiber y)) (x : X)
    (h : Scheme.Hom.IsCohenMacaulayAt f hf (j x)) :
    Scheme.Hom.IsCohenMacaulayAt (j ≫ f) he x := by
  have hy : (j ≫ f) x = f (j x) := source_comp_apply_explicit j f x
  have := he (f (j x))
  have := hf (f (j x))
  have : IsOpenImmersion (fiberMapOfSourceHom j f (f (j x))) :=
    MorphismProperty.of_isPullback (fiberMapOfSourceHom_isPullback j f (f (j x))).flip inferInstance
  let J := (fiberIsoOfEq (j ≫ f) hy).hom ≫ fiberMapOfSourceHom j f (f (j x))
  have hpoint : J ((j ≫ f).asFiber x) = f.asFiber (j x) := fiberMapOfSourceHom_asFiber j f x
  unfold Scheme.Hom.IsCohenMacaulayAt
  change IsFlatAt f.toLRSHom.toShHom (j x) ∧
      IsCohenMacaulayLocalRing ↑((f.fiber (f (j x))).presheaf.stalk (f.asFiber (j x))) at h
  refine ⟨?_, ?_⟩
  · change RingHom.Flat ((j ≫ f).stalkMap x).hom
    simp only [Scheme.Hom.stalkMap_comp]
    exact (RingHom.Flat.comp_iff_of_bijective_left
      (ConcreteCategory.bijective_of_isIso (j.stalkMap x))).mpr h.1
  · exact (isCohenMacaulayLocalRing_stalk_iff_of_isOpenImmersion J _).mp (by rw [hpoint]; exact h.2)

/-- Having constant relative dimension `d` is invariant under an isomorphism of sources. -/
private theorem relativeDimension_sourceIso_iff {X Y S : Scheme.{u}}
    (e : X ≅ Y) (f : Y ⟶ S) [LocallyOfFiniteType (e.hom ≫ f)]
    [LocallyOfFiniteType f] (d : ℕ) :
    RelativeDimension (e.hom ≫ f) d ↔ RelativeDimension f d := by
  rw [relativeDimension_iff, relativeDimension_iff]
  have key {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B)
      (hB : Equidimensional B ∧ topologicalKrullDim B = (d : WithBot ℕ∞)) :
      Equidimensional A ∧ topologicalKrullDim A = (d : WithBot ℕ∞) :=
    ⟨.of_homeomorph h hB.1, (IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph).trans hB.2⟩
  constructor
  · intro h s hs
    let E := fiberIsoOfSourceIso (f := f) e rfl s
    exact key E.inv.homeomorph (h s ⟨E.inv hs.some⟩)
  · intro h s hs
    let E := fiberIsoOfSourceIso (f := f) e rfl s
    exact key E.hom.homeomorph (h s ⟨E.hom hs.some⟩)

/-- Restricting a flat morphism locally of finite presentation to an open contained in its
Cohen–Macaulay locus gives Cohen–Macaulay fibres. -/
private theorem isCohenMacaulay_fiber_of_forall_isCohenMacaulayAt {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (hf : ∀ s : S, IsLocallyNoetherian (f.fiber s))
    (U : X.Opens) (hU : ∀ x : U, Scheme.Hom.IsCohenMacaulayAt f hf (U.ι x)) (s : S) :
    IsCohenMacaulay ((U.ι ≫ f).fiber s) := by
  let g : (U : Scheme) ⟶ S := U.ι ≫ f
  let hg : ∀ s : S, IsLocallyNoetherian (g.fiber s) := fun s =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g s
  have hchar := isCohenMacaulayAt_set_eq_fiberLocalRing g
  apply ((isCohenMacaulay_tfae_stalk (g.fiber s)).out 1 2).mpr
  refine ⟨hg s, ?_⟩
  intro w
  let x : U := g.fiberι s w
  have hgs : g x = s := by
    have hx : g.fiberι s w ∈ Set.range (g.fiberι s) := ⟨w, rfl⟩
    rw [g.range_fiberι s] at hx
    simpa using hx
  have hlocal := (congrArg (fun T : Set U => x ∈ T) hchar).mp
    (cohenMacaulayAt_of_openImmersion_source U.ι f hf hg x (hU x))
  change IsCohenMacaulayLocalRing
    ((g.fiber (g x)).presheaf.stalk (g.asFiber x)) at hlocal
  let E := fiberIsoOfEq g hgs
  have hpoint : E.hom (g.asFiber x) = w := by
    apply (g.fiberι s).isEmbedding.injective
    change (E.hom ≫ g.fiberι s) (g.asFiber x) = g.fiberι s w
    rw [fiberIsoOfEq_hom_fiberι]
    simp [x, Scheme.Hom.fiberι_asFiber]
  have := hg s
  have := hg (g x)
  have hlocal' := (isCohenMacaulayLocalRing_stalk_iff_of_isOpenImmersion E.hom _).mpr hlocal
  rw [hpoint] at hlocal'
  exact ⟨inferInstance, hlocal'⟩

/-- The images of a cover of an open subscheme `C` cover `C`. -/
private theorem iSup_ι_image_eq_of_iSup_eq_top {X : Scheme.{u}} (C : X.Opens) {ι : Type*}
    (V : ι → (C : Scheme).Opens) (hV : iSup V = ⊤) : (⨆ i, C.ι ''ᵁ V i) = C := by
  apply le_antisymm
  · exact iSup_le fun i => Scheme.Opens.ι_image_le C (V i)
  · intro x hx
    let xc : (C : Scheme) := ⟨x, hx⟩
    have hxV : xc ∈ ⨆ i, V i := by
      rw [hV]
      simp
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxV
    exact Opens.mem_iSup.mpr
      ⟨i, (Scheme.Opens.mem_ι_image_iff (U := C) (x := xc) (V := V i)).2 hi⟩

/-- **Stacks Project, Tag 054T.** A flat morphism locally of finite presentation admits open
pieces of every nonnegative relative dimension whose union is dense in every fibre. -/
@[stacks 054T]
public theorem exists_open_relativeDimension_fiberwise_dense
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    ∃ U : ℕ → X.Opens,
      (∀ s : S, Dense ((f.fiberι s) ⁻¹' (((iSup U : X.Opens) : Set X)))) ∧
        (∀ d : ℕ, RelativeDimension ((U d).ι ≫ f) d) := by
  classical
  let hf : ∀ s : S, IsLocallyNoetherian (f.fiber s) := fun s =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f s
  let C : X.Opens :=
    ⟨{x | Scheme.Hom.IsCohenMacaulayAt f hf x}, isOpen_setOf_isCohenMacaulayAt f⟩
  let g : (C : Scheme) ⟶ S := C.ι ≫ f
  have hCM : ∀ s : S, IsCohenMacaulay (g.fiber s) :=
    isCohenMacaulay_fiber_of_forall_isCohenMacaulayAt f hf C fun x => x.property
  obtain ⟨V, hVcl, hVcover, hVpair, hVdim⟩ :=
    exists_clopen_relativeDimension g hCM
  let U : ℕ → X.Opens := fun d => C.ι ''ᵁ V d
  have hcoverX : (⨆ d : ℕ, U d) = C := iSup_ι_image_eq_of_iSup_eq_top C V hVcover
  refine ⟨U, ?_, ?_⟩
  · intro s
    change Dense ((f.fiberι s) ⁻¹' ((⨆ d : ℕ, U d : X.Opens) : Set X))
    rw [hcoverX]
    exact dense_cohenMacaulayAt_fiber f s
  · intro d
    let E : (V d : Scheme) ≅ (U d : Scheme) :=
      IsOpenImmersion.isoOfRangeEq ((V d).ι ≫ C.ι) (U d).ι (by
        simp [U, Set.range_comp])
    have hfac : E.hom ≫ (U d).ι = (V d).ι ≫ C.ι :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hmor : E.hom ≫ ((U d).ι ≫ f) = (V d).ι ≫ g := by
      simpa only [Category.assoc, g] using congrArg (fun k => k ≫ f) hfac
    have hsource : RelativeDimension (E.hom ≫ ((U d).ι ≫ f)) d := by
      simpa only [hmor] using hVdim d
    exact (relativeDimension_sourceIso_iff E ((U d).ι ≫ f) d).mp hsource

end AlgebraicGeometry
