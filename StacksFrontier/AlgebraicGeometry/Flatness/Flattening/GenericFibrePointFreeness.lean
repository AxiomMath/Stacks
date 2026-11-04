module

public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocus
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Freeness of some rank near a point generic in its fibre

Let `f : X ⟶ S` be a smooth morphism of finite presentation, let `F` be an `𝒪_X`-module of finite
presentation and let `x` be a point of `X` which is the generic point of the fibre of `f` through
it. If `F` is flat over `S` at `x`, then `F` is free of some finite rank on a neighbourhood of
`x`. This is Stacks 080Q with its fibre hypothesis discharged: a fibre of a smooth morphism is
reduced, a fibre with a generic point is irreducible, so the local ring of the fibre at that
generic point is a field and every module over it is flat.

The generic-point hypothesis is also shown to pass to an open subscheme of the source, and
freeness of a fixed rank near a point of an open subscheme is shown to be freeness of that rank
near the corresponding point of the ambient scheme. Together these let the statement be applied
on a quasi-compact — in practice affine — open of a source which is not itself quasi-compact over
the base, where Stacks 080Q does not apply directly.

## Main results

* `AlgebraicGeometry.flat_fiber_stalk_of_isGenericPoint`: the restriction of a module to the fibre
  of a smooth morphism has flat stalk at a generic point of that fibre.
* `AlgebraicGeometry.exists_freeAtPointOfRank_of_isFlatOverAt`: **Stacks 080Q** at a generic point
  of a fibre of a smooth morphism, with no fibre hypothesis left to check.
* `AlgebraicGeometry.isGenericPoint_asFiber_comp_ι`: a point of an open subscheme which is generic
  in its fibre for the ambient morphism is generic in its fibre for the restricted morphism.
* `AlgebraicGeometry.freeAtPointOfRank_of_opens`: freeness of a fixed rank near a point of an open
  subscheme is freeness of that rank near the corresponding point of the ambient scheme.

## Implementation notes

The two topological lemmas `isGenericPoint_univ_subtype_iff` and
`isGenericPoint_univ_preimage_of_isEmbedding` reduce `IsGenericPoint _ Set.univ` on a subspace to a
containment in a closure in the ambient space, which is what makes the comparison of the fibre of
`W.ι ≫ f` with the fibre of `f` a one-line consequence of
`Topology.IsEmbedding.closure_eq_preimage_closure_image`. Mathlib's `Scheme.Hom.fiberHomeo`
transports between the fibre as a scheme and the fibre as a subspace of the source, and
`AlgebraicGeometry.FreeAtGenericPointsSituation.isGenericPoint_univ_of_surjective` carries
`IsGenericPoint _ Set.univ` along those homeomorphisms.

Irreducibility of the fibre is *derived* from the generic point rather than assumed: the closure of
the generic point is the whole fibre and the closure of a point is irreducible. This is why no
geometric irreducibility hypothesis appears, even though the companion statement for the
flattening functors of Stacks 05MP is used only for families whose fibres are geometrically
irreducible.

Pushing freeness forward along an open immersion uses `AlgebraicGeometry.Scheme.Hom.isoImage` to
identify the witness open of the subscheme with its image, and then
`AlgebraicGeometry.invertibleRank_pullback_comp` to compare the two pullbacks of the module.

## References

* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Generic points of subspaces -/

/-- A point of a subspace is generic for the whole subspace exactly when the subspace is contained
in the closure of that point in the ambient space. -/
@[ega "0 2.1.2" "more general"]
theorem isGenericPoint_univ_subtype_iff {Z : Type*} [TopologicalSpace Z] {A : Set Z} (a : A) :
    IsGenericPoint a (Set.univ : Set ↥A) ↔ A ⊆ closure {(a : Z)} := by
  rw [IsGenericPoint, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Set.image_singleton, Set.eq_univ_iff_forall]
  exact ⟨fun h z hz ↦ h ⟨z, hz⟩, fun h b ↦ h b.2⟩

/-- A point generic for a subspace is generic for the preimage of that subspace under an
embedding. -/
theorem isGenericPoint_univ_preimage_of_isEmbedding {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {j : Y → Z} (hj : Topology.IsEmbedding j) {A : Set Z} {y : Y}
    (hy : y ∈ j ⁻¹' A) (h : IsGenericPoint (⟨j y, hy⟩ : ↥A) (Set.univ : Set ↥A)) :
    IsGenericPoint (⟨y, hy⟩ : ↥(j ⁻¹' A)) (Set.univ : Set ↥(j ⁻¹' A)) := by
  rw [isGenericPoint_univ_subtype_iff] at h ⊢
  intro b hb
  rw [hj.closure_eq_preimage_closure_image, Set.image_singleton]
  exact h hb

/-- A generic point of a fibre, read in the fibre through its own image, is again generic. -/
theorem isGenericPoint_asFiber {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (ξ : f.fiber s)
    (hξ : IsGenericPoint ξ (Set.univ : Set (f.fiber s))) :
    IsGenericPoint (f.asFiber (f.fiberι s ξ)) (Set.univ : Set (f.fiber (f (f.fiberι s ξ)))) := by
  have hbase : f (f.fiberι s ξ) = s := by simpa using (f.fiberHomeo s ξ).2
  have hsets : f ⁻¹' {s} = f ⁻¹' {f (f.fiberι s ξ)} := by rw [hbase]
  let e : f.fiber s ≃ₜ f.fiber (f (f.fiberι s ξ)) :=
    (f.fiberHomeo s).trans <|
      (Homeomorph.setCongr hsets).trans (f.fiberHomeo (f (f.fiberι s ξ))).symm
  have heξ : e ξ = f.asFiber (f.fiberι s ξ) := by
    apply (f.fiberι (f (f.fiberι s ξ))).isEmbedding.injective
    rfl
  rw [← heξ]
  simpa using hξ.image e.continuous

/-- A point of an open subscheme which is generic in its fibre for the ambient morphism is generic
in its fibre for the restricted morphism: that fibre is the part of the ambient fibre lying in the
open subscheme. -/
theorem isGenericPoint_asFiber_comp_ι {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens)
    (x : W.toScheme)
    (h : IsGenericPoint (f.asFiber (W.ι x)) (Set.univ : Set (f.fiber (f (W.ι x))))) :
    IsGenericPoint ((W.ι ≫ f).asFiber x) (Set.univ : Set ((W.ι ≫ f).fiber ((W.ι ≫ f) x))) := by
  have h1 : IsGenericPoint (⟨W.ι x, rfl⟩ : ↥(f ⁻¹' {f (W.ι x)})) Set.univ := by
    have hgen := FreeAtGenericPointsSituation.isGenericPoint_univ_of_surjective
      (f.fiberHomeo (f (W.ι x))) (f.fiberHomeo _).continuous (f.fiberHomeo _).surjective h
    have he : f.fiberHomeo (f (W.ι x)) (f.asFiber (W.ι x)) = ⟨W.ι x, rfl⟩ :=
      Subtype.ext (by simp)
    rwa [he] at hgen
  have h2 := isGenericPoint_univ_preimage_of_isEmbedding W.ι.isEmbedding
    (A := f ⁻¹' {f (W.ι x)}) (y := x) rfl h1
  rw [isGenericPoint_univ_subtype_iff] at h2
  have h2' : (W.ι : W.toScheme → X) ⁻¹' (f ⁻¹' {f (W.ι x)}) ⊆
      closure ({x} : Set W.toScheme) := h2
  have hsets : (W.ι : W.toScheme → X) ⁻¹' (f ⁻¹' {f (W.ι x)})
      = (W.ι ≫ f) ⁻¹' {(W.ι ≫ f) x} := by
    ext b
    simp
  rw [hsets] at h2'
  exact FreeAtGenericPointsSituation.isGenericPoint_univ_of_surjective
    ((W.ι ≫ f).fiberHomeo ((W.ι ≫ f) x)).symm (Homeomorph.continuous _)
    (Homeomorph.surjective _) ((isGenericPoint_univ_subtype_iff _).mpr h2')

/-! ### Flatness of the fibre stalk at a generic point -/

/-- The local ring of a reduced irreducible scheme at a generic point is a field. -/
@[ega "IV 20.1.3.1" "partial", sga "3 VIA 2.5.4" "special case", sga "3 VIB 3.11" "partial"]
theorem isField_stalk_of_isGenericPoint {Y : Scheme.{u}} [IsReduced Y]
    [IrreducibleSpace Y] (ξ : Y) (hξ : IsGenericPoint ξ (Set.univ : Set Y)) :
    IsField (Y.presheaf.stalk ξ) := by
  have hcomp : closure ({ξ} : Set Y) ∈ irreducibleComponents Y := by
    rw [hξ, irreducibleComponents_eq_singleton]
    simp
  exact isField_stalk_of_closure_mem_irreducibleComponents Y ξ hcomp

/-- For a smooth morphism, the restriction of any module to a fibre has flat stalk at a generic
point of that fibre: the fibre is smooth over a field, hence reduced, and it is irreducible
because it is the closure of that point, so its local ring there is a field. -/
theorem flat_fiber_stalk_of_isGenericPoint {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (x : X) (hξ : IsGenericPoint (f.asFiber x) (Set.univ : Set (f.fiber (f x))))
    (F : X.Modules) :
    letI := Stacks.Flatness.stalkModule
      ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x)
    Module.Flat (ToType ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x))) := by
  let Y := f.fiber (f x)
  let g := f.fiberToSpecResidueField (f x)
  let G := (Scheme.Modules.pullback (f.fiberι (f x))).obj F
  let y := f.asFiber x
  have : IrreducibleSpace Y := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hξ]
    exact isIrreducible_singleton.closure
  have hSmooth : Smooth g := by
    change Smooth (pullback.snd f (S.fromSpecResidueField (f x)))
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))) ‹Smooth f›
  have : IsReduced Y :=
    (geometricallyReduced_of_smooth g).geometrically_isReduced
      (y := 𝟙 (Spec (.of (S.residueField (f x))))) (fst := 𝟙 Y) (snd := g) IsPullback.of_id_fst
  let A := ToType (Y.presheaf.stalk y)
  let M := ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf y)
  let _ : Module A M := Stacks.Flatness.stalkModule G y
  let _ : Field A := (isField_stalk_of_isGenericPoint y hξ).toField
  have : Module.Free A M := Module.Free.of_divisionRing A M
  exact Module.Flat.of_free

/-! ### Freeness of some rank near a generic point of a fibre -/

/-- A trivialisation of a module over an open neighbourhood of a point exhibits it as free of that
rank near the point. -/
theorem freeAtPointOfRank_of_over_iso_free {X : Scheme.{u}} (F : X.Modules)
    {x : X} {U : X.Opens} (hU : x ∈ U) (n : ℕ)
    (e : F.over U ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    FreeAtPointOfRank F x n := by
  have e1 : F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)) :=
    (Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso
        U (ULift.{u} (Fin n)) F e).symm ≪≫
      _root_.restrictFunctor_obj_free_iso U.ι _
  have h3 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) n :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F)
      (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e1.symm
        (SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} n))
  exact ⟨U, hU, { exists_isFiniteLocallyFreeOfRankData :=
    h3.exists_isFiniteLocallyFreeOfRankData }⟩

/-- **Stacks Project, Tag 080Q** at a generic point of a fibre of a smooth morphism: a finitely
presented module flat over the base at such a point is free of some finite rank near it. The
fibre hypothesis of the source is automatic there. -/
theorem exists_freeAtPointOfRank_of_isFlatOverAt {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (hf : AlgebraicGeometry.FinitePresentation f) (F : X.Modules)
    [F.IsFinitePresentation] (x : X)
    (hξ : IsGenericPoint (f.asFiber x) (Set.univ : Set (f.fiber (f x))))
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ n : ℕ, FreeAtPointOfRank F x n := by
  obtain ⟨U, hU, n, ⟨e⟩⟩ :=
    Scheme.Modules.exists_iso_free_over_of_flat_over_at_of_flat_fiber_stalk f hf F x hflat
      (flat_fiber_stalk_of_isGenericPoint f x hξ F)
  exact ⟨n, freeAtPointOfRank_of_over_iso_free F hU n e⟩

/-- Freeness of a fixed rank near a point of an open subscheme is freeness of that rank near the
corresponding point of the ambient scheme: the witness open transports to its image. -/
theorem freeAtPointOfRank_of_opens {X : Scheme.{u}} (F : X.Modules) (W : X.Opens)
    (x : W.toScheme) (n : ℕ)
    (h : FreeAtPointOfRank ((Scheme.Modules.pullback W.ι).obj F) x n) :
    FreeAtPointOfRank F (W.ι x) n := by
  obtain ⟨U, hxU, hU⟩ := h
  refine ⟨W.ι ''ᵁ U, (Scheme.Hom.apply_mem_image_iff W.ι).mpr hxU, ?_⟩
  refine invertibleRank_pullback_comp F n (a := (W.ι.isoImage U).inv) (b := U.ι ≫ W.ι)
    (d := (W.ι ''ᵁ U).ι) ?_
    (invertibleRank_of_moduleIso ((Scheme.Modules.pullbackComp U.ι W.ι).app F) n hU)
  rw [← Scheme.Hom.isoImage_hom_ι]
  simp

end AlgebraicGeometry

end
