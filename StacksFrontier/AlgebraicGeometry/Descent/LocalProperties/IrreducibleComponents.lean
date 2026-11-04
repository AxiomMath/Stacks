module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints
public import StacksFrontier.Topology.Sober.SurjectionComponents
public import StacksFrontier.Topology.Irreducible.GenericPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the irreducible components of quasi-compact opens is fppf local

A scheme has the property that every quasi-compact open subscheme has finitely many
irreducible components if and only if the members of an fppf covering family do.

## Main results

* `AlgebraicGeometry.finiteIrreducibleComponents_isLocal_fppf` states fppf locality of
  this property.

## Implementation notes

Ascent uses that a flat morphism is generalizing, so the generic points of the source lie
over generic points of the target and, over each of them, give generic points of the fibre;
the fibre of a morphism locally of finite presentation over a residue field is Noetherian,
so its set of irreducible components is finite. Descent only needs that a surjective
quasi-compact morphism does not increase the number of irreducible components.

Zariski locality is checked on quasi-compact opens through
`IsCompactOpenCovered.exists_mem_of_isBasis`, which refines a quasi-compact open of the base
by finitely many affine opens of the members of the cover.

## References

* [Stacks Project, Tag 0BAL](https://stacks.math.columbia.edu/tag/0BAL)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- The property that every quasi-compact open of a scheme has finitely many irreducible
components. -/
private def FiniteIrreducibleComponents : ObjectProperty Scheme.{u} := fun X =>
  ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite

/-- The property passes to the source of an open immersion of schemes: a quasi-compact open
of the source is homeomorphic to a quasi-compact open of the target. -/
private theorem finiteIrreducibleComponents_of_isOpenImmersion {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (hX : FiniteIrreducibleComponents X) :
    FiniteIrreducibleComponents Y := by
  intro V hV
  let g : (V : Scheme) ⟶ X := V.ι ≫ f
  let W : X.Opens := ⟨Set.range g, g.isOpenEmbedding.isOpen_range⟩
  have hWc : IsCompact (W : Set X) := by
    have : CompactSpace V := isCompact_iff_compactSpace.mp (by simpa using hV)
    simpa [W, Set.image_univ] using isCompact_univ.image g.continuous
  have hHomeo : V ≃ₜ W :=
    (Homeomorph.Set.univ V).symm.trans <|
      (g.isOpenEmbedding.homeomorphImage Set.univ).trans (Homeomorph.setCongr (by simp [W]))
  exact Set.Finite.irreducibleComponents_of_isOpenEmbedding hHomeo hHomeo.isOpenEmbedding
    (hX W hWc)

private instance finiteIrreducibleComponents_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms FiniteIrreducibleComponents.{u} where
  of_iso e hX := finiteIrreducibleComponents_of_isOpenImmersion e.inv hX

private instance finiteIrreducibleComponents_isLocal_zariski :
    ObjectProperty.IsLocal FiniteIrreducibleComponents.{u} Scheme.zariskiPrecoverage := by
  refine isLocal_zariskiPrecoverage_of_openCover _
    (fun U hX => finiteIrreducibleComponents_of_isOpenImmersion U.ι hX) ?_
  intro X U hU h V hV
  classical
  let f : ∀ x : X, ↥(U x) → ↥X := fun x y => (U x).ι y
  have hcovered : IsCompactOpenCovered f (V : Set X) :=
    IsCompactOpenCovered.of_isOpenMap (fun x => (U x).ι.continuous)
      (fun x => (U x).ι.isOpenEmbedding.isOpenMap)
      (fun y _ => ⟨(hU.exists_mem y).choose, ⟨y, (hU.exists_mem y).choose_spec⟩, rfl⟩)
      V.2 hV
  obtain ⟨n, a, W, hWbasis, hWcover⟩ := hcovered.exists_mem_of_isBasis
    (fun x => (U x).toScheme.isBasis_affineOpens) fun _ _ hB => hB.isCompact
  have hmem (j : Fin n) (y : ↥(W j)) : f (a j) y.1 ∈ (V : Set X) := by
    rw [← hWcover]
    exact Set.mem_iUnion.mpr ⟨j, y.1, y.2, rfl⟩
  let g (j : Fin n) : ↥(W j) → ↥V := fun y => ⟨f (a j) y.1, hmem j y⟩
  have hgc (j : Fin n) : Continuous (g j) :=
    (((U (a j)).ι.continuous).comp continuous_subtype_val).subtype_mk (hmem j)
  have hgi (j : Fin n) : Function.Injective (g j) := fun x y hxy =>
    Subtype.ext ((U (a j)).ι.isOpenEmbedding.injective
      (congrArg (fun z : ↥V => (z : X)) hxy))
  have hsoberV : QuasiSober ↥V := V.2.isOpenEmbedding_subtypeVal.quasiSober
  have hsoberW (j : Fin n) : QuasiSober ↥(W j) :=
    (W j).2.isOpenEmbedding_subtypeVal.quasiSober
  have hgen (j : Fin n) : Finite (genericPoints ↥(W j)) :=
    genericPoints.finite (h (a j) (W j) (hWbasis j).isCompact)
  have hchoice (η : genericPoints ↥V) : ∃ (j : Fin n) (y : ↥(W j)), g j y = η.1 := by
    have hη : (η.1 : X) ∈ (V : Set X) := η.1.2
    simp only [← hWcover, Set.mem_iUnion] at hη
    obtain ⟨j, y, hy, hyeq⟩ := hη
    exact ⟨j, ⟨y, hy⟩, Subtype.ext hyeq⟩
  choose j y hy using hchoice
  have hVgen : Finite (genericPoints ↥V) := by
    refine Finite.of_injective
      (fun η => (⟨j η, ⟨y η, mem_genericPoints_of_mem_genericPoints_image (g (j η))
        (hgc (j η)) (hgi (j η)) (hy η ▸ η.2)⟩⟩ :
          Σ k : Fin n, genericPoints ↥(W k))) fun η θ heq => ?_
    refine Subtype.ext ?_
    calc η.1 = g (j η) (y η) := (hy η).symm
      _ = g (j θ) (y θ) :=
          congrArg (fun z : Σ k, genericPoints ↥(W k) => g z.1 z.2.1) heq
      _ = θ.1 := hy θ
  exact Finite.of_equiv _ (genericPoints.equiv (α := ↥V))

/-- A generic point of the source of a morphism gives a generic point of the fibre through
its image. -/
@[ega "0 2.1.8" "partial, special case"]
private theorem mem_genericPoints_fiber {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hx : x ∈ genericPoints X) (η : S) (hη : f x = η) :
    (f.fiberHomeo η).symm ⟨x, by simp [hη]⟩ ∈ genericPoints (f.fiber η) := by
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz => ?_
  have hxy : f.fiberι η z ⤳ x := by
    simpa [Scheme.Hom.fiberι_fiberHomeo_symm] using hz.map (f.fiberι η).continuous
  exact (f.fiberι η).isEmbedding.injective (by
    simpa [Scheme.Hom.fiberι_fiberHomeo_symm] using
      (mem_genericPoints_iff_forall_specializes_eq x).1 hx _ hxy)

/-- A flat morphism of finite presentation between affine schemes with finitely many
irreducible components downstairs has finitely many generic points upstairs. -/
private theorem finite_genericPoints_of_flat_of_locallyOfFinitePresentation
    {T S : Scheme.{u}} [IsAffine T] [IsAffine S] (f : T ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (hS : (irreducibleComponents S).Finite) :
    (genericPoints T).Finite := by
  classical
  have : Finite (genericPoints S) := genericPoints.finite hS
  have hfg (η : genericPoints S) : Finite (genericPoints (f.fiber η.1)) := by
    have : LocallyOfFiniteType (f.fiberToSpecResidueField η.1) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
      infer_instance
    have : IsLocallyNoetherian (f.fiber η.1) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η.1)
    have : IsNoetherian (f.fiber η.1) := AlgebraicGeometry.IsNoetherian.mk
    exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian
  refine Finite.of_injective
    (fun x : genericPoints T =>
      let η : genericPoints S :=
        ⟨f x.1, genericPoints_image_of_generalizingMap f (Flat.generalizingMap f) x.2⟩
      (⟨η, ⟨(f.fiberHomeo η.1).symm ⟨x.1, by simp [η]⟩,
        mem_genericPoints_fiber f x.1 x.2 η.1 rfl⟩⟩ :
          Σ η : genericPoints S, genericPoints (f.fiber η.1))) fun x y h => ?_
  refine Subtype.ext ?_
  simpa [Scheme.Hom.fiberι_fiberHomeo_symm] using
    congrArg (fun z : Σ η : genericPoints S, genericPoints (f.fiber η.1) =>
      f.fiberι z.1.1 z.2.1) h

/-- Having finitely many irreducible components on every quasi-compact open is local in the
fppf topology. -/
@[stacks 0BAL]
instance finiteIrreducibleComponents_isLocal_fppf :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} =>
        ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
      Scheme.fppfPrecoverage := by
  refine isLocal_fppfPrecoverage_of_affine FiniteIrreducibleComponents ?_ ?_
  · intro T S _ _ f _ hfp hSprop
    have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
    have hScomp : (irreducibleComponents S).Finite := by
      have hStop : (irreducibleComponents (⊤ : S.Opens)).Finite :=
        hSprop ⊤ (by simpa using (isCompact_univ : IsCompact (Set.univ : Set S)))
      have : QuasiSober (↑(Set.univ : Set S)) :=
        (Homeomorph.Set.univ S).isOpenEmbedding.quasiSober
      exact Set.Finite.irreducibleComponents_of_isOpenEmbedding (Homeomorph.Set.univ S).symm
        (Homeomorph.Set.univ S).symm.isOpenEmbedding hStop
    have : Finite (genericPoints T) :=
      finite_genericPoints_of_flat_of_locallyOfFinitePresentation f hScomp
    intro U hU
    exact Set.Finite.irreducibleComponents_of_isOpenEmbedding (Subtype.val : U → T)
      U.ι.isOpenEmbedding (Finite.of_equiv (genericPoints T) (genericPoints.equiv (α := T)))
  · intro T S _ _ f _ hfp _ hTprop
    have : QuasiCompact f := hfp.quasiCompact
    intro U hU
    let g : (f ⁻¹ᵁ U : Set T) → (U : Set S) := fun x => ⟨f x.1, x.2⟩
    have hgc : Continuous g :=
      (f.continuous.comp continuous_subtype_val).subtype_mk fun x => x.2
    have hgsurj : Function.Surjective g := fun y => by
      obtain ⟨x, hx⟩ := f.surjective y.1
      exact ⟨⟨x, show f x ∈ U from hx ▸ y.2⟩, Subtype.ext hx⟩
    exact (ncard_irreducibleComponents_le_of_surjective g hgc hgsurj
      (hTprop (f ⁻¹ᵁ U) (f.isCompact_preimage hU))).1

end AlgebraicGeometry
