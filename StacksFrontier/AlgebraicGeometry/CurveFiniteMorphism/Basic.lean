module

public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentIntersectionDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Preimage
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A non-constant morphism from a proper curve to projective space is finite

Let `X` be a curve over a field `k` whose structure morphism `f : X ⟶ Spec k` is proper, let `L`
be an invertible `𝒪_X`-module and let `s₀, …, sₙ` be global sections of `L` whose nonvanishing
loci cover `X`, so that `Stacks.ProjectiveSpaceSections.morphismOver` is the morphism
`φ = φ_{(L, s)} : X ⟶ ℙⁿ_k`. If one of the sections vanishes somewhere but not everywhere, then
`φ` is a finite morphism, and consequently every nonvanishing locus `X_{sⱼ}` is an affine open of
`X`: it is the preimage of a standard affine chart of `ℙⁿ_k`. In particular, if one of the
sections has nonvanishing locus `X \ {x}` for a closed point `x`, then `X \ {x}` is affine.

## Main results

* `Stacks.Topology.Dimension.isClosed_singleton_of_closure_ne_univ`: in an irreducible space of
  Krull dimension at most one, a point that is not a generic point is closed.
* `Stacks.Topology.Dimension.discreteTopology_of_isClosed_ne_univ_of_irreducible`: in an
  irreducible Noetherian sober space of Krull dimension at most one, a proper closed subset is
  discrete.
* `AlgebraicGeometry.topologicalKrullDim_fiber_le_zero_of_universallyClosed`: every fibre of a
  universally closed, non-constant morphism out of an irreducible Noetherian scheme of dimension
  at most one has dimension at most zero.
* `AlgebraicGeometry.isFinite_of_isProper_of_exists_apply_ne`: such a morphism is finite when it
  is proper.
* `Stacks.ProjectiveSpaceSections.isFinite_morphismOver`: `φ_{(L, s)}` is finite when one of the
  generating sections vanishes somewhere but not everywhere.
* `Stacks.ProjectiveSpaceSections.isAffineOpen_nonvanishingChart_of_isCurve`: every `X_{sⱼ}` is
  then an affine open.
* `Stacks.ProjectiveSpaceSections.nonvanishingChart_ne_top_of_isCurve`: no member of the
  generating family is then nowhere vanishing.
* `Stacks.ProjectiveSpaceSections.isAffineOpen_compl_singleton_of_nonvanishingChart_eq` and
  `Stacks.ProjectiveSpaceSections.isAffineOpen_compl_singleton_of_isClosedImmersion`: if one of
  the generating sections has nonvanishing locus `X \ {x}` for a closed point `x`, then `X \ {x}`
  is affine, for a proper curve and for an H-projective curve respectively.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
-/


@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits Set
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Topology.Dimension

variable {X : Type u} [TopologicalSpace X]

/-- In an irreducible space, no irreducible component is contained in a proper subset. -/
private theorem not_subset_of_mem_irreducibleComponents [IrreducibleSpace X] {T : Set X}
    (hT : T ≠ univ) : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ T := by
  intro C hC hsub
  rw [irreducibleComponents_eq_singleton, mem_singleton_iff] at hC
  exact hT (univ_subset_iff.mp (hC ▸ hsub))

/-- In an irreducible `T₀` space of Krull dimension at most one, a point whose closure is not the
whole space is closed. -/
theorem isClosed_singleton_of_closure_ne_univ [T0Space X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {z : X} (h : closure ({z} : Set X) ≠ univ) :
    IsClosed ({z} : Set X) :=
  isClosed_singleton_of_not_irreducibleComponent_subset hdim isClosed_closure
    (not_subset_of_mem_irreducibleComponents h) (subset_closure (mem_singleton z))

/-- In an irreducible Noetherian quasi-sober `T₀` space of Krull dimension at most one, a proper
closed subset is a discrete subspace. -/
@[ega "II 7.4.3" "partial"]
theorem discreteTopology_of_isClosed_ne_univ_of_irreducible [T0Space X] [NoetherianSpace X]
    [QuasiSober X] [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) {T : Set X}
    (hT : IsClosed T) (hTne : T ≠ univ) : DiscreteTopology T := by
  have hTc := not_subset_of_mem_irreducibleComponents hTne
  exact StacksTag09NX.discreteTopology_of_finite_of_isClosed
    (finite_of_not_irreducibleComponent_subset hdim hT hTc)
    (fun x hx => isClosed_singleton_of_not_irreducibleComponent_subset hdim hT hTc hx)

end Stacks.Topology.Dimension

namespace AlgebraicGeometry

/-- Let `g : X ⟶ P` be a universally closed morphism out of an irreducible Noetherian scheme of
dimension at most one. If no fibre of `g` is the whole of `X`, then every fibre of `g` has
dimension at most zero. -/
theorem topologicalKrullDim_fiber_le_zero_of_universallyClosed {X P : Scheme.{u}} (g : X ⟶ P)
    [UniversallyClosed g] [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (hnc : ∀ y : P, (g.base ⁻¹' {y}) ≠ univ) (y : P) :
    topologicalKrullDim (g.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _ (g.fiberHomeo y).isHomeomorph]
  have hdisc : DiscreteTopology (g.base ⁻¹' {y} : Set X) := by
    by_cases hy : IsClosed ({y} : Set P)
    · exact Stacks.Topology.Dimension.discreteTopology_of_isClosed_ne_univ_of_irreducible hdim
        (hy.preimage g.base.hom.continuous) (hnc y)
    · have hss : Subsingleton (g.base ⁻¹' {y} : Set X) := by
        have key : ∀ c : (g.base ⁻¹' {y} : Set X), closure ({(c : X)} : Set X) = univ := by
          intro c
          by_contra hcl
          have himg : IsClosed (g.base '' ({(c : X)} : Set X)) :=
            g.isClosedMap _ (Stacks.Topology.Dimension.isClosed_singleton_of_closure_ne_univ
              hdim hcl)
          rw [Set.image_singleton] at himg
          exact hy ((c.2 : g.base (c : X) = y) ▸ himg)
        exact ⟨fun a b => Subtype.ext
          (inseparable_iff_closure_eq.mpr ((key a).trans (key b).symm)).eq⟩
      exact Subsingleton.discreteTopology
  simpa using topologicalKrullDim_zero_of_discreteTopology (g.base ⁻¹' {y} : Set X)

/-- A proper morphism out of an irreducible Noetherian scheme of dimension at most one which
takes two different values is finite. -/
theorem isFinite_of_isProper_of_exists_apply_ne {X P : Scheme.{u}} (g : X ⟶ P) [IsProper g]
    [IrreducibleSpace X] [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (hnc : ∃ a b : X, g.base a ≠ g.base b) : IsFinite g := by
  obtain ⟨a, b, hab⟩ := hnc
  refine isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero g
    (topologicalKrullDim_fiber_le_zero_of_universallyClosed g hdim fun y h => hab ?_)
  exact (Set.eq_univ_iff_forall.mp h a : g.base a = y).trans (Set.eq_univ_iff_forall.mp h b).symm

end AlgebraicGeometry

namespace Stacks.ProjectiveSpaceSections

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

variable {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}

/-- A curve over a field is a Noetherian scheme. -/
theorem isNoetherian_of_isCurve (f : X ⟶ Spec (.of k)) [IsCurve k f] : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

/-- A curve over a field has a point different from any given point. -/
theorem exists_ne_of_isCurve (f : X ⟶ Spec (.of k)) [IsCurve k f] (x : X) : ∃ y : X, y ≠ x := by
  by_contra! hcon
  have : Subsingleton X := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
  have : DiscreteTopology X := Subsingleton.discreteTopology
  have hd : topologicalKrullDim X ≤ 0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [IsCurve.topologicalKrullDim_eq_one f] at hd
  exact absurd hd (by decide)

variable {n : ℕ} (s : Fin (n + 1) → L.sections)
  (hs : (⨆ i, nonvanishingChart L (s i)) = ⊤)

/-- The morphism `morphismOver L s hs f` to projective space defined by generating sections of an
invertible module on a proper curve is finite, as soon as one of the sections vanishes somewhere
but not everywhere. -/
theorem isFinite_morphismOver (hf : IsProper f) (hc : IsCurve k f) (i₀ : Fin (n + 1))
    (hne : nonvanishingChart L (s i₀) ≠ ⊤)
    (hnb : (nonvanishingChart L (s i₀) : Set X).Nonempty) :
    IsFinite (morphismOver L s hs f) := by
  have := hf
  have := hc
  have := isNoetherian_of_isCurve (k := k) f
  have hpre : morphismOver L s hs f ⁻¹ᵁ Stacks.ProjectiveCohomology.chart n (.of k) i₀
      = nonvanishingChart L (s i₀) := morphismOver_preimage_basicOpen L s hs f i₀
  have h : morphismOver L s hs f ≫ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) = f :=
    morphismOver_fst L s hs f
  have : IsProper (morphismOver L s hs f ≫
      (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))) := by rwa [h]
  have : IsProper (morphismOver L s hs f) :=
    IsProper.of_comp _ (projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨a, ha⟩ := hnb
  obtain ⟨b, hb⟩ : ∃ b : X, b ∉ (nonvanishingChart L (s i₀) : Set X) := by
    by_contra hcon
    exact hne (TopologicalSpace.Opens.ext (Set.eq_univ_of_forall (by simpa using hcon)))
  refine isFinite_of_isProper_of_exists_apply_ne _ (by
    rw [IsCurve.topologicalKrullDim_eq_one f]) ⟨a, b, fun hab => hb ?_⟩
  rw [← hpre] at ha ⊢
  simpa [hab] using ha

include hs in
/-- Under the hypotheses of `isFinite_morphismOver`, every nonvanishing locus `X_{sⱼ}` is an
affine open of `X`. -/
theorem isAffineOpen_nonvanishingChart_of_isCurve (hf : IsProper f) (hc : IsCurve k f)
    (i₀ : Fin (n + 1)) (hne : nonvanishingChart L (s i₀) ≠ ⊤)
    (hnb : (nonvanishingChart L (s i₀) : Set X).Nonempty) (j : Fin (n + 1)) :
    IsAffineOpen (nonvanishingChart L (s j)) := by
  have := isFinite_morphismOver L s hs hf hc i₀ hne hnb
  rw [← morphismOver_preimage_basicOpen L s hs f j]
  exact IsAffineHom.isAffine_preimage _
    (Stacks.ProjectiveCohomology.isAffineOpen_chart n (.of k) j)

include hs in
/-- Under the hypotheses of `isFinite_morphismOver`, no nonvanishing locus `X_{sⱼ}` is the whole
of `X`. -/
theorem nonvanishingChart_ne_top_of_isCurve (hf : IsProper f) (hc : IsCurve k f)
    (i₀ : Fin (n + 1)) (hne : nonvanishingChart L (s i₀) ≠ ⊤)
    (hnb : (nonvanishingChart L (s i₀) : Set X).Nonempty) (j : Fin (n + 1)) :
    nonvanishingChart L (s j) ≠ ⊤ :=
  have := hf
  have := hc
  (isAffineOpen_nonvanishingChart_of_isCurve L s hs hf hc i₀ hne hnb j).ne_top_of_isCurve k f

include hs in
/-- Let `X` be a proper curve over `k` and `x` a closed point of `X`. If an invertible module `L`
on `X` is generated by global sections one of which has nonvanishing locus exactly `X \ {x}`, then
`X \ {x}` is affine. -/
theorem isAffineOpen_compl_singleton_of_nonvanishingChart_eq (hf : IsProper f) (hc : IsCurve k f)
    {x : X} (hx : IsClosed ({x} : Set X)) (i₀ : Fin (n + 1))
    (h0 : (nonvanishingChart L (s i₀) : Set X) = ({x} : Set X)ᶜ) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) := by
  have := hc
  obtain ⟨y, hy⟩ := exists_ne_of_isCurve (k := k) f x
  have hne : nonvanishingChart L (s i₀) ≠ ⊤ := by
    intro h
    rw [h] at h0
    exact (h0 ▸ (Set.mem_univ x : x ∈ (⊤ : X.Opens).carrier) : x ∈ ({x} : Set X)ᶜ) rfl
  have hnb : (nonvanishingChart L (s i₀) : Set X).Nonempty := ⟨y, by rw [h0]; exact hy⟩
  have key := isAffineOpen_nonvanishingChart_of_isCurve L s hs hf hc i₀ hne hnb i₀
  rwa [show (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) = nonvanishingChart L (s i₀) from
    TopologicalSpace.Opens.ext h0.symm]

include hs in
/-- Let `X` be a curve over `k` with a closed immersion into projective space over `k` compatible
with its structure morphism, and `x` a closed point of `X`. If an invertible module `L` on `X` is
generated by global sections one of which has nonvanishing locus exactly `X \ {x}`, then
`X \ {x}` is affine. -/
theorem isAffineOpen_compl_singleton_of_isClosedImmersion (hc : IsCurve k f) {N : ℕ}
    (i : X ⟶ projectiveSpaceOver N (Spec (.of k)))
    [IsClosedImmersion i] (hi : i ≫ (projectiveSpaceOver N (Spec (.of k)) ↘ Spec (.of k)) = f)
    {x : X} (hx : IsClosed ({x} : Set X)) (i₀ : Fin (n + 1))
    (h0 : (nonvanishingChart L (s i₀) : Set X) = ({x} : Set X)ᶜ) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
  isAffineOpen_compl_singleton_of_nonvanishingChart_eq L s hs
    (isProper_of_isClosedImmersion_projectiveSpaceOver i hi) hc hx i₀ h0

end Stacks.ProjectiveSpaceSections

end
