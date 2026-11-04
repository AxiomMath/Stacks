module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement

/-!
# Open subsets descend along an fpqc covering

Let `{f i : X i ⟶ T}` be an fpqc covering of schemes and let `W i ⊆ X i` be open subsets whose
inverse images along the two projections of `X i ×_T X j` agree for all `i` and `j`. Then there
is a unique open subset `V ⊆ T` with `W i = f i ⁻¹ᵁ V` for every `i`.

The topological input is that an fpqc covering is *jointly submersive*: the map from the
topological sum of the sources of the covering to its target is a quotient map.

## Main results

* `AlgebraicGeometry.isQuotientMap_sigma_of_mem_fpqcPrecoverage`: the map from the topological
  sum of the sources of an fpqc covering to its target is a quotient map.
* `AlgebraicGeometry.existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage`: open subsets of the
  sources of an fpqc covering which agree on the pairwise fibre products come from a unique open
  subset of the target.
* `AlgebraicGeometry.fpqc_jointly_surjective`: the members of an fpqc covering family are
  jointly surjective.

## Implementation notes

An fpqc covering family need not be quasi-compact member by member, and the single morphism out
of the coproduct of its sources need not be a quasi-compact morphism either — a covering of
`Spec k` by countably many copies of `Spec k` is an fpqc covering whose coproduct morphism has a
non-compact source. So Stacks 02JY, that a surjective flat quasi-compact morphism of schemes is a
quotient map, cannot be applied to the coproduct morphism of an arbitrary fpqc covering. It is
applied instead over an affine open of the target, where Stacks 022E refines the covering by a
*standard* one: finitely many flat morphisms with affine sources. The coproduct of those is
affine, so the morphism out of it is quasi-compact over the affine base and is a quotient map;
and a map which becomes a quotient map after precomposition with a continuous map is itself a
quotient map, which is how the refinement is discarded again. The passage from the affine opens
of the target to the target itself is by base change, which an fpqc covering survives.

The index type of the refining family is moved to the universe of the schemes by `ULift`, since
the coproduct comparison `AlgebraicGeometry.sigmaSpec` and the homeomorphism
`AlgebraicGeometry.sigmaMk` between a topological sum and the underlying space of a coproduct
are both stated for an index type in that universe.

The agreement hypothesis is used only through the set-theoretic consequence that a point of
`X i` and a point of `X j` with the same image in `T` lie in `W i` and in `W j` together; the
passage from the hypothesis to that statement is the surjectivity of
`|X i ×_T X j| → |X i| ×_{|T|} |X j|`, Stacks 02KI, which is Mathlib's
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

## References

* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 02JY](https://stacks.math.columbia.edu/tag/02JY)
* [Stacks Project, Tag 02KI](https://stacks.math.columbia.edu/tag/02KI)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The map from the topological sum of the sources of a family of morphisms of schemes with
common target to the underlying space of that target. -/
private def sigmaPointMap {I : Type v} {T : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) : (Σ i, (X i : Type u)) → T :=
  fun p ↦ (f p.1) p.2

private lemma continuous_sigmaPointMap {I : Type v} {T : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ T) : Continuous (sigmaPointMap f) :=
  continuous_sigma fun i ↦ (f i).continuous

/-- An fpqc covering of an *affine* scheme is jointly submersive. -/
private theorem isQuotientMap_sigmaPointMap_of_isAffine {I : Type v} {T : Scheme.{u}}
    [IsAffine T] (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T) :
    Topology.IsQuotientMap (sigmaPointMap f) := by
  classical
  let 𝒰 : PreZeroHypercover.{v} T := { I₀ := I, X := X, f := f }
  obtain ⟨n, 𝒱, φ, hn, -, -⟩ := exists_fin_affineCover_flat_hom_of_mem_fpqcPrecoverage 𝒰 hf
  -- Move the finite index type of the refining family into the universe of the schemes.
  let e : ULift.{u} (Fin n) ≃ 𝒱.I₀ := Equiv.ulift.trans (Equiv.cast hn.symm)
  let R : ULift.{u} (Fin n) → CommRingCat.{u} := fun k ↦ 𝒱.X (e k)
  let h : ∀ k, Spec (R k) ⟶ T := fun k ↦ 𝒱.f (e k)
  have hhflat (k : ULift.{u} (Fin n)) : Flat (h k) := 𝒱.map_prop (e k)
  have haff : IsAffine (∐ fun k ↦ Spec (R k)) := .of_isIso (sigmaSpec R)
  set g : (∐ fun k ↦ Spec (R k)) ⟶ T := Sigma.desc h with hg
  have hgsurj : Surjective g := by
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨y, hy⟩ : t ∈ Set.range (h (e.symm (𝒱.idx t))) := by
      show t ∈ Set.range (𝒱.f (e (e.symm (𝒱.idx t))))
      rw [e.apply_symm_apply]
      exact 𝒱.covers t
    refine ⟨Sigma.ι (fun k ↦ Spec (R k)) (e.symm (𝒱.idx t)) y, ?_⟩
    rw [hg, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    exact hy
  have hgq : Topology.IsQuotientMap g.base := Flat.isQuotientMap_of_surjective g
  set p : (Σ k, (Spec (R k) : Type u)) → (Σ i, (X i : Type u)) :=
    fun q ↦ ⟨φ.s₀ (e q.1), (φ.h₀ (e q.1)) q.2⟩ with hp
  have hcont : Continuous p := by
    refine continuous_sigma fun k ↦ ?_
    exact (continuous_sigmaMk (σ := fun i ↦ (X i : Type u))
      (i := φ.s₀ (e k))).comp (φ.h₀ (e k)).continuous
  refine Topology.IsQuotientMap.of_comp hcont (continuous_sigmaPointMap f) ?_
  have he : sigmaPointMap f ∘ p = g.base ∘ (sigmaMk fun k ↦ Spec (R k)) := by
    refine funext fun q ↦ ?_
    obtain ⟨k, y⟩ := q
    have hw : (𝒰.f (φ.s₀ (e k))) ((φ.h₀ (e k)) y) = (𝒱.f (e k)) y :=
      congrFun (congrArg (fun m : 𝒱.cover.X (e k) ⟶ T ↦ (⇑m : _ → _)) (φ.w₀ (e k))) y
    have h₂ : g.base ((sigmaMk fun k ↦ Spec (R k)) ⟨k, y⟩) = (h k) y := by
      rw [sigmaMk_mk, hg, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    exact hw.trans h₂.symm
  rw [he]
  exact hgq.comp (sigmaMk _).isQuotientMap

/-- The members of an fpqc covering family are jointly surjective and flat. -/
private theorem jointly_surjective_and_flat_of_mem_fpqcPrecoverage {I : Type v} {T : Scheme.{u}}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T) :
    (∀ t : T, ∃ i, t ∈ Set.range (f i)) ∧ ∀ i, Flat (f i) :=
  (Scheme.ofArrows_mem_precoverage_iff (P := (@Flat : MorphismProperty Scheme.{u}))).mp hf.2

/-- **An fpqc covering is jointly submersive.** The map from the topological sum of the sources
of an fpqc covering of schemes to its target is a quotient map: it is surjective, and a subset
of the target is open as soon as its inverse image in every source is open.

For a single surjective flat quasi-compact morphism this is Stacks 02JY,
`AlgebraicGeometry.Flat.isQuotientMap_of_surjective`; the passage to a family is the first half
of the proof of Stacks 03N0. -/
@[sga "1 IX 2.2" "Submersivity", sga "1 VIII 4.3" "more general"]
theorem isQuotientMap_sigma_of_mem_fpqcPrecoverage {I : Type v} {T : Scheme.{u}}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T) :
    Topology.IsQuotientMap (fun p : Σ i, (X i : Type u) ↦ (f p.1) p.2) := by
  classical
  let 𝒰 : PreZeroHypercover.{v} T := { I₀ := I, X := X, f := f }
  have hqc : QuasiCompactCover 𝒰 := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hf.1
  obtain ⟨hjs, hfl⟩ := jointly_surjective_and_flat_of_mem_fpqcPrecoverage hf
  -- The base change of the family along any morphism is again an fpqc covering.
  have hbc : ∀ {Z : Scheme.{u}} (q : Z ⟶ T),
      Presieve.ofArrows (fun i ↦ pullback (f i) q) (fun i ↦ pullback.snd (f i) q) ∈
        Scheme.fpqcPrecoverage Z := by
    intro Z q
    refine ⟨?_, ?_⟩
    · have : QuasiCompactCover (𝒰.pullback₂ q) := inferInstance
      exact Scheme.presieve₀_mem_qcPrecoverage_iff.mpr this
    · refine (Scheme.ofArrows_mem_precoverage_iff
        (P := (@Flat : MorphismProperty Scheme.{u}))).mpr ⟨fun z ↦ ?_, fun i ↦ ?_⟩
      · obtain ⟨i, x, hx⟩ := hjs (q z)
        obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
        exact ⟨i, w, hw⟩
      · have := hfl i
        infer_instance
  refine (Topology.isQuotientMap_iff _).mpr
    ⟨.of_isOpen_preimage_iff_isOpen fun s ↦ ⟨fun hs ↦ ?_,
      fun hs ↦ hs.preimage (continuous_sigmaPointMap f)⟩, fun t ↦ ?_⟩
  -- Openness of a subset of the target is checked on an affine open cover.
  · let 𝒲 := T.affineCover
    rw [𝒲.isOpenCover_opensRange.isOpen_iff_inter]
    intro k
    rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
    refine (𝒲.f k).isOpenEmbedding.isOpenMap _ ?_
    have hqm := isQuotientMap_sigmaPointMap_of_isAffine
      (fun i ↦ pullback (f i) (𝒲.f k)) (fun i ↦ pullback.snd (f i) (𝒲.f k)) (hbc (𝒲.f k))
    refine hqm.isCoinducing.isOpen_preimage.mp ?_
    have he : sigmaPointMap (fun i ↦ pullback.snd (f i) (𝒲.f k)) ⁻¹' ((𝒲.f k) ⁻¹' s) =
        (fun p : Σ i, ↥(pullback (f i) (𝒲.f k)) ↦
          (⟨p.1, (pullback.fst (f p.1) (𝒲.f k)) p.2⟩ : Σ i, (X i : Type u))) ⁻¹'
          (sigmaPointMap f ⁻¹' s) := by
      refine Set.ext fun p ↦ ?_
      obtain ⟨i, z⟩ := p
      have : (𝒲.f k) ((pullback.snd (f i) (𝒲.f k)) z) =
          (f i) ((pullback.fst (f i) (𝒲.f k)) z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      simp only [Set.mem_preimage, sigmaPointMap, this]
    rw [he]
    exact hs.preimage (continuous_sigma fun i ↦
      (continuous_sigmaMk (σ := fun i ↦ (X i : Type u)) (i := i)).comp
        (pullback.fst (f i) (𝒲.f k)).continuous)
  · obtain ⟨i, x, hx⟩ := hjs t
    exact ⟨⟨i, x⟩, hx⟩

/-- A single surjective quasi-compact flat morphism, as a one-member fpqc covering family. -/
theorem ofArrows_unit_mem_fpqcPrecoverage {X S : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    [QuasiCompact f] [Flat f] :
    Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) ∈ Scheme.fpqcPrecoverage S := by
  rw [show Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) = Presieve.singleton f from
    Presieve.ofArrows_pUnit.{0} f]
  exact f.singleton_mem_fpqcPrecoverage

/-- **Stacks 03N0.** Let `{f i : X i ⟶ T}` be an fpqc covering of schemes and let `W i` be an
open subset of `X i` for each `i`, such that the two projections of `X i ×_T X j` pull `W i` and
`W j` back to the same open subset for all `i` and `j`. Then there is a unique open subset `V`
of `T` whose inverse image in `X i` is `W i` for every `i`. -/
@[stacks 03N0, sga "1 VIII 4.4" "more general"]
theorem existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage {I : Type v} {T : Scheme.{u}}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T)
    (W : ∀ i, (X i).Opens)
    (hW : ∀ i j, pullback.fst (f i) (f j) ⁻¹ᵁ W i = pullback.snd (f i) (f j) ⁻¹ᵁ W j) :
    ∃! V : T.Opens, ∀ i, f i ⁻¹ᵁ V = W i := by
  classical
  have hjs := (jointly_surjective_and_flat_of_mem_fpqcPrecoverage hf).1
  -- A point of `X i` and a point of `X j` over the same point of `T` lie in `W i`, `W j`
  -- together.
  have hsat : ∀ (i j : I) (x : X i) (y : X j), (f i) x = (f j) y → (x ∈ W i ↔ y ∈ W j) := by
    intro i j x y hxy
    obtain ⟨z, hzx, hzy⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
    have hz : (z ∈ pullback.fst (f i) (f j) ⁻¹ᵁ W i) ↔
        (z ∈ pullback.snd (f i) (f j) ⁻¹ᵁ W j) := by rw [hW i j]
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, hzx, hzy] at hz
    exact hz
  set Z : Set T := ⋃ i, (f i) '' (W i : Set (X i)) with hZ
  have hpre : ∀ i, (f i) ⁻¹' Z = (W i : Set (X i)) := by
    intro i
    refine Set.ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨j, y, hy, hyx⟩ := Set.mem_iUnion.mp hx
      exact (hsat i j x y hyx.symm).mpr hy
    · exact Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  have hmem (i : I) (x : X i) : (f i) x ∈ Z ↔ x ∈ W i := Set.ext_iff.mp (hpre i) x
  have hopen : IsOpen Z := by
    refine (isQuotientMap_sigma_of_mem_fpqcPrecoverage X f hf).isCoinducing.isOpen_preimage.mp ?_
    have he : (fun p : Σ i, (X i : Type u) ↦ (f p.1) p.2) ⁻¹' Z =
        {p : Σ i, (X i : Type u) | p.2 ∈ W p.1} := by
      refine Set.ext fun p ↦ ?_
      obtain ⟨i, x⟩ := p
      exact hmem i x
    rw [he]
    exact isOpen_sigma_iff.mpr fun i ↦ (W i).2
  refine ⟨⟨Z, hopen⟩, fun i ↦ TopologicalSpace.Opens.ext (hpre i), fun V hV ↦ ?_⟩
  refine TopologicalSpace.Opens.ext (Set.ext fun t ↦ ?_)
  obtain ⟨i, x, hx⟩ := hjs t
  have h₁ : t ∈ V ↔ x ∈ W i := by
    rw [← hV i, Scheme.Hom.mem_preimage, hx]
  have h₂ : t ∈ Z ↔ x ∈ W i := by rw [← hx]; exact hmem i x
  exact h₁.trans h₂.symm

/-- The members of an fpqc covering family are jointly surjective: an fpqc covering family is in
particular a family of flat morphisms which is jointly surjective and quasi-compact. -/
theorem fpqc_jointly_surjective {Y : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage Y) :
    ∀ y : Y, ∃ i, y ∈ Set.range (f i) :=
  (jointly_surjective_and_flat_of_mem_fpqcPrecoverage hf).1

end AlgebraicGeometry

end
