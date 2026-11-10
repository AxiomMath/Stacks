module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.RingHomPi
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Standard fppf refinements over an affine open

An fppf refinement of a morphism of schemes `f : X ⟶ Y` gives, over any affine open `V` of
`Y`, a finite standard fppf covering of `V` whose members factor through affine opens of `X`
contained in `f ⁻¹ᵁ V`. The product of the coordinate rings of the covering members is then
faithfully flat and of finite presentation over the coordinate ring of `V`, which is the
ring-theoretic input to descent of finiteness properties along an fppf refinement.

## Main results

* `AlgebraicGeometry.exists_standardFppfCovering_through_affineOpens` supplies the affine
  opens, their affine fppf refinements, and the faithfully flat finite-presentation product
  map.

## Implementation notes

The statement is made over an arbitrary affine open of the target, without choosing an
ambient affine open of a further base scheme: restriction along a morphism to that base
supplies the map `C → B`. The maps `B → Aᵢ → Bᵢ` come from the restricted scheme morphisms,
and their compatibility is asserted on each component. The map `B → ∏ Bᵢ` is their canonical
`RingHom.pi`. The refinement hypothesis is a morphism from an fppf cover of the target to the
singleton cover consisting of `f`. A finite index type is replaced by `Fin n` so that the
covering is indexed as in the source.

## References

* [Stacks Project, Lemma 35.23.16](https://stacks.math.columbia.edu/tag/06NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- An fppf refinement of `f` gives, over an affine open `V` of the target, a finite affine fppf
cover of `V` each of whose members, composed with the inclusion of `V`, factors through `f`. -/
theorem exists_affineCover_lift_of_fppf_refinement
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∃ 𝒰 : Y.Cover.{v} Scheme.fppfPrecoverage,
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton f)))
    (V : Y.affineOpens) :
    ∃ (F : Scheme.AffineCover.{v} (@Flat ⊓ @LocallyOfFinitePresentation) V.1.toScheme)
      (q : ∀ j, Spec (F.X j) ⟶ X), Finite F.I₀ ∧ ∀ j, q j ≫ f = F.f j ≫ V.1.ι := by
  obtain ⟨𝒰, ⟨r⟩⟩ := h
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  have : CategoryTheory.MorphismProperty.RespectsLeft
      (@Flat ⊓ @LocallyOfFinitePresentation) @IsOpenImmersion :=
    ⟨fun i hi g hg => ⟨MorphismProperty.comp_mem @Flat i g (by infer_instance) hg.1,
      MorphismProperty.comp_mem @LocallyOfFinitePresentation i g (by infer_instance) hg.2⟩⟩
  let E := 𝒰.pullback₁ V.1.ι
  let 𝒰V : (V.1.toScheme).Cover Scheme.fppfPrecoverage := E
  have : QuasiCompactCover E.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun j => by
      have : Flat (𝒰V.f j) := (𝒰V.map_prop j).1
      have : LocallyOfFinitePresentation (𝒰V.f j) := (𝒰V.map_prop j).2
      exact Scheme.Hom.isOpenMap _
  obtain ⟨F, φ, hF, _⟩ := QuasiCompactCover.exists_hom 𝒰V
  let q0 (j : F.I₀) : Spec (F.X j) ⟶ X :=
    φ.h₀ j ≫ pullback.snd V.1.ι (𝒰.f (φ.s₀ j)) ≫ r.h₀ (φ.s₀ j)
  refine ⟨F, q0, hF, fun j => ?_⟩
  have hr : r.h₀ (φ.s₀ j) ≫ f = 𝒰.f (φ.s₀ j) := r.w₀ (φ.s₀ j)
  have hφ : φ.h₀ j ≫ pullback.fst V.1.ι (𝒰.f (φ.s₀ j)) = F.f j := φ.w₀ j
  have hq : q0 j ≫ f = φ.h₀ j ≫ pullback.snd V.1.ι (𝒰.f (φ.s₀ j)) ≫ r.h₀ (φ.s₀ j) ≫ f := by
    dsimp [q0]
    cat_disch
  rw [hq, hr]
  exact (congrArg (φ.h₀ j ≫ ·)
    (pullback.condition (f := V.1.ι) (g := 𝒰.f (φ.s₀ j))).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.1.ι) hφ))

/-- The open cover of `S` by the preimages under `q` of the affine opens of `X` contained in an
open `W` through which `q` factors. -/
@[reducible] def Scheme.Hom.affineOpensLECover {S X : Scheme.{u}} (q : S ⟶ X) (W : X.Opens)
    (hq : ∀ x, q.base x ∈ W) : S.OpenCover where
  I₀ := {A : X.affineOpens // A.1 ≤ W}
  X a := (q ⁻¹ᵁ a.1.1).toScheme
  f a := (q ⁻¹ᵁ a.1.1).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun _ => inferInstance⟩
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hq x) W.isOpen
    exact ⟨⟨⟨A, hA⟩, hAW⟩, ⟨x, hxA⟩, by simp⟩

/-- Refining each member of a finite affine fppf cover by a finite affine open cover gives a
standard fppf covering. -/
theorem isStandardFppfCovering_sigma {S : Scheme.{u}} [IsAffine S]
    (F : Scheme.AffineCover (@Flat ⊓ @LocallyOfFinitePresentation) S) [Finite F.I₀]
    (G : ∀ j, Scheme.AffineCover @IsOpenImmersion (Spec (F.X j))) [∀ j, Finite (G j).I₀] :
    IsStandardFppfCovering (fun i : Σ j, (G j).I₀ => Spec ((G i.1).X i.2))
      (fun i => (G i.1).f i.2 ≫ F.f i.1) := by
  have hF (j : F.I₀) := (F.map_prop j : Flat (F.f j) ∧ LocallyOfFinitePresentation (F.f j))
  have (j : F.I₀) (k : (G j).I₀) : IsOpenImmersion ((G j).f k) := (G j).map_prop k
  refine ⟨inferInstance, inferInstance, fun _ => inferInstance, ?_, ?_, ?_⟩
  · rintro ⟨j, k⟩
    have := (hF j).1
    change Flat ((G j).f k ≫ F.f j)
    infer_instance
  · rintro ⟨j, k⟩
    have := (hF j).2
    change AlgebraicGeometry.FinitePresentation ((G j).f k ≫ F.f j)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨j, x, hx⟩ := F.cover.exists_eq y
    obtain ⟨k, z, hz⟩ := (G j).cover.exists_eq x
    refine Set.mem_iUnion.mpr ⟨⟨j, k⟩, Set.mem_range.mpr ⟨z, ?_⟩⟩
    change F.cover.f j ((G j).cover.f k z) = y
    rw [hz, hx]

/-- Reindexing a standard fppf covering along an equivalence gives a standard fppf covering. -/
theorem IsStandardFppfCovering.reindex {T : Scheme.{u}} {I I' : Type*} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T} (h : IsStandardFppfCovering U f) (e : I' ≃ I) :
    IsStandardFppfCovering (fun i => U (e i)) (fun i => f (e i)) := by
  have := h.finite_index
  refine ⟨.of_equiv _ e.symm, h.affine_target, fun i => h.affine_source (e i),
    fun i => h.flat (e i), fun i => h.finite_presentation (e i),
    Set.eq_univ_of_forall fun x => ?_⟩
  have hx : x ∈ ⋃ j, Set.range (f j) := h.jointly_surjective ▸ trivial
  obtain ⟨j, z, hz⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, rfl⟩ := e.surjective j
  exact Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨z, hz⟩⟩

/-- An fppf refinement of `f` restricts, over an affine open `V` of the target, to a finite
standard fppf covering of `V` whose members factor through affine opens of the source. -/
private theorem exists_finite_affine_refinement
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∃ 𝒰 : Y.Cover.{v} Scheme.fppfPrecoverage,
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton f)))
    (V : Y.affineOpens) :
    ∃ (I : Type max u v) (_ : Finite I) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ V.1.toScheme)
      (U : I → X.affineOpens) (t : ∀ i, T i ⟶ (U i).1.toScheme)
      (hU : ∀ i, (U i).1 ≤ f ⁻¹ᵁ V.1),
      (∀ i, IsAffine (T i)) ∧
      AlgebraicGeometry.IsStandardFppfCovering T g ∧
      ∀ i, t i ≫ f.resLE V.1 (U i).1 (hU i) = g i := by
  obtain ⟨F, q0, _, q0factor⟩ := exists_affineCover_lift_of_fppf_refinement f h V
  have hq0 (j : F.I₀) (x : Spec (F.X j)) : (q0 j).base x ∈ f ⁻¹ᵁ V.1 := by
    have hpt := congrArg (fun k : Spec (F.X j) ⟶ Y => k.base x) (q0factor j)
    simp only [Scheme.Hom.comp_apply] at hpt
    change f.base ((q0 j).base x) ∈ (V.1 : Set Y)
    rw [hpt]
    exact ((F.f j).base x).2
  let O (j : F.I₀) := (q0 j).affineOpensLECover (f ⁻¹ᵁ V.1) (hq0 j)
  have hGexists (j : F.I₀) : ∃ (G : Scheme.AffineCover.{u} @IsOpenImmersion (Spec (F.X j)))
      (ψ : G.cover ⟶ O j), Finite G.I₀ ∧ ∀ k, IsOpenImmersion (ψ.h₀ k) := by
    have : QuasiCompactCover (O j).toPreZeroHypercover :=
      .of_isOpenMap fun a => have := (O j).map_prop a; ((O j).f a).isOpenMap
    exact QuasiCompactCover.exists_hom (P := @IsOpenImmersion) (O j)
  choose G ψ hGfin _ using hGexists
  let I : Type max u v := Σ j : F.I₀, (G j).I₀
  let T : I → Scheme.{u} := fun i => Spec ((G i.1).X i.2)
  let g : ∀ i, T i ⟶ V.1.toScheme := fun i => (G i.1).f i.2 ≫ F.f i.1
  let U : I → X.affineOpens := fun i => ((ψ i.1).s₀ i.2).1
  let t : ∀ i, T i ⟶ (U i).1.toScheme := fun i =>
    (ψ i.1).h₀ i.2 ≫ (q0 i.1).resLE (U i).1 (q0 i.1 ⁻¹ᵁ (U i).1) le_rfl
  have hU (i : I) : (U i).1 ≤ f ⁻¹ᵁ V.1 := ((ψ i.1).s₀ i.2).2
  have ht : ∀ i, t i ≫ f.resLE V.1 (U i).1 (hU i) = g i := by
    rintro ⟨j, k⟩
    refine (cancel_mono V.1.ι).mp ?_
    let qres := (q0 j).resLE (U ⟨j, k⟩).1 (q0 j ⁻¹ᵁ (U ⟨j, k⟩).1) le_rfl
    let fres := f.resLE V.1 (U ⟨j, k⟩).1 (hU ⟨j, k⟩)
    have hqres : qres ≫ (U ⟨j, k⟩).1.ι = (O j).f ((ψ j).s₀ k) ≫ q0 j :=
      Scheme.Hom.resLE_comp_ι (q0 j) le_rfl
    have hfres : fres ≫ V.1.ι = (U ⟨j, k⟩).1.ι ≫ f := Scheme.Hom.resLE_comp_ι f (hU ⟨j, k⟩)
    have hψmap : (ψ j).h₀ k ≫ (O j).f ((ψ j).s₀ k) = (G j).f k := (ψ j).w₀ k
    change (((ψ j).h₀ k ≫ qres) ≫ fres) ≫ V.1.ι = ((G j).f k ≫ F.f j) ≫ V.1.ι
    simp only [Category.assoc]
    rw [hfres, reassoc_of% hqres, reassoc_of% hψmap, q0factor j]
    rfl
  exact ⟨I, inferInstance, T, g, U, t, hU, fun _ => inferInstance,
    isStandardFppfCovering_sigma F G, ht⟩

/-- A morphism admitting an fppf refinement has, over every affine open of its target,
a standard fppf covering factoring through affine opens of its source. The associated
map to the finite product of the covering coordinate rings is faithfully flat and of
finite presentation. -/
theorem exists_standardFppfCovering_through_affineOpens
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∃ 𝒰 : Y.Cover.{v} Scheme.fppfPrecoverage,
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton f)))
    (V : Y.affineOpens) :
    ∃ (n : ℕ) (U : Fin n → X.affineOpens)
      (hU : ∀ i, (U i).1 ≤ f ⁻¹ᵁ V.1)
      (T : Fin n → Scheme.{u})
      (t : ∀ i, T i ⟶ (U i).1.toScheme),
      AlgebraicGeometry.IsStandardFppfCovering T
        (fun i ↦ t i ≫ f.resLE V.1 (U i).1 (hU i)) ∧
      (∀ i, (t i ≫ f.resLE V.1 (U i).1 (hU i)).appTop.hom =
        (t i).appTop.hom.comp (f.resLE V.1 (U i).1 (hU i)).appTop.hom) ∧
      (RingHom.pi (fun i ↦
          (t i ≫ f.resLE V.1 (U i).1 (hU i)).appTop.hom)).FaithfullyFlat ∧
      (RingHom.pi (fun i ↦
          (t i ≫ f.resLE V.1 (U i).1 (hU i)).appTop.hom)).FinitePresentation := by
  obtain ⟨I, hI, T, g, U, t, hU, -, hgstd, ht⟩ := exists_finite_affine_refinement f h V
  let e : Fin (Nat.card I) ≃ I := (Finite.equivFin I).symm
  have hstd : IsStandardFppfCovering (fun i => T (e i))
      (fun i => t (e i) ≫ f.resLE V.1 (U (e i)).1 (hU (e i))) := by
    simpa only [ht] using hgstd.reindex e
  have (i : Fin (Nat.card I)) : IsAffine (T (e i)) := hstd.affine_source i
  have hprime : ∀ {S : Scheme.{u}} [IsAffine S] {T' : Fin (Nat.card I) → Scheme.{u}}
      [∀ i, IsAffine (T' i)] (g : ∀ i, T' i ⟶ S), ⋃ i, Set.range (g i) = Set.univ →
      ∀ p : PrimeSpectrum Γ(S, ⊤), ∃ i, ∃ q : PrimeSpectrum Γ(T' i, ⊤),
        PrimeSpectrum.comap (g i).appTop.hom q = p := by
    intro S _ T' _ g hg p
    have hx : S.isoSpec.inv.base p ∈ ⋃ i, Set.range (g i) := hg ▸ trivial
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hx
    refine ⟨i, (T' i).isoSpec.hom.base z, ?_⟩
    have hnat := congrArg (fun k : Scheme.Hom (T' i) (Spec Γ(S, ⊤)) => k.base z)
      (Scheme.isoSpec_hom_naturality (g i))
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      Scheme.Hom.comp_apply, Spec.map_base] at hnat
    change PrimeSpectrum.comap ((g i).appTop.hom) ((T' i).isoSpec.hom.base z) =
      S.isoSpec.hom.base ((g i).base z) at hnat
    rw [hz] at hnat
    have hinv : S.isoSpec.hom.base (S.isoSpec.inv.base p) = p := by
      change ((S.isoSpec.inv ≫ S.isoSpec.hom) p) = p
      rw [S.isoSpec.inv_hom_id]
      rfl
    rwa [hinv] at hnat
  refine ⟨Nat.card I, fun i => U (e i), fun i => hU (e i), fun i => T (e i), fun i => t (e i),
    hstd, fun i => ?_, ?_, ?_⟩
  · simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  · refine RingHom.FaithfullyFlat.pi (S := fun i => (Γ(T (e i), ⊤) : Type u)) _ (fun i => ?_)
      (hprime _ hstd.jointly_surjective)
    have := hstd.flat i
    exact Scheme.Hom.flat_appTop _
  · refine RingHom.FinitePresentation.pi (S := fun i => (Γ(T (e i), ⊤) : Type u)) _ fun i => ?_
    have := (hstd.finite_presentation i).1
    exact Scheme.Hom.finitePresentation_appTop _

end AlgebraicGeometry
