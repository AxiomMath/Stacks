module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionChartStage
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionSolution
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal
public import StacksFrontier.RingTheory.AdicCompletion.ExtendedIdealOfTorsionGap
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Points of an affine chart of the base

Let `V₀ = Spec A` be an affine object of the big fppf site over `S`. A morphism `v : V ⟶ V₀`
of the site is read through the ring map `ρ_v : A → Γ(V)`. This file records a dictionary
between properties of such points and properties of `ρ_v`:

* for `V` affine, `v` avoids the zero locus of `I ⊆ A` exactly when `I Γ(V) = Γ(V)`;
* for a closed subspace `G` of `h_{V₀}` and `V` affine, `v` lies in `G` exactly when `ρ_v` kills
  the ideal cutting out `G`;
* a point killing `I ^ (n + 1)` factors through the quotient stage `Spec (A^∧ ⧸ I ^ (n + 1))`
  of the `I`-adic completion;
* a section of the completion of a closed subspace `G` of a subterminal presheaf exists only
  over objects lying in `G`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Chart

variable {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))} {f : Spec (.of A) ⟶ S}

/-- The ring map `A → Γ(V)` of a morphism `v : V ⟶ Spec A` of the site. -/
noncomputable def chartRing {V : BigFppfOver B S hS} (v : V ⟶ affineOver B S hS hA f) :
    A →+* Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((BigFppfOver.toScheme B S hS).map v).appTop).hom

/-- The ring map of a composite `g ≫ v` is the ring map of `v` followed by the map on global
sections induced by `g`. -/
theorem chartRing_comp {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (v : V ⟶ affineOver B S hS hA f) (a : A) :
    chartRing (g ≫ v) a = ((BigFppfOver.toScheme B S hS).map g).appTop (chartRing v a) := rfl

/-- A morphism into an affine scheme is the spectrum of its ring map. -/
theorem toSpecΓ_comp_spec_chartRing {V : BigFppfOver B S hS} (v : V ⟶ affineOver B S hS hA f) :
    ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartRing v)) =
      (BigFppfOver.toScheme B S hS).map v :=
  Space.toSpecΓ_comp_specMap_appTop _

/-- A point of `h_{Spec A}` lies in `zeroLocusPoints I` exactly when its scheme point lies in
`V(I)`. -/
theorem mem_zeroLocusPoints_iff (I : Ideal A)
    (x : Space.points B S hS (yoneda.obj (affineOver B S hS hA f))) :
    x ∈ zeroLocusPoints B S hS hA f I ↔
      Space.pointsToScheme B S hS _ x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  refine ⟨fun h => h p rfl, fun h q hq => ?_⟩
  rwa [← Space.pointsToScheme_class, hq]

/-- **A point of an affine object avoids `V(I)` exactly when `I` generates the unit ideal of
its ring of functions.** -/
theorem range_subset_compl_zeroLocusPoints_iff (I : Ideal A) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ affineOver B S hS hA f) :
    Set.range (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map v)) ⊆
        (zeroLocusPoints B S hS hA f I)ᶜ ↔ I.map (chartRing v) = ⊤ := by
  have hpts : Set.range (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map v)) ⊆
        (zeroLocusPoints B S hS hA f I)ᶜ ↔
      ∀ y : (BigFppfOver.toScheme B S hS).obj V,
        (BigFppfOver.toScheme B S hS).map v y ∉ PrimeSpectrum.zeroLocus (I : Set A) := by
    constructor
    · intro h y
      obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS V y
      have := h ⟨p, rfl⟩
      rwa [Set.mem_compl_iff, mem_zeroLocusPoints_iff, Space.pointsToScheme_pointsMap_yoneda]
        at this
    · rintro h _ ⟨p, rfl⟩
      rw [Set.mem_compl_iff, mem_zeroLocusPoints_iff, Space.pointsToScheme_pointsMap_yoneda]
      exact h _
  rw [hpts, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top, Set.eq_empty_iff_forall_notMem]
  have : IsIso ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ := IsAffine.affine
  have e : ∀ y, (BigFppfOver.toScheme B S hS).map v y =
      PrimeSpectrum.comap (chartRing v) (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ y) := by
    intro y
    rw [← toSpecΓ_comp_spec_chartRing v]
    rfl
  constructor
  · intro h P hP
    obtain ⟨y, hy⟩ := ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ.homeomorph.surjective P
    apply h y
    rw [e]
    intro a ha
    change chartRing v a ∈ (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ y).asIdeal
    have hy' : ((BigFppfOver.toScheme B S hS).obj V).toSpecΓ y = P := hy
    rw [hy']
    exact hP (Ideal.mem_map_of_mem _ ha)
  · intro h y hy
    apply h (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ y)
    rw [e] at hy
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, ha, rfl⟩ := hb
      exact (hy ha : _)
    | zero => exact Ideal.zero_mem _
    | add a b _ _ ha hb => exact Ideal.add_mem _ ha hb
    | smul r b _ hb => exact Ideal.mul_mem_left _ r hb

/-- **A point of an affine object lies in a closed subspace of `h_{Spec A}` exactly when its
ring map kills the ideal cutting the subspace out.** -/
theorem mem_iff_closedChartRingIdeal_le (G : Subfunctor (yoneda.obj (affineOver B S hS hA f)))
    (hG : Space.IsClosedSubspace B S hS G) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ affineOver B S hS hA f) :
    v ∈ G.obj (Opposite.op V) ↔
      Space.closedChartRingIdeal B S hS f hA G hG ≤ RingHom.ker (chartRing v) := by
  let j := Space.closedChartHom B S hS G hG
  have hj := Space.isClosedImmersion_closedChartHom B S hS G hG
  have hiso := Space.isIso_rep_fst_id B S hS G hG
  have hcomp := Space.rep_fst_id_comp_ι B S hS G hG
  have hrange : v ∈ G.obj (Opposite.op V) ↔ v ∈ (Subfunctor.range (yoneda.map j)).obj
      (Opposite.op V) := by
    constructor
    · intro hv
      let Rf := hG.2.rep.fst (𝟙 (yoneda.obj (affineOver B S hS hA f)))
      refine ⟨(inv Rf).app _ ⟨v, hv⟩, ?_⟩
      have h1 : (yoneda.map j).app _ ((inv Rf).app _ ⟨v, hv⟩) =
          G.ι.app _ (Rf.app _ ((inv Rf).app _ ⟨v, hv⟩)) := by
        rw [← hcomp]; rfl
      have h2 : Rf.app _ ((inv Rf).app _ ⟨v, hv⟩) = ⟨v, hv⟩ := by
        change (inv Rf ≫ Rf).app _ ⟨v, hv⟩ = ⟨v, hv⟩
        rw [IsIso.inv_hom_id]
        rfl
      rw [h1, h2]
      rfl
    · rintro ⟨x, rfl⟩
      rw [← hcomp]
      exact ((hG.2.rep.fst (𝟙 (yoneda.obj (affineOver B S hS hA f)))).app _ x).2
  rw [hrange, Space.mem_range_yoneda_map_iff B S hS j hj]
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map v) := inferInstance
  constructor
  · intro h a ha
    have h' := h ⟨⊤, isAffineOpen_top _⟩
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at h'
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).2).1 ha
    apply RingHom.mem_ker.2
    change ((BigFppfOver.toScheme B S hS).map v).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ((Scheme.ΓSpecIso (CommRingCat.of A)).hom b)) = 0
    rw [Iso.hom_inv_id_apply]
    exact RingHom.mem_ker.1 (h' hb)
  · intro h
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
    intro b hb
    have := RingHom.mem_ker.1 (h (Ideal.mem_map_of_mem _ hb))
    apply RingHom.mem_ker.2
    change ((BigFppfOver.toScheme B S hS).map v).appTop b = 0
    rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of A)) b]
    exact this

end Chart

section Completion

/-- **Sections of the completion of a subterminal algebraic space exist only over objects of
it.** If `G` is a subfunctor of the terminal presheaf which is an algebraic space, an object `V`
of the site over which the completion `G_{/T}` has a section lies in `G`: the section is locally
a section of `G`, and `G` is a sheaf whose values are subsingletons. -/
theorem nonempty_of_completionSheaf (G : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    (hG : IsAlgebraicSpace B S hS G.toFunctor) (T : Set (Space.points B S hS G.toFunctor))
    {V : BigFppfOver B S hS}
    (s : (Space.completionSheaf B S hS G.toFunctor T).obj.obj (Opposite.op V)) :
    Nonempty (G.toFunctor.obj (Opposite.op V)) := by
  classical
  let P := (Space.completionSubfunctor B S hS G.toFunctor T).toFunctor
  let R := Presheaf.imageSieve ((BigFppfOver.topology B S hS).toSheafify P) s
  have hR : R ∈ BigFppfOver.topology B S hS V :=
    Presheaf.imageSieve_mem (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).toSheafify P) s
  have hsub : ∀ W : (BigFppfOver B S hS)ᵒᵖ, Subsingleton (G.toFunctor.obj W) := fun W => by
    have := Artin.ContractionSituation.subsingleton_terminal_obj (B := B) (S := S) (hS := hS) W
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hx : ∀ ⦃V' : BigFppfOver B S hS⦄ (g : V' ⟶ V), R g →
      Nonempty (G.toFunctor.obj (Opposite.op V')) := fun _ _ ⟨t, _⟩ => ⟨t.1.down⟩
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 hG.isSheaf R hR
  let x : Presieve.FamilyOfElements G.toFunctor R.arrows := fun _ g hg => (hx g hg).some
  have hxc : x.Compatible := fun _ _ _ _ _ _ _ _ _ _ => (hsub _).elim _ _
  exact ⟨(hsheaf x hxc).choose⟩

end Completion

end AlgebraicGeometry.FormalSpace
