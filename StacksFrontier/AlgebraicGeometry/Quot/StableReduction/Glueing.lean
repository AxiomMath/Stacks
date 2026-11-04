module

public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.FibreTransport
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.SemilocalDedekind
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.WideSpan

/-!
# Glueing families of curves over a semi-local Dedekind domain

Let `A` be a Dedekind domain with finitely many maximal ideals `𝔪₁, …, 𝔪ₙ` and fraction field
`L`, and let `C` be a scheme over `L`. Suppose that for every `i` there is a proper flat morphism
of finite presentation `Xᵢ ⟶ Spec A_{𝔪ᵢ}`, at-worst-nodal of relative dimension one with stable
fibres of genus `g`, whose generic fibre is `C`. The opens `Spec A_{𝔪ᵢ}` cover `Spec A` and meet
pairwise in the generic point `Spec L`, so the `Xᵢ` glue along `C` to a morphism `Y ⟶ Spec A`
with the same properties (the alternative argument in the proof of [Stacks, Tag 0E98] via
[Stacks, Tag 0E8Z]).

## Main results

* `Stacks.Models.exists_family_of_forall_isLocalization_atPrime`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.WideSpanGlue

/-- If a map `q` out of a wide-span glueing restricts to `r i` on each chart, `r j` lands in `U`,
and every other chart meets `q ⁻¹' U` only in the image of the common subscheme, then
`q ⁻¹' U` is exactly the image of the `j`-th chart. -/
private theorem preimage_eq_range_ι {J : Type u} [Nonempty J] {W T : Scheme.{u}}
    (X : J → Scheme.{u})
    (g : ∀ i, W ⟶ X i) [∀ i, IsOpenImmersion (g i)] {r : ∀ i, X i ⟶ T} {q : glued X g ⟶ T}
    (hq : ∀ i, ι X g i ≫ q = r i)
    {j : J} {U : Set T} (hj : ∀ x, r j x ∈ U)
    (h : ∀ i ≠ j, ∀ x, r i x ∈ U → x ∈ Set.range (g i)) :
    q ⁻¹' U = Set.range (ι X g j) := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, x, rfl⟩ := ι_jointly_surjective X g y
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hq] at hy
    rcases eq_or_ne i j with rfl | hij
    · exact ⟨x, rfl⟩
    · obtain ⟨w, rfl⟩ := h i hij x hy
      exact ⟨g j w, by rw [← Scheme.Hom.comp_apply, glue_condition X g j i, Scheme.Hom.comp_apply]⟩
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hq]
    exact hj x

end AlgebraicGeometry.WideSpanGlue

namespace Stacks.Models

/-- **Glueing stable families over a semi-local Dedekind domain.** Let `A` be a Dedekind domain
with finitely many maximal ideals and fraction field `L`, and `c : C ⟶ Spec L`. If over the
localization of `A` at every maximal ideal there is a proper flat morphism of finite presentation,
at-worst-nodal of relative dimension one, with stable fibres of genus `g` and generic fibre `C`,
then there is such a morphism over `A` itself. -/
theorem exists_family_of_forall_isLocalization_atPrime (A L : Type u) [CommRing A]
    [IsDedekindDomain A] [Field L] [Algebra A L] [IsFractionRing A L]
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) {C : Scheme.{u}} (c : C ⟶ Spec (.of L)) (g : ℕ)
    (h : ∀ (m : Ideal A) [m.IsMaximal],
      ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Algebra A' L)
        (_ : IsScalarTower A A' L) (_ : IsLocalization.AtPrime A' m)
        (X : Scheme.{u}) (p : X ⟶ Spec (.of A'))
        (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap A' L)))),
        e.hom ≫ pullback.snd _ _ = c ∧ IsProper p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧
          IsAtWorstNodalOfRelativeDimensionOne p ∧ ∀ s, IsStableFibreOfGenus g p s) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (.of A))
      (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap A L)))),
      e.hom ≫ pullback.snd _ _ = c ∧ IsProper p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧
        IsAtWorstNodalOfRelativeDimensionOne p ∧ ∀ s, IsStableFibreOfGenus g p s := by
  classical
  choose A' iR iAA' iA'L iT iL X p e he hP hF hLFP hN hS using
    fun m : {m : Ideal A // m.IsMaximal} => @h m.1 m.2
  let jm : ∀ m, Spec (.of (A' m)) ⟶ Spec (.of A) :=
    fun m => Spec.map (CommRingCat.ofHom (algebraMap A (A' m)))
  let tm : ∀ m, Spec (.of L) ⟶ Spec (.of (A' m)) :=
    fun m => Spec.map (CommRingCat.ofHom (algebraMap (A' m) L))
  let jL : Spec (.of L) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A L))
  have htj : ∀ m, tm m ≫ jm m = jL := fun m => by
    simp only [tm, jm, jL, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  have hjm : ∀ m, IsOpenImmersion (jm m) := fun m => by
    have := m.2
    exact isOpenImmersion_specMap_of_isLocalization_atPrime hfin m.1 (A' m)
  have : IsOpenImmersion jL := isOpenImmersion_specMap_of_isFractionRing hfin L
  have htm : ∀ m, IsOpenImmersion (tm m) := fun m => by
    have : IsOpenImmersion (tm m ≫ jm m) := by
      rw [htj]
      infer_instance
    exact IsOpenImmersion.of_comp (tm m) (jm m)
  have hrange : ∀ m (x : Spec (.of A)), x ∈ Set.range (jm m) ↔ x.asIdeal ≤ m.1 := by
    intro m x
    have := m.2
    rw [range_specMap_of_isLocalization_atPrime m.1 (A' m)]
    rfl
  let gm : ∀ m, C ⟶ X m := fun m => (e m).hom ≫ pullback.fst (p m) (tm m)
  have : ∀ m, IsOpenImmersion (gm m) := fun m => inferInstance
  have hgq : ∀ m, gm m ≫ (p m ≫ jm m) = c ≫ jL := fun m => by
    simp only [gm, Category.assoc]
    rw [pullback.condition_assoc, htj, ← Category.assoc, he m]
  let Y := WideSpanGlue.glued X gm
  let q : Y ⟶ Spec (.of A) := WideSpanGlue.desc X gm (fun m => p m ≫ jm m) (c ≫ jL) hgq
  have hιq : ∀ m, WideSpanGlue.ι X gm m ≫ q = p m ≫ jm m :=
    WideSpanGlue.ι_desc X gm (fun m => p m ≫ jm m) (c ≫ jL) hgq
  have hne : Nonempty {m : Ideal A // m.IsMaximal} := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal A
    exact ⟨⟨M, hM⟩⟩
  have hcov : ∀ x : Spec (.of A), ∃ m y, jm m y = x := by
    intro x
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal x.asIdeal x.2.ne_top
    obtain ⟨y, hy⟩ := (hrange ⟨M, hM⟩ x).mpr hle
    exact ⟨⟨M, hM⟩, y, hy⟩
  have hpre : ∀ m, q ⁻¹ᵁ (jm m).opensRange = (WideSpanGlue.ι X gm m).opensRange := fun m => by
    refine TopologicalSpace.Opens.ext <| WideSpanGlue.preimage_eq_range_ι X gm hιq
      (U := Set.range (jm m)) (fun x => ⟨p m x, (Scheme.Hom.comp_apply _ _ _).symm⟩) ?_
    intro i hi x hx
    rw [Scheme.Hom.comp_apply] at hx
    have := m.2
    have := i.2
    obtain ⟨w, hw⟩ : jm i (p i x) ∈ Set.range jL := by
      rw [range_specMap_of_isFractionRing L]
      exact eq_bot_of_le_of_le_of_ne (jm i (p i x)).2 ((hrange m _).mp hx)
        ((hrange i _).mp (Set.mem_range_self (p i x))) (fun h => hi (Subtype.ext h.symm))
    have hw' : tm i w = p i x := (jm i).isOpenEmbedding.injective (by
      rwa [← Scheme.Hom.comp_apply, htj])
    obtain ⟨v, rfl⟩ : x ∈ Set.range (pullback.fst (p i) (tm i)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨w, hw'⟩
    exact ⟨(e i).inv v, by simp only [gm, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩
  have hpb : ∀ m, IsPullback (WideSpanGlue.ι X gm m) (p m) q (jm m) := fun m =>
    (IsOpenImmersion.isPullback (p m) (WideSpanGlue.ι X gm m) (jm m) q (hιq m) (hpre m)).flip
  let 𝒰 : (Spec (.of A)).OpenCover :=
    Scheme.Cover.mkOfCovers {m : Ideal A // m.IsMaximal} (fun m => Spec (.of (A' m))) jm hcov
  have hloc : ∀ (Q : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget Q],
      (∀ m, Q (p m)) → Q q := by
    intro Q _ hQ
    have key : ∀ m : {m : Ideal A // m.IsMaximal}, Q (pullback.snd q (jm m)) := by
      intro m
      refine (Q.cancel_left_of_respectsIso (hpb m).isoPullback.hom _).mp ?_
      rw [(hpb m).isoPullback_hom_snd]
      exact hQ m
    exact IsZariskiLocalAtTarget.of_openCover 𝒰 key
  obtain ⟨m₀⟩ := hne
  have hpbC : IsPullback (gm m₀) c (p m₀) (tm m₀) :=
    IsPullback.of_iso_pullback ⟨by
      simp only [gm, Category.assoc]
      rw [pullback.condition, ← Category.assoc, he m₀]⟩ (e m₀) rfl (he m₀)
  have hgen : IsPullback (gm m₀ ≫ WideSpanGlue.ι X gm m₀) c q jL := by
    have := hpbC.paste_horiz (hpb m₀)
    rwa [htj] at this
  have : IsZariskiLocalAtTarget (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u})
  have : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u})
  refine ⟨Y, q, hgen.isoPullback, hgen.isoPullback_hom_snd, hloc @IsProper hP, hloc @Flat hF,
    hloc @LocallyOfFinitePresentation hLFP,
    hloc (@IsAtWorstNodalOfRelativeDimensionOne) hN, ?_⟩
  intro s
  obtain ⟨m, s', rfl⟩ := hcov s
  exact IsStableFibreOfGenus.of_isPullback (hpb m) s' (hS m s')

end Stacks.Models

end
