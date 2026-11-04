module

public import StacksFrontier.AlgebraicGeometry.Assembly.Relativize

/-!
# Gluing a finite family of charts onto one base chart

Let `S` be a scheme, `V` an open of `S`, and `W : I → S.Opens` a finite family of opens with
`V ⊔ ⨆ i, W i = ⊤` whose **pairwise intersections all lie inside `V`**.  Given a scheme of finite
presentation over `V`, one over each `W i`, and an isomorphism of their base changes to each
`V ⊓ W i`, there is a scheme of finite presentation over `S` restricting to all of them,
compatibly.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_isPullback_glueFamily`: the statement above.

## References

* [Stacks Project, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A chart is the restriction of itself: the square whose top row is the identity and whose
right column is the chart followed by the inclusion of its open. -/
private lemma isPullback_id_ι {S : Scheme.{u}} {V : S.Opens} {A : Scheme.{u}}
    (a : A ⟶ (V : Scheme.{u})) : IsPullback a (𝟙 A) V.ι (a ≫ V.ι) :=
  IsPullback.of_vert_isIso_mono ⟨by simp⟩

section GlueFamily

variable {S : Scheme.{u}} {I : Type u} {V : S.Opens} {W : I → S.Opens} {A : Scheme.{u}}
  {a : A ⟶ (V : Scheme.{u})} {Z : I → Scheme.{u}}
  {z : ∀ i, Z i ⟶ ((W i : S.Opens) : Scheme.{u})}

/-- The gluing statement for the charts indexed by a finset `J`: there is a scheme of finite
presentation over an open `T = V ⊔ ⨆ i ∈ J, W i` restricting to `a` over `V` and to each `z i`,
`i ∈ J`, compatibly with the `φ i`. -/
private theorem exists_glue_finset
    (hinter : ∀ i j, i ≠ j → W i ⊓ W j ≤ V) (ha : FinitePresentation a)
    (hz : ∀ i, FinitePresentation (z i))
    (φ : ∀ i, (Over.pullback (S.homOfLE (inf_le_left : V ⊓ W i ≤ V))).obj (Over.mk a) ≅
      (Over.pullback (S.homOfLE (inf_le_right : V ⊓ W i ≤ W i))).obj (Over.mk (z i)))
    (J : Finset I) :
    ∃ T : S.Opens, T = V ⊔ ⨆ i ∈ J, W i ∧
      ∃ (X : Scheme.{u}) (p : X ⟶ (T : Scheme.{u})) (jA : A ⟶ X),
        FinitePresentation p ∧ IsPullback a jA V.ι (p ≫ T.ι) ∧
          ∀ i ∈ J, ∃ jZ : Z i ⟶ X, IsPullback (z i) jZ (W i).ι (p ≫ T.ι) ∧
            pullback.fst a (S.homOfLE (inf_le_left : V ⊓ W i ≤ V)) ≫ jA =
              (φ i).hom.left ≫
                pullback.fst (z i) (S.homOfLE (inf_le_right : V ⊓ W i ≤ W i)) ≫ jZ := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨V, by simp, A, a, 𝟙 A, ha, isPullback_id_ι a, by simp⟩
  | insert i₀ J hi₀ ih =>
    obtain ⟨T, hT, X, p, jA, hfp, sqA, hrest⟩ := ih
    have hVT : V ≤ T := hT ▸ le_sup_left
    have hWT : ∀ i ∈ J, W i ≤ T := fun i hiJ ↦
      hT ▸ le_sup_of_le_right (le_iSup₂ (f := fun i (_ : i ∈ J) ↦ W i) i hiJ)
    have hOT : V ⊓ W i₀ ≤ T := inf_le_left.trans hVT
    have hOeq : T ⊓ W i₀ = V ⊓ W i₀ := by
      refine le_antisymm (fun x hx ↦ ?_) (inf_le_inf_right _ hVT)
      obtain ⟨hx₁, hx₂⟩ := hx
      rw [hT] at hx₁
      rcases hx₁ with hxV | hxW
      · exact ⟨hxV, hx₂⟩
      · simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk,
          Set.mem_iUnion] at hxW
        obtain ⟨i, hiJ, hxi⟩ := hxW
        exact ⟨hinter i i₀ (fun h ↦ hi₀ (h ▸ hiJ)) ⟨hxi, hx₂⟩, hx₂⟩
    have hsq1 : IsPullback (pullback.fst p (S.homOfLE hOT)) (pullback.snd p (S.homOfLE hOT))
        (p ≫ T.ι) (V ⊓ W i₀ : S.Opens).ι := by
      rw [← Scheme.homOfLE_ι S hOT]
      exact (isPullback_comp_mono_iff T.ι).mpr (IsPullback.of_hasPullback _ _)
    have hsq2 : IsPullback
        (pullback.fst a (S.homOfLE (inf_le_left : V ⊓ W i₀ ≤ V)) ≫ jA)
        (pullback.snd a (S.homOfLE (inf_le_left : V ⊓ W i₀ ≤ V)))
        (p ≫ T.ι) (V ⊓ W i₀ : S.Opens).ι := by
      have h := ((IsPullback.of_hasPullback a
        (S.homOfLE (inf_le_left : V ⊓ W i₀ ≤ V))).flip.paste_vert sqA).flip
      rwa [Scheme.homOfLE_ι] at h
    have hef : (hsq1.isoIsPullback _ _ hsq2).hom ≫
          pullback.fst a (S.homOfLE (inf_le_left : V ⊓ W i₀ ≤ V)) ≫ jA =
        pullback.fst p (S.homOfLE hOT) := hsq1.isoIsPullback_hom_fst _ _ hsq2
    have hes : (hsq1.isoIsPullback _ _ hsq2).hom ≫
          pullback.snd a (S.homOfLE (inf_le_left : V ⊓ W i₀ ≤ V)) =
        pullback.snd p (S.homOfLE hOT) := hsq1.isoIsPullback_hom_snd _ _ hsq2
    obtain ⟨X', p', jX, jZ₀, hfp', sq1', sq2', hcompat'⟩ :=
      exists_finitePresentation_isPullback_sup_of_eq T (W i₀) (V ⊓ W i₀) hOT inf_le_right hOeq
        p (z i₀) hfp (hz i₀) (Over.isoMk (hsq1.isoIsPullback _ _ hsq2) hes ≪≫ φ i₀)
    have sqA' : IsPullback a jA (S.homOfLE hVT) p :=
      (isPullback_comp_mono_iff T.ι).mp (by rwa [Scheme.homOfLE_ι])
    refine ⟨T ⊔ W i₀, ?_, X', p', jA ≫ jX, hfp', ?_, ?_⟩
    · rw [hT, Finset.iSup_insert]
      ac_rfl
    · have h := sqA'.paste_vert sq1'
      rwa [Scheme.homOfLE_ι] at h
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiJ
      · refine ⟨jZ₀, sq2', ?_⟩
        rw [← cancel_epi (hsq1.isoIsPullback _ _ hsq2).hom, reassoc_of% hef]
        simpa only [Iso.trans_hom, Over.comp_left, Over.isoMk_hom_left, Category.assoc]
          using hcompat'
      · obtain ⟨jZi, sqi, hci⟩ := hrest i hiJ
        refine ⟨jZi ≫ jX, ?_, ?_⟩
        · have sqi' : IsPullback (z i) jZi (S.homOfLE (hWT i hiJ)) p :=
            (isPullback_comp_mono_iff T.ι).mp (by rwa [Scheme.homOfLE_ι])
          have h := sqi'.paste_vert sq1'
          rwa [Scheme.homOfLE_ι] at h
        · rw [← Category.assoc, hci]
          simp only [Category.assoc]

/-- **A finite family of charts glues onto a base chart.**  Let `V` and `W i` be opens of `S`
covering it, with `W i ⊓ W j ≤ V` for `i ≠ j`; let `a` be a scheme of finite presentation over
`V`, `z i` one over each `W i`, and `φ i` an isomorphism of their base changes to `V ⊓ W i`.
Then there is a scheme of finite presentation over `S` whose restriction to `V` is `a` and whose
restriction to each `W i` is `z i`, the two restrictions agreeing over `V ⊓ W i` through `φ i`.
-/
theorem exists_finitePresentation_isPullback_glueFamily [Finite I]
    (hcov : V ⊔ ⨆ i, W i = ⊤) (hinter : ∀ i j, i ≠ j → W i ⊓ W j ≤ V)
    (ha : FinitePresentation a) (hz : ∀ i, FinitePresentation (z i))
    (φ : ∀ i, (Over.pullback (S.homOfLE (inf_le_left : V ⊓ W i ≤ V))).obj (Over.mk a) ≅
      (Over.pullback (S.homOfLE (inf_le_right : V ⊓ W i ≤ W i))).obj (Over.mk (z i))) :
    ∃ (X : Scheme.{u}) (q : X ⟶ S) (jA : A ⟶ X), FinitePresentation q ∧
      IsPullback a jA V.ι q ∧
        ∀ i, ∃ jZ : Z i ⟶ X, IsPullback (z i) jZ (W i).ι q ∧
          pullback.fst a (S.homOfLE (inf_le_left : V ⊓ W i ≤ V)) ≫ jA =
            (φ i).hom.left ≫
              pullback.fst (z i) (S.homOfLE (inf_le_right : V ⊓ W i ≤ W i)) ≫ jZ := by
  classical
  have _ : Fintype I := Fintype.ofFinite I
  obtain ⟨T, hT, X, p, jA, hfp, sqA, hrest⟩ := exists_glue_finset hinter ha hz φ Finset.univ
  have hTtop : T = ⊤ := by rw [hT, ← hcov]; simp
  subst hTtop
  refine ⟨X, p ≫ (⊤ : S.Opens).ι, jA, ?_, sqA, fun i ↦ hrest i (Finset.mem_univ i)⟩
  rw [Scheme.Opens.topIso_hom_eq_ι]
  exact hfp.comp_isIso _

end GlueFamily

end AlgebraicGeometry

end
