module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAlgebraizationFibreTower
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismAlgebraizationLocallyFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The open part of the algebraized chart closure

This continues step 3 of the design of the quasi-separated case of Stacks 0GHK
(`StacksFrontier/AlgebraicGeometry/Spaces/MorphismAlgebraizationQuasiSeparated.lean`), after
`AlgebraicGeometry.Space.exists_algebraization_chartClosure`.

The algebraized closed subspace `W ⊆ F ×_S P` has adic fibres `W_n = M_n ×_{V̄ ×_S P} Ṽ`, where
`M = F ×_S P`. These contain the open parts `O_n = M_n ×_{V̄ ×_S P} V`, which are the fibre products
`X_n ×_Y V`, étale over `X_n`. The open subspace `E ⊆ W` with point set
`(|W| \ |W_0|) ∪ G`, where `G` is open with `G ∩ |W_0| = |O_0|`, intersected with the inverse image
of `V ⊆ P`, has adic fibres exactly the `O_n`: so its adic fibres are étale over those of `X`, it
maps to `V`, and the composite `E ⟶ V ⟶ Y` has adic fibres `E_n ⟶ X_n ⟶ Y_n`.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_chart_adicFibre`: the open subspace `E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))}

/-! ### Generic lemmas -/

section Generic

variable {M R Vt V' : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (h : M ⟶ R) (c : Vt ⟶ R)
  (k : V' ⟶ Vt)

/-- The morphism `M ×_R V' ⟶ M ×_R Vt` induced by `k : V' ⟶ Vt` over `R`. -/
def pullbackCompIncl : pullback h (k ≫ c) ⟶ pullback h c :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k) (by
    rw [pullback.condition, Category.assoc])

/-- `M ×_R V' ⟶ M ×_R Vt` followed by the projection to `M`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIncl_fst :
    pullbackCompIncl h c k ≫ pullback.fst h c = pullback.fst h (k ≫ c) :=
  pullback.lift_fst _ _ _

/-- `M ×_R V' ⟶ M ×_R Vt` followed by the projection to `Vt`. -/
@[reassoc (attr := simp)]
theorem pullbackCompIncl_snd :
    pullbackCompIncl h c k ≫ pullback.snd h c = pullback.snd h (k ≫ c) ≫ k :=
  pullback.lift_snd _ _ _

/-- `M ×_R V' ⟶ M ×_R Vt` is the base change of `k`. -/
theorem isPullback_pullbackCompIncl :
    IsPullback (pullback.snd h (k ≫ c)) (pullbackCompIncl h c k) k (pullback.snd h c) := by
  refine IsPullback.of_bot ?_ (pullbackCompIncl_snd h c k).symm
    (IsPullback.of_hasPullback h c).flip
  rw [pullbackCompIncl_fst]
  exact (IsPullback.of_hasPullback h (k ≫ c)).flip

end Generic

/-- **The points of the adic fibre of an open subspace.** For a subfunctor `E` of `W` over the
base, the image on points of `E_n ⟶ W_n` is the inverse image of the points of `E` under
`W_n ⟶ W`. -/
theorem range_pointsMap_adicFibreMap_ι {hSn : ∀ n, B.Contains (adicThickening A I n)}
    {W : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    {fW : W ⟶ yoneda.obj (baseObject A B hS)} (E : Subfunctor W) (n : ℕ) :
    Set.range (pointsMap B _ hS _ (adicFibreMap A I B hS hSn E.ι rfl n)) =
      pointsMap B _ hS _ (pullback.fst fW (yoneda.map (adicThickeningMap A I B hS hSn n))) ⁻¹'
        Set.range (pointsMap B _ hS _ E.ι) := by
  have hsq := isPullback_adicFibreMap_fst (fF := fW) (hSn := hSn) E.ι n
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage, ← pointsMap_comp_apply, ← hsq.w, pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B _ hS hsq z y hz
    exact ⟨w, hw⟩

/-- **Two open immersions with the same image on points differ by an isomorphism.** -/
theorem exists_isIso_comp_eq_of_range_pointsMap_eq
    {P₁ P₂ Q : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (h₁ : IsAlgebraicSpace B _ hS P₁) (h₂ : IsAlgebraicSpace B _ hS P₂) {j₁ : P₁ ⟶ Q}
    {j₂ : P₂ ⟶ Q} (hj₁ : IsOpenImmersion B _ hS j₁) (hj₂ : IsOpenImmersion B _ hS j₂)
    (h : Set.range (pointsMap B _ hS _ j₁) = Set.range (pointsMap B _ hS _ j₂)) :
    ∃ l : P₁ ⟶ P₂, IsIso l ∧ l ≫ j₂ = j₁ := by
  have := mono_of_isOpenImmersion B _ hS _ hj₁
  have := mono_of_isOpenImmersion B _ hS _ hj₂
  have hrange : Subfunctor.range j₁ = Subfunctor.range j₂ := by
    refine le_antisymm
      (le_of_range_pointsMap_ι_subset B _ hS (isOpenSubspace_subfunctorRange B _ hS h₂ hj₂) ?_)
      (le_of_range_pointsMap_ι_subset B _ hS (isOpenSubspace_subfunctorRange B _ hS h₁ hj₁) ?_) <;>
    rw [range_pointsMap_ι_range_of_mono, range_pointsMap_ι_range_of_mono, h]
  let l : P₁ ⟶ P₂ := Subfunctor.lift j₁ hrange.le ≫ (rangeIsoOfMono B _ hS j₂).inv
  let m : P₂ ⟶ P₁ := Subfunctor.lift j₂ hrange.ge ≫ (rangeIsoOfMono B _ hS j₁).inv
  have hl : l ≫ j₂ = j₁ := by
    simp only [l, Category.assoc, rangeIsoOfMono_inv_comp, Subfunctor.lift_ι]
  have hm : m ≫ j₁ = j₂ := by
    simp only [m, Category.assoc, rangeIsoOfMono_inv_comp, Subfunctor.lift_ι]
  exact ⟨l, ⟨⟨m, (cancel_mono j₁).1 (by rw [Category.assoc, hm, hl, Category.id_comp]),
    (cancel_mono j₂).1 (by rw [Category.assoc, hl, hm, Category.id_comp])⟩⟩, hl⟩

/-! ### The chart closure and its open part -/

section Chart

variable {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
  {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
  (g : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) fX n ⟶ adicFibre A I B hS
      (contains_adicThickening A I B hS) fY n)
  {V P : BigFppfOver B (Spec (.of A)) hS} (v : yoneda.obj V ⟶ Y) (p : P ⟶ baseObject A B hS)
  (o : V ⟶ P) {Vb Vt : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (πb : Vb ⟶ Y)
  (k : yoneda.obj V ⟶ Vt) (c : Vt ⟶ pullback (πb ≫ fY) (yoneda.map p))
  {F : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (π : F ⟶ X)
  (u : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) (π ≫ fX) n ⟶ Vb)
  {W : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (i : W ⟶ pullback (π ≫ fX) (yoneda.map p))
  (e : ∀ n, pullback (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c ≅
    adicFibre A I B hS (contains_adicThickening A I B hS) (i ≫ pullback.fst (π ≫ fX) (yoneda.map p)
        ≫ π ≫ fX) n)

/-- The open part `O_n = M_n ×_{V̄ ×_S P} V` of the `n`-th adic fibre of the chart closure is
`X_n ×_Y V`: its projections to `V` and to `X_n` form a cartesian square over `v`. -/
theorem isPullback_chartOpenPart
    (hsqu : ∀ n, IsPullback (u n) (adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG :=
        fX) π rfl n) πb
      (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B
          hS) n))))
    (hkv : k ≫ c ≫ pullback.fst _ _ ≫ πb = v) (n : ℕ) :
    IsPullback (pullback.snd (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) (k ≫ c))
      (pullback.fst _ _ ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := π ≫ fX)
        (pullback.fst (π ≫ fX) (yoneda.map p)) rfl n ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := fX) π rfl n) v
      (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B
          hS) n))) := by
  have h1 := (IsPullback.of_hasPullback (adicFibreProdMap (fQ := πb ≫ fY) p n (u n))
    (k ≫ c)).flip.paste_vert ((isPullback_adicFibreProdMap p n (u n)).paste_vert (hsqu n))
  have h2 : (k ≫ c) ≫ pullback.fst (πb ≫ fY) (yoneda.map p) ≫ πb = v := by
    simpa only [Category.assoc] using hkv
  rwa [h2] at h1

/-- The open part of the `n`-th adic fibre, followed by `W_n ⟶ W ⟶ P`, is `O_n ⟶ V ⟶ P`. -/
theorem chartOpenPart_comp_snd
    (he1 : ∀ n, (e n).hom ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) i rfl n =
        pullback.fst _ _)
    (hko : k ≫ c ≫ pullback.snd _ _ = yoneda.map o) (n : ℕ) :
    pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k ≫ (e n).hom ≫
        pullback.fst (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
          (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)) ≫
        i ≫ pullback.snd (π ≫ fX) (yoneda.map p) =
      pullback.snd _ _ ≫ yoneda.map o := by
  have h1 : (e n).hom ≫ pullback.fst (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)) ≫ i =
      pullback.fst _ _ ≫ pullback.fst (pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)) := by
    have h := congrArg (fun t => t ≫ pullback.fst (pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
      (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n))) (he1 n)
    simp only [Category.assoc, adicFibreMap_fst] at h
    exact h
  rw [reassoc_of% h1, ← adicFibreProdMap_snd (fQ := πb ≫ fY) p n (u n), pullback.condition_assoc,
    pullbackCompIncl_snd_assoc, hko]

/-- The open part of the `n`-th adic fibre, followed by `W_n ⟶ X_n`, is `O_n ⟶ M_n ⟶ X_n`. -/
theorem chartOpenPart_comp_adicFibreMap
    (he1 : ∀ n, (e n).hom ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) i rfl n =
        pullback.fst _ _) (n : ℕ) :
    pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k ≫ (e n).hom ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) (fG := fX)
          (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π) (by simp only [Category.assoc]) n =
      pullback.fst _ _ ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := π ≫ fX)
        (pullback.fst (π ≫ fX) (yoneda.map p)) rfl n ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := fX) π rfl n := by
  have h1 : adicFibreMap A I B hS (contains_adicThickening A I B hS)
      (fF := i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) (fG := fX)
      (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π) (by simp only [Category.assoc]) n =
      adicFibreMap A I B hS (contains_adicThickening A I B hS) i rfl n ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := π ≫ fX)
        (pullback.fst (π ≫ fX) (yoneda.map p)) rfl n ≫
          adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := fX) π rfl n := by
    apply pullback.hom_ext <;> simp
  rw [h1, ← Category.assoc ((e n).hom), he1 n, pullbackCompIncl_fst_assoc]

/-- The image on points of the open part `O_n ⟶ W_n` consists of the points of `W_n` whose image
in `Ṽ` lies in `V`. -/
theorem range_pointsMap_chartOpenPart (n : ℕ) :
    Set.range (pointsMap B _ hS _
      (pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k ≫ (e n).hom)) =
      pointsMap B _ hS _ ((e n).inv ≫
        pullback.snd (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c) ⁻¹'
          Set.range (pointsMap B _ hS _ k) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨pointsMap B _ hS _ (pullback.snd _ _) z, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]
    congr 1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, pullbackCompIncl_snd]
  · rintro ⟨t, ht⟩
    obtain ⟨z, -, hz⟩ := exists_points_of_isPullback B _ hS
      (isPullback_pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k) t
      (pointsMap B _ hS _ (e n).inv y) (by rw [ht, ← pointsMap_comp_apply])
    refine ⟨z, ?_⟩
    rw [pointsMap_comp_apply, hz, ← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id]
    rfl

/-- **The open part of every adic fibre is cut out by one open subset of `|W|`.** There is an
open `U ⊆ |W|` whose inverse image in every `|W_n|` is the set of points lying over `V ⊆ Ṽ`. -/
theorem exists_isOpen_preimage_chartOpenPart (hW : IsAlgebraicSpace B _ hS W)
    (hk : IsOpenImmersion B _ hS k)
    (hu : ∀ n, adicFibreSucc A I B hS (contains_adicThickening A I B hS) (π ≫ fX) n ≫ u (n + 1) = u
        n)
    (he2 : ∀ n, fibreTowerSucc (fun n => adicFibreProdMap (fQ := πb ≫ fY) p n (u n))
        (adicFibreSucc_adicFibreProdMap p u hu) c n ≫ (e (n + 1)).hom =
      (e n).hom ≫ adicFibreSucc A I B hS (contains_adicThickening A I B hS)
        (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n) :
    ∃ U : Set (points B _ hS W), IsOpen U ∧ ∀ n,
      pointsMap B _ hS _ (pullback.fst (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n))) ⁻¹' U =
      pointsMap B _ hS _ ((e n).inv ≫
        pullback.snd (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c) ⁻¹'
          Set.range (pointsMap B _ hS _ k) := by
  classical
  have hopen : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hω0 : IsOpenImmersion B _ hS
      (pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p 0 (u 0)) c k ≫ (e 0).hom) :=
    isOpenImmersion_comp B _ hS _ _
      (MorphismProperty.of_isPullback (isPullback_pullbackCompIncl _ c k) hk)
      (isOpenImmersion_of_isIso B _ hS _)
  have hr0 : IsClosedImmersion B _ hS
      (pullback.fst (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
          (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) 0))) := by
    have := isClosedImmersion_isStableUnderBaseChange B (Spec (.of A)) hS
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) _).flip
      ((presheaf_yoneda_map_iff B (Spec (.of A)) hS inferInstance _).2
        (isClosedImmersion_toScheme_map_adicThickeningMap A I B hS _ 0))
  have hemb := isEmbedding_pointsMap_of_isImmersion B _ hS hW _
    (isImmersion_of_isClosedImmersion B _ hS hr0)
  obtain ⟨G, hGo, hG⟩ := hemb.isInducing.isOpen_iff.1
    (isOpen_range_pointsMap_of_isOpenImmersion B _ hS _ hω0)
  refine ⟨(Set.range (pointsMap B _ hS _
      (pullback.fst (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
          (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) 0)))))ᶜ ∪ G,
    (isClosed_range_pointsMap_of_isClosedImmersion B _ hS hW _ hr0).isOpen_compl.union hGo,
    fun n => ?_⟩
  induction n with
  | zero =>
    rw [Set.preimage_union, Set.preimage_compl, Set.preimage_range, Set.compl_univ,
      Set.empty_union, hG, range_pointsMap_chartOpenPart]
  | succ n ih =>
    have hσP : (e n).inv ≫ pullback.snd (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c =
        adicFibreSucc A I B hS (contains_adicThickening A I B hS) (i ≫ pullback.fst (π ≫ fX)
            (yoneda.map p) ≫ π ≫ fX)
            n ≫ (e (n + 1)).inv ≫
          pullback.snd (adicFibreProdMap (fQ := πb ≫ fY) p (n + 1) (u (n + 1))) c := by
      have h1 : (e n).inv ≫ fibreTowerSucc (fun n => adicFibreProdMap (fQ := πb ≫ fY) p n (u n))
          (adicFibreSucc_adicFibreProdMap p u hu) c n =
          adicFibreSucc A I B hS (contains_adicThickening A I B hS) (i ≫ pullback.fst (π ≫ fX)
              (yoneda.map p) ≫ π ≫ fX)
              n ≫ (e (n + 1)).inv := by
        calc _ = (e n).inv ≫ fibreTowerSucc (fun n => adicFibreProdMap (fQ := πb ≫ fY) p n (u n))
              (adicFibreSucc_adicFibreProdMap p u hu) c n ≫ (e (n + 1)).hom ≫ (e (n + 1)).inv := by
              rw [Iso.hom_inv_id, Category.comp_id]
          _ = _ := by rw [reassoc_of% (he2 n), Iso.inv_hom_id_assoc]
      rw [← reassoc_of% h1, fibreTowerSucc_snd]
    have hT : Function.Surjective (pointsMap B _ hS _
        (yoneda.map (adicThickeningSuccMap A I B hS (contains_adicThickening A I B hS) n))) :=
      (surjective_yonedaMap_iff_surjective_pointsMap B _ hS _).1
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B _ hS @Surjective _).2
          (surjective_adicThickeningSucc A I n))
    ext y
    obtain ⟨t, ht⟩ := hT (pointsMap B _ hS _
      (pullback.snd (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
          (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) (n + 1)))) y)
    obtain ⟨x, rfl, -⟩ := exists_points_of_isPullback B _ hS
      (isPullback_adicFibreSucc A I B hS _ (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
          n) y t ht.symm
    have hx := congrArg (x ∈ ·) ih
    simp only [Set.mem_preimage, eq_iff_iff] at hx ⊢
    simp only [← pointsMap_comp_apply]
    rw [adicFibreSucc_fst, ← hσP]
    exact hx

/-- **The adic fibres of `E ⟶ V ⟶ Y`.** Let `E ⊆ W` be a subfunctor with a morphism
`ℓ : E ⟶ V` lying over `P`, and let `E_n ⟶ O_n` identify the `n`-th adic fibre of `E` with the
open part `O_n` of `W_n`. Then the `n`-th adic fibre of `E ⟶ V ⟶ Y` is `E_n ⟶ X_n` followed by
`g_n`. -/
theorem adicFibreMap_chart_comp_eq (ho : IsOpenImmersion B _ hS (yoneda.map o))
    (hg : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS
        (contains_adicThickening A I B hS) n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS)
          n)))
    (hsqu : ∀ n, IsPullback (u n) (adicFibreMap A I B hS (contains_adicThickening A I B hS) π rfl
        n) πb
      (g n ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B
          hS) n))))
    (hkv : k ≫ c ≫ pullback.fst _ _ ≫ πb = v) (hko : k ≫ c ≫ pullback.snd _ _ = yoneda.map o)
    (he1 : ∀ n, (e n).hom ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) i rfl n =
        pullback.fst _ _)
    (E : Subfunctor W) (ℓ : E.toFunctor ⟶ yoneda.obj V)
    (hℓ : ℓ ≫ yoneda.map o = E.ι ≫ i ≫ pullback.snd (π ≫ fX) (yoneda.map p)) (n : ℕ)
    (lam : adicFibre A I B hS (contains_adicThickening A I B hS) (E.ι ≫ i ≫ pullback.fst (π ≫ fX)
        (yoneda.map p) ≫ π ≫ fX) n ⟶
      pullback (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) (k ≫ c))
    (hlam : lam ≫ pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k ≫
      (e n).hom = adicFibreMap A I B hS (contains_adicThickening A I B hS) E.ι rfl n)
    (hcompE : adicFibreMap A I B hS (contains_adicThickening A I B hS)
      (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
      (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n =
      lam ≫ pullback.fst _ _ ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := π ≫ fX) (pullback.fst (π ≫
            fX) (yoneda.map p)) rfl n ≫
          adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := fX) π rfl n) :
    adicFibreMap A I B hS (contains_adicThickening A I B hS) (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π
        ≫ fX) (fG := fY)
        (ℓ ≫ v) (eq_of_hom_yoneda_baseObject _ _) n =
      adicFibreMap A I B hS (contains_adicThickening A I B hS) (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫
          π ≫ fX) (fG := fX)
        (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n ≫ g n := by
  have hmo : Mono (yoneda.map o) := mono_of_isOpenImmersion B _ hS _ ho
  apply pullback.hom_ext
  · have hsq := isPullback_chartOpenPart g v p πb k c π u hsqu hkv n
    have hV : pullback.fst (E.ι ≫ i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)) ≫ ℓ =
        lam ≫ pullback.snd (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) (k ≫ c) := by
      refine (cancel_mono (yoneda.map o)).1 ?_
      rw [Category.assoc, hℓ, Category.assoc,
        ← chartOpenPart_comp_snd p o πb k c π u i e he1 hko n, reassoc_of% hlam,
        adicFibreMap_fst_assoc]
    rw [adicFibreMap_fst, Category.assoc, hcompE, reassoc_of% hV, hsq.w]
    simp only [Category.assoc]
  · rw [adicFibreMap_snd, Category.assoc, hg n, adicFibreMap_snd]

end Chart

/-- **The open part of the algebraized chart closure.** In the situation of
`AlgebraicGeometry.Space.exists_algebraization_chartClosure`, with `k : V ⟶ Ṽ` an open immersion
such that `V ⟶ Ṽ ⟶ V̄ ×_S P` is `v` after `π̄` and `o` on the second factor, there is an open
subspace `E ⊆ W` and a morphism `ℓ : E ⟶ V` over `P` such that the adic fibres of
`E ⟶ W ⟶ X` are étale, surjective on the closed fibre, and the adic fibres of `E ⟶ V ⟶ Y` are
those of `E ⟶ X` followed by `g_n`. -/
theorem exists_isOpenSubspace_chart_adicFibre
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (g : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) fX n ⟶
      adicFibre A I B hS (contains_adicThickening A I B hS) fY n)
    (hg : ∀ n, g n ≫ pullback.snd fY
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)) =
      pullback.snd fX
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n)))
    {V P : BigFppfOver B (Spec (.of A)) hS} (v : yoneda.obj V ⟶ Y) (hv : IsEtale B _ hS v)
    (hvs : IsSurjective B _ hS v) (p : P ⟶ baseObject A B hS) (o : V ⟶ P)
    (ho : IsOpenImmersion B _ hS (yoneda.map o))
    {Vb Vt : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hVb : IsAlgebraicSpace B _ hS Vb)
    (πb : Vb ⟶ Y) (k : yoneda.obj V ⟶ Vt)
    (hk : IsOpenImmersion B _ hS k) (c : Vt ⟶ pullback (πb ≫ fY) (yoneda.map p))
    (hkv : k ≫ c ≫ pullback.fst _ _ ≫ πb = v) (hko : k ≫ c ≫ pullback.snd _ _ = yoneda.map o)
    {F : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B _ hS F)
    (π : F ⟶ X)
    (u : ∀ n, adicFibre A I B hS (contains_adicThickening A I B hS) (π ≫ fX) n ⟶ Vb)
    (hsqu : ∀ n, IsPullback (u n)
      (adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := fX) π rfl n)
      πb (g n ≫ pullback.fst fY
        (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B hS) n))))
    (hu : ∀ n, adicFibreSucc A I B hS (contains_adicThickening A I B hS) (π ≫ fX) n ≫
      u (n + 1) = u n)
    {W : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B _ hS W)
    (i : W ⟶ pullback (π ≫ fX) (yoneda.map p))
    (e : ∀ n, pullback (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c ≅
      adicFibre A I B hS (contains_adicThickening A I B hS)
        (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n)
    (he1 : ∀ n, (e n).hom ≫ adicFibreMap A I B hS (contains_adicThickening A I B hS) i rfl n =
      pullback.fst _ _)
    (he2 : ∀ n, fibreTowerSucc (fun n => adicFibreProdMap (fQ := πb ≫ fY) p n (u n))
        (adicFibreSucc_adicFibreProdMap p u hu) c n ≫ (e (n + 1)).hom =
      (e n).hom ≫ adicFibreSucc A I B hS (contains_adicThickening A I B hS)
        (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n) :
    ∃ (E : Subfunctor W) (ℓ : E.toFunctor ⟶ yoneda.obj V),
      IsOpenSubspace B _ hS E ∧
      ℓ ≫ yoneda.map o = E.ι ≫ i ≫ pullback.snd _ _ ∧
      (∀ n, IsEtale B _ hS (adicFibreMap A I B hS (contains_adicThickening A I B hS)
        (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
          (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n)) ∧
      (∀ x : points B _ hS (adicFibre A I B hS (contains_adicThickening A I B hS) fX 0),
        ∃ y, pointsMap B _ hS _ (adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
          (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) 0) y = x) ∧
      ∀ n, adicFibreMap A I B hS (contains_adicThickening A I B hS) (fF := E.ι ≫ i ≫ pullback.fst _
          _ ≫ π ≫ fX) (fG := fY)
          (ℓ ≫ v) (eq_of_hom_yoneda_baseObject _ _) n =
        adicFibreMap A I B hS (contains_adicThickening A I B hS)
          (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
          (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n ≫ g n := by
  classical
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  have hPyo := isAlgebraicSpace_yoneda B _ hS P
  have hVyo := isAlgebraicSpace_yoneda B _ hS V
  have hopen : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨U, hUo, hU⟩ := exists_isOpen_preimage_chartOpenPart p πb k c π u i e hW hk hu he2
  have hRo : IsOpen (Set.range (pointsMap B _ hS _ (yoneda.map o))) :=
    isOpen_range_pointsMap_of_isOpenImmersion B _ hS _ ho
  have hU'o : IsOpen (U ∩ pointsMap B _ hS _ (i ≫ pullback.snd (π ≫ fX) (yoneda.map p)) ⁻¹'
      Set.range (pointsMap B _ hS _ (yoneda.map o))) :=
    hUo.inter (hRo.preimage (continuous_pointsMap B _ hS _))
  obtain ⟨E, hEdef⟩ : ∃ E : Subfunctor W, E = openSubspaceOfPoints B _ hS W (U ∩
      pointsMap B _ hS _ (i ≫ pullback.snd (π ≫ fX) (yoneda.map p)) ⁻¹'
        Set.range (pointsMap B _ hS _ (yoneda.map o))) := ⟨_, rfl⟩
  have hE : IsOpenSubspace B _ hS E := hEdef ▸ isOpenSubspace_openSubspaceOfPoints B _ hS hW _ hU'o
  have hω : ∀ n, IsOpenImmersion B _ hS
      (pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k ≫ (e n).hom) :=
    fun n => isOpenImmersion_comp B _ hS _ _
      (MorphismProperty.of_isPullback (isPullback_pullbackCompIncl _ c k) hk)
      (isOpenImmersion_of_isIso B _ hS _)
  have hj1 : ∀ n, IsOpenImmersion B _ hS (adicFibreMap A I B hS (contains_adicThickening A I B hS)
      E.ι
      (rfl : E.ι ≫ i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX = _) n) := fun n =>
    MorphismProperty.of_isPullback
      (isPullback_adicFibreMap_fst (fF := i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX)
        (hSn := (contains_adicThickening A I B hS)) E.ι n) hE.2
  have hpts : ∀ n, Set.range (pointsMap B _ hS _ (adicFibreMap A I B hS (contains_adicThickening A
      I B hS) E.ι
      (rfl : E.ι ≫ i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX = _) n)) =
      Set.range (pointsMap B _ hS _
        (pullbackCompIncl (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) c k ≫ (e n).hom)) := by
    intro n
    rw [range_pointsMap_adicFibreMap_ι, hEdef, range_pointsMap_ι_openSubspaceOfPoints,
      Set.preimage_inter, hU n, ← range_pointsMap_chartOpenPart, Set.inter_eq_left]
    rintro _ ⟨z, rfl⟩
    have h1 := chartOpenPart_comp_snd p o πb k c π u i e he1 hko n
    simp only [Set.mem_preimage, ← pointsMap_comp_apply, Category.assoc, h1]
    rw [pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  have hEn : ∀ n, IsAlgebraicSpace B _ hS (adicFibre A I B hS (contains_adicThickening A I B hS)
      (E.ι ≫ i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n) :=
    isAlgebraicSpace_adicFibre A I B hS _ hE.1 _
  have hMn : ∀ n, IsAlgebraicSpace B _ hS (adicFibre A I B hS (contains_adicThickening A I B hS)
      (pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) n) :=
    isAlgebraicSpace_adicFibre A I B hS _ (isAlgebraicSpace_pullback B _ hS _ _ hF hPyo hbase) _
  have hVbP : IsAlgebraicSpace B _ hS (pullback (πb ≫ fY) (yoneda.map p)) :=
    isAlgebraicSpace_pullback B _ hS _ _ hVb hPyo hbase
  have hOn : ∀ n, IsAlgebraicSpace B _ hS
      (pullback (adicFibreProdMap (fQ := πb ≫ fY) p n (u n)) (k ≫ c)) := fun n =>
    isAlgebraicSpace_pullback B _ hS _ _ (hMn n) hVyo hVbP
  choose lam hlamiso hlam using fun n =>
    exists_isIso_comp_eq_of_range_pointsMap_eq (hEn n) (hOn n) (hj1 n) (hω n) (hpts n)
  have hcompE : ∀ n, adicFibreMap A I B hS (contains_adicThickening A I B hS)
      (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
      (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n =
      lam n ≫ pullback.fst _ _ ≫
        adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := π ≫ fX)
        (pullback.fst (π ≫ fX) (yoneda.map p)) rfl n ≫
          adicFibreMap A I B hS (contains_adicThickening A I B hS) (fG := fX) π rfl n := by
    intro n
    have h1 : adicFibreMap A I B hS (contains_adicThickening A I B hS)
        (fF := E.ι ≫ i ≫ pullback.fst _ _ ≫ π ≫ fX) (fG := fX)
        (E.ι ≫ i ≫ pullback.fst _ _ ≫ π) (by simp only [Category.assoc]) n =
        adicFibreMap A I B hS (contains_adicThickening A I B hS) E.ι rfl n ≫
          adicFibreMap A I B hS (contains_adicThickening A I B hS)
            (fF := i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π ≫ fX) (fG := fX)
            (i ≫ pullback.fst (π ≫ fX) (yoneda.map p) ≫ π) (by simp only [Category.assoc]) n := by
      apply pullback.hom_ext <;> simp
    rw [h1, ← hlam n, Category.assoc, Category.assoc,
      chartOpenPart_comp_adicFibreMap p πb k c π u i e he1 n]
  -- `ℓ : E ⟶ V`
  have hEle : E ≤ (Subfunctor.range (yoneda.map o)).preimage
      (i ≫ pullback.snd (π ≫ fX) (yoneda.map p)) := by
    rw [hEdef, range_eq_openSubspaceOfPoints_of_isOpenImmersion B _ hS _ ho,
      preimage_openSubspaceOfPoints']
    intro T x hx
    exact (mem_openSubspaceOfPoints_iff B _ hS _ x).2
      (((mem_openSubspaceOfPoints_iff B _ hS _ x).1 hx).trans Set.inter_subset_right)
  have hmo : Mono (yoneda.map o) := mono_of_isOpenImmersion B _ hS _ ho
  have hEle' : Subfunctor.range (E.ι ≫ i ≫ pullback.snd (π ≫ fX) (yoneda.map p)) ≤
      Subfunctor.range (yoneda.map o) := by
    rintro T _ ⟨x, rfl⟩
    exact hEle T x.2
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : E.toFunctor ⟶ yoneda.obj V,
      ℓ ≫ yoneda.map o = E.ι ≫ i ≫ pullback.snd (π ≫ fX) (yoneda.map p) :=
    ⟨Subfunctor.lift _ hEle' ≫ (rangeIsoOfMono B _ hS (yoneda.map o)).inv, by
      simp only [Category.assoc, rangeIsoOfMono_inv_comp, Subfunctor.lift_ι]⟩
  refine ⟨E, ℓ, hE, hℓ, fun n => ?_, fun x => ?_, fun n => ?_⟩
  · -- étale
    have := hlamiso n
    rw [hcompE n]
    exact isEtale_comp B _ hS (isEtale_of_isIso B _ hS _)
      (isEtale_snd_of_isPullback (hOn n) hVyo
        (isAlgebraicSpace_adicFibre A I B hS _ hX fX n) hY
        (isPullback_chartOpenPart g v p πb k c π u hsqu hkv n) hv)
  · -- surjective on the closed fibre
    have := hlamiso 0
    obtain ⟨t, ht⟩ := hvs (pointsMap B _ hS _
      (g 0 ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS (contains_adicThickening A I B
          hS) 0))) x)
    obtain ⟨z, -, hzx⟩ := exists_points_of_isPullback B _ hS
      (isPullback_chartOpenPart g v p πb k c π u hsqu hkv 0) t x ht
    refine ⟨pointsMap B _ hS _ (inv (lam 0)) z, ?_⟩
    rw [hcompE 0, ← pointsMap_comp_apply, IsIso.inv_hom_id_assoc, hzx]
  · -- the adic fibres of `E ⟶ V ⟶ Y`
    exact adicFibreMap_chart_comp_eq g v p o πb k c π u i e ho hg hsqu hkv hko he1 E ℓ hℓ n (lam n)
      (hlam n) (hcompE n)

end AlgebraicGeometry.Space

end
