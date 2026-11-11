module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAgreementQuotientLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal

/-!
# The agreement relation of a morphism out of an étale space

Let `π : E ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` and `ψ : E ⟶ Y` a
morphism into an fppf sheaf. Let `K ⊆ E ×_X E` be the largest open subspace on which
`ψ ∘ pr₁ = ψ ∘ pr₂` (`AlgebraicGeometry.Space.agreementOpenSubspace`). Then `K ⟶ E ×_X E` is an
equivalence relation on `E` over `X`:

* it contains the diagonal, which is an open subspace since `π` is unramified;
* it is symmetric, its image under the swap of the factors being an open subspace on which the
  two composites agree;
* it is transitive: the image of `K ×_E K` in `E ×_X E` under `(x, y, z) ↦ (x, z)` is open, the
  map being étale, and the two composites agree on the open subspace it cuts out, since they do
  after the étale surjection from `K ×_E K` and `Y` is a sheaf.

## Main definitions

* `AlgebraicGeometry.Space.etaleAgreementLocus`: the open subspace `K ⊆ E ×_X E`.
* `AlgebraicGeometry.Space.etaleAgreementPreRelation`: `K` as a pre-relation on `E` over `X`.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_etaleAgreementPreRelation`: it is an
  equivalence relation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {E X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_etaleAgreementRelation
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_etaleAgreementRelation
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The largest open subspace `K ⊆ E ×_X E` on which `ψ ∘ pr₁ = ψ ∘ pr₂`. -/
abbrev etaleAgreementLocus (π : E ⟶ X) (ψ : E ⟶ Y) : Subfunctor (pullback π π) :=
  agreementOpenSubspace (pullback.fst π π ≫ ψ) (pullback.snd π π ≫ ψ)

/-- The open subspace `K ⊆ E ×_X E`, as an object over `X`. -/
abbrev etaleAgreementRelationSource (π : E ⟶ X) (ψ : E ⟶ Y) : Over X :=
  Over.mk ((etaleAgreementLocus π ψ).ι ≫ pullback.fst π π ≫ π)

/-- The open subspace `K ⊆ E ×_X E`, as a pre-relation on `E` over `X`. -/
def etaleAgreementPreRelation (π : E ⟶ X) (ψ : E ⟶ Y) :
    PreRelation (etaleAgreementRelationSource π ψ) (Over.mk π) :=
  prod.lift (Over.homMk ((etaleAgreementLocus π ψ).ι ≫ pullback.fst π π) (by simp))
    (Over.homMk ((etaleAgreementLocus π ψ).ι ≫ pullback.snd π π)
      (by simp [pullback.condition]))

/-- The target of the agreement relation is the first projection. -/
@[simp]
theorem etaleAgreementPreRelation_target_left (π : E ⟶ X) (ψ : E ⟶ Y) :
    (etaleAgreementPreRelation π ψ).target.left =
      (etaleAgreementLocus π ψ).ι ≫ pullback.fst π π := by
  simp [etaleAgreementPreRelation, PreRelation.target]

/-- The source of the agreement relation is the second projection. -/
@[simp]
theorem etaleAgreementPreRelation_source_left (π : E ⟶ X) (ψ : E ⟶ Y) :
    (etaleAgreementPreRelation π ψ).source.left =
      (etaleAgreementLocus π ψ).ι ≫ pullback.snd π π := by
  simp [etaleAgreementPreRelation, PreRelation.source]

/-- The square presenting the product of `E` with itself over `X` as the fibre product. -/
theorem isPullback_prod_mk_left (π : E ⟶ X) :
    IsPullback (prod.fst : Over.mk π ⨯ Over.mk π ⟶ Over.mk π).left
      (prod.snd : Over.mk π ⨯ Over.mk π ⟶ Over.mk π).left π π :=
  Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst : Over.mk π ⨯ Over.mk π ⟶ Over.mk π) prod.snd) (prodIsProd _ _)

/-- The agreement relation is the inclusion of `K` followed by the identification of
`E ×_X E` with the product over `X`. -/
theorem etaleAgreementPreRelation_left (π : E ⟶ X) (ψ : E ⟶ Y) :
    (etaleAgreementPreRelation π ψ).left =
      (etaleAgreementLocus π ψ).ι ≫ (isPullback_prod_mk_left π).isoPullback.inv := by
  apply (isPullback_prod_mk_left π).hom_ext
  · have h := etaleAgreementPreRelation_target_left π ψ
    simp only [PreRelation.target, Over.comp_left] at h
    rw [h, Category.assoc, IsPullback.isoPullback_inv_fst]
  · have h := etaleAgreementPreRelation_source_left π ψ
    simp only [PreRelation.source, Over.comp_left] at h
    rw [h, Category.assoc, IsPullback.isoPullback_inv_snd]

/-- The two composites agree on `K`. -/
theorem etaleAgreementLocus_ι_comp_eq (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (π : E ⟶ X) (ψ : E ⟶ Y) :
    (etaleAgreementLocus π ψ).ι ≫ pullback.fst π π ≫ ψ =
      (etaleAgreementLocus π ψ).ι ≫ pullback.snd π π ≫ ψ :=
  agreementOpenSubspace_ι_comp_eq hY _ _

/-- Two test points are related by the agreement relation exactly when their pair factors
through `K`. -/
theorem etaleAgreementPreRelation_rel_iff (π : E ⟶ X) (ψ : E ⟶ Y) {T : BigFppfOver B S hS}
    {b : yoneda.obj T ⟶ X} (x y : TestPoint T b (Over.mk π)) :
    (etaleAgreementPreRelation π ψ).Rel b x y ↔
      Subfunctor.range (pullback.lift (f := π) (g := π) x.1 y.1 (x.2.trans y.2.symm)) ≤
        etaleAgreementLocus π ψ := by
  constructor
  · rintro ⟨r, h₁, h₂⟩
    simp only [etaleAgreementPreRelation_target_left,
      etaleAgreementPreRelation_source_left] at h₁ h₂
    have : pullback.lift (f := π) (g := π) x.1 y.1 (x.2.trans y.2.symm) =
        r.1 ≫ (etaleAgreementLocus π ψ).ι := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, h₁]
      · rw [pullback.lift_snd, Category.assoc, h₂]
    rw [this]
    exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le
  · intro h
    refine ⟨⟨Subfunctor.lift _ h, ?_⟩, ?_, ?_⟩
    · change Subfunctor.lift _ h ≫ (etaleAgreementLocus π ψ).ι ≫ pullback.fst π π ≫ π = b
      rw [Subfunctor.lift_ι_assoc, pullback.lift_fst_assoc]
      exact x.2
    · rw [etaleAgreementPreRelation_target_left]
      exact (Subfunctor.lift_ι_assoc _ h _).trans (pullback.lift_fst _ _ _)
    · rw [etaleAgreementPreRelation_source_left]
      exact (Subfunctor.lift_ι_assoc _ h _).trans (pullback.lift_snd _ _ _)

/-- **The diagonal lies in the agreement locus**: the diagonal of the étale `π` is an open
immersion and the two composites agree on its image. -/
theorem range_diagonal_le_etaleAgreementLocus (hE : IsAlgebraicSpace B S hS E)
    (hX : IsAlgebraicSpace B S hS X) {π : E ⟶ X} (hπ : IsEtale B S hS π) (ψ : E ⟶ Y) :
    Subfunctor.range (pullback.diagonal π) ≤ etaleAgreementLocus π ψ := by
  have hP : IsAlgebraicSpace B S hS (pullback π π) := isAlgebraicSpace_pullback B S hS π π hE hE hX
  have hd : IsOpenImmersion B S hS (pullback.diagonal π) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS hE hX π (isUnramified_of_isEtale B S hS hπ)
  refine le_agreementOpenSubspace hP (isOpenSubspace_subfunctorRange B S hS hE hd) ?_
  rw [← cancel_epi (Subfunctor.toRange (pullback.diagonal π))]
  simp

/-- **The agreement locus is symmetric.** -/
theorem range_lift_swap_le_etaleAgreementLocus (hE : IsAlgebraicSpace B S hS E)
    (hX : IsAlgebraicSpace B S hS X) (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (π : E ⟶ X) (ψ : E ⟶ Y) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a b : T ⟶ E}
    (h : a ≫ π = b ≫ π)
    (hab : Subfunctor.range (pullback.lift a b h) ≤ etaleAgreementLocus π ψ) :
    Subfunctor.range (pullback.lift b a h.symm) ≤ etaleAgreementLocus π ψ := by
  set K := etaleAgreementLocus π ψ
  have hP : IsAlgebraicSpace B S hS (pullback π π) := isAlgebraicSpace_pullback B S hS π π hE hE hX
  let σ : pullback π π ⟶ pullback π π :=
    pullback.lift (pullback.snd π π) (pullback.fst π π) pullback.condition.symm
  have hσ₁ : σ ≫ pullback.fst π π = pullback.snd π π := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pullback.snd π π = pullback.fst π π := pullback.lift_snd _ _ _
  have hK := isOpenSubspace_agreementOpenSubspace hP (pullback.fst π π ≫ ψ) (pullback.snd π π ≫ ψ)
  have hagree := etaleAgreementLocus_ι_comp_eq hY π ψ
  have hV : K.preimage σ ≤ K := by
    refine le_agreementOpenSubspace hP (isOpenSubspace_preimage B S hS σ K hP hP hK) ?_
    calc (K.preimage σ).ι ≫ pullback.fst π π ≫ ψ
        = K.fromPreimage σ ≫ K.ι ≫ pullback.snd π π ≫ ψ := by
          rw [Subfunctor.fromPreimage_ι_assoc, reassoc_of% hσ₂]
      _ = K.fromPreimage σ ≫ K.ι ≫ pullback.fst π π ≫ ψ := by rw [hagree]
      _ = (K.preimage σ).ι ≫ pullback.snd π π ≫ ψ := by
          rw [Subfunctor.fromPreimage_ι_assoc, reassoc_of% hσ₁]
  refine le_trans ?_ hV
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp]
  have : pullback.lift b a h.symm ≫ σ = pullback.lift a b h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσ₁, pullback.lift_snd, pullback.lift_fst]
    · rw [Category.assoc, hσ₂, pullback.lift_fst, pullback.lift_snd]
  rw [this]
  exact hab

/-- **The agreement locus is transitive.** -/
theorem range_lift_trans_le_etaleAgreementLocus (hE : IsAlgebraicSpace B S hS E)
    (hX : IsAlgebraicSpace B S hS X) (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {π : E ⟶ X} (hπ : IsEtale B S hS π) (ψ : E ⟶ Y) {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b c : T ⟶ E} (hab : a ≫ π = b ≫ π) (hbc : b ≫ π = c ≫ π)
    (h₁ : Subfunctor.range (pullback.lift a b hab) ≤ etaleAgreementLocus π ψ)
    (h₂ : Subfunctor.range (pullback.lift b c hbc) ≤ etaleAgreementLocus π ψ) :
    Subfunctor.range (pullback.lift a c (hab.trans hbc)) ≤ etaleAgreementLocus π ψ := by
  set K := etaleAgreementLocus π ψ
  have hP : IsAlgebraicSpace B S hS (pullback π π) := isAlgebraicSpace_pullback B S hS π π hE hE hX
  have hK := isOpenSubspace_agreementOpenSubspace hP (pullback.fst π π ≫ ψ) (pullback.snd π π ≫ ψ)
  have hagree := etaleAgreementLocus_ι_comp_eq hY π ψ
  have hp₁ : IsEtale B S hS (pullback.fst π π) := isEtale_pullback_fst B S hS hE hX hE π π hπ
  have hp₂ : IsEtale B S hS (pullback.snd π π) := isEtale_pullback_snd B S hS hE hX hE π π hπ
  have hι : IsEtale B S hS K.ι := isEtale_of_isOpenImmersion B S hS hK.2
  have hK₁ : IsEtale B S hS (K.ι ≫ pullback.fst π π) := isEtale_comp B S hS hι hp₁
  -- The space of composable pairs `K ×_E K` and the composition map to `E ×_X E`.
  let Q := pullback (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π)
  have hQ : IsAlgebraicSpace B S hS Q := isAlgebraicSpace_pullback B S hS _ _ hK.1 hK.1 hE
  have e : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : W ⟶ K.toFunctor),
      k ≫ K.ι ≫ pullback.fst π π ≫ π = k ≫ K.ι ≫ pullback.snd π π ≫ π :=
    fun k => by rw [pullback.condition]
  have hw : (pullback.fst (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
      pullback.fst π π) ≫ π = (pullback.snd (K.ι ≫ pullback.snd π π)
        (K.ι ≫ pullback.fst π π) ≫ K.ι ≫ pullback.snd π π) ≫ π := by
    calc _ = pullback.fst (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
          pullback.fst π π ≫ π := by simp only [Category.assoc]
      _ = pullback.fst (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
          pullback.snd π π ≫ π := e _
      _ = pullback.snd (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
          pullback.fst π π ≫ π := by
        rw [← Category.assoc K.ι, pullback.condition_assoc, Category.assoc]
      _ = pullback.snd (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
          pullback.snd π π ≫ π := e _
      _ = _ := by simp only [Category.assoc]
  let m : Q ⟶ pullback π π := pullback.lift _ _ hw
  have hm₁ : m ≫ pullback.fst π π =
      pullback.fst (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
        pullback.fst π π := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd π π =
      pullback.snd (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
        pullback.snd π π := pullback.lift_snd _ _ _
  have hm : IsEtale B S hS m :=
    isEtale_of_isEtale_over B S hS hQ hP hE m _ (pullback.fst π π)
      (isEtale_comp B S hS (isEtale_pullback_fst B S hS hK.1 hE hK.1 _ _ hK₁) hK₁) hp₁ hm₁
  -- The open subspace `V ⊆ E ×_X E` cut out by the image of `m`.
  set V := openSubspaceOfPoints B S hS (pullback π π) (Set.range (pointsMap B S hS Q m))
  have hVo : IsOpenSubspace B S hS V := by
    refine isOpenSubspace_openSubspaceOfPoints B S hS hP _ ?_
    rw [← Set.image_univ]
    exact isOpenMap_pointsMap_of_isEtale B S hS m hQ hP hm _ isOpen_univ
  have hmV : Subfunctor.range m ≤ V := by
    rw [← Subfunctor.preimage_eq_top_iff, preimage_openSubspaceOfPoints', Set.preimage_range]
    ext T x
    simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
    exact Set.subset_univ _
  let m' : Q ⟶ V.toFunctor := Subfunctor.lift m hmV
  have hm' : IsEtale B S hS m' :=
    isEtale_of_isEtale_over B S hS hQ hVo.1 hP m' m V.ι hm
      (isEtale_of_isOpenImmersion B S hS hVo.2) (Subfunctor.lift_ι _ _)
  have hm's : IsSurjective B S hS m' := by
    intro v
    have hv : pointsMap B S hS V.toFunctor V.ι v ∈ Set.range (pointsMap B S hS Q m) := by
      rw [← range_pointsMap_ι_openSubspaceOfPoints B S hS (Set.range (pointsMap B S hS Q m))]
      exact ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hv
    refine ⟨w, pointsMap_injective_of_mono B S hS V.ι ?_⟩
    rw [← hw, ← Function.comp_apply (f := pointsMap B S hS V.toFunctor V.ι), ← pointsMap_comp,
      Subfunctor.lift_ι]
  -- The two composites agree on `V`, hence `V ⊆ K`.
  have hVK : V ≤ K := by
    refine le_agreementOpenSubspace hP hVo ?_
    let Qs : AlgebraicSpaces B S hS := ⟨Q, hQ⟩
    let Vs : AlgebraicSpaces B S hS := ⟨V.toFunctor, hVo.1⟩
    have hcov := isFppfCovering_singleton.{u, 0} B S hS (ObjectProperty.homMk m' : Qs ⟶ Vs) hm's
      (isFlat_of_isEtale B S hS hm') (isLocallyOfFinitePresentation_of_isEtale B S hS hm')
    refine hom_ext_of_isFppfCovering B S hS (fun _ => Q) (fun _ => m') hcov hY fun _ => ?_
    have hm'ι : m' ≫ V.ι = m := Subfunctor.lift_ι _ _
    change m' ≫ V.ι ≫ pullback.fst π π ≫ ψ = m' ≫ V.ι ≫ pullback.snd π π ≫ ψ
    have hc : pullback.fst (K.ι ≫ pullback.snd π π) (K.ι ≫ pullback.fst π π) ≫ K.ι ≫
        pullback.snd π π ≫ ψ = pullback.snd (K.ι ≫ pullback.snd π π)
          (K.ι ≫ pullback.fst π π) ≫ K.ι ≫ pullback.fst π π ≫ ψ := by
      rw [← Category.assoc K.ι, pullback.condition_assoc, Category.assoc]
    rw [reassoc_of% hm'ι, reassoc_of% hm'ι, reassoc_of% hm₁, reassoc_of% hm₂, hagree, hc,
      hagree]
  -- Conclusion.
  set kab := Subfunctor.lift _ h₁
  set kbc := Subfunctor.lift _ h₂
  have hab' : kab ≫ K.ι = pullback.lift a b hab := Subfunctor.lift_ι _ _
  have hbc' : kbc ≫ K.ι = pullback.lift b c hbc := Subfunctor.lift_ι _ _
  have hk : kab ≫ K.ι ≫ pullback.snd π π = kbc ≫ K.ι ≫ pullback.fst π π := by
    rw [reassoc_of% hab', reassoc_of% hbc']
    exact (pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm
  have : pullback.lift a c (hab.trans hbc) = pullback.lift kab kbc hk ≫ m := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm₁, pullback.lift_fst_assoc, reassoc_of% hab']
      exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hm₂, pullback.lift_snd_assoc, reassoc_of% hbc']
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  rw [this]
  exact ((Subfunctor.range_comp_le _ _).trans hmV).trans hVK

/-- **The agreement relation is an equivalence relation.** Let `π : E ⟶ X` be an étale
morphism of algebraic spaces and `ψ : E ⟶ Y` a morphism into an fppf sheaf. The largest open
subspace `K ⊆ E ×_X E` on which `ψ ∘ pr₁ = ψ ∘ pr₂` is an equivalence relation on `E` over
`X`. -/
theorem isEquivalenceRelation_etaleAgreementPreRelation (hE : IsAlgebraicSpace B S hS E)
    (hX : IsAlgebraicSpace B S hS X) (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {π : E ⟶ X} (hπ : IsEtale B S hS π) (ψ : E ⟶ Y) :
    CategoryTheory.IsEquivalenceRelation (etaleAgreementPreRelation π ψ).target
      (etaleAgreementPreRelation π ψ).source := by
  rw [isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation]
  refine ⟨⟨fun {W} f g hfg => ?_⟩, fun T b => ⟨fun x => ?_, fun {x y} hxy => ?_,
    fun {x y z} hxy hyz => ?_⟩⟩
  · have h₁ := congrArg
      (fun k => (k ≫ (prod.fst : Over.mk π ⨯ Over.mk π ⟶ Over.mk π)).left) hfg
    have h₂ := congrArg
      (fun k => (k ≫ (prod.snd : Over.mk π ⨯ Over.mk π ⟶ Over.mk π)).left) hfg
    simp only [Category.assoc, Over.comp_left] at h₁ h₂
    have h₁' := etaleAgreementPreRelation_target_left π ψ
    have h₂' := etaleAgreementPreRelation_source_left π ψ
    simp only [PreRelation.target, PreRelation.source, Over.comp_left] at h₁' h₂'
    rw [h₁'] at h₁
    rw [h₂'] at h₂
    ext : 1
    rw [← cancel_mono (etaleAgreementLocus π ψ).ι]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h₁
    · simpa only [Category.assoc] using h₂
  · rw [etaleAgreementPreRelation_rel_iff]
    have : pullback.lift (f := π) (g := π) x.1 x.1 (x.2.trans x.2.symm) =
        x.1 ≫ pullback.diagonal π := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans (by simp)
      · exact (pullback.lift_snd _ _ _).trans (by simp)
    rw [this]
    exact (Subfunctor.range_comp_le _ _).trans (range_diagonal_le_etaleAgreementLocus hE hX hπ ψ)
  · rw [etaleAgreementPreRelation_rel_iff] at hxy ⊢
    exact range_lift_swap_le_etaleAgreementLocus hE hX hY π ψ _ hxy
  · rw [etaleAgreementPreRelation_rel_iff] at hxy hyz ⊢
    exact range_lift_trans_le_etaleAgreementLocus hE hX hY hπ ψ _ _ hxy hyz

end AlgebraicGeometry.Space

end
