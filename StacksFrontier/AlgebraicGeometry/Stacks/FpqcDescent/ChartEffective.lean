module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.ChartGroupoid
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.SubobjectFlatDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentSizeBound
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# A descent datum becomes effective after a smooth surjective base change

Let `𝒳` be an algebraic stack over `S` with quasi-affine diagonal, let `D` be a descent datum
of `𝒳` relative to a sieve `R` of `U`, and let `f : W ⟶ U` be an arrow of `R` which is an fpqc
covering. This file proves that there are a smooth surjective `w₀ : W₀ ⟶ U` and an object of `𝒳`
over `W₀` to which the pullback of `D` along `w₀` descends. This is the geometric step of the
proof of Stacks 0GRH.

The object `W₀` is the descent along `T = W × P ⟶ U × P` of the chart `Q` of the object of `D`
at `f` against a smooth presentation `g : 𝒮/P ⥤ 𝒳`: `Q` is quasi-affine over `T`, so it descends
by Stacks 0247 (`AlgebraicGeometry.Stack.ChartAction.exists_descended_chart`). Then
`Q = W ×_U W₀`, so `W₀ ⟶ U` is smooth and surjective because `Q ⟶ W` is. The object over `W₀` is
the restriction of `g`, and the tautological morphism of the chart descends the datum along the
fpqc covering `Q ⟶ W₀`, by
`CategoryTheory.Functor.SieveDescentDatum.isEffective_pullback_of_singleArrow_slice`.

## Main results

* `AlgebraicGeometry.Stack.exists_smooth_surjective_isEffective_pullback`.

## References

* [Stacks Project, Tag 0GRH](https://stacks.math.columbia.edu/tag/0GRH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

/-- A diagram chase: the compatibility of the tautological morphism of the chart. -/
lemma chart_compat_aux {𝒞 : Type*} [Category 𝒞] {A₁ A₂ X₀ G₀ G₁ G₂ Yt : 𝒞}
    (ih : A₁ ⟶ A₂) (ii : A₂ ⟶ A₁) (hii : ih ≫ ii = 𝟙 A₁) (P₁ : A₁ ⟶ X₀) (P₂ : A₂ ⟶ X₀)
    (s : X₀ ⟶ G₀) (ρ : G₀ ⟶ Yt) (r₁ : A₁ ⟶ G₁) (r₂ : A₂ ⟶ G₂) (Y₁ : G₁ ⟶ G₀) (Y₂ : G₂ ⟶ G₀)
    (E : G₁ ⟶ G₂) (fac₁ : r₁ ≫ Y₁ = P₁ ≫ s) (fac₂ : r₂ ≫ Y₂ = P₂ ≫ s) (tw : r₂ = ii ≫ r₁ ≫ E)
    (hO : E ≫ Y₂ ≫ ρ = Y₁ ≫ ρ) : ih ≫ P₂ ≫ s ≫ ρ = P₁ ≫ s ≫ ρ := by
  rw [← Category.assoc P₂, ← fac₂, tw]
  simp only [Category.assoc]
  rw [← Category.assoc ih, hii, Category.id_comp, hO, ← Category.assoc, fac₁, Category.assoc]

/-- **Stacks 0GRH, the geometric step.** For an algebraic stack `𝒳` with quasi-affine diagonal, a
descent datum `D` relative to a sieve `R` of `U`, a morphism `u : V ⟶ U` and a surjective, flat,
quasi-compact `f : W ⟶ V` with `f ≫ u` an arrow of `R`, there is a smooth surjective
`w₀ : W₀ ⟶ V` along whose composite with `u` the datum `D` becomes effective. -/
theorem exists_smooth_surjective_isEffective_pullback
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) [𝒳.val.p.IsFibered]
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳))
    {U V W : BigFppfOver B S hS} {R : Sieve U} (D : SieveDescentDatum 𝒳.val.p R)
    (u : V ⟶ U) {f : W ⟶ V} (hf : R.arrows (f ≫ u))
    [Surjective ((BigFppfOver.toScheme B S hS).map f)]
    [Flat ((BigFppfOver.toScheme B S hS).map f)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map f)] :
    ∃ (W₀ : BigFppfOver B S hS) (w₀ : W₀ ⟶ V),
      Smooth ((BigFppfOver.toScheme B S hS).map w₀) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map w₀) ∧ (D.pullback (w₀ ≫ u)).IsEffective := by
  set F := BigFppfOver.toScheme B S hS with hF
  have hp := 𝒳.isFiberedInGroupoids
  obtain ⟨P, g, hg, hpres⟩ := exists_slicePresentation 𝒳 h𝒳
  -- the products `T = W × P` and `Y = U × P`
  obtain ⟨T, pr₁, pr₂, ⟨hT⟩⟩ : ∃ (T : BigFppfOver B S hS) (pr₁ : T ⟶ W) (pr₂ : T ⟶ P),
      Nonempty (IsLimit (BinaryFan.mk pr₁ pr₂)) := ⟨_, _, _, ⟨prodIsProd W P⟩⟩
  obtain ⟨Y, q₁, q₂, ⟨hY⟩⟩ : ∃ (Y : BigFppfOver B S hS) (q₁ : Y ⟶ V) (q₂ : Y ⟶ P),
      Nonempty (IsLimit (BinaryFan.mk q₁ q₂)) := ⟨_, _, _, ⟨prodIsProd V P⟩⟩
  obtain ⟨g', hg₁, hg₂⟩ : ∃ g' : T ⟶ Y, g' ≫ q₁ = pr₁ ≫ f ∧ g' ≫ q₂ = pr₂ :=
    ⟨_, (BinaryFan.IsLimit.lift' hY (pr₁ ≫ f) pr₂).2⟩
  have hg₁' : g' ≫ q₁ ≫ u = pr₁ ≫ f ≫ u := by rw [← Category.assoc, hg₁, Category.assoc]
  -- the chart
  obtain ⟨hA, hsurj, hsmooth⟩ := hpres W (pullbackSliceFunctor 𝒳.val.p (D.obj (f ≫ u) hf))
    (pullbackSliceFunctor_comp 𝒳.val.p (D.obj (f ≫ u) hf))
  obtain ⟨Q, π, e, he, hqa, hsm, hsu⟩ := exists_chart 𝒳 hg
    (pullbackSliceFunctor_comp 𝒳.val.p (D.obj (f ≫ u) hf)) h𝒳 hΔ hT hA hsurj hsmooth
  -- `T = W ×_U Y`
  have hTpb : IsPullback pr₁ g' f q₁ := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk pr₁ g' hg₁.symm)
      (PullbackCone.IsLimit.mk _ (fun s => (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).1)
        (fun s => (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).2.1) (fun s => ?_)
        (fun s m h₁ h₂ => ?_))
    · obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l = (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).1 ∧
          l ≫ pr₁ = s.fst ∧ l ≫ pr₂ = s.snd ≫ q₂ :=
        ⟨_, rfl, (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).2.1,
          (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).2.2⟩
      rw [← hl₁]
      obtain ⟨hl₁, hl₂⟩ := hl₂
      refine BinaryFan.IsLimit.hom_ext hY ?_ ?_
      · simp only [BinaryFan.mk_fst, Category.assoc, hg₁]
        rw [← Category.assoc, hl₁, s.condition]
      · simp only [BinaryFan.mk_snd, Category.assoc, hg₂]
        exact hl₂
    · obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l = (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).1 ∧
          l ≫ pr₁ = s.fst ∧ l ≫ pr₂ = s.snd ≫ q₂ :=
        ⟨_, rfl, (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).2.1,
          (BinaryFan.IsLimit.lift' hT s.fst (s.snd ≫ q₂)).2.2⟩
      rw [← hl₁]
      obtain ⟨hl₁, hl₂⟩ := hl₂
      refine BinaryFan.IsLimit.hom_ext hT ?_ ?_
      · simp only [BinaryFan.mk_fst]
        exact h₁.trans hl₁.symm
      · simp only [BinaryFan.mk_snd]
        rw [hl₂, ← h₂, Category.assoc, hg₂]
  have hTpbF := hTpb.map F
  have : Surjective (F.map g') :=
    MorphismProperty.of_isPullback (P := @Surjective) hTpbF ‹_›
  have : Flat (F.map g') := MorphismProperty.of_isPullback (P := @Flat) hTpbF ‹_›
  have : QuasiCompact (F.map g') := MorphismProperty.of_isPullback (P := @QuasiCompact) hTpbF ‹_›
  -- the descent of the chart
  obtain ⟨W₀, i, k, hpb, hinv⟩ :=
    ChartAction.exists_descended_chart 𝒳 D hf hg pr₁ pr₂ hg₁' hg₂ e he hqa
  have : Surjective k := MorphismProperty.of_isPullback (P := @Surjective) hpb ‹_›
  have : Flat k := MorphismProperty.of_isPullback (P := @Flat) hpb ‹_›
  have : QuasiCompact k := MorphismProperty.of_isPullback (P := @QuasiCompact) hpb ‹_›
  -- the descended scheme as an object of the site, over `U × P`
  have hW : B.Contains W₀ := BigFppfSite.contains_of_flat_surjective B k Q.left.property
  let i' : B.obj hW ⟶ Y.left := B.inclusion.preimage i
  have hi' : B.inclusion.map i' = i :=
    B.inclusion.map_preimage (X := B.obj hW) (Y := Y.left) i
  let W₀' : BigFppfOver B S hS := Over.mk (i' ≫ Y.hom)
  let w₀' : W₀' ⟶ Y := Over.homMk i'
  have hw₀' : F.map w₀' = i := hi'
  obtain ⟨pr, hpr⟩ : ∃ pr : Q ⟶ W₀', F.map pr = k := by
    refine ⟨Over.homMk (ObjectProperty.homMk k) ?_, rfl⟩
    apply ObjectProperty.hom_ext
    show k ≫ B.inclusion.map (i' ≫ Y.hom) = B.inclusion.map Q.hom
    rw [Functor.map_comp, hi', ← Category.assoc, ← hpb.w, Category.assoc]
    show B.inclusion.map π.left ≫ B.inclusion.map g'.left ≫ B.inclusion.map Y.hom =
      B.inclusion.map Q.hom
    rw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w g', Over.w π]
  have hprw : pr ≫ w₀' = π ≫ g' :=
    F.map_injective (by rw [F.map_comp, hpr, hw₀', F.map_comp]; exact hpb.w.symm)
  -- `Q = W ×_U W₀`, so `W₀ ⟶ U` is smooth and surjective
  have hQW := hpb.flip.paste_vert hTpbF.flip
  have hFw₀ : F.map (w₀' ≫ q₁) = i ≫ F.map q₁ := by rw [F.map_comp, hw₀']
  have hfpqc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (F.map f) :=
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  have hsm' : Smooth (F.map (w₀' ≫ q₁)) := by
    rw [hFw₀]
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) hQW.flip hfpqc
      (by rw [← F.map_comp]; exact hsm)
  have hsu' : Surjective (F.map (w₀' ≫ q₁)) := by
    rw [hFw₀]
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hQW.flip hfpqc
      (by rw [← F.map_comp]; exact hsu)
  -- the descent along the fpqc covering `Q ⟶ W₀`
  have hmor := fun V (x y : 𝒳.val.p.Fiber V) =>
    isMorSheaf_fpqc_of_isAlgebraicStack B S hS 𝒳 h𝒳 V x y
  have he' : Sieve.generate (Presieve.singleton pr) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck W₀' := by
    refine Precoverage.generate_mem_toGrothendieck
      (Space.singleton_mem_fpqcPrecoverage_comap pr ?_ ?_ ?_) <;> rw [← hF, hpr] <;> infer_instance
  set s₀ := e.hom.app (op Q) (𝟙 Q) with hs₀def
  have hs₀ : s₀.1 = 𝟙 Q ≫ π := ChartAction.fst_hom_app 𝒳 D hf hg pr₁ pr₂ e he (𝟙 Q)
  have hb : pr ≫ w₀' ≫ q₁ = (s₀.1 ≫ pr₁) ≫ f := by
    rw [hs₀, Category.id_comp, ← Category.assoc, hprw, Category.assoc, hg₁, Category.assoc]
  have hpr₂ : pr ≫ w₀' ≫ q₂ = s₀.1 ≫ pr₂ := by
    rw [hs₀, Category.id_comp, ← Category.assoc, hprw, Category.assoc, hg₂]
  let y : 𝒳.val.p.Fiber W₀' := ⟨g.obj (Over.mk (w₀' ≫ q₂)), Functor.congr_obj hg _⟩
  let prH : (Over.map pr₂).obj (Over.mk s₀.1) ⟶ Over.mk (w₀' ≫ q₂) := Over.homMk pr hpr₂
  let ζ₁ : (pullbackFiber 𝒳.val.p (D.obj (f ≫ u) hf) (s₀.1 ≫ pr₁)).1 ⟶ y.1 := s₀.2.1 ≫ g.map prH
  have hζ₁ : 𝒳.val.p.IsHomLift pr ζ₁ := by
    have : 𝒳.val.p.IsHomLift (𝟙 Q) s₀.2.1 := s₀.2.2
    have : 𝒳.val.p.IsHomLift pr (g.map prH) := VertHom.isHomLift_map hg prH
    have : 𝒳.val.p.IsHomLift (𝟙 Q ≫ pr) (s₀.2.1 ≫ g.map prH) := inferInstance
    rw [Category.id_comp] at this
    exact this
  have hb' : pr ≫ (w₀' ≫ q₁) ≫ u = (s₀.1 ≫ pr₁) ≫ f ≫ u := by
    rw [← Category.assoc pr, hb, Category.assoc]
  refine ⟨W₀', w₀' ≫ q₁, hsm', hsu', D.isEffective_pullback_of_singleArrow_slice hp hmor
    ((w₀' ≫ q₁) ≫ u) pr he' hf (s₀.1 ≫ pr₁) hb' y ζ₁ hζ₁ ?_⟩
  intro Z k₁ k₂ hk a₁ a₂ ha₁ ha₂
  obtain rfl : a₁ = (k₁ ≫ s₀.1) ≫ pr₁ := ha₁.symm.trans (Category.assoc _ _ _).symm
  obtain rfl : a₂ = (k₂ ≫ s₀.1) ≫ pr₁ := ha₂.symm.trans (Category.assoc _ _ _).symm
  -- the action relates the two points
  have hcond : k₁ ≫ π ≫ g' = (k₂ ≫ s₀.1) ≫ g' := by
    rw [hs₀, Category.id_comp, Category.assoc, ← hprw, ← Category.assoc, ← Category.assoc, hk]
  set a := ChartAction.actY 𝒳 D hf hg pr₁ pr₂ hg₁' hg₂ e he k₁ (k₂ ≫ s₀.1) hcond with hadef
  have haπ' : a ≫ π = k₂ ≫ s₀.1 :=
    ChartAction.actY_comp_π 𝒳 D hf hg pr₁ pr₂ hg₁' hg₂ e he k₁ (k₂ ≫ s₀.1) hcond
  have haπ : a ≫ π = k₂ ≫ π := by rw [haπ', hs₀, Category.id_comp]
  have hak : F.map k₁ ≫ k = F.map a ≫ k :=
    hinv k₁ a (by rw [haπ']; exact hcond)
      (ChartAction.actY_congr 𝒳 D hf hg pr₁ pr₂ hg₁' hg₂ e he rfl haπ' _ _)
  have hak₂ : a = k₂ := F.map_injective (hpb.hom_ext
    (by rw [← F.map_comp, ← F.map_comp, haπ])
    (hak.symm.trans (by rw [← hpr, ← F.map_comp, ← F.map_comp, hk])))
  have hsec : ∀ kk : Z ⟶ Q, e.hom.app (op Z) kk =
      ⟨kk ≫ s₀.1, VertHom.restrict 𝒳.isFiberedInGroupoids
        (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj (f ≫ u) hf)) pr₁)
        (overMap_comp_eq_forget 𝒳 hg pr₂)
        (Over.homMk kk rfl : Over.mk (kk ≫ s₀.1) ⟶ Over.mk s₀.1) s₀.2⟩ := by
    intro kk
    have h1 := NatTrans.naturality_apply e.hom kk.op (𝟙 Q)
    have h2 : (yoneda.obj Q).map kk.op (𝟙 Q) = kk := by simp
    rw [h2] at h1
    exact h1
  have hcond' : (k₁ ≫ s₀.1) ≫ g' = (k₂ ≫ s₀.1) ≫ g' :=
    calc (k₁ ≫ s₀.1) ≫ g' = k₁ ≫ π ≫ g' := by rw [hs₀, Category.id_comp, Category.assoc]
      _ = _ := hcond
  have hpair := ChartAction.comp_g'_eq_imp pr₁ pr₂ hg₁' hg₂ _ _ hcond'
  have h3 : e.hom.app (op Z) a = ChartAction.moveSection 𝒳 D hf hg pr₁ pr₂ (e.hom.app (op Z) k₁)
      (k₂ ≫ s₀.1) _ _ := ChartAction.hom_app_act 𝒳 D hf hg pr₁ pr₂ e he k₁ (k₂ ≫ s₀.1) _ _
  rw [hak₂, hsec k₂] at h3
  have h4 := h3.trans (ChartAction.moveSection_congr 𝒳 D hf hg pr₁ pr₂ (hsec k₁) (k₂ ≫ s₀.1) _ _
    hpair.1 hpair.2)
  have htw := eq_of_heq (Sigma.mk.inj_iff.mp h4).2
  have fac₁ := VertHom.restrict_fac 𝒳.isFiberedInGroupoids
    (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj (f ≫ u) hf)) pr₁)
    (overMap_comp_eq_forget 𝒳 hg pr₂) (Over.homMk k₁ rfl : Over.mk (k₁ ≫ s₀.1) ⟶ Over.mk s₀.1) s₀.2
  have fac₂ := VertHom.restrict_fac 𝒳.isFiberedInGroupoids
    (overMap_comp_eq_forget 𝒳 (pullbackSliceFunctor_comp 𝒳.val.p (D.obj (f ≫ u) hf)) pr₁)
    (overMap_comp_eq_forget 𝒳 hg pr₂) (Over.homMk k₂ rfl : Over.mk (k₂ ≫ s₀.1) ⟶ Over.mk s₀.1) s₀.2
  have hO : g.map (eqToHom (show (Over.map pr₂).obj (Over.mk (k₁ ≫ s₀.1)) =
        (Over.map pr₂).obj (Over.mk (k₂ ≫ s₀.1)) from congrArg Over.mk hpair.2)) ≫
      (Over.map pr₂ ⋙ g).map (Over.homMk k₂ rfl : Over.mk (k₂ ≫ s₀.1) ⟶ Over.mk s₀.1) ≫
        g.map prH =
      (Over.map pr₂ ⋙ g).map (Over.homMk k₁ rfl : Over.mk (k₁ ≫ s₀.1) ⟶ Over.mk s₀.1) ≫
        g.map prH := by
    refine (congrArg (g.map _ ≫ ·) (g.map_comp _ _).symm).trans
      ((g.map_comp _ _).symm.trans ((congrArg g.map ?_).trans (g.map_comp _ _)))
    refine Over.OverMorphism.ext ?_
    simp [prH, hk]
  have hii : Fiber.fiberInclusion.map (D.iso hf hf ((k₁ ≫ s₀.1) ≫ pr₁) ((k₂ ≫ s₀.1) ≫ pr₁)
      (by simpa only [Category.assoc] using hpair.1)).hom ≫
      Fiber.fiberInclusion.map (D.iso hf hf ((k₁ ≫ s₀.1) ≫ pr₁) ((k₂ ≫ s₀.1) ≫ pr₁)
        (by simpa only [Category.assoc] using hpair.1)).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  exact chart_compat_aux _ _ hii _ _ s₀.2.1 (g.map prH) _ _ _ _ _ fac₁ fac₂
    (congrArg Subtype.val htw) hO

end AlgebraicGeometry.Stack

end
