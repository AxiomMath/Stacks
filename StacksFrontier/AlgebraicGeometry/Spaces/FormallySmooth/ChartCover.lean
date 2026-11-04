module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtCompactSet
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleChartFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# A section over an affine object presented by one affine chart on an étale cover

Let `X` be an algebraic space over `S` and `g : h_T ⟶ X` a section of `X` over an object `T` of
the big fppf site whose underlying scheme is affine. This file produces an affine object `Z` with
an étale morphism `c : h_Z ⟶ X`, and an affine object `W` with a surjective étale morphism
`π : W ⟶ T` along which `g` factors through `c`
(`AlgebraicGeometry.Space.exists_affine_chart_cover`).

The chart and the cover are both finite disjoint unions of affine opens: the fibre product
`P = U ×_X T` of an atlas `U ⟶ X` with `g` is covered by affine opens mapping into affine opens
of `U`; their images in `T` are open because `P ⟶ T` is étale, so finitely many of them cover the
quasi-compact scheme `T`, and the disjoint unions of those finitely many affine opens of `P` and
of `U` are the cover `W` and the chart `Z`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_chart_cover`.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms out of a coproduct of the site agreeing on the summands agree. -/
theorem coproduct_hom_ext {σ : Type u} {T' : σ → BigFppfOver B S hS} {T : BigFppfOver B S hS}
    {c : ∀ a, T' a ⟶ T}
    {e : (∐ fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) ≅
      (BigFppfOver.toScheme B S hS).obj T}
    (hce : ∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c a))
    {M : BigFppfOver B S hS} {d d' : T ⟶ M} (h : ∀ a, c a ≫ d = c a ≫ d') : d = d' := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [← cancel_epi e.hom]
  refine Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, hce, ← Functor.map_comp, ← Category.assoc, hce, ← Functor.map_comp, h a]

/-- A morphism out of a coproduct of the site, étale on each summand, is étale. -/
private theorem etale_of_coproduct_desc {σ : Type u} {T' : σ → BigFppfOver B S hS}
    {T M : BigFppfOver B S hS} {c : ∀ a, T' a ⟶ T}
    {e : (∐ fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) ≅
      (BigFppfOver.toScheme B S hS).obj T}
    (hce : ∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c a))
    {d : T ⟶ M} (κ : ∀ a, T' a ⟶ M) (hd : ∀ a, c a ≫ d = κ a)
    (hκ : ∀ a, AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (κ a))) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map d) := by
  have : HasRingHomProperty @Etale RingHom.Etale := inferInstance
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  have hmap : (BigFppfOver.toScheme B S hS).map d =
      e.inv ≫ Sigma.desc fun a => (BigFppfOver.toScheme B S hS).map (κ a) := by
    rw [Iso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [← Category.assoc, hce a, ← Functor.map_comp, hd a, Sigma.ι_desc]
  rw [hmap]
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Etale) _ _
    (inferInstance : AlgebraicGeometry.Etale _) (IsZariskiLocalAtSource.sigmaDesc hκ)

/-- **A section over an affine object factors through one affine étale chart on a surjective
étale affine cover.** -/
theorem exists_affine_chart_cover {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (g : yoneda.obj T ⟶ X) :
    ∃ (Z W : BigFppfOver B S hS) (c : yoneda.obj Z ⟶ X) (m : W ⟶ Z) (π : W ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map π) ∧
      yoneda.map m ≫ c = yoneda.map π ≫ g := by
  classical
  obtain ⟨U, f, hfS, hfE⟩ := hX.exists_atlas
  set P : BigFppfOver B S hS := hfE.rep.pullback g with hPdef
  set a : P ⟶ U := hfE.rep.fst' g with hadef
  set b : P ⟶ T := hfE.rep.snd g with hbdef
  have hsq : yoneda.map a ≫ f = yoneda.map b ≫ g := (hfE.rep.isPullback' g).w
  have hbs : Surjective ((BigFppfOver.toScheme B S hS).map b) :=
    hfS.property g (hfE.rep.fst g) (hfE.rep.snd g) (hfE.rep.isPullback g)
  have hbe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map b) :=
    hfE.property g (hfE.rep.fst g) (hfE.rep.snd g) (hfE.rep.isPullback g)
  set α := (BigFppfOver.toScheme B S hS).map a with hαdef
  -- through every point of `P` an affine open of `P` mapping into an affine open of `U`
  have hchoice : ∀ x : (BigFppfOver.toScheme B S hS).obj P,
      ∃ (A : ((BigFppfOver.toScheme B S hS).obj U).Opens)
        (C : ((BigFppfOver.toScheme B S hS).obj P).Opens),
        IsAffineOpen A ∧ IsAffineOpen C ∧ x ∈ C ∧ C ≤ α ⁻¹ᵁ A := by
    intro x
    obtain ⟨A, hA, hAx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj U)
        (x := α.base x) (U := ⊤) trivial
    obtain ⟨C, hC, hCx, hCsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj P)
        (x := x) (U := α ⁻¹ᵁ A) hAx
    exact ⟨A, C, hA, hC, hCx, hCsub⟩
  choose A C hA hC hCx hCle using hchoice
  -- finitely many of them cover `T`
  have hbopen : IsOpenMap ((BigFppfOver.toScheme B S hS).map b).base := by
    have := hbe
    exact ((BigFppfOver.toScheme B S hS).map b).isOpenMap
  have hcover : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj T)) ⊆
      ⋃ x, ((BigFppfOver.toScheme B S hS).map b).base '' (C x : Set _) := by
    intro t _
    have := hbs
    obtain ⟨x, hx⟩ := Scheme.Hom.surjective ((BigFppfOver.toScheme B S hS).map b) t
    exact Set.mem_iUnion.2 ⟨x, x, hCx x, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _
    (fun x => hbopen _ (C x).2) hcover
  -- the chosen affine opens as objects of the site
  have hCcont : ∀ x, B.Contains (C x).toScheme := fun x =>
    Scheme.size_lt_of_isOpenImmersion (C x).ι P.left.property
  have hAcont : ∀ x, B.Contains (A x).toScheme := fun x =>
    Scheme.size_lt_of_isOpenImmersion (A x).ι U.left.property
  set V : (BigFppfOver.toScheme B S hS).obj P → BigFppfOver B S hS := fun x =>
    Over.mk (ObjectProperty.homMk ((C x).ι ≫ B.inclusion.map P.hom) :
      B.obj (hCcont x) ⟶ B.obj hS) with hVdef
  set Y : (BigFppfOver.toScheme B S hS).obj P → BigFppfOver B S hS := fun x =>
    Over.mk (ObjectProperty.homMk ((A x).ι ≫ B.inclusion.map U.hom) :
      B.obj (hAcont x) ⟶ B.obj hS) with hYdef
  set ρ : ∀ x, V x ⟶ P := fun x => Over.homMk (ObjectProperty.homMk (C x).ι) rfl with hρdef
  set κ : ∀ x, Y x ⟶ U := fun x => Over.homMk (ObjectProperty.homMk (A x).ι) rfl with hκdef
  have hρmap : ∀ x, (BigFppfOver.toScheme B S hS).map (ρ x) = (C x).ι := fun _ => rfl
  have hκmap : ∀ x, (BigFppfOver.toScheme B S hS).map (κ x) = (A x).ι := fun _ => rfl
  have hPover : α ≫ B.inclusion.map U.hom = B.inclusion.map P.hom := by
    have h := congrArg B.inclusion.map (Over.w a)
    rw [B.inclusion.map_comp] at h
    exact h
  have hm : ∀ x, ∃ ψ : V x ⟶ Y x,
      (BigFppfOver.toScheme B S hS).map ψ = α.resLE (A x) (C x) (hCle x) := by
    intro x
    refine BigFppfOver.exists_hom_of_comp_eq B S hS (X := V x) (Y := Y x)
      (α.resLE (A x) (C x) (hCle x)) ?_
    show α.resLE (A x) (C x) (hCle x) ≫ (A x).ι ≫ B.inclusion.map U.hom =
      (C x).ι ≫ B.inclusion.map P.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hPover]
  choose μ hμmap using hm
  have htri : ∀ x, μ x ≫ κ x = ρ x ≫ a := by
    intro x
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hμmap, hκmap, hρmap, ← hαdef]
    exact Scheme.Hom.resLE_comp_ι α (hCle x)
  -- the two disjoint unions
  let σ := {x // x ∈ s}
  have hσ : Cardinal.mk σ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  obtain ⟨Z, cZ, eZ, hZι, huZ⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (B := B) (S := S) (hS := hS) hσ
      fun k : σ => Y k.1
  obtain ⟨W, cW, eW, hWι, huW⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (B := B) (S := S) (hS := hS) hσ
      fun k : σ => V k.1
  obtain ⟨dU, hdU⟩ := huZ fun k : σ => κ k.1
  obtain ⟨dP, hdP⟩ := huW fun k : σ => ρ k.1
  obtain ⟨m, hm⟩ := huW fun k : σ => μ k.1 ≫ cZ k
  -- affineness
  have : ∀ k : σ, IsAffine ((BigFppfOver.toScheme B S hS).obj (Y k.1)) := fun k => hA k.1
  have : ∀ k : σ, IsAffine ((BigFppfOver.toScheme B S hS).obj (V k.1)) := fun k => hC k.1
  have hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) := IsAffine.of_isIso eZ.inv
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := IsAffine.of_isIso eW.inv
  -- étaleness of the two coproduct maps
  have hdUe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map dU) :=
    etale_of_coproduct_desc B S hS hZι (fun k : σ => κ k.1) hdU fun k => by
      rw [hκmap]; infer_instance
  have hdPe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map dP) :=
    etale_of_coproduct_desc B S hS hWι (fun k : σ => ρ k.1) hdP fun k => by
      rw [hρmap]; infer_instance
  refine ⟨Z, W, yoneda.map dU ≫ f, m, dP ≫ b, hZaff, hWaff,
    etale_comp_of_scheme B S hS dU f hdUe hfE, ?_, ?_, ?_⟩
  · rw [Functor.map_comp]
    have := hbe
    infer_instance
  · refine ⟨fun t => ?_⟩
    obtain ⟨x, hx, ht⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
    obtain ⟨v, hv, rfl⟩ := ht
    obtain ⟨v', rfl⟩ : ∃ v' : (C x).toScheme, (C x).ι.base v' = v := ⟨⟨v, hv⟩, rfl⟩
    refine ⟨((BigFppfOver.toScheme B S hS).map (cW ⟨x, hx⟩)).base v', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Category.assoc, hdP, Functor.map_comp,
      Scheme.Hom.comp_apply, hρmap]
  · have h1 : m ≫ dU = dP ≫ a := coproduct_hom_ext B S hS hWι fun k => by
      rw [← Category.assoc, hm k, Category.assoc, hdU k, htri k.1, ← Category.assoc, hdP k]
    rw [← Category.assoc, ← Functor.map_comp, h1, Functor.map_comp, Category.assoc, hsq,
      ← Category.assoc, ← Functor.map_comp]

end AlgebraicGeometry.Space

end
