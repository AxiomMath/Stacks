module

public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationAtlasQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.RingTheory.Etale.AffineStageCore

/-!
# An algebraic space with a cartesian affine chart over an fpqc covering is affine

This is the last step of the proof of Stacks 07SQ. Work over the terminal scheme, so that every
scheme of the site is an object over the base. Let `F` be an algebraic space with an affine
surjective étale chart `f : h_U ⟶ F` and kernel pair `R`. Let `Spec P ⟶ Spec A` be flat and
surjective, both spectra in the site. Let `a : U ⟶ Spec A` and `b : U ⟶ Spec P` be morphisms
with `b ≫ π = a`, and suppose the two pullbacks of `a` to `R` agree. Then `a` descends to a
morphism `g : F ⟶ h_{Spec A}`.

Suppose moreover that the morphism `R ⟶ U ×_{Spec A} Spec P` with components `(s, t ≫ b)` is
an isomorphism. That is display 70.5.10.1 of the source, the square of Stacks 084U, read on the
chart. Then the square

```
  h_U     ⟶  h_{Spec P}
   ↓f            ↓
   F      ⟶  h_{Spec A}
```

is cartesian, so the base change of `g` along the fpqc covering `Spec P ⟶ Spec A` is
represented by the affine scheme `U`. By effective descent for affine morphisms along fpqc
coverings, `F` itself is represented by an affine scheme.

## Main results

* `AlgebraicGeometry.Space.isPullback_chart_of_isIso_lift`: the square above is cartesian.
* `AlgebraicGeometry.Space.isAffineSpace_of_isIso_lift`: `F` is affine.

## Implementation notes

The square is shown to be cartesian by showing the comparison morphism into the fibre product
of presheaves to be a monomorphism and locally surjective. Both are checked on points: two
points of `U` with the same image are the two projections of one point of `R`, and the
isomorphism with `U ×_{Spec A} Spec P` identifies that point with a diagonal one. A point of the
fibre product lifts to `U` étale-locally, through the chart, and the isomorphism moves the lift
into the position required.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Over the terminal scheme, a morphism of underlying schemes is a morphism of the site. -/
def terminalHomMk {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (φ : (BigFppfOver.toScheme B _ hZ).obj X ⟶ (BigFppfOver.toScheme B _ hZ).obj Y) : X ⟶ Y :=
  Over.homMk (ObjectProperty.homMk φ) (by apply ObjectProperty.hom_ext; exact terminal.hom_ext _ _)

/-- The underlying morphism of schemes of `terminalHomMk φ` is `φ`. -/
@[simp] theorem toScheme_map_terminalHomMk {X Y : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (φ : (BigFppfOver.toScheme B _ hZ).obj X ⟶ (BigFppfOver.toScheme B _ hZ).obj Y) :
    (BigFppfOver.toScheme B _ hZ).map (terminalHomMk B hZ φ) = φ := rfl

/-- Over the terminal scheme, a scheme of the site is an object of the site. -/
abbrev terminalObj {X : Scheme.{u}} (hX : B.Contains X) : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  BigFppfOver.mk B _ hZ hX (terminal.from X)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over the terminal scheme (instance search
times out without this shortcut). -/
private instance hasPullbacks_presheaf_AffineOfCartesianChart :
    HasPullbacks ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_AffineOfCartesianChart
    {X Y Z : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Chart

variable {B hZ} {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  (hF : IsAlgebraicSpace B _ hZ F) {U R : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  (f : yoneda.obj U ⟶ F) (t s : R ⟶ U) (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
  (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hZ))) f)
  (het : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B _ hZ))) f)
  {SA SP : BigFppfOver B (⊤_ Scheme.{u}) hZ} (π : SP ⟶ SA) (a : U ⟶ SA) (b : U ⟶ SP)
  (hab : b ≫ π = a) (hsa : s ≫ a = t ≫ a)

include hR hF hsurj het hsa in
/-- The morphism `a` descends along the chart to a morphism `g : F ⟶ h_{SA}`. -/
theorem exists_desc_chart : ∃ g : F ⟶ yoneda.obj SA, f ≫ g = yoneda.map a := by
  obtain ⟨hRsh, hUsh, ⟨hcolim⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B _ hZ f t s hR hF hsurj het
  let J := BigFppfOver.topology B (⊤_ Scheme.{u}) hZ
  have hSAsh : Presheaf.IsSheaf J (yoneda.obj SA) := BigFppfOver.isSheaf_yoneda_obj B _ hZ SA
  let G : Sheaf J (Type u) := ⟨yoneda.obj SA, hSAsh⟩
  let k : (⟨yoneda.obj U, hUsh⟩ : Sheaf J (Type u)) ⟶ G := ⟨yoneda.map a⟩
  have hk :
      (⟨yoneda.map t⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj U, hUsh⟩) ≫ k =
      (⟨yoneda.map s⟩ : (⟨yoneda.obj R, hRsh⟩ : Sheaf J (Type u)) ⟶ ⟨yoneda.obj U, hUsh⟩) ≫ k := by
    apply Sheaf.hom_ext
    show yoneda.map t ≫ yoneda.map a = yoneda.map s ≫ yoneda.map a
    rw [← Functor.map_comp, ← Functor.map_comp, hsa]
  exact ⟨(hcolim.desc (Cofork.ofπ k hk)).hom,
    congrArg (fun m => m.hom) (hcolim.fac (Cofork.ofπ k hk) WalkingParallelPair.one)⟩

variable {f t s π a b} in
/-- The compatibility making `(s, t ≫ b) : R ⟶ U ×_{SA} SP` a morphism into the fibre product. -/
theorem lift_condition (hab : b ≫ π = a) (hsa : s ≫ a = t ≫ a) :
    (BigFppfOver.toScheme B _ hZ).map s ≫ (BigFppfOver.toScheme B _ hZ).map a =
      ((BigFppfOver.toScheme B _ hZ).map t ≫ (BigFppfOver.toScheme B _ hZ).map b) ≫
        (BigFppfOver.toScheme B _ hZ).map π := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, hab, hsa]

include hR hF hsurj het in
/-- **The square of Stacks 084U is cartesian** as soon as the comparison morphism
`R ⟶ U ×_{SA} SP` with components `(s, t ≫ b)` is an isomorphism of schemes. -/
theorem isPullback_chart_of_isIso_lift (g : F ⟶ yoneda.obj SA) (hg : f ≫ g = yoneda.map a)
    (hiso : IsIso (pullback.lift ((BigFppfOver.toScheme B _ hZ).map s)
      ((BigFppfOver.toScheme B _ hZ).map t ≫ (BigFppfOver.toScheme B _ hZ).map b)
      (lift_condition hab hsa))) :
    IsPullback f (yoneda.map b) g (yoneda.map π) := by
  set G := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  set Θ := pullback.lift (G.map s) (G.map t ≫ G.map b) (lift_condition hab hsa) with hΘ
  have hsq : f ≫ g = yoneda.map b ≫ yoneda.map π := by rw [hg, ← Functor.map_comp, hab]
  let c : yoneda.obj U ⟶ pullback g (yoneda.map π) := pullback.lift f (yoneda.map b) hsq
  have hcfst : c ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd _ _ = yoneda.map b := pullback.lift_snd _ _ _
  -- `c` is a monomorphism
  have hmono : Mono c := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    rw [mono_iff_injective]
    intro v v' hvv'
    have hc : yoneda.map v ≫ c = yoneda.map v' ≫ c :=
      yonedaEquiv.injective (by
        rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map])
    have h1 : yoneda.map v ≫ f = yoneda.map v' ≫ f := by
      rw [← hcfst, ← Category.assoc, hc, Category.assoc]
    have h2 : v ≫ b = v' ≫ b := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_comp, ← hcsnd, ← Category.assoc, hc, Category.assoc]
    have hRlift : ∀ x y : T.unop ⟶ U, yoneda.map x ≫ f = yoneda.map y ≫ f →
        ∃ r : T.unop ⟶ R, r ≫ t = x ∧ r ≫ s = y := fun x y h =>
      ⟨yoneda.preimage (hR.lift (yoneda.map x) (yoneda.map y) h),
        yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hR.lift_fst]),
        yoneda.map_injective (by rw [Functor.map_comp, Functor.map_preimage, hR.lift_snd])⟩
    obtain ⟨r, hrt, hrs⟩ := hRlift v v' h1
    obtain ⟨r₀, hr₀t, hr₀s⟩ := hRlift v' v' rfl
    have hΘeq : G.map r ≫ Θ = G.map r₀ ≫ Θ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hΘ, pullback.lift_fst,
          ← Functor.map_comp, ← Functor.map_comp, hrs, hr₀s]
      · rw [Category.assoc, Category.assoc, hΘ, pullback.lift_snd]
        simp only [← Functor.map_comp]
        rw [← Category.assoc, hrt, ← Category.assoc, hr₀t, h2]
    have hrr : r = r₀ := BigFppfOver.map_toScheme_injective B _ hZ ((cancel_mono Θ).1 hΘeq)
    rw [← hrt, ← hr₀t, hrr]
  -- `c` is locally surjective
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B _ hZ) c := by
    constructor
    intro T x
    let X : yoneda.obj T ⟶ pullback g (yoneda.map π) := yonedaEquiv.symm x
    let zz : yoneda.obj T ⟶ F := X ≫ pullback.fst _ _
    refine (BigFppfOver.topology B _ hZ).superset_covering ?_
      ((isLocallySurjective_of_surjective_etale B _ hZ f hsurj het).imageSieve_mem
        (yonedaEquiv zz))
    rintro T' h ⟨v, hv⟩
    have hv' : yoneda.map v ≫ f = yoneda.map h ≫ zz :=
      yonedaEquiv.injective (by
        rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality])
    let y : T' ⟶ SP := h ≫ yoneda.preimage (X ≫ pullback.snd _ _)
    have hy : yoneda.map y = yoneda.map h ≫ X ≫ pullback.snd _ _ := by
      simp only [y, Functor.map_comp, Functor.map_preimage]
    have hva : v ≫ a = y ≫ π := by
      apply yoneda.map_injective
      rw [Functor.map_comp, ← hg, ← Category.assoc, hv', Functor.map_comp, hy]
      simp only [zz, Category.assoc, pullback.condition]
    have hℓ : G.map v ≫ G.map a = G.map y ≫ G.map π := by
      rw [← Functor.map_comp, ← Functor.map_comp, hva]
    let ℓ := pullback.lift (G.map v) (G.map y) hℓ
    let wR : T' ⟶ R := terminalHomMk B hZ (ℓ ≫ inv Θ)
    have hinvfst : inv Θ ≫ G.map s = pullback.fst _ _ := by
      rw [IsIso.inv_comp_eq, hΘ, pullback.lift_fst]
    have hinvsnd : inv Θ ≫ (G.map t ≫ G.map b) = pullback.snd _ _ := by
      rw [IsIso.inv_comp_eq, hΘ, pullback.lift_snd]
    have hws : wR ≫ s = v := by
      apply BigFppfOver.map_toScheme_injective B _ hZ
      show (ℓ ≫ inv Θ) ≫ G.map s = G.map v
      rw [Category.assoc, hinvfst, pullback.lift_fst]
    have hwtb : wR ≫ t ≫ b = y := by
      apply BigFppfOver.map_toScheme_injective B _ hZ
      show (ℓ ≫ inv Θ) ≫ G.map (t ≫ b) = G.map y
      rw [Functor.map_comp, Category.assoc, hinvsnd, pullback.lift_snd]
    refine ⟨wR ≫ t, ?_⟩
    have hmain : yoneda.map (wR ≫ t) ≫ c = yoneda.map h ≫ X := by
      apply pullback.hom_ext
      · rw [Category.assoc, hcfst, Functor.map_comp, Category.assoc, hR.w, ← Category.assoc,
          ← Functor.map_comp, hws, hv', Category.assoc]
      · rw [Category.assoc, hcsnd, ← Functor.map_comp, Category.assoc, hwtb, hy, Category.assoc]
    have := congrArg yonedaEquiv hmain
    rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality,
      Equiv.apply_symm_apply] at this
  have : IsIso c :=
    NormalizationGluing.isIso_of_mono_of_isLocallySurjective_of_isSheaf B _ hZ
      (BigFppfOver.isSheaf_yoneda_obj B _ hZ U)
      (Presheaf.isSheaf_pullback _ g (yoneda.map π) hF.isSheaf
        (BigFppfOver.isSheaf_yoneda_obj B _ hZ SP) (BigFppfOver.isSheaf_yoneda_obj B _ hZ SA))
      c hmono hloc
  exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso c) hcfst hcsnd

include hR hF hsurj het in
/-- **The source of a cartesian chart over an fpqc covering of an affine scheme is affine.**
With the data of `AlgebraicGeometry.Space.isPullback_chart_of_isIso_lift`, if `U`, `SA` and `SP`
have affine underlying schemes and `SP ⟶ SA` is flat and surjective, then `F` is an affine
algebraic space. -/
theorem isAffineSpace_of_isIso_lift
    (hU : IsAffine ((BigFppfOver.toScheme B _ hZ).obj U))
    (hSA : IsAffine ((BigFppfOver.toScheme B _ hZ).obj SA))
    (hSP : IsAffine ((BigFppfOver.toScheme B _ hZ).obj SP))
    [Flat ((BigFppfOver.toScheme B _ hZ).map π)] [Surjective ((BigFppfOver.toScheme B _ hZ).map π)]
    (hiso : IsIso (pullback.lift ((BigFppfOver.toScheme B _ hZ).map s)
      ((BigFppfOver.toScheme B _ hZ).map t ≫ (BigFppfOver.toScheme B _ hZ).map b)
      (lift_condition hab hsa))) :
    IsAffineSpace B _ hZ F := by
  obtain ⟨g, hg⟩ := exists_desc_chart hF f t s hR hsurj het a hsa
  have hpb := isPullback_chart_of_isIso_lift hF f t s hR hsurj het π a b hab hsa g hg hiso
  let SA' : BigAffineFppf B _ hZ := ⟨SA, hSA⟩
  let SP' : BigAffineFppf B _ hZ := ⟨SP, hSP⟩
  let U' : BigAffineFppf B _ hZ := ⟨U, hU⟩
  let π' : SP' ⟶ SA' := ObjectProperty.homMk π
  let 𝒰 : PreZeroHypercover.{u + 1} SA' := PreZeroHypercover.singleton π'
  have hmem : Presieve.map (BigAffineFppf.toScheme B _ hZ) 𝒰.presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B _ hZ).obj SA') := by
    rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
    have : Flat ((BigAffineFppf.toScheme B _ hZ).map π') :=
      inferInstanceAs (Flat ((BigFppfOver.toScheme B _ hZ).map π))
    have : Surjective ((BigAffineFppf.toScheme B _ hZ).map π') :=
      inferInstanceAs (Surjective ((BigFppfOver.toScheme B _ hZ).map π))
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage _
  obtain ⟨W, p, q, hpq⟩ := isEffectiveAffineDescentAlongFpqc B _ hZ SA' 𝒰
    (inferInstanceAs (Finite PUnit)) hmem hF (isAlgebraicSpace_yoneda B _ hZ SA) g (𝟙 _)
    (fun _ => ⟨U', f, b, by rwa [Category.comp_id]⟩)
  have : IsIso p := hpq.isIso_fst_of_isIso
  exact ⟨W.obj, W.property, ⟨(asIso p).symm⟩⟩

end Chart

/-! ### The cartesian square, from the rings -/

section Rings

variable {U R : Scheme.{u}} (s t : R ⟶ U) {A P : Type u} [CommRing A] [CommRing P] [Algebra A P]
  (α : CommRingCat.of A ⟶ Γ(U, ⊤)) (ψ : CommRingCat.of P ⟶ Γ(U, ⊤))

variable {s t α ψ} in
/-- The compatibility making `(s, t ≫ U.toSpecΓ ≫ Spec.map ψ)` a point of the fibre product
`U ×_{Spec A} Spec P` used in the square of Stacks 084U: it holds as soon as `α` pulls back to
the same map along `s` and `t`, and `ψ` restricts to `α` on `A`. -/
theorem lift_cond_of_rings (hψ : CommRingCat.ofHom (algebraMap A P) ≫ ψ = α)
    (hst : α ≫ s.appTop = α ≫ t.appTop) :
    s ≫ U.toSpecΓ ≫ Spec.map α =
      (t ≫ U.toSpecΓ ≫ Spec.map ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A P)) := by
  have h1 : ∀ f : R ⟶ U, f ≫ U.toSpecΓ ≫ Spec.map α = R.toSpecΓ ≫ Spec.map (α ≫ f.appTop) :=
    fun f => by rw [Spec.map_comp, Scheme.toSpecΓ_naturality_assoc]
  rw [h1 s, hst, ← h1 t, ← hψ, Spec.map_comp]
  simp only [Category.assoc]

/-- **The square of Stacks 084U on affine schemes, from the rings.** If `R → U ×_{Spec A} Spec P`
is described on rings by a bijection `Γ(U) ⊗_A P ≅ Γ(R)`, `x ⊗ p ↦ s^* x · t^* (ψ p)`, then the
morphism `(s, t ≫ b)` into the fibre product is an isomorphism. -/
theorem isIso_lift_of_bijective [IsAffine U] [IsAffine R]
    (hψ : CommRingCat.ofHom (algebraMap A P) ≫ ψ = α)
    (hst : α ≫ s.appTop = α ≫ t.appTop)
    (hbij : letI := α.hom.toAlgebra
      ∃ h, Function.Bijective (Stacks.AffineStageCore.tensorLift (A := A) s.appTop.hom
        (t.appTop.hom.comp ψ.hom) h)) :
    IsIso (pullback.lift s (t ≫ U.toSpecΓ ≫ Spec.map ψ) (lift_cond_of_rings hψ hst) :
      R ⟶ pullback (U.toSpecΓ ≫ Spec.map α) (Spec.map (CommRingCat.ofHom (algebraMap A P)))) := by
  let := α.hom.toAlgebra
  obtain ⟨h, hb⟩ := hbij
  let Θ : Γ(U, ⊤) ⊗[A] P ≃+* Γ(R, ⊤) := RingEquiv.ofBijective
    (Stacks.AffineStageCore.tensorLift (A := A) s.appTop.hom (t.appTop.hom.comp ψ.hom) h) hb
  have hpo : IsPushout α (CommRingCat.ofHom (algebraMap A P)) s.appTop (ψ ≫ t.appTop) := by
    refine (CommRingCat.isPushout_tensorProduct A Γ(U, ⊤) P).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) Θ.toCommRingCatIso ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · ext x
      simp [Θ]
    · ext x
      simp [Θ]
  have hpb : IsPullback s (t ≫ U.toSpecΓ ≫ Spec.map ψ) (U.toSpecΓ ≫ Spec.map α)
      (Spec.map (CommRingCat.ofHom (algebraMap A P))) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).of_iso
    (asIso R.toSpecΓ).symm (asIso U.toSpecΓ).symm (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.eq_inv_comp,
        ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id])
    (by
      rw [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp, Iso.refl_hom, Category.comp_id,
        Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc])
    (by simp)
    (by simp)
  have : pullback.lift s (t ≫ U.toSpecΓ ≫ Spec.map ψ) (lift_cond_of_rings hψ hst) =
      hpb.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [this]
  infer_instance

end Rings

end AlgebraicGeometry.Space

end
