module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGeometricallyConnectedGlobalFunctions
public import StacksFrontier.RingTheory.Flat.EqualizerTensorExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsKernelPair

/-!
# Global functions of an algebraic space as an equalizer

Let `F` be an algebraic space over `S`, let `p : U ⟶ F` be a surjective étale atlas and let
`r₁, r₂ : R ⟶ U` present `R` as `U ×_F U`. Then pullback of global functions to `U` identifies
`Γ(F, 𝒪_F)` with the equalizer of `r₁^*, r₂^* : Γ(U, 𝒪_U) ⇉ Γ(R, 𝒪_R)`. For `F` over `Spec A`
with `U` and `R` affine, and an `A`-algebra `A'`, it follows that the global functions of the
base change `F_{A'}` are `A'` exactly when `0 → A' → A' ⊗_A Γ(U) → A' ⊗_A Γ(R)` is exact.

## Main results

* `AlgebraicGeometry.Space.injective_globalFunctionsToChart_of_atlas`: pullback of global
  functions to a surjective étale atlas is injective.
* `AlgebraicGeometry.Space.exists_globalFunctionsToChart_eq_iff`: a function on the atlas comes
  from a global function exactly when its two pullbacks to `U ×_F U` agree, with
  `AlgebraicGeometry.Space.Presentation.exists_globalFunctionsToChart_eq_iff` its form for an
  étale presentation.
* `AlgebraicGeometry.Space.exists_addEquiv_tensor_of_isPullback_spec`: the functions on
  `X ×_{Spec A} Spec A'` for an affine `X` are `A' ⊗_A Γ(X)`.
* `AlgebraicGeometry.Space.presheaf_surjective_chartRelocalizeRestrict`,
  `AlgebraicGeometry.Space.presheaf_etale_chartRelocalizeRestrict` and
  `AlgebraicGeometry.Space.isPullback_chartRelocalizeRestrict`: a surjective étale atlas and its
  kernel pair base change to a surjective étale atlas and its kernel pair.
* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_relocalizeRestrict_iff`: the
  global functions of `F_{A'}` are `A'` if and only if
  `AlgHom.EqualizerTensorExact r₁^* r₂^* A'` holds, and
  `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_iff` is the case `A' = A`,
  without base change and without affineness.

## Implementation notes

The descent is that of `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas`,
run from a function on the atlas equalized by its kernel pair
(`AlgebraicGeometry.Space.gamma_eq_of_isPullback_kernelPair`) rather than from a global function:
on each scheme chart `T` of `F` the function descends uniquely along the surjective étale
covering `U ×_F T ⟶ T`, and the values are compatible by
`AlgebraicGeometry.Space.atlas_extension_gamma_compatible`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The extension to all scheme charts of the restriction of an all-chart family to the étale
charts is the family itself. -/
theorem globalFunctionsChartEquiv_chartFunctionsToSmall (t : chartFunctions B S hS F) :
    (globalFunctionsChartEquiv B S hS ⟨F, hF⟩).val (chartFunctionsToSmall B S hS F t) = t :=
  chartFunctionsToSmall_injective B S hS F hF
    ((globalFunctionsChartEquiv B S hS ⟨F, hF⟩).property _)

section Equalizer

variable {U R : BigFppfOver B S hS} (p : yoneda.obj U ⟶ F)
  (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf p)
  (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf p)
  (r₁ r₂ : R ⟶ U) (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p)

include hps hpe in
/-- Pullback of global functions to a surjective étale atlas is injective. -/
theorem injective_globalFunctionsToChart_of_atlas :
    Function.Injective (globalFunctionsToChart B S hS ⟨F, hF⟩ p) := by
  have h : ⇑(globalFunctionsToChart B S hS ⟨F, hF⟩ p) =
      fun s : globalFunctions B S hS F =>
        s.val (op (⟨CostructuredArrow.mk p, hpe⟩ : SmallEtale B S hS F)) :=
    funext fun s => globalFunctionsToChart_etale B S hS F hF ⟨CostructuredArrow.mk p, hpe⟩ s
  rw [h]
  exact injective_globalFunctions_val_of_isSurjective B S hS F hF _
    (isSurjective_of_presheafSurjective B S hS p hps)

include hR in
/-- A function on the atlas pulled back from a global function is equalized by the two
projections of the kernel pair. -/
theorem globalFunctionsToChart_comp_eq (s : globalFunctions B S hS F) :
    ((BigFppfOver.toScheme B S hS).map r₁).appTop (globalFunctionsToChart B S hS ⟨F, hF⟩ p s) =
      ((BigFppfOver.toScheme B S hS).map r₂).appTop
        (globalFunctionsToChart B S hS ⟨F, hF⟩ p s) := by
  rw [← globalFunctionsToChart_yoneda_map_comp, ← globalFunctionsToChart_yoneda_map_comp, hR.w]

include hps hpe hR in
/-- **Global functions are the functions on an atlas equalized by its kernel pair.** A function
`c` on a surjective étale atlas `U ⟶ F` is pulled back from a global function of `F` exactly when
its two pullbacks to `R = U ×_F U` agree: it then descends to every scheme chart `T` of `F` along
the surjective étale covering `U ×_F T ⟶ T`. -/
theorem exists_globalFunctionsToChart_eq_iff (c : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (∃ s, globalFunctionsToChart B S hS ⟨F, hF⟩ p s = c) ↔
      ((BigFppfOver.toScheme B S hS).map r₁).appTop c =
        ((BigFppfOver.toScheme B S hS).map r₂).appTop c := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    exact globalFunctionsToChart_comp_eq B S hS F hF p r₁ r₂ hR s
  intro hc
  have hex : ∀ j : CostructuredArrow yoneda F, ∃ (P : BigFppfOver B S hS) (α : P ⟶ j.left)
      (pHom : P ⟶ U) (v : Γ((BigFppfOver.toScheme B S hS).obj j.left, ⊤)),
      IsPullback (yoneda.map pHom) (yoneda.map α) p j.hom ∧
        Etale ((BigFppfOver.toScheme B S hS).map α) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map α) ∧
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map α).op).hom v =
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom c := by
    intro j
    obtain ⟨P, α, q, hpb⟩ := hpe.1 j.hom
    have hαE : Etale ((BigFppfOver.toScheme B S hS).map α) := hpe.2 j.hom q α hpb
    have hαS : Surjective ((BigFppfOver.toScheme B S hS).map α) := hps.2 j.hom q α hpb
    let pHom := Yoneda.fullyFaithful.preimage q
    have hpHom : yoneda.map pHom = q := Yoneda.fullyFaithful.map_preimage q
    obtain ⟨v, hv, -⟩ := existsUnique_gamma_of_etale_surjection B S hS α hαS hαE
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map pHom).op).hom c) (by
        intro Z g₁ g₂ hg
        rw [gamma_map_comp, gamma_map_comp, ← Functor.map_comp, ← Functor.map_comp]
        exact gamma_eq_of_isPullback_kernelPair B S hS F p r₁ r₂ hR c hc _ _ (by
          rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hpHom,
            hpb.w, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
            hg]))
    exact ⟨P, α, pHom, v, hpHom ▸ hpb, hαE, hαS, hv⟩
  choose P α pHom v hpb hαE hαS hv using hex
  let t : chartFunctions B S hS F := ⟨fun j => v j.unop, by
    intro j k f
    obtain ⟨d, hdP, hdAlpha⟩ := atlas_extension_pullback_maps B S hS F U p f.unop
      (α k.unop) (α j.unop) _ _ (pHom k.unop) (pHom j.unop) rfl rfl (hpb k.unop) (hpb j.unop)
    exact atlas_extension_gamma_compatible B S hS F U f.unop (α k.unop) (α j.unop)
      (pHom k.unop) (pHom j.unop) d hdP hdAlpha (hαE k.unop) (hαS k.unop) c
      (v k.unop) (v j.unop) (hv k.unop) (hv j.unop)⟩
  refine ⟨chartFunctionsToSmall B S hS F t, ?_⟩
  show ((globalFunctionsChartEquiv B S hS ⟨F, hF⟩).val _).val _ = _
  rw [globalFunctionsChartEquiv_chartFunctionsToSmall B S hS F hF t]
  let j₀ : CostructuredArrow yoneda F := CostructuredArrow.mk p
  show v j₀ = c
  refine gamma_injective_of_etale_surjection B S hS (α j₀) (hαS j₀) (hαE j₀) ?_
  rw [hv j₀]
  exact (gamma_eq_of_isPullback_kernelPair B S hS F p r₁ r₂ hR c hc (α j₀) (pHom j₀)
    (hpb j₀).w.symm).symm

/-- **Global functions through an étale presentation.** For a presentation `R ⇉ U ⟶ F` of an
algebraic space, pullback of global functions to `U` is injective, and its image consists of the
functions on `U` whose two pullbacks to `R` agree. -/
theorem Presentation.exists_globalFunctionsToChart_eq_iff (P : Presentation B S hS F hF)
    (c : Γ((BigFppfOver.toScheme B S hS).obj P.U, ⊤)) :
    (∃ s, globalFunctionsToChart B S hS ⟨F, hF⟩ P.toSpace s = c) ↔
      ((BigFppfOver.toScheme B S hS).map P.target).appTop c =
        ((BigFppfOver.toScheme B S hS).map P.source).appTop c :=
  AlgebraicGeometry.Space.exists_globalFunctionsToChart_eq_iff B S hS F hF P.toSpace
    P.surjective P.etale P.target P.source P.isPullback c

/-- Pullback of global functions to the atlas of a presentation is injective. -/
theorem Presentation.injective_globalFunctionsToChart (P : Presentation B S hS F hF) :
    Function.Injective (globalFunctionsToChart B S hS ⟨F, hF⟩ P.toSpace) :=
  injective_globalFunctionsToChart_of_atlas B S hS F hF P.toSpace P.surjective P.etale

end Equalizer

/-! ### Base change of the base ring -/

/-- **Functions on a base change of an affine scheme along a ring map.** For an affine scheme `X`
over `Spec A`, an `A`-algebra `A'` and `P = X ×_{Spec A} Spec A'`, the functions on `P` are
`A' ⊗_A Γ(X)`, an elementary tensor `a ⊗ c` being the product of the pullbacks of `a` and `c`. -/
theorem exists_addEquiv_tensor_of_isPullback_spec {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {X P : Scheme.{u}} [IsAffine X] {f : X ⟶ Spec (.of A)} {fst : P ⟶ X}
    {snd : P ⟶ Spec (.of A')}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) :
    letI : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
    ∃ e : A' ⊗[A] Γ(X, ⊤) ≃+ Γ(P, ⊤), ∀ a c,
      e (a ⊗ₜ c) = ((Scheme.ΓSpecIso (.of A')).inv ≫ snd.appTop) a * fst.appTop c := by
  have hpo' : IsPushout ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop)
      (CommRingCat.ofHom (algebraMap A A')) fst.appTop
      ((Scheme.ΓSpecIso (.of A')).inv ≫ snd.appTop) :=
    (isPushout_appTop_of_isPullback h).of_iso (Scheme.ΓSpecIso (.of A)) (Iso.refl _)
      (Scheme.ΓSpecIso (.of A')) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  let : Algebra A Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(P, ⊤) := fst.appTop.hom.toAlgebra
  let : Algebra A' Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of A')).inv ≫ snd.appTop).hom.toAlgebra
  let : Algebra A Γ(P, ⊤) := (CommRingCat.ofHom (algebraMap A A') ≫
    (Scheme.ΓSpecIso (.of A')).inv ≫ snd.appTop).hom.toAlgebra
  have : IsScalarTower A A' Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Γ(X, ⊤) Γ(P, ⊤) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom hpo'.w).symm
  have : Algebra.IsPushout A Γ(X, ⊤) A' Γ(P, ⊤) := CommRingCat.isPushout_iff_isPushout.mp hpo'
  have : Algebra.IsPushout A A' Γ(X, ⊤) Γ(P, ⊤) := Algebra.IsPushout.symm this
  exact ⟨(Algebra.IsPushout.equiv A A' Γ(X, ⊤) Γ(P, ⊤)).toRingEquiv.toAddEquiv,
    Algebra.IsPushout.equiv_tmul A A' Γ(X, ⊤) Γ(P, ⊤)⟩

section BaseChangeChart

variable {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'} (g : B.obj hS ⟶ B.obj hS')
  {X : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S' hS'} (p : yoneda.obj U ⟶ X)

/-- The base change along `g : S ⟶ S'` of a chart `p : U ⟶ X`: the chart `U ×_{S'} S ⟶ X_S`. -/
noncomputable abbrev chartRelocalizeRestrict :
    yoneda.obj ((Over.pullback g).obj U) ⟶ (OverShriek.relocalizeRestrict g).obj X :=
  (OverShriek.restrictYonedaIso g U).hom ≫ (OverShriek.relocalizeRestrict g).map p

/-- The base change of a chart which is `Q` after every representable base change is again so,
for a morphism property `Q` of schemes respecting isomorphisms. -/
private theorem presheaf_chartRelocalizeRestrict_of_respectsIso
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (hp : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S' hS')).presheaf p) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      (chartRelocalizeRestrict B g p) := by
  have _ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (OverShriek.relative_relocalizeRestrict_map g
      (inverseImage_restrictReindexSnd B S S' hS hS' g Q) hp)

/-- The base change of a chart which is surjective after every representable base change is
again so. -/
theorem presheaf_surjective_chartRelocalizeRestrict
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf p) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (chartRelocalizeRestrict B g p) :=
  presheaf_chartRelocalizeRestrict_of_respectsIso B g p _ hps

/-- The base change of an étale chart is an étale chart. -/
theorem presheaf_etale_chartRelocalizeRestrict
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf p) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (chartRelocalizeRestrict B g p) :=
  have _ : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  presheaf_chartRelocalizeRestrict_of_respectsIso B g p _ hpe

/-- The base change of the kernel pair of a chart is the kernel pair of the base-changed chart. -/
theorem isPullback_chartRelocalizeRestrict (r₁ r₂ : R ⟶ U)
    (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p) :
    IsPullback (yoneda.map ((Over.pullback g).map r₁)) (yoneda.map ((Over.pullback g).map r₂))
      (chartRelocalizeRestrict B g p) (chartRelocalizeRestrict B g p) := by
  apply (hR.map (OverShriek.relocalizeRestrict g)).of_iso'
    (OverShriek.restrictYonedaIso g R) (OverShriek.restrictYonedaIso g U)
    (OverShriek.restrictYonedaIso g U) (Iso.refl _)
  · exact (OverShriek.restrictYonedaIso_naturality g r₁).symm
  · exact (OverShriek.restrictYonedaIso_naturality g r₂).symm
  · simp
  · simp

end BaseChangeChart

/-- The bookkeeping behind `bijective_algebraMap_globalFunctions_relocalizeRestrict_iff`: if `ψ`
embeds `G` into `V` as the equalizer of `t, t' : V ⇉ W`, and `V ⇉ W` is identified with
`d₁, d₂ : M ⇉ N` compatibly with maps `ι : A' → M` and `φ : A' → G`, then `φ` is bijective
exactly when `ι` is injective with image the equalizer of `d₁, d₂`. -/
theorem bijective_iff_of_isEqualizer {A' G V W M N : Type*} (φ : A' → G) (ψ : G → V)
    (hψ : Function.Injective ψ) (t t' : V → W) (hrange : ∀ c, (∃ s, ψ s = c) ↔ t c = t' c)
    (eU : M ≃ V) (eR : N → W) (heR : Function.Injective eR) (ι : A' → M) (d₁ d₂ : M → N)
    (h₁ : ∀ x, t (eU x) = eR (d₁ x)) (h₂ : ∀ x, t' (eU x) = eR (d₂ x))
    (hι : ∀ a, eU (ι a) = ψ (φ a)) :
    Function.Bijective φ ↔ Function.Injective ι ∧ ∀ x, d₁ x = d₂ x → ∃ n, ι n = x := by
  constructor
  · rintro ⟨hφi, hφs⟩
    refine ⟨fun a b hab => hφi (hψ (by rw [← hι, ← hι, hab])), fun x hx => ?_⟩
    obtain ⟨s, hs⟩ := (hrange (eU x)).mpr (by rw [h₁, h₂, hx])
    obtain ⟨a, rfl⟩ := hφs s
    exact ⟨a, eU.injective (by rw [hι, hs])⟩
  · rintro ⟨hιi, hex⟩
    refine ⟨fun a b hab => hιi (eU.injective (by rw [hι, hι, hab])), fun s => ?_⟩
    obtain ⟨x, hx⟩ := eU.surjective (ψ s)
    obtain ⟨a, ha⟩ := hex x (heR ((h₁ x).symm.trans (((hrange _).mp ⟨s, hx.symm⟩).trans (h₂ x))))
    exact ⟨a, hψ (by rw [← hι, ha, hx])⟩

section BaseChangeIff

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A'] {hA : B.Contains (Spec (.of A))}
  {hA' : B.Contains (Spec (.of A'))}

variable (A) in
/-- The `A`-algebra structure on the functions of a scheme over `Spec A` of the big fppf site,
given by its structure morphism. -/
noncomputable abbrev siteObjectAlgebra (T : BigFppfOver B (Spec (.of A)) hA) :
    Algebra A Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map T.hom).appTop).hom.toAlgebra

/-- Pullback of functions along a morphism of schemes over `Spec A` is a map of `A`-algebras. -/
noncomputable def siteObjectAlgHom {T T' : BigFppfOver B (Spec (.of A)) hA} (r : T ⟶ T') :
    letI := siteObjectAlgebra B A T
    letI := siteObjectAlgebra B A T'
    Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T', ⊤) →ₐ[A]
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj T, ⊤) :=
  letI := siteObjectAlgebra B A T
  letI := siteObjectAlgebra B A T'
  { ((BigFppfOver.toScheme B (Spec (.of A)) hA).map r).appTop.hom with
    commutes' := fun a => by
      change (((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map T'.hom).appTop) ≫
        (B.inclusion.map r.left).appTop).hom a = _
      rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← Functor.map_comp, Over.w r]
      rfl }

/-- **Global functions of a base change along a ring map, through an affine presentation.** Let
`X` be an algebraic space over `Spec A` with a surjective étale atlas `p : U ⟶ X` from an affine
scheme whose kernel pair `R = U ×_X U` is affine, and let `A'` be an `A`-algebra. Then the global
functions of the base change `X_{A'}` are `A'` exactly when the sequence
`0 → A' → A' ⊗_A Γ(U) → A' ⊗_A Γ(R)` (the last map induced by the difference of the two
pullbacks) is exact. Indeed `U_{A'} ⟶ X_{A'}` is again a surjective étale atlas with kernel pair
`R_{A'}`, its functions are `A' ⊗_A Γ(U)`, and global functions are the functions on an atlas
equalized by its kernel pair. -/
theorem bijective_algebraMap_globalFunctions_relocalizeRestrict_iff
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    {U R : BigFppfOver B (Spec (.of A)) hA} (p : yoneda.obj U ⟶ X)
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p)
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p)
    (r₁ r₂ : R ⟶ U) (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p)
    (hU : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U))
    (hRa : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj R))
    (g : B.obj hA' ⟶ B.obj hA)
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    letI := siteObjectAlgebra B A U
    letI := siteObjectAlgebra B A R
    Function.Bijective (algebraMap A'
        (globalFunctions B (Spec (.of A')) hA' ((OverShriek.relocalizeRestrict g).obj X))) ↔
      AlgHom.EqualizerTensorExact (siteObjectAlgHom B r₁) (siteObjectAlgHom B r₂) A' := by
  let := siteObjectAlgebra B A U
  let := siteObjectAlgebra B A R
  rw [AlgHom.equalizerTensorExact_iff_tmulOne]
  let X' := (OverShriek.relocalizeRestrict g).obj X
  have hX' : IsAlgebraicSpace B (Spec (.of A')) hA' X' :=
    isAlgebraicSpace_relocalizeRestrict B (Spec (.of A')) (Spec (.of A)) hA' hA g X hX
  let p' := chartRelocalizeRestrict B g p
  have hps' := presheaf_surjective_chartRelocalizeRestrict B g p hps
  have hpe' := presheaf_etale_chartRelocalizeRestrict B g p hpe
  let U' := (Over.pullback g).obj U
  let R' := (Over.pullback g).obj R
  let σ : A' → Γ((BigFppfOver.toScheme B (Spec (.of A')) hA').obj U', ⊤) := fun a =>
    ((Scheme.ΓSpecIso (.of A')).inv ≫ (B.inclusion.map U'.hom).appTop) a
  have hpb (T : BigFppfOver B (Spec (.of A)) hA) : IsPullback
      (B.inclusion.map (pullback.fst T.hom g)) (B.inclusion.map (pullback.snd T.hom g))
      (B.inclusion.map T.hom) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    hg ▸ (IsPullback.of_hasPullback T.hom g).map B.inclusion
  have : IsAffine (B.inclusion.obj U.left) := hU
  have : IsAffine (B.inclusion.obj R.left) := hRa
  obtain ⟨eU, heU⟩ : ∃ e : A' ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) ≃+
      Γ((BigFppfOver.toScheme B (Spec (.of A')) hA').obj U', ⊤), ∀ a c,
      e (a ⊗ₜ c) = ((Scheme.ΓSpecIso (.of A')).inv ≫
        (B.inclusion.map (pullback.snd U.hom g)).appTop) a *
          (B.inclusion.map (pullback.fst U.hom g)).appTop c :=
    exists_addEquiv_tensor_of_isPullback_spec (hpb U)
  obtain ⟨eR, heR⟩ : ∃ e : A' ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj R, ⊤) ≃+
      Γ((BigFppfOver.toScheme B (Spec (.of A')) hA').obj R', ⊤), ∀ a c,
      e (a ⊗ₜ c) = ((Scheme.ΓSpecIso (.of A')).inv ≫
        (B.inclusion.map (pullback.snd R.hom g)).appTop) a *
          (B.inclusion.map (pullback.fst R.hom g)).appTop c :=
    exists_addEquiv_tensor_of_isPullback_spec (hpb R)
  have hF1 (a : A') : eU (AlgHom.tmulOne A _ A' a) = σ a := by
    rw [AlgHom.tmulOne_apply, heU, map_one, mul_one]
    rfl
  have hF2 (r : R ⟶ U) (x : A' ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤)) :
      ((BigFppfOver.toScheme B (Spec (.of A')) hA').map ((Over.pullback g).map r)).appTop
          (eU x) = eR ((siteObjectAlgHom B r).toLinearMap.lTensor A' x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
    | tmul a c =>
      rw [heU, LinearMap.lTensor_tmul, heR, map_mul]
      have h1 : B.inclusion.map ((Over.pullback g).map r).left ≫
          B.inclusion.map (pullback.snd U.hom g) = B.inclusion.map (pullback.snd R.hom g) := by
        rw [← Functor.map_comp]
        exact congrArg B.inclusion.map (Over.w ((Over.pullback g).map r))
      have h2 : B.inclusion.map ((Over.pullback g).map r).left ≫
          B.inclusion.map (pullback.fst U.hom g) =
            B.inclusion.map (pullback.fst R.hom g) ≫ B.inclusion.map r.left := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg B.inclusion.map (pullback.lift_fst _ _ _)
      congr 1
      · show ((Scheme.ΓSpecIso (.of A')).inv ≫ (B.inclusion.map (pullback.snd U.hom g)).appTop ≫
          (B.inclusion.map ((Over.pullback g).map r).left).appTop) a = _
        rw [← Scheme.Hom.comp_appTop, h1]
      · show ((B.inclusion.map (pullback.fst U.hom g)).appTop ≫
          (B.inclusion.map ((Over.pullback g).map r).left).appTop) c =
            ((B.inclusion.map r.left).appTop ≫
              (B.inclusion.map (pullback.fst R.hom g)).appTop) c
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h2]
  simp only [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
  exact bijective_iff_of_isEqualizer _ _
    (injective_globalFunctionsToChart_of_atlas B _ hA' X' hX' p' hps' hpe') _ _
    (exists_globalFunctionsToChart_eq_iff B _ hA' X' hX' p' hps' hpe' _ _
      (isPullback_chartRelocalizeRestrict B g p r₁ r₂ hR))
    eU.toEquiv eR eR.injective _ _ _
    (hF2 r₁) (hF2 r₂) fun a =>
      (hF1 a).trans (globalFunctionsToChart_algebraMap A' B hA' X' hX' p' a).symm

/-- **Global functions through an atlas, over `Spec A`.** For an algebraic space `X` over
`Spec A` with a surjective étale atlas `p : U ⟶ X` and kernel pair `R = U ×_X U`, the global
functions of `X` are `A` exactly when `0 → A → Γ(U) → Γ(R)` is exact, the last map being the
difference of the two pullbacks. No affineness is needed. -/
theorem bijective_algebraMap_globalFunctions_iff
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    {U R : BigFppfOver B (Spec (.of A)) hA} (p : yoneda.obj U ⟶ X)
    (hps : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p)
    (hpe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf p)
    (r₁ r₂ : R ⟶ U) (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) p p) :
    letI := siteObjectAlgebra B A U
    letI := siteObjectAlgebra B A R
    Function.Bijective (algebraMap A (globalFunctions B (Spec (.of A)) hA X)) ↔
      AlgHom.EqualizerTensorExact (siteObjectAlgHom B r₁) (siteObjectAlgHom B r₂) A := by
  let := siteObjectAlgebra B A U
  let := siteObjectAlgebra B A R
  rw [AlgHom.equalizerTensorExact_iff_tmulOne]
  simp only [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
  have hF2 (r : R ⟶ U) (x : A ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤)) :
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map r).appTop (TensorProduct.lid A _ x) =
        TensorProduct.lid A _ ((siteObjectAlgHom B r).toLinearMap.lTensor A x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
    | tmul a c =>
      rw [TensorProduct.lid_tmul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul]
      exact (siteObjectAlgHom B r).toLinearMap.map_smul a c
  exact bijective_iff_of_isEqualizer _ _
    (injective_globalFunctionsToChart_of_atlas B _ hA X hX p hps hpe) _ _
    (exists_globalFunctionsToChart_eq_iff B _ hA X hX p hps hpe r₁ r₂ hR)
    (TensorProduct.lid A _).toEquiv (TensorProduct.lid A _) (TensorProduct.lid A _).injective
    _ _ _ (hF2 r₁) (hF2 r₂) fun a => by
      show TensorProduct.lid A _ (a ⊗ₜ 1) = _
      rw [TensorProduct.lid_tmul, globalFunctionsToChart_algebraMap A B hA X hX p a,
        ← Algebra.algebraMap_eq_smul_one]
      rfl

end BaseChangeIff

end AlgebraicGeometry.Space

end
