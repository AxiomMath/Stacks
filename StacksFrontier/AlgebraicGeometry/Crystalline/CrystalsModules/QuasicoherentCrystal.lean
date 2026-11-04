module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverCrystal
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality

/-!
# A quasi-coherent sheaf of modules on the big crystalline site is a crystal

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the big crystalline site of a global crystalline
situation.  This file proves the implication (1) ⇒ (2)(b) of [Stacks, Tag 07IT]:

> quasi-coherent on `CRIS(X/S)` implies that `F` is a crystal in `𝒪_{X/S}`-modules,

that is, that for every morphism `f : (U, T, δ) ⟶ (U', T', δ')` the comparison map
`c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules of [Stacks, Tag 07IQ] is an isomorphism.
The crystal condition is read at sheaf level, which is
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`; the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal` explains why that is the
reading under which the tag is true.

## The two steps

The source's computation — a presentation `⊕_J 𝒪_{X/S} → ⊕_I 𝒪_{X/S} → F → 0` restricts to
presentations of `F_T` and of `F_{T'}`, whence `c_f` is an isomorphism — is performed on a
localised site in
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverCrystal`.  Quasi-coherence
does not give a presentation on all of `CRIS(X/S)`; it gives one on a covering, and the source
reduces to that case with "since it suffices to prove (a) and (b) Zariski locally".  This file
supplies the two things that reduction needs.

The first is the **cocycle of the `f`-map**: composing with the `f`-map of `g₁` and then with the
`f`-map of `g₂` is composing with the `f`-map of `g₁ ≫ g₂`.  It is
`Crystalline.GlobalCrystallineSituation.Thickening.fmapComp_comp`, and it rests on the cocycle of
the restricted structure sheaves, which over an open of the ambient scheme is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_comp`.  The two sides live over
the iterated direct image and over the direct image along the composite; those two sheaves of
modules have the same sections and the two actions of the restricted structure sheaf on them agree
by the cocycle, so they are compared by
`Crystalline.GlobalCrystallineSituation.Thickening.pushforwardCompIso`, an isomorphism which is
the identity on sections.  Composition with the `f`-map mentions no pullback of sheaves of
modules, which is what makes this cocycle elementary; the comparison map itself is reached through
`Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`, in the namespace
`Crystalline.GlobalCrystallineSituation`.

The second is that the **crystal condition at a morphism is Zariski-local on the ambient scheme of
its source**.  Invertibility of a morphism of sheaves of modules is local on the site, by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`, and the restriction of `c_f` to
an open `W` of `T` is invertible as soon as composition with the `f`-map is bijective at every
direct image from `W`: restriction along the image functor of the structure morphism of `A|_W` is
left adjoint to that direct image, which is
`Crystalline.GlobalCrystallineSituation.Thickening.modulePushforwardAdjunction`, so the two
bijectivity statements are transposes of one another.

Putting them together: around every point of `T'` quasi-coherence gives an open `V` on whose
restriction the module has a global presentation; the preimages of those opens cover `T`; the
square `A|_{f⁻¹V} ⟶ A ⟶ B` equals `A|_{f⁻¹V} ⟶ B|_V ⟶ B` has invertible comparison maps at the
two structure morphisms, which are Cartesian open immersions, and at `A|_{f⁻¹V} ⟶ B|_V` by the
computation on the localised site; so the cocycle gives bijectivity at the direct images from the
cover, and locality concludes.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.fmapComp_comp` — **composition with the
  `f`-map composes.**
* `Crystalline.GlobalCrystallineSituation.Thickening.bijective_fmapComp_pushforward_of_comm` — the
  form of the cocycle the Zariski-local reduction uses, at a commuting square.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparisonSheaf_of_isOpenCover` —
  **the crystal condition at a morphism is Zariski-local on the ambient scheme of its source.**
* `Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite` —
  **[Stacks, Tag 07IT], the implication (1) ⇒ (2)(b): a quasi-coherent sheaf of
  `𝒪_{X/S}`-modules on `CRIS(X/S)` is a crystal in `𝒪_{X/S}`-modules.**

## Implementation notes

The cocycle is stated for composition with the `f`-map rather than for the comparison map, because
the comparison map of a composite is formed with the pullback along the composite while the
composite of the comparison maps is formed with the composite of the pullbacks; no such
reconciliation is needed on the direct-image side, where
`CategoryTheory.PresheafOfModules.pushforwardComp` identifies the two functors.  That identity is
used as a term, not re-established: the definitional equality it asserts is affordable for
Mathlib's variables and not for the concrete sheaves of rings here.

The adjunction transposing the two bijectivity statements is taken at the level of presheaves of
modules, a morphism of sheaves of modules being its underlying morphism of presheaves of modules,
so no lift of that adjunction to sheaves is needed.

[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike; the same
implication for the small site is
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_of_isQuasicoherentOnSite`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation.Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Composition with the `f`-map composes -/

/-- **The `f`-maps of the restricted structure sheaves compose.**  This is the cocycle condition
of [Stacks, Tag 07IQ] for the structure sheaf: over an open of the ambient scheme of the final
target both sides are the restriction map of `𝒪_{X/S}` along the restriction of the composite
morphism, which factors by
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_comp`. -/
theorem restrictionFMap_comp {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'') :
    restrictionFMap (crisRing S) g₂ ≫
        Functor.whiskerLeft (Opens.map g₂.targetHom.hom.base).op
          (restrictionFMap (crisRing S) g₁) =
      restrictionFMap (crisRing S) (g₁ ≫ g₂) := by
  ext W : 2
  exact ((crisRing S).map_comp _ _).symm.trans (congrArg (crisRing S).map
    (congrArg Quiver.Hom.op (restrictOpenMap_comp g₁ g₂ W.unop).symm))

/-- The `f`-map cocycle of the restricted structure sheaves, read on the ring of sections over an
open of the ambient scheme of the final target. -/
theorem restrictionFMap_app_comp {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (W : (A''.thickening.target.scheme.Opens)ᵒᵖ) :
    ((restrictionFMap (crisRing S) (g₁ ≫ g₂)).app W).hom =
      RingHom.comp
        ((restrictionFMap (crisRing S) g₁).app (op (g₂.targetHom.hom ⁻¹ᵁ W.unop))).hom
        ((restrictionFMap (crisRing S) g₂).app W).hom :=
  congrArg RingCat.Hom.hom (NatTrans.congr_app (restrictionFMap_comp g₁ g₂).symm W)

/-- **The direct image of a sheaf of modules along a composite of morphisms of `CRIS(X/S)` is the
iterated direct image.**  The two sheaves of modules have the same sections over every open of the
ambient scheme, and the two actions of the restricted structure sheaf on them agree by the `f`-map
cocycle, so the comparison is the identity on sections. -/
noncomputable def pushforwardCompIso {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₂)).obj
        ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₁)).obj Z) ≅
      (SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap (g₁ ≫ g₂))).obj Z :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun W ↦ (ModuleCat.restrictScalarsComp'App
        ((restrictionFMap (crisRing S) g₂).app W).hom
        ((restrictionFMap (crisRing S) g₁).app (op (g₂.targetHom.hom ⁻¹ᵁ W.unop))).hom
        ((restrictionFMap (crisRing S) (g₁ ≫ g₂)).app W).hom (restrictionFMap_app_comp g₁ g₂ W)
        (Z.val.obj (op (g₁.targetHom.hom ⁻¹ᵁ (g₂.targetHom.hom ⁻¹ᵁ W.unop))))).symm)
      (by intro X Y f; ext x; rfl))

/-- **Composition with the `f`-map composes.**  Composing with the `f`-map of `g₁` and then with
the `f`-map of `g₂` is composing with the `f`-map of `g₁ ≫ g₂`, read through the identification of
the iterated direct image with the direct image along the composite.

This is the form of the cocycle condition that the Zariski-local reduction of
[Stacks, Tag 07IT] consumes: it mentions no pullback of sheaves of modules, only the restrictions
to the ambient schemes and their direct images, all computed on sections. -/
theorem fmapComp_comp (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf)
    (k : (moduleRestrictionSheafFunctor.{u} A).obj M ⟶ Z) :
    fmapComp.{u} M g₂ ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₁)).obj Z)
        (fmapComp.{u} M g₁ Z k) ≫ (pushforwardCompIso g₁ g₂ Z).hom =
      fmapComp.{u} M (g₁ ≫ g₂) Z k := by
  apply SheafOfModules.Hom.ext
  ext W x
  exact congrArg (ModuleCat.Hom.hom (k.val.app
      (op (g₁.targetHom.hom ⁻¹ᵁ (g₂.targetHom.hom ⁻¹ᵁ W.unop)))))
    ((M.val.map_comp_apply (restrictOpenMap g₂ W.unop).op
        (restrictOpenMap g₁ (g₂.targetHom.hom ⁻¹ᵁ W.unop)).op x).symm.trans
      (M.val.congr_map_apply
        (congrArg Quiver.Hom.op (restrictOpenMap_comp g₁ g₂ W.unop)).symm x))

/-- Postcomposition with an isomorphism is bijective on morphisms. -/
theorem bijective_comp_right_of_iso {C₁ : Type*} [Category C₁] {X Y Z : C₁} (e : Y ≅ Z) :
    Function.Bijective (fun k : X ⟶ Y ↦ k ≫ e.hom) :=
  ⟨fun _ _ hab ↦ by simpa using congrArg (fun t ↦ t ≫ e.inv) hab,
    fun c ↦ ⟨c ≫ e.inv, by simp⟩⟩

/-- Bijectivity of the `f`-map composition along a composite is that of the two-step composite. -/
private theorem bijective_fmapComp_comp_iff (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    Function.Bijective (fmapComp.{u} M (g₁ ≫ g₂) Z) ↔
      Function.Bijective ((fmapComp.{u} M g₂
        ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₁)).obj Z)) ∘
          (fmapComp.{u} M g₁ Z)) := by
  have hfun : fmapComp.{u} M (g₁ ≫ g₂) Z =
      (fun v ↦ v ≫ (pushforwardCompIso g₁ g₂ Z).hom) ∘
        ((fmapComp.{u} M g₂ _) ∘ (fmapComp.{u} M g₁ Z)) :=
    funext fun k ↦ (fmapComp_comp M g₁ g₂ Z k).symm
  rw [hfun]
  exact (bijective_comp_right_of_iso (X := (moduleRestrictionSheafFunctor.{u} A'').obj M)
    (pushforwardCompIso g₁ g₂ Z)).of_comp_iff' _

/-- **Composition with the `f`-map of a composite is bijective as soon as it is bijective at each
factor.** -/
theorem bijective_fmapComp_comp (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf)
    (h₁ : Function.Bijective (fmapComp.{u} M g₁ Z))
    (h₂ : Function.Bijective (fmapComp.{u} M g₂
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₁)).obj Z))) :
    Function.Bijective (fmapComp.{u} M (g₁ ≫ g₂) Z) := by
  exact (bijective_fmapComp_comp_iff M g₁ g₂ Z).2 (h₂.comp h₁)

/-- **The middle factor of a bijective two-step `f`-map composition is bijective**, the first
factor being bijective. -/
theorem bijective_fmapComp_of_comp (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A A' A'' : Thickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf)
    (h₁ : Function.Bijective (fmapComp.{u} M g₁ Z))
    (h : Function.Bijective (fmapComp.{u} M (g₁ ≫ g₂) Z)) :
    Function.Bijective (fmapComp.{u} M g₂
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₁)).obj Z)) := by
  exact Function.Bijective.of_comp_iff _ h₁ |>.1 ((bijective_fmapComp_comp_iff M g₁ g₂ Z).1 h)

/-- **Composition with the `f`-map is bijective at a direct image, for a morphism factoring
through a commuting square of two further morphisms with bijective `f`-map composition.**

The square is the one the Zariski-local reduction of [Stacks, Tag 07IT] uses: the restriction of a
morphism over an open of its target, followed by the structure morphism of that open, is the
structure morphism of the preimage followed by the morphism itself. -/
theorem bijective_fmapComp_pushforward_of_comm
    (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    {A A' A'' A''' : Thickening S} {g₁ : A ⟶ A'} {g₂ : A' ⟶ A''} {h₁ : A ⟶ A'''}
    {h₂ : A''' ⟶ A''} (hsq : g₁ ≫ g₂ = h₁ ≫ h₂)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf)
    (hg₁ : Function.Bijective (fmapComp.{u} M g₁ Z))
    (hh₁ : Function.Bijective (fmapComp.{u} M h₁ Z))
    (hh₂ : Function.Bijective (fmapComp.{u} M h₂
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap h₁)).obj Z))) :
    Function.Bijective (fmapComp.{u} M g₂
      ((SheafOfModules.pushforward.{u} (ringRestrictionSheafFMap g₁)).obj Z)) := by
  have h := bijective_fmapComp_comp M h₁ h₂ Z hh₁ hh₂
  rw [← hsq] at h
  exact bijective_fmapComp_of_comp M g₁ g₂ Z hg₁ h


/-! ### The crystal condition is Zariski-local on the ambient scheme -/

/-- **Postcomposition with the comparison map is bijective at a sheaf of `𝒪_T`-modules exactly
when composition with the `f`-map is bijective there.**  The two are transposes of one another
along the adjunction between pullback and pushforward of sheaves of modules. -/
theorem bijective_comp_moduleComparisonSheaf_iff
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A B : Thickening S} (g : A ⟶ B)
    (Z : SheafOfModules.{u} A.ringRestrictionSheaf) :
    Function.Bijective (fun k : moduleRestrictionSheaf M A ⟶ Z ↦ moduleComparisonSheaf M g ≫ k) ↔
      Function.Bijective (fmapComp.{u} M g Z) := by
  have hE := Equiv.bijective ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z)
  have hfun : (fun k : moduleRestrictionSheaf M A ⟶ Z ↦
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (ringRestrictionSheafFMap g)).homEquiv (moduleRestrictionSheaf M B) Z
            (moduleComparisonSheaf M g ≫ k)) = fmapComp.{u} M g Z :=
    funext fun k ↦ homEquiv_moduleComparisonSheaf_comp M g Z k
  rw [← hfun]
  exact (hE.of_comp_iff' _).symm

/-- **Restriction of sheaves of `𝒪_T`-modules to an open of the ambient scheme**, as a morphism of
sheaves of rings over the image functor of the structure morphism of the restriction: the
restriction of `𝒪_{X/S}` to the ambient scheme of `A|_W` is its restriction to the ambient scheme
of `A` taken over the images of the opens, by
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionImageIso`. -/
noncomputable def restrictImageHom (A : Thickening S) (W : A.thickening.target.scheme.Opens) :
    (A.restrictOpen W).ringRestrictionSheaf ⟶
      ((A.restrictOpenHom W).targetHom.hom.opensFunctor.sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology ↥(A.restrictOpen W).thickening.target.scheme)
          (Opens.grothendieckTopology ↥A.thickening.target.scheme)).obj
        A.ringRestrictionSheaf :=
  ⟨(ringRestrictionImageIso (A.restrictOpenHom W) (A.isCartesian_restrictOpenHom W)).inv⟩

/-- **The transpose of a morphism out of the restriction of a sheaf of modules to an open of the
ambient scheme.**  Restriction along the image functor is left adjoint to the direct image along
the structure morphism of the restriction, which is
`Crystalline.GlobalCrystallineSituation.Thickening.modulePushforwardAdjunction`; a morphism of
sheaves of modules is its underlying morphism of presheaves of modules, so the transpose is taken
there. -/
noncomputable def restrictImageTranspose (A : Thickening S)
    (W : A.thickening.target.scheme.Opens) (X : SheafOfModules.{u} A.ringRestrictionSheaf)
    (Z₀ : SheafOfModules.{u} (A.restrictOpen W).ringRestrictionSheaf) :
    ((SheafOfModules.pushforward.{u} (restrictImageHom A W)).obj X ⟶ Z₀) →
      (X ⟶ (SheafOfModules.pushforward.{u}
        (ringRestrictionSheafFMap (A.restrictOpenHom W))).obj Z₀) :=
  fun k ↦ ⟨(modulePushforwardAdjunction (A.restrictOpenHom W)
    (A.isCartesian_restrictOpenHom W)).homEquiv X.val Z₀.val k.val⟩

/-- **Taking the transpose is bijective.** -/
theorem bijective_restrictImageTranspose (A : Thickening S)
    (W : A.thickening.target.scheme.Opens) (X : SheafOfModules.{u} A.ringRestrictionSheaf)
    (Z₀ : SheafOfModules.{u} (A.restrictOpen W).ringRestrictionSheaf) :
    Function.Bijective (restrictImageTranspose A W X Z₀) := by
  constructor
  · intro a b hab
    exact SheafOfModules.Hom.ext ((Equiv.injective _) (congrArg SheafOfModules.Hom.val hab))
  · intro c
    refine ⟨⟨((modulePushforwardAdjunction (A.restrictOpenHom W)
      (A.isCartesian_restrictOpenHom W)).homEquiv X.val Z₀.val).symm c.val⟩, ?_⟩
    exact SheafOfModules.Hom.ext (Equiv.apply_symm_apply _ _)

/-- **The transpose is natural in the restricted module**, which is naturality of the adjunction
in its left variable. -/
theorem restrictImageTranspose_comp (A : Thickening S) (W : A.thickening.target.scheme.Opens)
    {X X' : SheafOfModules.{u} A.ringRestrictionSheaf} (u : X' ⟶ X)
    (Z₀ : SheafOfModules.{u} (A.restrictOpen W).ringRestrictionSheaf)
    (k : (SheafOfModules.pushforward.{u} (restrictImageHom A W)).obj X ⟶ Z₀) :
    restrictImageTranspose A W X' Z₀
        ((SheafOfModules.pushforward.{u} (restrictImageHom A W)).map u ≫ k) =
      u ≫ restrictImageTranspose A W X Z₀ k :=
  SheafOfModules.Hom.ext (Adjunction.homEquiv_naturality_left _ _ _)

/-- **The comparison map restricted to an open of the ambient scheme is an isomorphism as soon as
composition with the `f`-map is bijective at every direct image from that open.** -/
theorem isIso_pushforward_restrictImage_moduleComparisonSheaf
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A B : Thickening S} (g : A ⟶ B)
    (W : A.thickening.target.scheme.Opens)
    (h : ∀ Z₀ : SheafOfModules.{u} (A.restrictOpen W).ringRestrictionSheaf,
      Function.Bijective (fmapComp.{u} M g ((SheafOfModules.pushforward.{u}
        (ringRestrictionSheafFMap (A.restrictOpenHom W))).obj Z₀))) :
    IsIso ((SheafOfModules.pushforward.{u} (restrictImageHom A W)).map
      (moduleComparisonSheaf M g)) := by
  refine isIso_of_coyoneda_map_bijective _ fun Z₀ ↦ ?_
  have hA := bijective_restrictImageTranspose A W (moduleRestrictionSheaf M A) Z₀
  have hB := bijective_restrictImageTranspose A W
    ((SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).obj
      (moduleRestrictionSheaf M B)) Z₀
  have hc : Function.Bijective (fun k : moduleRestrictionSheaf M A ⟶
      (SheafOfModules.pushforward.{u}
        (ringRestrictionSheafFMap (A.restrictOpenHom W))).obj Z₀ ↦
          moduleComparisonSheaf M g ≫ k) :=
    (bijective_comp_moduleComparisonSheaf_iff M g _).2 (h Z₀)
  have hsq : (restrictImageTranspose A W
          ((SheafOfModules.pullback.{u} (ringRestrictionSheafFMap g)).obj
            (moduleRestrictionSheaf M B)) Z₀) ∘
        (fun k ↦ (SheafOfModules.pushforward.{u} (restrictImageHom A W)).map
          (moduleComparisonSheaf M g) ≫ k) =
      (fun k ↦ moduleComparisonSheaf M g ≫ k) ∘
        (restrictImageTranspose A W (moduleRestrictionSheaf M A) Z₀) :=
    funext fun k ↦ restrictImageTranspose_comp A W (moduleComparisonSheaf M g) Z₀ k
  refine (hB.of_comp_iff' _).1 ?_
  rw [hsq]
  exact hc.comp hA

/-- An open of the ambient scheme contained in `W` is the image of its preimage in `W`. -/
theorem restrictOpenHom_image_preimage (A : Thickening S)
    (W : A.thickening.target.scheme.Opens) {W' : A.thickening.target.scheme.Opens}
    (hW' : W' ≤ W) :
    (A.restrictOpenHom W).targetHom.hom ''ᵁ ((A.restrictOpenHom W).targetHom.hom ⁻¹ᵁ W') = W' := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, restrictOpenHom_targetHom_opensRange]
  exact inf_eq_right.mpr hW'

/-- **The crystal condition at a morphism is Zariski-local on the ambient scheme of its source.**
If the ambient scheme of the source is covered by opens over each of which composition with the
`f`-map is bijective at every direct image, then the comparison map is an isomorphism.

Invertibility of a morphism of sheaves of modules is local on the site
(`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`), and the component of the
comparison map at an open contained in a member of the cover is a component of its restriction to
that member. -/
theorem isIso_moduleComparisonSheaf_of_isOpenCover
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A B : Thickening S} (g : A ⟶ B)
    {ι : Type*} (W : ι → A.thickening.target.scheme.Opens) (hW : IsOpenCover W)
    (h : ∀ (i : ι) (Z₀ : SheafOfModules.{u} (A.restrictOpen (W i)).ringRestrictionSheaf),
      Function.Bijective (fmapComp.{u} M g ((SheafOfModules.pushforward.{u}
        (ringRestrictionSheafFMap (A.restrictOpenHom (W i)))).obj Z₀))) :
    IsIso (moduleComparisonSheaf M g) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop
    ((Opens.coversTop_iff _ W).mpr hW) _ fun i W' p ↦ ?_
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_congr _
    (congrArg op (restrictOpenHom_image_preimage A (W i) (leOfHom p))) ?_
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
    (restrictImageHom A (W i)) _
    (isIso_pushforward_restrictImage_moduleComparisonSheaf M g (W i) (h i))
    (op ((A.restrictOpenHom (W i)).targetHom.hom ⁻¹ᵁ W'))


end Crystalline.GlobalCrystallineSituation.Thickening

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **Stacks Project, Tag 07IT, the implication (1) ⇒ (2)(b): a quasi-coherent sheaf of
`𝒪_{X/S}`-modules on the big crystalline site is a crystal in `𝒪_{X/S}`-modules.**

For a morphism `f : (U, T, δ) ⟶ (U', T', δ')` the comparison map `c_f : f^* F_{T'} ⟶ F_T` of
sheaves of `𝒪_T`-modules is an isomorphism.  This is the source's argument, with its opening
reduction "it suffices to prove (a) and (b) Zariski locally" carried out: quasi-coherence gives,
around every point of `T'`, an open `V` on whose restriction `(U' ∩ V, V, δ'|_V)` the module has a
global presentation, the restrictions of `f` over those opens cover `T`, and over each of them the
source's computation applies on the localised site `CRIS(X/S)/(U' ∩ V, V, δ'|_V)`, by
`Thickening.isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target`.
The comparison maps of the structure morphisms of the two restrictions are isomorphisms, those
morphisms being Cartesian open immersions, so the `f`-map cocycle
(`Crystalline.GlobalCrystallineSituation.Thickening.fmapComp_comp`) transfers bijectivity of the
`f`-map composition to the direct images from the members of the cover, and invertibility of
`c_f` follows because it is Zariski-local on `T`. -/
@[stacks 07IT "the implication (1) ⇒ (2)(b) on the big site CRIS(X/S): a quasi-coherent sheaf of
  𝒪_{X/S}-modules is a crystal in 𝒪_{X/S}-modules, the crystal condition being read with the
  comparison maps of sheaves of modules.  The same implication on the small site Cris(X/S), and
  the implication (1) ⇒ (2)(a) on each of the two sites, carry this tag separately.  The converse
  (2) ⇒ (1) is a separate statement"]
theorem isSheafCrystal_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (hM : M.IsQuasicoherentOnSite) :
    IsSheafCrystal M := by
  choose V hxV hV using exists_hasGlobalPresentation_restrictOpen M hM
  intro A B g
  refine Thickening.isIso_moduleComparisonSheaf_of_isOpenCover M g
    (fun x : B.thickening.target.scheme ↦ g.targetHom.hom ⁻¹ᵁ V B x) ?_ ?_
  · refine eq_top_iff.2 fun y _ ↦ ?_
    exact Opens.mem_iSup.2 ⟨g.targetHom.hom.base y, hxV B (g.targetHom.hom.base y)⟩
  · intro x Z₀
    have key {A₁ B₁ : Thickening S} {g' : A₁ ⟶ B₁}
        (hg : IsIso (Thickening.moduleComparisonSheaf M g'))
        (Z : SheafOfModules.{u} A₁.ringRestrictionSheaf) :
        Function.Bijective (Thickening.fmapComp.{u} M g' Z) :=
      (Thickening.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1 hg Z
    exact Thickening.bijective_fmapComp_pushforward_of_comm M
      (Thickening.restrictOpenMap_restrictOpenHom g (V B x)).symm Z₀
      (key (Thickening.isIso_moduleComparisonSheaf_of_isCartesian M _
        (A.isCartesian_restrictOpenHom _)) Z₀)
      (key (Thickening.isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target M (hV B x) _) Z₀)
      (key (Thickening.isIso_moduleComparisonSheaf_of_isCartesian M _
        (B.isCartesian_restrictOpenHom _)) _)

end Crystalline.GlobalCrystallineSituation

end
