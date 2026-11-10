module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverCrystal

/-!
# A quasi-coherent sheaf of modules on the small crystalline site is a crystal

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` of a global
crystalline situation.  This file proves [Stacks, Tag 07IT] for `𝒞 = Cris(X/S)`, the implication
(1) ⇒ (2)(b): if `F` is quasi-coherent on the site, then it is a crystal in `𝒪_{X/S}`-modules,
that is, for every morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` the comparison map
`c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules is an isomorphism.

This is the small-site form of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentCrystal`, and it is not a
consequence of it: a sheaf of modules on `Cris(X/S)` is in general not the restriction of one on
`CRIS(X/S)`, so the argument is repeated here, as it is in
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverCrystal` for the computation on
a localised site.  The source's opening reduction "it suffices to prove (a) and (b) Zariski locally"
is carried out: quasi-coherence gives, around every point of `T'`, an open `V` on whose
restriction `(U' ∩ V, V, δ'|_V)` the module has a global presentation, the restrictions of `f` over
those opens cover `T`, and over each of them the source's computation applies on the localised site
`Cris(X/S)/(U' ∩ V, V, δ'|_V)`.  The `f`-map cocycle then transfers bijectivity of the `f`-map
composition from the members of that cover to `f` itself, and invertibility of `c_f` follows
because it is Zariski-local on `T`.

## Main results

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite`, the comparison maps in its subnamespace
`CohomologyRestriction`.

* `CohomologyRestriction.fmapComp_comp` and
  `CohomologyRestriction.bijective_fmapComp_pushforward_of_comm` — **the `f`-map cocycle on
  `Cris(X/S)`** and the consequence the Zariski-local reduction consumes: composition with the
  `f`-map of the second leg of a commuting square is bijective when it is so along the other two
  sides.
* `CohomologyRestriction.isIso_moduleComparison` and
  `CohomologyRestriction.isIso_moduleComparisonSheaf_of_isCartesian` — **the comparison map of a
  Cartesian open immersion of `Cris(X/S)` is an isomorphism**, for presheaves and for sheaves of
  modules.
* `CohomologyRestriction.isIso_moduleComparisonSheaf_of_isOpenCover` — **the crystal condition at
  a morphism of `Cris(X/S)` is Zariski-local on the ambient scheme of its source.**
* `isSheafCrystal_of_isQuasicoherentOnSite` — **[Stacks, Tag 07IT], the implication (1) ⇒ (2)(b)
  on `Cris(X/S)`: a quasi-coherent sheaf of `𝒪_{X/S}`-modules is a crystal in
  `𝒪_{X/S}`-modules.**

## Implementation notes

The ring level of the small crystalline site is the ring level of the big one: the restriction of
`𝒪_{X/S}` to the ambient scheme of an object of `Cris(X/S)` is the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestriction` at the underlying object, and
the `f`-map of a morphism is the big site's at the underlying morphism, both by `rfl`.  Everything
in the big-site file that mentions only that data is therefore applied here at the underlying
morphism rather than restated: the cocycle of the restricted structure sheaves
(`Crystalline.GlobalCrystallineSituation.Thickening.restrictionFMap_comp`), the identification of
the iterated direct image (`...Thickening.pushforwardCompIso`), the second adjunction of a
Cartesian open immersion (`...Thickening.modulePushforwardAdjunction`) and the transposition
bijection of a restriction to an open (`...Thickening.restrictImageTranspose`).  Only the
module-level statements are new, a sheaf of modules on `Cris(X/S)` not being the restriction of
one on `CRIS(X/S)`.

Invertibility of the comparison map of sheaves of modules at a Cartesian open immersion is proved
here rather than taken from the big site, for the same reason: the big site's statement is about a
sheaf of modules on `CRIS(X/S)`, and the transport lemmas of
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal` carry the crystal condition
along restriction from the big site only for modules that come from it.  The small-site proof
follows the big site's: the restriction to the ambient scheme of the source is the restriction to
the ambient scheme of the target read over the images of the opens
(`CohomologyRestriction.moduleRestrictionImageMap`), whose transpose for the second adjunction is
the `f`-map, so the comparison morphism of presheaves of modules is invertible; and the passage
from the presheaf level to the sheaf level is made through the test
`...SmallSite.CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp`, which
mentions no pullback and therefore needs no sheafification.  Injectivity and surjectivity of
composition with the `f`-map are separate declarations: each of the two identifications of a
morphism of sheaves of modules with its underlying morphism of presheaves of modules unfolds the
restriction along an identity of sheaves of rings, and one declaration carrying all of them
exhausts the elaborator's budget.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}}

/-! ### Composition with the `f`-map composes -/

/-- **Composition with the `f`-map composes.** -/
theorem fmapComp_comp (M : SheafOfModules.{u} (structureSheaf S))
    {A A' A'' : CrystallineThickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (k : (moduleRestrictionSheafFunctor.{u} A).obj M ⟶ Z) :
    fmapComp.{u} M g₂ ((SheafOfModules.pushforward.{u}
            (Thickening.ringRestrictionSheafFMap g₁.hom)).obj Z)
          (fmapComp.{u} M g₁ Z k) ≫
        (Thickening.pushforwardCompIso g₁.hom g₂.hom Z).hom =
      fmapComp.{u} M (g₁ ≫ g₂) Z k := by
  apply SheafOfModules.Hom.ext
  ext W x
  exact congrArg (ModuleCat.Hom.hom (k.val.app
      (op (g₁.hom.targetHom.hom ⁻¹ᵁ (g₂.hom.targetHom.hom ⁻¹ᵁ W.unop)))))
    ((M.val.map_comp_apply (CrystallineThickening.restrictOpenMap g₂ W.unop).op
        (CrystallineThickening.restrictOpenMap g₁
          (g₂.hom.targetHom.hom ⁻¹ᵁ W.unop)).op x).symm.trans
      (M.val.congr_map_apply
        (congrArg Quiver.Hom.op (restrictOpenMap_comp g₁ g₂ W.unop)).symm x))

/-- **The `f`-map of a composite is the composite of the `f`-maps**, followed by the
composition isomorphism of direct images. -/
private theorem fmapComp_comp_eq (M : SheafOfModules.{u} (structureSheaf S))
    {A A' A'' : CrystallineThickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    fmapComp.{u} M (g₁ ≫ g₂) Z =
      (fun v ↦ v ≫ (Thickening.pushforwardCompIso g₁.hom g₂.hom Z).hom) ∘
        ((fmapComp.{u} M g₂ _) ∘ (fmapComp.{u} M g₁ Z)) :=
  funext fun k ↦ (fmapComp_comp M g₁ g₂ Z k).symm

/-- **Composition with the `f`-map of a composite is bijective as soon as it is bijective at each
factor.** -/
theorem bijective_fmapComp_comp (M : SheafOfModules.{u} (structureSheaf S))
    {A A' A'' : CrystallineThickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (h₁ : Function.Bijective (fmapComp.{u} M g₁ Z))
    (h₂ : Function.Bijective (fmapComp.{u} M g₂
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap g₁.hom)).obj Z))) :
    Function.Bijective (fmapComp.{u} M (g₁ ≫ g₂) Z) := by
  rw [fmapComp_comp_eq]
  exact (Thickening.bijective_comp_right_of_iso
    (X := (moduleRestrictionSheafFunctor.{u} A'').obj M)
    (Thickening.pushforwardCompIso g₁.hom g₂.hom Z)).comp (h₂.comp h₁)

/-- **The middle factor of a bijective two-step `f`-map composition is bijective**, the first
factor being bijective. -/
theorem bijective_fmapComp_of_comp (M : SheafOfModules.{u} (structureSheaf S))
    {A A' A'' : CrystallineThickening S} (g₁ : A ⟶ A') (g₂ : A' ⟶ A'')
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (h₁ : Function.Bijective (fmapComp.{u} M g₁ Z))
    (h : Function.Bijective (fmapComp.{u} M (g₁ ≫ g₂) Z)) :
    Function.Bijective (fmapComp.{u} M g₂
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap g₁.hom)).obj Z)) := by
  rw [fmapComp_comp_eq] at h
  exact Function.Bijective.of_comp_iff _ h₁ |>.1
    (((Thickening.bijective_comp_right_of_iso
      (X := (moduleRestrictionSheafFunctor.{u} A'').obj M)
      (Thickening.pushforwardCompIso g₁.hom g₂.hom Z)).of_comp_iff'
        ((fmapComp.{u} M g₂ _) ∘ (fmapComp.{u} M g₁ Z))).1 h)

/-- **Composition with the `f`-map is bijective at a direct image, for a morphism factoring
through a commuting square of two further morphisms with bijective `f`-map composition.** -/
theorem bijective_fmapComp_pushforward_of_comm (M : SheafOfModules.{u} (structureSheaf S))
    {A A' A'' A''' : CrystallineThickening S} {g₁ : A ⟶ A'} {g₂ : A' ⟶ A''} {h₁ : A ⟶ A'''}
    {h₂ : A''' ⟶ A''} (hsq : g₁ ≫ g₂ = h₁ ≫ h₂)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (hg₁ : Function.Bijective (fmapComp.{u} M g₁ Z))
    (hh₁ : Function.Bijective (fmapComp.{u} M h₁ Z))
    (hh₂ : Function.Bijective (fmapComp.{u} M h₂
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap h₁.hom)).obj Z))) :
    Function.Bijective (fmapComp.{u} M g₂
      ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap g₁.hom)).obj Z)) :=
  bijective_fmapComp_of_comp M g₁ g₂ Z hg₁ (hsq ▸ bijective_fmapComp_comp M h₁ h₂ Z hh₁ hh₂)

/-! ### The comparison map of a Cartesian open immersion -/

variable {A B : CrystallineThickening S}

/-- **The restrictions of an object of `Cris(X/S)` to the opens of its ambient scheme, mapped to
the restrictions of the target of an open immersion out of it over the images of those opens.** -/
noncomputable def restrictOpenFunctorImageMap (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] :
    CrystallineThickening.restrictOpenFunctor A ⟶
      g.hom.targetHom.hom.opensFunctor ⋙ CrystallineThickening.restrictOpenFunctor B where
  app V := ObjectProperty.homMk ((Thickening.restrictOpenFunctorImageMap g.hom).app V)
  naturality _ _ i := ObjectProperty.hom_ext _
    ((Thickening.restrictOpenFunctorImageMap g.hom).naturality i)

/-- **Over the opens of the ambient scheme of its source a Cartesian open immersion of `Cris(X/S)`
restricts to an isomorphism onto the restriction of its target to the image.** -/
theorem isIso_restrictOpenFunctorImageMap_app (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom)
    (V : A.obj.thickening.target.scheme.Opens) :
    IsIso ((restrictOpenFunctorImageMap g).app V) :=
  have : IsIso ((CrystallineThickening.ι S).map ((restrictOpenFunctorImageMap g).app V)) :=
    Thickening.isIso_restrictOpenFunctorImageMap_app g.hom hg V
  isIso_of_fully_faithful (CrystallineThickening.ι S) _

/-- **The restriction of a morphism of `Cris(X/S)` which is an open immersion on ambient schemes,
over an open of the ambient scheme of its target, is its restriction over the image of the
preimage of that open, followed by the inclusion of that image.** -/
theorem restrictOpenFunctorImageMap_app_comp (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (W : B.obj.thickening.target.scheme.Opens) :
    (restrictOpenFunctorImageMap g).app (g.hom.targetHom.hom ⁻¹ᵁ W) ≫
        (CrystallineThickening.restrictOpenFunctor B).map
          (g.hom.targetHom.hom.opensFunctorAdjunction.counit.app W) =
      CrystallineThickening.restrictOpenMap g W :=
  ObjectProperty.hom_ext _ (Thickening.restrictOpenLE_restrictOpenMap_image_preimage g.hom W)

/-- **The restriction of the structure presheaf of `Cris(X/S)` to the ambient scheme of the source
of a Cartesian open immersion is its restriction to the ambient scheme of the target, taken over
the images of the opens.**  The structure presheaf of the small site is the restriction along the
inclusion of that of the big site, so this is the big site's isomorphism at the underlying
morphism. -/
noncomputable def ringRestrictionImageIso (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    g.hom.targetHom.hom.opensFunctor.op ⋙ ringRestriction B ≅ ringRestriction A :=
  Thickening.ringRestrictionImageIso g.hom hg

/-- **For a Cartesian open immersion of `Cris(X/S)`, restriction of presheaves of modules along
the image functor on the opens of the ambient schemes is a second left adjoint of the direct
image.**  The ring level of the small site is that of the big site, so this is the big site's
adjunction at the underlying morphism. -/
noncomputable def modulePushforwardAdjunction (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    PresheafOfModules.pushforward.{u} (F := g.hom.targetHom.hom.opensFunctor)
        (ringRestrictionImageIso g hg).inv ⊣
      PresheafOfModules.pushforward.{u} (F := Opens.map g.hom.targetHom.hom.base)
        (restrictionFMap (crisRing S) g) :=
  Thickening.modulePushforwardAdjunction g.hom hg

/-- **The comparison between the sections of the restriction of a presheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` to the ambient scheme of the target of an open immersion over the images of opens, and
the restriction to the ambient scheme of the source.** -/
noncomputable def moduleRestrictionImageMap (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    (PresheafOfModules.pushforward.{u} (F := g.hom.targetHom.hom.opensFunctor)
          (ringRestrictionImageIso g hg).inv).obj (moduleRestriction M B) ⟶
      moduleRestriction M A where
  app V := ModuleCat.ofHom
    (X := ((PresheafOfModules.pushforward.{u} (F := g.hom.targetHom.hom.opensFunctor)
      (ringRestrictionImageIso g hg).inv).obj (moduleRestriction M B)).obj V)
    (Y := (moduleRestriction M A).obj V)
    { toFun := fun x ↦ M.map ((restrictOpenFunctorImageMap g).app V.unop).op x
      map_add' := fun x y ↦
        map_add (M.map ((restrictOpenFunctorImageMap g).app V.unop).op).hom x y
      map_smul' := fun r x ↦ by
        refine (M.map_smul ((restrictOpenFunctorImageMap g).app V.unop).op _ x).trans ?_
        exact congrArg (fun s ↦ s • M.map ((restrictOpenFunctorImageMap g).app V.unop).op x)
          (RingHom.congr_fun (congrArg RingCat.Hom.hom
            (Iso.inv_hom_id_app (ringRestrictionImageIso g hg) V)) r) }
  naturality {V V'} i := by
    ext x
    exact (M.map_comp_apply
          ((g.hom.targetHom.hom.opensFunctor ⋙
            CrystallineThickening.restrictOpenFunctor B).map i.unop).op
          ((restrictOpenFunctorImageMap g).app V'.unop).op x).symm.trans
      ((M.congr_map_apply (congrArg Quiver.Hom.op
            ((restrictOpenFunctorImageMap g).naturality i.unop)).symm x).trans
        (M.map_comp_apply ((restrictOpenFunctorImageMap g).app V.unop).op
          ((CrystallineThickening.restrictOpenFunctor A).map i.unop).op x))

/-- **For a Cartesian open immersion of `Cris(X/S)`, the restriction of a presheaf of
`𝒪_{X/S}`-modules to the ambient scheme of the source is the sections of the restriction to the
ambient scheme of the target over the images of the opens.** -/
theorem isIso_moduleRestrictionImageMap (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    IsIso (moduleRestrictionImageMap M g hg) := by
  refine PresheafOfModules.isIso_of_forall_isIso_app _ fun V ↦ ?_
  have := isIso_restrictOpenFunctorImageMap_app g hg V.unop
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (M.bijective_map_of_isIso ((restrictOpenFunctorImageMap g).app V.unop).op)

/-- The `f`-map of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` along a Cartesian open immersion
is the transpose of the comparison over images for the second adjunction. -/
theorem homEquiv_moduleRestrictionImageMap (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    (modulePushforwardAdjunction g hg).homEquiv
        (moduleRestriction M B) (moduleRestriction M A) (moduleRestrictionImageMap M g hg) =
      moduleFMap M g := by
  rw [Adjunction.homEquiv_unit]
  ext W x
  exact (M.map_comp_apply ((CrystallineThickening.restrictOpenFunctor B).map
        (g.hom.targetHom.hom.opensFunctorAdjunction.counit.app W.unop)).op
      ((restrictOpenFunctorImageMap g).app (g.hom.targetHom.hom ⁻¹ᵁ W.unop)).op x).symm.trans
    (M.congr_map_apply (congrArg Quiver.Hom.op
      (restrictOpenFunctorImageMap_app_comp g W.unop)) x)

/-- **The comparison morphism of an open immersion of `Cris(X/S)` for presheaves of modules is an
isomorphism.** -/
theorem isIso_moduleComparison (M : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    IsIso (moduleComparison M g) := by
  have he : moduleComparison M g =
      ((PresheafOfModules.pullbackPushforwardAdjunction
            (restrictionFMap (crisRing S) g)).leftAdjointUniq
          (modulePushforwardAdjunction g hg)).hom.app (moduleRestriction M B) ≫
        moduleRestrictionImageMap M g hg := by
    refine ((PresheafOfModules.pullbackPushforwardAdjunction
      (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction M B)
        (moduleRestriction M A)).injective ?_
    rw [← moduleFMap_eq_moduleComparison, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact (homEquiv_moduleRestrictionImageMap M g hg).symm
  have := isIso_moduleRestrictionImageMap M g hg
  rw [he]
  infer_instance

/-- Postcomposing the comparison morphism of presheaves of modules and transposing gives the
`f`-map of presheaves of modules followed by the pushforward of the postcomposed morphism. -/
theorem homEquiv_moduleComparison_comp (N : PresheafOfModules.{u} (crisRing S)) (g : A ⟶ B)
    (W : PresheafOfModules.{u} (ringRestriction A)) (k : moduleRestriction N A ⟶ W) :
    (PresheafOfModules.pullbackPushforwardAdjunction
          (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction N B) W
        (moduleComparison N g ≫ k) =
      moduleFMap N g ≫
        (PresheafOfModules.pushforward (F := Opens.map g.hom.targetHom.hom.base)
          (restrictionFMap (crisRing S) g)).map k := by
  rw [Adjunction.homEquiv_naturality_right, moduleComparison, Equiv.apply_symm_apply]

/-- Precomposition with an isomorphism is bijective on morphisms. -/
theorem bijective_comp_left_of_isIso {C₁ : Type*} [Category C₁] {X Y : C₁} (u : X ⟶ Y)
    (hu : IsIso u) (Z : C₁) : Function.Bijective fun k : Y ⟶ Z ↦ u ≫ k :=
  ⟨fun _ _ ↦ (cancel_epi u).1, fun c ↦ ⟨inv u ≫ c, by simp⟩⟩

/-- **Composition with the `f`-map of a sheaf of modules on `Cris(X/S)` is composition with the
`f`-map of the underlying presheaf of modules**, both the restriction to the ambient scheme and
the direct image being computed on sections. -/
theorem fmapComp_val (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))
    (k : (moduleRestrictionSheafFunctor.{u} A).obj M ⟶ Z) :
    (fmapComp.{u} M g Z k).val =
      moduleFMap (M.val : PresheafOfModules.{u} (crisRing S)) g ≫
        (PresheafOfModules.pushforward.{u} (F := Opens.map g.hom.targetHom.hom.base)
          (restrictionFMap (crisRing S) g)).map k.val := rfl

/-- **Composition with the `f`-map of presheaves of modules is bijective as soon as the comparison
morphism of presheaves of modules is invertible**, the two being transposes of one another along
the adjunction between pullback and pushforward of presheaves of modules. -/
theorem bijective_homEquiv_moduleComparison_comp (N : PresheafOfModules.{u} (crisRing S))
    (g : A ⟶ B) (h : IsIso (moduleComparison N g))
    (W : PresheafOfModules.{u} (ringRestriction A)) :
    Function.Bijective (fun k : moduleRestriction N A ⟶ W ↦
      moduleFMap N g ≫ (PresheafOfModules.pushforward.{u}
        (F := Opens.map g.hom.targetHom.hom.base) (restrictionFMap (crisRing S) g)).map k) := by
  simpa only [Function.comp_def, homEquiv_moduleComparison_comp] using
    (Equiv.bijective ((PresheafOfModules.pullbackPushforwardAdjunction
      (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction N B) W)).comp
        (bijective_comp_left_of_isIso (moduleComparison N g) h W)

/-- **Composition with the `f`-map is injective as soon as the comparison morphism of presheaves
of modules is invertible**, a morphism of sheaves of modules being its underlying morphism of
presheaves of modules. -/
theorem injective_fmapComp_of_isIso_moduleComparison
    (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (h : IsIso (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g))
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Injective (fmapComp.{u} M g Z) := fun k₁ k₂ hk ↦
  SheafOfModules.Hom.ext ((bijective_homEquiv_moduleComparison_comp
      (M.val : PresheafOfModules.{u} (crisRing S)) g h Z.val).injective
    ((fmapComp_val M g Z k₁).symm.trans
      ((congrArg SheafOfModules.Hom.val hk).trans (fmapComp_val M g Z k₂))))

/-- **Composition with the `f`-map is surjective as soon as the comparison morphism of presheaves
of modules is invertible**, every morphism of presheaves of modules between sheaves of modules
being a morphism of sheaves of modules. -/
theorem surjective_fmapComp_of_isIso_moduleComparison
    (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (h : IsIso (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g))
    (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Surjective (fmapComp.{u} M g Z) := by
  intro v
  obtain ⟨w, hw⟩ := (bijective_homEquiv_moduleComparison_comp
    (M.val : PresheafOfModules.{u} (crisRing S)) g h Z.val).surjective v.val
  exact ⟨⟨w⟩, SheafOfModules.Hom.ext ((fmapComp_val M g Z ⟨w⟩).trans hw)⟩

/-- **The comparison map of sheaves of modules on `Cris(X/S)` is an isomorphism as soon as the
comparison morphism of presheaves of modules is.** -/
theorem isIso_moduleComparisonSheaf (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (h : IsIso (moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g)) :
    IsIso (moduleComparisonSheaf M g) :=
  (isIso_moduleComparisonSheaf_iff_bijective_fmapComp M g).2 fun Z ↦
    ⟨injective_fmapComp_of_isIso_moduleComparison M g h Z,
      surjective_fmapComp_of_isIso_moduleComparison M g h Z⟩

/-- **Stacks Project, Tag 07IQ.**  The comparison map of sheaves of modules of a Cartesian open
immersion of `Cris(X/S)` is an isomorphism. -/
theorem isIso_moduleComparisonSheaf_of_isCartesian (M : SheafOfModules.{u} (structureSheaf S))
    (g : A ⟶ B) [IsOpenImmersion g.hom.targetHom.hom] (hg : Thickening.IsCartesian g.hom) :
    IsIso (moduleComparisonSheaf M g) :=
  isIso_moduleComparisonSheaf M g
    (isIso_moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) g hg)

/-- **The comparison map of sheaves of modules at the structure morphism of the restriction of an
object of `Cris(X/S)` to an open of its ambient scheme is an isomorphism.** -/
theorem isIso_moduleComparisonSheaf_restrictOpenHom (M : SheafOfModules.{u} (structureSheaf S))
    (A : CrystallineThickening S) (W : A.obj.thickening.target.scheme.Opens) :
    IsIso (moduleComparisonSheaf M (A.restrictOpenHom W)) :=
  have : IsOpenImmersion (A.restrictOpenHom W).hom.targetHom.hom :=
    inferInstanceAs (IsOpenImmersion (A.obj.restrictOpenHom W).targetHom.hom)
  isIso_moduleComparisonSheaf_of_isCartesian M (A.restrictOpenHom W)
    (A.obj.isCartesian_restrictOpenHom W)

/-! ### The crystal condition is Zariski-local on the ambient scheme -/

/-- **Postcomposition with the comparison map is bijective at a sheaf of `𝒪_T`-modules exactly
when composition with the `f`-map is bijective there.** -/
theorem bijective_comp_moduleComparisonSheaf_iff (M : SheafOfModules.{u} (structureSheaf S))
    (g : A ⟶ B) (Z : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj)) :
    Function.Bijective (fun k : moduleRestrictionSheaf M A ⟶ Z ↦ moduleComparisonSheaf M g ≫ k) ↔
      Function.Bijective (fmapComp.{u} M g Z) := by
  rw [← (Equiv.bijective ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv
      (moduleRestrictionSheaf M B) Z)).of_comp_iff']
  simp only [Function.comp_def, homEquiv_moduleComparisonSheaf_comp]
  exact Iff.rfl

/-- **The comparison map restricted to an open of the ambient scheme is an isomorphism as soon as
composition with the `f`-map is bijective at every direct image from that open.** -/
theorem isIso_pushforward_restrictImage_moduleComparisonSheaf
    (M : SheafOfModules.{u} (structureSheaf S)) (g : A ⟶ B)
    (W : A.obj.thickening.target.scheme.Opens)
    (h : ∀ Z₀ : SheafOfModules.{u} (Thickening.ringRestrictionSheaf (A.restrictOpen W).obj),
      Function.Bijective (fmapComp.{u} M g ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap (A.restrictOpenHom W).hom)).obj Z₀))) :
    IsIso ((SheafOfModules.pushforward.{u} (Thickening.restrictImageHom A.obj W)).map
      (moduleComparisonSheaf M g)) := by
  refine isIso_of_coyoneda_map_bijective _ fun Z₀ ↦ ?_
  have hA := Thickening.bijective_restrictImageTranspose A.obj W (moduleRestrictionSheaf M A) Z₀
  have hB := Thickening.bijective_restrictImageTranspose A.obj W
    ((SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).obj
      (moduleRestrictionSheaf M B)) Z₀
  have hsq : (Thickening.restrictImageTranspose A.obj W
          ((SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).obj
            (moduleRestrictionSheaf M B)) Z₀) ∘
        (fun k ↦ (SheafOfModules.pushforward.{u} (Thickening.restrictImageHom A.obj W)).map
          (moduleComparisonSheaf M g) ≫ k) =
      (fun k ↦ moduleComparisonSheaf M g ≫ k) ∘
        (Thickening.restrictImageTranspose A.obj W (moduleRestrictionSheaf M A) Z₀) :=
    funext fun k ↦ Thickening.restrictImageTranspose_comp A.obj W
      (moduleComparisonSheaf M g) Z₀ k
  refine (hB.of_comp_iff' _).1 ?_
  rw [hsq]
  exact ((bijective_comp_moduleComparisonSheaf_iff M g _).2 (h Z₀)).comp hA

/-- **The crystal condition at a morphism of `Cris(X/S)` is Zariski-local on the ambient scheme of
its source.** -/
theorem isIso_moduleComparisonSheaf_of_isOpenCover (M : SheafOfModules.{u} (structureSheaf S))
    (g : A ⟶ B) {ι : Type*} (W : ι → A.obj.thickening.target.scheme.Opens) (hW : IsOpenCover W)
    (h : ∀ (i : ι) (Z₀ : SheafOfModules.{u}
        (Thickening.ringRestrictionSheaf (A.restrictOpen (W i)).obj)),
      Function.Bijective (fmapComp.{u} M g ((SheafOfModules.pushforward.{u}
        (Thickening.ringRestrictionSheafFMap (A.restrictOpenHom (W i)).hom)).obj Z₀))) :
    IsIso (moduleComparisonSheaf M g) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop
    ((Opens.coversTop_iff _ W).mpr hW) _ fun i W' p ↦ ?_
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_congr _
    (congrArg op (Thickening.restrictOpenHom_image_preimage A.obj (W i) (leOfHom p))) ?_
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
    (Thickening.restrictImageHom A.obj (W i)) _
    (isIso_pushforward_restrictImage_moduleComparisonSheaf M g (W i) (h i))
    (op ((A.restrictOpenHom (W i)).hom.targetHom.hom ⁻¹ᵁ W'))

end Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **Stacks Project, Tag 07IT, the implication (1) ⇒ (2)(b): a quasi-coherent sheaf of
`𝒪_{X/S}`-modules on the small crystalline site is a crystal in `𝒪_{X/S}`-modules.**

For a morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` the comparison map
`c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules is an isomorphism.  This is the source's
argument, with its opening reduction "it suffices to prove (a) and (b) Zariski locally" carried
out: quasi-coherence gives, around every point of `T'`, an open `V` on whose restriction
`(U' ∩ V, V, δ'|_V)` the module has a global presentation
(`Crystalline.GlobalCrystallineSituation.SmallSite.exists_hasGlobalPresentation_restrictOpen`), the
restrictions of `f` over those opens cover `T`, and over each of them the source's computation
applies on the localised site `Cris(X/S)/(U' ∩ V, V, δ'|_V)`, by
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
`.isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target`.  The comparison maps of the
structure morphisms of the two restrictions are isomorphisms, those morphisms being Cartesian open
immersions, so the `f`-map cocycle
(`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.fmapComp_comp`) transfers
bijectivity of the `f`-map composition to the direct images from the members of the cover, and
invertibility of `c_f` follows because it is Zariski-local on `T`. -/
@[stacks 07IT "the implication (1) ⇒ (2)(b) on the small site Cris(X/S): a quasi-coherent sheaf of
  𝒪_{X/S}-modules is a crystal in 𝒪_{X/S}-modules, the crystal condition being read with the
  comparison maps of sheaves of modules.  The same implication on the big site CRIS(X/S), and the
  implication (1) ⇒ (2)(a) on each of the two sites, carry this tag separately.  The converse
  (2) ⇒ (1) is a separate statement"]
theorem isSheafCrystal_of_isQuasicoherentOnSite
    (M : SheafOfModules.{u} (structureSheaf S)) (hM : M.IsQuasicoherentOnSite) :
    IsSheafCrystal M := by
  choose V hxV hV using exists_hasGlobalPresentation_restrictOpen M hM
  intro A B g
  refine CohomologyRestriction.isIso_moduleComparisonSheaf_of_isOpenCover M g
    (fun x : B.obj.thickening.target.scheme ↦ g.hom.targetHom.hom ⁻¹ᵁ V B x) ?_ ?_
  · exact eq_top_iff.2 fun y _ ↦
      Opens.mem_iSup.2 ⟨g.hom.targetHom.hom.base y, hxV B (g.hom.targetHom.hom.base y)⟩
  · intro x Z₀
    refine CohomologyRestriction.bijective_fmapComp_pushforward_of_comm M
      (CrystallineThickening.restrictOpenMap_restrictOpenHom g (V B x)).symm Z₀ ?_ ?_ ?_
    · exact (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1
        (CohomologyRestriction.isIso_moduleComparisonSheaf_restrictOpenHom M A _) Z₀
    · exact (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1
        (CohomologyRestriction.isIso_moduleComparisonSheaf_of_hasGlobalPresentation_target M
          (hV B x) _) Z₀
    · exact (CohomologyRestriction.isIso_moduleComparisonSheaf_iff_bijective_fmapComp M _).1
        (CohomologyRestriction.isIso_moduleComparisonSheaf_restrictOpenHom M B _) _

end Crystalline.GlobalCrystallineSituation.SmallSite

end
