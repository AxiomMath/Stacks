module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism

/-!
# Locally quasi-finite morphisms out of an affine formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
presheaves on the big fppf site of `S`. If `X` is an affine formal algebraic space and `f` is
representable by algebraic spaces and locally quasi-finite, then `f` is representable by schemes.

## Main definitions

* `AlgebraicGeometry.FormalSpace.liftedSheaf`: a sheaf of `Type u` regarded as a sheaf of
  `Type (u + 1)` by lifting its values.
* `AlgebraicGeometry.FormalSpace.presheafMapOfLiftedSheafification`: the morphism of presheaves
  of `Type u` underlying a morphism between the sheafified universe lifts of two sheaves.

## Main results

* `AlgebraicGeometry.FormalSpace.isRepresentable_of_isAffineFormalAlgebraicSpace_of_jointlyMono`:
  an algebraic space with a locally quasi-finite morphism to a representable sheaf and a morphism
  to an affine formal algebraic space, jointly monic, is representable.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isAffineFormalAlgebraicSpace`: a
  locally quasi-finite morphism out of an affine formal algebraic space which is representable by
  algebraic spaces is representable by schemes.

## Implementation notes

An affine formal algebraic space is a sheaf of `Type (u + 1)`, whereas algebraic spaces and their
morphism properties are formulated for presheaves of `Type u`. So `X` is a sheaf of `Type u`, and
the hypothesis that it is an affine formal algebraic space is imposed on the sheaf obtained from
it by lifting its values one universe up.

## References

* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Descending a morphism of sheafified universe lifts -/

/-- A sheaf of `Type u` regarded as a sheaf of `Type (u + 1)` by lifting its values. -/
abbrev liftedSheaf {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf J F) : Sheaf J (Type (u + 1)) :=
  ⟨F ⋙ uliftFunctor.{u + 1, u},
    (isSheaf_iff_isSheaf_of_type J _).2
      (Presieve.isSheaf_comp_uliftFunctor J
        ((isSheaf_iff_isSheaf_of_type J F).1 hF))⟩

/-- A morphism between the sheafified universe lifts of two sheaves of `Type u` comes from a
morphism of the original presheaves. -/
noncomputable def presheafMapOfLiftedSheafification
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))]
    {F G : Cᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf J F) (hG : Presheaf.IsSheaf J G)
    (α : (presheafToSheaf J (Type (u + 1))).obj (F ⋙ uliftFunctor.{u + 1, u}) ⟶
      (presheafToSheaf J (Type (u + 1))).obj (G ⋙ uliftFunctor.{u + 1, u})) : F ⟶ G := by
  let SF := liftedSheaf J hF
  let SG := liftedSheaf J hG
  let eF : SF ≅ (presheafToSheaf J (Type (u + 1))).obj SF.obj :=
    asIso ((sheafificationNatIso J (Type (u + 1))).hom.app SF)
  let eG : SG ≅ (presheafToSheaf J (Type (u + 1))).obj SG.obj :=
    asIso ((sheafificationNatIso J (Type (u + 1))).hom.app SG)
  let β : SF ⟶ SG := eF.hom ≫ α ≫ eG.inv
  exact (fullyFaithfulULiftFunctor.whiskeringRight Cᵒᵖ).preimage β.hom

/-- Naturality of the sheafification isomorphism with respect to a morphism of sheaves. -/
private lemma sheafificationNatIso_hom_app_comp
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))] {A B : Sheaf J (Type (u + 1))} (β : A ⟶ B) :
    (sheafificationNatIso J (Type (u + 1))).hom.app A ≫
        (presheafToSheaf J (Type (u + 1))).map β.hom =
      β ≫ (sheafificationNatIso J (Type (u + 1))).hom.app B := by
  simpa [Functor.comp_map] using ((sheafificationNatIso J (Type (u + 1))).hom.naturality β).symm

/-- Sheafifying the universe lift of `presheafMapOfLiftedSheafification J hF hG α` gives back
`α`. -/
lemma presheafMapOfLiftedSheafification_spec
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))]
    {F G : Cᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf J F) (hG : Presheaf.IsSheaf J G)
    (α : (presheafToSheaf J (Type (u + 1))).obj (F ⋙ uliftFunctor.{u + 1, u}) ⟶
      (presheafToSheaf J (Type (u + 1))).obj (G ⋙ uliftFunctor.{u + 1, u})) :
    (presheafToSheaf J (Type (u + 1))).map
        (Functor.whiskerRight (presheafMapOfLiftedSheafification J hF hG α)
          uliftFunctor.{u + 1, u}) = α := by
  let SF := liftedSheaf J hF
  let SG := liftedSheaf J hG
  let eF : SF ≅ (presheafToSheaf J (Type (u + 1))).obj SF.obj :=
    asIso ((sheafificationNatIso J (Type (u + 1))).hom.app SF)
  let eG : SG ≅ (presheafToSheaf J (Type (u + 1))).obj SG.obj :=
    asIso ((sheafificationNatIso J (Type (u + 1))).hom.app SG)
  let β : SF ⟶ SG := eF.hom ≫ α ≫ eG.inv
  let f := presheafMapOfLiftedSheafification J hF hG α
  have hf : Functor.whiskerRight f uliftFunctor.{u + 1, u} = β.hom :=
    (fullyFaithfulULiftFunctor.whiskeringRight Cᵒᵖ).map_preimage _
  have hcomp : eF.hom ≫ (presheafToSheaf J (Type (u + 1))).map β.hom = β ≫ eG.hom :=
    sheafificationNatIso_hom_app_comp J β
  rw [hf, ← cancel_epi eF.hom, hcomp]
  simp [β]

/-- Sheafifying the universe lift is faithful on morphisms of sheaves of `Type u`. -/
lemma eq_of_liftedSheafification_map_eq
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (u + 1))]
    {F G : Cᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf J F) (hG : Presheaf.IsSheaf J G)
    {f g : F ⟶ G}
    (h : (presheafToSheaf J (Type (u + 1))).map
        (Functor.whiskerRight f uliftFunctor.{u + 1, u}) =
      (presheafToSheaf J (Type (u + 1))).map
        (Functor.whiskerRight g uliftFunctor.{u + 1, u})) : f = g := by
  let SF := liftedSheaf J hF
  let SG := liftedSheaf J hG
  let eF : SF ≅ (presheafToSheaf J (Type (u + 1))).obj SF.obj :=
    asIso ((sheafificationNatIso J (Type (u + 1))).hom.app SF)
  let eG : SG ≅ (presheafToSheaf J (Type (u + 1))).obj SG.obj :=
    asIso ((sheafificationNatIso J (Type (u + 1))).hom.app SG)
  let fS : SF ⟶ SG := ObjectProperty.homMk (Functor.whiskerRight f uliftFunctor.{u + 1, u})
  let gS : SF ⟶ SG := ObjectProperty.homMk (Functor.whiskerRight g uliftFunctor.{u + 1, u})
  have hf : eF.hom ≫ (presheafToSheaf J (Type (u + 1))).map fS.hom = fS ≫ eG.hom :=
    sheafificationNatIso_hom_app_comp J fS
  have hg : eF.hom ≫ (presheafToSheaf J (Type (u + 1))).map gS.hom = gS ≫ eG.hom :=
    sheafificationNatIso_hom_app_comp J gS
  have hfg : fS = gS :=
    (cancel_mono eG.hom).1 (by rw [← hf, ← hg]; exact congrArg (eF.hom ≫ ·) h)
  exact (fullyFaithfulULiftFunctor.whiskeringRight Cᵒᵖ).map_injective
    (congrArg (fun k => k.hom) hfg)

/-! ### Auxiliary results -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_quasiFiniteRepresentable :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_quasiFiniteRepresentable
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Binary products of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasBinaryProducts_presheaf_quasiFiniteRepresentable :
    HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasBinaryProduct_presheaf_quasiFiniteRepresentable
    (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : HasBinaryProduct X Y :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_quasiFiniteRepresentable
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- A monomorphism of algebraic spaces over `S` into a representable presheaf which is
locally quasi-finite has representable source. -/
private theorem isRepresentable_of_mono_isLocallyQuasiFinite_to_stage
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (V : BigFppfOver B S hS) (m : W ⟶ yoneda.obj V)
    (hm : Space.IsLocallyQuasiFinite B S hS m) (hmono : Mono m) : W.IsRepresentable :=
  Space.isRepresentable_of_locallyQuasiFinite_separated B S hS W (yoneda.obj V) hW
    (isAlgebraicSpace_yoneda B S hS V) m inferInstance hm
    (Space.isSeparated_of_mono B S hS m hmono)

/-- An open immersion of algebraic spaces over `S` is an immersion. -/
private theorem isImmersion_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : Space.IsOpenImmersion B S hS f) : Space.IsImmersion B S hS f := by
  refine MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)) ?_ _ hf
  intro A A' g hg
  let _ : AlgebraicGeometry.IsOpenImmersion _ := hg
  show AlgebraicGeometry.IsImmersion _
  exact inferInstance

/-- A morphism from a quasi-compact algebraic space over `S` to an affine formal algebraic
space factors through an object of the site. -/
private theorem exists_stage_factor_presheaf
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hX : IsAffineFormalAlgebraicSpace B S hS
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (X.1 ⋙ uliftFunctor.{u + 1, u})))
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W)
    (hWqc : Space.IsQuasiCompactSpace B S hS W) (φ : W ⟶ X.1) :
    ∃ (U : BigFppfOver B S hS) (a : W ⟶ yoneda.obj U) (p : yoneda.obj U ⟶ X.1),
      a ≫ p = φ := by
  classical
  let J := BigFppfOver.topology B S hS
  let Psh := presheafToSheaf J (Type (u + 1))
  obtain ⟨I, _, _, _, D, hD, ⟨e⟩⟩ := hX.2
  let formalX := Psh.obj (X.1 ⋙ uliftFunctor.{u + 1, u})
  let stages := D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  let hWsheaf := hW.isSheaf
  let φsheaf := Psh.map (Functor.whiskerRight φ uliftFunctor.{u + 1, u})
  obtain ⟨i, g, hfac⟩ := exists_factor_through_thickening' B S hS I D (fun _ _ g ↦ (hD g).1)
    formalX e W hWqc φsheaf
  let U := (BigAffineFppf.inclusion B S hS).obj (D.obj i)
  have hUsheaf : Presheaf.IsSheaf J (yoneda.obj U) :=
    (isAlgebraicSpace_yoneda B S hS U).isSheaf
  let α : Psh.obj (W ⋙ uliftFunctor.{u + 1, u}) ⟶
      Psh.obj (yoneda.obj U ⋙ uliftFunctor.{u + 1, u}) := by
    simpa only [Sheaf.sheafifiedYoneda_obj, CategoryTheory.uliftYoneda,
      Functor.whiskeringRight_obj_obj, Functor.comp_obj] using g
  let a := presheafMapOfLiftedSheafification J hWsheaf hUsheaf α
  have haSpec : Psh.map (Functor.whiskerRight a uliftFunctor.{u + 1, u}) = α :=
    presheafMapOfLiftedSheafification_spec J hWsheaf hUsheaf α
  let αstage : Psh.obj (yoneda.obj U ⋙ uliftFunctor.{u + 1, u}) ⟶ formalX := by
    simpa only [stages, U, Sheaf.sheafifiedYoneda_obj, CategoryTheory.uliftYoneda,
      Functor.whiskeringRight_obj_obj, Functor.comp_obj] using (colimit.ι stages i ≫ e.inv)
  let p := presheafMapOfLiftedSheafification J hUsheaf X.property αstage
  have hpSpec : Psh.map (Functor.whiskerRight p uliftFunctor.{u + 1, u}) = αstage :=
    presheafMapOfLiftedSheafification_spec J hUsheaf X.property αstage
  refine ⟨U, a, p, eq_of_liftedSheafification_map_eq J hWsheaf X.property ?_⟩
  calc
    Psh.map (Functor.whiskerRight (a ≫ p) uliftFunctor.{u + 1, u}) =
        Psh.map (Functor.whiskerRight a uliftFunctor.{u + 1, u}) ≫
          Psh.map (Functor.whiskerRight p uliftFunctor.{u + 1, u}) := by simp
    _ = α ≫ αstage := by rw [haSpec, hpSpec]
    _ = φsheaf := hfac

/-! ### Representability -/

/-- Let `X` be a sheaf of `Type u` on the big fppf site
of `S` whose sheafified universe lift is an affine formal algebraic space, let `T` be an object
of the site, and let `P` be an algebraic space over `S` carrying a locally quasi-finite morphism
`qP` to the sheaf represented by `T` and a morphism `rP` to `X`, the two being jointly monic.
Then `P` is representable. -/
theorem isRepresentable_of_isAffineFormalAlgebraicSpace_of_jointlyMono
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (hX : IsAffineFormalAlgebraicSpace B S hS
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (X.1 ⋙ uliftFunctor.{u + 1, u})))
    {T : BigFppfOver B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (qP : P ⟶ yoneda.obj T) (rP : P ⟶ X.1)
    (hjm : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g₁ g₂ : Z ⟶ P),
      g₁ ≫ qP = g₂ ≫ qP → g₁ ≫ rP = g₂ ≫ rP → g₁ = g₂)
    (hlqf : Space.IsLocallyQuasiFinite B S hS qP) :
    P.IsRepresentable := by
  obtain ⟨I, W, hcover, hAtlas⟩ := Space.exists_zariski_cover_affine_etale_atlas B S hS P hP
  apply Space.isRepresentable_of_isZariskiCover B S hS P hP I W hcover
  intro i
  let Wi := W i
  obtain ⟨A, atlas, _V₀, hAaff, hatlasSurj, hatlasEtale, _hV₀aff, _hbase⟩ := hAtlas i
  have hWiOpen : Space.IsOpenSubspace B S hS Wi := hcover.1 i
  have hWi : IsAlgebraicSpace B S hS Wi.toFunctor := hWiOpen.1
  have hWiQc : Space.IsQuasiCompactSpace B S hS Wi.toFunctor := by
    refine ⟨A, atlas, ?_, hatlasSurj, ?_⟩
    · let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hAaff
      infer_instance
    · exact (Space.isEtale_iff_presheaf_of_yoneda B S hS atlas).2 hatlasEtale
  let φ := Wi.ι ≫ rP
  obtain ⟨U, a, p, hstage⟩ :=
    exists_stage_factor_presheaf B S hS X hX Wi.toFunctor hWi hWiQc φ
  let b := Wi.ι ≫ qP
  let C := BigFppfOver B S hS
  let _ : HasPullbacks B.Schemes := inferInstance
  let _ : HasPullbacks C := inferInstance
  let _ : HasBinaryProducts C := Over.ConstructProducts.over_binaryProduct_of_pullback
  let V := U ⨯ T
  let e : yoneda.obj V ≅ yoneda.obj U ⨯ yoneda.obj T := asIso (prodComparison yoneda U T)
  let m : Wi.toFunctor ⟶ yoneda.obj V := prod.lift a b ≫ e.inv
  have hmfst : m ≫ yoneda.map prod.fst = a := by
    simp [m, e, Category.assoc, inv_prodComparison_map_fst]
  have hmsnd : m ≫ yoneda.map prod.snd = b := by
    simp [m, e, Category.assoc, inv_prodComparison_map_snd]
  have hmMono : Mono m := by
    refine ⟨fun g₁ g₂ hEq => ?_⟩
    have h₁ : g₁ ≫ a = g₂ ≫ a := by
      simpa [Category.assoc, hmfst] using congrArg (fun k => k ≫ yoneda.map prod.fst) hEq
    have h₂ : g₁ ≫ b = g₂ ≫ b := by
      simpa [Category.assoc, hmsnd] using congrArg (fun k => k ≫ yoneda.map prod.snd) hEq
    apply (cancel_mono Wi.ι).1
    refine hjm _ _ ?_ ?_
    · simpa [b, Category.assoc] using h₂
    · calc
        (g₁ ≫ Wi.ι) ≫ rP = (g₁ ≫ a) ≫ p := by
          simpa [φ, Category.assoc] using congrArg (fun z => g₁ ≫ z) hstage.symm
        _ = (g₂ ≫ a) ≫ p := by rw [h₁]
        _ = (g₂ ≫ Wi.ι) ≫ rP := by
          simpa [φ, Category.assoc] using congrArg (fun z => g₂ ≫ z) hstage
  have hWiOpenLft : Space.IsLocallyOfFiniteType B S hS Wi.ι :=
    Space.isLocallyOfFiniteType_of_isImmersion B S hS Wi.ι
      (isImmersion_of_isOpenImmersion B S hS hWiOpen.2)
  have hWiOpenLqf : Space.IsLocallyQuasiFinite B S hS Wi.ι :=
    Space.isLocallyQuasiFinite_of_mono B S hS hWi hP Wi.ι inferInstance hWiOpenLft
  have hWTLqf : Space.IsLocallyQuasiFinite B S hS (Wi.ι ≫ qP) :=
    Space.isLocallyQuasiFinite_comp B S hS hWi hP (isAlgebraicSpace_yoneda B S hS T) Wi.ι qP
      hWiOpenLqf hlqf
  have hmLqf : Space.IsLocallyQuasiFinite B S hS m :=
    Space.isLocallyQuasiFinite_of_comp B S hS hWi (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS T) m (yoneda.map prod.snd)
      (by simpa [hmsnd, b] using hWTLqf)
  exact isRepresentable_of_mono_isLocallyQuasiFinite_to_stage B S hS hWi V m hmLqf hmMono

/-- Let `S` be a scheme contained in a big fppf site `B` and let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`. If `X` is an affine
formal algebraic space and `f` is representable by algebraic spaces and locally quasi-finite,
then `f` is representable by schemes.

`X` is a sheaf of `Type u`, the universe of the schemes, and the hypothesis that it is an
affine formal algebraic space is imposed on the sheaf obtained from it by lifting its values
one universe up. Local quasi-finiteness of a morphism which is only representable by
algebraic spaces is the assertion that each of its base changes along a scheme-valued point
of the target, an algebraic space over `S`, is locally quasi-finite over that point. -/
@[stacks 0AIG]
theorem relativelyRepresentable_of_isAffineFormalAlgebraicSpace
    (X : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : X.1 ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS
      ((presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        (X.1 ⋙ uliftFunctor.{u + 1, u})))
    (hf : Space.IsRepresentableByAlgebraicSpaces B S hS f)
    (hlqf : ∀ (T : BigFppfOver B S hS) (ξ : yoneda.obj T ⟶ Y),
      Space.IsLocallyQuasiFinite B S hS (pullback.fst ξ f)) :
    yoneda.relativelyRepresentable f := by
  rw [yoneda_relativelyRepresentable_iff_pullback_representable]
  intro T ξ
  let ξ' := yonedaEquiv.symm ξ
  exact isRepresentable_of_isAffineFormalAlgebraicSpace_of_jointlyMono B S hS X hX (hf T ξ')
    (pullback.fst ξ' f) (pullback.snd ξ' f) (fun _ _ h₁ h₂ => pullback.hom_ext h₁ h₂)
    (hlqf T ξ')

end AlgebraicGeometry.FormalSpace

end
