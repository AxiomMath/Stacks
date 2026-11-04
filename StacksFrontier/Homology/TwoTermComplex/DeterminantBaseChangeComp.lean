module

public import StacksFrontier.Homology.TwoTermComplex.DeterminantBaseChange
public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom
import all StacksFrontier.Homology.TwoTermComplex.DeterminantFunctor

/-!
# The base change map of determinants along a composite of ring maps

For ring maps `f : R → S` and `g : S → T`, the base change map of determinants along `g ∘ f` is the
composite of the base change maps along `f` and along `g`, the isomorphism
`T ⊗ᴸ_S (S ⊗ᴸ_R K) ≅ T ⊗ᴸ_R K` being the composition isomorphism of derived extension of
scalars.

## Main results

* `TwoTermDeterminant.baseChangeMap_comp`: the base change map along `g ∘ f` is the composite.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

namespace TwoTermDeterminant

attribute [local instance] HasDerivedCategory.standard

attribute [local irreducible] determinantTransport

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- The composition isomorphism of derived extension of scalars. -/
abbrev compIso (X : DerivedCategory (ModuleCat.{u} R)) :
    (Lext g).obj ((Lext f).obj X) ≅ (Lext (g.comp f)).obj X :=
  (PseudoCoherence.derivedExtensionScalarsComp.{u, u} f g).app X

/-- The composition isomorphism of termwise extension of scalars on complexes. -/
def escompIso (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    bcComplex (g.comp f) P ≅ bcComplex g (bcComplex f P) :=
  (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (ComplexShape.up ℤ)).app P

/-- The composition isomorphism `escompIso` sends `1 ⊗ m` to `1 ⊗ (1 ⊗ m)`. -/
theorem escompIso_hom_apply (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) (m : P.X i) :
    ((escompIso f g P).hom.f i) (bcUnit (g.comp f) P i m) =
      bcUnit g (bcComplex f P) i (bcUnit f P i m) :=
  ModuleCat.extendScalarsComp_hom_app_one_tmul f g (P.X i) m

/-- The composition isomorphism of derived extension of scalars is compatible with the comparison
maps `cmpA` and the termwise composition isomorphism `escompIso`. -/
theorem compIso_hom_cmpA (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (compIso f g (DerivedCategory.Q.obj P)).hom ≫ cmpA (g.comp f) P =
      (Lext g).map (cmpA f P) ≫ cmpA g (bcComplex f P) ≫
        DerivedCategory.Q.map (escompIso f g P).inv := by
  rw [Iso.app_hom, PseudoCoherence.derivedExtensionScalarsComp_hom]
  exact PseudoCoherence.derivedExtensionScalarsCompHom_fac.{u, u} f g P

/-- The `R`-module structure on a twofold extension of scalars. -/
instance bcComplex₂Module (P : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module R ((bcComplex g (bcComplex f P)).X i) :=
  Module.compHom _ (g.comp f)

variable {K L M : DerivedCategory (ModuleCat.{u} R)}

/-- The determinant isomorphism of the surjective quasi-isomorphism induced by `escompIso` sends
the base change of `x` along `g ∘ f` to its iterated base change along `f` and then `g`. -/
private theorem surjectiveDeterminantEquiv_escomp_bcLine (P : TwoTermPresentation K)
    (hs : ((P.bcPresentation (g.comp f)).hom ((P.bcPresentation f).bcPresentation g)
      (escompIso f g P.complex).hom).IsDegreewiseSurjective)
    (hq : ((P.bcPresentation (g.comp f)).hom ((P.bcPresentation f).bcPresentation g)
      (escompIso f g P.complex).hom).IsQuasiIso) (x : presentationDeterminant P) :
    surjectiveDeterminantEquiv (P.bcPresentation (g.comp f)) ((P.bcPresentation f).bcPresentation g)
        (escompIso f g P.complex).hom hs hq (bcLine (g.comp f) P x) =
      bcLine g (P.bcPresentation f) (bcLine f P x) := by
  let := P.finite (-1)
  let := P.projective (-1)
  let := P.finite 0
  let := P.projective 0
  let := (P.bcPresentation f).finite (-1)
  let := (P.bcPresentation f).projective (-1)
  let := (P.bcPresentation f).finite 0
  let := (P.bcPresentation f).projective 0
  let := (P.bcPresentation (g.comp f)).finite (-1)
  let := (P.bcPresentation (g.comp f)).projective (-1)
  let := (P.bcPresentation (g.comp f)).finite 0
  let := (P.bcPresentation (g.comp f)).projective 0
  let := ((P.bcPresentation f).bcPresentation g).finite (-1)
  let := ((P.bcPresentation f).bcPresentation g).projective (-1)
  let := ((P.bcPresentation f).bcPresentation g).finite 0
  let := ((P.bcPresentation f).bcPresentation g).projective 0
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := isScalarTower_bc f P.complex (-1)
  let := isScalarTower_bc f P.complex 0
  let := isScalarTower_bc (g.comp f) P.complex (-1)
  let := isScalarTower_bc (g.comp f) P.complex 0
  let := isScalarTower_bc g (bcComplex f P.complex) (-1)
  let := isScalarTower_bc g (bcComplex f P.complex) 0
  have hRT (i : ℤ) : IsScalarTower R T ((bcComplex g (bcComplex f P.complex)).X i) :=
    ⟨fun r t x => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have hRS (i : ℤ) : IsScalarTower R S ((bcComplex g (bcComplex f P.complex)).X i) :=
    ⟨fun r s x => by
      show (g (f r * s)) • x = g (f r) • (g s • x)
      rw [map_mul, mul_smul]⟩
  have h₁ := isBaseChange_bcUnit f P.complex (-1)
  have h₀ := isBaseChange_bcUnit f P.complex 0
  have k₁ := isBaseChange_bcUnit g (bcComplex f P.complex) (-1)
  have k₀ := isBaseChange_bcUnit g (bcComplex f P.complex) 0
  have hc := TwoTermComplex.detLineMap_comp h₁ h₀ k₁ k₀ (P.complex.d (-1) 0).hom
    ((bcComplex f P.complex).d (-1) 0).hom ((bcComplex g (bcComplex f P.complex)).d (-1) 0).hom x
  have ha : (P.hom P (𝟙 P.complex)).IsDegreewiseSurjective :=
    ⟨Function.surjective_id, Function.surjective_id⟩
  have hqa := twoTerm_quasiIso_of_homotopyEquiv P P (HomotopyEquiv.refl _)
  have hstar := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_isBaseChange
    (P.complex.d (-1) 0).hom (P.complex.d (-1) 0).hom
    ((bcComplex (g.comp f) P.complex).d (-1) 0).hom
    ((bcComplex g (bcComplex f P.complex)).d (-1) 0).hom
    (isBaseChange_bcUnit (g.comp f) P.complex (-1)) (isBaseChange_bcUnit (g.comp f) P.complex 0)
    (h₁.comp k₁) (h₀.comp k₀) (LinearMap.ext fun _ => rfl) (P.hom P (𝟙 P.complex))
    ((P.bcPresentation (g.comp f)).hom ((P.bcPresentation f).bcPresentation g)
      (escompIso f g P.complex).hom)
    (LinearMap.ext fun m => escompIso_hom_apply f g P.complex (-1) m)
    (LinearMap.ext fun m => escompIso_hom_apply f g P.complex 0 m) ha hqa hs hq x
  have hid := LinearEquiv.congr_fun (isoSurjectiveDeterminant_id P) x
  exact hstar.trans ((congrArg _ hid).trans hc)

/-- The map of presentations induced by `escompIso` is surjective in each degree. -/
theorem isDegreewiseSurjective_escomp (P : TwoTermPresentation K) :
    ((P.bcPresentation (g.comp f)).hom ((P.bcPresentation f).bcPresentation g)
      (escompIso f g P.complex).hom).IsDegreewiseSurjective :=
  ⟨((HomologicalComplex.eval _ _ (-1)).mapIso (escompIso f g P.complex)).toLinearEquiv.surjective,
    ((HomologicalComplex.eval _ _ 0).mapIso (escompIso f g P.complex)).toLinearEquiv.surjective⟩

/-- The composite of the comparison maps along `f` and along `g` is the composition isomorphism
followed by the comparison map along `g ∘ f` and the termwise composition isomorphism. -/
theorem cmpA_comp_cmpA (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (Lext g).map (cmpA f P) ≫ cmpA g (bcComplex f P) =
      (compIso f g (DerivedCategory.Q.obj P)).hom ≫ cmpA (g.comp f) P ≫
        DerivedCategory.Q.map (escompIso f g P).hom := by
  rw [reassoc_of% (compIso_hom_cmpA f g P), ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

section Core

variable {N₁ : DerivedCategory (ModuleCat.{u} S)} {N₂ : DerivedCategory (ModuleCat.{u} T)}

/-- The isomorphism between the presentations of the base change along `g ∘ f` and of the iterated
base change, obtained from their structure isomorphisms, is the image of `escompIso`. -/
theorem comp_iso_eq (P : TwoTermPresentation K) (e₁ : (Lext f).obj K ≅ N₁)
    (e₂ : (Lext g).obj N₁ ≅ N₂) :
    ((P.bcPresentation (g.comp f)).ofIso
        ((compIso f g K).symm ≪≫ (Lext g).mapIso e₁ ≪≫ e₂)).iso.symm ≪≫
        Iso.refl _ ≪≫ ((((P.bcPresentation f).ofIso e₁).bcPresentation g).ofIso e₂).iso =
      asIso (DerivedCategory.Q.map (escompIso f g P.complex).hom) := by
  have key : ((P.bcPresentation (g.comp f)).ofIso
      ((compIso f g K).symm ≪≫ (Lext g).mapIso e₁ ≪≫ e₂)).iso.hom ≫
      DerivedCategory.Q.map (escompIso f g P.complex).hom =
      ((((P.bcPresentation f).ofIso e₁).bcPresentation g).ofIso e₂).iso.hom := by
    have hn := (PseudoCoherence.derivedExtensionScalarsComp.{u, u} f g).hom.naturality P.iso.hom
    have hk := cmpA_comp_cmpA f g P.complex
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, comparisonIso, asIso_hom, Category.assoc,
      Functor.map_comp, compIso, Iso.app_hom, Functor.comp_map] at hn hk ⊢
    rw [hk, reassoc_of% hn]
  ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_hom, Iso.refl_hom, Category.id_comp, ← key,
    Iso.inv_hom_id_assoc, asIso_hom]

/-- Transport of determinants along the image of `escompIso` sends the base change of `y` along
`g ∘ f` to its iterated base change along `f` and then `g`. -/
theorem comp_core (P : TwoTermPresentation K) (e₁ : (Lext f).obj K ≅ N₁)
    (e₂ : (Lext g).obj N₁ ≅ N₂) (y : presentationDeterminant P) :
    determinantTransport
        ((P.bcPresentation (g.comp f)).ofIso ((compIso f g K).symm ≪≫ (Lext g).mapIso e₁ ≪≫ e₂))
        ((((P.bcPresentation f).ofIso e₁).bcPresentation g).ofIso e₂)
        (asIso (DerivedCategory.Q.map (escompIso f g P.complex).hom)) (bcLine (g.comp f) P y) =
      bcLine g (P.bcPresentation f) (bcLine f P y) := by
  have i1 := determinantTransport_ofIso_left' (P.bcPresentation (g.comp f))
    ((((P.bcPresentation f).ofIso e₁).bcPresentation g).ofIso e₂)
    ((compIso f g K).symm ≪≫ (Lext g).mapIso e₁ ≪≫ e₂)
    (asIso (DerivedCategory.Q.map (escompIso f g P.complex).hom))
  have i2 := determinantTransport_ofIso_right' (P.bcPresentation (g.comp f))
    (((P.bcPresentation f).ofIso e₁).bcPresentation g) e₂
    (asIso (DerivedCategory.Q.map (escompIso f g P.complex).hom))
  have i3 := determinantTransport_baseChange_withIso_right g (P.bcPresentation (g.comp f))
    (P.bcPresentation f) (e₁.symm ≪≫ (P.bcPresentation f).iso)
    (asIso (DerivedCategory.Q.map (escompIso f g P.complex).hom))
  have i4 := determinantTransport_eq_of_surjective (P.bcPresentation (g.comp f))
    ((P.bcPresentation f).bcPresentation g) (escompIso f g P.complex).hom
    (isDegreewiseSurjective_escomp f g P)
  rw [i1, i2, i3, i4]
  exact surjectiveDeterminantEquiv_escomp_bcLine f g P _ _ y

end Core

section

variable {K : PerfectTwoTermComplex R} {L : PerfectTwoTermComplex S} {M : PerfectTwoTermComplex T}

/-- Elements of the determinant lines of two presentations of `N` that correspond under
`presentationTransport` define the same element of the determinant of `N`. -/
theorem symm_detPresentationIso_eq {T' : Type u} [CommRing T'] (N : PerfectTwoTermComplex T')
    (Q Q' : TwoTermPresentation N.obj) (w : presentationDeterminant Q)
    (w' : presentationDeterminant Q') (h : presentationTransport Q Q' (Iso.refl _) w = w') :
    (detPresentationIso N Q).symm w = (detPresentationIso N Q').symm w' := by
  rw [LinearEquiv.eq_symm_apply, ← h]
  have h5 := presentationTransport_detPresentationIso N Q Q' ((detPresentationIso N Q).symm w)
  rw [LinearEquiv.apply_symm_apply] at h5
  exact h5.symm

/-- **The base change map of determinants along `g ∘ f` is the composite of the base change maps
along `f` and along `g`.** -/
theorem baseChangeMap_comp (e₁ : (Lext f).obj K.obj ≅ L.obj) (e₂ : (Lext g).obj L.obj ≅ M.obj)
    (x : ((det R).obj ⟨K⟩).of.obj) :
    baseChangeMap (g.comp f) K M ((compIso f g K.obj).symm ≪≫ (Lext g).mapIso e₁ ≪≫ e₂) x =
      baseChangeMap g L M e₂ (baseChangeMap f K L e₁ x) := by
  let P := presentation R K
  let Q₁ := (P.bcPresentation f).ofIso e₁
  let ec := (compIso f g K.obj).symm ≪≫ (Lext g).mapIso e₁ ≪≫ e₂
  let Q₃ := (P.bcPresentation (g.comp f)).ofIso ec
  let Q₂ := (Q₁.bcPresentation g).ofIso e₂
  have lhs : baseChangeMap (g.comp f) K M ec x =
      (detPresentationIso M Q₃).symm (bcLine (g.comp f) P (detPresentationIso K P x)) :=
    baseChangeMapVia_apply _ _ _ _
  have rhs1 : baseChangeMap f K L e₁ x =
      (detPresentationIso L Q₁).symm (bcLine f P (detPresentationIso K P x)) :=
    baseChangeMapVia_apply _ _ _ _
  have rhs2 (z : ((det S).obj ⟨L⟩).of.obj) : baseChangeMap g L M e₂ z =
      (detPresentationIso M Q₂).symm (bcLine g Q₁ (detPresentationIso L Q₁ z)) := by
    rw [baseChangeMap_eq g Q₁ e₂]
    exact baseChangeMapVia_apply _ _ _ _
  rw [lhs, rhs2, rhs1, LinearEquiv.apply_symm_apply]
  refine symm_detPresentationIso_eq M Q₃ Q₂ _ _ ?_
  exact (congrArg (fun a => determinantTransport Q₃ Q₂ a
      (bcLine (g.comp f) P (detPresentationIso K P x)))
    (comp_iso_eq f g P e₁ e₂)).trans (comp_core f g P e₁ e₂ _)

end

end TwoTermDeterminant

end
