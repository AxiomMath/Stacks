module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutRegular
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.StalkResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Spreading out the resolution in the proof of [Stacks, Tag 0EA3]

Assembling `PurityRamification/ResolutionSpreadOut*.lean`: in the proof of [Stacks, Tag 0EA3]
the resolution `W ⟶ Spec(𝒪_{X, x})` is spread out to `b : X' ⟶ U` over an affine open
neighbourhood `U` of `x` with `X' ×_U Spec(𝒪_{X, x}) = W`, and after shrinking `U` the morphism
`b` is proper, projective, an isomorphism over `U \ \overline{\{x\}}`, and `X'` is regular. This
file proves that for any H-projective `g : W ⟶ Spec(𝒪_{X, x})` of finite presentation with `W`
regular, over a locally Noetherian J-2 scheme `X`, with `U \ \overline{\{x\}}` replaced by
`U ∩ V` for any open `V ⊆ X` over whose preimage `g` is an isomorphism.

## Main results

* `AlgebraicGeometry.exists_regular_projective_model_specStalk`
* `AlgebraicGeometry.isJ2_of_locallyOfFiniteType_of_isExcellent`: a scheme locally of finite type
  over an excellent ring is J-2.
* `AlgebraicGeometry.exists_spreadOut_resolution_stalk`: the situation of the proof of
  [Stacks, Tag 0EA3]: an H-projective resolution `W` of `Spec(𝒪_{X, x})` and its spread-out model
  over an affine open neighbourhood `U` of `x`, an isomorphism over `U \ \overline{\{x\}}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The spread-out resolution of the proof of [Stacks, Tag 0EA3].** Let `X` be a locally
Noetherian J-2 scheme, `x ∈ X`, `V ⊆ X` open, and let `g : W ⟶ Spec(𝒪_{X, x})` be H-projective
and of finite presentation, with `W` regular and with base change to the preimage of `V` an
isomorphism. Then `g` is the base change, along `Spec(𝒪_{X, x}) ⟶ U`, of a morphism `Z ⟶ U`
over an affine open neighbourhood `U` of `x` which is of finite presentation, proper and
H-projective, has regular source, and whose base change to `U ∩ V` is an isomorphism. -/
@[ega "IV 8.1.2" "special case"]
theorem exists_regular_projective_model_specStalk (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hJ : X.IsJ2) (x : X) {W : Scheme.{u}} (g : W ⟶ Spec (X.presheaf.stalk x)) [IsProper g]
    (hg : FinitePresentation g) (hproj : IsProjectiveMorphism g) (hW : IsRegular W)
    (V : X.Opens) (hV : IsIso (pullback.snd g ((X.fromSpecStalk x) ⁻¹ᵁ V).ι)) :
    ∃ (j : AffineOpenNhds X x) (Z : Over ((affineOpenNhdsDiagram X x).obj j)),
      FinitePresentation Z.hom ∧ IsProper Z.hom ∧ IsProjectiveMorphism Z.hom ∧
        IsRegular Z.left ∧
        IsIso (pullback.snd Z.hom (Scheme.Opens.ι (X := X) j.obj.1 ⁻¹ᵁ V).ι) ∧
        Nonempty (Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) := by
  let D := affineOpenNhdsDiagram X x
  obtain ⟨j₀, Z₀, hfp₀, hprop₀, ⟨e₀⟩⟩ := exists_isProper_model_specStalk X x g hg
  -- an isomorphism over `U ∩ V`
  obtain ⟨j₁, h₁, hiso₁⟩ := exists_hom_isIso_pullback_snd_model X x g V hV Z₀ hfp₀ e₀
  let Z₁ := (Over.pullback (D.map h₁)).obj Z₀
  let e₁ := specStalkModelShrinkIso X x h₁ e₀
  have hfp₁ : FinitePresentation Z₁.hom := finitePresentation_overPullback_obj _ Z₀ hfp₀
  -- H-projective
  obtain ⟨j₂, h₂, hproj₂⟩ := exists_hom_isProjectiveMorphism_model X x g hproj Z₁ hfp₁ e₁
  let Z₂ := (Over.pullback (D.map h₂)).obj Z₁
  let e₂ := specStalkModelShrinkIso X x h₂ e₁
  have hfp₂ : FinitePresentation Z₂.hom := finitePresentation_overPullback_obj _ Z₁ hfp₁
  have hiso₂ : IsIso (pullback.snd Z₂.hom (Scheme.Opens.ι (X := X) j₂.obj.1 ⁻¹ᵁ V).ι) :=
    isIso_pullback_snd_model_shrink X x V h₂ Z₁.hom hiso₁
  have : IsProper Z₂.hom := isProper_of_isProjectiveMorphism _ hproj₂
  -- regular
  obtain ⟨j₃, h₃, hreg₃⟩ := exists_hom_isRegular_model X hJ x g hW Z₂ e₂
  let Z₃ := (Over.pullback (D.map h₃)).obj Z₂
  refine ⟨j₃, Z₃, finitePresentation_overPullback_obj _ Z₂ hfp₂,
    inferInstanceAs (IsProper (pullback.snd Z₂.hom (D.map h₃))), hproj₂.baseChange _, hreg₃,
    isIso_pullback_snd_model_shrink X x V h₃ Z₂.hom hiso₂,
    ⟨specStalkModelShrinkIso X x h₃ e₂⟩⟩

/-- The J-2 property of a ring is invariant under ring isomorphism. -/
theorem _root_.isJ2_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : IsJ2 R) : IsJ2 S := by
  intro T _ _ _
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra R T := ((algebraMap S T).comp e.toRingHom).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R S := Algebra.FiniteType.of_surjective (Algebra.ofId R S)
    e.surjective
  have : Algebra.FiniteType R T := Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  exact h T

/-- **A scheme locally of finite type over an excellent ring is J-2** ([Stacks, Tags 07QT and
07R4]): an excellent ring is J-2 by definition, so is its spectrum, and J-2 passes to schemes
locally of finite type. -/
@[ega "IV 7.8.3" "more general",
  ega "IV 7.8.6" "(i), (iii), special case",
  ega "IV 7.9.7" "partial", sga "5 I 3.1.1" "special case"]
theorem isJ2_of_locallyOfFiniteType_of_isExcellent {A : Type u} [CommRing A] (hA : IsExcellent A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    haveI : IsNoetherianRing A := hA.1.1
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    X.IsJ2 := by
  have : IsNoetherianRing A := hA.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hS : (Spec (.of A)).IsJ2 := by
    refine Scheme.IsJ2.mk fun Y g _ => ?_
    refine Scheme.isOpen_regularLocus_of_affineJ2_cover
      (fun _ : PUnit.{u + 1} => ⟨⊤, isAffineOpen_top _⟩) (by simp) (fun _ => ?_) g
    exact isJ2_of_ringEquiv (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv hA.1.2.2
  exact Scheme.isJ2_of_locallyOfFiniteType' hS f

/-- **The spread-out resolution in the situation of [Stacks, Tag 0EA3].** Let `A` be excellent,
`f : X ⟶ Spec(A)` locally of finite type, and `x ∈ X` with `𝒪_{X, x}` a normal domain of
dimension two. Then `Spec(𝒪_{X, x})` has an H-projective resolution of singularities
`g : W ⟶ Spec(𝒪_{X, x})`, and `g` is the base change, along `Spec(𝒪_{X, x}) ⟶ U`, of a morphism
`Z ⟶ U` over an affine open neighbourhood `U` of `x` which is of finite presentation, proper and
H-projective, has regular source, and is an isomorphism over `U \ \overline{\{x\}}`. (The
punctured spectrum of `𝒪_{X, x}` is the preimage of `X \ \overline{\{x\}}`, over which `g` is an
isomorphism, `𝒪_{X, x}` being normal of dimension two.) -/
theorem exists_spreadOut_resolution_stalk {A : Type u} [CommRing A] (hA : IsExcellent A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)] [IsNormalDomain (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2) :
    ∃ (W : Scheme.{u}) (g : W ⟶ Spec (X.presheaf.stalk x)),
      IsResolution (Y := Spec (.of (X.presheaf.stalk x))) g ∧ IsProjectiveMorphism g ∧
      ∃ (j : AffineOpenNhds X x) (Z : Over ((affineOpenNhdsDiagram X x).obj j)),
        FinitePresentation Z.hom ∧ IsProper Z.hom ∧ IsProjectiveMorphism Z.hom ∧
          IsRegular Z.left ∧
          IsIso (pullback.snd Z.hom (Scheme.Opens.ι (X := X) j.obj.1 ⁻¹ᵁ
            ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩).ι) ∧
          Nonempty (Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) := by
  have : IsNoetherianRing A := hA.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨W, g, hres, hproj⟩ :=
    exists_isResolution_isProjectiveMorphism_stalk_of_locallyOfFiniteType hA f x hdim
  refine ⟨W, g, hres, hproj, ?_⟩
  have : IsProper g := hres.1.isProper
  have hfp : FinitePresentation g := ⟨inferInstance, inferInstance, inferInstance⟩
  let V : X.Opens := ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩
  have hV : IsIso (pullback.snd g ((X.fromSpecStalk x) ⁻¹ᵁ V).ι) := by
    have hcl : IsLocalRing.closedPoint (X.presheaf.stalk x) ∉ (X.fromSpecStalk x) ⁻¹ᵁ V := by
      show X.fromSpecStalk x (IsLocalRing.closedPoint _) ∉ V
      rw [Scheme.fromSpecStalk_closedPoint]
      exact fun h => h (subset_closure rfl)
    have := isIso_morphismRestrict_of_isModification _ hdim.le g hres.1 _ hcl
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  exact exists_regular_projective_model_specStalk X
    (isJ2_of_locallyOfFiniteType_of_isExcellent hA f) x g hfp hproj hres.2 V hV

end AlgebraicGeometry

end
