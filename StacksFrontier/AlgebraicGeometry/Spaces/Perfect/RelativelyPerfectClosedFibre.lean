module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.AffineChartModelBaseChange
public import StacksFrontier.Homology.RelativelyPerfect.JacobsonFibreClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectJacobsonFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeEnoughFields
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
import StacksCore.Tactic.StacksAttribute

/-!
# Relative perfectness from the closed fibre over a Jacobson pair

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, `𝒮 = Spec R`,
`𝒮₀ = Spec (R/I)`, and let `f : X ⟶ 𝒮` be a proper, flat morphism of algebraic spaces, locally
of finite presentation, with `X₀ = 𝒮₀ ×_𝒮 X`. A pseudo-coherent object `E` of `D(𝒪_X)` whose
derived restriction to `X₀` is `𝒮₀`-perfect is `𝒮`-perfect. This is Stacks 0DL5.

## Main results

* `AlgebraicGeometry.Space.isRelativelyPerfect_of_isRelativelyPerfect_closedFibre`: Stacks 0DL5.

## References

* [Stacks Project, Lemma 76.54.5 (Tag 0DL5)](https://stacks.math.columbia.edu/tag/0DL5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change and fibre products of algebraic spaces -/

/-- A pullback square of algebraic spaces is a pullback square of the underlying presheaves: the
fibre product of presheaves of algebraic spaces is an algebraic space. -/
theorem isPullback_hom_of_isPullback {W X Y Z : AlgebraicSpaces B S hS} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    IsPullback fst.hom snd.hom f.hom g.hom := by
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback f.hom g.hom, isAlgebraicSpace_pullback B S hS f.hom g.hom X.2 Y.2 Z.2⟩
  have hP : IsPullback (ObjectProperty.homMk (pullback.fst f.hom g.hom) : P ⟶ X)
      (ObjectProperty.homMk (pullback.snd f.hom g.hom)) f g :=
    IsPullback.of_map (ObjectProperty.ι _) ((ObjectProperty.ι _).map_injective pullback.condition)
      (IsPullback.of_hasPullback f.hom g.hom)
  refine (IsPullback.of_hasPullback f.hom g.hom).of_iso
    ((ObjectProperty.ι _).mapIso (h.isoIsPullback _ _ hP)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · exact (Category.comp_id _).trans
      (congrArg (fun φ => φ.hom) (h.isoIsPullback_inv_fst _ _ hP)).symm
  · exact (Category.comp_id _).trans
      (congrArg (fun φ => φ.hom) (h.isoIsPullback_inv_snd _ _ hP)).symm

/-- **Flatness is stable under base change** of algebraic spaces (Stacks 03MM). -/
theorem isFlat_snd_of_isPullback {W X Y Z : AlgebraicSpaces B S hS} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (hf : IsFlat B S hS f.hom) : IsFlat B S hS snd.hom :=
  have := holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS _
    isEtaleLocalOnSourceAndTarget_flat
  MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    HoldsOnEveryEtaleChart B S hS (@AlgebraicGeometry.Flat.{u}) f.hom) h hf

/-- **Local finite presentation is stable under base change** of algebraic spaces
(Stacks 03XR). -/
theorem isLocallyOfFinitePresentation_snd_of_isPullback {W X Y Z : AlgebraicSpaces B S hS}
    {fst : W ⟶ X} {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom) :
    IsLocallyOfFinitePresentation B S hS snd.hom :=
  have := holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS _
    isEtaleLocalOnSourceAndTarget_locallyOfFinitePresentation
  MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
    HoldsOnEveryEtaleChart B S hS (@AlgebraicGeometry.LocallyOfFinitePresentation.{u}) f.hom)
    h hf

/-! ### An affine étale chart by the spectrum of a ring -/

/-- **An affine étale chart by a spectrum.** A quasi-compact algebraic space has a surjective
étale chart `h_{Spec A} ⟶ X` by the spectrum of a ring, as an object of the big fppf site. -/
theorem exists_specFppfOver_surjective_etale_chart (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1) :
    ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (CommRingCat.of A)))
      (gA : B.obj hA ⟶ B.obj hS)
      (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
        AlgebraicSpaces B S hS) ⟶ X),
      IsEtale B S hS φ.hom ∧ Function.Surjective (pointsMap B S hS _ φ.hom) := by
  obtain ⟨U, a, hUaff, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hqc
  let e := ((BigFppfOver.toScheme B S hS).obj U).isoSpec
  have hA : B.Contains (Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) U.left.2
  let gA : B.obj hA ⟶ B.obj hS := ObjectProperty.homMk e.inv ≫ U.hom
  let eV : specFppfOver B S hS hA gA ≅ U :=
    Over.isoMk (B.inclusion.preimageIso e.symm) (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      rfl))
  refine ⟨_, inferInstance, hA, gA, ObjectProperty.homMk (yoneda.map eV.hom ≫ a), ?_, ?_⟩
  · intro U' ψ hψ
    have h₁ : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map eV.hom) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ eV.hom).2 inferInstance
    have := isMultiplicative_presheaf_etale B S hS
    have h₂ := MorphismProperty.comp_mem _ ψ _ hψ h₁
    simpa [Category.assoc] using het U' (ψ ≫ yoneda.map eV.hom) h₂
  · have ha := (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U a).1 hsurj
    intro x
    obtain ⟨y, rfl⟩ := ha x
    refine ⟨pointsMap B S hS _ (yoneda.map eV.inv) y, ?_⟩
    have h1 := pointsMap_comp_apply B S hS (yoneda.map eV.inv) (yoneda.map eV.hom ≫ a) y
    rw [← Functor.map_comp_assoc, eV.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp] at h1
    exact h1.symm

/-- The identity of a represented algebraic space is étale after every represented base change. -/
alias presheaf_etale_id_yoneda := etale_presheaf_id_yoneda

/-- **The ring map of an affine chart over `Spec R`.** Let `f : X ⟶ 𝒮` with `𝒮 = Spec R` be flat
and locally of finite presentation, and let `φ : h_{Spec A} ⟶ X` be étale. Then `f ∘ φ` is the
morphism of spectra of a flat ring map `R → A` of finite presentation. -/
theorem exists_algebra_of_chart {R : Type u} [CommRing R]
    (hR : B.Contains (Spec (CommRingCat.of R))) (gR : B.obj hR ⟶ B.obj hS) {A : Type u}
    [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A))) (gA : B.obj hA ⟶ B.obj hS)
    {X : AlgebraicSpaces B S hS}
    (f : X ⟶ ⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩)
    (hflat : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom) :
    ∃ _ : Algebra R A, ∃ w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
          B.obj hA ⟶ B.obj hR) ≫ gR = gA,
        yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom ∧
          Module.Flat R A ∧ Algebra.FinitePresentation R A := by
  let g : specFppfOver B S hS hA gA ⟶ specFppfOver B S hS hR gR := yoneda.preimage (φ.hom ≫ f.hom)
  let c : CommRingCat.of R ⟶ CommRingCat.of A := Spec.preimage ((BigFppfOver.toScheme B S hS).map g)
  let := c.hom.toAlgebra
  have hm : Spec.map (CommRingCat.ofHom (algebraMap R A)) = (BigFppfOver.toScheme B S hS).map g :=
    Spec.map_preimage _
  have hl : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) = g.left := B.inclusion.map_injective hm
  have w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA := by rw [hl]; exact Over.w g
  have hg : specFppfOverMap B S hS hR gR hA gA w = g := Over.OverMorphism.ext hl
  have hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom := by
    rw [hg]; exact yoneda.map_preimage _
  have hφp := (isEtale_iff_presheaf_of_yoneda B S hS φ.hom).1 hφ
  have hsq : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) ≫ 𝟙 _ = φ.hom ≫ f.hom := by
    rw [Category.comp_id, hφf]
  have h₁ : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    hflat _ _ φ.hom (𝟙 _) _ hφp (presheaf_etale_id_yoneda B S hS _) hsq
  have h₂ : AlgebraicGeometry.LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    hlfp _ _ φ.hom (𝟙 _) _ hφp (presheaf_etale_id_yoneda B S hS _) hsq
  refine ⟨c.hom.toAlgebra, w, hφf, ?_, ?_⟩
  · exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h₁)
  · exact (LocallyOfFinitePresentation.SpecMap_iff _).mp h₂

section ClosedFibreChart

attribute [local instance] Algebra.TensorProduct.rightAlgebra pointTopology

variable {R : Type u} [CommRing R] (hR : B.Contains (Spec (CommRingCat.of R)))
  (gR : B.obj hR ⟶ B.obj hS) (I : Ideal R) (hR₀ : B.Contains (Spec (CommRingCat.of (R ⧸ I))))
  {A : Type u} [CommRing A] [Algebra R A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (gA : B.obj hA ⟶ B.obj hS)

/-- The structure morphism of `Spec (R/I)` to `S`, through `Spec R`. -/
abbrev quotientStructureMap : B.obj hR₀ ⟶ B.obj hS :=
  (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I)))) :
    B.obj hR₀ ⟶ B.obj hR) ≫ gR

/-- The closed immersion `Spec (R/I) ⟶ Spec R`, as a morphism of the big fppf site over `S`. -/
abbrev quotientSpecMap :
    specFppfOver B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀) ⟶
      specFppfOver B S hS hR gR :=
  specFppfOverMap B S hS hR gR hR₀ (quotientStructureMap B S hS hR gR I hR₀) rfl

variable (hA₀ : B.Contains (Spec (CommRingCat.of ((R ⧸ I) ⊗[R] A))))

/-- The structure morphism of the closed fibre `Spec ((R/I) ⊗_R A)` to `S`, through `Spec A`. -/
abbrev closedFibreStructureMap :
    B.obj hA₀ ⟶ B.obj hS :=
  (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A ((R ⧸ I) ⊗[R] A)))) :
    B.obj hA₀ ⟶ B.obj hA) ≫ gA

variable (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    B.obj hA ⟶ B.obj hR) ≫ gR = gA)

/-- The square `Spec ((R/I) ⊗_R A) ⟶ Spec A`, `Spec (R/I) ⟶ Spec R` commutes in the big site. -/
private theorem closedFibre_homMk_square :
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] A)))) : B.obj hA₀ ⟶ B.obj hR₀) ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I)))) :
          B.obj hR₀ ⟶ B.obj hR) =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A ((R ⧸ I) ⊗[R] A)))) :
        B.obj hA₀ ⟶ B.obj hA) ≫
        (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
          B.obj hA ⟶ B.obj hR) :=
  B.inclusion.map_injective (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq])

include w in
/-- The closed fibre of `Spec A` lies over `Spec (R/I)`. -/
theorem closedFibre_structureMap_comp :
    (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) ((R ⧸ I) ⊗[R] A)))) :
      B.obj hA₀ ⟶ B.obj hR₀) ≫
        quotientStructureMap B S hS hR gR I hR₀ = closedFibreStructureMap B S hS I hA gA hA₀ := by
  rw [quotientStructureMap, ← Category.assoc, closedFibre_homMk_square B hR I hR₀ hA hA₀,
    Category.assoc, w]

variable {X X₀ : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩)
  (f₀ : X₀ ⟶ ⟨yoneda.obj (specFppfOver B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀)),
    isAlgebraicSpace_yoneda B S hS _⟩) (i : X₀ ⟶ X)
  (hpb : IsPullback i.hom f₀.hom f.hom (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)))
  (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
    AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)
  (hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom)

include hpb hφ hφf in
/-- **The closed fibre of an affine étale chart.** For `X₀ = 𝒮₀ ×_𝒮 X` and an étale chart
`φ : h_{Spec A} ⟶ X` over `Spec R`, the closed fibre `Spec ((R/I) ⊗_R A)` of the chart is an étale
chart of `X₀` over `Spec (R/I)`, lying over `φ`. -/
theorem exists_closedFibre_chart :
    ∃ φ₀ : (⟨yoneda.obj (specFppfOver B S hS hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀)), isAlgebraicSpace_yoneda B S hS _⟩ :
        AlgebraicSpaces B S hS) ⟶ X₀,
      IsEtale B S hS φ₀.hom ∧
      IsPullback (yoneda.map (specFppfOverMap B S hS hA gA hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl)) φ₀.hom φ.hom i.hom ∧
      φ₀ ≫ i = representedSpaceMap B S hS (specFppfOverMap B S hS hA gA
        hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl) ≫ φ ∧
      yoneda.map (specFppfOverMap B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀)
          hA₀
          (closedFibreStructureMap B S hS I hA gA hA₀)
          (closedFibre_structureMap_comp B S hS hR gR I hR₀ hA gA hA₀ w)) = φ₀.hom ≫ f₀.hom := by
  let A₀ := (R ⧸ I) ⊗[R] A
  let gA₀ := closedFibreStructureMap B S hS I hA gA hA₀
  let ψ := specFppfOverMap B S hS hA gA hA₀ gA₀ rfl
  let π₀ := specFppfOverMap B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀) hA₀ gA₀
    (closedFibre_structureMap_comp B S hS hR gR I hR₀ hA gA hA₀ w)
  let gU := specFppfOverMap B S hS hR gR hA gA w
  let jT := quotientSpecMap B S hS hR gR I hR₀
  have hleft : π₀.left ≫ jT.left = ψ.left ≫ gU.left :=
    closedFibre_homMk_square B hR I hR₀ hA hA₀
  have hsqO : π₀ ≫ jT = ψ ≫ gU := Over.OverMorphism.ext hleft
  have hSch := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (R ⧸ I) A A₀)
  have hB : IsPullback π₀.left ψ.left jT.left gU.left := IsPullback.of_map B.inclusion hleft hSch
  have hO : IsPullback π₀ ψ jT gU := IsPullback.of_map (Over.forget _) hsqO hB
  have hY := yoneda.map_isPullback hO
  let φ₀' : yoneda.obj (specFppfOver B S hS hA₀ gA₀) ⟶ X₀.1 :=
    hpb.lift (yoneda.map ψ ≫ φ.hom) (yoneda.map π₀) (by
      rw [Category.assoc, ← hφf, ← Functor.map_comp, ← hsqO, Functor.map_comp])
  have h₁ : φ₀' ≫ i.hom = yoneda.map ψ ≫ φ.hom := hpb.lift_fst _ _ _
  have h₂ : φ₀' ≫ f₀.hom = yoneda.map π₀ := hpb.lift_snd _ _ _
  have hs : IsPullback (φ₀' ≫ f₀.hom) (yoneda.map ψ) (yoneda.map jT) (φ.hom ≫ f.hom) := by
    rw [h₂, ← hφf]; exact hY
  have hleftSq : IsPullback φ₀' (yoneda.map ψ) i.hom φ.hom := IsPullback.of_right hs h₁ hpb.flip
  have hφp := (isEtale_iff_presheaf_of_yoneda B S hS φ.hom).1 hφ
  refine ⟨ObjectProperty.homMk φ₀', (isEtale_iff_presheaf_of_yoneda B S hS φ₀').2
    (presheaf_of_isPullback B S hS hleftSq.flip hφp), hleftSq.flip,
    (ObjectProperty.ι _).map_injective h₁, h₂.symm⟩

include hpb in
/-- **A geometric point of the closed fibre of a chart over a point of the closed fibre.** If a
point `u₀` of the chart `h_{Spec A}` maps to a point of `X` lying over `𝒮₀`, then some geometric
point of the closed fibre `Spec ((R/I) ⊗_R A)` of the chart lies over the prime of `u₀`. -/
theorem exists_closedFibre_geometricPoint
    (φ₀ : (⟨yoneda.obj (specFppfOver B S hS hA₀ (closedFibreStructureMap B S hS I hA gA hA₀)),
      isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ X₀)
    (hsq : IsPullback (yoneda.map (specFppfOverMap B S hS hA gA hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl)) φ₀.hom φ.hom i.hom)
    (u₀ : points B S hS (yoneda.obj (specFppfOver B S hS hA gA)))
    (hu₀ : pointsMap B S hS X.1 f.hom (pointsMap B S hS _ φ.hom u₀) ∈
      Set.range (pointsMap B S hS _ (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)))) :
    ∃ ū₀ : GeometricPoint B S hS
        (yoneda.obj (specFppfOver B S hS hA₀ (closedFibreStructureMap B S hS I hA gA hA₀))),
      (identityChartPrime B S hS hA₀ _ ū₀).asIdeal.under A =
        (pointsToScheme B S hS (specFppfOver B S hS hA gA) u₀).asIdeal := by
  obtain ⟨s₀, hs₀⟩ := hu₀
  obtain ⟨x₀', hx₀'₁, -⟩ := exists_points_of_isPullback B S hS hpb _ s₀ hs₀.symm
  obtain ⟨v, hv₁, hv₂⟩ := exists_points_of_isPullback B S hS hsq u₀ x₀' hx₀'₁.symm
  let Y₀ := yoneda.obj (specFppfOver B S hS hA₀ (closedFibreStructureMap B S hS I hA gA hA₀))
  obtain ⟨ū₀, hū₀⟩ := (geometricPoints_large_enough B S hS Y₀ Y₀
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)).1 v
  refine ⟨ū₀, ?_⟩
  have h := pointsToScheme_pointsMap_yoneda B S hS (specFppfOverMap B S hS hA gA hA₀
    (closedFibreStructureMap B S hS I hA gA hA₀) rfl) v
  rw [hv₁] at h
  rw [h, ← hū₀]
  rfl

/-- The image of the points of `Spec (R/I)` in the points of `Spec R` is the zero locus of `I`. -/
theorem range_pointsMap_quotientSpecMap :
    Set.range (pointsMap B S hS _ (yoneda.map (quotientSpecMap B S hS hR gR I hR₀))) =
      schemePointsHomeomorph B S hS (specFppfOver B S hS hR gR) ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set R) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change pointsToScheme B S hS (specFppfOver B S hS hR gR)
      (pointsMap B S hS _ (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)) z) ∈
        PrimeSpectrum.zeroLocus (I : Set R)
    rw [pointsToScheme_pointsMap_yoneda]
    intro r hr
    change Ideal.Quotient.mk I r ∈ (pointsToScheme B S hS _ z).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr]
    exact Ideal.zero_mem _
  · intro hy
    have hr := range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker] at hr
    obtain ⟨p, hp⟩ : schemePointsHomeomorph B S hS (specFppfOver B S hS hR gR) y ∈
        Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := hr ▸ hy
    refine ⟨(schemePointsHomeomorph B S hS (specFppfOver B S hS hR₀
      (quotientStructureMap B S hS hR gR I hR₀))).symm p, ?_⟩
    apply (schemePointsHomeomorph B S hS (specFppfOver B S hS hR gR)).injective
    change pointsToScheme B S hS (specFppfOver B S hS hR gR)
      (pointsMap B S hS _ (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)) _) = _
    rw [pointsToScheme_pointsMap_yoneda, ← hp]
    exact congrArg (PrimeSpectrum.comap (Ideal.Quotient.mk I))
      ((schemePointsHomeomorph B S hS (specFppfOver B S hS hR₀
        (quotientStructureMap B S hS hR gR I hR₀))).apply_symm_apply p)

end ClosedFibreChart

/-! ### Stacks 0DL5 -/

section Main

attribute [local instance] Algebra.TensorProduct.rightAlgebra pointTopology
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- `AlgebraicGeometry.Space.exists_isBoundedAboveFiniteFree_etaleModulePullback_iso` and the stalk
-- computations it feeds are stated at the standard model of `D(𝒪_X)`.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable {R : Type u} [CommRing R] {hR : B.Contains (Spec (CommRingCat.of R))}
  {gR : B.obj hR ⟶ B.obj hS} {I : Ideal R} {hR₀ : B.Contains (Spec (CommRingCat.of (R ⧸ I)))}
  {X X₀ : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩)
  (f₀ : X₀ ⟶ ⟨yoneda.obj (specFppfOver B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀)),
    isAlgebraicSpace_yoneda B S hS _⟩)
  [HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
  [∀ U : (inverseImageRingedSite B S hS f).C,
    HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]
  [HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f₀))]
  [∀ U : (inverseImageRingedSite B S hS f₀).C,
    HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f₀).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

omit [HasDerivedCategory.{u + 1}
    (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
  [∀ U : (inverseImageRingedSite B S hS f).C, HasDerivedCategory.{u + 1}
    (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]
  [HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f₀))]
  [∀ U : (inverseImageRingedSite B S hS f₀).C, HasDerivedCategory.{u + 1}
    (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f₀).over U))] in
/-- **The bound at a generization of a point of the closed fibre of the chart.** With `E` modelled
by `P` on an affine étale chart `Spec A ⟶ X` and the Tor amplitude of the geometric stalks of
`Li^*E` bounded by `[a, b]`, the complex `P` has Tor amplitude in `[a - d, b]` over `R` at every
prime of `A` contained in the prime of a point of the chart lying over `𝒮₀` (Stacks 0DJH). -/
theorem hasTorAmplitudeAt_of_le_of_closedFibre
    (i : X₀ ⟶ X)
    (hpb : IsPullback i.hom f₀.hom f.hom (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)))
    {A : Type u} [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom)
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpres : Function.Surjective presentation)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
      letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
      letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
        (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj
              (specFppfOver B S hS hA gA))).hom).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)))
    (hA₀ : B.Contains (Spec (CommRingCat.of ((R ⧸ I) ⊗[R] A))))
    (φ₀ : (⟨yoneda.obj (specFppfOver B S hS hA₀ (closedFibreStructureMap B S hS I hA gA hA₀)),
      isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ X₀)
    (hφ₀ : IsEtale B S hS φ₀.hom)
    (hsq : IsPullback (yoneda.map (specFppfOverMap B S hS hA gA hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl)) φ₀.hom φ.hom i.hom)
    (hcomm : φ₀ ≫ i = representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl) ≫ φ)
    (hφf₀ : yoneda.map (specFppfOverMap B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀) hA₀
          (closedFibreStructureMap B S hS I hA gA hA₀)
          (closedFibre_structureMap_comp B S hS hR gR I hR₀ hA gA hA₀ w)) = φ₀.hom ≫ f₀.hom)
    (a b : ℤ)
    (hab : ∀ x₀ : GeometricPoint B S hS X₀.1,
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X₀.1 x₀ X₀.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f₀).O.obj)
        ((ModuleCat.restrictScalars.{u}
          (inverseImageStalkRingHom B S hS f₀ x₀)).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS x₀).mapDerivedCategory.obj
            (haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i;
              (smallEtaleDerivedModulePullback B S hS i).obj E))) a b)
    (u₀ : points B S hS (yoneda.obj (specFppfOver B S hS hA gA)))
    (hu₀ : pointsMap B S hS X.1 f.hom (pointsMap B S hS _ φ.hom u₀) ∈
      Set.range (pointsMap B S hS _ (yoneda.map (quotientSpecMap B S hS hR gR I hR₀))))
    (q : Ideal A) [q.IsPrime]
    (hq : q ≤ (pointsToScheme B S hS (specFppfOver B S hS hA gA) u₀).asIdeal) :
    StacksDraft.TorAmplitude.HasTorAmplitudeAt R P q (a - (d : ℤ)) b := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i
  obtain ⟨eP₀⟩ := nonempty_etaleModulePullback_derivedPullback_chartModel_iso B S hS i hA gA hA₀
    (closedFibreStructureMap B S hS I hA gA hA₀) rfl φ hφ φ₀ hφ₀ hcomm E P hP eP
  obtain ⟨ū₀, hū₀⟩ := exists_closedFibre_geometricPoint B S hS hR gR I hR₀ hA gA hA₀ f f₀ i hpb φ φ₀
    hsq u₀ hu₀
  have h₀ := (hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt B S hS hR₀
    (quotientStructureMap B S hS hR gR I hR₀) hA₀ (closedFibreStructureMap B S hS I hA gA hA₀) f₀ φ₀
    (closedFibre_structureMap_comp B S hS hR gR I hR₀ hA gA hA₀ w) hφf₀ ū₀ hφ₀ _ _ eP₀ a b).1
    (hab _)
  refine PseudoCoherence.hasTorAmplitudeAt_of_hasTorAmplitudeAt_closedFibre d presentation hpres I
    _ q ?_ P hP a b h₀
  rw [hū₀]
  exact hq

omit [HasDerivedCategory.{u + 1}
    (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
  [∀ U : (inverseImageRingedSite B S hS f).C, HasDerivedCategory.{u + 1}
    (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]
  [HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f₀))]
  [∀ U : (inverseImageRingedSite B S hS f₀).C, HasDerivedCategory.{u + 1}
    (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f₀).over U))] in
/-- **The bound at every geometric point.** Every point of `X` specializes into the closed fibre
(`f` being closed and `I` lying in the Jacobson radical), the specialization lifts to the chart
(Stacks 03K2) and the geometric point lifts along it (Stacks 05VN); at the lift the Tor amplitude
of `E_x̄` over the stalk of `f⁻¹𝒪_𝒮` is that of `P` at the corresponding prime over `R`. -/
theorem hasTorAmplitudeCanonical_geometricStalk_of_closedFibre
    (hI : I ≤ (⊥ : Ideal R).jacobson) (hclosed : IsClosedMorphism B S hS f.hom)
    (hdec : IsDecentSpace B S hS X.1)
    (i : X₀ ⟶ X)
    (hpb : IsPullback i.hom f₀.hom f.hom (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)))
    {A : Type u} [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom)
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpres : Function.Surjective presentation)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
      letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
      letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
        (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj
              (specFppfOver B S hS hA gA))).hom).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)))
    (hA₀ : B.Contains (Spec (CommRingCat.of ((R ⧸ I) ⊗[R] A))))
    (φ₀ : (⟨yoneda.obj (specFppfOver B S hS hA₀ (closedFibreStructureMap B S hS I hA gA hA₀)),
      isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ X₀)
    (hφ₀ : IsEtale B S hS φ₀.hom)
    (hsq : IsPullback (yoneda.map (specFppfOverMap B S hS hA gA hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl)) φ₀.hom φ.hom i.hom)
    (hcomm : φ₀ ≫ i = representedSpaceMap B S hS (specFppfOverMap B S hS hA gA hA₀
        (closedFibreStructureMap B S hS I hA gA hA₀) rfl) ≫ φ)
    (hφf₀ : yoneda.map (specFppfOverMap B S hS hR₀ (quotientStructureMap B S hS hR gR I hR₀) hA₀
          (closedFibreStructureMap B S hS I hA gA hA₀)
          (closedFibre_structureMap_comp B S hS hR gR I hR₀ hA gA hA₀ w)) = φ₀.hom ≫ f₀.hom)
    (a b : ℤ)
    (hab : ∀ x₀ : GeometricPoint B S hS X₀.1,
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X₀.1 x₀ X₀.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f₀).O.obj)
        ((ModuleCat.restrictScalars.{u}
          (inverseImageStalkRingHom B S hS f₀ x₀)).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS x₀).mapDerivedCategory.obj
            (haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i;
              (smallEtaleDerivedModulePullback B S hS i).obj E))) a b)
    (hφsurj : Function.Surjective (pointsMap B S hS _ φ.hom))
    (x : GeometricPoint B S hS X.1) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f).O.obj)
        ((ModuleCat.restrictScalars.{u}
          (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.obj
          ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E)) (a - (d : ℤ)) b := by
  obtain ⟨x₀, hxx₀, hx₀⟩ := exists_specializes_mem_range_of_isClosedMorphism B S hS f
    (representedSpaceMap B S hS (quotientSpecMap B S hS hR gR I hR₀)) hclosed
    (closedFibre_meets_isClosed_of_jacobson B S hS _ hI
      (schemePointsHomeomorph B S hS (specFppfOver B S hS hR gR))
      (range_pointsMap_quotientSpecMap B S hS hR gR I hR₀)) x.image
  obtain ⟨u₀, hu₀⟩ := hφsurj x₀
  obtain ⟨u, huu₀, hu⟩ := exists_specialization_lift_of_isDecentSpace B S hS X.1 X.2 hdec x₀
    x.image hxx₀ _ φ.hom ((isEtale_iff_presheaf_of_yoneda B S hS φ.hom).1 hφ) u₀ hu₀
  obtain ⟨ū, hū, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS
    (isAlgebraicSpace_yoneda B S hS _) X.2 φ.hom hφ x u hu
  have hx : geometricPointMap φ.hom ū = x := Subtype.ext hval
  subst hx
  rw [hasTorAmplitudeCanonical_geometricStalk_iff_hasTorAmplitudeAt B S hS hR gR hA gA f φ w hφf ū
    hφ E P eP]
  have hspec := huu₀.map (schemePointsHomeomorph B S hS (specFppfOver B S hS hA gA)).continuous
  rw [← hū] at hspec
  exact hasTorAmplitudeAt_of_le_of_closedFibre B S hS f f₀ i hpb w φ hφ hφf d presentation hpres E
    P hP eP hA₀ φ₀ hφ₀ hsq hcomm hφf₀ a b hab u₀ (by rw [hu₀]; exact hx₀) _
    ((PrimeSpectrum.le_iff_specializes _ _).2 hspec)

/-- **The Tor clause from an affine chart.** With `E` modelled by `P` on a surjective affine étale
chart `Spec A ⟶ X` presented by `d` variables over `R`, and `Li^*E` locally of finite Tor
dimension over `f₀⁻¹𝒪_{𝒮₀}`, the object `E` locally has finite Tor dimension over `f⁻¹𝒪_𝒮`. -/
theorem locallyHasFiniteTorDimension_of_chart (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hclosed : IsClosedMorphism B S hS f.hom) (hdec : IsDecentSpace B S hS X.1) (i : X₀ ⟶ X)
    (hpb : IsPullback i.hom f₀.hom f.hom (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)))
    {A : Type u} [CommRing A] [Algebra R A] (hAflat : Module.Flat R A)
    (hAfp : Algebra.FinitePresentation R A) {hA : B.Contains (Spec (CommRingCat.of A))}
    {gA : B.obj hA ⟶ B.obj hS}
    (w : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA)
    (φ : (⟨yoneda.obj (specFppfOver B S hS hA gA), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hφsurj : Function.Surjective (pointsMap B S hS _ φ.hom))
    (hφf : yoneda.map (specFppfOverMap B S hS hR gR hA gA w) = φ.hom ≫ f.hom)
    (d : ℕ) (presentation : MvPolynomial (Fin d) R →ₐ[R] A)
    (hpres : Function.Surjective presentation)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (eP : letI := etaleModulePullback_additive.{u, u} B S hS φ hφ
      letI := preservesFiniteLimits_etaleModulePullback B S hS φ hφ
      letI := preservesFiniteColimits_etaleModulePullback B S hS φ hφ
      (etaleModulePullback.{u, u} B S hS φ hφ).mapDerivedCategory.obj E ≅
        (representedDerivedAssociatedModule B S hS (specFppfOver B S hS hA gA)).obj
          ((tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.restrictFunctor
            (Iso.refl ((BigFppfOver.toScheme B S hS).obj
              (specFppfOver B S hS hA gA))).hom).mapDerivedCategory.obj
              (DerivedCategory.Q.obj P)))
    (hE₀ : haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
        (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
          ((inverseImageRingedSite B S hS f₀).over U))
        ((derivedScalarRestriction B S hS f₀).obj
          ((smallEtaleDerivedModulePullback B S hS i).obj E))) :
    Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E) := by
  have hs : Function.Surjective (algebraMap A ((R ⧸ I) ⊗[R] A)) :=
    Algebra.IsPushout.algebraMap_surjective_of_surjective (R := R) (R' := R ⧸ I)
      Ideal.Quotient.mk_surjective
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (algebraMap A ((R ⧸ I) ⊗[R] A))) hs
  have hA₀ : B.Contains (Spec (CommRingCat.of ((R ⧸ I) ⊗[R] A))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap A ((R ⧸ I) ⊗[R] A))))) hA
  obtain ⟨φ₀, hφ₀, hsq, hcomm, hφf₀⟩ := @exists_closedFibre_chart B S hS R _ hR gR I hR₀ A _ _ hA gA
    hA₀ w X X₀ f f₀ i hpb φ hφ hφf
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i
  have := hAflat
  have := hAfp
  have hqc₀ : IsQuasiCompactSpace B S hS X₀.1 :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X₀.1 X₀.2).2
      ⟨_, φ₀.hom, inferInstanceAs (IsAffine (Spec _)),
        (surjective_iff_surjective_pointsMap B S hS X₀.1 X₀.2 _ φ₀.hom).2
          (surjective_pointsMap_of_isPullback B S hS hsq hφsurj), hφ₀⟩
  obtain ⟨a, b, hab⟩ := exists_stalkBound_of_locallyHasFiniteTorDimension B S hS f₀ hqc₀ _ _ hE₀
  exact locallyHasFiniteTorDimension_derivedScalarRestriction_of_stalkBound B S hS f _ E
    (a - (d : ℤ)) b fun x => hasTorAmplitudeCanonical_geometricStalk_of_closedFibre B S hS f f₀ hI
      hclosed hdec i hpb w φ hφ hφf d presentation hpres E P hP eP hA₀ φ₀ hφ₀ hsq hcomm hφf₀ a b
      hab hφsurj x

/-- **Stacks 0DL5.** Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, let
`𝒮 = Spec R` and `𝒮₀ = Spec (R/I)`, and let `f : X ⟶ 𝒮` be a proper and flat morphism of
algebraic spaces, locally of finite presentation (hence of finite presentation, `f` being proper).
Let `X₀ = 𝒮₀ ×_𝒮 X`, with projections `i : X₀ ⟶ X` and `f₀ : X₀ ⟶ 𝒮₀`. If a pseudo-coherent object
`E` of `D(𝒪_X)` has `𝒮₀`-perfect derived restriction `Li^*E` to `X₀`, then `E` is `𝒮`-perfect.

On an affine étale chart `Spec A ⟶ X`, presented by `d` variables over `R`, `E` is `ε^*(P~)` for a
bounded above complex `P` of finite free `A`-modules, and `Li^*E` is `ε^*((P ⊗_R R/I)~)` on the
closed fibre of the chart. One interval `[a, b]` bounds the Tor amplitude of the geometric stalks
of `Li^*E` on the quasi-compact `X₀`, and then `[a - d, b]` bounds those of `E` over the stalks of
`f⁻¹𝒪_𝒮` (`hasTorAmplitudeCanonical_geometricStalk_of_closedFibre`); a uniform bound at the
geometric stalks gives locally finite Tor dimension (Stacks 0DJJ, 04K5).

`X₀` is the fibre product in the category of algebraic spaces; flatness and local finite
presentation of `f₀`, the preconditions of `𝒮₀`-perfectness (Stacks 0DKN), are those of `f` by base
change. -/
@[stacks 0DL5]
theorem isRelativelyPerfect_of_isRelativelyPerfect_closedFibre
    (hI : I ≤ (⊥ : Ideal R).jacobson) (i : X₀ ⟶ X)
    (hpb : IsPullback i f₀ f (representedSpaceMap B S hS (quotientSpecMap B S hS hR gR I hR₀)))
    (hproper : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (hE₀ : haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i
      IsRelativelyPerfect B S hS f₀ (isFlat_snd_of_isPullback B S hS hpb hflat)
        (isLocallyOfFinitePresentation_snd_of_isPullback B S hS hpb hlfp)
        ((smallEtaleDerivedModulePullback B S hS i).obj E)) :
    IsRelativelyPerfect B S hS f hflat hlfp E := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS i
  have hpb' : IsPullback i.hom f₀.hom f.hom (yoneda.map (quotientSpecMap B S hS hR gR I hR₀)) :=
    isPullback_hom_of_isPullback B S hS hpb
  let 𝒮 : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (specFppfOver B S hS hR gR), isAlgebraicSpace_yoneda B S hS _⟩
  have hqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom
      ⟨specFppfOver B S hS hR gR, inferInstanceAs (IsAffine (Spec (CommRingCat.of R))),
        ⟨Iso.refl _⟩⟩ hproper.2.1.2
  have hdec : IsDecentSpace B S hS X.1 :=
    isDecentSpace_of_isDecent B S hS X.2 𝒮.2 f.hom (isDecentSpace_yoneda B S hS _)
      (isDecent_of_isReasonable B S hS X.2 𝒮.2 f.hom
        (isReasonable_of_isVeryReasonable B S hS X.2 𝒮.2
          (isVeryReasonable_of_isQuasiSeparated B S hS X.2 𝒮.2
            (isQuasiSeparated_of_isSeparated B S hS hproper.1))))
  obtain ⟨A, _, hA, gA, φ, hφ, hφsurj⟩ := exists_specFppfOver_surjective_etale_chart B S hS X hqc
  obtain ⟨_, w, hφf, hAflat, hAfp⟩ := exists_algebra_of_chart B S hS hR gR hA gA f hflat hlfp φ hφ
  obtain ⟨d, presentation, hpres, -⟩ := hAfp.out
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_isBoundedAboveFiniteFree_etaleModulePullback_iso B S hS hA gA φ hφ
    E hE
  exact ⟨hE, locallyHasFiniteTorDimension_of_chart B S hS f f₀ hI
    (isClosed_of_universallyClosed B S hS 𝒮.2 f.hom hproper.2.2) hdec i hpb' hAflat hAfp w φ hφ
    hφsurj hφf d presentation hpres E P hP eP hE₀.2⟩

end Main

end AlgebraicGeometry.Space

end
