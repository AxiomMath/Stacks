/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.IsomQuasiCompactOfHilbertBound
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveHilbertModelReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveClosedImmersionFibreHilbert
public import StacksFrontier.AlgebraicGeometry.Quot.CurveTensorPowerEuler
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveCurveGraphTwist
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectivePairProductEmbedding
public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.OverScheme
public import StacksFrontier.AlgebraicGeometry.PicardTrivialOpenUFD.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.TwistInvertibleOverBase.Basic

/-!
# `Isom_U(Y, X)` is quasi-compact for H-projective curves over a Noetherian affine base

Let `U` be a Noetherian affine object of the big fppf site over `Spec ℤ` and let `q₁ : Z₁ ⟶ U`,
`q₂ : Z₂ ⟶ U` be H-projective, flat and of finite presentation, with fibres of dimension at most
one. This is the last paragraph of the proof of Stacks 0DSQ: `Isom_U(Z₁, Z₂) ⟶ U` is
quasi-compact.

Embed `Z₁ ×_U Z₂` into `ℙᴺ_U` with `𝒪(1)` pulling back to `(pr₁^*𝒜 ⊗ pr₂^*ℬ)^{⊗ e}`, `𝒜` and `ℬ`
ample on `Z₁` and `Z₂` (`AlgebraicGeometry.ProjectivePairProductEmbedding`). The graph of an
isomorphism `f : (Z₁)_t ⟶ (Z₂)_t` over a field `t ⟶ U` is a closed subscheme of `ℙᴺ_t` whose
Hilbert polynomial is `d ↦ χ((Z₁)_t, (𝒜_t ⊗ f^*ℬ_t)^{⊗ ed})`, which by Riemann–Roch
(Stacks 0AYR, 0AYX) is `d ↦ ed (χ(𝒜_t) + χ(ℬ_t) - 2χ(𝒪)) + χ(𝒪)`, using that `f` is an
isomorphism. The three Euler characteristics are those of the fibres of `Z₁` and `Z₂` over the
image of `t` in `U`, and they are locally constant on `U` (Stacks 0B9T), so take finitely many
values on the quasi-compact `U`. Hence the graphs lie in finitely many of the Hilbert schemes
`Hilb^P_{ℙᴺ_U/U}`, and `AlgebraicGeometry.Space.isQuasiCompact_isomSubfunctor_of_hilbertBound`
concludes.

## Main results

* `AlgebraicGeometry.ProjectiveCurveIsomQuasiCompact.isQuasiCompact_isomSubfunctor`.

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.ProjectiveCurveIsomQuasiCompact

open ProperFlatFibreEulerCharacteristic Stacks.Ample

/-- **Riemann–Roch for the twist of a graph.** On a proper scheme of dimension at most one over a
field, if `𝒩 ≅ (c₁^*𝒜 ⊗ c₂^*ℬ)^{⊗ e}` then
`χ(𝒩^{⊗ d}) = d e (χ(c₁^*𝒜) + χ(c₂^*ℬ) - 2 χ(𝒪)) + χ(𝒪)`. -/
theorem eulerSum_graphTwist (K : Type u) [Field K] {R Z₁ Z₂ : Scheme.{u}} (g : R ⟶ Spec (.of K))
    [IsProper g] (hdim : topologicalKrullDim R ≤ 1) (A : Z₁.Modules) (B : Z₂.Modules)
    [IsInvertibleModule Z₁ A] [IsInvertibleModule Z₂ B] (c₁ : R ⟶ Z₁) (c₂ : R ⟶ Z₂)
    (N : R.Modules) [IsInvertibleModule R N] (e : ℕ)
    (eN : N ≅ tensorPowModule R
      (Stacks.RelativeVeryAmple.tensorModules R ((Scheme.Modules.pullback c₁).obj A)
        ((Scheme.Modules.pullback c₂).obj B)) (e : ℤ)) (d : ℤ) :
    eulerSum K g (tensorPowModule R N d) =
      d * e * (eulerSum K g ((Scheme.Modules.pullback c₁).obj A) +
        eulerSum K g ((Scheme.Modules.pullback c₂).obj B) - 2 * eulerSum K g (unitModule R)) +
        eulerSum K g (unitModule R) := by
  rw [CurveTensorPowerEuler.eulerSum_tensorPowModule K g hdim N d, eulerSum_congr K g eN,
    CurveTensorPowerEuler.eulerSum_tensorPowModule K g hdim _ e,
    CurveTensorPowerEuler.eulerSum_tensorSheaf K g hdim]
  ring

/-- **The Euler characteristic of a fibre over a field-valued point is the value of the fibre
Euler characteristic function of Stacks 0B9T at its image.** -/
theorem eulerSum_eq_fibreEulerCharacteristic {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (K : Type u) [Field K] (p : Spec (.of K) ⟶ S)
    {Y : Scheme.{u}} (q : Y ⟶ X) (g : Y ⟶ Spec (.of K)) (hsq : IsPullback q g f p)
    (pt : Spec (.of K)) :
    eulerSum K g ((Scheme.Modules.pullback q).obj F) = fibreEulerCharacteristic f F (p.base pt) :=
  (chiDerivedFibre_eq_eulerSum f hf F hF hflat K p q g hsq pt).symm.trans
    (congrFun (fibreEulerCharacteristic_eq_chiDerivedFibre f hf F hF hflat) (p.base pt)).symm

/-- An invertible module on a scheme flat over `S` is of finite presentation and flat over `S`. -/
theorem isFinitePresentation_and_isFlatOver_of_isInvertibleModule {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] (L : X.Modules) [IsInvertibleModule X L] :
    L.IsFinitePresentation ∧ IsFlatOver f.toLRSHom.toShHom L := by
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible _ _ L :=
    Stacks.TwoAffineCech.isInvertible_of_isInvertibleModule L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L hL')
  have : L.IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule L
  exact ⟨@Stacks.Divisors.isFinitePresentation_of_isInvertible _ L hL',
    AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree f L⟩

/-- The fibre Euler characteristic of an invertible module over a flat proper morphism of finite
presentation is locally constant. -/
private theorem isLocallyConstant_fibreEulerCharacteristic_of_isInvertibleModule
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] (hf : FinitePresentation f)
    (L : X.Modules) [IsInvertibleModule X L] :
    IsLocallyConstant (fibreEulerCharacteristic f L) :=
  let h := isFinitePresentation_and_isFlatOver_of_isInvertibleModule f L
  isLocallyConstant_fibreEulerCharacteristic f hf L h.1 h.2

/-- `eulerSum_eq_fibreEulerCharacteristic` for an invertible module. -/
private theorem eulerSum_eq_fibreEulerCharacteristic_of_isInvertibleModule {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] (hf : FinitePresentation f) (L : X.Modules)
    [IsInvertibleModule X L] (K : Type u) [Field K] (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}}
    (q : Y ⟶ X) (g : Y ⟶ Spec (.of K)) (hsq : IsPullback q g f p) (pt : Spec (.of K)) :
    eulerSum K g ((Scheme.Modules.pullback q).obj L) = fibreEulerCharacteristic f L (p.base pt) :=
  let h := isFinitePresentation_and_isFlatOver_of_isInvertibleModule f L
  eulerSum_eq_fibreEulerCharacteristic f hf L h.1 h.2 K p q g hsq pt

/-- The Euler characteristic is invariant under pullback along an isomorphism of schemes. -/
theorem eulerSum_pullback_of_isIso (K : Type u) [Field K] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (g : Y ⟶ Spec (.of K)) (E : Y.Modules) :
    eulerSum K (f ≫ g) ((Scheme.Modules.pullback f).obj E) = eulerSum K g E :=
  finsum_congr fun n => by rw [finrank_cohomologyOverField_pullback K f g E n]

/-- A cartesian square stays cartesian after an isomorphism of one of its bottom corners. -/
theorem isPullback_comp_iso {P X Y Z Y' : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : Y ≅ Y') :
    IsPullback fst (snd ≫ e.hom) f (e.inv ≫ g) := by
  have h₁ : IsPullback (𝟙 P) (snd ≫ e.hom) snd e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using h₁.paste_horiz h

/-- The polynomial `d ↦ e d (a + b - 2c) + c`, the Hilbert polynomial of a graph. -/
def graphPolynomial (e : ℕ) (a b c : ℤ) : Polynomial ℚ :=
  Polynomial.C ((e : ℚ) * ((a : ℚ) + b - 2 * c)) * Polynomial.X + Polynomial.C (c : ℚ)

/-- The value of `graphPolynomial e a b c` at an integer `d` is the integer
`d e (a + b - 2c) + c`. -/
theorem eval_graphPolynomial (e : ℕ) (a b c d : ℤ) :
    (graphPolynomial e a b c).eval (d : ℚ) = ((d * e * (a + b - 2 * c) + c : ℤ) : ℚ) := by
  simp only [graphPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  push_cast
  ring

section Core

open C1590Private ProjectiveQuot ProjectiveCurveGraphHilbert ProjectiveCurveGraphTwist
  Stacks.AmpleProjectiveImmersion Stacks.AmpleExternalTensor

variable {B : BigFppfSite.{u}}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- `Isom_U(Z₁, Z₂)` for morphisms `q₁ : Z₁ ⟶ U` and `q₂ : Z₂ ⟶ U` of the site. -/
abbrev isomSub {U Z₁ Z₂ : BigFppfOver B integerBase B.contains_integerBase} (q₁ : Z₁ ⟶ U)
    (q₂ : Z₂ ⟶ U) :=
  Space.isomSubfunctor B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
    (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)

/-- The relative morphism `(a, b)` a section of `Mor_U(Z₁, Z₂)` over `T` is. -/
abbrev homSections {U Z₁ Z₂ : BigFppfOver B integerBase B.contains_integerBase} (q₁ : Z₁ ⟶ U)
    (q₂ : Z₂ ⟶ U) (T : BigFppfOver B integerBase B.contains_integerBase) :=
  Space.relativeHomSections B integerBase B.contains_integerBase (yoneda.obj Z₁) (yoneda.obj Z₂)
    (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
    (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U) T

variable {U Z₁ Z₂ : BigFppfOver B integerBase B.contains_integerBase} {q₁ : Z₁ ⟶ U} {q₂ : Z₂ ⟶ U}
  {N : ℕ}

/-- **The graph of an isomorphism over a field has the Hilbert polynomial
`d ↦ e d (χ(𝒜_x) + χ(ℬ_x) - 2χ(𝒪_x)) + χ(𝒪_x)`**, `x` the image point in `U`. -/
theorem mem_hilbertModelSubfunctor_graph
    (i : pullback ((𝒯).map q₁) ((𝒯).map q₂) ⟶ projectiveSpaceOver N ((𝒯).obj U))
    (hi : i ≫ (projectiveSpaceOver N ((𝒯).obj U) ↘ (𝒯).obj U) =
      pullback.snd ((𝒯).map q₁) ((𝒯).map q₂) ≫ (𝒯).map q₂)
    (hi'c : IsClosedImmersion ((𝒯).map (siteEmbedding i)))
    (A : ((𝒯).obj Z₁).Modules) (B' : ((𝒯).obj Z₂).Modules)
    [IsInvertibleModule _ A] [IsInvertibleModule _ B'] (e : ℕ)
    (eL : tensorPowModule (pullback ((𝒯).map q₁) ((𝒯).map q₂))
      (externalTensor ((𝒯).map q₁) ((𝒯).map q₂) A B') (e : ℤ) ≅
      (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf N ((𝒯).obj U)))
    [Flat ((𝒯).map q₁)] [Flat ((𝒯).map q₂)] [IsProper ((𝒯).map q₁)] [IsProper ((𝒯).map q₂)]
    (hfp₁ : FinitePresentation ((𝒯).map q₁)) (hfp₂ : FinitePresentation ((𝒯).map q₂))
    (hsep : Space.IsSeparated B integerBase B.contains_integerBase (yoneda.map q₂))
    (hfp : Space.IsFinitePresentation B integerBase B.contains_integerBase (yoneda.map q₁))
    (hflat : Space.IsFlat B integerBase B.contains_integerBase (yoneda.map q₁))
    (hproper : Space.IsProper B integerBase B.contains_integerBase (yoneda.map q₁))
    {K : Type u} [Field K] {T : BigFppfOver B integerBase B.contains_integerBase}
    (eT : (𝒯).obj T ≅ Spec (.of K)) (v : (isomSub q₁ q₂).toFunctor.obj (Opposite.op T))
    (hdim : topologicalKrullDim ((𝒯).obj (pullback (graphBase (homSections q₁ q₂ T v.1)) q₁)) ≤ 1)
    (pt : Spec (.of K)) :
    ((isomSub q₁ q₂).ι ≫ Space.graphHilbertModelMap q₁ q₂ N (graphEmbedding q₁ q₂ (siteEmbedding i))
        (graphEmbedding_comp (siteEmbedding_comp i hi)) (isClosedImmersion_graphEmbedding hi'c)
        hsep hfp hflat hproper).app _ v ∈
      (hilbertModelSubfunctor N U (graphPolynomial e
        (fibreEulerCharacteristic ((𝒯).map q₁) A
          ((eT.inv ≫ (𝒯).map (graphBase (homSections q₁ q₂ T v.1))).base pt))
        (fibreEulerCharacteristic ((𝒯).map q₂) B'
          ((eT.inv ≫ (𝒯).map (graphBase (homSections q₁ q₂ T v.1))).base pt))
        (fibreEulerCharacteristic ((𝒯).map q₁) (unitModule _)
          ((eT.inv ≫ (𝒯).map (graphBase (homSections q₁ q₂ T v.1))).base pt)))).obj _ := by
  classical
  set rv := homSections q₁ q₂ T v.1 with hrv
  set x := (eT.inv ≫ (𝒯).map (graphBase rv)).base pt with hx
  set P := graphPolynomial e (fibreEulerCharacteristic ((𝒯).map q₁) A x)
    (fibreEulerCharacteristic ((𝒯).map q₂) B' x)
    (fibreEulerCharacteristic ((𝒯).map q₁) (unitModule _) x) with hP
  have hv : rv.IsRelativeIso := v.2
  have hi' := siteEmbedding_comp i hi
  have hj : IsClosedImmersion ((𝒯).map (graphClosedMap rv hi')) :=
    isClosedImmersion_graphClosedMap rv hi' hi'c hsep
  set s := ((isomSub q₁ q₂).ι ≫ Space.graphHilbertModelMap q₁ q₂ N
    (graphEmbedding q₁ q₂ (siteEmbedding i)) (graphEmbedding_comp hi')
    (isClosedImmersion_graphEmbedding hi'c) hsep hfp hflat hproper).app _ v with hs
  have h1 : (Space.HilbertPresheafModel.canonical _).familyEquiv T
      ((Space.morToHilbertModel (yoneda.map q₁) (yoneda.map q₂) _ _ _
        (Space.HilbertPresheafModel.canonical _) hsep hfp hflat hproper).app (Opposite.op T) v.1) =
      (Space.graphTransformation _ _ _ hsep hfp hflat hproper).app (Opposite.op T) ⟨v.1⟩ :=
    types_congr_hom ((Space.HilbertPresheafModel.canonical _).iso.inv_hom_id_app (Opposite.op T)) _
  have hfam : (projectiveSpaceHilbertModel N U).familyEquiv T s =
      Space.hilbertFamilyOverImageOfClosed (graphEmbedding_comp hi')
        (isClosedImmersion_graphEmbedding hi'c) T
        ((Space.graphTransformation _ _ _ hsep hfp hflat hproper).app (Opposite.op T) ⟨v.1⟩) :=
    (Space.familyEquiv_hilbertModelMapOfClosed _ _ _ _ T _).trans (congrArg _ h1)
  have hZ : ((projectiveSpaceHilbertModel N U).familyEquiv T s).family.Z =
      Subfunctor.range (yoneda.map (graphClosedMap rv hi') ≫
        (ProjectiveHilbertModelReading.spaceIso' (projectiveSpaceFrame N U)
          (CostructuredArrow.mk (ObjectProperty.homMk
            ((projectiveSpaceHilbertModel N U).familyEquiv T s).toBase))).hom.hom) := by
    rw [hfam]
    exact (range_graphSpaceMap rv hi' hi'c hsep hfp hflat hproper).symm.trans
      (congrArg Subfunctor.range (graphClosedMap_spaceIso rv hi').symm)
  obtain ⟨eQ⟩ := ProjectiveHilbertModelReading.nonempty_quotient_modelQuotient_iso U s
    (graphClosedMap rv hi') hZ
  have hQfp := (modelQuotient N U s).2.1
  have hpush : ((Scheme.Modules.pushforward ((𝒯).map (graphClosedMap rv hi'))).obj
      (unitModule ((𝒯).obj (pullback (graphBase rv) q₁)))).IsFinitePresentation :=
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso eQ hQfp
  have hinv : IsInvertibleModule ((𝒯).obj (pullback (graphBase rv) q₁))
      ((Scheme.Modules.pullback ((𝒯).map (graphClosedMap rv hi'))).obj
        (projectiveSpaceTwistingSheaf N ((𝒯).obj T))) :=
    Stacks.TwistInvertibleOverBase.isInvertibleModule_pullback_projectiveSpaceTwistingSheaf
      (S := (𝒯).obj T) N ((𝒯).map (graphClosedMap rv hi'))
  have : IsProper (projectiveSpaceOver N ((𝒯).obj T) ↘ (𝒯).obj T) :=
    isProper_projectiveSpaceOver N _
  have hg : (𝒯).map (graphClosedMap rv hi') ≫ (projectiveSpaceOver N ((𝒯).obj T) ↘ (𝒯).obj T) =
      (𝒯).map (pullback.fst (graphBase rv) q₁) := by
    rw [← graphClosedMap_comp_structure rv hi', Functor.map_comp]
    rfl
  have hsq₁ : IsPullback ((𝒯).map (pullback.snd (graphBase rv) q₁))
      ((𝒯).map (pullback.fst (graphBase rv) q₁)) ((𝒯).map q₁) ((𝒯).map (graphBase rv)) :=
    (IsPullback.of_hasPullback (graphBase rv) q₁).flip.map (𝒯)
  have hsq₂ : IsPullback ((𝒯).map (pullback.snd (graphBase rv) q₂))
      ((𝒯).map (pullback.fst (graphBase rv) q₂)) ((𝒯).map q₂) ((𝒯).map (graphBase rv)) :=
    (IsPullback.of_hasPullback (graphBase rv) q₂).flip.map (𝒯)
  have : IsProper ((𝒯).map (pullback.fst (graphBase rv) q₁)) :=
    MorphismProperty.of_isPullback (P := @IsProper) hsq₁ inferInstance
  have hχA : eulerSum K ((𝒯).map (pullback.fst (graphBase rv) q₁) ≫ eT.hom)
      ((Scheme.Modules.pullback ((𝒯).map (pullback.snd (graphBase rv) q₁))).obj A) =
      fibreEulerCharacteristic ((𝒯).map q₁) A x :=
    eulerSum_eq_fibreEulerCharacteristic_of_isInvertibleModule _ hfp₁ A K _ _ _
      (isPullback_comp_iso hsq₁ eT) pt
  have hχO : eulerSum K ((𝒯).map (pullback.fst (graphBase rv) q₁) ≫ eT.hom)
      (unitModule ((𝒯).obj (pullback (graphBase rv) q₁))) =
      fibreEulerCharacteristic ((𝒯).map q₁) (unitModule _) x :=
    (eulerSum_congr K _ (Stacks.PicardTrivialOpenUFD.pullbackUnitIso
      ((𝒯).map (pullback.snd (graphBase rv) q₁)))).symm.trans
      (eulerSum_eq_fibreEulerCharacteristic_of_isInvertibleModule _ hfp₁ _ K _ _ _
        (isPullback_comp_iso hsq₁ eT) pt)
  have hχB : eulerSum K ((𝒯).map (pullback.fst (graphBase rv) q₁) ≫ eT.hom)
      ((Scheme.Modules.pullback ((𝒯).map (graphPairMap rv ≫ pullback.snd q₁ q₂))).obj B') =
      fibreEulerCharacteristic ((𝒯).map q₂) B' x := by
    have hc₂ : (𝒯).map (graphPairMap rv ≫ pullback.snd q₁ q₂) =
        (𝒯).map (graphPairIso rv hv).hom ≫ (𝒯).map (pullback.snd (graphBase rv) q₂) := by
      rw [← Functor.map_comp, graphPairIso_hom_snd]
    have hg₂ : (𝒯).map (pullback.fst (graphBase rv) q₁) ≫ eT.hom =
        (𝒯).map (graphPairIso rv hv).hom ≫ ((𝒯).map (pullback.fst (graphBase rv) q₂) ≫ eT.hom) := by
      rw [← Category.assoc, ← Functor.map_comp, graphPairIso_hom_fst]
    rw [hg₂, eulerSum_congr K _ ((Scheme.Modules.pullbackCongr hc₂).app B' ≪≫
      ((Scheme.Modules.pullbackComp _ _).app B').symm)]
    exact (eulerSum_pullback_of_isIso K ((𝒯).map (graphPairIso rv hv).hom) _ _).trans
      (eulerSum_eq_fibreEulerCharacteristic_of_isInvertibleModule _ hfp₂ B' K _ _ _
        (isPullback_comp_iso hsq₂ eT) pt)
  have key : Set.range ((𝒯).map (𝟙 T)) ⊆
      fibreHilbertLocus P (quotient (modelQuotient N U s).1) := by
    rintro _ ⟨t, rfl⟩ d
    have hH := @fibreHilbert_pushforward_unitModule_eq_eulerSum N ((𝒯).obj T) K _ eT _
        ((𝒯).map (graphClosedMap rv hi')) hj hpush hinv ((𝒯).map (𝟙 T) t) d
    have hH2 := hH.trans ((congrArg (fun g => eulerSum K (g ≫ eT.hom) (tensorPowModule _
      ((Scheme.Modules.pullback ((𝒯).map (graphClosedMap rv hi'))).obj
        (projectiveSpaceTwistingSheaf N ((𝒯).obj T))) d)) hg).trans
      (eulerSum_graphTwist K _ hdim A B' _ _ _ e (graphTwistIso i rv hi A B' e eL) d))
    rw [hχA, hχB, hχO] at hH2
    rw [congrFun (@fibreHilbert_eq_of_iso N ((𝒯).obj T) _ _ hQfp hpush eQ _) d, hP,
      eval_graphPolynomial]
    exact congrArg (fun z : ℤ => (z : ℚ)) hH2
  have hmem := (map_mem_hilbertModelSubfunctor_iff N U P (𝟙 T) s).2 key
  have hid : (ConcreteCategory.hom ((projectiveSpaceQuotModel N U).presheaf.map (𝟙 T).op)) s =
      s := by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  exact hid ▸ hmem

/-- **`Isom_U(Z₁, Z₂) ⟶ U` is quasi-compact** for `q₁ : Z₁ ⟶ U` and `q₂ : Z₂ ⟶ U` H-projective,
flat and locally of finite presentation over a Noetherian affine `U`, the fibres of `q₁` over the
spectra of fields having dimension at most one. This is the last paragraph of the proof of
Stacks 0DSQ. -/
theorem isQuasiCompact_isomSubfunctor (q₁ : Z₁ ⟶ U) (q₂ : Z₂ ⟶ U)
    (hU : IsAffine ((𝒯).obj U)) (hUn : IsNoetherian ((𝒯).obj U))
    (hq₁ : IsProjectiveMorphism ((𝒯).map q₁)) (hq₂ : IsProjectiveMorphism ((𝒯).map q₂))
    (hflat₁ : Flat ((𝒯).map q₁)) (hflat₂ : Flat ((𝒯).map q₂))
    (hlfp₁ : LocallyOfFinitePresentation ((𝒯).map q₁))
    (hlfp₂ : LocallyOfFinitePresentation ((𝒯).map q₂))
    (hdim : ∀ {T : BigFppfOver B integerBase B.contains_integerBase} (a : T ⟶ U),
      Subsingleton ((𝒯).obj T) → topologicalKrullDim ((𝒯).obj (pullback a q₁)) ≤ 1) :
    Space.IsQuasiCompact B integerBase B.contains_integerBase
      ((isomSub q₁ q₂).ι ≫ Space.relativeHomProjection B integerBase B.contains_integerBase
        (yoneda.obj Z₁) (yoneda.obj Z₂) (yoneda.obj U) (yoneda.map q₁) (yoneda.map q₂)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₁)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase Z₂)
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase U)) := by
  classical
  have := hU
  have := hflat₁
  have := hflat₂
  have : IsProper ((𝒯).map q₁) := isProper_of_isProjectiveMorphism _ hq₁
  have : IsProper ((𝒯).map q₂) := isProper_of_isProjectiveMorphism _ hq₂
  have hfp₁ : FinitePresentation ((𝒯).map q₁) := ⟨hlfp₁, inferInstance, inferInstance⟩
  have hfp₂ : FinitePresentation ((𝒯).map q₂) := ⟨hlfp₂, inferInstance, inferInstance⟩
  obtain ⟨A, B', hA, hB', e, N, i, hic, hi, ⟨eL⟩⟩ :=
    ProjectivePairProductEmbedding.exists_isClosedImmersion_twist ((𝒯).map q₁) ((𝒯).map q₂)
      hq₁ hq₂
  have hi'c : IsClosedImmersion ((𝒯).map (siteEmbedding i)) := by
    change IsClosedImmersion ((PreservesPullback.iso (𝒯) q₁ q₂).hom ≫ i)
    infer_instance
  have hsep : Space.IsSeparated B integerBase B.contains_integerBase (yoneda.map q₂) :=
    (Space.isSeparated_yoneda_map_iff B integerBase B.contains_integerBase q₂).2 inferInstance
  have hfp := Space.isFinitePresentation_yoneda_map B integerBase B.contains_integerBase q₁ hfp₁
  have hflat := Space.isFlat_yoneda_map B integerBase B.contains_integerBase q₁ hflat₁
  have hproper := (Space.isProper_yoneda_map_iff B integerBase B.contains_integerBase q₁).2
    inferInstance
  have hxproper := (Space.isProper_yoneda_map_iff B integerBase B.contains_integerBase q₂).2
    inferInstance
  have hlc : IsLocallyConstant fun x => graphPolynomial e
      (fibreEulerCharacteristic ((𝒯).map q₁) A x) (fibreEulerCharacteristic ((𝒯).map q₂) B' x)
      (fibreEulerCharacteristic ((𝒯).map q₁) (unitModule _) x) :=
    (isLocallyConstant_fibreEulerCharacteristic_of_isInvertibleModule _ hfp₁ A).comp₂
      ((isLocallyConstant_fibreEulerCharacteristic_of_isInvertibleModule _ hfp₂ B').comp₂
        (isLocallyConstant_fibreEulerCharacteristic_of_isInvertibleModule _ hfp₁ _) Prod.mk)
      (fun a bc => graphPolynomial e a bc.1 bc.2)
  have hfin := hlc.range_finite
  refine Space.isQuasiCompact_isomSubfunctor_of_hilbertBound q₁ q₂ N
    (graphEmbedding q₁ q₂ (siteEmbedding i)) (graphEmbedding_comp (siteEmbedding_comp i hi))
    (isClosedImmersion_graphEmbedding hi'c) hsep hfp hflat hproper hU hUn hxproper
    hfin.toFinset fun p => ?_
  have hsub : Subsingleton ((𝒯).obj (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶
      B.obj B.contains_integerBase))) := by
    change Subsingleton (Spec (.of p.carrier))
    infer_instance
  exact ⟨_, hfin.mem_toFinset.2 ⟨_, rfl⟩, mem_hilbertModelSubfunctor_graph i hi hi'c A B' e eL
    hfp₁ hfp₂ hsep hfp hflat hproper (Iso.refl _) p.value (hdim _ hsub)
    (IsLocalRing.closedPoint p.carrier)⟩

end Core

end AlgebraicGeometry.ProjectiveCurveIsomQuasiCompact

end
