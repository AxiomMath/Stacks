module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatLimitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectDescentInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectIsoDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelDerivedPullbackCube

/-!
# Descent of perfect objects over the integers, in the form Stacks 0D3F consumes

`AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper`
(Stacks 0D3F) takes the essential surjectivity half of Stacks 09RJ, for situations over the final
scheme with bounded charts, as its argument `hdescent`. This file derives a statement of exactly
that shape from the induction of Stacks 08GP
(`DescentSituation.perfectObjectsDescend_of_restrictTo_isElementaryDistinguishedSquare`), given its
step across an elementary distinguished square for objects for every such situation; the step for
morphisms is `DescentSituation.perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare`.

## Main results

* `AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers_of_restrictTo_objectsSquareStep`.
* `AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_chartsBounded`: the essential
  surjectivity half of Stacks 09RJ.
* `AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers`: the hypothesis `hdescent` of
  Stacks 0D3F.
* `AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_chartsBounded`: the full
  faithfulness half of Stacks 09RJ.
* `AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_and_perfectHomsDescend`:
  **Stacks 09RJ**.

## Implementation notes

The goals in the proof of
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_restrictTo_id` are large: every
derived pullback in them carries the models of its source and target derived categories. The proof
names the existential statements it destructures before `obtain`, and reads the equation for `ψ'`
off the `Iso` lemmas instead of rewriting with it.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_isGrothendieckAbelian

variable {B : BigFppfSite.{u}}

/-- **Perfect objects descend along approximating systems over the final scheme**, in the shape of
the hypothesis `hdescent` of Stacks 0D3F
(`AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper`),
given, for every such situation, the step of the induction of Stacks 08GP across an elementary
distinguished square for objects, `hobj` (essential surjectivity). The step for morphisms (full
faithfulness, the Mayer–Vietoris step) is
`DescentSituation.perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare`.
-/
theorem perfectObjectsDescend_overIntegers_of_restrictTo_objectsSquareStep
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hobj : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I)
      (W V : SpacesEtale B _ hZ ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
      (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B _ hZ W.1.left.property U f →
      IsQuasiCompactSpace B _ hZ W.1.left.1 →
      IsAbsolutelyQuasiSeparated B _ hZ hZ W.1.left.1 →
      IsQuasiCompactSpace B _ hZ U.toFunctor →
      IsAffineSpace B _ hZ V.1.left.1 →
      D.RestrictedObjectsDescend (U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend V.1.hom.hom →
      D.RestrictedHomsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend W.1.hom.hom) :
    ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E) :=
  fun I _ _ D hb => D.perfectObjectsDescend_of_restrictTo_isElementaryDistinguishedSquare hb
    (hobj I D)

namespace DescentSituation

variable {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u}
  [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- An object on the limit that is the pullback of a perfect object on a stage `i` is the pullback
of a perfect object on every later stage. -/
theorem exists_isPerfect_derivedPullback_iso_of_le {i k : I} (hik : i ≤ k)
    {E : DerivedCategory (spacesEtaleModelRingedTopos B S hS
      ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules}
    {Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B S hS
      ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules}
    (hEᵢ : (spacesEtaleModelRingedSite B S hS
      ⟨D.system.obj (op i), D.algebraicSpace i⟩).IsPerfect Eᵢ)
    (α : (derivedPullback.{u} (spacesEtaleModelHom B S hS
      (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E) :
    ∃ Eₖ : DerivedCategory (spacesEtaleModelRingedTopos B S hS
        ⟨D.system.obj (op k), D.algebraicSpace k⟩).Modules,
      (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op k), D.algebraicSpace k⟩).IsPerfect Eₖ ∧
        Nonempty ((derivedPullback.{u} (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op k)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op k), D.algebraicSpace k⟩))).obj Eₖ ≅ E) :=
  ⟨_, isPerfect_derivedPullback_spacesEtaleModelHom _ Eᵢ hEᵢ,
    ⟨D.stageProjectionDerivedPullbackIso hik Eᵢ ≪≫ α⟩⟩

/-- **The step of the induction of Stacks 08GP in the proof of Stacks 09RJ, for objects.** For an
elementary distinguished square `(U ⊆ W₀, f : V₀ ⟶ W₀)` of quasi-compact quasi-separated
algebraic spaces over the chosen stage, with intersection `P₀ = U ×_{W₀} V₀`: if perfect objects
descend in the restrictions of `D` to `U` and `V₀` and morphisms of perfect objects descend in its
restriction to `P₀`, then perfect objects descend in its restriction to `W₀`. Given the
compatibility of the comparisons of Stacks 03G1 with composition, `hT`.

A perfect `E` on `X ×_{X₀} W₀` restricts to `X ×_{X₀} U` and `X ×_{X₀} V₀`, where it comes from
perfect `A`, `B` on a common stage `k₁`; the identification of the restrictions of `A` and `B` to
`X ×_{X₀} P₀` comes from an isomorphism `c` over a later stage `k` by the descent of morphisms for
`P₀`; and over the stage `k` the square is elementary distinguished, where the objects glue
(Stacks 08HB) to a perfect `F` whose pullback to the limit is `E`, since over the limit morphisms
glue and the restrictions jointly reflect isomorphisms. -/
theorem perfectObjectsDescend_restrictTo_of_isElementaryDistinguishedSquare
    (hT : SpacesEtaleModelEtaleTransportCoherent B S hS)
    {W₀ V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW₀ : IsAlgebraicSpace B S hS W₀)
    (hW₀qc : IsQuasiCompactSpace B S hS W₀) (hW₀qs : IsAbsolutelyQuasiSeparated B S hS hZ W₀)
    (w : W₀ ⟶ D.system.obj (op D.base)) (U : Subfunctor W₀) (f : V₀ ⟶ W₀)
    (hsq : IsElementaryDistinguishedSquare B S hS hW₀ U f)
    (hU : IsAlgebraicSpace B S hS U.toFunctor) (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V₀) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V₀)
    (hP : IsAlgebraicSpace B S hS (pullback U.ι f))
    (hPqc : IsQuasiCompactSpace B S hS (pullback U.ι f))
    (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback U.ι f))
    (hESU : (D.restrictTo hU hUqc hUqs (U.ι ≫ w)).PerfectObjectsDescend)
    (hESV : (D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).PerfectObjectsDescend)
    (hFFP : (D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).PerfectHomsDescend) :
    (D.restrictTo hW₀ hW₀qc hW₀qs w).PerfectObjectsDescend := by
  have := isDirected_laterStages D
  intro E hE
  obtain ⟨iU, hiU, A₀, hA₀, ⟨αU₀⟩⟩ := hESU _ (isPerfect_derivedPullback_spacesEtaleModelHom
    (baseChangeOverOpenHom B S hS w U (D.limitCone.π.app (op D.base))
      (D.restrictTo hU hUqc hUqs (U.ι ≫ w)).limitAlgebraicSpace
      (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace) E hE)
  obtain ⟨iV, hiV, Bo₀, hBo₀, ⟨αV₀⟩⟩ := hESV _ (isPerfect_derivedPullback_spacesEtaleModelHom
    (baseChangeOverEtaleHom B S hS w f (D.limitCone.π.app (op D.base))
      (D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).limitAlgebraicSpace
      (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace) E hE)
  obtain ⟨k₁, h₁, h₂⟩ := directed_of (· ≤ ·) iU iV
  obtain ⟨A, hA, ⟨αU⟩⟩ :=
    (D.restrictTo hU hUqc hUqs (U.ι ≫ w)).exists_isPerfect_derivedPullback_iso_of_le h₁ hA₀ αU₀
  obtain ⟨Bo, hBo, ⟨αV⟩⟩ := (D.restrictTo hsq.isAlgebraicSpace hVqc hVqs
    (f ≫ w)).exists_isPerfect_derivedPullback_iso_of_le h₂ hBo₀ αV₀
  obtain ⟨k, hk, ψ, hψ⟩ := hFFP.exists_iso _ k₁.2
    (isPerfect_derivedPullback_spacesEtaleModelHom
      (baseChangeOverInterFstHom B S hS w U f ((laterStagesToBaseStage D).app (op k₁))
        ((D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).algebraicSpace k₁)
        ((D.restrictTo hU hUqc hUqs (U.ι ≫ w)).algebraicSpace k₁)) A hA)
    (isPerfect_derivedPullback_spacesEtaleModelHom
      (baseChangeOverInterSndHom B S hS w U f ((laterStagesToBaseStage D).app (op k₁))
        ((D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).algebraicSpace k₁)
        ((D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).algebraicSpace k₁)) Bo hBo)
    (spacesEtaleModelBaseChangeOverInterIso (D.limitCone.π.app (op D.base))
      (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace
      (D.restrictTo hU hUqc hUqs (U.ι ≫ w)).limitAlgebraicSpace
      (D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).limitAlgebraicSpace
      (D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).limitAlgebraicSpace
      ((laterStagesToBaseStage D).app (op k₁)) ((laterStages D).limitCone.π.app (op k₁))
      (limitCone_π_comp_laterStagesToBaseStage D (op k₁))
      ((D.restrictTo hU hUqc hUqs (U.ι ≫ w)).algebraicSpace k₁)
      ((D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).algebraicSpace k₁)
      ((D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).algebraicSpace k₁) E A Bo αU αV)
  obtain ⟨F, hF, ⟨e⟩⟩ := exists_isPerfect_iso_spacesEtaleModel_baseChangeOver hsq
    (D.limitCone.π.app (op D.base)) (D.restrictTo hW₀ hW₀qc hW₀qs w).limitAlgebraicSpace
    (D.restrictTo hU hUqc hUqs (U.ι ≫ w)).limitAlgebraicSpace
    (D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).limitAlgebraicSpace
    (D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).limitAlgebraicSpace hT
    ((laterStagesToBaseStage D).app (op k)) ((laterStagesToBaseStage D).app (op k₁))
    ((laterStages D).limitCone.π.app (op k)) ((laterStages D).system.map (homOfLE hk).op)
    ((laterStages D).limitCone.π.app (op k₁)) (limitCone_π_comp_laterStagesToBaseStage D (op k))
    (((laterStagesToBaseStage D).naturality (homOfLE hk).op).trans (Category.comp_id _))
    (limitCone_π_comp_laterStagesToBaseStage D (op k₁))
    ((laterStages D).limitCone.w (homOfLE hk).op)
    ((D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace k)
    ((D.restrictTo hU hUqc hUqs (U.ι ≫ w)).algebraicSpace k)
    ((D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).algebraicSpace k)
    ((D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).algebraicSpace k)
    ((D.restrictTo hU hUqc hUqs (U.ι ≫ w)).algebraicSpace k₁)
    ((D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).algebraicSpace k₁)
    ((D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).algebraicSpace k₁)
    E A Bo hA hBo αU αV ψ hψ
  exact ⟨k, k.2, F, hF, ⟨e⟩⟩

end DescentSituation

/-- The finiteness and algebraicity facts about the pieces `U`, `V₀` and `U ×_{W₀} V₀` of an
elementary distinguished square that the induction of Stacks 08GP needs. -/
private theorem isAlgebraicSpace_and_qcqs_of_isElementaryDistinguishedSquare
    {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
    {W₀ V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW₀ : IsAlgebraicSpace B S hS W₀)
    (U : Subfunctor W₀) (f : V₀ ⟶ W₀) (hsq : IsElementaryDistinguishedSquare B S hS hW₀ U f)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W₀) (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hVaff : IsAffineSpace B S hS V₀) :
    ∃ (_ : IsAlgebraicSpace B S hS U.toFunctor)
      (_ : IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor)
      (_ : IsQuasiCompactSpace B S hS V₀) (_ : IsAbsolutelyQuasiSeparated B S hS hZ V₀)
      (_ : IsAlgebraicSpace B S hS (pullback U.ι f))
      (_ : IsQuasiCompactSpace B S hS (pullback U.ι f)),
      IsAbsolutelyQuasiSeparated B S hS hZ (pullback U.ι f) := by
  have hUa : IsAlgebraicSpace B S hS U.toFunctor := hsq.isOpenSubspace.1
  have hUqs := isAbsolutelyQuasiSeparated_subfunctor B S hS hZ hWqs U hUa
  have hVqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hVaff
  exact ⟨hUa, hUqs, hVaff.isQuasiCompactSpace, hVqs,
    isAlgebraicSpace_pullback B S hS U.ι f hUa hsq.isAlgebraicSpace hW₀,
    isQuasiCompactSpace_pullback B S hS hZ U.ι f hUa hW₀ hUqc hVaff.isQuasiCompactSpace hWqs,
    isAbsolutelyQuasiSeparated_pullback B S hS hZ U.ι f hUa hsq.isAlgebraicSpace hW₀ hUqs hVqs⟩

/-- **Perfect objects descend for the restriction of Situation 09RH to `W` once they descend for
the pieces of an elementary distinguished square** (the step of the induction of Stacks 08GP for
objects in the proof of Stacks 09RJ, in the shape the induction
`DescentSituation.perfectObjectsDescend_of_restrictTo_isElementaryDistinguishedSquare` takes),
given the compatibility of the comparisons of Stacks 03G1 with composition, `hT`. -/
theorem DescentSituation.restrictedObjectsDescend_of_isElementaryDistinguishedSquare
    {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hT : SpacesEtaleModelEtaleTransportCoherent B S hS)
    (W V : SpacesEtale B S hS ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
    (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1)
    (hf : f ≫ W.1.hom.hom = V.1.hom.hom)
    (hsq : IsElementaryDistinguishedSquare B S hS W.1.left.property U f)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) (hVaff : IsAffineSpace B S hS V.1.left.1)
    (hESU : D.RestrictedObjectsDescend (U.ι ≫ W.1.hom.hom))
    (hESV : D.RestrictedObjectsDescend V.1.hom.hom)
    (hFFP : D.RestrictedHomsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom)) :
    D.RestrictedObjectsDescend W.1.hom.hom := by
  intro hW' hWqc' hWqs'
  obtain ⟨hUa, hUqs, hVqc, hVqs, hPa, hPqc, hPqs⟩ :=
    isAlgebraicSpace_and_qcqs_of_isElementaryDistinguishedSquare W.1.left.property U f hsq hWqs
      hUqc hVaff
  have hESV' := hESV hsq.isAlgebraicSpace hVqc hVqs
  rw [← hf] at hESV'
  exact D.perfectObjectsDescend_restrictTo_of_isElementaryDistinguishedSquare hT hW' hWqc' hWqs'
    W.1.hom.hom U f hsq hUa hUqc hUqs hVqc hVqs hPa hPqc hPqs (hESU hUa hUqc hUqs) hESV'
    (hFFP hPa hPqc hPqs)

/-- **The step `hobj` of
`AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers_of_restrictTo_objectsSquareStep`**
(Stacks 09RJ, the step of the induction of Stacks 08GP for objects), for every situation over the
final scheme, given the compatibility of the comparisons of Stacks 03G1 with composition,
`hTcoh`. -/
theorem objectsSquareStep_overIntegers_of_etaleTransportCoherent
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hTcoh : SpacesEtaleModelEtaleTransportCoherent B (⊤_ Scheme.{u}) hZ) :
    ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I)
      (W V : SpacesEtale B _ hZ ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩)
      (U : Subfunctor W.1.left.1) (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B _ hZ W.1.left.property U f →
      IsQuasiCompactSpace B _ hZ W.1.left.1 →
      IsAbsolutelyQuasiSeparated B _ hZ hZ W.1.left.1 →
      IsQuasiCompactSpace B _ hZ U.toFunctor →
      IsAffineSpace B _ hZ V.1.left.1 →
      D.RestrictedObjectsDescend (U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend V.1.hom.hom →
      D.RestrictedHomsDescend (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      D.RestrictedObjectsDescend W.1.hom.hom :=
  fun _ _ _ D W V U f hf hsq _ hWqs hUqc hVaff hESU hESV hFFP =>
    D.restrictedObjectsDescend_of_isElementaryDistinguishedSquare hTcoh W V U f hf hsq hWqs hUqc
      hVaff hESU hESV hFFP

/-- **Stacks 09RJ, essential surjectivity**: in Situation 09RH with bounded charts, every perfect
object on the limit `X` is `Lfᵢ^* Eᵢ` for some stage `i ≥ 0` and some perfect object `Eᵢ` on `Xᵢ`.
The induction of Stacks 08GP
(`DescentSituation.perfectObjectsDescend_of_restrictTo_isElementaryDistinguishedSquare`) with its
step for objects `DescentSituation.restrictedObjectsDescend_of_isElementaryDistinguishedSquare`,
whose input `AlgebraicGeometry.Space.SpacesEtaleModelEtaleTransportCoherent` is
`AlgebraicGeometry.Space.spacesEtaleModelEtaleTransportCoherent`. -/
theorem DescentSituation.perfectObjectsDescend_of_chartsBounded
    {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hb : ChartsBounded B S hS D.system) : D.PerfectObjectsDescend :=
  D.perfectObjectsDescend_of_restrictTo_isElementaryDistinguishedSquare hb
    fun W V U f hf hsq _ hWqs hUqc hVaff hESU hESV hFFP =>
      D.restrictedObjectsDescend_of_isElementaryDistinguishedSquare
        (spacesEtaleModelEtaleTransportCoherent B S hS) W V U f hf hsq hWqs hUqc hVaff hESU hESV
        hFFP

/-- **Perfect objects descend along approximating systems over the final scheme with bounded
charts**, in the shape of the hypothesis `hdescent` of Stacks 0D3F
(`AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule_of_isProper`):
`AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers_of_restrictTo_objectsSquareStep` with
its step `AlgebraicGeometry.Space.objectsSquareStep_overIntegers_of_etaleTransportCoherent`, whose
input is `AlgebraicGeometry.Space.spacesEtaleModelEtaleTransportCoherent`. -/
theorem perfectObjectsDescend_overIntegers (hZ : B.Contains (⊤_ Scheme.{u})) :
    ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E) :=
  perfectObjectsDescend_overIntegers_of_restrictTo_objectsSquareStep hZ
    (objectsSquareStep_overIntegers_of_etaleTransportCoherent hZ
      (spacesEtaleModelEtaleTransportCoherent B _ hZ))

section CompOfEqCube

variable (B) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparisons `Lf^* ∘ Lg^* ≅ Lp^*` across a commutative cube**: for a commutative diagram
of algebraic spaces `X' → X'_j → X'_i`, `X → X_j → X_i` with vertical maps `σ`, `τ_j`, `τ_i`, the
two identifications of `Lπ'_i^* Lτ_i^* E` with `L(σ ≫ π_j)^* Lt^* E` built from
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq` agree (both are canonical, by
the cocycle identity). -/
theorem spacesEtaleModelDerivedPullbackCompIsoOfEq_square_coherence
    {X' Xj' Xi' Xi Xj X : AlgebraicSpaces B S hS} (πj' : X' ⟶ Xj') (t' : Xj' ⟶ Xi')
    (πi' : X' ⟶ Xi') (τi : Xi' ⟶ Xi) (τj : Xj' ⟶ Xj) (t : Xj ⟶ Xi) (σ : X' ⟶ X)
    (πj : X ⟶ Xj) (πi : X ⟶ Xi) (h1 : πj' ≫ t' = πi') (h2 : πj ≫ t = πi)
    (h3 : τj ≫ t = t' ≫ τi) (h4 : πj' ≫ τj = σ ≫ πj) (h5 : πi' ≫ τi = σ ≫ πi)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Xi).O))) :
    (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πj' t' h1
        ((derivedPullback (spacesEtaleModelHom B S hS τi)).obj E)).inv ≫
        (derivedPullback (spacesEtaleModelHom B S hS πj')).map
          ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS t' τi rfl E).hom ≫
            (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS τj t h3 E).inv) ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πj' τj h4
          ((derivedPullback (spacesEtaleModelHom B S hS t)).obj E)).hom =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πi' τi h5 E).hom ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS σ πi rfl E).inv ≫
        (derivedPullback (spacesEtaleModelHom B S hS σ)).map
          (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πj t h2 E).inv ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS σ πj rfl
          ((derivedPullback (spacesEtaleModelHom B S hS t)).obj E)).hom := by
  have hr' : πj' ≫ (t' ≫ τi) = σ ≫ πi := by rw [← Category.assoc, h1, h5]
  have hr : (σ ≫ πj) ≫ t = σ ≫ πi := by rw [Category.assoc, h2]
  have hα := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS πj' t' τi h1 rfl h5 hr' E
  have hβ := spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS πj' τj t h4 h3 hr hr' E
  have hN := (Iso.eq_inv_comp _).mpr
    (spacesEtaleModelDerivedPullbackCompIsoOfEq_cocycle B S hS σ πj t rfl h2 hr rfl E).symm
  rw [← cancel_epi (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS πj' t' h1
      ((derivedPullback (spacesEtaleModelHom B S hS τi)).obj E)).hom,
    Iso.hom_inv_id_assoc, ← reassoc_of% hα, Functor.map_comp, Category.assoc, cancel_epi,
    ← cancel_epi ((derivedPullback (spacesEtaleModelHom B S hS πj')).map
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS τj t h3 E).hom),
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% hβ, hN]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- `AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality`, solved for
`Lf^*(Lg^* χ)`. -/
theorem spacesEtaleModelDerivedPullback_map_map_eq {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y ⟶ Z) {p : X ⟶ Z} (hp : f ≫ g = p)
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Z).O))} (χ : E ⟶ K) :
    (derivedPullback (spacesEtaleModelHom B S hS f)).map
        ((derivedPullback (spacesEtaleModelHom B S hS g)).map χ) =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS f g hp E).hom ≫
        (derivedPullback (spacesEtaleModelHom B S hS p)).map χ ≫
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS f g hp K).inv := by
  rw [← reassoc_of% spacesEtaleModelDerivedPullbackCompIsoOfEq_hom_naturality B S hS f g hp χ,
    Iso.hom_inv_id, Category.comp_id]

/-- Whether two morphisms agree after `Lg^*` then `Lf^*` depends only on `f ≫ g`. -/
theorem spacesEtaleModelDerivedPullback_map_map_eq_iff {X Y Y' Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z) (hfg : f ≫ g = f' ≫ g')
    {E K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS Z).O))} (χ χ' : E ⟶ K) :
    (derivedPullback (spacesEtaleModelHom B S hS f)).map
        ((derivedPullback (spacesEtaleModelHom B S hS g)).map χ) =
      (derivedPullback (spacesEtaleModelHom B S hS f)).map
        ((derivedPullback (spacesEtaleModelHom B S hS g)).map χ') ↔
    (derivedPullback (spacesEtaleModelHom B S hS f')).map
        ((derivedPullback (spacesEtaleModelHom B S hS g')).map χ) =
      (derivedPullback (spacesEtaleModelHom B S hS f')).map
        ((derivedPullback (spacesEtaleModelHom B S hS g')).map χ') := by
  rw [spacesEtaleModelDerivedPullback_map_map_eq B S hS f g rfl,
    spacesEtaleModelDerivedPullback_map_map_eq B S hS f g rfl χ',
    spacesEtaleModelDerivedPullback_map_map_eq B S hS f' g' hfg.symm,
    spacesEtaleModelDerivedPullback_map_map_eq B S hS f' g' hfg.symm χ']
  simp only [cancel_epi, cancel_mono]

end CompOfEqCube

namespace DescentSituation

variable {S : Scheme.{u}} {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u}
  [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **Morphisms of perfect objects descend in Situation 09RH as soon as they descend for its
restriction to `X₀` itself**, the system `X_i ×_{X₀} X₀` with limit `X ×_{X₀} X₀`: the cartesian
projections `σ : X ×_{X₀} X₀ ⟶ X` and `τᵢ : X_i ×_{X₀} X₀ ⟶ X_i` are isomorphisms commuting with
the projections and the transition morphisms, derived pullback along them is an equivalence, and
the comparisons of composites of derived pullbacks match by
`AlgebraicGeometry.Space.spacesEtaleModelDerivedPullbackCompIsoOfEq_square_coherence`. This is
the last step of the induction of Stacks 08GP in the proof of Stacks 09RI–09RJ for morphisms
(`AlgebraicGeometry.Space.DescentSituation.perfectObjectsDescend_of_restrictTo_id` for objects). -/
theorem perfectHomsDescend_of_restrictTo_id
    (h : (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
      (𝟙 _)).PerfectHomsDescend) : D.PerfectHomsDescend := by
  intro i hi E K hE hK
  have hσ : IsIso (pullback.fst (D.limitCone.π.app (op D.base)) (𝟙 (D.system.obj (op D.base)))) :=
    (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso
  let σ : (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
      (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base)
      (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ :
      AlgebraicSpaces B S hS) ≅ (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S
      hS) := ObjectProperty.isoMk _
    (@asIso _ _ _ _ (pullback.fst (D.limitCone.π.app (op D.base)) (𝟙 (D.system.obj (op D.base))))
      hσ)
  have hτ : ∀ k : {k : I // D.base ≤ k},
      IsIso (pullback.fst (D.system.map (homOfLE k.2).op) (𝟙 (D.system.obj (op D.base)))) :=
    fun _ => (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso
  let τ : ∀ k : {k : I // D.base ≤ k}, (⟨(D.restrictTo (D.algebraicSpace D.base)
      (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op k),
      (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
      (𝟙 _)).algebraicSpace k⟩ : AlgebraicSpaces B S hS) ≅ (⟨D.system.obj (op k.1), D.algebraicSpace
      k.1⟩ : AlgebraicSpaces B S hS) := fun k => ObjectProperty.isoMk _
    (@asIso _ _ _ _ (pullback.fst (D.system.map (homOfLE k.2).op) (𝟙 (D.system.obj (op D.base))))
      (hτ k))
  have hπ : ∀ k, (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base)
      (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op k)) :
      (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
      (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
      (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
      (𝟙 _)).system.obj (op k), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
      (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace k⟩ : AlgebraicSpaces B S hS)) ≫ (τ k).hom =
      σ.hom ≫ (ObjectProperty.homMk (D.limitCone.π.app (op k.1)) :
      (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨D.system.obj (op k.1), D.algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) := fun k =>
    ObjectProperty.hom_ext _ (by
      exact baseChangeOverMap_fst B S hS (D.limitCone.π.app (op D.base))
        ((laterStagesToBaseStage D).app (op k)) ((laterStages D).limitCone.π.app (op k))
        (limitCone_π_comp_laterStagesToBaseStage D (op k)) (𝟙 _))
  have ht : ∀ {k k' : {k : I // D.base ≤ k}} (hkk : k ≤ k'),
      (τ k').hom ≫ (ObjectProperty.homMk (D.system.map (homOfLE (X := I) hkk).op) :
          (⟨D.system.obj (op k'.1), D.algebraicSpace k'.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op k.1), D.algebraicSpace k.1⟩ : AlgebraicSpaces B S hS)) =
        (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hkk).op) :
            (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).system.obj (op k'), (D.restrictTo
            (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
            (𝟙 _)).algebraicSpace k'⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).system.obj (op k), (D.restrictTo
            (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
            (𝟙 _)).algebraicSpace k⟩ : AlgebraicSpaces B S hS)) ≫ (τ k).hom :=
    fun _ => ObjectProperty.hom_ext _ (by
      exact (baseChangeOverSystem_map_fst B S hS _ _ _ _).symm)
  obtain ⟨i', rfl⟩ : ∃ i' : {k : I // D.base ≤ k}, i'.1 = i := ⟨⟨i, hi⟩, rfl⟩
  have hE' := isPerfect_derivedPullback_spacesEtaleModelHom (τ i').hom E hE
  have hK' := isPerfect_derivedPullback_spacesEtaleModelHom (τ i').hom K hK
  obtain ⟨hsurj, hinj⟩ := h i' hi _ _ hE' hK'
  refine ⟨fun φ => ?_, fun φ ψ hφψ => ?_⟩
  · have hsurj' := hsurj (((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op i')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (hπ i') (E)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS (σ.hom)
        ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) : (⟨D.limitCone.pt,
        D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1),
        D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (rfl) (E))).symm).hom ≫
        (derivedPullback (spacesEtaleModelHom B S hS (σ.hom))).map φ ≫
        ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
        ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.π.app (op i')) : (⟨(D.restrictTo (D.algebraicSpace D.base)
        (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt,
        (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
        (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (hπ i') (K)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS (σ.hom)
        ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) : (⟨D.limitCone.pt,
        D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1),
        D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (rfl) (K))).symm).inv)
    obtain ⟨j', hj', ψ', hψ'⟩ := hsurj'
    have hij : i'.1 ≤ j'.1 := hj'
    have h1 : (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS)) =
        (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op i')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS)) :=
        ObjectProperty.hom_ext _ ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.w (homOfLE hj').op)
    have h2 : (ObjectProperty.homMk (D.limitCone.π.app (op j'.1)) :
        (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk (D.system.map (homOfLE hij).op) : (⟨D.system.obj (op j'.1),
        D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1),
        D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS)) = (ObjectProperty.homMk
        (D.limitCone.π.app (op i'.1)) : (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B
        S hS) ⟶ (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS)) :=
        ObjectProperty.hom_ext _ (D.limitCone.w (homOfLE hij).op)
    have hψ := (derivedPullback (spacesEtaleModelHom B S hS ((τ j').hom))).map_surjective
        (((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
        ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.map (homOfLE hj').op) : (⟨(D.restrictTo (D.algebraicSpace D.base)
        (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'),
        (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
        (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (rfl) (E)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((τ j').hom)
        ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (ht hj')
        (E))).symm).inv ≫ ψ' ≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (rfl) (K)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((τ j').hom)
        ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (ht hj')
        (K))).symm).hom)
    obtain ⟨ψ, hψ⟩ := hψ
    have hψ'' : ψ' = ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (rfl) (E)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((τ j').hom)
        ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (ht hj')
        (E))).symm).hom ≫ (derivedPullback (spacesEtaleModelHom B S hS ((τ j').hom))).map ψ ≫
        ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
        ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.map (homOfLE hj').op) : (⟨(D.restrictTo (D.algebraicSpace D.base)
        (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'),
        (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
        (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (rfl) (K)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((τ j').hom)
        ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (ht hj')
        (K))).symm).inv := by
      exact ((Iso.eq_comp_inv _).mpr ((Iso.eq_inv_comp _).mp hψ).symm).trans (Category.assoc _ _ _)
    refine ⟨j'.1, hij, ψ, ?_⟩
    apply (derivedPullback (spacesEtaleModelHom B S hS (σ.hom))).map_injective
    have cohE := spacesEtaleModelDerivedPullbackCompIsoOfEq_square_coherence B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS)))
        (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))
      ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op i')) :
          (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op i'),
          (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) (τ i').hom (τ j').hom
          (ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
          (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS)) σ.hom
          ((ObjectProperty.homMk (D.limitCone.π.app (op j'.1)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS)))
          ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) h1 h2
          (ht hj') (hπ j') (hπ i') E
    have cohK := spacesEtaleModelDerivedPullbackCompIsoOfEq_square_coherence B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS)))
        (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))
      ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op i')) :
          (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ :
          AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op i'),
          (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) (τ i').hom (τ j').hom
          (ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
          (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS)) σ.hom
          ((ObjectProperty.homMk (D.limitCone.π.app (op j'.1)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS)))
          ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) h1 h2
          (ht hj') (hπ j') (hπ i') K
    have cohKI : ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS)))
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) (h1)
        ((derivedPullback (spacesEtaleModelHom B S hS ((τ i').hom))).obj K))).symm ≪≫
        (derivedPullback (spacesEtaleModelHom B S hS ((ObjectProperty.homMk
            ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
            (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base)
            (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ :
            AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo (D.algebraicSpace D.base)
            (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'),
            (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS))))).mapIso
            ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
            ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
            (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'), (D.restrictTo
            (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
            (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).system.obj (op i'), (D.restrictTo
            (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
            (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom) (rfl) (K)) ≪≫
            ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((τ j').hom)
            ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
            (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (ht hj')
            (K))).symm) ≪≫
          (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
              ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
              (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
              (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
              (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base)
              (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo (D.algebraicSpace D.base)
              (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'),
              (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
              (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS)))
              ((τ j').hom) (hπ j') ((derivedPullback (spacesEtaleModelHom B S hS
              ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
              (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))))).obj K))
              =
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
            ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op i')) :
            (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base)
            (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ :
            AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo (D.algebraicSpace D.base)
            (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op i'),
            (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
            (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS)))
            ((τ i').hom) (hπ i') (K)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS (σ.hom)
            ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (rfl)
            (K))).symm ≪≫
          (derivedPullback (spacesEtaleModelHom B S hS (σ.hom))).mapIso
              ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
              (D.limitCone.π.app (op j'.1)) : (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ :
              AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ :
              AlgebraicSpaces B S hS))) ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
              (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (h2)
              (K))).symm ≪≫ (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS (σ.hom)
              ((ObjectProperty.homMk (D.limitCone.π.app (op j'.1)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS))) (rfl)
              ((derivedPullback (spacesEtaleModelHom B S hS ((ObjectProperty.homMk
              (D.system.map (homOfLE hij).op) : (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ :
              AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ :
              AlgebraicSpaces B S hS))))).obj K)) :=
      Iso.ext (by simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using cohK)
    have cohK' := congrArg Iso.inv cohKI
    have N1 := spacesEtaleModelDerivedPullback_map_map_eq B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op j')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op j'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS))) (τ j').hom
        (hπ j') ψ
    have N2 := spacesEtaleModelDerivedPullback_map_map_eq B S hS σ.hom
        ((ObjectProperty.homMk (D.limitCone.π.app (op j'.1)) : (⟨D.limitCone.pt,
        D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op j'.1),
        D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS))) rfl ψ
    have e1 : (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).stageProjectionDerivedPullbackIso hj'
        ((derivedPullback (spacesEtaleModelHom B S hS ((τ i').hom))).obj E) =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
          ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).limitCone.π.app (op j')) : (⟨(D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt,
          (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'), (D.restrictTo
          (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS))) ((ObjectProperty.homMk
          ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).system.map (homOfLE hj').op) : (⟨(D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'),
          (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
          (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) (h1)
          ((derivedPullback (spacesEtaleModelHom B S hS ((τ i').hom))).obj E)) := rfl
    have e2 : (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).stageProjectionDerivedPullbackIso hj'
        ((derivedPullback (spacesEtaleModelHom B S hS ((τ i').hom))).obj K) =
      (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
          ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).limitCone.π.app (op j')) : (⟨(D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt,
          (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'), (D.restrictTo
          (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS))) ((ObjectProperty.homMk
          ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).system.map (homOfLE hj').op) : (⟨(D.restrictTo (D.algebraicSpace D.base)
          (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'),
          (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
          (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) (h1)
          ((derivedPullback (spacesEtaleModelHom B S hS ((τ i').hom))).obj K)) := rfl
    have e3 : D.stageProjectionDerivedPullbackIso hij E =
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
        (D.limitCone.π.app (op j'.1)) : (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B
        S hS) ⟶ (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS)))
        ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (h2) (E)) :=
        rfl
    have e4 : D.stageProjectionDerivedPullbackIso hij K =
        (spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
        (D.limitCone.π.app (op j'.1)) : (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B
        S hS) ⟶ (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS)))
        ((ObjectProperty.homMk (D.system.map (homOfLE hij).op) :
        (⟨D.system.obj (op j'.1), D.algebraicSpace j'.1⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨D.system.obj (op i'.1), D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (h2) (K)) :=
        rfl
    rw [← cancel_epi ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS
        ((ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitCone.π.app (op i')) :
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.pt, (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
        (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (hπ i') (E)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS (σ.hom)
        ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) : (⟨D.limitCone.pt,
        D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1),
        D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (rfl) (E))).symm).hom, ← cancel_mono
        ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS ((ObjectProperty.homMk
        ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.π.app (op i')) : (⟨(D.restrictTo (D.algebraicSpace D.base)
        (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt,
        (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
        (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS))) ((τ i').hom)
        (hπ i') (K)) ≪≫ ((spacesEtaleModelDerivedPullbackCompIsoOfEq B S hS (σ.hom)
        ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) : (⟨D.limitCone.pt,
        D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1),
        D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) (rfl) (K))).symm).inv]
    simp only [Category.assoc]
    simp only [hψ', hψ'']
    simp only [e1, e2, e3, e4]
    simp only [Functor.map_comp, N1, N2]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.map_comp,
      Functor.mapIso_inv, Category.assoc] at cohE cohK' ⊢
    simp only [reassoc_of% cohE, cohK']
  · have h1 := (spacesEtaleModelDerivedPullback_map_map_eq_iff B S hS σ.hom
        ((ObjectProperty.homMk (D.limitCone.π.app (op i'.1)) : (⟨D.limitCone.pt,
        D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨D.system.obj (op i'.1),
        D.algebraicSpace i'.1⟩ : AlgebraicSpaces B S hS))) ((ObjectProperty.homMk
        ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitCone.π.app (op i')) : (⟨(D.restrictTo (D.algebraicSpace D.base)
        (D.quasiCompact D.base) (D.quasiSeparated D.base) (𝟙 _)).limitCone.pt,
        (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
        (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
        (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
        (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS)))
      (τ i').hom (hπ i').symm φ ψ).mp (congrArg (derivedPullback
          (spacesEtaleModelHom B S hS σ.hom)).map hφψ)
    obtain ⟨j', hj', hj⟩ := hinj _ _ h1
    have h2 := (spacesEtaleModelDerivedPullback_map_map_eq_iff B S hS
      (ObjectProperty.homMk ((D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).system.map (homOfLE hj').op) :
          (⟨(D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).system.obj (op j'), (D.restrictTo
          (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).algebraicSpace j'⟩ : AlgebraicSpaces B S hS) ⟶ (⟨(D.restrictTo
          (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base)
          (𝟙 _)).system.obj (op i'), (D.restrictTo (D.algebraicSpace D.base) (D.quasiCompact D.base)
          (D.quasiSeparated D.base) (𝟙 _)).algebraicSpace i'⟩ : AlgebraicSpaces B S hS)) (τ i').hom
      (τ j').hom (ObjectProperty.homMk (D.system.map (homOfLE (show i'.1 ≤ j'.1 from hj')).op))
      (ht hj').symm φ ψ).mp hj
    refine ⟨j'.1, hj', ?_⟩
    exact (derivedPullback (spacesEtaleModelHom B S hS (τ j').hom)).map_injective h2

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Stacks 09RJ, full faithfulness**: in Situation 09RH with bounded charts, for perfect objects
`Eᵢ`, `Kᵢ` on a stage `Xᵢ`, `colim_{j ≥ i} Hom(Lf_{ji}^*Eᵢ, Lf_{ji}^*Kᵢ) ⟶ Hom(Lfᵢ^*Eᵢ, Lfᵢ^*Kᵢ)`
is bijective. The induction of Stacks 08GP over the quasi-compact quasi-separated objects of
`(X₀)_{spaces,étale}`: the affine case
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_restrictTo_of_isAffineSpace`, the
Mayer–Vietoris step
`DescentSituation.perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare`, and
`AlgebraicGeometry.Space.DescentSituation.perfectHomsDescend_of_restrictTo_id`. -/
theorem perfectHomsDescend_of_chartsBounded (hb : ChartsBounded B S hS D.system) :
    D.PerfectHomsDescend := by
  have h := qcqs_induction_on_self B S hS hZ
    ⟨D.system.obj (op D.base), D.algebraicSpace D.base⟩ (D.quasiCompact D.base)
    (D.quasiSeparated D.base) (fun _ y => D.RestrictedHomsDescend y)
    (fun V hV hU₀ hU₀qc hU₀qs =>
      D.perfectHomsDescend_restrictTo_of_isAffineSpace hU₀ hU₀qc hU₀qs _ hb hV)
    (fun W V U f hf hsq hWqc hWqs hUqc hVaff hFU hFV hFP hW' hWqc' hWqs' => by
      obtain ⟨hUa, hUqs, hVqc, hVqs, hPa, hPqc, hPqs⟩ :=
        isAlgebraicSpace_and_qcqs_of_isElementaryDistinguishedSquare W.1.left.property U f hsq
          hWqs hUqc hVaff
      have hFV' := hFV hsq.isAlgebraicSpace hVqc hVqs
      rw [← hf] at hFV'
      exact D.perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare hW' hWqc' hWqs'
        W.1.hom.hom U f hsq hUa hUqc hUqs hVqc hVqs hPa hPqc hPqs (hFU hUa hUqc hUqs) hFV'
        (hFP hPa hPqc hPqs))
  exact D.perfectHomsDescend_of_restrictTo_id
    (h (D.algebraicSpace D.base) (D.quasiCompact D.base) (D.quasiSeparated D.base))

/-- **Stacks 09RJ.** In Situation 09RH (`X = lim Xᵢ` along affine transition morphisms of
quasi-compact quasi-separated algebraic spaces) the category of perfect objects of `D(𝒪_X)` is the
colimit of the categories of perfect objects of `D(𝒪_{Xᵢ})`: every perfect object on `X` is
`Lfᵢ^*Eᵢ` for some stage `i` and some perfect `Eᵢ`
(`AlgebraicGeometry.Space.DescentSituation.PerfectObjectsDescend`), and for perfect `Eᵢ`, `Kᵢ`
on `Xᵢ` the map `colim_{j ≥ i} Hom(Lf_{ji}^*Eᵢ, Lf_{ji}^*Kᵢ) ⟶ Hom(Lfᵢ^*Eᵢ, Lfᵢ^*Kᵢ)` is
bijective (`AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend`).

**Correction.** The statement carries the hypothesis `ChartsBounded` (the size bound
`AlgebraicGeometry.Space.ChartsBounded` on the chart systems of the stages), which the source does
not state: the sites here are `u`-small models of the big fppf site with a size cutoff, and the
bound is what keeps the limits of the affine charts of the stages inside the site
(`AlgebraicGeometry.Space.ChartsBounded.sizeBound`). It holds for instance when `#I` is below the
cofinality of the cutoff (`AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord`). -/
@[stacks 09RJ "Under the size bound `ChartsBounded` on the chart systems of the stages, which the
source does not state (the sites are size-bounded models of the big fppf site)."]
theorem perfectObjectsDescend_and_perfectHomsDescend (hb : ChartsBounded B S hS D.system) :
    D.PerfectObjectsDescend ∧ D.PerfectHomsDescend :=
  ⟨D.perfectObjectsDescend_of_chartsBounded hb, D.perfectHomsDescend_of_chartsBounded hb⟩

end DescentSituation

end AlgebraicGeometry.Space

end
