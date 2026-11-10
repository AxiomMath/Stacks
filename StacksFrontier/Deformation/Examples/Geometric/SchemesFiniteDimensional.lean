module

public import StacksFrontier.Deformation.CofiberedPresentation.Criteria
public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.Examples.Geometric.NaiveCotangentCoherent
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsFiniteDimensionalDerivations
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismConjugationArrowLinear
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinearEquivExt
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# The deformation category of a proper scheme is finite dimensional (Stacks 0DYA)

Let `k` be a field and `X` a scheme proper over `k`, in the setting of Example 0DY7.
[Stacks Project, Tag 0DYA] states that `Inf(𝓓_X)` and `T𝓓_X` are finite dimensional `k`-vector
spaces. This file proves both, for the vector-space structures of [Stacks Project, Tag 06JV]
(on `Inf`) and of [Stacks Project, Tag 06IH] (on `T`).

## The tangent space

The source's proof: by [Stacks Project, Tag 0DY9], `T𝓓_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`
(`Deformation.Examples.schemeTangentSpaceLinearEquivExt`, read at the model of the derived
category in which it is constructed); by [Stacks Project, Tag 0D0K] and since `X` is Noetherian,
`NL_{X/k}` has coherent cohomology sheaves, zero except in degrees `-1` and `0`
(`AlgebraicGeometry.Scheme.isCoherent_homology_naiveCotangentComplex`); so by
[Stacks Project, Tag 0D0D] (`moduleFinite_ext_of_proper`) the `Ext` group is a finite
`k`-vector space.

## The infinitesimal automorphisms

The source writes `Inf(𝓓_X) = Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)` (Tag 0DY9) and
concludes again by Tag 0D0D. The vector space `Inf(𝓓_X)` of Tag 06JV is
`Deformation.localizedAutomorphismFunctorTangent`, the tangent space at the identity of the
automorphism functor of a point, with addition composition and scalar action transport along
`ε ↦ cε`. What is used of Tag 0DY9 is its first identification `Inf(𝓓_X) → Der_k(𝒪_X, 𝒪_X)`
**as a `k`-linear injection**: an infinitesimal automorphism `α` of the first-order deformation
`X'` goes to the derivation `D` with `α = D ⬝ id_{X'}`. In the library this is the arrow `b` of
[Stacks Project, Tag 0E3V] at the identity of `X`, `α ↦ b(α, 0)`
(`Deformation.Examples.schemeMorphismConjugationArrowLinear` at `f = 𝟙 X` and the lift
`f' = 𝟙 X'`), whose `k`-linearity for the structure of Tag 06JV is proved there; it is injective
because `b(α, 0) = 0` says that conjugating `id_{X'}` by `(α, id)` fixes it, i.e. `α = id`.
`Der_k(𝒪_X, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` is finite dimensional by Tag 0D0D
(`Deformation.Examples.finiteDimensional_schemeMorphismDerivations` at `f = 𝟙 X`).

## Main results

* `Deformation.Examples.finiteDimensional_localizedAutomorphismFunctorTangent_schemeDeformation`:
  **[Stacks Project, Tag 0DYA], `Inf(𝓓_X)`**, at every point and every choice of pushforwards.
* `Deformation.Examples.finiteDimensional_schemeTangentSpace`: **[Stacks Project, Tag 0DYA],
  `T𝓓_X`**.
* `Deformation.Examples.isFiniteDimensionalDeformationCategory_schemeDeformationCategoryProjection`
  — the two together with [Stacks Project, Tag 0DY8], as condition (4) of
  [Stacks Project, Tag 06TE].
* `Deformation.Examples.hasSmoothPresentation_schemeDeformationCategoryProjection`: the remark
  following Tag 0DYA — `𝓓_X` admits a presentation by a smooth prorepresentable groupoid in
  functors, by [Stacks Project, Tag 06L8].

## References

* [Stacks Project, Tag 0DYA](https://stacks.math.columbia.edu/tag/0DYA)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 0D0K](https://stacks.math.columbia.edu/tag/0D0K)
* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06L8](https://stacks.math.columbia.edu/tag/06L8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (X : Over (Spec (CommRingCat.of k)))

/-! ### The tangent space -/

/-- `NL_{X/k}` lies in `D^-_Coh(𝒪_X)`, at any model of the derived category: it lives in
cohomological degrees `≤ 0` and its cohomology sheaves are coherent
(`AlgebraicGeometry.Scheme.isCoherent_homology_naiveCotangentComplex`). -/
theorem derivedCategoryBMinus_naiveCotangentComplex [HasDerivedCategory X.left.Modules]
    [LocallyOfFiniteType X.hom] :
    DerivedCategoryB.derivedCategoryBMinus (fun M : X.left.Modules => M.IsCoherent)
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex X.hom) :
        DerivedCategory X.left.Modules) := by
  have e : ∀ n : ℤ, (DerivedCategory.homologyFunctor X.left.Modules n).obj
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex X.hom) :
        DerivedCategory X.left.Modules) ≅
      (Scheme.naiveCotangentComplex X.hom).homology n :=
    fun n => (DerivedCategory.homologyFunctorFactors X.left.Modules n).app _
  refine ⟨⟨0, fun n hn => ?_⟩, fun n => ?_⟩
  · exact (Scheme.isZero_homology_naiveCotangentComplex X.hom n (by omega) (by omega)).of_iso
      (e n)
  · exact ObjectProperty.prop_of_iso
      (P := fun N : SheafOfModules.{u} X.left.ringCatSheaf => N.IsCoherent) (e n).symm
      (Scheme.isCoherent_homology_naiveCotangentComplex X.hom n)

/-- **Stacks 0DYA, the tangent space.** For a scheme `X` proper over the field `k`, the tangent
space `T𝓓_X` of its deformation category ([Stacks Project, Tag 0DY7]) — the isomorphism classes
of flat deformations of `X` over `k[ε]`, with the canonical vector-space structure of
[Stacks Project, Tag 06IH] — is finite dimensional over `k`.

By [Stacks Project, Tag 0DY9] it is `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`
(`Deformation.Examples.schemeTangentSpaceLinearEquivExtRankOne` and
`Deformation.Examples.schemeTangentExtRankOneLinearEquiv`, the identification of
`Deformation.Examples.schemeTangentSpaceLinearEquivExt` before the change of model of the
derived category); `NL_{X/k}` is in `D^-_Coh(𝒪_X)` by [Stacks Project, Tag 0D0K]
(`derivedCategoryBMinus_naiveCotangentComplex`) and `𝒪_X` in `D^+_Coh(𝒪_X)`, so the `Ext` group
is finite dimensional by [Stacks Project, Tag 0D0D]. -/
@[stacks 0DYA "the tangent space clause: for X proper over k, T Def_X (isomorphism classes of \
flat deformations of X over k[eps], with the canonical vector space structure of 06IH) is \
finite dimensional over k"]
theorem finiteDimensional_schemeTangentSpace [IsProper X.hom] :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
      ⟨schlessingerConditionS2_schemeDeformation X⟩
    FiniteDimensional k (schemeTangentSpace (Λ := Λ) (k := k) X) := by
  let : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
  let : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
    ⟨schlessingerConditionS2_schemeDeformation X⟩
  let := schemeTangentExtStdModule X (structureSheafModules X.left)
  let E := (schemeTangentSpaceLinearEquivExtRankOne (Λ := Λ) X).trans
    (schemeTangentExtRankOneLinearEquiv X)
  let : Linear k X.left.Modules := modulesLinear k X
  let : HasDerivedCategory X.left.Modules := HasDerivedCategory.standard _
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : (SheafOfModules.unit X.left.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hL := derivedCategoryBBounded_singleFunctor_isCoherent X.left
    (SheafOfModules.unit X.left.ringCatSheaf) inferInstance
  have hfin := Stacks.AlgebraicGeometry.ProperSupportCoherent.moduleFinite_ext_of_proper X
    (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex X.hom) : DerivedCategory X.left.Modules)
    ((DerivedCategory.singleFunctor X.left.Modules 0).obj (SheafOfModules.unit X.left.ringCatSheaf))
    (derivedCategoryBMinus_naiveCotangentComplex X) ⟨hL.1.1, hL.2⟩ 1
  have : FiniteDimensional k (RingedSpaceThickening.extOneNaiveCotangent X.hom.toLRSHom.toShHom
      (structureSheafModules X.left)) := hfin
  exact E.symm.finiteDimensional

/-! ### The infinitesimal automorphisms -/

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

section Helper

variable {Y : Scheme.{u}} (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-- The identity of the total space of a deformation is a lift of the identity of `Y` to that
deformation and itself. -/
def globalLiftsOverBaseId {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (Q : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
      (Over.mk pY)) y₀) :
    globalLiftsOverBase (𝟙 Y) (firstOrderPushforwardCross Q) (firstOrderPushforwardCross Q)
      (eqToHom ((firstOrderPushforwardCross_base Q).trans
        (firstOrderPushforwardCross_base Q).symm)) :=
  ⟨𝟙 _, by simp [deformationAmbientToBase], by simp⟩

/-- **The infinitesimal automorphisms of `Y` as derivations, `k`-linearly.** The arrow `b` of
[Stacks Project, Tag 0E3V] at the identity of `Y` and the lift `𝟙` of it, restricted to the
first factor: an infinitesimal automorphism `α` of the chosen first-order deformation goes to the
derivation of `𝒪_Y` over `k` by which conjugating the identity by `(α, 𝟙)` displaces it. -/
def infinitesimalAutomorphismDerivationLinearMap
    {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (Q : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
      (Over.mk pY)) y₀) :
    letI := naturalLocalizedTangentAddCommGroup Q
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule Q
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
    letI := schemeMorphismDerivationsModule (𝟙 Y) pY
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
    localizedAutomorphismFunctorTangent Q →ₗ[k] schemeMorphismDerivations (𝟙 Y) pY :=
  letI := naturalLocalizedTangentAddCommGroup Q
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
  letI := naturalLocalizedTangentModule Q
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
  letI := schemeMorphismDerivationsModule (𝟙 Y) pY
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
  (schemeMorphismConjugationArrowLinear (𝟙 Y) pY pY (Category.id_comp _) Q Q
      (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (Over.mk pY))
      (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (Over.mk pY))
      (firstOrderPushforwardCrossConormalIsoUnit Q)
      (firstOrderPushforwardCross_maximalIdeal_pow_two Q) (globalLiftsOverBaseId pY Q)
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ)
        (Over.mk pY)).satisfiesRS).comp
    (LinearMap.inl k _ _)

/-- **The derivation attached to an infinitesimal automorphism determines it.** If `b(α, 0)`
vanishes, then conjugating the lift `𝟙` by `(α, 𝟙)` fixes it, so the self-map attached to `α`
is the one attached to `0`. -/
theorem injective_infinitesimalAutomorphismDerivationLinearMap
    {y₀ : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (Q : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
      (Over.mk pY)) y₀) :
    Function.Injective (infinitesimalAutomorphismDerivationLinearMap pY Q) := by
  let := naturalLocalizedTangentAddCommGroup Q
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
  let := naturalLocalizedTangentModule Q
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) (Over.mk pY)).satisfiesRS
  let := schemeMorphismDerivationsModule (𝟙 Y) pY
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  let hp := schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (Over.mk pY)
  let G := localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pY pY hp hp Q Q
    (eqToHom ((firstOrderPushforwardCross_base Q).trans
      (firstOrderPushforwardCross_base Q).symm)) (a, 0)
  have hvadd := globalLiftsOverBaseDerivationVAdd_conjDerivation (𝟙 Y) pY pY
    (Category.id_comp _) (firstOrderPushforwardCrossConormalIsoUnit Q)
    (firstOrderPushforwardCross_maximalIdeal_pow_two Q) (globalLiftsOverBaseId pY Q) G
  have h0 : globalLiftsOverBaseConjDerivation (𝟙 Y) pY pY (Category.id_comp _)
      (firstOrderPushforwardCrossConormalIsoUnit Q)
      (firstOrderPushforwardCross_maximalIdeal_pow_two Q) (globalLiftsOverBaseId pY Q) G = 0 :=
    ha
  rw [h0, globalLiftsOverBaseDerivationVAdd_zero] at hvadd
  have hcomm := (globalLiftsOverBaseAutPairConj_eq_iff (𝟙 Y) pY pY G
    (globalLiftsOverBaseId pY Q) (globalLiftsOverBaseId pY Q)).mp hvadd.symm
  have hself : (localizedTangentEquivSelfMapsCross hp Q a).1 =
      (localizedTangentEquivSelfMapsCross hp Q 0).1 := by
    have h1 : G.1.1 = (localizedTangentEquivSelfMapsCross hp Q a).1 := rfl
    have h2 : G.1.2 = (localizedTangentEquivSelfMapsCross hp Q 0).1 := rfl
    have h3 : (globalLiftsOverBaseId pY Q).1 = 𝟙 _ := rfl
    rw [h3, Category.id_comp, Category.comp_id, h1, h2] at hcomm
    exact hcomm.symm
  exact (localizedTangentEquivSelfMapsCross hp Q).injective (Subtype.ext hself)

end Helper

/-- **Stacks 0DYA, the infinitesimal automorphisms.** For a scheme `X` proper over the field `k`,
the `k`-vector space `Inf(𝓓_X)` of infinitesimal automorphisms of its deformation category
([Stacks Project, Tag 0DY7]) is finite dimensional. `Inf(𝓓_X)` is the tangent space at the
identity of the automorphism functor of a point `x₀` of the deformation category, with the
vector-space structure of [Stacks Project, Tag 06JV] (addition is composition, the scalar action
is transport along `ε ↦ cε`); this holds at every point `x₀` and every choice `P` of
pushforwards, in particular at the trivial deformation `X` over `k`.

The proof is the source's: `Inf(𝓓_X)` embeds `k`-linearly in `Der_k(𝒪_X, 𝒪_X)`
(`infinitesimalAutomorphismDerivationLinearMap`, injective by
`injective_infinitesimalAutomorphismDerivationLinearMap`), the identification of
[Stacks Project, Tag 0DY9], and `Der_k(𝒪_X, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` is finite
dimensional by [Stacks Project, Tag 0D0D]. -/
@[stacks 0DYA "the infinitesimal automorphism clause: for X proper over k, Inf(Def_X) is finite \
dimensional over k, with the vector space structure of 06JV, at every point of the deformation \
category and every choice of pushforwards"]
theorem finiteDimensional_localizedAutomorphismFunctorTangent_schemeDeformation [IsProper X.hom]
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) :
    letI := naturalLocalizedTangentAddCommGroup P
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).satisfiesRS
    letI := naturalLocalizedTangentModule P
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  let := naturalLocalizedTangentAddCommGroup P
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).satisfiesRS
  let := naturalLocalizedTangentModule P
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).satisfiesRS
  let := schemeMorphismDerivationsModule (Λ := Λ) (𝟙 X.left) X.hom
    (SheafOfModules.unit (structureSheafRing X.left.toRingedSpace))
  have : FiniteDimensional k (schemeMorphismDerivations (Λ := Λ) (𝟙 X.left) X.hom) :=
    finiteDimensional_schemeMorphismDerivations (Λ := Λ) (𝟙 X.left) X.hom
  exact FiniteDimensional.of_injective (infinitesimalAutomorphismDerivationLinearMap X.hom P)
    (injective_infinitesimalAutomorphismDerivationLinearMap X.hom P)

/-! ### The package -/

/-- **The deformation category of a proper `k`-scheme is a finite-dimensional deformation
category**: condition (4) of [Stacks Project, Tag 06TE] — it is a deformation category
([Stacks Project, Tag 0DY8]) whose tangent space and whose infinitesimal automorphisms are finite
dimensional ([Stacks Project, Tag 0DYA]). -/
theorem isFiniteDimensionalDeformationCategory_schemeDeformationCategoryProjection
    [IsProper X.hom] :
    IsFiniteDimensionalDeformationCategory
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) := by
  have hp := isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X
  refine ⟨hp, ?_, fun x _ PF => ?_⟩
  · exact finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace _ hp.predeformation
      (tangentConditionS2 hp) (finiteDimensional_schemeTangentSpace X)
  · exact finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hp.satisfiesRS PF
      (finiteDimensional_localizedAutomorphismFunctorTangent_schemeDeformation X PF)

/-- **The remark following [Stacks Project, Tag 0DYA].** For `X` proper over `k`, `𝓓_X` admits
a presentation by a smooth prorepresentable groupoid in functors over `𝒞_Λ`, by
[Stacks Project, Tag 06L8]. -/
theorem hasSmoothPresentation_schemeDeformationCategoryProjection [IsNoetherianRing Λ]
    [Module.Finite Λ k] [IsProper X.hom] :
    HasSmoothPresentation (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) :=
  (hasSmoothPresentation_iff_isFiniteDimensionalDeformationCategory _).mpr
    (isFiniteDimensionalDeformationCategory_schemeDeformationCategoryProjection X)

end Deformation.Examples

end
