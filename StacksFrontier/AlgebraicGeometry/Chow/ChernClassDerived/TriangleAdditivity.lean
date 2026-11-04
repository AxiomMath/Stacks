module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ConeRepresentation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Criteria
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.MappingConeRank
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NewtonAdditivity
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of a distinguished triangle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let

  `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]`

be a distinguished triangle in `D(𝒪_X)`. [Stacks, Tag 0F9F] lists conditions under each of which
the Chern classes of `E₁`, `E₂`, `E₃` are defined and

  `c(E₂) = c(E₁) c(E₃)`,  `ch(E₂) = ch(E₁) + ch(E₃)`,  `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

This file proves that conclusion under the source's condition (1) — some envelope `f : Y ⟶ X` has
`Lf^*E₁ ⟶ Lf^*E₂` represented by a map `α` of locally bounded complexes of finite locally free
`𝒪_Y`-modules — and under its condition (2), that such a map already exists over `X`.

## Main results

* `Stacks.Chow.hasDefinedChernClasses_and_additive_of_envelope` — the conclusion of Stacks 0F9F
  under condition (1) of the source.
* `Stacks.Chow.hasDefinedChernClasses_and_additive_of_map` — the conclusion of Stacks 0F9F under
  condition (2) of the source.

## Implementation notes

The three presentations share one envelope: `(f, 𝓔₁^•)` presents `E₁`, `(f, 𝓔₂^•)` presents `E₂`
and `(f, C(α)^•)` presents `E₃`, the cone being a locally bounded complex of finite locally free
modules (`Stacks.Chow.isLocallyBoundedFiniteLocallyFree_mappingCone`) that represents `Lf^*E₃`
(`Stacks.Chow.derivedPullback_obj₃_iso_mappingCone`). Each class of Stacks 0F9E (2) is the unique
one restricting along the envelope of a presentation to the corresponding class of the presenting
complex, so the three identities are the identities for the complexes:
`Stacks.Chow.complexChern_mappingCone` for `c`, `Stacks.Chow.complexRankClass_mappingCone` for the
rank, and then `P_p` and `ch` by Newton's recursion
(`Stacks.Chow.TotalChowClass.newtonPowerSum_mul_of_commute_homComponent`), whose side conditions
are `Stacks.Chow.perfectChernClass_apply_zero` and
`Stacks.Chow.commute_homComponent_perfectChernClass`.

`ch` and `P_p` are read componentwise, as the source reads them: `P_p(E) ∈ A^p(X)` is
`Stacks.Chow.perfectPowerSumComponent` and `ch_p(E) ∈ A^p(X) ⊗ 𝐐` is
`Stacks.Chow.perfectChernCharacterComponent`, and an equality in `∏_{p ≥ 0} (A^p(X) ⊗ 𝐐)` is an
equality of all components.

Condition (2) is condition (1) for the envelope `𝟙 X`, which is proper and completely decomposed;
the square identifying `α` with the first map of the triangle transports along the naturality of
`L(𝟙 X)^* ≅ 𝟭`.

Neither statement needs the objects of the triangle to be perfect. The condition of Stacks
0F9E (1) is about the derived category of `X` alone and so are these proofs, exactly as for the
criteria of Stacks 0GUE in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Criteria`.

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 0F9E](https://stacks.math.columbia.edu/tag/0F9E)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0F9C](https://stacks.math.columbia.edu/tag/0F9C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The conclusion of Stacks 0F9F**: the Chern classes of the three terms of the triangle are
defined, the total Chern class is multiplicative, and the Chern character and every power sum are
additive. The three classes are read at the three given presentations; since
`Stacks.Chow.HasDefinedChernClasses` is a proposition, the classes do not depend on which proof of
it is supplied. -/
def TriangleChernAdditive (T : Triangle (DerivedCategory X.Modules)) : Prop :=
  ∃ (hE₁ : HasDefinedChernClasses T.obj₁) (hE₂ : HasDefinedChernClasses T.obj₂)
    (hE₃ : HasDefinedChernClasses T.obj₃),
    perfectChernClass C sX hE₂ = perfectChernClass C sX hE₁ * perfectChernClass C sX hE₃ ∧
      perfectChernCharacter C sX hE₂ =
          perfectChernCharacter C sX hE₁ + perfectChernCharacter C sX hE₃ ∧
        (∀ p : ℕ, perfectChernCharacterComponent C sX hE₂ p =
            perfectChernCharacterComponent C sX hE₁ p +
              perfectChernCharacterComponent C sX hE₃ p) ∧
          ∀ p : ℕ, perfectPowerSumComponent C sX hE₂ p =
            perfectPowerSumComponent C sX hE₁ p + perfectPowerSumComponent C sX hE₃ p

/-- **Stacks 0F9F under condition (1) of the source.** Let `T` be a distinguished triangle of
`D(𝒪_X)`. If there is an envelope `f : Y ⟶ X` such that `Lf^*T.mor₁ : Lf^*E₁ ⟶ Lf^*E₂` is
represented by a map `α : 𝓔₁^• ⟶ 𝓔₂^•` of locally bounded complexes of finite locally free
`𝒪_Y`-modules, then the Chern classes of `E₁`, `E₂`, `E₃` are defined and

  `c(E₂) = c(E₁) c(E₃)`,  `ch_p(E₂) = ch_p(E₁) + ch_p(E₃)`,  `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

The cone of `α` is a locally bounded complex of finite locally free modules representing
`Lf^*E₃`, so `f` together with `𝓔₁^•`, `𝓔₂^•` and `C(α)^•` presents all three objects, and each
identity is the corresponding identity for those complexes. -/
@[stacks 0F9F "condition (1): there is an envelope f : Y -> X such that Lf^*E_1 -> Lf^*E_2 is \
represented by a map of locally bounded complexes of finite locally free O_Y-modules.  The \
conclusion is the whole one: the Chern classes of E_1, E_2 and E_3 are defined, c(E_2) = \
c(E_1)c(E_3), ch(E_2) = ch(E_1) + ch(E_3) and P_p(E_2) = P_p(E_1) + P_p(E_3), the last two read \
componentwise in A^p(X) tensor Q and in A^p(X) as the source reads them.  Perfectness of the \
three objects is a standing hypothesis of the source that no step of this proof uses, so it is \
omitted, exactly as for the criteria of Tag 0GUE"]
theorem hasDefinedChernClasses_and_additive_of_envelope
    (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang (DerivedCategory X.Modules))
    {Y : Scheme.{u}} (f : Y ⟶ X) (hf : IsEnvelope f)
    {P₁ P₂ : CochainComplex Y.Modules ℤ} (α : P₁ ⟶ P₂)
    (h₁ : IsLocallyBoundedFiniteLocallyFree P₁) (h₂ : IsLocallyBoundedFiniteLocallyFree P₂)
    (e₁ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj T.obj₁ ≅ DerivedCategory.Q.obj P₁)
    (e₂ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj T.obj₂ ≅ DerivedCategory.Q.obj P₂)
    (hα : e₁.hom ≫ DerivedCategory.Q.map α =
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).map T.mor₁ ≫ e₂.hom) :
    TriangleChernAdditive C sX T := by
  have hfp := hf.isProper
  have hflft : LocallyOfFiniteType f := inferInstance
  have hC := isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂
  obtain ⟨e₃⟩ := derivedPullback_obj₃_iso_mappingCone f T hT α e₁ e₂ hα
  set H₁ : EnvelopePresentation T.obj₁ := ⟨Y, f, hf, P₁, h₁, ⟨e₁⟩⟩ with hH₁
  set H₂ : EnvelopePresentation T.obj₂ := ⟨Y, f, hf, P₂, h₂, ⟨e₂⟩⟩ with hH₂
  set H₃ : EnvelopePresentation T.obj₃ :=
    ⟨Y, f, hf, CochainComplex.mappingCone α, hC, ⟨e₃⟩⟩ with hH₃
  have hchern : perfectChernClass C sX ⟨H₂⟩ =
      perfectChernClass C sX ⟨H₁⟩ * perfectChernClass C sX ⟨H₃⟩ :=
    (eq_perfectChernClass C sX ⟨H₂⟩ H₂ (by
      rw [map_mul, res_perfectChernClass C sX ⟨H₁⟩ H₁, res_perfectChernClass C sX ⟨H₃⟩ H₃]
      exact (complexChern_mappingCone C (f ≫ sX) α h₁ h₂).symm)).symm
  have hrank : perfectRankClass C sX ⟨H₂⟩ =
      perfectRankClass C sX ⟨H₁⟩ + perfectRankClass C sX ⟨H₃⟩ :=
    (eq_perfectRankClass C sX ⟨H₂⟩ H₂ (by
      rw [map_add, res_perfectRankClass C sX ⟨H₁⟩ H₁, res_perfectRankClass C sX ⟨H₃⟩ H₃]
      exact (complexRankClass_mappingCone C (f ≫ sX) α h₁ h₂).symm)).symm
  have hps : ∀ p : ℕ, perfectPowerSum C sX (⟨H₂⟩ : HasDefinedChernClasses T.obj₂) p =
      perfectPowerSum C sX (⟨H₁⟩ : HasDefinedChernClasses T.obj₁) p +
        perfectPowerSum C sX (⟨H₃⟩ : HasDefinedChernClasses T.obj₃) p := fun p ↦ by
    simp only [perfectPowerSum, hrank, hchern]
    exact TotalChowClass.newtonPowerSum_mul_of_commute_homComponent
      (perfectChernClass_apply_zero C sX ⟨H₁⟩) (perfectChernClass_apply_zero C sX ⟨H₃⟩)
      (commute_homComponent_perfectChernClass C sX ⟨H₁⟩ ⟨H₃⟩) _ _ p
  have hpsc : ∀ p : ℕ, perfectPowerSumComponent C sX (⟨H₂⟩ : HasDefinedChernClasses T.obj₂) p =
      perfectPowerSumComponent C sX (⟨H₁⟩ : HasDefinedChernClasses T.obj₁) p +
        perfectPowerSumComponent C sX (⟨H₃⟩ : HasDefinedChernClasses T.obj₃) p := fun p ↦
    congrFun (hps p) p
  have hch : ∀ p : ℕ,
      perfectChernCharacterComponent C sX (⟨H₂⟩ : HasDefinedChernClasses T.obj₂) p =
      perfectChernCharacterComponent C sX (⟨H₁⟩ : HasDefinedChernClasses T.obj₁) p +
        perfectChernCharacterComponent C sX (⟨H₃⟩ : HasDefinedChernClasses T.obj₃) p :=
    fun p ↦ by
      simp only [perfectChernCharacterComponent, hpsc p]
      exact TensorProduct.tmul_add _ _ _
  exact ⟨⟨H₁⟩, ⟨H₂⟩, ⟨H₃⟩, hchern, funext hch, hch, hpsc⟩

/-- **Stacks 0F9F under condition (2) of the source.** If the first map `T.mor₁ : E₁ ⟶ E₂` of a
distinguished triangle of `D(𝒪_X)` is itself represented by a map `α : 𝓔₁^• ⟶ 𝓔₂^•` of locally
bounded complexes of finite locally free `𝒪_X`-modules, then the Chern classes of `E₁`, `E₂`,
`E₃` are defined and

  `c(E₂) = c(E₁) c(E₃)`,  `ch_p(E₂) = ch_p(E₁) + ch_p(E₃)`,  `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

This is condition (1) for the envelope `𝟙 X`, which is proper and completely decomposed; the
square identifying `α` with `T.mor₁` transports along the naturality of `L(𝟙 X)^* ≅ 𝟭`. -/
@[stacks 0F9F "condition (2): E_1 -> E_2 is represented by a map of locally bounded complexes of \
finite locally free O_X-modules.  The conclusion is the whole one: the Chern classes of E_1, E_2 \
and E_3 are defined, c(E_2) = c(E_1)c(E_3), ch(E_2) = ch(E_1) + ch(E_3) and P_p(E_2) = P_p(E_1) \
+ P_p(E_3), the last two read componentwise in A^p(X) tensor Q and in A^p(X) as the source reads \
them.  Perfectness of the three objects is a standing hypothesis of the source that no step of \
this proof uses, so it is omitted, exactly as for the criteria of Tag 0GUE"]
theorem hasDefinedChernClasses_and_additive_of_map
    (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang (DerivedCategory X.Modules))
    {P₁ P₂ : CochainComplex X.Modules ℤ} (α : P₁ ⟶ P₂)
    (h₁ : IsLocallyBoundedFiniteLocallyFree P₁) (h₂ : IsLocallyBoundedFiniteLocallyFree P₂)
    (i₁ : T.obj₁ ≅ DerivedCategory.Q.obj P₁) (i₂ : T.obj₂ ≅ DerivedCategory.Q.obj P₂)
    (hα : i₁.hom ≫ DerivedCategory.Q.map α = T.mor₁ ≫ i₂.hom) :
    TriangleChernAdditive C sX T := by
  refine hasDefinedChernClasses_and_additive_of_envelope C sX T hT (𝟙 X)
    ⟨inferInstance, isCompletelyDecomposed_id X⟩ α h₁ h₂
    ((Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app T.obj₁ ≪≫ i₁)
    ((Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace).app T.obj₂ ≪≫ i₂)
    ?_
  have hnat : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (𝟙 X : X ⟶ X).toLRSHom.toShHom).map T.mor₁ ≫
      ((Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso
        X.toRingedSpace).app T.obj₂).hom =
      ((Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso
        X.toRingedSpace).app T.obj₁).hom ≫ T.mor₁ :=
    (Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso
      X.toRingedSpace).hom.naturality T.mor₁
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t ↦ ((Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso
        X.toRingedSpace).app T.obj₁).hom ≫ t) hα).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ i₂.hom) hnat.symm).trans (Category.assoc _ _ _))))


end Stacks.Chow

end
