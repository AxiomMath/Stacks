module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ConeChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.EnvelopeMapPresentation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NoetherianComponentEnvelope
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The Chern classes of a distinguished triangle of perfect objects

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of perfect
objects of `D(𝒪_X)`. **Stacks 0F9F** says that if there is an envelope `f : Y ⟶ X` such that
`Lf^*E₁ ⟶ Lf^*E₂` is represented by a map of locally bounded complexes of finite locally free
`𝒪_Y`-modules (or one of the conditions implying this), then the Chern classes of `E₁`, `E₂`,
`E₃` are defined and

  `c(E₂) = c(E₁) c(E₃)`,   `ch(E₂) = ch(E₁) + ch(E₃)`,   `P_p(E₂) = P_p(E₁) + P_p(E₃)`.

## The proof

As in the source: if `α : 𝓔₁^• ⟶ 𝓔₂^•` represents `Lf^*E₁ ⟶ Lf^*E₂`, the mapping cone `C(α)^•`
represents `Lf^*E₃` — `Lf^*` is exact (Stacks 06YJ) and a distinguished triangle is determined up
to isomorphism by its first morphism — and it is a locally bounded complex of finite locally free
modules. So the Chern classes of the three objects are defined, and their restrictions along `f`
are the total Chern classes and power sums of `𝓔₁^•`, `𝓔₂^•`, `C(α)^•`, which satisfy the three
relations (`Stacks.Chow.complexChern_eq_mul_mappingCone`,
`Stacks.Chow.powerSumComplex_eq_add_mappingCone`). Restriction along an envelope is injective.

## Main definitions

* `Stacks.Chow.HasEnvelopeMapPresentation` — condition (1) of Stacks 0F9F.
* `Stacks.Chow.HasMapPresentation` — condition (2) of Stacks 0F9F.

## Main results

* `Stacks.Chow.hasEnvelopeMapPresentation_of_hasMapPresentation` — (2) implies (1).
* `Stacks.Chow.hasDefinedChernClasses_obj₁_of_hasEnvelopeMapPresentation`, `_obj₂_`, `_obj₃_` —
  the Chern classes of the three objects are defined under (1).
* `Stacks.Chow.perfectChernClass_obj₂_of_hasEnvelopeMapPresentation`,
  `Stacks.Chow.perfectPowerSum_obj₂_of_hasEnvelopeMapPresentation`,
  `Stacks.Chow.perfectChernCharacter_obj₂_of_hasEnvelopeMapPresentation` — the three relations
  under (1).

## References

* [Stacks Project, Tag 0F9F](https://stacks.math.columbia.edu/tag/0F9F)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-- **Condition (1) of Stacks 0F9F**: there is an envelope `f : Y ⟶ X` such that `Lf^*a` is
represented by a map of locally bounded complexes of finite locally free `𝒪_Y`-modules. -/
def HasEnvelopeMapPresentation {E₁ E₂ : DerivedCategory X.Modules} (a : E₁ ⟶ E₂) : Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P₁ P₂ : CochainComplex Y.Modules ℤ)
    (α : P₁ ⟶ P₂) (e₁ : DerivedCategory.Q.obj P₁ ≅ (derivedPullback f.toLRSHom.toShHom).obj E₁)
    (e₂ : DerivedCategory.Q.obj P₂ ≅ (derivedPullback f.toLRSHom.toShHom).obj E₂),
    IsLocallyBoundedFiniteLocallyFree P₁ ∧ IsLocallyBoundedFiniteLocallyFree P₂ ∧
      DerivedCategory.Q.map α ≫ e₂.hom = e₁.hom ≫ (derivedPullback f.toLRSHom.toShHom).map a

/-- **Condition (2) of Stacks 0F9F**: `a` is represented by a map of locally bounded complexes of
finite locally free `𝒪_X`-modules. -/
def HasMapPresentation {E₁ E₂ : DerivedCategory X.Modules} (a : E₁ ⟶ E₂) : Prop :=
  ∃ (P₁ P₂ : CochainComplex X.Modules ℤ) (α : P₁ ⟶ P₂) (e₁ : DerivedCategory.Q.obj P₁ ≅ E₁)
    (e₂ : DerivedCategory.Q.obj P₂ ≅ E₂),
    IsLocallyBoundedFiniteLocallyFree P₁ ∧ IsLocallyBoundedFiniteLocallyFree P₂ ∧
      DerivedCategory.Q.map α ≫ e₂.hom = e₁.hom ≫ a

/-- **Condition (2) of Stacks 0F9F implies condition (1)**: the identity of `X` is an envelope and
`L(𝟙 X)^* ≅ 𝟭`. -/
theorem hasEnvelopeMapPresentation_of_hasMapPresentation {E₁ E₂ : DerivedCategory X.Modules}
    {a : E₁ ⟶ E₂} (h : HasMapPresentation a) : HasEnvelopeMapPresentation a := by
  obtain ⟨P₁, P₂, α, e₁, e₂, h₁, h₂, w⟩ := h
  let ι := Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso X.toRingedSpace
  refine ⟨X, 𝟙 X, ⟨inferInstance, isCompletelyDecomposed_id X⟩, P₁, P₂, α, e₁ ≪≫ (ι.app E₁).symm,
    e₂ ≪≫ (ι.app E₂).symm, h₁, h₂, ?_⟩
  change DerivedCategory.Q.map α ≫ e₂.hom ≫ ι.inv.app E₂ = (e₁.hom ≫ ι.inv.app E₁) ≫ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ι.inv.app E₂) w).trans
    ((Category.assoc _ _ _).trans ((congrArg (e₁.hom ≫ ·) (ι.inv.naturality a)).trans
      (Category.assoc _ _ _).symm)))

/-- `Lf^* : D(𝒪_X) ⥤ D(𝒪_Y)` for a morphism of schemes, in the scheme spelling of the categories
of modules. -/
abbrev schemeDerivedPullback {Y : Scheme.{u}} (f : Y ⟶ X) :
    DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  derivedPullback f.toLRSHom.toShHom

/-- `Lf^*` commutes with the shift, by Stacks 06YJ. -/
instance {Y : Scheme.{u}} (f : Y ⟶ X) : (schemeDerivedPullback f).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := f.toLRSHom.toShHom)

/-- `Lf^*` is exact, by Stacks 06YJ. -/
instance {Y : Scheme.{u}} (f : Y ⟶ X) : (schemeDerivedPullback f).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
    (f := f.toLRSHom.toShHom)

/-- **The representing complexes of a distinguished triangle under condition (1) of Stacks 0F9F.**
If `α : 𝓔₁^• ⟶ 𝓔₂^•` represents `Lf^*E₁ ⟶ Lf^*E₂` on an envelope `f : Y ⟶ X`, then `𝓔₁^•`, `𝓔₂^•`
and the mapping cone `C(α)^•` represent `Lf^*E₁`, `Lf^*E₂`, `Lf^*E₃`: `Lf^*` is exact (Stacks 06YJ)
and a distinguished triangle is determined up to isomorphism by its first morphism. -/
theorem exists_envelope_triangle_presentation (T : Triangle (DerivedCategory X.Modules))
    (hT : T ∈ distTriang _) (h : HasEnvelopeMapPresentation T.mor₁) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsEnvelope f) (P₁ P₂ : CochainComplex Y.Modules ℤ)
      (α : P₁ ⟶ P₂) (_ : IsLocallyBoundedFiniteLocallyFree P₁)
      (_ : IsLocallyBoundedFiniteLocallyFree P₂),
      Nonempty ((derivedPullback f.toLRSHom.toShHom).obj T.obj₁ ≅ DerivedCategory.Q.obj P₁) ∧
      Nonempty ((derivedPullback f.toLRSHom.toShHom).obj T.obj₂ ≅ DerivedCategory.Q.obj P₂) ∧
      Nonempty ((derivedPullback f.toLRSHom.toShHom).obj T.obj₃ ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone (C := Y.Modules) α)) := by
  obtain ⟨Y, f, hf, P₁, P₂, α, e₁, e₂, h₁, h₂, w⟩ := h
  exact ⟨Y, f, hf, P₁, P₂, α, h₁, h₂, ⟨e₁.symm⟩, ⟨e₂.symm⟩, ⟨(Triangle.π₃.mapIso
    (isoTriangleOfIso₁₂ _ _ (DerivedCategory.mappingCone_triangle_distinguished α)
      ((schemeDerivedPullback f).map_distinguished T hT) e₁ e₂ w)).symm⟩⟩

section Classes

variable (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang _)
  (h : HasEnvelopeMapPresentation T.mor₁)

include hT h

/-- **Stacks 0F9F, definedness for `E₁`.** -/
theorem hasDefinedChernClasses_obj₁_of_hasEnvelopeMapPresentation :
    HasDefinedChernClasses T.obj₁ := by
  obtain ⟨Y, f, hf, P₁, P₂, α, h₁, h₂, ⟨e₁⟩, -, -⟩ :=
    exists_envelope_triangle_presentation T hT h
  exact hasDefinedChernClasses_of_envelope f hf _ P₁ h₁ ⟨e₁⟩

/-- **Stacks 0F9F, definedness for `E₂`.** -/
theorem hasDefinedChernClasses_obj₂_of_hasEnvelopeMapPresentation :
    HasDefinedChernClasses T.obj₂ := by
  obtain ⟨Y, f, hf, P₁, P₂, α, h₁, h₂, -, ⟨e₂⟩, -⟩ :=
    exists_envelope_triangle_presentation T hT h
  exact hasDefinedChernClasses_of_envelope f hf _ P₂ h₂ ⟨e₂⟩

/-- **Stacks 0F9F, definedness for `E₃`**: the mapping cone represents `Lf^*E₃`. -/
theorem hasDefinedChernClasses_obj₃_of_hasEnvelopeMapPresentation :
    HasDefinedChernClasses T.obj₃ := by
  obtain ⟨Y, f, hf, P₁, P₂, α, h₁, h₂, -, -, ⟨e₃⟩⟩ :=
    exists_envelope_triangle_presentation T hT h
  exact hasDefinedChernClasses_of_envelope f hf _ _
    (isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂) ⟨e₃⟩

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0F9F, the total Chern class**: `c(E₂) = c(E₁) c(E₃)`. -/
theorem perfectChernClass_obj₂_of_hasEnvelopeMapPresentation (d₁ : HasDefinedChernClasses T.obj₁)
    (d₂ : HasDefinedChernClasses T.obj₂) (d₃ : HasDefinedChernClasses T.obj₃) :
    perfectChernClass C sX d₂ = perfectChernClass C sX d₁ * perfectChernClass C sX d₃ := by
  obtain ⟨Y, f, hf, P₁, P₂, α, h₁, h₂, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_envelope_triangle_presentation T hT h
  have := hf.isProper
  refine TotalChowClass.res_injective_of_isEnvelope f hf rfl ?_
  rw [map_mul, res_perfectChernClass C sX d₂ ⟨Y, f, hf, P₂, h₂, ⟨e₂⟩⟩,
    res_perfectChernClass C sX d₁ ⟨Y, f, hf, P₁, h₁, ⟨e₁⟩⟩,
    res_perfectChernClass C sX d₃
      ⟨Y, f, hf, _, isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂, ⟨e₃⟩⟩]
  exact complexChern_eq_mul_mappingCone C (f ≫ sX) h₁ h₂ α

/-- **Stacks 0F9F, the power sums**: `P_p(E₂) = P_p(E₁) + P_p(E₃)`. -/
theorem perfectPowerSum_obj₂_of_hasEnvelopeMapPresentation (d₁ : HasDefinedChernClasses T.obj₁)
    (d₂ : HasDefinedChernClasses T.obj₂) (d₃ : HasDefinedChernClasses T.obj₃) (p : ℕ) :
    perfectPowerSum C sX d₂ p = perfectPowerSum C sX d₁ p + perfectPowerSum C sX d₃ p := by
  obtain ⟨Y, f, hf, P₁, P₂, α, h₁, h₂, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_envelope_triangle_presentation T hT h
  have := hf.isProper
  refine TotalChowClass.res_injective_of_isEnvelope f hf rfl ?_
  rw [map_add, res_perfectPowerSum_eq_powerSumComplex C sX d₂ ⟨Y, f, hf, P₂, h₂, ⟨e₂⟩⟩ p,
    res_perfectPowerSum_eq_powerSumComplex C sX d₁ ⟨Y, f, hf, P₁, h₁, ⟨e₁⟩⟩ p,
    res_perfectPowerSum_eq_powerSumComplex C sX d₃
      ⟨Y, f, hf, _, isLocallyBoundedFiniteLocallyFree_mappingCone α h₁ h₂, ⟨e₃⟩⟩ p]
  exact powerSumComplex_eq_add_mappingCone C (f ≫ sX) h₁ h₂ α p

/-- **Stacks 0F9F, the Chern character**: `ch_p(E₂) = ch_p(E₁) + ch_p(E₃)` in every degree. -/
theorem perfectChernCharacter_obj₂_of_hasEnvelopeMapPresentation
    (d₁ : HasDefinedChernClasses T.obj₁) (d₂ : HasDefinedChernClasses T.obj₂)
    (d₃ : HasDefinedChernClasses T.obj₃) (p : ℕ) :
    perfectChernCharacterComponent C sX d₂ p =
      perfectChernCharacterComponent C sX d₁ p + perfectChernCharacterComponent C sX d₃ p := by
  rw [perfectChernCharacterComponent, perfectChernCharacterComponent,
    perfectChernCharacterComponent, ← TensorProduct.tmul_add]
  congr 1
  change perfectPowerSum C sX d₂ p p = perfectPowerSum C sX d₁ p p + perfectPowerSum C sX d₃ p p
  rw [perfectPowerSum_obj₂_of_hasEnvelopeMapPresentation T hT h C sX d₁ d₂ d₃ p]
  rfl

end Classes

/-! ### Stacks 0F9F -/

section Tag

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The four conditions of Stacks 0F9F** on a morphism `a : E₁ ⟶ E₂` of `D(𝒪_X)`: (1) after some
envelope `a` is represented by a map of locally bounded complexes of finite locally free modules,
(2) `a` is so represented on `X`, (3) the irreducible components of `X` are quasi-compact, or
(4) `X` is quasi-compact. (The source's item (5), "add more here", is a placeholder and states no
condition.) -/
def HasTriangleChernCondition {E₁ E₂ : DerivedCategory X.Modules} (a : E₁ ⟶ E₂) : Prop :=
  HasEnvelopeMapPresentation a ∨ HasMapPresentation a ∨
    (∀ Z ∈ irreducibleComponents X, IsCompact Z) ∨ CompactSpace X

include C sX in
/-- Each of the four conditions of Stacks 0F9F gives condition (1), for perfect objects: (2) by the
identity envelope, (3) and (4) by the envelope of the proof of Stacks 0GUE (3). -/
theorem HasTriangleChernCondition.hasEnvelopeMapPresentation {E₁ E₂ : DerivedCategory X.Modules}
    {a : E₁ ⟶ E₂} (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₁)
    (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E₂)
    (h : HasTriangleChernCondition a) : HasEnvelopeMapPresentation a := by
  rcases h with h | h | h | h
  · exact h
  · exact hasEnvelopeMapPresentation_of_hasMapPresentation h
  · exact exists_envelope_mapPresentation_of_isCompact_irreducibleComponents C sX h h₁ h₂ a
  · exact exists_envelope_mapPresentation_of_compactSpace C sX h₁ h₂ a

variable (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang _)
  (h₁ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) T.obj₁)
  (h₂ : Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) T.obj₂)
  (h : HasTriangleChernCondition T.mor₁)

include C sX hT h₁ h₂ h

/-- **Stacks 0F9F, definedness.** Let `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]` be a distinguished triangle of
perfect objects of `D(𝒪_X)` satisfying one of the conditions of Stacks 0F9F. Then the Chern
classes of `E₁`, `E₂` and `E₃` are defined. -/
@[stacks 0F9F "the Chern classes of E₁, E₂, E₃ are defined"]
theorem hasDefinedChernClasses_triangle :
    HasDefinedChernClasses T.obj₁ ∧ HasDefinedChernClasses T.obj₂ ∧
      HasDefinedChernClasses T.obj₃ :=
  have h' := h.hasEnvelopeMapPresentation C sX h₁ h₂
  ⟨hasDefinedChernClasses_obj₁_of_hasEnvelopeMapPresentation T hT h',
    hasDefinedChernClasses_obj₂_of_hasEnvelopeMapPresentation T hT h',
    hasDefinedChernClasses_obj₃_of_hasEnvelopeMapPresentation T hT h'⟩

/-- **Stacks 0F9F, the total Chern class.** Under the hypotheses of Stacks 0F9F,
`c(E₂) = c(E₁) c(E₃)`. -/
@[stacks 0F9F "c(E₂) = c(E₁) c(E₃)"]
theorem perfectChernClass_triangle (d₁ : HasDefinedChernClasses T.obj₁)
    (d₂ : HasDefinedChernClasses T.obj₂) (d₃ : HasDefinedChernClasses T.obj₃) :
    perfectChernClass C sX d₂ = perfectChernClass C sX d₁ * perfectChernClass C sX d₃ :=
  perfectChernClass_obj₂_of_hasEnvelopeMapPresentation T hT
    (h.hasEnvelopeMapPresentation C sX h₁ h₂) C sX d₁ d₂ d₃

/-- **Stacks 0F9F, the Chern character.** Under the hypotheses of Stacks 0F9F,
`ch(E₂) = ch(E₁) + ch(E₃)`, in every degree `p`. -/
@[stacks 0F9F "ch(E₂) = ch(E₁) + ch(E₃), in every degree"]
theorem perfectChernCharacter_triangle (d₁ : HasDefinedChernClasses T.obj₁)
    (d₂ : HasDefinedChernClasses T.obj₂) (d₃ : HasDefinedChernClasses T.obj₃) (p : ℕ) :
    perfectChernCharacterComponent C sX d₂ p =
      perfectChernCharacterComponent C sX d₁ p + perfectChernCharacterComponent C sX d₃ p :=
  perfectChernCharacter_obj₂_of_hasEnvelopeMapPresentation T hT
    (h.hasEnvelopeMapPresentation C sX h₁ h₂) C sX d₁ d₂ d₃ p

/-- **Stacks 0F9F, the power sums.** Under the hypotheses of Stacks 0F9F,
`P_p(E₂) = P_p(E₁) + P_p(E₃)` for every `p`. -/
@[stacks 0F9F "P_p(E₂) = P_p(E₁) + P_p(E₃)"]
theorem perfectPowerSum_triangle (d₁ : HasDefinedChernClasses T.obj₁)
    (d₂ : HasDefinedChernClasses T.obj₂) (d₃ : HasDefinedChernClasses T.obj₃) (p : ℕ) :
    perfectPowerSum C sX d₂ p = perfectPowerSum C sX d₁ p + perfectPowerSum C sX d₃ p :=
  perfectPowerSum_obj₂_of_hasEnvelopeMapPresentation T hT
    (h.hasEnvelopeMapPresentation C sX h₁ h₂) C sX d₁ d₂ d₃ p

end Tag

end Stacks.Chow

end
