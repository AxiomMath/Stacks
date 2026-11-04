module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagramReduction

/-!
# Stacks 088S from Stacks 088Q

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces with `Y` Noetherian.
Assuming the conclusion of Stacks 088Q for quasi-compact quasi-separated bases, in the shape of
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`, there are
a dense open subspace `U ⊆ X`, an integer `n` and an immersion `U ⟶ ℙⁿ_Y` over `Y` for which the
diagram of Stacks 088S exists. Stacks 088R from the conclusion of Stacks 088Q is
`AlgebraicGeometry.Space.hasChowBlowupDiagram_of_commonAdmissibleBlowup`.

Stacks 088S itself is `AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram`, Stacks 088R
is `AlgebraicGeometry.Space.hasChowBlowupDiagram_of_isFiniteType_of_isSeparated`, and Stacks 088Q
is proved in `StacksFrontier.AlgebraicGeometry.Spaces.CommonAdmissibleBlowupUnconditional`.

## Main results

* `AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram_of_commonAdmissibleBlowup`:
  Stacks 088S, given the conclusion of Stacks 088Q as the hypothesis `hcommon`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 088S, from Stacks 088Q.**  Let `f : X ⟶ Y` be a separated morphism of finite type
of algebraic spaces over `S` with `Y` Noetherian, and assume the conclusion `hcommon` of
Stacks 088Q, in the shape of
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`.  Then
there are a dense open subspace `U ⊆ X`, an integer `n` and an immersion `i : U ⟶ ℙⁿ_Y` over `Y`
for which the diagram of Stacks 088S exists (`AlgebraicGeometry.Space.HasChowBlowupDiagram`). -/
theorem exists_denseOpen_hasChowBlowupDiagram_of_commonAdmissibleBlowup
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hcommon : ∀ {Y U X₁ X₂ : AlgebraicSpaces B S hS}
      (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂),
      IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
      ∀ (hj₁ : IsOpenImmersion B S hS j₁.hom) (hj₂ : IsOpenImmersion B S hS j₂.hom),
      j₁ ≫ f₁ = j₂ ≫ f₂ →
      IsFiniteType B S hS (j₁ ≫ f₁).hom → IsSeparated B S hS (j₁ ≫ f₁).hom →
      IsFiniteType B S hS f₁.hom → IsSeparated B S hS f₁.hom →
      IsFiniteType B S hS f₂.hom → IsSeparated B S hS f₂.hom →
      ∃ (X₁' X₂' X : AlgebraicSpaces B S hS) (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
        (i₁ : X₁' ⟶ X) (i₂ : X₂' ⟶ X) (g : X ⟶ Y) (u₁ : U ⟶ X₁') (u₂ : U ⟶ X₂'),
        IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₁.hom, @isOpenSubspace_range_of_open B S hS
          _ _ j₁.hom (mono_of_isOpenImmersion B S hS _ hj₁) U.2 hj₁⟩ b₁ ∧
        IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₂.hom, @isOpenSubspace_range_of_open B S hS
          _ _ j₂.hom (mono_of_isOpenImmersion B S hS _ hj₂) U.2 hj₂⟩ b₂ ∧
        IsOpenImmersion B S hS i₁.hom ∧ IsOpenImmersion B S hS i₂.hom ∧
        IsSeparated B S hS g.hom ∧ IsFiniteType B S hS g.hom ∧
        i₁ ≫ g = b₁ ≫ f₁ ∧ i₂ ≫ g = b₂ ≫ f₂ ∧
        u₁ ≫ b₁ = j₁ ∧ u₂ ≫ b₂ = j₂ ∧ u₁ ≫ i₁ = u₂ ≫ i₂ ∧
        IsOpenImmersion B S hS u₁.hom ∧ IsOpenImmersion B S hS u₂.hom)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYnoeth : IsNoetherian B S hS hZ Y) :
    ∃ (U : Subfunctor X) (hU : IsOpenSubspace B S hS U),
      (letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X;
        DenseRange (pointsMap B S hS U.toFunctor U.ι)) ∧
      ∃ (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n),
        IsImmersion B S hS i ∧ i ≫ prod.fst = U.ι ≫ f ∧
          HasChowBlowupDiagram B S hS hX f U hU n i :=
  exists_denseOpen_hasChowBlowupDiagram_of_forall B S hS hZ hX hY f hsep hft hYnoeth
    fun U hU n i hUqc hi hiY =>
      hasChowBlowupDiagram_of_commonAdmissibleBlowup B S hS hZ hcommon hX hY f U hU hUqc
        hYnoeth.1 hYnoeth.2.1 n i hi hiY hft hsep

end AlgebraicGeometry.Space

end
