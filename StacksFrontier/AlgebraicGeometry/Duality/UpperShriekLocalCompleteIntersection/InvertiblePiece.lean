module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Decomposition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.StalkRankOne

/-!
# The piece of [Stacks, Tag 0E9Z] through a point, with `ω_{X/Y}` of rank one

Let `f : X ⟶ Y` be a local complete intersection morphism of `FTS S`, `S` Noetherian, factoring
as an immersion `ι : X ⟶ P` followed by a proper smooth `g : P ⟶ Y`. Every point `x₀` of `X`
lies on an open and closed piece `V = ι⁻¹(O)` of `X` on which the relative dimension `d` of `g`
and the rank `m` of the conormal sheaf of `ι` are constant. On `V`, for `f_V = V ⟶ X ⟶ Y` and
`r = d - m`:

* the stalk of `H^k(f_V^!𝒪_Y)` is nonzero exactly for `k = -r`;
* every stalk of `ω_{V/Y} = H^{-r}(f_V^!𝒪_Y)` is free of rank one;
* the map `∧^r Ω_{V/Y} ⟶ ω_{V/Y}` of [Stacks, Tag 0E9Z] is an isomorphism on the stalk at `y`
  exactly when `f_V` is smooth at `y`.

This is the form of [Stacks, Tag 0E9Z] (together with the invertibility of `ω_{X/Y}`) used in
the proof of [Stacks, Tag 0EA3]. The construction of the pieces is the one of
`exists_fundamentalClass_of_isLocalCompleteIntersection` (same namespace).

## Main results

* `Stacks.Duality.ClosedOpenProperFactorization.exists_piece_fundamentalClass`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.ClosedOpenProperFactorization

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {P : Scheme.{u}} (ι : X.left ⟶ P) [IsImmersion ι] (g : P ⟶ Y.left) [Smooth g] [IsProper g]
  (hfac : ι ≫ g = f.left)

include hfac in
/-- **The piece through `x₀`.** See the module docstring. -/
theorem exists_piece_fundamentalClass (hlci : IsLocalCompleteIntersectionMorphism f.left)
    (c : CompactificationOf (Over.mk f.left)) (x₀ : X.left) :
    ∃ (O : P.Opens) (r : ℤ), x₀ ∈ ι ⁻¹ᵁ O ∧
      IsClosed ((ι ⁻¹ᵁ O : X.left.Opens) : Set X.left) ∧
      (∀ (y : (ι ⁻¹ᵁ O).toScheme) (k : ℤ),
        Nontrivial ↑((upperShriekHomology (pieceHom ι O ≫ f) (c.precompOpen (pieceHom ι O).left)
          k).presheaf.stalk y) ↔ k = -r) ∧
      (∀ y : (ι ⁻¹ᵁ O).toScheme,
        letI : Module ((ι ⁻¹ᵁ O).toScheme.presheaf.stalk y)
            (ToType ((upperShriekHomology (pieceHom ι O ≫ f)
              (c.precompOpen (pieceHom ι O).left) (-r)).presheaf.stalk y)) :=
          PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
            (R := (ι ⁻¹ᵁ O).toScheme.presheaf) (upperShriekHomology (pieceHom ι O ≫ f)
              (c.precompOpen (pieceHom ι O).left) (-r)).val y
        Nonempty (ToType ((upperShriekHomology (pieceHom ι O ≫ f)
            (c.precompOpen (pieceHom ι O).left) (-r)).presheaf.stalk y) ≃ₗ[
          (ι ⁻¹ᵁ O).toScheme.presheaf.stalk y] (ι ⁻¹ᵁ O).toScheme.presheaf.stalk y)) ∧
      ∃ φ : Scheme.Modules.exteriorPower
          (Scheme.Hom.relativeDifferentials (pieceHom ι O ≫ f).left) r ⟶
          upperShriekHomology (pieceHom ι O ≫ f) (c.precompOpen (pieceHom ι O).left) (-r),
        ∀ y : (ι ⁻¹ᵁ O).toScheme, IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
            (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology
              ↥(ι ⁻¹ᵁ O).toScheme.toLocallyRingedSpace.toRingedSpace.carrier)
              (ι ⁻¹ᵁ O).toScheme.toLocallyRingedSpace.toRingedSpace.sheaf) y φ) ↔
          InfinitesimalLifting.SmoothAt (pieceHom ι O ≫ f).left y := by
  have := isFiniteLocallyFree_conormalSheaf f ι g hfac hlci
  let C : X.left.Modules := Stacks.Conormal.conormalSheaf ι
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) C :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree C ‹_›
  let mf : X.left → ℕ := Scheme.Modules.fiberRank C
  have hmf : IsLocallyConstant mf := Scheme.Modules.isLocallyConstant_fiberRank C
  let df : LocallyConstant P ℕ := relativeDimensionFunction g (isCohenMacaulay_fiber_of_smooth g)
  have hdf : IsLocallyConstant (fun x : X.left => df (ι x)) :=
    df.isLocallyConstant.comp_continuous ι.continuous
  let m := mf x₀
  let d := df (ι x₀)
  obtain ⟨t, ht, hts⟩ := ι.isEmbedding.isInducing.isOpen_iff.1 (hmf.isOpen_fiber m)
  let T : P.Opens := ⟨t, ht⟩
  have hT : ∀ x : X.left, x ∈ ι ⁻¹ᵁ T ↔ mf x = m := Set.ext_iff.1 hts
  let O : P.Opens := T ⊓ dimensionOpen g d ⊓ ι.coborderRange
  have hOd : O ≤ dimensionOpen g d := inf_le_left.trans inf_le_right
  have hOc : O ≤ ι.coborderRange := inf_le_right
  have hmem : ∀ x, x ∈ ι ⁻¹ᵁ O ↔ mf x = m ∧ df (ι x) = d := by
    intro x
    change (ι x ∈ T ∧ ι x ∈ dimensionOpen g d) ∧ ι x ∈ ι.coborderRange ↔ _
    have h3 := mem_relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) d (ι x)
    exact ⟨fun h => ⟨(hT x).1 h.1.1, h3.1 h.1.2⟩,
      fun h => ⟨⟨(hT x).2 h.1, h3.2 h.2⟩, subset_coborder ⟨x, rfl⟩⟩⟩
  let i : (pieceFTS ι O).left ⟶ (pieceOpen g d O).toScheme := pieceImmersion ι g d O hOd
  have : IsClosedImmersion i := isClosedImmersion_pieceImmersion ι g d O hOd hOc
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := (pieceFTS ι O).left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) m :=
    isFiniteLocallyFreeOfRank_pieceImmersion ι g d O hOd hOc m fun x hx => ((hmem x).1 hx).1
  have hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i :=
    isKoszulRegularImmersion_pieceImmersion f ι g hfac d O hOd hOc hlci
  have hf : i ≫ (pieceOpen g d O).ι ≫ (dimensionOpen g d).ι ≫ g = (pieceHom ι O ≫ f).left :=
    pieceImmersion_fac f ι g hfac d O hOd
  let c' := c.precompOpen (pieceHom ι O).left
  refine ⟨O, (d : ℤ) - m, (hmem x₀).2 ⟨rfl, rfl⟩, ?_, fun y k =>
    nontrivial_stalk_upperShriekHomology_iff (pieceHom ι O ≫ f) (pieceOpen g d O) i
      ((dimensionOpen g d).ι ≫ g) hf c' d m hi y k, fun y =>
    nonempty_stalk_upperShriekHomology_linearEquiv (pieceHom ι O ≫ f) (pieceOpen g d O) i
      ((dimensionOpen g d).ι ≫ g) hf c' d m hi y,
    fundamentalClass (pieceHom ι O ≫ f) (pieceOpen g d O) i
      ((dimensionOpen g d).ι ≫ g) hf c' d m hi,
    isIso_stalkMap_fundamentalClass_iff (pieceHom ι O ≫ f) (pieceOpen g d O) i
      ((dimensionOpen g d).ι ≫ g) hf c' d m hi⟩
  have hV : ((ι ⁻¹ᵁ O : X.left.Opens) : Set X.left) =
      {x | mf x = m} ∩ {x | df (ι x) = d} := Set.ext hmem
  rw [hV]
  exact (hmf.isClosed_fiber _).inter (hdf.isClosed_fiber _)

end Stacks.Duality.ClosedOpenProperFactorization

end
