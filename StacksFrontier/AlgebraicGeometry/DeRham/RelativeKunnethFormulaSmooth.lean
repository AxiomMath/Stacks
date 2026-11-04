module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBoxKunnethSingle
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethDevissage
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethFormula
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeKunnethLocallyBounded
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethFormulaAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsFlat
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocallyBounded

/-!
# The relative de Rham Künneth formula for smooth morphisms

Let `a : X ⟶ S` and `b : Y ⟶ S` be smooth and quasi-compact morphisms of schemes whose relative
diagonals are affine. [Stacks, Tag 0FMC] asserts that the relative cup product

`Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}`

is an isomorphism in `D(𝒪_S)`.

## Main results

* `Stacks.Cohomology.BoxKunneth.isIso_deRhamRelativeKunnethMap_of_smooth`: the relative cup product
  above is an isomorphism.
* `Stacks.Cohomology.BoxKunneth.isFlat_deRhamDiffOpCochainComplex_X`: the terms of the extended
  de Rham complex in nonnegative degrees are flat `𝒪_X`-modules.
* `Stacks.Cohomology.BoxKunneth.isLocallyBounded_leftComplex_deRham`: read over `a^{-1}𝒪_S`, the
  de Rham complex is locally bounded.
* `isIso_deRhamRelativeKunnethMap_of_single_of_devissage_of_truncation`: the formula from the
  single-degree case, the dévissage and the truncation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.BoxKunneth

/-- A term of a stupid truncation at an index in the image of the embedding is, as an object, the
term of the complex. -/
theorem stupidTrunc_X_eq_of_eq {C : Type*} [Category C] [HasZeroObject C] [HasZeroMorphisms C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex C c')
    (e : c.Embedding c') [e.IsRelIff] {i : ι} {i' : ι'} (hi : e.f i = i') :
    (K.stupidTrunc e).X i' = K.X i' := by
  subst hi
  show HomologicalComplex.extend.X _ (e.r (e.f i)) = _
  rw [e.r_f]
  rfl

variable {X S : Scheme.{u}} (a : X ⟶ S)

/-- In a nonnegative degree the extended de Rham complex is, as an object, `Ω^n_{X/S}`. -/
theorem deRhamDiffOpCochainComplex_X_eq (n : ℕ) :
    (Scheme.Hom.deRhamDiffOpCochainComplex a).X (n : ℤ) =
      (Scheme.Hom.deRhamDiffOpComplex a).X n := by
  show HomologicalComplex.extend.X _ (ComplexShape.embeddingUpNat.r (n : ℤ)) = _
  rw [ComplexShape.embeddingUpNat.r_eq_some
    (by simp : ComplexShape.embeddingUpNat.f n = (n : ℤ))]
  rfl

/-- **The terms of the de Rham complex of a smooth morphism are flat `𝒪_X`-modules**: in degree
`n ≥ 0` the term is `Ω^n_{X/S}`, finite locally free by [Stacks, Tag 02G1]. -/
theorem isFlat_deRhamDiffOpCochainComplex_X [Smooth a] (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      ((Scheme.Hom.deRhamDiffOpCochainComplex a).X (n : ℤ)).module := by
  rw [deRhamDiffOpCochainComplex_X_eq]
  exact AlgebraicGeometry.ProperSmoothDeRham.isFlat_relativeDifferentialForms a n

/-- **The de Rham complex of a smooth morphism, read over `a^{-1}𝒪_S`, has flat terms.** -/
theorem isFlat_leftComplex_deRham_X [Smooth a] (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (Stacks.DeRhamDirectImage.inverseImageBase a).sheaf)
      ((leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)).X i) :=
  AlgebraicGeometry.SheafOfModules.IsFlat.of_iso _
    (((HomologicalComplex.eval _ _ i).mapIso (leftComplexDeRhamIso a)).symm)
    (Stacks.DeRhamDirectImage.isFlat_deRhamCochainComplex_X a i)

open Stacks.DeRhamDirectImage in
/-- **The de Rham complex of a smooth morphism, read over `a^{-1}𝒪_S`, is locally bounded**:
locally on `X` only finitely many `Ω^n_{X/S}` are nonzero. -/
theorem isLocallyBounded_leftComplex_deRham [Smooth a] :
    Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a)
      (leftComplex a (Scheme.Hom.deRhamDiffOpCochainComplex a)) :=
  isLocallyBounded_of_isZero_or_nonempty_iso (isLocallyBounded_deRhamCochainComplex a)
    fun i => Or.inr ⟨(HomologicalComplex.eval _ _ i).mapIso (leftComplexDeRhamIso a)⟩

/-- In degrees `0 ≤ i ≤ N` the stupid truncation `σ^{≤N}` of the de Rham complex of a smooth
morphism has a flat `𝒪_X`-module as its term. -/
theorem isFlat_stupidTrunc_deRhamDiffOpCochainComplex_X [Smooth a] (N i : ℤ) (h₀ : 0 ≤ i)
    (hN : i ≤ N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (((Scheme.Hom.deRhamDiffOpCochainComplex a).stupidTrunc
        (ComplexShape.embeddingUpIntLE N)).X i).module := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h₀
  rw [stupidTrunc_X_eq_of_eq _ (ComplexShape.embeddingUpIntLE N) (i := (N - n).toNat)
    (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)]
  exact isFlat_deRhamDiffOpCochainComplex_X a n

section Relative

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DeRhamDirectImage in
/-- The relative cup product of [Stacks, Tag 0FMC] is invertible as soon as the relative Künneth
map of [Stacks, Tag 0G4B] at the two de Rham complexes is: the remaining factor is `Rf_*` of the
isomorphism `Tot(Ω^•_{X/S} ⊠ Ω^•_{Y/S}) ≅ Ω^•_{X ×_S Y/S}` of [Stacks, Tag 0FMA]. -/
theorem isIso_deRhamRelativeKunnethMap_of_isIso {Y : Scheme.{u}} (b : Y ⟶ S)
    (h : IsIso (relativeBoxKunnethMap a b (Scheme.Hom.deRhamDiffOpCochainComplex a)
      (Scheme.Hom.deRhamDiffOpCochainComplex b) 0 0)) :
    IsIso (deRhamRelativeKunnethMap a b) := by
  have hiso : IsIso ((derivedPushforward
      (inverseImageBaseProjection (pullback.fst a b ≫ a))).map
      (DerivedCategory.Q.map
        (((FiniteOrderDifferentialOperatorCategory.toInverseImageModules
          (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (deRhamBoxTotalKunnethIso a b).hom))) :=
    (((derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a))).mapIso
      (DerivedCategory.Q.mapIso
        (((FiniteOrderDifferentialOperatorCategory.toInverseImageModules
          (pullback.fst a b ≫ a)).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso (deRhamBoxTotalKunnethIso a b))))).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h hiso


open Stacks.DeRhamDirectImage ComplexShape in
/-- **[Stacks, Tag 0FMC] from the single-degree case, the dévissage and the truncation.** The
relative cup product of the two de Rham complexes is invertible as soon as: the relative Künneth
map of [Stacks, Tag 0G4B] is invertible at two flat modules placed in single degrees
(`hsingle`); invertibility at single degrees with terms satisfying `Pa`, `Pb` gives it at bounded
complexes with such terms (`hdevissage`, [Stacks, Tag 0FLT]); and invertibility at the stupid
truncations gives it at a locally bounded complex with terms flat over `a^{-1}𝒪_S`
(`htruncation`). The three hypotheses are the shapes of
`isIso_relativeBoxKunnethMap_single`, `isIso_relativeBoxKunnethMap_of_isIso_single` and
`isIso_relativeBoxKunnethMap_of_isIso_stupidTrunc` at `a` and `b`. -/
theorem isIso_deRhamRelativeKunnethMap_of_single_of_devissage_of_truncation [Smooth a]
    {Y : Scheme.{u}} (b : Y ⟶ S) [Smooth b]
    (hsingle : ∀ (i j : ℤ) (E : FiniteOrderDifferentialOperatorCategory a)
      (E' : FiniteOrderDifferentialOperatorCategory b),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) E.module →
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) E'.module →
      IsIso (relativeBoxKunnethMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E') i j))
    (hdevissage : ∀ (Pa : FiniteOrderDifferentialOperatorCategory a → Prop)
      (Pb : FiniteOrderDifferentialOperatorCategory b → Prop),
      (∀ (i j : ℤ) (E : FiniteOrderDifferentialOperatorCategory a)
        (E' : FiniteOrderDifferentialOperatorCategory b), Pa E → Pb E' →
        IsIso (relativeBoxKunnethMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E') i j)) →
      ∀ (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
        (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
        (n₁ m₁ n₂ m₂ : ℤ) [K.IsStrictlyGE n₁] [K.IsStrictlyLE m₁] [L.IsStrictlyGE n₂]
        [L.IsStrictlyLE m₂], (∀ i, n₁ ≤ i → i ≤ m₁ → Pa (K.X i)) →
        (∀ j, n₂ ≤ j → j ≤ m₂ → Pb (L.X j)) → IsIso (relativeBoxKunnethMap a b K L n₁ n₂))
    (htruncation : ∀ (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
      (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
      (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂],
      Stacks.SheafOfModules.OnSpace.IsLocallyBounded (inverseImageBase a) (leftComplex a K) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := (inverseImageBase a).sheaf) ((leftComplex a K).X i)) →
      (∀ N : ℤ, IsIso (relativeBoxKunnethMap a b (K.stupidTrunc (embeddingUpIntLE N))
        (L.stupidTrunc (embeddingUpIntLE N)) n₁ n₂)) →
      IsIso (relativeBoxKunnethMap a b K L n₁ n₂)) :
    IsIso (deRhamRelativeKunnethMap a b) :=
  isIso_deRhamRelativeKunnethMap_of_isIso a b
    (htruncation _ _ 0 0 (isLocallyBounded_leftComplex_deRham a) (isFlat_leftComplex_deRham_X a)
      fun N => hdevissage _ _ hsingle _ _ 0 N 0 N
        (fun i h₀ hN => isFlat_stupidTrunc_deRhamDiffOpCochainComplex_X a N i h₀ hN)
        (fun j h₀ hN => isFlat_stupidTrunc_deRhamDiffOpCochainComplex_X b N j h₀ hN))

/-- **[Stacks, Tag 0FMC]: the relative Künneth formula for de Rham complexes.** Let `a : X ⟶ S`
and `b : Y ⟶ S` be smooth and quasi-compact morphisms of schemes with affine diagonals. Then the
relative cup product
`Ra_*Ω^•_{X/S} ⊗^𝐋_{𝒪_S} Rb_*Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X ×_S Y/S}`
is an isomorphism in `D(𝒪_S)`. The relative Künneth map of [Stacks, Tag 0G4B] is invertible at
two flat modules in single degrees, by [Stacks, Tag 0FLQ] through the change of rings
(`isIso_relativeBoxKunnethMap_single`); hence at bounded complexes with flat terms, by the
dévissage of [Stacks, Tag 0FLT] (`isIso_relativeBoxKunnethMap_of_isIso_single`); hence at the
locally bounded de Rham complexes, by truncation
(`isIso_relativeBoxKunnethMap_of_isIso_stupidTrunc`). -/
@[stacks 0FMC]
theorem isIso_deRhamRelativeKunnethMap_of_smooth {Y : Scheme.{u}} (b : Y ⟶ S) [Smooth a]
    [Smooth b] [QuasiCompact a] [QuasiCompact b] [IsAffineHom (pullback.diagonal a)]
    [IsAffineHom (pullback.diagonal b)] :
    IsIso (deRhamRelativeKunnethMap a b) := by
  have : QuasiSeparated a := ⟨inferInstance⟩
  have : QuasiSeparated b := ⟨inferInstance⟩
  exact isIso_deRhamRelativeKunnethMap_of_single_of_devissage_of_truncation a b
    (fun i j E E' hE hE' => isIso_relativeBoxKunnethMap_single a b
      (AlgebraicGeometry.torIndependent_of_flat_left a b) E E' i j hE hE')
    (isIso_relativeBoxKunnethMap_of_isIso_single a b)
    (isIso_relativeBoxKunnethMap_of_isIso_stupidTrunc a b)

end Relative

end Stacks.Cohomology.BoxKunneth

end
