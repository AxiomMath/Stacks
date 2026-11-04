module

public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalNormalizationExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionIntegralMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ConstructibleSets
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationGenericStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# Reducing a proper birational morphism over a Nagata space to normal spaces

Let `X` be a Noetherian Nagata algebraic space over a scheme `S` and let `f : Y ⟶ X` be a proper
birational morphism. The first paragraph of the proof of Stacks 0BHM replaces `Y` by its
normalization `Y^ν` and `X` by its normalization `X₀ = X^ν`: the morphism `Y^ν ⟶ X` factors
through `X^ν` (Stacks 0BBG), and the factoring morphism `Y^ν ⟶ X^ν` is again proper and
birational. This file records that step together with the properties of `X^ν` that the rest of
the proof consumes: `X^ν ⟶ X` is finite, hence proper (Stacks 0BB5, 04NZ), and `X^ν` is normal,
Noetherian, Nagata and of dimension at most that of `X`, while `Y^ν` is normal, hence reduced.

## Main results

* `AlgebraicGeometry.Space.isNoetherian_of_isProper`: an algebraic space proper over a
  Noetherian algebraic space is Noetherian.
* `AlgebraicGeometry.Space.exists_normalization_lift_of_isProper_of_isBirational`: the
  reduction step above.

## References

* [Stacks Project, Tag 0BHM](https://stacks.math.columbia.edu/tag/0BHM)
* [Stacks Project, Tag 0BBG](https://stacks.math.columbia.edu/tag/0BBG)
* [Stacks Project, Tag 0BB5](https://stacks.math.columbia.edu/tag/0BB5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space proper over a Noetherian algebraic space is Noetherian**: it is
quasi-compact because the morphism and the target are, absolutely quasi-separated because the
morphism is separated and the target is quasi-separated, and locally Noetherian because the
morphism is locally of finite type (Stacks 04ZK). -/
theorem isNoetherian_of_isProper (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYN : IsNoetherian B S hS hZ Y) (f : X ⟶ Y)
    (hf : IsProper B S hS f) : IsNoetherian B S hS hZ X :=
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYN.1 hf.2.1.2,
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYN.2.1
      (isQuasiSeparated_of_isSeparated B S hS hf.1),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX hY f hf.2.1.1 hYN.2.2⟩

/-- The structure morphism of a normalization of an algebraic space with Nagata étale-local
property is proper, since it is finite. -/
private theorem isProper_normalizationData_hom {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hnag : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsNagataScheme T))
    (D : NormalizationData B S hS X) : IsProper B S hS D.hom :=
  (isProper_and_isLocallyQuasiFinite_of_isFinite B S hS D.isAlgebraicSpace hX _
    (D.isFinite_hom hX hnag)).1

/-- **The reduction to normal spaces in the proof of Stacks 0BHM.** Let `X` be a Noetherian
Nagata algebraic space and `f : Y ⟶ X` a proper birational morphism. There are normalizations
`X^ν ⟶ X` and `Y^ν ⟶ Y` and a morphism `l : Y^ν ⟶ X^ν` with `l ≫ (X^ν ⟶ X) = (Y^ν ⟶ Y) ≫ f`,
such that `X^ν ⟶ X` and `l` are proper, `l` is birational, `X^ν` is Noetherian, Nagata and
normal of dimension at most `dim X`, and `Y^ν` is normal and reduced. -/
theorem exists_normalization_lift_of_isProper_of_isBirational (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXN : IsNoetherian B S hS hZ X)
    (hXnag : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsNagataScheme T))
    (f : Y ⟶ X) (hf : IsProper B S hS f)
    (hbir : ∃ (hDY : IsDecentSpace B S hS Y) (hDX : IsDecentSpace B S hS X)
      (hCY : (letI := pointTopology B S hS Y; (irreducibleComponents (points B S hS Y)).Finite))
      (hCX : (letI := pointTopology B S hS X; (irreducibleComponents (points B S hS X)).Finite)),
      IsBirational B S hS hY hX hDY hDX hCY hCX f) :
    ∃ (DX : NormalizationData B S hS X) (DY : NormalizationData B S hS Y)
      (l : DY.space ⟶ DX.space),
      l ≫ DX.hom = DY.hom ≫ f ∧ IsProper B S hS DX.hom ∧ IsProper B S hS l ∧
        (∃ (hDY : IsDecentSpace B S hS DY.space) (hDX : IsDecentSpace B S hS DX.space)
          (hCY : (letI := pointTopology B S hS DY.space;
            (irreducibleComponents (points B S hS DY.space)).Finite))
          (hCX : (letI := pointTopology B S hS DX.space;
            (irreducibleComponents (points B S hS DX.space)).Finite)),
          IsBirational B S hS DY.isAlgebraicSpace DX.isAlgebraicSpace hDY hDX hCY hCX l) ∧
        IsNoetherian B S hS hZ DX.space ∧
        HasEtaleLocalProperty B S hS DX.space (fun T : Scheme.{u} => IsNagataScheme T) ∧
        Space.IsNormal B S hS DX.space ∧
        dimension B S hS DX.space DX.isAlgebraicSpace ≤ dimension B S hS X hX ∧
        Space.IsNormal B S hS DY.space ∧
        HasEtaleLocalProperty B S hS DY.space (fun T : Scheme.{u} => IsReduced T) := by
  obtain ⟨hDY, hDX, hCY, hCX, hb⟩ := hbir
  obtain ⟨DY, DX, l, hl, hlbir⟩ :=
    exists_normalizationData_isBirational_lift_of_isBirational B S hS hY hX hDY hDX hCY hCX hb
  have hνX := isProper_normalizationData_hom hX hXnag DX
  have hYnag : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsNagataScheme T) :=
    isNagata_of_isLocallyOfFiniteType B S hS hY hX f hf.2.1.1 hXnag
  have hνY := isProper_normalizationData_hom hY hYnag DY
  have hlp : IsProper B S hS l := by
    refine isProper_of_comp_of_isSeparated B S hS DY.isAlgebraicSpace DX.isAlgebraicSpace hX l
      DX.hom ?_ (isSeparated_of_isIntegralHom B S hS DX.hom DX.isAlgebraicSpace hX
        (DX.isIntegralHom_hom hX))
    rw [hl]
    exact isProper_comp B S hS DY.isAlgebraicSpace hY hX _ _ hνY hf
  exact ⟨DX, DY, l, hl, hνX, hlp, ⟨_, _, _, _, hlbir⟩,
    isNoetherian_of_isProper hZ DX.isAlgebraicSpace hX hXN _ hνX,
    isNagata_of_isLocallyOfFiniteType B S hS DX.isAlgebraicSpace hX DX.hom hνX.2.1.1 hXnag,
    DX.isNormal hX,
    dimension_le_of_isIntegralHom B S hS DX.isAlgebraicSpace hX _ (DX.isIntegralHom_hom hX),
    DY.isNormal hY,
    hasEtaleLocalProperty_isReduced_of_isNormal B S hS DY.space (DY.isNormal hY)⟩

end AlgebraicGeometry.Space

end
