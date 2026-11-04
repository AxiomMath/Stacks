module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimeKilledTransfer
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstantConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DenseOpenComplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiltrationInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.StrongAssertions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ZModLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericInduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero of `Z/ℓ` from a dense open

Let `X` be of finite type over an algebraically closed field with `dim X ≤ 1` and `j : V ⟶ X`
the inclusion of a dense open. If the eight assertions of Tag 03SC hold for the constant sheaf
`Z/ℓ` on `X`, they hold, in the strong form, for `j_! Z/ℓ`: the complement of `V` is finite over
the field (`AlgebraicGeometry.isFinite_comp_of_range_eq_compl_of_dense`), so Tag 0GJA applies to
the constructible sheaf `Z/ℓ` (`TorsionCurveAssertions.of_extensionByZero_sub`), and
`j_! Z/ℓ ⊆ Z/ℓ` is constructible again.

## Main results

* `Stacks.EtaleCohomology.StrongTorsionCurveAssertions.extensionByZero_constant_of_dense`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace StrongTorsionCurveAssertions

/-- The constant abelian sheaf `Z/ℓ` on the small étale site. -/
@[sga "7 XXII 2.0"]
abbrev constantZModAb (X : Scheme.{u}) (ℓ : ℕ) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The eight assertions for `Z/ℓ` give the strong assertions for `j_! Z/ℓ`.** For `X` of finite
type over an algebraically closed field with `dim X ≤ 1` and `j : V ⟶ X` the inclusion of a dense
open, if the eight assertions hold for `Z/ℓ` on `X`, the strong assertions hold for `j_! Z/ℓ`. -/
theorem extensionByZero_constant_of_dense {X V : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (j : V ⟶ X) [IsOpenImmersion j]
    (hden : Dense (Set.range j.base)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : TorsionCurveAssertions f (constantZModAb X ℓ)) :
    StrongTorsionCurveAssertions f ((extensionByZero.{u, u + 1} j).obj
      ((forgetZModSheaf V ℓ).obj (constantZMod.{u + 1, u} ℓ V))) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsNoetherian X := TorsionCurveAssertions.isNoetherian_of_finiteType f
  set F := constantZModAb X ℓ
  have hF : IsConstructibleSmallEtaleSheaf F := isConstructibleEtaleSheaf_constantSheaf X _
  have hℓF : ℓ • 𝟙 F = 0 := nsmul_id_constantSheaf_zmod.{u + 1} ℓ X.smallEtaleTopology
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds X)
  have hirange : Set.range I.subschemeι.base = (Set.range j.base)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hij : Set.range j.base = (Set.range I.subschemeι.base)ᶜ := by
    rw [hirange, compl_compl]
  have : IsFinite (I.subschemeι ≫ f) :=
    isFinite_comp_of_range_eq_compl_of_dense k f hdim j.opensRange (by simpa using hden)
      I.subschemeι (by rw [hirange]; rfl)
  have h₁ := TorsionCurveAssertions.of_extensionByZero_sub f I.subschemeι j hij hℓ hF hℓF h
  have hS := openClosedShortComplex_shortExact.{u, u + 1} I.subschemeι j hij F
  have hmono : Mono ((extensionByZeroAdj.{u, u + 1} j).counit.app F) := hS.mono_f
  have hc : IsConstructibleSmallEtaleSheaf ((extensionByZero.{u, u + 1} j).obj
      ((etaleRestriction.{u, u + 1} j).obj F)) := by
    obtain ⟨B, hX, hB⟩ := hF
    exact ⟨B, hX, IsConstructibleEtaleSheafIn.of_mono
      ((extensionByZeroAdj.{u, u + 1} j).counit.app F) hB⟩
  exact of_iso f ((extensionByZero.{u, u + 1} j).mapIso
    (etaleRestrictionConstantSheafIso j _ ≪≫ (forgetZModSheafConstantIso V ℓ).symm))
    (of_isConstructibleEtaleSheaf f h₁ hc)

end StrongTorsionCurveAssertions

end Stacks.EtaleCohomology

end
