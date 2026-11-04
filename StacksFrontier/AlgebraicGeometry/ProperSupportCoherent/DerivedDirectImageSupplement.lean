module

public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.BasicSupplement
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.Unconditional

/-!
# Further results on `DerivedDirectImage`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImage` that need imports beyond
those of that module.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] isWeakSerreClass_isCoherent

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The hypothesis of the dévissage at a coherent module whose support is proper over `S`.**
Coherence of the higher direct images is [Stacks, Tag 08DS]. Their vanishing in large degrees
is by `exists_isProper_rightDerivedPlus_iso` the vanishing of the higher direct images of a
coherent module along a *proper* morphism `Z ⟶ S`, which is quasi-compact and quasi-separated
over the quasi-compact base `S`, so [Stacks, Tag 01XJ] provides a uniform vanishing degree. -/
@[ega "III 4.1.10" "more general"]
theorem hasCoherentBoundedDirectImages_of_isProperOver_supp_unconditional [IsNoetherian S]
    [LocallyOfFiniteType f] (M : X.Modules) (hM : M.IsCoherent)
    (hsupp : IsProperOver f
      ⟨SheafOfModules.supp M, @SheafOfModules.isClosed_supp _ _ _ hM.isFiniteType⟩) :
    HasCoherentBoundedDirectImages f M := by
  have := hM
  have : M.IsFiniteType := hM.isFiniteType
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  refine ⟨fun p =>
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isCoherent_higherDirectImage_of_properSupp f M
      hsupp p, ?_⟩
  obtain ⟨J, G, hG, hJ, he⟩ := exists_isProper_rightDerivedPlus_iso f M hsupp
  have := hJ
  have := hG
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  obtain ⟨N, hN⟩ :=
    Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedPlus_pushforward
      (J.subschemeι ≫ f)
  exact ⟨N, fun p hp => IsZero.of_iso (hN p hp G inferInstance) (he p).some⟩

/-- **[Stacks, Tag 08E2].** Let `S` be a Noetherian scheme, `f : X ⟶ S` locally of finite type
and `E` a bounded object of `D(𝒪_X)` whose cohomology sheaves are coherent with support proper
over `S`. Then `Rf_*E` is an object of `D^b_Coh(𝒪_S)`.

The dévissage is applied to the window `[a, b]` of `E`; at each cohomology sheaf of `E` its
hypothesis is `hasCoherentBoundedDirectImages_of_isProperOver_supp_unconditional`, this library's
form of [Stacks, Tag 08DS] together with the uniform vanishing of [Stacks, Tag 01XJ]. -/
@[stacks 08E2,
  ega "II 7.3.12" "special case",
  ega "III 6.2.5" "special case",
  sga "6 III 2.2.1" "special case",
  sga "6 XIV 2.3" "special case"]
theorem derivedCategoryBBounded_derivedPushforward_of_isProperOver_supp_unconditional
    [IsNoetherian S] [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsCoherent)
    (hsupp : ∀ j : ℤ, IsProperOver f
      ⟨SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules j).obj E),
        @SheafOfModules.isClosed_supp _ _ _ (hcoh j).isFiniteType⟩)
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) :
    DerivedCategoryB.derivedCategoryBBounded (fun N : S.Modules => N.IsCoherent)
      ((derivedPushforwardModules f).obj E) := by
  have hLE' := hLE
  refine derivedCategoryBBounded_derivedPushforward_of_bounded f (b - a).toNat a E
    (fun j _ => ?_) hGE
    (DerivedCategory.TStructure.t.isLE_of_le E b (a + (((b - a).toNat : ℕ) : ℤ)) (by omega))
  exact hasCoherentBoundedDirectImages_of_isProperOver_supp_unconditional f _ (hcoh j) (hsupp j)

end DerivedPushforward

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end
