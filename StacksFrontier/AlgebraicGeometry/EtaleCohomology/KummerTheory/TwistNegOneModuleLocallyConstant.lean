module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallyConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleLocallyConstant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Tate twist of a locally constant sheaf is locally constant

`μ_N` is locally the constant sheaf `ℤ/N`, a finitely presented `ℤ/N`-module, on a scheme over a
field in which `N` is invertible (`Stacks.Kummer.isLocallyConstant_rootsOfUnityModule`). By
Tag 093T (3) (`Stacks.ConstantSheaf.isLocallyConstant_moduleSheafHom`), `G(-1) = 𝓗om(μ_N, G)` is
then locally constant whenever `G` is.

## Main results

* `Stacks.Kummer.isFinitePresentationLocallyConstant_rootsOfUnityModule`.
* `Stacks.Kummer.isLocallyConstant_twistNegOneModule`.
* `Stacks.Kummer.isFiniteTypeLocallyConstant_twistNegOneModule`: the twist of a sheaf locally
  constant of finite type is locally constant of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero N]
  [NeZero (N : k)]

include f in
/-- **`μ_N` is locally constant with finitely presented values**: on the covering
`U ×_k k(ζ_N) ⟶ U` it is the constant sheaf `ℤ/N`. -/
@[sga "4 XIX 3.3" "partial", sga "4 XVI 3.10" "Remark 3.10 a)"]
theorem isFinitePresentationLocallyConstant_rootsOfUnityModule :
    Stacks.ConstantSheaf.IsFinitePresentationLocallyConstantModuleSheaf X.smallEtaleTopology
      (ZMod N) (rootsOfUnityModule.{u, v} X N) := by
  intro U
  have := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, max (u + 1) v}
    X.smallEtaleTopology (ZMod N) (cyclotomicBaseChange f N U)
  refine ⟨PUnit, fun _ => cyclotomicBaseChange f N U, fun _ => cyclotomicBaseChangeπ f N U, ?_,
    fun _ => ⟨ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N)), ?_,
      ⟨sliceRootSheafIso.{u, v} _ (cyclotomicBaseChangeStructMap f N U)
        (IsCyclotomicExtension.zeta_spec N k _)⟩⟩⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
      rw [range_cyclotomicBaseChangeπ]; trivial⟩
  · exact Module.FinitePresentation.of_equiv ULift.moduleEquiv.symm

include f in
/-- **The Tate twist of a locally constant sheaf is locally constant** (Tag 093T (3)). -/
theorem isLocallyConstant_twistNegOneModule
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)))
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U)
      (ModuleCat.{max (u + 1) v} (ZMod N))]
    [Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology G] :
    Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology
      (twistNegOneModule.{u, v} X N G) :=
  Stacks.ConstantSheaf.isLocallyConstant_moduleSheafHom.{u + 1, u, 0, v} X.smallEtaleTopology
    (ZMod N) _ G (isFinitePresentationLocallyConstant_rootsOfUnityModule f N)

include f in
/-- **`μ_N` is locally the constant sheaf on the free module `ℤ/N` of rank one.** -/
@[sga "4 XIX 3.3" "partial", sga "4 XVI 3.10" "Remark 3.10 a)", sga "4 XVIII 1.1.1" "partial"]
theorem isFreeFiniteLocallyConstant_rootsOfUnityModule :
    Stacks.ConstantSheaf.IsFreeFiniteLocallyConstantModuleSheaf X.smallEtaleTopology
      (ZMod N) (rootsOfUnityModule.{u, v} X N) := by
  intro U
  have := Stacks.ConstantSheaf.hasSheafify_over_moduleCat_of_univLE.{u + 1, u, 0, max (u + 1) v}
    X.smallEtaleTopology (ZMod N) (cyclotomicBaseChange f N U)
  refine ⟨PUnit, fun _ => cyclotomicBaseChange f N U, fun _ => cyclotomicBaseChangeπ f N U, ?_,
    fun _ => ⟨ModuleCat.of (ZMod N) (ULift.{max (u + 1) v} (ZMod N)),
      Module.Free.of_equiv ULift.moduleEquiv.symm, Module.Finite.equiv ULift.moduleEquiv.symm,
      ⟨sliceRootSheafIso.{u, v} _ (cyclotomicBaseChangeStructMap f N U)
        (IsCyclotomicExtension.zeta_spec N k _)⟩⟩⟩
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
    rw [range_cyclotomicBaseChangeπ]; trivial⟩

include f in
/-- **The Tate twist of a sheaf locally constant of finite type is locally constant of finite
type**: `μ_N` is locally constant on the free module `ℤ/N`, so on a common refinement
`𝓗om(μ_N, G)` is the constant sheaf on `Hom(ℤ/N, E)`, `E` finite. -/
theorem isFiniteTypeLocallyConstant_twistNegOneModule
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)))
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U)
      (ModuleCat.{max (u + 1) v} (ZMod N))]
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) X.smallEtaleTopology G) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) X.smallEtaleTopology
      (twistNegOneModule.{u, v} X N G) :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_moduleSheafHom.{u + 1, u, 0, v}
    X.smallEtaleTopology (ZMod N) _ G (isFreeFiniteLocallyConstant_rootsOfUnityModule f N) hG

end Stacks.Kummer

end
