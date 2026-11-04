module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTorsionUnitSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleLiftLocallyConstant

/-!
# The `p`-torsion of a lisse sheaf of `ℤ/pᵐ`-modules is lisse

Let `d ∣ N` and write `R` for restriction of scalars along `ℤ/N ↠ ℤ/d`, from sheaves of
`ℤ/d`-modules to sheaves of `ℤ/N`-modules on the small étale site of a scheme `X`. A sheaf `G` of
`ℤ/d`-modules is locally constant of finite type as soon as `R G` is: on a member `V` of a
trivializing covering of `R G` with value `E`, the sheaf `R G|_V` is killed by `d`, so the
constant sheaf on `E` is the constant sheaf on `E / dE`, which is the restriction of scalars of a
`ℤ/d`-module; restriction of scalars commutes with the constant sheaf functor and is fully
faithful (`Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_of_restrict`).

For `N = pᵐ` and a lisse sheaf `F` of `ℤ/pᵐ`-modules this shows that the `p`-torsion `F[p]`,
a sheaf of `ℤ/p`-modules, is lisse, and so is `F / F[p]`
(`Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_coextend`,
`Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_cokernel_torsionCounit`): these
are the closure properties of the dévissage
`Stacks.EtaleCohomology.LevelChange.isDualityPerfect_of_coextend` for lisse coefficients, in the
proof of Poincaré duality with `ℤ/ℓⁿ` coefficients for the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.LevelChange.overRestrictConstantIso`: restriction of scalars commutes
  with the constant sheaf functor on a localized small étale site.
* `Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_of_restrict`.
* `Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_coextend`.
* `Stacks.EtaleCohomology.LevelChange.isFiniteTypeLocallyConstant_cokernel_torsionCounit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology.LevelChange

variable {X : Scheme.{u}} {N d : ℕ} (h : d ∣ N)

/-- **Restriction of scalars of a constant sheaf on a localized small étale site is constant**:
restriction of scalars along `ℤ/N ↠ ℤ/d` commutes with sheafification, having a right adjoint. -/
def overRestrictConstantIso (V : X.Etale) :
    constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod d)) ⋙
        sheafCompose (X.smallEtaleTopology.over V)
          (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))) ≅
      ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d)) ⋙
        constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod N)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const (Over V)ᵒᵖ)
      (sheafComposeNatIso (X.smallEtaleTopology.over V)
        (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d)))
        (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.compConstIso (Over V)ᵒᵖ
      (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d)))).symm _ ≪≫
    Functor.associator _ _ _

/-- A `ℤ/d`-module read as a `ℤ/N`-module is the given `ℤ/N`-module on the same group: the two
actions of `ℤ/N` agree, both being iterated addition. -/
def restrictScalarsOfIso (M : ModuleCat.{u + 1} (ZMod N)) [Module (ZMod d) M] :
    (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).obj (ModuleCat.of (ZMod d) M) ≅
      M where
  hom := ConcreteCategory.ofHom (C := ModuleCat (ZMod N))
    (AddMonoidHom.toZModLinearMap N (AddMonoidHom.id M))
  inv := ConcreteCategory.ofHom (C := ModuleCat (ZMod N))
    (AddMonoidHom.toZModLinearMap N (AddMonoidHom.id M))

/-- **Restriction of scalars reflects local constancy of finite type**: a sheaf `G` of
`ℤ/d`-modules is locally constant of finite type when `R G` is, as a sheaf of `ℤ/N`-modules. -/
theorem isFiniteTypeLocallyConstant_of_restrict [NeZero N] [NeZero d]
    (G : EtaleModules.{u, 0} (ZMod d) X)
    (hG : IsFiniteTypeLocallyConstant (ZMod N) X.smallEtaleTopology ((restrict X h).obj G)) :
    IsFiniteTypeLocallyConstant (ZMod d) X.smallEtaleTopology G := by
  intro U
  obtain ⟨I, V, f, hcov, hE⟩ := hG U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  obtain ⟨E, hEfg, ⟨e⟩⟩ := hE i
  let J' := X.smallEtaleTopology.over (V i)
  let R' := sheafCompose J' (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d)))
  let Q := E ⧸ LinearMap.range (d • 𝟙 E).hom
  let : Module (ZMod d) Q := AddCommGroup.zmodModule (fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩)
  have : Module.Finite (ZMod N) E := hEfg
  have : Finite E := Module.finite_of_finite (ZMod N)
  have : Finite Q := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  refine ⟨ModuleCat.of.{u + 1} (ZMod d) Q, Module.Finite.of_finite, ⟨?_⟩⟩
  have hP : PreservesColimitsOfSize.{0, 0} (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))) :=
    (constantSheafAdj J' (ModuleCat.{u + 1} (ZMod N))
      (Over.mkIdTerminal (X := V i))).leftAdjoint_preservesColimits
  have : PreservesColimit (parallelPair (d • 𝟙 E) 0)
      (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))) :=
    (hP.preservesColimitsOfShape (J := WalkingParallelPair)).preservesColimit
  have hzero : (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))).map (d • 𝟙 E) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    have h0 : d • 𝟙 ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) (V i)).obj
        ((restrict X h).obj G)) = 0 := by
      rw [← (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) (V i)).map_id,
        ← Functor.map_nsmul, nsmul_id_restrict, Functor.map_zero]
    rw [← cancel_mono e.hom, zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id e.hom, ← Preadditive.comp_nsmul, h0, comp_zero]
  -- the constant sheaf on `E / dE` is that on `E`
  let eQ : (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))).obj (ModuleCat.of (ZMod N) Q) ≅
      (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))).obj E :=
    (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))).mapIso
        (ModuleCat.cokernelIsoRangeQuotient (d • 𝟙 E)).symm ≪≫
      PreservesCokernel.iso (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))) (d • 𝟙 E) ≪≫
      cokernelIsoOfEq hzero ≪≫ cokernelZeroIsoTarget
  -- `E / dE` is the restriction of scalars of a `ℤ/d`-module
  let eR : (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).obj
      (ModuleCat.of (ZMod d) Q) ≅ ModuleCat.of (ZMod N) Q :=
    restrictScalarsOfIso h (ModuleCat.of (ZMod N) Q)
  let e' : R'.obj ((constantSheaf J' (ModuleCat.{u + 1} (ZMod d))).obj (ModuleCat.of (ZMod d) Q)) ≅
      R'.obj ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod d)) (V i)).obj G) :=
    (overRestrictConstantIso h (V i)).app (ModuleCat.of (ZMod d) Q) ≪≫
      (constantSheaf J' (ModuleCat.{u + 1} (ZMod N))).mapIso eR ≪≫ eQ ≪≫ e ≪≫ Iso.refl _
  have : (ModuleCat.restrictScalars.{u + 1} (ZMod.castHom h (ZMod d))).Full :=
    { map_surjective := fun {M M'} g => by
        refine ⟨ModuleCat.ofHom
          { toFun := g.hom
            map_add' := map_add g.hom
            map_smul' := fun s x => ?_ }, rfl⟩
        obtain ⟨r, rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod d)) s
        exact g.hom.map_smul r x }
  exact (Functor.FullyFaithful.ofFullyFaithful R').preimageIso e'

variable {p : ℕ} [Fact p.Prime] {m : ℕ} [NeZero m] (X)

/-- `R(F[p]) ≅ ker(p : F → F)`. -/
def restrictCoextendIsoKernel (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) :
    (restrict X (dvd_pow_self_of_neZero (p := p) (m := m))).obj
        ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F) ≅
      kernel (p • 𝟙 F) :=
  IsLimit.conePointUniqueUpToIso (isTorsionKernel_torsionCounit X F).isLimit
    (limit.isLimit _)

/-- **The `p`-torsion of a lisse sheaf of `ℤ/pᵐ`-modules is a lisse sheaf of `ℤ/p`-modules.** -/
theorem isFiniteTypeLocallyConstant_coextend (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X)
    (hF : IsFiniteTypeLocallyConstant (ZMod (p ^ m)) X.smallEtaleTopology F) :
    IsFiniteTypeLocallyConstant (ZMod p) X.smallEtaleTopology
      ((coextend X (dvd_pow_self_of_neZero (p := p) (m := m))).obj F) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine isFiniteTypeLocallyConstant_of_restrict (dvd_pow_self_of_neZero (p := p) (m := m)) _ ?_
  exact isFiniteTypeLocallyConstant_congr _ _ (restrictCoextendIsoKernel X F).symm
    (isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0} X.smallEtaleTopology
      (ZMod (p ^ m)) (p • 𝟙 F) hF hF)

/-- **`F / F[p]` is lisse** for a lisse sheaf `F` of `ℤ/pᵐ`-modules. -/
theorem isFiniteTypeLocallyConstant_cokernel_torsionCounit
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X)
    (hF : IsFiniteTypeLocallyConstant (ZMod (p ^ m)) X.smallEtaleTopology F) :
    IsFiniteTypeLocallyConstant (ZMod (p ^ m)) X.smallEtaleTopology
      (cokernel (torsionCounit X F)) :=
  isFiniteTypeLocallyConstantModuleSheaf_cokernel.{u, u + 1, 0, 0} X.smallEtaleTopology
    (ZMod (p ^ m)) (torsionCounit X F)
    (isFiniteTypeLocallyConstant_congr _ _ (restrictCoextendIsoKernel X F).symm
      (isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0} X.smallEtaleTopology
        (ZMod (p ^ m)) (p • 𝟙 F) hF hF)) hF

end Stacks.EtaleCohomology.LevelChange

end
