module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModules
public import StacksFrontier.CategoryTheory.Sites.Modules.TorsionSheavesAsZModModulesFunctor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ForgetEtaleModuleStructure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.UnboundedTorsionBaseChange

/-!
# Base change for unbounded complexes of étale sheaves of modules over a torsion ring

Let `Λ` be a ring with `n · 1 = 0` in `Λ` for some `n ≥ 1`, i.e. a torsion ring. A sheaf of
`Λ`-modules on `X_étale` is in particular a sheaf of `ℤ/nℤ`-modules, compatibly with the
underlying abelian sheaves. So the base change theorem for unbounded complexes of sheaves of
`ℤ/nℤ`-modules ([Stacks, Tag 0F0C]) applies to the underlying abelian complex of every object of
`D(X_étale, Λ)`. This is the reduction used in the proof of [Stacks, Tag 0F0G].

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleToZMod`: the functor from étale sheaves of `Λ`-modules to
  sheaves of modules over the constant sheaf of rings `ℤ/nℤ`, for `n · 1 = 0` in `Λ`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetDerivedZModIso`: forgetting the `Λ`-structure on
  `D(X_étale, Λ)` factors through `D(X_étale, ℤ/nℤ)`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_forget_of_isProper`: for `f`
  proper, granted Tags 095T and 095U, the base change map is invertible at the underlying abelian
  complex of every object of `D(X_étale, Λ)`.

## References

* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 0F0G](https://stacks.math.columbia.edu/tag/0F0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.ZModSheaf

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {n : ℕ} (hn : (n : Λ) = 0) (X : Scheme.{u})

include hn in
/-- The sections of the underlying abelian sheaf of a sheaf of `Λ`-modules are killed by `n`
when `n · 1 = 0` in `Λ`. -/
theorem nsmul_etaleModuleForget_eq_zero (M : EtaleModules.{u, r} Λ X) (U : X.Etaleᵒᵖ)
    (x : ToType
      (((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X).obj M).obj.obj U)) :
    n • x = 0 := by
  let y : M.obj.obj U := x
  have : n • y = 0 := by rw [← Nat.cast_smul_eq_nsmul Λ n y, hn, zero_smul]
  exact this

/-- **Étale sheaves of `Λ`-modules as sheaves of `ℤ/nℤ`-modules**, for `n · 1 = 0` in `Λ`: the
underlying abelian sheaf, with its action of the constant sheaf of rings `ℤ/nℤ`. -/
abbrev etaleModuleToZMod :
    EtaleModules.{u, r} Λ X ⥤
      SheafOfModules.{max (u + 1) r} (zmodRingSheaf.{max (u + 1) r} X.smallEtaleTopology n) :=
  torsionSheafToModulesFunctor.{max (u + 1) r, max (u + 1) r} X.smallEtaleTopology n
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X)
    (nsmul_etaleModuleForget_eq_zero Λ hn X)

/-- The underlying abelian sheaf of `etaleModuleToZMod Λ hn X M` is that of `M`. -/
abbrev etaleModuleToZModCompToSheaf :
    etaleModuleToZMod.{u, r} Λ hn X ⋙ zmodToSheaf.{u, r} X n ≅
      _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X :=
  torsionSheafToModulesFunctorCompToSheaf.{max (u + 1) r, max (u + 1) r} X.smallEtaleTopology n
    (_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X)
    (nsmul_etaleModuleForget_eq_zero Λ hn X)

/-- The functor `etaleModuleToZMod Λ hn X` from étale sheaves of `Λ`-modules to sheaves of
`ℤ/nℤ`-modules preserves finite limits. -/
instance etaleModuleToZMod_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleToZMod.{u, r} Λ hn X) := by
  have : PreservesFiniteLimits (etaleModuleToZMod.{u, r} Λ hn X ⋙ zmodToSheaf.{u, r} X n) :=
    preservesFiniteLimits_of_natIso (etaleModuleToZModCompToSheaf.{u, r} Λ hn X).symm
  have : ReflectsFiniteLimits (zmodToSheaf.{u, r} X n) :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteLimits_of_reflects_of_preserves _ (zmodToSheaf.{u, r} X n)

/-- The functor `etaleModuleToZMod Λ hn X` from étale sheaves of `Λ`-modules to sheaves of
`ℤ/nℤ`-modules preserves finite colimits. -/
instance etaleModuleToZMod_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleToZMod.{u, r} Λ hn X) := by
  have : PreservesFiniteColimits (etaleModuleToZMod.{u, r} Λ hn X ⋙ zmodToSheaf.{u, r} X n) :=
    preservesFiniteColimits_of_natIso (etaleModuleToZModCompToSheaf.{u, r} Λ hn X).symm
  have : ReflectsFiniteColimits (zmodToSheaf.{u, r} X n) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves _ (zmodToSheaf.{u, r} X n)

/-- **Forgetting the `Λ`-structure on `D(X_étale, Λ)` factors through `D(X_étale, ℤ/nℤ)`**, for
`n · 1 = 0` in `Λ`. -/
def etaleModuleForgetDerivedZModIso :
    etaleModuleForgetDerived.{u, r} Λ X ≅
      (etaleModuleToZMod.{u, r} Λ hn X).mapDerivedCategory ⋙
        (zmodToSheaf.{u, r} X n).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfIso (etaleModuleToZModCompToSheaf.{u, r} Λ hn X)

variable {X} {X' Y Y' : Scheme.{u}}

include hn in
/-- **[Stacks, Tag 0F0C] for étale sheaves of modules over a torsion ring, granted Tags 095T and
095U.** Let `f : X ⟶ Y` be proper, `g : Y' ⟶ Y`, `X' = Y' ×_Y X`, and let `n · 1 = 0` in `Λ` with
`n ≥ 1`. Granted that cohomology commutes with base change for `f` (`h095T`, [Stacks, Tag 095T])
and the bound on higher direct images of proper morphisms of [Stacks, Tag 095U] (`h095U`), the
base change map `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` is invertible at the underlying abelian complex of every
object of `D(X_étale, Λ)`: that complex is the underlying complex of an object of
`D(X_étale, ℤ/nℤ)`. -/
theorem isIso_etaleAbelianDerivedBaseChange_forget_of_isProper
    {f : X ⟶ Y} [IsProper f] (h095T : CohomologyCommutesWithBaseChange.{u, r} f)
    (h095U : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p] (N : ℕ),
      (∀ t : T, topologicalKrullDim (p.fiber t) ≤ N) →
        ∀ F : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) r},
          Stacks.Torsion.torsionSheafProperty S.smallEtaleTopology F → ∀ q : ℕ, 2 * N < q →
            IsZero (((etaleAbelianDirectImage.{u, r} p).rightDerived q).obj F))
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (hn0 : 0 < n)
    (M : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, r} f g g' f' sq.w).app
      ((etaleModuleForgetDerived.{u, r} Λ X).obj M)) := by
  rw [NatTrans.isIso_app_iff_of_iso _ ((etaleModuleForgetDerivedZModIso.{u, r} Λ hn X).app M)]
  exact isIso_etaleAbelianDerivedBaseChange_zmod_of_cohomologyCommutesWithBaseChange.{u, r}
    h095T h095U sq hn0 _

end Stacks.EtaleCohomology

end
