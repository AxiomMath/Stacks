module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsUnconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.ConstructibleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleTorsionBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived lower shriek along a quasi-finite morphism preserves `D_c`

Let `g : Z ⟶ V` be a separated quasi-finite morphism of finite presentation to a quasi-compact
quasi-separated scheme, and `Λ` a Noetherian ring. This file shows that `Rg_!` carries a
bounded below complex with torsion constructible cohomology sheaves to one with constructible
cohomology sheaves. This is the use the proof of Tag 0GKX makes of Tag 0GK3: by Zariski's main
theorem
(Tag 0F2N) `g` factors as a quasi-compact open immersion `j` followed by a finite morphism `π` of
finite presentation, `Rg_! = π_* ∘ j_!` for that compactification, and `j_!` and `π_*` preserve
constructibility (Tags 03S8 and 095R).

## Main results

* `AlgebraicGeometry.CompactificationOf.ofFactorizationGeneral`,
  `AlgebraicGeometry.CompactificationOf.ofIsProper`, `AlgebraicGeometry.CompactificationOf.ofEq`:
  compactifications from a factorization, of a proper morphism, and along an equality of
  morphisms.
* In the namespace `Stacks.EtaleCohomology`:
  * `isConstructibleEtaleComplex_etaleModuleDerivedDirectImageUnbounded_of_isFinite`:
    `Rπ_*` preserves `D_c` for `π` finite of finite presentation.
  * `isConstructibleEtaleComplex_etaleModuleDerivedExtensionByZeroUnbounded`:
    `Rj_!` preserves `D_c` for a quasi-compact open immersion into a quasi-compact
    quasi-separated scheme.
  * `isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_locallyQuasiFinite`:
    `Rg_!` preserves `D_c` on bounded below objects, for any compactification of `g`, granted
    the proper base change theorem (through the comparison of compactifications, Tag 0F7I).

## References

* [Stacks Project, Tag 0GK3](https://stacks.math.columbia.edu/tag/0GK3)
* [Stacks Project, Tag 0F2N](https://stacks.math.columbia.edu/tag/0F2N)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry.CompactificationOf

/-- The compactification of a morphism `g = j ≫ π` with `j` an open immersion and `π` proper. -/
@[sga "4 XVII 3.2.5"]
def ofFactorizationGeneral {Z V T : Scheme.{u}} (g : Z ⟶ V) (j : Z ⟶ T) (π : T ⟶ V)
    [IsOpenImmersion j] [IsProper π] (h : j ≫ π = g) : CompactificationOf (Over.mk g) :=
  ⟨StructuredArrow.mk (Y := Over.mk π) (Over.homMk j h),
    ⟨inferInstanceAs (IsOpenImmersion j), inferInstanceAs (IsProper π)⟩⟩

/-- A proper morphism is its own compactification. -/
abbrev ofIsProper {Z V : Scheme.{u}} (p : Z ⟶ V) [IsProper p] : CompactificationOf (Over.mk p) :=
  ofFactorizationGeneral p (𝟙 Z) p (Category.id_comp p)

/-- A compactification of `f'` read as a compactification of a morphism `f = f'`: the same ambient
scheme, open immersion and structure morphism. -/
def ofEq {Z V : Scheme.{u}} {f f' : Z ⟶ V} (h : f = f') (J : CompactificationOf (Over.mk f')) :
    CompactificationOf (Over.mk f) :=
  ⟨StructuredArrow.mk (Y := J.obj.right) (Over.homMk (U := Over.mk f) J.immersion
      (by rw [h]; exact J.immersion_toBase_general)), J.property⟩

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

section General

variable (Λ : Type r) [Ring Λ]

/-- **The derived direct image along an integral morphism is the underived one**, applied
degreewise: `Ra_* ≅ a_*` on `D(-_étale, Λ)`, `a_*` being exact. -/
def etaleModuleDerivedDirectImageUnboundedIsoOfIsIntegralHom {X Y : Scheme.{u}} (a : X ⟶ Y)
    [IsIntegralHom a] :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ a ≅
      (etaleModuleDirectImage.{u, r} Λ a).mapDerivedCategory :=
  eqToIso (congrArg (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ) (Category.comp_id a).symm) ≪≫
    etaleModuleDerivedDirectImageUnboundedCompIso.{u, r} Λ a (𝟙 Y) ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedDirectImageUnboundedIdIso.{u, r} Λ Y) ≪≫
    Functor.rightUnitor _

end General

section Constructible

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **`Rπ_*` preserves `D_c` for `π` finite of finite presentation** (Tag 095R applied to every
cohomology sheaf, `π_*` being exact). -/
@[sga "4 IX 2.14" "(i)"]
theorem isConstructibleEtaleComplex_etaleModuleDerivedDirectImageUnbounded_of_isFinite
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] (hπ : FinitePresentation π)
    (K : DerivedCategory (EtaleModules.{u, u + 1} Λ X)) (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ ((etaleModuleDerivedDirectImageUnbounded.{u, u + 1} Λ π).obj K) :=
  fun i ↦ (IsConstructibleEtaleModule Λ).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((etaleModuleDerivedDirectImageUnboundedIsoOfIsIntegralHom.{u, u + 1} Λ π).app K) ≪≫
      ((etaleModuleDirectImage.{u, u + 1} Λ π).mapDerivedCategoryHomologyIso i).app K).symm
    (isConstructibleEtaleModule_etaleModuleDirectImage_of_isFinite Λ π hπ _ (hK i))

/-- **`Rj_!` preserves `D_c`** for a quasi-compact open immersion `j : U ⟶ X` into a quasi-compact
quasi-separated scheme (Tag 03S8 for an open immersion, applied to every cohomology sheaf, `j_!`
being exact). -/
theorem isConstructibleEtaleComplex_etaleModuleDerivedExtensionByZeroUnbounded
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace U] [CompactSpace X]
    [QuasiSeparatedSpace X] (K : DerivedCategory (EtaleModules.{u, u + 1} Λ U))
    (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, u + 1} Λ j).obj K) :=
  fun i ↦ (IsConstructibleEtaleModule Λ).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u + 1} Λ j).app K) ≪≫
      ((etaleModuleExtensionByZero.{u, u + 1} Λ j).mapDerivedCategoryHomologyIso i).app K).symm
    (isConstructibleEtaleModule_etaleModuleExtensionByZero Λ j _ (hK i))

/-- **`Rg_!` preserves `D_c` along a quasi-finite morphism, granted the proper base change
theorem.** Let `g : Z ⟶ V` be separated, locally quasi-finite, quasi-compact and locally of
finite presentation, with `V` quasi-compact and quasi-separated, let `Λ` be a Noetherian ring
and let `J` be a compactification of `g`. Then `Rg_!`, computed through `J`, carries a bounded
below object of `D_c(Z_étale, Λ)` with torsion cohomology sheaves into `D_c(V_étale, Λ)`.

By Zariski's main theorem (Tag 0F2N) `g = j ≫ π` with `j` a quasi-compact open immersion and `π`
finite of finite presentation; through that compactification `Rg_! = Rπ_* ∘ Rj_!` preserves
`D_c`, and the comparison of compactifications (Tag 0F7I, granted `h095T`) gives the statement
for `J`.

closing step: `h095T` is Stacks Tag 095T. -/
theorem isConstructibleEtaleComplex_derivedLowerShriekUnbounded_of_locallyQuasiFinite
    (h095T : ∀ ⦃S T : Scheme.{u}⦄ (p : S ⟶ T) [IsProper p],
      CohomologyCommutesWithBaseChange.{u, u + 1} p)
    {Z V : Scheme.{u}} (g : Z ⟶ V) [IsSeparated g] [LocallyQuasiFinite g] [QuasiCompact g]
    [LocallyOfFinitePresentation g] [CompactSpace V] [QuasiSeparatedSpace V]
    (J : CompactificationOf (Over.mk g)) (K : DerivedCategory (EtaleModules.{u, u + 1} Λ Z))
    (m : ℤ) [K.IsGE m]
    (hKt : Stacks.Torsion.torsionCohomologyProperty.{u + 1} Z.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, u + 1} Λ Z).obj K))
    (hK : IsConstructibleEtaleComplex Λ K) :
    IsConstructibleEtaleComplex Λ ((derivedLowerShriekUnbounded.{u, u + 1} g J Λ).obj K) := by
  obtain ⟨T, j, π, hj, hjqc, hπ, hπfp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization g
  have := hj
  have := hjqc
  have := hπ
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace T := (quasiSeparatedSpace_of_quasiSeparated π)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  let J₀ := CompactificationOf.ofFactorizationGeneral g j π hfac.symm
  refine isConstructibleEtaleComplex_of_iso Λ
    (derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, u + 1} Λ J₀ J h095T K m
      hKt) ?_
  exact isConstructibleEtaleComplex_etaleModuleDerivedDirectImageUnbounded_of_isFinite Λ π hπfp _
    (isConstructibleEtaleComplex_etaleModuleDerivedExtensionByZeroUnbounded Λ j K hK)

end Constructible

end Stacks.EtaleCohomology

end
