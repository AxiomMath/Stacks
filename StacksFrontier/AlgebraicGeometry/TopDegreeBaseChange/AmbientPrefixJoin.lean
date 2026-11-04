module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineOpenBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeCrossingSections

/-!
# The `γ⁺` side's prefix at the ambient pair, with its degeneration discharged

`…TopDegreeBaseChange.prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`
(`TopDegreeCrossingSections.lean`) reads the `γ⁺` side's tail of conclusion (c) of
[Stacks, Tag 0EX3] at `(f', V)` on the ambient `X'`, and hoists the prefix it begins with onto a
variable `Pre` fixed by a hypothesis `hPre`. The prefix is

> the edge morphism of `RΓ(V, -)` at `Rf'_*((E Z)[0])`, then `Γ(V, -)` of
> `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso`,

and `…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map`
`_homologyFunctorDerivedPushforwardIso_hom_eq` computes exactly it — behind Grothendieck's
pointwise hypothesis `hpl` at the pair `(f'_*, Γ(V, -))` on the **ambient** base.

`Stacks.Cohomology.AffineBase`
`.preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen` supplies that hypothesis
for a quasi-compact quasi-separated morphism, an **affine open** of the base and a quasi-coherent
coefficient, with nothing assumed of the base scheme, and this file composes the two statements.

## Main results

* `…TopDegreeBaseChange.hpl_of_isAffineOpen`: **the degeneration at the ambient pair, in the
  spelling the comparison's consumers ask for.** For a quasi-compact quasi-separated
  `f : X ⟶ Y`, an affine open `V ⊆ Y` and a functor `E : Dc ⥤ Mod(𝒪_X)` with quasi-coherent
  values, sections over `V` preserve the left homology of the degree-`n` short complex of `f_*`
  of the chosen injective resolution of each `E Z`. Nothing is assumed of `Y`.
* `…TopDegreeBaseChange.hpl_isQuasicoherent_of_isAffineOpen`: the same at the index functor
  [Stacks, Tag 01XK] whiskers by, the inclusion of the quasi-coherent modules, where the
  quasi-coherence of the values is each object's own `property`.
* `…TopDegreeBaseChange.isIso_sectionsOverOpenHomologyComparison_app_of_isAffineOpen`: **the
  cohomology edge morphism of `RΓ(V, -)` is invertible over an affine open**, at a cohomologically
  bounded below object with quasi-coherent cohomology sheaves, with nothing assumed of the scheme:
  the acyclicity of [Stacks, Tag 01XB] is about the open.
* `…TopDegreeBaseChange.collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`:
  **the join.** The prefix written out through [Stacks, Tag 01XK]'s collapse, followed by
  `Γ(V, -)` of the leading crossing inverted and the rest of the tail, is the degree-`n`
  cohomology of derived sections of `β`, the Leray left inverse at `g`, and the edge morphism of
  `RΓ(g⁻¹V, -)`. This is item 1(a) of the tail chase with `hPre` supplied at `(f', V)`.

## Implementation notes

*The quasi-coherence hypothesis is explicit.*
`preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen` declares its coefficient
as `X.Modules` with `[F.IsQuasicoherent]` an instance argument, while the comparison's index
functor `E` lands in `SheafOfModules (structureSheafRing X.toSheafedSpace)`. The two types are
equal by `rfl`, and the coefficient goes in by defeq; but a local `[(E.obj Z).IsQuasicoherent]`
at the `SheafOfModules` spelling is not found by instance search at the `X.Modules` one, and a type
ascription does not help. So the quasi-coherence is taken as an **explicit** family hypothesis and
passed positionally, where the elaborator checks it against the expected type at default
transparency.

*Why `hPre` is supplied on the ambient base.* The degeneration lemma
`preservesLeftHomology_pushforward_injectiveResolution` asks `IsAffine` of the morphism's target,
which here is `Y'` and carries no hypothesis in (c). Its variant over an affine open asks the
affineness of `V` only, so the ambient prefix is computed directly, with no transport to
`((f' ∣_ V), ⊤)` across [Stacks, Tag 01E5].

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.EdgeCompat
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)
open Stacks.Cohomology.AffineBase
  (preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (V : Y.Opens) (n : ℕ)
  {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))

/-! ### The degeneration at the ambient pair

The quasi-compactness and quasi-separatedness of `f` are confined to this section: the join below
takes the degeneration as a hypothesis and needs neither. -/

section Degeneration

variable [QuasiCompact f] [QuasiSeparated f]

/-- **Grothendieck's pointwise hypothesis at the pair `(f_*, Γ(V, -))` on the ambient base.** For
a quasi-compact and quasi-separated morphism of schemes `f : X ⟶ Y`, an **affine open** `V ⊆ Y`, a
functor `E : Dc ⥤ Mod(𝒪_X)` whose values are quasi-coherent and a degree `n`, sections over `V`
preserve the left homology of the degree-`n` short complex of the image under `f_*` of the chosen
injective resolution of `E Z`, for every `Z`.

This is the `hpl` of `sectionsOverOpenHomologyComparison_comp_map`
`_homologyFunctorDerivedPushforwardIso_hom_eq` and of
`…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv`
(`FactorOneCollapseMirror.lean`), and
**nothing is assumed of `Y`** — in particular `Y` need not be affine. The quasi-coherence of the
values is an explicit family hypothesis rather than an instance; see the implementation notes of
the module docstring. -/
theorem hpl_of_isAffineOpen (hV : IsAffineOpen V)
    (hE : ∀ Z : Dc, (E.obj Z).IsQuasicoherent) :
    ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n) := fun Z =>
  @preservesLeftHomology_pushforward_injectiveResolution_of_isAffineOpen
    X Y f inferInstance inferInstance V hV (E.obj Z) (hE Z) n

/-- **The degeneration at the index functor [Stacks, Tag 01XK] whiskers by.** The same hypothesis
at `E := (SheafOfModules.isQuasicoherent 𝒪_X).ι`, the inclusion of the quasi-coherent modules,
where the quasi-coherence of the values is each object's own `property` and so costs nothing.
This is the instantiation `Stacks.Cohomology.AffineBase`
`.cohomologyIsoGlobalSectionsRightDerivedPushforward` is stated at. -/
theorem hpl_isQuasicoherent_of_isAffineOpen (hV : IsAffineOpen V) :
    ∀ Z : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      (sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
        ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution
            ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.obj Z)).cocomplex).sc n) :=
  hpl_of_isAffineOpen f V n (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι hV
    fun Z => Z.property

end Degeneration

/-! ### The edge morphism of derived sections over an affine open -/

/-- **The cohomology edge morphism of `RΓ(V, -)` is invertible over an affine open**, at a
cohomologically bounded below object with quasi-coherent cohomology sheaves. Nothing is assumed of
the scheme.

This is `Stacks.EdgeCompat.isIso_sectionsOverOpenHomologyComparison_app_of_isGE` with its
acyclicity hypothesis discharged by `rightAcyclic_sectionsOverOpen_of_isAffineOpen`, which
needs the affineness of the open only ([Stacks, Tag 01XB]). -/
theorem isIso_sectionsOverOpenHomologyComparison_app_of_isAffineOpen (hV : IsAffineOpen V)
    (q m : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)))
    [K.IsGE m]
    (hH : ∀ j : ℤ, ((homologyFunctor
      (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)) j).obj K).IsQuasicoherent) :
    IsIso ((derivedHomologyComparison (sectionsOverOpen Y.toSheafedSpace V)
      (derivedSectionsOverOpen Y.toSheafedSpace V)
      (derivedSectionsOverOpenUnit Y.toSheafedSpace V)
      (exists_quasiIso_isKInjective Y.toSheafedSpace) q).app K) :=
  Stacks.EdgeCompat.isIso_sectionsOverOpenHomologyComparison_app_of_isGE V q m K fun j =>
    @Stacks.Cohomology.AffineBase.rightAcyclic_sectionsOverOpen_of_isAffineOpen Y V hV _ (hH j)

/-! ### The join -/

variable {Z'' : RingedSpace.{u, u}} (g : Z'' ⟶ Y.toSheafedSpace)

/-- **Item 1(a) of the tail chase of [Stacks, Tag 0EX3] (c): the `γ⁺` side's prefix supplied at
`(f', V)` through [Stacks, Tag 01XK]'s collapse.** For a morphism of schemes `f : X ⟶ Y`, an open
`V ⊆ Y`, a functor `E : Dc ⥤ Mod(𝒪_X)`, a degree `n`, a morphism of ringed spaces
`g : Z'' ⟶ Y`, an object `K` of `D(𝒪_{Z''})` and **any** morphism
`β : Rf_*((E Z)[0]) ⟶ Rg_* K` of `D(𝒪_Y)`, the composite

> the Leray left inverse at `f`, the crossing of the two models of `Rⁿ(f_* ⋙ Γ(V, -))`,
> Grothendieck's comparison of [Stacks, Tag 01XK] inverted, `Γ(V, -)` of the comparison of the
> two indexings of the right derived functors, and then `Γ(V, -)` of
> `…homologyFunctorDerivedPushforwardIso` **inverted** followed by `v`

is the degree-`n` cohomology of `RΓ(V, β)`, then the Leray left inverse at `g`, then the edge
morphism of `RΓ(g⁻¹V, -)` at `K`.

The left-hand side's first four factors are what `sectionsOverOpenHomologyComparison_comp_map`
`_homologyFunctorDerivedPushforwardIso_hom_eq` computes the prefix as, so this is
`prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` with its `hPre` supplied
at the ambient pair.

The hypotheses are exactly its two inputs': `hpl`, which `hpl_of_isAffineOpen` inhabits whenever
`f` is quasi-compact and quasi-separated, `V` is affine and the values of `E` are quasi-coherent;
`hv`, which fixes the rest of the tail; and the two Leray left inverses, each unconditional by
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`. **Nothing is assumed of `g`**,
which is what the situation of (c) requires. -/
theorem collapse_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison
    (hpl : ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc)
    [(sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    {lInvF : (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedSectionsOverOpen Y.toSheafedSpace V).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
              (E.obj Z)))) ⟶
      (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
            (E.obj Z)))}
    (hlF : lInvF ≫ (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).map
          ((lerayComparison f.toLRSHom.toShHom V).app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
              (E.obj Z))) = 𝟙 _)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'')))
    (β : (derivedPushforward f.toLRSHom.toShHom).obj
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
          (E.obj Z)) ⟶ (derivedPushforward g).obj K)
    {v : (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))
          (n : ℤ)).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
            (E.obj Z))) ⟶
      (modulePushforward g).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Z'')) (n : ℤ)).obj K)}
    (hv : (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))
            (n : ℤ)).map β ≫
          (derivedPushforwardHomologyComparison g (n : ℤ)).app K = v)
    {lInvG : (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedSectionsOverOpen Y.toSheafedSpace V).obj ((derivedPushforward g).obj K)) ⟶
      (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedPreimageSections g V).obj K)}
    (hlG : lInvG ≫ (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).map
          ((lerayComparison g V).app K) = 𝟙 _) :
    (lInvF ≫ ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (modulePushforward f.toLRSHom.toShHom ⋙ sectionsOverOpen Y.toSheafedSpace V)
              (derivedPreimageSections f.toLRSHom.toShHom V)
              (derivedPreimageSectionsUnitComp f.toLRSHom.toShHom V)
              (exists_quasiIso_isKInjective X.toSheafedSpace) n).hom.app (E.obj Z) ≫
            (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E
              (modulePushforward f.toLRSHom.toShHom) (sectionsOverOpen Y.toSheafedSpace V) n
              hpl).inv.app Z) ≫
          (sectionsOverOpen Y.toSheafedSpace V).map
            ((Stacks.DerivedIndexing.rightDerivedIso
              (modulePushforward f.toLRSHom.toShHom) n).hom.app (E.obj Z))) ≫
        (sectionsOverOpen Y.toSheafedSpace V).map
          ((homologyFunctorDerivedPushforwardIso f (E.obj Z) (n : ℤ)).inv ≫ v) =
      (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).map
          ((derivedSectionsOverOpen Y.toSheafedSpace V).map β) ≫
        lInvG ≫ (derivedHomologyComparison
          (modulePushforward g ⋙ sectionsOverOpen Y.toSheafedSpace V)
          (derivedPreimageSections g V) (derivedPreimageSectionsUnitComp g V)
          (exists_quasiIso_isKInjective Z'') (n : ℤ)).app K :=
  prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison f V n E g Z
    (sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq
      f V n E hpl Z hlF) K β hv hlG

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
