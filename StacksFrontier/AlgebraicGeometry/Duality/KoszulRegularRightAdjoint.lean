module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularExtPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalExterior
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalExteriorPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularNormalRank
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QcqsRightAdjoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByZeroClosedPushforward
import StacksCore.Tactic.StacksAttribute

/-!
# The twisted inverse image of `𝒪_Y` along a Koszul-regular closed immersion: [Stacks, Tag 0BR0]

Let `Y` be a quasi-compact and quasi-separated scheme, `i : X ⟶ Y` a Koszul-regular closed
immersion and `a` the right adjoint of `Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]).
[Stacks, Tag 0BR0] computes `a(𝒪_Y)`:

`⋀^r 𝒩 [-r] ≅ a(𝒪_Y)`,

`𝒩` being the normal sheaf of `i` and `r` its rank, a locally constant function on `X`. The object
`⋀^r 𝒩 [-r]` is `Stacks.Duality.KoszulRegular.normalExteriorComplex`
(`StacksFrontier/AlgebraicGeometry/Duality/KoszulRegularNormalExterior.lean`).

## Main results

* `Stacks.Duality.KoszulRegular.nonempty_normalExteriorComplex_iso_rightAdjoint_structureSheaf`:
  **[Stacks, Tag 0BR0]**.

## The proof

As in the source: `a(𝒪_Y) = R ℰom(𝒪_X, 𝒪_Y)` ([Stacks, Tag 0A9X], at the locally small model,
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion`; the
Koszul-regular immersion is perfect, hence pseudo-coherent, [Stacks, Tag 068C]); its pushforward is
`R𝓗om_{𝒪_Y}(i_*𝒪_X, 𝒪_Y)` ([Stacks, Tag 0A77]), whose cohomology sheaves [Stacks, Tag 0BQZ]
computes (`Stacks.Duality.KoszulRegular.nonempty_pushforward_homology_iso_extInto` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.extIsoRankExteriorTerm`). Two comparisons transport the
answer of [Stacks, Tag 0BQZ], which lives on `Y`, to `X`: the pushforward of `⋀ⁿ𝒩` is the exterior
power over `𝒪_Y/𝓘` of the normal sheaf `𝓗om_{𝒪_Y}(𝓘/𝓘², 𝒪_Y/𝓘)` of the ideal sheaf
(`Stacks.Duality.KoszulRegular.exists_exteriorAlgebra_pushforward_iso`), and the rank of `𝒩` at a
point of `X` is the local number of generators of `𝓘` at its image
(`Stacks.Duality.KoszulRegular.preimage_rankLocus_definingIdealOfHom`), extension by zero commuting
with `i_*` (`Stacks.Duality.KoszulRegular.pushforwardExtensionByZeroIso`). Full faithfulness of
`i_*` on modules ([Stacks, Tag 08KS]) then identifies the cohomology sheaves of `a(𝒪_Y)` with the
terms of `⋀^r 𝒩 [-r]`, and formality over the disjoint cover of `X` by the rank loci
(`Stacks.SheafOfModules.nonempty_iso_zeroDifferentialComplex_homology_of_cover`) concludes.

## References

* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules

universe u

namespace Stacks.Duality.KoszulRegular

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- A sheaf of modules on `X` whose stalks vanish on an open `V` is zero on the slice site
over `V`. -/
private theorem isZero_overFunctor_of_stalk_isZero {V : Opens X.carrier}
    {M : SheafOfModules (structureSheaf X.toRingedSpace.sheaf)}
    (h : ∀ x ∈ V, IsZero (TopCat.Presheaf.stalk (X := X.carrier) M.val.presheaf x)) :
    IsZero ((SheafOfModules.overFunctor (structureSheaf X.toRingedSpace.sheaf) V).obj M) :=
  isZero_overFunctor_of_isZero_jStar (Y := X.toRingedSpace)
    (Stacks.Cohomology.PushforwardRestriction.isZero_jStar_obj_of_stalk_isZero _ _ _ h)

/-- **The degree-`k` term of `⋀^r 𝒩 [-r]` vanishes on the rank-`n` locus for `k ≠ n`**: it is
extended by zero from the rank-`k` locus, which is disjoint from the rank-`n` locus. -/
theorem isZero_overFunctor_normalExteriorTerm (hi : IsKoszulRegularImmersion i) {n k : ℤ}
    (hkn : k ≠ n) :
    IsZero ((SheafOfModules.overFunctor (structureSheaf X.toRingedSpace.sheaf)
      (normalRankLocus i hi n)).obj (normalExteriorTerm i hi k)) :=
  isZero_overFunctor_of_stalk_isZero fun x hx =>
    isZero_stalk_jShriek _ _ _ x fun hx' => hkn (hx'.symm.trans hx)

/-- The rank loci of the normal sheaf of a Koszul-regular immersion cover `X`. -/
private theorem iSup_normalRankLocus_eq_top (hi : IsKoszulRegularImmersion i) :
    (⨆ n : ℤ, normalRankLocus i hi n) = ⊤ :=
  top_le_iff.mp fun _ _ => Opens.mem_iSup.mpr ⟨_, rfl⟩

/-- **Stacks Project, Tag 0BR0.** Let `Y` be a quasi-compact and quasi-separated scheme, let
`i : X ⟶ Y` be a Koszul-regular closed immersion, and let `a` be the right adjoint of
`Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. Then there is an isomorphism

`⋀^r 𝒩 [-r] ≅ a(𝒪_Y)`,

where `𝒩 = 𝓗om_{𝒪_X}(𝒞_{X/Y}, 𝒪_X)` is the normal sheaf of `i` (`Stacks.Divisors.normalSheaf`)
and `r` is its rank, a locally constant function on `X` (`normalRank`). Since `r` is only locally
constant, `⋀^r 𝒩 [-r]` is the complex with zero differential whose degree-`n` term is `⋀ⁿ𝒩` on
the open and closed locus where `r = n`, extended by zero (`normalExteriorComplex`): on that locus
it is `⋀ⁿ𝒩[-n]`.

The right adjoint `a` is quantified over together with its adjunction, which determines it up to
unique isomorphism; the derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which [Stacks, Tag 0A9E] produces `a`.
The isomorphism is one of objects of `D(𝒪_X)`; `D_QCoh(𝒪_X)` being a full subcategory, it is an
isomorphism there.

The proof is the source's. By [Stacks, Tags 0A9X and 0A77], `a(𝒪_Y)` is `R ℰom(𝒪_X, 𝒪_Y)` and its
pushforward is `R𝓗om_{𝒪_Y}(i_*𝒪_X, 𝒪_Y)`, which [Stacks, Tag 0BQZ] computes: its cohomology
sheaves are `⋀ⁿ𝒩` on the locus where `r = n`, extended by zero
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.extIsoRankExteriorTerm`). As `i_*` is exact and fully
faithful on modules ([Stacks, Tag 08KS]), the cohomology sheaves of `a(𝒪_Y)` are the terms of
`⋀^r 𝒩 [-r]`; they are concentrated in one degree on each member of the disjoint open cover of
`X` by the rank loci, so `a(𝒪_Y)` is isomorphic to the complex of its cohomology sheaves with zero
differential (`Stacks.SheafOfModules.nonempty_iso_zeroDifferentialComplex_homology_of_cover`). -/
@[stacks 0BR0]
theorem nonempty_normalExteriorComplex_iso_rightAdjoint_structureSheaf
    [CompactSpace Y] [QuasiSeparatedSpace Y] (hi : IsKoszulRegularImmersion i)
    (a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X)
    (adj : DerivedPushforward.qcqsRestrictedDerivedPushforward i ⊣ a) :
    Nonempty ((DerivedCategory.Q (C := X.Modules)).obj (normalExteriorComplex i hi) ≅
      (a.obj (DerivedPushforward.derivedStructureSheaf Y)).obj) := by
  have hpc : PseudoCoherent i := by
    have := perfect_of_isKoszulRegularImmersion i hi
    infer_instance
  -- [Stacks, Tag 0A9X]: `a(𝒪_Y) = R ℰom(𝒪_X, 𝒪_Y)`
  obtain ⟨e⟩ := LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion i hpc a adj
  let e1 := e.app ⟨DerivedPushforward.derivedStructureSheaf Y, ⟨0, fun n hn =>
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ n hn.ne).of_iso
      ((DerivedCategory.homologyFunctor Y.Modules n).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app _) ≪≫
        (DerivedCategory.homologyFunctorFactors Y.Modules n).app _)⟩⟩
  -- a K-injective resolution of `𝒪_Y`, and the model `ℰom(𝒪_X, J)` of `R ℰom(𝒪_X, 𝒪_Y)`
  obtain ⟨J, s, hJ, hs⟩ := Stacks.DerivedFunctor.exists_quasiIso_isKInjective (structureComplex i)
  have := hJ
  have := hs
  let C := ((Stacks.Duality.closedQuotient i).sheafHomExactSupport.mapHomologicalComplex
    (ComplexShape.up ℤ)).obj J
  have e2 : (LocallySmall.derivedSheafHomExactSupport i).obj
      (DerivedPushforward.derivedStructureSheaf Y).obj ≅ DerivedCategory.Q.obj C :=
    (LocallySmall.derivedSheafHomExactSupport i).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app _ ≪≫
          ((DerivedCategory.quotientCompQhIso _).app (structureComplex i)).symm) ≪≫
      AnyModel.derivedSheafHomExactSupportObjIso (Stacks.Duality.closedQuotient i) s hJ hs
  -- the cohomology sheaves of the model, through `i_*` and [Stacks, Tag 0BQZ]
  have eH : ∀ n : ℤ, Nonempty (C.homology n ≅ normalExteriorTerm i hi n) := by
    intro n
    obtain ⟨A, ι, hA, hiso⟩ := exists_exteriorAlgebra_pushforward_iso i
    obtain ⟨f1⟩ := nonempty_pushforward_homology_iso_extInto i s n
    obtain ⟨f3⟩ := hiso n
    exact ⟨(modulePushforward (Stacks.Duality.closedQuotient i).i).preimageIso
      (f1 ≪≫ extIsoRankExteriorTerm (definingIdealOfHom i)
          (isKoszulRegularIdealSheaf_definingIdealOfHom i hi) A ι hA n ≪≫
        (jShriek _ _).mapIso ((jStar _ _).mapIso f3) ≪≫
        (pushforwardExtensionByZeroIso i _ _
          (preimage_rankLocus_definingIdealOfHom i hi n) _).symm)⟩
  -- formality on `X`, over the cover by the rank loci of `𝒩`
  have hH : ∀ (n k : ℤ), k ≠ n → IsZero ((SheafOfModules.overFunctor
      (structureSheaf X.toRingedSpace.sheaf) (normalRankLocus i hi n)).obj (C.homology k)) :=
    fun n k hkn => (isZero_overFunctor_normalExteriorTerm i hi hkn).of_iso
      ((SheafOfModules.overFunctor _ _).mapIso (eH k).some)
  have hX : ∀ (n m k : ℤ), n ≠ m → IsZero ((SheafOfModules.overFunctor
      (structureSheaf X.toRingedSpace.sheaf)
        (normalRankLocus i hi n ⊓ normalRankLocus i hi m)).obj (C.X k)) :=
    fun n m k hnm => isZero_overFunctor_of_stalk_isZero fun x hx =>
      (hnm (hx.1.symm.trans hx.2)).elim
  obtain ⟨e3⟩ := Stacks.SheafOfModules.nonempty_iso_zeroDifferentialComplex_homology_of_cover
    (structureSheaf X.toRingedSpace.sheaf) C (normalRankLocus i hi)
    (iSup_normalRankLocus_eq_top i hi) (fun n => n) hH hX
  exact ⟨(DerivedCategory.Q.mapIso (zeroDifferentialComplexIsoOfIso (Y := X.toRingedSpace)
      fun n => (eH n).some)).symm ≪≫ e3.symm ≪≫ e2.symm ≪≫ e1.symm⟩

end Stacks.Duality.KoszulRegular
