module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeIsomorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.VanishingTransfer

/-!
# [Stacks, Tag 07MU] reduced to an abelian-valued assertion in each degree

`SmallSite/BaseChangeIsomorphism.lean` proves [Stacks, Tag 07MU] equivalent to its degreewise
form `Crystalline.GlobalCrystallineSituation.SmallSite.DegreewiseBaseChangeIso07MU`, and records
two reasons the degreewise form could not be attacked.  One of them was that the de Rham
computation [Stacks, Tag 07LG] is *abelian*-valued — it concludes about
`(cohomologyFunctor S j).obj (abelianSheaf F)` — while `RΓ(Cris(X/S), F)` has the `A`-modules
`moduleULiftCohomology` as its cohomology, and that crossing is [Stacks, Tag 03FD], which at the
universes of `Cris(X/S)` was then unavailable.

It is available now: `SmallSite/ModuleCohomologyComparison.lean` proves [Stacks, Tag 03FD] here
(`...SmallSite.abelianComparisonIso`) and `SmallSite/VanishingTransfer.lean` identifies the two
global sections functors and hence the two cohomology theories
(`...SmallSite.moduleCohomologyFunctorIsoAbelian`).  This file carries that crossing to the
objects and maps of [Stacks, Tag 07MU] and thereby replaces the module-valued degreewise
statement by an abelian-valued one, **as an equivalence and not as a weakening**.

## The two changes of shape, and why neither loses content

The degreewise form asks that
`(DerivedCategory.homologyFunctor (ModuleCat A) n).map φ` be an isomorphism of `A`-modules for
every `n : ℤ`.  Two things happen to that assertion here.

* **Forgetting the `A`-action loses nothing.**  `forgetBaseAction S` reflects isomorphisms — a
  bijective `A`-linear map is `A`-linear in its inverse — so being an isomorphism of `A`-modules
  and being one of abelian groups are the same condition on this map.  That is
  `isIso_homologyMap_baseChangeMap07MT_iff_forgetBaseAction`, an iff, and it is what lets the
  abelian-valued conclusion of [Stacks, Tag 07LG] be the right target at all.
* **The degrees split at zero.**  The target `RΓ(Cris(X/S), F)` has no cohomology below degree
  zero (`isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg`), so in a negative
  degree the assertion is exactly that the *source* `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no
  cohomology there either, with no comparison of the two left to make.  Above degree zero the
  degrees are `j : ℕ` and the target is the chapter's named cohomology group.  So the degreewise
  form is the conjunction of `NegativeDegreeVanishing07MU` and an assertion indexed by `ℕ`,
  which is `degreewiseBaseChangeIso07MU_iff_abelian`.  The split is not a restriction of the
  range of degrees: the negative half is kept, as the vanishing it amounts to.

Put together, `AbelianDegreewiseBaseChangeIso07MU` is a form of [Stacks, Tag 07MU] whose
degree-`j` clause asserts that an explicit map of abelian groups

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(Cris(X/S), abelianSheaf F)`

is an isomorphism, the target being *literally* the object
`(cohomologyFunctor S j).obj (abelianSheaf F)` that [Stacks, Tag 07LG] computes.  That map is
`abelianBaseChangeCohomologyMap`, and `isBaseChangeIso07MU_iff_abelianDegreewise` is the machine
check that nothing was gained or lost on the way.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `moduleULiftCohomologyIsoAbelian` — the crossing of [Stacks, Tag 03FD] at the chapter's own
  cohomology objects: forgetting the `A`-action on `H^j(Cris(X/S), F)` gives the abelian group
  `(cohomologyFunctor S j).obj (abelianSheaf F)`.  `moduleULiftCohomologyFunctorIsoAbelian` is
  the same thing as an isomorphism of functors.
* `abelianBaseChangeCohomologyMap` — the base change map in degree `j`, read as a map of abelian
  groups into `(cohomologyFunctor S j).obj (abelianSheaf F)`.
* `NegativeDegreeVanishing07MU` — the negative-degree half of the degreewise form: under the
  seven conditions, `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology below degree zero.
* `AbelianDegreewiseBaseChangeIso07MU` — the abelian-valued form of [Stacks, Tag 07MU].

## Main results

* `isIso_homologyMap_baseChangeMap07MT_iff_forgetBaseAction` — the degreewise assertion is
  indifferent to the `A`-action.
* `isIso_abelianBaseChangeCohomologyMap_iff` — the explicit abelian map of degree `j` is an
  isomorphism exactly when the base change map is one on `H^j`.
* `degreewiseBaseChangeIso07MU_iff_abelian` and `isBaseChangeIso07MU_iff_abelianDegreewise` —
  **[Stacks, Tag 07MU], its degreewise form and its abelian degreewise form are the same
  statement.**
* `baseChangeCohomologyIsoAbelian` — the abelian graded form of the conclusion, for a base change
  map that is an isomorphism.

## What is and is not proved

[Stacks, Tag 07MU] is **not** proved here and no `@[stacks 07MU]` attribute is placed.  What is
proved is that its whole content, after [Stacks, Tag 03FD], is the pair of assertions in
`AbelianDegreewiseBaseChangeIso07MU`.  Two facts about the remaining gap are
recorded here.

* **[Stacks, Tag 07LG], as proved, does not discharge the degree-`j` clause.**  It is
  `...SmallSite.crystalPairDeRhamDerivedPlusIso` of `SmallSite/CrystalDeRhamDerived07LG.lean`,
  the canonical isomorphism `M ⊗^∧_D Ω^*_D ≅ RΓ(Cris(X/S), ℱ)` in `D⁺(Ab)` of the proof, with
  degreewise consequence `...SmallSite.crystalPairDeRhamComplex_computesCohomology` (and the
  older proposition is `Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CompletedConnectionDeRham.lean`).  The degree-`j`
  clause here — like `DegreewiseBaseChangeIso07MU` itself — is about the given base change map,
  so what the reduction needs from the de Rham side is the compatibility of that named
  comparison with change of divided power base, which is not stated; the two theorems in the
  library that conclude `Computes07LG`,
  `...SmallSite.computes07LG_of_sectionsComplexHomologyIso`
  (`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFrom07JN.lean`) and
  `...SmallSite.computes07LG_of_doubleComplex`
  (`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFromDoubleComplex.lean`), each take
  a hypothesis that is the remaining content.
* **The Mayer–Vietoris step of the source's hint still cannot be stated**, for the reason
  `SmallSite/BaseChangeIsomorphism.lean` records: `Crystalline.GlobalCrystallineSituation.restrict`
  exists (`StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/SituationRestrict.lean:176`) but
  nothing compares the derived global sections of a situation with those of a restriction of it,
  so a carried `BaseChangeMap07MT` has no restriction to an open of `X'`.  Nothing here changes
  that; what this file does is make the *affine* case, once it is reachable, an assertion about
  the abelian groups the de Rham complex computes.  The small-site Mayer–Vietoris material
  (`SmallSite/MayerVietorisCover.lean`, `SmallSite/MayerVietorisShortExact.lean`,
  `SmallSite/MayerVietorisTriangle.lean`) is all stated at a fixed object `(U, T, δ)` of the
  site, not for derived global sections, so it does not supply the missing comparison either.

No `@[stacks 03FD]` attribute is placed either: the tag already sits on the general comparison,
`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying`
(`StacksFrontier/CategoryTheory/Sites/GlobalSections/ModuleCohomologyComparison.lean:1082`), and the
declarations here are that comparison transported to this chapter's objects, not a second proof
of it.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wS' wA wA'

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### [Stacks, Tag 03FD] at the chapter's own cohomology objects -/

section Crossing

variable (S : GlobalCrystallineSituation.{u})

/-- **Forgetting the `A`-action on `H^j(Cris(X/S), F)` gives the abelian cohomology group
`H^j(Cris(X/S), abelianSheaf F)`.**

This is the crossing between the module-valued and the abelian-valued crystalline cohomology of
the chapter, at the objects its statements name: `moduleULiftCohomology S F j` on the one side,
and on the other the `(cohomologyFunctor S j).obj (abelianSheaf F)` that [Stacks, Tag 07LF] and
[Stacks, Tag 07LG] are stated about.  Three steps, none of them new mathematics: the cohomology
of `F` is that of its universe lift (`moduleULiftCohomology_eq`), the module-valued and the
abelian-valued derived global sections agree by [Stacks, Tag 03FD] at this site
(`moduleCohomologyFunctorIsoAbelian`), and the abelian derived global sections are the abelian
cohomology (`rightDerivedGlobalSectionsIso`).  That the abelian sheaf reached is the chapter's
`abelianSheaf F` on the nose is `toAbelianSheaf_obj_moduleULift`. -/
def moduleULiftCohomologyIsoAbelian (F : SheafOfModules.{u} (structureSheaf S)) (j : ℕ) :
    (forgetBaseAction S).obj (moduleULiftCohomology S F j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  (moduleCohomologyFunctorIsoAbelian S j).app ((moduleULift S).obj F) ≪≫
    (rightDerivedGlobalSectionsIso S j).app (abelianSheaf F)

/-- **The functorial form of the crossing**: the module-valued `H^j(Cris(X/S), -)` at the
predicates' module universe, with the `A`-action forgotten, is the abelian-valued
`H^j(Cris(X/S), -)` of the underlying abelian sheaf.  `moduleULiftCohomologyIsoAbelian` is its
component at `F`, read through `toAbelianSheaf_obj_moduleULift`. -/
def moduleULiftCohomologyFunctorIsoAbelian (j : ℕ) :
    moduleULiftCohomologyFunctor S j ⋙ forgetBaseAction S ≅
      moduleULift S ⋙ toAbelianSheaf S ⋙ cohomologyFunctor S j :=
  Functor.isoWhiskerLeft (moduleULift S) (moduleCohomologyFunctorIsoAbelian S j) ≪≫
    Functor.isoWhiskerLeft (moduleULift S)
      (Functor.isoWhiskerLeft (toAbelianSheaf S) (rightDerivedGlobalSectionsIso S j))

end Crossing

/-! ### The abelian-valued degreewise form of [Stacks, Tag 07MU] -/

section BaseChange

variable {S S' : GlobalCrystallineSituation.{u}} [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The degreewise assertion of [Stacks, Tag 07MU] is indifferent to the `A`-action.**  A map
of `A`-modules is an isomorphism exactly when it is one of abelian groups, because
`forgetBaseAction` reflects isomorphisms: the inverse of a bijective `A`-linear map is
`A`-linear.

This is what makes the abelian-valued conclusion of [Stacks, Tag 07LG] an admissible target for
the degreewise form of the tag, and it is an equivalence, so replacing the module-valued
assertion by the abelian one below weakens nothing. -/
theorem isIso_homologyMap_baseChangeMap07MT_iff_forgetBaseAction (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ) ↔
      IsIso ((forgetBaseAction S).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ)) :=
  ⟨fun _ => inferInstance, fun _ => isIso_of_reflects_iso _ (forgetBaseAction S)⟩

/-- The isomorphism by which the degree-`j` component of a base change map is read as a map into
the abelian cohomology group `H^j(Cris(X/S), abelianSheaf F)`: the identification of
`H^j(RΓ(Cris(X/S), F))` with `H^j(Cris(X/S), F)` as `A`-modules, followed by the crossing
`moduleULiftCohomologyIsoAbelian`. -/
def abelianBaseChangeCohomologyFactor (F : SheafOfModules.{u} (structureSheaf S)) (j : ℕ) :
    (forgetBaseAction S).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
          (DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections S F))) ≅
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  (forgetBaseAction S).mapIso (homologyModuleULiftDerivedGlobalSectionsIso S F j) ≪≫
    moduleULiftCohomologyIsoAbelian S F j

/-- **The base change map (07MT) in degree `j`, as a map of abelian groups**

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(Cris(X/S), abelianSheaf F)`.

The target is the object [Stacks, Tag 07LG] computes, `(cohomologyFunctor S j).obj
(abelianSheaf F)`, so this is the shape in which the de Rham computation could meet the tag.  The
map itself is the given `φ` and nothing else: its degree-`j` homology, with the `A`-action
forgotten, composed with the identifications of `abelianBaseChangeCohomologyFactor`.  No
hypothesis of the tag is used, and `isIso_abelianBaseChangeCohomologyMap_iff` says that asking
this map to be an isomorphism is asking exactly what the degreewise form asks in degree `j`. -/
def abelianBaseChangeCohomologyMap (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) (j : ℕ) :
    (forgetBaseAction S).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
          (derivedBaseChangeTensorGlobalSections f F')) ⟶
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  (forgetBaseAction S).map
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).map φ) ≫
    (abelianBaseChangeCohomologyFactor F j).hom

/-- **The abelian map of degree `j` is an isomorphism exactly when the base change map is one on
`H^j`.**  The two differ by the isomorphism `abelianBaseChangeCohomologyFactor` and by forgetting
the `A`-action, and neither of those can create or destroy invertibility. -/
theorem isIso_abelianBaseChangeCohomologyMap_iff (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) (j : ℕ) :
    IsIso (abelianBaseChangeCohomologyMap f φ j) ↔
      IsIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).map φ) := by
  rw [abelianBaseChangeCohomologyMap, isIso_comp_right_iff]
  exact (isIso_homologyMap_baseChangeMap07MT_iff_forgetBaseAction f φ (j : ℤ)).symm

/-- **The negative-degree half of the degreewise form of [Stacks, Tag 07MU]**: under the seven
conditions, `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology below degree zero.

This is not an extra assumption added to the tag — it is the part of the degreewise statement
that lives in negative degrees, written out.  The target `RΓ(Cris(X/S), F)` has no cohomology
there (`isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg`), so in a negative
degree "the base change map is an isomorphism" and "the source vanishes" are the same condition,
with no comparison left to make; `degreewiseBaseChangeIso07MU_iff_abelian` is the machine check
of that.  The hypothesis block is that of `IsBaseChangeIso07MU`, condition for condition and in
the same order; see its docstring for what each condition renders. -/
def NegativeDegreeVanishing07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (_φ : BaseChangeMap07MT f F' F) : Prop :=
  IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)) →
    F'.IsQuasicoherentOnSite → IsSheafCrystal F' →
      QuasiCompact S'.toClosedFiber → QuasiSeparated S'.toClosedFiber →
        IsPullback g S.toClosedFiber S'.toClosedFiber
            (DividedPowerScheme.closedFiberMap f) →
          IsFlatModule S' F' →
            AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber →
              AlgebraicGeometry.TorIndependent S'.toClosedFiber
                  (DividedPowerScheme.closedFiberMap f) →
                ∀ n : ℤ, n < 0 →
                  IsZero ((DerivedCategory.homologyFunctor
                      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).obj
                    (derivedBaseChangeTensorGlobalSections f F'))

/-- **The abelian-valued degreewise form of [Stacks, Tag 07MU]**: under the seven conditions of
the remark, the base change map (07MT) induces an isomorphism of *abelian groups*

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ⟶ H^j(Cris(X/S), abelianSheaf F)`

for every `j : ℕ`, and `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` has no cohomology in negative degrees.

The hypothesis block is that of `IsBaseChangeIso07MU`, condition for condition and in the same
order, and `isBaseChangeIso07MU_iff_abelianDegreewise` is the machine check that this is the tag
and not a second, silently different, statement.  Two shifts from `DegreewiseBaseChangeIso07MU`
are made here, and both are equivalences rather than weakenings:

* the `A`-action is forgotten, by `isIso_homologyMap_baseChangeMap07MT_iff_forgetBaseAction`;
* the degrees are split at zero, the negative ones kept as the vanishing
  `NegativeDegreeVanishing07MU` they amount to.

What the shifts buy is that the target of the degree-`j` clause is now *literally* the object
[Stacks, Tag 07LG] computes, `(cohomologyFunctor S j).obj (abelianSheaf F)`. -/
def AbelianDegreewiseBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) : Prop :=
  IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)) →
    F'.IsQuasicoherentOnSite → IsSheafCrystal F' →
      QuasiCompact S'.toClosedFiber → QuasiSeparated S'.toClosedFiber →
        IsPullback g S.toClosedFiber S'.toClosedFiber
            (DividedPowerScheme.closedFiberMap f) →
          IsFlatModule S' F' →
            AlgebraicGeometry.IsLocalCompleteIntersectionMorphism S'.toClosedFiber →
              AlgebraicGeometry.TorIndependent S'.toClosedFiber
                  (DividedPowerScheme.closedFiberMap f) →
                (∀ j : ℕ, IsIso (abelianBaseChangeCohomologyMap f φ j)) ∧
                  ∀ n : ℤ, n < 0 →
                    IsZero ((DerivedCategory.homologyFunctor
                        (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).obj
                      (derivedBaseChangeTensorGlobalSections f F'))

/-- **The degreewise form of [Stacks, Tag 07MU] and its abelian form are the same statement.**

Forgetting the `A`-action is an equivalence on the degreewise assertion, and the degrees split at
zero: in a negative degree the target has no cohomology, so the assertion there is the vanishing
of the source and nothing more, while in degree `j : ℕ` it is the invertibility of the explicit
abelian map `abelianBaseChangeCohomologyMap`.  Nothing is assumed and no condition is added. -/
theorem degreewiseBaseChangeIso07MU_iff_abelian (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) :
    DegreewiseBaseChangeIso07MU f g F' F φ ↔
      AbelianDegreewiseBaseChangeIso07MU f g F' F φ := by
  constructor
  · intro h hp hqc hcr hqcpt hqsep hpb hflat hlci htor
    have hn := h hp hqc hcr hqcpt hqsep hpb hflat hlci htor
    refine ⟨fun j => (isIso_abelianBaseChangeCohomologyMap_iff f φ j).2 (hn (j : ℤ)),
      fun n hneg => ?_⟩
    have := hn n
    exact IsZero.of_iso
      (isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg F n hneg)
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ))
  · intro h hp hqc hcr hqcpt hqsep hpb hflat hlci htor n
    obtain ⟨hpos, hneg⟩ := h hp hqc hcr hqcpt hqsep hpb hflat hlci htor
    rcases lt_or_ge n 0 with hlt | hle
    · have hsrc := hneg n hlt
      exact hsrc.eq_of_src
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) n).map φ)
        (hsrc.iso (isZero_homologyFunctor_obj_moduleULiftDerivedGlobalSections_of_neg F n
          hlt)).hom ▸ inferInstance
    · lift n to ℕ using hle
      exact (isIso_abelianBaseChangeCohomologyMap_iff f φ n).1 (hpos n)

/-- **[Stacks, Tag 07MU] is the abelian degreewise statement, and nothing else.**  Composing
`isBaseChangeIso07MU_iff_degreewise` with `degreewiseBaseChangeIso07MU_iff_abelian`: the whole
content of the tag is that an explicit map of abelian groups into
`(cohomologyFunctor S j).obj (abelianSheaf F)` is an isomorphism for every `j : ℕ`, together with
the vanishing of `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A` in negative degrees.

This measures where the remaining work sits.  The first clause is in the shape the de Rham
computation [Stacks, Tag 07LG] speaks in — its target is that tag's own target — and the second
is what conditions (4), (5) and (7) of the remark have to buy.  This is not a proof of the tag;
see the module documentation for what the first clause still needs from the de Rham side. -/
theorem isBaseChangeIso07MU_iff_abelianDegreewise (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) :
    IsBaseChangeIso07MU f g F' F φ ↔ AbelianDegreewiseBaseChangeIso07MU f g F' F φ :=
  (isBaseChangeIso07MU_iff_degreewise f g F' F φ).trans
    (degreewiseBaseChangeIso07MU_iff_abelian f g F' F φ)

/-- **The negative-degree vanishing is part of the tag**, as the restriction of the abelian
degreewise form to its second clause.  Kept as a named proposition because it is the half of the
degreewise statement that the de Rham computation says nothing about. -/
theorem negativeDegreeVanishing07MU_of_isBaseChangeIso07MU (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (F' : SheafOfModules.{u} (structureSheaf S')) (F : SheafOfModules.{u} (structureSheaf S))
    (φ : BaseChangeMap07MT f F' F) (h : IsBaseChangeIso07MU f g F' F φ) :
    NegativeDegreeVanishing07MU f g F' F φ :=
  fun hp hqc hcr hqcpt hqsep hpb hflat hlci htor =>
    ((isBaseChangeIso07MU_iff_abelianDegreewise f g F' F φ).1 h
      hp hqc hcr hqcpt hqsep hpb hflat hlci htor).2

/-- **The abelian graded form of the conclusion of [Stacks, Tag 07MU]**: an isomorphism of
abelian groups

`H^j(RΓ(Cris(X'/S'), F') ⊗^L_{A'} A) ≅ H^j(Cris(X/S), abelianSheaf F)`

for every `j : ℕ`, from a base change map (07MT) that is an isomorphism in `D(A)`.  This is
`baseChangeCohomologyIso` carried across [Stacks, Tag 03FD] by
`moduleULiftCohomologyIsoAbelian`, and its underlying map is
`abelianBaseChangeCohomologyMap`.

Only `IsIso φ` is asked for, not the seven conditions, exactly as in `baseChangeCohomologyIso`:
this is the shape in which the conclusion is consumed. -/
def baseChangeCohomologyIsoAbelian (f : S.S ⟶ S'.S)
    {F' : SheafOfModules.{u} (structureSheaf S')} {F : SheafOfModules.{u} (structureSheaf S)}
    (φ : BaseChangeMap07MT f F' F) [IsIso φ] (j : ℕ) :
    (forgetBaseAction S).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
          (derivedBaseChangeTensorGlobalSections f F')) ≅
      (cohomologyFunctor S j).obj (abelianSheaf F) :=
  (forgetBaseAction S).mapIso (baseChangeCohomologyIso f φ j) ≪≫
    moduleULiftCohomologyIsoAbelian S F j

end BaseChange

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
