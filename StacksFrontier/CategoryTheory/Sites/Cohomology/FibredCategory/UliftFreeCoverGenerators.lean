module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomologyIso
public import StacksFrontier.CategoryTheory.Sites.IntegralCechHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Cellular
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafified canonical presentation is a direct sum of free abelian sheaves

Let `C` be a small category with a Grothendieck topology `J` admitting sheafification of abelian
presheaves with values in `AddCommGrpCat.{max u v}`. Every such abelian presheaf `X` carries the
canonical presentation `Stacks.CategoryHomology.uliftFreeCover X`, the sectionwise direct sum over
all pairs `(U, x)` with `x` a section of `X` over `U` of the universe-lifted free abelian
presheaves `ULift ℤ^{(- ⟶ U)}` on representables. This file identifies its sheafification with a
direct sum of the free abelian sheaves `j_{U!} ℤ_U`:

```
(uliftFreeCover X)^# ≅ ∐_{(U, x)} j_{U!} ℤ_U.
```

That is the identification the module docstring of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomologyIso`
records as missing, and with it the acyclicity hypothesis `UliftFreeCoverLowerShriekAcyclic` that
the comparison of Stacks 08PJ carries is discharged: it follows from
`AbelianLowerShriekGeneratorsAcyclic` alone, through the reduction
`uliftFreeCoverLowerShriekAcyclic_of_isSumOfExtensionByZeroUnitsAb` in the namespace
`Stacks.Sites.FibredCategory.FibredCategorySituation`.
Both of those are proved for every fibred situation — the first in
`ProjectionLowerShriekAcyclic.lean`, the second here from the computation of `Lπ_!` on bounded
above complexes of direct sums of the `j_{U!} ℤ_U` — so Stacks 08PJ is stated here with no
hypothesis at all.

The identification has two halves, and both are supplied here.

*The sectionwise direct sum is a coproduct.* `Stacks.CategoryHomology.directSumPresheaf` is built
by hand, with an inclusion of each summand and a descent morphism out of it, and its universal
property was never recorded; it is recorded here as a colimit cofan, from which sheafification —
a left adjoint, hence preserving all coproducts — carries it to a coproduct of abelian sheaves.

*The sheafification of a free abelian presheaf on a representable is a free abelian sheaf.* This
is already true before sheafifying, at the level of presheaves: the universe lift of a free
abelian group is the free abelian group on the lifted type.

## Main definitions

* `Stacks.CategoryHomology.isColimitCofanDirectSumPresheaf`: the sectionwise direct sum of a
  family of abelian presheaves, with the inclusions of its summands, is a coproduct.
* `Stacks.Cohomology.DerivedLowerShriek.uliftFreeRepresentablePresheafIsoFreeAbelian`: the
  universe-lifted free abelian presheaf on a representable is the free abelian presheaf on the
  universe-lifted representable.
* `Stacks.Cohomology.DerivedLowerShriek.sheafifyUliftFreeRepresentablePresheafIso`: its
  sheafification is `j_{U!} ℤ_U`.

## Main results

* `Stacks.CategoryHomology.directSumPresheafIncl_desc` and
  `Stacks.CategoryHomology.directSumPresheaf_hom_ext`: the two halves of the universal property
  of the sectionwise direct sum.
* `Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnitsAb_sheafify_uliftFreeCover`:
  **the missing identification** — the sheafification of the canonical presentation of an abelian
  presheaf is a direct sum of the free abelian sheaves `j_{U!} ℤ_U`.
* `uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic`, in the namespace
  `Stacks.Sites.FibredCategory.FibredCategorySituation`: the hypothesis
  `UliftFreeCoverLowerShriekAcyclic` of the comparison of Stacks 08PJ follows from
  `AbelianLowerShriekGeneratorsAcyclic`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyIsoOfGenerators`
  and `...derivedLowerShriekHomologyObjIsoOfGenerators`: the comparison of Stacks 08PJ with the
  cover acyclicity hypothesis discharged, the two acyclicity statements of Stacks 07AC still taken
  as arguments.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianLowerShriekGeneratorsAcyclic`:
  `Lπ_!` is acyclic on the direct sums of the `j_{U!} ℤ_U`, for every fibred situation.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyIsoFiberHomology`:
  **Stacks 08PJ**. For every `n ≥ 0`, `L_n π_!(F) = H^{-n}(Lπ_! F)` is the sheaf `L_n(F)` of
  Stacks 08PI, naturally in `F`, with no hypothesis.

## Implementation notes

**Which universe lift.** `ULift.{a} α` and `ULift.{b} α` are different types whenever `a ≠ b`,
even when both land in the same `Type`, because the lifting level is a parameter of the
constant. The cover's summand `Stacks.CategoryHomology.uliftFreeRepresentablePresheaf.{u, v}`
lifts by `v`, so the free abelian sheaf it has to be compared with is
`Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{v}`, whose representable is lifted
by `v` as well — the instantiation `extensionByZeroUnitAb.{max u v}`, which has the same
coefficient category, states a different thing and does not typecheck against the cover. This is
the phenomenon the target file records as "`uliftFreeRepresentablePresheaf` has its value
universe occurring alone inside a `ULift`", and every call below writes its universes out for it.

**Only one commuting iso is needed.** `AddCommGrpCat.freeCompUliftFunctorIso` is applied once,
whiskered by `yoneda.obj U`, and the rest is associativity. The two-step assembly
`Stacks.IntegralCech.uliftFreeChainIso`, which additionally composes
`CategoryTheory.uliftFunctorCompIso`, is not needed: there the index universe of the family is
independent of the coefficient universe and the types get lifted twice, whereas here the cover
and the free abelian sheaf lift the hom sets of `C` by the single level `v`.

**The coproduct of sheaves must be seated by hand.** Synthesising
`HasColimit (Discrete.functor fun i => extensionByZeroUnitAb J (U i))` exhausts the typeclass
heartbeat budget ("deterministic timeout at `typeclass`" at the default 20000), exactly
as `Stacks.Cohomology.DerivedLowerShriek.hasColimitsOfShape_discrete_sheafAb` records for the
colimits it exists to supply. So that instance is applied explicitly and the resulting
`HasCoproduct` is put in the local context before the coproduct is mentioned.

**Decidable equality on the index.** `Stacks.CategoryHomology.directSumPresheafIncl` carries a
`DecidableEq` instance on the index type, as `DirectSum.of` does. The conclusion is a `Nonempty`
of an isomorphism, so which instance is used is immaterial; `classical` supplies one and every
occurrence inside a single proof is synthesised from it, which is what the computation rules of
the direct sum need.

**Universes of the corollaries.** The situation is taken at `vC = uC` with coefficients
`AddCommGrpCat.{max w uD vD uC}`, as in the file whose hypothesis is being discharged, and the
generic statement is instantiated at `u := uC`, `v := max w uD vD uC`; the coefficient category
`AddCommGrpCat.{max u v}` of the generic statement then normalises to
`AddCommGrpCat.{max w uD vD uC}` and the index universe `Type (max u v)` of
`IsSumOfExtensionByZeroUnitsAb` to `Type (max w uD vD uC)`, so the two agree on the nose.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology
open scoped DirectSum

universe u v t uD vD uC w

namespace Stacks.CategoryHomology

section Coproduct

variable {C : Type u} [SmallCategory C] {ι : Type t} (F : ι → (Cᵒᵖ ⥤ AddCommGrpCat.{t}))
  [DecidableEq ι]

/-- **The inclusion of a summand followed by a descent morphism is the given component.** This is
`Stacks.CategoryHomology.directSumPresheafDesc_app_of` read as an identity of morphisms of
presheaves rather than of sections over an object. -/
lemma directSumPresheafIncl_desc {G : Cᵒᵖ ⥤ AddCommGrpCat.{t}} (η : ∀ i, F i ⟶ G) (i : ι) :
    directSumPresheafIncl F i ≫ directSumPresheafDesc F η = η i :=
  NatTrans.ext (funext fun Y => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    directSumPresheafDesc_app_of F η i Y x))

/-- **A morphism out of a sectionwise direct sum is determined by its restrictions to the
summands.** Over each object a homomorphism out of a direct sum of abelian groups is determined by
its restrictions to the summands, which is `DirectSum.addHom_ext'`. -/
lemma directSumPresheaf_hom_ext {G : Cᵒᵖ ⥤ AddCommGrpCat.{t}} (f g : directSumPresheaf F ⟶ G)
    (h : ∀ i, directSumPresheafIncl F i ≫ f = directSumPresheafIncl F i ≫ g) : f = g :=
  NatTrans.ext (funext fun Y => AddCommGrpCat.hom_ext (DirectSum.addHom_ext' fun i =>
    congrArg (fun k : F i ⟶ G => (k.app Y).hom) (h i)))

/-- **The sectionwise direct sum of abelian presheaves is a coproduct.** The cofan of the
inclusions of the summands is a colimit: the descent morphism of
`Stacks.CategoryHomology.directSumPresheafDesc` factors every cofan, and it is the only morphism
that does. This is the universal property that
`Stacks.CategoryHomology.directSumPresheaf` was built to have but which was never recorded. -/
def isColimitCofanDirectSumPresheaf :
    IsColimit (Cofan.mk (directSumPresheaf F) (directSumPresheafIncl F)) :=
  Cofan.IsColimit.mk _ (fun s => directSumPresheafDesc F s.inj)
    (fun s j => directSumPresheafIncl_desc F s.inj j)
    (fun s _m hm => directSumPresheaf_hom_ext F _ _ fun i =>
      (hm i).trans (directSumPresheafIncl_desc F s.inj i).symm)

end Coproduct

end Stacks.CategoryHomology

namespace Stacks.Cohomology.DerivedLowerShriek

section Sheafify

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- **The universe lift of the free abelian presheaf on a representable is the free abelian
presheaf on the universe-lifted representable.** Pointwise this is the identification of
`ULift ℤ^{(V ⟶ U)}` with `ℤ^{ULift (V ⟶ U)}`, which is
`AddCommGrpCat.freeCompUliftFunctorIso` whiskered by the representable presheaf of `U`; the
lifting level is `v` on both sides, as it must be. -/
def uliftFreeRepresentablePresheafIsoFreeAbelian (U : C) :
    uliftFreeRepresentablePresheaf.{u, v} U ≅
      uliftYoneda.{v}.obj U ⋙ AddCommGrpCat.free.{max u v} :=
  Functor.associator (yoneda.obj U) AddCommGrpCat.free.{u}
      AddCommGrpCat.uliftFunctor.{v, u} ≪≫
    Functor.isoWhiskerLeft (yoneda.obj U) AddCommGrpCat.freeCompUliftFunctorIso.{v, u} ≪≫
    (Functor.associator (yoneda.obj U) CategoryTheory.uliftFunctor.{v, u}
      AddCommGrpCat.free.{max v u}).symm

/-- **The sheafification of the universe-lifted free abelian presheaf on a representable is the
free abelian sheaf `j_{U!} ℤ_U`.** The two presheaves are already isomorphic before sheafifying,
so this is the image of
`Stacks.Cohomology.DerivedLowerShriek.uliftFreeRepresentablePresheafIsoFreeAbelian` under
sheafification. -/
def sheafifyUliftFreeRepresentablePresheafIso (U : C) :
    (presheafToSheaf J AddCommGrpCat.{max u v}).obj (uliftFreeRepresentablePresheaf.{u, v} U) ≅
      extensionByZeroUnitAb.{v} J U :=
  (presheafToSheaf J AddCommGrpCat.{max u v}).mapIso
    (uliftFreeRepresentablePresheafIsoFreeAbelian.{u, v} U)

/-- **The sheafification of the canonical presentation is a direct sum of the free abelian sheaves
`j_{U!} ℤ_U`.** The canonical presentation of an abelian presheaf `X` is the sectionwise direct
sum, over all pairs `(U, x)` with `x` a section of `X` over `U`, of the universe-lifted free
abelian presheaves on representables. That direct sum is a coproduct of presheaves
(`Stacks.CategoryHomology.isColimitCofanDirectSumPresheaf`); sheafification is a left adjoint,
hence preserves it; and each sheafified summand is `j_{U!} ℤ_U`
(`Stacks.Cohomology.DerivedLowerShriek.sheafifyUliftFreeRepresentablePresheafIso`). So the
sheafified presentation is the coproduct of the `j_{U!} ℤ_U` over the same index family, which is
the class on which `AbelianLowerShriekGeneratorsAcyclic` asserts acyclicity. -/
theorem isSumOfExtensionByZeroUnitsAb_sheafify_uliftFreeCover
    (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    IsSumOfExtensionByZeroUnitsAb.{v, u, u} J
      ((presheafToSheaf J AddCommGrpCat.{max u v}).obj (uliftFreeCover.{u, v} X)) := by
  classical
  have hcop : HasCoproduct fun i : uliftFreeCoverIndex.{u, v} X =>
      extensionByZeroUnitAb.{v} J i.1 :=
    (hasColimitsOfShape_discrete_sheafAb.{max u v, u, u} J
      (uliftFreeCoverIndex.{u, v} X)).has_colimit _
  refine ⟨uliftFreeCoverIndex.{u, v} X, fun i => i.1, ⟨?_⟩⟩
  set P : uliftFreeCoverIndex.{u, v} X → (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
    fun i => uliftFreeRepresentablePresheaf.{u, v} i.1
  have hsheafify : IsColimit (Cofan.mk ((presheafToSheaf J AddCommGrpCat.{max u v}).obj
      (directSumPresheaf P))
      (fun i => (presheafToSheaf J AddCommGrpCat.{max u v}).map
        (directSumPresheafIncl P i)) :
      Cofan fun i => (presheafToSheaf J AddCommGrpCat.{max u v}).obj (P i)) :=
    isColimitCofanMkObjOfIsColimit _ _ _ (isColimitCofanDirectSumPresheaf P)
  have hgen := (IsColimit.precomposeHomEquiv
    (Discrete.natIso (F := Discrete.functor fun i : uliftFreeCoverIndex.{u, v} X =>
        extensionByZeroUnitAb.{v} J i.1)
      (G := Discrete.functor fun i : uliftFreeCoverIndex.{u, v} X =>
        (presheafToSheaf J AddCommGrpCat.{max u v}).obj (P i))
      fun i => (sheafifyUliftFreeRepresentablePresheafIso.{u, v} J i.as.1).symm) _).symm hsheafify
  exact (coproductIsCoproduct fun i : uliftFreeCoverIndex.{u, v} X =>
    extensionByZeroUnitAb.{v} J i.1).coconePointUniqueUpToIso hgen

end Sheafify

end Stacks.Cohomology.DerivedLowerShriek

namespace Stacks.Sites.FibredCategory

namespace FibredCategorySituation

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

variable [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC})
    (ComplexShape.up ℤ))]

/-- **The acyclicity of the sheafified canonical presentation follows from the acyclicity of the
generators.** The missing identification of the sheafified presentation with a direct sum of the
free abelian sheaves `j_{U!} ℤ_U` is
`Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnitsAb_sheafify_uliftFreeCover`, so
the reduction `uliftFreeCoverLowerShriekAcyclic_of_isSumOfExtensionByZeroUnitsAb` applies with
nothing left to assume beyond `AbelianLowerShriekGeneratorsAcyclic`. -/
theorem uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic
    (hgen : s.AbelianLowerShriekGeneratorsAcyclic) :
    s.UliftFreeCoverLowerShriekAcyclic :=
  s.uliftFreeCoverLowerShriekAcyclic_of_isSumOfExtensionByZeroUnitsAb hgen fun X =>
    Stacks.Cohomology.DerivedLowerShriek.isSumOfExtensionByZeroUnitsAb_sheafify_uliftFreeCover.{uC,
      max w uD vD uC} s.topology X

/-- **Stacks 08PJ, with the cover acyclicity discharged.** For every `n ≥ 0` the functor
`F ↦ H^{-n}(Lπ_! F) = L_n π_!(F)` on abelian sheaves on the total category is the functor
`F ↦ L_n(F)` of Stacks 08PI, the sheaf on the base associated to `V ↦ H_n(C_V, F|_{C_V})`,
naturally in `F`, for any choice of `Lπ_!` and granted that it is acyclic on the direct sums of
the free abelian sheaves `j_{U!} ℤ_U`. Both inputs are proved for every fibred situation, and the
statement with neither is `derivedLowerShriekHomologyIsoFiberHomology`. -/
def derivedLowerShriekHomologyIsoOfGenerators (h : s.AbelianLowerShriekAcyclic)
    (hgen : s.AbelianLowerShriekGeneratorsAcyclic) (n : ℕ) :
    s.derivedAbelianLowerShriekHomology n ≅
      sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        fiberHomologyPresheafFunctor s n ⋙
          presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  s.derivedLowerShriekHomologyIso h (s.uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic hgen) n

/-- **Stacks 08PJ at a single abelian sheaf, with the cover acyclicity discharged.** For an
abelian sheaf `F` on the total category and `n ≥ 0`, the `n`th derived lower shriek
`L_n π_!(F) = H^{-n}(Lπ_! F)` is the sheaf `L_n(F)` of fibre homology of Stacks 08PI, formed from
the underlying presheaf of `F`. -/
def derivedLowerShriekHomologyObjIsoOfGenerators (h : s.AbelianLowerShriekAcyclic)
    (hgen : s.AbelianLowerShriekGeneratorsAcyclic) (n : ℕ)
    (F : Sheaf s.topology AddCommGrpCat.{max w uD vD uC}) :
    (s.derivedAbelianLowerShriekHomology n).obj F ≅ fiberHomologySheaf s F.obj n :=
  (s.derivedLowerShriekHomologyIsoOfGenerators h hgen n).app F

end Derived

section Unconditional

universe vC

attribute [local instance] HasDerivedCategory.standard

/-- **`Lπ_!` is acyclic on the direct sums of the free abelian sheaves `j_{U!} ℤ_U`**, for the
projection of every fibred category. Such a sum `P`, placed in degree zero, is a bounded above
complex with terms in the class with which Stacks 07AC builds `Lπ_!`, so `Lπ_!` is computed on it
degreewise (`isIso_derivedAbelianLowerShriekComparison_app`): `Lπ_!(P) = π_!(P)` sits in degree
zero. -/
theorem abelianLowerShriekGeneratorsAcyclic (s : FibredCategorySituation.{uD, vD, uC, vC, w}) :
    s.AbelianLowerShriekGeneratorsAcyclic := by
  intro P hP
  have : s.abelianLowerShriek.Additive := s.abelianLowerShriek_additive
  have : s.abelianLowerShriek.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (F := s.abelianLowerShriek)
  let K := (HomologicalComplex.single (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
    (ComplexShape.up ℤ) 0).obj P
  have hK : ∀ n, Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{max w uD vD uC}
      s.topology (K.X n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · obtain ⟨ι, U, ⟨e⟩⟩ := hP
      exact ⟨ι, U, ⟨e ≪≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P).symm⟩⟩
    · obtain ⟨Z, hZ, ι, U, ⟨e⟩⟩ :=
        (inferInstance : (Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb.{
          max w uD vD uC} s.topology).ContainsZero).exists_zero
      exact ⟨ι, U, ⟨e ≪≫ hZ.iso (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)⟩⟩
  have := s.isIso_derivedAbelianLowerShriekComparison_app K hK
  let e₂ : s.derivedAbelianLowerShriek.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        ((s.abelianLowerShriek.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    s.derivedAbelianLowerShriek.mapIso
        ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
      asIso ((Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{
        max w uD vD uC, vC, uC, vD, uD} s.topology s.base.J s.p).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app _
  let e : (DerivedCategory.singleFunctor _ 0).obj (s.abelianLowerShriek.obj P) ≅
      s.derivedAbelianLowerShriek.obj ((DerivedCategory.singleFunctor _ 0).obj P) :=
    (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      s.abelianLowerShriek (ComplexShape.up ℤ) 0).app P)).symm ≪≫ e₂.symm
  exact DerivedCategory.TStructure.t.isGE_of_iso e 0

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

/-- **Stacks 08PJ.** Let `p : C ⥤ D` be a fibred category over a ringed site `D`, with `C` carrying
the inherited topology and `π` the induced morphism of topoi (Stacks 08P8). For every `n ≥ 0`,
the functor `F ↦ L_n π_!(F) = H^{-n}(Lπ_! F)` on abelian sheaves on `C` is the functor
`F ↦ L_n(F)` of Stacks 08PI, the sheaf on `D` associated to the presheaf
`V ↦ H_n(C_V, F|_{C_V})`, naturally in `F`.

Here `Lπ_!` is the left derived functor whose existence is Stacks 07AC
(`hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy`), and the two acyclicity inputs of
the comparison `derivedLowerShriekHomologyIso` are proved for every fibred situation:
`abelianLowerShriekAcyclic` and `abelianLowerShriekGeneratorsAcyclic`. -/
@[stacks 08PJ]
def derivedLowerShriekHomologyIsoFiberHomology (n : ℕ) :
    s.derivedAbelianLowerShriekHomology n ≅
      sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        fiberHomologyPresheafFunctor s n ⋙
          presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  s.derivedLowerShriekHomologyIso s.abelianLowerShriekAcyclic
    (s.uliftFreeCoverLowerShriekAcyclic_of_generatorsAcyclic
      (abelianLowerShriekGeneratorsAcyclic s)) n

end Unconditional

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
