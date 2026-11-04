module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeSquareRinged07MS
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHomOrdinaryPullback

/-!
# The base change map of [Stacks, Tag 07MS] on `S_Zar`

In the situation of [Stacks, Tag 07MJ] — a morphism `f : (S, I, γ) ⟶ (S', I', γ')` of divided
power schemes and an arbitrary compatible `g : X ⟶ X'` — let `F'` be an `𝒪_{X'/S'}`-module and
`F = f_cris^*F'` its pullback.  [Stacks, Tag 07MS] constructs a canonical base change map

`L(S ⟶ S')^* Rτ_{X'/S', *}F' ⟶ Rτ_{X/S, *}F`

in `D(𝒪_S)`, with the hint: compose the base change map of Cohomology on Sites, Remark 07A7, with
the canonical map `Lf_cris^*F' ⟶ f_cris^*F' = F`.  This file does exactly that.

* The four morphisms of ringed topoi are `structureRingedHom S` and `structureRingedHom S'`
  (`τ`, [Stacks, Tag 07IM]), `crisRingedHomComp f g h` (`f_cris`, [Stacks, Tag 07IK]) and
  `zariskiRingedHom f.hom` (`f_Zar`); the square 2-commutes by `structureSquareTwoIso`.
* The base change map of [Stacks, Tag 07A7] for a 2-commutative square, followed by
  `Rτ_{X/S, *}` of `Lf_cris^*F' ⟶ f_cris^*F'`, is
  `Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMapOfTwoIsoOfModule`.
* `f_cris^*F'` is identified with the chapter's pullback `crisModuleInverseImage f g h F'` by
  `crisModuleInverseImageIsoPullbackModules`.

Derived categories are the unbounded ones, `D(𝒪_S)` being the derived category of sheaves of
modules over `𝒪_S` (sections raised to the universe `u + 1` of the topoi,
`zariskiRingedTopos`), and `𝒪_{X/S}`-modules are the chapter's `ModuleSheaf S` read through
`crisModuleEquivalence`.

## Main definitions

* `tauDerivedDirectImage` — `Rτ_{X/S, *}F ∈ D(𝒪_S)`.
* `crisSheafBaseChangeMap` — **the base change map of [Stacks, Tag 07MS]**.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {S S' : GlobalCrystallineSituation.{u}} (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- `F` in degree zero of `D(𝒪_{X/S})`, the unbounded derived category of modules on the
crystalline ringed topos. -/
abbrev crisModuleSingle (S : GlobalCrystallineSituation.{u}) (F : ModuleSheaf S) :
    DerivedCategory (SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u + 1} (J := (crisRingedTopos S).J))
        (crisRingedTopos S).O)) :=
  (DerivedCategory.singleFunctor _ (0 : ℤ)).obj ((crisModuleEquivalence S).functor.obj F)

/-- **`Rτ_{X/S, *}F` in `D(𝒪_S)`**, the derived direct image along the structure morphism
`τ_{X/S}` of [Stacks, Tag 07IM] of a sheaf of `𝒪_{X/S}`-modules placed in degree zero. -/
abbrev tauDerivedDirectImage (S : GlobalCrystallineSituation.{u}) (F : ModuleSheaf S) :
    DerivedCategory (SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u + 1}
          (J := (zariskiRingedTopos S.S.scheme).J))
        (zariskiRingedTopos S.S.scheme).O)) :=
  (derivedPushforward (structureRingedHom S)).obj (crisModuleSingle S F)

/-- The derived pullback along `f_Zar` exists: the general existence statement of Stacks 06YY,
`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`, at the
morphism of small Zariski ringed topoi of `f`. -/
instance hasLeftDerivedFunctor_zariskiRingedHom :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
      (X := zariskiRingedTopos S.S.scheme) (Y := zariskiRingedTopos S'.S.scheme)
      (zariskiRingedHom f.hom)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget
        (Y := zariskiRingedTopos S'.S.scheme)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := zariskiRingedTopos S.S.scheme) (Y := zariskiRingedTopos S'.S.scheme)
    (zariskiRingedHom f.hom)

/-- **Stacks Project, Tag 07MS: the canonical base change map**

`L(S ⟶ S')^* Rτ_{X'/S', *}F' ⟶ Rτ_{X/S, *}F`   in `D(𝒪_S)`,

for an `𝒪_{X'/S'}`-module `F'`, its pullback `F = f_cris^*F'` (`crisModuleInverseImage`), and an
arbitrary morphism `g : X ⟶ X'` over a morphism of divided power bases `f` — the situation of
[Stacks, Tag 07MJ].  As the source's hint prescribes, it is the base change map of
[Stacks, Tag 07A7] for the square `structureSquareTwoIso`, followed by `Rτ_{X/S, *}` of the
canonical map `Lf_cris^*F' ⟶ f_cris^*F' = F`. -/
@[stacks 07MS "the canonical base change map L(S ⟶ S')^* Rτ_{X'/S',*} F' ⟶ Rτ_{X/S,*} F in D(O_S),
F = f_cris^* F', for an arbitrary morphism g : X ⟶ X', built as the hint prescribes"]
def crisSheafBaseChangeMap (F' : ModuleSheaf S') :
    (derivedPullback (X := zariskiRingedTopos S.S.scheme) (Y := zariskiRingedTopos S'.S.scheme)
        (zariskiRingedHom f.hom)).obj (tauDerivedDirectImage S' F') ⟶
      tauDerivedDirectImage S ((crisModuleInverseImage f g h).obj F') :=
  derivedBaseChangeMapOfTwoIsoOfModule (structureRingedHom S') (crisRingedHomComp f g h)
      (structureRingedHom S) (zariskiRingedHom f.hom) (structureSquareTwoIso f g h)
      ((crisModuleEquivalence S').functor.obj F') ≫
    (derivedPushforward (structureRingedHom S)).map
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).map
        (crisModuleInverseImageIsoPullbackModules f g h F').inv)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
