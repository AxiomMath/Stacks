module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtZero
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentTwoTermOfDouble
public import StacksFrontier.Deformation.ToposThickening.LiftingBetweenThickenings

/-!
# The derivations of a thickening diagram are the homomorphisms out of `H⁰(NL(α))`

Let `D` be a diagram of two square-zero thickenings of ringed topoi as in
[Stacks Project, Tag 08UG], presented after the source's own reduction as a diagram of sheaves
of commutative rings on one site. `Deformation.ToposThickening.Derivation D.toSituation` is the
group acting on the morphisms filling that diagram: a section-wise derivation `O'₁ ⟶ 𝒢₂` over
`O_{B'₁}` which vanishes on the ideal `𝒢₁`. The source writes the acting group instead as

`Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*𝒢₂) = Hom(H⁰(NL(α)), 𝒢₂)`,

a group of homomorphisms out of the degree `0` cohomology of the naive cotangent complex of a
polynomial presentation `α` of `O₁` over `O_{B₁}`. This file identifies the two, and feeds that
identification into `Deformation.ToposThickening.LiftDiagram.liftEquivFactorization`.

The identification has two halves. The first is the descent of a section-wise derivation of the
*thickened* structure sheaf `O'₁` to a relative derivation of the *reduced* one `O₁`: a
derivation of the diagram kills the ideal, so it is constant on the fibres of the reduction
`O'₁ ⟶ O₁`, and that reduction is locally surjective, so the resulting family glues. This is
`Stacks.Sites.QuotientDerivation.descend`, applied through
`Deformation.ToposThickening.Derivation.toQuotientDerivation`. The second half is the universal
property of the sheaf of relative differentials, `Stacks 04BL`, which corepresents relative
derivations, together with the degree `0` half of `Stacks 08TY` identifying `H⁰(NL(α))` with
`Ω_{O₁/O_{B₁}}`; both are in the library, and are composed here as
`Deformation.ToposThickening.differentialsOfSiteHomEquiv` and
`Stacks.SheafOfModules.presentationConormalCokernelIsoDifferentials`.

## Main definitions

* `Deformation.ToposThickening.derivation'CompEquiv`: relative derivations for a base map `c`
  and for a base map `ρ ≫ c` with `ρ` locally surjective are the same.
* `Deformation.ToposThickening.Derivation.toQuotientDerivation` and
  `Deformation.ToposThickening.Derivation.descendDerivation`: a derivation of a situation, as
  section-wise derivation data through the reduction, and the relative derivation of the reduced
  structure sheaf it descends to.
* `Deformation.ToposThickening.derivationEquivDerivation'`: those two descriptions are the same
  — the derivations of a situation are exactly the relative derivations of its reduced structure
  sheaf over its thickened base.
* `Deformation.ToposThickening.differentialsOfSiteHomEquiv`: the universal property of
  `Ω_{O₂/O₁}` as a bijection, `Hom(Ω_{O₂/O₁}, 𝒢) ≃ Der_{O₁}(O₂, 𝒢)`.
* `Deformation.ToposThickening.LiftDiagram.values`: the module the derivations of a diagram take
  their values in, `𝒢₂` read over `O₁` through the comparison `g`.
* `Deformation.ToposThickening.LiftDiagram.presentationTwoTerm`: `NL(α)` for a polynomial
  presentation `α` of the reduced structure sheaf of the front square over its reduced base, as
  a two-term complex in the derived category of sheaves of modules, with
  `presentationTwoTerm_conormal`, `presentationTwoTerm_base` and `presentationTwoTerm_d`
  naming its two terms and its differential by the conormal sequence of the presentation.

## Main results

* `Deformation.ToposThickening.LiftDiagram.derivationEquivDifferentialsDerivation`: the
  derivations of the diagram are the relative derivations of `O₁` over `O_{B₁}` with values in
  `g_*𝒢₂`. This is the source's first equality.
* `Deformation.ToposThickening.LiftDiagram.derivationEquivCokernelHom` and
  `LiftDiagram.derivationEquivTwoTermCokernelHom`: the identification of the two acting groups,
  `Derivation D.toSituation ≃ Hom(H⁰(NL(α)), 𝒢₂)`, written at the conormal map of the
  presentation and at the differential of `NL(α)` respectively — the same map by
  `LiftDiagram.cokernelHom_eq`. This is the input called `κ` by
  `LiftDiagram.liftEquivFactorization`.
* `Deformation.ToposThickening.LiftDiagram.cokernelHomTranslate_existsUnique`: clause (2) of
  [Stacks Project, Tag 08UG] at the source's own acting group — the morphisms filling the
  diagram form a principal homogeneous space under `Hom(H⁰(NL(α)), 𝒢₂)`.
* `Deformation.ToposThickening.LiftDiagram.liftEquivFactorizationOfPresentation`: the bijection
  of Steps 2 and 3 of the proof of [Stacks Project, Tag 08UG] between the morphisms filling the
  source's diagram and the factorizations of a homomorphism out of the conormal module through
  the degree `0` term of `NL(α)`, with nothing assumed beyond the presentation and the two
  base points at which the two principal homogeneous spaces are trivialized.

## Implementation notes

The descent is taken from `Stacks.Sites.QuotientDerivation`, which is stated for a locally
surjective morphism of sheaves of rings on an arbitrary site, so nothing about it is redone
here: what this file supplies is the translation of the section-wise `Derivation` of a
`DerivationSituation` into that vocabulary, and the inverse translation, which is
precomposition with the reduction.

`DerivationSituation` carries neither the local surjectivity of its reduction nor the
identification of its ideal module with the kernel of that reduction — both are properties of
the squares a situation comes from rather than of the situation itself — so the general
statements below take them as hypotheses. The `LiftDiagram` statements take none: a diagram
supplies `LiftSquare.locallySurjective`, `LiftSquare.exists_incl` and
`LiftSquare.reduction_incl` itself.

The base ring of the descended derivation is the *thickened* base `O_{B'₁}`, since that is what
a derivation of a situation is given to kill. For a diagram the two agree, because the base
reduction `O_{B'₁} ⟶ O_{B₁}` is locally surjective and the values are a sheaf; that step is
`derivation'CompEquiv`, and it is what lets the acting group be stated over `O_{B₁}`, as the
source states it.

Universes. The sheaves of rings are taken in `CommRingCat.{max w u v}` on a site `C : Type u`
with `Category.{v} C`. This is forced rather than chosen, exactly as for
`Stacks.SheafOfModules.exists_presentation_conormalExtClass`: the sheaf of relative
differentials corepresents a functor whose values are hom types of `SheafOfModules` on the
site, so its module universe absorbs `max u v`, while `Stacks.Sites.QuotientDerivation` is
stated for a module universe equal to the ring universe. As `w` is free, the statements cover
every ring universe containing `max u v`.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), `H⁰(NL(α)) = Ω_{B/A}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite derivationsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe v u w t

namespace Deformation.ToposThickening

/-! ### Changing the base ring of a relative derivation -/

section Base

-- `ringSheaf` unfolds to `sheafCompose`, whose action on objects is a structure
-- instance; without this, unification cannot see that the sections of the underlying sheaf of
-- rings are the sections of the sheaf of commutative rings. It is scoped to this section: made
-- file-wide it also unfolds inside the derived category of the sheaves of modules below, where
-- the resulting unification does not terminate.
attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R S O : Sheaf J CommRingCat.{w}} (ρ : R ⟶ S) (c : S ⟶ O)
  (M : SheafOfModules.{w} (ringSheaf O))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A relative derivation for the base map `ρ ≫ c` kills the whole image of `c`, as soon as `ρ`
is locally surjective: the sections of `S` are locally in the image of `ρ`, and the values are a
sheaf. -/
public theorem derivation'_app_eq_zero_of_comp [Presheaf.IsLocallySurjective J ρ.hom]
    (D : M.val.Derivation' (ρ ≫ c).hom) (U : Cᵒᵖ) (b : S.obj.obj U) :
    D.d (c.hom.app U b) = 0 := by
  refine M.isSheaf.isSeparated U.unop (Presheaf.imageSieve ρ.hom b)
    (Presheaf.imageSieve_mem J ρ.hom b) _ _ ?_
  intro V k hk
  obtain ⟨a, ha⟩ := hk
  have key : (ρ ≫ c).hom.app (Opposite.op V) a = O.obj.map k.op (c.hom.app U b) := by
    have h1 : (ρ ≫ c).hom.app (Opposite.op V) a =
        c.hom.app (Opposite.op V) (ρ.hom.app (Opposite.op V) a) := rfl
    rw [h1, ha, sheafHom_naturality_apply]
  change M.val.map k.op (D.d (c.hom.app U b)) = M.val.map k.op 0
  rw [map_zero]
  exact (D.d_map k.op (c.hom.app U b)).symm.trans
    ((congrArg (fun z => D.d z) key.symm).trans (D.d_app a))

/-- The relative derivations for the base map `ρ ≫ c` and for the base map `c` are the same
family of additive maps, when `ρ` is locally surjective. -/
public noncomputable def derivation'CompEquiv [Presheaf.IsLocallySurjective J ρ.hom] :
    M.val.Derivation' (ρ ≫ c).hom ≃ M.val.Derivation' c.hom where
  toFun D :=
    { d := D.d
      d_mul := D.d_mul
      d_map := D.d_map
      d_app := fun {U} b => derivation'_app_eq_zero_of_comp ρ c M D U b }
  invFun D :=
    { d := D.d
      d_mul := D.d_mul
      d_map := D.d_map
      d_app := fun {U} a => D.d_app (ρ.hom.app U a) }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Relative derivations for two equal base maps. -/
public noncomputable def derivation'CongrBase {c₁ c₂ : S ⟶ O} (h : c₁ = c₂)
    (M : SheafOfModules.{w} (ringSheaf O)) :
    M.val.Derivation' c₁.hom ≃ M.val.Derivation' c₂.hom :=
  Equiv.cast (by rw [h])

end Base

/-! ### The derivations of a situation as relative derivations of the reduced structure sheaf -/

section Situation

-- `ringSheaf` unfolds to `sheafCompose`, whose action on objects is a structure
-- instance; without this, unification cannot see that the sections of the underlying sheaf of
-- rings are the sections of the sheaf of commutative rings. It is scoped to this section: made
-- file-wide it also unfolds inside the derived category of the sheaves of modules below, where
-- the resulting unification does not terminate.
attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The module a derivation of a situation takes its values in, read as a module over the
reduced structure sheaf of the source through the comparison `g`. -/
public noncomputable abbrev DerivationSituation.values (T : DerivationSituation J) :
    SheafOfModules.{w} (ringSheaf T.O) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map T.g)).obj T.G

/-- The reduction of the source thickening, as a morphism of the underlying sheaves of rings. -/
public noncomputable abbrev DerivationSituation.ringReduction (T : DerivationSituation J) :
    ringSheaf T.O' ⟶ ringSheaf T.O :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map T.reduction

/-- A locally surjective reduction of sheaves of commutative rings is locally surjective on the
underlying sheaves of rings: the two morphisms have the same components, hence the same image
sieves. -/
public instance DerivationSituation.isLocallySurjective_ringReduction (T : DerivationSituation J)
    [Presheaf.IsLocallySurjective J T.reduction.hom] :
    Sheaf.IsLocallySurjective T.ringReduction where
  imageSieve_mem {_U} y := Presheaf.imageSieve_mem J T.reduction.hom y

variable (T : DerivationSituation J)

/-- A derivation of a situation, read as section-wise derivation data through the reduction of
its source thickening: the Leibniz rule holds for the action of the reduced structure sheaf, and
the family vanishes on the sections killed by the reduction because those come from the ideal. -/
public noncomputable def Derivation.toQuotientDerivation
    (hker : ∀ (U : Cᵒᵖ) (a : T.O'.obj.obj U), T.reduction.hom.app U a = 0 →
      ∃ m : T.I.val.obj U, T.incl m = a)
    (δ : Derivation T) :
    Stacks.Sites.QuotientDerivation T.ringReduction T.values where
  d {U} := AddMonoidHom.mk' (δ.toFun U) (δ.map_add' U)
  d_mul {U} a b := δ.leibniz U a b
  d_map {_U _V} f x := δ.naturality f x
  d_eq_zero_of_app_eq_zero {U} a ha := by
    obtain ⟨m, hm⟩ := hker U a ha
    rw [← hm]
    exact δ.map_kernel U m

variable [Presheaf.IsLocallySurjective J T.reduction.hom] [HasSheafify J AddCommGrpCat.{w}]

omit [HasSheafify J AddCommGrpCat.{w}] in
/-- A relative derivation of the reduced structure sheaf is determined by its values on the
sections coming from the thickening, because those cover. -/
public theorem derivation'_ext_of_reduction
    (D E : T.values.val.Derivation' (T.f' ≫ T.reduction).hom)
    (h : ∀ (U : Cᵒᵖ) (x : T.O'.obj.obj U),
      D.d (T.reduction.hom.app U x) = E.d (T.reduction.hom.app U x)) : D = E := by
  ext U y
  refine T.values.isSheaf.isSeparated U.unop (Presheaf.imageSieve T.reduction.hom y)
    (Presheaf.imageSieve_mem J T.reduction.hom y) _ _ ?_
  intro V k hk
  obtain ⟨x, hx⟩ := hk
  change T.values.val.map k.op (D.d y) = T.values.val.map k.op (E.d y)
  refine (D.d_map k.op y).symm.trans (Eq.trans ?_ (E.d_map k.op y))
  exact (congrArg (fun z => D.d z) hx).symm.trans
    ((h _ x).trans (congrArg (fun z => E.d z) hx))

/-- The relative derivation of the reduced structure sheaf obtained by descending a derivation
of the situation along the locally surjective reduction of its source thickening. -/
public noncomputable def Derivation.descendDerivation
    (hker : ∀ (U : Cᵒᵖ) (a : T.O'.obj.obj U), T.reduction.hom.app U a = 0 →
      ∃ m : T.I.val.obj U, T.incl m = a)
    (δ : Derivation T) :
    T.values.val.Derivation' (T.f' ≫ T.reduction).hom where
  d := (δ.toQuotientDerivation T hker).descend
  d_mul := (δ.toQuotientDerivation T hker).descend_mul
  d_map := (δ.toQuotientDerivation T hker).descend_map
  d_app := fun {U} a =>
    ((δ.toQuotientDerivation T hker).descend_app (T.f'.hom.app U a)).trans (δ.map_base U a)

/-- The value of the descended derivation on a section coming from the thickening. -/
public theorem Derivation.descendDerivation_reduction
    (hker : ∀ (U : Cᵒᵖ) (a : T.O'.obj.obj U), T.reduction.hom.app U a = 0 →
      ∃ m : T.I.val.obj U, T.incl m = a)
    (δ : Derivation T) (U : Cᵒᵖ) (x : T.O'.obj.obj U) :
    (δ.descendDerivation T hker).d (T.reduction.hom.app U x) = δ.toFun U x :=
  (δ.toQuotientDerivation T hker).descend_app x

/-- A relative derivation of the reduced structure sheaf, precomposed with the reduction, is a
derivation of the situation. -/
public noncomputable def derivationOfDerivation'
    (hzero : ∀ (U : Cᵒᵖ) (m : T.I.val.obj U), T.reduction.hom.app U (T.incl m) = 0)
    (D : T.values.val.Derivation' (T.f' ≫ T.reduction).hom) : Derivation T where
  toFun U x := D.d (T.reduction.hom.app U x)
  map_add' U x y := by
    have key : D.d (T.reduction.hom.app U (x + y)) =
        D.d (T.reduction.hom.app U x) + D.d (T.reduction.hom.app U y) := by
      rw [map_add, map_add]
    exact key
  naturality {U V} h x := by
    rw [sheafHom_naturality_apply]
    exact D.d_map h _
  leibniz U x y := by
    rw [map_mul]
    exact D.d_mul _ _
  map_kernel U m := by
    have key : D.d (T.reduction.hom.app U (T.incl m)) = 0 := by
      rw [hzero U m, map_zero]
    exact key
  map_base U a := D.d_app a

/-- **The derivations of a situation are the relative derivations of its reduced structure sheaf
over its thickened base.** A derivation is given section-wise on the thickened structure sheaf
and kills the ideal, so it descends along the locally surjective reduction; conversely a
relative derivation of the reduced structure sheaf pulls back to one. -/
public noncomputable def derivationEquivDerivation'
    (hker : ∀ (U : Cᵒᵖ) (a : T.O'.obj.obj U), T.reduction.hom.app U a = 0 →
      ∃ m : T.I.val.obj U, T.incl m = a)
    (hzero : ∀ (U : Cᵒᵖ) (m : T.I.val.obj U), T.reduction.hom.app U (T.incl m) = 0) :
    Derivation T ≃ T.values.val.Derivation' (T.f' ≫ T.reduction).hom where
  toFun δ := δ.descendDerivation T hker
  invFun D := derivationOfDerivation' T hzero D
  left_inv δ :=
    Derivation.ext_apply fun U x => Derivation.descendDerivation_reduction T hker δ U x
  right_inv D :=
    derivation'_ext_of_reduction T _ D fun U x =>
      Derivation.descendDerivation_reduction T hker (derivationOfDerivation' T hzero D) U x

end Situation

/-! ### The universal property of the sheaf of relative differentials, as a bijection -/

section Differentials

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]

/-- **Stacks 04BL** as a bijection: the homomorphisms out of the sheaf of relative differentials
`Ω_{O₂/O₁}` with values in a sheaf of `O₂`-modules are exactly the relative derivations of `O₂`
over `O₁` with those values. -/
public noncomputable def differentialsOfSiteHomEquiv (O₁ O₂ : Sheaf J CommRingCat.{max w u v})
    (φ : O₁ ⟶ O₂) (G : SheafOfModules.{max w u v} (ringSheaf O₂)) :
    (moduleOfDifferentialsOfSite.{v, u, max w u v, w} O₁ O₂ φ ⟶ G) ≃ G.val.Derivation' φ.hom :=
  (derivationsFunctor.{w} O₁ O₂ φ).corepresentableBy.homEquiv

end Differentials

/-! ### The acting group of Stacks 08UG, and the bijection of Steps 2 and 3 -/

namespace LiftDiagram

section Values

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The module the derivations of a diagram take their values in: the ideal module `𝒢₂` of the
back square, read as a module over the reduced structure sheaf `O₁` of the front square through
the comparison `g`. This is `D.toSituation.values`, written over `D.front.O` rather than over
`D.toSituation.O`. -/
public noncomputable abbrev values (D : LiftDiagram J) :
    SheafOfModules.{w} (ringSheaf D.front.O) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map D.g)).obj D.back.G

/-- The values of the derivations of a diagram are the values of the derivations of its
situation. -/
public theorem toSituation_values (D : LiftDiagram J) :
    D.toSituation.values = D.values := rfl

end Values

section Acting

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max w u v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})]
  [HasSheafify J AddCommGrpCat.{max w u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  (D : LiftDiagram.{v, u, max w u v} J)

/-- **The first equality of the display of [Stacks Project, Tag 08UG].** The derivations of the
diagram — the group acting on the morphisms filling it — are the relative derivations of the
reduced structure sheaf `O₁` of the front square over its reduced base `O_{B₁}`, with values in
the ideal module `𝒢₂` of the back square through the comparison `g`. -/
public noncomputable def derivationEquivDifferentialsDerivation :
    Derivation D.toSituation ≃ D.values.val.Derivation' D.front.f.hom :=
  haveI : Presheaf.IsLocallySurjective J D.toSituation.reduction.hom :=
    D.front.locallySurjective
  haveI : Presheaf.IsLocallySurjective J D.front.baseReduction.hom :=
    D.front.baseLocallySurjective
  (derivationEquivDerivation' D.toSituation
      (fun _U a ha => D.front.exists_incl a ha) (fun _U m => D.front.reduction_incl m)).trans
    ((derivation'CongrBase D.front.comm D.values).trans
      (derivation'CompEquiv D.front.baseReduction D.front.f D.values))

variable (E : Functor Cᵒᵖ (Type (max w u v)))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J D.front.O)
  [Presheaf.IsLocallySurjective J
    (Stacks.SheafOfModules.presentation J D.front.OB D.front.O D.front.f E α).hom]

/-- **The identification of the two acting groups of [Stacks Project, Tag 08UG]**, which is the
input called `κ` by `Deformation.ToposThickening.LiftDiagram.liftEquivFactorization`. The
derivations of the diagram are the homomorphisms out of `H⁰(NL(α))`, for `α` a polynomial
presentation of the reduced structure sheaf `O₁` of the front square over its reduced base
`O_{B₁}`: they are the relative derivations of `O₁` over `O_{B₁}` with values in `g_*𝒢₂`, which
`Ω_{O₁/O_{B₁}}` corepresents, and that sheaf is the cokernel of the conormal map of the
presentation. -/
public noncomputable def derivationEquivCokernelHom :
    Derivation D.toSituation ≃
      (cokernel (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).f ⟶ D.values) :=
  D.derivationEquivDifferentialsDerivation.trans
    (((differentialsOfSiteHomEquiv D.front.OB D.front.O D.front.f D.values).symm).trans
      (Iso.homCongr (Stacks.SheafOfModules.presentationConormalCokernelIsoDifferentials.{v, u,
          max w u v, w} J D.front.OB D.front.O D.front.f E α) (Iso.refl _)).symm)

/-! ### The principal homogeneous space structure at the source's acting group -/

/-- Translating a morphism filling the source's diagram by a homomorphism out of `H⁰(NL(α))`:
the morphism is moved by the derivation of the diagram to which that homomorphism corresponds
under `LiftDiagram.derivationEquivCokernelHom`. -/
public noncomputable def cokernelHomTranslate
    (a : cokernel (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
      J D.front.OB D.front.O D.front.f E α).f ⟶ D.values) (p : D.Lift) : D.Lift :=
  translate p ((D.derivationEquivCokernelHom E α).symm a)

/-- **Clause (2) of [Stacks Project, Tag 08UG] at the source's own acting group.** The morphisms
`(Sh(C'₂), O'₂) ⟶ (Sh(C'₁), O'₁)` filling the source's diagram compatibly with `ν` form a
principal homogeneous space under
`Hom(H⁰(NL(α)), 𝒢₂) = Hom_{O₁}(Ω_{O₁/O_{B₁}}, g_*𝒢₂)`: any one of them is carried to any other
by exactly one homomorphism out of the degree `0` cohomology of the naive cotangent complex of
a polynomial presentation. -/
public theorem cokernelHomTranslate_existsUnique (p q : D.Lift) :
    ∃! a : cokernel (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
      J D.front.OB D.front.O D.front.f E α).f ⟶ D.values,
      D.cokernelHomTranslate E α a p = q := by
  obtain ⟨δ, hδ, huniq⟩ := translate_existsUnique p q
  refine ⟨D.derivationEquivCokernelHom E α δ, ?_, fun a ha => ?_⟩
  · change translate p ((D.derivationEquivCokernelHom E α).symm
      (D.derivationEquivCokernelHom E α δ)) = q
    rw [Equiv.symm_apply_apply]
    exact hδ
  · have h : (D.derivationEquivCokernelHom E α).symm a = δ := huniq _ ha
    rw [← h, Equiv.apply_symm_apply]

variable [HasDerivedCategory.{t}
  (SheafOfModules.{max w u v} (ringSheaf D.front.O))]

/-- The naive cotangent complex `NL(α)` of a polynomial presentation `α` of the reduced
structure sheaf of the front square over its reduced base, as a two-term complex in the derived
category of sheaves of `O₁`-modules: `ℐ/ℐ²` in degree `-1` and `Ω_{O_{B₁}[ℰ]/O_{B₁}} ⊗ O₁` in
degree `0`. -/
public noncomputable def presentationTwoTerm :
    AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm
      (DerivedCategory.singleFunctor
        (SheafOfModules.{max w u v} (ringSheaf D.front.O)) 0) :=
  AlgebraicGeometry.RingedSpaceThickening.NaiveCotangentTwoTerm.ofDoubleNegOne
    (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
      J D.front.OB D.front.O D.front.f E α).f

/-- The degree `-1` term of `NL(α)` is the conormal module `ℐ/ℐ²` of the presentation. -/
@[simp]
public theorem presentationTwoTerm_conormal :
    (D.presentationTwoTerm E α).conormal =
      (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).X₁ := rfl

/-- The degree `0` term of `NL(α)` is the middle term of the conormal sequence. -/
@[simp]
public theorem presentationTwoTerm_base :
    (D.presentationTwoTerm E α).base =
      (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).X₂ := rfl

/-- The differential of `NL(α)` is the conormal map of the presentation. -/
@[simp]
public theorem presentationTwoTerm_d :
    (D.presentationTwoTerm E α).d =
      (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).f := rfl

/-- The two spellings of the acting group of clause (2): the homomorphisms out of the cokernel
of the conormal map of the presentation are the homomorphisms out of the cokernel of the
differential of `NL(α)`, those two maps being the same map. -/
public theorem cokernelHom_eq :
    (cokernel (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).f ⟶ D.values) =
      (cokernel (D.presentationTwoTerm E α).d ⟶ D.values) := rfl

/-- **The identification of the two acting groups of [Stacks Project, Tag 08UG]**, read at the
differential of `NL(α)`: this is the input called `κ` by
`Deformation.ToposThickening.LiftDiagram.liftEquivFactorization`. -/
public noncomputable def derivationEquivTwoTermCokernelHom :
    Derivation D.toSituation ≃ (cokernel (D.presentationTwoTerm E α).d ⟶ D.values) :=
  (D.derivationEquivCokernelHom E α).trans (Equiv.cast (D.cokernelHom_eq E α))

/-- **Steps 2 and 3 of the proof of [Stacks Project, Tag 08UG].** The morphisms
`(Sh(C'₂), O'₂) ⟶ (Sh(C'₁), O'₁)` filling the source's diagram compatibly with `ν` are in
bijection with the factorizations of a homomorphism `ξ : ℐ/ℐ² ⟶ 𝒢₂` out of the conormal module
of a polynomial presentation through the degree `0` term of `NL(α)`. Both sides are principal
homogeneous spaces — the first under the derivations of the diagram, by
`LiftDiagram.translate_existsUnique`, the second under `Hom(H⁰(NL(α)), 𝒢₂)`, by
`factorizationEquivCokernelHom` — and the two acting groups are identified by
`LiftDiagram.derivationEquivCokernelHom`; the two base points trivialize them.

The conormal module and the degree `0` term are named by the conormal sequence of the
presentation rather than by `NL(α)`, which is the same pair of sheaves of modules
(`presentationTwoTerm_conormal` and `presentationTwoTerm_base`). -/
public noncomputable def liftEquivFactorizationOfPresentation
    (ξ : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
      J D.front.OB D.front.O D.front.f E α).X₁ ⟶ D.values) (p : D.Lift)
    (θ₀ : {θ : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).X₂ ⟶ D.values //
      (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).f ≫ θ = ξ}) :
    D.Lift ≃ {θ : (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).X₂ ⟶ D.values //
      (Stacks.SheafOfModules.presentationConormalSequence.{v, u, max w u v, w}
        J D.front.OB D.front.O D.front.f E α).f ≫ θ = ξ} :=
  D.liftEquivFactorization (D.presentationTwoTerm E α) D.values ξ p θ₀
    (D.derivationEquivTwoTermCokernelHom E α)

end Acting

end LiftDiagram

end Deformation.ToposThickening

end
