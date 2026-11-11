module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.CupProductOnCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.BoundaryChernComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.Defs
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksCore.Tactic.StacksAttribute

/-!
# Cup product by the class of a divisor kills classes that vanish on it

Let `X → S` be a morphism of schemes, let `Y ⊆ X` be an effective Cartier divisor and assume the
de Rham complex of log poles is defined for `Y ⊆ X` over `S`. **Tag 0FMX** says that for a
relative de Rham cohomology class `b ∈ H^m_{dR}(X/S)` whose restriction to `Y` is zero

`c₁^{dR}(𝒪_X(Y)) ∪ b = 0`

in `H^{m + 2}_{dR}(X/S)`. The source deduces it from Tag 0FUQ in one line: writing
`ξ = c₁^{dR}(𝒪_X(-Y))` and `ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` for the morphism Tag 0FU7 attaches to
it, and `δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` for the boundary map of the log poles sequence of Tag
0FMW,

`c₁^{dR}(𝒪_X(Y)) ∪ b = -c₁^{dR}(𝒪_X(-Y)) ∪ b = -ξ'(b) = -δ(b|_Y) = 0`.

The first equality is the additivity of `c₁^{dR}` on the Picard group, `𝒪_X(Y)` being the inverse
of `𝒪_X(-Y)`; the second is Remark 0FU7, property (3); the third is the upper left triangle of
Tag 0FUQ, which factors `ξ'` through `δ` along the restriction of relative forms; and the last is
the hypothesis `b|_Y = 0`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.derivedHypercohomology` and
  `AlgebraicGeometry.SheafOfModules.derivedHypercohomologyMap`: hypercohomology of an object of
  the derived category of sheaves of `A`-modules, and the map a morphism of that category induces
  on it. Relative de Rham cohomology is the first of these at the de Rham complex, and the
  restriction of a de Rham class to the divisor is the second at the restriction of relative
  forms.
* `AlgebraicGeometry.SheafOfModules.DeRhamClassCupAction`: **the parameter**, Remark 0FU7,
  property (3): the morphism `ξ'` attached to a de Rham class `ξ` acts on `H^m_{dR}` as cup
  product by `ξ`.
* `AlgebraicGeometry.Scheme.Hom.LogPolesDivisorData`: the hypotheses of Tag 0FMX on the divisor —
  that it is an effective Cartier divisor and that the de Rham complex of log poles is defined
  for it — together with the global-form sequences of Tag 0FUQ that the source builds from them.

## Main results

* `AlgebraicGeometry.SheafOfModules.derivedHypercohomologyMap_comp`: the map induced on
  hypercohomology is functorial. This is what turns `ξ' = δ ∘ (restriction of forms)` into
  `ξ'(b) = δ(b|_Y)`.
* `AlgebraicGeometry.SheafOfModules.deRhamCupProduct_neg_left`: cup product on `H^*_{dR}` is
  compatible with negation in its first variable, the first equality of the proof.
* `AlgebraicGeometry.SheafOfModules.cup_deRhamFirstChernClass_eq_zero_of_restriction_eq_zero`:
  the chain of Tag 0FMX for the relative de Rham complex of a morphism of sheaves of rings on a
  ringed space, with the inputs listed below as parameters.
* `AlgebraicGeometry.Scheme.Hom.cup_deRhamFirstChernClass_eq_zero`: the same chain for a
  morphism of schemes, with the same parameters.

The complete statement of Tag 0FMX, with no parameter beyond the source's hypotheses, is
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyCup_firstChernClass_eq_zero` in
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.CupFirstChernClassVanishing`, which carries the
Stacks attribution; the two results here are not registered.

## Implementation notes

**The source's own hypotheses.** Both hypotheses that Tag 0FMX states — that `Y ⊆ X` is an
effective Cartier divisor, Tag 01WR, and that the de Rham complex of log poles is defined for
`Y ⊆ X` over `S`, Tag 0FMV — are fields of
`AlgebraicGeometry.Scheme.Hom.LogPolesDivisorData`, for the morphism of schemes and the ideal
sheaf the statement is about. They are fields rather than separate binders so that they stand
alongside, and are visibly about the same divisor as, the third field, which is what the source
produces from them.

**What is carried, and why.** The third field of
`AlgebraicGeometry.Scheme.Hom.LogPolesDivisorData` is
`AlgebraicGeometry.SheafOfModules.LogPolesResidueData`, the input of Tag 0FUQ: the log poles
sequence of Tag 0FMW and the two residue sequences of Tag 0FUF in global, shifted form, together
with the two morphisms between them. The library has none of these globally — see the
implementation notes of `StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.BoundaryChernComparison`,
where they are carried for the same reason — so the passage from the two hypotheses above to the
sequences is not available, and the sequences are data. Four further inputs are carried as
binders, exactly as the library's Tag 0FUQ carries them: the cup product on hypercohomology of
Cohomology, Section 0FKU
(`AlgebraicGeometry.SheafOfModules.HypercohomologyCupProduct`), an identification of
Differential Graded Sheaves, Section 0FU3
(`AlgebraicGeometry.SheafOfModules.DeRhamDerivedModuleCorrespondence`, whose canonical term is
`AlgebraicGeometry.SheafOfModules.deRhamDerivedModuleCorrespondence`), the comparison
`realizationComparison` of the two realizations of de Rham cohomology, and the two clauses
`hlift` and `hev` of Tag 0FUG.

**Remark 0FU7, property (3) is a parameter here.** The morphism `ξ'` of this file is the one
attached through an arbitrary identification `cc` of Section 0FU3
(`AlgebraicGeometry.SheafOfModules.deRhamClassDerivedMorphism`), and its action on
`derivedHypercohomology`, so property (3), that `ξ'` sends `η ∈ H^m_{dR}` to `ξ ∪ η`, is the
parameter `AlgebraicGeometry.SheafOfModules.DeRhamClassCupAction`. Its second field is property
(3) itself; its first is the identification `H^m(X, Ω^•_{X/S}[n]) = H^{n + m}_{dR}(X/S)` without
which property (3) cannot be stated, since `ξ'` induces a map to the hypercohomology of a
translate. The library proves property (3) for the canonical morphism
`AlgebraicGeometry.SheafOfModules.deRhamClassMorphism`, read through derived global sections
`derivedSectionsBase` and the identification
`AlgebraicGeometry.SheafOfModules.deRhamShiftHomologyIso`
(`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism`); this file is
stated in the realization `derivedHypercohomology`, and the comparison of the two is not made
here.

**What is proved.** The chain of the source. The third equality is the library's Tag 0FUQ,
`AlgebraicGeometry.SheafOfModules.LogPolesResidueData.deRhamClassDerivedMorphism_eq`, turned from
an equality of morphisms into an equality of maps on `H^m` by the functoriality of
`AlgebraicGeometry.SheafOfModules.derivedHypercohomologyMap`; the first is the additivity of
`c₁^{dR}`, which the library's Tag 0FLE already provides, `c₁^{dR}` being a homomorphism out of
the Picard group, together with the additivity of the cup product in its first variable; and the
vanishing is then the hypothesis on `b`.

**`𝒪_X(Y)` enters through its Picard class.** The de Rham first Chern class of Tag 0FLE is a
homomorphism on `Pic(X)`, so `c₁^{dR}(𝒪_X(Y))` is determined by the class of `𝒪_X(Y)` in
`Pic(X)`, which is by definition the inverse of the class of the ideal sheaf `𝒪_X(-Y)`. That is
how `𝒪_X(Y)` appears below: as a Picard class `ℓ` whose sum with the class of `L = 𝒪_X(-Y)` is
zero. No construction of the invertible module `𝒪_X(Y)` is needed, and none is in the library.

**The degree of the conclusion.** The cup product of a class of degree `2` with a class of degree
`m` lands in `H^{2 + m}_{dR}(X/S)`, which is the `H^{m + 2}_{dR}(X/S)` of the source.

## References

* [Stacks Project, Tag 0FMX](https://stacks.math.columbia.edu/tag/0FMX)
* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FUG](https://stacks.math.columbia.edu/tag/0FUG)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### Hypercohomology of an object of the derived category -/

/-- **Hypercohomology in degree `m`** of an object `Z` of the derived category of sheaves of
`A`-modules: the `m`-th cohomology of its derived global sections. Relative de Rham cohomology
`H^m_{dR}` is this at the relative de Rham complex. -/
@[ega "0 12.4.2", ega "III 6.2.1"]
abbrev derivedHypercohomology
    (Z : DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A))) (m : ℤ) :
    ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤)) :=
  (DerivedCategory.homologyFunctor _ m).obj ((derivedSectionsBase A).obj Z)

/-- **The map on hypercohomology induced by a morphism `g : Z ⟶ W` of the derived category** of
sheaves of `A`-modules: the map derived global sections and the `m`-th cohomology functor send it
to. -/
abbrev derivedHypercohomologyMap
    {Z W : DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A))} (g : Z ⟶ W)
    (m : ℤ) :
    derivedHypercohomology Z m ⟶ derivedHypercohomology W m :=
  (DerivedCategory.homologyFunctor _ m).map ((derivedSectionsBase A).map g)

/-- Relative de Rham cohomology is the hypercohomology of the relative de Rham complex. -/
theorem derivedHypercohomology_deRhamDerivedObject (m : ℤ) :
    derivedHypercohomology (deRhamDerivedObject B D) m = deRhamCohomology B D m := rfl

/-- **The map induced on hypercohomology is functorial.** This is what turns an equality of
morphisms of the derived category into an equality of the maps they induce on `H^m`. -/
theorem derivedHypercohomologyMap_comp
    {Z W V : DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A))}
    (g : Z ⟶ W) (h : W ⟶ V) (m : ℤ) :
    derivedHypercohomologyMap (g ≫ h) m =
      derivedHypercohomologyMap g m ≫ derivedHypercohomologyMap h m := by
  simp only [derivedHypercohomologyMap, Functor.map_comp]

/-! ### Cup product as the action of the morphism attached to a class -/

/-- **Remark 0FU7, property (3), as a hypothesis.**

A term of this structure provides, in every pair of degrees, the identification

`H^m(X, Ω^•_{X/S}[n]) = H^{n + m}_{dR}(X/S)`

of the hypercohomology of a translate of the relative de Rham complex with de Rham cohomology in
the shifted degree, together with property (3) of Remark 0FU7: the morphism
`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` which Tag 0FU7 attaches to a de Rham class `ξ ∈ H^n_{dR}(X/S)`
sends `η ∈ H^m_{dR}(X/S)` to `ξ ∪ η`.

This is the one parameter of this file beyond those the library's Tag 0FUQ already takes. The
library proves property (3) for the canonical morphism
(`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism`), in the
realization `derivedSectionsBase` of derived global sections; this structure states it for the
morphism attached through `cc`, in the realization `derivedHypercohomology`. -/
structure DeRhamClassCupAction (cp : HypercohomologyCupProduct B D)
    (cc : DeRhamDerivedModuleCorrespondence B D) where
  /-- The identification `H^m(X, Ω^•_{X/S}[n]) = H^{n + m}_{dR}(X/S)`. -/
  shiftComparison (n m : ℤ) :
    derivedHypercohomology ((deRhamDerivedObject B D)⟦n⟧) m ⟶ deRhamCohomology B D (n + m)
  /-- Remark 0FU7, property (3): the morphism attached to `ξ` acts on `H^m_{dR}` as cup product
  by `ξ`. -/
  cup_eq (n m : ℤ) (ξ : deRhamCohomology B D n) (η : deRhamCohomology B D m) :
    deRhamCupProduct B D cp n m ξ η =
      (shiftComparison n m).hom
        ((derivedHypercohomologyMap (deRhamClassDerivedMorphism B D cc n ξ) m).hom η)

/-! ### Negation in the first variable of the cup product -/

/-- Cup product by the zero class of `H^i_{dR}(X/S)` is zero. -/
theorem deRhamCupProduct_zero_left (cp : HypercohomologyCupProduct B D) (i j : ℤ)
    (η : deRhamCohomology B D j) : deRhamCupProduct B D cp i j 0 η = 0 := by
  have h := deRhamCupProduct_add_left B D cp i j 0 0 η
  rw [add_zero] at h
  have h' : deRhamCupProduct B D cp i j 0 η + deRhamCupProduct B D cp i j 0 η =
      0 + deRhamCupProduct B D cp i j 0 η := by rw [zero_add]; exact h.symm
  exact add_right_cancel h'

/-- **Cup product on `H^*_{dR}(X/S)` is compatible with negation in its first variable**,
`(-ξ) ∪ η = -(ξ ∪ η)`: it is additive there. -/
theorem deRhamCupProduct_neg_left (cp : HypercohomologyCupProduct B D) (i j : ℤ)
    (ξ : deRhamCohomology B D i) (η : deRhamCohomology B D j) :
    deRhamCupProduct B D cp i j (-ξ) η = -deRhamCupProduct B D cp i j ξ η := by
  have h := deRhamCupProduct_add_left B D cp i j (-ξ) ξ η
  rw [neg_add_cancel, deRhamCupProduct_zero_left] at h
  exact add_eq_zero_iff_eq_neg.mp h.symm

/-! ### Tag 0FMX for the de Rham complex of a ringed space -/

section Chern

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The abelian group structure on the Picard group of a ringed space. It is
`Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup`, named here for the same reason as in
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass`: instance search
does not find that instance through the universe constraints of a ringed space. -/
local instance logPolesPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.sheaf.obj
    (structureSheaf X.sheaf).property

/-- **The chain of Tag 0FMX, with its inputs as parameters**, for the relative de Rham complex of a
morphism `φ : A ⟶ 𝒪_X` of sheaves of commutative rings on a ringed space. The complete statement
of Tag 0FMX, with none of these parameters, is
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyCup_firstChernClass_eq_zero`.

`c₁^{dR}(𝒪_X(Y)) ∪ b = 0`

in `H^{2 + m}_{dR}`: a relative de Rham cohomology class `b ∈ H^m_{dR}` whose restriction to the
divisor is zero is killed by cup product with the de Rham first Chern class of `𝒪_X(Y)`. The
divisor enters through the invertible module `L = 𝒪_X(-Y)` and through the Picard class `ℓ` of
`𝒪_X(Y)`, which is the inverse of that of `L`; the restriction of `b` is the map that the
restriction of relative forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}` induces on `H^m`, the de Rham complex of
the divisor being read on the ambient space as in Section 50.15 of the source.

The proof is the chain of the source: `c₁^{dR}(𝒪_X(Y)) = -c₁^{dR}(L)` by additivity of the first
Chern class, `c₁^{dR}(L) ∪ b = ξ'(b)` by Remark 0FU7, property (3), `ξ' = δ ∘ (restriction of
forms)` by the upper left triangle of Tag 0FUQ, and `δ(b|_Y) = 0` because `b|_Y = 0`.

Carried as explicit named hypotheses are the sequences of Tag 0FUQ, `d`; the cup product of
Cohomology, Section 0FKU, `cp`; the identification of Differential Graded Sheaves, Section 0FU3,
`cc`; property (3) of Remark 0FU7, `act`; the comparison `realizationComparison` of the two
realizations of de Rham cohomology; and the two clauses `hlift` and `hev` of Tag 0FUG. -/
theorem cup_deRhamFirstChernClass_eq_zero_of_restriction_eq_zero (d : LogPolesResidueData B D)
    (cp : HypercohomologyCupProduct B D) (cc : DeRhamDerivedModuleCorrespondence B D)
    (act : DeRhamClassCupAction B D cp cc)
    (realizationComparison : deRhamCohomologyAbelian B D 2 →+ deRhamCohomology B D 2)
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hlift : ∃ g : deRhamDerivedRegular B D ⟶ deRhamDerivedRegularShift B D 2,
      cc.forget 2 g = d.ambientChernBoundary)
    (hev : cc.evalOne 2 d.ambientChernBoundary =
      realizationComparison (deRhamFirstChernClassAbelianOf B D L hL))
    (ℓ : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property)
    (hℓ : ℓ + Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
      (structureSheaf X.sheaf).property L hL = 0)
    (m : ℤ) (b : deRhamCohomology B D m)
    (hb : (derivedHypercohomologyMap (DerivedCategory.Q.map d.restriction) m).hom b = 0) :
    deRhamCupProduct B D cp 2 m
      (realizationComparison (deRhamFirstChernClassAbelian B D ℓ)) b = 0 := by
  have hxi : deRhamCupProduct B D cp 2 m
      (realizationComparison (deRhamFirstChernClassAbelianOf B D L hL)) b = 0 := by
    rw [act.cup_eq 2 m _ b,
      d.deRhamClassDerivedMorphism_eq cc realizationComparison L hL hlift hev,
      derivedHypercohomologyMap_comp]
    simp [hb]
  have hneg : realizationComparison (deRhamFirstChernClassAbelian B D ℓ) =
      -realizationComparison (deRhamFirstChernClassAbelianOf B D L hL) := by
    rw [add_eq_zero_iff_eq_neg.mp hℓ, map_neg, map_neg]
  rw [hneg, deRhamCupProduct_neg_left, hxi, neg_zero]

end Chern

end AlgebraicGeometry.SheafOfModules

/-! ### Tag 0FMX for a morphism of schemes -/

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

/-- The abelian group structure on the Picard group of a scheme, for the same reason as
`AlgebraicGeometry.SheafOfModules.logPolesPicardGroupAddCommGroup`. -/
local instance logPolesSchemePicardGroupAddCommGroup {Z : Scheme.{u}} :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup Z.sheaf.obj
      (structureSheaf Z.sheaf).property) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup Z.sheaf.obj
    (structureSheaf Z.sheaf).property

variable {X S : Scheme.{u}}

/-- **The hypotheses of Stacks Project, Tag 0FMX on the divisor**, for a morphism of schemes
`p : X ⟶ S` and a closed subscheme `Y ⊆ X` recorded by its ideal sheaf `I`: that `Y` is an
effective Cartier divisor and that the de Rham complex of log poles is defined for `Y ⊆ X` over
`S`, together with the sequences of Tag 0FUQ that the source builds from them.

The third field is what the library cannot produce from the first two: the log poles sequence of
Tag 0FMW and the two residue sequences of Tag 0FUF in global, shifted form, with the two
morphisms between them. See the implementation notes of this module and of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.BoundaryChernComparison`. -/
structure LogPolesDivisorData (p : X ⟶ S) (I : X.IdealSheafData) where
  /-- Stacks Tag 01WR: `Y` is an effective Cartier divisor on `X`. -/
  isEffectiveCartierDivisor : Stacks.Divisors.IsEffectiveCartierDivisor I
  /-- Stacks Tag 0FMV: the de Rham complex of log poles is defined for `Y ⊆ X` over `S`. -/
  hasLogPolesDeRhamComplex : HasLogPolesDeRhamComplex p I
  /-- The three short exact sequences of Tag 0FUQ in global form, with the two morphisms between
  them: the log poles sequence of Tag 0FMW for `Y ⊆ X` and the residue sequences of Tag 0FUF for
  `𝒪_X(-Y)` and for its restriction to `Y`. -/
  residueData : SheafOfModules.LogPolesResidueData (deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (deRhamAlgebras p))

/-- **The chain of Tag 0FMX for a morphism of schemes, with its inputs as parameters.** The
complete statement of Tag 0FMX, with none of the parameters below, is
`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyCup_firstChernClass_eq_zero`.

Let `p : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an
effective Cartier divisor for which the de Rham complex of log poles is defined over `S`. If the
restriction to `Y` of a relative de Rham cohomology class `b ∈ H^m_{dR}(X/S)` is zero, then

`c₁^{dR}(𝒪_X(Y)) ∪ b = 0`

in `H^{2 + m}_{dR}(X/S)`. Here `𝒪_X(Y)` enters through its class `ℓ` in `Pic(X)`, the inverse of
the class of `L = 𝒪_X(-Y)`, and the restriction of `b` is the map induced on `H^m` by the
restriction of relative forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`.

The two hypotheses the source states on the divisor are the first two fields of `h`. Carried as
explicit named hypotheses are the sequences of Tag 0FUQ, the third field of `h`; the cup product
of Cohomology, Section 0FKU, `cp`; the identification of Differential Graded Sheaves, Section
0FU3, `cc`; property (3) of Remark 0FU7, `act`; the comparison `realizationComparison` of the two
realizations of de Rham cohomology; and the two clauses `hlift` and `hev` of Tag 0FUG. -/
theorem cup_deRhamFirstChernClass_eq_zero {p : X ⟶ S} {I : X.IdealSheafData}
    (h : LogPolesDivisorData p I)
    (cp : SheafOfModules.HypercohomologyCupProduct (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
    (cc : SheafOfModules.DeRhamDerivedModuleCorrespondence (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
    (act : SheafOfModules.DeRhamClassCupAction (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) cp cc)
    (realizationComparison :
      SheafOfModules.deRhamCohomologyAbelian (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 2 →+
        SheafOfModules.deRhamCohomology (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 2)
    (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hlift : ∃ g : SheafOfModules.deRhamDerivedRegular (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ⟶
        SheafOfModules.deRhamDerivedRegularShift (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) 2,
      cc.forget 2 g = h.residueData.ambientChernBoundary)
    (hev : cc.evalOne 2 h.residueData.ambientChernBoundary =
      realizationComparison (SheafOfModules.deRhamFirstChernClassAbelianOf (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) L hL))
    (ℓ : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property)
    (hℓ : ℓ + Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
      (structureSheaf X.sheaf).property L hL = 0)
    (m : ℤ)
    (b : SheafOfModules.deRhamCohomology (deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) m)
    (hb : (SheafOfModules.derivedHypercohomologyMap
      (DerivedCategory.Q.map h.residueData.restriction) m).hom b = 0) :
    SheafOfModules.deRhamCupProduct (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) cp 2 m
        (realizationComparison (SheafOfModules.deRhamFirstChernClassAbelian (deRhamAlgebras p)
          (SheafOfModules.deRhamDifferential (deRhamAlgebras p)) ℓ)) b = 0 :=
  SheafOfModules.cup_deRhamFirstChernClass_eq_zero_of_restriction_eq_zero _ _ h.residueData cp cc
    act realizationComparison L hL hlift hev ℓ hℓ m b hb

end AlgebraicGeometry.Scheme.Hom

end
