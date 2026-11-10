module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftGroup
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftTorsor
public import StacksFrontier.Deformation.LiftTorsorFactorization

/-!
# The bijection of Steps 1 to 3 of Stacks 08U8 for a deformation of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, let `X'` and `Y'` be deformations of
`X` and of `Y` over one object `A` of `𝒞_Λ`, and suppose `f` lifts to a morphism `F : X' ⟶ Y'`
over `baseSpec A`. `Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts`
makes the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the exact sequence of [Stacks Project, Tag 0E3V]
act simply transitively on the morphisms `X' ⟶ Y'` over the base that restrict to `f`.

This file feeds that torsor structure into
`AlgebraicGeometry.RingedSpaceThickening.liftEquivFactorizationOfAct` and so produces, for the
morphism-deformation situation, the equivalence `e` that
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff` — clause (1) of
[Stacks Project, Tag 08U8] — and its clause (2) carry as a hypothesis: a bijection between the
lifts of `f` and the factorizations `{θ : P.base ⟶ G // P.d ≫ θ = ξ}` of the difference
homomorphism through the degree `0` term of a two-term naive cotangent complex.

**One input is carried**: the identification `κ` of the two acting groups,
`Der_k(𝒪_Y, f_*𝒪_X) ≃ Hom(H⁰(NL), 𝒢)`. It is exactly what the tag docstrings of
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentLiftingObstruction.lean` say
**Stacks 08U8** as formalized does not prove — "its further identification with
`Hom(g^*Ω_{X₁/S₁}, 𝒢₂)` and with `Ext⁰(Lg^*NL_{X₁/S₁}, 𝒢₂)` is not proved here". It stays a
parameter here, as `P`, `G` and `ξ` do; it is constructed, for this situation, by
`Deformation.Examples.schemeMorphismDerivationsEquivCokernelHom` in
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftCokernelHom.lean`, which imports
this file.

## Main results

* `Deformation.Examples.nonempty_schemeMorphismLiftEquivCokernelHom`: **the lifts of `f` between
  two deformations are the homomorphisms out of `H⁰(NL)`**, on the identification `κ` of the
  acting groups. This needs no factorization of `ξ`, only the given lift `F`, and it is the
  source's own description of the acting group of clause (2) of [Stacks Project, Tag 08U8].
* `Deformation.Examples.nonempty_schemeMorphismLiftEquivFactorization`: **the equivalence `e` of
  Steps 1 to 3 of [Stacks Project, Tag 08U8] for the lifts of `f` between two deformations**, on
  the identification `κ` of the acting groups.
* `Deformation.Examples.exists_simplyTransitive_cokernelHom_schemeMorphismLifts`:
  **[Stacks Project, Tag 08U8], clause (2), for the lifts of a morphism of schemes.** The
  homomorphisms out of `H⁰(NL)` act simply transitively on those lifts. This is what the
  equivalence buys with content; see the implementation notes for what it does not buy.

## Implementation notes

The two-term structure `P`, the coefficient module `G` and the difference homomorphism `ξ` are
parameters, as they are at every call site of **Stacks 08U8** in the library
(`StacksFrontier/Deformation/RingedSpaceThickening/DerivedExtensionClassCriterion.lean` and
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassComparison.lean` both carry their
own `δ` and `e`). Keeping them general is what
makes the single real input visible: `κ`. For the sequence of [Stacks Project, Tag 0E3V] the
intended instance is
`P = AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentTwoTerm` on
`Lf^*𝖭𝖫_{Y/k}` and `G = 𝒪_X`, so that `P.conormalExtClass G ξ` lies in the sixth term
`Ext¹_{𝒪_X}(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)` built by
`Deformation.Examples.schemeMorphismObstructionExt`; at that instance `P.d` is
`AlgebraicGeometry.RingedSpaceThickening.pulledConormalMap`, and `κ` would be the composite

`Der_k(𝒪_Y, f_*𝒪_X) ≃ Hom_{𝒪_X}(f^*Ω_{Y/k}, 𝒪_X) ≃ Hom(Coker(f^*(𝒥/𝒥² ⟶ Ω)), 𝒪_X)`

whose first factor is `Deformation.Examples.schemeMorphismLiftHomLinearEquiv`. The second factor
is an identification `Coker(pulledConormalMap) ≅ f^*Ω_{Y/k}`, which is
`AlgebraicGeometry.RingedSpaceThickening.pulledCokernelConormalIsoPullbackCotangent`:
`twoStepPullbackCokernelConormalIso` carries the cokernel of the conormal map across `f^*`,
`AlgebraicGeometry.RingedSpace.naiveCotangentCokernelIsoDifferentials` is **Stacks 08TY** in
degree `0` for the cokernel before pulling back, and
`AlgebraicGeometry.SheafOfModules.relativeDifferentialsIsoSectionwise` together with
`AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` put the result at the
spelling of `f^*Ω_{Y/k}` that `Deformation.Examples.schemeMorphismPullbackCotangent` — equal by
`rfl` to `Stacks.Smooth.pullbackCotangentSheaf`, the sheaf the acting group of
[Stacks Project, Tag 0CK2] is read out of — is written in. The composite is
`Deformation.Examples.schemeMorphismDerivationsEquivCokernelHom`.

**What the equivalence does and does not carry.** Both base points of
`AlgebraicGeometry.RingedSpaceThickening.liftEquivFactorizationOfAct` are present here: the lift
is `F`, through `Deformation.Examples.liftsOverBaseTopEquiv`, and the factorization `θ₀` is a
parameter. So clause (1) of **Stacks 08U8** is discharged only vacuously at this instance — with
`F` and `θ₀` both in hand, both sides of its biconditional already hold. Clause (2) is
discharged with content, and that content is not a restatement of
`exists_simplyTransitive_addAction_schemeMorphismLifts`: the acting group there is the
*derivations*, and here it is the homomorphisms out of `H⁰(NL)`, the group the source identifies
with `Ext⁰(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)`.

A non-vacuous clause (1) — the obstruction arrow of [Stacks Project, Tag 0E3V], which is what
would let the `@[stacks 0E3V "PARTIAL. …"]` marker of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismEndpoints.lean` be strengthened —
needs `ξ` constructed from the pair of deformations rather than given, and needs the bijection
built canonically rather than from base points. The library does construct a Step 1 difference
homomorphism, `AlgebraicGeometry.RingedSpaceThickening.PresentedSquareZeroExtension.obstruction`
in `StacksFrontier/Deformation/RingedSpaceThickening/ExtensionPresentationClass.lean`, out of the
sheaf of polynomial algebras `Stacks.SheafOfModules.freeAlgebraSheaf` and the ideal of a
presentation; but it is built for a *pair of square-zero extensions of one structure sheaf*, not
for a pair of deformations of the two endpoints of a morphism, and nothing connects it to the
lifts of `f`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Thickenings (immersionConormalSheaf liftsOverBase)

universe v₂ u₂ v₃ u₃ u

namespace Deformation.Examples

attribute [local instance] residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

section Factorization

variable {A : ArtinianLocalAlgCat.{u, u, u} Λ k} {X' Y' : Scheme.{u}}
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (hf : f ≫ pY = pX)
  {i : X ⟶ X'} {j : Y ⟶ Y'} [IsClosedImmersion i] [IsImmersion j]
  {pX' : X' ⟶ baseSpec A} {pY' : Y' ⟶ baseSpec A}
  (hX : IsPullback i pX pX' (residueSpecMap A))
  (hY : IsPullback j pY pY' (residueSpecMap A))
  (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥)
  {F : X' ⟶ Y'} (hF₁ : F ≫ pY' = pX') (hF₂ : i ≫ F = f ≫ j)
  (ε : immersionConormalSheaf i ≅ SheafOfModules.unit (structureSheafRing X.toRingedSpace))

variable {M : Type u₂} [Category.{v₂} M] [Abelian M] {T : Type u₃} [Category.{v₃} T]
  [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] {single : M ⥤ T}

variable (P : NaiveCotangentTwoTerm single) (G : M) (ξ : P.conormal ⟶ G)
  (κ : schemeMorphismDerivations f pY ≃ (cokernel P.d ⟶ G))
  (θ₀ : {θ : P.base ⟶ G // P.d ≫ θ = ξ})

include pX hf hX hY hA hF₁ hF₂ ε κ in
/-- **The lifts of a morphism of schemes are the homomorphisms out of `H⁰(NL)`.** Let
`f : X ⟶ Y` be a morphism of schemes over `k`, let `X'` and `Y'` be deformations of `X` and of
`Y` over one object `A` of `𝒞_Λ` whose maximal ideal has square zero, let `i : X ⟶ X'` be the
special-fibre immersion with its conormal sheaf identified with `𝒪_X` by `ε`, and suppose `f`
lifts to `F : X' ⟶ Y'` over `baseSpec A`. Then, given an identification `κ` of the third term
`Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V] with the homomorphisms out
of `H⁰(NL)`, the morphisms `X' ⟶ Y'` over the base that restrict to `f` are in bijection with
those homomorphisms.

This is the source's own description of the set of lifts in clause (2) of
[Stacks Project, Tag 08U8] — the identification of the acting group with
`Hom(H⁰(NL(α)), 𝒢) = Ext⁰(Lg^*NL_{X₁/S₁}, 𝒢₂)` that the tag docstrings of
`AlgebraicGeometry.RingedSpaceThickening.existsUnique_liftTranslate` say is not proved there —
and it needs no factorization of `ξ`: the lift `F` is the only base point used. It is the
statement from which
`Deformation.Examples.nonempty_schemeMorphismLiftEquivFactorization` follows by composing with
`Deformation.ToposThickening.factorizationEquivCokernelHom`. -/
theorem nonempty_schemeMorphismLiftEquivCokernelHom :
    Nonempty (liftsOverBase i j pX' pY' f ⊤ ≃ (cokernel P.d ⟶ G)) := by
  obtain ⟨act, -, -, htrans⟩ :=
    exists_simplyTransitive_addAction_schemeMorphismLifts f pY pX hf hX hY hA hF₁ hF₂ ε
  exact ⟨(equivOfExistsUniqueAct act htrans
    ((liftsOverBaseTopEquiv i j pX' pY' f).symm ⟨F, hF₁, hF₂⟩)).trans κ⟩

include pX hf hX hY hA hF₁ hF₂ ε ξ κ θ₀ in
/-- **The equivalence `e` of Steps 1 to 3 of [Stacks Project, Tag 08U8] for the lifts of a
morphism of schemes.** Let `f : X ⟶ Y` be a morphism of schemes over `k`, let `X'` and `Y'` be
deformations of `X` and of `Y` over one object `A` of `𝒞_Λ` whose maximal ideal has square zero,
let `i : X ⟶ X'` be the special-fibre immersion with its conormal sheaf identified with `𝒪_X`
by `ε`, and suppose `f` lifts to `F : X' ⟶ Y'` over `baseSpec A`. Then, given an identification
`κ` of the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V] with
the homomorphisms out of `H⁰(NL)`, and a factorization `θ₀` of `ξ` through the degree `0` term,
the morphisms `X' ⟶ Y'` over the base that restrict to `f` are in bijection with the
factorizations of `ξ`.

This is the hypothesis `e` of
`AlgebraicGeometry.RingedSpaceThickening.liftingObstruction_eq_zero_iff`, supplied for the
morphism-deformation situation. The torsor structure it is built from is
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts`, which is
[Stacks Project, Tag 0CK2] at this situation, and the base point on the lift side is `F` through
`Deformation.Examples.liftsOverBaseTopEquiv`. The conclusion is a `Nonempty` because the
action of Tag 0CK2 is produced existentially there. -/
theorem nonempty_schemeMorphismLiftEquivFactorization :
    Nonempty (liftsOverBase i j pX' pY' f ⊤ ≃ {θ : P.base ⟶ G // P.d ≫ θ = ξ}) := by
  obtain ⟨e⟩ := nonempty_schemeMorphismLiftEquivCokernelHom f pY pX hf hX hY hA hF₁ hF₂ ε P G κ
  exact ⟨e.trans (Deformation.ToposThickening.factorizationEquivCokernelHom P G ξ θ₀).symm⟩

include pX hf hX hY hA hF₁ hF₂ ε ξ κ θ₀ in
/-- **[Stacks Project, Tag 08U8], clause (2), for the lifts of a morphism of schemes.** In the
situation of `Deformation.Examples.nonempty_schemeMorphismLiftEquivFactorization`, the
homomorphisms out of `H⁰(NL)` — written as the Hom out of the cokernel of the differential, the
group the source further identifies with `Ext⁰(Lf^*𝖭𝖫_{Y/k}, 𝒪_X)` — act simply transitively on
the morphisms `X' ⟶ Y'` over the base that restrict to `f`.

This is `AlgebraicGeometry.RingedSpaceThickening.liftTranslate` and the three conclusions of
clause (2) proved there, read through the equivalence. It is not a restatement of
`Deformation.Examples.exists_simplyTransitive_addAction_schemeMorphismLifts`: the acting group
there is `Der_k(𝒪_Y, f_*𝒪_X)`, and the content here is that it may be replaced by the
homomorphisms out of the degree `0` cohomology of the naive cotangent complex — which is what
the identification `κ` asserts. -/
theorem exists_simplyTransitive_cokernelHom_schemeMorphismLifts :
    ∃ act : (cokernel P.d ⟶ G) → liftsOverBase i j pX' pY' f ⊤ → liftsOverBase i j pX' pY' f ⊤,
      (∀ c : liftsOverBase i j pX' pY' f ⊤, act 0 c = c) ∧
        (∀ (a b : cokernel P.d ⟶ G) (c : liftsOverBase i j pX' pY' f ⊤),
          act a (act b c) = act (a + b) c) ∧
          ∀ c₀ c₁ : liftsOverBase i j pX' pY' f ⊤,
            ∃! a : cokernel P.d ⟶ G, act a c₀ = c₁ := by
  obtain ⟨e⟩ := nonempty_schemeMorphismLiftEquivFactorization f pY pX hf hX hY hA hF₁ hF₂ ε
    P G ξ κ θ₀
  exact ⟨liftTranslate P G ξ e, liftTranslate_zero P G ξ e, liftTranslate_add P G ξ e,
    existsUnique_liftTranslate P G ξ e⟩

end Factorization

end Deformation.Examples

end
