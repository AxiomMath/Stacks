module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionDifference
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalConormalTrack

/-!
# A derivation is determined by the lift it produces, and every lift arises

Let `S` be a scheme, let `i : X ⟶ X'` be a first-order thickening, let `j : Y ⟶ Y'` be an
immersion with structure morphism `q : Y' ⟶ S`, and let `(a, a')` be a morphism of thickenings
`(X ⊂ X') ⟶ (Y ⊂ Y')`. [Stacks Project, Tag 02H5] says that each
`θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` produces exactly one lift `θ ⬝ a'` of `a` satisfying Equation
[Stacks Project, Tag 04BV], and that is
`Stacks.Thickenings.existsUnique_derivationActionGlobal`. This file proves the statement in the
*other* variable: the assignment

`θ ↦ θ ⬝ a'`

is a **bijection** onto the lifts of `a` over `S` satisfying the two conditions of
[Stacks Project, Tag 04FG] relative to `a'`.

That is what makes `Stacks.Thickenings.derivationActionGlobal` an identification of the
derivations with the lifts, rather than a map from the one to the other; together with
`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal` it makes the
identification of self-maps of a first-order thickening with derivations an isomorphism of
groups.

## Main results

* `Stacks.Thickenings.derivationActionSheaf_injective` and
  `Stacks.Thickenings.derivationActionGlobal_injective`: **a derivation is determined by the
  lift it produces.**
* `Stacks.Thickenings.exists_eq_derivationActionGlobal`: **every lift of `a` over `S` satisfying
  the two conditions of [Stacks Project, Tag 04FG] is `θ ⬝ a'` for some `θ`.**
* `Stacks.Thickenings.immersionConormalSheafMap_derivationActionGlobal`: the modified lift does
  satisfy those conditions, so the two statements above are about the same set.
* `Stacks.Thickenings.derivationActionGlobalEquiv`: **the bijection**, as data.

## Route

Injectivity is where the two conditions of [Stacks Project, Tag 04FG] do real work, and it is
not the comorphism computation one might expect. Two lifts with the same comorphism give an
equality of derivations only on the sections of `𝒪_Y` in the image of `j^♯`, which does not
determine a map out of `Ω_{Y/S}`. What does determine it is the *difference derivation* of
[Stacks Project, Tag 04FG] attached to the pair `(a', θ ⬝ a')`, which is an honest `𝒪_S`-
derivation on every section of `𝒪_Y` and is `θ ∘ d_{Y/S}` by
`Stacks.Thickenings.derivationActionDifferenceDerivation_eq` — [Stacks Project, Tag 0CK1]. Two
data with the same modified lift therefore have the same difference derivation, hence agree
after `d_{Y/S}`, and a datum is determined by that
(`Stacks.Thickenings.pullback_relativeDifferentials_hom_ext`). The argument runs in the
derivation track and is carried across to the global track by
`Stacks.Thickenings.derivationActionGlobal_eq_derivationActionSheaf` and the datum bijection
`Stacks.Thickenings.derivationDatumEquiv`.

Surjectivity is the unrestricted [Stacks Project, Tag 04FG] itself,
`Stacks.Thickenings.exists_isDerivationAction_pullbackCotangentSheaf`, followed by the
uniqueness half of [Stacks Project, Tag 02H5]
(`Stacks.Thickenings.eq_of_isDerivationAction`) to identify the lift it produces with the
modified lift, and then the same track bridge.

## Implementation notes

The difference derivation of a pair depends on the second lift through the three hypotheses that
name it, so replacing that lift by an equal one is a transport;
`Stacks.Thickenings.differenceDerivation_congr_of_eq` performs it by `subst` and proof
irrelevance, which is why it needs no content. The same device gives
`Stacks.Thickenings.immersionConormalSheafMap_congr_lift`, and both are what let the global
track inherit the derivation track's statements without re-proving them.

The two conditions of [Stacks Project, Tag 04FG] are carried in the subtype as an existential
over the commuting square with the remaining two clauses as its components, so that the
conormal-sheaf condition is stated at the square it belongs to; the square itself is proof-
irrelevant, so nothing is lost and the forward map supplies it from
`Stacks.Thickenings.comm_derivationActionGlobal`.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' : X' ⟶ Y'}

section Bijective

variable [IsClosedImmersion i] [IsImmersion j]

/-! ### Transports along an equality of lifts -/

/-- **The difference derivation of a pair of lifts depends on the lifts and not on how they are
named.** The three hypotheses of `Stacks.Thickenings.differenceDerivation` mention one of the
lifts, so replacing it by an equal one is a transport; after `subst` the hypotheses are proofs of
one proposition. -/
theorem differenceDerivation_congr_of_eq (q : Y' ⟶ S) (hi : i.ker ^ 2 = ⊥)
    {b' L₁ L₂ : X' ⟶ Y'} (hL : L₁ = L₂)
    (hq₁ : b' ≫ q = L₁ ≫ q) (c₁ : i ≫ L₁ = a ≫ j) (cb : i ≫ b' = a ≫ j)
    (hC₁ : immersionConormalSheafMap i j a L₁ (toShHom_square c₁)
      = immersionConormalSheafMap i j a b' (toShHom_square cb))
    (hq₂ : b' ≫ q = L₂ ≫ q) (c₂ : i ≫ L₂ = a ≫ j)
    (hC₂ : immersionConormalSheafMap i j a L₂ (toShHom_square c₂)
      = immersionConormalSheafMap i j a b' (toShHom_square cb)) :
    differenceDerivation q hi hq₁ c₁ cb hC₁ = differenceDerivation q hi hq₂ c₂ cb hC₂ := by
  subst hL
  rfl

/-- **Two equal lifts induce the same map of conormal sheaves**, the squares being
proof-irrelevant. -/
theorem immersionConormalSheafMap_congr_lift {c d : X' ⟶ Y'} (h : c = d)
    (cc : i ≫ c = a ≫ j) (cd : i ≫ d = a ≫ j) :
    immersionConormalSheafMap i j a c (toShHom_square cc)
      = immersionConormalSheafMap i j a d (toShHom_square cd) := by
  subst h
  rfl

/-- **Two morphisms of modules whose postcompositions with a derivation agree, agree on the
universal differentials.** -/
theorem derivation_postcomp_congr_app_of_eq {Y₁ S₁ : Scheme.{u}} {q₁ : Y₁ ⟶ S₁}
    {M N : Y₁.Modules}
    (Dv : SheafOfModules.SheafDerivation (inverseImageStructureMap q₁) M)
    {F₁ F₂ : M ⟶ N} (h : Dv.postcomp F₁.val = Dv.postcomp F₂.val) (W : Y₁.Opens)
    (s : Γ(Y₁, W)) :
    (F₁.val.app (op W)).hom (Dv.d s) = (F₂.val.app (op W)).hom (Dv.d s) :=
  congrArg (fun D : SheafOfModules.SheafDerivation (inverseImageStructureMap q₁) N =>
    D.d (X := op W) s) h

/-! ### Injectivity -/

/-- **A derivation datum is determined by the modified lift it produces**, in the derivation
track.

The content is that the difference derivation of [Stacks Project, Tag 04FG] attached to the pair
`(a', θ ⬝ a')` is `θ ∘ d_{Y/S}` ([Stacks Project, Tag 0CK1],
`Stacks.Thickenings.derivationActionDifferenceDerivation_eq`). That is an equality of derivations
on *every* section of `𝒪_Y`, which is strictly more than the comorphisms give — they agree only
on the image of `j^♯` — and a map out of `Ω_{Y/S}` is determined by it. -/
theorem derivationActionSheaf_injective (hi : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (ca : i ≫ a' = a ≫ j)
    {θ₁ θ₂ : (Scheme.Modules.pullback a).obj (Scheme.Hom.relativeDifferentials (j ≫ q)) ⟶
      Stacks.Conormal.conormalSheaf i}
    (h : derivationActionSheaf hi q ca θ₁ = derivationActionSheaf hi q ca θ₂) : θ₁ = θ₂ := by
  have hdd : derivationActionDifferenceDerivation hi q ca θ₁
      = derivationActionDifferenceDerivation hi q ca θ₂ :=
    differenceDerivation_congr_of_eq q hi h _ _ _ _ _ _ _
  rw [derivationActionDifferenceDerivation_eq, derivationActionDifferenceDerivation_eq] at hdd
  refine pullback_relativeDifferentials_hom_ext a (j ≫ q) fun V s => ?_
  exact derivation_postcomp_congr_app_of_eq (Scheme.Hom.universalRelativeDerivation (j ≫ q))
    hdd V s

/-- **A derivation is determined by the modified lift it produces.** The statement of
`Stacks.Thickenings.derivationActionSheaf_injective` carried to the global track along
`Stacks.Thickenings.derivationActionGlobal_eq_derivationActionSheaf` and the datum bijection
`Stacks.Thickenings.derivationDatumEquiv`. -/
theorem derivationActionGlobal_injective (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (comm_a : i ≫ a' = a ≫ j)
    {θ η : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i}
    (h : derivationActionGlobal hsq θ comm_a = derivationActionGlobal hsq η comm_a) : θ = η := by
  have hdd : derivationDatumOfCotangent θ = derivationDatumOfCotangent η :=
    derivationActionSheaf_injective hsq q comm_a
      (((derivationActionGlobal_eq_derivationActionSheaf hsq q comm_a θ).symm.trans h).trans
        (derivationActionGlobal_eq_derivationActionSheaf hsq q comm_a η))
  exact (cotangentDatum_derivationDatumOfCotangent θ).symm.trans
    ((congrArg cotangentDatumOfDerivationDatum hdd).trans
      (cotangentDatum_derivationDatumOfCotangent η))

/-! ### Surjectivity -/

/-- **The modified lift satisfies the conormal-sheaf condition of [Stacks Project, Tag 04FG]**,
condition (2) for the pair `(a', θ ⬝ a')`. -/
theorem immersionConormalSheafMap_derivationActionGlobal (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (comm_a : i ≫ a' = a ≫ j)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) :
    immersionConormalSheafMap i j a a' (toShHom_square comm_a)
      = immersionConormalSheafMap i j a (derivationActionGlobal hsq θ comm_a)
          (toShHom_square (comm_derivationActionGlobal hsq θ comm_a)) :=
  (immersionConormalSheafMap_derivationActionSheaf hsq q comm_a
      (derivationDatumOfCotangent θ)).symm.trans
    (immersionConormalSheafMap_congr_lift
      (derivationActionGlobal_eq_derivationActionSheaf hsq q comm_a θ).symm
      (derivationActionSheaf_comm hsq q comm_a (derivationDatumOfCotangent θ))
      (comm_derivationActionGlobal hsq θ comm_a))

/-- **Every lift of `a` over `S` satisfying the two conditions of [Stacks Project, Tag 04FG]
relative to `a'` is a modified lift.** This is the unrestricted [Stacks Project, Tag 04FG],
`Stacks.Thickenings.exists_isDerivationAction_pullbackCotangentSheaf`, followed by the uniqueness
half of [Stacks Project, Tag 02H5] identifying the lift the datum produces with `b'`. -/
theorem exists_eq_derivationActionGlobal (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (comm_a : i ≫ a' = a ≫ j) {b' : X' ⟶ Y'} (hq : b' ≫ q = a' ≫ q)
    (cb : i ≫ b' = a ≫ j)
    (hC : immersionConormalSheafMap i j a a' (toShHom_square comm_a)
      = immersionConormalSheafMap i j a b' (toShHom_square cb)) :
    ∃ θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i,
      derivationActionGlobal hsq θ comm_a = b' := by
  obtain ⟨θ, hθ⟩ := exists_isDerivationAction_pullbackCotangentSheaf hsq q hq comm_a cb hC
  refine ⟨θ, ?_⟩
  rw [derivationActionGlobal_eq_derivationActionSheaf hsq q comm_a θ]
  exact eq_of_isDerivationAction hsq q comm_a
    (derivationActionSheaf_comm hsq q comm_a (derivationDatumOfCotangent θ)) cb
    (isDerivationAction_derivationActionSheaf hsq q comm_a (derivationDatumOfCotangent θ)) hθ

/-! ### The bijection -/

/-- The modified lift as a map into the lifts of `a` over `S` satisfying the two conditions of
[Stacks Project, Tag 04FG] relative to `a'`. -/
def derivationActionGlobalLift (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S) (comm_a : i ≫ a' = a ≫ j)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) :
    { b' : X' ⟶ Y' // ∃ cb : i ≫ b' = a ≫ j, b' ≫ q = a' ≫ q ∧
        immersionConormalSheafMap i j a a' (toShHom_square comm_a)
          = immersionConormalSheafMap i j a b' (toShHom_square cb) } :=
  ⟨derivationActionGlobal hsq θ comm_a, comm_derivationActionGlobal hsq θ comm_a,
    comp_derivationActionGlobal hsq θ comm_a rfl,
    immersionConormalSheafMap_derivationActionGlobal hsq q comm_a θ⟩

/-- **`θ ↦ θ ⬝ a'` is a bijection onto the lifts of `a` over `S` satisfying the two conditions
of [Stacks Project, Tag 04FG] relative to `a'`.** -/
theorem derivationActionGlobalLift_bijective (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (comm_a : i ≫ a' = a ≫ j) :
    Function.Bijective (derivationActionGlobalLift hsq q comm_a) := by
  refine ⟨fun θ η h => derivationActionGlobal_injective hsq q comm_a
    (congrArg Subtype.val h), fun b => ?_⟩
  obtain ⟨cb, hq, hC⟩ := b.2
  obtain ⟨θ, hθ⟩ := exists_eq_derivationActionGlobal hsq q comm_a hq cb hC
  exact ⟨θ, Subtype.ext hθ⟩

/-- **The derivations are the lifts**, [Stacks Project, Tag 04FG] and
[Stacks Project, Tag 02H5] read as one bijection. This is the identification as *data*: the
inverse sends a lift to the derivation measuring its difference from `a'`. -/
def derivationActionGlobalEquiv (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (comm_a : i ≫ a' = a ≫ j) :
    (Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) ≃
      { b' : X' ⟶ Y' // ∃ cb : i ≫ b' = a ≫ j, b' ≫ q = a' ≫ q ∧
          immersionConormalSheafMap i j a a' (toShHom_square comm_a)
            = immersionConormalSheafMap i j a b' (toShHom_square cb) } :=
  Equiv.ofBijective _ (derivationActionGlobalLift_bijective hsq q comm_a)

/-- The bijection is the modified-lift construction. -/
@[simp]
theorem derivationActionGlobalEquiv_apply (hsq : i.ker ^ 2 = ⊥) (q : Y' ⟶ S)
    (comm_a : i ≫ a' = a ≫ j)
    (θ : Stacks.Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i) :
    (derivationActionGlobalEquiv hsq q comm_a θ).1 = derivationActionGlobal hsq θ comm_a :=
  rfl

end Bijective

end Stacks.Thickenings

end
