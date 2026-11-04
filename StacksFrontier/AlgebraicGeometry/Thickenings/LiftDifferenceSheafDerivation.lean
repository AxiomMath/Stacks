module

public import StacksFrontier.AlgebraicGeometry.Thickenings.LiftBaseIdentification
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian

/-!
# The difference of two lifts as a bundled derivation on the Zariski site

`StacksFrontier/AlgebraicGeometry/Thickenings/LiftBaseIdentification.lean` carries the difference
`Stacks.Thickenings.mapDifferenceApp` of two lifts of a map along a thickening over an
**arbitrary** open, together with the equations it satisfies sectionwise: additivity, the Leibniz
rule, compatibility with restriction, the vanishing at `1` and the vanishing on sections pulled
back from the base. This file packages those equations as a single
`PresheafOfModules.Derivation'` on the Zariski site of `Y'`, which is the notion of derivation
that [Stacks Project, Tag 04BV] — `AlgebraicGeometry.Scheme.Hom.derivationDirectImageEquiv` of
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/DerivationsIntoDirectImage.lean` —
consumes, and in exactly the shape it consumes: a
`AlgebraicGeometry.SheafOfModules.SheafDerivation (inverseImageStructureMap q)` whose
coefficients are a pushforward `(AlgebraicGeometry.Scheme.Modules.pushforward a').obj _`.

The algebraic-spaces analogue of this bundling, on the small étale site, is
`AlgebraicGeometry.Space.liftDifferenceDerivation` of
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceBundledDerivation.lean`.

## Main definitions

* `Stacks.Thickenings.mapDifferenceCoefficients`: the defining ideal of `i : X ⟶ X'`, pushed
  forward along `a'` to a sheaf of `𝒪_{Y'}`-modules.
* `Stacks.Thickenings.mapDifferenceDerivationData`: the four equations bundled as a
  `PresheafOfModules.Derivation'` over the constant presheaf `ℤ`, that is, with no vanishing
  condition beyond the Leibniz rule.
* `Stacks.Thickenings.mapDifferenceSheafDerivation`: the same derivation read over
  `q⁻¹𝒪_S ⟶ 𝒪_{Y'}`, so that it is a derivation of `𝒪_{Y'}` **relative to `S`**.

## Main results

* `Stacks.Thickenings.mapDifferenceApp_mul_eq`: the two lifts induce the *same* scalar action on
  the difference, so the Leibniz rule may be read with scalars acting through either lift.
* `Stacks.Thickenings.mapDifferenceApp_leibniz_app`: the Leibniz rule with scalars acting through
  the comorphism of `a'`, which is the action the coefficients carry.
* `Stacks.Thickenings.mapDifferenceSheafDerivation_d`: the bundled derivation differentiates a
  section to the difference of the two comorphisms on it, so nothing about it has to be unfolded.

## Implementation notes

Two things have to be arranged.

**The coefficients carry the scalar action of the *first* lift.** The module structure on
`(AlgebraicGeometry.Scheme.Modules.pushforward a').obj _` is restriction of scalars along the
comorphism of `a'`, whereas `Stacks.Thickenings.mapDifferenceApp_leibniz` states the Leibniz rule
with scalars acting through the second lift, `Stacks.Thickenings.secondLiftAppLE`. The two actions
agree on the difference: their discrepancy on `D y` is `D x * D y`, a product of two sections of
the defining ideal, which vanishes by
`Stacks.Thickenings.mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot`. That is
`Stacks.Thickenings.mapDifferenceApp_mul_eq`, and it is where the square-zero condition enters a
second time. So no transport along `Stacks.Thickenings.preimage_eq_of_comm_of_surjective` is needed
to build
the coefficients, and no `eqToHom` appears in this file: the pushforward is taken along `a'`
throughout, which is the lift whose preimages `mapDifferenceApp` is already stated over.

**The vanishing condition is checked on the comorphism image, not on the inverse image.** A
`SheafDerivation (inverseImageStructureMap q)` must annihilate every section of the *sheaf*
`q⁻¹𝒪_S`, and such a section need not come from a single section of `𝒪_S`. It is
`AlgebraicGeometry.SheafOfModules.ofComorphism` that reduces this to the sections that do, which
is why the derivation is first built over the constant presheaf `ℤ` — as in
`AlgebraicGeometry.Scheme.Hom.restrictDerivationData` of
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/RestrictOpen.lean` — and only then read
over `q⁻¹𝒪_S`. The hypothesis `ofComorphism` asks for is exactly
`Stacks.Thickenings.mapDifferenceApp_base_app_eq_zero`. That reduction needs the coefficients to
be a *sheaf*, which is why they are built with
`AlgebraicGeometry.SheafOfModules.kerObj` — whose sheaf condition is part of
`AlgebraicGeometry.SheafOfModules.kerSubmodule` — rather than by hand.

The kernel is taken **after** the pushforward, so that the sections over `V` are a submodule of
`Γ(X', a' ⁻¹ᵁ V)` over `Γ(Y', V)` directly, with membership
`Stacks.Thickenings.mapDifferenceApp_mem_coefficients` reading as the vanishing of
`i.app (a' ⁻¹ᵁ V)`. Taking the kernel first and only then pushing forward gives a module over
`Γ(X', a' ⁻¹ᵁ V)` instead, and typeclass resolution — which unfolds at reducible transparency
only — does not then find the `Γ(Y', V)`-action the derivation fields are stated with.

## What is not done here

The derivation built here differentiates `𝒪_{Y'}`. [Stacks Project, Tag 04FG] asks for a
derivation of `𝒪_Y`, the structure sheaf of the closed subscheme. Descending along
`𝒪_{Y'} ⟶ j_*𝒪_Y` needs, in addition:

* the vanishing of the difference on the defining ideal of `j : Y ⟶ Y'` over a general open,
  which is hypothesis (2) of the source and is **not** proved here or anywhere else in the tree;
* the descent itself, which is proved generically over any site as
  `Stacks.Sites.Conormal.existsUnique_derivation_of_vanishing_on_kernel` of
  `StacksFrontier/CategoryTheory/Sites/Modules/DerivationKernelDescent.lean`, and whose vanishing
  hypothesis is precisely the previous item.

Neither is done here, and no `@[stacks 04FG]` is claimed: this file is an interior step.

## References

* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}}
variable {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'} {p : X' ⟶ S} {q : Y' ⟶ S}

/-! ### The coefficients -/

/-- **The defining ideal of `i : X ⟶ X'`, pushed forward along `a'`.** This is the sheaf of
`𝒪_{Y'}`-modules in which the difference of two lifts takes its values: its sections over an open
`V` of `Y'` are the sections of the defining ideal over `a' ⁻¹ᵁ V`, with `Γ(Y', V)` acting through
the comorphism of `a'`.

The kernel is taken after the pushforward rather than before, so that the sections are a
`Γ(Y', V)`-submodule of `Γ(X', a' ⁻¹ᵁ V)` on the nose. -/
noncomputable def mapDifferenceCoefficients (i : X ⟶ X') (a' : X' ⟶ Y') : Y'.Modules :=
  SheafOfModules.kerObj ((Scheme.Modules.pushforward a').map
    (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))

/-- The difference of two lifts is killed by `i.app (a' ⁻¹ᵁ V)`. -/
private theorem app_mapDifferenceApp_eq_zero (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x : Γ(Y', V)) :
    (i.app (a' ⁻¹ᵁ V)).hom
      ((mapDifferenceApp hi comm_a comm_b V x :
        RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V)) = 0 := by
  rw [← Scheme.Hom.appLE_eq_app]
  exact (mapDifferenceApp hi comm_a comm_b V x).2

/-- **The difference of two lifts is a section of the coefficients.** Membership is the vanishing
of `i.app (a' ⁻¹ᵁ V)`, which is what `Stacks.Thickenings.mapDifferenceApp` carries by
construction, read through `AlgebraicGeometry.Scheme.Hom.appLE_eq_app`. -/
theorem mapDifferenceApp_mem_coefficients (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x : Γ(Y', V)) :
    ((mapDifferenceApp hi comm_a comm_b V x :
        RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
      ∈ (SheafOfModules.kerSubmodule ((Scheme.Modules.pushforward a').map
          (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))).obj (op V) :=
  (SheafOfModules.mem_kerSubmodule _ _ _).mpr (app_mapDifferenceApp_eq_zero hi comm_a comm_b V x)

/-! ### The Leibniz rule for the action of the first lift -/

/-- **The two lifts induce the same scalar action on the difference.** Multiplying `D y` by
`a'.appLE x` and by `b'.appLE x` gives the same section, because the discrepancy is
`D x * D y`, a product of two sections of the defining ideal of `i`, and that vanishes by
`Stacks.Thickenings.mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot`.

This is what lets the coefficients be the pushforward along `a'`, whose scalar action is through
`a'`, while the Leibniz rule `Stacks.Thickenings.mapDifferenceApp_leibniz` is stated with scalars
through `b'`. -/
theorem mapDifferenceApp_mul_eq [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x y : Γ(Y', V)) :
    (a'.appLE V (a' ⁻¹ᵁ V) le_rfl).hom x
        * ((mapDifferenceApp hi comm_a comm_b V y :
            RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
      = (secondLiftAppLE hi comm_a comm_b V).hom x
        * ((mapDifferenceApp hi comm_a comm_b V y :
            RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) :
              Γ(X', a' ⁻¹ᵁ V)) := by
  have hz := mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot i hsq (a' ⁻¹ᵁ V) _ _
    (app_mapDifferenceApp_eq_zero hi comm_a comm_b V x)
    (app_mapDifferenceApp_eq_zero hi comm_a comm_b V y)
  simp only [mapDifferenceApp_coe] at hz ⊢
  linear_combination hz

/-- **The Leibniz rule with scalars acting through the first lift**, which is the action the
coefficients `Stacks.Thickenings.mapDifferenceCoefficients` carry. This is
`Stacks.Thickenings.mapDifferenceApp_leibniz` read through
`Stacks.Thickenings.mapDifferenceApp_mul_eq`. -/
theorem mapDifferenceApp_leibniz_app [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x y : Γ(Y', V)) :
    ((mapDifferenceApp hi comm_a comm_b V (x * y) :
        RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
      = (a'.app V).hom x
          * ((mapDifferenceApp hi comm_a comm_b V y :
              RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
        + (a'.app V).hom y
          * ((mapDifferenceApp hi comm_a comm_b V x :
              RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) :
                Γ(X', a' ⁻¹ᵁ V)) := by
  rw [Scheme.Hom.app_eq_appLE, mapDifferenceApp_mul_eq hsq hi comm_a comm_b V x y,
    mapDifferenceApp_mul_eq hsq hi comm_a comm_b V y x]
  exact mapDifferenceApp_leibniz hsq hi comm_a comm_b V x y

/-! ### The bundling -/

/-- **The difference of two lifts, bundled as a derivation with no relative vanishing
condition.** The four fields are `Stacks.Thickenings.mapDifferenceApp_add`,
`Stacks.Thickenings.mapDifferenceApp_leibniz_app`, `Stacks.Thickenings.mapDifferenceApp_res` and
`Stacks.Thickenings.mapDifferenceApp_one`, the last through
`AlgebraicGeometry.SheafOfModules.constIntMap_app_eq_zero`.

Differentiating over the constant presheaf `ℤ` imposes no condition beyond the Leibniz rule; the
condition relative to `S` is imposed by `Stacks.Thickenings.mapDifferenceSheafDerivation`. -/
noncomputable def mapDifferenceDerivationData [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) :
    (mapDifferenceCoefficients i a').val.Derivation'
      (SheafOfModules.constIntMap Y'.presheaf) where
  d {W} := AddMonoidHom.mk'
    (fun x => ⟨_, mapDifferenceApp_mem_coefficients hi comm_a comm_b W.unop x⟩)
    (fun x y => Subtype.ext (by
      change (a'.appLE W.unop (a' ⁻¹ᵁ W.unop) le_rfl).hom (x + y)
            - (secondLiftAppLE hi comm_a comm_b W.unop).hom (x + y)
          = ((a'.appLE W.unop (a' ⁻¹ᵁ W.unop) le_rfl).hom x
              - (secondLiftAppLE hi comm_a comm_b W.unop).hom x)
            + ((a'.appLE W.unop (a' ⁻¹ᵁ W.unop) le_rfl).hom y
              - (secondLiftAppLE hi comm_a comm_b W.unop).hom y)
      have h1 := map_add (a'.appLE W.unop (a' ⁻¹ᵁ W.unop) le_rfl).hom x y
      have h2 := map_add (secondLiftAppLE hi comm_a comm_b W.unop).hom x y
      linear_combination h1 - h2))
  d_mul {W} x y :=
    Subtype.ext (mapDifferenceApp_leibniz_app hsq hi comm_a comm_b W.unop x y)
  d_map {W W'} f x :=
    Subtype.ext (mapDifferenceApp_res hi comm_a comm_b f.unop.le x).symm
  d_app {W} r := by
    refine SheafOfModules.constIntMap_app_eq_zero _ (Subtype.ext ?_) r
    have h : ((mapDifferenceApp hi comm_a comm_b W.unop 1 :
        RingHom.ker (i.appLE (a' ⁻¹ᵁ W.unop) (i ⁻¹ᵁ a' ⁻¹ᵁ W.unop) le_rfl).hom) :
          Γ(X', a' ⁻¹ᵁ W.unop)) = 0 := by
      rw [mapDifferenceApp_one, ZeroMemClass.coe_zero]
    exact h

/-- **The difference of two lifts, as a derivation of `𝒪_{Y'}` relative to `S`.** Let `i : X ⟶ X'`
be a closed immersion with square-zero defining ideal and surjective on points, let `j : Y ⟶ Y'`
be any morphism, and let `a' b' : X' ⟶ Y'` be two lifts of one and the same `a : X ⟶ Y`, both of
them morphisms over `S` in the sense that `a' ≫ q = p` and `b' ≫ q = p`. Then the difference of
the two comorphisms is a derivation of `𝒪_{Y'}` over `q⁻¹𝒪_S` with values in the defining ideal
of `i` pushed forward along `a'`.

This is `Stacks.Thickenings.mapDifferenceDerivationData` read over `q⁻¹𝒪_S ⟶ 𝒪_{Y'}` by
`AlgebraicGeometry.SheafOfModules.ofComorphism`, whose vanishing hypothesis is
`Stacks.Thickenings.mapDifferenceApp_base_app_eq_zero`.

It is **not** yet the derivation of [Stacks Project, Tag 04FG], which differentiates `𝒪_Y`; see
the section "What is not done here" of the module documentation. -/
noncomputable def mapDifferenceSheafDerivation [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap q)
      (mapDifferenceCoefficients i a') :=
  SheafOfModules.ofComorphism q (mapDifferenceDerivationData hsq hi comm_a comm_b)
    (fun W r => Subtype.ext (by
      have h : ((mapDifferenceApp hi comm_a comm_b (q ⁻¹ᵁ W) ((q.app W).hom r) :
          RingHom.ker (i.appLE (a' ⁻¹ᵁ q ⁻¹ᵁ W) (i ⁻¹ᵁ a' ⁻¹ᵁ q ⁻¹ᵁ W) le_rfl).hom) :
            Γ(X', a' ⁻¹ᵁ q ⁻¹ᵁ W)) = 0 := by
        rw [mapDifferenceApp_base_app_eq_zero hi comm_a comm_b ha' hb' W r,
          ZeroMemClass.coe_zero]
      exact h))

/-- **The bundled derivation differentiates a section to the difference of the two comorphisms on
it**, so that no consumer has to unfold `Stacks.Thickenings.mapDifferenceSheafDerivation`. -/
theorem mapDifferenceSheafDerivation_d [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (V : Y'.Opens) (x : Γ(Y', V)) :
    (mapDifferenceSheafDerivation hsq hi comm_a comm_b ha' hb').d x
      = ⟨((mapDifferenceApp hi comm_a comm_b V x :
            RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V)),
          mapDifferenceApp_mem_coefficients hi comm_a comm_b V x⟩ :=
  rfl

end Stacks.Thickenings

end
