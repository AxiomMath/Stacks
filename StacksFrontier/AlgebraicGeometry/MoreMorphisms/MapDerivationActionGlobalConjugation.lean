module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalBase
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobalComposition

/-!
# Translating a lift by a derivation commutes with conjugating it

Let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings over a scheme `S` and let
`(a, a') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a morphism of thickenings. There are two independent ways to
perturb the lift `a'`:

* **translating** it by an `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`, which is
  `Stacks.Thickenings.derivationActionGlobal`, the `θ ⬝ a'` of [Stacks Project, Tag 0CK1];
* **conjugating** it by a pair of modified self-maps of `X'` and of `Y'`, each restricting to
  the identity on the closed subscheme — that is, by `u ⬝ 𝟙_{X'}` on the source and `v ⬝ 𝟙_{Y'}`
  on the target.

This file proves that the two **commute**. Translating and then conjugating gives the same
morphism as conjugating and then translating, with the *same* derivation `θ` in both readings.

This is the input `hcomm` of `Deformation.map_add_of_simplyTransitive` and of
`Deformation.map_add_of_simplyTransitiveVAdd`, and so it is what makes the arrow `b` of the
six-term exact sequence of [Stacks Project, Tag 0E3V] additive: `b` sends a pair of
infinitesimal automorphisms of the two endpoint deformations to the unique derivation carrying
the trivial lift of `f` where conjugation by that pair carries it, and additivity of such a map
is formal from the two perturbations being independent operations. The source's reason is that
both perturbations are of order `ε` on a base where `ε² = 0`; here that is the vanishing of the
cross terms.

## Main results

* `Stacks.Thickenings.derivationActionGlobal_comp_targetSelfMap`: translation commutes with
  postcomposition by a modified self-map of the target, `(θ ⬝ a') ≫ (v ⬝ 𝟙) = θ ⬝ (a' ≫ v ⬝ 𝟙)`.
* `Stacks.Thickenings.sourceSelfMap_comp_derivationActionGlobal`: translation commutes with
  precomposition by a modified self-map of the source,
  `(u ⬝ 𝟙) ≫ (θ ⬝ a') = θ ⬝ ((u ⬝ 𝟙) ≫ a')`.
* `Stacks.Thickenings.derivationActionGlobalEquivOfBase_comp_targetSelfMap` and
  `Stacks.Thickenings.derivationActionGlobalEquivOfBase_sourceSelfMap_comp`: the same two, read
  through the torsor bijection of [Stacks Project, Tag 0CK2] that presents the lifts of `a` over
  the base as the derivations. These are the companions of
  `Stacks.Thickenings.derivationActionGlobalEquivOfBase_comp`, which records that the bijection
  carries addition of derivations to composition of self-maps; together the three are the laws
  that an additive action consumes.

## Implementation notes

Both are proved by the uniqueness statement `Stacks.Thickenings.eq_derivationActionGlobal`
applied at the *conjugated* base lift, so neither constructs anything: each only computes the
comorphism of the candidate over an arbitrary pair of opens and matches it against the
perturbation `D_θ`.

In both cases the computation has exactly one nonformal step, the vanishing of a cross term, and
it is the vanishing of `D` applied to a value of `D`:

* for the target, `D_θ (D_v g) = 0` because `D_v g` is a section of the defining ideal of `j`
  (`Stacks.Thickenings.derivationSection_mem_ker` for the self-map thickening of `Y'`, whose
  closed immersion is `j`) while `D_θ` restricts its argument along `j` before differentiating
  it, so it annihilates that ideal
  (`Stacks.Thickenings.derivationSection_eq_zero_of_app_eq_zero`);
* for the source, `D_u (D_θ g) = 0` for the same reason with the roles exchanged: `D_θ g` is a
  section of the defining ideal of `i` and `D_u` restricts along `i`.

What makes the opens bookkeeping go through is that a modified lift has the same underlying map
as the lift it modifies (`Stacks.Thickenings.derivationActionGlobal_preimage`), so a modified
self-map has the same preimages as the identity and the intermediate open of
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` may be taken to be `W` on the target side and
`V` on the source side. The comorphism of `𝟙` over a pair of opens is handled by
`Stacks.Thickenings.id_appLE_apply_self` and `Stacks.Thickenings.id_appLE_apply_map`, which are
stated applied to a section because the codomain `Γ(X', 𝟙 ⁻¹ᵁ W)` is `Γ(X', W)` by `rfl` but not
reducibly, so `rw` refuses the resulting motive.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' : X' ⟶ Y'}
  {p : X' ⟶ S} {q : Y' ⟶ S}

/-! ### Translation commutes with conjugation on the target -/

/-- **Translating a lift by a derivation commutes with postcomposing it by a modified self-map
of the target**, `(θ ⬝ a') ≫ (v ⬝ 𝟙_{Y'}) = θ ⬝ (a' ≫ (v ⬝ 𝟙_{Y'}))`.

The content is the vanishing of the cross term `D_θ (D_v g)`: the comorphism of the composite
sends `g` to `(a')^♯(g + D_v g) + D_θ(g + D_v g)`, and `D_v g` lies in the defining ideal of `j`
while `D_θ` annihilates that ideal. What is left is
`(a')^♯(g + D_v g) + D_θ(g)`, which is the comorphism of the conjugated lift perturbed by the
same `θ`. -/
theorem derivationActionGlobal_comp_targetSelfMap [IsClosedImmersion i] [IsClosedImmersion j]
    (hsq : i.ker ^ 2 = ⊥) (hsqj : j.ker ^ 2 = ⊥)
    (θ : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
    (v : Smooth.pullbackCotangentSheaf (j ≫ q) (𝟙 Y) ⟶ conormalModules j)
    (comm_a : i ≫ a' = a ≫ j)
    (comm_j : j ≫ (𝟙 Y' : Y' ⟶ Y') = (𝟙 Y : Y ⟶ Y) ≫ j)
    (comm_c : i ≫ (a' ≫ derivationActionGlobal hsqj v comm_j) = a ≫ j) :
    derivationActionGlobal hsq θ comm_a ≫ derivationActionGlobal hsqj v comm_j =
      derivationActionGlobal hsq θ comm_c := by
  have hcomm_total : i ≫ (derivationActionGlobal hsq θ comm_a ≫
      derivationActionGlobal hsqj v comm_j) = a ≫ j := by
    rw [← Category.assoc, comm_derivationActionGlobal hsq θ comm_a, Category.assoc,
      comm_derivationActionGlobal hsqj v comm_j, Category.id_comp]
  refine eq_derivationActionGlobal hsq θ comm_c hcomm_total ?_
  intro W V hA g
  -- a modified self-map has the same preimages as the identity, so the three lifts
  -- `a'`, `θ ⬝ a'` and their composites with `v ⬝ 𝟙` carry `V` into `W` by the same proof
  have hAa : V ≤ a' ⁻¹ᵁ W := hA
  -- the comorphism of `v ⬝ 𝟙` over `(W, W)` is `g + D_v g`
  have hβapp : ((derivationActionGlobal hsqj v comm_j).appLE W W le_rfl).hom g
      = g + derivationSection hsqj v W W le_rfl g := by
    rw [derivationActionGlobal_appLE hsqj v comm_j W W le_rfl g,
      id_appLE_apply_self Y' W le_rfl g]
  -- the cross term dies: a value of `D_v` is a section of the defining ideal of `j`
  have hcross : derivationSection hsq θ W V (preimage_le_of_comm comm_a hAa)
      (derivationSection hsqj v W W le_rfl g) = 0 :=
    derivationSection_eq_zero_of_app_eq_zero hsq θ W V _ _
      (RingHom.mem_ker.mp (derivationSection_mem_ker (hsq := hsqj) (θ := v) W W le_rfl g))
  -- both composites factor through the comorphism of `v ⬝ 𝟙` at the open `W` of `Y'`
  have e1 : ((derivationActionGlobal hsq θ comm_a ≫
        derivationActionGlobal hsqj v comm_j).appLE W V hAa).hom g
      = ((derivationActionGlobal hsq θ comm_a).appLE W V hAa).hom
          (((derivationActionGlobal hsqj v comm_j).appLE W W le_rfl).hom g) :=
    congrArg (fun z : Γ(Y', W) ⟶ Γ(X', V) => z.hom g)
      (Scheme.Hom.appLE_comp_appLE (derivationActionGlobal hsq θ comm_a)
        (derivationActionGlobal hsqj v comm_j) W W V le_rfl hAa).symm
  have e2 : ((a' ≫ derivationActionGlobal hsqj v comm_j).appLE W V hAa).hom g
      = (a'.appLE W V hAa).hom
          (((derivationActionGlobal hsqj v comm_j).appLE W W le_rfl).hom g) :=
    congrArg (fun z : Γ(Y', W) ⟶ Γ(X', V) => z.hom g)
      (Scheme.Hom.appLE_comp_appLE a' (derivationActionGlobal hsqj v comm_j) W W V le_rfl hAa).symm
  change ((derivationActionGlobal hsq θ comm_a ≫
        derivationActionGlobal hsqj v comm_j).appLE W V hAa).hom g
      = ((a' ≫ derivationActionGlobal hsqj v comm_j).appLE W V hAa).hom g
        + derivationSection hsq θ W V (preimage_le_of_comm comm_a hAa) g
  rw [e1, e2, hβapp, map_add, map_add,
    derivationActionGlobal_appLE hsq θ comm_a W V hAa g,
    derivationActionGlobal_appLE hsq θ comm_a W V hAa
      (derivationSection hsqj v W W le_rfl g),
    hcross]
  ring

/-! ### Translation commutes with conjugation on the source -/

/-- **Translating a lift by a derivation commutes with precomposing it by a modified self-map of
the source**, `(u ⬝ 𝟙_{X'}) ≫ (θ ⬝ a') = θ ⬝ ((u ⬝ 𝟙_{X'}) ≫ a')`.

The content is the vanishing of the cross term `D_u (D_θ g)`, the mirror of the one in
`Stacks.Thickenings.derivationActionGlobal_comp_targetSelfMap`: the comorphism of the composite
sends `g` to `s + D_u s` for `s = (a')^♯ g + D_θ g`, and `D_θ g` lies in the defining ideal of
`i` while `D_u` restricts its argument along `i` before differentiating it. -/
theorem sourceSelfMap_comp_derivationActionGlobal [IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥)
    (θ : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
    (u : Smooth.pullbackCotangentSheaf (i ≫ p) (𝟙 X) ⟶ conormalModules i)
    (comm_a : i ≫ a' = a ≫ j)
    (comm_i : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
    (comm_c : i ≫ (derivationActionGlobal hsq u comm_i ≫ a') = a ≫ j) :
    derivationActionGlobal hsq u comm_i ≫ derivationActionGlobal hsq θ comm_a =
      derivationActionGlobal hsq θ comm_c := by
  have hcomm_total : i ≫ (derivationActionGlobal hsq u comm_i ≫
      derivationActionGlobal hsq θ comm_a) = a ≫ j := by
    rw [← Category.assoc, comm_derivationActionGlobal hsq u comm_i, Category.id_comp,
      comm_derivationActionGlobal hsq θ comm_a]
  refine eq_derivationActionGlobal hsq θ comm_c hcomm_total ?_
  intro W V hA g
  -- a modified self-map of the source has the same preimages as the identity
  have hAa : V ≤ a' ⁻¹ᵁ W := hA
  -- the cross term dies: a value of `D_θ` is a section of the defining ideal of `i`
  have hcross : derivationSection hsq u V V (preimage_le_of_comm comm_i le_rfl)
      (derivationSection hsq θ W V (preimage_le_of_comm comm_a hAa) g) = 0 :=
    derivationSection_eq_zero_of_app_eq_zero hsq u V V _ _
      (RingHom.mem_ker.mp
        (derivationSection_mem_ker (hsq := hsq) (θ := θ) W V
          (preimage_le_of_comm comm_a hAa) g))
  -- the comorphism of `u ⬝ 𝟙` over `(V, V)` is `s + D_u s`
  have hαapp : ∀ s : Γ(X', V),
      ((derivationActionGlobal hsq u comm_i).appLE V V le_rfl).hom s
        = s + derivationSection hsq u V V (preimage_le_of_comm comm_i le_rfl) s := by
    intro s
    rw [derivationActionGlobal_appLE hsq u comm_i V V le_rfl s,
      id_appLE_apply_self X' V le_rfl s]
  -- both composites factor through the comorphism of `u ⬝ 𝟙` at the open `V` of `X'`
  have e1 : ((derivationActionGlobal hsq u comm_i ≫
        derivationActionGlobal hsq θ comm_a).appLE W V hAa).hom g
      = ((derivationActionGlobal hsq u comm_i).appLE V V le_rfl).hom
          (((derivationActionGlobal hsq θ comm_a).appLE W V hAa).hom g) :=
    congrArg (fun z : Γ(Y', W) ⟶ Γ(X', V) => z.hom g)
      (Scheme.Hom.appLE_comp_appLE (derivationActionGlobal hsq u comm_i)
        (derivationActionGlobal hsq θ comm_a) W V V hAa le_rfl).symm
  have e2 : ((derivationActionGlobal hsq u comm_i ≫ a').appLE W V hAa).hom g
      = ((derivationActionGlobal hsq u comm_i).appLE V V le_rfl).hom
          ((a'.appLE W V hAa).hom g) :=
    congrArg (fun z : Γ(Y', W) ⟶ Γ(X', V) => z.hom g)
      (Scheme.Hom.appLE_comp_appLE (derivationActionGlobal hsq u comm_i) a' W V V
        hAa le_rfl).symm
  change ((derivationActionGlobal hsq u comm_i ≫
        derivationActionGlobal hsq θ comm_a).appLE W V hAa).hom g
      = ((derivationActionGlobal hsq u comm_i ≫ a').appLE W V hAa).hom g
        + derivationSection hsq θ W V (preimage_le_of_comm comm_a hAa) g
  rw [e1, e2, derivationActionGlobal_appLE hsq θ comm_a W V hAa g, hαapp, hαapp,
    derivationSection_add, hcross]
  ring

/-! ### The two commutations read through the torsor bijection -/

section Base

variable {Z Z' : Scheme.{u}} {kk : Z ⟶ Z'} [IsClosedImmersion i] [IsImmersion j] [IsImmersion kk]
  {h : Y ⟶ Z} {h' : Y' ⟶ Z'} {g' : X' ⟶ Z'}

/-- **Translation commutes with conjugation on the target, read through the torsor bijection of
[Stacks Project, Tag 0CK2].** `Stacks.Thickenings.derivationActionGlobalEquivOfBase` presents the
lifts of `a` over the base as the derivations, by `θ ↦ θ ⬝ a'`; this says that postcomposing the
lift attached to `θ` by a modified self-map of the target gives the lift attached to the *same*
`θ` at the conjugated base point.

This is the companion of `Stacks.Thickenings.derivationActionGlobalEquivOfBase_comp` — which
records that the bijection carries addition to composition — and together they are the two laws
that make the arrow `b` of [Stacks Project, Tag 0E3V] additive. -/
theorem derivationActionGlobalEquivOfBase_comp_targetSelfMap (hsq : i.ker ^ 2 = ⊥)
    [IsClosedImmersion j] (hsqj : j.ker ^ 2 = ⊥)
    (sq : IsPullback j h h' kk) (ci : i ≫ g' = (a ≫ h) ≫ kk)
    (comm_a : i ≫ a' = a ≫ j) (ha : a' ≫ h' = g')
    (v : Stacks.Smooth.pullbackCotangentSheaf (j ≫ h') (𝟙 Y) ⟶ conormalModules j)
    (comm_j : j ≫ (𝟙 Y' : Y' ⟶ Y') = (𝟙 Y : Y ⟶ Y) ≫ j)
    (comm_c : i ≫ (a' ≫ derivationActionGlobal hsqj v comm_j) = a ≫ j)
    (hac : (a' ≫ derivationActionGlobal hsqj v comm_j) ≫ h' = g')
    (θ : Stacks.Smooth.pullbackCotangentSheaf h a ⟶ conormalModules i) :
    (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha θ).1 ≫
        derivationActionGlobal hsqj v comm_j =
      (derivationActionGlobalEquivOfBase hsq sq ci comm_c hac θ).1 := by
  rw [derivationActionGlobalEquivOfBase_apply, derivationActionGlobalEquivOfBase_apply]
  exact derivationActionGlobal_comp_targetSelfMap hsq hsqj _ v comm_a comm_j comm_c

/-- **Translation commutes with conjugation on the source, read through the torsor bijection of
[Stacks Project, Tag 0CK2].** The mirror of
`Stacks.Thickenings.derivationActionGlobalEquivOfBase_comp_targetSelfMap`: precomposing the lift
attached to `θ` by a modified self-map of the source gives the lift attached to the same `θ` at
the conjugated base point. -/
theorem derivationActionGlobalEquivOfBase_sourceSelfMap_comp (hsq : i.ker ^ 2 = ⊥)
    (sq : IsPullback j h h' kk) (ci : i ≫ g' = (a ≫ h) ≫ kk)
    (comm_a : i ≫ a' = a ≫ j) (ha : a' ≫ h' = g')
    (u : Stacks.Smooth.pullbackCotangentSheaf (i ≫ g') (𝟙 X) ⟶ conormalModules i)
    (comm_i : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
    (comm_c : i ≫ (derivationActionGlobal hsq u comm_i ≫ a') = a ≫ j)
    (hac : (derivationActionGlobal hsq u comm_i ≫ a') ≫ h' = g')
    (θ : Stacks.Smooth.pullbackCotangentSheaf h a ⟶ conormalModules i) :
    derivationActionGlobal hsq u comm_i ≫
        (derivationActionGlobalEquivOfBase hsq sq ci comm_a ha θ).1 =
      (derivationActionGlobalEquivOfBase hsq sq ci comm_c hac θ).1 := by
  rw [derivationActionGlobalEquivOfBase_apply, derivationActionGlobalEquivOfBase_apply]
  exact sourceSelfMap_comp_derivationActionGlobal hsq _ u comm_a comm_i comm_c

end Base

end Stacks.Thickenings

end
