module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal

/-!
# Composing two modified lifts adds their derivations

Let `i : X ⟶ X'` be a first-order thickening and let `(a, a') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a
morphism of thickenings over `S`. For an `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` the
modified lift `θ ⬝ a'` of [Stacks Project, Tag 0CK1] is
`Stacks.Thickenings.derivationActionGlobal`, whose comorphism is `(a')^♯ + D_θ` with
`D_θ = θ ∘ d_{Y/S}`. This file records how the construction interacts with *addition of
derivations*, in the two ways that an addition can be read off it.

The first is iteration: perturbing `a'` by `η` and then perturbing the result by `θ` perturbs
`a'` by `θ + η`. This is the group law of the action of [Stacks Project, Tag 04FJ] and holds for
an arbitrary morphism of thickenings, because in `θ ⬝ (η ⬝ a')` the derivation `θ` is applied to
the original section and not to the perturbed one.

The second is **composition of self-maps**, and it is the one that makes the action a group
homomorphism rather than merely additive. When `Y' = X'`, `j = i` and `(a, a') = (𝟙_X, 𝟙_{X'})`
the modified lifts are self-maps of `X'` fixing `X`, and these compose:

`(θ ⬝ 𝟙) ≫ (η ⬝ 𝟙) = (θ + η) ⬝ 𝟙`.

Here the two derivations genuinely meet, since `θ ⬝ 𝟙` is applied to the already-perturbed
section `g + D_η g`. The cross term `D_θ (D_η g)` vanishes: `D_η g` is a section of the defining
ideal of `i` (`Stacks.Thickenings.derivationSection_mem_ker`) and `D_θ` restricts a section
along `i` before differentiating it, so it annihilates that ideal
(`Stacks.Thickenings.derivationSection_eq_zero_of_mem_ker`). What is left is the Leibniz-free
statement that `D_θ + D_η = D_{θ+η}`, which is additivity of `θ ↦ θ ∘ d_{Y/S}` in `θ`.

## Main results

* `Stacks.Thickenings.derivationSection_add_hom`: the perturbation `D_θ = θ ∘ d_{Y/S}` is
  additive in `θ`.
* `Stacks.Thickenings.derivationActionGlobal_derivationActionGlobal`: iterating the construction
  adds the derivations, `θ ⬝ (η ⬝ a') = (θ + η) ⬝ a'`.
* `Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`: **composing two
  modified self-maps of a first-order thickening adds their derivations.** This is the
  multiplicativity of `θ ↦ θ ⬝ 𝟙`, and it is what upgrades the simply transitive action of
  [Stacks Project, Tag 04FJ] on the self-maps of `X'` fixing `X` to an isomorphism of groups.

## Implementation notes

Both results are proved by the uniqueness statement
`Stacks.Thickenings.eq_derivationActionGlobal`: a lift of `a` whose comorphism differs from that
of `a'` by `D_{θ+η}` over every pair of opens *is* the modified lift for `θ + η`. So neither
proof constructs anything; each only computes the comorphism of the candidate over an arbitrary
pair of opens `(W, V)` and matches it against `D_{θ+η}`.

For the composition the comorphism of `c ≫ d` over `(W, V)` is obtained from
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` at the intermediate open `V`, which is legitimate
because a modified lift has the same underlying map as the lift it modifies
(`Stacks.Thickenings.derivationActionGlobal_preimage`), so `V` is carried into `W` by the second
factor exactly when it is by the identity. The two auxiliary lemmas
`Stacks.Thickenings.id_appLE_apply_map` and `Stacks.Thickenings.id_appLE_apply_self` say that the
comorphism of `𝟙` over a pair of opens is the restriction map, and the identity when the two
opens coincide. They are stated applied to a section rather than as an equality of ring
homomorphisms: the comorphism of `𝟙_{X'}` has codomain `Γ(X', 𝟙 ⁻¹ᵁ W)`, which is `Γ(X', W)` by
`rfl` but not reducibly, so `rw` refuses the resulting motive while a declared-type `show`
crosses it.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {q : Y' ⟶ S}

/-! ### The perturbation is additive in the derivation -/

/-- **`Stacks.Thickenings.derivationSection` is additive in `θ`.** The perturbation
`D_θ = θ ∘ d_{Y/S}` is obtained from `θ` by evaluating it on a section and including the result
into `𝒪_{X'}`, and both of those steps are additive. -/
theorem derivationSection_add_hom [IsClosedImmersion i] {hsq : i.ker ^ 2 = ⊥}
    (θ η : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
    (W : Y'.Opens) (V : X'.Opens) (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) :
    derivationSection hsq (θ + η) W V hU g
      = derivationSection hsq θ W V hU g + derivationSection hsq η W V hU g := by
  rw [derivationSection, derivationSection, derivationSection, ← conormalSection_add]
  rfl

/-! ### The comorphism of the identity -/

/-- **The comorphism of `𝟙` over a pair of opens is the restriction map.** -/
theorem id_appLE_apply_map (Z : Scheme.{u}) (W V : Z.Opens) (h : V ≤ (𝟙 Z : Z ⟶ Z) ⁻¹ᵁ W)
    (h' : V ≤ W) (g : Γ(Z, W)) :
    ((𝟙 Z : Z ⟶ Z).appLE W V h).hom g = (Z.presheaf.map (homOfLE h').op).hom g := by
  have e : (𝟙 Z : Z ⟶ Z).appLE W V h = Z.presheaf.map (homOfLE h').op := by
    show 𝟙 Γ(Z, W) ≫ Z.presheaf.map (homOfLE h').op = Z.presheaf.map (homOfLE h').op
    rw [Category.id_comp]
  exact congrArg (fun z : Γ(Z, W) ⟶ Γ(Z, V) => z.hom g) e

/-- **The comorphism of `𝟙` over one open is the identity.** -/
theorem id_appLE_apply_self (Z : Scheme.{u}) (V : Z.Opens) (h : V ≤ (𝟙 Z : Z ⟶ Z) ⁻¹ᵁ V)
    (x : Γ(Z, V)) : ((𝟙 Z : Z ⟶ Z).appLE V V h).hom x = x := by
  rw [id_appLE_apply_map Z V V h le_rfl x]
  show (Z.presheaf.map (𝟙 (Opposite.op V))).hom x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-! ### Iterating the construction -/

section Iterate

variable [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
  (θ η : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
  {a' : X' ⟶ Y'} (comm_a : i ≫ a' = a ≫ j)

/-- **Iterating the modified-lift construction adds the derivations**, `θ ⬝ (η ⬝ a') =
(θ + η) ⬝ a'`. This is the group law of the action of [Stacks Project, Tag 04FJ]: the comorphism
of `θ ⬝ (η ⬝ a')` is `((a')^♯ + D_η) + D_θ`, and `D_θ + D_η = D_{θ + η}` by
`Stacks.Thickenings.derivationSection_add_hom`.

Nothing here makes the two derivations interact, since in `θ ⬝ (η ⬝ a')` the derivation `θ` is
applied to the original section of `𝒪_{Y'}`. The statement that does is
`Stacks.Thickenings.derivationActionGlobal_comp_derivationActionGlobal`. -/
theorem derivationActionGlobal_derivationActionGlobal :
    derivationActionGlobal (a' := derivationActionGlobal hsq η comm_a) hsq θ
        (comm_derivationActionGlobal hsq η comm_a)
      = derivationActionGlobal hsq (θ + η) comm_a := by
  refine eq_derivationActionGlobal hsq (θ + η) comm_a
    (comm_derivationActionGlobal (a' := derivationActionGlobal hsq η comm_a) hsq θ
      (comm_derivationActionGlobal hsq η comm_a)) ?_
  intro W V hA g
  rw [derivationActionGlobal_appLE (a' := derivationActionGlobal hsq η comm_a) hsq θ
      (comm_derivationActionGlobal hsq η comm_a) W V hA g,
    derivationActionGlobal_appLE hsq η comm_a W V hA g,
    derivationSection_add_hom θ η W V (preimage_le_of_comm comm_a hA) g]
  ring

end Iterate

/-! ### Composing two modified self-maps -/

section Compose

variable [IsClosedImmersion i] {p : X' ⟶ S}

/-- **Composing two modified self-maps of a first-order thickening adds their derivations**,
`(θ ⬝ 𝟙) ≫ (η ⬝ 𝟙) = (θ + η) ⬝ 𝟙`.

Let `i : X ⟶ X'` be a first-order thickening of a scheme over `S`. Taking `Y' = X'`, `j = i` and
`(a, a') = (𝟙_X, 𝟙_{X'})` in [Stacks Project, Tag 02H5], the modified lift `θ ⬝ 𝟙` is a self-map
of `X'` restricting to the identity of `X`, and `θ ↦ θ ⬝ 𝟙` carries addition of derivations to
composition of self-maps.

This is what makes that assignment a homomorphism of groups, and not merely an additive action:
the torsor axioms of [Stacks Project, Tag 04FJ] relate `θ + η` to iterating the action, which is
`Stacks.Thickenings.derivationActionGlobal_derivationActionGlobal` and says nothing about
composing the two self-maps.

The content is the vanishing of the cross term. The comorphism of the composite over an open `W`
of `X'` sends `g` to `(g + D_η g) + D_θ (g + D_η g)`, and `D_θ (D_η g) = 0` because `D_η g` lies
in the defining ideal of `i` (`Stacks.Thickenings.derivationSection_mem_ker`) while `D_θ`
restricts its argument along `i` before differentiating it
(`Stacks.Thickenings.derivationSection_eq_zero_of_mem_ker`). -/
theorem derivationActionGlobal_comp_derivationActionGlobal (hsq : i.ker ^ 2 = ⊥)
    (comm : i ≫ (𝟙 X' : X' ⟶ X') = (𝟙 X : X ⟶ X) ≫ i)
    (θ η : Smooth.pullbackCotangentSheaf (i ≫ p) (𝟙 X) ⟶ conormalModules i) :
    derivationActionGlobal hsq θ comm ≫ derivationActionGlobal hsq η comm
      = derivationActionGlobal hsq (θ + η) comm := by
  have comm_c : i ≫ (derivationActionGlobal hsq θ comm ≫ derivationActionGlobal hsq η comm)
      = (𝟙 X : X ⟶ X) ≫ i := by
    rw [← Category.assoc, comm_derivationActionGlobal hsq θ comm, Category.id_comp,
      comm_derivationActionGlobal hsq η comm, Category.id_comp]
  refine eq_derivationActionGlobal hsq (θ + η) comm comm_c ?_
  intro W V hA g
  have hA' : V ≤ W := hA
  have hV : V ≤ (𝟙 X' : X' ⟶ X') ⁻¹ᵁ V := le_rfl
  have hB := preimage_le_of_comm comm hV
  have hC := preimage_le_of_comm comm hA
  -- the comorphism of the composite factors through the two perturbations at the open `V`
  have e1 : ((derivationActionGlobal hsq θ comm ≫ derivationActionGlobal hsq η comm).appLE W V
        (le_preimage_of_comm hsq comm comm_c hA)).hom g
      = ((derivationActionGlobal hsq θ comm).appLE V V hV).hom
          (((derivationActionGlobal hsq η comm).appLE W V hA).hom g) :=
    congrArg (fun z : Γ(X', W) ⟶ Γ(X', V) => z.hom g)
      (Scheme.Hom.appLE_comp_appLE (derivationActionGlobal hsq θ comm)
        (derivationActionGlobal hsq η comm) W V V hA hV).symm
  -- the cross term dies: a value of the perturbation lies in the defining ideal of `i`
  have hcross : derivationSection hsq θ V V hB
        (derivationSection hsq η W V hC g) = 0 :=
    derivationSection_eq_zero_of_mem_ker V V hB
      (RingHom.mem_ker.mp (derivationSection_mem_ker W V hC g))
  -- the surviving term is the perturbation read over the original pair of opens
  have hshift : derivationSection hsq θ V V hB
        (((𝟙 X' : X' ⟶ X').appLE W V hA).hom g)
      = derivationSection hsq θ W V hC g := by
    rw [id_appLE_apply_map X' W V hA hA' g]
    exact derivationSection_map W V hA' V hC
      hB g
  rw [e1, derivationActionGlobal_appLE hsq η comm W V hA g,
    derivationActionGlobal_appLE hsq θ comm V V hV _, map_add, id_appLE_apply_self X' V hV,
    id_appLE_apply_self X' V hV, derivationSection_add V V hB,
    hcross, hshift, derivationSection_add_hom θ η W V hC g]
  ring

end Compose

end Stacks.Thickenings

end
