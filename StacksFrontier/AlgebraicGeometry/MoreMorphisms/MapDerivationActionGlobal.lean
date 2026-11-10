module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafKer
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationAction
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinitesimal deformations of maps: a derivation acts on a lift

Let `S` be a scheme and let `(a, a') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a morphism of first-order
thickenings over `S`. Given an `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`, there is exactly one
morphism of pairs `(a, b') : (X ⊂ X') ⟶ (Y ⊂ Y')` satisfying conditions (1) and (2) of
[Stacks Project, Tag 04FG] for which the associated derivation `D` and `θ` correspond under
Equation [Stacks Project, Tag 04BV]. That is [Stacks Project, Tag 02H5], and this file proves it
for arbitrary schemes: nothing is affine, and `θ` is a morphism of sheaves of modules out of the
pulled-back sheaf of relative differentials, as in the source.

`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDerivationAction.lean` proves the same statement
on global sections over affine ambient schemes; nothing here is deduced from it, and no affine
open is chosen anywhere.

## How the two conditions of Tag 04FG and Equation 04BV are written

The conditions are read on sections, over an arbitrary open `W` of `Y'` and an arbitrary open `V`
of `X'` carried into `W`.

* Condition (1) of [Stacks Project, Tag 04FG], that the two reductions agree, is imposed by
  writing both squares over the same `a`: a morphism of thickenings `(b, b')` with `b = a` is
  exactly a `b'` with `i ≫ b' = a ≫ j`. That `b'` is a morphism over `S` is `b' ≫ q = p`.
* Condition (2), that the two induced maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of
  [Stacks Project, Tag 01R4] agree, is unwound: for a first-order thickening `j` the conormal
  sheaf `𝒞_{Y/Y'}` *is* the defining ideal of `j` and the induced map of the square is the
  comorphism, so the condition says that `(a')^♯` and `(b')^♯` agree on the sections of `𝒪_{Y'}`
  killed by `j^♯`.
* Equation [Stacks Project, Tag 04BV] is the statement that `(b')^♯ - (a')^♯` is
  `Stacks.Thickenings.derivationSection`, that is `θ` applied to the pulled-back universal
  differential `Stacks.Smooth.pullbackD` and then included into `𝒪_{X'}` along
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι`. The difference derivation `D` of
  [Stacks Project, Tag 04FG] is not re-assumed: it is exactly this difference, and the factoring
  through `𝒪_Y` and through the subsheaf `𝒞_{X/X'} ⊆ 𝒪_{X'}` that Tag 04FG asserts is visible in
  the formula, which applies `θ` to `d_{Y/S}(j^♯ g)`.

Since `d_{Y/S}` kills the image of `j^♯` on the defining ideal of `j`, condition (2) is a
consequence of Equation [Stacks Project, Tag 04BV]; it is stated anyway, so that the conclusion
below is literally the source's.

## Main definitions

* `Stacks.Thickenings.conormalSection`: a section of the conormal sheaf of a first-order
  thickening `i`, read as a section of `𝒪_{X'}` through
  `Stacks.Thickenings.firstOrderImmersionConormalSheafι`.
* `Stacks.Thickenings.derivationSection`: the derivation `D = θ ∘ d_{Y/S}` of Equation
  [Stacks Project, Tag 04BV], on sections.
* `Stacks.Thickenings.derivationActionApp`: the modified comorphism `(a')^♯ + D` over an open of
  `Y'`, as a ring homomorphism.
* `Stacks.Thickenings.derivationActionC`: the same family as a morphism of sheaves of rings.
* `Stacks.Thickenings.derivationActionGlobal`: the modified lift `b' : X' ⟶ Y'` itself. In the
  notation of [Stacks Project, Tag 0CK1] this is `θ ⬝ a'`.

## Main results

* `Stacks.Thickenings.conormalSection_mul_conormalSection`: two sections of the conormal sheaf
  multiply to zero in `𝒪_{X'}`, the square-zero condition in the form the construction uses.
* `Stacks.Thickenings.comm_derivationActionGlobal`,
  `Stacks.Thickenings.comp_derivationActionGlobal`: the modified lift is a morphism of
  thickenings over `S` with the same reduction `a`.
* `Stacks.Thickenings.derivationActionGlobal_appLE`: Equation [Stacks Project, Tag 04BV] for the
  modified lift, over an arbitrary pair of opens.
* `Stacks.Thickenings.eq_derivationActionGlobal`: no other lift has these properties.
* `Stacks.Thickenings.existsUnique_derivationActionGlobal`: the three previous results assembled
  into the existence-and-uniqueness statement of [Stacks Project, Tag 02H5].

## Implementation notes

The modified lift is *constructed*, and it is constructed directly, not glued from affine
charts. Its underlying continuous map is that of `a'` and its comorphism is the family
`g ↦ (a')^♯ g + θ (d_{Y/S} (j^♯ g))` over every open of `Y'` at once; the verification that this
family is a morphism of sheaves of rings is the one the source omits.

* Multiplicativity is where the square-zero condition enters: the cross term is a product of two
  sections of the defining ideal of `i`, hence zero by
  `Stacks.Thickenings.conormalSection_mul_conormalSection`, which rests on
  `Stacks.Thickenings.ker_app_sq_eq_bot` — the defining ideal of a first-order thickening is
  square-zero over *every* open, not only over an affine one. The two surviving terms are the two
  halves of the Leibniz rule for `Stacks.Smooth.pullbackD` after the scalar action of `𝒪_Y` on
  the conormal sections is rewritten as multiplication by `(a')^♯` using the commuting square of
  the morphism of thickenings (`Stacks.Thickenings.appLE_comm_of_comm`).
* Compatibility with restriction is the naturality of each of the four factors; the two
  directions are `Stacks.Thickenings.map_derivationSection`, for shrinking the open of `X'`, and
  `Stacks.Thickenings.derivationSection_map`, for shrinking the open of `Y'`.
* The construction produces a morphism of *presheafed* spaces; what makes it a morphism of
  schemes is that its stalk maps are local. That is
  `Stacks.Thickenings.isLocalHom_stalkMap_derivationActionPshHom`: the perturbation takes values
  in a square-zero ideal, so the germ of `D` is nilpotent, the two stalk maps differ by a
  nilpotent element, and adding a nilpotent element to a unit gives a unit — so the locality of
  the stalk maps of `a'` is inherited.

Because the comorphism is defined over every open, Equation [Stacks Project, Tag 04BV] holds over
every pair of opens by construction, and uniqueness is immediate: two lifts of `a` have the same
underlying map, because `i` is surjective (`Stacks.Thickenings.base_eq_of_comm`), and their
comorphisms are then forced to agree open by open. No locality argument and no cover is used in
either direction.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

/-! ### The conormal sheaf of a first-order thickening as a subsheaf of `𝒪_{X'}` -/

variable {S X X' Y Y' : Scheme.{u}}

/-- `𝒞_{X/X'}`, the conormal sheaf of [Stacks Project, Tag 01R2], read as a sheaf of
`𝒪_X`-modules. -/
noncomputable abbrev conormalModules (i : X ⟶ X') [IsImmersion i] : X.Modules :=
  immersionConormalSheaf i

/-- `i_* 𝒞_{X/X'}`, read as a sheaf of `𝒪_{X'}`-modules. -/
noncomputable abbrev conormalModulesPush (i : X ⟶ X') [IsImmersion i] : X'.Modules :=
  (modulePushforward i.toLRSHom.toShHom).obj (immersionConormalSheaf i)

/-- The inclusion `i_* 𝒞_{X/X'} ⟶ 𝒪_{X'}` of a first-order thickening, in the scheme-module
vocabulary. -/
noncomputable abbrev conormalι (i : X ⟶ X') [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) :
    conormalModulesPush i ⟶ SheafOfModules.unit (structureSheafRing X'.toRingedSpace) :=
  firstOrderImmersionConormalSheafι i hsq

variable {i : X ⟶ X'}

/-- **A section of the conormal sheaf as a section of `𝒪_{X'}`.** For a first-order thickening
`i : X ⟶ X'` and an open `V` of `X'`, this is the inclusion
`Stacks.Thickenings.firstOrderImmersionConormalSheafι` read on sections over `V`, a map
`Γ(𝒞_{X/X'}, i⁻¹V) ⟶ Γ(X', V)`. -/
noncomputable def conormalSection [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens)
    (s : Γ(conormalModules i, i ⁻¹ᵁ V)) : Γ(X', V) :=
  (Scheme.Modules.Hom.app (conormalι i hsq) V).hom s

/-- `Stacks.Thickenings.conormalSection` is additive. -/
theorem conormalSection_add [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens)
    (s t : Γ(conormalModules i, i ⁻¹ᵁ V)) :
    conormalSection hsq V (s + t) = conormalSection hsq V s + conormalSection hsq V t :=
  map_add _ _ _

/-- `Stacks.Thickenings.conormalSection` kills zero. -/
@[simp]
theorem conormalSection_zero [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens) :
    conormalSection hsq V (0 : Γ(conormalModules i, i ⁻¹ᵁ V)) = 0 :=
  map_zero _

/-- **`Stacks.Thickenings.conormalSection` turns the `𝒪_X`-action into multiplication.** The
inclusion is `𝒪_{X'}`-linear and the `𝒪_{X'}`-action on `i_*𝒞_{X/X'}` is the `𝒪_X`-action read
through `i^♯`. -/
theorem conormalSection_smul [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens)
    (r : Γ(X', V)) (s : Γ(conormalModules i, i ⁻¹ᵁ V)) :
    conormalSection hsq V ((i.app V).hom r • s) = r * conormalSection hsq V s :=
  Scheme.Modules.Hom.app_smul (M := conormalModulesPush i)
    (N := SheafOfModules.unit (structureSheafRing X'.toRingedSpace)) (conormalι i hsq) r s

/-- **A section of the conormal sheaf is a section of the defining ideal.** -/
theorem conormalSection_mem_ker [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens)
    (s : Γ(conormalModules i, i ⁻¹ᵁ V)) :
    conormalSection hsq V s ∈ RingHom.ker (i.app V).hom := by
  rw [← Stacks.ClosedImmersion.range_idealSheafι_val_app i V]
  exact ⟨(firstOrderConormalIso i hsq).inv.val.app (op V)
    (((modulePushforward i.toLRSHom.toShHom).map
      (Stacks.Immersion.conormalSheafSelfIso i).inv).val.app (op V) s), rfl⟩

/-- **Two sections of the conormal sheaf of a first-order thickening multiply to zero.** The
defining ideal is square-zero over every open by
`Stacks.Thickenings.ker_app_sq_eq_bot`. -/
theorem conormalSection_mul_conormalSection [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (V : X'.Opens) (s t : Γ(conormalModules i, i ⁻¹ᵁ V)) :
    conormalSection hsq V s * conormalSection hsq V t = 0 := by
  have hm : conormalSection hsq V s * conormalSection hsq V t ∈ RingHom.ker (i.app V).hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (conormalSection_mem_ker hsq V s) (conormalSection_mem_ker hsq V t)
  rw [ker_app_sq_eq_bot i hsq V] at hm
  simpa using hm

/-! ### Commuting squares on sections over a pair of opens -/

/-- **A commuting square of schemes, read on sections over a pair of opens.** -/
theorem appLE_congr_hom {Z T : Scheme.{u}} {f g : Z ⟶ T} (h : f = g) (U : T.Opens)
    (V : Z.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

variable {j : Y ⟶ Y'} {a : X ⟶ Y} {a' : X' ⟶ Y'} {p : X' ⟶ S} {q : Y' ⟶ S}

/-- **The commuting square of a morphism of thickenings, on sections.** For
`i ≫ a' = a ≫ j`, an open `W` of `Y'` and an open `V` of `X'` mapping into `W` under `a'`, the
two routes from `Γ(Y', W)` to `Γ(X, i⁻¹V)` agree. -/
theorem appLE_comm_of_comm (comm_a : i ≫ a' = a ≫ j) (W : Y'.Opens) (V : X'.Opens)
    (hA : V ≤ a' ⁻¹ᵁ W) (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) :
    (a.appLE (j ⁻¹ᵁ W) (i ⁻¹ᵁ V) hU).hom ((j.app W).hom g)
      = (i.app V).hom ((a'.appLE W V hA).hom g) := by
  have h1 := Scheme.Hom.appLE_comp_appLE i a' W V (i ⁻¹ᵁ V) hA le_rfl
  have h2 := Scheme.Hom.appLE_comp_appLE a j W (j ⁻¹ᵁ W) (i ⁻¹ᵁ V) le_rfl hU
  rw [Scheme.Hom.appLE_eq_app] at h1
  rw [Scheme.Hom.appLE_eq_app] at h2
  have h4 : a'.appLE W V hA ≫ i.app V = j.app W ≫ a.appLE (j ⁻¹ᵁ W) (i ⁻¹ᵁ V) hU := by
    rw [h1, h2]
    exact appLE_congr_hom comm_a _ _ _ _
  exact (congrArg (fun z : Γ(Y', W) ⟶ Γ(X, i ⁻¹ᵁ V) => z.hom g) h4).symm

/-- **The open `i⁻¹V` maps into `j⁻¹W` under `a`.** For a morphism of thickenings `(a, a')` and
an open `V` of `X'` mapping into `W` under `a'`, the open `i⁻¹V` of `X` maps into `j⁻¹W`. -/
theorem preimage_le_of_comm (comm_a : i ≫ a' = a ≫ j) {W : Y'.Opens} {V : X'.Opens}
    (hA : V ≤ a' ⁻¹ᵁ W) : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W) := by
  have hpre : i ⁻¹ᵁ (a' ⁻¹ᵁ W) = a ⁻¹ᵁ (j ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, comm_a]
  exact hpre ▸ i.preimage_mono hA

/-! ### A self-map of the ambient scheme that fixes the subscheme -/

/-- **A self-map of the ambient scheme fixing the subscheme does not move the preimage of an
open.** For `σ : X' ⟶ X'` with `i ≫ σ = i`, the open `σ⁻¹V` has the same preimage under `i` as
`V` does, because `i ⁻¹ᵁ (σ ⁻¹ᵁ V)` is `(i ≫ σ) ⁻¹ᵁ V`.

No hypothesis on `i` is needed, and `σ` is not required to be over anything: it may cover a
nontrivial self-map of a base scheme, which is the case this is for. -/
theorem preimage_preimage_of_comp_eq_self {σ : X' ⟶ X'} (hσ : i ≫ σ = i) (V : X'.Opens) :
    i ⁻¹ᵁ (σ ⁻¹ᵁ V) = i ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, hσ]

/-- **Restricting along `i` after such a self-map is restricting along `i`.** For
`σ : X' ⟶ X'` with `i ≫ σ = i`, the composite

`Γ(X', V) --σ^♯--> Γ(X', σ⁻¹V) --i^♯--> Γ(X, i⁻¹V)`

is `i^♯` over `V`. The second map is written over the pair of opens `(σ⁻¹V, i⁻¹V)`, which is
legitimate by `Stacks.Thickenings.preimage_preimage_of_comp_eq_self`, so that the statement
carries no transport along an equality of opens.

This is the whole of what `i ≫ σ = i` says on sections, and it is the input a computation of
how `σ` acts on the conormal sheaf of a thickening starts from: it says exactly that `σ^♯`
preserves the defining ideal of `i`, which is
`Stacks.Thickenings.app_mem_ker_of_comp_eq_self`. -/
theorem app_comp_appLE_of_comp_eq_self {σ : X' ⟶ X'} (hσ : i ≫ σ = i) (V : X'.Opens) :
    σ.app V ≫ i.appLE (σ ⁻¹ᵁ V) (i ⁻¹ᵁ V)
        (preimage_preimage_of_comp_eq_self hσ V).ge = i.app V := by
  have h1 := Scheme.Hom.appLE_comp_appLE i σ V (σ ⁻¹ᵁ V) (i ⁻¹ᵁ V) le_rfl
    (preimage_preimage_of_comp_eq_self hσ V).ge
  rw [Scheme.Hom.appLE_eq_app] at h1
  rw [h1, appLE_congr_hom hσ V (i ⁻¹ᵁ V) _ le_rfl, Scheme.Hom.appLE_eq_app]

/-- **A self-map of the ambient scheme fixing the subscheme preserves the defining ideal.** For
`σ : X' ⟶ X'` with `i ≫ σ = i`, a section of `𝒪_{X'}` over `V` killed by `i^♯` is carried by
`σ^♯` to a section killed by `i^♯`. This is
`Stacks.Thickenings.app_comp_appLE_of_comp_eq_self` read on an element. -/
theorem app_mem_ker_of_comp_eq_self {σ : X' ⟶ X'} (hσ : i ≫ σ = i) (V : X'.Opens)
    {g : Γ(X', V)} (hg : g ∈ RingHom.ker (i.app V).hom) :
    (σ.app V).hom g ∈ RingHom.ker (i.appLE (σ ⁻¹ᵁ V) (i ⁻¹ᵁ V)
      (preimage_preimage_of_comp_eq_self hσ V).ge).hom := by
  have h := congrArg (fun z : Γ(X', V) ⟶ Γ(X, i ⁻¹ᵁ V) => z.hom g)
    (app_comp_appLE_of_comp_eq_self hσ V)
  exact h.trans hg

/-! ### The derivation attached to the datum of the source, on sections -/

/-- **The derivation `D = θ ∘ d_{Y/S}` of Equation [Stacks Project, Tag 04BV], on sections.**
For an `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`, an open `W` of `Y'` and an open `V` of `X'`
with `i⁻¹V` mapping into `j⁻¹W`, this is the composite
`Γ(Y', W) --j^♯--> Γ(Y, j⁻¹W) --d--> Γ(a^*Ω_{Y/S}, i⁻¹V) --θ--> Γ(𝒞_{X/X'}, i⁻¹V) ⟶ Γ(X', V)`,
the perturbation `D` that the proof of [Stacks Project, Tag 02H5] adds to `(a')^♯`. -/
noncomputable def derivationSection [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (θ : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
    (W : Y'.Opens) (V : X'.Opens) (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) : Γ(X', V) :=
  conormalSection hsq V ((Scheme.Modules.Hom.app θ (i ⁻¹ᵁ V)).hom
    (Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ W) hU ((j.app W).hom g)))

section Perturbation

variable [IsClosedImmersion i] {hsq : i.ker ^ 2 = ⊥}
  {θ : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i}

/-- `Stacks.Thickenings.derivationSection` is additive. -/
theorem derivationSection_add (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g₁ g₂ : Γ(Y', W)) :
    derivationSection hsq θ W V hU (g₁ + g₂)
      = derivationSection hsq θ W V hU g₁ + derivationSection hsq θ W V hU g₂ := by
  rw [derivationSection, derivationSection, derivationSection, map_add, map_add, map_add,
    conormalSection_add]

/-- `Stacks.Thickenings.derivationSection` kills the unit section. -/
theorem derivationSection_one (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) :
    derivationSection hsq θ W V hU 1 = 0 := by
  rw [derivationSection, map_one, Smooth.pullbackD_one, map_zero, conormalSection_zero]

/-- `Stacks.Thickenings.derivationSection` kills the zero section. -/
theorem derivationSection_zero (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) :
    derivationSection hsq θ W V hU 0 = 0 := by
  rw [derivationSection, map_zero, map_zero, map_zero, conormalSection_zero]

/-- **The values of `Stacks.Thickenings.derivationSection` lie in the defining ideal of `i`.** -/
theorem derivationSection_mem_ker (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) :
    derivationSection hsq θ W V hU g ∈ RingHom.ker (i.app V).hom :=
  conormalSection_mem_ker hsq V _

/-- **`Stacks.Thickenings.derivationSection` kills the sections that vanish on the special
fibre.** The perturbation `D = θ ∘ d_{Y/S}` restricts a section of `𝒪_{Y'}` along `j` before
differentiating it, so a section killed by `j^♯` — in particular any section of the defining
ideal of `j` — is killed by `D`.

Together with `Stacks.Thickenings.derivationSection_mem_ker` this is what makes modified
self-maps of a first-order thickening compose additively: the cross term of
`(1 + D_θ) ∘ (1 + D_η)` is `D_θ` applied to a value of `D_η`, which lies in the defining ideal
and is therefore annihilated. -/
theorem derivationSection_eq_zero_of_mem_ker (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) {g : Γ(Y', W)} (hg : (j.app W).hom g = 0) :
    derivationSection hsq θ W V hU g = 0 := by
  rw [derivationSection, hg, map_zero, map_zero, conormalSection_zero]

/-- **Two values of `Stacks.Thickenings.derivationSection` multiply to zero**, the square-zero
condition that makes the modified comorphism multiplicative. -/
theorem derivationSection_mul_derivationSection (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g₁ g₂ : Γ(Y', W)) :
    derivationSection hsq θ W V hU g₁ * derivationSection hsq θ W V hU g₂ = 0 :=
  conormalSection_mul_conormalSection hsq V _ _

/-- **The Leibniz rule for `Stacks.Thickenings.derivationSection`**, with the scalar action of
`Γ(Y, j⁻¹W)` on the conormal sections rewritten as multiplication by `(a')^♯` using the
commuting square of the morphism of thickenings. -/
theorem derivationSection_mul (comm_a : i ≫ a' = a ≫ j) (W : Y'.Opens) (V : X'.Opens)
    (hA : V ≤ a' ⁻¹ᵁ W) (g₁ g₂ : Γ(Y', W)) :
    derivationSection hsq θ W V (preimage_le_of_comm comm_a hA) (g₁ * g₂)
      = (a'.appLE W V hA).hom g₁ *
          derivationSection hsq θ W V (preimage_le_of_comm comm_a hA) g₂
        + (a'.appLE W V hA).hom g₂ *
          derivationSection hsq θ W V (preimage_le_of_comm comm_a hA) g₁ := by
  rw [derivationSection, derivationSection, derivationSection, map_mul,
    Smooth.pullbackD_mul', map_add, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul,
    conormalSection_add, appLE_comm_of_comm comm_a W V hA _ g₁,
    appLE_comm_of_comm comm_a W V hA _ g₂, conormalSection_smul, conormalSection_smul]

/-- **`Stacks.Thickenings.derivationSection` kills the sections coming from the base**, which is
the `𝒪_S`-linearity of the universal derivation of `Ω_{Y/S}`. -/
theorem derivationSection_appLE (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) {W₀ : S.Opens} (hW : W ≤ q ⁻¹ᵁ W₀) (r : Γ(S, W₀)) :
    derivationSection hsq θ W V hU ((q.appLE W₀ W hW).hom r) = 0 := by
  have h1 := Scheme.Hom.appLE_comp_appLE j q W₀ W (j ⁻¹ᵁ W) hW le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h1
  have h2 : (j.app W).hom ((q.appLE W₀ W hW).hom r)
      = ((j ≫ q).appLE W₀ (j ⁻¹ᵁ W) (le_rfl.trans ((TopologicalSpace.Opens.map j.base).map
          (homOfLE hW)).le)).hom r :=
    congrArg (fun z : Γ(S, W₀) ⟶ Γ(Y, j ⁻¹ᵁ W) => z.hom r) h1
  rw [derivationSection, h2, Smooth.pullbackD_appLE, map_zero, conormalSection_zero]

/-! ### The perturbation is natural in both opens -/

/-- **The pullback of a universal differential does not change when the chart is shrunk.** This
is `Stacks.Smooth.pullbackD_map` with the two restrictions of sections composed. -/
theorem pullbackD_shrink' {Z T W₀ : Scheme.{u}} (f : Z ⟶ W₀) (b : T ⟶ Z) {A A₃ : Z.Opens}
    {U : T.Opens} (hA₃A : A₃ ≤ A) (hUA : U ≤ b ⁻¹ᵁ A) (hUA₃ : U ≤ b ⁻¹ᵁ A₃) (x : Γ(Z, A)) :
    Smooth.pullbackD f b A₃ hUA₃ ((Z.presheaf.map (homOfLE hA₃A).op).hom x)
      = Smooth.pullbackD f b A hUA x := by
  rw [← Smooth.map_pullbackD f b A₃ (le_refl (b ⁻¹ᵁ A₃)) hUA₃ hUA₃,
    Smooth.pullbackD_map f b hA₃A x,
    ← Smooth.map_pullbackD f b A (le_refl (b ⁻¹ᵁ A)) hUA hUA, ← Functor.map_comp_apply]
  rfl

/-- **`Stacks.Thickenings.conormalSection` commutes with restriction of sections.** -/
theorem conormalSection_map (hsq : i.ker ^ 2 = ⊥) {V V' : X'.Opens} (hV : V' ≤ V)
    (s : Γ(conormalModules i, i ⁻¹ᵁ V)) :
    (X'.presheaf.map (homOfLE hV).op).hom (conormalSection hsq V s)
      = conormalSection hsq V'
        ((conormalModules i).presheaf.map (homOfLE (i.preimage_mono hV)).op s) := by
  have h := (Scheme.Modules.Hom.mapPresheaf (conormalι i hsq)).naturality (homOfLE hV).op
  exact (congrArg (fun z : Γ(conormalModulesPush i, V) ⟶
    Γ(SheafOfModules.unit (structureSheafRing X'.toRingedSpace), V') => z.hom s) h).symm

/-- **`Stacks.Thickenings.derivationSection` commutes with restriction to a smaller open of
`X'`.** -/
theorem map_derivationSection (W : Y'.Opens) {V V' : X'.Opens} (hV : V' ≤ V)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (hU' : i ⁻¹ᵁ V' ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) :
    (X'.presheaf.map (homOfLE hV).op).hom (derivationSection hsq θ W V hU g)
      = derivationSection hsq θ W V' hU' g := by
  have hθ := (Scheme.Modules.Hom.mapPresheaf θ).naturality (homOfLE (i.preimage_mono hV)).op
  have hθ' := congrArg (fun z : Γ(Smooth.pullbackCotangentSheaf (j ≫ q) a, i ⁻¹ᵁ V) ⟶
      Γ(conormalModules i, i ⁻¹ᵁ V') => z.hom
        (Smooth.pullbackD (j ≫ q) a (j ⁻¹ᵁ W) hU ((j.app W).hom g))) hθ
  rw [derivationSection, derivationSection, conormalSection_map hsq hV]
  exact congrArg (conormalSection hsq V')
    (hθ'.symm.trans (congrArg (Scheme.Modules.Hom.app θ (i ⁻¹ᵁ V') |>.hom)
      (Smooth.map_pullbackD (j ≫ q) a (j ⁻¹ᵁ W) hU hU' (i.preimage_mono hV) ((j.app W).hom g))))

/-- **`Stacks.Thickenings.derivationSection` commutes with restriction to a smaller open of
`Y'`.** -/
theorem derivationSection_map (W W' : Y'.Opens) (hW : W' ≤ W) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (hU' : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W')) (g : Γ(Y', W)) :
    derivationSection hsq θ W' V hU' ((Y'.presheaf.map (homOfLE hW).op).hom g)
      = derivationSection hsq θ W V hU g := by
  have h1 := Scheme.Hom.map_appLE j (le_rfl : j ⁻¹ᵁ W' ≤ j ⁻¹ᵁ W') (homOfLE hW).op
  rw [Scheme.Hom.appLE_eq_app] at h1
  have h2 := congrArg (fun z : Γ(Y', W) ⟶ Γ(Y, j ⁻¹ᵁ W') => z.hom g) h1
  rw [derivationSection, derivationSection]
  refine congrArg (conormalSection hsq V)
    (congrArg (Scheme.Modules.Hom.app θ (i ⁻¹ᵁ V) |>.hom) ?_)
  rw [show (j.app W').hom ((Y'.presheaf.map (homOfLE hW).op).hom g)
      = (Y.presheaf.map (homOfLE (j.preimage_mono hW)).op).hom ((j.app W).hom g) from h2]
  exact pullbackD_shrink' (j ≫ q) a (j.preimage_mono hW) hU hU' ((j.app W).hom g)

end Perturbation

/-! ### Two lifts of the same morphism -/

section Lifts

variable [IsClosedImmersion i]

/-- **Two lifts of the same morphism have the same underlying map.** A first-order thickening is
a thickening (`Stacks.Thickenings.isThickening_of_ker_pow_eq_bot`), so `i` is surjective and may
be cancelled. -/
theorem base_eq_of_comm (hsq : i.ker ^ 2 = ⊥) {b' : X' ⟶ Y'} (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) : b'.base = a'.base := by
  have hsurj : Function.Surjective i.base :=
    (isThickening_of_ker_pow_eq_bot i inferInstance (n := 1) hsq).2
  have : Epi i.base := (TopCat.epi_iff_surjective i.base).mpr hsurj
  refine (cancel_epi i.base).mp ?_
  rw [← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, comm_b, comm_a]

/-- **Two lifts of the same morphism agree pointwise.** -/
theorem apply_eq_of_comm (hsq : i.ker ^ 2 = ⊥) {b' : X' ⟶ Y'} (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) (x : X') : b' x = a' x := by
  obtain ⟨y, rfl⟩ := (isThickening_of_ker_pow_eq_bot i inferInstance (n := 1) hsq).2 x
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, comm_b, comm_a]

/-- **Two lifts of the same morphism have the same preimages.** -/
theorem preimage_eq_of_comm (hsq : i.ker ^ 2 = ⊥) {b' : X' ⟶ Y'} (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) (W : Y'.Opens) : b' ⁻¹ᵁ W = a' ⁻¹ᵁ W := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change x ∈ b' ⁻¹ᵁ W ↔ x ∈ a' ⁻¹ᵁ W
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, apply_eq_of_comm hsq comm_a comm_b x]

/-- An open mapping into `W` under `a'` maps into `W` under any other lift of `a`. -/
theorem le_preimage_of_comm (hsq : i.ker ^ 2 = ⊥) {b' : X' ⟶ Y'} (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) {W : Y'.Opens} {V : X'.Opens} (hA : V ≤ a' ⁻¹ᵁ W) :
    V ≤ b' ⁻¹ᵁ W :=
  hA.trans (preimage_eq_of_comm hsq comm_a comm_b W).ge

end Lifts

/-! ### The modified lift -/

section Construction

variable [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
  (θ : Smooth.pullbackCotangentSheaf (j ≫ q) a ⟶ conormalModules i)
  (comm_a : i ≫ a' = a ≫ j)

/-- **The modified comorphism over an open of `Y'`.** This is `(a')^♯ + D` over the open `W` of
`Y'`, the ring homomorphism `Γ(Y', W) ⟶ Γ(X', (a')⁻¹W)` of the proof of
[Stacks Project, Tag 02H5]. Multiplicativity is where the square-zero condition enters: the
cross term is a product of two sections of the defining ideal of `i`. -/
noncomputable def derivationActionApp (W : Y'.Opens) : Γ(Y', W) →+* Γ(X', a' ⁻¹ᵁ W) where
  toFun g := (a'.appLE W (a' ⁻¹ᵁ W) le_rfl).hom g
    + derivationSection hsq θ W (a' ⁻¹ᵁ W) (preimage_le_of_comm comm_a le_rfl) g
  map_one' := by rw [map_one, derivationSection_one, add_zero]
  map_zero' := by rw [map_zero, derivationSection_zero, add_zero]
  map_add' x y := by rw [map_add, derivationSection_add]; ring
  map_mul' x y := by
    have hz := derivationSection_mul_derivationSection (hsq := hsq) (θ := θ) W (a' ⁻¹ᵁ W)
      (preimage_le_of_comm comm_a le_rfl) x y
    rw [map_mul, derivationSection_mul comm_a W (a' ⁻¹ᵁ W) le_rfl]
    linear_combination -hz

/-- The value of `Stacks.Thickenings.derivationActionApp`. -/
theorem derivationActionApp_apply (W : Y'.Opens) (g : Γ(Y', W)) :
    derivationActionApp hsq θ comm_a W g = (a'.appLE W (a' ⁻¹ᵁ W) le_rfl).hom g
      + derivationSection hsq θ W (a' ⁻¹ᵁ W) (preimage_le_of_comm comm_a le_rfl) g :=
  rfl

/-- **`Stacks.Thickenings.derivationActionApp` is compatible with restriction**, so that the
family of modified comorphisms is a morphism of sheaves of rings. -/
theorem derivationActionApp_naturality (W W' : Y'.Opens) (hW : W' ≤ W) (g : Γ(Y', W)) :
    derivationActionApp hsq θ comm_a W' ((Y'.presheaf.map (homOfLE hW).op).hom g)
      = (X'.presheaf.map (homOfLE (a'.preimage_mono hW)).op).hom
          (derivationActionApp hsq θ comm_a W g) := by
  have hnat := Scheme.Hom.naturality a' (homOfLE hW).op
  have hnat' := congrArg (fun z : Γ(Y', W) ⟶ Γ(X', a' ⁻¹ᵁ W') => z.hom g) hnat
  simp only [CommRingCat.comp_apply] at hnat'
  rw [Subsingleton.elim ((TopologicalSpace.Opens.map a'.base).map (homOfLE hW).op.unop).op
    (homOfLE (a'.preimage_mono hW)).op] at hnat'
  rw [derivationActionApp_apply, derivationActionApp_apply, Scheme.Hom.appLE_eq_app,
    Scheme.Hom.appLE_eq_app, map_add, ← hnat',
    map_derivationSection W (a'.preimage_mono hW) (preimage_le_of_comm comm_a le_rfl)
      (preimage_le_of_comm comm_a (a'.preimage_mono hW)) g,
    derivationSection_map W W' hW (a' ⁻¹ᵁ W') (preimage_le_of_comm comm_a (a'.preimage_mono hW))
      (preimage_le_of_comm comm_a le_rfl) g]

/-- **The modified comorphism as a morphism of sheaves of rings**, `(a')^♯ + D`. -/
noncomputable def derivationActionC : Y'.presheaf ⟶ a'.base _* X'.presheaf where
  app W := CommRingCat.ofHom (derivationActionApp hsq θ comm_a W.unop)
  naturality := by
    rintro ⟨W⟩ ⟨W'⟩ h
    have hW : W' ≤ W := h.unop.le
    refine CommRingCat.hom_ext (RingHom.ext fun g => ?_)
    rw [Subsingleton.elim h (homOfLE hW).op]
    exact derivationActionApp_naturality hsq θ comm_a W W' hW g

/-- **The modified comorphism as a morphism of presheafed spaces**, with the same underlying
continuous map as `a'`. -/
noncomputable def derivationActionPshHom :
    X'.toLocallyRingedSpace.toPresheafedSpace.Hom Y'.toLocallyRingedSpace.toPresheafedSpace where
  base := a'.base
  c := derivationActionC hsq θ comm_a

/-- **The two stalk maps differ by a nilpotent element.** The perturbation `D` takes values in
the square-zero defining ideal of `i`, so its germ squares to zero. -/
theorem isNilpotent_stalkMap_sub (x : X')
    (z : Y'.presheaf.stalk ((derivationActionPshHom hsq θ comm_a).base x)) :
    IsNilpotent (((derivationActionPshHom hsq θ comm_a).stalkMap x).hom z
      - (a'.toLRSHom.stalkMap x).hom z) := by
  obtain ⟨W, hx, g, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y'.presheaf z
  have h1 : ((derivationActionPshHom hsq θ comm_a).stalkMap x).hom
        (Y'.presheaf.germ W _ hx g)
      = X'.presheaf.germ (a' ⁻¹ᵁ W) x hx (derivationActionApp hsq θ comm_a W g) :=
    PresheafedSpace.stalkMap_germ_apply (derivationActionPshHom hsq θ comm_a) W x hx g
  have h2 : (a'.toLRSHom.stalkMap x).hom (Y'.presheaf.germ W _ hx g)
      = X'.presheaf.germ (a' ⁻¹ᵁ W) x hx ((a'.app W).hom g) :=
    Scheme.Hom.germ_stalkMap_apply a' W x hx g
  rw [h1, h2, derivationActionApp_apply, Scheme.Hom.appLE_eq_app, map_add,
    add_sub_cancel_left]
  refine ⟨2, ?_⟩
  rw [pow_two, ← map_mul, derivationSection_mul_derivationSection, map_zero]

/-- **A ring homomorphism differing from a local one by nilpotent elements is local.** Adding a
nilpotent element to a unit gives a unit, so the two homomorphisms invert the same elements. -/
private theorem isLocalHom_of_isNilpotent_sub {R T : Type u} [CommRing R] [CommRing T]
    (φ ψ : R →+* T) (hψ : IsLocalHom ψ) (h : ∀ z, IsNilpotent (φ z - ψ z)) : IsLocalHom φ := by
  refine ⟨fun z hz => hψ.map_nonunit z ?_⟩
  have hu := (IsNilpotent.neg (h z)).isUnit_add_left_of_commute hz (Commute.all _ _)
  have key : φ z + -(φ z - ψ z) = ψ z := by ring
  rwa [key] at hu

/-- **The stalk maps of `Stacks.Thickenings.derivationActionPshHom` are local**, so that it is a
morphism of locally ringed spaces: a unit stays a unit when a nilpotent element is added, so the
locality of the stalk maps of `a'` is inherited. -/
theorem isLocalHom_stalkMap_derivationActionPshHom (x : X') :
    IsLocalHom ((derivationActionPshHom hsq θ comm_a).stalkMap x).hom :=
  isLocalHom_of_isNilpotent_sub _ ((a'.toLRSHom.stalkMap x)).hom (a'.toLRSHom.prop x)
    (isNilpotent_stalkMap_sub hsq θ comm_a x)

/-- **The lift modified by a derivation.** The morphism `b' : X' ⟶ Y'` of
[Stacks Project, Tag 02H5]: it has the same underlying continuous map as `a'`, and its
comorphism is `(a')^♯ + D` for `D = θ ∘ d_{Y/S}`. In the notation of
[Stacks Project, Tag 0CK1] this is `θ ⬝ a'`. -/
noncomputable def derivationActionGlobal : X' ⟶ Y' :=
  Scheme.Hom.mk ⟨derivationActionPshHom hsq θ comm_a,
    isLocalHom_stalkMap_derivationActionPshHom hsq θ comm_a⟩

/-- `Stacks.Thickenings.derivationActionGlobal` has the same underlying map as `a'`. -/
@[simp]
theorem derivationActionGlobal_base :
    (derivationActionGlobal hsq θ comm_a).base = a'.base :=
  rfl

/-- `Stacks.Thickenings.derivationActionGlobal` has the same preimages as `a'`. -/
@[simp]
theorem derivationActionGlobal_preimage (W : Y'.Opens) :
    derivationActionGlobal hsq θ comm_a ⁻¹ᵁ W = a' ⁻¹ᵁ W :=
  rfl

/-- **The comorphism of `Stacks.Thickenings.derivationActionGlobal`** is `(a')^♯ + D`. -/
theorem derivationActionGlobal_app (W : Y'.Opens) (g : Γ(Y', W)) :
    ((derivationActionGlobal hsq θ comm_a).app W).hom g = (a'.app W).hom g
      + derivationSection hsq θ W (a' ⁻¹ᵁ W) (preimage_le_of_comm comm_a le_rfl) g := by
  change derivationActionApp hsq θ comm_a W g = _
  rw [derivationActionApp_apply, Scheme.Hom.appLE_eq_app]

/-- **Equation [Stacks Project, Tag 04BV] for the modified lift**, over an arbitrary pair of
opens: the comorphisms of `θ ⬝ a'` and of `a'` over an open `W` of `Y'` and an open `V` of `X'`
mapping into `W` differ by `D = θ ∘ d_{Y/S}`. -/
theorem derivationActionGlobal_appLE (W : Y'.Opens) (V : X'.Opens) (hA : V ≤ a' ⁻¹ᵁ W)
    (g : Γ(Y', W)) :
    ((derivationActionGlobal hsq θ comm_a).appLE W V hA).hom g = (a'.appLE W V hA).hom g
      + derivationSection hsq θ W V (preimage_le_of_comm comm_a hA) g := by
  have h1 : ((derivationActionGlobal hsq θ comm_a).appLE W V hA).hom g
      = (X'.presheaf.map (homOfLE hA).op).hom
        (((derivationActionGlobal hsq θ comm_a).app W).hom g) := rfl
  have h2 : (a'.appLE W V hA).hom g
      = (X'.presheaf.map (homOfLE hA).op).hom ((a'.app W).hom g) := rfl
  rw [h1, h2, derivationActionGlobal_app, map_add,
    map_derivationSection W hA (preimage_le_of_comm comm_a le_rfl)
      (preimage_le_of_comm comm_a hA) g]

/-- Two morphisms of schemes with the same underlying map are equal if their comorphisms agree
elementwise, up to the identification of the two preimages of an open. -/
private theorem hom_eq_of_base_eq_of_app_heq {A B : Scheme.{u}} {f g : A ⟶ B}
    (hb : f.base = g.base)
    (h : ∀ (W : B.Opens) (r : Γ(B, W)), HEq ((f.app W).hom r) ((g.app W).hom r)) : f = g := by
  refine Scheme.Hom.ext hb fun W => CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  have key : ∀ (U V : A.Opens) (e : V = U) (x : Γ(A, U)) (y : Γ(A, V)), HEq x y →
      (A.presheaf.map (eqToHom e).op).hom x = y := by
    rintro U V rfl x y hxy
    simpa using eq_of_heq hxy
  exact key _ _ _ _ _ (h W r)

/-- **The modified lift is again a lift of `a`**, which is condition (1) of
[Stacks Project, Tag 04FG] for the pair `(a', b')`: it is a morphism of thickenings from
`i : X ⟶ X'` to `j : Y ⟶ Y'` whose restriction to the closed subschemes is the same `a`. The
perturbation `D` takes values in the defining ideal of `i`, so it disappears on `X`. -/
theorem comm_derivationActionGlobal :
    i ≫ derivationActionGlobal hsq θ comm_a = a ≫ j := by
  have key : i ≫ derivationActionGlobal hsq θ comm_a = i ≫ a' := by
    refine hom_eq_of_base_eq_of_app_heq (by exact rfl) fun W g => heq_of_eq ?_
    change (i.app (a' ⁻¹ᵁ W)).hom (((derivationActionGlobal hsq θ comm_a).app W).hom g)
      = (i.app (a' ⁻¹ᵁ W)).hom ((a'.app W).hom g)
    rw [derivationActionGlobal_app, map_add,
      RingHom.mem_ker.mp (derivationSection_mem_ker W (a' ⁻¹ᵁ W)
        (preimage_le_of_comm comm_a le_rfl) g), add_zero]
  rw [key, comm_a]

/-- **The modified lift is again a morphism over `S`.** The perturbation `D` kills the sections
pulled back from `S`, because a derivation is `𝒪_S`-linear. -/
theorem comp_derivationActionGlobal (ha' : a' ≫ q = p) :
    derivationActionGlobal hsq θ comm_a ≫ q = p := by
  have key : derivationActionGlobal hsq θ comm_a ≫ q = a' ≫ q := by
    refine hom_eq_of_base_eq_of_app_heq (by exact rfl) fun W₀ r => heq_of_eq ?_
    change ((derivationActionGlobal hsq θ comm_a).app (q ⁻¹ᵁ W₀)).hom ((q.app W₀).hom r)
      = (a'.app (q ⁻¹ᵁ W₀)).hom ((q.app W₀).hom r)
    rw [derivationActionGlobal_app,
      show (q.app W₀).hom r = (q.appLE W₀ (q ⁻¹ᵁ W₀) le_rfl).hom r from
        congrArg (fun z : Γ(S, W₀) ⟶ Γ(Y', q ⁻¹ᵁ W₀) => z.hom r)
          (Scheme.Hom.appLE_eq_app q).symm,
      derivationSection_appLE (q ⁻¹ᵁ W₀) (a' ⁻¹ᵁ (q ⁻¹ᵁ W₀))
        (preimage_le_of_comm comm_a le_rfl) le_rfl r, add_zero]
  rw [key, ha']

/-- **The perturbation kills the defining ideal of `j`**, since the universal differential of
`Ω_{Y/S}` is applied to the image of the section under `j^♯`. -/
theorem derivationSection_eq_zero_of_app_eq_zero (W : Y'.Opens) (V : X'.Opens)
    (hU : i ⁻¹ᵁ V ≤ a ⁻¹ᵁ (j ⁻¹ᵁ W)) (g : Γ(Y', W)) (hg : (j.app W).hom g = 0) :
    derivationSection hsq θ W V hU g = 0 :=
  derivationSection_eq_zero_of_mem_ker W V hU hg

/-- Two restriction maps along morphisms of opens with the same source and target agree: the
opens of a scheme form a poset, so there is at most one morphism between two of them. -/
private theorem presheaf_map_subsingleton {Z : Scheme.{u}} {A B : Z.Opens} (ζ ξ : A ⟶ B) :
    Z.presheaf.map ζ.op = Z.presheaf.map ξ.op :=
  congrArg (fun z : A ⟶ B => Z.presheaf.map z.op) (Subsingleton.elim ζ ξ)

/-- **Uniqueness of the modified lift.** A lift of `a` over `S` whose comorphism differs from
that of `a'` by `D = θ ∘ d_{Y/S}` is `Stacks.Thickenings.derivationActionGlobal`: the two
morphisms have the same underlying map, and their comorphisms agree over every open. -/
theorem eq_derivationActionGlobal {c : X' ⟶ Y'} (comm_c : i ≫ c = a ≫ j)
    (hD : ∀ (W : Y'.Opens) (V : X'.Opens) (hA : V ≤ a' ⁻¹ᵁ W) (g : Γ(Y', W)),
      (c.appLE W V (le_preimage_of_comm hsq comm_a comm_c hA)).hom g = (a'.appLE W V hA).hom g
        + derivationSection hsq θ W V (preimage_le_of_comm comm_a hA) g) :
    c = derivationActionGlobal hsq θ comm_a := by
  refine Scheme.Hom.ext ((base_eq_of_comm hsq comm_a comm_c).trans
    (derivationActionGlobal_base hsq θ comm_a).symm) fun W => ?_
  refine CommRingCat.hom_ext (RingHom.ext fun g => ?_)
  have hmap : ∀ ζ : derivationActionGlobal hsq θ comm_a ⁻¹ᵁ W ⟶ c ⁻¹ᵁ W,
      (X'.presheaf.map ζ.op).hom ((c.app W).hom g)
        = (c.appLE W (a' ⁻¹ᵁ W) (le_preimage_of_comm hsq comm_a comm_c le_rfl)).hom g := by
    intro ζ
    rw [presheaf_map_subsingleton ζ
      (homOfLE (le_preimage_of_comm hsq comm_a comm_c (le_refl (a' ⁻¹ᵁ W))))]
    rfl
  refine Eq.trans (hmap _) ?_
  rw [hD W (a' ⁻¹ᵁ W) le_rfl g, derivationActionGlobal_app, Scheme.Hom.appLE_eq_app]

/-- **A derivation acts in exactly one way on a lift of a map**, [Stacks Project, Tag 02H5].
Let `S` be a scheme, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings, let
`p : X' ⟶ S` and `q : Y' ⟶ S` be the structure morphisms, and let `(a, a')` be a morphism of
thickenings `(X ⊂ X') ⟶ (Y ⊂ Y')` over `S`. Then for every `𝒪_X`-linear map
`θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` there is exactly one morphism `b' : X' ⟶ Y'` such that `(a, b')` is
again a morphism of thickenings over `S` — conditions (1) and (2) of
[Stacks Project, Tag 04FG] for the pair `(a', b')` — and the derivation `D` of
[Stacks Project, Tag 04FG] attached to the pair is related to `θ` by Equation
[Stacks Project, Tag 04BV], `D = θ ∘ d_{Y/S}`.

Nothing is affine, and the datum is the one of the source: a morphism of sheaves of
`𝒪_X`-modules out of the pulled-back sheaf of relative differentials.

Tag 04FG numbers two conditions; with Equation 04BV they make the three requirements written out
on sections below. Condition (1), that the two reductions agree,
is `comm_b : i ≫ b' = a ≫ j`, the same `a` as for `a'`; that `b'` is a morphism over `S` is
`b' ≫ q = p`. Condition (2), that the two induced maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of
[Stacks Project, Tag 01R4] agree, is the first conjunct: for a first-order thickening `j` the
conormal sheaf `𝒞_{Y/Y'}` *is* the defining ideal of `j` and the induced map is the comorphism,
so the condition says that `(a')^♯` and `(b')^♯` agree on the sections killed by `j^♯`. Equation
[Stacks Project, Tag 04BV] is the second conjunct: the difference `(b')^♯ - (a')^♯`, which is the
derivation `D` of [Stacks Project, Tag 04FG] read through the inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` of
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`, is `θ` applied to the pulled-back
universal differential `Stacks.Smooth.pullbackD`.

Because `d_{Y/S}` kills `j^♯` of a section of the defining ideal of `j`, the second conjunct
implies the first, so the morphism characterised here is the same whether condition (2) is read
as above or as the equality of the two maps of conormal sheaves. For the same reason `j` need
only be a morphism of schemes: the source asks it to be a first-order thickening, and at that
hypothesis the first conjunct is exactly its condition (2), since `𝒞_{Y/Y'}` is then the
defining ideal of `j` and the map of [Stacks Project, Tag 01R4] is the comorphism. -/
@[stacks 02H5, sga "3 III 4.9" "Perturbation clause"]
theorem existsUnique_derivationActionGlobal (ha' : a' ≫ q = p) :
    ∃! b' : X' ⟶ Y', ∃ (comm_b : i ≫ b' = a ≫ j) (_ : b' ≫ q = p),
      (∀ (W : Y'.Opens) (V : X'.Opens) (hA : V ≤ a' ⁻¹ᵁ W) (g : Γ(Y', W)),
          (j.app W).hom g = 0 →
            (b'.appLE W V (le_preimage_of_comm hsq comm_a comm_b hA)).hom g
              = (a'.appLE W V hA).hom g)
        ∧ ∀ (W : Y'.Opens) (V : X'.Opens) (hA : V ≤ a' ⁻¹ᵁ W) (g : Γ(Y', W)),
            (b'.appLE W V (le_preimage_of_comm hsq comm_a comm_b hA)).hom g
              = (a'.appLE W V hA).hom g
                + derivationSection hsq θ W V (preimage_le_of_comm comm_a hA) g := by
  refine ⟨derivationActionGlobal hsq θ comm_a, ⟨comm_derivationActionGlobal hsq θ comm_a,
    comp_derivationActionGlobal hsq θ comm_a ha', fun W V hA g hg => ?_,
    fun W V hA g => derivationActionGlobal_appLE hsq θ comm_a W V hA g⟩, fun c hc => ?_⟩
  · have h := derivationActionGlobal_appLE hsq θ comm_a W V hA g
    rw [derivationSection_eq_zero_of_app_eq_zero hsq θ W V (preimage_le_of_comm comm_a hA) g hg,
      add_zero] at h
    exact h
  · obtain ⟨comm_c, -, -, hD⟩ := hc
    exact eq_derivationActionGlobal hsq θ comm_a comm_c hD

end Construction

end Stacks.Thickenings

end
