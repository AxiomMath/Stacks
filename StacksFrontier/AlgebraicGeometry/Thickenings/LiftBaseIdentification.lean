module

public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Two lifts of a map along a thickening agree on underlying spaces

Let `i : X ⟶ X'` be a thickening and let `j : Y ⟶ Y'` be any morphism. If `a' b' : X' ⟶ Y'`
both lift one and the same `a : X ⟶ Y`, in the sense that `i ≫ a' = a ≫ j = i ≫ b'`, then `a'`
and `b'` have the same underlying continuous map, and hence the same preimage of every open of
`Y'`.

Over `⊤` nothing needs to be identified, because `f ⁻¹ᵁ ⊤ = ⊤` for every `f`. Over a general
open `V` of `Y'` the two sections `a'.app V x` and `b'.app V x` live in `Γ(X', a' ⁻¹ᵁ V)` and
`Γ(X', b' ⁻¹ᵁ V)`, which are not the same group until those two opens are identified. With this
identification the difference of the two comorphisms is defined over every open of `Y'`.

## Main definitions

* `Stacks.Thickenings.mapDifferenceApp`: the difference of the two comorphisms over an open `V`
  of `Y'`, a section of the defining ideal of `i` over `a' ⁻¹ᵁ V`.

## Main results

* `Stacks.Thickenings.base_apply_eq_of_comm`: the two lifts agree at every point.
* `Stacks.Thickenings.base_eq_of_comm_of_surjective`: the two lifts have equal underlying
  continuous maps.
* `Stacks.Thickenings.preimage_eq_of_comm_of_surjective`: the two lifts have equal preimages of
  every open.
* `Stacks.Thickenings.IsThickening.preimage_eq_of_comm` and
  `Stacks.Thickenings.IsFirstOrderThickening.preimage_eq_of_comm`: the same with the surjectivity
  hypothesis read off a thickening.
* `Stacks.Thickenings.mapDifferenceApp_add`, `Stacks.Thickenings.mapDifferenceApp_res`,
  `Stacks.Thickenings.mapDifferenceApp_leibniz` and
  `Stacks.Thickenings.mapDifferenceApp_base_eq_zero`: the difference is additive, compatible with
  restriction, satisfies the Leibniz rule and vanishes on sections coming from the base.

## Implementation notes

Only surjectivity of the underlying map of `i` is used — not that `i` is a closed immersion, and
not the square-zero condition. The hypothesis is therefore stated as
`Function.Surjective i.base` rather than as `Stacks.Thickenings.IsThickening i`, and the two
thickening-flavoured corollaries supply it from `Stacks.Thickenings.IsThickening.2` and from
`Stacks.Thickenings.IsFirstOrderThickening.isThickening`.

Nothing here identifies the two *schemes* `X` and `X'`, or the two *lifts* `a'` and `b'` — the
lifts are genuinely different morphisms, and their difference is the content of
[Stacks Project, Tag 04FG]. What is identified is only the data on which the pushforward functors
`a'_*` and `b'_*` depend, namely the continuous maps.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}}

/-- **Two lifts of the same map along a surjection agree at every point.** If `i ≫ a' = a ≫ j`
and `i ≫ b' = a ≫ j` with `i` surjective on points, then `a'` and `b'` agree on points. -/
theorem base_apply_eq_of_comm {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'}
    (hi : Function.Surjective i.base) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (x : X') : a'.base x = b'.base x := by
  obtain ⟨y, rfl⟩ := hi x
  simpa using congr(($(comm_a.trans comm_b.symm)).base y)

/-- **Two lifts of the same map along a surjection have the same underlying continuous map.** -/
theorem base_eq_of_comm_of_surjective {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'}
    (hi : Function.Surjective i.base) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) :
    a'.base = b'.base := by
  ext x
  exact base_apply_eq_of_comm hi comm_a comm_b x

/-- **Two lifts of the same map along a surjection have the same preimage of every open.** -/
theorem preimage_eq_of_comm_of_surjective {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'}
    (hi : Function.Surjective i.base) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (V : Y'.Opens) : a' ⁻¹ᵁ V = b' ⁻¹ᵁ V :=
  congrArg (fun g => (Opens.map g).obj V) (base_eq_of_comm_of_surjective hi comm_a comm_b)

/-- **Two lifts of the same map along a thickening have the same preimage of every open**, the
surjectivity hypothesis of `Stacks.Thickenings.preimage_eq_of_comm_of_surjective` being part of
`Stacks.Thickenings.IsThickening`. -/
theorem IsThickening.preimage_eq_of_comm {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' b' : X' ⟶ Y'} (hi : IsThickening i) (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) : a' ⁻¹ᵁ V = b' ⁻¹ᵁ V :=
  Stacks.Thickenings.preimage_eq_of_comm_of_surjective hi.2 comm_a comm_b V

/-- **Two lifts of the same map along a first-order thickening have the same preimage of every
open.** -/
theorem IsFirstOrderThickening.preimage_eq_of_comm {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' b' : X' ⟶ Y'} (hi : IsFirstOrderThickening i) (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) : a' ⁻¹ᵁ V = b' ⁻¹ᵁ V :=
  Stacks.Thickenings.preimage_eq_of_comm_of_surjective hi.isThickening.2 comm_a comm_b V

/-! ### The difference of two lifts over an arbitrary open -/

section Difference

variable {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'}

/-- **The second lift's comorphism, read on the first lift's preimage.** The two lifts have the
same preimage of `V` by `Stacks.Thickenings.preimage_eq_of_comm_of_surjective`, so `b'.app V` may
be read as a map into `Γ(X', a' ⁻¹ᵁ V)`, the target of `a'.app V`. -/
noncomputable def secondLiftAppLE (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) :
    Γ(Y', V) ⟶ Γ(X', a' ⁻¹ᵁ V) :=
  b'.appLE V (a' ⁻¹ᵁ V) (le_of_eq (preimage_eq_of_comm_of_surjective hi comm_a comm_b V))

/-- **Both comorphisms reduce to the comorphism of `a ≫ j`.** Composing either lift's comorphism
over `V` with that of `i` gives the comorphism of `i ≫ a' = a ≫ j = i ≫ b'`, so the two agree
after restriction to `X`. This is the arbitrary-open form of
`Stacks.Thickenings.appTop_comm_of_comm`. -/
theorem secondLiftAppLE_comm_of_comm (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) :
    a'.appLE V (a' ⁻¹ᵁ V) le_rfl ≫ i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl =
      secondLiftAppLE hi comm_a comm_b V ≫ i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl := by
  have hle : i ⁻¹ᵁ a' ⁻¹ᵁ V ≤ (a ≫ j) ⁻¹ᵁ V := by rw [← comm_a]; exact le_rfl
  rw [secondLiftAppLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_congr_hom comm_a V (i ⁻¹ᵁ a' ⁻¹ᵁ V) _ hle,
    Scheme.Hom.appLE_congr_hom comm_b V (i ⁻¹ᵁ a' ⁻¹ᵁ V) _ hle]

/-- **The difference of two lifts of a map, over an arbitrary open.** Given two morphisms of
thickenings `(a, a')` and `(a, b')` from `i : X ⟶ X'` to `j : Y ⟶ Y'` with the same reduction
`a`, the difference of the two comorphisms over `V` lies in the defining ideal of `i` over
`a' ⁻¹ᵁ V`, because both comorphisms reduce to the comorphism of `a ≫ j` by
`Stacks.Thickenings.secondLiftAppLE_comm_of_comm`.

Over `V = ⊤` this is `Stacks.Thickenings.mapDifference`, which needs no surjectivity hypothesis
because `f ⁻¹ᵁ ⊤ = ⊤` already gives the two comorphisms a common target. -/
noncomputable def mapDifferenceApp (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x : Γ(Y', V)) :
    RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom :=
  ⟨(a'.appLE V (a' ⁻¹ᵁ V) le_rfl).hom x - (secondLiftAppLE hi comm_a comm_b V).hom x, by
    have h := ConcreteCategory.congr_hom (secondLiftAppLE_comm_of_comm hi comm_a comm_b V) x
    simp only [ConcreteCategory.comp_apply] at h
    rw [RingHom.mem_ker, map_sub, h, sub_self]⟩

/-- The underlying section of `Stacks.Thickenings.mapDifferenceApp`. -/
@[simp]
theorem mapDifferenceApp_coe (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x : Γ(Y', V)) :
    ((mapDifferenceApp hi comm_a comm_b V x :
        RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
      = (a'.appLE V (a' ⁻¹ᵁ V) le_rfl).hom x - (secondLiftAppLE hi comm_a comm_b V).hom x :=
  rfl

/-- `Stacks.Thickenings.mapDifferenceApp` is additive. -/
theorem mapDifferenceApp_add (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x y : Γ(Y', V)) :
    mapDifferenceApp hi comm_a comm_b V (x + y)
      = mapDifferenceApp hi comm_a comm_b V x + mapDifferenceApp hi comm_a comm_b V y :=
  Subtype.ext (by
    rw [mapDifferenceApp_coe, AddMemClass.coe_add, mapDifferenceApp_coe, mapDifferenceApp_coe,
      map_add, map_add]
    ring)

/-- `Stacks.Thickenings.mapDifferenceApp` takes differences to differences. -/
theorem mapDifferenceApp_sub (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x y : Γ(Y', V)) :
    mapDifferenceApp hi comm_a comm_b V (x - y)
      = mapDifferenceApp hi comm_a comm_b V x - mapDifferenceApp hi comm_a comm_b V y :=
  Subtype.ext (by
    rw [mapDifferenceApp_coe, AddSubgroupClass.coe_sub, mapDifferenceApp_coe,
      mapDifferenceApp_coe, map_sub, map_sub]
    ring)

/-- **The difference of two lifts vanishes at `1`**: both comorphisms are ring maps. -/
theorem mapDifferenceApp_one (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) :
    mapDifferenceApp hi comm_a comm_b V 1 = 0 :=
  Subtype.ext (by
    rw [mapDifferenceApp_coe, ZeroMemClass.coe_zero, map_one, map_one, sub_self])

/-- **The difference of two lifts is compatible with restriction.** Restricting the difference
over `V` to `a' ⁻¹ᵁ W` gives the difference over `W` of the restricted section. -/
theorem mapDifferenceApp_res (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) {V W : Y'.Opens} (hWV : W ≤ V)
    (x : Γ(Y', V)) :
    (X'.presheaf.map (homOfLE (a'.preimage_mono hWV)).op).hom
        ((mapDifferenceApp hi comm_a comm_b V x :
          RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
      = ((mapDifferenceApp hi comm_a comm_b W ((Y'.presheaf.map (homOfLE hWV).op).hom x) :
          RingHom.ker (i.appLE (a' ⁻¹ᵁ W) (i ⁻¹ᵁ a' ⁻¹ᵁ W) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ W)) := by
  rw [mapDifferenceApp_coe, mapDifferenceApp_coe, map_sub, secondLiftAppLE, secondLiftAppLE,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]

/-- **The Leibniz rule for the difference of two lifts, over an arbitrary open.** With scalars
acting through the second lift,
`D(xy) = b'(x) D(y) + b'(y) D(x)`. This is where the square-zero condition on the defining ideal
of `i` enters: the cross term is the product of the two differences, which are both sections of
that ideal, so it vanishes by `Stacks.Thickenings.mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot`. -/
theorem mapDifferenceApp_leibniz [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) (x y : Γ(Y', V)) :
    ((mapDifferenceApp hi comm_a comm_b V (x * y) :
        RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
      = (secondLiftAppLE hi comm_a comm_b V).hom x
          * ((mapDifferenceApp hi comm_a comm_b V y :
              RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
        + (secondLiftAppLE hi comm_a comm_b V).hom y
          * ((mapDifferenceApp hi comm_a comm_b V x :
              RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) :
                Γ(X', a' ⁻¹ᵁ V)) := by
  have hker : ∀ z : Γ(Y', V),
      ((mapDifferenceApp hi comm_a comm_b V z :
          RingHom.ker (i.appLE (a' ⁻¹ᵁ V) (i ⁻¹ᵁ a' ⁻¹ᵁ V) le_rfl).hom) : Γ(X', a' ⁻¹ᵁ V))
        ∈ RingHom.ker (i.app (a' ⁻¹ᵁ V)).hom := by
    intro z
    rw [RingHom.mem_ker, ← Scheme.Hom.appLE_eq_app]
    exact (mapDifferenceApp hi comm_a comm_b V z).2
  have hz := mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot i hsq (a' ⁻¹ᵁ V) _ _
    (RingHom.mem_ker.mp (hker x)) (RingHom.mem_ker.mp (hker y))
  rw [mapDifferenceApp_coe, mapDifferenceApp_coe, mapDifferenceApp_coe, map_mul, map_mul]
  simp only [mapDifferenceApp_coe] at hz
  linear_combination hz

/-- **The difference of two lifts kills the sections pulled back from the base, over an
arbitrary open.** If both lifts are morphisms over `S`, in the sense that `a' ≫ q = p` and
`b' ≫ q = p` for structure morphisms `p : X' ⟶ S` and `q : Y' ⟶ S`, then the difference
vanishes on every section of `𝒪_{Y'}` that comes from a section of `𝒪_S`. This is the
`𝒪_S`-linearity of the difference; neither a thickening hypothesis nor the square-zero condition
is needed. -/
theorem mapDifferenceApp_base_eq_zero (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) {p : X' ⟶ S} {q : Y' ⟶ S}
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) {W : S.Opens} {V : Y'.Opens} (hV : V ≤ q ⁻¹ᵁ W)
    (r : Γ(S, W)) :
    mapDifferenceApp hi comm_a comm_b V ((q.appLE W V hV).hom r) = 0 := by
  have hp : a' ⁻¹ᵁ V ≤ p ⁻¹ᵁ W := by
    rw [← ha']
    exact a'.preimage_mono hV
  have hcomm : q.appLE W V hV ≫ a'.appLE V (a' ⁻¹ᵁ V) le_rfl =
      q.appLE W V hV ≫ secondLiftAppLE hi comm_a comm_b V := by
    rw [secondLiftAppLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_congr_hom ha' W _ _ hp, Scheme.Hom.appLE_congr_hom hb' W _ _ hp]
  refine Subtype.ext ?_
  have h := ConcreteCategory.congr_hom hcomm r
  simp only [ConcreteCategory.comp_apply] at h
  rw [mapDifferenceApp_coe, ZeroMemClass.coe_zero, h, sub_self]

/-- **The difference of two lifts kills the image of the comorphism of the structure morphism
of the base.** This is `Stacks.Thickenings.mapDifferenceApp_base_eq_zero` at `V = q ⁻¹ᵁ W`. -/
theorem mapDifferenceApp_base_app_eq_zero (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) {p : X' ⟶ S} {q : Y' ⟶ S}
    (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) (W : S.Opens) (r : Γ(S, W)) :
    mapDifferenceApp hi comm_a comm_b (q ⁻¹ᵁ W) ((q.app W).hom r) = 0 := by
  rw [Scheme.Hom.app_eq_appLE]
  exact mapDifferenceApp_base_eq_zero hi comm_a comm_b ha' hb' le_rfl r

end Difference

end Stacks.Thickenings

end
