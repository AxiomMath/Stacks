module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeilCohomologyTheory
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity

/-!
# Proper pushforward on the Chow groups `CH^i(X)` of equidimensional smooth schemes

The groups `CH^i(X) = ∏_d CH_{d-i}(X_d)` of codimension-`i` cycles of a scheme `X` smooth over a
field `k` (`Stacks.Chow.codimensionChowGroup`) carry the proper pushforward
`f_* : CH^r(X) → CH^s(Y)` of `Stacks.WeilCohomology.chowCodimPushforward`, read through the maps
`chowCodimTotal : CH^i(X) → CH_n(X)` and `chowCodimPart : ∏_n CH_n(Y) → CH^j(Y)`. This file
records the bookkeeping that Section 45.14 of the Stacks Project (Tag 0FID) uses without comment
when it pushes cycle classes forward:

* `f_*` is additive (`Stacks.WeilDeRham.chowCodimPushforwardHom`);
* when `X` is equidimensional of dimension `d` (relative dimension `d` over `k`), the part `X_d`
  is all of `X` and the other parts are empty, so a codimension-`i` class lives in the single
  dimension `d - i`, and `chowCodimTotal`, `chowCodimPart` are mutually inverse there.

## Main results

* `Stacks.WeilDeRham.chowCodimTotal_chowCodimPart`,
  `Stacks.WeilDeRham.chowCodimPart_chowCodimTotal`: `chowCodimTotal` and `chowCodimPart` are
  inverse to each other in the right degree.
* `Stacks.WeilDeRham.properChowPushforward_dimPart_eq_chowCodimTotal`: pushing the
  `X_d`-coordinate of `α ∈ CH^i(X)` forward to `X` gives the class `α_{(d-i)}`.

## References

* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Section 0FE2](https://stacks.math.columbia.edu/tag/0FE2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow Stacks.WeilCohomology

universe u

namespace Stacks.WeilDeRham

/-! ### The parts of an equidimensional smooth scheme -/

section Parts

variable {X S : Scheme.{u}} (sX : X ⟶ S) [Smooth sX]

end Parts

/-! ### `chowCodimTotal` and `chowCodimPart` on an equidimensional scheme -/

section Codim

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]
  (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sZ]

/-- The codimension-`j` part of a family of classes is additive in the family. -/
theorem chowCodimPart_add (β β' : ∀ n : ℤ, chowGroup (fieldChowSituation k) sX n) (j : ℕ) :
    chowCodimPart k sX (β + β') j = chowCodimPart k sX β j + chowCodimPart k sX β' j := by
  funext d
  simp [chowCodimPart, map_add]

/-- The codimension-`j` part of the zero family is zero. -/
theorem chowCodimPart_zero (j : ℕ) : chowCodimPart k sX 0 j = 0 := by
  funext d
  simp [chowCodimPart]

/-- **`chowCodimPart ∘ chowCodimTotal = id`** on `CH^i(X)`, for any `X` smooth over `k`: the
`X_d`-coordinate of the codimension-`i` part of the classes `α_{(n)}` is `α_d`. -/
theorem chowCodimPart_chowCodimTotal (i : ℕ) (α : codimensionChowGroup k sX i) :
    chowCodimPart k sX (fun n ↦ chowCodimTotal k sX i n α) i = α := by
  funext d
  have h := congrFun ((chowGroupDimPartEquiv k sX ((d : ℤ) - i)).apply_symm_apply
    fun d' : ULift.{u} ℕ ↦ if h : (d'.down : ℤ) - i = (d : ℤ) - i then
      chowGroupDegreeEquiv (fieldChowSituation k) _ h (α d'.down) else 0) ⟨d⟩
  rw [chowGroupDimPartEquiv_apply, dite_eq_left rfl] at h
  exact h

/-- On `X` equidimensional of dimension `d`, the Chow groups of the part `X_{d'}` with `d' ≠ d`
are subsingletons. -/
private theorem chowGroup_partBase_eq_of_ne {d d' : ℕ} (hX : RelativeDimension sX d)
    (hd' : d' ≠ d) (n : ℤ) (x y : chowGroup (fieldChowSituation k) (partBase sX d') n) : x = y :=
  have := isEmpty_dimPart_of_ne sX hX hd'
  (subsingleton_chowGroup_of_isEmpty _ _ _).elim _ _

/-- On `X` equidimensional of dimension `d`, a codimension-`i` class has no component in
dimensions `n ≠ d - i`: `α_{(n)} = 0`. -/
theorem chowCodimTotal_eq_zero_of_ne {d : ℕ} (hX : RelativeDimension sX d) (i : ℕ) {n : ℤ}
    (hn : n ≠ (d : ℤ) - i) (α : codimensionChowGroup k sX i) : chowCodimTotal k sX i n α = 0 := by
  refine (chowGroupDimPartEquiv k sX n).injective (funext fun d' ↦ ?_)
  change chowGroupDimPartEquiv k sX n ((chowGroupDimPartEquiv k sX n).symm _) d' = _
  rw [AddEquiv.apply_symm_apply, map_zero]
  split_ifs with h
  · have hd' : d'.down ≠ d := fun h' ↦ hn (by rw [← h, h'])
    exact chowGroup_partBase_eq_of_ne k sX hX hd' n _ _
  · rfl

/-- **`chowCodimTotal ∘ chowCodimPart = id` in the degree of `Y`**: on `Y` equidimensional of
dimension `e`, the class in dimension `n = e - j` of the codimension-`j` part of a family
`β_n ∈ CH_n(Y)` is `β_n`. -/
theorem chowCodimTotal_chowCodimPart {e : ℕ} (hY : RelativeDimension sY e) (j : ℕ) {n : ℤ}
    (hn : (e : ℤ) - j = n) (β : ∀ n : ℤ, chowGroup (fieldChowSituation k) sY n) :
    chowCodimTotal k sY j n (chowCodimPart k sY β j) = β n := by
  refine (chowGroupDimPartEquiv k sY n).injective (funext fun d' ↦ ?_)
  change chowGroupDimPartEquiv k sY n ((chowGroupDimPartEquiv k sY n).symm _) d' = _
  rw [AddEquiv.apply_symm_apply, chowGroupDimPartEquiv_apply]
  by_cases hd' : d'.down = e
  · have h : (d'.down : ℤ) - j = n := by rw [hd', hn]
    rw [dite_eq_left h]
    subst h
    rfl
  · exact chowGroup_partBase_eq_of_ne k sY hY hd' n _ _

/-- **The pushforward of the `X_d`-coordinate of `α ∈ CH^i(X)` is `α_{(d-i)}`**: pushing `α_d`
forward along the inclusion of the part `X_d` gives the class in dimension `d - i` of `α`, for
any `X` smooth over `k`. -/
theorem properChowPushforward_dimPart_eq_chowCodimTotal (i : ℕ) (d : ℕ)
    [IsProper (dimPart sX d).ι] (α : codimensionChowGroup k sX i) :
    properChowPushforward (fieldChowSituation k) (partBase sX d) sX (dimPart sX d).ι rfl
        ((d : ℤ) - i) (properPushforwardDescends _ _ _ _ _ _) (α d) =
      chowCodimTotal k sX i ((d : ℤ) - i) α := by
  refine (chowGroupDimPartEquiv k sX ((d : ℤ) - i)).injective (funext fun d' ↦ ?_)
  change _ = chowGroupDimPartEquiv k sX _ ((chowGroupDimPartEquiv k sX _).symm _) d'
  rw [AddEquiv.apply_symm_apply, chowGroupDimPartEquiv_apply]
  by_cases hd' : d'.down = d
  · obtain ⟨d''⟩ := d'
    obtain rfl : d'' = d := hd'
    rw [dite_eq_left rfl]
    exact chowGroupRestrict_properChowPushforward_opens_self _ _ _ _ _ _
  · rw [dite_eq_right (fun h ↦ hd' (by exact_mod_cast (sub_left_inj.mp h)))]
    exact chowGroupRestrict_properChowPushforward_opens_of_disjoint _ _ _ _
      ((isClopenDecomposition_dimPart sX).disjoint d d'.down (Ne.symm hd')) _ _ _

/-! ### Additivity -/

/-- **The proper pushforward `f_* : CH^r(X) → CH^s(Y)` as an additive map.** -/
def chowCodimPushforwardHom (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r s : ℕ) :
    codimensionChowGroup k sX r →+ codimensionChowGroup k sY s where
  toFun := chowCodimPushforward k sX sY f hf r s
  map_zero' := by
    simp only [chowCodimPushforward, map_zero]
    exact chowCodimPart_zero k sY s
  map_add' α β := by
    simp only [chowCodimPushforward, map_add]
    exact chowCodimPart_add k sY _ _ s

/-- `chowCodimPushforwardHom` is `chowCodimPushforward`. -/
@[simp]
theorem chowCodimPushforwardHom_apply (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r s : ℕ)
    (α : codimensionChowGroup k sX r) :
    chowCodimPushforwardHom k sX sY f hf r s α = chowCodimPushforward k sX sY f hf r s α :=
  rfl

/-- `f_*(-α) = -f_*α`. -/
theorem chowCodimPushforward_neg (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r s : ℕ)
    (α : codimensionChowGroup k sX r) :
    chowCodimPushforward k sX sY f hf r s (-α) = -chowCodimPushforward k sX sY f hf r s α :=
  map_neg (chowCodimPushforwardHom k sX sY f hf r s) α

/-- `f_*(α - β) = f_*α - f_*β`. -/
theorem chowCodimPushforward_sub (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r s : ℕ)
    (α β : codimensionChowGroup k sX r) :
    chowCodimPushforward k sX sY f hf r s (α - β) =
      chowCodimPushforward k sX sY f hf r s α - chowCodimPushforward k sX sY f hf r s β :=
  map_sub (chowCodimPushforwardHom k sX sY f hf r s) α β

/-! ### Functoriality -/

/-- On `X` equidimensional of dimension `d` and `Y` equidimensional of dimension `e`, with
`d - r = e - s`, the class in dimension `n` of `f_*α ∈ CH^s(Y)` is the pushforward of the class
in dimension `n` of `α ∈ CH^r(X)`. -/
theorem chowCodimTotal_chowCodimPushforward {d e : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (r s : ℕ)
    (hrs : (d : ℤ) - r = e - s) (n : ℤ) (α : codimensionChowGroup k sX r) :
    chowCodimTotal k sY s n (chowCodimPushforward k sX sY f hf r s α) =
      properChowPushforward (fieldChowSituation k) sX sY f hf n
        (properPushforwardDescends _ _ _ _ _ _) (chowCodimTotal k sX r n α) := by
  by_cases hn : (e : ℤ) - s = n
  · exact chowCodimTotal_chowCodimPart k sY hY s hn _
  · rw [chowCodimTotal_eq_zero_of_ne k sY hY s (Ne.symm hn),
      chowCodimTotal_eq_zero_of_ne k sX hX r (by rw [hrs]; exact Ne.symm hn), map_zero]

end Codim

end Stacks.WeilDeRham

end
