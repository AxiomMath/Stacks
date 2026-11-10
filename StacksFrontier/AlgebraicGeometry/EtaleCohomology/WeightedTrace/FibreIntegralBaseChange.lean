module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegral
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the fibre integral

The fibre integral `AlgebraicGeometry.fibreIntegral` of a locally constant section supported on a
part finite over the base is compatible with base change of the test object: if `V' ⟶ V` is any
morphism and `U' = U ×_V V'`, then the fibre integral computed on `U' ⟶ V'` is the fibre integral
computed on `U ⟶ V`, pulled back along `V' ⟶ V`. This is the naturality that makes the fibre
integral a morphism of presheaves on the small étale site, and it is the second of the two
ingredients that Stacks 0GKG needs and that
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/WeightedTrace/FibreIntegral.lean` leaves open.

## Main results

* `AlgebraicGeometry.levelOpens_preimage` — the level sets of the pulled-back section are the
  preimages of the level sets of the section.
* `AlgebraicGeometry.weight_comp_morphismRestrict` — the weight of a level set, precomposed with
  the restriction of the base-change morphism, is the weight of the preimage level set.
* `AlgebraicGeometry.isPullback_morphismRestrict_comp` — a cartesian square stays cartesian after
  restricting the source of its vertical maps to an open of the top-right corner and its
  preimage.
* `AlgebraicGeometry.isPullback_levelOpens_of_isPullback` — the induced square on the level sets
  of a section and of its pullback is cartesian.
* `AlgebraicGeometry.separableDegreeWeightedFiberSum_levelOpens_comp_of_isPullback` — base change
  for the weighted fibre sum over a single level set, which is Stacks 0F39 applied to the level
  set rather than to the whole of `U`.
* `AlgebraicGeometry.fibreIntegralTerm_comp_of_isPullback` — **base change for one summand of the
  fibre integral.**
* `AlgebraicGeometry.fibreIntegral_comp_of_isPullback` — **base change for the fibre integral**:
  `fibreIntegral h π w hs ∘ g = fibreIntegral (p ≫ h) π' w hs'`.

## Implementation notes

**Why Stacks 0F39 cannot be applied directly.** The base-change statement for weighted fibre
sums, `AlgebraicGeometry.separableDegreeWeightedFiberSum_comp_of_isPullback`, assumes that every
fibre of the morphism being integrated over is a finite set. The morphism `π : U ⟶ V` of a fibre
integral has no such property: only the *support* of the section is finite over `V`. The way
round this is the level-set decomposition that defines the fibre integral in the first place. For
`n ≠ 0` the level set `U_n = {s = n}` is finite over `V` by
`AlgebraicGeometry.isFinite_levelOpens_comp`, hence has finite fibres, so 0F39 does apply to
`U_n ⟶ V`; and the summand at `n = 0` is zero on both sides. So base change is proved termwise
and then summed.

**The square on the level sets.** The level sets of `s ∘ p` are literally the preimages under `p`
of the level sets of `s` — equal, not merely isomorphic, as open subschemes — so no transport
along an isomorphism and no `eqToHom` appears anywhere. The cartesian square on them is obtained
by pasting the restriction square `AlgebraicGeometry.isPullback_morphismRestrict` on top of the
given one with `CategoryTheory.IsPullback.paste_vert`; the resulting left vertical map is
`(p ⁻¹ᵁ U_n).ι ≫ π'`, which is exactly the morphism whose weighted fibre sum the pulled-back
fibre integral is built from.

**The weight.** On the pulled-back side the weight is `w ∘ (p ≫ h)` restricted to the level set,
whereas 0F39 produces the weight of the original side precomposed with the restricted morphism
`p ∣_ U_n`. The two agree because `p ∣_ U_n ≫ U_n.ι = (p ⁻¹ᵁ U_n).ι ≫ p`, which is
`AlgebraicGeometry.morphismRestrict_ι`; that is
`AlgebraicGeometry.weight_comp_morphismRestrict`.

**Generality.** Nothing here needs `g : V' ⟶ V` to be étale, or `π` to sit inside an étale base
change of the original morphism `f : X ⟶ Y`; the statements are for an arbitrary cartesian square
over an arbitrary `g`. The hypotheses are exactly those of
`AlgebraicGeometry.isFinite_levelOpens_comp`, namely that `π` is locally of finite type and
locally quasi-finite and that the section is supported on a closed subscheme finite over `V`.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F39](https://stacks.math.columbia.edu/tag/0F39)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section LevelOpens

variable {U U' : Scheme.{u}}

/-- **The level sets of a pulled-back section are the preimages of the level sets.** For
`p : U' ⟶ U` and a locally constant `s : U → ℤ`, the locus in `U'` where `s ∘ p` takes the value
`n` is the preimage of the locus in `U` where `s` takes the value `n`. This is an equality of open
subschemes, not merely an isomorphism, which is what keeps `eqToHom` out of everything below. -/
public theorem levelOpens_preimage (p : U' ⟶ U) {s : U → ℤ} (hs : IsLocallyConstant s)
    (hs' : IsLocallyConstant (s ∘ ⇑p)) (n : ℤ) :
    p ⁻¹ᵁ (levelOpens hs n) = levelOpens hs' n := rfl

/-- The weight of a level set, transported along the restriction of `p`, is the weight of the
preimage level set. This is `AlgebraicGeometry.morphismRestrict_ι` read as an equality of
functions on points. -/
public theorem weight_comp_morphismRestrict {X : Scheme.{u}} (p : U' ⟶ U) (h : U ⟶ X)
    (W : U.Opens) (w : X → ℤ) :
    (w ∘ ⇑(W.ι ≫ h)) ∘ ⇑(p ∣_ W) = w ∘ ⇑((p ⁻¹ᵁ W).ι ≫ (p ≫ h)) := by
  have hmr : ⇑((p ∣_ W) ≫ W.ι) = ⇑((p ⁻¹ᵁ W).ι ≫ p) := by rw [morphismRestrict_ι]
  funext x
  simp only [Function.comp_apply, Scheme.Hom.comp_apply]
  exact congrArg (fun y => w (h y)) (congrFun hmr x)

end LevelOpens

section Squares

variable {U U' V V' : Scheme.{u}}

/-- **Restricting a cartesian square to an open of the target of its top map.** Given a cartesian
square with top map `p : U' ⟶ U` and an open `W ⊆ U`, the square with top map `p ∣_ W`, left map
`(p ⁻¹ᵁ W).ι ≫ π'` and right map `W.ι ≫ π` is again cartesian. It is the vertical paste of the
restriction square of `p` along `W` on top of the given square. -/
public theorem isPullback_morphismRestrict_comp {p : U' ⟶ U} {π : U ⟶ V} {π' : U' ⟶ V'}
    {g : V' ⟶ V} (sq : IsPullback p π' π g) (W : U.Opens) :
    IsPullback (p ∣_ W) ((p ⁻¹ᵁ W).ι ≫ π') (W.ι ≫ π) g :=
  (isPullback_morphismRestrict p W).paste_vert sq

/-- **The square on level sets is cartesian.** If `U'` is the fibre product of `U` and `V'` over
`V`, then the level set `{s ∘ p = n}` in `U'` is the fibre product of the level set `{s = n}` in
`U` and of `V'` over `V`. -/
public theorem isPullback_levelOpens_of_isPullback {p : U' ⟶ U} {π : U ⟶ V} {π' : U' ⟶ V'}
    {g : V' ⟶ V} (sq : IsPullback p π' π g) {s : U → ℤ} (hs : IsLocallyConstant s)
    (hs' : IsLocallyConstant (s ∘ ⇑p)) (n : ℤ) :
    IsPullback (p ∣_ levelOpens hs n) ((levelOpens hs' n).ι ≫ π')
      ((levelOpens hs n).ι ≫ π) g :=
  isPullback_morphismRestrict_comp sq (levelOpens hs n)

end Squares

section BaseChange

variable {X U U' V V' Z : Scheme.{u}}

/-- **Base change for the weighted fibre sum over a single level set.** For `n ≠ 0` the level set
`{s = n}` is finite over `V`, so it has finite fibres and Stacks 0F39 applies to it. This is the
step that the whole base-change statement for the fibre integral is assembled from: the morphism
`π` itself has no finite fibres, and 0F39 cannot be applied to it. -/
public theorem separableDegreeWeightedFiberSum_levelOpens_comp_of_isPullback {h : U ⟶ X}
    {π : U ⟶ V} {π' : U' ⟶ V'} {p : U' ⟶ U} {g : V' ⟶ V} (sq : IsPullback p π' π g) (w : X → ℤ)
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (hs' : IsLocallyConstant (s ∘ ⇑p)) (i : Z ⟶ U) [IsClosedImmersion i]
    (hZ : IsFinite (i ≫ π)) (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base)
    {n : ℤ} (hn : n ≠ 0) :
    separableDegreeWeightedFiberSum ((levelOpens hs n).ι ≫ π)
        (w ∘ ⇑((levelOpens hs n).ι ≫ h)) ∘ ⇑g =
      separableDegreeWeightedFiberSum ((levelOpens hs' n).ι ≫ π')
        (w ∘ ⇑((levelOpens hs' n).ι ≫ (p ≫ h))) := by
  have hfin : IsFinite ((levelOpens hs n).ι ≫ π) := isFinite_levelOpens_comp hs i hZ hsupp hn
  have hfibres : ∀ v : V, ((⇑((levelOpens hs n).ι ≫ π)) ⁻¹' {v}).Finite :=
    fun v => ((levelOpens hs n).ι ≫ π).finite_preimage_singleton v
  have key := separableDegreeWeightedFiberSum_comp_of_isPullback ((levelOpens hs n).ι ≫ π)
    (p ∣_ levelOpens hs n) ((levelOpens hs' n).ι ≫ π') g
    (isPullback_levelOpens_of_isPullback sq hs hs' n) hfibres
    (w ∘ ⇑((levelOpens hs n).ι ≫ h))
  rw [key]
  congr 1
  exact weight_comp_morphismRestrict p h (levelOpens hs n) w

/-- **Base change for one summand of the fibre integral.** The summand indexed by `n` of the fibre
integral on `U ⟶ V`, pulled back along `g`, is the summand indexed by `n` of the fibre integral on
`U' ⟶ V'`. For `n = 0` both summands vanish; for `n ≠ 0` this is Stacks 0F39 on the level set. -/
public theorem fibreIntegralTerm_comp_of_isPullback {h : U ⟶ X} {π : U ⟶ V} {π' : U' ⟶ V'}
    {p : U' ⟶ U} {g : V' ⟶ V} (sq : IsPullback p π' π g) (w : X → ℤ)
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (hs' : IsLocallyConstant (s ∘ ⇑p)) (i : Z ⟶ U) [IsClosedImmersion i]
    (hZ : IsFinite (i ≫ π)) (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) (n : ℤ) :
    fibreIntegralTerm h π w hs n ∘ ⇑g = fibreIntegralTerm (p ≫ h) π' w hs' n := by
  rcases eq_or_ne n 0 with rfl | hn
  · funext v'
    simp only [Function.comp_apply, fibreIntegralTerm_zero]
  · have key := separableDegreeWeightedFiberSum_levelOpens_comp_of_isPullback (h := h) sq w hs hs'
      i hZ hsupp hn
    funext v'
    simp only [fibreIntegralTerm, Function.comp_apply]
    congr 1
    exact congrFun key v'

/-- **The fibre integral is compatible with base change of the test object.** If `U'` is the fibre
product of `U` and `V'` over `V` and `s ∘ p` is the pulled-back section, then the fibre integral
of `s ∘ p` on `V'` is the fibre integral of `s` on `V`, composed with `g : V' ⟶ V`.

Together with `AlgebraicGeometry.isLocallyConstant_fibreIntegral` and
`AlgebraicGeometry.fibreIntegral_add` this makes the fibre integral a natural
transformation of presheaves of abelian groups, which is what Stacks 0GKG assembles the trace map
`Tr_{f, w}` out of. -/
public theorem fibreIntegral_comp_of_isPullback {h : U ⟶ X} {π : U ⟶ V} {π' : U' ⟶ V'}
    {p : U' ⟶ U} {g : V' ⟶ V} (sq : IsPullback p π' π g) (w : X → ℤ)
    [LocallyOfFiniteType π] [LocallyQuasiFinite π] {s : U → ℤ} (hs : IsLocallyConstant s)
    (hs' : IsLocallyConstant (s ∘ ⇑p)) (i : Z ⟶ U) [IsClosedImmersion i]
    (hZ : IsFinite (i ≫ π)) (hsupp : ∀ x : U, s x ≠ 0 → x ∈ Set.range i.base) :
    fibreIntegral h π w hs ∘ ⇑g = fibreIntegral (p ≫ h) π' w hs' := by
  funext v'
  change (∑ᶠ n : ℤ, fibreIntegralTerm h π w hs n (g v')) =
    ∑ᶠ n : ℤ, fibreIntegralTerm (p ≫ h) π' w hs' n v'
  exact finsum_congr fun n =>
    congrFun (fibreIntegralTerm_comp_of_isPullback sq w hs hs' i hZ hsupp n) v'

end BaseChange

end AlgebraicGeometry

end
