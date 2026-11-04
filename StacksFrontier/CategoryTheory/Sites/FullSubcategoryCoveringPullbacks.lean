module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable

/-!
# Covering pullbacks of the inclusion of a full subsite

Let `(𝒞, J)` be a site, let `Q` be a property of morphisms of `𝒞` by which every `J`-covering sieve
is refinable, and let `P` be a property of objects of `𝒞` closed under `Q`. The full subcategory
cut out by `P` need not have fibre products, but it has the fibre product of a `Q`-morphism with an
arbitrary morphism of the same target, by `CategoryTheory.ObjectProperty.exists_isPullback_ι`. This
file proves the covering-pullback condition `Stacks.Sites.PreservesCoveringPullbacks` of Stacks
00WV for the inclusion of the full subcategory, localized at an object of it.

## Main results

* `CategoryTheory.Coverage.isRefinableBy_of_mem_toGrothendieck`: refinability by `Q` propagates
  from the generating families of a coverage to every covering sieve of the topology it generates.
* `CategoryTheory.ObjectProperty.isRefinableBy_inheritedTopology`: every covering sieve of a full
  subcategory closed under `Q` is refinable by the `Q`-morphisms of the subcategory.
* `CategoryTheory.ObjectProperty.hasPullback_over_ι` and
  `CategoryTheory.ObjectProperty.preservesLimit_cospan_overPost`: a `Q`-morphism of a slice of the
  full subcategory has a fibre product with every morphism of the same target, and `Over.post P.ι`
  preserves it.
* `CategoryTheory.ObjectProperty.preservesCoveringPullbacks_over_ι`: the covering-pullback
  condition of Stacks 00WV for `Over.post P.ι`.

## References

* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Refinability of the saturation of a coverage -/

/-- **Refinability propagates from the generators of a coverage to all of its covering sieves.** If
every generating covering family of the coverage `K` consists of `Q`-morphisms, and `Q` contains
the identities and is stable under composition, then every covering sieve of the topology `K`
generates is refinable by `Q`. -/
theorem Coverage.isRefinableBy_of_mem_toGrothendieck {K : Coverage C} {Q : MorphismProperty C}
    [Q.ContainsIdentities] [Q.IsStableUnderComposition]
    (hgen : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → Q g)
    ⦃X : C⦄ (S : Sieve X) (hS : S ∈ K.toGrothendieck X) :
    K.toGrothendieck.IsRefinableBy Q S := by
  replace hS : K.Saturate X S := hS
  induction hS with
  | of X R hR => exact ⟨R, Sieve.le_generate R, hgen R hR, Coverage.Saturate.of X R hR⟩
  | top X =>
      refine ⟨Presieve.singleton (𝟙 X), le_top, ?_, ?_⟩
      · rintro _ _ ⟨⟩
        exact Q.id_mem X
      · rw [Sieve.id_mem_iff_eq_top.1 (Sieve.le_generate _ _ _ Presieve.singleton.mk)]
        exact K.toGrothendieck.top_mem X
  | transitive X R S _ _ ihR ihS =>
      obtain ⟨T, hTR, hTQ, hTJ⟩ := ihR
      refine ⟨fun ⦃_⦄ k ↦ Q k ∧ S.arrows k, fun _ _ hk ↦ hk.2, fun _ _ hk ↦ hk.1, ?_⟩
      refine K.toGrothendieck.transitive hTJ _ ?_
      rintro Y g ⟨W, i, t, ht, rfl⟩
      rw [Sieve.pullback_comp]
      refine K.toGrothendieck.pullback_stable i ?_
      obtain ⟨U, hUS, hUQ, hUJ⟩ := ihS (hTR _ _ ht)
      refine K.toGrothendieck.superset_covering ?_ hUJ
      rw [Sieve.generate_le_iff]
      intro Z u hu
      exact Sieve.le_generate _ _ _ ⟨Q.comp_mem _ _ (hUQ u hu) (hTQ t ht), hUS _ _ hu⟩

namespace ObjectProperty

variable {P : ObjectProperty C} {J : GrothendieckTopology C} {Q : MorphismProperty C}

/-! ### Refinability on a full subcategory closed under `Q` -/

/-- **Every covering sieve of a full subcategory closed under `Q` is refinable by `Q`**: every
covering sieve of the topology `P.FullSubcategory` inherits from `J` is refinable by the morphisms
of `P.FullSubcategory` whose underlying morphism satisfies `Q`. -/
theorem isRefinableBy_inheritedTopology [Q.ContainsIdentities] [Q.IsStableUnderComposition]
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S)
    ⦃x : P.FullSubcategory⦄ (S : Sieve x) (hS : S ∈ P.ι.inheritedTopology J x) :
    (P.ι.inheritedTopology J).IsRefinableBy (Q.inverseImage P.ι) S := by
  rw [← subcategoryCoverage_toGrothendieck hPQ hJQ] at hS ⊢
  refine Coverage.isRefinableBy_of_mem_toGrothendieck ?_ S hS
  exact fun _ _ hR _ g hg ↦ hR.1 g hg

/-! ### Covering pullbacks on a slice of a full subcategory closed under `Q` -/

section Pullbacks

variable [Q.IsStableUnderBaseChange]

/-- A morphism of a slice of a full subcategory closed under `Q` whose underlying morphism
satisfies `Q` has a fibre product with every morphism of the same target. -/
theorem hasPullback_over_ι
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    {x : P.FullSubcategory} {U V W : Over x} (f : V ⟶ U) (g : W ⟶ U)
    (hf : Q (P.ι.map f.left)) :
    HasPullback f g := by
  obtain ⟨w, a, b, hup, -⟩ := exists_isPullback_ι hQpb hPQ f.left g.left hf
  have : HasPullback ((Over.forget x).map f) ((Over.forget x).map g) := ⟨⟨⟨_, hup.isLimit⟩⟩⟩
  have : HasLimit (cospan f g ⋙ Over.forget x) :=
    hasLimit_of_iso (cospanCompIso (Over.forget x) f g).symm
  exact hasLimit_of_created (cospan f g) (Over.forget x)

/-- `Over.post P.ι` preserves the fibre product of
`CategoryTheory.ObjectProperty.hasPullback_over_ι`. -/
theorem preservesLimit_cospan_overPost
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    {x : P.FullSubcategory} {U V W : Over x} (f : V ⟶ U) (g : W ⟶ U)
    (hf : Q (P.ι.map f.left)) :
    PreservesLimit (cospan f g) (Over.post (X := x) P.ι) := by
  obtain ⟨w, a, b, hup, hdown⟩ := exists_isPullback_ι hQpb hPQ f.left g.left hf
  have h₁ : PreservesLimit (cospan ((Over.forget x).map f) ((Over.forget x).map g)) P.ι :=
    preservesLimit_of_preserves_limit_cone hup.isLimit
      ((isLimitMapConePullbackConeEquiv P.ι hup.w).symm hdown.isLimit)
  have h₂ : PreservesLimit (cospan f g ⋙ Over.forget x) P.ι :=
    preservesLimit_of_iso_diagram P.ι (cospanCompIso (Over.forget x) f g).symm
  have h₃ : PreservesLimit (cospan f g) (Over.post (X := x) P.ι ⋙ Over.forget (P.ι.obj x)) := by
    rw [Over.post_forget_eq_forget_comp]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves (Over.post (X := x) P.ι)
    (Over.forget (P.ι.obj x))

/-- **The covering-pullback condition of Stacks 00WV for the inclusion of a full subsite, localized
at an object.** Let `(𝒞, J)` be a site, let `Q` be a property of morphisms of `𝒞`, stable under
base change and having fibre products against arbitrary morphisms of the same target, by which
every `J`-covering sieve is refinable, and let `P` be a property of objects closed under `Q`. Then
for every object `x` of `P` the slice functor `Over.post P.ι` satisfies the covering-pullback
clause of continuity on the slice at `x` of the topology `P.FullSubcategory` inherits from
`(𝒞, J)`. -/
theorem preservesCoveringPullbacks_over_ι [Q.ContainsIdentities] [Q.IsStableUnderComposition]
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S)
    (x : P.FullSubcategory) :
    Stacks.Sites.PreservesCoveringPullbacks ((P.ι.inheritedTopology J).over x)
      (Over.post (X := x) P.ι) where
  exists_cover U S hS := by
    obtain ⟨R, hRS, hRQ, hRJ⟩ := (P.ι.inheritedTopology J).isRefinableBy_over
      (Q.inverseImage P.ι) x (isRefinableBy_inheritedTopology hPQ hJQ) S hS
    exact ⟨R, hRJ, hRS, fun _ f hf _ g ↦
      ⟨hasPullback_over_ι hQpb hPQ f g (hRQ f hf),
        preservesLimit_cospan_overPost hQpb hPQ f g (hRQ f hf)⟩⟩

end Pullbacks

end ObjectProperty

end CategoryTheory

end
