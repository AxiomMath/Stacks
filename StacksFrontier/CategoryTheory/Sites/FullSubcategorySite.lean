module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.FiberedCategory.FullSubcategoryCartesian
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A full subcategory closed under the covering morphisms of a site

Let `(𝒞, J)` be a site, let `Q` be a property of morphisms of `𝒞`, and let `P` be a property of
objects of `𝒞` which is *closed under `Q`*: if `f : X ⟶ Y` satisfies `Q` and `Y` satisfies `P`,
then `X` satisfies `P`. Suppose moreover that every `J`-covering sieve is *refined by a covering
family of `Q`-morphisms*, and that a `Q`-morphism has a fibre product with every morphism of the
same target.

Then the inclusion `P.ι : P.FullSubcategory ⥤ 𝒞` is continuous and cocontinuous for the topology
`P.ι.inheritedTopology J` that the full subcategory inherits from `(𝒞, J)` — in which a family of
morphisms of `P.FullSubcategory` covers exactly when its image covers in `(𝒞, J)`, the
cartesianness clause of Stacks 06NU being automatic for a fully faithful functor
(`CategoryTheory.ObjectProperty.instIsStronglyCartesianIotaMap`).

The argument is the one the Stacks project gives in the first paragraph of the proof of 07AK:
"the coverings of objects of `𝒳'` agree with their coverings seen as objects of `𝒳`". Concretely,
a `J`-covering sieve of an object of `P` is refined by a covering family of `Q`-morphisms, and
closure of `P` under `Q` puts the *sources* of that family in `P` too; so that family is already
a covering family of the full subcategory. Cocontinuity is exactly this. Continuity needs in
addition that the full subcategory contains the fibre products of two members of such a family —
again by closure under `Q`, since a base change of a `Q`-morphism is a `Q`-morphism — after which
the sheaf condition for the family upstairs and for its image downstairs are literally the same
condition.

The same hypotheses settle the *relative* statement, **Stacks 07AJ (a)**: if `P₁ ≤ P₂` are two such
full subcategories, then `ObjectProperty.ιOfLE h : P₁.FullSubcategory ⥤ P₂.FullSubcategory` is
fully faithful, continuous and cocontinuous for the two inherited topologies. Full faithfulness is
`CategoryTheory.ObjectProperty.fullyFaithfulιOfLE`, and the other two are deduced from the absolute
case along `P₁.ι = ObjectProperty.ιOfLE h ⋙ P₂.ι`. Only the closure hypothesis — clause (1)(a) of
07AJ — is used; clauses (1)(b) and (2) of 07AJ are needed for part (b) only, and continuity here
needs nothing of `P₂` beyond `P₁ ≤ P₂`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.IsRefinableBy`: a covering sieve is refinable by `Q` when
  it contains a covering family all of whose members satisfy `Q`.
* `CategoryTheory.ObjectProperty.SubcategoryCovering` and
  `CategoryTheory.ObjectProperty.subcategoryCoverage`: the coverage on `P.FullSubcategory` whose
  covering presieves are the families of `Q`-morphisms whose image covers in `(𝒞, J)`. It
  generates `P.ι.inheritedTopology J`.

## Main results

* `CategoryTheory.Precoverage.isRefinableBy_of_mem_toGrothendieck`: refinability by `Q` propagates
  from the generating families of a precoverage to every covering sieve of the topology it
  generates. This is what makes the refinability hypothesis checkable in practice.
* `CategoryTheory.ObjectProperty.subcategoryCoverage_toGrothendieck`: the coverage generates the
  inherited topology.
* `CategoryTheory.ObjectProperty.isCocontinuous_ι_inheritedTopology` and
  `CategoryTheory.ObjectProperty.isContinuous_ι_inheritedTopology`: the two conclusions.
* `CategoryTheory.ObjectProperty.isCocontinuous_ιOfLE_inheritedTopology` and
  `CategoryTheory.ObjectProperty.isContinuous_ιOfLE_inheritedTopology`: **Stacks 07AJ (a)**, the
  same two conclusions for the inclusion of one such full subcategory into another.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-! ### Refinability of a covering sieve by a property of morphisms -/

/-- A covering sieve `S` of `X` is *refinable by* the morphism property `Q` when it contains a
family of `Q`-morphisms which is itself covering. -/
@[sga "4 IV 4.10.6" "Condition (d)"]
def GrothendieckTopology.IsRefinableBy (J : GrothendieckTopology C) (Q : MorphismProperty C)
    {X : C} (S : Sieve X) : Prop :=
  ∃ R : Presieve X, R ≤ S.arrows ∧ (∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Q f) ∧ Sieve.generate R ∈ J X

/-- Refinability only becomes easier for a larger sieve. -/
lemma GrothendieckTopology.IsRefinableBy.mono {J : GrothendieckTopology C}
    {Q : MorphismProperty C} {X : C} {S T : Sieve X} (h : S ≤ T) (hS : J.IsRefinableBy Q S) :
    J.IsRefinableBy Q T :=
  have ⟨R, hRS, hRQ, hRJ⟩ := hS
  ⟨R, hRS.trans h, hRQ, hRJ⟩

/-- **Refinability propagates from the generators of a topology to all of its covering sieves.**
If every sieve generated by a covering family of the precoverage `K` is refinable by `Q`, and `Q`
contains the identities, is stable under composition and under base change, and a `Q`-morphism has
a fibre product with every morphism of the same target, then *every* covering sieve of the topology
generated by `K` is refinable by `Q`.

The four cases are the four clauses of `CategoryTheory.Precoverage.Saturate`: the generators are
the hypothesis; the identity refines the maximal sieve; a base change of a `Q`-family is a
`Q`-family refining the base-changed sieve; and composing a `Q`-family with `Q`-families over each
of its members gives a `Q`-family, by stability of `Q` under composition. -/
theorem Precoverage.isRefinableBy_of_mem_toGrothendieck {K : Precoverage C}
    {Q : MorphismProperty C} [Q.ContainsIdentities] [Q.IsStableUnderComposition]
    [Q.IsStableUnderBaseChange]
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hgen : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X →
      K.toGrothendieck.IsRefinableBy Q (Sieve.generate R))
    ⦃X : C⦄ (S : Sieve X) (hS : S ∈ K.toGrothendieck X) :
    K.toGrothendieck.IsRefinableBy Q S := by
  replace hS : K.Saturate X S := hS
  induction hS with
  | of X R hR => exact hgen R hR
  | top X =>
      refine ⟨Presieve.singleton (𝟙 X), le_top, ?_, ?_⟩
      · rintro _ _ ⟨⟩
        exact Q.id_mem X
      · have h1 : (Sieve.generate (Presieve.singleton (𝟙 X))).arrows (𝟙 X) :=
          Sieve.le_generate _ _ _ Presieve.singleton.mk
        rw [Sieve.id_mem_iff_eq_top.1 h1]
        exact K.toGrothendieck.top_mem X
  | pullback X S _ Y f ih =>
      obtain ⟨R, hRS, hRQ, hRJ⟩ := ih
      have hpb : R.HasPullbacks f := ⟨fun {_} {h} hh ↦ hQpb h f (hRQ h hh)⟩
      refine ⟨R.pullbackArrows f, ?_, ?_, ?_⟩
      · rintro Z g ⟨W, h, hh⟩
        have := R.hasPullback f hh
        simp only [Sieve.pullback_apply, ← pullback.condition (f := h) (g := f)]
        exact S.downward_closed (hRS _ _ hh) _
      · rintro Z g ⟨W, h, hh⟩
        have := R.hasPullback f hh
        exact Q.pullback_snd h f (hRQ h hh)
      · rw [Sieve.pullbackArrows_comm]
        exact K.toGrothendieck.pullback_stable f hRJ
  | transitive X S R _ _ ihS ihR =>
      obtain ⟨T, hTS, hTQ, hTJ⟩ := ihS
      refine ⟨fun ⦃_⦄ k ↦ Q k ∧ R.arrows k, fun _ _ hk ↦ hk.2, fun _ _ hk ↦ hk.1, ?_⟩
      refine K.toGrothendieck.transitive hTJ _ ?_
      rintro Y g ⟨W, i, t, ht, rfl⟩
      rw [Sieve.pullback_comp]
      refine K.toGrothendieck.pullback_stable i ?_
      obtain ⟨U, hUR, hUQ, hUJ⟩ := ihR (hTS _ _ ht)
      refine K.toGrothendieck.superset_covering ?_ hUJ
      rw [Sieve.generate_le_iff]
      intro Z u hu
      exact Sieve.le_generate _ _ _ ⟨Q.comp_mem _ _ (hUQ u hu) (hTQ t ht), hUR _ _ hu⟩

/-- If every member of every generating covering family of a precoverage satisfies `Q`, then
every covering sieve of the generated topology is refinable by `Q`: the generating families are
their own refinements. -/
theorem Precoverage.isRefinableBy_of_members {K : Precoverage C} {Q : MorphismProperty C}
    [Q.ContainsIdentities] [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hK : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → Q g)
    ⦃X : C⦄ (S : Sieve X) (hS : S ∈ K.toGrothendieck X) :
    K.toGrothendieck.IsRefinableBy Q S :=
  isRefinableBy_of_mem_toGrothendieck hQpb
    (fun _ R hR ↦ ⟨R, Sieve.le_generate R, hK R hR, Precoverage.generate_mem_toGrothendieck hR⟩)
    S hS

namespace ObjectProperty

/-- The covering presieves of a full subcategory inside a site: the families of morphisms of
`P.FullSubcategory` whose members satisfy `Q` after inclusion and whose image covers in
`(𝒞, J)`. -/
def SubcategoryCovering (P : ObjectProperty C) (J : GrothendieckTopology C)
    (Q : MorphismProperty C) {x : P.FullSubcategory} (R : Presieve x) : Prop :=
  (∀ ⦃y : P.FullSubcategory⦄ (g : y ⟶ x), R g → Q (P.ι.map g)) ∧
    Sieve.generate (R.map P.ι) ∈ J (P.ι.obj x)

variable {P : ObjectProperty C} {J : GrothendieckTopology C} {Q : MorphismProperty C}

/-- The sieve generated by a presieve of `P.FullSubcategory` whose image generates a `J`-covering
sieve is covering for the inherited topology. -/
private lemma generate_mem_inheritedTopology {x : P.FullSubcategory} (R : Presieve x)
    (hR : Sieve.generate (R.map P.ι) ∈ J (P.ι.obj x)) :
    Sieve.generate R ∈ P.ι.inheritedTopology J x := by
  rw [Functor.inheritedTopology_eq]
  refine Precoverage.generate_mem_toGrothendieck ⟨fun _ _ _ ↦ inferInstance, ?_⟩
  rwa [GrothendieckTopology.mem_toPrecoverage_iff]

/-- Every `Q`-morphism in a `J`-covering sieve of an object of `P` is the image of a morphism of
`P.FullSubcategory`, by closure of `P` under `Q`; hence the `Q`-morphisms of `P.FullSubcategory`
lying in such a sieve form a covering family of the full subcategory. -/
private lemma subcategoryCovering_qPart
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S)
    {x : P.FullSubcategory} (S : Sieve (P.ι.obj x)) (hS : S ∈ J (P.ι.obj x)) :
    SubcategoryCovering P J Q (fun ⦃_⦄ k ↦ Q (P.ι.map k) ∧ S.arrows (P.ι.map k)) := by
  obtain ⟨R, hRS, hRQ, hRJ⟩ := hJQ S hS
  refine ⟨fun _ _ hk ↦ hk.1, J.superset_covering ?_ hRJ⟩
  rw [Sieve.generate_le_iff]
  intro W h hh
  have hW : P W := hPQ h (hRQ h hh) x.property
  exact Sieve.le_generate _ _ _
    (Presieve.map_map (f := (homMk h : ⟨W, hW⟩ ⟶ x)) ⟨hRQ h hh, hRS _ _ hh⟩)

/-- **The site of a full subcategory closed under `Q`.** Its covering presieves are the families
of `Q`-morphisms of `P.FullSubcategory` whose image covers in `(𝒞, J)`.

The pullback axiom of a coverage holds with no fibre products: the covering family over `y`
refining a covering family `R` over `x` along `f : y ⟶ x` is taken to be *all* `Q`-morphisms of
`P.FullSubcategory` into `y` lying in the pullback along `f` of the sieve generated by `R`. That
it covers is the refinement hypothesis applied to that pullback sieve, and each of its members
factors through a member of `R` because the pullback sieve is generated by `R`. -/
def subcategoryCoverage (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) :
    Coverage P.FullSubcategory where
  coverings x := {R | SubcategoryCovering P J Q R}
  pullback {x y} f R hR := by
    refine ⟨fun ⦃_⦄ k ↦ Q (P.ι.map k) ∧
      ((Sieve.generate (R.map P.ι)).pullback (P.ι.map f)).arrows (P.ι.map k), ?_, ?_⟩
    · exact subcategoryCovering_qPart hPQ hJQ _ (J.pullback_stable (P.ι.map f) hR.2)
    · rintro z k ⟨-, hk⟩
      obtain ⟨W, i, e, he, hie⟩ := hk
      obtain ⟨hg⟩ := he
      obtain ⟨i₀, rfl⟩ := P.ι.map_surjective i
      exact ⟨_, i₀, _, hg, P.ι.map_injective (by simpa using hie)⟩

/-- The coverage of a full subcategory closed under `Q` generates exactly the topology the full
subcategory inherits from `(𝒞, J)` (Stacks 06NV). -/
theorem subcategoryCoverage_toGrothendieck
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) :
    (subcategoryCoverage hPQ hJQ).toGrothendieck = P.ι.inheritedTopology J := by
  refine le_antisymm (((Coverage.gi _).gc _ _).mpr ?_) ?_
  · intro x R hR
    rw [GrothendieckTopology.mem_toCoverage_iff]
    exact generate_mem_inheritedTopology R hR.2
  · rw [Functor.inheritedTopology_eq, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro x R hR
    obtain ⟨-, hR2⟩ := hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff] at hR2 ⊢
    refine Coverage.saturate_of_superset _ ?_
      (Coverage.Saturate.of x _
        (subcategoryCovering_qPart hPQ hJQ (Sieve.generate (R.map P.ι)) hR2))
    rw [Sieve.generate_le_iff]
    intro z k hk
    obtain ⟨-, W, i, e, he, hie⟩ := hk
    obtain ⟨hg⟩ := he
    obtain ⟨i₀, rfl⟩ := P.ι.map_surjective i
    have hk2 : i₀ ≫ _ = k := P.ι.map_injective (by simpa using hie)
    rw [← hk2]
    exact (Sieve.generate R).downward_closed (Sieve.le_generate _ _ _ hg) _

/-- **Stacks 07AK, cocontinuity.** The inclusion of a full subcategory closed under `Q` is
cocontinuous for the inherited topology: a `J`-covering sieve of an object of `P` is refined by a
covering family of `Q`-morphisms, whose sources lie in `P` by closure, so the sieve the given one
pulls back to upstairs is covering. -/
theorem isCocontinuous_ι_inheritedTopology
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) :
    P.ι.IsCocontinuous (P.ι.inheritedTopology J) J where
  cover_lift {x} {S} hS := by
    rw [← subcategoryCoverage_toGrothendieck hPQ hJQ]
    refine Coverage.saturate_of_superset _ ?_
      (Coverage.Saturate.of x _ (subcategoryCovering_qPart hPQ hJQ S hS))
    rw [Sieve.generate_le_iff]
    exact fun z k hk ↦ hk.2

section Pullbacks

variable [Q.IsStableUnderBaseChange]

/-- The fibre product of a `Q`-morphism with an arbitrary morphism inside a full subcategory
closed under `Q`: it exists, and the inclusion preserves it. Both statements come from the fibre
product in `𝒞`, whose vertex lies in `P` because the projection parallel to the `Q`-morphism is a
base change of it, hence again a `Q`-morphism; the inclusion is fully faithful, so it reflects the
limit it has created. -/
lemma exists_isPullback_ι
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    {x y z : P.FullSubcategory} (g : y ⟶ x) (f : z ⟶ x) (hg : Q (P.ι.map g)) :
    ∃ (w : P.FullSubcategory) (a : w ⟶ y) (b : w ⟶ z),
      IsPullback a b g f ∧ IsPullback (P.ι.map a) (P.ι.map b) (P.ι.map g) (P.ι.map f) := by
  have := hQpb (P.ι.map g) (P.ι.map f) hg
  have hd : IsPullback (pullback.fst (P.ι.map g) (P.ι.map f))
      (pullback.snd (P.ι.map g) (P.ι.map f)) (P.ι.map g) (P.ι.map f) :=
    IsPullback.of_hasPullback _ _
  have hsnd : Q (pullback.snd (P.ι.map g) (P.ι.map f)) := Q.pullback_snd _ _ hg
  refine ⟨⟨pullback (P.ι.map g) (P.ι.map f), hPQ _ hsnd z.property⟩,
    homMk (pullback.fst _ _), homMk (pullback.snd _ _), ?_, hd⟩
  have hw : (homMk (pullback.fst (P.ι.map g) (P.ι.map f)) :
      (⟨pullback (P.ι.map g) (P.ι.map f), hPQ _ hsnd z.property⟩ : P.FullSubcategory) ⟶ y) ≫ g =
      homMk (pullback.snd (P.ι.map g) (P.ι.map f)) ≫ f :=
    P.ι.map_injective (by simpa using hd.w)
  exact IsPullback.of_isLimit (isLimitOfReflects P.ι
    ((isLimitMapConePullbackConeEquiv P.ι hw).symm hd.isLimit))

/-- A family of `Q`-morphisms of a full subcategory closed under `Q` has pairwise fibre products
inside the full subcategory. -/
lemma hasPairwisePullbacks_of_subcategoryCovering
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    {x : P.FullSubcategory} (R : Presieve x)
    (hR : ∀ ⦃y : P.FullSubcategory⦄ (g : y ⟶ x), R g → Q (P.ι.map g)) :
    R.HasPairwisePullbacks where
  has_pullbacks {_ _} {g} hg {f} _ := by
    obtain ⟨w, a, b, hup, -⟩ := exists_isPullback_ι hQpb hPQ g f (hR g hg)
    exact ⟨⟨_, hup.isLimit⟩⟩

/-- The inclusion preserves the pairwise fibre products of a family of `Q`-morphisms. -/
lemma preservesPairwisePullbacks_of_subcategoryCovering
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    {x : P.FullSubcategory} (R : Presieve x)
    (hR : ∀ ⦃y : P.FullSubcategory⦄ (g : y ⟶ x), R g → Q (P.ι.map g)) :
    P.ι.PreservesPairwisePullbacks R where
  preservesLimit {_ _} {g} {f} hg _ := by
    obtain ⟨w, a, b, hup, hdown⟩ := exists_isPullback_ι hQpb hPQ g f (hR g hg)
    exact preservesLimit_of_preserves_limit_cone hup.isLimit
      ((isLimitMapConePullbackConeEquiv P.ι hup.w).symm hdown.isLimit)

/-- **Stacks 07AK, continuity.** The inclusion of a full subcategory closed under `Q` is
continuous for the inherited topology: the restriction of a `J`-sheaf is a sheaf for every
covering family of `Q`-morphisms upstairs, because such a family and its image satisfy literally
the same sheaf condition — the inclusion being fully faithful and carrying the pairwise fibre
products of the family to those of its image. -/
theorem isContinuous_ι_inheritedTopology
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hPQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P Y → P X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) :
    P.ι.IsContinuous (P.ι.inheritedTopology J) J where
  op_comp_isSheaf_of_types G := by
    rw [← subcategoryCoverage_toGrothendieck hPQ hJQ, Presieve.isSheaf_coverage]
    intro x R hR
    have := hasPairwisePullbacks_of_subcategoryCovering hQpb hPQ R hR.1
    have := preservesPairwisePullbacks_of_subcategoryCovering hQpb hPQ R hR.1
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks,
      Presieve.isSheafFor_iff_generate]
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.2) _ hR.2

/-! ### Nested full subcategories -/

section Nested

variable {P₁ P₂ : ObjectProperty C}

/-- The inclusion of a smaller full subcategory into a larger one preserves the pairwise fibre
products of a family of `Q`-morphisms of the smaller one.

Those fibre products are computed in the ambient category `𝒞` by
`CategoryTheory.ObjectProperty.preservesPairwisePullbacks_of_subcategoryCovering`, which says that
`P₁.ι = ObjectProperty.ιOfLE h ⋙ P₂.ι` preserves them; and `P₂.ι`, being fully faithful, reflects
limits. -/
lemma preservesPairwisePullbacks_ιOfLE_of_subcategoryCovering
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hP₁Q : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P₁ Y → P₁ X) (h : P₁ ≤ P₂)
    {x : P₁.FullSubcategory} (R : Presieve x)
    (hR : ∀ ⦃y : P₁.FullSubcategory⦄ (g : y ⟶ x), R g → Q (P₁.ι.map g)) :
    (ιOfLE h).PreservesPairwisePullbacks R where
  preservesLimit {_ _} {f} {g} hf hg := by
    have := preservesPairwisePullbacks_of_subcategoryCovering hQpb hP₁Q R hR
    have : PreservesLimit (cospan f g) (ιOfLE h ⋙ P₂.ι) :=
      P₁.ι.preservesLimit_cospan_of_mem_presieve R hf hg
    exact preservesLimit_of_reflects_of_preserves (ιOfLE h) P₂.ι

/-- **Stacks 07AJ (a), cocontinuity.** Let `P₁ ≤ P₂` be full subcategories of a site `(𝒞, J)`,
both closed under the morphism property `Q` by which every `J`-covering sieve is refinable, and
give each the topology it inherits from `(𝒞, J)`. Then `ObjectProperty.ιOfLE h : P₁ ⥤ P₂` is
cocontinuous.

A covering sieve of `P₂` has a `J`-covering image downstairs, because `P₂.ι` is continuous and so
cover-preserving; the sieve that image pulls back to in `P₁` is covering because `P₁.ι` is
cocontinuous; and that pullback is the pullback of the original sieve along `ιOfLE h`, since
`P₁.ι = ιOfLE h ⋙ P₂.ι` and the fully faithful `P₂.ι` pulls its own pushforward back to the
identity. -/
@[sga "4 III 3.4" "ii) u cocontinuous"]
theorem isCocontinuous_ιOfLE_inheritedTopology
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hP₁Q : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P₁ Y → P₁ X)
    (hP₂Q : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P₂ Y → P₂ X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) (h : P₁ ≤ P₂) :
    (ιOfLE h).IsCocontinuous (P₁.ι.inheritedTopology J) (P₂.ι.inheritedTopology J) where
  cover_lift {x} {S} hS := by
    have := isContinuous_ι_inheritedTopology (P := P₂) hQpb hP₂Q hJQ
    have := isCocontinuous_ι_inheritedTopology hP₁Q hJQ
    have hp := (CoverPreserving.of_isContinuous P₂.ι
      (P₂.ι.inheritedTopology J) J).cover_preserve hS
    have key : Sieve.functorPullback P₁.ι (Sieve.functorPushforward P₂.ι S)
        = Sieve.functorPullback (ιOfLE h) S := by
      have e := Sieve.functorPullback_comp (ιOfLE h) P₂.ι (Sieve.functorPushforward P₂.ι S)
      rwa [Sieve.functorPullback_functorPushforward_eq] at e
    rw [← key]
    exact Functor.cover_lift P₁.ι (P₁.ι.inheritedTopology J) J (U := x) hp

/-- **Stacks 07AJ (a), continuity.** In the situation of
`CategoryTheory.ObjectProperty.isCocontinuous_ιOfLE_inheritedTopology`, the inclusion
`ObjectProperty.ιOfLE h : P₁ ⥤ P₂` is continuous.

The topology of `P₁` is generated by the covering families of `Q`-morphisms
(`CategoryTheory.ObjectProperty.subcategoryCoverage_toGrothendieck`), and such a family and its
image in `P₂` satisfy literally the same sheaf condition: the inclusion is fully faithful and
carries the pairwise fibre products of the family to those of its image. The image is a covering
family of `P₂` because its own image in `𝒞` is the image of the original family, which covers.

Unlike cocontinuity this needs nothing of `P₂` beyond `P₁ ≤ P₂`. -/
@[sga "4 III 3.4" "ii) u continuous"]
theorem isContinuous_ιOfLE_inheritedTopology
    (hQpb : ∀ ⦃X Y Z : C⦄ (g : Y ⟶ X) (f : Z ⟶ X), Q g → HasPullback g f)
    (hP₁Q : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → P₁ Y → P₁ X)
    (hJQ : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → J.IsRefinableBy Q S) (h : P₁ ≤ P₂) :
    (ιOfLE h).IsContinuous (P₁.ι.inheritedTopology J) (P₂.ι.inheritedTopology J) where
  op_comp_isSheaf_of_types G := by
    rw [← subcategoryCoverage_toGrothendieck hP₁Q hJQ, Presieve.isSheaf_coverage]
    intro x R hR
    have := hasPairwisePullbacks_of_subcategoryCovering hQpb hP₁Q R hR.1
    have := preservesPairwisePullbacks_ιOfLE_of_subcategoryCovering hQpb hP₁Q h R hR.1
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks,
      Presieve.isSheafFor_iff_generate]
    refine ((isSheaf_iff_isSheaf_of_type _ _).1 G.2) _ ?_
    refine generate_mem_inheritedTopology _ (J.superset_covering ?_ hR.2)
    rw [Sieve.generate_le_iff]
    rintro V f ⟨hg⟩
    exact Sieve.le_generate _ _ _ (Presieve.map_map (Presieve.map_map hg))

end Nested

end Pullbacks

end ObjectProperty

end CategoryTheory

end
