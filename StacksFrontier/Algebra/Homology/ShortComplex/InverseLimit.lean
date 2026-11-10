module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.CategoryTheory.MittagLefflerSections

@[expose] public section

universe u v w

/-!
# Inverse limits of short exact sequences of towers; the Mittag-Leffler lemma

Let `R` be a ring and let `S` be a short complex of towers of `R`-modules, that is of functors
`ℕᵒᵖ ⥤ ModuleCat R`, which is short exact at every index `n`. Write `K = S.X₁`, `L = S.X₂` and
`M = S.X₃`. If the tower `K` satisfies the Mittag-Leffler condition, then the sequence of
inverse limits `0 → lim K → lim L → lim M → 0` is short exact.

Left exactness is formal: an element of `lim L` killed by `lim M` is a compatible family of
elements of the kernels `ker(L n → M n) = im(K n → L n)`, and the preimages in `K n` are unique,
hence automatically compatible. The content is surjectivity of `lim L → lim M`. Given a
compatible family `c` in `lim M`, the fibres `E n = {b ∈ L n | g n b = c n}` form a tower of
nonempty sets, and a compatible family in it is exactly a preimage of `c`. Each `E n` is a coset
of `im(K n → L n)`, so `im(E j → E n)` is a coset of `im(K j → K n)`; since those images
stabilize, so do the former, and `E` is Mittag-Leffler. A Mittag-Leffler tower of nonempty sets
indexed by `ℕᵒᵖ` has a compatible family: passing to the eventual ranges makes all transition
maps surjective, and a tower of surjections indexed by `ℕᵒᵖ` has a compatible family lying over
any prescribed element at index `0`.

## Main results

* `CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler`: Stacks 03CA.
* `Ab.mono_lim_map_and_exact_of_shortExact`, `Ab.isMittagLeffler_X₃_of_shortExact`,
  `Ab.shortExact_lim_of_isMittagLeffler`: Stacks 02N1, the version for towers of abelian groups.
* `Ab.exact_lim_map_of_isMittagLeffler`: Stacks 070B, for an exact sequence `A → B → C → D` of
  towers of abelian groups with `A` Mittag-Leffler, `lim B → lim C → lim D` is exact.
* `ModuleCat.exists_limit_π_eq_of_sections`: a compatible family of elements of a tower of modules
  is the family of components of an element of the inverse limit.
* `ModuleCat.shortExact_lim_of_isMittagLeffler`, `ModuleCat.isMittagLeffler_X₃_of_shortExact`,
  `ModuleCat.exact_lim_map_of_isMittagLeffler`: the same two statements for towers of modules over
  a ring, which is the form in which towers of sections and of local cohomology arise.
* `isMittagLeffler_forget_iff_of_isEssentiallyConstantPro`: Stacks 070D, in a short exact sequence
  of inverse systems of abelian groups whose third term is essentially constant, the first term is
  Mittag-Leffler iff the second is.

## Implementation notes

The source deduces this lemma from its Mittag-Leffler criterion for an exact sequence of
directed inverse systems of abelian groups over a countable directed index set (Lemma 0598). That
statement is not available here, so the argument is carried out for the index category `ℕᵒᵖ`
directly. Only two features of `ℕᵒᵖ` are used: it is cofiltered, and a tower of surjections of
sets indexed by it has a section, which is Mathlib's
`CategoryTheory.Limits.Types.surjective_π_app_zero_of_surjective_map`.

The Mittag-Leffler condition is Mathlib's `CategoryTheory.Functor.IsMittagLeffler`, and the two
lemmas isolated below are the two steps of the source's proof of 0598 that are not formal:
`nonempty_sections_of_isMittagLeffler`, that a Mittag-Leffler tower of nonempty sets over `ℕᵒᵖ`
has a section (the source's Lemma 0597), and `isMittagLeffler_fibreTower`, that the tower of
fibres over a compatible family in `lim M` inherits the condition from `K`.

## References

* [Stacks Project, Tag 03CA](https://stacks.math.columbia.edu/tag/03CA)
-/

open CategoryTheory Limits

/-- The tower of fibres of a map of towers of sets over a fixed compatible family in the target:
at the index `n` it is the fibre of `g n` over `c n`. -/
private def fibreTower {J : Type*} [Category J] {X₂ X₃ : J ⥤ Type w} (g : X₂ ⟶ X₃)
    (c : X₃.sections) : J ⥤ Type w where
  obj n := {b : X₂.obj n // g.app n b = c.val n}
  map {m n} φ := ↾(fun b => (⟨X₂.map φ b.1, by
    have h1 := ConcreteCategory.congr_hom (g.naturality φ) b.1
    simp only [ConcreteCategory.comp_apply] at h1
    rw [h1, b.2, c.property φ]⟩ : {b : X₂.obj n // g.app n b = c.val n}))
  map_id n := by ext b; simp
  map_comp φ ψ := by ext b; simp

private theorem fibreTower_coe_map {J : Type*} [Category J] {X₂ X₃ : J ⥤ Type w} (g : X₂ ⟶ X₃)
    (c : X₃.sections) {m n : J} (φ : m ⟶ n) (b : (fibreTower g c).obj m) :
    ((fibreTower g c).map φ b).1 = X₂.map φ b.1 :=
  rfl

/-- The tower of fibres over a compatible family in `lim S.X₃` is Mittag-Leffler as soon as the
subobject tower `S.X₁` is: the fibre `E n` is a coset of the image of `S.X₁.obj n`, so
`im(E j → E n)` is a coset of `im(S.X₁.obj j → S.X₁.obj n)`, and cosets of one and the same
subgroup that are nested are equal. -/
private theorem isMittagLeffler_fibreTower {R : Type u} [Ring R]
    (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R))
    (hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj n)).ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler)
    (c : (S.X₃ ⋙ forget (ModuleCat.{v} R)).sections) :
    (fibreTower (Functor.whiskerRight S.g (forget (ModuleCat.{v} R))) c).IsMittagLeffler := by
  have hsurj : ∀ n : ℕᵒᵖ, Function.Surjective (S.g.app n) :=
    fun n => (ModuleCat.epi_iff_surjective _).1 (hS n).epi_g
  have hex : ∀ (n : ℕᵒᵖ) (x : S.X₂.obj n), S.g.app n x = 0 → ∃ y : S.X₁.obj n, S.f.app n y = x :=
    fun n => (S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj n)).moduleCat_exact_iff.1 (hS n).exact
  have hzero : ∀ (n : ℕᵒᵖ) (y : S.X₁.obj n), S.g.app n (S.f.app n y) = 0 :=
    fun n => (S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj n)).moduleCat_zero_apply
  refine (Functor.isMittagLeffler_iff_subset_range_comp _).2 fun n => ?_
  obtain ⟨m, φ₀, hφ₀⟩ := hML n
  refine ⟨m, φ₀, fun k χ y hy => ?_⟩
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨b', hb'⟩ := hsurj k (c.val k)
  have hb2 : S.g.app m b.1 = c.val m := b.2
  have hw2 : S.g.app m (S.X₂.map χ b') = c.val m := by
    rw [NatTrans.naturality_apply S.g χ b', hb']; exact c.property χ
  let bm : S.X₂.obj m := b.1
  have hkey : S.g.app m (bm - S.X₂.map χ b') = 0 := by
    rw [_root_.map_sub, hb2, hw2, sub_self]
  obtain ⟨a, ha⟩ := hex m _ hkey
  have hmem : (S.X₁ ⋙ forget (ModuleCat.{v} R)).map φ₀ a ∈
      Set.range ((S.X₁ ⋙ forget (ModuleCat.{v} R)).map (χ ≫ φ₀)) := hφ₀ (χ ≫ φ₀) ⟨a, rfl⟩
  obtain ⟨a', ha'⟩ := hmem
  have ha'' : S.X₁.map (χ ≫ φ₀) a' = S.X₁.map φ₀ a := ha'
  refine ⟨⟨b' + S.f.app k a', ?_⟩, ?_⟩
  · change S.g.app k (b' + S.f.app k a') = c.val k
    rw [_root_.map_add, hb', hzero k a', add_zero]
  · apply Subtype.ext
    change S.X₂.map (χ ≫ φ₀) (b' + S.f.app k a') = S.X₂.map φ₀ b.1
    have h1 : S.X₂.map (χ ≫ φ₀) (S.f.app k a') = S.X₂.map φ₀ (S.f.app m a) := by
      rw [← NatTrans.naturality_apply S.f (χ ≫ φ₀) a', ha'',
        NatTrans.naturality_apply S.f φ₀ a]
    have h2 : S.X₂.map (χ ≫ φ₀) b' = S.X₂.map φ₀ (S.X₂.map χ b') :=
      Functor.map_comp_apply _ _ _ _
    rw [_root_.map_add, h1, h2, ha, ← _root_.map_add]
    congr 1
    abel

/-- A compatible family of elements of a tower of `R`-modules is the family of components of an
element of the inverse limit. -/
private theorem exists_limit_π_eq {R : Type u} [Ring R] (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (s : (F ⋙ forget (ModuleCat.{v} R)).sections) :
    ∃ x : ToType (limit F), ∀ n, limit.π F n x = s.val n := by
  refine ⟨(Types.isLimitEquivSections (isLimitOfPreserves (forget (ModuleCat.{v} R))
    (limit.isLimit F))).symm s, fun n => ?_⟩
  simpa using Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves (forget (ModuleCat.{v} R)) (limit.isLimit F)) s n

/-- A compatible family of elements of a tower of `R`-modules is the family of components of an
element of the inverse limit. -/
alias ModuleCat.exists_limit_π_eq_of_sections := exists_limit_π_eq

private theorem limit_π_limMap {R : Type u} [Ring R] {F G : ℕᵒᵖ ⥤ ModuleCat.{v} R} (α : F ⟶ G)
    (n : ℕᵒᵖ) (x : ToType (limit F)) :
    limit.π G n (limMap α x) = α.app n (limit.π F n x) := by
  simp

private theorem map_limit_π {R : Type u} [Ring R] (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) {m n : ℕᵒᵖ}
    (φ : m ⟶ n) (x : ToType (limit F)) : F.map φ (limit.π F m x) = limit.π F n x := by
  simp

/-!
## Inverse limits of a tower of short exact sequences of modules

Let `R` be a ring and let

  `0 → K i → L i → M i → 0`,  `i : ℕ`,

be short exact sequences of `R`-modules fitting together into maps of short exact sequences, so
that `K (i + 1) → K i`, `L (i + 1) → L i` and `M (i + 1) → M i` are compatible with the given
maps. Such data is a short complex `S` of towers of `R`-modules, that is a short complex in the
category `ℕᵒᵖ ⥤ ModuleCat R`, which is short exact at every index. If the tower `K = S.X₁`
satisfies the Mittag-Leffler condition — for every `i` there is a `c ≥ i` with
`Im(K c → K i) = Im(K j → K i)` for all `j ≥ c` — then the sequence of inverse limits

  `0 → lim K → lim L → lim M → 0`

is short exact as well. Left exactness of `lim` is formal; the content of the lemma is that
`lim L → lim M` is surjective.

### Main results

* `CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler`: the inverse limit of a
  tower of short exact sequences of `R`-modules whose subobject tower is Mittag-Leffler is short
  exact.

### Implementation notes

A tower of `R`-modules is a functor `ℕᵒᵖ ⥤ ModuleCat R` and a map of towers is a natural
transformation, so a compatible family of short exact sequences of towers is a `ShortComplex` in
that functor category which becomes short exact after evaluation at each index. The source indexes
its systems by `i ≥ 1`; reindexing by all of `ℕ` is a cofinal shift, and changes neither the
Mittag-Leffler condition nor the three limits.

Short exactness is asked for index by index, as the source states it, rather than for `S` in the
functor category. Evaluation at an index is exact, so the pointwise form is implied by short
exactness of `S` in the functor category, and it is the form a user has at hand.

The Mittag-Leffler hypothesis is Mathlib's `CategoryTheory.Functor.IsMittagLeffler`, taken on the
underlying tower of sets `S.X₁ ⋙ forget (ModuleCat R)`. Over `ℕᵒᵖ` it says that for each `i` some
image `Im(K c → K i)` is contained in all the images `Im(K j → K i)`, which is exactly the
source's stabilization condition: those images decrease as `j` grows, so containment in all of
them forces equality for `j ≥ c`, while for `j ≤ c` the containment is automatic. A tower with
surjective transition maps is Mittag-Leffler by
`CategoryTheory.Functor.isMittagLeffler_of_surjective`, which is how the hypothesis is met in the
source's applications.

The conclusion is short exactness of the image of `S` under `CategoryTheory.Limits.lim`, so the
two maps of limits are `lim.map S.f` and `lim.map S.g`. In `ModuleCat R` it unfolds, by
`ModuleCat.mono_iff_injective`, `ShortComplex.moduleCat_exact_iff` and
`ModuleCat.epi_iff_surjective`, to injectivity of `lim K → lim L`, exactness at `lim L`, and
surjectivity of `lim L → lim M`.

The source deduces this lemma from its more general Mittag-Leffler criterion for an exact sequence
of directed inverse systems of abelian groups over a countable directed index set (Lemma 0598).

Faithfulness. (1) No hypothesis is idle: the pointwise short exact sequences supply the three
towers and both maps occurring in the conclusion, and the Mittag-Leffler hypothesis is what makes
`lim L → lim M` surjective — for `R = ℤ`, the tower `K i = 2 ^ i • ℤ` inside `L i = ℤ` with
quotients `M i = ℤ ⧸ 2 ^ i • ℤ` is short exact at every index and fails the condition, and there
`lim L = ℤ → lim M = ℤ₂` is not surjective. (2) The scalars are the source's: a single ring `R`
throughout, with all towers, all maps of towers and all three limits `R`-linear and no change of
rings; the statement is for an arbitrary, not necessarily commutative, ring, since commutativity
of `R` is nowhere used. (3) The canonical maps are pinned rather than asserted to exist: the
limits are the ones computed by `lim` and the maps between them are induced by the given maps of
towers, `lim.map S.f` and `lim.map S.g`. (4) The instantiation is not degenerate: for a short
exact sequence `0 → K → N → M → 0` of `R`-modules and an ideal `I ⊆ R`, the towers
`i ↦ K ⧸ (I ^ i • N ⊓ K)`, `i ↦ N ⧸ I ^ i • N` and `i ↦ M ⧸ I ^ i • M` have surjective transition
maps, hence are Mittag-Leffler, and the conclusion is the short exactness of
`0 → lim K/(Iⁿ N ∩ K) → N^∧ → M^∧ → 0` used by the source (Lemma 0315).

### References

* [Stacks Project, Tag 03CA](https://stacks.math.columbia.edu/tag/03CA)
-/

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

/-- **Stacks 03CA.** Let `R` be a ring and let `S` be a short complex of towers of `R`-modules,
that is of functors `ℕᵒᵖ ⥤ ModuleCat R`, which is short exact at every index: for each `i` the
sequence `0 → S.X₁ i → S.X₂ i → S.X₃ i → 0` is short exact. If the tower `S.X₁` satisfies the
Mittag-Leffler condition, that is for every `i` there is a `c ≥ i` with
`Im(S.X₁ c → S.X₁ i) = Im(S.X₁ j → S.X₁ i)` for all `j ≥ c`, then the sequence of inverse limits
`0 → lim S.X₁ → lim S.X₂ → lim S.X₃ → 0` is short exact. -/
@[stacks 03CA, ega "0 13.2.2" "ℕ-indexed systems", ega "III 4.1.7.21" "more general"]
public theorem shortExact_map_lim_of_isMittagLeffler {R : Type u} [Ring R]
    (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R))
    (hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj n)).ShortExact)
    (hML : (S.X₁ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler) :
    (S.map (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).ShortExact := by
  have hinj : ∀ n : ℕᵒᵖ, Function.Injective (S.f.app n) :=
    fun n => (ModuleCat.mono_iff_injective _).1 (hS n).mono_f
  have hsurj : ∀ n : ℕᵒᵖ, Function.Surjective (S.g.app n) :=
    fun n => (ModuleCat.epi_iff_surjective _).1 (hS n).epi_g
  have hex : ∀ (n : ℕᵒᵖ) (x : S.X₂.obj n), S.g.app n x = 0 → ∃ y : S.X₁.obj n, S.f.app n y = x :=
    fun n => (S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj n)).moduleCat_exact_iff.1 (hS n).exact
  have hfe : (S.map (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).f = limMap S.f := rfl
  have hge : (S.map (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).g = limMap S.g := rfl
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · -- exactness at `lim S.X₂`
    refine (S.map (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).moduleCat_exact_iff.2 ?_
    simp only [hfe, hge]
    intro y hy
    have hy' : ∀ n : ℕᵒᵖ, S.g.app n (limit.π S.X₂ n y) = 0 := by
      intro n
      rw [← limit_π_limMap S.g n y, hy, map_zero]
    choose a ha using fun n => hex n _ (hy' n)
    have hcompat : ∀ {m n : ℕᵒᵖ} (φ : m ⟶ n), S.X₁.map φ (a m) = a n := by
      intro m n φ
      refine hinj n ?_
      rw [NatTrans.naturality_apply S.f φ (a m), ha m, ha n, map_limit_π]
    obtain ⟨x, hx⟩ := exists_limit_π_eq S.X₁ ⟨a, fun φ => hcompat φ⟩
    refine ⟨x, Concrete.limit_ext S.X₂ _ _ fun n => ?_⟩
    have hxn : limit.π S.X₁ n x = a n := hx n
    rw [limit_π_limMap S.f n x, hxn, ha n]
  · -- injectivity of `lim S.X₁ → lim S.X₂`
    rw [hfe]
    refine (ModuleCat.mono_iff_injective _).2 fun x x' hxx' => ?_
    refine Concrete.limit_ext S.X₁ _ _ fun n => hinj n ?_
    rw [← limit_π_limMap S.f n x, ← limit_π_limMap S.f n x']
    exact congrArg (limit.π S.X₂ n) hxx'
  · -- surjectivity of `lim S.X₂ → lim S.X₃`
    rw [hge]
    refine (ModuleCat.epi_iff_surjective _).2 fun z => ?_
    obtain ⟨c, hc⟩ : ∃ c : (S.X₃ ⋙ forget (ModuleCat.{v} R)).sections,
        ∀ n, c.val n = limit.π S.X₃ n z :=
      ⟨⟨fun n => limit.π S.X₃ n z, fun φ => map_limit_π S.X₃ φ z⟩, fun n => rfl⟩
    obtain ⟨sec⟩ := nonempty_sections_of_isMittagLeffler
      (isMittagLeffler_fibreTower S hS hML c)
      (fun n => let ⟨b, hb⟩ := hsurj n (c.val n); ⟨⟨b, hb⟩⟩)
    have hcompat : ∀ {m n : ℕᵒᵖ} (φ : m ⟶ n), S.X₂.map φ (sec.val m).1 = (sec.val n).1 :=
      fun {_ _} φ => (fibreTower_coe_map _ _ φ (sec.val _)).symm.trans
        (congrArg (fun t => t.1) (sec.property φ))
    obtain ⟨x, hx⟩ := exists_limit_π_eq S.X₂ ⟨fun n => (sec.val n).1, fun φ => hcompat φ⟩
    refine ⟨x, Concrete.limit_ext S.X₃ _ _ fun n => ?_⟩
    have hxn : limit.π S.X₂ n x = (sec.val n).1 := hx n
    rw [limit_π_limMap S.g n x, hxn, ← hc n]
    exact (sec.val n).2

end CategoryTheory.ShortComplex

section

/-!
## Mittag-Leffler condition for inverse systems of abelian groups

For a short exact sequence `0 → (A_i) → (B_i) → (C_i) → 0` of inverse
systems of abelian groups indexed by `ℕᵒᵖ`:

* The induced sequence `0 → lim A → lim B → lim C` is exact.
* If `(B_i)` is ML, then so is `(C_i)`.
* If `(A_i)` is ML, then `0 → lim A → lim B → lim C → 0` is short exact.

The last statement is deduced from its version for modules,
`CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler`, by regarding abelian groups
as `ℤ`-modules.
-/

open CategoryTheory CategoryTheory.Limits


/-- The image of a Mittag-Leffler inverse system of sets under a pointwise surjective map of
inverse systems is Mittag-Leffler. -/
lemma IsMittagLeffler_of_surjective_natTrans
    {B C : ℕᵒᵖ ⥤ Type u} (α : B ⟶ C)
    (hα : ∀ i, Function.Surjective (α.app i))
    (hB : B.IsMittagLeffler) : C.IsMittagLeffler := by
  apply (C.isMittagLeffler_iff_subset_range_comp).2
  intro j
  obtain ⟨i, f, hf⟩ := (B.isMittagLeffler_iff_subset_range_comp).1 hB j
  refine ⟨i, f, fun k g y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨a, rfl⟩ := hα i x
  obtain ⟨b, hb⟩ := hf g ⟨a, rfl⟩
  refine ⟨α.app k b, ?_⟩
  rw [← NatTrans.naturality_apply α (g ≫ f), hb,
    NatTrans.naturality_apply α f]

/-- Abelian groups with their canonical integer-module structure. -/
@[implicit_reducible]
private def abToIntModules : Ab.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

/-- Forgetting the `ℤ`-module structure of an abelian group gives back the abelian group. -/
private def abToIntModulesCompForget₂ :
    abToIntModules ⋙ forget₂ (ModuleCat.{u} ℤ) Ab.{u} ≅ 𝟭 Ab.{u} :=
  NatIso.ofComponents (fun A => Iso.refl A)

private instance : abToIntModules.{u}.IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((Functor.isoWhiskerLeft _ (forget₂ (ModuleCat.{u} ℤ) Ab.{u}).asEquivalence.unitIso).trans
      ((Functor.associator _ _ _).symm.trans
        ((Functor.isoWhiskerRight abToIntModulesCompForget₂ _).trans
          (Functor.leftUnitor _)))).symm

/-- Taking limits commutes with regarding abelian groups as `ℤ`-modules and back. -/
private noncomputable def limIsoOfIntModules :
    ((Functor.whiskeringRight ℕᵒᵖ Ab.{u} (ModuleCat.{u} ℤ)).obj abToIntModules.{u} ⋙ lim) ⋙
      forget₂ (ModuleCat.{u} ℤ) Ab.{u} ≅ (lim : (ℕᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u}) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (preservesLimitNatIso (forget₂ (ModuleCat.{u} ℤ) Ab.{u})) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso abToIntModulesCompForget₂.{u} ≪≫
        Functor.whiskeringRightObjIdIso) lim ≪≫
    Functor.leftUnitor _

/-- Part (1): for any short exact sequence of inverse systems, the limit
sequence `0 → lim A → lim B → lim C` is exact. -/
@[stacks 02N1 "left_exact"]
theorem Ab.mono_lim_map_and_exact_of_shortExact
    (S : ShortComplex (ℕᵒᵖ ⥤ Ab.{u})) (h : S.ShortExact) :
    Mono (S.map (lim : (ℕᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u})).f ∧
      (S.map (lim : (ℕᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u})).Exact := by
  have := h.mono_f
  exact ⟨inferInstanceAs (Mono (lim.map S.f)),
    h.exact.map_of_mono_of_preservesKernel _ h.mono_f inferInstance⟩

/-- Part (2): a quotient of a Mittag-Leffler inverse system is Mittag-Leffler. -/
@[stacks 02N1 "ML_quotient", ega "0 13.2.1" "(i), systems over ℕ", sga "5 V 2.1.2" "(i)"]
theorem Ab.isMittagLeffler_X₃_of_shortExact
    (S : ShortComplex (ℕᵒᵖ ⥤ Ab.{u})) (h : S.ShortExact)
    (hB : (S.X₂ ⋙ forget Ab).IsMittagLeffler) : (S.X₃ ⋙ forget Ab).IsMittagLeffler :=
  IsMittagLeffler_of_surjective_natTrans (Functor.whiskerRight S.g (forget Ab))
    (fun i => (AddCommGrpCat.epi_iff_surjective _).1
      (h.map_of_exact ((evaluation ℕᵒᵖ Ab.{u}).obj i)).epi_g) hB

/-- Part (3): if the kernel system is Mittag-Leffler, then the limit sequence
`0 → lim A → lim B → lim C → 0` is short exact. -/
@[stacks 02N1 "ML_short_exact", ega "0 13.2.2" "systems over ℕ"]
theorem Ab.shortExact_lim_of_isMittagLeffler
    (S : ShortComplex (ℕᵒᵖ ⥤ Ab.{u})) (h : S.ShortExact)
    (hA : (S.X₁ ⋙ forget Ab).IsMittagLeffler) :
    (S.map (lim : (ℕᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u})).ShortExact := by
  let L := (Functor.whiskeringRight ℕᵒᵖ Ab.{u} (ModuleCat.{u} ℤ)).obj abToIntModules
  have hT := h.map_of_exact L
  have hlim := (S.map L).shortExact_map_lim_of_isMittagLeffler
    (fun i => hT.map_of_exact ((evaluation ℕᵒᵖ (ModuleCat.{u} ℤ)).obj i)) hA
  refine ShortComplex.shortExact_of_iso (S.mapNatIso limIsoOfIntModules) ?_
  rw [ShortComplex.map_comp, ShortComplex.map_comp]
  exact hlim.map_of_exact _

end

section

/-!
## Stacks tag 070B

Applying the Mittag-Leffler condition: given an exact sequence of inverse
systems `A → B → C → D` of abelian groups indexed by `ℕ`, if `A` satisfies the
Mittag-Leffler condition then `lim B → lim C → lim D` is exact.
-/

open CategoryTheory CategoryTheory.Limits

/-- Stacks 070B in an abelian category with `ℕᵒᵖ`-limits, for a property `P` of towers that passes
from the middle to the third term of a short exact sequence and under which `lim` preserves
epimorphisms of short exact sequences. -/
private theorem exact_lim_map_of_isMittagLeffler_aux {T : Type*} [Category T] [Abelian T]
    [HasLimitsOfShape ℕᵒᵖ T] (P : (ℕᵒᵖ ⥤ T) → Prop)
    (hquot : ∀ S : ShortComplex (ℕᵒᵖ ⥤ T), S.ShortExact → P S.X₂ → P S.X₃)
    (hlim : ∀ S : ShortComplex (ℕᵒᵖ ⥤ T), S.ShortExact → P S.X₁ → Epi (lim.map S.g))
    {A B C D : ℕᵒᵖ ⥤ T} (φ : A ⟶ B) (ψ : B ⟶ C) (χ : C ⟶ D)
    (hφψ : φ ≫ ψ = 0) (hψχ : ψ ≫ χ = 0)
    (hAB : (ShortComplex.mk φ ψ hφψ).Exact) (hBC : (ShortComplex.mk ψ χ hψχ).Exact)
    (hA : P A) :
    (ShortComplex.mk (lim.map ψ) (lim.map χ)
      (by rw [← lim.map_comp, hψχ, Functor.map_zero])).Exact := by
  let ψ' : B ⟶ kernel χ := kernel.lift χ ψ hψχ
  have hψ' : Epi ψ' := hBC.epi_kernelLift
  have hφψ' : φ ≫ ψ' = 0 := by
    rw [← cancel_mono (kernel.ι χ), Category.assoc, kernel.lift_ι, hφψ, zero_comp]
  let φ' : A ⟶ kernel ψ' := kernel.lift ψ' φ hφψ'
  have hφ' : Epi φ' := by
    let α : ShortComplex.mk φ ψ' hφψ' ⟶ ShortComplex.mk φ ψ hφψ :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι χ, comm₂₃ := by simp [ψ'] }
    have : Mono α.τ₃ := inferInstanceAs (Mono (kernel.ι χ))
    have : IsIso α.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Epi α.τ₁ := inferInstanceAs (Epi (𝟙 _))
    exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).2 hAB).epi_kernelLift
  have hS₁ : (ShortComplex.mk (kernel.ι φ') φ' (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ') }
  have hS₂ : (ShortComplex.mk (kernel.ι ψ') ψ' (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel ψ') }
  have : Epi (lim.map ψ') :=
    hlim _ hS₂ (hquot _ hS₁ hA)
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have e : kernel.lift (lim.map χ) (lim.map ψ) (by rw [← lim.map_comp, hψχ, Functor.map_zero]) =
      lim.map ψ' ≫ kernelComparison χ lim := by
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, Category.assoc, kernelComparison_comp_ι,
      ← lim.map_comp, kernel.lift_ι]
  rw [e]
  exact epi_comp _ _

/-- Let `A → B → C → D` be an exact sequence of inverse systems of abelian groups indexed by
`ℕ`. If `A` satisfies the Mittag-Leffler condition, then the induced sequence on inverse limits
`lim B → lim C → lim D` is exact at `lim C`.

The proof is the source's: `ψ` factors through `K = Ker(χ)` by an epimorphism `ψ'`, whose kernel
is a quotient of `A`, hence Mittag-Leffler (02N1); so `lim B → lim K` is onto (02N1), and
`lim K = Ker(lim χ)` because `lim` preserves kernels. -/
@[stacks 070B, ega "0 13.2.2" "partial"]
theorem Ab.exact_lim_map_of_isMittagLeffler {A B C D : ℕᵒᵖ ⥤ Ab.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (χ : C ⟶ D)
    (hφψ : φ ≫ ψ = 0) (hψχ : ψ ≫ χ = 0)
    (hAB : (ShortComplex.mk φ ψ hφψ).Exact) (hBC : (ShortComplex.mk ψ χ hψχ).Exact)
    (hML : (A ⋙ forget Ab).IsMittagLeffler) :
    (ShortComplex.mk (lim.map ψ) (lim.map χ)
      (by rw [← lim.map_comp, hψχ, Functor.map_zero])).Exact := by
  exact exact_lim_map_of_isMittagLeffler_aux (fun F => (F ⋙ forget Ab).IsMittagLeffler)
    (fun S h => Ab.isMittagLeffler_X₃_of_shortExact S h)
    (fun S h hA => (Ab.shortExact_lim_of_isMittagLeffler S h hA).epi_g) φ ψ χ hφψ hψχ hAB hBC hML

/-- Stacks 02N1 part (3) for towers of modules: if the kernel system is Mittag-Leffler, then the
limit sequence `0 → lim A → lim B → lim C → 0` is short exact. This is
`CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler` with the pointwise short
exactness obtained from short exactness in the functor category, evaluation being exact. -/
@[stacks 02N1 "ML_short_exact, for towers of modules",
  ega "0 13.2.2" "ℕ-indexed systems",
  ega "III 4.1.7.21" "more general"]
theorem ModuleCat.shortExact_lim_of_isMittagLeffler {R : Type u} [Ring R]
    (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R)) (h : S.ShortExact)
    (hA : (S.X₁ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler) :
    (S.map (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).ShortExact :=
  CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler S
    (fun n => h.map_of_exact ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj n)) hA

/-- Stacks 02N1 part (2) for towers of modules: a quotient of a Mittag-Leffler inverse system is
Mittag-Leffler. -/
@[stacks 02N1 "ML_quotient, for towers of modules"]
theorem ModuleCat.isMittagLeffler_X₃_of_shortExact {R : Type u} [Ring R]
    (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R)) (h : S.ShortExact)
    (hB : (S.X₂ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler) :
    (S.X₃ ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler :=
  IsMittagLeffler_of_surjective_natTrans
    (Functor.whiskerRight S.g (forget (ModuleCat.{v} R)))
    (fun i => (ModuleCat.epi_iff_surjective _).1
      (h.map_of_exact ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj i)).epi_g) hB

/-- **Stacks 070B for towers of modules.** Let `A → B → C → D` be an exact sequence of inverse
systems of `R`-modules indexed by `ℕ`. If `A` satisfies the Mittag-Leffler condition, then the
induced sequence on inverse limits `lim B → lim C → lim D` is exact at `lim C`.

This is the same argument as `Ab.exact_lim_map_of_isMittagLeffler`, run with the two inputs for
towers of modules: `ψ` factors through `K = Ker(χ)` by an epimorphism `ψ'`, whose kernel is a
quotient of `A`, hence Mittag-Leffler; so `lim B → lim K` is onto, and `lim K = Ker(lim χ)`
because `lim` preserves kernels. -/
@[stacks 070B "for towers of modules", ega "0 13.2.2" "partial"]
theorem ModuleCat.exact_lim_map_of_isMittagLeffler {R : Type u} [Ring R]
    {A B C D : ℕᵒᵖ ⥤ ModuleCat.{v} R} (φ : A ⟶ B) (ψ : B ⟶ C) (χ : C ⟶ D)
    (hφψ : φ ≫ ψ = 0) (hψχ : ψ ≫ χ = 0)
    (hAB : (ShortComplex.mk φ ψ hφψ).Exact) (hBC : (ShortComplex.mk ψ χ hψχ).Exact)
    (hML : (A ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler) :
    (ShortComplex.mk (lim.map ψ) (lim.map χ)
      (by rw [← lim.map_comp, hψχ, Functor.map_zero])).Exact := by
  exact exact_lim_map_of_isMittagLeffler_aux
    (fun F => (F ⋙ forget (ModuleCat.{v} R)).IsMittagLeffler)
    (fun S h => ModuleCat.isMittagLeffler_X₃_of_shortExact S h)
    (fun S h hA => (ModuleCat.shortExact_lim_of_isMittagLeffler S h hA).epi_g)
    φ ψ χ hφψ hψχ hAB hBC hML

end

section

/-!
## Stacks tag 070D

Let `0 → (A_i) → (B_i) → (C_i) → 0` be a short exact sequence of inverse
systems of abelian groups indexed by a cofiltered category `J`. If `(C_i)` is
essentially constant, then `(A_i)` has the Mittag-Leffler property iff
`(B_i)` does.

Essential constancy is `CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro`
(Stacks 05PU for inverse systems). After restricting to the objects over the index `i` of the
witness, the cone of the witness has injective legs, and every object `k` admits a transition map
into it whose image lies in the image of the leg at `k`. These two properties are all the proof
uses, see `isMittagLeffler_forget_iff_of_cone`.
-/

open CategoryTheory CategoryTheory.Limits

/-- The Mittag-Leffler condition for an inverse system of abelian groups, read on subgroups: for
every `j` some `f : i ⟶ j` has image contained in the image of every `g : k ⟶ j`. -/
lemma isMittagLeffler_forget_iff {J : Type*} [Category J] (F : J ⥤ Ab) :
    (F ⋙ forget Ab).IsMittagLeffler ↔ ∀ (j : J), ∃ (i : J) (f : i ⟶ j),
      ∀ ⦃k : J⦄ (g : k ⟶ j), (F.map f).hom.range ≤ (F.map g).hom.range :=
  Iff.rfl

/-- Descent of ML along `Over.forget i₀`. -/
lemma isMittagLeffler_forget_descend {J : Type*} [Category J] (i₀ : J) (F : J ⥤ Ab)
    (h : (F ⋙ forget Ab).IsMittagLeffler) :
    ((Over.forget i₀ ⋙ F) ⋙ forget Ab).IsMittagLeffler := by
  rw [isMittagLeffler_forget_iff] at *
  intro X
  obtain ⟨i, f, hf⟩ := h X.left
  refine ⟨Over.mk (f ≫ X.hom), Over.homMk f, ?_⟩
  intro Y g
  simpa only [Functor.comp_map, Over.forget_map, Over.homMk_left] using hf g.left

/-- Ascent of ML along `Over.forget i₀` when `J` is cofiltered. -/
lemma isMittagLeffler_forget_ascend {J : Type*} [Category J] [IsCofiltered J]
    (i₀ : J) (F : J ⥤ Ab) (h : ((Over.forget i₀ ⋙ F) ⋙ forget Ab).IsMittagLeffler) :
    (F ⋙ forget Ab).IsMittagLeffler := by
  rw [isMittagLeffler_forget_iff] at *
  intro j
  obtain ⟨i, p, q, _⟩ := IsCofilteredOrEmpty.cone_objs j i₀
  obtain ⟨X, f, hf⟩ := h (Over.mk q)
  refine ⟨X.left, f.left ≫ p, ?_⟩
  intro k g x hx
  obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan p g
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, hz⟩ := hf (Over.homMk a : Over.mk (a ≫ q) ⟶ Over.mk q) ⟨y, rfl⟩
  refine ⟨(F.map b).hom z, ?_⟩
  simp only [Functor.comp_map, Over.forget_map, Over.homMk_left] at hz
  calc
    (F.map g).hom ((F.map b).hom z) = (F.map p).hom ((F.map a).hom z) := by
      simpa only [Functor.map_comp, AddCommGrpCat.comp_apply] using
        congrArg (fun t => (F.map t).hom z) hab.symm
    _ = (F.map (f.left ≫ p)).hom y := by
      rw [hz, Functor.map_comp, AddCommGrpCat.comp_apply]
    _ = x := hy

/-- ML on `J` is equivalent to ML on `Over i₀`. -/
lemma isMittagLeffler_forget_over_iff {J : Type*} [Category J] [IsCofiltered J]
    (i₀ : J) (F : J ⥤ Ab) :
    (F ⋙ forget Ab).IsMittagLeffler ↔ ((Over.forget i₀ ⋙ F) ⋙ forget Ab).IsMittagLeffler :=
  ⟨isMittagLeffler_forget_descend i₀ F, isMittagLeffler_forget_ascend i₀ F⟩

section Cone

variable {K : Type*} [Category K] (S : ShortComplex (K ⥤ Ab))

/-- If `S.X₁` has ML, so does `S.X₂`, provided that every object `k` admits a transition map
into it whose image lies in the image of the leg at `k` of a cone over `S.X₃`. -/
lemma isMittagLeffler_forget_of_cone_of_shortExact [IsCofiltered K] (hS : S.ShortExact)
    (c : Cone S.X₃)
    (hcof : ∀ k, ∃ (l : K) (τ : l ⟶ k), ∀ z, ∃ x, (S.X₃.map τ).hom z = (c.π.app k).hom x)
    (hA : (S.X₁ ⋙ forget Ab).IsMittagLeffler) : (S.X₂ ⋙ forget Ab).IsMittagLeffler := by
  rw [isMittagLeffler_forget_iff] at *
  have hpoint (i : K) := hS.map_of_exact ((evaluation K Ab).obj i)
  have hsurj (i : K) : Function.Surjective (S.g.app i).hom :=
    (AddCommGrpCat.epi_iff_surjective _).1 (hpoint i).epi_g
  have hexact (i : K) (y : S.X₂.obj i) (hy : (S.g.app i).hom y = 0) :
      ∃ x, (S.f.app i).hom x = y :=
    (ShortComplex.ab_exact_iff _).1 (hpoint i).exact y hy
  intro j
  obtain ⟨a, fA, hfA⟩ := hA j
  obtain ⟨l, τ, hτ⟩ := hcof a
  refine ⟨l, τ ≫ fA, ?_⟩
  rintro k g _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := hτ ((S.g.app l).hom y)
  obtain ⟨m, α, β, hαβ⟩ := IsCofiltered.cospan g fA
  obtain ⟨w, hw⟩ := hsurj m ((c.π.app m).hom x)
  have hker : (S.g.app a).hom ((S.X₂.map τ).hom y - (S.X₂.map β).hom w) = 0 := by
    rw [map_sub, S.g.naturality_apply, S.g.naturality_apply, hx, hw,
      ← AddCommGrpCat.comp_apply, c.w, sub_self]
  obtain ⟨d, hd⟩ := hexact a _ hker
  obtain ⟨e, he⟩ := hfA (α ≫ g) ⟨d, rfl⟩
  refine ⟨(S.X₂.map α).hom w + (S.f.app k).hom ((S.X₁.map α).hom e), ?_⟩
  calc
    _ = (S.X₂.map (α ≫ g)).hom w + (S.f.app j).hom ((S.X₁.map (α ≫ g)).hom e) := by
      simp
    _ = (S.X₂.map fA).hom ((S.X₂.map β).hom w + (S.f.app a).hom d) := by
      rw [he, hαβ, S.f.naturality_apply, Functor.map_comp, AddCommGrpCat.comp_apply, map_add]
    _ = _ := by rw [hd, add_sub_cancel, Functor.map_comp, AddCommGrpCat.comp_apply]

/-- If `S.X₂` has ML, so does `S.X₁`, provided that the legs of a cone over `S.X₃` are injective
and every object `k` admits a transition map into it whose image lies in the image of the leg
at `k`. -/
lemma isMittagLeffler_forget_of_cone_of_shortExact' (hS : S.ShortExact) (c : Cone S.X₃)
    (hinj : ∀ k, Function.Injective (c.π.app k).hom)
    (hcof : ∀ k, ∃ (l : K) (τ : l ⟶ k), ∀ z, ∃ x, (S.X₃.map τ).hom z = (c.π.app k).hom x)
    (hB : (S.X₂ ⋙ forget Ab).IsMittagLeffler) : (S.X₁ ⋙ forget Ab).IsMittagLeffler := by
  rw [isMittagLeffler_forget_iff] at *
  have hpoint (i : K) := hS.map_of_exact ((evaluation K Ab).obj i)
  have hinjf (i : K) : Function.Injective (S.f.app i).hom :=
    (AddCommGrpCat.mono_iff_injective _).1 (hpoint i).mono_f
  have hexact (i : K) (y : S.X₂.obj i) (hy : (S.g.app i).hom y = 0) :
      ∃ x, (S.f.app i).hom x = y :=
    (ShortComplex.ab_exact_iff _).1 (hpoint i).exact y hy
  have hzero (i : K) (x : S.X₁.obj i) : (S.g.app i).hom ((S.f.app i).hom x) = 0 :=
    (S.map ((evaluation K Ab).obj i)).ab_zero_apply x
  intro j
  obtain ⟨b, fB, hfB⟩ := hB j
  refine ⟨b, fB, ?_⟩
  rintro k g _ ⟨a, rfl⟩
  obtain ⟨l, τ, hτ⟩ := hcof k
  obtain ⟨y, hy⟩ := hfB (τ ≫ g) ⟨(S.f.app b).hom a, rfl⟩
  obtain ⟨x, hx⟩ := hτ ((S.g.app l).hom y)
  have hx0 : x = 0 := hinj j (by
    rw [map_zero, ← c.w g, AddCommGrpCat.comp_apply, ← hx, ← AddCommGrpCat.comp_apply,
      ← Functor.map_comp, ← S.g.naturality_apply, hy, ← S.f.naturality_apply, hzero])
  obtain ⟨e, he⟩ := hexact k ((S.X₂.map τ).hom y) (by rw [S.g.naturality_apply, hx, hx0, map_zero])
  refine ⟨e, hinjf j ?_⟩
  rw [S.f.naturality_apply, S.f.naturality_apply, he, ← AddCommGrpCat.comp_apply,
    ← Functor.map_comp, hy]

/-- `S.X₁` has ML iff `S.X₂` does, provided that the legs of a cone over `S.X₃` are injective
and every object `k` admits a transition map into it whose image lies in the image of the leg
at `k`. -/
lemma isMittagLeffler_forget_iff_of_cone [IsCofiltered K] (hS : S.ShortExact) (c : Cone S.X₃)
    (hinj : ∀ k, Function.Injective (c.π.app k).hom)
    (hcof : ∀ k, ∃ (l : K) (τ : l ⟶ k), ∀ z, ∃ x, (S.X₃.map τ).hom z = (c.π.app k).hom x) :
    (S.X₁ ⋙ forget Ab).IsMittagLeffler ↔ (S.X₂ ⋙ forget Ab).IsMittagLeffler :=
  ⟨isMittagLeffler_forget_of_cone_of_shortExact S hS c hcof,
    isMittagLeffler_forget_of_cone_of_shortExact' S hS c hinj hcof⟩

end Cone

/-- The whiskered short complex on `Over i₀`. -/
@[implicit_reducible]
noncomputable def whiskerOverShortComplex {J : Type*} [Category J] (i₀ : J)
    (S : ShortComplex (J ⥤ Ab)) : ShortComplex (Over i₀ ⥤ Ab) :=
  ShortComplex.mk (Functor.whiskerLeft (Over.forget i₀) S.f)
                  (Functor.whiskerLeft (Over.forget i₀) S.g)
    (by
      ext X : 2
      rw [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app, ← NatTrans.comp_app,
        S.zero, NatTrans.app_zero, NatTrans.app_zero])

lemma whiskerOverShortComplex_X₃_map {J : Type*} [Category J] (i₀ : J)
    (S : ShortComplex (J ⥤ Ab)) {X Y : Over i₀} (φ : X ⟶ Y) :
    (whiskerOverShortComplex i₀ S).X₃.map φ = S.X₃.map φ.left :=
  rfl

/-- The whiskered short complex remains short exact. -/
lemma whiskerOverShortComplex_shortExact {J : Type*} [Category J] (i₀ : J)
    (S : ShortComplex (J ⥤ Ab)) (hS : S.ShortExact) :
    (whiskerOverShortComplex i₀ S).ShortExact :=
  hS.map_of_exact ((Functor.whiskeringLeft (Over i₀) J Ab).obj (Over.forget i₀))

/-- Let `0 → (A_i) → (B_i) → (C_i) → 0` be a short exact sequence of inverse
systems of abelian groups indexed by a cofiltered category `J`. If `(C_i)` is
essentially constant, then `(A_i)` has the Mittag-Leffler property iff
`(B_i)` does. -/
@[stacks 070D]
theorem isMittagLeffler_forget_iff_of_isEssentiallyConstantPro
    {J : Type*} [Category J] [IsCofiltered J]
    (S : ShortComplex (J ⥤ Ab))
    (hS : S.ShortExact)
    (hC : EssentiallyConstantPro.IsEssentiallyConstantPro S.X₃) :
    (S.X₁ ⋙ forget Ab).IsMittagLeffler ↔ (S.X₂ ⋙ forget Ab).IsMittagLeffler := by
  obtain ⟨c, i, s, hs⟩ := hC
  rw [isMittagLeffler_forget_over_iff i S.X₁, isMittagLeffler_forget_over_iff i S.X₂]
  refine isMittagLeffler_forget_iff_of_cone (whiskerOverShortComplex i S)
    (whiskerOverShortComplex_shortExact i S hS) (c.whisker (Over.forget i)) (fun k => ?_)
    (fun k => ?_)
  · have h : c.π.app k.left ≫ S.X₃.map k.hom ≫ s = 𝟙 c.pt := by
      rw [← Category.assoc, c.w, hs.retraction]
    simp only [Cone.whisker_π, Functor.whiskerLeft_app, Over.forget_obj]
    exact (AddCommGrpCat.mono_iff_injective _).1 (SplitMono.mono ⟨_, h⟩)
  · obtain ⟨l, σ, τ, h⟩ := hs.cofinal k.left
    refine ⟨Over.mk (τ ≫ k.hom), Over.homMk τ, fun z => ⟨(S.X₃.map σ ≫ s).hom z, ?_⟩⟩
    simp only [Cone.whisker_π, Functor.whiskerLeft_app, Over.forget_obj]
    simp only [whiskerOverShortComplex_X₃_map, Over.homMk_left]
    rw [h, ← Category.assoc, AddCommGrpCat.comp_apply]

end
