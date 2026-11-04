module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.MeasureComparisonUpper
public import StacksFrontier.AlgebraicGeometry.Pushout.ColimitSections

/-!
# The elementary-step branch of [Stacks, Tag 0C1L]

The hypothesis `hsplit` of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` is a
dichotomy: an almost isomorphism `g` is either already a chain of elementary modifications, or it
splits into two almost isomorphisms of strictly smaller measure. The *splitting* branch is
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt_of_ne`, which needs two distinct
points at which the stalk extension `𝒪_{X,x} ⊂ (g_*𝒪_{X'})_x` is proper. **This file supplies the
other branch**, and with it the whole of `hsplit` except for one statement.

## The dichotomy is taken on the stalk extensions

The bad set is `Stacks.GlueSquishFactor.badSet g`, the set of points at which the stalk map
`𝒪_{X,x} ⟶ (g_*𝒪_{X'})_x` fails to be surjective. That is neither of the two sets one might
expect, and the choice is what makes the file short.

* It is **not** `IsZero`-locus of the cokernel `g_*𝒪_{X'}/𝒪_X`. The two sets coincide, but the
  comparison costs a bridge between `SheafOfModules.supp` of that cokernel — a stalk of a sheaf of
  modules, computed by `AlgebraicGeometry.Scheme.Modules.stalkFunctor` — and
  `Stacks.GlueSquishFactor.stalkPushforwardMap`, the stalk of `g.c` in `CommRingCat`. No such
  bridge exists in the tree, and none is needed: both consumers of the bad set speak the stalk
  form. The splitting branch asks for `⊥ ≠ ⊤` in
  `Subalgebra 𝒪_{X,x} (g_*𝒪_{X'})_x`, which is
  `Stacks.GlueSquishFactor.bot_ne_top_iff_mem_badSet`, and the elementary-step branch asks for
  surjectivity through `Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range`, which is
  phrased in `stalkPushforwardMap` too.
* It is **not** the complement of the open `U` that `Stacks.GlueSquishFactor.IsAlmostIsoCore`
  provides. That open is merely *some* open with finite complement on which `g` restricts to an
  isomorphism; at a point of its complement the stalk extension may well be trivial, so two such
  points do not give the splitting branch what it asks for.

## The converse of `isZero_stalk_cokernel_structureUnitHom`

With the bad set a single point `x₀`, the hypothesis `hiso` of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` — an
isomorphism over the complement of *that* point — is exactly the converse direction of
`Stacks.GlueSquishFactor.isZero_stalk_cokernel_structureUnitHom`, which the tree did not have:
from surjectivity of the stalk maps on an open, an isomorphism over that open. It is proved here
in three steps and needs no quasi-coherence, no coherence and no affine exactness:

* `Stacks.GlueSquishFactor.surjective_app_of_forall_surjective_stalkPushforwardMap` — a section of
  `g_*𝒪_{X'}` over `W` is *locally* in the image of `g.app` by
  `Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range`, the local preimages agree on overlaps
  because `g.app` is injective (`Mono (pushforwardAlgebra g).hom`), and they glue by the sheaf
  axiom for `𝒪_X`; the glued section has the right image by the sheaf axiom for `𝒪_{X'}` on the
  preimage cover. This is the whole content: `TopCat.Sheaf.existsUnique_gluing'` and
  `TopCat.Sheaf.eq_of_locally_eq'` on the two structure sheaves.
* `Stacks.GlueSquishFactor.isIso_morphismRestrict_of_forall_surjective_stalkPushforwardMap` —
  bijectivity of `g.app W` on affine opens `W` of the given open is an isomorphism over it, by
  `Stacks.Pushout.isIso_morphismRestrict_of_forall_isIso_app`.
* `Stacks.GlueSquishFactor.isIso_of_forall_surjective_stalkPushforwardMap` — the same at `⊤`,
  which is the empty-bad-set case of the dichotomy: there `g` is an isomorphism, hence the empty
  chain `Stacks.GlueSquishFactor.IsElementaryChain.of_isIso`.

## Main results

* `Stacks.GlueSquishFactor.exists_isIso_morphismRestrict_compl_singleton` — **`hiso`**: from a
  single closed bad point, an isomorphism over its complement.
* `Stacks.GlueSquishFactor.exists_split_measureOver_lt_or_forall_isFinite_subalg` — **`hno`**:
  either the splitting branch holds, or no finite quasi-coherent subalgebra proper over an affine
  open captures a section outside `𝒪_X`. The negative case of the `by_cases` is fed to
  `Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt` through the two properness
  readings `Stacks.GlueSquishFactor.nonempty_supp_cokernel_unitModuleMap_of_notMem_range` and
  `Stacks.GlueSquishFactor.nonempty_supp_cokernel_underlyingModuleMap_incl`. This is the
  hypothesis `hno` of
  `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg`, from which
  `Stacks.GlueSquishFactor.forall_eq_bot_or_eq_top_of_forall_isFinite_subalg` derives `hmin`.
* `Stacks.GlueSquishFactor.isCoherent_underlyingModule_pushforwardAlgebra_of_isAlmostIso` and
  `Stacks.GlueSquishFactor.isCoherent_cokernel_structureUnitHom_of_isAlmostIso` — **the coherence
  hypotheses of the measure results, discharged.** Every measure drop in the tree carries
  coherence of `g_*𝒪_{X'}/𝒪_X` as an undischarged hypothesis `hcoh`; it is in fact free for an
  almost isomorphism. An algebraic `k`-scheme is locally Noetherian
  (`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`), there the structure sheaf is
  coherent, `g_*𝒪_{X'}` **is** `(Scheme.Modules.pushforward g)(𝒪_{X'})` on the nose
  (`Stacks.GlueSquishFactor.pushforward_obj_unitModule`, an equality) so
  [Stacks, Tag 01Y6] applies to it, and coherence passes to cokernels.
* `Stacks.GlueSquishFactor.isElementaryChain_or_exists_split_measureOver_lt` — **`hsplit` at
  `μ = measureOver`, modulo one hypothesis.** The dichotomy, assembled: empty bad set gives an
  isomorphism, two bad points give a splitting, one bad point gives an elementary modification.
* `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso_of_isSquishingProducer` —
  **[Stacks, Tag 0C1L] modulo that one hypothesis**, by feeding the dichotomy to
  `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`.

## The one hypothesis, and no stacks attribute here

**No `@[stacks]` attribute is attached in this file, and none is earned here.** The results below
are conditional on `Stacks.GlueSquishFactor.IsSquishingProducer`, *the squishing half of the
one-step classification*, which is not a hypothesis of the source. When the bad set is a single
point the fibre `(g_*𝒪_{X'})_{x₀} ⧸ m_{x₀}(g_*𝒪_{X'})_{x₀}` is `k × k` or `k[ε]`
(`Stacks.GlueSquishFactor.fibre_algEquiv_prod_or_dualNumber`). In the first case
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` delivers
`AlgebraicGeometry.IsGlueingTwoPoints` in full. In the second,
`Stacks.GlueSquishFactor.exists_tangentVector_of_fibre_algEquiv_dualNumber` delivers only the
*data* `θ : Spec k[ε] ⟶ X'` with its two equations; `AlgebraicGeometry.IsSquishingTangentVector`
asks in addition that `θ` be a closed immersion and that the `ε`-coefficient present
`x_*k` as `g_*𝒪_{X'}/𝒪_X` as a short exact sequence of sheaves of abelian groups.
`IsSquishingProducer` is stated verbatim as the `DualNumber k` twin of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`, and it was
the *only* statement between this tree and [Stacks, Tag 0C1L].

It is **proved**, in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingProducer`, as
`Stacks.GlueSquishFactor.isSquishingProducer`; the unconditional form of the lemma, which carries
the `@[stacks 0C1L]` attribute, is
`Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain` there.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 0C1K](https://stacks.math.columbia.edu/tag/0C1K)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-- **Where `f` restricts to an isomorphism, the stalk map of the pushforward is surjective.** A
germ of `f_*𝒪_{X'}` at `x ∈ U` is a section over some open `W`; on `W ⊓ U` the map `f.app` is an
isomorphism (`Stacks.GlueSquishFactor.isIso_app_of_isIso_morphismRestrict`), so that section is
the image of its own preimage, and `Stacks.GlueSquishFactor.app_comp_germ_pushforward` turns that
into the germ statement.

This is the ring-level twin of
`Stacks.GlueSquishFactor.surjective_stalkLinearMap_structureUnitHom`, and it is what makes
`Stacks.GlueSquishFactor.badSet` finite: the bad set is contained in the complement of the
isomorphism locus. -/
theorem surjective_stalkPushforwardMap_of_isIso_morphismRestrict {X' X : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] {x : X} (hx : x ∈ U) :
    Function.Surjective (stalkPushforwardMap f x).hom := by
  intro t
  obtain ⟨W, hxW, s, hs⟩ := (f.base _* X'.presheaf).exists_germ_eq t
  set W' : X.Opens := W ⊓ U
  have hxW' : x ∈ W' := ⟨hxW, hx⟩
  have hs' : (f.base _* X'.presheaf).germ W' x hxW'
      ((f.base _* X'.presheaf).map (homOfLE (inf_le_left : W' ≤ W)).op s) = t := by
    rw [(f.base _* X'.presheaf).germ_res_apply (homOfLE (inf_le_left : W' ≤ W)) x hxW' s, hs]
  have : IsIso (f.app W') := isIso_app_of_isIso_morphismRestrict f U W' inf_le_right
  refine ⟨X.presheaf.germ W' x hxW' (CategoryTheory.inv (f.app W')
    ((f.base _* X'.presheaf).map (homOfLE (inf_le_left : W' ≤ W)).op s)), ?_⟩
  have h := congrArg
    (fun m : Γ(X, W') ⟶ (f.base _* X'.presheaf).stalk x => m.hom
      (CategoryTheory.inv (f.app W') ((f.base _* X'.presheaf).map
        (homOfLE (inf_le_left : W' ≤ W)).op s)))
    (app_comp_germ_pushforward f W' x hxW')
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  rw [← h, CategoryTheory.IsIso.inv_hom_id_apply (f.app W'), hs']

/-- **Surjectivity on sections from surjectivity on stalks.** If `f.app` is injective on every
open and the stalk map `𝒪_{X,x} ⟶ (f_*𝒪_{X'})_x` is surjective at every point of `W`, then
`f.app W` is surjective.

This is the only real work in the converse of
`Stacks.GlueSquishFactor.isZero_stalk_cokernel_structureUnitHom`, and it is pure sheaf theory —
no quasi-coherence, no finiteness, no affineness of `W`. A section `s` of `f_*𝒪_{X'}` over `W` is
locally in the image of `f.app` by
`Stacks.GlueSquishFactor.exists_app_eq_of_germ_mem_range`; the local preimages agree on overlaps
because `f.app` is injective there, so they glue to `t ∈ Γ(X, W)` by the sheaf axiom for `𝒪_X`;
and `f.app W t = s` because the two agree on the preimage cover, which covers `f ⁻¹ᵁ W` because
the original cover covers `W`. -/
theorem surjective_app_of_forall_surjective_stalkPushforwardMap {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hinj : ∀ V : X.Opens, Function.Injective (f.app V).hom) (W : X.Opens)
    (hW : ∀ x ∈ W, Function.Surjective (stalkPushforwardMap f x).hom) :
    Function.Surjective (f.app W).hom := by
  intro s
  have hloc : ∀ x : W, ∃ (V : X.Opens) (hVW : V ≤ W) (_ : (x : X) ∈ V) (t : Γ(X, V)),
      (X'.presheaf.map (homOfLE (f.preimage_mono hVW)).op).hom s = (f.app V).hom t :=
    fun x => exists_app_eq_of_germ_mem_range f W x.2 s
      (hW x x.2 ((f.base _* X'.presheaf).germ W (x : X) x.2 s))
  choose V hVW hxV t ht using hloc
  have hcover : W ≤ iSup V := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  have key : ∀ (i : W) (Z : X.Opens) (hZ : Z ≤ V i),
      (f.app Z).hom ((X.presheaf.map (homOfLE hZ).op).hom (t i)) =
        (X'.presheaf.map (homOfLE (f.preimage_mono (hZ.trans (hVW i)))).op).hom s := by
    intro i Z hZ
    have hnat := congrArg (fun m : Γ(X, V i) ⟶ Γ(X', f ⁻¹ᵁ Z) => m.hom (t i))
      (f.naturality (homOfLE hZ).op)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
    rw [hnat, ← ht i, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V t := by
    intro i j
    refine hinj (V i ⊓ V j) ?_
    rw [show Opens.infLELeft (V i) (V j) = homOfLE (inf_le_left) from rfl,
      show Opens.infLERight (V i) (V j) = homOfLE (inf_le_right) from rfl,
      key i _ inf_le_left, key j _ inf_le_right]
  obtain ⟨g, hg, -⟩ :=
    X.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hVW i)) hcover t hcompat
  have hgw : ∀ i : W, (X.presheaf.map (homOfLE (hVW i)).op).hom g = t i := hg
  have key2 : ∀ i : W, (f.app (V i)).hom ((X.presheaf.map (homOfLE (hVW i)).op).hom g) =
      (X'.presheaf.map (homOfLE (f.preimage_mono (hVW i))).op).hom ((f.app W).hom g) := by
    intro i
    have hnat := congrArg (fun m : Γ(X, W) ⟶ Γ(X', f ⁻¹ᵁ V i) => m.hom g)
      (f.naturality (homOfLE (hVW i)).op)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hnat
    exact hnat
  have hloceq : ∀ i : W,
      (X'.presheaf.map (homOfLE (f.preimage_mono (hVW i))).op).hom ((f.app W).hom g) =
        (X'.presheaf.map (homOfLE (f.preimage_mono (hVW i))).op).hom s := fun i => by
    rw [← key2 i, hgw i, ← ht i]
  exact ⟨g, X'.sheaf.eq_of_locally_eq' (fun i => f ⁻¹ᵁ V i) (f ⁻¹ᵁ W)
    (fun i => homOfLE (f.preimage_mono (hVW i)))
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨f.base y, hy⟩, hxV ⟨f.base y, hy⟩⟩) _ _ hloceq⟩

/-- **The converse of `Stacks.GlueSquishFactor.isZero_stalk_cokernel_structureUnitHom`.** An
affine morphism whose stalk maps are surjective over an open `V`, and which is injective on
sections, is an isomorphism over `V`.

Only the forward direction was in the tree; this is the direction the hypothesis `hiso` of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` needs.
Bijectivity of `f.app W` for an affine open `W ≤ V` comes from
`Stacks.GlueSquishFactor.surjective_app_of_forall_surjective_stalkPushforwardMap`, and
`Stacks.Pushout.isIso_morphismRestrict_of_forall_isIso_app` assembles those into an isomorphism
over `V` — being an isomorphism is Zariski-local at the target. -/
theorem isIso_morphismRestrict_of_forall_surjective_stalkPushforwardMap {X' X : Scheme.{u}}
    (f : X' ⟶ X) [IsAffineHom f] (hinj : ∀ V : X.Opens, Function.Injective (f.app V).hom)
    (V : X.Opens) (hV : ∀ x ∈ V, Function.Surjective (stalkPushforwardMap f x).hom) :
    IsIso (f ∣_ V) :=
  Stacks.Pushout.isIso_morphismRestrict_of_forall_isIso_app f V fun W _ hWV =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨hinj W, surjective_app_of_forall_surjective_stalkPushforwardMap f hinj W
        fun x hx => hV x (hWV hx)⟩

/-- **No bad point at all means `f` is an isomorphism.** The previous result at `V = ⊤`.

This is the branch of the dichotomy of `hsplit` in which the source says "`f` is an isomorphism
and there is nothing to prove", and it lands in
`Stacks.GlueSquishFactor.IsElementaryChain.of_isIso`. -/
theorem isIso_of_forall_surjective_stalkPushforwardMap {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsAffineHom f] (hinj : ∀ V : X.Opens, Function.Injective (f.app V).hom)
    (h : ∀ x : X, Function.Surjective (stalkPushforwardMap f x).hom) : IsIso f := by
  have htop := isIso_morphismRestrict_of_forall_surjective_stalkPushforwardMap f hinj ⊤
    fun x _ => h x
  exact AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun _ => ⟨⊤, trivial, htop⟩

/-- **The bad set of a morphism**: the points at which the stalk map
`𝒪_{X,x} ⟶ (f_*𝒪_{X'})_x` is not surjective, equivalently (by
`Stacks.GlueSquishFactor.bot_ne_top_iff_mem_badSet`) at which the stalk extension
`𝒪_{X,x} ⊂ (f_*𝒪_{X'})_x` is proper.

This is the set the dichotomy of `hsplit` is taken on; see the implementation notes of this file
for why it is this set and not the support of `f_*𝒪_{X'}/𝒪_X` nor the complement of the
isomorphism locus that `Stacks.GlueSquishFactor.IsAlmostIsoCore` happens to name. -/
def badSet {X' X : Scheme.{u}} (f : X' ⟶ X) : Set X :=
  {x | ¬ Function.Surjective (stalkPushforwardMap f x).hom}

/-- The bad set misses every open over which `f` is an isomorphism; with
`Stacks.GlueSquishFactor.IsAlmostIsoCore` this makes it finite, and
`Stacks.GlueSquishFactor.isClosed_singleton_of_mem_compl_isoLocus` makes each of its points
closed. -/
theorem badSet_subset_compl {X' X : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    badSet f ⊆ ((U : Set X)ᶜ) := fun _ hx hxU =>
  hx (surjective_stalkPushforwardMap_of_isIso_morphismRestrict f U hxU)

/-- **The two readings of a bad point agree.** Non-surjectivity of the stalk map is properness of
the stalk extension as a subalgebra, which is the form
`Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt_of_ne` and
`Stacks.GlueSquishFactor.fibre_algEquiv_prod_or_dualNumber` ask for. The proof is
`Algebra.mem_bot` and `Algebra.mem_top`: the bottom subalgebra is the range of the structure map,
so it is everything exactly when that map is surjective. -/
theorem bot_ne_top_iff_mem_badSet {X' X : Scheme.{u}} (f : X' ⟶ X) (x : X) :
    x ∈ badSet f ↔
      letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        (stalkPushforwardMap f x).hom.toAlgebra
      (⊥ : Subalgebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)) ≠ ⊤ := by
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    (stalkPushforwardMap f x).hom.toAlgebra
  refine ⟨fun hx hbot => hx fun b => Algebra.mem_bot.mp ?_,
    fun hne hsurj => hne (le_antisymm le_top fun b _ => Algebra.mem_bot.mpr (hsurj b))⟩
  exact hbot ▸ Algebra.mem_top

/-- **`hiso`, from a single bad point.** If the bad set of `f` is one closed point `x₀`, then `f`
restricts to an isomorphism over the open complement of `x₀`.

This is the hypothesis `hiso` of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` and of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg` — the source's "we
may assume that `f` is not an isomorphism in exactly one point", which `IsAlmostIso` does not
give because the open it names may be smaller than `{x₀}ᶜ`. -/
theorem exists_isIso_morphismRestrict_compl_singleton {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsAffineHom f] (hinj : ∀ V : X.Opens, Function.Injective (f.app V).hom) {x₀ : X}
    (hcl : IsClosed ({x₀} : Set X)) (hbad : badSet f = {x₀}) :
    ∃ U : X.Opens, (U : Set X) = {x₀}ᶜ ∧ IsIso (f ∣_ U) :=
  ⟨⟨{x₀}ᶜ, hcl.isOpen_compl⟩, rfl,
    isIso_morphismRestrict_of_forall_surjective_stalkPushforwardMap f hinj _ fun x hx => by
      by_contra hns
      exact hx (hbad ▸ hns : x ∈ ({x₀} : Set X))⟩

/-- **`hno`, or else the splitting branch.** For an affine open `U`, either `f` splits into two
almost isomorphisms of strictly smaller measure, or no finite quasi-coherent subalgebra of
`f_*𝒪_{X'}` which is proper over `U` has a section over `U` outside `𝒪_X`.

A `by_cases` on the second alternative: a subalgebra violating it is proper at the upper end by
`Stacks.GlueSquishFactor.nonempty_supp_cokernel_underlyingModuleMap_incl` and at the lower end by
`Stacks.GlueSquishFactor.nonempty_supp_cokernel_unitModuleMap_of_notMem_range`, which is exactly
what `Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt` consumes. So the hypothesis
`hno` of `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_forall_isFinite_subalg` is the
*negation of the splitting branch*, which is where the source has it. -/
theorem exists_split_measureOver_lt_or_forall_isFinite_subalg {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Over (Spec (.of k))} (f : X' ⟶ X) (hf : IsAlmostIso f)
    (hcoh : (cokernel (structureUnitHom f.left)).IsCoherent) (U : X.left.Opens) :
    (∃ (Z : Over (Spec (.of k))) (p : X' ⟶ Z) (q : Z ⟶ X), p ≫ q = f ∧
      IsAlmostIso p ∧ IsAlmostIso q ∧
        measureOver p < measureOver f ∧ measureOver q < measureOver f) ∨
      ∀ C : AlgebraSheaf.Subalg (pushforwardAlgebra f.left),
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent →
          (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite → C.obj U ≠ ⊤ →
            ∀ s ∈ C.obj U, s ∈ Set.range (f.left.app U).hom := by
  classical
  by_cases hno : ∀ C : AlgebraSheaf.Subalg (pushforwardAlgebra f.left),
      (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsQuasicoherent →
        (AlgebraSheaf.Subalg.toAlgebraSheaf C).IsFinite → C.obj U ≠ ⊤ →
          ∀ s ∈ C.obj U, s ∈ Set.range (f.left.app U).hom
  · exact Or.inr hno
  refine Or.inl ?_
  push Not at hno
  obtain ⟨C, hqc, hfin, hCtop, s, hsC, hsnot⟩ := hno
  have := hqc
  exact exists_split_isAlmostIso_measureOver_lt f hf hcoh C hfin
    (nonempty_supp_cokernel_unitModuleMap_of_notMem_range f.left hf.2 C hsC hsnot)
    (nonempty_supp_cokernel_underlyingModuleMap_incl C hCtop)

/-- An `Over (Spec k)`-scheme locally of finite type over `k` is locally Noetherian. -/
private theorem isLocallyNoetherian_left_of_locallyOfFiniteType {k : Type u} [Field k]
    {Z : Over (Spec (.of k))} (h : LocallyOfFiniteType (Z.left ↘ Spec (.of k))) :
    IsLocallyNoetherian Z.left :=
  LocallyOfFiniteType.isLocallyNoetherian (Z.left ↘ Spec (.of k))

/-- **Coherence of `f_*𝒪_{X'}` is free for an almost isomorphism.** Both schemes are algebraic
over `k`, hence locally Noetherian by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`; there the structure sheaf of `X'` is
coherent, and `f_*𝒪_{X'}` is its direct image along a finite morphism, so [Stacks, Tag 01Y6]
applies. The one thing that makes this usable is that `f_*𝒪_{X'}` **is**
`(Scheme.Modules.pushforward f).obj (unitModule X')` on the nose
(`Stacks.GlueSquishFactor.pushforward_obj_unitModule`), so no transport is needed. -/
theorem isCoherent_underlyingModule_pushforwardAlgebra_of_isAlmostIso {k : Type u} [Field k]
    [IsAlgClosed k] {Z' Z : Over (Spec (.of k))} (h : Z' ⟶ Z) (hh : IsAlmostIso h) :
    (AlgebraSheaf.underlyingModule (pushforwardAlgebra h.left) : Z.left.Modules).IsCoherent := by
  obtain ⟨⟨hZ'ft, -, hZft, -, hhfin, -⟩, -⟩ := id hh
  have := hhfin
  have := hZft
  have := hZ'ft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hZft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hZ'ft
  have : (unitModule Z'.left).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  exact Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
    h.left (unitModule Z'.left)

/-- **The coherence hypothesis `hcoh` of the measure results, discharged.** Every strict drop of
`Stacks.GlueSquishFactor.measureOver` in this tree carries coherence of `f_*𝒪_{X'}/𝒪_X` as an
undischarged hypothesis; for an almost isomorphism it follows from coherence of the two ends and
closure of coherence under cokernels. -/
theorem isCoherent_cokernel_structureUnitHom_of_isAlmostIso {k : Type u} [Field k]
    [IsAlgClosed k] {Z' Z : Over (Spec (.of k))} (h : Z' ⟶ Z) (hh : IsAlmostIso h) :
    (cokernel (structureUnitHom h.left)).IsCoherent := by
  obtain ⟨⟨-, -, hZft, -, -, -⟩, -⟩ := id hh
  have := hZft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hZft
  exact Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_cokernel'
    (structureUnitHom h.left)
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
    (isCoherent_underlyingModule_pushforwardAlgebra_of_isAlmostIso h hh)

/-- **The squishing half of the one-step classification of [Stacks, Tag 0C1L]**: for a while the
one statement between this tree and the lemma, now proved as
`Stacks.GlueSquishFactor.isSquishingProducer`. It is kept as a named predicate because the
dichotomy below is stated conditionally on it, which keeps the sheaf-theoretic construction out
of the measure induction.

Verbatim the `DualNumber k` twin of
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod`: a finite
morphism of algebraic `k`-schemes, injective on structure sheaves, an isomorphism away from a
single rational point `x`, whose stalk extension at `x` is proper and admits no intermediate
subalgebra and whose fibre there is `k[ε]`, squishes a tangent vector.

`Stacks.GlueSquishFactor.exists_tangentVector_of_stalkHom` produces the *data*
`θ : Spec k[ε] ⟶ X'`, defined over `k` and contracted to `x`. The rest of
`AlgebraicGeometry.IsSquishingTangentVector` — that `θ` is a closed immersion, and the short exact
sequence `0 → 𝒪_X → f_*𝒪_{X'} → x_*k → 0` of sheaves of abelian groups whose second map is the
coefficient of `ε` — is the squishing analogue of what
`Stacks.GlueSquishFactor.exists_two_points_sequence_of_fibre_algEquiv_prod` and
`Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_fibre_algEquiv_prod` do on the glueing side,
and is supplied by
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingProducer`. -/
def IsSquishingProducer (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∀ {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))] (f : X' ⟶ X),
    ∀ [IsFinite f], f.IsOver (Spec (.of k)) →
      ∀ x : Spec (.of k) ⟶ X, x.IsOver (Spec (.of k)) →
        LocallyOfFiniteType (X' ↘ Spec (.of k)) → QuasiCompact (X' ↘ Spec (.of k)) →
          LocallyOfFiniteType (X ↘ Spec (.of k)) → QuasiCompact (X ↘ Spec (.of k)) →
            Mono (pushforwardAlgebra f).hom →
              (∃ U : X.Opens, (U : Set X) = {basePoint x}ᶜ ∧ IsIso (f ∣_ U)) →
      letI : Algebra (X.presheaf.stalk (basePoint x))
          ((f.base _* X'.presheaf).stalk (basePoint x)) :=
        (stalkPushforwardMap f (basePoint x)).hom.toAlgebra
      letI : Algebra k (X.presheaf.stalk (basePoint x)) :=
        (stalkConstMap X (basePoint x)).hom.toAlgebra
      letI : Algebra k ((f.base _* X'.presheaf).stalk (basePoint x)) :=
        ((stalkPushforwardMap f (basePoint x)).hom.comp
          (stalkConstMap X (basePoint x)).hom).toAlgebra
      (⊥ : Subalgebra (X.presheaf.stalk (basePoint x))
          ((f.base _* X'.presheaf).stalk (basePoint x))) ≠ ⊤ →
        (∀ E : Subalgebra (X.presheaf.stalk (basePoint x))
          ((f.base _* X'.presheaf).stalk (basePoint x)), E = ⊥ ∨ E = ⊤) →
          (((f.base _* X'.presheaf).stalk (basePoint x) ⧸
            stalkFibreIdeal f (basePoint x)) ≃ₐ[k] DualNumber k) →
            ∃ θ : Spec (.of (DualNumber k)) ⟶ X', IsSquishingTangentVector f θ

/-- **The singleton case of the splitting dichotomy.** If the bad set of an almost isomorphism
`g` is a single closed point, then `g` is an elementary step or splits into two almost
isomorphisms of strictly smaller measure. -/
theorem isElementaryChain_or_exists_split_of_badSet_eq_singleton {k : Type u} [Field k]
    [IsAlgClosed k] (hsq : IsSquishingProducer k)
    {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y) (hg : IsAlmostIso g) {x₀ : Y.left}
    (hcl : IsClosed ({x₀} : Set Y.left)) (hsingle : badSet g.left = {x₀}) :
    IsElementaryChain k g ∨ ∃ (Z : Over (Spec (.of k))) (p : Y' ⟶ Z) (q : Z ⟶ Y),
      p ≫ q = g ∧ IsAlmostIso p ∧ IsAlmostIso q ∧
        measureOver p < measureOver g ∧ measureOver q < measureOver g := by
  classical
  obtain ⟨⟨hY'ft, hY'qc, hYft, hYqc, hgfin, -⟩, hmono⟩ := id hg
  have := hgfin
  have := hmono
  have := hYft
  have := hY'ft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hYft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hY'ft
  have : (unitModule Y.left).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have : (unitModule Y'.left).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have := isCoherent_underlyingModule_pushforwardAlgebra_of_isAlmostIso g hg
  have hcoh := isCoherent_cokernel_structureUnitHom_of_isAlmostIso g hg
  have hinj := injective_app_of_mono_hom_pushforwardAlgebra g.left hmono
  have hx₀ : x₀ ∈ badSet g.left := hsingle ▸ Set.mem_singleton x₀
  obtain ⟨V, hVset, hViso⟩ :=
    exists_isIso_morphismRestrict_compl_singleton g.left hinj hcl hsingle
  have hgover : g.left.IsOver (Spec (.of k)) := ⟨Over.w g⟩
  set x : Spec (.of k) ⟶ Y.left :=
    AlgebraicGeometry.pointOfClosedPoint (Y.left ↘ Spec (.of k)) x₀ hcl with hxdef
  have hxbase : basePoint x = x₀ :=
    AlgebraicGeometry.pointOfClosedPoint_apply (Y.left ↘ Spec (.of k)) x₀ hcl _
  have hxover : x.IsOver (Spec (.of k)) := ⟨by
    rw [hxdef, AlgebraicGeometry.pointOfClosedPoint_comp]
    rfl⟩
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp Y.left.isBasis_affineOpens
    (show x₀ ∈ (⊤ : Y.left.Opens) from trivial)
  rcases exists_split_measureOver_lt_or_forall_isFinite_subalg g hg hcoh U
    with hs | hno
  · exact Or.inr hs
  refine Or.inl (IsElementaryChain.of_step g ?_)
  have hmin := forall_eq_bot_or_eq_top_of_forall_isFinite_subalg g.left hU
    (show basePoint x ∈ U from hxbase ▸ hxU) hno
  have hbne := (bot_ne_top_iff_mem_badSet g.left (basePoint x)).mp (hxbase ▸ hx₀)
  have hVx : ∃ W : Y.left.Opens, (W : Set Y.left) = {basePoint x}ᶜ ∧ IsIso (g.left ∣_ W) :=
    ⟨V, by rw [hVset, hxbase], hViso⟩
  rcases fibre_algEquiv_prod_or_dualNumber g.left (basePoint x)
      (exists_sub_stalkConstMap_mem_maximalIdeal x hxover) hbne hmin with hprod | hdual
  · exact Or.inl (exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod g.left hgover x
      hxover hY'ft hY'qc hYft hYqc hmono hVx hbne hmin hprod.some)
  · exact Or.inr (hsq g.left hgover x hxover hY'ft hY'qc hYft hYqc hmono hVx hbne hmin
      hdual.some)

/-- **`hsplit` at `μ = Stacks.GlueSquishFactor.measureOver`, modulo the squishing producer.**
Every almost isomorphism of algebraic `k`-schemes either is a chain of elementary modifications,
or splits into two almost isomorphisms of strictly smaller measure.

The dichotomy is on `Stacks.GlueSquishFactor.badSet g`, in three cases.

* *Empty.* Then `g` is an isomorphism by
  `Stacks.GlueSquishFactor.isIso_of_forall_surjective_stalkPushforwardMap` — in `Over (Spec k)`
  because `CategoryTheory.Over.forget` reflects isomorphisms — hence the empty chain.
* *Two distinct points.* Then
  `Stacks.GlueSquishFactor.exists_split_isAlmostIso_measureOver_lt_of_ne` splits `g` with both
  measures dropping; its two properness hypotheses are the two bad points read through
  `Stacks.GlueSquishFactor.bot_ne_top_iff_mem_badSet`, and the closedness it asks for comes from
  `Stacks.GlueSquishFactor.isClosed_singleton_of_mem_compl_isoLocus`.
* *One point `x₀`.* Then `hiso` is
  `Stacks.GlueSquishFactor.exists_isIso_morphismRestrict_compl_singleton`; `x₀` is a *rational*
  point by `AlgebraicGeometry.pointOfClosedPoint`, `k` being algebraically closed and `X`
  locally of finite type over it; and on an affine open around `x₀` either the splitting branch
  holds — in which case we are in the second disjunct after all — or `hno` does, and then
  `Stacks.GlueSquishFactor.forall_eq_bot_or_eq_top_of_forall_isFinite_subalg` gives `hmin` and
  `Stacks.GlueSquishFactor.fibre_algEquiv_prod_or_dualNumber` splits into the glueing case, which
  `Stacks.GlueSquishFactor.exists_isGlueingTwoPoints_of_mono_of_fibre_algEquiv_prod` closes, and
  the squishing case, which is the hypothesis `hsq`.

Note that finiteness of the bad set is never used: the trichotomy empty / singleton / at least two
is available for any set. -/
theorem isElementaryChain_or_exists_split_measureOver_lt {k : Type u} [Field k] [IsAlgClosed k]
    (hsq : IsSquishingProducer k)
    {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y) (hg : IsAlmostIso g) :
    IsElementaryChain k g ∨ ∃ (Z : Over (Spec (.of k))) (p : Y' ⟶ Z) (q : Z ⟶ Y),
      p ≫ q = g ∧ IsAlmostIso p ∧ IsAlmostIso q ∧
        measureOver p < measureOver g ∧ measureOver q < measureOver g := by
  classical
  obtain ⟨⟨hY'ft, -, hYft, -, hgfin, U₀, hU₀fin, hU₀iso⟩, hmono⟩ := id hg
  have := hgfin
  have := hU₀iso
  have := hmono
  have := hYft
  have := hY'ft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hYft
  have := isLocallyNoetherian_left_of_locallyOfFiniteType hY'ft
  have := isCoherent_underlyingModule_pushforwardAlgebra_of_isAlmostIso g hg
  have hcoh := isCoherent_cokernel_structureUnitHom_of_isAlmostIso g hg
  have hinj := injective_app_of_mono_hom_pushforwardAlgebra g.left hmono
  have hcls : ∀ y ∈ badSet g.left, IsClosed ({y} : Set Y.left) := fun y hy =>
    isClosed_singleton_of_mem_compl_isoLocus (Y.left ↘ Spec (.of k)) hU₀fin
      (badSet_subset_compl g.left U₀ hy)
  by_cases hempty : badSet g.left = ∅
  · refine Or.inl (IsElementaryChain.of_isIso g ?_)
    have : IsIso ((Over.forget (Spec (.of k))).map g) :=
      isIso_of_forall_surjective_stalkPushforwardMap g.left hinj fun x => by
        by_contra hns
        exact absurd (hempty ▸ (hns : x ∈ badSet g.left)) (Set.notMem_empty x)
    exact isIso_of_reflects_iso g (Over.forget (Spec (.of k)))
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  by_cases hsingle : badSet g.left = {x₀}
  · exact isElementaryChain_or_exists_split_of_badSet_eq_singleton hsq g hg (hcls x₀ hx₀)
      hsingle
  obtain ⟨y₀, hy₀, hyne⟩ : ∃ y ∈ badSet g.left, y ≠ x₀ := by
    by_contra hcon
    push Not at hcon
    exact hsingle (Set.eq_singleton_iff_unique_mem.mpr ⟨hx₀, hcon⟩)
  exact Or.inr (exists_split_isAlmostIso_measureOver_lt_of_ne g hg hcoh hyne
    (hcls x₀ hx₀) ((bot_ne_top_iff_mem_badSet g.left y₀).mp hy₀)
    ((bot_ne_top_iff_mem_badSet g.left x₀).mp hx₀))

/-- **[Stacks, Tag 0C1L], modulo the squishing producer.** A finite morphism of algebraic
`k`-schemes which is injective on structure sheaves and an isomorphism away from a finite set of
points is a composite of glueings of two rational points and squishings of tangent vectors —
provided `Stacks.GlueSquishFactor.IsSquishingProducer k`, the squishing half of the one-step
classification.

`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` reduced the lemma to `hsplit`, and
`Stacks.GlueSquishFactor.isElementaryChain_or_exists_split_measureOver_lt` proves `hsplit` at
`μ = Stacks.GlueSquishFactor.measureOver` from `hsq`. No `@[stacks 0C1L]` attribute: `hsq` is not
a hypothesis of the source. It is discharged in
`Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain`, which is the lemma and does carry the
attribute. -/
theorem isElementaryChain_of_isAlmostIso_of_isSquishingProducer {k : Type u} [Field k]
    [IsAlgClosed k] (hsq : IsSquishingProducer k) {X' X : Over (Spec (.of k))} (f : X' ⟶ X)
    (hf : IsAlmostIso f) : IsElementaryChain k f :=
  isElementaryChain_of_isAlmostIso k measureOver
    (fun g hg => isElementaryChain_or_exists_split_measureOver_lt hsq g hg) f hf

end Stacks.GlueSquishFactor

end
