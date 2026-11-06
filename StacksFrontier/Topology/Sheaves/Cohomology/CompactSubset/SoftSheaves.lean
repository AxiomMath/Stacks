module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Separation.Regular
public import Mathlib.CategoryTheory.Sites.EpiMono
import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Soft sheaves of abelian groups

A sheaf of abelian groups `F` on a topological space `Z` is *soft* if every section defined on an
open neighbourhood of a closed subset `K ⊆ Z` agrees, on a possibly smaller neighbourhood of `K`,
with a global section of `F`. On a compact Hausdorff space this is the classical notion: by
[Stacks, Tag 09V3] in degree zero the sections of `F` along a closed subset `K` are the filtered
colimit of the sections of `F` over the open neighbourhoods of `K`, so softness says exactly that
`Γ(Z, F) ⟶ Γ(K, F|_K)` is surjective for every closed `K`. The neighbourhood form used here is
stated without reference to the restriction of `F` to a subspace, which is what makes it usable
without any comparison between `Γ(K, F|_K)` and that colimit.

The point of the notion is that a soft sheaf on a compact Hausdorff space is acyclic. This file
proves the step of that argument which carries all of its content:

**if `0 ⟶ S ⟶ A ⟶ B ⟶ 0` is a short exact sequence of sheaves of abelian groups on a compact
Hausdorff space and `S` is soft, then `Γ(A) ⟶ Γ(B)` is surjective.**

A global section of `B` lifts locally to `A`; compactness turns that into a finite family of local
lifts, each over an open neighbourhood of a closed set, the closed sets covering `Z`. The lifts are
then patched *two at a time*: on the overlap the difference of two lifts is a section of `S`, which
softness extends to a global section of `S`, and correcting one lift by that extension makes the
two agree on a neighbourhood of the intersection of the two closed sets. Normality of `Z` shrinks
the two opens so that their intersection lies inside that neighbourhood, after which the two
corrected lifts glue. No Cech theory and no colimit of covers is involved; the induction is over a
`Finset` of indices.

## Main definitions

* `Stacks.Topology.IsSoft`: the softness condition above.
* `Stacks.Topology.sectionsAtFunctorUnivLE`: sections over one open set, as a functor, at a
  coefficient universe independent of the space.

## Main results

* `Stacks.Topology.IsSoft.of_isFlasque`: a flasque sheaf is soft.
* `Stacks.Topology.exists_lift_of_isSoft_of_isCompact_univLE`: the relative form of the patching
  theorem — a section of `B` on an open set `U` lifts to `A` on a neighbourhood of any compact
  subset of `U`.
* `Stacks.Topology.surjective_sections_of_isSoft_univLE`: the absolute form, surjectivity of
  `Γ(Z, A) ⟶ Γ(Z, B)` on a compact Hausdorff space.
* `Stacks.Topology.IsSoft.of_shortExact_univLE`: the quotient of a soft sheaf by a soft subsheaf is
  soft.
* `Stacks.Topology.compactSpace_coe_of_isCompact` and
  `Stacks.Topology.t2Space_coe_of_pairwiseSeparated`: a quasi-compact subset of an arbitrary space
  whose distinct points are separated by disjoint open subsets of that space is compact Hausdorff
  as a subspace. These turn the hypotheses of [Stacks, Tag 09V3] into the hypotheses above.

## Implementation notes

The patching induction is stated for an arbitrary index type with a `Finset` of indices, so that
the two uses of it — a cover of the whole space and a cover of a compact subset — are the same
statement. Its conclusion keeps the open set it produces inside the open set on which the section
of `B` is given, which is what lets the relative form be applied to a closed subset of a closed
subset.

Everything in this file is stated at a coefficient universe independent of the space's. For
softness itself, the two restriction-is-additive lemmas, the vanishing of sections over `⊥`, a
flasque sheaf being soft and the correction step this costs nothing, since everything they use is
universe-polymorphic; `exists_glue_pair` and the patching theorem need in addition the dominance
hypothesis `UnivLE.{u, v}`, which is what makes `HasLimitsOfSize` and the preservation of limits
by the forgetful functor hold at the size of `Opens Z`. The patching theorem also needs
`HasZeroMorphisms` on the off-diagonal sheaf category — so even the type
`ShortComplex (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{v})` — which comes from
sheafification at a dominating coefficient universe,
`Stacks.SheafOfModules.coefficientSheafification`. Since `UnivLE.{u, u}` is an instance, the
statements with the coefficients pinned to the space's universe are the `v := u` cases of these,
and are not stated separately; `CompactSubset/SoftSheavesUnivLE.lean` records that specialisation
explicitly in its `NoWeakening` section.

`StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian`, which carries that sheafification
instance, is imported **privately**: it must not be re-exported. Everything downstream of this file
reaches it otherwise, and `Stacks.SheafOfModules.coefficientSheafification` then competes with the
pinned sheafification instances in parts of the library that fix their universes by unification —
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/GlobalSectionsGeneration.lean` is one, and
`StacksFrontier/AlgebraicGeometry/Thickenings/SquareZeroExtension.lean` already disables the instance
by hand for the same reason.

Two steps are not available in the pinned spelling Mathlib offers them in, because
`TopCat.Sheaf.isLocallySurjective_iff_epi`, `TopCat.Presheaf.isLocallySurjective_iff` and
`TopCat.Sheaf.sections_exact_of_left_exact` all force the coefficient universe equal to the
space's. Local liftability of a section of `B` is instead
`CategoryTheory.Presheaf.imageSieve_mem` for `S.g`, which is locally surjective by the
universe-independent `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`; and the fact that a
section of `A` killed by `g` comes from `S` is `exists_preimage_of_app_eq_zero`, re-derived from
left exactness of `sectionsAtFunctorUnivLE`.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V2](https://stacks.math.columbia.edu/tag/09V2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe v u

variable {Z : TopCat.{u}}

/-- A sheaf of abelian groups is **soft** if a section defined on an open neighbourhood of a closed
subset `K` agrees with a global section on a neighbourhood of `K`. -/
@[sga "6 II 2.3.1"]
def IsSoft (F : Sheaf AddCommGrpCat.{v} Z) : Prop :=
  ∀ K : Set Z, IsClosed K → ∀ U : Opens Z, K ⊆ (U : Set Z) →
    ∀ s : ToType (F.obj.obj (op U)), ∃ (t : ToType (F.obj.obj (op ⊤))) (V : Opens Z)
      (hVU : V ≤ U), K ⊆ (V : Set Z) ∧ t |_ V = s |_ₗ V ⟪hVU⟫

/-- A flasque sheaf is soft: a section on a neighbourhood of `K` is already the restriction of a
global section. -/
theorem IsSoft.of_isFlasque (F : Sheaf AddCommGrpCat.{v} Z) [TopCat.Sheaf.IsFlasque F] :
    IsSoft F := by
  intro K _ U hKU s
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE (le_top : U ≤ ⊤)).op)).mp inferInstance s
  refine ⟨t, U, le_rfl, hKU, ?_⟩
  rw [show t |_ U = s from ht]
  exact (Presheaf.restrict_self s).symm

/-- A section of a sheaf of abelian groups over the empty open set is zero. -/
theorem eq_zero_of_bot (F : Sheaf AddCommGrpCat.{v} Z) (s : ToType (F.obj.obj (op ⊥))) :
    s = 0 :=
  have : Subsingleton (ToType (F.obj.obj (op (⊥ : Opens Z)))) :=
    AddCommGrpCat.subsingleton_of_isZero F.isTerminalOfEmpty.isZero
  Subsingleton.elim _ _

/-- Two sections of a sheaf agreeing on the intersection of their domains glue to a section on the
union. -/
theorem exists_glue_pair [UnivLE.{u, v}] (F : Sheaf AddCommGrpCat.{v} Z) {V₁ V₂ : Opens Z}
    (s₁ : ToType (F.obj.obj (op V₁))) (s₂ : ToType (F.obj.obj (op V₂)))
    (h : s₁ |_ (V₁ ⊓ V₂) = s₂ |_ (V₁ ⊓ V₂)) :
    ∃ s : ToType (F.obj.obj (op (V₁ ⊔ V₂))), s |_ V₁ = s₁ ∧ s |_ V₂ = s₂ := by
  classical
  let f : Fin 2 → Opens Z := ![V₁, V₂]
  let sf : (i : Fin 2) → ToType (F.obj.obj (op (f i)))
  | 0 => s₁
  | 1 => s₂
  have hcompat : Presheaf.IsCompatible F.obj f sf := by
    simp only [Presheaf.IsCompatible, Fin.forall_fin_two]
    refine ⟨⟨rfl, h⟩, Eq.symm ?_, rfl⟩
    apply_fun (fun x ↦ Presheaf.restrictOpen x (V₂ ⊓ V₁) (le_of_eq (inf_comm _ _))) at h
    rwa [Presheaf.restrict_restrict, Presheaf.restrict_restrict] at h
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' f (V₁ ⊔ V₂)
    (fun i ↦ homOfLE (by
      revert i
      rw [Fin.forall_fin_two]
      exact ⟨le_sup_left, le_sup_right⟩))
    (sup_le (le_iSup f 0) (le_iSup f 1)) sf hcompat
  exact ⟨s, hs 0, hs 1⟩

/-- Restriction of sections of a sheaf of abelian groups commutes with sums. -/
theorem restrict_add {F : Presheaf AddCommGrpCat.{v} Z} {U V : Opens Z} (h : V ≤ U)
    (s t : ToType (F.obj (op U))) : (s + t) |_ₗ V ⟪h⟫ = s |_ₗ V ⟪h⟫ + t |_ₗ V ⟪h⟫ := by
  delta Presheaf.restrict
  exact map_add _ _ _

/-- Restriction of sections of a sheaf of abelian groups commutes with differences. -/
theorem restrict_sub {F : Presheaf AddCommGrpCat.{v} Z} {U V : Opens Z} (h : V ≤ U)
    (s t : ToType (F.obj (op U))) : (s - t) |_ₗ V ⟪h⟫ = s |_ₗ V ⟪h⟫ - t |_ₗ V ⟪h⟫ := by
  delta Presheaf.restrict
  exact map_sub _ _ _

/-- **Correcting a lift by an extension of the difference.** If `σ` is a section of the kernel over
an overlap `D` whose image is the difference of two lifts `α` and `aj` of the same section, and if
a global section `τ` of the kernel restricts to `σ` on `V' ≤ D`, then correcting `aj` by `τ` makes
it agree with `α` on `V'`.

It is stated for a bare morphism of presheaves `f` rather than for the `f` of a short complex of
sheaves: the short-complex form would tie the two sheaves to the outer terms of one complex, which
the patching theorem below does not need, and the presheaf form applies to it unchanged. -/
theorem correction_agree {P Q : Presheaf AddCommGrpCat.{v} Z} (f : P ⟶ Q)
    {V W D V' : Opens Z} (hDV : D ≤ V) (hDW : D ≤ W) (hV'D : V' ≤ D)
    (α : ToType (Q.obj (op V))) (aj : ToType (Q.obj (op W)))
    (σ : ToType (P.obj (op D))) (τ : ToType (P.obj (op ⊤)))
    (hσ : f.app (op D) σ = α |_ₗ D ⟪hDV⟫ - aj |_ₗ D ⟪hDW⟫ )
    (hτ : τ |_ₗ V' ⟪le_top⟫ = σ |_ₗ V' ⟪hV'D⟫ ) :
    (aj + f.app (op W) (τ |_ₗ W ⟪le_top⟫ )) |_ₗ V' ⟪le_trans hV'D hDW⟫
      = α |_ₗ V' ⟪le_trans hV'D hDV⟫ := by
  have hV'W : V' ≤ W := le_trans hV'D hDW
  have hV'V : V' ≤ V := le_trans hV'D hDV
  calc (aj + f.app (op W) (τ |_ₗ W ⟪le_top⟫ )) |_ₗ V' ⟪hV'W⟫
      = aj |_ₗ V' ⟪hV'W⟫ + (f.app (op W) (τ |_ₗ W ⟪le_top⟫ )) |_ₗ V' ⟪hV'W⟫ :=
        restrict_add hV'W _ _
    _ = aj |_ₗ V' ⟪hV'W⟫ + f.app (op V') (τ |_ₗ V' ⟪le_top⟫ ) :=
        congrArg (fun z ↦ aj |_ₗ V' ⟪hV'W⟫ + z)
          ((Presheaf.map_restrict f hV'W (τ |_ₗ W ⟪le_top⟫ )).symm.trans
            (congrArg (fun z ↦ ConcreteCategory.hom (f.app (op V')) z)
              (Presheaf.restrict_restrict hV'W le_top τ)))
    _ = aj |_ₗ V' ⟪hV'W⟫ + f.app (op V') (σ |_ₗ V' ⟪hV'D⟫ ) :=
        congrArg (fun z ↦ aj |_ₗ V' ⟪hV'W⟫ + ConcreteCategory.hom (f.app (op V')) z) hτ
    _ = aj |_ₗ V' ⟪hV'W⟫ + (f.app (op D) σ) |_ₗ V' ⟪hV'D⟫ :=
        congrArg (fun z ↦ aj |_ₗ V' ⟪hV'W⟫ + z) (Presheaf.map_restrict f hV'D σ)
    _ = aj |_ₗ V' ⟪hV'W⟫ + (α |_ₗ D ⟪hDV⟫ - aj |_ₗ D ⟪hDW⟫ ) |_ₗ V' ⟪hV'D⟫ :=
        congrArg (fun z ↦ aj |_ₗ V' ⟪hV'W⟫ + Presheaf.restrict z (homOfLE hV'D)) hσ
    _ = aj |_ₗ V' ⟪hV'W⟫ + (α |_ₗ V' ⟪hV'V⟫ - aj |_ₗ V' ⟪hV'W⟫ ) :=
        congrArg (fun z ↦ aj |_ₗ V' ⟪hV'W⟫ + z)
          ((restrict_sub hV'D (α |_ₗ D ⟪hDV⟫ ) (aj |_ₗ D ⟪hDW⟫ )).trans
            (congrArg₂ (fun x y ↦ x - y) (Presheaf.restrict_restrict hV'D hDV α)
              (Presheaf.restrict_restrict hV'D hDW aj)))
    _ = α |_ₗ V' ⟪hV'V⟫ := by abel

/-- A set contained in `W` whose part outside `V'` lies in the open set `O` is contained in
`W ⊓ (V' ⊔ O)`. -/
private theorem subset_inf_sup_of_diff_subset {K : Set Z} {W V' : Opens Z} {O : Set Z}
    (hO : IsOpen O) (hKW : K ⊆ (W : Set Z)) (hKO : K \ (V' : Set Z) ⊆ O) :
    K ⊆ ((W ⊓ (V' ⊔ ⟨O, hO⟩) : Opens Z) : Set Z) := by
  intro x hx
  refine ⟨hKW hx, ?_⟩
  by_cases hx' : x ∈ (V' : Set Z)
  · exact Or.inl hx'
  · exact Or.inr (hKO ⟨hx, hx'⟩)

/-- Enlarging `V'` by two disjoint open sets inside `A` and `B` gives open sets meeting only
inside `V'`. -/
private theorem inf_sup_inf_sup_le_of_disjoint {A B V' : Opens Z} {O₁ O₂ : Set Z}
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (h : Disjoint O₁ O₂) :
    (A ⊓ (V' ⊔ ⟨O₁, hO₁⟩)) ⊓ (B ⊓ (V' ⊔ ⟨O₂, hO₂⟩)) ≤ V' := by
  intro x hx
  rcases hx.1.2 with h₁ | h₁
  · exact h₁
  · rcases hx.2.2 with h₂ | h₂
    · exact h₂
    · exact absurd h₂ (Set.disjoint_left.mp h h₁)

noncomputable section

variable [UnivLE.{u, v}]

/-- **Sections of an abelian sheaf over one open set, as a functor**, at a coefficient universe
independent of the space. It is spelled as the composite `sheafToPresheaf ⋙ evaluation`, not as
`(sheafSections _ _).obj (op U)`, although the two are definitionally equal: it is the composite
spelling whose additivity and preservation of finite limits are available from those of its two
factors by instance search. -/
abbrev sectionsAtFunctorUnivLE (Z : TopCat.{u}) (U : Opens Z) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v} :=
  sheafToPresheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{v} ⋙
    (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{v}).obj (op U)

variable {S : ShortComplex (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{v})}

/-- **A section of the middle term of a short exact sequence of abelian sheaves killed by the
second map comes from the first**, at a coefficient universe independent of the space. This is
`TopCat.Sheaf.sections_exact_of_left_exact`, whose coefficient universe is forced equal to the
space's, re-derived from left exactness of evaluation at the open set. -/
theorem exists_preimage_of_app_eq_zero (hS : S.ShortExact) (U : Opens Z)
    (y : ToType (S.X₂.obj.obj (op U))) (hy : S.g.hom.app (op U) y = 0) :
    ∃ x : ToType (S.X₁.obj.obj (op U)), S.f.hom.app (op U) x = y :=
  (ShortComplex.ab_exact_iff (S.map (sectionsAtFunctorUnivLE.{v} Z U))).mp
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (sectionsAtFunctorUnivLE.{v} Z U)).mp inferInstance S hS).1 y hy

omit [UnivLE.{u, v}] in
/-- The composite of the two maps of a short complex of sheaves vanishes on sections, at a
coefficient universe independent of the space. -/
theorem app_comp_eq_zero_univLE
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{v})) (U : Opens Z)
    (y : ToType (S.X₁.obj.obj (op U))) :
    S.g.hom.app (op U) (S.f.hom.app (op U) y) = 0 := by
  calc S.g.hom.app (op U) (S.f.hom.app (op U) y)
      = ConcreteCategory.hom (S.f.hom.app (op U) ≫ S.g.hom.app (op U)) y :=
        (ConcreteCategory.comp_apply _ _ y).symm
    _ = 0 :=
        (ConcreteCategory.congr_hom (S.map (sectionsAtFunctorUnivLE.{v} Z U)).zero y).trans
          (by simp)

/-- Two lifts of a section of `S₃` along `S.g`, over `V₁` and `V₂`, that agree on `V₁ ⊓ V₂` glue
to a lift over `V₁ ⊔ V₂`. -/
private theorem exists_lift_sup_of_restrict_eq {U₀ V₁ V₂ : Opens Z}
    (b : ToType (S.X₃.obj.obj (op U₀)))
    (h₁ : V₁ ≤ U₀) (h₂ : V₂ ≤ U₀) (a₁ : ToType (S.X₂.obj.obj (op V₁)))
    (a₂ : ToType (S.X₂.obj.obj (op V₂))) (ha₁ : S.g.hom.app (op V₁) a₁ = b |_ₗ V₁ ⟪h₁⟫ )
    (ha₂ : S.g.hom.app (op V₂) a₂ = b |_ₗ V₂ ⟪h₂⟫ ) (h : a₁ |_ (V₁ ⊓ V₂) = a₂ |_ (V₁ ⊓ V₂)) :
    ∃ α : ToType (S.X₂.obj.obj (op (V₁ ⊔ V₂))),
      S.g.hom.app (op (V₁ ⊔ V₂)) α = b |_ₗ (V₁ ⊔ V₂) ⟪sup_le h₁ h₂⟫ := by
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_glue_pair.{v} S.X₂ a₁ a₂ h
  refine ⟨β, TopCat.Sheaf.eq_of_locally_eq₂ S.X₃ (homOfLE (le_sup_left : V₁ ≤ _))
    (homOfLE (le_sup_right : V₂ ≤ _)) le_rfl _ _ ?_ ?_⟩
  · exact (Presheaf.map_restrict S.g.hom le_sup_left β).symm.trans
      ((congrArg (fun z ↦ ConcreteCategory.hom (S.g.hom.app (op V₁)) z) hβ₁).trans
        (ha₁.trans (Presheaf.restrict_restrict le_sup_left (sup_le h₁ h₂) b).symm))
  · exact (Presheaf.map_restrict S.g.hom le_sup_right β).symm.trans
      ((congrArg (fun z ↦ ConcreteCategory.hom (S.g.hom.app (op V₂)) z) hβ₂).trans
        (ha₂.trans (Presheaf.restrict_restrict le_sup_right (sup_le h₁ h₂) b).symm))

/-- **The patching step for a soft kernel.** Let `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` be a short exact sequence
of sheaves of abelian groups on a normal space with `S₁` soft, and let `b` be a section of `S₃`
over an open set `U₀`. Given a finite family of closed sets `K i`, each contained in an open set
`W i ≤ U₀` over which `b` lifts to `S₂`, the section `b` lifts to `S₂` over an open neighbourhood
of the union of those closed sets.

The lifts are corrected and glued two at a time: softness of `S₁` extends the difference of two
lifts from a neighbourhood of the overlap of the two closed sets, and normality shrinks the two
open sets so that they meet only where the corrected lifts agree. -/
theorem exists_lift_of_finset_univLE [NormalSpace Z] (hS : S.ShortExact) (hsoft : IsSoft S.X₁)
    {U₀ : Opens Z} (b : ToType (S.X₃.obj.obj (op U₀))) {ι : Type*} {K : ι → Set Z}
    (hK : ∀ i, IsClosed (K i)) {W : ι → Opens Z} (hKW : ∀ i, K i ⊆ (W i : Set Z))
    (hWU : ∀ i, W i ≤ U₀) (a : ∀ i, ToType (S.X₂.obj.obj (op (W i))))
    (ha : ∀ i, S.g.hom.app (op (W i)) (a i) = b |_ₗ (W i) ⟪hWU i⟫ ) (t : Finset ι) :
    ∃ (V : Opens Z) (hV : V ≤ U₀), (∀ i ∈ t, K i ⊆ (V : Set Z)) ∧
      ∃ α : ToType (S.X₂.obj.obj (op V)), S.g.hom.app (op V) α = b |_ₗ V ⟪hV⟫ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨⊥, bot_le, by simp, 0, ?_⟩
      rw [map_zero]
      exact (eq_zero_of_bot S.X₃ _).symm
  | @insert j t _ ih =>
      obtain ⟨V, hV, hcov, α, hα⟩ := ih
      have hPclosed : IsClosed (⋃ i ∈ t, K i) := isClosed_biUnion_finset fun i _ ↦ hK i
      have hPV : (⋃ i ∈ t, K i) ⊆ (V : Set Z) := Set.iUnion₂_subset hcov
      have hDV : V ⊓ W j ≤ V := inf_le_left
      have hDW : V ⊓ W j ≤ W j := inf_le_right
      -- on the overlap the difference of the two lifts is a section of the kernel
      have hdg : S.g.hom.app (op (V ⊓ W j))
          ((α |_ₗ (V ⊓ W j) ⟪hDV⟫ ) - ((a j) |_ₗ (V ⊓ W j) ⟪hDW⟫ )) = 0 := by
        rw [map_sub, Presheaf.map_restrict, Presheaf.map_restrict, hα, ha j,
          Presheaf.restrict_restrict, Presheaf.restrict_restrict, sub_self]
      obtain ⟨σ, hσ⟩ := exists_preimage_of_app_eq_zero.{v} hS (V ⊓ W j) _ hdg
      -- softness extends that difference from a neighbourhood of the overlap of the closed sets
      obtain ⟨τ, V', hV'D, hKV', hτ⟩ :=
        hsoft ((⋃ i ∈ t, K i) ∩ K j) (hPclosed.inter (hK j)) (V ⊓ W j)
          (fun x hx ↦ ⟨hPV hx.1, hKW j hx.2⟩) σ
      have hV'V : V' ≤ V := le_trans hV'D hDV
      have hV'W : V' ≤ W j := le_trans hV'D hDW
      have hagree := correction_agree S.f.hom hDV hDW hV'D α (a j) σ τ hσ hτ
      have ha'g : S.g.hom.app (op (W j))
          (a j + S.f.hom.app (op (W j)) (τ |_ₗ (W j) ⟪le_top⟫ )) = b |_ₗ (W j) ⟪hWU j⟫ := by
        rw [map_add, ha j, app_comp_eq_zero_univLE, add_zero]
      -- normality shrinks the two open sets so that they meet only inside `V'`
      obtain ⟨O₁, O₂, hO₁, hO₂, hPO₁, hKO₂, hOdisj⟩ :=
        normal_separation (hPclosed.sdiff V'.2) ((hK j).sdiff V'.2)
          (Set.disjoint_left.mpr fun x hx hx' ↦ hx.2 (hKV' ⟨hx.1, hx'.1⟩))
      have hV₁V : V ⊓ (V' ⊔ ⟨O₁, hO₁⟩) ≤ V := inf_le_left
      have hV₂W : W j ⊓ (V' ⊔ ⟨O₂, hO₂⟩) ≤ W j := inf_le_left
      have hmeet := inf_sup_inf_sup_le_of_disjoint (A := V) (B := W j) (V' := V') hO₁ hO₂ hOdisj
      obtain ⟨β, hβ⟩ := exists_lift_sup_of_restrict_eq (S := S) b (hV₁V.trans hV)
        (hV₂W.trans (hWU j)) (α |_ₗ _ ⟪hV₁V⟫)
        ((a j + S.f.hom.app (op (W j)) (τ |_ₗ (W j) ⟪le_top⟫ )) |_ₗ _ ⟪hV₂W⟫)
        (by rw [Presheaf.map_restrict, hα, Presheaf.restrict_restrict])
        (by rw [Presheaf.map_restrict, ha'g, Presheaf.restrict_restrict])
        (((Presheaf.restrict_restrict inf_le_left hV₁V α).trans
          ((Presheaf.restrict_restrict hmeet hV'V α).symm.trans
            (congrArg (fun z ↦ Presheaf.restrict z (homOfLE hmeet)) hagree.symm))).trans
          ((Presheaf.restrict_restrict hmeet hV'W _).trans
            (Presheaf.restrict_restrict inf_le_right hV₂W _).symm))
      refine ⟨_, _, fun i hi x hx ↦ ?_, β, hβ⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact Or.inr (subset_inf_sup_of_diff_subset hO₂ (hKW i) hKO₂ hx)
      · exact Or.inl (subset_inf_sup_of_diff_subset hO₁ hPV hPO₁ (Set.mem_biUnion hi' hx))

section Compact

variable [CompactSpace Z] [T2Space Z]

/-- **Lifting a section near a compact set.** On a compact Hausdorff space, a section of `S₃` over
an open set `U₀` lifts to `S₂` over an open neighbourhood of any compact subset of `U₀`, provided
the kernel `S₁` is soft.

Local liftability is `CategoryTheory.Presheaf.imageSieve_mem` for the locally surjective `S.g`;
regularity shrinks each open set to a closed neighbourhood and compactness makes the family finite,
after which `exists_lift_of_finset_univLE` patches the lifts. -/
theorem exists_lift_of_isSoft_of_isCompact_univLE (hS : S.ShortExact) (hsoft : IsSoft S.X₁)
    {U₀ : Opens Z} (b : ToType (S.X₃.obj.obj (op U₀))) {L : Set Z} (hL : IsCompact L)
    (hLU : L ⊆ (U₀ : Set Z)) :
    ∃ (V : Opens Z) (hV : V ≤ U₀), L ⊆ (V : Set Z) ∧
      ∃ α : ToType (S.X₂.obj.obj (op V)), S.g.hom.app (op V) α = b |_ₗ V ⟪hV⟫ := by
  classical
  have _hls : CategoryTheory.Sheaf.IsLocallySurjective S.g :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{v} S.g).2 hS.epi_g
  have key : ∀ z : Z, ∃ (W : Opens Z) (hWU : W ≤ U₀) (C : Set Z), IsClosed C ∧
      C ⊆ (W : Set Z) ∧ (z ∈ L → C ∈ nhds z) ∧ ∃ aw : ToType (S.X₂.obj.obj (op W)),
        S.g.hom.app (op W) aw = b |_ₗ W ⟪hWU⟫ := by
    intro z
    by_cases hz : z ∈ L
    · obtain ⟨W, f, ⟨aw, haw⟩, hzW⟩ :=
        Presheaf.imageSieve_mem (Opens.grothendieckTopology Z) S.g.hom b z (hLU hz)
      obtain ⟨C, hCnhd, hCclosed, hCW⟩ := exists_mem_nhds_isClosed_subset (W.2.mem_nhds hzW)
      refine ⟨W, f.le, C, hCclosed, hCW, fun _ ↦ hCnhd, aw, haw.trans ?_⟩
      exact congrArg (fun g : W ⟶ U₀ ↦ ConcreteCategory.hom (S.X₃.obj.map g.op) b)
        (Subsingleton.elim f (homOfLE f.le))
    · refine ⟨⊥, bot_le, ∅, isClosed_empty, Set.empty_subset _, fun h ↦ absurd h hz, 0, ?_⟩
      rw [map_zero]
      exact (eq_zero_of_bot S.X₃ _).symm
  choose W hWU C hCclosed hCW hCnhd aw haw using key
  obtain ⟨tfin, -, hcover⟩ := hL.elim_nhds_subcover C fun z hz ↦ hCnhd z hz
  obtain ⟨V, hV, hcov, α, hα⟩ :=
    exists_lift_of_finset_univLE.{v} hS hsoft b hCclosed hCW hWU aw haw tfin
  exact ⟨V, hV, hcover.trans (Set.iUnion₂_subset hcov), α, hα⟩

/-- **Global sections are exact on a short exact sequence with soft kernel**, on a compact
Hausdorff space. This is the content of the acyclicity of soft sheaves. -/
theorem surjective_sections_of_isSoft_univLE (hS : S.ShortExact) (hsoft : IsSoft S.X₁) :
    Function.Surjective
      (ConcreteCategory.hom (S.g.hom.app (op (⊤ : Opens Z)))) := by
  intro b
  obtain ⟨V, hV, hLV, α, hα⟩ :=
    exists_lift_of_isSoft_of_isCompact_univLE.{v} hS hsoft b (L := Set.univ) isCompact_univ
      (by simp)
  obtain rfl : V = ⊤ := eq_top_iff.mpr fun x _ ↦ hLV (Set.mem_univ x)
  exact ⟨α, hα.trans (Presheaf.restrict_self b)⟩

/-- **The quotient of a soft sheaf by a soft subsheaf is soft**, on a compact Hausdorff space.
This is the second half of the dimension-shifting argument for the acyclicity of soft sheaves. -/
theorem IsSoft.of_shortExact_univLE (hS : S.ShortExact) (h₁ : IsSoft S.X₁) (h₂ : IsSoft S.X₂) :
    IsSoft S.X₃ := by
  intro K hKclosed U hKU s
  obtain ⟨V, hVU, hKV, α, hα⟩ :=
    exists_lift_of_isSoft_of_isCompact_univLE.{v} hS h₁ s hKclosed.isCompact hKU
  obtain ⟨u, V', hV'V, hKV', hu⟩ := h₂ K hKclosed V hKV α
  refine ⟨S.g.hom.app (op ⊤) u, V', le_trans hV'V hVU, hKV', ?_⟩
  rw [← Presheaf.map_restrict, hu, Presheaf.map_restrict, hα, Presheaf.restrict_restrict]

end Compact

end

section Subspace

variable {X : Type u} [TopologicalSpace X] {Y : Set X}

/-- A subset whose distinct points are separated by disjoint open subsets of the ambient space is
Hausdorff as a subspace. This is the separation hypothesis of [Stacks, Tag 09V3], which does not
assume the ambient space Hausdorff. -/
theorem t2Space_coe_of_pairwiseSeparated
    (hSep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y →
      ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ Disjoint U V) :
    T2Space Y := by
  refine ⟨fun z w hzw ↦ ?_⟩
  obtain ⟨U, V, hU, hV, hzU, hwV, hUV⟩ :=
    hSep z.1 z.2 w.1 w.2 fun h ↦ hzw (Subtype.ext h)
  exact ⟨Subtype.val ⁻¹' U, Subtype.val ⁻¹' V, hU.preimage continuous_subtype_val,
    hV.preimage continuous_subtype_val, hzU, hwV, hUV.preimage _⟩

end Subspace

end Stacks.Topology

end
