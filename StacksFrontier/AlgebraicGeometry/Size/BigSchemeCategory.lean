module

public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.SmallRepresentatives
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.Order.TransfiniteIterationSmall
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# The category `Sch_α` constructed in the proof of Stacks 000J

Starting from a set `S₀` of schemes, the proof of Stacks 000J builds an increasing transfinite
sequence of sets of schemes: each step adds, up to isomorphism, every scheme of size at most
`Bound(size S)` for a scheme `S` already present, and every limit and every colimit, taken in
the category of schemes whenever it exists there, of a countable diagram of schemes already
present; at limit stages the union is taken. The category `Sch_α` is the full subcategory on the
union of the stages below an ordinal `β` of uncountable cofinality.

Here the stages are `AlgebraicGeometry.bigSchemeCategoryStage`, the transfinite iteration
(`transfiniteIterate`) of `AlgebraicGeometry.bigSchemeCategoryStep`, and the category is the full
subcategory on `AlgebraicGeometry.bigSchemeCategory S₀ β`.

## Main definitions

* `AlgebraicGeometry.bigSchemeCategoryStep`: one step of the construction.
* `AlgebraicGeometry.bigSchemeCategory`: the objects of `Sch_α`.

## Main results

* `AlgebraicGeometry.small_bigSchemeCategory`: the objects of `Sch_α` form a set.
* `AlgebraicGeometry.bigSchemeCategory_of_mem`: Stacks 000J (1), `S₀ ⊂ Ob(Sch_α)`.
* `AlgebraicGeometry.exists_bigSchemeCategory_iso_of_size_le`: Stacks 000J (2).
* `AlgebraicGeometry.hasLimit_of_hasLimit_comp_bigSchemeCategory_ι`,
  `AlgebraicGeometry.preservesLimit_bigSchemeCategory_ι`: Stacks 000J (3) as proved in the
  source: if the limit of a countable diagram of `Sch_α` exists in the category of schemes, then
  it exists in `Sch_α` and the comparison morphism is an isomorphism.
* `AlgebraicGeometry.hasColimit_of_hasColimit_comp_bigSchemeCategory_ι`,
  `AlgebraicGeometry.preservesColimit_bigSchemeCategory_ι`: the same for colimits, Stacks 000J
  (4).
* `AlgebraicGeometry.hasPullbacks_bigSchemeCategory`: `Sch_α` has fibre products, computed as
  in the category of schemes.

## Implementation notes

Lean has no von Neumann hierarchy in which schemes live, so the stages `Sch_{f(β)}` of the source
are sets of schemes produced by the step function above, and a set is a `Small.{u}` collection.
The source quantifies over a set `CountCat` of countable categories representing every countable
category up to isomorphism; that set is `CategoryTheory.SmallCategoryOfSet ℕ`, whose members
represent every category with countably many objects and morphisms
(`CategoryTheory.SmallCategoryOfSet.exists_equivalence`). The schemes added for the bound are
chosen representatives (`AlgebraicGeometry.essentiallySmall_schemeSizeBelow`).

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- For every cardinal `c` there is a set of schemes containing a scheme isomorphic to each scheme
of size at most `c` (Stacks 000I). -/
public theorem exists_small_representatives_size_le (c : Cardinal.{u}) :
    ∃ Q : ObjectProperty Scheme.{u}, ObjectProperty.Small.{u} Q ∧
      ∀ T : Scheme.{u}, T.size ≤ c → ∃ T', Q T' ∧ Nonempty (T ≅ T') := by
  have hκ : ℵ₀ ≤ Order.succ (max c ℵ₀) := (le_max_right _ _).trans (Order.le_succ _)
  have := essentiallySmall_schemeSizeBelow _ hκ
  obtain ⟨Q, hQ, hle⟩ := ObjectProperty.EssentiallySmall.exists_small_le'
    (schemeSizeBelow (Order.succ (max c ℵ₀)))
  refine ⟨Q, hQ, fun T hT => ?_⟩
  obtain ⟨T', hT', e⟩ := hle T (hT.trans_lt ((le_max_left _ _).trans_lt (Order.lt_succ _)))
  exact ⟨T', hT', e⟩

/-- A chosen set of schemes containing a scheme isomorphic to each scheme of size at most `c`. -/
public noncomputable def sizeLeRepresentatives (c : Cardinal.{u}) : ObjectProperty Scheme.{u} :=
  (exists_small_representatives_size_le c).choose

/-- The chosen representatives of the schemes of size at most `c` form a set. -/
public instance small_sizeLeRepresentatives (c : Cardinal.{u}) :
    ObjectProperty.Small.{u} (sizeLeRepresentatives c) :=
  (exists_small_representatives_size_le c).choose_spec.1

/-- Every scheme of size at most `c` is isomorphic to one of the chosen representatives. -/
public theorem exists_sizeLeRepresentatives_iso {c : Cardinal.{u}} {T : Scheme.{u}}
    (hT : T.size ≤ c) : ∃ T', sizeLeRepresentatives c T' ∧ Nonempty (T ≅ T') :=
  (exists_small_representatives_size_le c).choose_spec.2 T hT

/-- One step of the construction in the proof of Stacks 000J: to a collection `Q` of schemes add
the chosen limits and colimits, in the category of schemes, of the countable diagrams with values
in `Q` that have one, and representatives of the schemes of size at most `Bound(size S)` for
each `S` in `Q`. The countable diagram categories are the members of `SmallCategoryOfSet ℕ`. -/
public noncomputable def bigSchemeCategoryStep (Q : ObjectProperty Scheme.{u}) :
    ObjectProperty Scheme.{u} :=
  Q ⊔ (⨆ S : SmallCategoryOfSet ℕ, Q.strictLimitsOfShape S.obj) ⊔
    (⨆ S : SmallCategoryOfSet ℕ, Q.strictColimitsOfShape S.obj) ⊔
    (⨆ X : Subtype Q, sizeLeRepresentatives (Cardinal.stacksBound X.1.size))

/-- A step of the construction keeps every scheme already present. -/
public theorem le_bigSchemeCategoryStep (Q : ObjectProperty Scheme.{u}) :
    Q ≤ bigSchemeCategoryStep Q :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

/-- A step of the construction applied to a set of schemes gives a set of schemes. -/
public theorem small_bigSchemeCategoryStep (Q : ObjectProperty Scheme.{u})
    [ObjectProperty.Small.{u} Q] : ObjectProperty.Small.{u} (bigSchemeCategoryStep Q) := by
  unfold bigSchemeCategoryStep
  infer_instance

/-- The stage indexed by the ordinal `β` in the proof of Stacks 000J, starting from `S₀`. -/
public noncomputable def bigSchemeCategoryStage (S₀ : Set Scheme.{u}) (β : Ordinal.{u}) :
    ObjectProperty Scheme.{u} :=
  transfiniteIterate bigSchemeCategoryStep β (· ∈ S₀)

/-- The objects of the category `Sch_α` of Stacks 000J constructed from `S₀` and an ordinal `β`
of uncountable cofinality: the union of the stages below `β`, which for `β` a limit ordinal is
the stage indexed by `β`. -/
public noncomputable def bigSchemeCategory (S₀ : Set Scheme.{u}) (β : Ordinal.{u}) :
    ObjectProperty Scheme.{u} :=
  bigSchemeCategoryStage S₀ β

variable {S₀ : Set Scheme.{u}} {β : Ordinal.{u}}

/-- The stages of the construction increase. -/
public theorem bigSchemeCategoryStage_mono {o o' : Ordinal.{u}} (h : o ≤ o') :
    bigSchemeCategoryStage S₀ o ≤ bigSchemeCategoryStage S₀ o' :=
  monotone_transfiniteIterate _ _ le_bigSchemeCategoryStep h

/-- The stage indexed by a successor ordinal is a step applied to the previous stage. -/
public theorem bigSchemeCategoryStage_succ (o : Ordinal.{u}) :
    bigSchemeCategoryStage S₀ (Order.succ o) =
      bigSchemeCategoryStep (bigSchemeCategoryStage S₀ o) :=
  transfiniteIterate_succ _ _ _ (not_isMax o)

/-- Every stage of the construction is a set of schemes. -/
public instance small_bigSchemeCategoryStage [Small.{u} S₀] (o : Ordinal.{u}) :
    ObjectProperty.Small.{u} (bigSchemeCategoryStage S₀ o) :=
  small_transfiniteIterate _ (fun Q hQ => @small_bigSchemeCategoryStep Q hQ) _
    (inferInstanceAs (Small.{u} S₀)) o

/-- The objects of `Sch_α` form a set. -/
public instance small_bigSchemeCategory [Small.{u} S₀] :
    ObjectProperty.Small.{u} (bigSchemeCategory S₀ β) :=
  small_bigSchemeCategoryStage β

/-- **Stacks 000J (1).** Every scheme of `S₀` is an object of `Sch_α`. -/
public theorem bigSchemeCategory_of_mem {X : Scheme.{u}} (hX : X ∈ S₀) :
    bigSchemeCategory S₀ β X := by
  have h : bigSchemeCategoryStage S₀ ⊥ X := by
    simp only [bigSchemeCategoryStage, transfiniteIterate_bot]
    exact hX
  exact bigSchemeCategoryStage_mono bot_le X h

/-- A countable category is equivalent to a member of `SmallCategoryOfSet ℕ`. -/
private theorem exists_smallCategoryOfSet_equivalence (J : Type*) [Category* J]
    [CountableCategory J] :
    ∃ S : SmallCategoryOfSet ℕ, Nonempty (SmallCategoryOfSet.categoryFamily ℕ S ≌ J) :=
  SmallCategoryOfSet.exists_equivalence ℕ J (by simp) (fun X Y => by simp)

section

variable (hβ : ℵ₀ < β.cof)
include hβ

/-- An ordinal of uncountable cofinality is a limit ordinal. -/
public theorem isSuccLimit_of_aleph0_lt_cof : Order.IsSuccLimit β :=
  Ordinal.one_lt_cof_iff.1 (one_lt_aleph0.trans hβ)

/-- An object of `Sch_α` lies in some stage below `β`. -/
public theorem bigSchemeCategory_iff {X : Scheme.{u}} :
    bigSchemeCategory S₀ β X ↔ ∃ o < β, bigSchemeCategoryStage S₀ o X :=
  transfiniteIterate_apply_iff_of_isSuccLimit _ _ (isSuccLimit_of_aleph0_lt_cof hβ) X

/-- A step applied to a stage below `β` stays inside `Sch_α`. -/
public theorem bigSchemeCategory_of_step {o : Ordinal.{u}} (ho : o < β) {X : Scheme.{u}}
    (hX : bigSchemeCategoryStep (bigSchemeCategoryStage S₀ o) X) : bigSchemeCategory S₀ β X :=
  (bigSchemeCategory_iff hβ).2 ⟨Order.succ o, (isSuccLimit_of_aleph0_lt_cof hβ).succ_lt ho,
    (bigSchemeCategoryStage_succ o).symm ▸ hX⟩

/-- Every countable family of objects of `Sch_α` lies in a single stage below `β`; this is where
the cofinality of `β` is used. -/
public theorem exists_lt_forall_bigSchemeCategoryStage {ι : Type*} [Countable ι]
    (X : ι → Scheme.{u}) (hX : ∀ i, bigSchemeCategory S₀ β (X i)) :
    ∃ o < β, ∀ i, bigSchemeCategoryStage S₀ o (X i) := by
  choose o ho hXo using fun i => (bigSchemeCategory_iff hβ).1 (hX i)
  obtain ⟨m, hm, hom⟩ := Ordinal.exists_lt_forall_le_of_aleph0_lt_cof hβ o ho
  exact ⟨m, hm, fun i => bigSchemeCategoryStage_mono (hom i) _ (hXo i)⟩

/-- **Stacks 000J (2).** For an object `S` of `Sch_α` and a scheme `T` of size at most
`Bound(size S)`, there is an object of `Sch_α` isomorphic to `T`. -/
public theorem exists_bigSchemeCategory_iso_of_size_le {S T : Scheme.{u}}
    (hS : bigSchemeCategory S₀ β S) (hT : T.size ≤ Cardinal.stacksBound S.size) :
    ∃ S', bigSchemeCategory S₀ β S' ∧ Nonempty (T ≅ S') := by
  obtain ⟨o, ho, hSo⟩ := (bigSchemeCategory_iff hβ).1 hS
  obtain ⟨S', hS', e⟩ := exists_sizeLeRepresentatives_iso hT
  refine ⟨S', bigSchemeCategory_of_step hβ ho (Or.inr ?_), e⟩
  simp only [iSup_apply, iSup_Prop_eq]
  exact ⟨⟨S, hSo⟩, hS'⟩

/-- The limit in the category of schemes of a countable diagram of `Sch_α` is isomorphic to an
object of `Sch_α`. -/
public theorem exists_bigSchemeCategory_iso_limit {J : Type*} [Category* J]
    [CountableCategory J] (F : J ⥤ (bigSchemeCategory S₀ β).FullSubcategory)
    [HasLimit (F ⋙ (bigSchemeCategory S₀ β).ι)] :
    ∃ X : (bigSchemeCategory S₀ β).FullSubcategory,
      Nonempty ((bigSchemeCategory S₀ β).ι.obj X ≅ limit (F ⋙ (bigSchemeCategory S₀ β).ι)) := by
  obtain ⟨o, ho, hFo⟩ :=
    exists_lt_forall_bigSchemeCategoryStage hβ (fun j => (F.obj j).1) (fun j => (F.obj j).2)
  obtain ⟨S, ⟨e⟩⟩ := exists_smallCategoryOfSet_equivalence J
  let G := e.functor ⋙ F ⋙ (bigSchemeCategory S₀ β).ι
  have hG : bigSchemeCategoryStep (bigSchemeCategoryStage S₀ o) (limit G) := by
    refine Or.inl (Or.inl (Or.inr ?_))
    simp only [iSup_apply, iSup_Prop_eq]
    exact ⟨S, ObjectProperty.strictLimitsOfShape.limit G fun j => hFo _⟩
  exact ⟨⟨limit G, bigSchemeCategory_of_step hβ ho hG⟩,
    ⟨HasLimit.isoOfEquivalence e (Iso.refl _)⟩⟩

/-- The colimit in the category of schemes of a countable diagram of `Sch_α` is isomorphic to an
object of `Sch_α`. -/
public theorem exists_bigSchemeCategory_iso_colimit {J : Type*} [Category* J]
    [CountableCategory J] (F : J ⥤ (bigSchemeCategory S₀ β).FullSubcategory)
    [HasColimit (F ⋙ (bigSchemeCategory S₀ β).ι)] :
    ∃ X : (bigSchemeCategory S₀ β).FullSubcategory,
      Nonempty ((bigSchemeCategory S₀ β).ι.obj X ≅
        colimit (F ⋙ (bigSchemeCategory S₀ β).ι)) := by
  obtain ⟨o, ho, hFo⟩ :=
    exists_lt_forall_bigSchemeCategoryStage hβ (fun j => (F.obj j).1) (fun j => (F.obj j).2)
  obtain ⟨S, ⟨e⟩⟩ := exists_smallCategoryOfSet_equivalence J
  let G := e.functor ⋙ F ⋙ (bigSchemeCategory S₀ β).ι
  have hG : bigSchemeCategoryStep (bigSchemeCategoryStage S₀ o) (colimit G) := by
    refine Or.inl (Or.inr ?_)
    simp only [iSup_apply, iSup_Prop_eq]
    exact ⟨S, ObjectProperty.strictColimitsOfShape.colimit G fun j => hFo _⟩
  exact ⟨⟨colimit G, bigSchemeCategory_of_step hβ ho hG⟩,
    ⟨HasColimit.isoOfEquivalence e (Iso.refl _)⟩⟩

/-- **Stacks 000J (3), existence.** If the limit of a countable diagram of `Sch_α` exists in the
category of schemes, then it exists in `Sch_α`. -/
public theorem hasLimit_of_hasLimit_comp_bigSchemeCategory_ι {J : Type*} [Category* J]
    [CountableCategory J] (F : J ⥤ (bigSchemeCategory S₀ β).FullSubcategory)
    [HasLimit (F ⋙ (bigSchemeCategory S₀ β).ι)] : HasLimit F := by
  obtain ⟨X, ⟨i⟩⟩ := exists_bigSchemeCategory_iso_limit hβ F
  let := createsLimitOfFullyFaithfulOfIso X i
  exact hasLimit_of_created F (bigSchemeCategory S₀ β).ι

/-- **Stacks 000J (3), comparison.** If the limit of a countable diagram of `Sch_α` exists in the
category of schemes, then the inclusion of `Sch_α` preserves it: the natural morphism between the
two limits is an isomorphism. -/
public theorem preservesLimit_bigSchemeCategory_ι {J : Type*} [Category* J]
    [CountableCategory J] (F : J ⥤ (bigSchemeCategory S₀ β).FullSubcategory)
    [HasLimit (F ⋙ (bigSchemeCategory S₀ β).ι)] :
    PreservesLimit F (bigSchemeCategory S₀ β).ι := by
  obtain ⟨X, ⟨i⟩⟩ := exists_bigSchemeCategory_iso_limit hβ F
  let := createsLimitOfFullyFaithfulOfIso X i
  infer_instance

/-- **Stacks 000J (4), existence.** If the colimit of a countable diagram of `Sch_α` exists in the
category of schemes, then it exists in `Sch_α`. -/
public theorem hasColimit_of_hasColimit_comp_bigSchemeCategory_ι {J : Type*} [Category* J]
    [CountableCategory J] (F : J ⥤ (bigSchemeCategory S₀ β).FullSubcategory)
    [HasColimit (F ⋙ (bigSchemeCategory S₀ β).ι)] : HasColimit F := by
  obtain ⟨X, ⟨i⟩⟩ := exists_bigSchemeCategory_iso_colimit hβ F
  let := createsColimitOfFullyFaithfulOfIso X i
  exact hasColimit_of_created F (bigSchemeCategory S₀ β).ι

/-- **Stacks 000J (4), comparison.** If the colimit of a countable diagram of `Sch_α` exists in
the category of schemes, then the inclusion of `Sch_α` preserves it: the natural morphism between
the two colimits is an isomorphism. -/
public theorem preservesColimit_bigSchemeCategory_ι {J : Type*} [Category* J]
    [CountableCategory J] (F : J ⥤ (bigSchemeCategory S₀ β).FullSubcategory)
    [HasColimit (F ⋙ (bigSchemeCategory S₀ β).ι)] :
    PreservesColimit F (bigSchemeCategory S₀ β).ι := by
  obtain ⟨X, ⟨i⟩⟩ := exists_bigSchemeCategory_iso_colimit hβ F
  let := createsColimitOfFullyFaithfulOfIso X i
  infer_instance

/-- `Sch_α` has fibre products. -/
public theorem hasPullbacks_bigSchemeCategory :
    HasPullbacks (bigSchemeCategory S₀ β).FullSubcategory :=
  ⟨fun F => hasLimit_of_hasLimit_comp_bigSchemeCategory_ι hβ F⟩

/-- The inclusion of `Sch_α` into the category of schemes preserves fibre products. -/
public theorem preservesPullbacks_bigSchemeCategory_ι :
    PreservesLimitsOfShape WalkingCospan (bigSchemeCategory S₀ β).ι :=
  ⟨fun {F} => preservesLimit_bigSchemeCategory_ι hβ F⟩

end

end AlgebraicGeometry
