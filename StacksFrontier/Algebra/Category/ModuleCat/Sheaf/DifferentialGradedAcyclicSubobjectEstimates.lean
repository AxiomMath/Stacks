module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import StacksFrontier.Homology.Injectives.Size.SmallWithRespectToInjections

/-!
# Small subfamilies under a supremum of subobjects

Let `C` be a Grothendieck abelian category and `T` a subobject of `X` having few subobjects.
If `T` lies under a supremum of subobjects of `X`, then it already lies under one stage of an
increasing ordinal-indexed family, and under the supremum of a `κ`-small subfamily of an
arbitrary family.

Both replace a frame distributivity law for the subobject lattice, which is not available: in
place of intersecting the family with `T` and distributing, `T` is small with respect to
monomorphisms and the family is a monomorphic system whose colimit is its supremum.

## Main results

* `Stacks.Injectives.exists_le_of_le_iSup`: the ordinal-chain form.
* `Stacks.Injectives.exists_small_subfamily_le`: the `κ`-small subfamily form.
* `Stacks.Injectives.exists_obj_iSup`: images preserve suprema of subobjects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

omit [Abelian C] [IsGrothendieckAbelian.{w} C] in
/-- The comparison morphism between two nested subobjects is a monomorphism. -/
private theorem mono_ofLE {X : C} (P Q : Subobject X) (h : P ≤ Q) :
    Mono (Subobject.ofLE P Q h) :=
  mono_of_mono_fac (Subobject.ofLE_arrow h)

/-- If every map from `T` into a colimit of a monomorphic system indexed by `J` factors through
a stage, then `T` lies under a stage of any monotone family of subobjects whose supremum
contains it. -/
private theorem exists_le_of_factorization {J : Type w} [Preorder J] [IsFiltered J] {X : C}
    (t : J → Subobject X) (ht : Monotone t) (T : Subobject X) (hle : T ≤ ⨆ j, t j)
    (H : ∀ (B : J ⥤ C), (∀ {i j : J} (f : i ⟶ j), Mono (B.map f)) → ∀ {c : Cocone B},
      IsColimit c → ∀ f : (T : C) ⟶ c.pt, ∃ (j : J) (g : (T : C) ⟶ B.obj j), g ≫ c.ι.app j = f) :
    ∃ j, T ≤ t j := by
  set S : Subobject X := ⨆ j, t j with hS
  let F : J ⥤ MonoOver X :=
    { obj j := MonoOver.mk (t j).arrow
      map {i j} g := MonoOver.homMk (Subobject.ofLE (t i) (t j) (ht (leOfHom g)))
        (Subobject.ofLE_arrow _)
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }
  let cMono : Cocone F :=
    { pt := MonoOver.mk S.arrow
      ι :=
        { app j := MonoOver.homMk (Subobject.ofLE (t j) S (le_iSup t j))
            (Subobject.ofLE_arrow _)
          naturality _ _ _ := Subsingleton.elim _ _ } }
  let cOver := (MonoOver.forget X).mapCocone cMono
  have : Mono cOver.pt.hom := Subobject.arrow_mono S
  have hsup : Subobject.mk cOver.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
    simp [cOver, cMono, F, hS]
  obtain ⟨j, g, hg⟩ := H (F ⋙ MonoOver.forget X ⋙ Over.forget X)
    (fun u => mono_ofLE _ _ (ht (leOfHom u)))
    (IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup F cOver hsup)
    (Subobject.ofLE T S hle)
  refine ⟨j, Subobject.le_of_comm (Y := t j) g ?_⟩
  rw [← Subobject.ofLE_arrow hle, ← hg]
  exact (congrArg (g ≫ ·) (Subobject.ofLE_arrow (le_iSup t j))).symm.trans
    (Category.assoc _ _ _).symm

/-- **A subobject with few subobjects that lies under an increasing ordinal-indexed supremum
of subobjects already lies under one of its stages.**

This is the step that replaces a frame distributivity law for the subobject lattice: instead
of intersecting the increasing family with `T` and distributing, one uses that `T` is small
with respect to monomorphisms (Tag 079F), the increasing family being a monomorphic system
whose colimit is its supremum. -/
theorem exists_le_of_le_iSup {X : C} (α : Ordinal.{w})
    (s : α.ToType → Subobject X) (hs : Monotone s)
    (T : Subobject X) (hT : HasCardinalLT (Subobject (T : C)) α.cof)
    (hle : T ≤ ⨆ i, s i) :
    ∃ i, T ≤ s i := by
  have h1 : (1 : Cardinal.{w}) < α.cof :=
    Stacks.Injectives.one_lt_of_hasCardinalLT_subobject hT
  have hα : α ≠ 0 := by
    rintro rfl
    simp at h1
  have : Nonempty α.ToType := Ordinal.nonempty_toType_iff.2 hα
  exact exists_le_of_factorization s hs T hle fun B hB _ hc f =>
    exists_factorization_of_hasCardinalLT_subobject_cof (T : C) α hT B hB hc f

section Subfamily

variable {ι : Type w} (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- The `κ`-small subsets of `ι`, ordered by inclusion, form a `κ`-filtered category: a
family of fewer than `κ` of them has their union as an upper bound, and a union of fewer than
`κ` sets each of cardinality less than `κ` has cardinality less than `κ` because `κ` is
regular. -/
theorem isCardinalFiltered_smallSet :
    IsCardinalFiltered {S : Set ι // HasCardinalLT (S : Type w) κ} κ :=
  isCardinalFiltered_preorder _ _ fun {_K} f hK =>
    ⟨⟨⋃ k, (f k).1,
      hasCardinalLT_iUnion _ ((hasCardinalLT_iff_cardinal_mk_lt _ _).2 hK)
        fun k => (f k).2⟩,
      fun k => Set.subset_iUnion (fun k => (f k).1) k⟩

/-- The subobject generated by a `κ`-small subfamily. -/
noncomputable def partialSup {X : C} (s : ι → Subobject X)
    (S : {S : Set ι // HasCardinalLT (S : Type w) κ}) : Subobject X :=
  ⨆ i : S.1, s i

omit [Fact κ.IsRegular] in
/-- The subobject generated by a `κ`-small subfamily is monotone in the subfamily. -/
theorem partialSup_mono {X : C} (s : ι → Subobject X)
    {S S' : {S : Set ι // HasCardinalLT (S : Type w) κ}} (h : S ≤ S') :
    partialSup κ s S ≤ partialSup κ s S' :=
  iSup_le fun i => le_iSup (fun j : S'.1 => s j) ⟨i.1, h i.2⟩

/-- The supremum over all `κ`-small subfamilies of the subobjects they generate is the supremum
of the whole family. -/
theorem iSup_partialSup {X : C} (s : ι → Subobject X) :
    (⨆ S : {S : Set ι // HasCardinalLT (S : Type w) κ}, partialSup κ s S) = ⨆ i, s i := by
  refine le_antisymm (iSup_le fun S => iSup_le fun i => le_iSup s i.1) (iSup_le fun i => ?_)
  have hsingle : HasCardinalLT (({i} : Set ι) : Type w) κ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_singleton]
    exact lt_of_lt_of_le Cardinal.one_lt_aleph0 (Fact.out : κ.IsRegular).aleph0_le
  exact (le_iSup (fun j : (({i} : Set ι) : Type w) => s j) ⟨i, rfl⟩).trans
    (le_iSup (partialSup κ s) ⟨{i}, hsingle⟩)

/-- **A subobject with few subobjects that lies under the supremum of an arbitrary family of
subobjects already lies under the supremum of a `κ`-small subfamily.**

This is the size-bookkeeping step of Tag 0FST's tower: it replaces a frame distributivity law
for the subobject lattice by the smallness of `T` with respect to monomorphisms, applied to
the `κ`-filtered system of suprema of `κ`-small subfamilies. -/
theorem exists_small_subfamily_le {X : C} (s : ι → Subobject X) (T : Subobject X)
    (hT : HasCardinalLT (Subobject (T : C)) κ) (hle : T ≤ ⨆ i, s i) :
    ∃ S : Set ι, HasCardinalLT (S : Type w) κ ∧ T ≤ ⨆ i : S, s i := by
  have hcf := isCardinalFiltered_smallSet (ι := ι) κ
  have : IsFiltered {S : Set ι // HasCardinalLT (S : Type w) κ} :=
    isFiltered_of_isCardinalFiltered _ κ
  obtain ⟨S, hS⟩ := exists_le_of_factorization (partialSup κ s)
    (fun _ _ => partialSup_mono κ s) T (hle.trans (iSup_partialSup κ s).ge)
    fun B hB _ hc f => by
      have : ∀ (j j' : {S : Set ι // HasCardinalLT (S : Type w) κ}) (φ : j ⟶ j'),
          Mono (B.map φ) := fun _ _ φ => hB φ
      obtain ⟨j, y, hy⟩ := IsGrothendieckAbelian.IsPresentable.surjectivity hc (κ := κ) hT f
      exact ⟨j, y, hy.symm⟩
  exact ⟨S.1, S.2, hS⟩

end Subfamily

/-- **Images preserve suprema of subobjects.** For `f : X ⟶ Y` in an abelian category the
image functor `Subobject.exists f` is a left adjoint, hence commutes with suprema. -/
theorem exists_obj_iSup {X Y : C} (f : X ⟶ Y) {ι : Type*} (s : ι → Subobject X) :
    (Subobject.exists f).obj (⨆ i, s i) = ⨆ i, (Subobject.exists f).obj (s i) :=
  (Subobject.existsPullbackAdj f).gc.l_iSup

end Stacks.Injectives

end
