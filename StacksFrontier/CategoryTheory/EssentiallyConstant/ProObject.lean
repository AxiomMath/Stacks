module

public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject

/-!
# Essentially constant pro-objects

For a diagram `M : I ⥤ C` indexed by a *cofiltered* category `I`, this file characterises when
`M` is an *essentially constant pro-object*, i.e. when the formal cofiltered limit that `M`
represents is already represented by a single object `X` of `C`. The four equivalent conditions
are

1. `IsEssentiallyConstantPro M`: there are a cone `c` with apex `X`, an index `i`
   and a morphism `s : M i ⟶ X` splitting the projection `p_i` (so
   `p_i ≫ s = 𝟙 X`) which is cofinal, in the sense that for every `j` some
   transition map into `M j` factors as a transition map into `M i` followed by
   `s ≫ p_j`;
2. there is a cone `c` with apex `X` for which the canonical comparison
   `colim_{i ∈ Iᵒᵖ} Mor(M_i, W) → Mor(X, W)` is bijective for every `W`;
3. the same, for a cone that is in addition a limit cone;
4. there are `X`, an index `i` and a morphism `s : M i ⟶ X` for which the reverse
   map `Mor(X, W) → colim_j Mor(M_j, W)`, `h ↦ [s ≫ h]`, is bijective for every
   `W`.

Conditions (2), (3), (4) are *defined* as the corresponding ind-object conditions of
`EssentiallyConstantInd` applied to `M.op : Iᵒᵖ ⥤ Cᵒᵖ`. Unfolding the opposites turns them into
the displayed statements: a cocone on `M.op` is a cone on `M`, an object `W : Cᵒᵖ` is an object of
`C`, and `Mor_{Cᵒᵖ}(op W, op M_i) = Mor_C(M_i, W)`, so
`EssentiallyConstantInd.homDiagram M.op (op W)` is the `Iᵒᵖ`-indexed diagram `i ↦ Mor(M_i, W)` and
`EssentiallyConstantInd.homComparison M.op c.op (op W)` is the comparison
`colim_i Mor(M_i, W) → Mor(c.pt, W)`.

In cases (2), (3), (4) the object `X` is moreover a value of the essentially constant system:
see `isEssentiallyConstantWith_of_bijective_homComparison` and
`isEssentiallyConstantWith_of_bijective_homComparisonInv`.

## Implementation notes

Condition (1) mentions no limit, so `IsEssentiallyConstantWith` and the two lemmas
`isEssentiallyConstantWith_op` and `isEssentiallyConstantWith_of_op`, which move a witness across
`Cone.op` / `Cocone.unop`, are stated for an arbitrary index category. Conditions (2), (3), (4)
and their equivalence keep `I : Type v` with `SmallCategory I`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.EssentiallyConstantPro

universe v' u' v u

section ArbitraryIndex

variable {C : Type u} [Category.{v} C] {I : Type u'} [Category.{v'} I]

section Witness

variable {J : Type*} [Category J]

/-- `M` is essentially constant as a pro-object with value `c.pt`, with respect to
the cone `c`, witnessed by an index `i` and a morphism `s : M i ⟶ c.pt`, if `s`
splits the projection `p_i` and is cofinal. -/
structure IsEssentiallyConstantWith (M : J ⥤ C) (c : Cone M) (i : J)
    (s : M.obj i ⟶ c.pt) : Prop where
  /-- `s ∘ p_i = id_X`. -/
  retraction : c.π.app i ≫ s = 𝟙 c.pt
  /-- For each `j`, the composite `M_k → M_i → X → M_j` is a transition map of the
  diagram for a suitable `k`. -/
  cofinal : ∀ j : J, ∃ (k : J) (σ : k ⟶ i) (τ : k ⟶ j),
      M.map τ = M.map σ ≫ s ≫ c.π.app j

end Witness

/-- `M` is an *essentially constant pro-object* if there exist a cone `c`, an
index `i`, and a morphism `s : M i ⟶ c.pt` witnessing it. -/
@[stacks 05PU "(2), cofiltered case: the predicate that M is essentially constant"]
def IsEssentiallyConstantPro (M : I ⥤ C) : Prop :=
  ∃ (c : Cone M) (i : I) (s : M.obj i ⟶ c.pt), IsEssentiallyConstantWith M c i s

/-! ### Duality for condition (1) -/

/-- Opposite of an essential-constancy witness for a pro-object: it becomes one
for the ind-object `M.op` on the opposite cocone. -/
theorem isEssentiallyConstantWith_op {M : I ⥤ C} {c : Cone M} {i : I}
    {s : M.obj i ⟶ c.pt} (hs : IsEssentiallyConstantWith M c i s) :
    EssentiallyConstantInd.IsEssentiallyConstantWith M.op c.op (op i) s.op where
  retraction := by
    simpa [← op_comp] using congrArg Quiver.Hom.op hs.retraction
  cofinal := by
    intro j
    obtain ⟨k, σ, τ, hkστ⟩ := hs.cofinal j.unop
    refine ⟨op k, σ.op, τ.op, ?_⟩
    simpa [← op_comp] using congrArg Quiver.Hom.op hkστ

/-- Unopposite of an essential-constancy witness for the ind-object `M.op`: it
becomes one for the pro-object `M` on the underlying cone. -/
theorem isEssentiallyConstantWith_of_op {M : I ⥤ C} {t : Cocone M.op} {i : Iᵒᵖ}
    {r : t.pt ⟶ M.op.obj i}
    (hr : EssentiallyConstantInd.IsEssentiallyConstantWith M.op t i r) :
    IsEssentiallyConstantWith M t.unop i.unop r.unop where
  retraction := by
    simpa [← unop_comp] using congrArg Quiver.Hom.unop hr.retraction
  cofinal := by
    intro j
    obtain ⟨k, σ, τ, hkστ⟩ := hr.cofinal (op j)
    refine ⟨k.unop, σ.unop, τ.unop, Quiver.Hom.op_inj ?_⟩
    simpa [op_comp] using hkστ

/-- `M` is an essentially constant pro-object if and only if `M.op` is an essentially constant
ind-object. -/
theorem isEssentiallyConstantPro_iff_op (M : I ⥤ C) :
    IsEssentiallyConstantPro M ↔ EssentiallyConstantInd.IsEssentiallyConstantInd M.op := by
  constructor
  · rintro ⟨c, i, s, hs⟩
    exact ⟨c.op, op i, s.op, isEssentiallyConstantWith_op hs⟩
  · rintro ⟨t, i, r, hr⟩
    exact ⟨t.unop, i.unop, r.unop, isEssentiallyConstantWith_of_op hr⟩

end ArbitraryIndex

section SmallIndex

variable {C : Type u} [Category.{v} C] {I : Type v} [SmallCategory I]

/-- There is a cone `(X, {p_i})` for `M` such that the comparison
`colim_i Mor(M_i, W) → Mor(X, W)` is bijective for every `W`, stated for the opposite diagram. -/
abbrev HasConeWithBijectiveHomColimit (M : I ⥤ C) : Prop :=
  EssentiallyConstantInd.HasCoconeWithBijectiveHomComparison M.op

/-- The limit `X = lim_i M_i` exists and the comparison `colim_i Mor(M_i, W) → Mor(X, W)` is
bijective for every `W`, stated for the opposite diagram: a colimit cocone on `M.op` is the
opposite of a limit cone on `M`. -/
abbrev HasLimitWithBijectiveHomColimit (M : I ⥤ C) : Prop :=
  EssentiallyConstantInd.HasColimitWithBijectiveHomComparison M.op

/-- There exist an object `X`, an index `i` and a morphism `s : M i ⟶ X` such that
`Mor(X, W) → colim_j Mor(M_j, W)`, `h ↦ [s ≫ h]`, is bijective for every `W`, stated for the
opposite diagram. -/
abbrev HasReflectionWithBijectiveHomColimit (M : I ⥤ C) : Prop :=
  EssentiallyConstantInd.HasCoreflectionWithBijectiveHomComparison M.op

/-! ### The equivalence, and the value of the essentially constant system -/

/-- If the comparison map `colim_i Mor(M_i, W) → Mor(c.pt, W)` is bijective for every `W` at the
cone `c`, then `M` is essentially constant as a pro-object with value `c.pt`, with respect to the
cone `c`. -/
@[stacks 05PZ]
theorem isEssentiallyConstantWith_of_bijective_homComparison (M : I ⥤ C) [IsCofiltered I]
    (c : Cone M)
    (h : ∀ W : Cᵒᵖ, Function.Bijective
      (EssentiallyConstantInd.homComparison M.op c.op W)) :
    ∃ (i : I) (s : M.obj i ⟶ c.pt), IsEssentiallyConstantWith M c i s := by
  obtain ⟨i, r, hr⟩ :=
    EssentiallyConstantInd.isEssentiallyConstantWith_of_bijective_homComparison M.op c.op h
  exact ⟨i.unop, r.unop, isEssentiallyConstantWith_of_op hr⟩

/-- If the reverse comparison map `Mor(X, W) → colim_j Mor(M_j, W)` is bijective for every `W`
at `(X, i, s)`, then `X` is the apex of a cone with respect to which `M` is essentially constant,
so `X` is a value of the essentially constant system. -/
@[stacks 05PZ]
theorem isEssentiallyConstantWith_of_bijective_homComparisonInv (M : I ⥤ C) [IsCofiltered I]
    (X : C) (i : I) (s : M.obj i ⟶ X)
    (h : ∀ W : Cᵒᵖ, Function.Bijective
      (EssentiallyConstantInd.homComparisonInv M.op s.op W)) :
    ∃ c : Cone M, c.pt = X ∧
      ∃ (i' : I) (s' : M.obj i' ⟶ c.pt), IsEssentiallyConstantWith M c i' s' := by
  obtain ⟨t, ht, i', r', hr'⟩ :=
    EssentiallyConstantInd.isEssentiallyConstantWith_of_bijective_homComparisonInv
      M.op (op X) (op i) s.op h
  exact ⟨t.unop, congrArg Opposite.unop ht, i'.unop, r'.unop,
    isEssentiallyConstantWith_of_op hr'⟩

/-- For a cofiltered diagram `M : I ⥤ C` the four conditions (1) `M` is an essentially constant
pro-object, (2) some cone has a bijective Hom-colimit comparison at every `W`, (3) some limit cone
does, and (4) some `s : M i ⟶ X` has a bijective reverse comparison at every `W`, are
equivalent. -/
@[stacks 05PZ]
theorem essentiallyConstantPro_tfae [IsCofiltered I] (M : I ⥤ C) :
    [ IsEssentiallyConstantPro M,
      HasConeWithBijectiveHomColimit M,
      HasLimitWithBijectiveHomColimit M,
      HasReflectionWithBijectiveHomColimit M ].TFAE := by
  have hop := EssentiallyConstantInd.essentiallyConstantInd_tfae M.op
  tfae_have 1 → 2 := fun h₁ =>
    (hop.out 1 2).mp ((isEssentiallyConstantPro_iff_op M).mp h₁)
  tfae_have 2 → 3 := (hop.out 2 3).mp
  tfae_have 3 → 4 := (hop.out 3 4).mp
  tfae_have 4 → 1 := fun h₄ =>
    (isEssentiallyConstantPro_iff_op M).mpr ((hop.out 4 1).mp h₄)
  tfae_finish

end SmallIndex

end CategoryTheory.EssentiallyConstantPro
