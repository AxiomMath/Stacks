module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.ColimitDescent
public import StacksFrontier.AlgebraicGeometry.QcqsOpenInduction

/-!
# Colimit comparisons along long exact sequences of diagrams

Let `I` be a shape along which colimits of abelian groups are exact — a filtered category, for
instance. Suppose given, for every degree `n`, a sequence of diagrams `I ⥤ Ab`

`D₄ n ⟶ M n ⟶ D₁ n ⟶ D₄ (n + 1) ⟶ M (n + 1) ⟶ D₁ (n + 1) ⟶ ⋯`

which is exact, starting with a monomorphism `D₄ 0 ⟶ M 0`, a sequence of abelian groups of the
same shape which is exact in the same sense, and comparison morphisms `colim D ⟶ T` from the
colimit of each diagram to the corresponding group, commuting with the maps of the two sequences.
If the comparisons at `M` and `D₁` are isomorphisms in every degree, so is the comparison at `D₄`.
In positive degrees this is the five lemma on a window of the colimit sequence, which is exact
because colimits along `I` are exact; in degree zero it is the four lemma on the initial segment.

This is the formal half of the Mayer–Vietoris induction of [Stacks, Tag 03Q6]: with
`D₄ = H(U ⊔ V)`, `M = H(U) ⊞ H(V)` and `D₁ = H(U ⊓ V)` on the levels of an inverse system and `T`
the same groups on the limit, the colimit statement passes from `U`, `V` and `U ⊓ V` to `U ⊔ V`.
Nothing here depends on how the cohomology groups are modelled; the sequences and their
compatibility are data. The comparison at a biproduct term `M = D₂ ⊞ D₃` is reduced to those at
`D₂` and `D₃` by `Stacks.Cohomology.MayerVietoris.isIso_of_additive_of_split_biprod`.

## Main definitions

* `Stacks.Cohomology.ColimitLongExact.Ladder` — the two long exact sequences and the comparisons.

## Main results

* `Stacks.Cohomology.ColimitLongExact.Ladder.isIso_comparison₄` — the descent, and
  `Stacks.Cohomology.ColimitLongExact.Ladder.isIso_comparisonM` its form at the middle term.
* `Stacks.Cohomology.ColimitLongExact.isIso_colimitDesc_iff` — a comparison `colim D ⟶ T` built
  from a cocone is invertible exactly when the cocone is a colimit cocone.
* `AlgebraicGeometry.Scheme.Opens.MayerVietorisColimitSystem.holds_of_affine` — **the
  Mayer–Vietoris induction**: for a system of cohomology diagrams over the opens of a
  quasi-separated scheme with Mayer–Vietoris ladders, the colimit property over affine opens
  implies it over every quasi-compact open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁

namespace Stacks.Cohomology.ColimitLongExact

variable {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I AddCommGrpCat.{w}]

/-- **A ladder from a long exact sequence of diagrams to a long exact sequence of abelian groups.**
The terms of the first are diagrams `D₄ n`, `M n`, `D₁ n`; those of the second are groups `T₄ n`,
`TM n`, `T₁ n`; the comparisons `c₄ n`, `cM n`, `c₁ n` go from the colimit of each diagram to the
corresponding group. -/
structure Ladder (I : Type u₁) [Category.{v₁} I] [HasColimitsOfShape I AddCommGrpCat.{w}] where
  /-- The diagrams. -/
  D₄ : ℕ → I ⥤ AddCommGrpCat.{w}
  /-- The diagrams. -/
  M : ℕ → I ⥤ AddCommGrpCat.{w}
  /-- The diagrams. -/
  D₁ : ℕ → I ⥤ AddCommGrpCat.{w}
  /-- The maps of the sequence of diagrams. -/
  a : ∀ n, D₄ n ⟶ M n
  /-- The maps of the sequence of diagrams. -/
  b : ∀ n, M n ⟶ D₁ n
  /-- The connecting maps of the sequence of diagrams. -/
  δ : ∀ n, D₁ n ⟶ D₄ (n + 1)
  /-- The groups. -/
  T₄ : ℕ → AddCommGrpCat.{w}
  /-- The groups. -/
  TM : ℕ → AddCommGrpCat.{w}
  /-- The groups. -/
  T₁ : ℕ → AddCommGrpCat.{w}
  /-- The maps of the sequence of groups. -/
  A : ∀ n, T₄ n ⟶ TM n
  /-- The maps of the sequence of groups. -/
  B' : ∀ n, TM n ⟶ T₁ n
  /-- The connecting maps of the sequence of groups. -/
  Δ : ∀ n, T₁ n ⟶ T₄ (n + 1)
  /-- The composite `a n ≫ b n` vanishes. -/
  wab : ∀ n, a n ≫ b n = 0
  /-- The composite `b n ≫ δ n` vanishes. -/
  wbδ : ∀ n, b n ≫ δ n = 0
  /-- The composite `δ n ≫ a (n + 1)` vanishes. -/
  wδa : ∀ n, δ n ≫ a (n + 1) = 0
  /-- The sequence of diagrams is exact at `M n`. -/
  exact_ab : ∀ n, (ShortComplex.mk _ _ (wab n)).Exact
  /-- The sequence of diagrams is exact at `D₁ n`. -/
  exact_bδ : ∀ n, (ShortComplex.mk _ _ (wbδ n)).Exact
  /-- The sequence of diagrams is exact at `D₄ (n + 1)`. -/
  exact_δa : ∀ n, (ShortComplex.mk _ _ (wδa n)).Exact
  /-- The first map `a 0` of the sequence of diagrams is a monomorphism. -/
  mono_a : Mono (a 0)
  /-- The composite `A n ≫ B' n` vanishes. -/
  wAB : ∀ n, A n ≫ B' n = 0
  /-- The composite `B' n ≫ Δ n` vanishes. -/
  wBΔ : ∀ n, B' n ≫ Δ n = 0
  /-- The composite `Δ n ≫ A (n + 1)` vanishes. -/
  wΔA : ∀ n, Δ n ≫ A (n + 1) = 0
  /-- The sequence of groups is exact at `TM n`. -/
  exact_AB : ∀ n, (ShortComplex.mk _ _ (wAB n)).Exact
  /-- The sequence of groups is exact at `T₁ n`. -/
  exact_BΔ : ∀ n, (ShortComplex.mk _ _ (wBΔ n)).Exact
  /-- The sequence of groups is exact at `T₄ (n + 1)`. -/
  exact_ΔA : ∀ n, (ShortComplex.mk _ _ (wΔA n)).Exact
  /-- The first map `A 0` of the sequence of groups is a monomorphism. -/
  mono_A : Mono (A 0)
  /-- The comparisons. -/
  c₄ : ∀ n, colimit (D₄ n) ⟶ T₄ n
  /-- The comparisons. -/
  cM : ∀ n, colimit (M n) ⟶ TM n
  /-- The comparisons. -/
  c₁ : ∀ n, colimit (D₁ n) ⟶ T₁ n
  /-- The comparisons commute with `a n` and `A n`. -/
  comm_a : ∀ n, colim.map (a n) ≫ cM n = c₄ n ≫ A n
  /-- The comparisons commute with `b n` and `B' n`. -/
  comm_b : ∀ n, colim.map (b n) ≫ c₁ n = cM n ≫ B' n
  /-- The comparisons commute with `δ n` and `Δ n`. -/
  comm_δ : ∀ n, colim.map (δ n) ≫ c₄ (n + 1) = c₁ n ≫ Δ n

namespace Ladder

/-- A four-arrow sequence is exact when its consecutive composites vanish and its three short
complexes are exact. -/
private theorem exact_mk₄ {C : Type*} [Category C] [Preadditive C] {X₀ X₁ X₂ X₃ X₄ : C}
    {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂} {h : X₂ ⟶ X₃} {k : X₃ ⟶ X₄} (w₀ : f ≫ g = 0) (w₁ : g ≫ h = 0)
    (w₂ : h ≫ k = 0) (e₀ : (ShortComplex.mk f g w₀).Exact) (e₁ : (ShortComplex.mk g h w₁).Exact)
    (e₂ : (ShortComplex.mk h k w₂).Exact) : (ComposableArrows.mk₄ f g h k).Exact := by
  refine ComposableArrows.Exact.mk (ComposableArrows.IsComplex.mk ?_) ?_ <;> intro i hi <;>
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  exacts [w₀, w₁, w₂, e₀, e₁, e₂]

variable [HasExactColimitsOfShape I AddCommGrpCat.{w}] (L : Ladder.{w} I)

/-- The window of the colimit sequence in degrees `n`, `n + 1`. -/
def colimWindow (n : ℕ) : ComposableArrows AddCommGrpCat.{w} 4 :=
  ComposableArrows.mk₄ (colim.map (L.b n)) (colim.map (L.δ n)) (colim.map (L.a (n + 1)))
    (colim.map (L.b (n + 1)))

/-- The window of the sequence of groups in degrees `n`, `n + 1`. -/
def window (n : ℕ) : ComposableArrows AddCommGrpCat.{w} 4 :=
  ComposableArrows.mk₄ (L.B' n) (L.Δ n) (L.A (n + 1)) (L.B' (n + 1))

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
/-- If `f ≫ g = 0` for morphisms of diagrams, then `colim.map f ≫ colim.map g = 0`. -/
theorem colim_map_comp_eq_zero {A B C : I ⥤ AddCommGrpCat.{w}} (f : A ⟶ B) (g : B ⟶ C)
    (h : f ≫ g = 0) : colim.map f ≫ colim.map g = 0 := by
  rw [← Functor.map_comp, h, Functor.map_zero]

/-- The window `colimWindow n` of the colimit sequence is exact. -/
theorem colimWindow_exact (n : ℕ) : (L.colimWindow n).Exact :=
  exact_mk₄ (colim_map_comp_eq_zero _ _ (L.wbδ n)) (colim_map_comp_eq_zero _ _ (L.wδa n))
    (colim_map_comp_eq_zero _ _ (L.wab (n + 1))) ((L.exact_bδ n).map colim)
    ((L.exact_δa n).map colim) ((L.exact_ab (n + 1)).map colim)

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
/-- The window `window n` of the sequence of groups is exact. -/
theorem window_exact (n : ℕ) : (L.window n).Exact :=
  exact_mk₄ (L.wBΔ n) (L.wΔA n) (L.wAB (n + 1)) (L.exact_BΔ n) (L.exact_ΔA n)
    (L.exact_AB (n + 1))

/-- The comparison of the two windows. -/
def windowMap (n : ℕ) : L.colimWindow n ⟶ L.window n :=
  ComposableArrows.homMk₄ (L.cM n) (L.c₁ n) (L.c₄ (n + 1)) (L.cM (n + 1)) (L.c₁ (n + 1))
    (L.comm_b n) (L.comm_δ n) (L.comm_a (n + 1)) (L.comm_b (n + 1))

/-- The initial segment of the colimit sequence. -/
def colimInitial : ComposableArrows AddCommGrpCat.{w} 2 :=
  ComposableArrows.mk₂ (colim.map (L.a 0)) (colim.map (L.b 0))

/-- The initial segment of the sequence of groups. -/
def initial : ComposableArrows AddCommGrpCat.{w} 2 :=
  ComposableArrows.mk₂ (L.A 0) (L.B' 0)

/-- The comparison of the two initial segments. -/
def initialMap : L.colimInitial ⟶ L.initial :=
  ComposableArrows.homMk₂ (L.c₄ 0) (L.cM 0) (L.c₁ 0) (L.comm_a 0) (L.comm_b 0)

/-- **Descent along the ladder.** If the comparisons at `M` and at `D₁` are isomorphisms in every
degree, so is the comparison at `D₄`. -/
theorem isIso_comparison₄ (hM : ∀ n, IsIso (L.cM n)) (h₁ : ∀ n, IsIso (L.c₁ n)) :
    ∀ n, IsIso (L.c₄ n)
  | 0 => by
    have : IsIso (ComposableArrows.app' L.initialMap 1) := hM 0
    have : IsIso (ComposableArrows.app' L.initialMap 2) := h₁ 0
    have : Mono (L.a 0) := L.mono_a
    have hm : Mono (colim.map (L.a 0)) := inferInstance
    exact Abelian.isIso_of_isIso_of_mono L.initialMap
      (ComposableArrows.exact₂_mk _ _ ((L.exact_ab 0).map colim))
      (ComposableArrows.exact₂_mk _ _ (L.exact_AB 0)) hm L.mono_A
      inferInstance inferInstance
  | m + 1 => by
    have : IsIso (ComposableArrows.app' (L.windowMap m) 0) := hM m
    have : IsIso (ComposableArrows.app' (L.windowMap m) 1) := h₁ m
    have : IsIso (ComposableArrows.app' (L.windowMap m) 3) := hM (m + 1)
    have : IsIso (ComposableArrows.app' (L.windowMap m) 4) := h₁ (m + 1)
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (L.colimWindow_exact m)
      (L.window_exact m) (L.windowMap m) inferInstance inferInstance inferInstance inferInstance

open ZeroObject

/-- The window of the colimit sequence centred at `M (n + 1)`. -/
def colimWindowM (n : ℕ) : ComposableArrows AddCommGrpCat.{w} 4 :=
  ComposableArrows.mk₄ (colim.map (L.δ n)) (colim.map (L.a (n + 1))) (colim.map (L.b (n + 1)))
    (colim.map (L.δ (n + 1)))

/-- The window of the sequence of groups centred at `TM (n + 1)`. -/
def windowM (n : ℕ) : ComposableArrows AddCommGrpCat.{w} 4 :=
  ComposableArrows.mk₄ (L.Δ n) (L.A (n + 1)) (L.B' (n + 1)) (L.Δ (n + 1))

/-- The window `colimWindowM n` of the colimit sequence is exact. -/
theorem colimWindowM_exact (n : ℕ) : (L.colimWindowM n).Exact :=
  exact_mk₄ (colim_map_comp_eq_zero _ _ (L.wδa n)) (colim_map_comp_eq_zero _ _ (L.wab (n + 1)))
    (colim_map_comp_eq_zero _ _ (L.wbδ (n + 1))) ((L.exact_δa n).map colim)
    ((L.exact_ab (n + 1)).map colim) ((L.exact_bδ (n + 1)).map colim)

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
/-- The window `windowM n` of the sequence of groups is exact. -/
theorem windowM_exact (n : ℕ) : (L.windowM n).Exact :=
  exact_mk₄ (L.wΔA n) (L.wAB (n + 1)) (L.wBΔ (n + 1)) (L.exact_ΔA n) (L.exact_AB (n + 1))
    (L.exact_BΔ (n + 1))

/-- The comparison of the two windows centred at the middle term. -/
def windowMapM (n : ℕ) : L.colimWindowM n ⟶ L.windowM n :=
  ComposableArrows.homMk₄ (L.c₁ n) (L.c₄ (n + 1)) (L.cM (n + 1)) (L.c₁ (n + 1)) (L.c₄ (n + 2))
    (L.comm_δ n) (L.comm_a (n + 1)) (L.comm_b (n + 1)) (L.comm_δ (n + 1))

/-- The initial window of the colimit sequence, `0 ⟶ D₄ 0 ⟶ M 0 ⟶ D₁ 0 ⟶ D₄ 1`. -/
def colimInitialM : ComposableArrows AddCommGrpCat.{w} 4 :=
  ComposableArrows.mk₄ (0 : 0 ⟶ colimit (L.D₄ 0)) (colim.map (L.a 0)) (colim.map (L.b 0))
    (colim.map (L.δ 0))

/-- The initial window of the sequence of groups, `0 ⟶ T₄ 0 ⟶ TM 0 ⟶ T₁ 0 ⟶ T₄ 1`. -/
def initialM : ComposableArrows AddCommGrpCat.{w} 4 :=
  ComposableArrows.mk₄ (0 : 0 ⟶ L.T₄ 0) (L.A 0) (L.B' 0) (L.Δ 0)

/-- The initial window `0 ⟶ colim D₄ 0 ⟶ colim M 0 ⟶ colim D₁ 0 ⟶ colim D₄ 1` is exact. -/
theorem colimInitialM_exact : L.colimInitialM.Exact :=
  have : Mono (L.a 0) := L.mono_a
  exact_mk₄ zero_comp (colim_map_comp_eq_zero _ _ (L.wab 0)) (colim_map_comp_eq_zero _ _ (L.wbδ 0))
    ((ShortComplex.exact_iff_mono _ rfl).mpr (inferInstanceAs (Mono (colim.map (L.a 0)))))
    ((L.exact_ab 0).map colim) ((L.exact_bδ 0).map colim)

omit [HasExactColimitsOfShape I AddCommGrpCat.{w}] in
/-- The initial window `0 ⟶ T₄ 0 ⟶ TM 0 ⟶ T₁ 0 ⟶ T₄ 1` is exact. -/
theorem initialM_exact : L.initialM.Exact :=
  have : Mono (L.A 0) := L.mono_A
  exact_mk₄ zero_comp (L.wAB 0) (L.wBΔ 0)
    ((ShortComplex.exact_iff_mono _ rfl).mpr (inferInstanceAs (Mono (L.A 0))))
    (L.exact_AB 0) (L.exact_BΔ 0)

/-- The comparison of the two initial windows. -/
def initialMapM : L.colimInitialM ⟶ L.initialM :=
  ComposableArrows.homMk₄ 0 (L.c₄ 0) (L.cM 0) (L.c₁ 0) (L.c₄ 1)
    ((isZero_zero AddCommGrpCat.{w}).eq_of_src _ _) (L.comm_a 0)
    (L.comm_b 0) (L.comm_δ 0)

/-- **Descent along the ladder, at the middle term.** If the comparisons at `D₄` and at `D₁` are
isomorphisms in every degree, so is the comparison at `M`. -/
theorem isIso_comparisonM (h₄ : ∀ n, IsIso (L.c₄ n)) (h₁ : ∀ n, IsIso (L.c₁ n)) :
    ∀ n, IsIso (L.cM n)
  | 0 => by
    have : Epi (ComposableArrows.app' L.initialMapM 0) :=
      ⟨fun _ _ _ => (isZero_zero AddCommGrpCat.{w}).eq_of_src _ _⟩
    have : IsIso (ComposableArrows.app' L.initialMapM 1) := h₄ 0
    have : IsIso (ComposableArrows.app' L.initialMapM 3) := h₁ 0
    have : IsIso (ComposableArrows.app' L.initialMapM 4) := h₄ 1
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono L.colimInitialM_exact L.initialM_exact
      L.initialMapM inferInstance inferInstance inferInstance inferInstance
  | m + 1 => by
    have : IsIso (ComposableArrows.app' (L.windowMapM m) 0) := h₁ m
    have : IsIso (ComposableArrows.app' (L.windowMapM m) 1) := h₄ (m + 1)
    have : IsIso (ComposableArrows.app' (L.windowMapM m) 3) := h₁ (m + 1)
    have : IsIso (ComposableArrows.app' (L.windowMapM m) 4) := h₄ (m + 2)
    exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (L.colimWindowM_exact m)
      (L.windowM_exact m) (L.windowMapM m) inferInstance inferInstance inferInstance inferInstance

end Ladder

/-- A comparison `colim D ⟶ T` built from a cocone is invertible exactly when the cocone is a
colimit cocone. -/
theorem isIso_colimitDesc_iff {D : I ⥤ AddCommGrpCat.{w}} (c : Cocone D) :
    IsIso (colimit.desc D c) ↔ Nonempty (IsColimit c) := by
  constructor
  · intro h
    exact ⟨@IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit D) h⟩
  · rintro ⟨h⟩
    have := IsColimit.hom_isIso (colimit.isColimit D) h
      ((colimit.isColimit D).descCoconeMorphism c)
    exact (Cocone.forget D).map_isIso ((colimit.isColimit D).descCoconeMorphism c)

/-- A morphism of diagrams and a morphism of vertices compatible with two cocones commute with the
comparisons from the colimits. -/
theorem colimMap_desc_comm {D D' : I ⥤ AddCommGrpCat.{w}} (a : D ⟶ D') (c : Cocone D)
    (c' : Cocone D') (f : c.pt ⟶ c'.pt) (h : ∀ j, c.ι.app j ≫ f = a.app j ≫ c'.ι.app j) :
    colim.map a ≫ colimit.desc D' c' = colimit.desc D c ≫ f := by
  refine colimit.hom_ext fun j => ?_
  rw [← colimMap_eq, ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc, h]

/-- **The comparison at a split middle term.** If `M` splits as `A` and `B` in the bicone sense
and the cocones on `A` and `B` are colimit cocones, a comparison `colim M ⟶ a.pt ⊞ b.pt`
compatible with the two projections is invertible. -/
theorem isIso_of_split {A B M : I ⥤ AddCommGrpCat.{w}} (π₁ : M ⟶ A) (π₂ : M ⟶ B) (ι₁ : A ⟶ M)
    (ι₂ : B ⟶ M) (h₁₁ : ι₁ ≫ π₁ = 𝟙 A) (h₂₂ : ι₂ ≫ π₂ = 𝟙 B) (h₁₂ : ι₁ ≫ π₂ = 0)
    (h₂₁ : ι₂ ≫ π₁ = 0) (htot : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 M) (a : Cocone A) (b : Cocone B)
    (ha : IsColimit a) (hb : IsColimit b) (f : colimit M ⟶ a.pt ⊞ b.pt)
    (hf₁ : f ≫ biprod.fst = colim.map π₁ ≫ colimit.desc A a)
    (hf₂ : f ≫ biprod.snd = colim.map π₂ ≫ colimit.desc B b) : IsIso f := by
  have : IsIso (colimit.desc A a) := (isIso_colimitDesc_iff a).mpr ⟨ha⟩
  have : IsIso (colimit.desc B b) := (isIso_colimitDesc_iff b).mpr ⟨hb⟩
  exact Stacks.Cohomology.MayerVietoris.isIso_of_additive_of_split_biprod colim π₁ π₂ ι₁ ι₂
    h₁₁ h₂₂ h₁₂ h₂₁ htot (colimit.desc A a) (colimit.desc B b) f hf₁ hf₂

/-- **Filtered colimits of abelian groups are exact**, for a filtered shape in any universes below
that of the groups. -/
theorem hasExactColimitsOfShape_of_isFiltered (J : Type u₁) [Category.{v₁} J] [IsFiltered J] :
    HasExactColimitsOfShape J AddCommGrpCat.{max u₁ v₁ w} := by
  have : IsFiltered (AsSmall.{max u₁ v₁ w} J) := IsFiltered.of_equivalence AsSmall.equiv
  exact HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{max u₁ v₁ w}
    (AsSmall.equiv.{v₁, u₁, max u₁ v₁ w}).symm

end Stacks.Cohomology.ColimitLongExact

namespace AlgebraicGeometry.Scheme.Opens

open Stacks.Cohomology.ColimitLongExact

/-- **A Mayer–Vietoris colimit system on the opens of a scheme.** For every open `W` and degree
`n`, a diagram `H W n : I ⥤ Ab` (the cohomology over `W` of the levels of an inverse system) and a
cocone `c W n` on it (the restriction maps to the cohomology over `W` of the limit); and for every
pair of opens `U`, `V` a `Stacks.Cohomology.ColimitLongExact.Ladder` (the Mayer–Vietoris sequences
of the levels and of the limit, and the comparisons) whose comparisons at the three kinds of term
are related to the cocones as stated. -/
structure MayerVietorisColimitSystem (X : Scheme.{u₁}) (I : Type u₁) [Category.{v₁} I]
    [HasColimitsOfShape I AddCommGrpCat.{w}] where
  /-- The diagrams of cohomology groups of the levels over an open. -/
  H : X.Opens → ℕ → I ⥤ AddCommGrpCat.{w}
  /-- The cocones of restriction maps to the cohomology of the limit over an open. -/
  c : ∀ W n, Cocone (H W n)
  /-- The Mayer–Vietoris ladder of a pair of opens. -/
  ladder : X.Opens → X.Opens → Ladder.{w} I
  /-- At the union, invertibility of the comparison gives the colimit property. -/
  union : ∀ U V n, IsIso ((ladder U V).c₄ n) → Nonempty (IsColimit (c (U ⊔ V) n))
  /-- At the intersection, the colimit property gives invertibility of the comparison. -/
  inter : ∀ U V n, Nonempty (IsColimit (c (U ⊓ V) n)) → IsIso ((ladder U V).c₁ n)
  /-- At the middle term, the colimit properties at `U` and `V` give invertibility. -/
  middle : ∀ U V n, Nonempty (IsColimit (c U n)) → Nonempty (IsColimit (c V n)) →
    IsIso ((ladder U V).cM n)

namespace MayerVietorisColimitSystem

variable {X : Scheme.{u₁}} {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I AddCommGrpCat.{w}]
  [HasExactColimitsOfShape I AddCommGrpCat.{w}] (S : MayerVietorisColimitSystem.{w} X I)

/-- The colimit property of the system over an open, in every degree. -/
def Holds (W : X.Opens) : Prop := ∀ n, Nonempty (IsColimit (S.c W n))

/-- **The Mayer–Vietoris step.** The colimit property passes from `U`, `V`, `U ⊓ V` to `U ⊔ V`. -/
theorem holds_sup {U V : X.Opens} (hU : S.Holds U) (hV : S.Holds V) (hUV : S.Holds (U ⊓ V)) :
    S.Holds (U ⊔ V) := fun n =>
  S.union U V n ((S.ladder U V).isIso_comparison₄ (fun m => S.middle U V m (hU m) (hV m))
    (fun m => S.inter U V m (hUV m)) n)

/-- **The Mayer–Vietoris induction, over an affine open.** If the colimit property holds over
every affine open, it holds over every quasi-compact open contained in an affine open. -/
theorem holds_of_le_affine (haff : ∀ W : X.Opens, IsAffineOpen W → S.Holds W) {V W : X.Opens}
    (hV : IsAffineOpen V) (hWV : W ≤ V) (hW : IsCompact (W : Set X)) : S.Holds W :=
  mayerVietoris_induction_of_le_affine S.Holds haff (fun _ _ => S.holds_sup) hV hWV hW

/-- **The Mayer–Vietoris induction.** On a quasi-separated scheme, if the colimit property holds
over every affine open, it holds over every quasi-compact open; in particular over `⊤` when the
scheme is moreover quasi-compact. -/
theorem holds_of_affine [QuasiSeparatedSpace X]
    (haff : ∀ W : X.Opens, IsAffineOpen W → S.Holds W) {W : X.Opens}
    (hW : IsCompact (W : Set X)) : S.Holds W :=
  mayerVietoris_induction S.Holds haff (fun _ _ => S.holds_sup) hW

/-- The quasi-compact quasi-separated case at the whole scheme. -/
theorem holds_top_of_affine [QuasiSeparatedSpace X] [CompactSpace X]
    (haff : ∀ W : X.Opens, IsAffineOpen W → S.Holds W) : S.Holds ⊤ :=
  S.holds_of_affine haff (by simpa using isCompact_univ)

end MayerVietorisColimitSystem

end AlgebraicGeometry.Scheme.Opens

end
