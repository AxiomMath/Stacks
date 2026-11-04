module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.QuotientStages
import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03K0: quasi-compact open subrelations

Composition and iterates of open subschemes of an étale equivalence relation `R` on `U`, and the
key geometric step of Stacks 03K0: a quasi-compact open of `R` is contained in a quasi-compact
open subscheme of `R` which is still an equivalence relation on `U`, when the geometric fibres
are bounded (also in the form over the fields of the site).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] ReasonableApproximation.schemeCutoff_isClosedUnderIsomorphisms
  ReasonableApproximation.schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
  ReasonableApproximation.schemeCutoff_hasTerminal
  ReasonableApproximation.schemeCutoff_hasPullbacks

namespace ReasonableApproximation

universe u₁ u₂ v₁ v₂

/-- The composition map of two opens `A, B ⊆ R`: the morphism
`pullback (A.ι ≫ s) (B.ι ≫ t) ⟶ R` obtained from the composition `c` of the relation by
restricting along `A` and `B`. -/
private noncomputable def openRelationCompMap
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R)
    (A B : R.Opens) : pullback (A.ι ≫ s) (B.ι ≫ t) ⟶ R :=
  pullback.map _ _ s t A.ι B.ι (𝟙 U) (by simp) (by simp) ≫ c

/-- The composition map of two opens of `R` is étale whenever the composition morphism `c` is. -/
private theorem etale_openRelationCompMap
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R)
    [Etale c] (A B : R.Opens) :
    Etale (openRelationCompMap s t c A B) := by
  dsimp only [openRelationCompMap]
  infer_instance

/-- A morphism `c : pullback s t ⟶ R` with `c ≫ t = pullback.fst s t ≫ t` is étale when `t` is,
since then `c ≫ t` is étale. -/
private theorem etale_of_comp_eq_pullback_fst_comp
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale t]
    (hc : c ≫ t = pullback.fst s t ≫ t) : Etale c := by
  have : Etale (c ≫ t) := by rw [hc]; infer_instance
  exact Etale.of_comp c t

/-- The range of the composition map of two quasi-compact opens of `R` is compact, the source of
the map being quasi-compact because `U` is quasi-separated. -/
private theorem isCompact_range_openRelationCompMap
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R)
    [QuasiSeparatedSpace U] (A B : R.Opens)
    (hA : IsCompact (A : Set R)) (hB : IsCompact (B : Set R)) :
    IsCompact (Set.range (openRelationCompMap s t c A B)) := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : CompactSpace (pullback (A.ι ≫ s) (B.ι ≫ t) : Scheme.{u}) := inferInstance
  exact isCompact_range (openRelationCompMap s t c A B).continuous

/-- For an étale morphism `f` and a point `g : Spec K ⟶ X` with `K` separably closed, the range of
`g` lies in the range of `f` exactly when `g` lifts through `f`. -/
private theorem range_subset_iff_exists_lift_of_etale
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {K : Type u} [Field K] [IsSepClosed K] (g : Spec (.of K) ⟶ X) :
    Set.range g ⊆ Set.range f ↔ ∃ l : Spec (.of K) ⟶ Y, l ≫ f = g := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h ⟨default, rfl⟩
    obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f g y hy
    exact ⟨l, hl⟩
  · rintro ⟨l, rfl⟩
    rintro _ ⟨x, rfl⟩
    exact ⟨l x, rfl⟩

/-- An open `A` of a scheme is contained in an open `B` as soon as every point with values in an
algebraically closed field landing in `A` also lands in `B`, it being enough to test the fields
whose spectra satisfy a predicate `Good` that holds for the algebraic closures of the residue
fields of `X`: opens are detected by geometric points. -/
private theorem opens_le_of_geometric_range_subset_of_good
    (Good : Scheme.{u} → Prop) {X : Scheme.{u}}
    (hgood : ∀ x : X, Good (Spec (.of (AlgebraicClosure (X.residueField x)))))
    (A B : X.Opens)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K], Good (Spec (.of K)) →
      ∀ g : Spec (.of K) ⟶ X, Set.range g ⊆ A → Set.range g ⊆ B) : A ≤ B := by
  intro x hx
  let K := AlgebraicClosure (X.residueField x)
  let g : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x
  have hg : ∀ y, g y = x := fun y => X.fromSpecResidueField_apply x _
  have hA : Set.range g ⊆ A := by
    rintro _ ⟨y, rfl⟩
    show g y ∈ A
    rwa [hg]
  have hxB := h K (hgood x) g hA (Set.mem_range_self default)
  change g default ∈ B at hxB
  rwa [hg] at hxB

/-- An open `A` of a scheme is contained in an open `B` as soon as every point with values in an
algebraically closed field landing in `A` also lands in `B`: opens are detected by geometric
points. -/
private theorem opens_le_of_geometric_range_subset
    {X : Scheme.{u}} (A B : X.Opens)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ X),
      Set.range g ⊆ A → Set.range g ⊆ B) : A ≤ B :=
  opens_le_of_geometric_range_subset_of_good (fun _ => True) (fun _ => trivial) A B
    fun K _ _ _ => h K

/-- The composite `c(A ×_{s, U, t} B)` of two opens `A, B ⊆ R`, as an open of `R`: the image of the
composition map, open because that map is étale. -/
private noncomputable def openRelationComp
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    (A B : R.Opens) : R.Opens := by
  let := etale_openRelationCompMap s t c A B
  exact ⟨Set.range (openRelationCompMap s t c A B),
    (openRelationCompMap s t c A B).isOpenMap.isOpen_range⟩

/-- The composite of two quasi-compact opens of `R` is quasi-compact, for `U` quasi-separated. -/
private theorem isCompact_openRelationComp
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    [QuasiSeparatedSpace U] (A B : R.Opens)
    (hA : IsCompact (A : Set R)) (hB : IsCompact (B : Set R)) :
    IsCompact (openRelationComp s t c A B : Set R) :=
  isCompact_range_openRelationCompMap s t c A B hA hB

/-- A morphism whose range lies in the image of an open immersion `f` factors through `f`. -/
private theorem exists_lift_of_range_subset {X Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [_root_.AlgebraicGeometry.IsOpenImmersion f] (g : X ⟶ Z) (h : Set.range g ⊆ Set.range f) :
    ∃ l, l ≫ f = g :=
  ⟨IsOpenImmersion.lift f g h, IsOpenImmersion.lift_fac _ _ _⟩

/-- A morphism into an open `A ⊆ R`, followed by the inclusion, has range inside `A`. -/
private theorem range_comp_ι_subset {R T : Scheme.{u}} (A : R.Opens) (g : T ⟶ A) :
    Set.range (g ≫ A.ι) ⊆ A := by
  rintro _ ⟨x, rfl⟩
  exact (g x).property

/-- Compatibility of the composition map with lifts into the pullback: a pair `(a, b)` into `A` and
`B` composes to the same morphism whether one restricts to the opens first or applies `c`
directly. -/
private theorem lift_openRelationCompMap
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R)
    (A B : R.Opens) {T : Scheme.{u}}
    (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ A.ι ≫ s = b ≫ B.ι ≫ t) :
    pullback.lift a b h ≫ openRelationCompMap s t c A B =
      pullback.lift (a ≫ A.ι) (b ≫ B.ι) (by simpa only [Category.assoc] using h) ≫ c := by
  dsimp only [openRelationCompMap]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map,
    pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- A point with values in a separably closed field lands in `openRelationComp s t c A B` exactly
when it is the composite `c` of a pair of points of `R` lying in `A` and in `B` respectively and
matching under `s` and `t`. -/
private theorem range_subset_openRelationComp_iff
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    (A B : R.Opens) {K : Type u} [Field K] [IsSepClosed K]
    (g : Spec (.of K) ⟶ R) :
    Set.range g ⊆ openRelationComp s t c A B ↔
      ∃ (a b : Spec (.of K) ⟶ R) (h : a ≫ s = b ≫ t),
        Set.range a ⊆ A ∧ Set.range b ⊆ B ∧ pullback.lift a b h ≫ c = g := by
  let m := openRelationCompMap s t c A B
  let := etale_openRelationCompMap s t c A B
  show Set.range g ⊆ Set.range m ↔ _
  rw [range_subset_iff_exists_lift_of_etale m g]
  constructor
  · rintro ⟨l, hl⟩
    let a := (l ≫ pullback.fst (A.ι ≫ s) (B.ι ≫ t)) ≫ A.ι
    let b := (l ≫ pullback.snd (A.ι ≫ s) (B.ι ≫ t)) ≫ B.ι
    have hab : a ≫ s = b ≫ t := by
      simp only [a, b, Category.assoc, pullback.condition]
    refine ⟨a, b, hab, range_comp_ι_subset A _, range_comp_ι_subset B _, ?_⟩
    · have heq : pullback.lift a b hab = l ≫
          pullback.map (A.ι ≫ s) (B.ι ≫ t) s t A.ι B.ι (𝟙 U) (by simp) (by simp) := by
        apply pullback.hom_ext <;> simp only [a, b, Category.assoc, pullback.map,
          pullback.lift_fst, pullback.lift_snd]
      rwa [heq, Category.assoc]
  · rintro ⟨a, b, hab, ha, hb, hg⟩
    obtain ⟨a', haf⟩ := exists_lift_of_range_subset A.ι a (by simpa using ha)
    obtain ⟨b', hbf⟩ := exists_lift_of_range_subset B.ι b (by simpa using hb)
    have hab' : a' ≫ A.ι ≫ s = b' ≫ B.ι ≫ t := by
      rwa [← Category.assoc, ← Category.assoc, haf, hbf]
    refine ⟨pullback.lift a' b' hab', ?_⟩
    show pullback.lift a' b' hab' ≫ openRelationCompMap s t c A B = g
    rw [lift_openRelationCompMap]
    simpa only [haf, hbf] using hg

/-- The iterates of an open `A ⊆ R` over a base open `E`: `E` at step `0` and
`openRelationComp s t c (A ^ n) A` at step `n + 1`. On geometric points `A ^ n` is the set of
pairs joined by a chain of `n` steps in `A`. -/
private noncomputable def openRelationPow
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    (E A : R.Opens) : ℕ → R.Opens
  | 0 => E
  | n + 1 => openRelationComp s t c (openRelationPow s t c E A n) A

/-- Every iterate of a quasi-compact open over a quasi-compact base open is quasi-compact. -/
private theorem isCompact_openRelationPow
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    [QuasiSeparatedSpace U] (E A : R.Opens)
    (hE : IsCompact (E : Set R)) (hA : IsCompact (A : Set R)) (n : ℕ) :
    IsCompact (openRelationPow s t c E A n : Set R) := by
  induction n with
  | zero => exact hE
  | succ n ih => exact isCompact_openRelationComp s t c _ A ih hA

/-- The composite of opens of `R` is monotone in both arguments. -/
private theorem openRelationComp_mono
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    {A B A' B' : R.Opens} (hA : A ≤ A') (hB : B ≤ B') :
    openRelationComp s t c A B ≤ openRelationComp s t c A' B' := by
  apply opens_le_of_geometric_range_subset
  intro K _ _ g hg
  obtain ⟨a, b, h, ha, hb, hab⟩ := (range_subset_openRelationComp_iff s t c A B g).mp hg
  exact (range_subset_openRelationComp_iff s t c A' B' g).mpr
    ⟨a, b, h, ha.trans hA, hb.trans hB, hab⟩

/-- The iterates of an open of `R` are monotone in the base open and in the step open. -/
private theorem openRelationPow_mono
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    {E A E' A' : R.Opens} (hE : E ≤ E') (hA : A ≤ A') (n : ℕ) :
    openRelationPow s t c E A n ≤ openRelationPow s t c E' A' n := by
  induction n with
  | zero => exact hE
  | succ n ih => exact openRelationComp_mono s t c ih hA

/-- The relation on `T`-points of `U` cut out by an open `A ⊆ R`: `a` and `b` are related when some
`r : T ⟶ R` with range inside `A` satisfies `r ≫ t = a` and `r ≫ s = b`. -/
abbrev openRelationOn
    {R U : Scheme.{u}} (s t : R ⟶ U) (A : R.Opens) (T : Scheme.{u})
    (a b : T ⟶ U) : Prop :=
  ∃ r : T ⟶ R, Set.range r ⊆ A ∧ r ≫ t = a ∧ r ≫ s = b

/-- On points with values in a separably closed field, the relation of a composite of opens is the
composite of the relations: `u` and `v` are `openRelationComp s t c A B`-related exactly when
some `w` is `A`-related to `u` and `B`-related to `v`. -/
private theorem openRelationOn_comp_iff
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    (hc_t : c ≫ t = pullback.fst s t ≫ t)
    (hc_s : c ≫ s = pullback.snd s t ≫ s)
    (A B : R.Opens) {K : Type u} [Field K] [IsSepClosed K]
    (u v : Spec (.of K) ⟶ U) :
    openRelationOn s t (openRelationComp s t c A B) (Spec (.of K)) u v ↔
      ∃ w, openRelationOn s t A (Spec (.of K)) u w ∧
        openRelationOn s t B (Spec (.of K)) w v := by
  constructor
  · rintro ⟨g, hg, hgt, hgs⟩
    obtain ⟨a, b, hab, ha, hb, hcomp⟩ :=
      (range_subset_openRelationComp_iff s t c A B g).mp hg
    refine ⟨a ≫ s, ⟨a, ha, ?_, rfl⟩, ⟨b, hb, hab.symm, ?_⟩⟩
    · rw [← hgt, ← hcomp, Category.assoc, hc_t, pullback.lift_fst_assoc]
    · rw [← hgs, ← hcomp, Category.assoc, hc_s, pullback.lift_snd_assoc]
  · rintro ⟨w, ⟨a, ha, hat, has⟩, ⟨b, hb, hbt, hbs⟩⟩
    have hab : a ≫ s = b ≫ t := has.trans hbt.symm
    refine ⟨pullback.lift a b hab ≫ c, ?_, ?_, ?_⟩
    · exact (range_subset_openRelationComp_iff s t c A B _).mpr ⟨a, b, hab, ha, hb, rfl⟩
    · rw [Category.assoc, hc_t, pullback.lift_fst_assoc, hat]
    · rw [Category.assoc, hc_s, pullback.lift_snd_assoc, hbs]

/-- When `s` and `t` are jointly monic on `T`-points, a morphism `g : T ⟶ R` has range inside `A`
exactly when `g ≫ t` and `g ≫ s` are `A`-related. -/
private theorem range_subset_iff_openRelationOn
    {R U : Scheme.{u}} (s t : R ⟶ U) (A : R.Opens) {T : Scheme.{u}}
    (hmono : ∀ a b : T ⟶ R, a ≫ t = b ≫ t → a ≫ s = b ≫ s → a = b)
    (g : T ⟶ R) :
    Set.range g ⊆ A ↔ openRelationOn s t A T (g ≫ t) (g ≫ s) := by
  constructor
  · intro h
    exact ⟨g, h, rfl, rfl⟩
  · rintro ⟨r, hr, ht, hs⟩
    exact hmono r g ht hs ▸ hr

/-- The relation cut out by the open image of the unit `e : U ⟶ R` is equality of `T`-points. -/
private theorem openRelationOn_identity_iff
    {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R) [_root_.AlgebraicGeometry.IsOpenImmersion e]
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U)
    (T : Scheme.{u}) (u v : T ⟶ U) :
    openRelationOn s t e.opensRange T u v ↔ u = v := by
  constructor
  · rintro ⟨r, hr, ht, hs⟩
    obtain ⟨l, rfl⟩ := exists_lift_of_range_subset e r hr
    rw [Category.assoc, het, Category.comp_id] at ht
    rw [Category.assoc, hes, Category.comp_id] at hs
    exact ht.symm.trans hs
  · rintro rfl
    refine ⟨u ≫ e, ?_, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨u x, rfl⟩
    · rw [Category.assoc, het, Category.comp_id]
    · rw [Category.assoc, hes, Category.comp_id]

/-- Composition in an equivalence relation: a pair `(a, b)` of morphisms with `a ≫ s = b ≫ t`
composes to a morphism `m` with `m ≫ t = a ≫ t` and `m ≫ s = b ≫ s`. -/
private theorem exists_comp_of_equivalenceRelation
    {R U P : Scheme.{u}} {s t : R ⟶ U} (E : EquivalenceRelation t s) (a b : P ⟶ R)
    (hab : a ≫ s = b ≫ t) : ∃ m : P ⟶ R, m ≫ t = a ≫ t ∧ m ≫ s = b ≫ s := by
  let l : P ⟶ E.c.pt := E.isLimit.lift (PullbackCone.mk a b hab)
  have h₁ : l ≫ E.c.fst = a := E.isLimit.fac _ WalkingCospan.left
  have h₂ : l ≫ E.c.snd = b := E.isLimit.fac _ WalkingCospan.right
  exact ⟨l ≫ E.t, by rw [Category.assoc, E.transitivity₁, ← Category.assoc, h₁],
    by rw [Category.assoc, E.transitivity₂, ← Category.assoc, h₂]⟩

/-- An étale equivalence relation has a composition morphism `c : pullback s t ⟶ R`, which is étale
and satisfies `c ≫ t = pullback.fst s t ≫ t` and `c ≫ s = pullback.snd s t ≫ s`. -/
private theorem exists_etale_composition_of_equivalenceRelation
    {R U : Scheme.{u}} (s t : R ⟶ U) [IsEquivalenceRelation t s] [Etale t] :
    ∃ c : pullback s t ⟶ R, Etale c ∧
      c ≫ t = pullback.fst s t ≫ t ∧ c ≫ s = pullback.snd s t ≫ s := by
  let e : EquivalenceRelation t s :=
    Classical.choice IsEquivalenceRelation.nonempty_equivalenceRelation
  obtain ⟨m, ht, hs⟩ := exists_comp_of_equivalenceRelation e (pullback.fst s t) (pullback.snd s t)
    pullback.condition
  exact ⟨m, etale_of_comp_eq_pullback_fst_comp s t _ ht, ht, hs⟩

/-- A chain of `n + 1` steps from `x` to `y` is the same as a chain of `n` steps from `x` to some
`z` followed by a single step from `z` to `y`. -/
private theorem exists_chain_succ_iff
    {α : Type*} (r : α → α → Prop) (n : ℕ) (x y : α) :
    (∃ a : Fin (n + 1 + 1) → α, a 0 = x ∧ a (Fin.last (n + 1)) = y ∧
      ∀ i : Fin (n + 1), r (a i.castSucc) (a i.succ)) ↔
      ∃ z, (∃ a : Fin (n + 1) → α, a 0 = x ∧ a (Fin.last n) = z ∧
        ∀ i : Fin n, r (a i.castSucc) (a i.succ)) ∧ r z y := by
  constructor
  · rintro ⟨a, hx, hy, ha⟩
    refine ⟨a (Fin.last n).castSucc, ⟨fun i => a i.castSucc, hx, rfl,
      fun i => ha i.castSucc⟩, ?_⟩
    simpa only [hy, Fin.succ_last] using ha (Fin.last n)
  · rintro ⟨z, ⟨a, hx, hz, ha⟩, hzy⟩
    refine ⟨Fin.snoc a y, ?_, by simp, ?_⟩
    · simpa using hx
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [hz] using hzy
      · simpa only [Fin.snoc_castSucc, ← Fin.castSucc_succ] using ha j

/-- **The iterates are chains.** On points with values in a separably closed field, `x` and `y` are
related by the `n`-th iterate `openRelationPow s t c e.opensRange A n` exactly when they are
joined by a chain of `n` steps in the relation cut out by `A`, the base open being the image of
the unit `e`. -/
private theorem openRelationOn_pow_iff
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    (hc_t : c ≫ t = pullback.fst s t ≫ t)
    (hc_s : c ≫ s = pullback.snd s t ≫ s)
    (e : U ⟶ R) [_root_.AlgebraicGeometry.IsOpenImmersion e]
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U)
    (A : R.Opens) {K : Type u} [Field K] [IsSepClosed K]
    (n : ℕ) (x y : Spec (.of K) ⟶ U) :
    openRelationOn s t (openRelationPow s t c e.opensRange A n) (Spec (.of K)) x y ↔
      ∃ a : Fin (n + 1) → (Spec (.of K) ⟶ U),
        a 0 = x ∧ a (Fin.last n) = y ∧
          ∀ i : Fin n, openRelationOn s t A (Spec (.of K)) (a i.castSucc) (a i.succ) := by
  induction n generalizing x y with
  | zero =>
    rw [openRelationPow, openRelationOn_identity_iff s t e hes het]
    constructor
    · rintro rfl
      exact ⟨fun _ => x, rfl, rfl, fun i => Fin.elim0 i⟩
    · rintro ⟨a, hx, hy, _⟩
      exact hx.symm.trans hy
  | succ n ih =>
    rw [openRelationPow, openRelationOn_comp_iff s t c hc_t hc_s,
      exists_chain_succ_iff]
    exact exists_congr fun z => and_congr (ih x z) Iff.rfl

/-- **The iterates stabilise at the fibre bound.** If the relation cut out by `A` on points with
values in a separably closed field is reflexive, symmetric and constant on the fibres of an
invariant `f` whose fibres have at most `N` elements, then the `N`-th iterate of `A` cuts out an
equivalence relation: a chain longer than `N` repeats a point of a fibre and can be shortened. -/
private theorem equivalence_openRelationOn_pow
    {R U : Scheme.{u}} (s t : R ⟶ U) (c : pullback s t ⟶ R) [Etale c]
    (hc_t : c ≫ t = pullback.fst s t ≫ t)
    (hc_s : c ≫ s = pullback.snd s t ≫ s)
    (e : U ⟶ R) [_root_.AlgebraicGeometry.IsOpenImmersion e]
    (hes : e ≫ s = 𝟙 U) (het : e ≫ t = 𝟙 U)
    (A : R.Opens) {K : Type u} [Field K] [IsSepClosed K]
    {β : Type*} (f : (Spec (.of K) ⟶ U) → β)
    (hA_refl : ∀ x, openRelationOn s t A (Spec (.of K)) x x)
    (hA_symm : ∀ ⦃x y⦄, openRelationOn s t A (Spec (.of K)) x y →
      openRelationOn s t A (Spec (.of K)) y x)
    (hf : ∀ ⦃x y⦄, openRelationOn s t A (Spec (.of K)) x y → f x = f y)
    [∀ x, Finite {a // f a = f x}] {N : ℕ}
    (hN : ∀ x, Nat.card {a // f a = f x} ≤ N) :
    Equivalence (openRelationOn s t (openRelationPow s t c e.opensRange A N)
      (Spec (.of K))) := by
  have h := equivalence_bounded_chains f (openRelationOn s t A (Spec (.of K)))
    hA_refl hA_symm hf hN
  have heq : openRelationOn s t (openRelationPow s t c e.opensRange A N) (Spec (.of K)) =
      (fun x y => ∃ a : Fin (N + 1) → (Spec (.of K) ⟶ U),
        a 0 = x ∧ a (Fin.last N) = y ∧
          ∀ i : Fin N, openRelationOn s t A (Spec (.of K)) (a i.castSucc) (a i.succ)) := by
    funext x y
    exact propext (openRelationOn_pow_iff s t c hc_t hc_s e hes het A N x y)
  rwa [heq]

/-- A morphism `f : T ⟶ R` has range inside an open `A` as soon as every point of `T` with values
in an algebraically closed field whose spectrum satisfies `Good` composes into `A`. -/
private theorem range_subset_open_of_geometric_of_good
    (Good : Scheme.{u} → Prop)
    (hgood : ∀ X, Good X → ∀ x : X, Good (Spec (.of (AlgebraicClosure (X.residueField x)))))
    {T R : Scheme.{u}} (hT : Good T) (f : T ⟶ R) (A : R.Opens)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K], Good (Spec (.of K)) →
      ∀ g : Spec (.of K) ⟶ T, Set.range (g ≫ f) ⊆ A) : Set.range f ⊆ A := by
  have ht : (⊤ : T.Opens) ≤ f ⁻¹ᵁ A := by
    apply opens_le_of_geometric_range_subset_of_good Good (hgood T hT)
    intro K _ _ hK g _
    rintro _ ⟨x, rfl⟩
    exact h K hK g (Set.mem_range_self x)
  rintro _ ⟨x, rfl⟩
  exact ht (Set.mem_univ x)

/-- **From geometric points back to schemes.** If an open `A ⊆ R` cuts out an equivalence relation
on the points with values in every algebraically closed field whose spectrum satisfies `Good`, then
`(A.ι ≫ t, A.ι ≫ s)` is an equivalence relation on `U`: the unit, the symmetry and the composition
of the ambient relation all have range inside `A`, so they restrict to `A`. -/
private theorem isEquivalenceRelation_restrict_of_geometric
    (Good : Scheme.{u} → Prop)
    (hgood : ∀ X, Good X → ∀ x : X, Good (Spec (.of (AlgebraicClosure (X.residueField x)))))
    {R U : Scheme.{u}} (s t : R ⟶ U) (E : EquivalenceRelation t s)
    (A : R.Opens) (hU : Good U) (hA' : Good A) (hP : Good (pullback (A.ι ≫ s) (A.ι ≫ t)))
    (hA : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Good (Spec (.of K)) → Equivalence (openRelationOn s t A (Spec (.of K)))) :
    IsEquivalenceRelation (A.ι ≫ t) (A.ι ≫ s) := by
  classical
  -- a morphism into `R` lies in `A` once its geometric points are `A`-related
  have key : ∀ {T : Scheme.{u}}, Good T → ∀ f : T ⟶ R,
      (∀ (K : Type u) [Field K] [IsAlgClosed K], Good (Spec (.of K)) →
        ∀ g : Spec (.of K) ⟶ T,
          openRelationOn s t A (Spec (.of K)) (g ≫ f ≫ t) (g ≫ f ≫ s)) →
      Set.range f ⊆ A := by
    intro T hT f h
    refine range_subset_open_of_geometric_of_good Good hgood hT f A fun K _ _ hK g => ?_
    rw [range_subset_iff_openRelationOn s t A (fun a b ha hb => E.right_cancellation a b ha hb)]
    simpa only [Category.assoc] using h K hK g
  have he : Set.range E.r ⊆ A := key hU _ fun K _ _ hK g => by
    rw [E.reflexivity₁, E.reflexivity₂, Category.comp_id]
    exact (hA K hK).refl g
  have hi : Set.range (A.ι ≫ E.s) ⊆ A := key hA' _ fun K _ _ hK g => by
    have hg : openRelationOn s t A (Spec (.of K)) (g ≫ A.ι ≫ t) (g ≫ A.ι ≫ s) :=
      ⟨g ≫ A.ι, range_comp_ι_subset A g, by simp, by simp⟩
    simpa only [Category.assoc, E.symmetry₁, E.symmetry₂] using (hA K hK).symm hg
  let a : pullback (A.ι ≫ s) (A.ι ≫ t) ⟶ R := pullback.fst _ _ ≫ A.ι
  let b : pullback (A.ι ≫ s) (A.ι ≫ t) ⟶ R := pullback.snd _ _ ≫ A.ι
  have hab : a ≫ s = b ≫ t := by
    simpa only [a, b, Category.assoc] using pullback.condition (f := A.ι ≫ s) (g := A.ι ≫ t)
  obtain ⟨m, hm₁, hm₂⟩ := exists_comp_of_equivalenceRelation E a b hab
  have hc : Set.range m ⊆ A := key hP _ fun K _ _ hK g => by
    have ha : openRelationOn s t A (Spec (.of K)) (g ≫ a ≫ t) (g ≫ a ≫ s) :=
      ⟨g ≫ a, range_comp_ι_subset A (g ≫ pullback.fst _ _), by simp, by simp⟩
    have hb : openRelationOn s t A (Spec (.of K)) (g ≫ a ≫ s) (g ≫ b ≫ s) :=
      ⟨g ≫ b, range_comp_ι_subset A (g ≫ pullback.snd _ _),
        by rw [Category.assoc, ← hab], by simp⟩
    rw [hm₁, hm₂]
    exact (hA K hK).trans ha hb
  let eA : EquivalenceRelation (A.ι ≫ t) (A.ι ≫ s) := {
    right_cancellation := fun {_} f g ht hs => (cancel_mono A.ι).mp
      (E.right_cancellation _ _ (by simpa only [Category.assoc] using ht)
        (by simpa only [Category.assoc] using hs))
    r := IsOpenImmersion.lift A.ι E.r (by simpa using he)
    reflexivity₁ := by rw [← Category.assoc, IsOpenImmersion.lift_fac, E.reflexivity₁]
    reflexivity₂ := by rw [← Category.assoc, IsOpenImmersion.lift_fac, E.reflexivity₂]
    s := IsOpenImmersion.lift A.ι (A.ι ≫ E.s) (by simpa using hi)
    symmetry₁ := by rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, E.symmetry₁]
    symmetry₂ := by rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, E.symmetry₂]
    c := pullback.cone (A.ι ≫ s) (A.ι ≫ t)
    isLimit := pullback.isLimit _ _
    t := IsOpenImmersion.lift A.ι m (by simpa using hc)
    transitivity₁ := by rw [← Category.assoc, IsOpenImmersion.lift_fac, hm₁]; rfl
    transitivity₂ := by rw [← Category.assoc, IsOpenImmersion.lift_fac, hm₂]; rfl }
  exact eA.isEquivalenceRelation

/-- A morphism out of a one-point scheme has range inside `A ⊔ B` exactly when its range lies
inside `A` or inside `B`. -/
private theorem range_subset_sup_iff_of_subsingleton
    {T R : Scheme.{u}} [Subsingleton T] [Nonempty T]
    (g : T ⟶ R) (A B : R.Opens) :
    Set.range g ⊆ A ⊔ B ↔ Set.range g ⊆ A ∨ Set.range g ⊆ B := by
  constructor
  · intro h
    obtain ⟨x⟩ := ‹Nonempty T›
    rcases h (Set.mem_range_self x) with ha | hb
    · exact Or.inl (by rintro _ ⟨y, rfl⟩; simpa only [Subsingleton.elim y x] using ha)
    · exact Or.inr (by rintro _ ⟨y, rfl⟩; simpa only [Subsingleton.elim y x] using hb)
  · exact fun h => h.elim (fun ha => ha.trans le_sup_left) (fun hb => hb.trans le_sup_right)

/-- On points of a one-point scheme, the relation cut out by `A ⊔ B` is the union of the relations
cut out by `A` and by `B`. -/
private theorem openRelationOn_sup_iff
    {R U T : Scheme.{u}} [Subsingleton T] [Nonempty T]
    (s t : R ⟶ U) (A B : R.Opens) (x y : T ⟶ U) :
    openRelationOn s t (A ⊔ B) T x y ↔
      openRelationOn s t A T x y ∨ openRelationOn s t B T x y := by
  constructor
  · rintro ⟨g, hg, ht, hs⟩
    rcases (range_subset_sup_iff_of_subsingleton g A B).mp hg with hA | hB
    · exact Or.inl ⟨g, hA, ht, hs⟩
    · exact Or.inr ⟨g, hB, ht, hs⟩
  · rintro (⟨g, hg, ht, hs⟩ | ⟨g, hg, ht, hs⟩)
    · exact ⟨g, hg.trans le_sup_left, ht, hs⟩
    · exact ⟨g, hg.trans le_sup_right, ht, hs⟩

/-- The symmetry morphism of an equivalence relation is an isomorphism, being its own inverse. -/
private theorem isIso_equivalenceRelation_symmetry
    {R U : Scheme.{u}} {s t : R ⟶ U} (E : EquivalenceRelation t s) : IsIso E.s := by
  have h : E.s ≫ E.s = 𝟙 R := E.right_cancellation _ _
    (by simp only [Category.assoc, E.symmetry₁, E.symmetry₂, Category.id_comp])
    (by simp only [Category.assoc, E.symmetry₁, E.symmetry₂, Category.id_comp])
  exact ⟨E.s, h, h⟩

/-- The open image of `A` under the symmetry of the relation cuts out the opposite relation: `x`
and `y` are related by `(A.ι ≫ E.s).opensRange` exactly when `y` and `x` are `A`-related. -/
private theorem openRelationOn_image_symmetry_iff
    {R U : Scheme.{u}} {s t : R ⟶ U} (E : EquivalenceRelation t s)
    (A : R.Opens) (T : Scheme.{u}) (x y : T ⟶ U) :
    letI := isIso_equivalenceRelation_symmetry E
    openRelationOn s t (A.ι ≫ E.s).opensRange T x y ↔ openRelationOn s t A T y x := by
  let := isIso_equivalenceRelation_symmetry E
  constructor
  · rintro ⟨g, hg, ht, hs⟩
    obtain ⟨l, rfl⟩ := exists_lift_of_range_subset (A.ι ≫ E.s) g hg
    refine ⟨l ≫ A.ι, range_comp_ι_subset A l, ?_, ?_⟩
    · rwa [Category.assoc, Category.assoc, E.symmetry₂] at hs
    · rwa [Category.assoc, Category.assoc, E.symmetry₁] at ht
  · rintro ⟨g, hg, ht, hs⟩
    obtain ⟨l, rfl⟩ := exists_lift_of_range_subset A.ι g (by simpa using hg)
    refine ⟨(l ≫ A.ι) ≫ E.s, ?_, ?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact ⟨l z, rfl⟩
    · rw [Category.assoc, E.symmetry₁, hs]
    · rw [Category.assoc, E.symmetry₂, ht]

/-- Every quasi-compact open `A ⊆ R` is contained in a quasi-compact open `A'` whose relation on
the points with values in any field is reflexive and symmetric: adjoin to `A` the open image of the
unit and the open image of `A` under the symmetry. -/
private theorem exists_compact_open_reflexive_symmetric
    {R U : Scheme.{u}} (s t : R ⟶ U) [Etale s] [CompactSpace U]
    (E : EquivalenceRelation t s) (A : R.Opens) (hA : IsCompact (A : Set R)) :
    ∃ A' : R.Opens, IsCompact (A' : Set R) ∧ A ≤ A' ∧
      ∀ (K : Type u) [Field K],
        (∀ x, openRelationOn s t A' (Spec (.of K)) x x) ∧
        (∀ ⦃x y⦄, openRelationOn s t A' (Spec (.of K)) x y →
          openRelationOn s t A' (Spec (.of K)) y x) := by
  let := isIso_equivalenceRelation_symmetry E
  let := AlgebraicGeometry.isOpenImmersion_of_section_of_etale s E.r E.reflexivity₂
  let Ai := (A.ι ≫ E.s).opensRange
  let A' := E.r.opensRange ⊔ (A ⊔ Ai)
  have hei : IsCompact (E.r.opensRange : Set R) := isCompact_range E.r.continuous
  have hAi : IsCompact (Ai : Set R) := by
    let : CompactSpace A := isCompact_iff_compactSpace.mp hA
    exact isCompact_range (A.ι ≫ E.s).continuous
  refine ⟨A', hei.union (hA.union hAi), le_sup_of_le_right le_sup_left, ?_⟩
  intro K _
  have hrel (x y : Spec (.of K) ⟶ U) :
      openRelationOn s t A' (Spec (.of K)) x y ↔
        x = y ∨ openRelationOn s t A (Spec (.of K)) x y ∨
          openRelationOn s t A (Spec (.of K)) y x := by
    rw [show A' = E.r.opensRange ⊔ (A ⊔ Ai) from rfl,
      openRelationOn_sup_iff, openRelationOn_sup_iff,
      openRelationOn_identity_iff s t E.r E.reflexivity₂ E.reflexivity₁,
      openRelationOn_image_symmetry_iff]
  refine ⟨fun x => (hrel x x).mpr (Or.inl rfl), ?_⟩
  intro x y h
  rcases (hrel x y).mp h with h | h | h
  · exact (hrel y x).mpr (Or.inl h.symm)
  · exact (hrel y x).mpr (Or.inr (Or.inr h))
  · exact (hrel y x).mpr (Or.inr (Or.inl h))

/-- **The key geometric step, for a predicate on schemes.** As
`exists_compact_open_subrelation_of_bounded_geometric_fibers`, but the bounded invariant is only
required over the algebraically closed fields whose spectra satisfy `Good`, a predicate holding
for `R`, `U`, the opens of `R` and their self-pullbacks and closed under passing to the spectra of
algebraic closures of residue fields. -/
private theorem exists_compact_open_subrelation_of_good
    (Good : Scheme.{u} → Prop)
    (hgood : ∀ X, Good X → ∀ x : X, Good (Spec (.of (AlgebraicClosure (X.residueField x)))))
    {R U : Scheme.{u}} (hR : Good R) (hU : Good U) (s t : R ⟶ U) [Etale s] [Etale t]
    [CompactSpace U] [QuasiSeparatedSpace U]
    (hopen : ∀ A : R.Opens, Good A)
    (hpb : ∀ A : R.Opens, Good (pullback (A.ι ≫ s) (A.ι ≫ t)))
    (E : EquivalenceRelation t s) (N : ℕ)
    (hN : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Good (Spec (.of K)) → ∃ (β : Type u) (f : (Spec (.of K) ⟶ U) → β),
        (∀ (r : Spec (.of K) ⟶ R), f (r ≫ t) = f (r ≫ s)) ∧
        (∀ x, Finite {a // f a = f x}) ∧
        ∀ x, Nat.card {a // f a = f x} ≤ N)
    (A : R.Opens) (hA : IsCompact (A : Set R)) :
    ∃ A' : R.Opens, IsCompact (A' : Set R) ∧ A ≤ A' ∧
      IsEquivalenceRelation (A'.ι ≫ t) (A'.ι ≫ s) := by
  classical
  let := E.isEquivalenceRelation
  let := AlgebraicGeometry.isOpenImmersion_of_section_of_etale s E.r E.reflexivity₂
  obtain ⟨c, hc, hct, hcs⟩ := exists_etale_composition_of_equivalenceRelation s t
  let := hc
  obtain ⟨A₀, hA₀, hAA₀, hrel⟩ := exists_compact_open_reflexive_symmetric s t E A hA
  let A' := openRelationPow s t c E.r.opensRange A₀ N
  have hgeom (K : Type u) [Field K] [IsAlgClosed K] (hK : Good (Spec (.of K))) :
      Equivalence (openRelationOn s t A' (Spec (.of K))) := by
    obtain ⟨β, f, hf, hfinite, hcard⟩ := hN K hK
    let := hfinite
    apply equivalence_openRelationOn_pow s t c hct hcs E.r E.reflexivity₂
      E.reflexivity₁ A₀ f (hrel K).1 (hrel K).2 _ hcard
    rintro x y ⟨r, _, rfl, rfl⟩
    exact hf r
  have hAA' : A₀ ≤ A' := by
    apply opens_le_of_geometric_range_subset_of_good Good (hgood R hR)
    intro K _ _ hK g hg
    obtain ⟨β, f, hf, hfinite, hcard⟩ := hN K hK
    let := hfinite
    have hgf : openRelationOn s t A₀ (Spec (.of K)) (g ≫ t) (g ≫ s) :=
      ⟨g, hg, rfl, rfl⟩
    have hchain := (eqvGen_iff_bounded_chain f (openRelationOn s t A₀ (Spec (.of K)))
      (hrel K).1 (hrel K).2 (by rintro x y ⟨r, _, rfl, rfl⟩; exact hf r)
        (hcard (g ≫ t))).mp (Relation.EqvGen.rel _ _ hgf)
    apply (range_subset_iff_openRelationOn s t A'
      (fun a b ha hb => E.right_cancellation a b ha hb) g).mpr
    exact (openRelationOn_pow_iff s t c hct hcs E.r E.reflexivity₂
      E.reflexivity₁ A₀ N _ _).mpr hchain
  exact ⟨A', isCompact_openRelationPow s t c E.r.opensRange A₀
    (isCompact_range E.r.continuous) hA₀ N, hAA₀.trans hAA',
    isEquivalenceRelation_restrict_of_geometric Good hgood s t E A' hU (hopen A') (hpb A') hgeom⟩
/-- **The key geometric step of Stacks 03K0.** If the relation `(s, t)` on `U` has, over every
algebraically closed field, an invariant whose fibres have at most `N` elements, then every
quasi-compact open `A ⊆ R` is contained in a quasi-compact open `A'` which is still an
equivalence relation on `U`. One first enlarges `A` to be reflexive and symmetric, then takes
the `N`-th iterate, which is an equivalence relation on geometric points by
`equivalence_openRelationOn_pow` and hence on `U`. -/
private theorem exists_compact_open_subrelation_of_bounded_geometric_fibers
    {R U : Scheme.{u}} (s t : R ⟶ U) [Etale s] [Etale t]
    [CompactSpace U] [QuasiSeparatedSpace U]
    (E : EquivalenceRelation t s) (N : ℕ)
    (hN : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      ∃ (β : Type u) (f : (Spec (.of K) ⟶ U) → β),
        (∀ (r : Spec (.of K) ⟶ R), f (r ≫ t) = f (r ≫ s)) ∧
        (∀ x, Finite {a // f a = f x}) ∧
        ∀ x, Nat.card {a // f a = f x} ≤ N)
    (A : R.Opens) (hA : IsCompact (A : Set R)) :
    ∃ A' : R.Opens, IsCompact (A' : Set R) ∧ A ≤ A' ∧
      IsEquivalenceRelation (A'.ι ≫ t) (A'.ι ≫ s) := by
  exact exists_compact_open_subrelation_of_good (fun _ => True) (fun _ _ _ => trivial) trivial
    trivial s t (fun _ => trivial) (fun _ => trivial) E N (fun K _ _ _ => hN K) A hA

/-- The canonical morphism from the spectrum of a residue field of a scheme is quasi-compact, its
source being a one-point space. -/
private theorem residueFieldMap_quasiCompact {S : Scheme.{u}} (x : S) :
    QuasiCompact (S.fromSpecResidueField x) := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro W _
  exact (Set.toFinite (S.fromSpecResidueField x ⁻¹' (W : Set S))).isCompact

/-- The spectrum of an algebraic closure of a residue field of a scheme of the site again lies in
the site: an algebraic closure has cardinality at most the maximum of `ℵ₀` and the cardinality
of the field. -/
private theorem algebraicClosureResidueFieldSpec_contained
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (x : X) :
    B.Contains (Spec (.of (AlgebraicClosure (X.residueField x)))) := by
  let := residueFieldMap_quasiCompact x
  have hκ := Scheme.size_lt_of_mono_quasiCompact (X.fromSpecResidueField x) hX
  rw [Scheme.size_Spec] at hκ
  have hcard := Algebra.IsAlgebraic.cardinalMk_le_max (X.residueField x)
    (AlgebraicClosure (X.residueField x))
  show (Spec (.of (AlgebraicClosure (X.residueField x)))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (hcard.trans_lt
    (max_lt ((le_max_right _ _).trans_lt hκ) B.aleph0_lt_cutoff))

/-- **The key geometric step, in site form.** As
`exists_compact_open_subrelation_of_bounded_geometric_fibers`, but the bounded invariant on
geometric points is only required over the algebraically closed fields whose spectra lie in the
site, which is the form in which Stacks 03JL supplies it. -/
theorem exists_compact_open_subrelation_of_bounded_geometric_fibers_in_site
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R U : Scheme.{u}}
    (hR : B.Contains R) (hU : B.Contains U) (s t : R ⟶ U) [Etale s] [Etale t]
    [CompactSpace U] [QuasiSeparatedSpace U]
    (E : EquivalenceRelation t s) (N : ℕ)
    (hN : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      B.Contains (Spec (.of K)) → ∃ (β : Type u) (f : (Spec (.of K) ⟶ U) → β),
        (∀ (r : Spec (.of K) ⟶ R), f (r ≫ t) = f (r ≫ s)) ∧
        (∀ x, Finite {a // f a = f x}) ∧
        ∀ x, Nat.card {a // f a = f x} ≤ N)
    (A : R.Opens) (hA : IsCompact (A : Set R)) :
    ∃ A' : R.Opens, IsCompact (A' : Set R) ∧ A ≤ A' ∧
      IsEquivalenceRelation (A'.ι ≫ t) (A'.ι ≫ s) := by
  have hopen : ∀ A : R.Opens, B.Contains A := fun A => (Scheme.size_coe_opens_le R A).trans_lt hR
  exact exists_compact_open_subrelation_of_good B.Contains
    (fun _ hX x => algebraicClosureResidueFieldSpec_contained B hX x) hR hU s t hopen
    (fun A => Scheme.size_pullback_lt _ _ (hopen A) (hopen A)) E N hN A hA

end ReasonableApproximation

end AlgebraicGeometry.Space

end
