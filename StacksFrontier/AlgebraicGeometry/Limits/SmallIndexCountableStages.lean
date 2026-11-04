module

public import Mathlib.LinearAlgebra.Countable
public import StacksFrontier.AlgebraicGeometry.Limits.CountableFlatModel
public import StacksFrontier.AlgebraicGeometry.Limits.SmallDominantIndex

/-!
# Small subsystems of a limit of schemes with countable rings of sections

Let `(D_i)` be a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms and limit `X`, indexed by a directed set `I` of arbitrary cardinality. If
the affine opens of the stages have countable rings of sections (for instance, if every stage is
of finite type over `Spec ℤ`) and the affine opens of `X` have rings of sections of cardinality
below an uncountable cardinal `κ`, then `X` is already the limit of the restriction of the system
to a directed subset `J ⊆ I` of cardinality below `κ`.

This is what puts the Noetherian approximations constructed in the proof of Stacks 07SU in the
range of the size conditions of the limit theory of algebraic spaces in this development
(`AlgebraicGeometry.Space.ChartsBounded`): the index set of an approximation can be taken smaller
than the size cutoff of the site.

## Main results

* `AlgebraicGeometry.exists_small_isColimit_whisker_of_countable`: a finite family of filtered
  colimits of countable rings over a directed set is already the colimit of its restriction to a
  directed subset of cardinality below any uncountable cardinal bounding the colimits.
* `AlgebraicGeometry.exists_small_isLimit_whisker_of_countable_over`: the same for limits of
  schemes affine over quasi-compact bases.
* `AlgebraicGeometry.exists_small_isLimit_whisker_of_countable`: the same for a finite family of
  inverse systems of quasi-compact and quasi-separated schemes with affine transition morphisms.

## Implementation notes

Unlike `AlgebraicGeometry.exists_small_isLimit_whisker_of_isSchemeTheoreticallyDominant`, the
structure maps of the stages into the limit need not be injective on sections, so the subset must
also contain, for each of its indices and each pair of sections at that index with equal image in
the limit, an index at which the two sections already agree. The subset is the union of an
increasing sequence of subsets, each obtained from the previous one by adding chosen upper bounds
of pairs and these equalizing indices; the countability of the rings at the stages keeps every
member of the sequence, and hence the union, below `κ`.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

section SmallIndex

/-- A finite option-sigma type of types of cardinality below an uncountable `κ` has cardinality
below `κ`. -/
theorem _root_.Cardinal.mk_option_sigma_lt {K : Type u} [Finite K] {X : K → Type u}
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (h : ∀ k, #(X k) < κ) : #(Option (Σ k, X k)) < κ := by
  rw [Cardinal.mk_option, Cardinal.mk_sigma]
  refine Cardinal.add_lt_of_lt hκ.le ?_ (Cardinal.one_lt_aleph0.trans hκ)
  refine (Cardinal.sum_le_mk_mul_iSup _).trans_lt
    (Cardinal.mul_lt_of_lt hκ.le ((Cardinal.lt_aleph0_of_finite K).trans hκ) ?_)
  rcases isEmpty_or_nonempty K with hK | hK
  · rw [ciSup_of_empty]
    exact zero_le.trans_lt (Cardinal.aleph0_pos.trans hκ)
  · obtain ⟨k, hk⟩ := exists_eq_ciSup_of_finite (f := fun k => #(X k))
    exact hk ▸ h k

/-- Two elements of a stage of a filtered colimit of commutative rings with equal images in the
colimit already agree at a later stage. -/
lemma exists_le_map_eq_of_isColimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {A : I ⥤ CommRingCat.{u}} {c : Cocone A} (hc : IsColimit c) {i : I}
    (a b : A.obj i) : ∃ (i' : I) (h : i ≤ i'), (c.ι.app i).hom a = (c.ι.app i).hom b →
      (A.map (homOfLE h)).hom a = (A.map (homOfLE h)).hom b := by
  by_cases ht : (c.ι.app i).hom a = (c.ι.app i).hom b
  · obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat) hc) a b).mp ht
    exact ⟨j, leOfHom f, fun _ => by rwa [Subsingleton.elim (homOfLE (leOfHom f)) f]⟩
  · exact ⟨i, le_rfl, fun h => absurd h ht⟩

/-- **Countable closure in a directed set.** A subset `S` of cardinality at most an infinite `μ`
of a directed set `I` is contained in a directed subset of cardinality at most `μ` which is closed
under a family of maps `X i → I` with countable domains. -/
lemma exists_isDirected_superset_of_countable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    {X : I → Type u} [∀ i, Countable (X i)] (f : ∀ i, X i → I) {S : Set I} {μ : Cardinal.{u}}
    (hμ : ℵ₀ ≤ μ) (hS : #S ≤ μ) :
    ∃ J : Set I, S ⊆ J ∧ #J ≤ μ ∧ IsDirected J (· ≤ ·) ∧ ∀ i ∈ J, ∀ x, f i x ∈ J := by
  classical
  choose sup hsup using fun a b : I => exists_ge_ge a b
  let step : Set I → Set I := fun T =>
    T ∪ (fun p : T × T => sup p.1.1 p.2.1) '' Set.univ ∪
      (fun p : Σ a : T, X a.1 => f p.1.1 p.2) '' Set.univ
  let T : ℕ → Set I := fun n => Nat.rec S (fun _ Tn => step Tn) n
  have hTs : ∀ n, T (n + 1) = step (T n) := fun _ => rfl
  have hT : Monotone T := monotone_nat_of_le_succ fun n => by
    rw [hTs]
    exact Set.subset_union_left.trans Set.subset_union_left
  have hTcard : ∀ n, #↥(T n) ≤ μ := by
    intro n
    induction n with
    | zero => exact hS
    | succ n ih =>
      rw [hTs]
      refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hμ ?_ ?_)
      · refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hμ ih ?_)
        refine Cardinal.mk_image_le.trans ?_
        rw [Cardinal.mk_univ, Cardinal.mk_prod, Cardinal.lift_id]
        exact Cardinal.mul_le_of_le hμ ih ih
      · refine Cardinal.mk_image_le.trans ?_
        rw [Cardinal.mk_univ, Cardinal.mk_sigma]
        refine (Cardinal.sum_le_sum _ (fun _ => ℵ₀) fun a => Cardinal.mk_le_aleph0).trans ?_
        rw [Cardinal.sum_const']
        exact Cardinal.mul_le_of_le hμ ih hμ
  refine ⟨⋃ n, T n, Set.subset_iUnion T 0, ?_, ⟨fun a b => ?_⟩, fun i hi x => ?_⟩
  · have h := Cardinal.mk_iUnion_le_lift T
    rw [Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0] at h
    exact h.trans (Cardinal.mul_le_of_le hμ hμ
      (ciSup_le fun n => (Cardinal.lift_uzero _).trans_le (hTcard n)))
  · obtain ⟨n, ha⟩ := Set.mem_iUnion.mp a.2
    obtain ⟨m, hb⟩ := Set.mem_iUnion.mp b.2
    refine ⟨⟨sup a.1 b.1, Set.mem_iUnion.mpr ⟨max n m + 1, ?_⟩⟩, (hsup a.1 b.1).1,
      (hsup a.1 b.1).2⟩
    rw [hTs]
    exact Or.inl (Or.inr ⟨(⟨a.1, hT (le_max_left n m) ha⟩, ⟨b.1, hT (le_max_right n m) hb⟩),
      Set.mem_univ _, rfl⟩)
  · obtain ⟨n, hi⟩ := Set.mem_iUnion.mp hi
    refine Set.mem_iUnion.mpr ⟨n + 1, ?_⟩
    rw [hTs]
    exact Or.inr ⟨⟨⟨i, hi⟩, x⟩, Set.mem_univ _, rfl⟩

/-- A cocone of commutative rings restricted along `e : J →o I`, with `J` directed, is a colimit
if every element of its point comes from a stage in the image of `e` and two elements of such a
stage with equal images agree at a later stage in the image of `e`. -/
lemma isColimit_whisker_of_forall_exists {I J : Type u} [Preorder I] [Preorder J] [Nonempty J]
    [IsDirected J (· ≤ ·)] {A : I ⥤ CommRingCat.{u}} (c : Cocone A) (e : J →o I)
    (hs : ∀ y : c.pt, ∃ j x, (c.ι.app (e j)).hom x = y)
    (hk : ∀ j (p q : A.obj (e j)), (c.ι.app (e j)).hom p = (c.ι.app (e j)).hom q →
      ∃ (j' : J) (h : j ≤ j'), (A.map (homOfLE (e.monotone h))).hom p =
        (A.map (homOfLE (e.monotone h))).hom q) :
    Nonempty (IsColimit (c.whisker e.monotone.functor)) := by
  have : ReflectsColimit (e.monotone.functor ⋙ A) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (forget CommRingCat) ?_⟩
  apply Types.FilteredColimit.isColimitOf'
  · intro y
    obtain ⟨j, x, hx⟩ := hs y
    exact ⟨j, x, hx.symm⟩
  · intro j p q hpq
    obtain ⟨j', h, hpq⟩ := hk j p q hpq
    exact ⟨j', homOfLE h, hpq⟩

/-- **A filtered colimit of countable rings is the colimit of a small subsystem.** A finite family
of filtered colimits of countable commutative rings over a directed set `I` is already the colimit
of its restriction to a directed subset of `I` of cardinality below an uncountable cardinal `κ`
which bounds the cardinalities of the colimits. -/
lemma exists_small_isColimit_whisker_of_countable
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {K : Type u} [Finite K] {A : K → I ⥤ CommRingCat.{u}}
    (c : ∀ k, Cocone (A k)) (hc : ∀ k, IsColimit (c k))
    (hA : ∀ k i, Countable ((A k).obj i))
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hpt : ∀ k, #(c k).pt < κ) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I), #J < κ ∧ ∀ k, Nonempty (IsColimit ((c k).whisker e.monotone.functor)) := by
  classical
  choose s x hx using fun k (y : (c k).pt) => exists_eq_ι_app_of_isColimit (c k) (hc k) y
  choose kill hkle hkeq using fun i (t : Σ k, (A k).obj i × (A k).obj i) =>
    exists_le_map_eq_of_isColimit (hc t.1) t.2.1 t.2.2
  obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
  let seed : Option (Σ k, (c k).pt) → I := fun o => o.elim i₀ (fun p => s p.1 p.2)
  let μ : Cardinal.{u} := max ℵ₀ #(Option (Σ k, (c k).pt))
  obtain ⟨J, hseed, hJcard, hdir, hkJ⟩ := exists_isDirected_superset_of_countable kill
    (le_max_left ℵ₀ _) (Cardinal.mk_range_le.trans (le_max_right _ _) : #(Set.range seed) ≤ μ)
  have hne : Nonempty J := ⟨⟨seed none, hseed ⟨none, rfl⟩⟩⟩
  refine ⟨J, inferInstance, hne, hdir, ⟨Subtype.val, fun _ _ h => h⟩,
    hJcard.trans_lt (max_lt hκ (Cardinal.mk_option_sigma_lt hκ hpt)), fun k =>
      isColimit_whisker_of_forall_exists (c k) _
        (fun y => ⟨⟨seed (some ⟨k, y⟩), hseed ⟨_, rfl⟩⟩, x k y, hx k y⟩)
        fun j p q hpq => ⟨⟨kill j.1 ⟨k, p, q⟩, hkJ j.1 j.2 _⟩, hkle j.1 ⟨k, p, q⟩,
          hkeq j.1 ⟨k, p, q⟩ hpq⟩⟩

/-- A morphism over `S` between schemes affine over `S` is affine. -/
theorem isAffineHom_left_of_isAffineHom_hom {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsAffineHom X.hom] [IsAffineHom Y.hom] : IsAffineHom f.left := by
  have : IsAffineHom (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  exact IsAffineHom.of_comp _ Y.hom

attribute [local instance] IsCofiltered.isConnected in
/-- **A limit of schemes affine over quasi-compact bases, with countable rings at the stages, is
the limit of a small subsystem.** A finite family of inverse systems of schemes affine over
quasi-compact bases, indexed by one directed set, whose affine opens at the stages have countable
rings of sections and whose limits have affine opens with rings of sections of cardinality below
an uncountable `κ`, stays a family of limits after restriction to a directed subset of cardinality
below `κ`. -/
lemma exists_small_isLimit_whisker_of_countable_over
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {M : Type} [Finite M] {S : M → Scheme.{u}} [∀ m, CompactSpace (S m)]
    (D : ∀ m, Iᵒᵖ ⥤ Over (S m)) (c : ∀ m, Cone (D m)) (hc : ∀ m, IsLimit (c m))
    [∀ m i, IsAffineHom ((D m).obj i).hom] [∀ m, IsAffineHom (c m).pt.hom]
    (hcount : ∀ m i (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ ((D m).obj i).left)
      [IsOpenImmersion f], Countable Γ(Y, ⊤))
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsize : ∀ m (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ (c m).pt.left) [IsOpenImmersion f],
      #Γ(Y, ⊤) < κ) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I), #J < κ ∧ ∀ m, Nonempty (IsLimit ((c m).whisker e.monotone.functor.op)) := by
  classical
  let U (m : M) := (S m).affineCover.finiteSubcover
  let K := Σ m, (U m).I₀
  have : Finite K := by
    have : ∀ m, Finite (U m).I₀ := fun m => inferInstance
    infer_instance
  let B (k : K) := Over.pullback ((U k.1).f k.2) ⋙ Over.forget _
  let cU (k : K) := (B k).mapCone (c k.1)
  have hU (k : K) : IsLimit (cU k) := isLimitOfPreserves (B k) (hc k.1)
  have hXaff (k : K) : IsAffine ((U k.1).X k.2) :=
    inferInstanceAs (IsAffine ((S k.1).affineCover.X _))
  let _ (k : K) (i : Iᵒᵖ) : IsAffine ((D k.1 ⋙ B k).obj i) :=
    inferInstanceAs (IsAffine (pullback ((D k.1).obj i).hom ((U k.1).f k.2)))
  let _ (k : K) : IsAffine (cU k).pt :=
    inferInstanceAs (IsAffine (pullback (c k.1).pt.hom ((U k.1).f k.2)))
  let A (k : K) := (opOpEquivalence I).inverse ⋙
    ((D k.1 ⋙ B k) ⋙ Scheme.Γ.rightOp).leftOp
  let r (k : K) : Cocone (A k) :=
    (coconeLeftOpOfCone (Scheme.Γ.rightOp.mapCone (cU k))).whisker
      (opOpEquivalence I).inverse
  have hr (k : K) : IsColimit (r k) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm
      (isColimitCoconeLeftOpOfCone _ (isLimitOfPreserves Scheme.Γ.rightOp (hU k)))
  have hA (k : K) (i : I) : Countable ((A k).obj i) :=
    hcount k.1 (op i) _ (pullback.fst ((D k.1).obj (op i)).hom ((U k.1).f k.2))
  have hpt (k : K) : #(r k).pt < κ := hsize k.1 _ (pullback.fst (c k.1).pt.hom ((U k.1).f k.2))
  obtain ⟨J, _, _, _, e, hJκ, he⟩ :=
    exists_small_isColimit_whisker_of_countable r hr hA hκ hpt
  let E := e.monotone.functor.op
  refine ⟨J, inferInstance, inferInstance, inferInstance, e, hJκ, fun m => ⟨?_⟩⟩
  let _ (i j : Jᵒᵖ) (a : i ⟶ j) : IsAffineHom (((E ⋙ D m) ⋙ Over.forget (S m)).map a) :=
    isAffineHom_left_of_isAffineHom_hom ((D m).map (E.map a))
  let _ : HasLimit ((E ⋙ D m) ⋙ Over.forget (S m)) :=
    hasLimit_of_isCofiltered_of_isAffineHom _
  let _ : HasLimit (E ⋙ D m) := hasLimit_of_created _ (Over.forget (S m))
  apply isLimit_of_isLimit_overPullback (E ⋙ D m) ((c m).whisker E) (U m)
  intro l
  apply isLimitOfReflects (Over.forget _)
  let _ : IsAffine ((Over.forget ((U m).X l)).mapCone
      ((Over.pullback ((U m).f l)).mapCone ((c m).whisker E))).pt :=
    inferInstanceAs (IsAffine (pullback (c m).pt.hom ((U m).f l)))
  let _ (j : Jᵒᵖ) :
      IsAffine ((((E ⋙ D m) ⋙ Over.pullback ((U m).f l)) ⋙ Over.forget ((U m).X l)).obj j) :=
    inferInstanceAs (IsAffine (pullback ((D m).obj (E.obj j)).hom ((U m).f l)))
  apply isLimit_of_isLimit_globalSections
  apply isLimitOfCoconeLeftOpOfCone
  exact (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence J).inverse _).toFun
    (he ⟨m, l⟩).some

attribute [local instance] IsCofiltered.isConnected in
/-- **A limit of quasi-compact quasi-separated schemes with affine transition morphisms and
countable rings at the stages is the limit of a small subsystem.** A finite family of inverse
systems of quasi-compact and quasi-separated schemes with affine transition morphisms, indexed by
one directed set, whose affine opens at the stages have countable rings of sections and whose
limits have affine opens with rings of sections of cardinality below an uncountable `κ`, stays a
family of limits after restriction to a directed subset of cardinality below `κ`. -/
lemma exists_small_isLimit_whisker_of_countable
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {M : Type} [Finite M] (D : M → Iᵒᵖ ⥤ Scheme.{u}) (c : ∀ m, Cone (D m))
    (hc : ∀ m, IsLimit (c m))
    [∀ m {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom ((D m).map f)]
    [∀ m i, CompactSpace ((D m).obj i)] [∀ m i, QuasiSeparatedSpace ((D m).obj i)]
    (hcount : ∀ m i (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ (D m).obj i)
      [IsOpenImmersion f], Countable Γ(Y, ⊤))
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsize : ∀ m (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ (c m).pt) [IsOpenImmersion f],
      #Γ(Y, ⊤) < κ) :
    ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
      (e : J →o I), #J < κ ∧ ∀ m, Nonempty (IsLimit ((c m).whisker e.monotone.functor.op)) := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty I)
  let T := Set.Ici i₀
  have : Nonempty T := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirected T (· ≤ ·) := directed_tail i₀
  let Dt (m : M) : Tᵒᵖ ⥤ Over ((D m).obj (op i₀)) := tailToOver i₀ ⋙ Over.post (D m)
  let ct (m : M) : Cone (Dt m) := ((c m).overPost (op i₀)).whisker (tailToOver i₀)
  have : (tailToOver i₀).Initial := initial_tailToOver i₀
  have hct (m : M) : IsLimit (ct m) :=
    (Functor.Initial.isLimitWhiskerEquiv (tailToOver i₀) _).symm ((hc m).overPost (op i₀))
  have : ∀ (m : M) (i : Tᵒᵖ), IsAffineHom ((Dt m).obj i).hom := fun m i =>
    inferInstanceAs (IsAffineHom ((D m).map _))
  have : ∀ m : M, IsAffineHom (ct m).pt.hom := fun m =>
    isAffineHom_π_app (D m) (c m) (hc m) (op i₀)
  obtain ⟨J, hJ, hne, hd, e, hJκ, he⟩ :=
    exists_small_isLimit_whisker_of_countable_over Dt ct hct
      (fun m i Y _ f hf => @hcount m (op (unop i).1) Y _ f hf) hκ
      hsize
  let _ := hJ
  let _ := hne
  let _ := hd
  let e' : J →o I := ⟨fun j => (e j).1, fun _ _ h => e.monotone h⟩
  exact ⟨J, inferInstance, inferInstance, inferInstance, e', hJκ, fun m =>
    ⟨(isLimitOfPreserves (Over.forget _) (he m).some).ofIsoLimit
      (Cone.ext (Iso.refl _) fun _ => (Category.id_comp _).symm)⟩⟩

end SmallIndex

section Countable

/-- **The ring of functions of an affine scheme locally of finite type over an affine scheme with
countable ring of functions is countable.** -/
theorem countable_Γ_of_locallyOfFiniteType {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (f : X ⟶ T) [LocallyOfFiniteType f] (hT : Countable Γ(T, ⊤)) : Countable Γ(X, ⊤) := by
  let : Algebra Γ(T, ⊤) Γ(X, ⊤) := (f.appLE (⊤ : T.Opens) ⊤ le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(T, ⊤) Γ(X, ⊤) := RingHom.finiteType_algebraMap.mp
    (f.finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) _)
  exact countable_of_finiteType Γ(T, ⊤) Γ(X, ⊤)

/-- The ring of functions of the terminal scheme `Spec ℤ` is countable. -/
theorem countable_Γ_terminal : Countable Γ(⊤_ Scheme.{u}, ⊤) := by
  let e : ⊤_ Scheme.{u} ≅ Spec (.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  let r : Γ(⊤_ Scheme.{u}, ⊤) ≅ CommRingCat.of (ULift.{u} ℤ) :=
    (Scheme.Γ.mapIso e.op).symm ≪≫ Scheme.ΓSpecIso _
  exact Countable.of_equiv _ (r.commRingCatIsoToRingEquiv.toEquiv.symm)

/-- **An affine open of a scheme locally of finite type over `Spec ℤ` has a countable ring of
functions.** -/
theorem countable_Γ_of_isOpenImmersion_of_locallyOfFiniteType {X Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ X) [IsOpenImmersion f] [LocallyOfFiniteType (terminal.from X)] :
    Countable Γ(Y, ⊤) := by
  have : LocallyOfFiniteType (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  exact countable_Γ_of_locallyOfFiniteType (terminal.from Y) countable_Γ_terminal

end Countable

end AlgebraicGeometry

end
