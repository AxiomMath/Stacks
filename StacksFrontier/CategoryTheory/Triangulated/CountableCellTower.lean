module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects

/-!
# Objects with countably many cells are derived colimits of compact objects

Let `D` be a pre-triangulated category with direct sums and let `E : ι → D` be a countable family
of compact objects generating `D`, in the sense that the only object receiving only zero maps
from the shifts `(E i)⟦m⟧` is zero. Suppose that every group `Hom((E i)⟦m⟧, E j)` is countable.
Then every object `M` of `D` such that every `Hom((E i)⟦m⟧, M)` is countable is a derived colimit
`M = hocolim Mₙ` of a system of *compact* objects.

This is the triangulated core of [Stacks, Tag 0CRM] and of [Stacks, Tag 0CRQ]. The source proves
0CRQ by passing through an equivalence `D_QCoh(𝒪_X) ≅ D(A, d)` with the derived category of a
differential graded algebra ([Stacks, Tag 09M5]) and then applying 0CRM there. The argument for
0CRM in this repository is a cell-tower argument which never uses that its category is the
derived category of a differential graded algebra beyond the single compact generator `A` and the
countability of `Hom(A[m], A)`, so it is carried out here once, for an arbitrary countable family
of compact generators. This makes the detour through 09M5 unnecessary.

## Main definitions

* `CategoryTheory.Pretriangulated.HasCountableCells E X`: every `Hom((E i)⟦m⟧, X)` is countable.

## Main results

* `CategoryTheory.Pretriangulated.HasCountableCells.shift`, `.biprod`, `.sigma`, `.obj₃`: the
  objects with countably many cells are stable under shifts, finite direct sums and cones.
* `CategoryTheory.Pretriangulated.exists_isHomotopyColimit_isCompactObject_of_hasCountableCells`:
  an object with countably many cells is a derived colimit of compact objects.

## Implementation notes

The construction is the diagonally refined cell tower of
`StacksFrontier/Algebra/DifferentialGraded/Module/CompactCountableConverse.lean`: at the `n`-th step
the `n`-th cell of `M` is attached and the dead cells in the window `4 ^ n` of the current
enumeration of cells are killed, finitely many at a time, so that every stage stays compact; the
gluing criterion
`CategoryTheory.Pretriangulated.isHomotopyColimit_of_forall_fac_of_forall_eventually_eq_zero`
then shows that `M` is the derived colimit of the stages. The only change is where the
countability of the cells of a stage comes from: there it is read off the cohomology of a compact
module, here it is propagated along the construction, since every stage is built from the `E i`
by shifts, finite direct sums and cones (`HasCountableCells.obj₃`).

## References

* [Stacks Project, Tag 0CRM](https://stacks.math.columbia.edu/tag/0CRM)
* [Stacks Project, Tag 0CRQ](https://stacks.math.columbia.edu/tag/0CRQ)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {ι : Type*} (E : ι → D)

/-! ### Objects with countably many cells -/

/-- An object `X` **has countably many cells** with respect to a family `E` if every group
`Hom((E i)⟦m⟧, X)` is countable. -/
def HasCountableCells (X : D) : Prop :=
  ∀ (i : ι) (m : ℤ), Countable ((E i)⟦m⟧ ⟶ X)

variable {E}

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Having countably many cells is invariant under isomorphism. -/
theorem HasCountableCells.of_iso {X Y : D} (h : HasCountableCells E X) (e : X ≅ Y) :
    HasCountableCells E Y := fun i m =>
  have := h i m
  Countable.of_equiv _ (Iso.homCongr (Iso.refl _) e)

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- A shift of an object with countably many cells has countably many cells:
`Hom((E i)⟦m⟧, X⟦n⟧)` embeds into `Hom((E i)⟦m - n⟧, X)` by shifting back. -/
theorem HasCountableCells.shift {X : D} (h : HasCountableCells E X) (n : ℤ) :
    HasCountableCells E (X⟦n⟧) := fun i m => by
  have := h i (m + -n)
  let a := (shiftFunctorAdd' D m (-n) (m + -n) rfl).hom.app (E i)
  let c := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app X
  let F : ((E i)⟦m⟧ ⟶ X⟦n⟧) → ((E i)⟦m + -n⟧ ⟶ X) := fun f =>
    a ≫ (shiftFunctor D (-n)).map f ≫ c
  exact Function.Injective.countable (f := F) fun f g hfg =>
    (shiftFunctor D (-n)).map_injective ((cancel_mono c).1 ((cancel_epi a).1 hfg))

/-- A binary direct sum of objects with countably many cells has countably many cells. -/
theorem HasCountableCells.biprod {X Y : D} (hX : HasCountableCells E X)
    (hY : HasCountableCells E Y) : HasCountableCells E (X ⊞ Y) := fun i m => by
  have := hX i m
  have := hY i m
  refine Function.Injective.countable
    (f := fun f : (E i)⟦m⟧ ⟶ X ⊞ Y => (f ≫ biprod.fst, f ≫ biprod.snd)) fun f g hfg => ?_
  simp only [Prod.mk.injEq] at hfg
  exact biprod.hom_ext _ _ hfg.1 hfg.2

/-- A finite direct sum of objects with countably many cells has countably many cells: it is a
biproduct, and morphisms into a biproduct are determined by their components. -/
theorem HasCountableCells.sigma {J : Type*} [Finite J] (Z : J → D) [HasCoproduct Z]
    (hZ : ∀ j, HasCountableCells E (Z j)) : HasCountableCells E (∐ Z) := by
  refine HasCountableCells.of_iso (fun i m => ?_) (biproduct.isoCoproduct Z)
  have := fun j => hZ j i m
  exact Function.Injective.countable
    (f := fun f : (E i)⟦m⟧ ⟶ ⨁ Z => fun j => f ≫ biproduct.π Z j)
    fun f g hfg => biproduct.hom_ext _ _ fun j => congr_fun hfg j

/-- **Two out of three for countably many cells.** If in a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` the objects `X₂` and `X₁⟦1⟧` have countably many cells, so does `X₃`:
the exact sequence `Hom(A, X₂) ⟶ Hom(A, X₃) ⟶ Hom(A, X₁⟦1⟧)` exhibits `Hom(A, X₃)` as covered by
`Hom(A, X₂) × Hom(A, X₁⟦1⟧)`. -/
theorem HasCountableCells.obj₃ (T : Triangle D) (hT : T ∈ distTriang D)
    (h₂ : HasCountableCells E T.obj₂) (h₁ : HasCountableCells E (T.obj₁⟦(1 : ℤ)⟧)) :
    HasCountableCells E T.obj₃ := fun i m => by
  classical
  have := h₂ i m
  have := h₁ i m
  let A := (E i)⟦m⟧
  let sec : (A ⟶ T.obj₁⟦(1 : ℤ)⟧) → (A ⟶ T.obj₃) := fun ψ =>
    if hψ : ∃ φ : A ⟶ T.obj₃, φ ≫ T.mor₃ = ψ then hψ.choose else 0
  refine Function.Surjective.countable
    (f := fun p : (A ⟶ T.obj₂) × (A ⟶ T.obj₁⟦(1 : ℤ)⟧) => p.1 ≫ T.mor₂ + sec p.2) fun φ => ?_
  have hex : ∃ φ' : A ⟶ T.obj₃, φ' ≫ T.mor₃ = φ ≫ T.mor₃ := ⟨φ, rfl⟩
  have hsec : sec (φ ≫ T.mor₃) = hex.choose := dite_eq_left hex
  have hzero : (φ - hex.choose) ≫ T.mor₃ = 0 := by
    rw [Preadditive.sub_comp, hex.choose_spec, sub_self]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T hT _ hzero
  refine ⟨(g, φ ≫ T.mor₃), ?_⟩
  dsimp only
  rw [hsec, ← hg, sub_add_cancel]

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Each member of the family has countably many cells, given that every `Hom((E i)⟦m⟧, E j)` is
countable. -/
theorem hasCountableCells_of_countable_hom (hEE : ∀ (i j : ι) (m : ℤ), Countable ((E i)⟦m⟧ ⟶ E j))
    (j : ι) : HasCountableCells E (E j) := fun i m => hEE i j m

/-! ### Cells -/

variable (E)

/-- A **cell** of an object `X`: a member `E i` of the family, a degree `m`, and a morphism
`(E i)⟦m⟧ ⟶ X`. These are the morphisms against which the generation criterion is tested. -/
private abbrev Cell (X : D) := Σ (i : ι) (m : ℤ), ((E i)⟦m⟧ ⟶ X)

/-- A cell of `X` pushed forward along a morphism `X ⟶ Y`. -/
private def pushCell {X Y : D} (f : X ⟶ Y) (t : Cell E X) : Cell E Y :=
  ⟨t.1, t.2.1, t.2.2 ≫ f⟩

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Pushing forward twice is pushing forward along the composition. -/
private theorem pushCell_pushCell {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) (t : Cell E X) :
    pushCell E g (pushCell E f t) = pushCell E (f ≫ g) t := by
  simp [pushCell]

variable {E}

omit [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- An object with countably many cells, over a countable family, has a countable set of cells. -/
private theorem countable_cell [Countable ι] {X : D} (hX : HasCountableCells E X) :
    Countable (Cell E X) := by
  have : ∀ i, Countable (Σ m : ℤ, ((E i)⟦m⟧ ⟶ X)) := fun i =>
    have := hX i
    inferInstance
  infer_instance

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] in
/-- The cells of an object with countably many cells can be enumerated, provided the family is
nonempty (so that there is a cell at all, the zero morphism). -/
private theorem exists_surjective_cell [Countable ι] [Nonempty ι] {X : D}
    (hX : HasCountableCells E X) : ∃ e : ℕ → Cell E X, Function.Surjective e :=
  have := countable_cell hX
  have : Nonempty (Cell E X) := ⟨⟨Classical.arbitrary ι, 0, 0⟩⟩
  exists_surjective_nat _

/-! ### Attaching finitely many cells at once -/

section Attach

variable [HasCoproducts.{w} D]

/-- **Finitely many cells dying in `M` can be killed by a single cell attachment**, keeping
compactness and countability of cells. Let `X` be compact with countably many cells and
`u : X ⟶ M`, and let `ρ j : (E (i j))⟦m j⟧ ⟶ X` be a finite family of cells all of which `u`
annihilates. Then there is `f : X ⟶ X'` into a compact object with countably many cells through
which `u` factors and which kills every `ρ j`: `X'` is the cone on `∐ⱼ (E (i j))⟦m j⟧ ⟶ X`. -/
private theorem exists_comp_eq_forall_comp_eq_zero [∀ i, IsCompactObject.{w} (E i)]
    (hEE : ∀ (i j : ι) (m : ℤ), Countable ((E i)⟦m⟧ ⟶ E j))
    {M X : D} (hXc : IsCompactObject.{w} X) (hX : HasCountableCells E X) (u : X ⟶ M)
    {J : Type w} [Finite J] (i : J → ι) (m : J → ℤ) (ρ : ∀ j, (E (i j))⟦m j⟧ ⟶ X)
    (hρ : ∀ j, ρ j ≫ u = 0) :
    ∃ (X' : D) (f : X ⟶ X') (u' : X' ⟶ M),
      IsCompactObject.{w} X' ∧ HasCountableCells E X' ∧ f ≫ u' = u ∧ ∀ j, ρ j ≫ f = 0 := by
  have hZ : IsCompactObject.{w} (∐ fun j => (E (i j))⟦m j⟧) :=
    isCompactObject_sigma _ fun j => isCompactObject_shift inferInstance (m j)
  have hZc : HasCountableCells E (∐ fun j => (E (i j))⟦m j⟧) :=
    HasCountableCells.sigma _ fun j => (hasCountableCells_of_countable_hom hEE (i j)).shift (m j)
  have hcu : Limits.Sigma.desc ρ ≫ u = 0 := by
    refine Limits.Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc, hρ j, comp_zero]
  obtain ⟨X', f, g, hT⟩ := distinguished_cocone_triangle (Limits.Sigma.desc ρ)
  obtain ⟨u', hu'⟩ := Triangle.yoneda_exact₂ _ hT u hcu
  refine ⟨X', f, u', isCompactObject_obj₃ _ hT hZ hXc, HasCountableCells.obj₃ _ hT hX
    (hZc.shift 1), hu'.symm, fun j => ?_⟩
  have h0 : Limits.Sigma.desc ρ ≫ f = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [← Limits.Sigma.ι_comp_desc ρ j, Category.assoc, h0, comp_zero]

end Attach

/-! ### Stages of the tower -/

section Tower

variable [HasCoproducts.{w} D] [∀ i, IsCompactObject.{w} (E i)] [Countable ι] [Nonempty ι]
  (hEE : ∀ (i j : ι) (m : ℤ), Countable ((E i)⟦m⟧ ⟶ E j))

variable (E) in
/-- A **stage** of the approximation of `M`: a compact object with countably many cells and a
morphism to `M`, together with an enumeration of its cells. -/
private structure Stage (M : D) where
  /-- the object of the stage -/
  obj : D
  /-- the object of the stage is compact -/
  compact : IsCompactObject.{w} obj
  /-- the object of the stage has countably many cells -/
  countable : HasCountableCells E obj
  /-- the structure morphism to `M` -/
  hom : obj ⟶ M
  /-- an enumeration of the cells of the stage -/
  enum : ℕ → Cell E obj
  /-- the enumeration is onto -/
  enum_surjective : Function.Surjective enum

/-- One step of the tower out of the stage `s`, the `n`-th step, attaching the cell `t` of `M`. -/
private structure StepData {M : D} (s : Stage.{w} E M) (n : ℕ) (t : Cell E M) where
  /-- the next stage -/
  next : Stage.{w} E M
  /-- the transition morphism -/
  hom : s.obj ⟶ next.obj
  /-- the structure morphisms are compatible with the transition -/
  comm : hom ≫ next.hom = s.hom
  /-- a cell in the window which dies in `M` dies in the next stage -/
  kill : ∀ j : ℕ, j < 4 ^ n → (s.enum j).2.2 ≫ s.hom = 0 → (s.enum j).2.2 ≫ hom = 0
  /-- the new enumeration extends the pushforward of the old one along the even indices -/
  enum_two_mul : ∀ k : ℕ, next.enum (2 * k) = pushCell E hom (s.enum k)
  /-- the prescribed cell of `M` is reached from the next stage -/
  hit : ∃ r : (E t.1)⟦t.2.1⟧ ⟶ next.obj, r ≫ next.hom = t.2.2

include hEE in
/-- **A step out of any stage exists**: attach the prescribed cell of `M` by a direct sum, then
kill the finitely many dead cells of the window at once. -/
private theorem nonempty_stepData {M : D} (s : Stage.{w} E M) (n : ℕ) (t : Cell E M) :
    Nonempty (StepData s n t) := by
  set X₁ := s.obj ⊞ (E t.1)⟦t.2.1⟧
  set u₁ : X₁ ⟶ M := biprod.desc s.hom t.2.2
  have hc₁ : IsCompactObject.{w} X₁ :=
    isCompactObject_biprod s.compact (isCompactObject_shift inferInstance t.2.1)
  have hn₁ : HasCountableCells E X₁ :=
    s.countable.biprod ((hasCountableCells_of_countable_hom hEE t.1).shift t.2.1)
  have hinl : (biprod.inl : s.obj ⟶ X₁) ≫ u₁ = s.hom := biprod.inl_desc _ _
  have hinr : (biprod.inr : (E t.1)⟦t.2.1⟧ ⟶ X₁) ≫ u₁ = t.2.2 := biprod.inr_desc _ _
  set J := ULift.{w} {j : Fin (4 ^ n) // (s.enum j.1).2.2 ≫ s.hom = 0}
  obtain ⟨X₂, f₂, u₂, hc₂, hn₂, hf₂, hkill⟩ :=
    exists_comp_eq_forall_comp_eq_zero hEE hc₁ hn₁ u₁ (J := J)
      (fun j => (s.enum j.down.1.1).1) (fun j => (s.enum j.down.1.1).2.1)
      (fun j => (s.enum j.down.1.1).2.2 ≫ biprod.inl)
      (fun j => by rw [Category.assoc, hinl]; exact j.down.2)
  obtain ⟨g, hg⟩ := exists_surjective_cell hn₂
  refine ⟨{
    next :=
      { obj := X₂
        compact := hc₂
        countable := hn₂
        hom := u₂
        enum := fun j => if j % 2 = 0 then pushCell E (biprod.inl ≫ f₂) (s.enum (j / 2))
          else g (j / 2)
        enum_surjective := fun x => ?_ }
    hom := biprod.inl ≫ f₂
    comm := ?_
    kill := ?_
    enum_two_mul := ?_
    hit := ⟨biprod.inr ≫ f₂, ?_⟩ }⟩
  · obtain ⟨k, rfl⟩ := hg x
    exact ⟨2 * k + 1, by simp [Nat.mul_add_div]⟩
  · rw [Category.assoc, hf₂, hinl]
  · intro j hj hdead
    simpa using hkill (ULift.up ⟨⟨j, hj⟩, hdead⟩)
  · intro k
    simp [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  · rw [Category.assoc, hf₂, hinr]

/-- The chosen step out of a stage, attaching the `n`-th cell of the enumeration `c`. -/
private noncomputable def stepData {M : D} (c : ℕ → Cell E M) (s : Stage.{w} E M) (n : ℕ) :
    StepData s n (c n) :=
  (nonempty_stepData hEE s n (c n)).some

/-- The stages of the tower over `M` starting at `s₀`. -/
private noncomputable def tower {M : D} (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) :
    ℕ → Stage.{w} E M := fun n =>
  Nat.rec s₀ (fun k s => (stepData hEE c s k).next) n

/-- The tower over `M` starting at `s₀`, as a system indexed by `ℕ`. -/
private noncomputable def cellTower {M : D} (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) : ℕ ⥤ D :=
  Functor.ofSequence (X := fun n => (tower hEE c s₀ n).obj)
    fun n => (stepData hEE c (tower hEE c s₀ n) n).hom

variable {M : D}

/-- The structure morphism of the `n`-th term of the tower. -/
private noncomputable def towerHom (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ) :
    (cellTower hEE c s₀).obj n ⟶ M :=
  (tower hEE c s₀ n).hom

/-- The enumeration of the cells of the `n`-th term of the tower. -/
private noncomputable def towerEnum (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ) :
    ℕ → Cell E ((cellTower hEE c s₀).obj n) :=
  (tower hEE c s₀ n).enum

private theorem isCompactObject_cellTower_obj (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ) :
    IsCompactObject.{w} ((cellTower hEE c s₀).obj n) :=
  (tower hEE c s₀ n).compact

private theorem towerEnum_surjective (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ) :
    Function.Surjective (towerEnum hEE c s₀ n) :=
  (tower hEE c s₀ n).enum_surjective

private theorem cellTower_map_succ (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ) :
    (cellTower hEE c s₀).map (homOfLE (Nat.le_succ n))
      = (stepData hEE c (tower hEE c s₀ n) n).hom :=
  Functor.ofSequence_map_homOfLE_succ _ n

private theorem cellTower_map_succ_comp_towerHom (c : ℕ → Cell E M) (s₀ : Stage.{w} E M)
    (n : ℕ) :
    (cellTower hEE c s₀).map (homOfLE (Nat.le_succ n)) ≫ towerHom hEE c s₀ (n + 1)
      = towerHom hEE c s₀ n := by
  rw [cellTower_map_succ]
  exact (stepData hEE c (tower hEE c s₀ n) n).comm

private theorem towerEnum_two_mul (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n k : ℕ) :
    towerEnum hEE c s₀ (n + 1) (2 * k)
      = pushCell E ((cellTower hEE c s₀).map (homOfLE (Nat.le_succ n)))
          (towerEnum hEE c s₀ n k) := by
  rw [cellTower_map_succ]
  exact (stepData hEE c (tower hEE c s₀ n) n).enum_two_mul k

private theorem comp_cellTower_map_succ_eq_zero (c : ℕ → Cell E M) (s₀ : Stage.{w} E M)
    (n j : ℕ) (hj : j < 4 ^ n)
    (hdead : (towerEnum hEE c s₀ n j).2.2 ≫ towerHom hEE c s₀ n = 0) :
    (towerEnum hEE c s₀ n j).2.2 ≫ (cellTower hEE c s₀).map (homOfLE (Nat.le_succ n)) = 0 := by
  rw [cellTower_map_succ]
  exact (stepData hEE c (tower hEE c s₀ n) n).kill j hj hdead

private theorem exists_comp_towerHom_succ_eq (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ) :
    ∃ r : (E (c n).1)⟦(c n).2.1⟧ ⟶ (cellTower hEE c s₀).obj (n + 1),
      r ≫ towerHom hEE c s₀ (n + 1) = (c n).2.2 :=
  (stepData hEE c (tower hEE c s₀ n) n).hit

/-- The transition map `n ⟶ n + (s + 1)` factors through the stage `n + s`. -/
private theorem cellTower_map_add_succ (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n s : ℕ) :
    (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n (s + 1)))
      = (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n s)) ≫
        (cellTower hEE c s₀).map (homOfLE (Nat.le_succ (n + s))) := by
  rw [← Functor.map_comp, homOfLE_comp]

private theorem towerHom_eq_map_comp_towerHom (c : ℕ → Cell E M) (s₀ : Stage.{w} E M)
    (n s : ℕ) :
    towerHom hEE c s₀ n
      = (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n s))
        ≫ towerHom hEE c s₀ (n + s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    change towerHom hEE c s₀ n
      = (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n (s + 1)))
        ≫ towerHom hEE c s₀ (n + s + 1)
    rw [cellTower_map_add_succ, Category.assoc, cellTower_map_succ_comp_towerHom]
    exact ih

private theorem towerEnum_two_pow_mul (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n k s : ℕ) :
    towerEnum hEE c s₀ (n + s) (2 ^ s * k)
      = pushCell E ((cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n s)))
          (towerEnum hEE c s₀ n k) := by
  induction s with
  | zero => simp [pushCell]
  | succ s ih =>
    change towerEnum hEE c s₀ (n + s + 1) (2 ^ (s + 1) * k)
      = pushCell E ((cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n (s + 1))))
          (towerEnum hEE c s₀ n k)
    rw [show 2 ^ (s + 1) * k = 2 * (2 ^ s * k) by ring, towerEnum_two_mul, ih,
      pushCell_pushCell, cellTower_map_add_succ]

/-- Every cell of `M` is reached from some stage of the tower. -/
private theorem exists_comp_eq_of_surjective (c : ℕ → Cell E M) (s₀ : Stage.{w} E M)
    (hc : Function.Surjective c) (t : Cell E M) :
    ∃ (n : ℕ) (r : (E t.1)⟦t.2.1⟧ ⟶ (cellTower hEE c s₀).obj n),
      t.2.2 = r ≫ towerHom hEE c s₀ n := by
  obtain ⟨n, rfl⟩ := hc t
  obtain ⟨r, hr⟩ := exists_comp_towerHom_succ_eq hEE c s₀ n
  exact ⟨n + 1, r, hr.symm⟩

/-- A cell of a stage which dies in `M` dies at some later stage. -/
private theorem exists_comp_map_eq_zero (c : ℕ → Cell E M) (s₀ : Stage.{w} E M) (n : ℕ)
    (i : ι) (m : ℤ) (ρ : (E i)⟦m⟧ ⟶ (cellTower hEE c s₀).obj n)
    (hρ : ρ ≫ towerHom hEE c s₀ n = 0) :
    ∃ s : ℕ, ρ ≫ (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n s)) = 0 := by
  obtain ⟨k, hk⟩ := towerEnum_surjective hEE c s₀ n ⟨i, m, ρ⟩
  obtain ⟨w, hw⟩ : ∃ s : ℕ, 2 ^ s * k < 4 ^ (n + s) := by
    refine ⟨k, ?_⟩
    have h2 : 2 ^ k * k < 2 ^ k * 2 ^ k :=
      (Nat.mul_lt_mul_left (Nat.two_pow_pos _)).mpr Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ k * 2 ^ k = 4 ^ k := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, Nat.mul_pow]
    exact lt_of_lt_of_le (h3 ▸ h2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have henum : towerEnum hEE c s₀ (n + w) (2 ^ w * k)
      = ⟨i, m, ρ ≫ (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n w))⟩ := by
    rw [towerEnum_two_pow_mul, hk]
    rfl
  have hdead : (towerEnum hEE c s₀ (n + w) (2 ^ w * k)).2.2 ≫ towerHom hEE c s₀ (n + w) = 0 := by
    rw [henum]
    change (ρ ≫ (cellTower hEE c s₀).map (homOfLE (Nat.le_add_right n w)))
      ≫ towerHom hEE c s₀ (n + w) = 0
    rw [Category.assoc, ← towerHom_eq_map_comp_towerHom, hρ]
  have hk2 := comp_cellTower_map_succ_eq_zero hEE c s₀ (n + w) (2 ^ w * k) hw hdead
  rw [henum] at hk2
  refine ⟨w + 1, ?_⟩
  rwa [cellTower_map_add_succ, ← Category.assoc]

end Tower

/-! ### The main result -/

/-- **An object with countably many cells is a derived colimit of compact objects.** Let `D` be a
pre-triangulated category with direct sums indexed by `Type w`, and let `E : ι → D` be a countable
family of compact objects which generates `D`, i.e. an object receiving only zero morphisms from
the shifts of the `E i` is zero. Suppose every `Hom((E i)⟦m⟧, E j)` is countable. If every
`Hom((E i)⟦m⟧, M)` is countable, then `M = hocolim Mₙ` for a system of compact objects `Mₙ`.

This is the cell-tower argument of [Stacks, Tag 0CRM], for an arbitrary countable family of
compact generators; see the module docstring. -/
theorem exists_isHomotopyColimit_isCompactObject_of_hasCountableCells [HasCoproducts.{w} D]
    [∀ i, IsCompactObject.{w} (E i)] [Countable ι]
    (hE : (ObjectProperty.ofObj E).IsWeakTriangulatedGenerator)
    (hEE : ∀ (i j : ι) (m : ℤ), Countable ((E i)⟦m⟧ ⟶ E j))
    (M : D) (hM : HasCountableCells E M) :
    ∃ F : ℕ ⥤ D, (∀ n : ℕ, IsCompactObject.{w} (F.obj n)) ∧ IsHomotopyColimit F M := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have hz : ∀ Y : D, IsZero Y := fun Y => hE Y fun X f hX => by
      obtain ⟨X', a, _, hX'⟩ := hX
      obtain ⟨i, -⟩ := (ObjectProperty.ofObj_iff E X').1 hX'
      exact isEmptyElim i
    let Z₀ : D := ∐ fun j : PEmpty.{w + 1} => (isEmptyElim j : D)
    refine ⟨(Functor.const ℕ).obj Z₀, fun _ => isCompactObject_sigma _ fun j => isEmptyElim j, ?_⟩
    obtain ⟨Z, p, q, hT⟩ := distinguished_cocone_triangle
      (Limits.Sigma.desc fun n ↦ Limits.Sigma.ι ((Functor.const ℕ).obj Z₀).obj n -
        ((Functor.const ℕ).obj Z₀).map (homOfLE (Nat.le_succ n)) ≫
          Limits.Sigma.ι ((Functor.const ℕ).obj Z₀).obj (n + 1))
    exact ⟨0, 0, isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((hz _).iso (hz _)) ((hz _).eq_of_src _ _) ((hz _).eq_of_src _ _) ((hz _).eq_of_src _ _))⟩
  | inr hι =>
    obtain ⟨c, hc⟩ := exists_surjective_cell hM
    let Z₀ : PEmpty.{w + 1} → D := fun j => isEmptyElim j
    have hZc : HasCountableCells E (∐ Z₀) := HasCountableCells.sigma _ fun j => isEmptyElim j
    obtain ⟨e₀, he₀⟩ := exists_surjective_cell hZc
    let s₀ : Stage.{w} E M :=
      ⟨∐ Z₀, isCompactObject_sigma _ fun j => isEmptyElim j, hZc, 0, e₀, he₀⟩
    exact ⟨cellTower hEE c s₀, isCompactObject_cellTower_obj hEE c s₀,
      isHomotopyColimit_of_forall_fac_of_forall_eventually_eq_zero E hE
        (cellTower hEE c s₀) (towerHom hEE c s₀) (cellTower_map_succ_comp_towerHom hEE c s₀)
        (fun i m ψ => exists_comp_eq_of_surjective hEE c s₀ hc ⟨i, m, ψ⟩)
        (exists_comp_map_eq_zero hEE c s₀)⟩

end CategoryTheory.Pretriangulated

end
