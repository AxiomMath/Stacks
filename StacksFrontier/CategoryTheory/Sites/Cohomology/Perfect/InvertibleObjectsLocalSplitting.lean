module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsIdempotentSplitting

/-!
# Gluing local splittings of the cohomology of a complex on a ringed site

Let `(C, O)` be a ringed site and `K` a complex of `O`-modules. A *local splitting* of `K` over
an object `V` is a finite family of orthogonal idempotents of `O(V)` summing to `1` which acts on
the cohomology sheaves of `K` over `V` as the degree projections — `f_n` acts on `H^k(K)` as the
identity for `k = n` and as zero otherwise — and faithfully: no nonzero section over an object of
`C/V` acts as zero on every cohomology sheaf of `K`. Faithfulness makes a local splitting unique,
so local splittings over the members of a covering glue to a locally finite complete family of
orthogonal idempotents of `Γ(C, O)` which acts on the cohomology sheaves of `K` as the degree
projections.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.LocalSplitting`: a local splitting of `K` over
  an object of the site.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.splittingSieve`: the sieve of arrows over whose
  source `K` has a local splitting.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.glueIdempotents`: the glued idempotents.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.glueIdempotents_val`: over an object carrying a
  local splitting, the glued idempotents are those of the local splitting.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.actsOnHomology_glueIdempotents`: the glued
  idempotents act on the cohomology sheaves of `K` as the degree projections.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

open Stacks.Cohomology.InvertibleDerived (ActsOnHomology)

variable {X : RingedSite.{u, u, u}}

/-- Two sections of a sheaf of `O`-modules which agree on the members of a covering sieve
agree. -/
theorem mod_eq_of_locally_eq [HasSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] (F : Mod X.O) {U : X.C} {S : Sieve U}
    (hS : S ∈ X.J U) (m m' : F.val.obj (op U))
    (h : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f → F.val.map f.op m = F.val.map f.op m') : m = m' := by
  refine sub_eq_zero.mp (Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (J := X.J) _ hS
    fun V f hf => ?_)
  rw [map_sub, h f hf, sub_self]

/-- Restricting a section of `O` along two arrows is restricting along their composite. -/
private theorem map_map_op_apply {V W Y : X.C} (g : W ⟶ V) (g' : Y ⟶ W)
    (s : (X.O.obj.obj (op V) : Type u)) :
    X.O.obj.map g'.op (X.O.obj.map g.op s) = X.O.obj.map (g' ≫ g).op s := by
  rw [op_comp, X.O.obj.map_comp, ConcreteCategory.comp_apply]

/-- Restriction of a section of `O` along the identity is trivial. -/
private theorem map_id_op_apply {V : X.C} (s : (X.O.obj.obj (op V) : Type u)) :
    X.O.obj.map (𝟙 V).op s = s := by
  rw [op_id, X.O.obj.map_id, ConcreteCategory.id_apply]

/-- A **local splitting** of the complex `K` over the object `V`: finitely many orthogonal
idempotents of `O(V)` summing to `1`, acting on the cohomology sheaves of `K` over `V` as the
degree projections, faithfully. -/
structure LocalSplitting (K : CochainComplex (Mod X.O) ℤ) (V : X.C) where
  /-- The degrees which occur over `V`. -/
  T : Finset ℤ
  /-- The idempotents. -/
  f : ℤ → (X.O.obj.obj (op V) : Type u)
  /-- Each `f n` is idempotent. -/
  idem : ∀ n, IsIdempotentElem (f n)
  /-- The idempotents are pairwise orthogonal. -/
  ortho : ∀ n m, n ≠ m → f n * f m = 0
  /-- `f n` vanishes for `n ∉ T`. -/
  eq_zero : ∀ n ∉ T, f n = 0
  /-- The idempotents sum to `1`. -/
  sum_eq_one : ∑ n ∈ T, f n = 1
  /-- `f n` acts on `H^k(K)` over `V` as `1` for `k = n` and as `0` otherwise. -/
  smul : ∀ (n k : ℤ) ⦃W : X.C⦄ (g : W ⟶ V) (m : (K.homology k).val.obj (op W)),
    ringSec (X.O.obj.map g.op (f n)) • m = if k = n then m else 0
  /-- No nonzero section over an object of `C/V` acts as zero on every cohomology sheaf of
  `K`. -/
  faithful : ∀ ⦃W : X.C⦄ (_ : W ⟶ V) (t : (X.O.obj.obj (op W) : Type u)),
    (∀ (k : ℤ) ⦃W' : X.C⦄ (g' : W' ⟶ W) (m : (K.homology k).val.obj (op W')),
      ringSec (X.O.obj.map g'.op t) • m = 0) → t = 0

namespace LocalSplitting

variable {K : CochainComplex (Mod X.O) ℤ}

/-- A local splitting restricts along an arrow of the site. -/
def map {V : X.C} (A : LocalSplitting K V) {W : X.C} (g : W ⟶ V) : LocalSplitting K W where
  T := A.T
  f n := X.O.obj.map g.op (A.f n)
  idem n := (A.idem n).map _
  ortho n m h := by rw [← map_mul, A.ortho n m h, map_zero]
  eq_zero n h := by rw [A.eq_zero n h, map_zero]
  sum_eq_one := by rw [← map_sum, A.sum_eq_one, map_one]
  smul n k W' g' m := by
    rw [← ConcreteCategory.comp_apply, ← X.O.obj.map_comp, ← op_comp]
    exact A.smul n k (g' ≫ g) m
  faithful W' g' t ht := A.faithful (g' ≫ g) t ht

/-- **Two local splittings agree on every common refinement**: their idempotents have the same
restrictions to any object mapping to both. -/
theorem map_f_eq {V₁ V₂ W : X.C} (A : LocalSplitting K V₁) (B : LocalSplitting K V₂)
    (g₁ : W ⟶ V₁) (g₂ : W ⟶ V₂) (n : ℤ) :
    X.O.obj.map g₁.op (A.f n) = X.O.obj.map g₂.op (B.f n) := by
  refine sub_eq_zero.mp (A.faithful g₁ _ fun k W' g' m => ?_)
  have h1 := A.smul n k (g' ≫ g₁) m
  have h2 := B.smul n k (g' ≫ g₂) m
  rw [← map_map_op_apply] at h1 h2
  rw [map_sub]
  exact (sub_smul (ringSec (X.O.obj.map g'.op (X.O.obj.map g₁.op (A.f n))))
    (ringSec (X.O.obj.map g'.op (X.O.obj.map g₂.op (B.f n)))) m).trans
    (sub_eq_zero.mpr (h1.trans h2.symm))

end LocalSplitting

/-- The sieve of arrows over whose source the complex `K` has a local splitting. -/
def splittingSieve (K : CochainComplex (Mod X.O) ℤ) (U : X.C) : Sieve U where
  arrows V _ := Nonempty (LocalSplitting K V)
  downward_closed := fun ⟨A⟩ g => ⟨A.map g⟩

section Glue

variable {K : CochainComplex (Mod X.O) ℤ} (hK : ∀ U : X.C, splittingSieve K U ∈ X.J U)

include hK in
/-- If `K` has a local splitting over the members of a covering sieve of every object, then for
each `n` and `U` there is a section of `O` over `U` restricting to the degree-`n` idempotent of
every local splitting over an object of `C/U`. -/
theorem exists_glueSection (n : ℤ) (U : X.C) :
    ∃ s : (X.O.obj.obj (op U) : Type u), ∀ ⦃V : X.C⦄ (f : V ⟶ U) (A : LocalSplitting K V),
      X.O.obj.map f.op s = A.f n := by
  obtain ⟨s, hs⟩ := exists_glue (hK U) (fun V f hf => (Classical.choice hf).f n)
    (fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ _ => LocalSplitting.map_f_eq _ _ g₁ g₂ n)
  refine ⟨s, fun V f A => ?_⟩
  refine eq_of_locally_eq (hK V) _ _ fun W g ⟨B⟩ => ?_
  rw [map_map_op_apply, hs (g ≫ f) ((splittingSieve K U).downward_closed ⟨A⟩ g)]
  have := LocalSplitting.map_f_eq (Classical.choice
    ((splittingSieve K U).downward_closed ⟨A⟩ g : (splittingSieve K U).arrows (g ≫ f))) A
    (𝟙 W) g n
  rwa [map_id_op_apply] at this

/-- The glued idempotent of degree `n`, as a global section of `O`. -/
def glueSection (n : ℤ) : GlobalSection X where
  val U := (exists_glueSection hK n U.unop).choose
  map_val U V g := by
    induction U with | op U => ?_
    induction V with | op V => ?_
    refine eq_of_locally_eq (hK V) _ _ fun W h ⟨B⟩ => ?_
    rw [← ConcreteCategory.comp_apply, ← X.O.obj.map_comp]
    change X.O.obj.map (h ≫ g.unop).op (exists_glueSection hK n U).choose =
      X.O.obj.map h.op (exists_glueSection hK n V).choose
    rw [(exists_glueSection hK n U).choose_spec (h ≫ g.unop) B,
      (exists_glueSection hK n V).choose_spec h B]

/-- Over an object carrying a local splitting, the glued idempotents are those of the local
splitting. -/
theorem glueSection_val (n : ℤ) {V : X.C} (A : LocalSplitting K V) :
    (glueSection hK n).val (op V) = A.f n := by
  have := (exists_glueSection hK n V).choose_spec (𝟙 V) A
  rwa [map_id_op_apply] at this

/-- **The glued idempotents**: the locally finite complete family of orthogonal idempotents of
`Γ(C, O)` whose restriction to every object carrying a local splitting of `K` is that splitting. -/
def glueIdempotents : LocallyFiniteIdempotents X where
  e := glueSection hK
  idem n U := by
    induction U with | op U => ?_
    refine eq_of_locally_eq (hK U) _ _ fun V f ⟨A⟩ => ?_
    rw [map_mul, (glueSection hK n).map_val, glueSection_val hK n A]
    exact (A.idem n).eq
  ortho n m h U := by
    induction U with | op U => ?_
    refine eq_of_locally_eq (hK U) _ _ fun V f ⟨A⟩ => ?_
    rw [map_mul, (glueSection hK n).map_val, (glueSection hK m).map_val,
      glueSection_val hK n A, glueSection_val hK m A, map_zero]
    exact A.ortho n m h
  locallyFinite U := ⟨splittingSieve K U, hK U, fun V f ⟨A⟩ => ⟨A.T,
    fun n hn => (glueSection_val hK n A).trans (A.eq_zero n hn),
    (Finset.sum_congr rfl fun n _ => glueSection_val hK n A).trans A.sum_eq_one⟩⟩

/-- Over an object carrying a local splitting, the glued idempotents are those of the local
splitting. -/
theorem glueIdempotents_val (n : ℤ) {V : X.C} (A : LocalSplitting K V) :
    ((glueIdempotents hK).e n).val (op V) = A.f n :=
  glueSection_val hK n A

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The glued idempotents act on the cohomology sheaves of `K` as the degree projections.** -/
theorem actsOnHomology_glueIdempotents :
    ActsOnHomology (fun n => smulNatTrans ((glueIdempotents hK).e n)) K := by
  intro n k
  rw [smulNatTrans_app]
  have key : ∀ (U : X.C) (m : (K.homology k).val.obj (op U)) ⦃V : X.C⦄ (f : V ⟶ U)
      (A : LocalSplitting K V),
      (K.homology k).val.map f.op ((smulHom ((glueIdempotents hK).e n) (K.homology k)).val.app
        (op U) m) = if k = n then (K.homology k).val.map f.op m else 0 := by
    intro U m V f A
    rw [smulHom_app, (K.homology k).val.map_smul]
    change ringSec (X.O.obj.map f.op (((glueIdempotents hK).e n).val (op U))) • _ = _
    rw [((glueIdempotents hK).e n).map_val, glueIdempotents_val hK n A]
    have := A.smul n k (𝟙 V) ((K.homology k).val.map f.op m)
    rwa [map_id_op_apply] at this
  split_ifs with hkn <;> (ext U m; induction U with | op U => ?_)
  all_goals refine mod_eq_of_locally_eq _ (hK U) _ _ fun V f ⟨A⟩ => (key U m f A).trans ?_
  · rw [ite_eq_left hkn]
    rfl
  · exact (ite_eq_right hkn).trans (map_zero _).symm

end Glue

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
