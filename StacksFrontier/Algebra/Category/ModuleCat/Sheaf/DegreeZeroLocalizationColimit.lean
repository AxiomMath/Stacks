module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree

/-!
# The degree-zero localization of a graded module is a sequential colimit

Let `A = ⨁_{n ≥ 0} A n` be a graded ring, let `M = ⨁_{i ∈ ℤ} B i` be a graded `A`-module and let
`f ∈ A d` be homogeneous. The degree-zero part `M₍f₎` of the localization `M_f`, that is
`GradedModuleDegreeZeroLocalization A B f`, consists of the fractions `x / f ^ n` with `x`
homogeneous of degree `n * d`. Multiplying numerator and denominator by `f` identifies the
fraction `x / f ^ n` with `f • x / f ^ (n + 1)`, so the homogeneous pieces

`B 0 → B d → B (2 * d) → ⋯`

form an `ℕ`-indexed system under multiplication by `f`, and its colimit is `M₍f₎`. This file builds
that system and proves the comparison.

## Main definitions

* `Stacks.SheafOfModules.homogeneousSmulHom`: multiplication by `f`, as a map from the numerators
  of degree `n * d` to those of degree `(n + 1) * d`.
* `Stacks.SheafOfModules.homogeneousSequence`: **the `ℕ`-indexed system** `ℕ ⥤ AddCommGrpCat` of
  homogeneous pieces `B (n * d)` with multiplication by `f` as its transition maps.
* `Stacks.SheafOfModules.fractionHom`: the `n`-th leg `x ↦ x / f ^ n`.
* `Stacks.SheafOfModules.degreeZeroCocone`: the resulting cocone with vertex `M₍f₎`.

## Main results

* `Stacks.SheafOfModules.isColimitDegreeZeroCocone`: **the degree-zero localization is the colimit
  of the system of homogeneous pieces.**
* `Stacks.SheafOfModules.colimitHomogeneousSequenceIso`: the same comparison read as an
  isomorphism `colim_n B (n * d) ≅ M₍f₎`.

## Implementation notes

**Why the argument is finite.** Surjectivity of the comparison is the fraction normal form
`Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree`: every element of `M₍f₎`
is a *single* fraction `x / f ^ n`, not a sum of fractions, so every element of the vertex is in
the image of one leg. That is what makes the uniqueness half of the universal property a finite
computation. The factorization in the other direction is
`Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree`, which descends a family of additive
maps compatible with multiplying numerator and denominator by `f`. A cocone supplies that family
only on the homogeneous pieces, while the lift wants it on all of `M`; the decomposition of `M`
closes the gap, each leg being precomposed with the projection
`Stacks.SheafOfModules.decomposeComponent` onto its degree. The compatibility the lift demands is
stated for the exponent jumping by an arbitrary `k`, and is obtained from the cocone relation,
which only jumps by one, by induction on `k`.

**Why `AddCommGrpCat` and not `ModuleCat`.** The homogeneous pieces `B i` are additive subgroups of
`M`, not submodules: nothing makes them modules over a ring that also acts on `M₍f₎`, whose scalars
are `HomogeneousLocalization.Away A f`. Accordingly `degreeZeroLocalizationLiftOfDegree` produces
an additive map, and the colimit here is a colimit of abelian groups. The ring and the module are
taken in the same universe, so that the pieces and the localization are objects of the same
`AddCommGrpCat`; the index types `σ` and `τ` of the two gradings are unconstrained.

**The degree of `f` is arbitrary.** The system is indexed by the *exponent* of the denominator, so
its `n`-th term is the piece of degree `n * d`. At `d = 1`, the case [Stacks, Tag 01PW] states its
graded section module in, the `n`-th term is `B (n * 1)`, which is `B n` after `Nat.mul_one`.

**Relation to the graded ring.** `HomogeneousLocalization.Away.directLimitEquiv` is the
counterpart for the graded ring `A` itself, phrased with `Module.DirectLimit` rather than with a
cocone.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory CategoryTheory.Limits DirectSum

universe u w t

attribute [local instance] instVAddNatIntDegreeZeroArbitraryDegree

variable {R M : Type u} {σ : Type w} {τ : Type t}
  [CommRing R] [AddCommGroup M] [Module R M]
  [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
  [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
  [SetLike.GradedSMul A B] {f : R} {d : ℕ}

/-! ### The `ℕ`-indexed system of homogeneous pieces -/

/-- **Multiplication by the homogeneous element `f` of degree `d`**, from the numerators of degree
`n * d` to those of degree `(n + 1) * d`. -/
public def homogeneousSmulHom (hf : f ∈ A d) (n : ℕ) :
    B ((n * d : ℕ) : ℤ) →+ B (((n + 1) * d : ℕ) : ℤ) where
  toFun x := ⟨f • (x : M), by
    simpa using pow_smul_mem_degree A B hf (n := n) (k := 1) rfl x.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [smul_add])

omit [Decomposition B] in
/-- The underlying element of `homogeneousSmulHom A B hf n x` is `f • x`. -/
@[simp]
public theorem coe_homogeneousSmulHom (hf : f ∈ A d) (n : ℕ) (x : B ((n * d : ℕ) : ℤ)) :
    (homogeneousSmulHom A B hf n x : M) = f • (x : M) := rfl

/-- **The `ℕ`-indexed system of homogeneous pieces of a graded module**, indexed by the exponent of
the denominator: its `n`-th term is the piece `B (n * d)` of numerators over `f ^ n`, and its
transition maps are multiplication by `f`. -/
public def homogeneousSequence (hf : f ∈ A d) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence (X := fun n => AddCommGrpCat.of (B ((n * d : ℕ) : ℤ)))
    fun n => AddCommGrpCat.ofHom (homogeneousSmulHom A B hf n)

omit [Decomposition B] in
/-- The `n`-th term of `homogeneousSequence A B hf` is the homogeneous piece `B (n * d)`. -/
@[simp]
public theorem homogeneousSequence_obj (hf : f ∈ A d) (n : ℕ) :
    (homogeneousSequence A B hf).obj n = AddCommGrpCat.of (B ((n * d : ℕ) : ℤ)) := rfl

omit [Decomposition B] in
/-- The transition map of `homogeneousSequence A B hf` from `n` to `n + 1` is
`homogeneousSmulHom A B hf n`. -/
@[simp]
public theorem homogeneousSequence_map_succ (hf : f ∈ A d) (n : ℕ) :
    (homogeneousSequence A B hf).map (homOfLE (Nat.le_add_right n 1)) =
      AddCommGrpCat.ofHom (homogeneousSmulHom A B hf n) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-! ### The cocone with vertex the degree-zero localization -/

/-- **The fraction `x / f ^ n` of a numerator `x` of degree `n * d`**, as an element of the
degree-zero localization. -/
public def fractionHom (hf : f ∈ A d) (n : ℕ) :
    B ((n * d : ℕ) : ℤ) →+ GradedModuleDegreeZeroLocalization A B f where
  toFun x := ⟨LocalizedModule.mk (S := Submonoid.powers f) (x : M)
      ⟨f ^ n, by exact ⟨n, rfl⟩⟩,
    mk_mem_degreeZeroLocalization_of_degree A B hf n _ x.2⟩
  map_zero' := Subtype.ext (by
    change LocalizedModule.mk (S := Submonoid.powers f) ((0 : B ((n * d : ℕ) : ℤ)) : M)
        ⟨f ^ n, by exact ⟨n, rfl⟩⟩ = 0
    simp)
  map_add' x y := Subtype.ext (by
    change LocalizedModule.mk (S := Submonoid.powers f) ((x : M) + (y : M))
        ⟨f ^ n, by exact ⟨n, rfl⟩⟩ =
      LocalizedModule.mk (S := Submonoid.powers f) (x : M) ⟨f ^ n, by exact ⟨n, rfl⟩⟩ +
        LocalizedModule.mk (S := Submonoid.powers f) (y : M) ⟨f ^ n, by exact ⟨n, rfl⟩⟩
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [smul_add, Submonoid.smul_def, mul_smul]⟩)

/-- The image of `fractionHom A B hf n x` in `LocalizedModule.Away f M` is the fraction
`x / f ^ n`. -/
@[simp]
public theorem coe_fractionHom (hf : f ∈ A d) (n : ℕ) (x : B ((n * d : ℕ) : ℤ)) :
    (fractionHom A B hf n x : LocalizedModule.Away f M) =
      LocalizedModule.mk (S := Submonoid.powers f) (x : M) ⟨f ^ n, by exact ⟨n, rfl⟩⟩ := rfl

/-- Multiplying numerator and denominator by `f` does not change the fraction:
`(f • x) / f ^ (n + 1) = x / f ^ n`. -/
public theorem fractionHom_homogeneousSmulHom (hf : f ∈ A d) (n : ℕ)
    (x : B ((n * d : ℕ) : ℤ)) :
    fractionHom A B hf (n + 1) (homogeneousSmulHom A B hf n x) = fractionHom A B hf n x := by
  apply Subtype.ext
  show LocalizedModule.mk (S := Submonoid.powers f) (f • (x : M))
      ⟨f ^ (n + 1), by exact ⟨n + 1, rfl⟩⟩ =
    LocalizedModule.mk (S := Submonoid.powers f) (x : M) ⟨f ^ n, by exact ⟨n, rfl⟩⟩
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, smul_smul, pow_succ]⟩

/-- **The cocone over the system of homogeneous pieces whose vertex is the degree-zero
localization**, the `n`-th leg sending a numerator `x` of degree `n * d` to the fraction
`x / f ^ n`. -/
public def degreeZeroCocone (hf : f ∈ A d) : Cocone (homogeneousSequence A B hf) where
  pt := AddCommGrpCat.of (GradedModuleDegreeZeroLocalization A B f)
  ι := NatTrans.ofSequence (fun n => AddCommGrpCat.ofHom (fractionHom A B hf n)) fun n => by
    rw [homogeneousSequence_map_succ]
    simp only [Functor.const_obj_map]
    ext x
    change fractionHom A B hf (n + 1) (homogeneousSmulHom A B hf n x) = fractionHom A B hf n x
    exact fractionHom_homogeneousSmulHom A B hf n x

/-- The vertex of `degreeZeroCocone A B hf` is the degree-zero localization `M₍f₎`. -/
@[simp]
public theorem degreeZeroCocone_pt (hf : f ∈ A d) :
    (degreeZeroCocone A B hf).pt =
      AddCommGrpCat.of (GradedModuleDegreeZeroLocalization A B f) := rfl

/-- The `n`-th leg of `degreeZeroCocone A B hf` is `fractionHom A B hf n`. -/
@[simp]
public theorem degreeZeroCocone_ι_app (hf : f ∈ A d) (n : ℕ) :
    (degreeZeroCocone A B hf).ι.app n = AddCommGrpCat.ofHom (fractionHom A B hf n) := rfl

/-! ### The comparison -/

/-- The projection of a graded module onto one homogeneous piece, as an additive map. -/
public def decomposeComponent (m : ℤ) : M →+ B m where
  toFun x := decompose B x m
  map_zero' := by simp
  map_add' x y := by simp

private theorem decomposeComponent_of_mem {m : ℤ} {x : M} (hx : x ∈ B m) :
    decomposeComponent B m x = ⟨x, hx⟩ :=
  Subtype.ext (decompose_of_mem_same B hx)

section Descent

variable (hf : f ∈ A d) (s : Cocone (homogeneousSequence A B hf))

/-- The `n`-th leg of a cocone, extended to all of `M` by projecting onto the degree `n * d` piece
first. -/
public def coconeFamily (n : ℕ) : M →+ s.pt :=
  (AddCommGrpCat.Hom.hom (s.ι.app n)).comp (decomposeComponent B ((n * d : ℕ) : ℤ))

private theorem coconeFamily_of_mem (n : ℕ) {x : M} (hx : x ∈ B ((n * d : ℕ) : ℤ)) :
    coconeFamily A B hf s n x = AddCommGrpCat.Hom.hom (s.ι.app n) ⟨x, hx⟩ := by
  show AddCommGrpCat.Hom.hom (s.ι.app n) (decomposeComponent B ((n * d : ℕ) : ℤ) x) = _
  rw [decomposeComponent_of_mem B hx]

omit [Decomposition B] in
/-- The `(n + 1)`-th leg of `s` takes the value of the `n`-th leg at `x` on
`homogeneousSmulHom A B hf n x`. -/
private theorem cocone_ι_app_homogeneousSmulHom (n : ℕ) (x : B ((n * d : ℕ) : ℤ)) :
    AddCommGrpCat.Hom.hom (s.ι.app (n + 1)) (homogeneousSmulHom A B hf n x) =
      AddCommGrpCat.Hom.hom (s.ι.app n) x := by
  have hw := s.w (homOfLE (Nat.le_add_right n 1))
  rw [homogeneousSequence_map_succ] at hw
  exact ConcreteCategory.congr_hom hw x

/-- The cocone relation, read on numerators: multiplying by `f` and moving one step along the
system does not change the value. -/
private theorem coconeFamily_smul (n : ℕ) {x : M} (hx : x ∈ B ((n * d : ℕ) : ℤ)) :
    coconeFamily A B hf s (n + 1) (f • x) = coconeFamily A B hf s n x := by
  have hfx : f • x ∈ B (((n + 1) * d : ℕ) : ℤ) := (homogeneousSmulHom A B hf n ⟨x, hx⟩).2
  rw [coconeFamily_of_mem A B hf s (n + 1) hfx, coconeFamily_of_mem A B hf s n hx]
  exact cocone_ι_app_homogeneousSmulHom A B hf s n ⟨x, hx⟩

/-- For `x` of degree `n * d`, the value of the `(n + k)`-th extended leg at `f ^ k • x` equals
the value of the `n`-th extended leg at `x`. -/
public theorem coconeFamily_pow_smul (n k : ℕ) {x : M} (hx : x ∈ B ((n * d : ℕ) : ℤ)) :
    coconeFamily A B hf s (n + k) (f ^ k • x) = coconeFamily A B hf s n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : f ^ k • x ∈ B (((n + k) * d : ℕ) : ℤ) := pow_smul_mem_degree A B hf rfl hx
    have hstep : coconeFamily A B hf s (n + (k + 1)) (f ^ (k + 1) • x) =
        coconeFamily A B hf s (n + k) (f ^ k • x) := by
      have hpow : f ^ (k + 1) • x = f • (f ^ k • x) := by rw [smul_smul, ← pow_succ']
      rw [hpow]
      exact coconeFamily_smul A B hf s (n + k) hy
    exact hstep.trans ih

/-- **The map out of the degree-zero localization determined by a cocone**, sending `x / f ^ n`
to the value of the `n`-th leg at `x`. -/
public def descHom : GradedModuleDegreeZeroLocalization A B f →+ s.pt :=
  degreeZeroLocalizationLiftOfDegree A B hf (coconeFamily A B hf s)
    fun n k _ hx => coconeFamily_pow_smul A B hf s n k hx

/-- The map `descHom A B hf s` sends the fraction `x / f ^ n` to the value of the `n`-th leg of
`s` at `x`. -/
public theorem descHom_fractionHom (n : ℕ) (x : B ((n * d : ℕ) : ℤ)) :
    descHom A B hf s (fractionHom A B hf n x) = AddCommGrpCat.Hom.hom (s.ι.app n) x := by
  show degreeZeroLocalizationLiftOfDegree A B hf (coconeFamily A B hf s)
      (fun n k x hx => coconeFamily_pow_smul A B hf s n k hx)
      (fractionHom A B hf n x) = _
  rw [degreeZeroLocalizationLiftOfDegree_fraction A B hf _ _ _ n (x : M) x.2 rfl,
    coconeFamily_of_mem A B hf s n x.2]

end Descent

/-- **The degree-zero localization of a graded module is the colimit of the system of its
homogeneous pieces** under multiplication by the homogeneous element `f`. -/
public def isColimitDegreeZeroCocone (hf : f ∈ A d) : IsColimit (degreeZeroCocone A B hf) where
  desc s := AddCommGrpCat.ofHom (descHom A B hf s)
  fac s n := AddCommGrpCat.ext fun x => by
    change descHom A B hf s (fractionHom A B hf n x) = AddCommGrpCat.Hom.hom (s.ι.app n) x
    exact descHom_fractionHom A B hf s n x
  uniq s m hm := AddCommGrpCat.ext fun z => by
    obtain ⟨n, x, hx, hz⟩ := degreeZeroLocalization_exists_fraction_of_degree A B hf z
    have hzx : z = fractionHom A B hf n ⟨x, hx⟩ := Subtype.ext hz
    have hmn : AddCommGrpCat.Hom.hom m (fractionHom A B hf n ⟨x, hx⟩) =
        AddCommGrpCat.Hom.hom (s.ι.app n) ⟨x, hx⟩ :=
      congrArg (fun φ : (homogeneousSequence A B hf).obj n ⟶ s.pt =>
        AddCommGrpCat.Hom.hom φ ⟨x, hx⟩) (hm n)
    change AddCommGrpCat.Hom.hom m z = descHom A B hf s z
    rw [hzx, hmn, descHom_fractionHom A B hf s n ⟨x, hx⟩]

/-- **The colimit of the system of homogeneous pieces is the degree-zero localization**, as an
isomorphism of abelian groups. -/
public def colimitHomogeneousSequenceIso (hf : f ∈ A d) :
    colimit (homogeneousSequence A B hf) ≅
      AddCommGrpCat.of (GradedModuleDegreeZeroLocalization A B f) :=
  colimit.isoColimitCocone ⟨degreeZeroCocone A B hf, isColimitDegreeZeroCocone A B hf⟩

/-- The `n`-th colimit inclusion followed by `colimitHomogeneousSequenceIso A B hf` is the leg
`fractionHom A B hf n`. -/
@[simp]
public theorem colimit_ι_colimitHomogeneousSequenceIso_hom (hf : f ∈ A d) (n : ℕ) :
    colimit.ι (homogeneousSequence A B hf) n ≫ (colimitHomogeneousSequenceIso A B hf).hom =
      AddCommGrpCat.ofHom (fractionHom A B hf n) :=
  colimit.isoColimitCocone_ι_hom _ n

end Stacks.SheafOfModules

end
