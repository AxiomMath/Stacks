module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.PositiveDegreeSurjectivity
public import StacksFrontier.Algebra.Category.Grp.TotalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology computes sheaf cohomology on a Hausdorff quasi-compact space

Let `X` be a Hausdorff quasi-compact topological space and `F` an abelian sheaf on `X`.  Stacks
09UZ produces the canonical comparison

`Ȟ^n(X, F) = colim_𝒰 Ȟ^n(𝒰, F) ⟶ H^n(X, F)`

from the Čech cohomology of `X`, the colimit over all open coverings of the Čech cohomology of
the covering, to sheaf cohomology.  This file proves Stacks 09V2: that comparison is an
isomorphism in every degree.  In degree one this is Stacks 09V1 and holds on an arbitrary space.

## The argument

Fix an injective resolution `F ⟶ J^•` and, for an open covering `𝒰`, let `A(𝒰)` be the Čech
bicomplex of `J^•` with the resolution degree first and the Čech degree second.  Stacks 03AX
computes sheaf cohomology as the cohomology of the total complex `Tot A(𝒰)`, through the
degreewise augmentation `α : Γ(J^•) ⟶ Tot A(𝒰)`, which is a quasi-isomorphism, and the
comparison from Čech cohomology is induced by `β : Č^•(𝒰, F) ⟶ Tot A(𝒰)`, the zeroth column.

Everything then rests on one statement about the columns of `A`,
`total_boundary_mod_column_after_refinement`: a total cochain in degree `n` whose boundary lies
in the zeroth column becomes, after finitely many refinements of the covering, a cochain of the
zeroth column modulo a total boundary.  Its proof clears the columns of the cochain from the
rightmost one inwards.  The component in the rightmost occupied column `p > 0` is killed by the
differential of the resolution, hence is locally in the image of the column `p - 1`; Stacks 09UW
— this is the one place where `X` being Hausdorff and quasi-compact is used — refines the
covering so that all those local primitives live on the iterated intersections of a *single*
covering, and subtracting the total boundary of the resulting primitive empties column `p`
without touching the columns to its right.  At the foot of the induction only the zeroth column
is left, where left exactness of the Čech complex functor identifies `F` with `ker(J^0 → J^1)`
in every Čech degree.

Applied to a total cocycle this gives surjectivity of the comparison; applied to a total
primitive of a Čech cocycle it gives that a Čech class killed by the comparison already dies
after a refinement.  Those two statements make the comparison out of the colimit bijective,
because any two open coverings have a common refinement, so every class in the colimit is
represented on a single covering.

## Main results

* `Stacks.Cohomology.CechRefinement.isIso_colimitToCohomology`: Stacks 09V2, the Čech-to-sheaf
  cohomology comparison of Stacks 09UZ on a Hausdorff quasi-compact space is an isomorphism in
  every degree.
* `Stacks.Cohomology.CechRefinement.exists_cechCocycle_and_totalBoundary`: the surjectivity
  half at the level of complexes — every cocycle of the total Čech complex of an injective
  resolution becomes, after a refinement, the image of a Čech cocycle of the sheaf modulo a
  total boundary.
* `Stacks.Cohomology.CechRefinement.exists_cechBoundary_of_totalBoundary`: the injectivity half
  at the level of complexes — a Čech cochain whose image in the total complex is a boundary
  becomes a Čech coboundary after a refinement.
* `Stacks.Cohomology.CechRefinement.isIso_colimit_of_cocycle_descent`: a map out of a colimit of
  abelian groups computed in a fixed degree by a map of families of complexes is invertible as
  soon as cocycles and boundaries descend along the index category.
* `Stacks.Cohomology.CechRefinement.exists_colimit_representative`: over an index category in
  which any two objects have a common target, every element of a colimit of abelian groups is
  represented on a single term.

## Implementation notes

The companion module `PositiveDegreeSurjectivity` proves the surjectivity half for nonnegative
degrees by a staircase through the bidegrees of a single class; the column induction used here
proves the two halves at once and in every integer degree, and reuses from that module the
refinement step `exists_refinement_cochain_preimage_int`, which is where Stacks 09UW enters.

A cochain of a total complex of abelian groups is handled through its coordinates on the
diagonal, the API of `StacksFrontier.Algebra.Category.Grp.TotalComplex`: `totalProjectionDiag` reads
off one summand, and `total_ext_elements` recovers a cochain from all of them.  The coordinates
are taken in a `DirectSum`, which is what makes the support of a cochain finite and therefore
gives the column bound `total_has_upper_bound` that starts the induction.

## References

* [Stacks Project, Tag 09V2](https://stacks.math.columbia.edu/tag/09V2)
* [Stacks Project, Tag 09V1](https://stacks.math.columbia.edu/tag/09V1)
* [Stacks Project, Tag 09UZ](https://stacks.math.columbia.edu/tag/09UZ)
* [Stacks Project, Tag 09UW](https://stacks.math.columbia.edu/tag/09UW)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe s t w v u

namespace Stacks.Cohomology.CechRefinement

open LeftComplexResolution

open OpenCoverSet

/-! ### Representatives of an element of a colimit of abelian groups -/

section Colimit

variable {I : Type s} [Category.{t} I] (D : I ⥤ AddCommGrpCat.{w}) [HasColimit D]

/-- Over an index category with an object and with a common target for any two objects, every
element of a colimit of abelian groups is the image of an element of a single term: the elements
of that shape form a subgroup, and the colimit factors through it. -/
theorem exists_colimit_representative (i₀ : I)
    (hconn : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (x : (colimit D : AddCommGrpCat.{w})) :
    ∃ (i : I) (a : D.obj i), colimit.ι D i a = x := by
  classical
  let S : AddSubgroup (colimit D : AddCommGrpCat.{w}) :=
    { carrier := {x | ∃ (i : I) (a : D.obj i), colimit.ι D i a = x}
      zero_mem' := ⟨i₀, 0, map_zero _⟩
      add_mem' := by
        rintro x y ⟨i, a, rfl⟩ ⟨j, b, rfl⟩
        obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hconn i j
        refine ⟨k, D.map f a + D.map g b, ?_⟩
        rw [map_add, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          colimit.w D f, colimit.w D g]
      neg_mem' := by
        rintro x ⟨i, a, rfl⟩
        exact ⟨i, -a, map_neg _ _⟩ }
  let c : Cocone D :=
    { pt := AddCommGrpCat.of S
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom
            { toFun := fun a ↦ ⟨colimit.ι D i a, i, a, rfl⟩
              map_zero' := by ext; exact map_zero _
              map_add' := by intros; ext; exact map_add _ _ _ }
          naturality := by
            intro i j r
            ext a
            exact Subtype.ext (ConcreteCategory.congr_hom (colimit.w D r) a) } }
  let incl : c.pt ⟶ colimit D := AddCommGrpCat.ofHom S.subtype
  have hi : colimit.desc D c ≫ incl = 𝟙 _ := by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, colimit.ι_desc]
    rfl
  have hx := (colimit.desc D c x).property
  change ∃ i a, colimit.ι D i a = incl (colimit.desc D c x) at hx
  rwa [← ConcreteCategory.comp_apply, hi, ConcreteCategory.id_apply] at hx

/-- A map out of a colimit of abelian groups is invertible as soon as every element of the
target comes from one term and every kernel class of a term dies after passing to a later
term. -/
theorem isIso_of_surjective_of_kernel_vanishes_later (i₀ : I)
    (hconn : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    {H : AddCommGrpCat.{w}} (t : colimit D ⟶ H)
    (hsurj : ∀ y : H, ∃ (i : I) (a : D.obj i), t (colimit.ι D i a) = y)
    (hker : ∀ (i : I) (a : D.obj i), t (colimit.ι D i a) = 0 →
      ∃ (j : I) (r : i ⟶ j), D.map r a = 0) :
    IsIso t := by
  refine (ConcreteCategory.isIso_iff_bijective t).2 ⟨(injective_iff_map_eq_zero t.hom).2 ?_, ?_⟩
  · intro x hx
    obtain ⟨i, a, rfl⟩ := exists_colimit_representative D i₀ hconn x
    obtain ⟨j, r, hr⟩ := hker i a hx
    calc colimit.ι D i a = colimit.ι D j (D.map r a) :=
          (ConcreteCategory.congr_hom (colimit.w D r) a).symm
      _ = 0 := by rw [hr, map_zero]
  · intro y
    obtain ⟨i, a, ha⟩ := hsurj y
    exact ⟨colimit.ι D i a, ha⟩

end Colimit

/-! ### Coordinates of a cochain of a total complex -/

section Total

variable (A : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The coordinates of a cochain of a total complex are natural in the bicomplex. -/
private theorem totalProjectionDiag_map
    {B : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (φ : A ⟶ B) (p q n : ℤ) (h : p + q = n) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n ≫ totalProjectionDiag B p q n h =
      totalProjectionDiag A p q n h ≫ (φ.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
  intro a b hab
  by_cases ha : a = p
  · subst a
    have hbq : b = q := by
      simp only [ComplexShape.π_def] at hab
      omega
    subst b
    rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
      inclusion_projection_self, Category.comp_id, ← Category.assoc,
      inclusion_projection_self, Category.id_comp]
  · rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
      inclusion_projection_ne _ a b p q n hab h ha, ← Category.assoc,
      inclusion_projection_ne _ a b p q n hab h ha]
    simp only [Limits.comp_zero, Limits.zero_comp]

end Total

/-- A cochain of a total complex is supported in the columns up to `k` if all its coordinates in
larger first degrees vanish. -/
private abbrev totalBounded
    (A : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (n k : ℤ) (z : (A.total (ComplexShape.up ℤ)).X n) : Prop :=
  ∀ p q (h : p + q = n), k < p → totalProjectionDiag A p q n h z = 0

/-- Being supported in the columns up to `k` is preserved by a map of bicomplexes. -/
private theorem totalBounded_map
    {A B : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (φ : A ⟶ B) {n k : ℤ}
    {z : (A.total (ComplexShape.up ℤ)).X n} (hz : totalBounded A n k z) :
    totalBounded B n k ((HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n z) := by
  intro p q h hp
  rw [← ConcreteCategory.comp_apply, totalProjectionDiag_map, ConcreteCategory.comp_apply,
    hz p q h hp, map_zero]

/-- The map of total complexes induced by a map of bicomplexes commutes with the differential. -/
private theorem total_map_d_apply
    {A B : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (φ : A ⟶ B) (n : ℤ) (z : (A.total (ComplexShape.up ℤ)).X n) :
    (B.total (ComplexShape.up ℤ)).d n (n + 1)
        ((HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n z) =
      (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f (n + 1)
        ((A.total (ComplexShape.up ℤ)).d n (n + 1) z) := by
  rw [← ConcreteCategory.comp_apply, (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).comm,
    ConcreteCategory.comp_apply]

/-- Adding a boundary to a cochain does not change its coboundary. -/
private theorem d_eq_of_eq_add_d (K : CochainComplex AddCommGrpCat.{w} ℤ) {n : ℤ}
    {a b : K.X n} {t : K.X (n - 1)} (h : a = b + K.d (n - 1) n t) :
    K.d n (n + 1) a = K.d n (n + 1) b := by
  have hdd : K.d n (n + 1) (K.d (n - 1) n t) = 0 :=
    ConcreteCategory.congr_hom (K.d_comp_d (n - 1) n (n + 1)) t
  rw [h, map_add, hdd, add_zero]

/-! ### Clearing the columns of a cochain of a total complex -/

section SingleColumn

variable {A : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
  {M : CochainComplex AddCommGrpCat.{w} ℤ}

/-- A map into a total complex factoring through the zeroth column has no coordinate outside
that column. -/
private theorem column_map_projection_zero (f : M ⟶ A.X 0) (g : M ⟶ A.total (ComplexShape.up ℤ))
    (hg : ∀ n, g.f n = f.f n ≫ A.ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n))
    (p q n : ℤ) (h : p + q = n) (hp : p ≠ 0) :
    g.f n ≫ totalProjectionDiag A p q n h = 0 := by
  rw [hg, Category.assoc, inclusion_projection_ne A 0 n p q n (zero_add n) h hp.symm]
  simp

/-- The coordinate in the rightmost occupied column of a cochain whose boundary lies in the
zeroth column is killed by the differential of the bicomplex. -/
private theorem column_top_closed (f : M ⟶ A.X 0) (g : M ⟶ A.total (ComplexShape.up ℤ))
    (hg : ∀ n, g.f n = f.f n ≫ A.ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n))
    (n p q : ℤ) (h : p + q = n) (hp : 0 ≤ p) (z : (A.total (ComplexShape.up ℤ)).X n)
    (u : M.X (n + 1)) (hz : (A.total (ComplexShape.up ℤ)).d n (n + 1) z = g.f (n + 1) u)
    (hb : totalBounded A n p z) :
    (A.d p (p + 1)).f q (totalProjectionDiag A p q n h z) = 0 := by
  have e := congrArg (totalProjectionDiag A (p + 1) q (n + 1) (by omega)) hz
  rw [← ConcreteCategory.comp_apply,
    differential_projection A (p + 1) q p (q - 1) n rfl (by omega) (by omega),
    ← ConcreteCategory.comp_apply,
    column_map_projection_zero f g hg (p + 1) q (n + 1) (by omega) (by omega)] at e
  simpa [Units.smul_def, AddCommGrpCat.hom_comp, ConcreteCategory.comp_apply,
    hb (p + 1) (q - 1) (by omega) (by omega)] using e

/-- A map into a total complex factoring through the zeroth column is injective in a degree as
soon as the map into that column is. -/
private theorem column_augmentation_injective (f : M ⟶ A.X 0)
    (g : M ⟶ A.total (ComplexShape.up ℤ))
    (hg : ∀ n, g.f n = f.f n ≫ A.ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n))
    (hf : ∀ n, Function.Injective (f.f n)) (n : ℤ) : Function.Injective (g.f n) := by
  intro x y hxy
  apply hf n
  have e := congrArg (totalProjectionDiag A 0 n n (zero_add n)) hxy
  have he : g.f n ≫ totalProjectionDiag A 0 n n (zero_add n) = f.f n := by
    rw [hg n, Category.assoc, inclusion_projection_self, Category.comp_id]
  simpa only [← ConcreteCategory.comp_apply, he] using e

end SingleColumn

section ColumnInduction

variable {I : Type s} [Category.{t} I]
  (A : I → HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  (Amap : ∀ {i j : I}, (i ⟶ j) → (A i ⟶ A j))
  (M : I → CochainComplex AddCommGrpCat.{w} ℤ)
  (Mmap : ∀ {i j : I}, (i ⟶ j) → (M i ⟶ M j))
  (f : ∀ i, M i ⟶ (A i).X 0)
  (g : ∀ i, M i ⟶ (A i).total (ComplexShape.up ℤ))
  (hAid : ∀ i : I, Amap (𝟙 i) = 𝟙 (A i))
  (hAcomp : ∀ {i j k : I} (r : i ⟶ j) (s : j ⟶ k), Amap (r ≫ s) = Amap r ≫ Amap s)
  (hg : ∀ i n, (g i).f n = (f i).f n ≫ (A i).ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n))
  (hgnat : ∀ {i j : I} (r : i ⟶ j),
    Mmap r ≫ g j = g i ≫ HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ))
  (hA : ∀ (i : I) (p : ℤ), p < 0 → IsZero ((A i).X p))
  (hzero : ∀ (i : I) (q : ℤ) (x : ((A i).X 0).X q),
    ((A i).d 0 1).f q x = 0 → ∃ y, (f i).f q y = x)
  (hpos : ∀ (i : I) (p p' q : ℤ) (_hp : 0 ≤ p) (_hp' : p + 1 = p') (x : ((A i).X p').X q),
    ((A i).d p' (p' + 1)).f q x = 0 →
    ∃ (j : I) (r : i ⟶ j) (y : ((A j).X p).X q),
      ((A j).d p p').f q y = ((Amap r).f p').f q x)
  (hf : ∀ (i : I) (n : ℤ), Function.Injective ((f i).f n))

include hAid hAcomp hg hgnat hA hzero hpos in
/-- **Stacks 09V2**, the column induction.  A cochain of the total complex whose boundary lies
in the zeroth column becomes, after finitely many steps along the index category, a cochain of
the zeroth column modulo a boundary of the total complex.

The coordinate in the rightmost occupied column is killed by the differential of the bicomplex,
hence by `hpos` is the image of a coordinate one column to the left after one step; subtracting
the total boundary of the latter empties that column. -/
private theorem total_boundary_mod_column_after_refinement
    (i : I) (n : ℤ) (k : ℕ) (z : ((A i).total (ComplexShape.up ℤ)).X n) (u : (M i).X (n + 1))
    (hz : ((A i).total (ComplexShape.up ℤ)).d n (n + 1) z = (g i).f (n + 1) u)
    (hb : totalBounded (A i) n k z) :
    ∃ (j : I) (r : i ⟶ j) (v : (M j).X n)
      (t : ((A j).total (ComplexShape.up ℤ)).X (n - 1)),
      (HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ)).f n z =
        (g j).f n v + ((A j).total (ComplexShape.up ℤ)).d (n - 1) n t := by
  induction k generalizing i with
  | zero =>
    have hc := column_top_closed (f i) (g i) (hg i) n 0 n (zero_add n) le_rfl z u hz hb
    obtain ⟨v, hv⟩ := hzero i n _ hc
    refine ⟨i, 𝟙 i, v, 0, ?_⟩
    rw [hAid i, HomologicalComplex₂.total.map_id, HomologicalComplex.id_f,
      ConcreteCategory.id_apply, map_zero, add_zero]
    apply total_ext_elements (A i) n
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hqn : q = n := by omega
      subst q
      rw [hg i n, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        inclusion_projection_self]
      exact hv.symm
    · rw [← ConcreteCategory.comp_apply,
        column_map_projection_zero (f i) (g i) (hg i) p q n hpq hp]
      change totalProjectionDiag (A i) p q n hpq z = 0
      by_cases hn : p < 0
      · have he : totalProjectionDiag (A i) p q n hpq = 0 :=
          ((HomologicalComplex.eval AddCommGrpCat.{w} (ComplexShape.up ℤ) q).map_isZero
            (hA i p hn)).eq_of_tgt _ _
        rw [he]
        rfl
      · exact hb p q hpq (by omega)
  | succ k ih =>
    obtain ⟨p₀, p, q, q', hp₀, hp, hpq, hq'⟩ :
        ∃ p₀ p q q' : ℤ, p₀ = (k : ℤ) ∧ p₀ + 1 = p ∧ p + q = n ∧ q + 1 = q' :=
      ⟨(k : ℤ), (k : ℤ) + 1, n - (k : ℤ) - 1, n - (k : ℤ), rfl, rfl, by omega, by omega⟩
    have hbp : totalBounded (A i) n p z := fun a b h ha ↦ hb a b h (by omega)
    have hc := column_top_closed (f i) (g i) (hg i) n p q hpq (by omega) z u hz hbp
    obtain ⟨j, r, y, hy⟩ := hpos i p₀ p q (by omega) hp _ hc
    have hw : ((A j).total (ComplexShape.up ℤ)).d n (n + 1)
        ((HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ)).f n z) =
        (g j).f (n + 1) ((Mmap r).f (n + 1) u) := by
      rw [total_map_d_apply, hz, ← ConcreteCategory.comp_apply]
      exact ConcreteCategory.congr_hom (congrArg (fun h ↦ h.f (n + 1)) (hgnat r)).symm u
    have hwb : totalBounded (A j) n p
        ((HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ)).f n z) :=
      totalBounded_map (Amap r) hbp
    have hy' : ((A j).d p₀ p).f q y =
        totalProjectionDiag (A j) p q n hpq
          ((HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ)).f n z) := by
      rw [← ConcreteCategory.comp_apply, totalProjectionDiag_map, ConcreteCategory.comp_apply]
      exact hy
    have hιpq : p₀ + q = n - 1 := by omega
    have hdy : ((A j).total (ComplexShape.up ℤ)).d (n - 1) n
          ((A j).ιTotal (ComplexShape.up ℤ) p₀ q (n - 1) hιpq y) =
        (A j).ιTotal (ComplexShape.up ℤ) p q n
            (by simp only [ComplexShape.π_def]; omega) (((A j).d p₀ p).f q y) +
          p₀.negOnePow • (A j).ιTotal (ComplexShape.up ℤ) p₀ q' n
            (by simp only [ComplexShape.π_def]; omega) (((A j).X p₀).d q q' y) :=
      differential_inclusion_apply (A j) p₀ q p q' (n - 1) n hιpq hp hq' (by omega) y
    have hd : ((A j).total (ComplexShape.up ℤ)).d n (n + 1)
        ((HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ)).f n z -
          ((A j).total (ComplexShape.up ℤ)).d (n - 1) n
            ((A j).ιTotal (ComplexShape.up ℤ) p₀ q (n - 1) hιpq y)) =
        (g j).f (n + 1) ((Mmap r).f (n + 1) u) := by
      rw [map_sub, ← ConcreteCategory.comp_apply
        (((A j).total (ComplexShape.up ℤ)).d (n - 1) n)
        (((A j).total (ComplexShape.up ℤ)).d n (n + 1)), HomologicalComplex.d_comp_d]
      simpa using hw
    have hb' : totalBounded (A j) n (k : ℤ)
        ((HomologicalComplex₂.total.map (Amap r) (ComplexShape.up ℤ)).f n z -
          ((A j).total (ComplexShape.up ℤ)).d (n - 1) n
            ((A j).ιTotal (ComplexShape.up ℤ) p₀ q (n - 1) hιpq y)) := by
      intro a b hab ha
      rw [map_sub, hdy, map_add, Units.smul_def, map_zsmul]
      by_cases hap : a = p
      · subst a
        have hbq : b = q := by omega
        subst b
        rw [projection_inclusion_self,
          projection_inclusion_ne (A j) p₀ q' p q n (by omega) hab (by omega),
          smul_zero, add_zero, hy']
        exact sub_self _
      · rw [hwb a b hab (by omega),
          projection_inclusion_ne (A j) p q a b n hpq hab (by omega),
          projection_inclusion_ne (A j) p₀ q' a b n (by omega) hab (by omega),
          smul_zero, add_zero, sub_zero]
    obtain ⟨l, s, v, t, ht⟩ := ih j _ ((Mmap r).f (n + 1) u) hd hb'
    refine ⟨l, r ≫ s, v, t + (HomologicalComplex₂.total.map (Amap s)
      (ComplexShape.up ℤ)).f (n - 1)
      ((A j).ιTotal (ComplexShape.up ℤ) p₀ q (n - 1) hιpq y), ?_⟩
    rw [hAcomp r s, HomologicalComplex₂.total.map_comp, HomologicalComplex.comp_f,
      ConcreteCategory.comp_apply, map_add]
    rw [map_sub, ← ConcreteCategory.comp_apply
      (((A j).total (ComplexShape.up ℤ)).d (n - 1) n)
      ((HomologicalComplex₂.total.map (Amap s) (ComplexShape.up ℤ)).f n),
      ← (HomologicalComplex₂.total.map (Amap s) (ComplexShape.up ℤ)).comm,
      ConcreteCategory.comp_apply] at ht
    exact (sub_eq_iff_eq_add.mp ht).trans (by abel)

end ColumnInduction

/-! ### Cocycles and boundaries of a family of complexes -/

section Descent

variable {I : Type s} [Category.{t} I]

/-- A cochain killed by the differential, viewed as a cycle of the complex. -/
private def cocycleOf (K : CochainComplex AddCommGrpCat.{w} ℤ) (n : ℤ) (x : K.X n)
    (hx : K.d n (n + 1) x = 0) : K.cycles n :=
  (K.sc n).abCyclesIso.inv ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
    exact hx⟩

/-- The cycle attached to a cochain killed by the differential has that cochain as its
image. -/
private theorem iCycles_cocycleOf (K : CochainComplex AddCommGrpCat.{w} ℤ) (n : ℤ) (x : K.X n)
    (hx : K.d n (n + 1) x = 0) : K.iCycles n (cocycleOf K n x hx) = x :=
  (K.sc n).abCyclesIso_inv_apply_iCycles ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
    exact hx⟩

/-- A cycle with vanishing homology class is a boundary: the projection to homology is a
cokernel of the map from the cochains one degree down. -/
private theorem exists_boundary_of_homologyπ_eq_zero (K : CochainComplex AddCommGrpCat.{w} ℤ)
    (n : ℤ) (x : K.cycles n) (hx : K.homologyπ n x = 0) :
    ∃ b : K.X (n - 1), K.d (n - 1) n b = K.iCycles n x := by
  have hT : (ShortComplex.mk (K.sc n).toCycles (K.sc n).homologyπ
      (K.sc n).toCycles_comp_homologyπ).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.sc n).homologyIsCokernel
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp hT x hx
  have h : ∃ b : K.X ((ComplexShape.up ℤ).prev n),
      K.d ((ComplexShape.up ℤ).prev n) n b = K.iCycles n x := by
    refine ⟨b, ?_⟩
    have e : K.iCycles n (K.toCycles ((ComplexShape.up ℤ).prev n) n b) = K.iCycles n x :=
      congrArg (K.iCycles n) hb
    exact ((ConcreteCategory.congr_hom
      (K.toCycles_i ((ComplexShape.up ℤ).prev n) n) b).symm.trans
      (ConcreteCategory.comp_apply _ _ b)).trans e
  rwa [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (n - 1) n by
    change n - 1 + 1 = n; omega)] at h

/-- The map induced on homology by a map of complexes, on homology classes of cycles. -/
private theorem homologyMap_homologyπ_apply {K L : CochainComplex AddCommGrpCat.{w} ℤ}
    (f : K ⟶ L) (n : ℤ) (x : K.cycles n) :
    HomologicalComplex.homologyMap f n (K.homologyπ n x) =
      L.homologyπ n (HomologicalComplex.cyclesMap f n x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) x

/-- The map induced on cycles by a map of complexes, read in the cochains. -/
private theorem iCycles_cyclesMap_apply {K L : CochainComplex AddCommGrpCat.{w} ℤ} (f : K ⟶ L)
    (n : ℤ) (x : K.cycles n) :
    L.iCycles n (HomologicalComplex.cyclesMap f n x) = f.f n (K.iCycles n x) :=
  ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) x

variable (D : I ⥤ AddCommGrpCat.{w}) [HasColimit D]
  (M T : I → CochainComplex AddCommGrpCat.{w} ℤ)
  (Mmap : ∀ {i j : I}, (i ⟶ j) → (M i ⟶ M j))
  (Tmap : ∀ {i j : I}, (i ⟶ j) → (T i ⟶ T j))
  (g : ∀ i, M i ⟶ T i) (n : ℤ)

/-- A map out of a colimit of abelian groups which in degree `n` is computed by a map of
families of complexes is invertible as soon as every cocycle of the target complex becomes a
cocycle of the source complex modulo a boundary, and every cochain of the source complex whose
image is a boundary becomes a boundary, after a step along the index category. -/
theorem isIso_colimit_of_cocycle_descent (i₀ : I)
    (hconn : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (e : ∀ i, D.obj i ≅ (M i).homology n)
    (he : ∀ {i j : I} (r : i ⟶ j),
      D.map r ≫ (e j).hom = (e i).hom ≫ HomologicalComplex.homologyMap (Mmap r) n)
    {H : AddCommGrpCat.{w}} (t : colimit D ⟶ H) (a : ∀ i, (T i).homology n ≅ H)
    (ha : ∀ {i j : I} (r : i ⟶ j),
      HomologicalComplex.homologyMap (Tmap r) n ≫ (a j).hom = (a i).hom)
    (ht : ∀ i, colimit.ι D i ≫ t =
      (e i).hom ≫ HomologicalComplex.homologyMap (g i) n ≫ (a i).hom)
    (hsurj : ∀ (i : I) (z : (T i).X n), (T i).d n (n + 1) z = 0 →
      ∃ (j : I) (r : i ⟶ j) (x : (M j).X n) (b : (T j).X (n - 1)),
        (M j).d n (n + 1) x = 0 ∧
        (Tmap r).f n z = (g j).f n x + (T j).d (n - 1) n b)
    (hker : ∀ (i : I) (x : (M i).X n) (b : (T i).X (n - 1)),
      (T i).d (n - 1) n b = (g i).f n x →
      ∃ (j : I) (r : i ⟶ j) (y : (M j).X (n - 1)),
        (Mmap r).f n x = (M j).d (n - 1) n y) :
    IsIso t := by
  refine isIso_of_surjective_of_kernel_vanishes_later D i₀ hconn t (fun y ↦ ?_) (fun i x hx ↦ ?_)
  · obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective ((T i₀).homologyπ n)).mp
      inferInstance ((a i₀).inv y)
    have hzc : (T i₀).d n (n + 1) ((T i₀).iCycles n z) = 0 :=
      ConcreteCategory.congr_hom ((T i₀).iCycles_d n (n + 1)) z
    obtain ⟨j, r, x, b, hxc, hxb⟩ := hsurj i₀ _ hzc
    have hc : (T j).homologyπ n (HomologicalComplex.cyclesMap (Tmap r) n z) =
        (T j).homologyπ n
          (HomologicalComplex.cyclesMap (g j) n (cocycleOf (M j) n x hxc)) := by
      refine homologyπ_eq_of_boundary _ n (n - 1) _ _ b ?_
      rw [iCycles_cyclesMap_apply, iCycles_cyclesMap_apply, iCycles_cocycleOf]
      exact hxb
    refine ⟨j, (e j).inv ((M j).homologyπ n (cocycleOf (M j) n x hxc)), ?_⟩
    rw [← ConcreteCategory.comp_apply, ht, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, homologyMap_homologyπ_apply, ← hc,
      ← homologyMap_homologyπ_apply, ← ConcreteCategory.comp_apply, ha, hz,
      Iso.inv_hom_id_apply]
  · obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective ((M i).homologyπ n)).mp
      inferInstance ((e i).hom x)
    have hgz : (T i).homologyπ n (HomologicalComplex.cyclesMap (g i) n z) = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (a i).hom).1
      rw [map_zero, ← homologyMap_homologyπ_apply, hz]
      simpa only [← ConcreteCategory.comp_apply, ht, Category.assoc] using hx
    obtain ⟨b, hb⟩ := exists_boundary_of_homologyπ_eq_zero _ n _ hgz
    rw [iCycles_cyclesMap_apply] at hb
    obtain ⟨j, r, y, hy⟩ := hker i _ b hb
    refine ⟨j, r, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (e j).hom).1
    rw [map_zero, ← ConcreteCategory.comp_apply, he, ConcreteCategory.comp_apply, ← hz,
      homologyMap_homologyπ_apply]
    have hc : HomologicalComplex.cyclesMap (Mmap r) n z = (M j).toCycles (n - 1) n y := by
      apply (AddCommGrpCat.mono_iff_injective ((M j).iCycles n)).mp inferInstance
      rwa [iCycles_cyclesMap_apply, ← ConcreteCategory.comp_apply ((M j).toCycles (n - 1) n)
        ((M j).iCycles n), HomologicalComplex.toCycles_i]
    rw [hc, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ]
    rfl

end Descent

/-! ### The Čech complexes of a space over its open coverings -/

section Refinements

variable {X : Type u} [TopologicalSpace X]

/-- The integer-graded Čech complex of an abelian sheaf for a fixed open covering of the
space. -/
abbrev cechComplexIntAt (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (U : OpenCoverSet X) : CochainComplex AddCommGrpCat.{max u v} ℤ :=
  (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U)).obj G

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]
  {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}
  (J : InjectiveResolution G)

/-- The inclusion of the Čech complex of a sheaf into the zeroth column of the Čech bicomplex
of an injective resolution, for a fixed open covering of the space. -/
abbrev cechInclusionAt (U : OpenCoverSet X) :
    cechComplexIntAt G U ⟶ (resolutionBicomplex U J).X 0 :=
  (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
    (hypercover U)).map J.inclusionZero

/-- **Stacks 03AX**, the map `β`: the Čech complex of a sheaf maps to the total Čech complex of
an injective resolution through the zeroth column. -/
abbrev cechToTotalAt (U : OpenCoverSet X) : cechComplexIntAt G U ⟶ resolutionTotal U J :=
  CechSite.cechToTotal.{v} (Opens.grothendieckTopology X) (hypercover U) G J

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The identity refinement induces the identity of Čech bicomplexes of a resolution. -/
theorem refinementBicomplexMap_id (U : OpenCoverSet X) :
    refinementBicomplexMap (𝟙 U) J = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  rw [HomologicalComplex.id_f]
  exact refinementComplexIntNat_app_id U (J.cochainComplex.X p)

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The refinement maps of Čech bicomplexes of a resolution compose contravariantly. -/
theorem refinementBicomplexMap_comp {U V W : OpenCoverSet X} (f : U ⟶ V) (g : V ⟶ W) :
    refinementBicomplexMap (f ≫ g) J =
      refinementBicomplexMap f J ≫ refinementBicomplexMap g J := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  rw [HomologicalComplex.comp_f]
  exact (refinementComplexIntNat_app_comp f g (J.cochainComplex.X p)).symm

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- A refinement commutes with the map `β` of Stacks 03AX from the Čech complex of the sheaf to
the total Čech complex of an injective resolution. -/
theorem cechToTotalAt_naturality {U V : OpenCoverSet X} (f : U ⟶ V) :
    (refinementComplexIntNat f).app G ≫ cechToTotalAt J V =
      cechToTotalAt J U ≫
        HomologicalComplex₂.total.map (refinementBicomplexMap f J) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  have hn := congrArg (fun h ↦ HomologicalComplex.Hom.f h p)
    ((refinementComplexIntNat f).naturality J.inclusionZero)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hn
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cechToTotal_f, cechToTotal_f,
    Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) 0 p p
    (zero_add p)) hn.symm

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- A refinement does not change the augmentation `α` of Stacks 03AX of the sections of an
injective resolution into the total Čech complex. -/
theorem totalAugmentation_naturality {U V : OpenCoverSet X} (f : U ⟶ V)
    (RU : CechSite.CechResolutionComparison.{v} (Opens.grothendieckTopology X) (hypercover U)
      (hypercover_mem_grothendieckTopology U) G J)
    (RV : CechSite.CechResolutionComparison.{v} (Opens.grothendieckTopology X) (hypercover V)
      (hypercover_mem_grothendieckTopology V) G J) :
    RU.α ≫ refinementTotalMap f J = RV.α := by
  refine HomologicalComplex.hom_ext _ _ fun q ↦ ?_
  rw [HomologicalComplex.comp_f, RU.α_f, RV.α_f, refinementTotalMap, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  change _ ≫ ((refinementComplexIntNat f).app (J.cochainComplex.X q)).f 0 ≫ _ = _
  rw [← Category.assoc, cechAugmentationInt_refinement f (J.cochainComplex.X q)]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The columns of the Čech bicomplex of a bounded-below resolution vanish in negative
degrees. -/
theorem resolutionBicomplexAt_isZero (U : OpenCoverSet X) (p : ℤ) (hp : p < 0) :
    IsZero ((resolutionBicomplex U J).X p) :=
  (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U)).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 p hp)

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- A Čech cochain of the degree-zero term of an injective resolution killed by the differential
of the resolution comes from the sheaf: the Čech complex functor is left exact. -/
theorem exists_cechInclusionAt_preimage (U : OpenCoverSet X) (q : ℤ)
    (x : ((resolutionBicomplex U J).X 0).X q)
    (hx : ((resolutionBicomplex U J).d 0 1).f q x = 0) :
    ∃ y, (cechInclusionAt J U).f q y = x := by
  have hC := preservesFiniteLimits_cechIntEval.{v} U q
  have hmono := mono_inclusionZero J
  have he := (inclusionZero_exact J).map_of_mono_of_preservesKernel
    (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
      HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) q)
    inferInstance inferInstance
  exact (ShortComplex.ab_exact_iff _).mp he x hx

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The Čech complex of the sheaf injects into the zeroth column of the Čech bicomplex of an
injective resolution, in every Čech degree. -/
theorem injective_cechInclusionAt (U : OpenCoverSet X) (q : ℤ) :
    Function.Injective ((cechInclusionAt J U).f q) := by
  have hC := preservesFiniteLimits_cechIntEval.{v} U q
  have hmono := mono_inclusionZero J
  refine (AddCommGrpCat.mono_iff_injective _).mp ?_
  exact (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
    HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) q).map_mono _

omit [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- **Stacks 09V2**, the refinement step read off the Čech bicomplex: a cochain in a positive
column killed by the differential of the resolution is, after a refinement of the covering, the
image of a cochain one column to the left.  This is the one place where `X` being Hausdorff and
quasi-compact is used, through Stacks 09UW. -/
theorem exists_refinement_column_preimage [T2Space X] [CompactSpace X] (U : OpenCoverSet X)
    (p p' q : ℤ) (hp : 0 ≤ p) (hp' : p + 1 = p')
    (x : ((resolutionBicomplex U J).X p').X q)
    (hx : ((resolutionBicomplex U J).d p' (p' + 1)).f q x = 0) :
    ∃ (V : OpenCoverSet X) (r : U ⟶ V) (y : ((resolutionBicomplex V J).X p).X q),
      ((resolutionBicomplex V J).d p p').f q y = (((refinementBicomplexMap r J).f p').f q) x := by
  have hS : (ShortComplex.mk (J.cochainComplex.d p p') (J.cochainComplex.d p' (p' + 1))
      (J.cochainComplex.d_comp_d p p' (p' + 1))).Exact :=
    (J.cochainComplex.exactAt_iff' p p' (p' + 1)
      ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel p p' from hp'))
      ((ComplexShape.up ℤ).next_eq' rfl)).mp
      (CochainComplex.exactAt_of_isLE J.cochainComplex 0 p' (by omega))
  exact exists_refinement_cochain_preimage_int.{v} _ hS U q x hx

end Refinements

/-! ### Stacks 09V2 -/

section Main

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]
  {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}
  (J : InjectiveResolution G)

/-- **Stacks 09V2**, the data of the column induction for the Čech bicomplex of an injective
resolution: the Čech complexes over the open coverings, the refinement maps between them, and
the compatibility of the map `β` with refinements. -/
private abbrev columnStepData := total_boundary_mod_column_after_refinement
    (fun U ↦ resolutionBicomplex U J) (fun r ↦ refinementBicomplexMap r J)
    (cechComplexIntAt G)
    (fun r ↦ (refinementComplexIntNat r).app G) (cechInclusionAt J) (cechToTotalAt J)
    (refinementBicomplexMap_id J) (fun r s ↦ refinementBicomplexMap_comp J r s)
    (fun U ↦ cechToTotal_f U J) (fun r ↦ cechToTotalAt_naturality J r)

/-- **Stacks 09V2**, the column induction for the Čech bicomplex of an injective resolution: a
cochain of the total complex whose boundary lies in the zeroth column becomes, after finitely
many refinements of the open covering, a Čech cochain of the sheaf modulo a boundary of the
total complex. -/
private abbrev columnStep := columnStepData J (resolutionBicomplexAt_isZero J)
    (exists_cechInclusionAt_preimage J) (exists_refinement_column_preimage J)

omit [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- **Stacks Project, Tag 09V2.** On a Hausdorff quasi-compact space every cocycle of the total
Čech complex of an injective resolution becomes, after a refinement of the open covering, the
image of a Čech cocycle of the sheaf modulo a boundary of the total complex. -/
theorem exists_cechCocycle_and_totalBoundary (U : OpenCoverSet X) (n : ℤ)
    (z : (resolutionTotal U J).X n) (hz : (resolutionTotal U J).d n (n + 1) z = 0) :
    ∃ (V : OpenCoverSet X) (r : U ⟶ V) (x : (cechComplexIntAt G V).X n)
      (b : (resolutionTotal V J).X (n - 1)),
      (cechComplexIntAt G V).d n (n + 1) x = 0 ∧
      (refinementTotalMap r J).f n z =
        (cechToTotalAt J V).f n x + (resolutionTotal V J).d (n - 1) n b := by
  obtain ⟨k, hk⟩ := total_has_upper_bound (resolutionBicomplex U J) n z
  obtain ⟨V, r, v, t, ht⟩ := columnStep J U n k z 0 (by simpa only [map_zero] using hz) hk
  refine ⟨V, r, v, t, ?_, ht⟩
  apply column_augmentation_injective (cechInclusionAt J V) (cechToTotalAt J V)
    (cechToTotal_f V J) (injective_cechInclusionAt J V) (n + 1)
  have e := d_eq_of_eq_add_d _ ht
  rw [total_map_d_apply, hz, map_zero, ← ConcreteCategory.comp_apply, (cechToTotalAt J V).comm,
    ConcreteCategory.comp_apply] at e
  exact e.symm.trans (map_zero _).symm

omit [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- **Stacks Project, Tag 09V2.** On a Hausdorff quasi-compact space a Čech cochain whose image
in the total Čech complex of an injective resolution is a boundary becomes a Čech coboundary
after a refinement of the open covering. -/
theorem exists_cechBoundary_of_totalBoundary (U : OpenCoverSet X) (n : ℤ)
    (x : (cechComplexIntAt G U).X (n + 1)) (b : (resolutionTotal U J).X n)
    (hb : (resolutionTotal U J).d n (n + 1) b = (cechToTotalAt J U).f (n + 1) x) :
    ∃ (V : OpenCoverSet X) (r : U ⟶ V) (y : (cechComplexIntAt G V).X n),
      ((refinementComplexIntNat r).app G).f (n + 1) x =
        (cechComplexIntAt G V).d n (n + 1) y := by
  obtain ⟨k, hk⟩ := total_has_upper_bound (resolutionBicomplex U J) n b
  obtain ⟨V, r, y, t, ht⟩ := columnStep J U n k b x hb hk
  refine ⟨V, r, y, ?_⟩
  apply column_augmentation_injective (cechInclusionAt J V) (cechToTotalAt J V)
    (cechToTotal_f V J) (injective_cechInclusionAt J V) (n + 1)
  have e := d_eq_of_eq_add_d _ ht
  rw [total_map_d_apply, hb] at e
  exact (ConcreteCategory.congr_hom (congrArg (fun h ↦ HomologicalComplex.Hom.f h (n + 1))
    (cechToTotalAt_naturality J r)) x).trans
    (e.trans (ConcreteCategory.congr_hom ((cechToTotalAt J V).comm n (n + 1)) y))

/-! ### The comparison out of the colimit -/

/-- The map induced on homology by a map of complexes is natural with respect to the identification
of homology with the homology functor of the derived category. -/
private theorem homologyMap_comp_factors_inv_comp {K L : CochainComplex AddCommGrpCat.{w} ℤ}
    (f : K ⟶ L) (n : ℤ) {Z : AddCommGrpCat.{w}}
    (k : (DerivedCategory.homologyFunctor AddCommGrpCat.{w} n).obj (DerivedCategory.Q.obj L) ⟶ Z) :
    HomologicalComplex.homologyMap f n ≫
        ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{w} n).app L).inv ≫ k =
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{w} n).app K).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{w} n).map (DerivedCategory.Q.map f) ≫ k :=
  (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{w} n).inv.naturality_assoc f k

variable (R : ∀ U : OpenCoverSet X, CechSite.CechResolutionComparison.{v}
  (Opens.grothendieckTopology X) (hypercover U) (hypercover_mem_grothendieckTopology U) G J)

omit [T2Space X] [CompactSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Any Čech resolution comparison of Stacks 03AX has the canonical map `β` as its second
augmentation. -/
private theorem resolutionComparison_beta (U : OpenCoverSet X) :
    (R U).β = cechToTotalAt J U :=
  HomologicalComplex.hom_ext _ _ fun m ↦ (R U).β_f m

/-- Sheaf cohomology is the cohomology of the total Čech complex of an injective resolution:
the augmentation `α` of Stacks 03AX is a quasi-isomorphism and the sections of the resolution
compute derived sections. -/
private def totalHomologyIso (n : ℤ) (U : OpenCoverSet X) :
    (resolutionTotal U J).homology n ≅
      (CechSite.derivedSectionsFunctor.{max u v} (Opens.grothendieckTopology X)
        (⊤ : Opens X) ⋙ DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} n).obj G :=
  ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} n).app
      (resolutionTotal U J)).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).mapIso (R U).αIso.symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).mapIso
      (@asIso _ _ _ _ _ (InjectiveResolution.isIso_toRightDerived
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
          (op (⊤ : Opens X))) J))

omit [T2Space X] [CompactSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The identification of sheaf cohomology with the cohomology of the total Čech complex,
written out as a composite. -/
private theorem totalHomologyIso_hom (n : ℤ) (U : OpenCoverSet X) :
    (totalHomologyIso J R n U).hom =
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} n).app
          (resolutionTotal U J)).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).map (R U).αIso.inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).map
          (J.toRightDerived ((sheafSections (Opens.grothendieckTopology X)
            AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X)))) := rfl

omit [T2Space X] [CompactSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The identification of sheaf cohomology with the cohomology of the total Čech complex is
unchanged by passing to a refinement of the open covering. -/
private theorem totalHomologyIso_naturality (n : ℤ) {U V : OpenCoverSet X} (r : U ⟶ V) :
    HomologicalComplex.homologyMap (refinementTotalMap r J) n ≫
      (totalHomologyIso J R n V).hom = (totalHomologyIso J R n U).hom := by
  have hr : DerivedCategory.Q.map (refinementTotalMap r J) ≫ (R V).αIso.inv =
      (R U).αIso.inv := by
    apply (cancel_epi (R U).αIso.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, (R U).αIso_hom, ← DerivedCategory.Q.map_comp,
      totalAugmentation_naturality J r (R U) (R V), ← (R V).αIso_hom, Iso.hom_inv_id]
  rw [totalHomologyIso_hom, totalHomologyIso_hom, ← hr]
  refine (homologyMap_comp_factors_inv_comp _ _ _).trans ?_
  simp only [Functor.map_comp, Category.assoc]
  rfl

omit [T2Space X] [CompactSpace X]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The comparison of Stacks 09UZ out of the colimit, read on a single open covering through
the two augmentations of Stacks 03AX. -/
private theorem ι_colimitToCohomology_eq (n : ℤ) (U : OpenCoverSet X) :
    colimit.ι (cechDiagram G n) U ≫ colimitToCohomology G n =
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} n).app
          (cechComplexIntAt G U)).hom ≫
        HomologicalComplex.homologyMap (cechToTotalAt J U) n ≫
          (totalHomologyIso J R n U).hom := by
  rw [ι_colimitToCohomology]
  change (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).map
    (((CechSite.cechToDerivedSections.{v} (Opens.grothendieckTopology X) (hypercover U)
      (hypercover_mem_grothendieckTopology U)).app G).hom) = _
  rw [(R U).comparison, resolutionComparison_beta J R U]
  simp only [totalHomologyIso_hom]
  refine Eq.trans ?_ (congrArg _ (homologyMap_comp_factors_inv_comp _ _ _).symm)
  rw [Iso.hom_inv_id_assoc]
  exact (Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))

end Main

/-! ### Stacks 09V2, the isomorphism -/

section Conclusion

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]

/-- **Stacks Project, Tag 09V2.** Let `X` be a Hausdorff quasi-compact topological space and
`F` an abelian sheaf on `X`.  The canonical comparison of Stacks 09UZ from the Čech cohomology
of `X` — the colimit, over all open coverings of `X`, of the Čech cohomology of the covering —
to the sheaf cohomology of `F` is an isomorphism in every degree. -/
@[stacks 09V2 "the comparison of Stacks 09UZ is an isomorphism in every degree"]
theorem isIso_colimitToCohomology
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) (n : ℤ) :
    IsIso (colimitToCohomology G n) := by
  classical
  let J := InjectiveResolution.of G
  let R : ∀ U : OpenCoverSet X, CechSite.CechResolutionComparison.{v}
      (Opens.grothendieckTopology X) (hypercover U)
      (hypercover_mem_grothendieckTopology U) G J := fun U ↦ Classical.choice
    (CechSite.nonempty_cechResolutionComparison.{v} (Opens.grothendieckTopology X)
      (hypercover U) (hypercover_mem_grothendieckTopology U) G J)
  refine isIso_colimit_of_cocycle_descent (cechDiagram G n) (cechComplexIntAt G)
    (fun U ↦ resolutionTotal U J) (fun r ↦ (refinementComplexIntNat r).app G)
    (fun r ↦ refinementTotalMap r J) (cechToTotalAt J) n (topCover X)
    exists_common_refinement
    (fun U ↦ (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} n).app
      (cechComplexIntAt G U))
    (fun r ↦ DerivedCategory.homologyFunctorFactors_hom_naturality _ n)
    (colimitToCohomology G n) (totalHomologyIso J R n)
    (fun r ↦ totalHomologyIso_naturality J R n r) (ι_colimitToCohomology_eq J R n)
    (fun U z hz ↦ exists_cechCocycle_and_totalBoundary J U n z hz) (fun U x b hb ↦ ?_)
  have h := exists_cechBoundary_of_totalBoundary J U (n - 1)
  rw [show n - 1 + 1 = n from by omega] at h
  exact h x b hb

end Conclusion

end Stacks.Cohomology.CechRefinement

end
