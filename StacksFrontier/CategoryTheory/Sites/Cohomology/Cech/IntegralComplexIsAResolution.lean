module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The integral Čech complex is a resolution

Let `E = {U_i → U}` be a family of morphisms of a category `C` with fixed target, all of
whose finite nonempty fibre products exist. Stacks 03AT asserts that the integral Čech
complex of Stacks 03AS is exact in positive degrees: all of its homology presheaves
`H_n`, `n > 0`, vanish.

The proof is the one in the source, carried out objectwise. Evaluating the integral Čech
complex at an object `V` of `C` turns it into the alternating face map complex of the free
abelian groups on the Čech nerve of the map
`∐_i Hom(V, U_i) → Hom(V, U)`, and the homology of a presheaf complex is zero exactly when
each of its values is zero. The Čech nerve of a map of sets which is surjective onto its
image carries an extra degeneracy — the section of that map chosen on its image gives the
contracting homotopy — and the alternating face map complex of an augmented simplicial
object with an extra degeneracy is homotopy equivalent to its point, hence has vanishing
homology in positive degrees.

## Main results

* `Stacks.CechSite.integralCechComplex_homology_isZero`: every positive-degree homology
  presheaf of the integral Čech complex vanishes.

## Implementation notes

A family of morphisms with fixed target is a `PreZeroHypercover`, as in Stacks 03AM, and the
fibre products are products in the over category. Exactness is stated, as in the source, as
the vanishing of the homology presheaves, expressed by `CategoryTheory.Limits.IsZero`.

The work of the file is the chain of identifications turning the degree-`n` term of the
evaluated integral Čech complex, a direct sum over `(n+1)`-tuples of indices of free
abelian groups on `Hom`-sets, into the free abelian group on the degree-`n` term of a Čech
nerve of types, which is a wide pullback. `ULift` is applied to the evaluated complex so
that the index universe `w` of the family and the coefficient universe `a` need not be
related; the free abelian group functor is then taken at `Type (max v w a)`, and
`Stacks.CechSite.liftReflectsShortComplexHomologyZero` transfers the vanishing back.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AS](https://stacks.math.columbia.edu/tag/03AS)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

universe w v u a

namespace Stacks.CechSite

universe z b c

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀),
    HasProduct (fun a ↦ Over.mk (E.f (i a)))]

-- The comparison below is between the integral Čech simplicial object and a Čech nerve of
-- types; the two agree degreewise by unfolding the realization of a formal coproduct, so
-- both definitions must be reducible at implicit transparency for the rewriting steps
-- there to typecheck.
attribute [local implicit_reducible] FormalCoproduct.eval cechFormalCoproduct
  integralCechRealization integralCechSimplicialObject

private theorem homology_isZero_of_extraDegeneracy
    {A : Type*} [Category* A] [Abelian A]
    {Y : SimplicialObject.Augmented A} (d : Y.ExtraDegeneracy)
    (n : ℕ) (hn : 0 < n) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj Y)).homology n) :=
  IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.down ℕ) 0 (SimplicialObject.Augmented.point.obj Y)
      n (Nat.ne_of_gt hn))
    (d.homotopyEquiv.toHomologyIso n)

private noncomputable def rangeAugmentation {A B : Type z}
    (f : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (Arrow.mk f).cechNerve.obj n ⟶ (↑(Set.range f) : Type z) := by
  refine TypeCat.ofHom (fun x => ?_)
  refine ⟨WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) x,
    ⟨WidePullback.π (fun _ : Fin (n.unop.len + 1) => f) 0 x, ?_⟩⟩
  have h := WidePullback.π_arrow
    (fun _ : Fin (n.unop.len + 1) => f) (0 : Fin (n.unop.len + 1))
  simpa only [types_comp, Function.comp_apply] using congrArg (fun k => k x) h

private noncomputable def rangeAugmentedCechNerve
    {A B : Type z} (f : A ⟶ B) : SimplicialObject.Augmented (Type z) where
  left := (Arrow.mk f).cechNerve
  right := Set.range f
  hom :=
    { app := fun n => rangeAugmentation f n
      naturality := by
        intro n m g
        apply TypeCat.homEquiv.injective
        funext x
        apply Subtype.ext
        exact types_congr_hom
          (WidePullback.lift_base
            (fun _ : Fin (m.unop.len + 1) => f)
            (WidePullback.base (fun _ : Fin (n.unop.len + 1) => f))
          (fun i => WidePullback.π (fun _ : Fin (n.unop.len + 1) => f)
              (g.unop.toOrderHom i)) (by simp)) x }

private noncomputable def rangeSection {A B : Type z} (f : A ⟶ B) :
    (↑(Set.range f) : Type z) ⟶ A :=
  TypeCat.ofHom (fun b => Classical.choose b.property)

private theorem rangeSection_comp {A B : Type z} (f : A ⟶ B) :
    rangeSection f ≫ f =
      TypeCat.ofHom (Subtype.val : (↑(Set.range f) : Type z) → B) := by
  apply TypeCat.homEquiv.injective
  funext b
  exact Classical.choose_spec b.property

private theorem rangeAugmentedCechNerve_hom_app_comp {A B : Type z}
    (f : A ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (rangeAugmentedCechNerve f).hom.app n ≫
      TypeCat.ofHom (Subtype.val : (↑(Set.range f) : Type z) → B) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) := by
  apply TypeCat.homEquiv.injective
  funext x
  rfl

private theorem integralCechSimplicialObject_ι_map
    {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t)
    (i : Fin (s.unop.len + 1) → E.I₀) :
    Sigma.ι (fun j : Fin (s.unop.len + 1) → E.I₀ =>
      freeAbelianYoneda.{v, u, a}.obj
        ((∏ᶜ (fun k => Over.mk (E.f (j k)))).left)) i ≫
      (integralCechSimplicialObject.{w, v, u, a} E).map g =
    freeAbelianYoneda.{v, u, a}.map
      ((cechFormalCoproductMap E g.unop.toOrderHom.toFun).φ i).left ≫
      Sigma.ι (fun j : Fin (t.unop.len + 1) → E.I₀ =>
        freeAbelianYoneda.{v, u, a}.obj
          ((∏ᶜ (fun k => Over.mk (E.f (j k)))).left))
        ((cechFormalCoproductMap E g.unop.toOrderHom.toFun).f i) := by
  show Sigma.ι
    ((Over.forget X ⋙ freeAbelianYoneda.{v, u, a}).obj ∘
      ((cechSimplicialObject E).obj s).obj) i ≫
      Sigma.desc (fun j =>
        (Over.forget X ⋙ freeAbelianYoneda.{v, u, a}).map
          (((cechSimplicialObject E).map g).φ j) ≫
        Sigma.ι
          ((Over.forget X ⋙ freeAbelianYoneda.{v, u, a}).obj ∘
            ((cechSimplicialObject E).obj t).obj)
          (((cechSimplicialObject E).map g).f j)) = _
  convert (Sigma.ι_desc (fun j =>
    (Over.forget X ⋙ freeAbelianYoneda.{v, u, a}).map
      (((cechSimplicialObject E).map g).φ j) ≫
    Sigma.ι
      ((Over.forget X ⋙ freeAbelianYoneda.{v, u, a}).obj ∘
        ((cechSimplicialObject E).obj t).obj)
      (((cechSimplicialObject E).map g).f j)) i) using 1 <;> rfl

private theorem rangeAugmentation_comp_of_base {A B : Type z}
    (f : A ⟶ B) {n m : SimplexCategoryᵒᵖ}
    (g : (Arrow.mk f).cechNerve.obj n ⟶ (Arrow.mk f).cechNerve.obj m)
    (hg : g ≫ WidePullback.base (fun _ : Fin (m.unop.len + 1) => f) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) => f)) :
    g ≫ rangeAugmentation f m = rangeAugmentation f n := by
  apply TypeCat.homEquiv.injective
  funext x
  apply Subtype.ext
  show (rangeAugmentation f m (g x)).val = (rangeAugmentation f n x).val
  calc
    _ = WidePullback.base (fun _ : Fin (m.unop.len + 1) => f) (g x) := rfl
    _ = WidePullback.base (fun _ : Fin (n.unop.len + 1) => f) x :=
      types_congr_hom hg x
    _ = _ := rfl

private theorem rangeAugmentation_naturality {A B : Type z}
    (f : A ⟶ B) {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m) :
    (Arrow.mk f).cechNerve.map g ≫ rangeAugmentation f m =
      rangeAugmentation f n :=
  rangeAugmentation_comp_of_base f _ (WidePullback.lift_base ..)

attribute [local simp] rangeAugmentation_naturality

private theorem rangeAugmentation_δ {A B : Type z}
    (f : A ⟶ B) (n : ℕ) (i : Fin (n + 2)) :
    (Arrow.mk f).cechNerve.δ i ≫ rangeAugmentation f (Opposite.op ⦋n⦌) =
      rangeAugmentation f (Opposite.op ⦋n + 1⦌) :=
  rangeAugmentation_naturality f (SimplexCategory.δ i).op

private theorem rangeAugmentation_σ {A B : Type z}
    (f : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.σ i ≫ rangeAugmentation f (Opposite.op ⦋n + 1⦌) =
      rangeAugmentation f (Opposite.op ⦋n⦌) :=
  rangeAugmentation_naturality f (SimplexCategory.σ i).op

/-- Two points of a sigma type of families of subtypes are equal when their base points and the
underlying values of their families agree. -/
private theorem sigma_subtype_pi_ext {B K : Type*} {A : K → Type*} {P : B → ∀ k, A k → Prop}
    {s t : Σ b : B, ∀ k, {p : A k // P b k p}} (hb : s.1 = t.1)
    (h : ∀ k, (s.2 k).val = (t.2 k).val) : s = t := by
  obtain ⟨b, p⟩ := s
  obtain ⟨_, q⟩ := t
  cases hb
  exact congrArg _ (funext fun k => Subtype.ext (h k))

private noncomputable def cechNervePointEquiv {A B : Type z}
    (f : A ⟶ B) (n : ℕ) :
    ((Arrow.mk f).cechNerve.obj (Opposite.op ⦋n⦌)) ≃
      Σ b : B, ∀ _k : Fin (n + 1), {p : A // f p = b} where
  toFun x :=
    ⟨WidePullback.base (fun _ : Fin (n + 1) => f) x,
      fun k => ⟨WidePullback.π (fun _ : Fin (n + 1) => f) k x,
        types_congr_hom (WidePullback.π_arrow (fun _ : Fin (n + 1) => f) k) x⟩⟩
  invFun t :=
    (WidePullback.lift
      (TypeCat.ofHom (fun _ : PUnit => t.1))
      (fun k => TypeCat.ofHom (fun _ : PUnit => (t.2 k).val))
      (by
        intro k
        apply TypeCat.homEquiv.injective
        funext _
        exact (t.2 k).property)) PUnit.unit
  left_inv x := by
    let q := WidePullback.lift
      (TypeCat.ofHom (fun _ : PUnit => WidePullback.base (fun _ : Fin (n + 1) => f) x))
      (fun k => TypeCat.ofHom
        (fun _ : PUnit => WidePullback.π (fun _ : Fin (n + 1) => f) k x))
      (by
        intro k
        apply TypeCat.homEquiv.injective
        funext _
        exact types_congr_hom
          (WidePullback.π_arrow (fun _ : Fin (n + 1) => f) k) x)
    have hq : q = TypeCat.ofHom (fun _ : PUnit => x) := by
      apply WidePullback.hom_ext
      · intro k
        change q ≫ WidePullback.π (fun _ : Fin (n + 1) => f) k =
          TypeCat.ofHom (fun _ : PUnit => WidePullback.π (fun _ : Fin (n + 1) => f) k x)
        exact WidePullback.lift_π ..
      · change q ≫ WidePullback.base (fun _ : Fin (n + 1) => f) =
          TypeCat.ofHom (fun _ : PUnit => WidePullback.base (fun _ : Fin (n + 1) => f) x)
        exact WidePullback.lift_base ..
    change q PUnit.unit = (TypeCat.ofHom (fun _ : PUnit => x)) PUnit.unit
    exact types_congr_hom hq PUnit.unit
  right_inv t := by
    rcases t with ⟨b, p⟩
    let wq : ∀ k : Fin (n + 1),
        TypeCat.ofHom (fun _ : PUnit => (p k).val) ≫ f =
          TypeCat.ofHom (fun _ : PUnit => b) := by
      intro k
      apply TypeCat.homEquiv.injective
      funext _
      exact (p k).property
    let q := WidePullback.lift
      (TypeCat.ofHom (fun _ : PUnit => b))
      (fun k => TypeCat.ofHom (fun _ : PUnit => (p k).val))
      wq
    have hb : WidePullback.base (fun _ : Fin (n + 1) => f) (q PUnit.unit) = b := by
      have h := types_congr_hom
        (WidePullback.lift_base (fun _ : Fin (n + 1) => f)
          (TypeCat.ofHom (fun _ : PUnit => b))
          (fun k => TypeCat.ofHom (fun _ : PUnit => (p k).val)) wq) PUnit.unit
      simpa [q] using h
    have hπ (k : Fin (n + 1)) :
        WidePullback.π (fun _ : Fin (n + 1) => f) k (q PUnit.unit) = (p k).val := by
      have h := types_congr_hom
        (WidePullback.lift_π (fun _ : Fin (n + 1) => f)
          (TypeCat.ofHom (fun _ : PUnit => b))
          (fun j => TypeCat.ofHom (fun _ : PUnit => (p j).val)) wq k) PUnit.unit
      simpa [q] using h
    exact sigma_subtype_pi_ext hb hπ

private theorem cechNervePointEquiv_map {A B : Type z} (f : A ⟶ B)
    {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t)
    (y : (Arrow.mk f).cechNerve.obj s) :
    (cechNervePointEquiv f t.unop.len)
      ((Arrow.mk f).cechNerve.map g y) =
    ⟨((cechNervePointEquiv f s.unop.len) y).1,
      fun k => ((cechNervePointEquiv f s.unop.len) y).2
        (g.unop.toOrderHom k)⟩ := by
  have hb : ((cechNervePointEquiv f t.unop.len)
      ((Arrow.mk f).cechNerve.map g y)).1 =
      ((cechNervePointEquiv f s.unop.len) y).1 :=
    types_congr_hom (WidePullback.lift_base ..) y
  exact sigma_subtype_pi_ext hb fun k => types_congr_hom (WidePullback.lift_π ..) y

private noncomputable def rangeExtraDegeneracy_s {A B : Type z}
    (f : A ⟶ B) (n : ℕ) :
    (Arrow.mk f).cechNerve.obj (Opposite.op ⦋n⦌) ⟶
      (Arrow.mk f).cechNerve.obj (Opposite.op ⦋n + 1⦌) :=
  WidePullback.lift
    (WidePullback.base (fun _ : Fin (n + 1) => f))
    (Fin.cases
      (rangeAugmentation f (Opposite.op ⦋n⦌) ≫ rangeSection f)
      (fun i => WidePullback.π (fun _ : Fin (n + 1) => f) i))
    (by
      intro i
      induction i using Fin.cases with
      | zero =>
          apply TypeCat.homEquiv.injective
          funext x
          calc
            f (rangeSection f (rangeAugmentation f
                (Opposite.op ⦋n⦌) x)) =
              (rangeAugmentation f (Opposite.op ⦋n⦌) x).val :=
              types_congr_hom (rangeSection_comp f) _
            _ = WidePullback.base (fun _ : Fin (n + 1) => f) x :=
              types_congr_hom
                (rangeAugmentedCechNerve_hom_app_comp f (Opposite.op ⦋n⦌)) x
      | succ i =>
          change WidePullback.π (fun _ : Fin (n + 1) => f) i ≫ f = _
          exact WidePullback.π_arrow (fun _ : Fin (n + 1) => f) i)

private theorem rangeExtraDegeneracy_s_comp_π_zero {A B : Type z}
    (f : A ⟶ B) (n : ℕ) :
    rangeExtraDegeneracy_s f n ≫
      WidePullback.π (fun _ : Fin (n + 2) => f) 0 =
      rangeAugmentation f (Opposite.op ⦋n⦌) ≫ rangeSection f :=
  WidePullback.lift_π ..

private theorem rangeExtraDegeneracy_s_comp_π_succ {A B : Type z}
    (f : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    rangeExtraDegeneracy_s f n ≫
      WidePullback.π (fun _ : Fin (n + 2) => f) i.succ =
      WidePullback.π (fun _ : Fin (n + 1) => f) i :=
  WidePullback.lift_π ..

private theorem rangeExtraDegeneracy_s_comp_base {A B : Type z}
    (f : A ⟶ B) (n : ℕ) :
    rangeExtraDegeneracy_s f n ≫ WidePullback.base _ =
      WidePullback.base (fun _ : Fin (n + 1) => f) :=
  WidePullback.lift_base ..

attribute [local simp] rangeExtraDegeneracy_s_comp_π_zero
  rangeExtraDegeneracy_s_comp_π_succ rangeExtraDegeneracy_s_comp_base

private noncomputable def rangeExtraDegeneracy {A B : Type z}
    (f : A ⟶ B) : (rangeAugmentedCechNerve f).ExtraDegeneracy where
  s' := WidePullback.lift
    (TypeCat.ofHom (Subtype.val : (↑(Set.range f) : Type z) → B))
    (fun _ : Fin 1 => rangeSection f)
    (by intro; exact rangeSection_comp f)
  s n := rangeExtraDegeneracy_s f n
  s'_comp_ε := by
    apply TypeCat.homEquiv.injective
    funext b
    apply Subtype.ext
    change ((rangeAugmentedCechNerve f).hom.app (Opposite.op ⦋0⦌)
      (WidePullback.lift
        (TypeCat.ofHom (Subtype.val : (↑(Set.range f) : Type z) → B))
        (fun _ : Fin 1 => rangeSection f)
        (by intro; exact rangeSection_comp f) b)).val = b.val
    calc
      _ = WidePullback.base (fun _ : Fin 1 => f)
          (WidePullback.lift
            (TypeCat.ofHom (Subtype.val : (↑(Set.range f) : Type z) → B))
            (fun _ : Fin 1 => rangeSection f)
            (by intro; exact rangeSection_comp f) b) :=
        types_congr_hom
          (rangeAugmentedCechNerve_hom_app_comp f (Opposite.op ⦋0⦌)) _
      _ = b.val :=
        types_congr_hom
          (WidePullback.lift_base
            (fun _ : Fin 1 => f)
            (TypeCat.ofHom (Subtype.val : (↑(Set.range f) : Type z) → B))
            (fun _ : Fin 1 => rangeSection f)
            (by intro; exact rangeSection_comp f)) b
  s₀_comp_δ₁ := by
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    apply WidePullback.hom_ext
    · intro j
      fin_cases j
      simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_π]
    · simpa [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_base]
        using (rangeAugmentedCechNerve_hom_app_comp f (Opposite.op ⦋0⦌)).symm
  s_comp_δ₀ n := by
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    apply WidePullback.hom_ext
    · intro j
      simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_π]
    · simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_base]
  s_comp_δ n i := by
    dsimp [SimplicialObject.δ, SimplexCategory.δ]
    apply WidePullback.hom_ext
    · intro j
      induction j using Fin.cases <;>
        simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_π]
      all_goals
        simpa [rangeAugmentedCechNerve, SimplicialObject.δ, SimplexCategory.δ,
          Arrow.cechNerve_map, Category.assoc]
          using congrArg (fun h => h ≫ rangeSection f) (rangeAugmentation_δ f n i).symm
    · simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_base]
  s_comp_σ n i := by
    dsimp [SimplicialObject.σ, SimplexCategory.σ]
    apply WidePullback.hom_ext
    · intro j
      induction j using Fin.cases <;>
        simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_π]
      all_goals
        simpa [rangeAugmentedCechNerve, SimplicialObject.σ, SimplexCategory.σ,
          Arrow.cechNerve_map, Category.assoc]
          using congrArg (fun h => h ≫ rangeSection f) (rangeAugmentation_σ f n i).symm
    · simp [rangeAugmentedCechNerve, Arrow.cechNerve_map, rangeExtraDegeneracy_s,
        WidePullback.lift_base]

@[sga "4 V 1.11" "partial"]
private theorem freeAb_cechNerve_homology_isZero
    {A B : Type z} (f : A ⟶ B) (n : ℕ) (hn : 0 < n) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj AddCommGrpCat.free).obj
          (rangeAugmentedCechNerve f)))).homology n) :=
  homology_isZero_of_extraDegeneracy
    ((rangeExtraDegeneracy f).map AddCommGrpCat.free) n hn

private theorem liftReflectsShortComplexHomologyZero
    (S : ShortComplex AddCommGrpCat.{b})
    (h : IsZero ((S.map AddCommGrpCat.uliftFunctor.{c, b}).homology)) :
    IsZero S.homology :=
  IsZero.of_full_of_faithful_of_isZero AddCommGrpCat.uliftFunctor.{c, b} _
    (IsZero.of_iso h (S.mapHomologyIso AddCommGrpCat.uliftFunctor.{c, b}).symm)

private noncomputable def freeCoproductIso {I : Type w}
    (S : I → Type (max w z)) :
    (∐ fun i => AddCommGrpCat.free.obj (S i)) ≅
      AddCommGrpCat.free.obj ((i : I) × S i) :=
  (PreservesCoproduct.iso AddCommGrpCat.free S).symm ≪≫
    AddCommGrpCat.free.mapIso (Types.coproductIso S)

private noncomputable def freeUliftIso (S : Type b) :
    (AddCommGrpCat.uliftFunctor.{c, b}).obj (AddCommGrpCat.free.obj S) ≅
      AddCommGrpCat.free.obj (ULift.{c} S) :=
  (AddEquiv.ulift.trans
    (FreeAbelianGroup.equivOfEquiv (Equiv.ulift : ULift.{c} S ≃ S)).symm).toAddCommGrpIso

private noncomputable def freeYonedaUliftIso (V U : C) :
    (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
      ((freeAbelianYoneda.{v, u, a}.obj U).obj (Opposite.op V)) ≅
    AddCommGrpCat.free.obj (ULift.{w} (ULift.{a} (V ⟶ U))) :=
  freeUliftIso (ULift.{a} (V ⟶ U))

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})] in
private theorem freeYonedaUliftIso_inv_of (V U : C)
    (x : ULift.{w} (ULift.{a} (V ⟶ U))) :
    (freeYonedaUliftIso.{w, v, u, a} V U).inv (FreeAbelianGroup.of x) =
      ⟨FreeAbelianGroup.of x.down⟩ := by
  show ULift.up ((FreeAbelianGroup.equivOfEquiv
    (Equiv.ulift : ULift.{w} (ULift.{a} (V ⟶ U)) ≃
      ULift.{a} (V ⟶ U))) (FreeAbelianGroup.of x)) = _
  simp [FreeAbelianGroup.equivOfEquiv]
  rfl

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})] in
private theorem freeAbelianYoneda_map_of (V U U' : C) (f : U ⟶ U')
    (x : ULift.{a} (V ⟶ U)) :
    ((freeAbelianYoneda.{v, u, a}.map f).app (Opposite.op V))
      (FreeAbelianGroup.of x) =
      FreeAbelianGroup.of (⟨x.down ≫ f⟩ : ULift.{a} (V ⟶ U')) := by
  show (AddCommGrpCat.free.map ((uliftYoneda.{a}.map f).app (Opposite.op V)))
    (FreeAbelianGroup.of x) = _
  simp only [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
  rfl

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})] in
private theorem freeYonedaUliftIso_hom_of (V U : C)
    (x : ULift.{a} (V ⟶ U)) :
    (freeYonedaUliftIso.{w, v, u, a} V U).hom
      (⟨FreeAbelianGroup.of x⟩ : ULift.{w} (FreeAbelianGroup (ULift.{a} (V ⟶ U)))) =
      FreeAbelianGroup.of (⟨x⟩ : ULift.{w} (ULift.{a} (V ⟶ U))) := by
  show ((FreeAbelianGroup.equivOfEquiv
    (Equiv.ulift : ULift.{w} (ULift.{a} (V ⟶ U)) ≃
      ULift.{a} (V ⟶ U))).symm (FreeAbelianGroup.of x)) = _
  simp [FreeAbelianGroup.equivOfEquiv]

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})] in
private theorem freeYonedaUliftIso_map (V U U' : C) (f : U ⟶ U') :
    (freeYonedaUliftIso.{w, v, u, a} V U).inv ≫
      (AddCommGrpCat.uliftFunctor.{w, max v a}).map
        ((freeAbelianYoneda.{v, u, a}.map f).app (Opposite.op V)) =
    AddCommGrpCat.free.map (TypeCat.ofHom
      (fun x : ULift.{w} (ULift.{a} (V ⟶ U)) =>
        (⟨⟨x.down.down ≫ f⟩⟩ : ULift.{w} (ULift.{a} (V ⟶ U'))))) ≫
      (freeYonedaUliftIso.{w, v, u, a} V U').inv := by
  apply (cancel_mono (freeYonedaUliftIso V U').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  show (freeYonedaUliftIso V U').hom
      (((AddCommGrpCat.uliftFunctor.{w, max v a}).map
        ((freeAbelianYoneda.{v, u, a}.map f).app (Opposite.op V)))
          ((freeYonedaUliftIso V U).inv (FreeAbelianGroup.of x))) =
    FreeAbelianGroup.of (⟨⟨x.down.down ≫ f⟩⟩ :
      ULift.{w} (ULift.{a} (V ⟶ U')))
  rw [freeYonedaUliftIso_inv_of]
  show (freeYonedaUliftIso V U').hom
      (⟨((freeAbelianYoneda.{v, u, a}.map f).app (Opposite.op V))
        (FreeAbelianGroup.of x.down)⟩) = _
  rw [freeAbelianYoneda_map_of]
  exact freeYonedaUliftIso_hom_of V U' _

private theorem iso_inv_ι_mapIso {I : Type w} {D : Type b} [Category.{c} D]
    [HasCoproductsOfShape I D] {F G : I → D} (p : ∀ i, F i ≅ G i) (i : I) :
    (p i).inv ≫ Sigma.ι F i ≫ (Sigma.mapIso p).hom = Sigma.ι G i := by
  simp

attribute [local simp] iso_inv_ι_mapIso

private theorem freeCoproductIso_ι_of {I : Type w}
    (S : I → Type (max w z)) (i : I) (x : S i) :
    (freeCoproductIso S).hom
      ((Sigma.ι (fun i => AddCommGrpCat.free.obj (S i)) i) (FreeAbelianGroup.of x)) =
        FreeAbelianGroup.of ⟨i, x⟩ := by
  have h : Sigma.ι (fun i => AddCommGrpCat.free.obj (S i)) i ≫
      (freeCoproductIso S).hom =
      AddCommGrpCat.free.map (TypeCat.ofHom (fun y : S i => ⟨i, y⟩)) := by
    simp only [freeCoproductIso, Iso.trans_hom, Iso.symm_hom,
      PreservesCoproduct.inv_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ι_comp_sigmaComparison, ← Functor.map_comp,
      Types.coproductIso_ι_comp_hom]
  have h' := CategoryTheory.congr_fun h (FreeAbelianGroup.of x)
  have hc :
      (Sigma.ι (fun i => AddCommGrpCat.free.obj (S i)) i ≫ (freeCoproductIso S).hom)
          (FreeAbelianGroup.of x) =
        (freeCoproductIso S).hom
          ((Sigma.ι (fun i => AddCommGrpCat.free.obj (S i)) i) (FreeAbelianGroup.of x)) := rfl
  rw [hc] at h'
  have hf : (TypeCat.ofHom (fun y : S i => ⟨i, y⟩) : S i ⟶ (Σ i, S i)) x =
      ⟨i, x⟩ := rfl
  simpa only [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, hf] using h'

private theorem homology_isZero_of_pointwise
    {J : Type*} [Category* J] {A : Type*} [Category* A] [Abelian A]
    (K : ChainComplex (J ⥤ A) ℕ) (n : ℕ)
    (h : ∀ j : J,
      IsZero (((K.sc n).map ((evaluation J A).obj j)).homology)) :
    IsZero (K.homology n) := by
  apply (Functor.isZero_iff _).2
  intro j
  exact IsZero.of_iso (h j)
    ((K.sc n).mapHomologyIso ((evaluation J A).obj j)).symm

private def cechLiftMap (V : C) :
    (Σ i : E.I₀, V ⟶ E.X i) ⟶ ULift.{w} (V ⟶ X) :=
  TypeCat.ofHom (fun ⟨i, g⟩ => ⟨g ≫ E.f i⟩)

private def cechLiftMapHigh (V : C) :
    (ULift.{a} (Σ i : E.I₀, V ⟶ E.X i) : Type (max w v a)) ⟶
      (ULift.{max w a} (V ⟶ X) : Type (max w v a)) :=
  TypeCat.ofHom (fun p => ⟨p.down.2 ≫ E.f p.down.1⟩)

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))] in
private theorem freeAb_cechLiftMapHigh_homology_isZero
    (V : C) (n : ℕ) (hn : 0 < n) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj AddCommGrpCat.free).obj
          (rangeAugmentedCechNerve (cechLiftMapHigh E V))))).homology n) :=
  freeAb_cechNerve_homology_isZero (cechLiftMapHigh E V) n hn

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))] in
private theorem freeAb_cechLiftMap_homology_isZero (V : C) (n : ℕ) (hn : 0 < n) :
    IsZero ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj AddCommGrpCat.free).obj
          (rangeAugmentedCechNerve (cechLiftMap E V))))).homology n) :=
  freeAb_cechNerve_homology_isZero (cechLiftMap E V) n hn

private noncomputable def homFiniteFiberProductEquiv (V : C) (n : ℕ)
    (i : Fin (n + 1) → E.I₀) :
    (V ⟶ (∏ᶜ (fun a => Over.mk (E.f (i a)))).left) ≃
      Σ φ : V ⟶ X, ∀ a : Fin (n + 1),
        {g : V ⟶ E.X (i a) // g ≫ E.f (i a) = φ} where
  toFun m :=
    ⟨m ≫ (∏ᶜ (fun a => Over.mk (E.f (i a)))).hom,
      fun a =>
        ⟨m ≫ (Pi.π (fun a => Over.mk (E.f (i a))) a).left, by
          have h := Over.w (Pi.π (fun a => Over.mk (E.f (i a))) a)
          change (Pi.π (fun a => Over.mk (E.f (i a))) a).left ≫ E.f (i a) =
            (∏ᶜ (fun a => Over.mk (E.f (i a)))).hom at h
          simpa only [Category.assoc] using congrArg (fun k => m ≫ k) h⟩⟩
  invFun t :=
    ((Pi.lift (fun a =>
      (Over.homMk (t.2 a).val (t.2 a).property :
        Over.mk t.1 ⟶ Over.mk (E.f (i a))))) :
      Over.mk t.1 ⟶ ∏ᶜ (fun a => Over.mk (E.f (i a)))).left
  left_inv m := by
    let q : Over.mk (m ≫ (∏ᶜ (fun a => Over.mk (E.f (i a)))).hom) ⟶
        ∏ᶜ (fun a => Over.mk (E.f (i a))) := Over.homMk m rfl
    have h : Pi.lift (fun a => Over.homMk
        (m ≫ (Pi.π (fun a => Over.mk (E.f (i a))) a).left)
        (by
          have h := Over.w (Pi.π (fun a => Over.mk (E.f (i a))) a)
          change (Pi.π (fun a => Over.mk (E.f (i a))) a).left ≫ E.f (i a) =
            (∏ᶜ (fun a => Over.mk (E.f (i a)))).hom at h
          change (m ≫ (Pi.π (fun a => Over.mk (E.f (i a))) a).left) ≫
            E.f (i a) = m ≫ (∏ᶜ (fun a => Over.mk (E.f (i a)))).hom
          simpa only [Category.assoc] using congrArg (fun k => m ≫ k) h)) = q := by
      apply Pi.hom_ext
      intro a
      ext
      simp [q]
    exact congrArg Over.Hom.left h
  right_inv t := by
    rcases t with ⟨φ, g⟩
    let q : Over.mk φ ⟶ ∏ᶜ (fun a => Over.mk (E.f (i a))) :=
      Pi.lift (fun a => Over.homMk (g a).val (g a).property)
    have hφ : q.left ≫ (∏ᶜ (fun a => Over.mk (E.f (i a)))).hom = φ := Over.w q
    dsimp only
    refine sigma_subtype_pi_ext ?_ fun a => ?_
    · exact hφ
    · change (q ≫ Pi.π (fun a => Over.mk (E.f (i a))) a).left = (g a).val
      rw [Pi.lift_comp_π]
      rfl

private noncomputable def cechSimplexEquiv (V : C) (n : ℕ) :
    (Σ i : Fin (n + 1) → E.I₀,
      V ⟶ (∏ᶜ (fun a => Over.mk (E.f (i a)))).left) ≃
      Σ φ : V ⟶ X, ∀ _a : Fin (n + 1),
        {p : Σ j : E.I₀, V ⟶ E.X j // p.2 ≫ E.f p.1 = φ} where
  toFun s :=
    let t := homFiniteFiberProductEquiv E V n s.1 s.2
    ⟨t.1, fun a => ⟨⟨s.1 a, (t.2 a).val⟩, (t.2 a).property⟩⟩
  invFun t :=
    let i : Fin (n + 1) → E.I₀ := fun a => (t.2 a).val.1
    let g : ∀ a : Fin (n + 1),
        {h : V ⟶ E.X (i a) // h ≫ E.f (i a) = t.1} :=
      fun a => ⟨(t.2 a).val.2, (t.2 a).property⟩
    ⟨i, (homFiniteFiberProductEquiv E V n i).symm ⟨t.1, g⟩⟩
  left_inv s := by
    rcases s with ⟨i, m⟩
    dsimp
    simp
  right_inv t := by
    rcases t with ⟨φ, g⟩
    dsimp
    simp only [Sigma.mk.injEq, Equiv.apply_symm_apply, true_and]
    rw [Equiv.apply_symm_apply]

private noncomputable def cechSimplexEquivHigh (V : C) (n : ℕ) :
    (Σ i : Fin (n + 1) → E.I₀,
      ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) ≃
      Σ φ : ULift.{max w a} (V ⟶ X), ∀ _k : Fin (n + 1),
        {p : ULift.{a} (Σ j : E.I₀, V ⟶ E.X j) // cechLiftMapHigh E V p = φ} where
  toFun s :=
    let t := cechSimplexEquiv E V n ⟨s.1, s.2.down⟩
    ⟨⟨t.1⟩, fun k => ⟨⟨(t.2 k).val⟩,
      congrArg ULift.up (t.2 k).property⟩⟩
  invFun t :=
    let p : Σ φ : V ⟶ X, ∀ k : Fin (n + 1),
        {q : Σ j : E.I₀, V ⟶ E.X j // q.2 ≫ E.f q.1 = φ} :=
      ⟨t.1.down, fun k => ⟨(t.2 k).val.down,
        congrArg ULift.down (t.2 k).property⟩⟩
    let s := (cechSimplexEquiv E V n).symm p
    ⟨s.1, ⟨s.2⟩⟩
  left_inv s := by
    rcases s with ⟨i, m⟩
    let t := cechSimplexEquiv E V n ⟨i, m.down⟩
    have ht :
        (⟨t.1, fun k => ⟨(t.2 k).val, (t.2 k).property⟩⟩ :
          Σ φ : V ⟶ X, ∀ k : Fin (n + 1),
            {p : Σ j : E.I₀, V ⟶ E.X j // p.2 ≫ E.f p.1 = φ}) = t := rfl
    dsimp only [t] at ht
    dsimp
    rw [ht]
    have h := (cechSimplexEquiv E V n).left_inv ⟨i, m.down⟩
    cases m with
    | up m =>
        simpa using congrArg
          (fun s : Σ i : Fin (n + 1) → E.I₀,
            V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left =>
              (⟨s.1, ⟨s.2⟩⟩ : Σ i : Fin (n + 1) → E.I₀,
                ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left))) h
  right_inv t := by
    rcases t with ⟨φ, g⟩
    let p : Σ ψ : V ⟶ X, ∀ k : Fin (n + 1),
        {q : Σ j : E.I₀, V ⟶ E.X j // q.2 ≫ E.f q.1 = ψ} :=
      ⟨φ.down, fun k => ⟨(g k).val.down,
        congrArg ULift.down (g k).property⟩⟩
    have hp : (cechSimplexEquiv E V n) ((cechSimplexEquiv E V n).symm p) = p :=
      Equiv.apply_symm_apply _ _
    dsimp
    rw [hp]

private noncomputable def cechSimplexNerveEquivHigh (V : C) (n : ℕ) :
    (Σ i : Fin (n + 1) → E.I₀,
      ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) ≃
      ((Arrow.mk (cechLiftMapHigh E V)).cechNerve.obj (Opposite.op ⦋n⦌)) :=
  (cechSimplexEquivHigh E V n).trans
    (cechNervePointEquiv (cechLiftMapHigh E V) n).symm

omit [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})] in
private theorem cechSimplexNerveEquivHigh_map (V : C)
    {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t)
    (i : Fin (s.unop.len + 1) → E.I₀)
    (x : ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) :
    ((Arrow.mk (cechLiftMapHigh E V)).cechNerve.map g)
      (cechSimplexNerveEquivHigh E V s.unop.len ⟨i, x⟩) =
    cechSimplexNerveEquivHigh E V t.unop.len
      ⟨(cechFormalCoproductMap E g.unop.toOrderHom.toFun).f i,
        ⟨x.down ≫
          ((cechFormalCoproductMap E g.unop.toOrderHom.toFun).φ i).left⟩⟩ := by
  apply (cechNervePointEquiv (cechLiftMapHigh E V) t.unop.len).injective
  rw [cechNervePointEquiv_map]
  simp only [cechSimplexNerveEquivHigh, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [Equiv.apply_symm_apply]
  show (⟨((cechSimplexEquivHigh E V s.unop.len) ⟨i, x⟩).1,
      fun k => ((cechSimplexEquivHigh E V s.unop.len) ⟨i, x⟩).2
        (g.unop.toOrderHom k)⟩ : _) =
      (cechSimplexEquivHigh E V t.unop.len) _
  let q := cechFormalCoproductMap E g.unop.toOrderHom.toFun
  have hb : ((cechSimplexEquivHigh E V s.unop.len) ⟨i, x⟩).1 =
      ((cechSimplexEquivHigh E V t.unop.len)
        ⟨q.f i, ⟨x.down ≫ (q.φ i).left⟩⟩).1 := by
    let : HasProduct (fun k : Fin (t.unop.len + 1) =>
        Over.mk (E.f ((q.f i) k))) :=
      (inferInstance : ∀ (n : ℕ) (j : Fin (n + 1) → E.I₀),
        HasProduct (fun k => Over.mk (E.f (j k)))) t.unop.len (q.f i)
    show (⟨x.down ≫ (∏ᶜ (fun k => Over.mk (E.f (i k)))).hom⟩ :
      ULift.{max w a} (V ⟶ X)) =
      ⟨(x.down ≫ (q.φ i).left) ≫
        (∏ᶜ (fun k => Over.mk (E.f ((q.f i) k)))).hom⟩
    apply congrArg ULift.up
    have hq : (q.φ i).left ≫
        (∏ᶜ (fun k => Over.mk (E.f ((q.f i) k)))).hom =
        (∏ᶜ (fun k => Over.mk (E.f (i k)))).hom := Over.w (q.φ i)
    calc
      x.down ≫ (∏ᶜ (fun k => Over.mk (E.f (i k)))).hom =
          x.down ≫ ((q.φ i).left ≫
            (∏ᶜ (fun k => Over.mk (E.f ((q.f i) k)))).hom) :=
        congrArg (fun h => x.down ≫ h) hq.symm
      _ = _ := (Category.assoc _ _ _).symm
  refine sigma_subtype_pi_ext hb fun k => ?_
  let : HasProduct (fun k : Fin (t.unop.len + 1) =>
      Over.mk (E.f ((q.f i) k))) :=
    (inferInstance : ∀ (n : ℕ) (j : Fin (n + 1) → E.I₀),
      HasProduct (fun k => Over.mk (E.f (j k)))) t.unop.len (q.f i)
  have hπ (k : Fin (t.unop.len + 1)) :
      (q.φ i).left ≫
        (Pi.π (fun k => Over.mk (E.f ((q.f i) k))) k).left =
      (Pi.π (fun k => Over.mk (E.f (i k))) (g.unop.toOrderHom k)).left := by
    show (Pi.lift (fun k => Pi.π (fun j => Over.mk (E.f (i j)))
      (g.unop.toOrderHom k)) ≫
      Pi.π (fun k => Over.mk (E.f ((q.f i) k))) k).left = _
    exact congrArg Over.Hom.left (Pi.lift_comp_π ..)
  show (⟨⟨i (g.unop.toOrderHom k),
      x.down ≫ (Pi.π (fun j => Over.mk (E.f (i j)))
        (g.unop.toOrderHom k)).left⟩⟩ :
      ULift.{a} (Σ j : E.I₀, V ⟶ E.X j)) =
    ⟨⟨(q.f i) k,
      (x.down ≫ (q.φ i).left) ≫
        (Pi.π (fun j => Over.mk (E.f ((q.f i) j))) k).left⟩⟩
  apply congrArg ULift.up
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  show x.down ≫ (Pi.π (fun j => Over.mk (E.f (i j)))
      (g.unop.toOrderHom k)).left =
    (x.down ≫ (q.φ i).left) ≫
      (Pi.π (fun j => Over.mk (E.f ((q.f i) j))) k).left
  exact (congrArg (fun h => x.down ≫ h) (hπ k).symm).trans
    (Category.assoc _ _ _).symm

private noncomputable def integralCechTermCoproductIso (V : C) (n : ℕ) :
    (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
      (((integralCechSimplicialObject.{w, v, u, a} E).obj
        (Opposite.op ⦋n⦌)).obj (Opposite.op V)) ≅
    ∐ fun i : Fin (n + 1) → E.I₀ =>
      (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
        ((freeAbelianYoneda.{v, u, a}.obj
          ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).obj (Opposite.op V)) := by
  let F : (Fin (n + 1) → E.I₀) → Cᵒᵖ ⥤ AddCommGrpCat.{max v a} :=
    fun i => freeAbelianYoneda.obj
      ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)
  let ev := (evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj (Opposite.op V)
  let : ∀ (A B : Cᵒᵖ), HasProductsOfShape (A ⟶ B) AddCommGrpCat.{max v a} :=
    by infer_instance
  let : PreservesColimit (Discrete.functor F) ev := inferInstance
  let e : Discrete.functor (fun i => ev.obj (F i)) ≅ Discrete.functor F ⋙ ev :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro A B f
      rcases A with ⟨A⟩
      rcases B with ⟨B⟩
      rcases f with ⟨h⟩
      cases h
      rfl)
  letI : HasCoproduct (fun i => ev.obj (F i)) := hasColimit_of_iso e
  let T := AddCommGrpCat.uliftFunctor.{w, max v a}
  change T.obj (ev.obj (∐ F)) ≅ ∐ fun i => T.obj (ev.obj (F i))
  exact T.mapIso (PreservesCoproduct.iso ev F) ≪≫
    PreservesCoproduct.iso T (fun i => ev.obj (F i))

private noncomputable def integralCechTermFreeIso (V : C) (n : ℕ) :
    (∐ fun i : Fin (n + 1) → E.I₀ =>
      (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
        ((freeAbelianYoneda.{v, u, a}.obj
          ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).obj (Opposite.op V))) ≅
    ∐ fun i : Fin (n + 1) → E.I₀ =>
      AddCommGrpCat.free.obj
        (ULift.{w} (ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left))) :=
  Sigma.mapIso (fun i =>
    freeYonedaUliftIso V ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left))

private noncomputable def integralCechTermSigmaIso (V : C) (n : ℕ) :
    (∐ fun i : Fin (n + 1) → E.I₀ =>
      AddCommGrpCat.free.obj
        (ULift.{w} (ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)))) ≅
    AddCommGrpCat.free.obj
      (Σ i : Fin (n + 1) → E.I₀,
        ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) := by
  let S : (Fin (n + 1) → E.I₀) → Type (max w v a) :=
    fun i => ULift.{w} (ULift.{a}
      (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left))
  let e : (Σ i, S i) ≃
      (Σ i : Fin (n + 1) → E.I₀,
        ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) :=
    Equiv.sigmaCongrRight (fun _ => Equiv.ulift)
  change (∐ fun i => AddCommGrpCat.free.obj (S i)) ≅
    AddCommGrpCat.free.obj _
  exact freeCoproductIso S ≪≫ AddCommGrpCat.free.mapIso e.toIso

private noncomputable def integralCechTermNerveIso (V : C) (n : ℕ) :
    (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
      (((integralCechSimplicialObject.{w, v, u, a} E).obj
        (Opposite.op ⦋n⦌)).obj (Opposite.op V)) ≅
    AddCommGrpCat.free.{max (max v w) a}.obj
      ((Arrow.mk (cechLiftMapHigh.{w, v, u, a} E V)).cechNerve.obj
        (Opposite.op ⦋n⦌)) :=
  integralCechTermCoproductIso E V n ≪≫
    integralCechTermFreeIso E V n ≪≫
      integralCechTermSigmaIso E V n ≪≫
        AddCommGrpCat.free.{max (max v w) a}.mapIso
          (cechSimplexNerveEquivHigh.{w, v, u, a} E V n).toIso

private theorem integralCechTermCoproductIso_inv_ι (V : C) (n : ℕ)
    (i : Fin (n + 1) → E.I₀) :
    Sigma.ι (fun i : Fin (n + 1) → E.I₀ =>
      (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
        ((freeAbelianYoneda.{v, u, a}.obj
          ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).obj (Opposite.op V))) i ≫
      (integralCechTermCoproductIso E V n).inv =
    (AddCommGrpCat.uliftFunctor.{w, max v a}).map
      ((Sigma.ι (fun i : Fin (n + 1) → E.I₀ =>
        freeAbelianYoneda.{v, u, a}.obj
          ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) i).app (Opposite.op V)) := by
  let F : (Fin (n + 1) → E.I₀) → Cᵒᵖ ⥤ AddCommGrpCat.{max v a} :=
    fun j => freeAbelianYoneda.obj
      ((∏ᶜ (fun k => Over.mk (E.f (j k)))).left)
  let ev := (evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj (Opposite.op V)
  let : ∀ (A B : Cᵒᵖ), HasProductsOfShape (A ⟶ B) AddCommGrpCat.{max v a} :=
    by infer_instance
  let : PreservesColimit (Discrete.functor F) ev := inferInstance
  let e : Discrete.functor (fun j => ev.obj (F j)) ≅ Discrete.functor F ⋙ ev :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro A B f
      rcases A with ⟨A⟩
      rcases B with ⟨B⟩
      rcases f with ⟨h⟩
      cases h
      rfl)
  let : HasCoproduct (fun j => ev.obj (F j)) := hasColimit_of_iso e
  let T := AddCommGrpCat.uliftFunctor.{w, max v a}
  show Sigma.ι (fun j => T.obj (ev.obj (F j))) i ≫
      (T.mapIso (PreservesCoproduct.iso ev F) ≪≫
        PreservesCoproduct.iso T (fun j => ev.obj (F j))).inv =
      T.map (ev.map (Sigma.ι F i))
  simp only [Iso.trans_inv, Functor.mapIso_inv,
    PreservesCoproduct.inv_hom]
  rw [← Category.assoc, ι_comp_sigmaComparison, ← Functor.map_comp,
    ι_comp_sigmaComparison]

private theorem integralCechTermNerveIso_ι (V : C) (n : ℕ)
    (i : Fin (n + 1) → E.I₀) :
    (freeYonedaUliftIso V
      ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).inv ≫
      Sigma.ι (fun i : Fin (n + 1) → E.I₀ =>
        (AddCommGrpCat.uliftFunctor.{w, max v a}).obj
          ((freeAbelianYoneda.{v, u, a}.obj
            ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).obj (Opposite.op V))) i ≫
      (integralCechTermCoproductIso E V n).inv ≫
      (integralCechTermNerveIso E V n).hom =
    AddCommGrpCat.free.map (TypeCat.ofHom (fun x : ULift.{w}
      (ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (i k)))).left)) =>
      cechSimplexNerveEquivHigh E V n ⟨i, x.down⟩)) := by
  simp only [integralCechTermNerveIso, Iso.trans_hom]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  unfold integralCechTermFreeIso
  conv_lhs =>
    arg 1
    arg 1
    rw [Category.assoc]
  rw [Sigma.ι_mapIso_hom]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  dsimp only [integralCechTermSigmaIso]
  let S : (Fin (n + 1) → E.I₀) → Type (max w v a) :=
    fun j => ULift.{w} (ULift.{a}
      (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (j k)))).left))
  let e : (Σ j, S j) ≃
      (Σ j : Fin (n + 1) → E.I₀,
        ULift.{a} (V ⟶ (∏ᶜ (fun k => Over.mk (E.f (j k)))).left)) :=
    Equiv.sigmaCongrRight (fun _ => Equiv.ulift)
  show (AddCommGrpCat.free.map (cechSimplexNerveEquivHigh E V n).toIso.hom)
      ((AddCommGrpCat.free.map e.toIso.hom)
        ((freeCoproductIso S).hom
          ((Sigma.ι (fun j => AddCommGrpCat.free.obj (S j)) i)
            (FreeAbelianGroup.of x)))) =
      FreeAbelianGroup.of (cechSimplexNerveEquivHigh E V n ⟨i, x.down⟩)
  rw [freeCoproductIso_ι_of]
  simp only [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of,
    Equiv.toIso_hom_hom_apply]
  rfl

private noncomputable def evaluatedIntegralCechSimplicialIso (V : C) :
    ((SimplicialObject.whiskering _ _).obj
      (((evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj (Opposite.op V)) ⋙
        AddCommGrpCat.uliftFunctor.{w, max v a})).obj
      (integralCechSimplicialObject.{w, v, u, a} E) ≅
    ((SimplicialObject.whiskering _ _).obj AddCommGrpCat.free.{max (max v w) a}).obj
      ((Arrow.mk (cechLiftMapHigh.{w, v, u, a} E V)).cechNerve) :=
  NatIso.ofComponents
    (fun s => integralCechTermNerveIso E V s.unop.len)
    (by
      intro s t g
      apply (cancel_epi (integralCechTermCoproductIso E V s.unop.len).inv).mp
      apply Sigma.hom_ext
      intro i
      apply (cancel_epi (freeYonedaUliftIso V
        ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).inv).mp
      conv_lhs =>
        arg 2
        rw [← Category.assoc]
      rw [integralCechTermCoproductIso_inv_ι]
      have hmap := congrArg
        (fun k => (AddCommGrpCat.uliftFunctor.{w, max v a}).map
          (k.app (Opposite.op V)))
        (integralCechSimplicialObject_ι_map E g i)
      simp only [NatTrans.comp_app, Functor.map_comp] at hmap
      have hmap' := congrArg (fun k =>
        (freeYonedaUliftIso V
          ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)).inv ≫ k ≫
          (integralCechTermNerveIso E V t.unop.len).hom) hmap
      refine hmap'.trans ?_
      simp only [Category.assoc]
      rw [← integralCechTermCoproductIso_inv_ι E V t.unop.len
        ((cechFormalCoproductMap E g.unop.toOrderHom.toFun).f i)]
      simp only [← Category.assoc]
      rw [freeYonedaUliftIso_map V
        ((∏ᶜ (fun k => Over.mk (E.f (i k)))).left)
        ((∏ᶜ (fun k => Over.mk (E.f
          ((cechFormalCoproductMap E g.unop.toOrderHom.toFun).f i k)))).left)
        ((cechFormalCoproductMap E g.unop.toOrderHom.toFun).φ i).left]
      simp only [Category.assoc, integralCechTermNerveIso_ι]
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro x
      simp only [SimplexCategory.mk_len, Opposite.op_unop, Arrow.cechNerve_obj,
        Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom, AddCommGrpCat.free_obj_coe,
        OrderHom.toFun_eq_coe, AddCommGrpCat.free_map, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
        Functor.whiskeringRight_obj_obj, Functor.comp_obj, Functor.comp_map,
        Arrow.cechNerve_map]
      exact (congrArg FreeAbelianGroup.of
        (cechSimplexNerveEquivHigh_map E V g i ⟨x.down.down⟩)).symm)

private noncomputable def evaluatedIntegralCechComplexIso (V : C) :
    ((AddCommGrpCat.uliftFunctor.{w, max v a}).mapHomologicalComplex _).obj
      ((Functor.mapHomologicalComplex
        ((evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj (Opposite.op V)) _).obj
          (integralCechComplex.{w, v, u, a} E)) ≅
    AlgebraicTopology.AlternatingFaceMapComplex.obj
      (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering _ _).obj
          AddCommGrpCat.free).obj
            (rangeAugmentedCechNerve (cechLiftMapHigh.{w, v, u, a} E V)))) := by
  let ev := (evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj (Opposite.op V)
  let T := AddCommGrpCat.uliftFunctor.{w, max v a}
  let Y := integralCechSimplicialObject.{w, v, u, a} E
  let F := (SimplicialObject.whiskering _ _).obj ev
  change (T.mapHomologicalComplex _).obj
      ((ev.mapHomologicalComplex _).obj ((AlgebraicTopology.alternatingFaceMapComplex _).obj Y)) ≅ _
  exact ((T.mapHomologicalComplex _).mapIso
      ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso ev).app Y))
    ≪≫ (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso T).app
      (F.obj Y)
    ≪≫ (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (evaluatedIntegralCechSimplicialIso E V)

/-- The homology presheaves of the integral Čech chain complex vanish in every positive degree:
the complex of abelian presheaves is exact in all degrees except `0`. The degree-`0` term of
`integralCechComplex` is `⊕_{i₀} Z_{U_{i₀}}`, so the hypothesis `0 < n` is exactly "all degrees
except `0`", and nothing is asserted at `n = 0`. -/
@[stacks 03AT, stacks 03OQ, sga "4 V 1.11" "partial"]
public theorem integralCechComplex_homology_isZero (n : ℕ) (hn : 0 < n) :
    IsZero ((integralCechComplex.{w, v, u, a} E).homology n) := by
  apply homology_isZero_of_pointwise (integralCechComplex.{w, v, u, a} E) n
  intro V
  apply liftReflectsShortComplexHomologyZero.{max v a, w}
  let ev := (evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj V
  let T := AddCommGrpCat.uliftFunctor.{w, max v a}
  let K := integralCechComplex.{w, v, u, a} E
  show IsZero (((T.mapHomologicalComplex _).obj
    ((ev.mapHomologicalComplex _).obj K)).homology n)
  exact IsZero.of_iso
    (freeAb_cechLiftMapHigh_homology_isZero.{w, v, u, a} E V.unop n hn)
    (HomologicalComplex.homologyMapIso
      (evaluatedIntegralCechComplexIso.{w, v, u, a} E V.unop) n)

end Stacks.CechSite

end
