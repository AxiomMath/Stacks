module

public import StacksFrontier.CategoryTheory.Triangulated.CompactObjectsFromCoyoneda
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.CoproductK
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaLemma

/-!
# A morphism from a representable module into a direct sum factors through a finite subsum

Let `C` be a differential graded category over a commutative ring `R`, let `B` be an object of
`C` and let `h_B = C(-, B)` be the representable right differential graded module. For a family
`M : α → ` of right differential graded modules indexed by a type of the universe of the
morphism modules of `C`, the canonical map

`⨁ a, Hom_{K(Mod^dg(C))}(h_B, M a) ⟶ Hom_{K(Mod^dg(C))}(h_B, ⊕ a, M a)`

is bijective: a morphism from `h_B` into a direct sum factors through a finite subsum, and in
exactly one way. That is the compactness of `h_B`, in the shape
`CategoryTheory.cofanMap`, and it is the only thing a representable module contributes to
[Stacks, Tag 09LK].

Both halves are the Yoneda lemma `DGCategory.yonedaEval` together with the fact that an element
of a direct sum has finite support. Evaluation at the identity of `B` identifies the degree-`p`
homogeneous morphisms `h_B ⟶ N` with the degree-`p` part of `N` at `B`, compatibly with the
differentials; for `N` the direct sum, that part is `⨁ a, (M a).obj B p` and the differential
is componentwise. So a closed morphism `h_B ⟶ ⊕ M` is a finitely supported family of closed
elements, which gives the surjectivity, and a nullhomotopy of such a family is a single element
of degree `-1`, again finitely supported, whose components are nullhomotopies of the
components, which gives the injectivity.

## Main results

* `DGCategory.RightModule.bijective_cofanMap_coprodCofan`: the canonical map from the direct
  sum of the morphism groups into the morphism group of the direct sum is bijective.
* `DGCategory.RightModule.mk_sum`: a finite sum of classes of cocycles is the class of the sum
  of the cocycles.

## Implementation notes

The additive structure of the homotopy category is `DGCategory.homotopyPreadditive`, which is
not registered as an instance where it is built; it is registered here for the homotopy
category of `Mod^dg(C)`, where nothing competes with it. Its two characterizations
`DGCategory.homotopyPreadditive_mk_add` and `DGCategory.homotopyPreadditive_zero` are the only
facts about it that are used.

An element of `(coprod M).obj x i` is an element of `⨁ a, (M a).obj x i`, but only at default
transparency: `DGCategory.RightModule.coprod` unfolds for unification and not for the coercion
that reads an element of a direct sum as a function on the index type. Every element whose
components are taken is therefore introduced at the direct-sum type by an `obtain`, after which
the component maps are reflexivity.
-/

@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite DirectSum

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- The homotopy category of right differential graded `C`-modules is preadditive: this is
`DGCategory.homotopyPreadditive`, registered as an instance where no other additive structure
competes with it. -/
noncomputable instance preadditiveRightModuleHomotopyCategory :
    Preadditive (rightModuleCategory.{w} C).K :=
  homotopyPreadditive _

namespace RightModule

attribute [local implicit_reducible] DGCategory.K

/-! ### Finite sums of cocycles and of their classes -/

section Sums

variable {X Y : (rightModuleCategory.{w} C).K} {α : Type*}

/-- The differential of the zero homogeneous morphism is zero. -/
@[simp] theorem homD_zero {M N : RightModule.{w} C} {p : ℤ} :
    homD (0 : HomogeneousMap M N p) = 0 := by
  simpa using (homD_add (0 : HomogeneousMap M N p) 0).symm

/-- The differential of a finite sum of homogeneous morphisms is the sum of the
differentials. -/
theorem homD_sum {M N : RightModule.{w} C} {p : ℤ} (s : Finset α)
    (g : α → HomogeneousMap M N p) : homD (∑ a ∈ s, g a) = ∑ a ∈ s, homD (g a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homD_add, ih]

/-- A finite sum of cocycles, as a cocycle. -/
def sumCocycle (s : Finset α)
    (f : α → (rightModuleCategory.{w} C).Cocycle (X : (rightModuleCategory.{w} C).Obj) Y) :
    (rightModuleCategory.{w} C).Cocycle (X : (rightModuleCategory.{w} C).Obj) Y :=
  ⟨∑ a ∈ s, (f a).1, by
    rw [show (rightModuleCategory.{w} C).d (∑ a ∈ s, (f a).1) =
      homD (∑ a ∈ s, (f a).1) from rfl, homD_sum]
    exact Finset.sum_eq_zero fun a _ => (f a).2⟩

/-- The underlying morphism of a finite sum of cocycles is the sum of the underlying morphisms. -/
@[simp] theorem sumCocycle_val (s : Finset α)
    (f : α → (rightModuleCategory.{w} C).Cocycle (X : (rightModuleCategory.{w} C).Obj) Y) :
    (sumCocycle s f).1 = ∑ a ∈ s, (f a).1 :=
  rfl

/-- The sum of the classes of a finite family of cocycles is the class of their sum. -/
theorem mk_sum (s : Finset α)
    (f : α → (rightModuleCategory.{w} C).Cocycle (X : (rightModuleCategory.{w} C).Obj) Y) :
    (@Finset.sum α (X ⟶ Y) _ s fun a => Quotient.mk _ (f a)) =
      Quotient.mk _ (sumCocycle s f) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine (homotopyPreadditive_zero (A := rightModuleCategory.{w} C) X Y).trans ?_
    exact congrArg (Quotient.mk _) (Subtype.ext (Finset.sum_empty (f := fun a => (f a).1)).symm)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih,
      homotopyPreadditive_mk_add (A := rightModuleCategory.{w} C) X Y (f a) (sumCocycle s f)]
    exact congrArg (Quotient.mk _)
      (Subtype.ext (Finset.sum_insert (f := fun a => (f a).1) ha).symm)

end Sums

/-! ### Evaluation at the identity, against a direct sum -/

section Yoneda

variable {B : C.Obj} {N : RightModule.{v} C} {p : ℤ}

/-- Evaluation at the identity undoes the right action of an element. -/
@[simp] theorem yonedaEval_yonedaOfElem (b : N.obj B p) :
    yonedaEval N B p (yonedaOfElem b) = b := by
  rw [← yonedaEval_symm_apply]
  exact (yonedaEval N B p).apply_symm_apply b

/-- Evaluation at the identity of the differential of the morphism attached to an element is
the differential of that element. -/
theorem yonedaEval_homD_yonedaOfElem (b : N.obj B p) :
    yonedaEval N B (p + 1) (homD (yonedaOfElem b)) = N.d rfl b := by
  rw [yonedaEval_homD N B p (yonedaOfElem b), yonedaEval_yonedaOfElem]

variable {α : Type v} {M : α → RightModule.{v} C} [DecidableEq α]

/-- Evaluation at the identity turns composition with the inclusion of a summand into the
inclusion of that summand. -/
theorem yonedaEval_homComp_coprodι (a : α)
    (χ : HomogeneousMap (yonedaRightModule C B) (M a) 0) :
    yonedaEval (coprod M) B 0 (homComp (add_zero 0) (coprodι M a) χ) =
      DirectSum.lof R α (fun c => (M c).obj B 0) a (yonedaEval (M a) B 0 χ) :=
  rfl

/-- A component of a finite sum of inclusions of summands. -/
theorem sum_lof_apply (s : Finset α) (y : ∀ a, (M a).obj B p) {b : α} (hb : b ∈ s) :
    (∑ a ∈ s, DirectSum.lof R α (fun c => (M c).obj B p) a (y a)) b = y b := by
  rw [DirectSum.sum_apply, Finset.sum_eq_single b]
  · rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · intro c _ hcb
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hcb)]
  · exact fun h => absurd hb h

/-- The inclusion of a summand, read as a homogeneous morphism. -/
@[simp] theorem coprodιCocycle_val (a : α) : (coprodιCocycle M a).1 = coprodι M a :=
  rfl

end Yoneda

/-! ### Compactness of a representable module -/

section Compact

/-- The representable right differential graded module `h_B = C(-, B)`, as an object of the
homotopy category `K(Mod^dg(C))`. The homotopy category is a definition and not an
abbreviation of the modules, so an object must be retyped for the categorical and additive
instances on `K(Mod^dg(C))` to be found for its morphism groups. -/
@[implicit_reducible]
def yonedaObjK (B : C.Obj) : (rightModuleCategory.{v} C).K := yonedaRightModule C B

variable (B : C.Obj) {α : Type v} (M : α → (rightModuleCategory.{v} C).K) [DecidableEq α]

/-- The cocycle `h_B ⟶ N` attached to a closed degree-zero element of `N` at `B`: the right
action of that element. -/
def yonedaCocycle {N : RightModule.{v} C} (b : N.obj B 0) (hb : N.d rfl b = 0) :
    (rightModuleCategory.{v} C).Cocycle (yonedaRightModule C B) N :=
  ⟨yonedaOfElem b, by
    refine (yonedaEval N B (0 + 1)).injective ?_
    rw [map_zero]
    exact (yonedaEval_homD_yonedaOfElem b).trans hb⟩

/-- The underlying morphism of the cocycle attached to a closed element is the right action of
that element. -/
@[simp] theorem yonedaCocycle_val {N : RightModule.{v} C} (b : N.obj B 0)
    (hb : N.d rfl b = 0) : (yonedaCocycle B b hb).1 = yonedaOfElem b :=
  rfl

/-- The canonical map sends the class of a cocycle placed in the `a`-th summand to the class of
its composite with the inclusion of that summand. -/
private theorem cofanMap_of_mk (a : α)
    (φ : (rightModuleCategory.{v} C).Cocycle (yonedaRightModule C B) (M a : _)) :
    cofanMap (yonedaObjK B) (coprodCofan M).inj (DirectSum.of _ a (Quotient.mk _ φ)) =
      Quotient.mk _ ((rightModuleCategory.{v} C).compCocycle (coprodιCocycle M a) φ) := by
  rw [cofanMap_of, coprodCofan_inj, comp_mk]

/-- **A morphism from a representable module into a direct sum factors through a finite subsum,
in exactly one way.** This is the compactness of `h_B = C(-, B)` in `K(Mod^dg(C))`, stated as
the bijectivity of the canonical map out of the direct sum of the morphism groups. -/
theorem bijective_cofanMap_coprodCofan :
    Function.Bijective (cofanMap (yonedaObjK B) (coprodCofan M).inj) := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hxs : cofanMap (yonedaObjK B) (coprodCofan M).inj x =
        (∑ a ∈ x.support, Quotient.mk _ ((rightModuleCategory.{v} C).compCocycle
          (coprodιCocycle M a) (Quotient.out (x a))) : yonedaObjK B ⟶ (coprodCofan M).pt) := by
      conv_lhs => rw [← DirectSum.sum_support_of x, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := cofanMap_of_mk B M a (Quotient.out (x a))
      rwa [Quotient.out_eq] at this
    rw [hxs] at hx
    rw [mk_sum, homotopyPreadditive_zero (A := rightModuleCategory.{v} C)] at hx
    obtain ⟨k, hk⟩ := Quotient.exact hx
    rw [dPrime_eq_homD] at hk
    have hval : (∑ a ∈ x.support,
        homComp (add_zero 0) (coprodι M a) (Quotient.out (x a)).1) = homD k := by
      simpa only [sumCocycle_val, compCocycle_val, coprodιCocycle_val, sub_zero] using hk
    obtain ⟨z, hz⟩ : ∃ z : ⨁ c, (M c).obj B (-1),
        yonedaEval (coprod M) B (-1) k = z := ⟨_, rfl⟩
    have key : (∑ a ∈ x.support, DirectSum.lof R α (fun c => (M c).obj B 0) a
          (yonedaEval (M a) B 0 (Quotient.out (x a)).1)) =
        ((coprod M).d (show (-1 : ℤ) + 1 = 0 by omega) z : ⨁ c, (M c).obj B 0) := by
      have h0 := congrArg (yonedaEval (coprod M) B 0) hval
      rw [map_sum] at h0
      refine Eq.trans ?_ (h0.trans ?_)
      · exact Finset.sum_congr rfl fun a _ =>
          (yonedaEval_homComp_coprodι a (Quotient.out (x a)).1).symm
      · exact (yonedaEval_homD (coprod M) B (-1) k).trans
          (congrArg ((coprod M).d rfl) hz)
    refine DirectSum.ext fun b => ?_
    rw [DirectSum.zero_apply]
    by_cases hb : b ∈ x.support
    swap
    · simpa using hb
    have keyb := congrArg (fun y : ⨁ c, (M c).obj B 0 => y b) key
    rw [sum_lof_apply _ _ hb] at keyb
    have hφ : (Quotient.out (x b)).1 = homD (yonedaOfElem (z b)) :=
      (yonedaEval (M b) B 0).injective (keyb.trans (yonedaEval_homD_yonedaOfElem (z b)).symm)
    conv_lhs => rw [← Quotient.out_eq (x b)]
    rw [homotopyPreadditive_zero (A := rightModuleCategory.{v} C)]
    refine Quotient.sound ⟨yonedaOfElem (z b), ?_⟩
    rw [dPrime_eq_homD]
    simpa using hφ
  · intro g
    obtain ⟨φ, rfl⟩ : ∃ φ, Quotient.mk _ φ = g := ⟨Quotient.out g, Quotient.out_eq g⟩
    obtain ⟨z, hz⟩ : ∃ z : ⨁ c, (M c).obj B 0,
        yonedaEval (coprod M) B 0 φ.1 = z := ⟨_, rfl⟩
    have hzero : ((coprod M).d rfl z : ⨁ c, (M c).obj B (0 + 1)) = 0 := by
      have h1 := yonedaEval_homD (coprod M) B 0 φ.1
      rw [show homD φ.1 = 0 from φ.2, map_zero, hz] at h1
      exact h1.symm
    have hclosed : ∀ a : α, (M a).d rfl (z a) = 0 := fun a =>
      congrArg (fun y : ⨁ c, (M c).obj B (0 + 1) => y a) hzero
    refine ⟨∑ a ∈ z.support, DirectSum.of _ a
      (Quotient.mk _ (yonedaCocycle B (z a) (hclosed a))), ?_⟩
    rw [map_sum]
    rw [Finset.sum_congr rfl fun a _ => cofanMap_of_mk B M a _, mk_sum]
    refine congrArg (Quotient.mk _) (Subtype.ext ?_)
    refine (yonedaEval (coprod M) B 0).injective ?_
    rw [sumCocycle_val, map_sum, hz]
    have hstep : ∀ a ∈ z.support,
        yonedaEval (coprod M) B 0 ((rightModuleCategory.{v} C).compCocycle
            (coprodιCocycle M a) (yonedaCocycle B (z a) (hclosed a))).1 =
          DirectSum.lof R α (fun c => (M c).obj B 0) a (z a) := by
      intro a _
      rw [compCocycle_val, coprodιCocycle_val,
        yonedaEval_homComp_coprodι a (yonedaCocycle B (z a) (hclosed a)).1,
        yonedaCocycle_val, yonedaEval_yonedaOfElem]
    rw [Finset.sum_congr rfl hstep]
    simpa only [DirectSum.lof_eq_of] using DirectSum.sum_support_of z

end Compact

end RightModule

end DGCategory

end
