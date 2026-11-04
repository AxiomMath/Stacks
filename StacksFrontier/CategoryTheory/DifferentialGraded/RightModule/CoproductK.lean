module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomotopyCategoryTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Coproduct

/-!
# The direct sum of right differential graded modules is a coproduct in the homotopy category

Let `C` be a differential graded category over a commutative ring `R` and let
`M : α → RightModule C` be a family of right differential graded `C`-modules indexed by a type of
their own universe. The degreewise direct sum of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Coproduct`, with the inclusions of
its summands, is a coproduct of the family in the homotopy category `K(Mod^dg(C))`.

The two halves of the proof are the two halves of the universal property of the direct sum, in
degree `0` and in degree `-1`. A family of closed degree-zero morphisms out of the summands
assembles into one out of the direct sum, which is closed because assembly commutes with the
differential; that is the existence half. A family of homotopies assembles likewise, and the
assembled homotopy is a homotopy between the assembled morphisms because the inclusions are
closed, so composing with one commutes with the differential; that is the uniqueness half.
Nothing about shifts or cones is used: the homotopy category of a differential graded category
has coproducts as soon as the underlying differential graded category does, whether or not it
is triangulated.

## Main definitions

* `DGCategory.RightModule.coprodCofan`: the direct sum with its inclusions, as a cofan in
  `K(Mod^dg(C))`.
* `DGCategory.RightModule.isColimitCoprodCofan`: that cofan is a colimit.

## Main results

* `DGCategory.RightModule.homotopic_of_forall_comp_coprodι`: two closed morphisms out of a
  direct sum whose restrictions to the summands are homotopic are homotopic.
* `DGCategory.RightModule.hasCoproducts_rightModuleHomotopyCategory`: `K(Mod^dg(C))` has
  coproducts indexed by its module universe.

## Implementation notes

`DGCategory.d'` transports the differential into a prescribed degree, and at degree `-1` the
prescribed degree is `0`; since `(-1) + 1` and `0` are the same integer definitionally, that
transport is the identity and `DGCategory.RightModule.dPrime_eq_homD` records it. Every
statement below is therefore phrased with `DGCategory.RightModule.homD` and
`DGCategory.RightModule.homComp` rather than with the differential and the composition of the
ambient differential graded category, which are the same maps behind a structure projection.

The index type carries no decidable equality in the statements that only assert existence; they
supply one classically, as Mathlib's `DirectSum.lof` requires.

`DGCategory.K` is a definition and not an abbreviation of the objects of the differential
graded category, so a term of `Mod^dg(C)` placed where an object of `K(Mod^dg(C))` is expected
is type-correct only at default transparency, and `rw` — which works at `implicit`
transparency — rejects such a goal. The section on the homotopy category therefore makes
`DGCategory.K` and `DGCategory.RightModule.coprodCofan` unfold at that transparency, which is
the device of `DGCategory.rightModuleCategory` and of
`DGCategory.RightModule.coprod` themselves.
-/

@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory CategoryTheory.Limits DirectSum

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

namespace RightModule

/-! ### Reading the homotopy category of `Mod^dg(C)` in the module language -/

variable {M N P : RightModule.{w} C}

/-- The differential of a degree `-1` homogeneous morphism, transported into degree zero, is
its differential: the transport is along an equality of integers that holds definitionally. -/
theorem dPrime_eq_homD (h : HomogeneousMap M N (-1)) :
    (rightModuleCategory.{w} C).d' (show (-1 : ℤ) + 1 = 0 by omega) h = homD h :=
  rfl

/-- Composition of cocycles is composition of homogeneous morphisms. -/
theorem compCocycle_val (g : (rightModuleCategory.{w} C).Cocycle N P)
    (f : (rightModuleCategory.{w} C).Cocycle M N) :
    ((rightModuleCategory.{w} C).compCocycle g f).1 = homComp (add_zero 0) g.1 f.1 :=
  rfl

/-- Composition in the homotopy category of `Mod^dg(C)`, on representatives. -/
theorem comp_mk {X Y Z : (rightModuleCategory.{w} C).K}
    (f : (rightModuleCategory.{w} C).Cocycle (X : (rightModuleCategory.{w} C).Obj) Y)
    (g : (rightModuleCategory.{w} C).Cocycle (Y : (rightModuleCategory.{w} C).Obj) Z) :
    @Eq (X ⟶ Z) ((Quotient.mk _ f : X ⟶ Y) ≫ (Quotient.mk _ g : Y ⟶ Z))
      (Quotient.mk _ ((rightModuleCategory.{w} C).compCocycle g f)) :=
  rfl

/-! ### Elementary identities for composition of homogeneous morphisms -/

variable {m n p : ℤ}

/-- Composing with the zero morphism on the right gives zero. -/
theorem homComp_zero_right (h : m + n = p) (ψ : HomogeneousMap N P m) :
    homComp h ψ (0 : HomogeneousMap M N n) = 0 := by
  ext x i j e a
  rw [app_homComp, zero_app, app_zero, zero_app]

/-- Composition is additive in the outer morphism, for subtraction. -/
theorem homComp_sub_left (h : m + n = p) (ψ₁ ψ₂ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) :
    homComp h (ψ₁ - ψ₂) φ = homComp h ψ₁ φ - homComp h ψ₂ φ := by
  ext x i j e a
  rw [app_homComp, sub_app, sub_app, app_homComp, app_homComp]

/-! ### Composing with the inclusion of a summand -/

variable {α : Type w} (M' : α → RightModule.{w} C) [DecidableEq α]

/-- Composing a homogeneous morphism out of a direct sum with the inclusion of a summand
evaluates it on that summand. -/
theorem app_homComp_coprodι (ψ : HomogeneousMap (coprod M') N p) (a : α) {x : C.Obj}
    {i j : ℤ} (e : i + p = j) (y : (M' a).obj x i) :
    app (homComp (add_zero p) ψ (coprodι M' a)) e y =
      app ψ e (DirectSum.lof R α (fun c => (M' c).obj x i) a y) := by
  rw [app_homComp, app_coprodι, ← coprod_objCast_lof,
    app_objCast ψ (show i = i + 0 by omega) (show i + 0 + p = j by omega) e]

/-- A homogeneous morphism out of a direct sum is determined by its composites with the
inclusions of the summands. -/
theorem coprod_hom_ext' {ψ ψ' : HomogeneousMap (coprod M') N p}
    (h : ∀ a, homComp (add_zero p) ψ (coprodι M' a) =
      homComp (add_zero p) ψ' (coprodι M' a)) :
    ψ = ψ' := by
  refine coprod_hom_ext fun a x i j e y => ?_
  rw [← app_homComp_coprodι, ← app_homComp_coprodι, h a]

/-- The differential of an assembled morphism, composed with the inclusion of a summand, is the
differential of the morphism that summand contributed. The second term of the graded Leibniz
rule drops out because the inclusion is closed. -/
theorem homComp_homD_coprodDesc_coprodι (φ : ∀ a, HomogeneousMap (M' a) N p) (a : α) :
    homComp (add_zero (p + 1)) (homD (coprodDesc M' φ)) (coprodι M' a) = homD (φ a) := by
  have hL := homD_homComp (add_zero p) (coprodDesc M' φ) (coprodι M' a)
  rw [coprodDesc_coprodι, coprodι_closed, homComp_zero_right, smul_zero, add_zero] at hL
  exact hL.symm

/-! ### The cocycles out of a direct sum -/

/-- The inclusion of a summand, as a morphism of the category of complexes. -/
def coprodιCocycle (a : α) : (rightModuleCategory.{w} C).Cocycle (M' a) (coprod M') :=
  ⟨coprodι M' a, coprodι_closed M' a⟩

/-- A family of closed degree-zero morphisms out of the summands assembles into a closed
degree-zero morphism out of the direct sum. -/
def coprodDescCocycle (φ : ∀ a, (rightModuleCategory.{w} C).Cocycle (M' a) N) :
    (rightModuleCategory.{w} C).Cocycle (coprod M') N := by
  refine ⟨coprodDesc M' (fun a => (φ a).1), ?_⟩
  rw [show (rightModuleCategory.{w} C).d (coprodDesc M' (fun a => (φ a).1)) =
    homD (coprodDesc M' (fun a => (φ a).1)) from rfl, homD_coprodDesc]
  refine coprod_hom_ext fun a x i j e y => ?_
  rw [app_coprodDesc_lof, zero_app, show homD (φ a).1 = 0 from (φ a).2, zero_app]

/-- The assembled cocycle restricts on each summand to the cocycle it was assembled from. -/
theorem compCocycle_coprodDescCocycle
    (φ : ∀ a, (rightModuleCategory.{w} C).Cocycle (M' a) N) (a : α) :
    (rightModuleCategory.{w} C).compCocycle (coprodDescCocycle M' φ) (coprodιCocycle M' a) =
      φ a :=
  Subtype.ext (coprodDesc_coprodι M' (fun a => (φ a).1) a)

/-- **Two closed morphisms out of a direct sum whose restrictions to the summands are homotopic
are homotopic.** The homotopy is the assembly of the homotopies on the summands. -/
theorem homotopic_of_forall_comp_coprodι
    {ψ ψ' : (rightModuleCategory.{w} C).Cocycle (coprod M') N}
    (h : ∀ a, (rightModuleCategory.{w} C).Homotopic
      ((rightModuleCategory.{w} C).compCocycle ψ (coprodιCocycle M' a))
      ((rightModuleCategory.{w} C).compCocycle ψ' (coprodιCocycle M' a))) :
    (rightModuleCategory.{w} C).Homotopic ψ ψ' := by
  choose k hk using h
  refine ⟨coprodDesc M' k, ?_⟩
  rw [dPrime_eq_homD]
  refine coprod_hom_ext' M' fun a => ?_
  rw [homComp_sub_left, homComp_homD_coprodDesc_coprodι]
  have hka := hk a
  rw [compCocycle_val, compCocycle_val, dPrime_eq_homD] at hka
  exact hka

/-! ### The coproduct in the homotopy category -/

section HomotopyCategory

attribute [local implicit_reducible] DGCategory.K

variable {α : Type w} (G : α → (rightModuleCategory.{w} C).K) [DecidableEq α]

/-- The direct sum of a family of right differential graded modules, with the inclusions of its
summands, as a cofan in the homotopy category `K(Mod^dg(C))`. -/
@[implicit_reducible]
def coprodCofan : Cofan G :=
  Cofan.mk (coprod G) fun a => Quotient.mk _ (coprodιCocycle G a)

/-- The point of `coprodCofan G` is the direct sum `coprod G`. -/
@[simp] theorem coprodCofan_pt : (coprodCofan G).pt = coprod G := rfl

/-- The `a`-th inclusion of `coprodCofan G` is the class of the cocycle `coprodιCocycle G a`. -/
@[simp] theorem coprodCofan_inj (a : α) :
    (coprodCofan G).inj a = Quotient.mk _ (coprodιCocycle G a) := rfl

/-- **The direct sum is a coproduct in the homotopy category.** A family of morphisms out of
the summands is assembled by assembling representing cocycles, and two morphisms out of the
direct sum agreeing on the summands are homotopic by assembling the homotopies. -/
noncomputable def isColimitCoprodCofan : IsColimit (coprodCofan G) := by
  refine Cofan.IsColimit.mk _
    (fun t => Quotient.mk _ (coprodDescCocycle G fun a => (t.inj a).out)) ?_ ?_
  · intro t a
    rw [coprodCofan_inj, comp_mk, compCocycle_coprodDescCocycle]
    exact Quotient.out_eq _
  · intro t m hm
    induction m using Quotient.inductionOn with
    | _ m₀ =>
      refine Quotient.sound (homotopic_of_forall_comp_coprodι G fun a => ?_)
      have h₁ := hm a
      rw [coprodCofan_inj, comp_mk] at h₁
      refine Quotient.exact (h₁.trans ?_)
      rw [compCocycle_coprodDescCocycle]
      exact (Quotient.out_eq _).symm

end HomotopyCategory

end RightModule

/-- The homotopy category of right differential graded `C`-modules has coproducts indexed by
the universe of the modules: they are the degreewise direct sums. -/
instance hasCoproducts_rightModuleHomotopyCategory :
    HasCoproducts.{w} (rightModuleCategory.{w} C).K := by
  classical
  intro α
  refine ⟨fun F => ?_⟩
  have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    ⟨⟨_, RightModule.isColimitCoprodCofan (F.obj ∘ Discrete.mk)⟩⟩
  exact hasColimit_of_iso Discrete.natIsoFunctor

end DGCategory

end
