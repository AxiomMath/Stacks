module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPowerPullbackMul
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaMultiplicativity

/-!
# Pullback carries the addition law of the tensor powers of Tag 01CU to itself

Let `f : X ⟶ S` be a morphism of schemes and `M` an invertible `𝒪_S`-module.
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` is the comparison
`f^*(M^{⊗ n}) ≅ (f^*M)^{⊗ n}` between the integer tensor powers of Stacks Tag 01CU, built by
iterating Stacks Tag 01CD, and `Stacks.Ample.tensorPowModuleAddIso` is the canonical
multiplication `M^{⊗ n} ⊗ M^{⊗ m} ≅ M^{⊗ (n+m)}` of those powers. This file proves that the
comparison is **multiplicative**: the commuting square

    f^*(M^{⊗n} ⊗ M^{⊗m}) ──f^*(mult)──> f^*(M^{⊗(n+m)})
           │                                   │
      01CD │                                   │ the comparison in degree n+m
           v                                   v
    f^*(M^{⊗n}) ⊗ f^*(M^{⊗m}) ──comparisons──> (f^*M)^{⊗n} ⊗ (f^*M)^{⊗m} ──mult──> (f^*M)^{⊗(n+m)}

in every pair of nonnegative degrees.

## Main definitions

* `Stacks.RelativeVeryAmple.pullbackPowOneIso`: the degree-one value
  `f^*(M^{⊗ 1}) ≅ (f^*M)^{⊗ 1}` of the comparison family, read through
  `Stacks.Ample.tensorPowModuleOneIso` on both sides.

## Main results

* `Stacks.TensorPowerPullbackMul.comparison_mulFamily`: **the square for an abstract
  multiplicative family and a monoidal functor.** Given families of objects `P` and `Q` indexed by
  `ℕ`, multiplications `a` and `b` on them that are associative against one and the same
  associator when the third factor is a fixed object, and a comparison `g` whose squares in the
  bidegrees `(n, 0)` and `(n, 1)` commute, the square commutes in every bidegree.
* `Stacks.TensorPowerPullbackMul.laxMul_assoc`: the multiplication obtained by transporting `a`
  through the tensorator of a monoidal functor is associative.
* `Stacks.TensorPowerPullbackMul.laxMul_unitor`: the same transport carries a right unitor to a
  right unitor.
* `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso`: **the square, for
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` and
  `Stacks.Ample.tensorPowModuleAddIso`.**
* `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_succ_square` and
  `..._zero_square`: the bidegrees `(n, 1)` and `(n, 0)`. The first is the recursion defining the
  comparison, read as a square; the second is the right unit law.

## Implementation notes

**Which monoidal structure.** Every tensor product occurring here is the tensor product sheaf of
Stacks Tag 01CA, `Stacks.RelativeVeryAmple.tensorModules`, which is the source of
`Stacks.Ample.tensorPowModuleAddIso` and both the source and target of
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`. That is the tensor product of the monoidal
structure `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, in which — and only in which — the
cotensorator of `f^*` is the comparison of Stacks Tag 01CD
(`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`) and the associativity and right
unit constraints of the multiplication of the powers are available
(`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` and
`tensorPowModuleAddIso_zero_right`). The *powers* themselves are the integer powers of Tag 01CU,
which live in a different monoidal structure; nothing below needs them to be powers for that
structure, only that they carry the multiplication `tensorPowModuleAddIso`, and that is why the
abstract statement takes the family of objects and the multiplication as data.

**The third factor is `M^{⊗ 1}`, not `M`.** The recursion defining `pullbackTensorPowModuleIso`
splits `M^{⊗ (n+1)}` as `M^{⊗ n} ⊗ M^{⊗ 1}` and compares the second factor by
`Stacks.RelativeVeryAmple.pullbackPowOneIso`. Taking the fixed third object of the abstract
statement to be `M^{⊗ 1}` therefore makes the bidegree `(n, 1)` square a consequence of the
recursion and two cancellations, with no normalisation of the comparison in degree one needed —
which is the step that the corresponding argument for the twists of `Proj`
(`Stacks.AlgebraicGeometry.ThetaMul.theta_one_eq`) has to take.

**`letI`, not `have`, for the monoidal structure of `f^*`.**
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` is not an instance, so it is
introduced in each proof by hand; it has to be introduced with its *value* visible, because the
identification of its cotensorator with `Stacks.RelativeVeryAmple.pullbackTensorModulesIso` holds
by `rfl` and that is unprovable once the structure has become an opaque hypothesis.

**`rw` and `simp` do not work on the unfolded recursion.** The term
`pullbackTensorPowModuleIso f M (n + 1)` mentions both `f^*(M^{⊗(n+1)})` and
`f^*(M^{⊗ n} ⊗ M^{⊗ 1})`, whose equality needs the degrees `((n+1 : ℕ) : ℤ)` and `(n : ℤ) + 1`
to be identified; that identification is definitional but not available at the transparency the
rewriting tactics check their motives at, so a goal containing the unfolded recursion is reported
as not type-correct and every `rw` on it fails. The two cancellations are therefore done by
`laxMul_cancel` and `comp_tail`, stated with the objects as variables, exactly as
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaMultiplicativity.lean` does for the same reason.

**Universes.** The abstract statements are polymorphic in both object and morphism universes of
both categories. The scheme-level statements are at a single universe, forced by
`RingedSpaceModuleAdjunction.modulePullback`.

**No `@[stacks]` attribute.** Tag 01CD is carried by `Stacks.RingedSpace.comparisonIso` and Tag
01CU by the multiplication of the powers; this is a compatibility of the two, not a new result.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the tensor powers of an
  invertible module and their canonical multiplication.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.ThetaMul

universe v₁ v₂ u₁ u₂ u

namespace Stacks.TensorPowerPullbackMul

/-! ### Cancellations with the objects as variables -/

section Cancel

variable {E : Type u₁} [Category.{v₁} E]

/-- A morphism from an object to itself that is known to be an identity, in front of a
composite. -/
theorem id_comp_of {A B : E} (i : A ⟶ A) (hi : i = 𝟙 A) (x : A ⟶ B) : i ≫ x = x := by
  rw [hi, Category.id_comp]

/-- Two morphisms whose composite is an identity, mapped by a functor in front of a composite. -/
theorem laxMul_cancel {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {A B : C} {x : A ⟶ B} {z : B ⟶ A} (h : x ≫ z = 𝟙 A) {G : D} (t : F.obj A ⟶ G) :
    F.map x ≫ F.map z ≫ t = t := by
  rw [← Category.assoc, ← F.map_comp, h, F.map_id, Category.id_comp]

/-- A three-fold composite followed by a morphism from an object to itself known to be an
identity. -/
theorem comp_comp_comp_id_of {A B G H : E} (u : A ⟶ B) (v : B ⟶ G) (p : G ⟶ H) (i : H ⟶ H)
    (hi : i = 𝟙 H) : u ≫ v ≫ p ≫ i = u ≫ v ≫ p := by rw [hi, Category.comp_id]

/-- Rewriting the two inner factors of a four-fold composite: the third factor is replaced by an
equal morphism and the last, an identity, is dropped. -/
theorem comp_tail {A B G H : E} (p : A ⟶ B) {w w' : B ⟶ G} (hw : w = w') (y : G ⟶ H)
    {i : H ⟶ H} (hi : i = 𝟙 H) : p ≫ w ≫ y ≫ i = p ≫ w' ≫ y := by
  rw [hw, hi, Category.comp_id]

/-- A morphism split off the front of a composite, when a retraction of it is available. -/
theorem eq_comp_of_comp_eq {A B G : E} (dd : A ⟶ B) (mm : B ⟶ A) (hmm : dd ≫ mm = 𝟙 A)
    {x : A ⟶ G} {t : B ⟶ G} (h : mm ≫ x = t) : x = dd ≫ t := by
  rw [← h, ← Category.assoc, hmm, Category.id_comp]

/-- The converse passage, available from the other cancellation. -/
theorem comp_eq_of_eq_comp {A B G : E} (dd : A ⟶ B) (mm : B ⟶ A) (hmm : mm ≫ dd = 𝟙 B)
    {x : A ⟶ G} {t : B ⟶ G} (h : x = dd ≫ t) : mm ≫ x = t := by
  rw [h, ← Category.assoc, hmm, Category.id_comp]

end Cancel

/-! ### The abstract square -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

/-- **Three commuting squares out of an associativity diagram force the fourth.** Given two
multiplications `(a, p, r)` and `(a', p', r')` that are associative against the same associator,
and a degreewise comparison `(f, g, h, fg, gh, fgh)` whose squares commute at `(A, B)`, at
`(AB, E)` and at `(B, E)`, the square at `(A, BE)` commutes. -/
theorem square_step {A B E AB BE ABE A' B' E' AB' BE' ABE' : D}
    {a : A ⊗ B ⟶ AB} {b : B ⊗ E ≅ BE} {p : AB ⊗ E ⟶ ABE} {r : A ⊗ BE ⟶ ABE}
    {a' : A' ⊗ B' ⟶ AB'} {b' : B' ⊗ E' ⟶ BE'} {p' : AB' ⊗ E' ⟶ ABE'}
    {r' : A' ⊗ BE' ⟶ ABE'}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : E ⟶ E'} {fg : AB ⟶ AB'} {gh : BE ⟶ BE'}
    {fgh : ABE ⟶ ABE'}
    (hL : a ▷ E ≫ p = (α_ A B E).hom ≫ A ◁ b.hom ≫ r)
    (hR : a' ▷ E' ≫ p' = (α_ A' B' E').hom ≫ A' ◁ b' ≫ r')
    (h1 : a ≫ fg = (f ⊗ₘ g) ≫ a')
    (h2 : p ≫ fgh = (fg ⊗ₘ h) ≫ p')
    (h3 : b.hom ≫ gh = (g ⊗ₘ h) ≫ b') :
    r ≫ fgh = (f ⊗ₘ gh) ≫ r' := by
  refine (Iso.cancel_iso_hom_left (α_ A B E ≪≫ MonoidalCategory.whiskerLeftIso A b) _ _).mp ?_
  simp only [Iso.trans_hom, MonoidalCategory.whiskerLeftIso_hom, Category.assoc]
  calc (α_ A B E).hom ≫ A ◁ b.hom ≫ r ≫ fgh
      = (a ▷ E ≫ p) ≫ fgh := by rw [hL]; simp only [Category.assoc]
    _ = a ▷ E ≫ (fg ⊗ₘ h) ≫ p' := by rw [Category.assoc, h2]
    _ = (((f ⊗ₘ g) ≫ a') ⊗ₘ h) ≫ p' := by
          rw [← h1, MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
    _ = ((f ⊗ₘ g) ⊗ₘ h) ≫ (a' ▷ E' ≫ p') := by
          rw [← Category.assoc, MonoidalCategory.tensorHom_comp_whiskerRight]
    _ = ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ A' B' E').hom ≫ A' ◁ b' ≫ r' := by rw [hR]
    _ = (α_ A B E).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) ≫ A' ◁ b' ≫ r' := by
          rw [← Category.assoc, MonoidalCategory.associator_naturality]
          simp only [Category.assoc]
    _ = (α_ A B E).hom ≫ (f ⊗ₘ ((g ⊗ₘ h) ≫ b')) ≫ r' := by
          rw [← MonoidalCategory.tensorHom_comp_whiskerLeft_assoc]
    _ = (α_ A B E).hom ≫ (f ⊗ₘ (b.hom ≫ gh)) ≫ r' := by rw [h3]
    _ = (α_ A B E).hom ≫ A ◁ b.hom ≫ (f ⊗ₘ gh) ≫ r' := by
          rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc]

/-- **One unit law of a tensor product of morphisms, in an abstract monoidal category.** If `q`
lands in the unit object, if a second object `A'` is identified with the unit object by `vh` and
`vi`, and if the comparison `g₀` out of the first is `q` followed by `vi`, then the square
relating the right unitor to the multiplication `T ◁ vh ≫ ρ_ T` along the tensor product of `θ`
with `g₀` commutes. -/
theorem unit_right_square {A A' P T : D} (q : A ⟶ 𝟙_ D) (vh : A' ⟶ 𝟙_ D) (vi : 𝟙_ D ⟶ A')
    (hv : vi ≫ vh = 𝟙 (𝟙_ D)) (θ : P ⟶ T) (g₀ : A ⟶ A') (hg₀ : g₀ = q ≫ vi) :
    (P ◁ q ≫ (ρ_ P).hom) ≫ θ = (θ ⊗ₘ g₀) ≫ T ◁ vh ≫ (ρ_ T).hom := by
  subst hg₀
  have hr : (θ ⊗ₘ (q ≫ vi)) ≫ T ◁ vh = θ ⊗ₘ q := by
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.assoc, hv, Category.comp_id]
  rw [← Category.assoc (θ ⊗ₘ (q ≫ vi)), hr, MonoidalCategory.tensorHom_def']
  simp only [Category.assoc]
  rw [MonoidalCategory.rightUnitor_naturality]

/-- **The multiplication transported through the tensorator of a monoidal functor is
associative**, when the multiplication it is transported from is. -/
theorem laxMul_assoc {P : ℕ → C} {N : C}
    (a : ∀ n m : ℕ, P n ⊗ P m ⟶ P (n + m)) (aL : ∀ n : ℕ, P n ⊗ N ⟶ P (n + 1))
    (haL : ∀ n m : ℕ,
      a n m ▷ N ≫ aL (n + m) = (α_ (P n) (P m) N).hom ≫ P n ◁ aL m ≫ a n (m + 1))
    (n m : ℕ) :
    (μ F (P n) (P m) ≫ F.map (a n m)) ▷ F.obj N ≫ μ F (P (n + m)) N ≫ F.map (aL (n + m)) =
      (α_ (F.obj (P n)) (F.obj (P m)) (F.obj N)).hom ≫
        F.obj (P n) ◁ (μ F (P m) N ≫ F.map (aL m)) ≫
          μ F (P n) (P (m + 1)) ≫ F.map (a n (m + 1)) := by
  rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [μ_natural_left_assoc F (a n m) N, ← F.map_comp, haL n m, F.map_comp, F.map_comp,
    Functor.LaxMonoidal.associativity_assoc F (P n) (P m) N,
    ← μ_natural_right_assoc F (P n) (aL m)]

/-- **The right unitor transported through the tensorator of a monoidal functor is a right
unitor**, the unit object being matched by the counit of the functor. -/
theorem laxMul_unitor {N₀ : C} (u : N₀ ≅ 𝟙_ C) (A : C) :
    μ F A N₀ ≫ F.map (A ◁ u.hom ≫ (ρ_ A).hom) =
      F.obj A ◁ (F.map u.hom ≫ η F) ≫ (ρ_ (F.obj A)).hom := by
  rw [F.map_comp, ← μ_natural_right_assoc F A u.hom,
    Functor.LaxMonoidal.right_unitality F A, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Category.assoc, Functor.Monoidal.η_ε, Category.comp_id]

/-- **The multiplicativity square of the comparison of a monoidal functor, in an arbitrary
bidegree.** `P` and `Q` are families of objects indexed by `ℕ`, `a` and `b` multiplications on
them, `aL` and `bL` the same multiplications with a fixed object in place of the degree-one
member, and `g` a degreewise comparison. The hypotheses are: the associativity of `a` and of `b`
when the third factor is that fixed object, against one and the same associator; the
invertibility of `aL`; and the squares in the bidegrees `(n, 0)` and `(n, 1)`. -/
theorem comparison_mulFamily {P : ℕ → C} {Q : ℕ → D} {N : C} {N' : D}
    (a : ∀ n m : ℕ, P n ⊗ P m ⟶ P (n + m)) (b : ∀ n m : ℕ, Q n ⊗ Q m ⟶ Q (n + m))
    (aL : ∀ n : ℕ, P n ⊗ N ⟶ P (n + 1)) (bL : ∀ n : ℕ, Q n ⊗ N' ⟶ Q (n + 1))
    (g : ∀ n : ℕ, F.obj (P n) ⟶ Q n) (hh : F.obj N ⟶ N')
    (haL : ∀ n m : ℕ,
      a n m ▷ N ≫ aL (n + m) = (α_ (P n) (P m) N).hom ≫ P n ◁ aL m ≫ a n (m + 1))
    (hbL : ∀ n m : ℕ,
      b n m ▷ N' ≫ bL (n + m) = (α_ (Q n) (Q m) N').hom ≫ Q n ◁ bL m ≫ b n (m + 1))
    (hiso : ∀ n : ℕ, IsIso (aL n))
    (h0 : ∀ n : ℕ, μ F (P n) (P 0) ≫ F.map (a n 0) ≫ g (n + 0) = (g n ⊗ₘ g 0) ≫ b n 0)
    (h1 : ∀ n : ℕ, μ F (P n) N ≫ F.map (aL n) ≫ g (n + 1) = (g n ⊗ₘ hh) ≫ bL n) :
    ∀ n m : ℕ, μ F (P n) (P m) ≫ F.map (a n m) ≫ g (n + m) = (g n ⊗ₘ g m) ≫ b n m := by
  intro n m
  induction m with
  | zero => exact h0 n
  | succ k ih =>
      have := hiso k
      have : IsIso (μ F (P k) N) := (Functor.Monoidal.μIso F (P k) N).isIso_hom
      rw [← Category.assoc]
      exact square_step (b := asIso (μ F (P k) N ≫ F.map (aL k)))
        (laxMul_assoc F a aL haL n k) (hbL n k)
        (by rw [Category.assoc]; exact ih)
        (by rw [Category.assoc]; exact h1 (n + k))
        (by rw [asIso_hom, Category.assoc]; exact h1 k)

end Abstract

end Stacks.TensorPowerPullbackMul

namespace Stacks.RelativeVeryAmple

/-- The monoidal structure of Stacks Tag 01CA on the `𝒪_X`-modules of a scheme, named at the
`structureSheafRing` spelling of the ring sheaf — the spelling the module
pullback of `RingedSpaceModuleAdjunction.modulePullback` records in its type, and hence the one
every statement about the comparison of Stacks Tag 01CD is read at. The body is
`Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`; only the name of the ring sheaf differs. -/
@[instance_reducible]
def ringSheafMonoidal (Z : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u}
      (structureSheafRing Z.toRingedSpace)) :=
  schemeMonoidal Z

attribute [local instance] schemeMonoidal strictSchemeMonoidal ringSheafMonoidal

open Stacks.TensorPowerPullbackMul

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules) [IsInvertibleModule S M]

/-- **The degree-one value of the comparison family**, `f^*(M^{⊗ 1}) ≅ (f^*M)^{⊗ 1}`: identify
both first powers with their modules by `Stacks.Ample.tensorPowModuleOneIso`. -/
def pullbackPowOneIso :
    (Scheme.Modules.pullback f).obj (tensorPowModule S M 1) ≅
      tensorPowModule X ((Scheme.Modules.pullback f).obj M) 1 :=
  (Scheme.Modules.pullback f).mapIso (tensorPowModuleOneIso S M) ≪≫
    (tensorPowModuleOneIso X ((Scheme.Modules.pullback f).obj M)).symm

/-- **The associativity constraint of the multiplication of the tensor powers with the third
factor in degree one.** This is
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` with the transport along
`n + (m + 1) = n + m + 1` removed: its two ends are the same object, the third degree being
`1`. -/
theorem tensorPowModuleAddIso_assoc_one (Z : Scheme.{u}) (L : Z.Modules)
    [IsInvertibleModule Z L] (n m : ℕ) :
    MonoidalCategoryStruct.whiskerRight
        (self := (schemeMonoidal Z).toMonoidalCategoryStruct)
        (tensorPowModuleAddIso Z L (n : ℤ) (m : ℤ)).hom (tensorPowModule Z L 1) ≫
        (tensorPowModuleAddIso Z L ((n + m : ℕ) : ℤ) 1).hom =
      (MonoidalCategoryStruct.associator (self := (schemeMonoidal Z).toMonoidalCategoryStruct)
          (tensorPowModule Z L (n : ℤ)) (tensorPowModule Z L (m : ℤ))
          (tensorPowModule Z L 1)).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (self := (schemeMonoidal Z).toMonoidalCategoryStruct)
          (tensorPowModule Z L (n : ℤ)) (tensorPowModuleAddIso Z L (m : ℤ) 1).hom ≫
          (tensorPowModuleAddIso Z L (n : ℤ) ((m + 1 : ℕ) : ℤ)).hom :=
  (tensorPowModuleAddIso_assoc Z L n m 1).trans (comp_comp_comp_id_of _ _ _ _ rfl)

/-- **The multiplicativity square in the bidegree `(n, 1)`.** This is the recursion defining
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` in degree `n + 1`, read as a square: the
comparison in that degree is by construction the inverse of the multiplication at `(n, 1)`,
followed by the comparison of Stacks Tag 01CD, the comparisons in degrees `n` and one, and the
multiplication at `(n, 1)` on the pullback side. -/
theorem pullbackTensorPowModuleIso_succ_square (k : ℕ) :
    (Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M (k : ℤ) 1).hom ≫
        (pullbackTensorPowModuleIso f M (k + 1)).hom =
      (pullbackTensorModulesIso f (tensorPowModule S M (k : ℤ))
          (tensorPowModule S M 1)).hom ≫
        ((pullbackTensorPowModuleIso f M k).hom ⊗ₘ (pullbackPowOneIso f M).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (k : ℤ) 1).hom := by
  have hraw : (pullbackTensorPowModuleIso f M (k + 1)).hom =
      (Scheme.Modules.pullback f).map
          ((tensorPowModuleCongr S M
                (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring)).hom ≫
            (tensorPowModuleAddIso S M (k : ℤ) 1).inv) ≫
        (pullbackTensorModulesIso f (tensorPowModule S M (k : ℤ))
            (tensorPowModule S M 1)).hom ≫
          (tensorModulesMapIso X (pullbackTensorPowModuleIso f M k)
              (pullbackPowOneIso f M)).hom ≫
            (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (k : ℤ) 1).hom ≫
              (tensorPowModuleCongr X ((Scheme.Modules.pullback f).obj M)
                (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring)).hom := rfl
  refine (congrArg (fun z ↦ (Scheme.Modules.pullback f).map
    (tensorPowModuleAddIso S M (k : ℤ) 1).hom ≫ z) hraw).trans ?_
  refine (laxMul_cancel (Scheme.Modules.pullback f)
    (Eq.trans (congrArg (fun z ↦ (tensorPowModuleAddIso S M (k : ℤ) 1).hom ≫ z)
        (id_comp_of _ rfl (tensorPowModuleAddIso S M (k : ℤ) 1).inv))
      (tensorPowModuleAddIso S M (k : ℤ) 1).hom_inv_id) _).trans ?_
  exact comp_tail _ (tensorModulesMapIso_hom X (pullbackTensorPowModuleIso f M k)
    (pullbackPowOneIso f M)) _ rfl

/-- **The multiplicativity square in the bidegree `(n, 0)`**, which is the right unit law: the
comparison in degree zero is the identification of the zeroth powers with the two structure
sheaves, matched by the structure-sheaf comparison of `f`, and the two multiplications agree with
the right unitor of Stacks Tag 01CA on that identification
(`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_right`). -/
theorem pullbackTensorPowModuleIso_zero_square (n : ℕ) :
    (Scheme.Modules.pullback f).map
          (tensorPowModuleAddIso S M (n : ℤ) ((0 : ℕ) : ℤ)).hom ≫
        (pullbackTensorPowModuleIso f M (n + 0)).hom =
      (pullbackTensorModulesIso f (tensorPowModule S M (n : ℤ))
          (tensorPowModule S M ((0 : ℕ) : ℤ))).hom ≫
        ((pullbackTensorPowModuleIso f M n).hom ⊗ₘ (pullbackTensorPowModuleIso f M 0).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
            (n : ℤ) ((0 : ℕ) : ℤ)).hom := by
  let _ : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
  refine eq_comp_of_comp_eq _ (μ (Scheme.Modules.pullback f) (tensorPowModule S M (n : ℤ))
      (tensorPowModule S M ((0 : ℕ) : ℤ)))
    (Functor.Monoidal.δ_μ (Scheme.Modules.pullback f) _ _) ?_
  have hg₀ : (pullbackTensorPowModuleIso f M 0).hom =
      ((Scheme.Modules.pullback f).map (tensorPowModuleZeroIso S M).hom ≫
          η (Scheme.Modules.pullback f)) ≫
        (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv :=
    (Category.assoc _ _ _).symm
  refine Eq.trans (congrArg (fun z ↦ μ (Scheme.Modules.pullback f) _ _ ≫
    (Scheme.Modules.pullback f).map z ≫ (pullbackTensorPowModuleIso f M n).hom)
      (tensorPowModuleAddIso_zero_right S M n).symm) ?_
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫ (pullbackTensorPowModuleIso f M n).hom)
      (laxMul_unitor (Scheme.Modules.pullback f) (tensorPowModuleZeroIso S M)
        (tensorPowModule S M (n : ℤ))))) ?_
  refine Eq.trans (unit_right_square _ (tensorPowModuleZeroIso X
        ((Scheme.Modules.pullback f).obj M)).hom
      (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv
      (tensorPowModuleZeroIso X ((Scheme.Modules.pullback f).obj M)).inv_hom_id
      (pullbackTensorPowModuleIso f M n).hom (pullbackTensorPowModuleIso f M 0).hom hg₀) ?_
  exact congrArg (fun z ↦ ((pullbackTensorPowModuleIso f M n).hom ⊗ₘ
    (pullbackTensorPowModuleIso f M 0).hom) ≫ z)
    (tensorPowModuleAddIso_zero_right X ((Scheme.Modules.pullback f).obj M) n)

/-- **Pullback carries the canonical multiplication of the tensor powers to the canonical
multiplication of the tensor powers of the pullback.** For a morphism of schemes `f : X ⟶ S` and
an invertible `𝒪_S`-module `M`: pulling back the multiplication
`M^{⊗ n} ⊗ M^{⊗ m} ≅ M^{⊗ (n+m)}` of Stacks Tag 01CU and then splitting the power in degree
`n + m` by `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` agrees with splitting first — by
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, Stacks Tag 01CD on a morphism of schemes,
followed by the comparisons in degrees `n` and `m` — and multiplying afterwards. -/
theorem pullbackTensorPowModuleIso_tensorPowModuleAddIso (n m : ℕ) :
    (Scheme.Modules.pullback f).map (tensorPowModuleAddIso S M (n : ℤ) (m : ℤ)).hom ≫
        (pullbackTensorPowModuleIso f M (n + m)).hom =
      (pullbackTensorModulesIso f (tensorPowModule S M (n : ℤ))
          (tensorPowModule S M (m : ℤ))).hom ≫
        ((pullbackTensorPowModuleIso f M n).hom ⊗ₘ (pullbackTensorPowModuleIso f M m).hom) ≫
          (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (n : ℤ) (m : ℤ)).hom := by
  let _ : (Scheme.Modules.pullback f).Monoidal := pullbackComparisonMonoidal f.toLRSHom.toShHom
  refine eq_comp_of_comp_eq _ (μ (Scheme.Modules.pullback f) (tensorPowModule S M (n : ℤ))
      (tensorPowModule S M (m : ℤ)))
    (Functor.Monoidal.δ_μ (Scheme.Modules.pullback f) _ _) ?_
  exact comparison_mulFamily (Scheme.Modules.pullback f)
    (P := fun k ↦ tensorPowModule S M (k : ℤ))
    (Q := fun k ↦ tensorPowModule X ((Scheme.Modules.pullback f).obj M) (k : ℤ))
    (N := tensorPowModule S M 1)
    (N' := tensorPowModule X ((Scheme.Modules.pullback f).obj M) 1)
    (fun i j ↦ (tensorPowModuleAddIso S M (i : ℤ) (j : ℤ)).hom)
    (fun i j ↦ (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M)
      (i : ℤ) (j : ℤ)).hom)
    (fun i ↦ (tensorPowModuleAddIso S M (i : ℤ) 1).hom)
    (fun i ↦ (tensorPowModuleAddIso X ((Scheme.Modules.pullback f).obj M) (i : ℤ) 1).hom)
    (fun i ↦ (pullbackTensorPowModuleIso f M i).hom) (pullbackPowOneIso f M).hom
    (tensorPowModuleAddIso_assoc_one S M)
    (tensorPowModuleAddIso_assoc_one X ((Scheme.Modules.pullback f).obj M))
    (fun i ↦ Iso.isIso_hom (tensorPowModuleAddIso S M (i : ℤ) 1))
    (fun i ↦ comp_eq_of_eq_comp _ _ (Functor.Monoidal.μ_δ (Scheme.Modules.pullback f) _ _)
      (pullbackTensorPowModuleIso_zero_square f M i))
    (fun i ↦ comp_eq_of_eq_comp _ _ (Functor.Monoidal.μ_δ (Scheme.Modules.pullback f) _ _)
      (pullbackTensorPowModuleIso_succ_square f M i)) n m

end Stacks.RelativeVeryAmple

end
