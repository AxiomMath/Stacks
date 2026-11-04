module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaf cohomology along an adjunction with exact inverse image

Let `(C, J)` and `(D, K)` be sites and let `L ⊣ R` be an adjunction between their categories of
abelian sheaves, with `L : Sheaf J AddCommGrpCat ⥤ Sheaf K AddCommGrpCat` the inverse image and
`R` the direct image. Assume both functors are exact and the unit of the adjunction is an
isomorphism. This file shows that cohomology on `(D, K)` of the inverse image of a sheaf agrees
with its cohomology on `(C, J)`, naturally in the sheaf:

`L ⋙ Sheaf.functorH K n ≅ Sheaf.functorH J n`.

Cohomology here is Mathlib's `CategoryTheory.Sheaf.functorH`, the `Ext` group out of the constant
sheaf with value `ULift ℤ`. The comparison therefore has two ingredients: `L` induces bijections
on `Ext` groups (`Stacks.ExtAdjunction.mapExtAddHom_bijective`), and `L` carries the constant
sheaf of `J` to the constant sheaf of `K`.

## Main definitions and results

* `Stacks.ExtAdjunction.restrictSections`: restriction of sheaves along a continuous functor,
  followed by evaluation at a terminal object, is evaluation at the image of that object.
* `Stacks.ExtAdjunction.constantSheafPullbackIso`: the inverse image carries constant sheaves to
  constant sheaves.
* `Stacks.ExtAdjunction.enoughInjectives_sheaf`: abelian sheaves on an essentially small site
  form a category with enough injectives.
* `Stacks.ExtAdjunction.hComparison_bijective`: the comparison map on cohomology is bijective.
* `Stacks.ExtAdjunction.functorHComparisonIso`: the comparison, as an isomorphism of cohomology
  functors.

## Implementation notes

The constant-sheaf comparison is obtained from uniqueness of left adjoints rather than
constructed by hand: the constant sheaf functor of `J` followed by `L` is left adjoint to the
direct image followed by global sections on `(C, J)`, and that composite *is* global sections on
`(D, K)` — the direct image is precomposition with the site functor, so evaluating it at a
terminal object `T` of `C` is evaluation at the terminal object `G.obj T` of `D`, on the nose.
`restrictSections` is therefore `Iso.refl`.

Enough injectives on the big site is what the induction in
`Stacks.ExtAdjunction.extMap_bijective` consumes, and it is the one hypothesis that is not
formal: it comes from the sheaf category being Grothendieck abelian, which for a site that is
only essentially small needs the transport to a small model. The statement is deliberately
phrased with a *single* universe variable `t` for the coefficients, so that the application site
instantiates it rather than asking the universe unifier to solve `?t + 1 =?= max (u + 2) (v + 1)`
for `IsGrothendieckAbelian AddCommGrpCat`, which it will not do.

Naturality of the comparison is proved as the standalone lemma `hComparison_naturality`, stated
in `Ext` types, and the natural transformation's square is discharged by `exact` from it. Rewriting
inside the square directly does not work: its elements are typed through the coercion of
`AddCommGrpCat.of (Sheaf.H F n)`, which is not type-correct at `implicit` transparency, so `rw`
refuses.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

universe t a u₁ v₁ u₂ v₂

namespace Stacks.ExtAdjunction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  {L : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf K AddCommGrpCat.{t}}
  {R : Sheaf K AddCommGrpCat.{t} ⥤ Sheaf J AddCommGrpCat.{t}}

/-- Restriction along a continuous functor commutes with evaluation at a terminal object. -/
def restrictSections (G : C ⥤ D) (A : Type*) [Category* A] [G.IsContinuous J K] (T : C) :
    G.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op (G.obj T)) :=
  Iso.refl _

/-- A sheaf category on an essentially small site with abelian-group coefficients in the
universe witnessing the smallness has enough injectives, being a Grothendieck abelian
category. -/
@[sga "4 V 0.2.1" "special case"]
theorem enoughInjectives_sheaf {C' : Type u₁} [Category.{v₁} C'] (K' : GrothendieckTopology C')
    [EssentiallySmall.{t} C']
    [∀ Y : C'ᵒᵖ,
      HasLimitsOfShape (StructuredArrow Y (equivSmallModel C').inverse.op) AddCommGrpCat.{t}]
    [HasSheafify ((equivSmallModel C').inverse.inducedTopology K') AddCommGrpCat.{t}] :
    EnoughInjectives (Sheaf K' AddCommGrpCat.{t}) := by
  have : HasSheafify K' AddCommGrpCat.{t} := hasSheafifyEssentiallySmallSite K' _
  have : IsGrothendieckAbelian.{t} (Sheaf K' AddCommGrpCat.{t}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  infer_instance

/-- The inverse image carries the constant sheaf to the constant sheaf. -/
def constantSheafPullbackIso (adj : L ⊣ R) {T : C} (hT : IsTerminal T) {T' : D}
    (hT' : IsTerminal T')
    (hΓ : R ⋙ (sheafSections J AddCommGrpCat.{t}).obj (op T) ≅
      (sheafSections K AddCommGrpCat.{t}).obj (op T')) :
    constantSheaf J AddCommGrpCat.{t} ⋙ L ≅ constantSheaf K AddCommGrpCat.{t} :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight ((constantSheafAdj J AddCommGrpCat.{t} hT).comp adj) hΓ)
    (constantSheafAdj K AddCommGrpCat.{t} hT')

variable [HasExt.{a} (Sheaf J AddCommGrpCat.{t})] [HasExt.{a} (Sheaf K AddCommGrpCat.{t})]
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (θ : constantSheaf J AddCommGrpCat.{t} ⋙ L ≅ constantSheaf K AddCommGrpCat.{t})

/-- The comparison map on sheaf cohomology. -/
def hComparison (n : ℕ) (F : Sheaf J AddCommGrpCat.{t}) :
    Ext.{a} ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift ℤ))) F n →+
      Ext.{a} ((constantSheaf K AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift ℤ)))
        (L.obj F) n :=
  ((Ext.mk₀ ((θ.app (AddCommGrpCat.of (ULift ℤ))).inv)).precomp (L.obj F) (zero_add n)).comp
    (L.mapExtAddHom _ F n)

/-- The comparison map sends `e` to the image of `e` under `L`, precomposed with the inverse of
`θ` at `ULift ℤ`. -/
lemma hComparison_apply (n : ℕ) (F : Sheaf J AddCommGrpCat.{t})
    (e : Ext.{a} ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift ℤ))) F n) :
    hComparison θ n F e =
      (Ext.mk₀ ((θ.app (AddCommGrpCat.of (ULift ℤ))).inv)).comp
        (e.mapExactFunctor L) (zero_add n) :=
  rfl

/-- The comparison map commutes with postcomposition by a morphism of sheaves `f` and its image
`L.map f`. -/
lemma hComparison_naturality (n : ℕ) {F F' : Sheaf J AddCommGrpCat.{t}} (f : F ⟶ F')
    (e : Ext.{a} ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift ℤ))) F n) :
    hComparison θ n F' (e.comp (Ext.mk₀ f) (add_zero n)) =
      (hComparison θ n F e).comp (Ext.mk₀ (L.map f)) (add_zero n) := by
  rw [hComparison_apply, hComparison_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

variable (adj : L ⊣ R) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{t})] [IsIso adj.unit]

include adj in
/-- If `L` has an exact right adjoint `R` whose unit is an isomorphism, and abelian sheaves on
`(D, K)` have enough injectives, the comparison map on cohomology is bijective. -/
lemma hComparison_bijective (n : ℕ) (F : Sheaf J AddCommGrpCat.{t}) :
    Function.Bijective (hComparison θ n F) :=
  (precomp_mk₀_bijective_of_isIso _ n).comp (mapExtAddHom_bijective adj _ F n)

/-- Cohomology on `(D, K)` of the inverse image agrees with cohomology on `(C, J)`. -/
def functorHComparisonIso (n : ℕ) : L ⋙ Sheaf.functorH K n ≅ Sheaf.functorH J n :=
  (NatIso.ofComponents
    (fun F ↦ (AddEquiv.ofBijective (hComparison θ n F)
      (hComparison_bijective θ adj n F)).toAddCommGrpIso)
    (by
      intro F F' f
      ext e
      exact hComparison_naturality θ n f e)).symm

end Stacks.ExtAdjunction

end
