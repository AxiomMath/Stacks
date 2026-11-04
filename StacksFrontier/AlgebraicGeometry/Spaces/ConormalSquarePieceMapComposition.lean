module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleCompositionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquareComparisonSpacesUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMapComposition

/-!
# Towards the composition law for the canonical map of a square of immersions

Let
```
Z₁ --i₁--→ X₁
|          |
f₁         g₁
↓          ↓
Z₂ --i₂--→ X₂
|          |
f₂         g₂
↓          ↓
Z₃ --i₃--→ X₃
```
be two commutative squares of algebraic spaces over a scheme `S` stacked vertically.
[Stacks Project, Tag 04G2] part (3) asserts that the canonical maps of
[Stacks Project, Tag 04CP] compose.
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionLaw.lean` proves that for a square
of **closed subspaces** and the defining ideal sheaves of [Stacks Project, Tag 03MB], and that is
where the tag's attribute sits. This file is about the same law for a square of **arbitrary**
morphisms — `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` in each degree, and hence
`AlgebraicGeometry.Space.conormalMapOfImmersions` at the generality of immersions, which is what
the reduction of part (2) of the tag to a pair of ambient opens needs.

The **comparison half** of that law is proved here, unconditionally, together with the
reassociations an assembly by hand would need.  **The law itself is proved**, in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapCompositionLaw.lean`, as
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp` and
`AlgebraicGeometry.Space.conormalMapOfImmersions_comp` — but *not* by a direct assembly of
the steps below.  The implementation notes below explain why.

## What is proved

* `AlgebraicGeometry.Space.squarePullbackCompIso_paste` and
  `AlgebraicGeometry.Space.squarePullbackCompIso_paste_app`: **the square comparisons of two
  vertically stacked squares paste**, for arbitrary morphisms. This is
  `AlgebraicGeometry.Space.conormalPullbackCompIso_paste` with the inclusions of closed subspaces
  replaced by plain variables, which is all that proof uses: the three-factor presentation
  `AlgebraicGeometry.Space.squarePullbackCompIso_hom` together with the associativity coherence
  of `AlgebraicGeometry.Space.modulePullbackCompIso`.
* `AlgebraicGeometry.Space.pasted_app_split`, `…_split_lower`, `…_lead`, `…_mid`, `…_last`: the
  pasted natural transformation read at a module, one component at a time.
* `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_outer_comp`: the degree-`n` map of
  the outer rectangle with the two maps of ideal sheaves split off as a right factor, using the
  composition law `AlgebraicGeometry.Space.kernelIdealSquareMap_comp`.
* `AlgebraicGeometry.Space.squarePullbackCompIso_hom_naturality_kernelIdealSquareMap` and
  `AlgebraicGeometry.Space.comp_conormalAlgebraSquarePieceMap_tail`: the tail of the composite
  the other way round the square.
* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_piece`: the two spellings of the
  degree-`n` piece of the conormal algebra bridged inside a component of the composition
  comparison, through `HEq` — the device
  `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_conormalModule` uses for the closed
  case.

## Why the assembly is not done here

The assembly —
`conormalAlgebraSquarePieceMap_comp` and `conormalMapOfImmersions_comp` — is not blocked merely by the
definitional equality between the two spellings `(conormalAlgebra i').piece n` and
`(modulePullback i').obj (kernelIdealSheafZPow i' n).toSheafOfModules` of the degree-`n`
piece, equal by `AlgebraicGeometry.Space.conormalAlgebra_piece` (`rfl`, through
the unfolding of `AlgebraicGeometry.Space.conormalAlgebra` to `toposPullbackGradedAlgebra` of
`kernelIdealGradedAlgebra`), which fits a heartbeat budget once and not twice.  Even with the whole chain
carried out at the second spelling, where the first never occurs, the steps fail, each as its
own declaration with its own budget:

* the composite step by `eq_whisker` and `Functor.map_comp` — kernel deterministic timeout;
* the same step as a single application of the generic
  `Stacks.CategoryTheory.map_comp_split`, with the factorisation as a hypothesis and **no**
  `piece` spelling anywhere — kernel deterministic timeout;
* the five-component expansion of the pasted transformation assembled in one term — kernel
  timeout, while each of its five components alone is free;
* the same expansion split into three declarations, **at a variable module**, where no spelling
  of the degree-`n` piece occurs at all — kernel timeout in the middle one;
* `attribute [local irreducible] modulePullback modulePullbackCompIso squarePullbackCompIso`,
  which the closed case uses, makes the **statements** here fail to typecheck instead, since they
  genuinely need the defeq.  No attribute reaches the kernel.

So the obstruction is not a particular spelling of a particular object: it is that *any*
intermediate statement written out at these morphisms hands the kernel two applications of
`CategoryTheory.Functor.map`, or of `CategoryTheory.NatTrans.app`, whose implicit objects are
definitionally but not syntactically equal, and reducing those projections unfolds
`AlgebraicGeometry.Space.modulePullback` to its construction by sheafification.  Splitting into
more declarations does not help, because each split introduces one more such statement.

The law is therefore proved with **no** intermediate statement at the geometric instance, by
instantiating a lemma proved at variables: `Stacks.CategoryTheory.square_map_comp` of
`StacksFrontier/CategoryTheory/SquareMapComposition.lean`, whose five hypotheses are, at the
instantiation, `AlgebraicGeometry.Space.squarePullbackCompIso_paste` of this file,
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp`, and three instances of a `rfl`.  See
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapCompositionLaw.lean`.

What this file keeps is the comparison half of the law and the reassociations around it, which
are used there and elsewhere.  No declaration in it takes a hypothesis naming any part of a
tag's own content.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z₁ Z₂ Z₃ X₁ X₂ X₃ : AlgebraicSpaces B S hS} (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) (i₃ : Z₃ ⟶ X₃)
    (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (hsq : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃)

/-! ### Pasting the two square comparisons -/

/-- **The square comparisons of two vertically stacked squares paste.**

This is `AlgebraicGeometry.Space.conormalPullbackCompIso_paste` with the inclusions of closed
subspaces replaced by arbitrary morphisms, which is all that proof uses: the three-factor
presentation `AlgebraicGeometry.Space.squarePullbackCompIso_hom` and the associativity coherence
of the composition comparison of [Stacks Project, Tag 03LU]. -/
theorem squarePullbackCompIso_paste :
    (squarePullbackCompIso B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq).hom ≫
        Functor.whiskerRight (modulePullbackCompIso B S hS g₁ g₂).inv
          (modulePullback B S hS i₁) =
      Functor.whiskerLeft (modulePullback B S hS i₃)
          (modulePullbackCompIso B S hS f₁ f₂).inv ≫
        Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
          (modulePullback B S hS f₁) ≫
        Functor.whiskerLeft (modulePullback B S hS g₂)
          (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom := by
  rw [squarePullbackCompIso_hom, squarePullbackCompIso_hom, squarePullbackCompIso_hom,
    Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  conv_lhs => rw [← modulePullbackCompIso_assoc_inv B S hS i₁ g₁ g₂]
  conv_rhs =>
    rw [modulePullbackCompIso_inv_comp_whiskerRight_hom_assoc B S hS f₁ f₂ i₃,
      modulePullbackCompIso_inv_eqToHom_right_assoc B S hS f₁ hsq₂.symm,
      ← modulePullbackCompIso_assoc_inv_assoc B S hS f₁ i₂ g₂,
      whiskerLeft_inv_hom_cancel,
      modulePullbackCompIso_inv_eqToHom_left_assoc B S hS hsq₁.symm g₂,
      eqToHom_trans_assoc]

/-- **The pasting of the two square comparisons, at a module.**  The comparison of the outer
rectangle, followed by the inverse image along `i₁` of the composition comparison of the two
lower edges, is the pasted composite of the comparisons of the two squares. -/
theorem squarePullbackCompIso_paste_app (M : Modules.{u, u} B S hS X₃.1 X₃.2) :
    (squarePullbackCompIso B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq).hom.app M ≫
        (modulePullback B S hS i₁).map ((modulePullbackCompIso B S hS g₁ g₂).inv.app M) =
      (Functor.whiskerLeft (modulePullback B S hS i₃)
            (modulePullbackCompIso B S hS f₁ f₂).inv ≫
          Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
            (modulePullback B S hS f₁) ≫
          Functor.whiskerLeft (modulePullback B S hS g₂)
            (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom).app M :=
  (congrArg
      (fun t ↦ (squarePullbackCompIso B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq).hom.app M ≫ t)
      (Functor.whiskerRight_app (modulePullbackCompIso B S hS g₁ g₂).inv
        (modulePullback B S hS i₁) M).symm).trans
    ((NatTrans.comp_app (squarePullbackCompIso B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq).hom
          (Functor.whiskerRight (modulePullbackCompIso B S hS g₁ g₂).inv
            (modulePullback B S hS i₁)) M).symm.trans
      (NatTrans.congr_app
        (squarePullbackCompIso_paste B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ hsq) M))

/-! ### The steps of the composition law -/

section Law

/-- The two spellings of the degree-`n` piece of the conormal algebra, bridged inside a component
of the composition comparison.

The two objects are equal by `AlgebraicGeometry.Space.conormalAlgebra_piece`, which holds by
`rfl`, but `CategoryTheory.NatTrans.app` depends on the object it is evaluated at, so `congrArg`
does not typecheck; the bridge goes through `HEq`, exactly as
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_conormalModule` does for the closed
case. -/
theorem modulePullbackCompIso_inv_app_piece (a : Z₁ ⟶ Z₂) (b : Z₂ ⟶ Z₃) (n : ℤ) :
    (modulePullbackCompIso B S hS a b).inv.app
        ((modulePullback B S hS i₃).obj
          (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules) =
      (modulePullbackCompIso B S hS a b).inv.app ((conormalAlgebra B S hS i₃).piece n) := by
  have hobj : (modulePullback B S hS i₃).obj
      (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules =
      (conormalAlgebra B S hS i₃).piece n := (conormalAlgebra_piece B S hS i₃ n).symm
  have hheq : HEq
      ((modulePullbackCompIso B S hS a b).inv.app
        ((modulePullback B S hS i₃).obj
          (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules))
      ((modulePullbackCompIso B S hS a b).inv.app
        ((conormalAlgebra B S hS i₃).piece n)) := by
    rw [hobj]
  exact eq_of_heq hheq

/-- The degree-`n` canonical map of the outer rectangle, with the inverse image along `i₁` of the
two maps of ideal sheaves split off as a right factor. -/
theorem conormalAlgebraSquarePieceMap_eq_outer_comp (n : ℤ) :
    conormalAlgebraSquarePieceMap B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n =
      ((squarePullbackCompIso B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq).hom.app
            (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules ≫
          (modulePullback B S hS i₁).map
            ((modulePullbackCompIso B S hS g₁ g₂).inv.app
              (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules)) ≫
        (modulePullback B S hS i₁).map
          ((modulePullback B S hS g₁).map
              (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n) ≫
            kernelIdealSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ n) :=
  (conormalAlgebraSquarePieceMap_eq_comp B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n).trans
    ((whisker_eq _
          ((congrArg (modulePullback B S hS i₁).map
              (kernelIdealSquareMap_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ hsq n)).trans
            ((modulePullback B S hS i₁).map_comp _ _))).trans
      (Category.assoc _ _ _).symm)

/-- The naturality of the square comparison of the upper square at the map of ideal sheaves of
the lower one.  Its own declaration, for the reason
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_app_naturality_comp` records. -/
theorem squarePullbackCompIso_hom_naturality_kernelIdealSquareMap (n : ℤ) :
    (modulePullback B S hS f₁).map
          ((modulePullback B S hS i₂).map
            (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n)) ≫
        (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom.app
          (kernelIdealSheafZPow B S hS i₂ n).toSheafOfModules =
      (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom.app
            ((modulePullback B S hS g₂).obj
              (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules) ≫
        (modulePullback B S hS i₁).map
          ((modulePullback B S hS g₁).map
            (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n)) :=
  (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom.naturality
    (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n)

/-- The tail of that composite, with the map of the upper square replaced by its two factors and
the naturality of the square comparison applied.  Its own declaration, for the same reason. -/
theorem comp_conormalAlgebraSquarePieceMap_tail (n : ℤ) :
    (modulePullback B S hS f₁).map
          ((modulePullback B S hS i₂).map
            (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n)) ≫
        conormalAlgebraSquarePieceMap B S hS i₁ i₂ f₁ g₁ hsq₁ n =
      (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom.app
            ((modulePullback B S hS g₂).obj
              (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules) ≫
        (modulePullback B S hS i₁).map
          ((modulePullback B S hS g₁).map
              (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n) ≫
            kernelIdealSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ n) :=
  (Stacks.CategoryTheory.comp_eq_of_split_and_square
        (conormalAlgebraSquarePieceMap_eq_comp B S hS i₁ i₂ f₁ g₁ hsq₁ n)
        (squarePullbackCompIso_hom_naturality_kernelIdealSquareMap
          B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ n)).trans
    (whisker_eq _ ((modulePullback B S hS i₁).map_comp _ _).symm)

/-- The pasted composite of the two square comparisons, read at a module as the composite of its
three components.  Each step is `rfl` — the component of a whiskering and of a composite of
natural transformations is what it is written as — and the steps are taken one at a time, as the
closed case in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionLaw.lean` does:
asking for the whole expansion at once is a kernel deterministic timeout. -/
theorem pasted_app_split (M : Modules.{u, u} B S hS X₃.1 X₃.2) :
    (Functor.whiskerLeft (modulePullback B S hS i₃)
            (modulePullbackCompIso B S hS f₁ f₂).inv ≫
          Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
            (modulePullback B S hS f₁) ≫
          Functor.whiskerLeft (modulePullback B S hS g₂)
            (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom).app M =
      (Functor.whiskerLeft (modulePullback B S hS i₃)
            (modulePullbackCompIso B S hS f₁ f₂).inv).app M ≫
        (Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
              (modulePullback B S hS f₁) ≫
            Functor.whiskerLeft (modulePullback B S hS g₂)
              (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom).app M :=
  rfl

/-- The lower two components of the pasted composite, split. -/
theorem pasted_app_split_lower (M : Modules.{u, u} B S hS X₃.1 X₃.2) :
    (Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
            (modulePullback B S hS f₁) ≫
          Functor.whiskerLeft (modulePullback B S hS g₂)
            (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom).app M =
      (Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
            (modulePullback B S hS f₁)).app M ≫
        (Functor.whiskerLeft (modulePullback B S hS g₂)
          (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom).app M :=
  rfl

/-- The leading component of the pasted composite. -/
theorem pasted_app_lead (M : Modules.{u, u} B S hS X₃.1 X₃.2) :
    (Functor.whiskerLeft (modulePullback B S hS i₃)
          (modulePullbackCompIso B S hS f₁ f₂).inv).app M =
      (modulePullbackCompIso B S hS f₁ f₂).inv.app
        ((modulePullback B S hS i₃).obj M) :=
  rfl

/-- The middle component of the pasted composite. -/
theorem pasted_app_mid (M : Modules.{u, u} B S hS X₃.1 X₃.2) :
    (Functor.whiskerRight (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom
          (modulePullback B S hS f₁)).app M =
      (modulePullback B S hS f₁).map
        ((squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂).hom.app M) :=
  rfl

/-- The last component of the pasted composite. -/
theorem pasted_app_last (M : Modules.{u, u} B S hS X₃.1 X₃.2) :
    (Functor.whiskerLeft (modulePullback B S hS g₂)
          (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom).app M =
      (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁).hom.app
        ((modulePullback B S hS g₂).obj M) :=
  rfl

end Law

end AlgebraicGeometry.Space

end
