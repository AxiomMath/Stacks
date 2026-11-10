module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLifting
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoMultiplicative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestrictionAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDifferentialGradedModule
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Base change along a quasi-isomorphism of sheaves of differential graded algebras

Let `(C, O)` be a ringed site and let `φ : A ⟶ B` be a unit-preserving homomorphism of sheaves
of differential graded `O`-algebras which induces an isomorphism on cohomology sheaves. The
source asserts that

`D(A, d) ⟶ D(B, d)`, `M ↦ M ⊗^𝐋_A B`

is an equivalence of categories, and proves it in four steps: base change is left adjoint to
restriction of scalars; restriction has a left derived extension given by restriction itself, so
the adjunction passes to the derived categories; the unit of the derived adjunction is invertible
because `φ` is a quasi-isomorphism of left differential graded `A`-modules, whence the functor is
fully faithful; and the kernel of the restriction functor
`D(B, d) ⟶ D(A, d)` is zero, whence the functor is an equivalence.

This file settles the *last* step, in the form in which the formal argument needs it, and the
formal argument itself. Concretely:

* restriction of scalars on the derived categories **reflects isomorphisms**. This is the content
  of "the kernel of the restriction functor is zero" in a form that does not presuppose a
  triangulated structure on the derived categories of a sheaf of differential graded algebras,
  which this development does not have. The proof is the one that the vanishing-kernel statement
  stands in for: a morphism of `D(B, d)` is a left fraction, restriction neither changes the
  underlying complexes nor reflects less than it preserves, and the quasi-isomorphisms are
  exactly the arrows that the localization functor inverts.

* an adjunction whose right adjoint reflects isomorphisms and whose unit is invertible is an
  equivalence: the triangle identity makes the restriction of the counit invertible, so the
  counit itself is. This replaces the appeal to the source's
  [Tag 09J1](https://stacks.math.columbia.edu/tag/09J1) and
  [Tag 07RB](https://stacks.math.columbia.edu/tag/07RB), which are statements about triangulated
  categories and about kernels of exact functors.

What is *not* here is the derived adjunction and the invertibility of its unit. Both are recorded
precisely in the implementation notes below, together with what they need.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.Hom.IsQuasiIso` is the hypothesis of the source: a
  homomorphism of sheaves of differential graded algebras induces an isomorphism on cohomology
  sheaves.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_of_isIso_toDerivedCategory_map` and
  `...isIso_toDerivedCategory_map_iff`: an arrow of the homotopy category becomes invertible in
  the derived category exactly when it is a quasi-isomorphism. So the class of
  quasi-isomorphisms is saturated.
* `SheafOfModules.DifferentialGradedModule.isIso_of_isIso_derivedRestriction_map` and
  `...reflectsIsomorphisms_derivedRestriction`: restriction of scalars on the derived categories
  reflects isomorphisms.
* `CategoryTheory.Adjunction.isEquivalence_of_isIso_unit_of_reflects_isIso`: an adjunction whose
  unit is invertible and whose right adjoint reflects isomorphisms is an equivalence.
* `SheafOfModules.DifferentialGradedModule.isEquivalence_of_isIso_unit_derivedRestriction`: any
  left adjoint of restriction of scalars on the derived categories whose unit is invertible is an
  equivalence of categories.

## Implementation notes

**Tag 0FTZ itself is in the module
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoDerivedEquivalence`**,
as `SheafOfModules.DifferentialGradedModule.isEquivalence_derivedExtension`, which constructs the
derived extension of scalars, its adjunction with restriction and the invertibility of its unit,
and then applies `isEquivalence_of_isIso_unit_derivedRestriction` of this file. The statement
`isEquivalence_derived_of_isQuasiIso` below, which takes those inputs as the bundle
`DerivedBaseChangeData`, is an older auxiliary form of the same argument and carries no tag.

**What the bundle still needs, field by field.** Four of its eleven fields can be written down
today, and the list below has been checked against the merged base by compiling each claim.

* `tensorData` — **available**. `SheafOfModules.RelativeTensor.tensorFunctorDataDgTensorRight`
  of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedBimoduleTensorUniversal.lean`
  applied to `φ.toBimodule hφ` is a term of the required type. It constrains the universes: the
  algebra component universe and the module universe must both be the universe of the ringed
  site.
* `IsKFlat`, `leftTensor`, `leftTensor_acyclic` — **available**, at
  `SheafOfModules.RelativeTensor.IsKFlat` and `SheafOfModules.RelativeTensor.dgTensor`, where
  the acyclicity clause is the definition of the former.
* `exists_isKFlat` — **available**. `SheafOfModules.DifferentialGradedModule.exists_flat_quasiIso`
  (Tag 0FSH) supplies the resolution, and
  `SheafOfModules.DifferentialGradedModule.acyclic_cone_iff_quasiIso` turns its
  quasi-isomorphism into the acyclicity of the cone. This needs `HasWeakSheafify X.J (Type _)`
  on the site, which Tag 0FSH carries.
* `derived` — **available once the exactness data below is**. It is
  `SheafOfModules.DifferentialGradedModule.derivedTensor` of [Stacks, Tag 0FTG] for the identity
  pullback, fed `tensorData` and
  `SheafOfModules.DifferentialGradedModule.GoodResolutionData.flat`. Its source and target are
  the two derived categories that `adj` needs.
* `adj`, `restrictionExtensionIso`, `unit_app` — **not yet available**. See 1 below;
  `restrictionExtensionIso` is `derivedTensorObjIso` of Tag 0FTG read through restriction of
  scalars, and `unit_app` is the compatibility of the derived unit with the underived one.
* `coneAlgebra`, `coneAlgebraIso` — the cone of `φ` read as a *left* differential graded
  `A`-module, the library's cone being for right modules.
* `unitConeIso` — tensoring as a functor of differential graded categories. This is the cone in
  the *bimodule* variable, `P ⊗_A cone(φ)`, and is a different statement from the `coneIso`
  field of `SheafOfModules.DifferentialGradedModule.PullbackTensorExactnessData`, which is the
  cone in the *module* variable.

Feeding `derivedTensor` means producing a
`SheafOfModules.DifferentialGradedModule.PullbackTensorExactnessData` for the identity pullback.
Its `coneIso` field is the exactness of [Stacks, Tag 0FTE]; its `acyclic_pullbackTensor` field
is [Stacks, Tag 0FSI] part (1), which in this development is
`SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isKFlat_of_acyclic`, which needs
only the K-flatness and the acyclicity of the module, and at a tensor product with a bimodule
`SheafOfModules.DifferentialGradedModule.acyclic_of_isTensorProduct_of_isKFlat_of_acyclic`.

1. *The derived adjunction* `- ⊗^𝐋_{A, φ} B ⊣ res_φ`. The underived adjunction is
   `SheafOfModules.DifferentialGradedModule.extensionRestrictionAdjunction` of
   `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedRestrictionAdjunction.lean`,
   and it descends to the homotopy categories by
   `SheafOfModules.DifferentialGradedModule.HomotopyCategory.descendAdjunction`. The derived
   adjunction then follows from
   `CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`
   (Tag 09T5, the functorial form of Tag 0FND) exactly as
   `SheafOfModules.DifferentialGradedModule.exists_adjunction_derivedPullback_derivedPushforward`
   (Tag 0FTR) does for pullback and pushforward. Of its two inputs the right-hand one is already
   proved: it is
   `SheafOfModules.DifferentialGradedModule.isRightDerivedValueAt_homotopyRestrictionValueCocone`.
   The left-hand one — a left derived value cone for base change at every object of
   `K(Mod(A, d))` — is the open piece, and it cannot be had for free, since base change does not
   invert quasi-isomorphisms. It is what a class of K-flat resolutions buys, and Tag 0FTF now
   produces exactly that: `rigidDerivedPullbackTensor` is a Kan extension along the localization
   functor and
   `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_of_isIso_app_of_isGood` is its
   left-derived-functor witness. So the work here is to read that witness as a left derived
   value cone and feed it to Tag 09T5, not to build a new theory.

2. *Invertibility of the unit.* At a K-flat module `P` the unit of the derived adjunction is the
   unit `P ⟶ res_φ(P ⊗_A B)` of the underived one, namely
   `SheafOfModules.DifferentialGradedModule.extensionUnit`, and the source's argument is that its
   cone is `P ⊗_A cone(A ⟶ B)`, which is acyclic because `P` is K-flat and `φ` is a
   quasi-isomorphism. That identification of cones is the analogue, in the left-hand variable, of
   the clause `DerivedTensorCounitData.leftTensorConeIso` which
   `SheafOfModules.DifferentialGradedModule.isIso_counit_app_of_isKFlatLeft` (Tag 0FTK) uses in
   the right-hand one; neither it nor the cone of `A ⟶ B` as a *left* differential graded
   `A`-module exists here.

**Hypotheses not in the source.** Two, both of them ambient rather than mathematical. The site
is required to admit sheafification for `AddCommGrp`-valued sheaves, which is what makes the
category of sheaves of modules abelian and the derived category exist at all, and it is already
required by `SheafOfModules.DifferentialGradedModule.derivedCategory`. And the derived category
of sheaves of modules is required to exist in a fixed universe, `HasDerivedCategory`, which is
what `SheafOfModules.DifferentialGradedModule.derivedForget` needs. The left calculus of
fractions on the quasi-isomorphisms of `K(Mod(B, d))`, which the source proves as part of
[Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4), is *not* a hypothesis here: it is
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions`.

**Why the last section is over a ringed site.** The results that use the calculus of fractions
are stated for a sheaf of differential graded algebras on a ringed site, which is the
setting of the source, rather than for one on an arbitrary sheaf of rings on a site. This is not
a convenience: it is what makes the calculus of fractions available at all. A left calculus of
fractions for `Qis` is obtained from the acyclic objects as a triangulated subcategory of
`K(Mod(B, d))`,
and the triangulated structure of
`SheafOfModules.DifferentialGradedModule.HomotopyCategory` (Tag 0FS7) is built from the
differential graded category of right modules and its cones
(`SheafOfModules.DifferentialGradedModule.dgCategoryData` and
`SheafOfModules.DifferentialGradedModule.coneSituation`, Tag 0FS6), both of which are constructed
over a ringed site; over an arbitrary sheaf of rings `K(Mod(A, d))` carries not even a shift.
The declarations that do not use the calculus of fractions are left at the wider generality.

**Where the saturation statement comes from.** That an arrow of `K(Mod(A, d))` inverted by the
localization functor is a quasi-isomorphism is not formal: it uses that the quasi-isomorphisms
are the arrows inverted by the forgetful functor to the derived category of sheaves of modules
(`...quasiIsomorphisms_iff_isIso_homotopyForget`, Tag 0FT4), which factors through `D(A, d)`.

## References

* [Stacks Project, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ)
* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 07RB](https://stacks.math.columbia.edu/tag/07RB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t a m v u

/-! ### An adjunction with invertible unit and conservative right adjoint -/

namespace CategoryTheory.Adjunction

/-- **An adjunction whose unit is invertible and whose right adjoint reflects isomorphisms is an
equivalence.** The triangle identity `η_{G Y} ≫ G(ε_Y) = 𝟙` exhibits `G(ε_Y)` as the inverse of
an isomorphism, so `G` carries the counit to an isomorphism and therefore the counit is one.

This is the formal content of the last step of
[Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ), where it is obtained from
[Tag 07RB](https://stacks.math.columbia.edu/tag/07RB) and
[Tag 09J1](https://stacks.math.columbia.edu/tag/09J1): a fully faithful exact functor between
triangulated categories whose right adjoint has vanishing kernel is an equivalence. Vanishing of
the kernel of an exact functor between triangulated categories is equivalent to reflecting
isomorphisms, and the statement below is the one that does not mention triangles. -/
theorem isEquivalence_of_isIso_unit_of_reflects_isIso {D : Type u} [Category.{v} D]
    {D' : Type w} [Category.{t} D'] {L : D ⥤ D'} {G : D' ⥤ D} (adj : L ⊣ G)
    (hu : ∀ X : D, IsIso (adj.unit.app X))
    (hG : ∀ (X Y : D') (g : X ⟶ Y), IsIso (G.map g) → IsIso g) :
    L.IsEquivalence := by
  have hc : ∀ Y : D', IsIso (adj.counit.app Y) := by
    intro Y
    have := hu (G.obj Y)
    have heq : inv (adj.unit.app (G.obj Y)) = G.map (adj.counit.app Y) :=
      IsIso.inv_eq_of_hom_inv_id (adj.right_triangle_components Y)
    refine hG _ _ _ ?_
    rw [← heq]
    infer_instance
  have := hu
  have := hc
  exact adj.toEquivalence.isEquivalence_functor

end CategoryTheory.Adjunction

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### A quasi-isomorphism of sheaves of differential graded algebras -/

namespace DifferentialGradedAlgebra

variable [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- A homomorphism of sheaves of differential graded algebras *is a quasi-isomorphism* when it
induces an isomorphism on cohomology sheaves, that is when the induced morphism of underlying
cochain complexes of sheaves of modules is a quasi-isomorphism.

This is the hypothesis of [Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ). It is
the same condition as `SheafOfModules.IsCohomologyIso` applied to
`DifferentialGradedAlgebra.Hom.toHomologicalComplex`, spelled with Mathlib's `QuasiIso` because
that is the spelling under which the quasi-isomorphisms of the homotopy category of right
differential graded modules are defined in
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms`. -/
def Hom.IsQuasiIso (φ : A ⟶ B) : Prop :=
  QuasiIso φ.toHomologicalComplex

/-- A quasi-isomorphism of sheaves of differential graded algebras is an isomorphism on the
cohomology sheaf of every degree. -/
theorem Hom.IsQuasiIso.isIso_homologyMap {φ : A ⟶ B} (hφ : φ.IsQuasiIso) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap φ.toHomologicalComplex n) :=
  (quasiIso_iff_isIso_homologyMap φ.toHomologicalComplex).1 hφ n

/-- An isomorphism on the cohomology sheaf of every degree is a quasi-isomorphism of sheaves of
differential graded algebras. -/
theorem Hom.isQuasiIso_of_isIso_homologyMap {φ : A ⟶ B}
    (hφ : ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap φ.toHomologicalComplex n)) :
    φ.IsQuasiIso :=
  (quasiIso_iff_isIso_homologyMap φ.toHomologicalComplex).2 hφ

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory.{w} (SheafOfModules.{m} R)]

/-! ### The quasi-isomorphisms are the arrows inverted by the localization functor -/

/-- An arrow of the homotopy category of right differential graded `A`-modules which becomes
invertible in the derived category `D(A, d)` is a quasi-isomorphism. Together with
`CategoryTheory.Localization.inverts` this says that the quasi-isomorphisms are *exactly* the
arrows inverted by the localization functor, that is that they are a saturated class.

The forgetful functor `K(Mod(A, d)) ⥤ D(Mod(O))` inverts precisely the quasi-isomorphisms
(`quasiIsomorphisms_iff_isIso_homotopyForget`) and factors through `D(A, d)`
(`toDerivedCategory_comp_derivedForget`), so an arrow inverted by the localization functor is
inverted by it. -/
theorem quasiIsomorphisms_of_isIso_toDerivedCategory_map
    (A : DifferentialGradedAlgebra.{t, a} R) {X Y : HomotopyCategory.{t, a, m} A} (ψ : X ⟶ Y)
    (hψ : IsIso ((toDerivedCategory.{t, a, m} A).map ψ)) :
    quasiIsomorphisms.{t, a, m} A ψ := by
  rw [quasiIsomorphisms_iff_isIso_homotopyForget.{w} A ψ]
  have h : IsIso ((toDerivedCategory.{t, a, m} A ⋙ derivedForget.{w, t, a, m} A).map ψ) := by
    have := hψ
    exact inferInstanceAs (IsIso ((derivedForget.{w, t, a, m} A).map
      ((toDerivedCategory.{t, a, m} A).map ψ)))
  rwa [toDerivedCategory_comp_derivedForget.{w} A] at h

/-- An arrow of the homotopy category of right differential graded `A`-modules becomes invertible
in the derived category `D(A, d)` exactly when it is a quasi-isomorphism. -/
theorem isIso_toDerivedCategory_map_iff (A : DifferentialGradedAlgebra.{t, a} R)
    {X Y : HomotopyCategory.{t, a, m} A} (ψ : X ⟶ Y) :
    IsIso ((toDerivedCategory.{t, a, m} A).map ψ) ↔ quasiIsomorphisms.{t, a, m} A ψ :=
  ⟨quasiIsomorphisms_of_isIso_toDerivedCategory_map.{w} A ψ,
    Localization.inverts (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A) ψ⟩

/-! ### Restriction of scalars on the derived categories reflects isomorphisms -/

section Conservative

/-! The ambient setting of this section is a ringed site, as in the source. The argument below
writes a morphism of the derived category as a left fraction, so it needs a left calculus of
fractions on the quasi-isomorphisms, and that is **taken from the library and not assumed**:
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedQuasiIsoMultiplicative.lean` is
an instance, Tag 0FT4 axioms MS2 and MS3, resting on the triangulated structure of
`K(Mod(A, d))` which Tag 0FS7,
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.instIsTriangulated`, supplies. The
statements below therefore carry no hypothesis beyond the ambient ringed site. -/

variable {X : AlgebraicGeometry.RingedSite.{t, t, t}}
  [HasSheafify X.J AddCommGrpCat.{m}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasDerivedCategory.{w} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  {A B : DifferentialGradedAlgebra.{t, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- Restriction of scalars on the derived categories reflects isomorphisms between the images of
objects of the homotopy category. Such a morphism is a left fraction `Q(f) ≫ Q(s)⁻¹`; since `Q(s)`
is already invertible, the hypothesis says that `res_φ Q(f)` is invertible, hence so is
`Q_A(res_φ f)`, hence `res_φ f` is a quasi-isomorphism and therefore so is `f`, because
restriction reflects quasi-isomorphisms. -/
theorem isIso_of_isIso_derivedRestriction_map_toDerivedCategory
    {M N : HomotopyCategory.{t, a, m} B}
    (g : (toDerivedCategory.{t, a, m} B).obj M ⟶ (toDerivedCategory.{t, a, m} B).obj N)
    (hg : IsIso ((derivedRestriction.{t, a, m} φ hφ).map g)) :
    IsIso g := by
  obtain ⟨ψ, rfl⟩ := Localization.exists_leftFraction (toDerivedCategory.{t, a, m} B)
    (quasiIsomorphisms.{t, a, m} B) g
  have hs : IsIso ((toDerivedCategory.{t, a, m} B).map ψ.s) :=
    Localization.inverts (toDerivedCategory.{t, a, m} B) (quasiIsomorphisms.{t, a, m} B) _ ψ.hs
  have hmap : ψ.map (toDerivedCategory.{t, a, m} B)
        (Localization.inverts (toDerivedCategory.{t, a, m} B)
          (quasiIsomorphisms.{t, a, m} B)) =
      (toDerivedCategory.{t, a, m} B).map ψ.f ≫
        inv ((toDerivedCategory.{t, a, m} B).map ψ.s) :=
    rfl
  rw [hmap] at hg
  rw [Functor.map_comp, Functor.map_inv] at hg
  have := hg
  have h1 : IsIso ((toDerivedCategory.{t, a, m} B ⋙
      derivedRestriction.{t, a, m} φ hφ).map ψ.f) :=
    IsIso.of_isIso_comp_right
      ((derivedRestriction.{t, a, m} φ hφ).map ((toDerivedCategory.{t, a, m} B).map ψ.f))
      (inv ((derivedRestriction.{t, a, m} φ hφ).map ((toDerivedCategory.{t, a, m} B).map ψ.s)))
  have h2 : IsIso ((homotopyRestriction.{t, a, m} φ hφ ⋙
      toDerivedCategory.{t, a, m} A).map ψ.f) :=
    (NatIso.isIso_map_iff (derivedRestrictionIso.{t, a, m} φ hφ) ψ.f).1 h1
  have h4 : quasiIsomorphisms.{t, a, m} B ψ.f :=
    (quasiIsomorphisms_homotopyRestriction_map_iff φ hφ ψ.f).1
      (quasiIsomorphisms_of_isIso_toDerivedCategory_map.{w} A _ h2)
  have : IsIso ((toDerivedCategory.{t, a, m} B).map ψ.f) :=
    Localization.inverts (toDerivedCategory.{t, a, m} B) (quasiIsomorphisms.{t, a, m} B) _ h4
  rw [hmap]
  infer_instance

/-- **Restriction of scalars on the derived categories reflects isomorphisms.** A morphism of
`D(B, d)` which becomes invertible in `D(A, d)` after restricting scalars along `φ` is already
invertible.

This is the step of [Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ) which says that
"the kernel of the restriction functor `D(B, d) ⟶ D(A, d)` is zero", in the form the formal
argument uses: in a triangulated category a morphism is invertible exactly when its cone
vanishes, so an exact functor reflects isomorphisms exactly when its kernel is zero, and the
proof below reaches the same conclusion without cones, by writing a morphism of the derived
category as a left fraction. -/
theorem isIso_of_isIso_derivedRestriction_map
    {X Y : derivedCategory.{t, a, m} B} (g : X ⟶ Y)
    (hg : IsIso ((derivedRestriction.{t, a, m} φ hφ).map g)) :
    IsIso g := by
  let eX := (toDerivedCategory.{t, a, m} B).objObjPreimageIso X
  let eY := (toDerivedCategory.{t, a, m} B).objObjPreimageIso Y
  have key : IsIso (eX.hom ≫ g ≫ eY.inv) := by
    refine isIso_of_isIso_derivedRestriction_map_toDerivedCategory.{w} φ hφ _ ?_
    have := hg
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have hrw : g = eX.inv ≫ (eX.hom ≫ g ≫ eY.inv) ≫ eY.hom := by simp
  rw [hrw]
  infer_instance

/-- Restriction of scalars on the derived categories reflects isomorphisms, as an instance of
`CategoryTheory.Functor.ReflectsIsomorphisms`. -/
theorem reflectsIsomorphisms_derivedRestriction :
    (derivedRestriction.{t, a, m} φ hφ).ReflectsIsomorphisms :=
  ⟨fun f _ => isIso_of_isIso_derivedRestriction_map.{w} φ hφ f inferInstance⟩

/-- **Tag 0FTZ, reduced to its derived adjunction and the invertibility of its unit.** Let `T` be
a left adjoint of restriction of scalars `res_φ : D(B, d) ⟶ D(A, d)` whose unit is invertible.
Then `T` is an equivalence of categories.

For the base change functor `- ⊗^𝐋_{A, φ} B` this is the conclusion of
[Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ); what is reduced away here is the
construction of the adjunction, which needs K-flat resolutions, and the invertibility of the
unit, which is where the hypothesis that `φ` is a quasi-isomorphism enters. See the
implementation notes of this file. -/
theorem isEquivalence_of_isIso_unit_derivedRestriction
    {T : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a, m} B}
    (adj : T ⊣ derivedRestriction.{t, a, m} φ hφ)
    (hu : ∀ X : derivedCategory.{t, a, m} A, IsIso (adj.unit.app X)) :
    T.IsEquivalence :=
  Adjunction.isEquivalence_of_isIso_unit_of_reflects_isIso adj hu
    fun _ _ g hg => isIso_of_isIso_derivedRestriction_map.{w} φ hφ g hg

end Conservative

/-! ### Base change along a quasi-isomorphism is an equivalence -/

section BaseChange

variable {X : AlgebraicGeometry.RingedSite.{t, t, t}}
  [HasSheafify X.J AddCommGrpCat.{a}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{a}]
  [HasSheafify X.J AddCommGrpCat.{m}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A B : DifferentialGradedAlgebra.{t, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- **Base change along `φ` on the derived categories, carried as data.** This bundles a tensor
product functor `- ⊗_{A, φ} B` with the bimodule `{}_A B_B`; a functor of the derived categories
adjoint to restriction of scalars and computed by base change on the K-flat modules; the K-flat
right differential graded `A`-modules, with the two clauses of the flat-resolution theory the
argument below uses — every module receives a quasi-isomorphism from a K-flat one, and a K-flat
module tensored with an acyclic left differential graded module is acyclic; and the cone of `φ`
read as a left differential graded `A`-module, whose tensor product with a module is the cone of
the unit `x ↦ x ⊗ 1` at that module.

None of it is constructible here: the tensor product of differential graded modules is pinned by
a universal property rather than built, and base change does not invert quasi-isomorphisms, so
its left derived extension needs a theory of K-flat resolutions. What is *not* carried is the
invertibility of the unit of the adjunction, which is the content of Tag 0FTZ and is proved
below. -/
structure DerivedBaseChangeData where
  /-- A tensor product functor `- ⊗_{A, φ} B` with the bimodule `{}_A B_B`, the datum of
  [Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE). -/
  tensorData : TensorFunctorData.{t, a, m, a, m, t, t} A B (φ.toBimodule hφ)
  /-- The derived base change `- ⊗^𝐋_{A, φ} B : D(A, d) ⥤ D(B, d)`. -/
  derived : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a, m} B
  /-- It is left adjoint to restriction of scalars: the adjunction `- ⊗_{A, φ} B ⊣ res_φ` of
  [Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) descends to the homotopy
  categories and then to the derived categories. -/
  adj : derived ⊣ derivedRestriction.{t, a, m} φ hφ
  /-- The K-flat right differential graded `A`-modules. -/
  IsKFlat : DifferentialGradedModule.{t, a, m} A → Prop
  /-- Every right differential graded `A`-module receives a quasi-isomorphism from a K-flat one,
  that is, admits a K-flat resolution. -/
  exists_isKFlat (M : DifferentialGradedModule.{t, a, m} A) :
    ∃ (P : DifferentialGradedModule.{t, a, m} A) (p : P ⟶ M),
      IsKFlat P ∧ (cone p).complex.Acyclic
  /-- On a K-flat module the derived base change is base change: the restriction of scalars of
  `P ⊗^𝐋_A B` is the image of `res_φ (P ⊗_A B)`. -/
  restrictionExtensionIso {P : DifferentialGradedModule.{t, a, m} A} (hP : IsKFlat P) :
    (derivedRestriction.{t, a, m} φ hφ).obj (derived.obj ((toDerivedCategory.{t, a, m} A).obj
        ((HomotopyCategory.quotient A).obj P))) ≅
      (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj
        ((restriction.{t, a, m} φ hφ).obj (tensorData.functor.obj P)))
  /-- Under that identification the unit of the derived adjunction at a K-flat module is the
  unit `x ↦ x ⊗ 1` of the underived one. -/
  unit_app {P : DifferentialGradedModule.{t, a, m} A} (hP : IsKFlat P) :
    adj.unit.app ((toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj P)) ≫
        (restrictionExtensionIso hP).hom =
      (toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map
        (extensionUnit φ hφ tensorData P))
  /-- The tensor product `P ⊗_A N` of a right differential graded `A`-module with a left one, a
  complex of sheaves of modules. -/
  leftTensor : DifferentialGradedModule.{t, a, m} A →
    LeftDifferentialGradedModule.{t, a, a} A →
      CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ
  /-- A K-flat module tensored with an acyclic left differential graded module is acyclic; this
  is K-flatness. -/
  leftTensor_acyclic {P : DifferentialGradedModule.{t, a, m} A} (hP : IsKFlat P)
      (N : LeftDifferentialGradedModule.{t, a, a} A) (hN : N.complex.Acyclic) :
    (leftTensor P N).Acyclic
  /-- The cone of `φ`, read as a left differential graded `A`-module. -/
  coneAlgebra : LeftDifferentialGradedModule.{t, a, a} A
  /-- Its underlying complex is the cone of `φ`. -/
  coneAlgebraIso : coneAlgebra.complex ≅ CochainComplex.mappingCone φ.toHomologicalComplex
  /-- Tensoring is a functor of differential graded categories, so the cone of the unit
  `P ⟶ res_φ (P ⊗_A B)` is the tensor product of `P` with the cone of `φ`. -/
  unitConeIso (P : DifferentialGradedModule.{t, a, m} A) :
    leftTensor P coneAlgebra ≅ (cone (extensionUnit φ hφ tensorData P)).complex

variable [HasDerivedCategory.{w} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Base change along a quasi-isomorphism of sheaves of differential graded algebras is an
equivalence of derived categories.** Let `φ : A ⟶ B` be a unit-preserving homomorphism of
sheaves of differential graded algebras on a ringed site which induces an isomorphism on
cohomology sheaves. Then

`D(A, d) ⟶ D(B, d)`, `M ↦ M ⊗^𝐋_A B`

is an equivalence of categories.

The cone of `φ` is acyclic because `φ` is a quasi-isomorphism, so at a K-flat module `P` the
cone of the unit `P ⟶ res_φ (P ⊗_A B)` — which is `P` tensored with the cone of `φ` — is acyclic
too, and the unit is therefore invertible in `D(A, d)`. Every object of `D(A, d)` is isomorphic
to the image of a K-flat module, so the unit of the derived adjunction is invertible everywhere;
and restriction of scalars reflects isomorphisms.

This form takes its inputs as the bundle `DerivedBaseChangeData` and carries no tag attribute;
Tag 0FTZ is `isEquivalence_derivedExtension`, which constructs them.
Apart from that bundle there is no hypothesis here beyond the ambient ringed site: the left
calculus of fractions the conservativity step uses comes from Tag 0FT4, as the note opening the
section on conservativity records. -/
theorem isEquivalence_derived_of_isQuasiIso
    (data : DerivedBaseChangeData.{t, a, m} φ hφ)
    (hφqis : φ.IsQuasiIso) : data.derived.IsEquivalence := by
  have hcone : data.coneAlgebra.complex.Acyclic := fun n =>
    ((CochainComplex.mappingCone.acyclic_iff_quasiIso φ.toHomologicalComplex).2 hφqis n).of_iso
      data.coneAlgebraIso.symm
  have key : ∀ P : DifferentialGradedModule.{t, a, m} A, data.IsKFlat P →
      IsIso (data.adj.unit.app ((toDerivedCategory.{t, a, m} A).obj
        ((HomotopyCategory.quotient A).obj P))) := by
    intro P hP
    have h₁ : (cone (extensionUnit φ hφ data.tensorData P)).complex.Acyclic := fun n =>
      (data.leftTensor_acyclic hP data.coneAlgebra hcone n).of_iso (data.unitConeIso P)
    have h₂ := isIso_toDerivedCategory_map_of_acyclic_cone _
      (extensionUnit φ hφ data.tensorData P) h₁
    have h₃ : IsIso (data.adj.unit.app ((toDerivedCategory.{t, a, m} A).obj
        ((HomotopyCategory.quotient A).obj P)) ≫
        (data.restrictionExtensionIso hP).hom) := by
      rw [data.unit_app hP]
      exact h₂
    exact IsIso.of_isIso_comp_right _ (data.restrictionExtensionIso hP).hom
  refine isEquivalence_of_isIso_unit_derivedRestriction.{w} φ hφ data.adj fun Y => ?_
  obtain ⟨⟨Mas⟩, ⟨eM⟩⟩ : ∃ M : HomotopyCategory.{t, a, m} A,
      Nonempty ((toDerivedCategory.{t, a, m} A).obj M ≅ Y) :=
    ⟨_, ⟨(toDerivedCategory.{t, a, m} A).objObjPreimageIso Y⟩⟩
  obtain ⟨P, p, hP, hp⟩ := data.exists_isKFlat Mas
  have hqp := isIso_toDerivedCategory_map_of_acyclic_cone _ p hp
  have hkey := key P hP
  have e : (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj P) ≅ Y :=
    asIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map p)) ≪≫ eM
  exact (NatTrans.isIso_app_iff_of_iso data.adj.unit e).1 hkey

end BaseChange

end DifferentialGradedModule

end SheafOfModules

end
