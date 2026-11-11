module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleStructures
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of scalars along a homomorphism of sheaves of differential graded algebras

Let `R` be a sheaf of rings on a site and let `φ : A ⟶ B` be a homomorphism of sheaves of
differential graded `R`-algebras which carries the unit of `A` to the unit of `B`. Restriction
of scalars

`res_φ : Mod(B, d) ⥤ Mod(A, d)`

reads a right differential graded `B`-module as a right differential graded `A`-module: the
underlying cochain complex of sheaves of modules is unchanged and a homogeneous local section
`a` of `A` acts through `φ(a)`. The same `φ` makes `B` into a differential graded
`(A, B)`-bimodule `{}_A B_B`, the bimodule whose tensor product `- ⊗_A {}_A B_B` is the base
change functor adjoint to `res_φ`.

Because `res_φ` does not change the underlying complex, it carries homotopies to homotopies and
quasi-isomorphisms to quasi-isomorphisms — indeed it *reflects* quasi-isomorphisms. So it
descends to the homotopy categories and then, since the composite with the localization functor
of `D(A, d)` inverts the quasi-isomorphisms of `K(B)`, all the way to a functor

`res_φ : D(B, d) ⥤ D(A, d)`

of derived categories, with no resolution and no derived-functor apparatus. This is the step
that [Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ) records by saying that
restriction "trivially has a left derived extension, given by restriction".

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.Hom.PreservesOne`: a homomorphism of sheaves of
  differential graded algebras carries the unit of the source to the unit of the target.
* `SheafOfModules.DifferentialGradedAlgebra.Hom.toBimodule`: the target of a unit-preserving
  homomorphism `φ : A ⟶ B`, read as a differential graded `(A, B)`-bimodule `{}_A B_B` with `A`
  acting on the left through `φ`.
* `SheafOfModules.DifferentialGradedModule.restrictionObj` and
  `SheafOfModules.DifferentialGradedModule.restrictionMap`: a right differential graded
  `B`-module, resp. a homomorphism of such, read over `A` through `φ`, and
  `SheafOfModules.DifferentialGradedModule.restriction` the resulting functor `res_φ`.
* `SheafOfModules.DifferentialGradedModule.restrictionHomotopy`: a homotopy of homomorphisms of
  right differential graded `B`-modules, read as a homotopy over `A`.
* `SheafOfModules.DifferentialGradedModule.homotopyRestriction`: the induced functor
  `K(Mod(B, d)) ⥤ K(Mod(A, d))` of homotopy categories.
* `SheafOfModules.DifferentialGradedModule.derivedRestriction`: the induced functor
  `D(B, d) ⥤ D(A, d)` of derived categories, and
  `SheafOfModules.DifferentialGradedModule.derivedRestrictionIso` its compatibility with the two
  localization functors.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.Hom.preservesOne_id` and
  `SheafOfModules.DifferentialGradedAlgebra.Hom.PreservesOne.comp`: unit preservation holds for
  the identity and is stable under composition, so restriction is available along every
  homomorphism built from unit-preserving ones.
* `SheafOfModules.DifferentialGradedModule.preservesHomotopic_restriction`: restriction carries
  homotopic homomorphisms to homotopic homomorphisms.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_homotopyRestriction_map_iff`: an
  arrow of `K(Mod(B, d))` is a quasi-isomorphism **if and only if** its restriction is one. So
  restriction both preserves and reflects quasi-isomorphisms.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isInvertedBy_homotopyRestriction`:
  restriction followed by the localization functor of `D(A, d)` inverts the quasi-isomorphisms
  of `K(Mod(B, d))`, which is what produces `derivedRestriction`.

## Implementation notes

**The bimodule and the restriction functor are those of
`DifferentialGradedBimoduleStructures.lean`.** `Hom.PreservesOne`, `Hom.toBimodule`,
`restrictionObj` and `restriction` are `Hom.IsUnital`, `asBimodule`, `restrictScalarsObj` and
`restrictScalars` of that file; the names here are the ones the homotopy and derived material
below, and `DifferentialGradedRestrictionAdjunction.lean`, are written in. Each is a definition
delegating to the other file's, so the two spellings are interchangeable by `rfl` and the simp
lemmas of both fire.

**Unit preservation is a hypothesis, not a consequence.** Definition
[Stacks, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF) asks of a homomorphism of sheaves
of differential graded algebras only that it be a map of complexes compatible with the
multiplication maps; it imposes no unit-preservation axiom, and neither does
`SheafOfModules.DifferentialGradedAlgebra.Hom`. But the `mul_one` axiom of a right differential
graded module says that the unit of the algebra acts as the identity, and for `res_φ N` that
statement is `φ(1_A)` acting as the identity on `N`. So `res_φ` is simply not defined for a
homomorphism which does not preserve the unit, and the hypothesis
`SheafOfModules.DifferentialGradedAlgebra.Hom.PreservesOne` — which is
`SheafOfModules.DifferentialGradedAlgebra.Hom.IsUnital` of
`DifferentialGradedBimoduleStructures.lean` — is carried explicitly by every construction below.
The same hypothesis is what makes `{}_A B_B` a *unital* bimodule. For
comparison, the semilinear homomorphisms of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean`, which present a
morphism of ringed sites, carry unit preservation as a field of the structure.

**Why restriction is not an instance of the direct image.** For `u = 𝟭 C` and the identity
structure map, the direct image `SheafOfModules.DifferentialGradedModule.pushforwardObj` of
`DifferentialGradedPushforward.lean` is restriction along `φ` composed with the pushforward of
sheaves of modules along the identity continuous functor; the latter is isomorphic to, but not
equal to, the identity, so its differential graded modules are not the ones here and nothing
below would be `rfl`. Restriction is therefore constructed directly, which is also what makes
the chain of reductions in the results below trivial: the underlying complex of `res_φ N` *is*
the underlying complex of `N`, and the underlying complex morphism of `res_φ f` *is* that of
`f`.

**Both algebras live over one sheaf of rings and one site.** This is the situation of
[Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP), where `A` and `B` are sheaves of
differential graded `O`-algebras on a single ringed site `(C, O)`; it is not the situation of
Tag 0FRT, which relates algebras on the two sides of a morphism of ringed sites and is treated
in `DifferentialGradedPullback.lean` and `DifferentialGradedPushforward.lean`. In particular the
two algebras share the universe of their homogeneous pieces, because a homomorphism between them
does.

**The derived category is the development's own.** `D(A, d)` is
`SheafOfModules.DifferentialGradedModule.derivedCategory`, the localization of the homotopy
category at the quasi-isomorphisms, and `derivedRestriction` is obtained from
`CategoryTheory.Localization.lift`; the two sheafification hypotheses which make sheaves of
modules abelian, and so make quasi-isomorphisms available, appear exactly in the section where
they are needed. No triangulated structure is used or asserted, matching
`DifferentialGradedDerivedCategory.lean`.

**The adjunction is elsewhere.** Tag 0FRP also asserts that `- ⊗_{A, φ} B` is left adjoint to
`res_φ`. That is
`SheafOfModules.DifferentialGradedModule.baseChangeRestrictionAdjunction` in
`DifferentialGradedBaseChangeAdjunction.lean`, where the base change functor is the tensor
product with the bimodule `{}_A B_B` supplied by `toBimodule` here.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) — the restriction
  functor `res_φ`, the bimodule `{}_A B_B` and their adjunction.
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF) — sheaves of
  differential graded algebras and their homomorphisms.
* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ) — differential graded
  bimodules.
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI) — right differential
  graded modules.
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5) — the derived category
  of a sheaf of differential graded algebras.
* [Stacks Project, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ) — the lemma whose proof
  opens with the restriction functor and its triviality as a derived functor.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedAlgebra

variable {A B : DifferentialGradedAlgebra.{t, a} R}

/-- A homomorphism of sheaves of differential graded algebras *preserves the unit* when its
degree-zero component carries the global unit of the source to the global unit of the target, on
local sections over every object of the site.

Definition [Stacks, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF) does not require this
of a homomorphism, so it is carried as a hypothesis wherever it is needed.

This is `SheafOfModules.DifferentialGradedAlgebra.Hom.IsUnital`. -/
def Hom.PreservesOne (φ : A ⟶ B) : Prop :=
  φ.IsUnital

/-- The identity homomorphism of a sheaf of differential graded algebras preserves the unit. -/
theorem Hom.preservesOne_id (A' : DifferentialGradedAlgebra.{t, a} R) :
    (𝟙 A' : A' ⟶ A').PreservesOne :=
  fun _ => rfl

/-- A composite of unit-preserving homomorphisms of sheaves of differential graded algebras
preserves the unit. -/
theorem Hom.PreservesOne.comp {A' B' D' : DifferentialGradedAlgebra.{t, a} R} {φ : A' ⟶ B'}
    {ψ : B' ⟶ D'} (hφ : φ.PreservesOne) (hψ : ψ.PreservesOne) : (φ ≫ ψ).PreservesOne :=
  fun U ↦ (congrArg ((ψ.toHomologicalComplex.f 0).val.app U) (hφ U)).trans (hψ U)

/-- A homomorphism of sheaves of differential graded algebras is linear over the sheaf of rings
on local sections. -/
theorem Hom.smul_app (φ : A ⟶ B) (i : ℤ) (U : Cᵒᵖ) (r : R.obj.obj U)
    (x : (A.complex.X i).val.obj U) :
    (φ.toHomologicalComplex.f i).val.app U (r • x) =
      r • (φ.toHomologicalComplex.f i).val.app U x := by
  simpa only [homSections_apply] using
    homSections_smul (φ.toHomologicalComplex.f i) U r x

/-- A homomorphism of sheaves of differential graded algebras commutes with the restriction maps
of the two complexes. -/
theorem Hom.naturality_app (φ : A ⟶ B) (i : ℤ) {U V : Cᵒᵖ} (k : U ⟶ V)
    (x : (A.complex.X i).val.obj U) :
    (B.complex.X i).val.map k ((φ.toHomologicalComplex.f i).val.app U x) =
      (φ.toHomologicalComplex.f i).val.app V ((A.complex.X i).val.map k x) :=
  (PresheafOfModules.naturality_apply (φ.toHomologicalComplex.f i).val k x).symm

/-- The target of a unit-preserving homomorphism `φ : A ⟶ B` of sheaves of differential graded
algebras, read as a differential graded `(A, B)`-bimodule `{}_A B_B`: the underlying complex is
that of `B`, the right action is the multiplication of `B`, and a homogeneous local section `a`
of `A` acts on the left through `φ(a)`.

This is `SheafOfModules.DifferentialGradedAlgebra.asBimodule`. -/
@[stacks 0FRP "the bimodule _A B_B attached to a homomorphism of differential graded algebras"]
def Hom.toBimodule (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    DifferentialGradedBimodule.{t, a, a} A B :=
  asBimodule φ hφ

/-- The underlying complex of `φ.toBimodule hφ` is that of `B`. -/
@[simp]
theorem Hom.toBimodule_complex (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    (φ.toBimodule hφ).complex = B.complex :=
  rfl

/-- A local section `a` of `A` acts on the left of `φ.toBimodule hφ` as multiplication by
`φ(a)` in `B`. -/
@[simp]
theorem Hom.toBimodule_leftMul_app (φ : A ⟶ B) (hφ : φ.PreservesOne) (n m : ℤ) (U : Cᵒᵖ)
    (a : (A.complex.X n).val.obj U) (x : (B.complex.X m).val.obj U) :
    ((φ.toBimodule hφ).leftMul n m).app U a x =
      (B.mul n m).app U ((φ.toHomologicalComplex.f n).val.app U a) x :=
  rfl

/-- The right action of `B` on `φ.toBimodule hφ` is the multiplication of `B`. -/
@[simp]
theorem Hom.toBimodule_rightMul (φ : A ⟶ B) (hφ : φ.PreservesOne) (n m : ℤ) :
    (φ.toBimodule hφ).rightMul n m = B.mul n m :=
  rfl

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

variable {A B : DifferentialGradedAlgebra.{t, a} R}

/-! ### Restriction of scalars on differential graded modules -/

/-- Restriction of scalars of a right differential graded `B`-module along a unit-preserving
homomorphism `φ : A ⟶ B` of sheaves of differential graded algebras: the underlying cochain
complex of sheaves of modules is unchanged and a homogeneous local section `a` of `A` acts
through `φ(a)`.

This is `SheafOfModules.DifferentialGradedModule.restrictScalarsObj`. -/
@[stacks 0FRP "the restriction functor res_φ on objects", ega "II 2.8.6" "more general"]
def restrictionObj (φ : A ⟶ B) (hφ : φ.PreservesOne)
    (N : DifferentialGradedModule.{t, a, m} B) : DifferentialGradedModule.{t, a, m} A :=
  restrictScalarsObj φ hφ N

/-- The underlying complex of `restrictionObj φ hφ N` is that of `N`. -/
@[simp]
theorem restrictionObj_complex (φ : A ⟶ B) (hφ : φ.PreservesOne)
    (N : DifferentialGradedModule.{t, a, m} B) :
    (restrictionObj φ hφ N).complex = N.complex :=
  rfl

/-- A local section `y` of `A` acts on `restrictionObj φ hφ N` as `φ(y)` acts on `N`. -/
@[simp]
theorem restrictionObj_mul_app (φ : A ⟶ B) (hφ : φ.PreservesOne)
    (N : DifferentialGradedModule.{t, a, m} B) (n i : ℤ) (U : Cᵒᵖ)
    (x : (N.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    ((restrictionObj φ hφ N).mul n i).app U x y =
      (N.mul n i).app U x ((φ.toHomologicalComplex.f i).val.app U y) :=
  rfl

/-- Restriction of scalars of a homomorphism of right differential graded `B`-modules: the same
morphism of underlying cochain complexes. -/
@[stacks 0FRP "the restriction functor res_φ on homomorphisms"]
def restrictionMap (φ : A ⟶ B) (hφ : φ.PreservesOne)
    {M N : DifferentialGradedModule.{t, a, m} B} (g : M ⟶ N) :
    restrictionObj φ hφ M ⟶ restrictionObj φ hφ N :=
  (restrictScalars φ hφ).map g

/-- The underlying morphism of complexes of `restrictionMap φ hφ g` is that of `g`. -/
@[simp]
theorem restrictionMap_toHomologicalComplex (φ : A ⟶ B) (hφ : φ.PreservesOne)
    {M N : DifferentialGradedModule.{t, a, m} B} (g : M ⟶ N) :
    (restrictionMap φ hφ g).toHomologicalComplex = g.toHomologicalComplex :=
  rfl

/-- **Restriction of scalars** `res_φ : Mod(B, d) ⥤ Mod(A, d)` along a unit-preserving
homomorphism `φ : A ⟶ B` of sheaves of differential graded algebras.

This is `SheafOfModules.DifferentialGradedModule.restrictScalars`. -/
@[stacks 0FRP "the restriction functor res_φ"]
def restriction (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    DifferentialGradedModule.{t, a, m} B ⥤ DifferentialGradedModule.{t, a, m} A :=
  restrictScalars φ hφ

/-- The functor `restriction φ hφ` sends `N` to `restrictionObj φ hφ N`. -/
@[simp]
theorem restriction_obj (φ : A ⟶ B) (hφ : φ.PreservesOne)
    (N : DifferentialGradedModule.{t, a, m} B) :
    (restriction.{t, a, m} φ hφ).obj N = restrictionObj φ hφ N :=
  rfl

/-- The underlying morphism of complexes of the image of `g` under `restriction φ hφ` is that of
`g`. -/
@[simp]
theorem restriction_map_toHomologicalComplex (φ : A ⟶ B) (hφ : φ.PreservesOne)
    {M N : DifferentialGradedModule.{t, a, m} B} (g : M ⟶ N) :
    ((restriction.{t, a, m} φ hφ).map g).toHomologicalComplex = g.toHomologicalComplex :=
  rfl

/-! ### Restriction on the homotopy categories -/

/-- A homotopy between homomorphisms of right differential graded `B`-modules, read as a
homotopy between their restrictions: the same degree `-1` components. -/
def restrictionHomotopy (φ : A ⟶ B) (hφ : φ.PreservesOne)
    {M N : DifferentialGradedModule.{t, a, m} B} {f g : M ⟶ N} (h : Homotopy f g) :
    Homotopy (restrictionMap φ hφ f) (restrictionMap φ hφ g) where
  app n := h.app n
  map_mul n i U x y :=
    h.map_mul n i U x ((φ.toHomologicalComplex.f i).val.app U y)
  comm n := h.comm n

/-- Restriction of scalars carries homotopic homomorphisms of right differential graded
`B`-modules to homotopic homomorphisms, because it does not change the underlying complexes. -/
theorem preservesHomotopic_restriction (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    PreservesHomotopic (restriction.{t, a, m} φ hφ) :=
  fun _ _ ⟨h⟩ => ⟨restrictionHomotopy φ hφ h⟩

/-- The functor `K(res_φ) : K(Mod(B, d)) ⥤ K(Mod(A, d))` induced on the homotopy categories by
restriction of scalars. -/
def homotopyRestriction (φ : A ⟶ B) (hφ : φ.PreservesOne) :
    HomotopyCategory.{t, a, m} B ⥤ HomotopyCategory.{t, a, m} A :=
  HomotopyCategory.descend (restriction.{t, a, m} φ hφ) (preservesHomotopic_restriction φ hφ)

/-- On the image of a homomorphism `g` in the homotopy category, `homotopyRestriction φ hφ` is
the image in the homotopy category of the restriction of `g`. -/
@[simp]
theorem homotopyRestriction_map_quotient_map (φ : A ⟶ B) (hφ : φ.PreservesOne)
    {M N : DifferentialGradedModule.{t, a, m} B} (g : M ⟶ N) :
    (homotopyRestriction.{t, a, m} φ hφ).map ((HomotopyCategory.quotient B).map g) =
      (HomotopyCategory.quotient A).map ((restriction.{t, a, m} φ hφ).map g) :=
  rfl

/-! ### Restriction on the derived categories -/

section Derived

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (φ : A ⟶ B) (hφ : φ.PreservesOne)

/-- An arrow of the homotopy category of right differential graded `B`-modules is a
quasi-isomorphism exactly when its restriction along `φ` is one: restriction changes neither the
underlying complexes nor the morphisms between them, so the two conditions are the same
condition on the same morphism of complexes of sheaves of modules.

In particular restriction of scalars both preserves and reflects quasi-isomorphisms. -/
theorem quasiIsomorphisms_homotopyRestriction_map_iff
    {X Y : HomotopyCategory.{t, a, m} B} (ψ : X ⟶ Y) :
    quasiIsomorphisms.{t, a, m} A ((homotopyRestriction.{t, a, m} φ hφ).map ψ) ↔
      quasiIsomorphisms.{t, a, m} B ψ := by
  obtain ⟨f, rfl⟩ : ∃ f : X.as ⟶ Y.as, (HomotopyCategory.quotient B).map f = ψ :=
    ⟨_, (HomotopyCategory.quotient B).map_preimage ψ⟩
  exact (quasiIsomorphisms_quotient_map_iff ((restriction.{t, a, m} φ hφ).map f)).trans
    (quasiIsomorphisms_quotient_map_iff f).symm

/-- Restriction of scalars followed by the localization functor of `D(A, d)` inverts the
quasi-isomorphisms of the homotopy category of right differential graded `B`-modules. -/
theorem quasiIsomorphisms_isInvertedBy_homotopyRestriction :
    (quasiIsomorphisms.{t, a, m} B).IsInvertedBy
      (homotopyRestriction.{t, a, m} φ hφ ⋙ toDerivedCategory.{t, a, m} A) :=
  fun _ _ ψ hψ => Localization.inverts (toDerivedCategory.{t, a, m} A)
    (quasiIsomorphisms.{t, a, m} A) _ ((quasiIsomorphisms_homotopyRestriction_map_iff φ hφ ψ).2 hψ)

/-- **Restriction of scalars on the derived categories** `res_φ : D(B, d) ⥤ D(A, d)`. No
resolution and no derived-functor apparatus is needed: restriction inverts the
quasi-isomorphisms, so it factors through the localization. This is the content of the step of
[Stacks, Tag 0FTZ](https://stacks.math.columbia.edu/tag/0FTZ) which says that restriction
"trivially has a left derived extension, given by restriction". -/
def derivedRestriction :
    derivedCategory.{t, a, m} B ⥤ derivedCategory.{t, a, m} A :=
  Localization.lift (homotopyRestriction.{t, a, m} φ hφ ⋙ toDerivedCategory.{t, a, m} A)
    (quasiIsomorphisms_isInvertedBy_homotopyRestriction φ hφ) (toDerivedCategory.{t, a, m} B)

/-- Restriction of scalars on the derived categories restricts along the localization functor of
`D(B, d)` to restriction of scalars on the homotopy categories followed by the localization
functor of `D(A, d)`. -/
def derivedRestrictionIso :
    toDerivedCategory.{t, a, m} B ⋙ derivedRestriction.{t, a, m} φ hφ ≅
      homotopyRestriction.{t, a, m} φ hφ ⋙ toDerivedCategory.{t, a, m} A :=
  Localization.fac (homotopyRestriction.{t, a, m} φ hφ ⋙ toDerivedCategory.{t, a, m} A)
    (quasiIsomorphisms_isInvertedBy_homotopyRestriction φ hφ) (toDerivedCategory.{t, a, m} B)

end Derived

end DifferentialGradedModule

end SheafOfModules

end
