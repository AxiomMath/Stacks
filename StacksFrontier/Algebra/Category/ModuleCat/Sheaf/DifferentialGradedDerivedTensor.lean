module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDifferentialGradedModule

/-!
# Derived pullback and the derived tensor product of sheaves of differential graded modules

Let `(f, f♯) : (Sh(C), O) → (Sh(C'), O')` be a morphism of ringed topoi, let `A` be a sheaf of
differential graded `O`-algebras, let `A'` be a sheaf of differential graded `O'`-algebras and
let `φ : A' → f_*A` be a homomorphism. Together with a second differential graded `O`-algebra
and a differential graded bimodule `N` one has the functor `M ↦ f^*M ⊗_A N` on differential
graded modules; it carries a quasi-isomorphism of *good* modules to a quasi-isomorphism and so
admits a left derived extension `D(A', d) → D(A, d)` of the derived categories, whose value on
a good module `P` is `f^*P ⊗_A N`. Its two instances are the derived tensor product
`- ⊗^L_A N` and the derived pullback `Lf^*`.

Three properties of these functors:

* For composable morphisms of ringed topoi `f` and `g` and homomorphisms `φ : A' → f_*A`,
  `φ' : A'' → g_*A'`, derived pullback along `f` after derived pullback along `g` is a left
  derived extension of pullback along `g ∘ f`, and so agrees with derived pullback along
  `g ∘ f` at every object of `D(A'', d)`.
* If a homomorphism `N → N'` of differential graded bimodules is an isomorphism on cohomology
  sheaves, then the canonical transformation `(- ⊗^L_A N) → (- ⊗^L_A N')` is an isomorphism of
  functors.
* If the differential graded `(A, B)`-bimodule `N` is good as a *left* differential graded
  `A`-module, then the derived tensor product with `N` needs no resolution at all: the canonical
  map `M ⊗^L_A N → M ⊗_A N` is an isomorphism of `D(B, d)` for every differential graded
  `A`-module `M`.

## Main definitions

* `SheafOfModules.IsCohomologyIso` says that a morphism of cochain complexes of sheaves of
  modules is an isomorphism on every cohomology sheaf.
* `SheafOfModules.DifferentialGradedModule.GoodModuleData` carries, for one sheaf of
  differential graded algebras, the derived category with its localization functor out of the
  homotopy category, the tensor product with a left differential graded module, and the good
  differential graded modules with two properties of the flat-resolution theory: an acyclic left
  module tensored with a good module is acyclic, and every module receives a quasi-isomorphism
  from a good one.
* `SheafOfModules.DifferentialGradedModule.ComputesOnGood` says that a functor of derived
  categories takes, on the image of a good differential graded module, the value prescribed by a
  given functor of differential graded modules, compatibly with homomorphisms of good modules.
* `SheafOfModules.DifferentialGradedModule.DerivedTensorData` carries the functor
  `M ↦ f^*M ⊗_A N` of differential graded modules together with a left derived extension
  computed on good modules by it.
* `SheafOfModules.DifferentialGradedModule.IsDerivedPullback` records the two further properties
  of the pullback of differential graded modules: it carries good modules to good modules, and
  good acyclic modules to acyclic modules.
* `SheafOfModules.DifferentialGradedModule.DerivedTensorData.derivedTensor` and
  `SheafOfModules.DifferentialGradedModule.DerivedTensorData.derivedPullback`: the left derived
  extension carried by a `DerivedTensorData`, read as a derived tensor product or as a derived
  pullback.
* `SheafOfModules.DifferentialGradedModule.DerivedTensorComparisonData` carries, for a
  homomorphism `ν : N → N'` of differential graded `(A, B)`-bimodules, the two tensor product
  functors with their derived extensions, the transformation between them, and the cone of `ν`
  as a left differential graded `A`-module.
* `SheafOfModules.DifferentialGradedModule.GoodModuleData.IsKFlatLeft` says that a left
  differential graded module is K-flat: tensoring an acyclic right differential graded module
  with it gives an acyclic complex of sheaves of modules.
* `SheafOfModules.DifferentialGradedModule.DerivedTensorCounitData` carries the functor
  `M ↦ M ⊗_A N` of differential graded modules, its left derived extension `- ⊗^L_A N`, the
  canonical map `M ⊗^L_A N → M ⊗_A N` natural in `M`, and the identification of the cone of
  `M ⊗_A N → M' ⊗_A N` with the tensor product of the cone of `M → M'` with `N`.

## Main results

* `SheafOfModules.DifferentialGradedModule.computesOnGood_derivedComp`: the composite
  `Lg^* ⋙ Lf^*` is computed on good modules by `g^* ⋙ f^*`, that is, it is a left derived
  extension of derived pullback along `g ∘ f`.
* `SheafOfModules.DifferentialGradedModule.nonempty_derivedPullback_comp_obj_iso`: consequently
  `L(g ∘ f)^*` and `Lf^* ∘ Lg^*` agree, up to isomorphism, at every object of `D(A'', d)`.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorComparison`: if `N → N'` is an
  isomorphism on cohomology sheaves then the canonical transformation
  `(- ⊗^L_A N) → (- ⊗^L_A N')` is an isomorphism of functors.
* `SheafOfModules.DifferentialGradedModule.isIso_counit_app_of_isKFlatLeft`: if the bimodule `N`
  is K-flat as a left differential graded `A`-module then `M ⊗^L_A N → M ⊗_A N` is an
  isomorphism of `D(B, d)` for every differential graded `A`-module `M`.
* `SheafOfModules.DifferentialGradedModule.isIso_counit_of_isKFlatLeft`: the same conclusion
  read as an isomorphism of the two functors on differential graded modules.

## References

* [Stacks Project, Tag 0FTD](https://stacks.math.columbia.edu/tag/0FTD)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTJ](https://stacks.math.columbia.edu/tag/0FTJ)
* [Stacks Project, Tag 0FTK](https://stacks.math.columbia.edu/tag/0FTK)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t a m v u t' a' m' v' u' t'' a'' m'' v'' u'' d e d' e' d'' e''

namespace SheafOfModules

/-- A morphism of cochain complexes of sheaves of modules is an isomorphism on cohomology
sheaves when the `n`-th cohomology sheaf functor carries it to an isomorphism for every integer
`n`. -/
def IsCohomologyIso {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{t}} [HasSheafify J AddCommGrpCat.{m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {K L : CochainComplex (SheafOfModules.{m} R) ℤ} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, IsIso ((HomologicalComplex.homologyFunctor
    (SheafOfModules.{m} R) (ComplexShape.up ℤ) n).map f)

section ToLeft

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

end ToLeft

namespace DifferentialGradedModule

/-! ### The flat-resolution theory and the derived category, carried as data -/

section GoodData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The flat-resolution theory of a sheaf of differential graded algebras `A` on a ringed site,
together with its derived category `D(A, d)`: the localization functor out of the homotopy
category, the tensor product of a right differential graded `A`-module with a left one, and the
class of good right differential graded `A`-modules with the properties that make them compute
derived functors. -/
structure GoodModuleData (A : DifferentialGradedAlgebra.{t, a} R) (D : Type d)
    [Category.{e} D] where
  /-- The localization functor from the homotopy category `K(A)` to the derived category
  `D(A, d)`. -/
  localization : HomotopyCategory.{t, a, m} A ⥤ D
  /-- Every object of the derived category is isomorphic to the image of a right differential
  graded module. -/
  exists_iso_localization (X : D) :
    ∃ M : DifferentialGradedModule.{t, a, m} A,
      Nonempty (localization.obj ((HomotopyCategory.quotient A).obj M) ≅ X)
  /-- The quasi-isomorphisms are exactly the arrows inverted by the localization functor: a
  homomorphism whose cone is acyclic becomes an isomorphism of the derived category. -/
  isIso_localization_map {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N)
      (hf : (cone f).complex.Acyclic) :
    IsIso (localization.map ((HomotopyCategory.quotient A).map f))
  /-- The good right differential graded `A`-modules: those which are flat and K-flat as graded
  modules and stay so after arbitrary base change. -/
  IsGood : DifferentialGradedModule.{t, a, m} A → Prop
  /-- The tensor product `P ⊗_A N` of a right differential graded `A`-module with a left one, a
  complex of sheaves of `R`-modules. -/
  leftTensor : DifferentialGradedModule.{t, a, m} A →
    LeftDifferentialGradedModule.{t, a, m} A → CochainComplex (SheafOfModules.{m} R) ℤ
  /-- A good module tensored with an acyclic left differential graded module is acyclic; this is
  the K-flatness clause in the definition of a good module. -/
  leftTensor_acyclic {P : DifferentialGradedModule.{t, a, m} A} (hP : IsGood P)
      (N : LeftDifferentialGradedModule.{t, a, m} A) (hN : N.complex.Acyclic) :
    (leftTensor P N).Acyclic
  /-- Every right differential graded `A`-module receives a quasi-isomorphism from a good
  one. -/
  exists_isGood (M : DifferentialGradedModule.{t, a, m} A) :
    ∃ (P : DifferentialGradedModule.{t, a, m} A) (p : P ⟶ M),
      IsGood P ∧ (cone p).complex.Acyclic

/-- Every object of the derived category is isomorphic to the image of a good module. -/
private theorem GoodModuleData.exists_isGood_iso_localization
    {A : DifferentialGradedAlgebra.{t, a} R} {D : Type d} [Category.{e} D]
    (gA : GoodModuleData.{t, a, m, v, u, d, e} A D) (X : D) :
    ∃ P : DifferentialGradedModule.{t, a, m} A, gA.IsGood P ∧
      Nonempty (gA.localization.obj ((HomotopyCategory.quotient A).obj P) ≅ X) := by
  obtain ⟨M, ⟨eM⟩⟩ := gA.exists_iso_localization X
  obtain ⟨P, p, hP, hp⟩ := gA.exists_isGood M
  have := gA.isIso_localization_map p hp
  exact ⟨P, hP, ⟨asIso (gA.localization.map ((HomotopyCategory.quotient A).map p)) ≪≫ eM⟩⟩

end GoodData

/-! ### The left derived extension, carried as data -/

section DerivedData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}

/-- A functor `L` of derived categories is *computed on good modules* by a functor `F` of
differential graded modules when `L` takes the image of a good module `P` to the image of
`F P`, and takes the image of a homomorphism of good modules to the image of its value under
`F`. -/
structure ComputesOnGood {A : DifferentialGradedAlgebra.{t, a} R}
    {A' : DifferentialGradedAlgebra.{t', a'} R'} {D : Type d} [Category.{e} D] {D' : Type d'}
    [Category.{e'} D'] (gA : GoodModuleData.{t, a, m, v, u, d, e} A D)
    (gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D')
    (F : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t', a', m'} A')
    (L : D ⥤ D') where
  /-- On the image in the derived category of a good module `P`, the functor takes the value
  prescribed by `F`. -/
  obj_eq {P : DifferentialGradedModule.{t, a, m} A} (hP : gA.IsGood P) :
    L.obj (gA.localization.obj ((HomotopyCategory.quotient A).obj P)) =
      gA'.localization.obj ((HomotopyCategory.quotient A').obj (F.obj P))
  /-- On the image of a homomorphism of good modules, the functor is the image of its value
  under `F`, read through the identifications of the previous clause. -/
  map_eq {P P' : DifferentialGradedModule.{t, a, m} A} (hP : gA.IsGood P) (hP' : gA.IsGood P')
      (φ : P ⟶ P') :
    L.map (gA.localization.map ((HomotopyCategory.quotient A).map φ)) =
      eqToHom (obj_eq hP) ≫
        gA'.localization.map ((HomotopyCategory.quotient A').map (F.map φ)) ≫
          eqToHom (obj_eq hP').symm

/-- The derived tensor product attached to a morphism of ringed topoi `f` and a differential
graded bimodule `N`: the functor `M ↦ f^*M ⊗_A N` of differential graded modules, its left
derived extension between the derived categories, and the clause pinning the value of that
extension on a good module `P` to be `f^*P ⊗_A N`. -/
structure DerivedTensorData {A : DifferentialGradedAlgebra.{t, a} R}
    {A' : DifferentialGradedAlgebra.{t', a'} R'} {D : Type d} [Category.{e} D] {D' : Type d'}
    [Category.{e'} D'] (gA : GoodModuleData.{t, a, m, v, u, d, e} A D)
    (gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D') where
  /-- The functor `M ↦ f^*M ⊗_A N` of differential graded modules. -/
  moduleFunctor :
    DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t', a', m'} A'
  /-- The left derived extension of that functor to the derived categories. -/
  derived : D ⥤ D'
  /-- Its value on a good module `P` is `f^*P ⊗_A N`. -/
  computes : ComputesOnGood gA gA' moduleFunctor derived

/-- The two further properties of the pullback `f^*` of differential graded modules along a
morphism of ringed topoi, which the general functor `M ↦ f^*M ⊗_A N` does not have: it carries
good modules to good modules, and good acyclic modules to acyclic modules. -/
structure IsDerivedPullback {A : DifferentialGradedAlgebra.{t, a} R}
    {A' : DifferentialGradedAlgebra.{t', a'} R'} {D : Type d} [Category.{e} D] {D' : Type d'}
    [Category.{e'} D'] (gA : GoodModuleData.{t, a, m, v, u, d, e} A D)
    (gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D')
    (data : DerivedTensorData gA gA') where
  /-- The pullback of a good module is good. -/
  isGood_moduleFunctor {P : DifferentialGradedModule.{t, a, m} A} (hP : gA.IsGood P) :
    gA'.IsGood (data.moduleFunctor.obj P)
  /-- The pullback of a good acyclic module is acyclic. -/
  acyclic_moduleFunctor {P : DifferentialGradedModule.{t, a, m} A} (hP : gA.IsGood P)
      (hPac : P.complex.Acyclic) : (data.moduleFunctor.obj P).complex.Acyclic

end DerivedData

/-! ### The derived tensor product and the derived pullback -/

section Naming

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t', a'} R'}
  {D : Type d} [Category.{e} D] {D' : Type d'} [Category.{e'} D']
  {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
  {gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D'}

/-- The left derived extension of a `DerivedTensorData` whose functor of differential graded
modules is the tensor product with a differential graded `(A, A')`-bimodule `N` on a ringed
site. -/
def DerivedTensorData.derivedTensor (data : DerivedTensorData gA gA') : D ⥤ D' :=
  data.derived

/-- The derived tensor product is the left derived extension carried by the data. -/
@[simp]
theorem DerivedTensorData.derivedTensor_eq (data : DerivedTensorData gA gA') :
    data.derivedTensor = data.derived :=
  rfl

/-- The left derived extension of a `DerivedTensorData` whose functor of differential graded
modules is a pullback `f^*`, in the sense of `IsDerivedPullback`. -/
def DerivedTensorData.derivedPullback (data : DerivedTensorData gA gA')
    (_hdata : IsDerivedPullback gA gA' data) : D ⥤ D' :=
  data.derived

/-- The derived pullback is the left derived extension carried by the data. -/
@[simp]
theorem DerivedTensorData.derivedPullback_eq (data : DerivedTensorData gA gA')
    (hdata : IsDerivedPullback gA gA' data) : data.derivedPullback hdata = data.derived :=
  rfl

end Naming

/-! ### Derived pullback along a composition -/

section Composition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t''}} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t', a'} R'} {A'' : DifferentialGradedAlgebra.{t'', a''} R''}
  {D : Type d} [Category.{e} D] {D' : Type d'} [Category.{e'} D'] {D'' : Type d''}
  [Category.{e''} D''] {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
  {gA' : GoodModuleData.{t', a', m', v', u', d', e'} A' D'}
  {gA'' : GoodModuleData.{t'', a'', m'', v'', u'', d'', e''} A'' D''}

/-- Derived pullback along `f` after derived pullback along `g` is computed on good modules by
the pullback along `g` followed by the pullback along `f`, which is the pullback along `g ∘ f`.
In other words `Lf^* ∘ Lg^*` is a left derived extension of pullback along the composition. -/
theorem computesOnGood_derivedComp (Df : DerivedTensorData gA' gA)
    (Dg : DerivedTensorData gA'' gA') (hDg : IsDerivedPullback gA'' gA' Dg) :
    ComputesOnGood gA'' gA (Dg.moduleFunctor ⋙ Df.moduleFunctor) (Dg.derived ⋙ Df.derived) where
  obj_eq {P} hP := by
    simp only [Functor.comp_obj]
    rw [Dg.computes.obj_eq hP, Df.computes.obj_eq (hDg.isGood_moduleFunctor hP)]
  map_eq {P P'} hP hP' φ := by
    simp only [Functor.comp_map, Functor.comp_obj]
    rw [Dg.computes.map_eq hP hP' φ]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc,
      Df.computes.map_eq (hDg.isGood_moduleFunctor hP) (hDg.isGood_moduleFunctor hP')
        (Dg.moduleFunctor.map φ), eqToHom_trans, eqToHom_trans_assoc]

/-- At every object of `D(A'', d)`, derived pullback along `g ∘ f` and derived pullback along
`f` after derived pullback along `g` take isomorphic values. -/
theorem nonempty_derivedPullback_comp_obj_iso (Df : DerivedTensorData gA' gA)
    (Dg : DerivedTensorData gA'' gA') (hDg : IsDerivedPullback gA'' gA' Dg) (Lgf : D'' ⥤ D)
    (hLgf : ComputesOnGood gA'' gA (Dg.moduleFunctor ⋙ Df.moduleFunctor) Lgf) (X : D'') :
    Nonempty (Lgf.obj X ≅ (Dg.derived ⋙ Df.derived).obj X) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := gA''.exists_isGood_iso_localization X
  exact ⟨(Lgf.mapIso e).symm ≪≫
    eqToIso ((hLgf.obj_eq hP).trans
      ((computesOnGood_derivedComp Df Dg hDg).obj_eq hP).symm) ≪≫
        (Dg.derived ⋙ Df.derived).mapIso e⟩

end Composition

/-! ### Changing the bimodule in the derived tensor product -/

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A B : DifferentialGradedAlgebra.{t, a} R} {D : Type d} [Category.{e} D] {D' : Type d'}
  [Category.{e'} D']

/-- The data comparing the derived tensor products with two differential graded
`(A, B)`-bimodules along a homomorphism `ν : N → N'`: the two tensor product functors on
differential graded modules with the transformation between them, their left derived extensions
with the transformation between those, and the cone of `ν` as a left differential graded
`A`-module. -/
structure DerivedTensorComparisonData (gA : GoodModuleData.{t, a, m, v, u, d, e} A D)
    (gB : GoodModuleData.{t, a, m, v, u, d', e'} B D')
    {N N' : DifferentialGradedBimodule.{t, a, m} A B} (ν : N ⟶ N') where
  /-- The functor `M ↦ M ⊗_A N` of differential graded modules. -/
  tensorN : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t, a, m} B
  /-- The functor `M ↦ M ⊗_A N'` of differential graded modules. -/
  tensorN' : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t, a, m} B
  /-- The transformation `M ⊗_A N → M ⊗_A N'` induced by `ν`. -/
  tensorMap : tensorN ⟶ tensorN'
  /-- The derived tensor product `- ⊗^L_A N`. -/
  derivedN : D ⥤ D'
  /-- Its value on a good module `P` is `P ⊗_A N`. -/
  computesN : ComputesOnGood gA gB tensorN derivedN
  /-- The derived tensor product `- ⊗^L_A N'`. -/
  derivedN' : D ⥤ D'
  /-- Its value on a good module `P` is `P ⊗_A N'`. -/
  computesN' : ComputesOnGood gA gB tensorN' derivedN'
  /-- The canonical transformation `t : (- ⊗^L_A N) → (- ⊗^L_A N')`. -/
  t : derivedN ⟶ derivedN'
  /-- On the image of a good module `P`, the transformation `t` is the map
  `P ⊗_A N → P ⊗_A N'`. -/
  t_app {P : DifferentialGradedModule.{t, a, m} A} (hP : gA.IsGood P) :
    t.app (gA.localization.obj ((HomotopyCategory.quotient A).obj P)) =
      eqToHom (computesN.obj_eq hP) ≫
        gB.localization.map ((HomotopyCategory.quotient B).map (tensorMap.app P)) ≫
          eqToHom (computesN'.obj_eq hP).symm
  /-- The cone of `ν`, viewed as a left differential graded `A`-module. -/
  coneBimodule : LeftDifferentialGradedModule.{t, a, m} A
  /-- The cone of a homomorphism which is an isomorphism on cohomology sheaves is acyclic. -/
  coneBimodule_acyclic (hν : IsCohomologyIso ν.toHomologicalComplex) :
    coneBimodule.complex.Acyclic
  /-- `P ⊗_A` applied to the cone of `ν` is the cone, as a complex of sheaves of `R`-modules, of
  `P ⊗_A ν`. -/
  leftTensorConeIso (P : DifferentialGradedModule.{t, a, m} A) :
    gA.leftTensor P coneBimodule ≅ (cone (tensorMap.app P)).complex

/-- If a homomorphism `ν : N → N'` of differential graded `(A, B)`-bimodules is an isomorphism
on cohomology sheaves, then the canonical transformation `(- ⊗^L_A N) → (- ⊗^L_A N')` is an
isomorphism of functors. -/
theorem isIso_derivedTensorComparison {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
    {gB : GoodModuleData.{t, a, m, v, u, d', e'} B D'}
    {N N' : DifferentialGradedBimodule.{t, a, m} A B} {ν : N ⟶ N'}
    (data : DerivedTensorComparisonData gA gB ν)
    (hν : IsCohomologyIso ν.toHomologicalComplex) : IsIso data.t := by
  have key : ∀ P : DifferentialGradedModule.{t, a, m} A, gA.IsGood P →
      IsIso (data.t.app (gA.localization.obj ((HomotopyCategory.quotient A).obj P))) := by
    intro P hP
    have h₂ : (cone (data.tensorMap.app P)).complex.Acyclic := fun n =>
      (gA.leftTensor_acyclic hP data.coneBimodule (data.coneBimodule_acyclic hν) n).of_iso
        (data.leftTensorConeIso P)
    have := gB.isIso_localization_map (data.tensorMap.app P) h₂
    rw [data.t_app hP]
    infer_instance
  have : ∀ X : D, IsIso (data.t.app X) := by
    intro X
    obtain ⟨P, hP, ⟨e⟩⟩ := gA.exists_isGood_iso_localization X
    have := key P hP
    have : IsIso (data.derivedN.map e.hom ≫ data.t.app X) := by
      rw [data.t.naturality e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_left (data.derivedN.map e.hom) (data.t.app X)
  exact NatIso.isIso_of_isIso_app data.t

end Comparison

/-! ### A bimodule good on the left computes the derived tensor product -/

section LeftGood

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {D : Type d} [Category.{e} D] {D' : Type d'}
  [Category.{e'} D']

/-- A left differential graded `A`-module `N` is *K-flat* when the tensor product `M ⊗_A N` is
acyclic for every acyclic right differential graded `A`-module `M`. -/
def GoodModuleData.IsKFlatLeft (gA : GoodModuleData.{t, a, m, v, u, d, e} A D)
    (N : LeftDifferentialGradedModule.{t, a, m} A) : Prop :=
  ∀ M : DifferentialGradedModule.{t, a, m} A, M.complex.Acyclic → (gA.leftTensor M N).Acyclic

/-- The derived tensor product with a differential graded `(A, B)`-bimodule `N`, together with
its comparison with the ordinary tensor product: the functor `M ↦ M ⊗_A N` of differential
graded modules, its left derived extension `- ⊗^L_A N : D(A, d) → D(B, d)`, the canonical map
`M ⊗^L_A N → M ⊗_A N` natural in the differential graded module `M`, and the identification of
the cone of `M ⊗_A N → M' ⊗_A N` with the tensor product of the cone of `M → M'` with `N`. -/
structure DerivedTensorCounitData (gA : GoodModuleData.{t, a, m, v, u, d, e} A D)
    (gB : GoodModuleData.{t, a, m, v, u, d', e'} B D')
    (N : DifferentialGradedBimodule.{t, a, m} A B) where
  /-- The functor `M ↦ M ⊗_A N` of differential graded modules. -/
  tensorN : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t, a, m} B
  /-- The derived tensor product `- ⊗^L_A N : D(A, d) → D(B, d)`. -/
  derived : D ⥤ D'
  /-- Its value on a good module `P` is `P ⊗_A N`. -/
  computes : ComputesOnGood gA gB tensorN derived
  /-- The canonical map `M ⊗^L_A N → M ⊗_A N` of `D(B, d)`, natural in the differential graded
  module `M`: the counit exhibiting `derived` as a left derived extension of `tensorN`. -/
  counit : HomotopyCategory.quotient A ⋙ gA.localization ⋙ derived ⟶
    tensorN ⋙ HomotopyCategory.quotient B ⋙ gB.localization
  /-- On a good module `P`, where the derived tensor product is already the ordinary one, the
  canonical map is the identity. -/
  counit_app {P : DifferentialGradedModule.{t, a, m} A} (hP : gA.IsGood P) :
    counit.app P = eqToHom (computes.obj_eq hP)
  /-- The cone of `M ⊗_A N → M' ⊗_A N`, as a complex of sheaves of modules, is the tensor product
  of the cone of `M → M'` with `N` read as a left differential graded `A`-module. -/
  leftTensorConeIso {M M' : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ M') :
    gA.leftTensor (cone f) N.toLeftDifferentialGradedModule ≅ (cone (tensorN.map f)).complex

/-- If the differential graded `(A, B)`-bimodule `N` is K-flat as a left differential graded
`A`-module, then the canonical map `M ⊗^L_A N → M ⊗_A N` is an isomorphism of `D(B, d)` for every
differential graded `A`-module `M`. -/
theorem isIso_counit_app_of_isKFlatLeft {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
    {gB : GoodModuleData.{t, a, m, v, u, d', e'} B D'}
    {N : DifferentialGradedBimodule.{t, a, m} A B} (data : DerivedTensorCounitData gA gB N)
    (hN : gA.IsKFlatLeft N.toLeftDifferentialGradedModule)
    (M : DifferentialGradedModule.{t, a, m} A) :
    IsIso (data.counit.app M) := by
  obtain ⟨P, p, hP, hp⟩ := gA.exists_isGood M
  have hcone : (cone (data.tensorN.map p)).complex.Acyclic := fun n =>
    (hN (cone p) hp n).of_iso (data.leftTensorConeIso p)
  have h₁ := gB.isIso_localization_map (data.tensorN.map p) hcone
  have h₂ := gA.isIso_localization_map p hp
  have h₃ : IsIso (data.counit.app P) := by
    rw [data.counit_app hP]
    infer_instance
  have h₄ : IsIso ((HomotopyCategory.quotient A ⋙ gA.localization ⋙ data.derived).map p) := by
    simp only [Functor.comp_map]
    infer_instance
  have h₅ : IsIso ((HomotopyCategory.quotient A ⋙ gA.localization ⋙ data.derived).map p ≫
      data.counit.app M) := by
    rw [data.counit.naturality p]
    simp only [Functor.comp_map]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((HomotopyCategory.quotient A ⋙ gA.localization ⋙ data.derived).map p) _

/-- The conclusion of `isIso_counit_app_of_isKFlatLeft` read as an isomorphism of functors on
differential graded modules: for a bimodule which is K-flat on the left, the derived tensor
product is the ordinary tensor product. -/
theorem isIso_counit_of_isKFlatLeft {gA : GoodModuleData.{t, a, m, v, u, d, e} A D}
    {gB : GoodModuleData.{t, a, m, v, u, d', e'} B D'}
    {N : DifferentialGradedBimodule.{t, a, m} A B} (data : DerivedTensorCounitData gA gB N)
    (hN : gA.IsKFlatLeft N.toLeftDifferentialGradedModule) : IsIso data.counit := by
  have : ∀ M : DifferentialGradedModule.{t, a, m} A, IsIso (data.counit.app M) := fun M =>
    isIso_counit_app_of_isKFlatLeft data hN M
  exact NatIso.isIso_of_isIso_app data.counit

end LeftGood

end DifferentialGradedModule

end SheafOfModules

end
