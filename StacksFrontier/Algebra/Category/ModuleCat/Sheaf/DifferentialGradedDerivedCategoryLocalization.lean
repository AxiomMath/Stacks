module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsomorphisms

/-!
# Objects and inverted arrows of the derived category of a sheaf of differential graded algebras

The derived category `D(A, d)` of a sheaf of differential graded algebras is the localization of
the homotopy category `K(Mod(A, d))` at the quasi-isomorphisms. Several consequences of that
description are recorded here: every object of `D(A, d)` is the image of a right differential
graded module, a homomorphism of right differential graded modules whose cone is acyclic
becomes invertible in `D(A, d)`, and — over a ringed site, where `K(Mod(A, d))` is triangulated
and the acyclic objects form a strictly full saturated triangulated subcategory `Ac` — the
quasi-isomorphisms are the class of arrows attached to `Ac`, and the kernel of the localization
functor is `Ac`.

The second rests on a fact about cochain complexes in an abelian category: a morphism is a
quasi-isomorphism exactly when its mapping cone is acyclic. This is Mathlib's identification of
the quasi-isomorphisms of the homotopy category with the arrows whose cone lies in the
triangulated subcategory of acyclic complexes.

## Main results

* `CochainComplex.mappingCone.acyclic_iff_quasiIso`: a morphism of cochain complexes in an
  abelian category is a quasi-isomorphism exactly when its mapping cone is acyclic.
* `SheafOfModules.DifferentialGradedModule.derivedCategoryModule`: the right differential graded
  module represented by an object of the derived category, with
  `toDerivedCategory_obj_quotient_obj_derivedCategoryModule` saying that the object is the image
  of that module on the nose.
* `SheafOfModules.DifferentialGradedModule.exists_toDerivedCategory_obj_eq`: every object of
  the derived category is the image of a right differential graded module.
* `SheafOfModules.DifferentialGradedModule.acyclic_cone_iff_quasiIso`: a homomorphism of right
  differential graded modules is a quasi-isomorphism exactly when its cone is acyclic.
* `SheafOfModules.DifferentialGradedModule.isIso_toDerivedCategory_map_of_acyclic_cone`: a
  homomorphism of right differential graded modules whose cone is acyclic becomes an
  isomorphism of the derived category.
* `SheafOfModules.DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`: **the
  quasi-isomorphisms are the class of arrows attached to the triangulated subcategory of
  acyclic objects.**
* `SheafOfModules.DifferentialGradedModule.toDerivedCategory_kernel_eq_acyclic`: **the kernel
  of the localization functor `K(Mod(A, d)) ⟶ D(A, d)` is the subcategory of acyclic
  objects.**

## Implementation notes

The last two results are proved over a ringed site, as in the source, because that is the
setting in which this development has the pre-triangulated structure on `K(Mod(A, d))` (tag
0FS7) and the triangulated subcategory of acyclic objects (tag 0FT3); the first three are
proved over an arbitrary sheaf of rings on an arbitrary site.

The identification of the quasi-isomorphisms with the arrows attached to `Ac` is proved from
the characterisation of the distinguished triangles of `K(Mod(A, d))`,
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.distinguished_iff`, rather than from
the source's `H^i(f) = H^0(f[i])`: that identification asks for the translations of
`K(Mod(A, d))` to be compared with the shift of complexes *on morphisms*, which this
development does not have. A distinguished triangle on the given arrow is isomorphic to the
triangle of an admissible short exact sequence `M → N → P`, whose underlying sequence of
complexes of sheaves of modules is short exact
(`SheafOfModules.DifferentialGradedModule.split_shortExact`, from the proof of tag 0FT2), and
for a short exact sequence of complexes the first map is a quasi-isomorphism exactly when the
third term is acyclic
(`SheafOfModules.DifferentialGradedModule.quasiIso_f_iff_acyclic_X₃`). The given arrow and the
first map of that sequence differ by isomorphisms of `K(Mod(A, d))`, which the
quasi-isomorphisms respect.

Tag 0FT6 is then the second clause of the Verdier correspondence,
`CategoryTheory.ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self`: a strictly full
saturated triangulated subcategory is recovered as the objects killed by the localization at
the class of arrows it determines. That is this development's form of the source's appeal to
Derived Categories, Tag 05R8.

## References

* [Stacks Project, Tag 0FT6](https://stacks.math.columbia.edu/tag/0FT6)
* [Stacks Project, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FT3](https://stacks.math.columbia.edu/tag/0FT3)
* [Stacks Project, Tag 05R8](https://stacks.math.columbia.edu/tag/05R8)
-/

@[expose] public section

open CategoryTheory

universe t a m v u w

namespace CochainComplex.mappingCone

/-- A morphism of cochain complexes in an abelian category is a quasi-isomorphism exactly when
its mapping cone is acyclic: the mapping cone triangle is distinguished, so the morphism lies in
the class of arrows attached to the triangulated subcategory of acyclic complexes exactly when
the cone lies in that subcategory, and that class of arrows is the class of
quasi-isomorphisms. -/
theorem acyclic_iff_quasiIso {B : Type*} [Category B] [Abelian B] {K L : CochainComplex B ℤ}
    (g : K ⟶ L) : (mappingCone g).Acyclic ↔ QuasiIso g := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
    ← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic B).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished g)).symm

end CochainComplex.mappingCone

namespace SheafOfModules.DifferentialGradedModule

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, a} R)
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- The right differential graded `A`-module represented by an object of the derived category
`D(A, d)`. Formally inverting arrows leaves the objects alone and the objects of the homotopy
category are the right differential graded modules, so an object of `D(A, d)` *is* a module,
and this reads it off. -/
def derivedCategoryModule (X : derivedCategory.{t, a, m} A) :
    DifferentialGradedModule.{t, a, m} A :=
  X.as.obj.as

/-- An object of the derived category is the image of the module it represents, on the nose. -/
@[simp]
theorem toDerivedCategory_obj_quotient_obj_derivedCategoryModule
    (X : derivedCategory.{t, a, m} A) :
    (toDerivedCategory.{t, a, m} A).obj
        ((HomotopyCategory.quotient A).obj (derivedCategoryModule A X)) = X :=
  rfl

/-- The module represented by the image of a module is that module. -/
@[simp]
theorem derivedCategoryModule_toDerivedCategory_obj (M : DifferentialGradedModule.{t, a, m} A) :
    derivedCategoryModule A
        ((toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj M)) = M :=
  rfl

/-- Every object of the derived category of `(A, d)` is the image of a right differential graded
`A`-module. The derived category is obtained from the homotopy category by formally inverting
arrows, which leaves the objects alone, and the objects of the homotopy category are the right
differential graded modules. -/
theorem exists_toDerivedCategory_obj_eq (X : derivedCategory.{t, a, m} A) :
    ∃ M : DifferentialGradedModule.{t, a, m} A,
      (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj M) = X :=
  ⟨derivedCategoryModule A X, rfl⟩

/-- A homomorphism of right differential graded `A`-modules is a quasi-isomorphism on the
underlying complexes of sheaves of modules exactly when its cone is acyclic: the cone's complex
is the mapping cone of the underlying morphism. -/
theorem acyclic_cone_iff_quasiIso {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) :
    (cone f).complex.Acyclic ↔ QuasiIso f.toHomologicalComplex := by
  rw [(conePackage f).cone_complex]
  exact CochainComplex.mappingCone.acyclic_iff_quasiIso _

/-- A homomorphism of right differential graded `A`-modules whose cone is acyclic becomes an
isomorphism of the derived category of `(A, d)`: it is a quasi-isomorphism, and the
quasi-isomorphisms are the arrows the localization functor inverts. -/
theorem isIso_toDerivedCategory_map_of_acyclic_cone
    {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) (hf : (cone f).complex.Acyclic) :
    IsIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map f)) :=
  (quasiIsomorphisms.{t, a, m} A).Q_inverts _
    ((quasiIsomorphisms_quotient_map_iff.{t, a, m} f).2
      ((acyclic_cone_iff_quasiIso.{t, a, m} A f).1 hf))

end General

/-! ### The quasi-isomorphisms are the arrows attached to the acyclic objects -/

section RingedSite

open CategoryTheory.Pretriangulated

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 0FT4.** The quasi-isomorphisms of `K(Mod(A, d))` are exactly the
arrows whose cone is acyclic, that is, the class of arrows attached to the triangulated
subcategory `Ac` of acyclic objects.

Both inclusions are read off one distinguished triangle on the given arrow: such a triangle is
isomorphic to the triangle of an admissible short exact sequence `M → N → P` of right
differential graded modules, whose underlying sequence of complexes of sheaves of modules is
short exact, and for a short exact sequence of complexes the first map is a quasi-isomorphism
exactly when the third term is acyclic. -/
@[stacks 0FT4 "Qis is the class of arrows attached to Ac"]
theorem acyclic_trW_eq_quasiIsomorphisms :
    (acyclic.{u, v, w} A).trW = quasiIsomorphisms A := by
  ext Y Z φ
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective φ
  obtain ⟨W, g, h, hT⟩ :=
    distinguished_cocone_triangle ((HomotopyCategory.quotient A).map f)
  obtain ⟨M, N, P, f', g', δ, E, hf, hg, ⟨e⟩, -⟩ :=
    (HomotopyCategory.distinguished_iff A _).1 hT
  have harrow : Arrow.mk ((HomotopyCategory.quotient A).map f) ≅
      Arrow.mk ((HomotopyCategory.quotient A).map f') :=
    Arrow.isoMk (Triangle.π₁.mapIso e) (Triangle.π₂.mapIso e) e.hom.comm₁.symm
  refine ((acyclic.{u, v, w} A).trW_iff_of_distinguished _ hT).trans
    (((acyclic.{u, v, w} A).prop_iff_of_iso (Triangle.π₃.mapIso e)).trans
      (((quasiIso_f_iff_acyclic_X₃ (split_shortExact A f' g' E hf hg)).symm.trans ?_)))
  exact ((quasiIsomorphisms_quotient_map_iff f').symm.trans
    ((quasiIsomorphisms A).arrow_mk_iso_iff harrow).symm)

/-- **Stacks Project, Tag 0FT6.** The kernel of the localization functor
`Q : K(Mod(A, d)) ⟶ D(A, d)` is the subcategory `Ac` of acyclic right differential graded
modules: the quasi-isomorphisms are the class of arrows attached to `Ac`, and a strictly full
saturated triangulated subcategory is recovered as the objects killed by the localization at
the class of arrows it determines. -/
@[stacks 0FT6 "ker(Q) = Ac"]
theorem toDerivedCategory_kernel_eq_acyclic :
    (toDerivedCategory.{u, v, w} A).kernel = acyclic.{u, v, w} A := by
  change (quasiIsomorphisms A).Q.kernel = acyclic.{u, v, w} A
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  exact ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self.2
    (acyclic.{u, v, w} A) (acyclic.{u, v, w} A).trW.Q

end RingedSite

end SheafOfModules.DifferentialGradedModule

end
