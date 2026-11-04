module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Complexes of modules on a site as a differential graded category over a base ring

Let `C` be a site and let `O` be a sheaf of rings on it whose rings of sections are commutative.
Multiplying by a global section of `O` makes the category of sheaves of `O`-modules linear over
the ring `Γ(C, O)` of global sections, which is
`Stacks.Cohomology.SiteModules.linearSheafOfModules`. The complexes of `O`-modules are therefore
the objects of a differential graded category *over `Γ(C, O)`*, and the endomorphism differential
graded algebra of a complex of `O`-modules is a `Γ(C, O)`-algebra, not merely a `ℤ`-algebra.

This is the base ring of Stacks 0CS6. There the datum is a ring `R` together with the structure
of a sheaf of commutative `R`-algebras on `O`; `AlgebraSheaf` is that datum, and
`AlgebraSheaf.toGlobalSections` identifies it with a ring map `R → Γ(C, O)`, so `Γ(C, O)` is the
universal choice of base ring and every other one is obtained from it by restricting scalars
along that map.

## Main definitions

* `CategoryTheory.Linear.ofRingHom`: a category linear over `S` is linear over any commutative
  ring mapping to `S`.
* `Stacks.Cohomology.SiteModules.AlgebraSheaf`: the structure of a sheaf of `R`-algebras on `O`,
  a ring map `R → O(U)` for every `U` compatible with restriction, and
  `AlgebraSheaf.toGlobalSections`, the ring map to `Γ(C, O)` that it is.
* `Stacks.Cohomology.SiteModules.compDGGlobalSections` and
  `Stacks.Cohomology.SiteModules.compDGOver`: `Comp^dg(O)` as a differential graded category over
  `Γ(C, O)`, and over an arbitrary base ring.
* `Stacks.Cohomology.SiteModules.endomorphismAlgebraGlobalSections` and
  `Stacks.Cohomology.SiteModules.endomorphismAlgebraOver`: the endomorphism differential graded
  algebra of a complex of `O`-modules, over those base rings.

## Implementation notes

The differential graded category is `CochainComplex.dgCategoryLinear`, which is the same objects,
homogeneous morphisms, differential, composition and identities as the `ℤ`-linear
`CochainComplex.dgCategory` of Stacks 09L9 — they agree by `rfl` — with the module structure on
homogeneous morphisms kept.

Commutativity of the sections of `O` is assumed in the unbundled form
`∀ U, IsMulCommutative (O.obj.obj U)`, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/GlobalSectionLinear.lean`; registering
`CommRing (O.obj.obj U)` globally would be a second route to `Ring (O.obj.obj U)` beside the one
`RingCat` carries. For a ringed site that hypothesis is discharged by
`AlgebraicGeometry.RingedSite.ringSheafSectionsIsMulCommutative`, which asserts only
commutativity of the multiplication and so introduces no such diamond.

`CategoryTheory.Linear.ofRingHom` is not an instance: a ring map is data, and two of them give
two different linear structures on the same category.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped IsMulCommutative

universe w r v u

namespace CategoryTheory.Linear

/-- A category linear over `S` is linear over any commutative ring mapping to `S`: a scalar acts
through its image. This is restriction of scalars for a linear structure, and it is data rather
than an instance because the ring map is. -/
@[instance_reducible]
public def ofRingHom {R S : Type*} [CommRing R] [CommRing S] {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear S D] (φ : R →+* S) : Linear R D where
  homModule P Q :=
    { smul := fun x f => φ x • f
      one_smul := fun f => show φ 1 • f = f by rw [map_one, one_smul]
      mul_smul := fun x y f => show φ (x * y) • f = φ x • φ y • f by rw [map_mul, mul_smul]
      smul_zero := fun x => show φ x • (0 : P ⟶ Q) = 0 from smul_zero _
      smul_add := fun x f g => show φ x • (f + g) = φ x • f + φ x • g from smul_add _ f g
      add_smul := fun x y f => show φ (x + y) • f = φ x • f + φ y • f by rw [map_add, add_smul]
      zero_smul := fun f => show φ 0 • f = 0 by rw [map_zero, zero_smul] }
  smul_comp P Q T x f g := Linear.smul_comp P Q T (φ x) f g
  comp_smul P Q T f x g := Linear.comp_smul P Q T f (φ x) g

/-- Scalars act through the ring map. -/
public theorem ofRingHom_smul {R S : Type*} [CommRing R] [CommRing S] {D : Type u}
    [Category.{v} D] [Preadditive D] [Linear S D] (φ : R →+* S) {P Q : D} (x : R) (f : P ⟶ Q) :
    letI := ofRingHom (D := D) φ
    x • f = φ x • f := rfl

end CategoryTheory.Linear

namespace AlgebraicGeometry.RingedSite

/-- The rings of sections of the structure sheaf of a ringed site are commutative. Only
commutativity of the multiplication is asserted, so no second `Ring` instance on the sections is
introduced. -/
public instance ringSheafSectionsIsMulCommutative (X : RingedSite.{u, v, w}) (U : X.Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  ⟨⟨fun a b => mul_comm (G := X.O.obj.obj U) a b⟩⟩

end AlgebraicGeometry.RingedSite

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ U : Cᵒᵖ, IsMulCommutative (O.obj.obj U)]

/-- **The base-ring datum of Stacks 0CS6.** The structure of a sheaf of `R`-algebras on `O`: a
ring map `R → O(U)` for every object `U` of the site, compatible with restriction. -/
public structure AlgebraSheaf (R : Type*) [CommRing R] where
  /-- The structure map of the algebra of sections over `U`. -/
  algebraMap (U : Cᵒᵖ) : R →+* O.obj.obj U
  /-- The structure maps are compatible with restriction. -/
  algebraMap_restrict {U V : Cᵒᵖ} (f : U ⟶ V) (x : R) :
    (O.obj.map f).hom (algebraMap U x) = algebraMap V x

namespace AlgebraSheaf

variable {O} {R : Type*} [CommRing R] (a : AlgebraSheaf O R)

/-- A sheaf of `R`-algebra structures on `O` is a ring map from `R` to the global sections of
`O`: the compatibility with restriction is exactly the condition for the family of images of a
scalar to be a global section. -/
public def toGlobalSections : R →+* ↥(GlobalSectionRing O) where
  toFun x := ⟨fun U => a.algebraMap U x, fun f => a.algebraMap_restrict f x⟩
  map_one' := Subtype.ext (funext fun U => map_one (a.algebraMap U))
  map_mul' x y := Subtype.ext (funext fun U => map_mul (a.algebraMap U) x y)
  map_zero' := Subtype.ext (funext fun U => map_zero (a.algebraMap U))
  map_add' x y := Subtype.ext (funext fun U => map_add (a.algebraMap U) x y)

/-- The section over `U` of the global section `a.toGlobalSections x` is `a.algebraMap U x`. -/
@[simp] public theorem toGlobalSections_val (x : R) (U : Cᵒᵖ) :
    (a.toGlobalSections x).val U = a.algebraMap U x := rfl

end AlgebraSheaf

/-- **`Comp^dg(O)` over the ring of global sections of `O`.** The complexes of `O`-modules form a
differential graded category over `Γ(C, O)`, because multiplying by a global section of `O` makes
the sheaves of `O`-modules a `Γ(C, O)`-linear category. The objects, homogeneous morphisms,
differential, composition and identities are those of the `ℤ`-linear
`CochainComplex.dgCategory`. -/
public abbrev compDGGlobalSections : DGCategory ↥(GlobalSectionRing O) :=
  CochainComplex.dgCategoryLinear (SheafOfModules.{w} O) ↥(GlobalSectionRing O)

/-- **The endomorphism differential graded algebra of a complex of `O`-modules over
`Γ(C, O)`.** This is the algebra `(E, d) = Hom_{Comp^dg(O)}(K, K)` of Stacks 09LV–09LX with its
scalars kept: a differential graded `Γ(C, O)`-algebra rather than a differential graded
`ℤ`-algebra. -/
public def endomorphismAlgebraGlobalSections (K : CochainComplex (SheafOfModules.{w} O) ℤ) :
    DifferentialGradedAlgebra ↥(GlobalSectionRing O) :=
  (DGCategory.homRepresentation (compDGGlobalSections O) K).algebra

/-- **`Comp^dg(O)` over an arbitrary base ring.** For a sheaf of `R`-algebra structures on `O`,
the complexes of `O`-modules form a differential graded category over `R`: scalars act through
the global sections of `O`. -/
public def compDGOver (R : Type*) [CommRing R] (a : AlgebraSheaf O R) :
    DGCategory R :=
  letI := Linear.ofRingHom (D := SheafOfModules.{w} O) a.toGlobalSections
  CochainComplex.dgCategoryLinear (SheafOfModules.{w} O) R

/-- **The endomorphism differential graded algebra of a complex of `O`-modules over an arbitrary
base ring.** For `O` a sheaf of `R`-algebras this is the `(E, d)` of Stacks 09LV–09LX as a
differential graded `R`-algebra. -/
public def endomorphismAlgebraOver (R : Type*) [CommRing R] (a : AlgebraSheaf O R)
    (K : CochainComplex (SheafOfModules.{w} O) ℤ) :
    DifferentialGradedAlgebra R :=
  (DGCategory.homRepresentation (compDGOver O R a) K).algebra

end Stacks.Cohomology.SiteModules

end
