module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.PullbackSquare

/-!
# Restriction squares of the relative spectrum of a quasi-coherent algebra

Let `X` be a scheme and let `A` be a sheaf of commutative `𝒪_X`-algebras whose underlying
module is quasi-coherent. For nested affine opens `U ≤ U'` of `X` this file proves that the
square
```
Spec A(U)  ⟶  Spec A(U')
   ↓              ↓
   U       ⟶      U'
```
is cartesian, which is Stacks Tag 01LN.

## Main definitions

* `Stacks.RelativeSpec.AlgebraSheaf` is a sheaf of commutative algebras over the structure
  sheaf of a scheme, with `AlgebraSheaf.ringSheaf`, `AlgebraSheaf.structureMap` and
  `AlgebraSheaf.underlyingModule` extracting the underlying sheaf of rings, the structure
  morphism of sheaves of rings and the underlying `𝒪_X`-module.
* `Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` is quasi-coherence of that module, and
  `Stacks.RelativeSpec.RelativeSpecSituation` bundles a scheme together with a quasi-coherent
  algebra over it.
* `Stacks.RelativeSpec.AlgebraSheaf.algebraSections`,
  `Stacks.RelativeSpec.AlgebraSheaf.algebraRestrict` and
  `Stacks.RelativeSpec.AlgebraSheaf.algebraSectionsOfLE` are the three algebra structures on
  sections of an algebra sheaf over nested opens, and
  `Stacks.RelativeSpec.AlgebraSheaf.isScalarTower_sections` and
  `Stacks.RelativeSpec.AlgebraSheaf.isScalarTower_restrict` are the two scalar towers they
  form.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.isPushout_sections` is the algebraic content: for a
  quasi-coherent algebra and affine opens `U ≤ U'`, the sections form a pushout square
  `A(U) = A(U') ⊗_{Γ(X, U')} Γ(X, U)` of commutative rings.
* `Stacks.RelativeSpec.AlgebraSheaf.isPushout_app_map` is the same statement in `CommRingCat`.
* `Stacks.RelativeSpec.isPullback_specMap_restriction` is Tag 01LN.
* `Stacks.RelativeSpec.specMap_restriction_comp` is Tag 01LO: the morphisms of Tag 01LN compose.

## Implementation notes

The whole content is the identification of Mathlib's `Algebra.IsPushout`, which is by
definition an `IsBaseChange` statement, with the base-change statement
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ` for the underlying
module. The `Γ(X, U)`-module structure on the sections of `AlgebraSheaf.underlyingModule A`
over `U` is obtained by restriction of scalars along the structure morphism, and the
`Γ(X, U)`-algebra structure `AlgebraSheaf.algebraSections` on the same sections is obtained
from the same ring map by `RingHom.toAlgebra`; the two induced module structures agree
definitionally, so `AlgebraSheaf.isPushout_sections` is literally
`isBaseChange_restrictₗ` for the underlying module, and no transport is needed.

From there `CommRingCat.isPushout_of_isPushout` produces the categorical pushout square of
rings (after a `CategoryTheory.IsPushout.flip`, since that lemma orients the square with the
map of structure sheaves on the first edge), and `isPullback_specMap_of_isPushout` turns it
into the cartesian square of spectra.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01LN](https://stacks.math.columbia.edu/tag/01LN)
* [Stacks Project, Tag 01LO](https://stacks.math.columbia.edu/tag/01LO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.RelativeSpec

/-- A sheaf of commutative `𝒪_X`-algebras on a scheme `X`, i.e. a sheaf of commutative rings
together with a morphism from the structure sheaf. -/
@[ega "0 4.1.3" "special case"]
abbrev AlgebraSheaf (X : Scheme.{u}) := Under X.sheaf

namespace AlgebraSheaf

variable {X : Scheme.{u}}

/-- The underlying sheaf of (not necessarily commutative) rings of an algebra sheaf. -/
noncomputable def ringSheaf (A : AlgebraSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj A.right

/-- The structure morphism of an algebra sheaf, as a morphism of sheaves of rings. -/
noncomputable def structureMap (A : AlgebraSheaf X) : X.ringCatSheaf ⟶ ringSheaf A :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map A.hom

/-- The underlying `𝒪_X`-module of an algebra sheaf: the sheaf of rings `ringSheaf A`, viewed
as a module over itself and then restricted along the structure morphism. -/
noncomputable def underlyingModule (A : AlgebraSheaf X) : X.Modules :=
  (SheafOfModules.restrictScalars.{u} (structureMap A)).obj (SheafOfModules.unit (ringSheaf A))

/-- An algebra sheaf is quasi-coherent when its underlying module is quasi-coherent. -/
@[ega "0 5.1.3"]
abbrev IsQuasicoherent (A : AlgebraSheaf X) : Prop := (underlyingModule A).IsQuasicoherent

/-- The commutative ring of sections of an algebra sheaf over an open. -/
noncomputable abbrev sections (A : AlgebraSheaf X) (U : X.Opens) : CommRingCat.{u} :=
  A.right.obj.obj (op U)

/-- Naturality of the structure morphism of an algebra sheaf: restricting a section of the
structure sheaf and then pushing it into the algebra agrees with pushing it into the algebra
and then restricting. -/
theorem presheaf_map_comp_app (A : AlgebraSheaf X) {U V : X.Opens} (h : U ≤ V) :
    X.presheaf.map (homOfLE h).op ≫ A.hom.hom.app (op U) =
      A.hom.hom.app (op V) ≫ A.right.obj.map (homOfLE h).op :=
  A.hom.hom.naturality (homOfLE h).op

/-- The `Γ(X, U)`-algebra structure on the sections of an algebra sheaf over `U`, given by the
structure morphism at `U`. -/
@[instance_reducible]
noncomputable def algebraSections (A : AlgebraSheaf X) (U : X.Opens) :
    Algebra Γ(X, U) (sections A U) :=
  (A.hom.hom.app (op U)).hom.toAlgebra

/-- For `U ≤ V`, the `A(V)`-algebra structure on `A(U)` given by restriction in the algebra
sheaf. -/
@[instance_reducible]
noncomputable def algebraRestrict (A : AlgebraSheaf X) {U V : X.Opens} (h : U ≤ V) :
    Algebra (sections A V) (sections A U) :=
  (A.right.obj.map (homOfLE h).op).hom.toAlgebra

/-- For `U ≤ V`, the `Γ(X, V)`-algebra structure on `A(U)`, given by restricting a section of
the structure sheaf to `U` and then pushing it into the algebra. -/
@[instance_reducible]
noncomputable def algebraSectionsOfLE (A : AlgebraSheaf X) {U V : X.Opens} (h : U ≤ V) :
    Algebra Γ(X, V) (sections A U) :=
  (X.presheaf.map (homOfLE h).op ≫ A.hom.hom.app (op U)).hom.toAlgebra

/-- The scalar tower `Γ(X, V) → Γ(X, U) → A(U)` for `U ≤ V`. -/
theorem isScalarTower_sections (A : AlgebraSheaf X) {U V : X.Opens} (h : U ≤ V) :
    letI := algebraOfLE X h
    letI := algebraSections A U
    letI := algebraSectionsOfLE A h
    IsScalarTower Γ(X, V) Γ(X, U) (sections A U) :=
  let := algebraOfLE X h
  let := algebraSections A U
  let := algebraSectionsOfLE A h
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The scalar tower `Γ(X, V) → A(V) → A(U)` for `U ≤ V`. -/
theorem isScalarTower_restrict (A : AlgebraSheaf X) {U V : X.Opens} (h : U ≤ V) :
    letI := algebraSections A V
    letI := algebraRestrict A h
    letI := algebraSectionsOfLE A h
    IsScalarTower Γ(X, V) (sections A V) (sections A U) :=
  let := algebraSections A V
  let := algebraRestrict A h
  let := algebraSectionsOfLE A h
  IsScalarTower.of_algebraMap_eq fun c ↦ congr($(presheaf_map_comp_app A h).hom c)

/-- For a quasi-coherent algebra sheaf and nested affine opens `U ≤ U'`, the sections over `U`
are the base change of the sections over `U'`, i.e. `A(U) = A(U') ⊗_{Γ(X, U')} Γ(X, U)`. -/
theorem isPushout_sections (A : AlgebraSheaf X) [A.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    letI := algebraOfLE X h
    letI := algebraSections A U
    letI := algebraSections A U'
    letI := algebraRestrict A h
    letI := algebraSectionsOfLE A h
    letI := isScalarTower_restrict A h
    letI := isScalarTower_sections A h
    Algebra.IsPushout Γ(X, U') Γ(X, U) (sections A U') (sections A U) :=
  let := algebraOfLE X h
  let := algebraSections A U
  let := algebraSections A U'
  let := algebraRestrict A h
  let := algebraSectionsOfLE A h
  let := isScalarTower_restrict A h
  let := isScalarTower_sections A h
  ⟨isBaseChange_restrictₗ (underlyingModule A) hU hU' h⟩

/-- The pushout square of `isPushout_sections`, as a pushout square in `CommRingCat`: for a
quasi-coherent algebra sheaf and nested affine opens `U ≤ U'`, the square formed by the
structure morphisms of `A` at `U'` and `U` and the two restriction maps is a pushout. -/
theorem isPushout_app_map (A : AlgebraSheaf X) [A.IsQuasicoherent] {U U' : X.Opens}
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    IsPushout (A.hom.hom.app (op U')) (X.presheaf.map (homOfLE h).op)
      (A.right.obj.map (homOfLE h).op) (A.hom.hom.app (op U)) :=
  let := algebraOfLE X h
  let := algebraSections A U
  let := algebraSections A U'
  let := algebraRestrict A h
  let := algebraSectionsOfLE A h
  let := isScalarTower_restrict A h
  let := isScalarTower_sections A h
  let := isPushout_sections A hU hU' h
  (CommRingCat.isPushout_of_isPushout Γ(X, U') Γ(X, U) (sections A U') (sections A U)).flip

end AlgebraSheaf

/-- A scheme equipped with a quasi-coherent sheaf of commutative
algebras over its structure sheaf. -/
@[stacks 01LM]
structure RelativeSpecSituation where
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The sheaf of commutative algebras over the structure sheaf of the base. -/
  algebra : AlgebraSheaf base
  /-- The module underlying the algebra sheaf is quasi-coherent. -/
  [isQuasicoherent : algebra.IsQuasicoherent]

attribute [instance] RelativeSpecSituation.isQuasicoherent

/-- For nested affine opens `U ⊆ U'` of the base of a relative spectrum situation, the square
formed by the spectra of the sections of the quasi-coherent algebra, the two open subschemes,
and their canonical restriction morphisms is cartesian. -/
@[stacks 01LN]
theorem isPullback_specMap_restriction (s : RelativeSpecSituation.{u})
    (U U' : s.base.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (h : U ≤ U') :
    IsPullback
      (Spec.map (s.algebra.right.obj.map (homOfLE h).op))
      (Spec.map (s.algebra.hom.hom.app (.op U)) ≫ hU.isoSpec.inv)
      (Spec.map (s.algebra.hom.hom.app (.op U')) ≫ hU'.isoSpec.inv)
      (s.base.homOfLE h) :=
  isPullback_specMap_of_isPushout hU hU' h _ _ _
    (AlgebraSheaf.isPushout_app_map s.algebra hU hU' h)

/-- For opens `U ⊆ U' ⊆ U''` of the base of a relative spectrum situation, the composition of
the morphisms `Spec A(U) ⟶ Spec A(U')` and `Spec A(U') ⟶ Spec A(U'')` of
`Stacks.RelativeSpec.isPullback_specMap_restriction` is the morphism `Spec A(U) ⟶ Spec A(U'')`
of the same lemma. -/
@[stacks 01LO "the composite of the restriction morphisms of spectra of sections is the \
restriction morphism"]
theorem specMap_restriction_comp (s : RelativeSpecSituation.{u}) {U U' U'' : s.base.Opens}
    (h : U ≤ U') (h' : U' ≤ U'') :
    Spec.map (s.algebra.right.obj.map (homOfLE h).op) ≫
        Spec.map (s.algebra.right.obj.map (homOfLE h').op) =
      Spec.map (s.algebra.right.obj.map (homOfLE (h.trans h')).op) := by
  rw [← Spec.map_comp, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end Stacks.RelativeSpec

end
