module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraIdentityGenerator

/-!
# Transporting an annihilation hypothesis, and a descended chain of presentations

`SheafOfModules.GradedAlgebra.descend` takes a sheaf of graded `R`-algebras whose every
homogeneous piece is annihilated by the kernel of a locally surjective `α : R ⟶ R'` to a sheaf
of graded `R'`-algebras, and `SheafOfModules.GradedAlgebra.UnitalHom.descend` descends a unital
homomorphism between two such algebras. A chain of presentations of one graded algebra therefore
descends link by link — except that each link needs its *own* annihilation hypothesis before
`descend` may even be written down, while a chain is typically produced with the annihilation
known at one end only.

This file supplies the missing transport. The pieces of two sheaves of graded algebras joined by
a homomorphism which is an isomorphism in that degree are isomorphic as sheaves of modules, and
annihilation of a sheaf of modules by a section of the ring sheaf passes across an isomorphism;
so one annihilation hypothesis serves for every algebra of a degreewise invertible chain. With
it, each link of the descended chain is a single application of
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_of_degreewiseIso`.

## Main results

* `SheafOfModules.GradedAlgebra.UnitalHom.smul_piece_eq_zero`: **the annihilation transport.** A
  section of the ring sheaf annihilating the degree-`n` piece of `B` annihilates that of `A`, for
  a unital homomorphism `A ⟶ B` invertible in degree `n`.
* `SheafOfModules.GradedAlgebra.UnitalHom.smul_piece_eq_zero_of_ker`: the same in the shape
  `SheafOfModules.GradedAlgebra.descend` consumes, quantified over degrees and objects.
* `SheafOfModules.GradedAlgebra.isExteriorAlgebra_id_descend_ofDegreewiseIso` and
  `isExteriorAlgebra_id_descend_of_degreewiseIso`: **one link of a descended chain**, in either
  direction: the descents along one quotient of two sheaves of graded algebras joined by a
  degreewise invertible unital homomorphism are exterior algebras of their own degree-one pieces
  together. The degreewise invertibility is an explicit hypothesis rather than an instance: the
  two sheaves of rings in play at a change of presentation are typically one sheaf of rings under
  two spellings, which unification crosses and instance search does not.

## Implementation notes

**The transport runs through the degreewise inverse and nothing else.** A unital homomorphism
invertible in degree `n` has an inverse morphism of sheaves of modules there, which is
`R`-linear; so the image of an annihilated section under it is annihilated, and a section is the
image of its own image. No sheaf condition and no local argument is used, the statement being
about one object of the site at a time.

**Why both directions of the link are recorded.** The chain of presentations a local-to-global
argument runs along is traversed in the direction opposite to the one in which its links are
constructed: the universal property is proved on the presentation a local computation produces
and consumed on the presentation in which the comparison map is built. The two directions differ
only by `SheafOfModules.GradedAlgebra.UnitalHom.inverse`, which
`SheafOfModules.GradedAlgebra.UnitalHom.isIso_inverse_app` keeps degreewise invertible.

**No `@[stacks]` attribute.** Nothing here is a clause of a tag: these are transport primitives
for a chain of presentations of one sheaf of graded algebras.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a v u

namespace SheafOfModules.GradedAlgebra

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- **The annihilation transport.** Let `φ : A ⟶ B` be a unital homomorphism of sheaves of graded
`R`-algebras which is an isomorphism in degree `n`. A section `b` of `R` over `V` which
annihilates every section of the degree-`n` piece of `B` over `V` annihilates every section of
the degree-`n` piece of `A` over `V`.

Every section of `A.piece n` over `V` is the image under the inverse of `φ.app n` of its own
image, that inverse is a morphism of sheaves of modules and so `R`-linear, and it carries `0`
to `0`. -/
theorem UnitalHom.smul_piece_eq_zero (φ : UnitalHom A B) (n : ℤ) [IsIso (φ.app n)] {V : Cᵒᵖ}
    {b : R.obj.obj V} (hB : ∀ m : (B.piece n).val.obj V, b • m = 0)
    (m : (A.piece n).val.obj V) : b • m = 0 := by
  have hrt : (inv (φ.app n)).val.app V ((φ.app n).val.app V m) = m :=
    congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom
      ((_root_.SheafOfModules.Hom.val g).app V))) (IsIso.hom_inv_id (φ.app n))) m
  calc b • m = b • (inv (φ.app n)).val.app V ((φ.app n).val.app V m) := by rw [hrt]
    _ = (inv (φ.app n)).val.app V (b • (φ.app n).val.app V m) := (map_smul _ _ _).symm
    _ = (inv (φ.app n)).val.app V 0 := by rw [hB]
    _ = 0 := map_zero _

variable {R' : Sheaf J RingCat.{t}} (α : R ⟶ R')

/-- **The annihilation transport, in the shape `SheafOfModules.GradedAlgebra.descend`
consumes.** -/
theorem UnitalHom.smul_piece_eq_zero_of_ker (φ : UnitalHom A B) [∀ n, IsIso (φ.app n)]
    (hB : ∀ (n : ℤ) (V : Cᵒᵖ) (b : R.obj.obj V), b ∈ RingHom.ker (α.hom.app V).hom →
      ∀ m : (B.piece n).val.obj V, b • m = 0)
    (n : ℤ) (V : Cᵒᵖ) (b : R.obj.obj V) (hb : b ∈ RingHom.ker (α.hom.app V).hom)
    (m : (A.piece n).val.obj V) : b • m = 0 :=
  φ.smul_piece_eq_zero n (hB n V b hb) m

end Transport

section Link

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{t}}
  (α : R ⟶ R') [Presheaf.IsLocallySurjective J α.hom] {A B : GradedAlgebra.{t, t} R}
  (hA : ∀ (n : ℤ) (V : Cᵒᵖ) (b : R.obj.obj V), b ∈ RingHom.ker (α.hom.app V).hom →
    ∀ m : (A.piece n).val.obj V, b • m = 0)
  (hB : ∀ (n : ℤ) (V : Cᵒᵖ) (b : R.obj.obj V), b ∈ RingHom.ker (α.hom.app V).hom →
    ∀ m : (B.piece n).val.obj V, b • m = 0)

/-- **One link of a descended chain of presentations.** If the descent of `A` along `α` is the
exterior algebra of its own degree-one piece and `φ : A ⟶ B` is an isomorphism in every degree,
then so is the descent of `B`.

`SheafOfModules.GradedAlgebra.UnitalHom.descend` descends `φ`, degreewise invertibly by
`SheafOfModules.GradedAlgebra.UnitalHom.isIso_descend_app`, and
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.id_ofDegreewiseIso` transports the universal
property along it. -/
theorem isExteriorAlgebra_id_descend_ofDegreewiseIso (φ : UnitalHom A B)
    (hφ : ∀ n, IsIso (φ.app n))
    (h : IsExteriorAlgebra (descend α A hA) (𝟙 ((descend α A hA).piece 1))) :
    IsExteriorAlgebra (descend α B hB) (𝟙 ((descend α B hB).piece 1)) :=
  have : ∀ n, IsIso (φ.app n) := hφ
  h.id_ofDegreewiseIso (φ.descend α hA hB)

/-- **One link of a descended chain of presentations, backwards.** The direction a
local-to-global argument traverses: the universal property is established on the presentation a
local computation produces and is needed on the presentation in which the comparison map is
built. -/
theorem isExteriorAlgebra_id_descend_of_degreewiseIso (φ : UnitalHom A B)
    (hφ : ∀ n, IsIso (φ.app n))
    (h : IsExteriorAlgebra (descend α B hB) (𝟙 ((descend α B hB).piece 1))) :
    IsExteriorAlgebra (descend α A hA) (𝟙 ((descend α A hA).piece 1)) :=
  have : ∀ n, IsIso (φ.app n) := hφ
  h.id_of_degreewiseIso (φ.descend α hA hB)

end Link

end SheafOfModules.GradedAlgebra

end
