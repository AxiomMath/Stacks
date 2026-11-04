module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraExtendScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Pullback of a sheaf of graded algebras along a morphism of ringed topoi

A morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` pulls back a sheaf of graded
`O_D`-algebras to a sheaf of graded `O_C`-algebras, degree by degree. Pullback of sheaves of
modules is the inverse image followed by extension of scalars along the inverse-image form of
the structure map, and the graded pullback is the composite of the two constructions of those
two steps, so its homogeneous pieces are the module pullbacks of the original homogeneous
pieces on the nose, not merely isomorphic to them.

## Main definitions

* `toposPullbackGradedAlgebra` is the pullback of a sheaf of graded algebras, and
  `toposPullbackGradedAlgebraFunctor` is that construction as a functor.
* `pullbackGeneratorSection` is the canonical local section of a pullback attached to a pure
  tensor, and `IsInducedPullbackMultiplication` and `IsInducedPullbackUnit` say that the
  multiplication and unit of a pullback are the induced ones, read on those sections.
* `GradedAlgebraPullbackSpecification` bundles the degreewise object and morphism equations
  with those two conditions.

## Main results

* `toposPullbackGradedAlgebra_piece` and `toposPullbackGradedAlgebraFunctor_map_app`: the
  homogeneous pieces and the degreewise components are the module pullbacks of the original
  ones, both on the nose.
* `gradedAlgebraPullbackSpecification` and `nonempty_gradedAlgebraPullbackSpecification`: the
  degreewise module pullbacks assemble into a functor of graded algebras with the induced
  multiplication and unit.

## Implementation notes

The two steps are `Stacks.Sheaves.GradedAlgebraInverseImage.inverseImageGradedAlgebra`, which
transports a graded algebra along the inverse image of the underlying morphism of topoi, and
`Stacks.Sheaves.GradedAlgebraExtendScalars.extendScalarsGradedAlgebra`, which extends scalars
along a morphism of presheaves of commutative rings. They compose on the nose because the
inverse-image sheaf of rings is the sheaf of rings underlying a presheaf of commutative rings,
by `Stacks.Sheaves.RingedToposModules.pullbackRingSheaf_eq_commRingSheaf`, and because the
structure sheaf of rings of the source is the one underlying its presheaf of commutative rings.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry TensorProduct Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraExtendScalars
open Stacks.Sheaves.GradedAlgebraInverseImage

namespace Stacks.Sheaves.GradedAlgebraPullback

universe w v u

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **Pullback of a sheaf of graded algebras along a morphism of ringed topoi.** The homogeneous
pieces are the module pullbacks of the original homogeneous pieces, and the multiplication and
unit are induced by the original ones.

This is part (2) of Stacks 0FQX: the inverse image of the graded algebra along the underlying
morphism of topoi, followed by extension of scalars along the inverse-image form of the
structure map. -/
public noncomputable def toposPullbackGradedAlgebra
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  extendScalarsGradedAlgebra (fSharpCommRing f) X.J
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B)

/-- The homogeneous pieces of the pullback of a sheaf of graded algebras are the module
pullbacks of the original homogeneous pieces. -/
public theorem toposPullbackGradedAlgebra_piece
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (n : ℤ) :
    (toposPullbackGradedAlgebra f B).piece n = (f.pullbackModules).obj (B.piece n) :=
  rfl

/-- **Pullback of sheaves of graded algebras along a morphism of ringed topoi, as a functor.**
It is the inverse image followed by extension of scalars, exactly as `pullbackModules` is for
sheaves of modules, so its degreewise components are the module pullbacks of the degreewise
components. -/
public noncomputable def toposPullbackGradedAlgebraFunctor :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  inverseImageGradedAlgebraFunctor f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
    extendScalarsGradedAlgebraFunctor (fSharpCommRing f) X.J
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

/-- The pullback functor of sheaves of graded algebras acts on objects by
`toposPullbackGradedAlgebra`. -/
public theorem toposPullbackGradedAlgebraFunctor_obj
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (toposPullbackGradedAlgebraFunctor f).obj B = toposPullbackGradedAlgebra f B :=
  rfl

/-- The degreewise components of the pullback of a homomorphism of sheaves of graded algebras
are the module pullbacks of its degreewise components. -/
public theorem toposPullbackGradedAlgebraFunctor_map_app
    {B C : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (g : B ⟶ C) (n : ℤ) :
    ((toposPullbackGradedAlgebraFunctor f).map g).app n = (f.pullbackModules).map (g.app n) :=
  rfl

/-! ### The characterisation of a pullback of sheaves of graded algebras -/

/-- The inverse image of a homogeneous piece, before extension of scalars. -/
public noncomputable abbrev inverseImagePiece
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (n : ℤ) :
    SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (B.piece n)

/-- **The canonical local sections of a specified pullback of a sheaf of graded algebras**: a
pure tensor of a local section of the inverse image of a homogeneous piece, carried through the
sheafification unit of the extension of scalars and then along the identification of the
specified pullback with the module pullback. Extension of scalars is a sheafified tensor
product, so these sections generate the pullback locally, and the multiplication and the unit
of a pullback are pinned down by their values on them. -/
public noncomputable def pullbackGeneratorSection
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (h : ∀ n, A.piece n = (f.pullbackModules).obj (B.piece n)) (n : ℤ) (U : X.Cᵒᵖ)
    (t : cofObj (fSharpCommRing f) (inverseImagePiece f B n).val U) :
    (A.piece n).val.obj U :=
  (eqToHom (h n).symm).val.app U
    (PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        ((changeOfRings (fSharpCommRing f)).obj (inverseImagePiece f B n).val)) U t)

/-- **The multiplication of a specified pullback is the one induced by the original
multiplication**: on the canonical local sections it is given by `(a ⊗ x) · (c ⊗ y) =
ac ⊗ xy`, where `xy` is the inverse image of the multiplication of the original algebra. -/
public def IsInducedPullbackMultiplication
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (h : ∀ n, A.piece n = (f.pullbackModules).obj (B.piece n)) : Prop :=
  ∀ (i j : ℤ) (U : X.Cᵒᵖ),
    letI := ((fSharpCommRing f).app U).hom.toAlgebra
    ∀ (a c : X.O.obj.obj U) (x : (inverseImagePiece f B i).val.obj U)
      (y : (inverseImagePiece f B j).val.obj U),
      (A.mul i j).app U
          (pullbackGeneratorSection f A B h i U
            (a ⊗ₜ[(inverseImageStructureCommRing f).obj U] x))
          (pullbackGeneratorSection f A B h j U
            (c ⊗ₜ[(inverseImageStructureCommRing f).obj U] y)) =
        pullbackGeneratorSection f A B h (i + j) U
          ((a * c) ⊗ₜ[(inverseImageStructureCommRing f).obj U]
            ((inverseImageGradedAlgebra f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).mul i j).app U
              x y)

/-- **The unit of a specified pullback is the image of the original unit**: the canonical local
section `1 ⊗ 1`, with `1` the inverse image of the unit of the original algebra. -/
public def IsInducedPullbackUnit
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (h : ∀ n, A.piece n = (f.pullbackModules).obj (B.piece n)) : Prop :=
  ∀ U : X.Cᵒᵖ,
    letI := ((fSharpCommRing f).app U).hom.toAlgebra
    A.one.eval U = pullbackGeneratorSection f A B h 0 U
      ((1 : X.O.obj.obj U) ⊗ₜ[(inverseImageStructureCommRing f).obj U]
        (inverseImageGradedAlgebra f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B).one.eval U)

/-- **A pullback of sheaves of graded algebras**: a functor of sheaves of graded algebras whose
homogeneous pieces and degreewise components are the module pullbacks of the originals, and
whose multiplication and unit are induced by the original ones.

This is the full content of part (2) of Stacks 0FQX: the pullback is a construction on graded
algebras, natural in the algebra, agreeing degreewise with the pullback of sheaves of modules
of Stacks 03D6 and with the induced multiplication and unit. -/
public abbrev GradedAlgebraPullbackSpecification : Type _ :=
  { F : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) //
    ∃ h : ∀ B n, (F.obj B).piece n = (f.pullbackModules).obj (B.piece n),
      (∀ ⦃B C⦄ (g : B ⟶ C) n,
        HEq ((F.map g).app n) ((f.pullbackModules).map (g.app n))) ∧
      (∀ B, IsInducedPullbackMultiplication f (F.obj B) B (h B)) ∧
      (∀ B, IsInducedPullbackUnit f (F.obj B) B (h B)) }

/-- The degreewise module pullbacks assemble into a functor of sheaves of graded algebras, with
the induced multiplication and unit.

This is the pullback half of Stacks 0FQX. -/
@[stacks 0FQX "graded_algebra_pullback"]
public noncomputable def gradedAlgebraPullbackSpecification :
    GradedAlgebraPullbackSpecification f :=
  ⟨toposPullbackGradedAlgebraFunctor f, fun _ _ => rfl, fun _ _ _ _ => HEq.rfl,
    fun B i j U => extendScalarsGradedAlgebra_mul_unit (fSharpCommRing f) X.J
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) i j U,
    fun B U => extendScalarsGradedAlgebra_one_eval (fSharpCommRing f) X.J
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) B) U⟩

/-- A pullback of sheaves of graded algebras exists.

This is the pullback half of Stacks 0FQX; see `gradedAlgebraPullbackSpecification`. -/
@[stacks 0FQX "graded_algebra_pullback"]
public theorem nonempty_gradedAlgebraPullbackSpecification :
    Nonempty (GradedAlgebraPullbackSpecification f) :=
  ⟨gradedAlgebraPullbackSpecification f⟩

end Stacks.Sheaves.GradedAlgebraPullback
