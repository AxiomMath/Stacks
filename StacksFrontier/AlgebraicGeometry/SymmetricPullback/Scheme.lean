module

public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Iso
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `f^*Sym(F) = Sym(f^*F)` for a morphism of schemes

`Stacks.RingedSpace.pullbackSymmetricPieceIso` proves Stacks 01CI for the symmetric algebra for
an arbitrary morphism of **ringed spaces**, at symmetric algebras given by their universal
property. The projective-bundle development works instead with a morphism of **schemes** and
with one particular symmetric algebra, `SheafOfModules.sheafifiedSymmetricAlgebra`, because
that is the algebra of `Stacks.RelativeProj.symmetricSituationOfQuasicoherent`. This file is
the instantiation that joins the two.

## Why it is only an instantiation

Three identifications hold by `rfl` at default transparency, and they are what makes this file
short:

* `AlgebraicGeometry.Scheme.Modules X = SheafOfModules (Stacks.RingedSpace.structureRingSheaf
  X.toRingedSpace)`;
* `X.ringCatSheaf = Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`;
* `AlgebraicGeometry.Scheme.Modules.pullback g = Stacks.RingedSpace.pullbackFunctor
  g.toLRSHom.toShHom`.

So a morphism of schemes *is* a morphism of ringed spaces as far as sheaves of modules and their
pullback are concerned, and `SheafOfModules.sheafifiedSymmetricAlgebra` *is* a symmetric algebra
by `SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra`. Every result below is the
corresponding result of `SymmetricPullback.Iso` applied to those two facts.

## Main definitions

* `Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIso`: `g^*(Symⁿ F) ≅ Symⁿ(g^*F)` for a
  morphism of schemes `g`, at `SheafOfModules.sheafifiedSymmetricAlgebra`.
* `Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso`: the same, presented for a module
  `E'` on the source together with an isomorphism `E' ≅ g^*E`. This is the shape in which a
  base-change hypothesis is usually given.
* `Stacks.RelativeProj.symmetricSituationPullbackPieceIso`: the same again, read on the graded
  algebra of `Stacks.RelativeProj.symmetricSituationOfQuasicoherent`, which is the algebra whose
  relative `Proj` is the projective bundle of Tag 01OB.

## Main results

* `Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIso_generator`,
  `pullbackSheafifiedPieceIso_mul`, `pullbackSheafifiedPieceIso_one`: the isomorphism carries the
  pulled-back degree-one generator to the generator, and is multiplicative and unital.
* `Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator`: the generator
  compatibility in the presence of an isomorphism `E' ≅ g^*E`, where the comparison of the
  degree-one pieces acquires `hE.inv`.

## Implementation notes

**The binders of `pullbackSheafifiedPieceIso_mul` name the pullback as
`Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom`, not as
`AlgebraicGeometry.Scheme.Modules.pullback g`.** The two are `rfl`-equal, but with the scheme
spelling in the types of the two homogeneous sections the statement does not elaborate inside
the default heartbeat budget: unifying them has to unfold the scheme-level pullback through its
chain of abbreviations once for each of the two arguments and once more under the degree
transport `i + j`. Naming the ringed-space spelling — the one the lemma being applied uses —
removes the unification entirely. The other statements are unaffected, since they mention a
single piece and no degree transport.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite SheafOfModules
universe u

namespace Stacks.SymmetricAlgebra

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules)

/-- **The pullback of the symmetric powers of a module on a scheme** (Tag 01CI). For a morphism of
schemes `g : X ⟶ Y` and a sheaf of `𝒪_Y`-modules `F`, the pullback of the degree-`n` symmetric
power of `F` is the degree-`n` symmetric power of `g^*F`, both taken in
`SheafOfModules.sheafifiedSymmetricAlgebra`. -/
noncomputable def pullbackSheafifiedPieceIso (n : ℤ) :
    (Scheme.Modules.pullback g).obj
        ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F).piece n) ≅
      (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
        ((Scheme.Modules.pullback g).obj F)).piece n :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso g.toLRSHom.toShHom
    (isSymmetricAlgebra_sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F)
    (isSymmetricAlgebra_sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
      ((Scheme.Modules.pullback g).obj F)) n

/-- The isomorphism carries the pulled-back degree-one generator of `Sym(F)` to the degree-one
generator of `Sym(g^*F)`. -/
theorem pullbackSheafifiedPieceIso_generator :
    Stacks.RingedSpace.pullbackGen g.toLRSHom.toShHom
        (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F)
        (sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥Y) F) ≫
      (pullbackSheafifiedPieceIso g F 1).hom =
      sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X)
        ((Scheme.Modules.pullback g).obj F) :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso_generator _ _ _

/-- The isomorphism is multiplicative on homogeneous local sections. -/
theorem pullbackSheafifiedPieceIso_mul (i j : ℤ) (U : (Opens ↥X)ᵒᵖ)
    (x : ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj
      ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F).piece i)).val.obj U)
    (y : ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj
      ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F).piece j)).val.obj U) :
    (pullbackSheafifiedPieceIso g F (i + j)).hom.val.app U
        (((Stacks.RingedSpace.pullbackGradedAlgebra g.toLRSHom.toShHom
          (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F)).mul i j).app U x y) =
      ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
          ((Scheme.Modules.pullback g).obj F)).mul i j).app U
        ((pullbackSheafifiedPieceIso g F i).hom.val.app U x)
        ((pullbackSheafifiedPieceIso g F j).hom.val.app U y) :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso_mul _ _ _ i j U x y

/-- The isomorphism carries the unit of the pulled-back algebra to the unit. -/
theorem pullbackSheafifiedPieceIso_one (U : (Opens ↥X)ᵒᵖ) :
    (pullbackSheafifiedPieceIso g F 0).hom.val.app U
        ((Stacks.RingedSpace.pullbackGradedAlgebra g.toLRSHom.toShHom
          (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) F)).one.eval U) =
      (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
        ((Scheme.Modules.pullback g).obj F)).one.eval U :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso_one _ _ _ U

/-- **The pullback of the symmetric powers, given an isomorphism `E' ≅ g^*E`.** The symmetric
powers of a module on the source identified with a pullback are the pullbacks of the symmetric
powers. The universal property transports along `hE` by
`SheafOfModules.GradedAlgebra.isSymmetricAlgebra_ofIso`, so `Sym(E')` is a symmetric algebra of
`g^*E` as well as of `E'`, and the isomorphism is the one between the two symmetric algebras of
`g^*E`. -/
noncomputable def pullbackSheafifiedPieceIsoOfIso (E : Y.Modules) (E' : X.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) (n : ℤ) :
    (Scheme.Modules.pullback g).obj
        ((sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) E).piece n) ≅
      (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) E').piece n :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso g.toLRSHom.toShHom
    (isSymmetricAlgebra_sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) E)
    (GradedAlgebra.isSymmetricAlgebra_ofIso hE.symm
      (isSymmetricAlgebra_sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) E')) n

/-- The generator compatibility of `pullbackSheafifiedPieceIsoOfIso`: in degree one the
comparison is the given isomorphism `hE` followed by the degree-one generator of `Sym(E')`. -/
theorem pullbackSheafifiedPieceIsoOfIso_generator (E : Y.Modules) (E' : X.Modules)
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) :
    Stacks.RingedSpace.pullbackGen g.toLRSHom.toShHom
        (sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥Y) E)
        (sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥Y) E) ≫
      (pullbackSheafifiedPieceIsoOfIso g E E' hE 1).hom =
      hE.inv ≫ sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X) E' :=
  Stacks.RingedSpace.pullbackSymmetricPieceIso_generator _ _ _

end Stacks.SymmetricAlgebra

namespace Stacks.RelativeProj

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The graded algebra of the projective-bundle situation base-changes.** The homogeneous
pieces of the algebra of `Stacks.RelativeProj.symmetricSituationOfQuasicoherent` on the source
are the pullbacks of those on the target.

The statement is literally `Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso`: the
`algebra` field of `Stacks.RelativeProj.symmetricSituation` is
`SheafOfModules.sheafifiedSymmetricAlgebra` by `rfl`
(`Stacks.RelativeProj.symmetricSituation_algebra`). -/
@[ega "II 4.1.3" "(E)"]
noncomputable def symmetricSituationPullbackPieceIso (E : Y.Modules) [E.IsQuasicoherent]
    (E' : X.Modules) [E'.IsQuasicoherent]
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) (n : ℤ) :
    (Scheme.Modules.pullback g).obj
        ((symmetricSituationOfQuasicoherent Y E).algebra.piece n) ≅
      (symmetricSituationOfQuasicoherent X E').algebra.piece n :=
  Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso g E E' hE n

end Stacks.RelativeProj

end
