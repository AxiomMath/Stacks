module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map for two module sheaves

Let `a : X ⟶ S` and `b : Y ⟶ S` be two spaces over a base `S`, let `p : W ⟶ X` and `q : W ⟶ Y`
be two morphisms and let `f : W ⟶ S` satisfy `p ≫ a = f = q ≫ b`; for instance `W = X ×_S Y`
with its two projections. Set `A = Γ(S, 𝒪_S)`. For an `𝒪_X`-module `ℱ` and an `𝒪_Y`-module `𝒢`
there is a canonical map

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(W, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`

in `D(A)`, where the tensor product on the left is the derived tensor product over `A` and the
one on the right is the ordinary tensor product of the two pulled-back module sheaves. It is the
global Künneth map `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap` at `K = ℱ[0]` and
`M = 𝒢[0]`, followed by derived global sections of the canonical comparison

`Lp^*ℱ[0] ⊗^𝐋_{𝒪_W} Lq^*𝒢[0] ⟶ (p^*ℱ ⊗_{𝒪_W} q^*𝒢)[0]`.

## Main definitions

* `Stacks.Cohomology.GlobalKunneth.singleD`: a module sheaf regarded as a complex in degree
  zero, as an object of the derived category.
* `Stacks.Cohomology.GlobalKunneth.pullbackSingleComparison`: the canonical comparison
  `Lp^*ℱ[0] ⟶ (p^*ℱ)[0]` from derived to ordinary pullback on a module sheaf.
* `Stacks.Cohomology.GlobalKunneth.externalTensorComparison`: the canonical comparison
  `Lp^*ℱ[0] ⊗^𝐋 Lq^*𝒢[0] ⟶ (p^*ℱ ⊗ q^*𝒢)[0]`.
* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves`: the global Künneth map for two module
  sheaves.
* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesScheme`: the same map for a cartesian
  square of schemes, with target the external tensor product
  `AlgebraicGeometry.externalTensorProduct` on the fibre product `X ×_S Y`.

## Main results

* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves_eq`: the map is the global Künneth map
  at the two sheaves placed in degree zero, followed by derived global sections of
  `externalTensorComparison`.
* `Stacks.Cohomology.GlobalKunneth.externalTensorComparison_eq`: the comparison is the
  composite of the two derived-to-ordinary pullback comparisons, the derived-to-ordinary tensor
  comparison `toTensor`, and the degree-zero identification of the total tensor complex of two
  complexes concentrated in degree zero.
* `Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheaves_naturality_derived`: the first factor of
  the map is natural in the two derived complexes `ℱ[0]` and `𝒢[0]`.

## Implementation notes

The derived-to-ordinary pullback comparison is the counit
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` of the left
derived functor `Lp^*`, transported along `DerivedCategory.quotientCompQhIso` and
`HomologicalComplex.singleMapHomologicalComplex`; the identification
`Tot(ℱ[0] ⊗ 𝒢[0]) ≅ (ℱ ⊗ 𝒢)[0]` is `HomologicalComplex.mapBifunctorSingleIso`.

## References

* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

/-! ### Module sheaves in degree zero -/

/-- A module sheaf on a space, regarded as a cochain complex concentrated in degree zero. -/
abbrev singleC {Z : RingedSpace.{u, u}} (F : Modules Z.sheaf) :
    CochainComplex (Modules Z.sheaf) ℤ :=
  (CochainComplex.singleFunctor (Modules Z.sheaf) 0).obj F

/-- A module sheaf on a space, regarded as an object of the derived category by placing it in
degree zero. -/
abbrev singleD {Z : RingedSpace.{u, u}} (F : Modules Z.sheaf) :
    DerivedCategory (Modules Z.sheaf) :=
  DerivedCategory.Q.obj (singleC F)

/-- The ordinary tensor product of two module sheaves on a space. -/
abbrev sheafTensorObj {Z : RingedSpace.{u, u}} (F G : Modules Z.sheaf) : Modules Z.sheaf :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj F).obj G

/-! ### The canonical derived-to-ordinary comparisons -/

section Comparisons

variable {X Y W : RingedSpace.{u, u}} (p : W ⟶ X) (q : W ⟶ Y)

/-- The derived-to-ordinary pullback comparison `Lp^*ℱ[0] ⟶ (p^*ℱ)[0]` on a module sheaf: the
counit of the left derived functor `Lp^*` at the complex `ℱ[0]`, read through the identification
of the degreewise pullback of `ℱ[0]` with `(p^*ℱ)[0]`. -/
def pullbackSingleComparison (F : Modules X.sheaf) :
    (derivedPullback p).obj (singleD F) ⟶ singleD ((modulePullback p).obj F) :=
  (derivedPullback p).map
      ((DerivedCategory.quotientCompQhIso (Modules X.sheaf)).inv.app (singleC F)) ≫
    (derivedPullbackComparison p).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (singleC F)) ≫
    (DerivedCategory.quotientCompQhIso (Modules W.sheaf)).hom.app
      (((modulePullback p).mapHomologicalComplex (ComplexShape.up ℤ)).obj (singleC F)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback p)
        (ComplexShape.up ℤ) 0).app F).hom

/-- The comparison `Lp^*ℱ[0] ⊗^𝐋_{𝒪_W} Lq^*𝒢[0] ⟶ (p^*ℱ ⊗_{𝒪_W} q^*𝒢)[0]`: the two
derived-to-ordinary pullback comparisons, followed by the canonical map from the derived tensor
product to the total tensor complex and the degree-zero identification of that total complex
with the ordinary tensor product placed in degree zero. -/
def externalTensorComparison (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    ((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj (singleD F))).obj
        ((derivedPullback q).obj (singleD G)) ⟶
      singleD (sheafTensorObj ((modulePullback p).obj F) ((modulePullback q).obj G)) :=
  ((derivedTensorProductFunctor W.sheaf).map (pullbackSingleComparison p F)).app
      ((derivedPullback q).obj (singleD G)) ≫
    ((derivedTensorProductFunctor W.sheaf).obj (singleD ((modulePullback p).obj F))).map
      (pullbackSingleComparison q G) ≫
    (canonicalDerivedTensorProduct W.sheaf).toTensor
      (singleC ((modulePullback p).obj F)) (singleC ((modulePullback q).obj G)) ≫
    DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
        ((modulePullback p).obj F) ((modulePullback q).obj G)).hom

/-- The comparison is the composite of the two derived-to-ordinary pullback comparisons, the
derived-to-ordinary tensor comparison and the degree-zero identification of the total tensor
complex of two complexes concentrated in degree zero. -/
theorem externalTensorComparison_eq (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    externalTensorComparison p q F G =
      ((derivedTensorProductFunctor W.sheaf).map (pullbackSingleComparison p F)).app
          ((derivedPullback q).obj (singleD G)) ≫
        ((derivedTensorProductFunctor W.sheaf).obj (singleD ((modulePullback p).obj F))).map
          (pullbackSingleComparison q G) ≫
        (canonicalDerivedTensorProduct W.sheaf).toTensor
          (singleC ((modulePullback p).obj F)) (singleC ((modulePullback q).obj G)) ≫
        DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)
            ((modulePullback p).obj F) ((modulePullback q).obj G)).hom :=
  rfl

end Comparisons

/-! ### The global Künneth map for two module sheaves -/

section

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- The global Künneth map for two module sheaves

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(W, p^*ℱ ⊗_{𝒪_W} q^*𝒢)`

in `D(A)` for `A = Γ(S, 𝒪_S)` and a global cup product `κ` over `A`, where `p ≫ a = f = q ≫ b`:
the derived Künneth map at the two sheaves placed in degree zero, followed by derived global
sections of `externalTensorComparison`. -/
def kunnethMapOfSheaves (κ : GlobalCupProduct S) (F : Modules X.sheaf) (G : Modules Y.sheaf) :
    ((tensorBase S).obj ((sectionsOverBase a).obj (singleD F))).obj
        ((sectionsOverBase b).obj (singleD G)) ⟶
      (sectionsOverBase f).obj
        (singleD (sheafTensorObj ((modulePullback p).obj F) ((modulePullback q).obj G))) :=
  kunnethGlobalMap a b p q f hp hq κ (singleD F) (singleD G) ≫
    (sectionsOverBase f).map (externalTensorComparison p q F G)

/-- The Künneth map for two module sheaves is the derived Künneth map at the two sheaves placed
in degree zero, followed by derived global sections of the canonical comparison from the derived
tensor product of the derived pullbacks to the ordinary tensor product of the ordinary pullbacks.
-/
theorem kunnethMapOfSheaves_eq (κ : GlobalCupProduct S) (F : Modules X.sheaf)
    (G : Modules Y.sheaf) :
    kunnethMapOfSheaves a b p q f hp hq κ F G =
      kunnethGlobalMap a b p q f hp hq κ (singleD F) (singleD G) ≫
        (sectionsOverBase f).map (externalTensorComparison p q F G) :=
  rfl

/-- The first factor of the Künneth map for two module sheaves, the derived Künneth map, is
natural in the two derived complexes `ℱ[0]` and `𝒢[0]`. -/
theorem kunnethMapOfSheaves_naturality_derived (κ : GlobalCupProduct S)
    {F F' : Modules X.sheaf} {G G' : Modules Y.sheaf} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((sectionsOverBase a).map (DerivedCategory.Q.map
              ((CochainComplex.singleFunctor (Modules X.sheaf) 0).map φ)) ×ₘ
            (sectionsOverBase b).map (DerivedCategory.Q.map
              ((CochainComplex.singleFunctor (Modules Y.sheaf) 0).map ψ))) ≫
        kunnethGlobalMap a b p q f hp hq κ (singleD F') (singleD G') =
      kunnethGlobalMap a b p q f hp hq κ (singleD F) (singleD G) ≫
        (sectionsOverBase f).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullback p).map (DerivedCategory.Q.map
                ((CochainComplex.singleFunctor (Modules X.sheaf) 0).map φ)) ×ₘ
              (derivedPullback q).map (DerivedCategory.Q.map
                ((CochainComplex.singleFunctor (Modules Y.sheaf) 0).map ψ)))) :=
  kunnethGlobalMap_naturality a b p q f hp hq κ _ _

end

/-! ### The Künneth map for two module sheaves on a cartesian square of schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The global Künneth map at the fibre product of two schemes: for schemes `a : X ⟶ S` and
`b : Y ⟶ S`, `A = Γ(S, 𝒪_S)`, a global cup product `κ` over `A`, an `𝒪_X`-module `ℱ` and an
`𝒪_Y`-module `𝒢`, the map

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, p^*ℱ ⊗_{𝒪_{X ×_S Y}} q^*𝒢)`

in `D(A)`, where `p` and `q` are the two projections of `X ×_S Y` and the target is the external
tensor product `AlgebraicGeometry.externalTensorProduct` placed in degree zero. -/
def kunnethMapOfSheavesScheme (κ : GlobalCupProduct S.toRingedSpace)
    (F : X.Modules) (G : Y.Modules) :
    ((tensorBase S.toRingedSpace).obj
          ((sectionsOverBase a.toLRSHom.toShHom).obj (singleD F))).obj
        ((sectionsOverBase b.toLRSHom.toShHom).obj (singleD G)) ⟶
      (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
        (singleD (externalTensorProduct a b F G)) :=
  kunnethMapOfSheaves a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl (toShHom_pullback_condition a b) κ F G

/-- The Künneth map at the fibre product of two schemes is the derived Künneth map at the two
sheaves placed in degree zero, followed by derived global sections of the canonical comparison
from the derived tensor product of the derived pullbacks to the external tensor product. -/
theorem kunnethMapOfSheavesScheme_eq (κ : GlobalCupProduct S.toRingedSpace)
    (F : X.Modules) (G : Y.Modules) :
    kunnethMapOfSheavesScheme a b κ F G =
      kunnethGlobalMapScheme a b κ (singleD F) (singleD G) ≫
        (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).map
          (externalTensorComparison (pullback.fst a b).toLRSHom.toShHom
            (pullback.snd a b).toLRSHom.toShHom F G) :=
  rfl

end Schemes

end Stacks.Cohomology.GlobalKunneth

end
