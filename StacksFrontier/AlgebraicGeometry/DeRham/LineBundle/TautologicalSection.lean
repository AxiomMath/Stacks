module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.Laurent
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tautological section on the total space of a line bundle

Let `L` be an invertible module on a scheme `X` and let `p : Tot(L) ⟶ X` be the total space of
`L`, the relative spectrum of `Sym(L) = ⨁_{n ≥ 0} L^{⊗ n}`. The degree-one summand of the
symmetric algebra is a morphism of `𝒪_X`-modules

`L ⟶ Sym(L) = p_* 𝒪_{Tot(L)}`,

and its adjoint under `p^* ⊣ p_*` is a morphism of `𝒪_{Tot(L)}`-modules

`p^* L ⟶ 𝒪_{Tot(L)}`,

the *tautological functional*: the fibrewise-linear function on `Tot(L)` given at a point of the
fibre over `x` by evaluation against that point. Since `p^* L` is invertible, a functional on it
is the same thing as a global section of its inverse, and the resulting global section of
`(p^* L)^{⊗ -1}` is the *tautological section*. On an affine open `U` of `X` over which `L` is
trivialized by `z`, the preimage `p^{-1}U` is `Spec Γ(X, U)[z]` and the tautological section is
the coordinate `z`.

This is the section out of which the relative spectrum of a symmetric algebra gets its
coordinates, and the datum the equations cutting out subschemes of a total space are written in:
a closed subscheme of `Tot(L)` given fibrewise by a polynomial in the fibre coordinate is the
zero scheme of a combination of powers of the tautological section with sections pulled back
from the base.

## Main definitions

* `Stacks.LineBundle.Situation.algebraSheafGen`: the degree-one inclusion `L ⟶ Sym(L)`, landing
  in the `𝒪_X`-module underlying the algebra sheaf of the line bundle.
* `Stacks.LineBundle.Situation.underlyingModuleIsoPushforward`: **the `𝒪_X`-module underlying
  the algebra sheaf of a line bundle is the pushforward `p_* 𝒪_{Tot(L)}` of the structure sheaf
  of the total space.** This is Tag 01LX(3), `A ≅ p_* 𝒪`, read on underlying modules.
* `Stacks.LineBundle.Situation.genToPushforward`: the composite `L ⟶ p_* 𝒪_{Tot(L)}`.
* `Stacks.LineBundle.Situation.tautologicalFunctional`: **the tautological functional
  `p^* L ⟶ 𝒪_{Tot(L)}`.**
* `Stacks.LineBundle.Situation.pullbackInverse`: the inverse `(p^* L)^{⊗ -1}` of the pullback of
  the line bundle to the total space, as an integer tensor power of Tag 01CU.
* `Stacks.LineBundle.Situation.pullbackDuality`: the duality
  `p^* L ⊗ (p^* L)^{⊗ -1} ≅ 𝒪_{Tot(L)}`.
* `Stacks.LineBundle.Situation.tautologicalSectionHom` and
  `Stacks.LineBundle.Situation.tautologicalSection`: **the tautological section of
  `(p^* L)^{⊗ -1}`**, as a morphism out of the structure sheaf and as a global section.

## Main results

* `Stacks.LineBundle.Situation.homEquiv_tautologicalFunctional` and
  `Stacks.LineBundle.Situation.unit_comp_map_tautologicalFunctional`: the tautological functional
  is the adjoint of the degree-one inclusion, in the two shapes the adjunction provides — as the
  image of `genToPushforward` under the inverse of the hom-equivalence, and as the factorization
  of `genToPushforward` through the unit of the adjunction.

## Implementation notes

The three identifications the functional passes through are all available in the library and
none of them needs a comparison built here.

The module underlying an algebra sheaf is
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule`, which is the algebra viewed as a module over
itself and then restricted along the structure morphism. For the pushforward algebra
`p_* 𝒪_{Tot(L)}` of a morphism of schemes that is, on each open `U`, the sections
`Γ(Tot(L), p^{-1}U)` with `Γ(X, U)` acting through the comorphism of `p` — which is exactly the
module pushforward `Scheme.Modules.pushforward p` of the unit module. The two therefore agree,
and `underlyingModuleIsoPushforward` composes
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso` with no transport.

That the structure morphism `Stacks.LineBundle.Situation.totalSpaceToBase` of the total space is
the structure morphism of the relative spectrum of the algebra sheaf, which is the shape Tag
01LX(3) is stated at, is also definitional: `Stacks.RelativeSpec.gluedSpectrum_toBase`.

The degree-one inclusion is read through
`Stacks.LineBundle.Situation.coprodIsoUnderlyingModule`, which identifies the underlying module
with `∐_{n : ℕ} Symⁿ(L)`, rather than through the per-open map
`Stacks.LineBundle.Situation.algebraSheafIncl`: the adjunction needs a morphism of sheaves of
modules, and the coproduct injection supplies one.

Passing from the functional to the section uses the coherent multiplication of Tag 01CU in the
degrees `(1, -1)` and not an abstract dual: `(p^* L)^{⊗ 1} ⊗ (p^* L)^{⊗ -1}` is the zeroth power,
which is the structure sheaf by `rfl`, so the duality isomorphism is the coherent multiplication
preceded by the comparison of the first tensor power with the module itself. The integer tensor
powers are indexed by the `Stacks` invertibility predicate, so the two invertibility instances
below transfer the one a `Situation` carries along
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry`, exactly as
`StacksFrontier/AlgebraicGeometry/DeRham/LineBundle/Laurent.lean` does for the line bundle itself;
`Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence` has to be applied by hand
because `tensorRightFunctor` is `@[implicit_reducible]` and instance search does not see through
it.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-! ### The tautological functional -/

/-- The degree-one inclusion `L ⟶ Sym(L)` of the symmetric algebra of a line bundle, landing in
the `𝒪_X`-module underlying the algebra sheaf of the line bundle. -/
def Situation.algebraSheafGen :
    D.L ⟶ Stacks.RelativeSpec.AlgebraSheaf.underlyingModule D.algebraSheaf :=
  D.symmetricAlgebraGen ≫ Sigma.ι (fun n : ℕ => D.symmetricAlgebra.piece (n : ℤ)) 1 ≫
    D.coprodIsoUnderlyingModule.hom

/-- **The `𝒪_X`-module underlying the algebra sheaf of a line bundle is the pushforward
`p_* 𝒪_{Tot(L)}` of the structure sheaf of the total space along the structure morphism.** This
is the isomorphism of sheaves of algebras `A ≅ p_* 𝒪` of Tag 01LX(3), read on underlying
modules. -/
def Situation.underlyingModuleIsoPushforward :
    Stacks.RelativeSpec.AlgebraSheaf.underlyingModule D.algebraSheaf ≅
      (Scheme.Modules.pushforward D.totalSpaceToBase).obj
        (SheafOfModules.unit D.totalSpace.ringCatSheaf) :=
  (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleIso
    (Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso D.algebraSheaf)).symm

/-- The degree-one inclusion of the symmetric algebra of a line bundle, read through Tag 01LX(3)
as a morphism `L ⟶ p_* 𝒪_{Tot(L)}` into the pushforward of the structure sheaf of the total
space. This is the datum whose adjoint is the tautological functional. -/
@[ega "IV 16.4.7" "special case"]
def Situation.genToPushforward :
    D.L ⟶ (Scheme.Modules.pushforward D.totalSpaceToBase).obj
      (SheafOfModules.unit D.totalSpace.ringCatSheaf) :=
  D.algebraSheafGen ≫ D.underlyingModuleIsoPushforward.hom

/-- **The tautological functional `p^* L ⟶ 𝒪_{Tot(L)}` on the total space of a line bundle**:
the adjoint, under the pullback--pushforward adjunction for sheaves of modules, of the degree-one
inclusion `L ⟶ Sym(L) = p_* 𝒪_{Tot(L)}` of the symmetric algebra whose relative spectrum the
total space is. -/
def Situation.tautologicalFunctional :
    (Scheme.Modules.pullback D.totalSpaceToBase).obj D.L ⟶
      SheafOfModules.unit D.totalSpace.ringCatSheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction D.totalSpaceToBase).homEquiv
    D.L (SheafOfModules.unit D.totalSpace.ringCatSheaf)).symm D.genToPushforward

/-- The tautological functional is the adjoint of the degree-one inclusion: applying the
hom-equivalence of the pullback--pushforward adjunction to it returns that inclusion. -/
theorem Situation.homEquiv_tautologicalFunctional :
    (Scheme.Modules.pullbackPushforwardAdjunction D.totalSpaceToBase).homEquiv
        D.L (SheafOfModules.unit D.totalSpace.ringCatSheaf) D.tautologicalFunctional =
      D.genToPushforward :=
  Equiv.apply_symm_apply _ _

/-- The degree-one inclusion `L ⟶ p_* 𝒪_{Tot(L)}` factors as the unit of the
pullback--pushforward adjunction followed by the pushforward of the tautological functional. -/
theorem Situation.unit_comp_map_tautologicalFunctional :
    (Scheme.Modules.pullbackPushforwardAdjunction D.totalSpaceToBase).unit.app D.L ≫
        (Scheme.Modules.pushforward D.totalSpaceToBase).map D.tautologicalFunctional =
      D.genToPushforward :=
  D.homEquiv_tautologicalFunctional

/-! ### The tautological section -/

/-- **The pullback `p^* L` of the line bundle to the total space is invertible** (Tag 0B8L), in
the spelling the integer tensor powers of Tag 01CU are indexed by. The invertibility in the
spelling a `Situation` carries is Tag 0B8L at the underlying morphism of ringed spaces, and is
not registered as an instance here: the general statement for schemes already is one, as
`Stacks.Divisors.pullback_isInvertible`. -/
instance Situation.isInvertible_stacks_pullback :
    Stacks.SheafOfModules.IsInvertible D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property
      ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L) :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
    (Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      D.totalSpaceToBase.toLRSHom.toShHom D.L D.invertible)

/-- Tensoring by `p^* L` is an autoequivalence of the sheaves of modules on the total space,
which is the datum the integer tensor powers are indexed by. -/
instance Situation.isEquivalence_tensorRightFunctor_pullback :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨D.totalSpace.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ D.totalSpace.sheaf.obj
        (forget₂ CommRingCat RingCat) D.totalSpace.ringCatSheaf.property⟩).flip.obj
          ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L)).IsEquivalence :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property
      ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      D.totalSpaceToBase.toLRSHom.toShHom D.L D.invertible
  Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence D.totalSpace.sheaf.obj
    D.totalSpace.ringCatSheaf.property ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L)

/-- **The inverse `(p^* L)^{⊗ -1}` of the pullback of the line bundle to the total space**, as an
integer tensor power of Tag 01CU. -/
def Situation.pullbackInverse : D.totalSpace.Modules :=
  Stacks.SheafOfModules.TensorPower.tensorPower D.totalSpace.sheaf.obj
    D.totalSpace.ringCatSheaf.property
    ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L) (-1)

/-- **The duality `p^* L ⊗ (p^* L)^{⊗ -1} ≅ 𝒪_{Tot(L)}`** on the total space of a line bundle:
the coherent multiplication of Tag 01CU in the degrees `(1, -1)`, preceded by the comparison of
the first tensor power of `p^* L` with `p^* L` itself. -/
def Situation.pullbackDuality :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨D.totalSpace.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (D.totalSpace.sheaf.obj) (forget₂ CommRingCat RingCat)
          (D.totalSpace.ringCatSheaf.property)⟩).obj
        (((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L))).obj (D.pullbackInverse)) ≅
      SheafOfModules.unit D.totalSpace.ringCatSheaf :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} D.totalSpace.sheaf).flip.obj
      (D.pullbackInverse))).mapIso
    (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property
      ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L)).symm ≪≫
  Stacks.SheafOfModules.TensorPower.coherentMulIso D.totalSpace.sheaf.obj
    D.totalSpace.ringCatSheaf.property
    ((Scheme.Modules.pullback D.totalSpaceToBase).obj D.L) 1 (-1)

/-- **The tautological section of `(p^* L)^{⊗ -1}` on the total space of a line bundle**, as a
morphism out of the structure sheaf: the tautological functional `p^* L ⟶ 𝒪_{Tot(L)}` tensored by
`(p^* L)^{⊗ -1}` and read through the duality of Tag 01CU. -/
def Situation.tautologicalSectionHom :
    SheafOfModules.unit D.totalSpace.ringCatSheaf ⟶ D.pullbackInverse :=
  D.pullbackDuality.inv ≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} D.totalSpace.sheaf).flip.obj
      (D.pullbackInverse))).map D.tautologicalFunctional ≫
    (Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property D.pullbackInverse).hom

/-- **The tautological section of `(p^* L)^{⊗ -1}` on the total space of a line bundle**, as a
global section. Over an affine open `U` of the base on which `L` is trivialized by `z`, the
preimage `p^{-1}U` is `Spec Γ(X, U)[z]` and this section is the coordinate `z`. -/
def Situation.tautologicalSection : Γ(D.pullbackInverse, ⊤) :=
  (SheafOfModules.unitHomEquiv D.pullbackInverse D.tautologicalSectionHom).eval (Opposite.op ⊤)

end Stacks.LineBundle

end
