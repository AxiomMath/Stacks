module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TautologicalSection
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections

/-!
# The fibre coordinate of a line bundle

Let `M` be an invertible module on a scheme `Y` and let `q : L(M) ⟶ Y` be the total space of
`M^{⊗ -1}`, the relative spectrum of `Sym(M^{⊗ -1}) = ⨁_{a ≥ 0} M^{⊗ -a}`. Over an affine open
`V = Spec B` of `Y` on which `M^{⊗ -1}` is trivialized by `z`, the preimage `q^{-1}V` is
`Spec B[z]`, and `z` is a `B`-linear functional on `Γ(M^{⊗ -1}, V)`, i.e. a section of `M` over
`V`. Globally the fibre coordinate is therefore a **global section of `q^*M`**.

That is the datum an equation in the fibre coordinates is written in — for instance the equation
`z₁ z₂ = q^*s` cutting out the line bundle of [Stacks, Tag 0F97] inside
`L(\mathcal{L}_1) \times_Y L(\mathcal{L}_2)`, whose two sides are sections of
`q^*\mathcal{L}_1 \otimes q^*\mathcal{L}_2` — and it is what
`Stacks.LineBundle.Situation.tautologicalSection` is one dualization short of: that section lives
in `(q^*(M^{⊗ -1}))^{⊗ -1}`, and the two steps carried out here identify that module with `q^*M`.

## Main definitions

* `Stacks.LineBundle.inverseSituation`: the line bundle `M^{⊗ -1}` on `Y` as a situation, so that
  its total space is the line bundle whose fibre coordinate is a section of `M`.
* `Stacks.LineBundle.lineBundleSpace` and `Stacks.LineBundle.lineBundleProj`: that total space
  `L(M)` and its structure morphism `q : L(M) ⟶ Y`.
* `Stacks.LineBundle.Situation.basePullbackInverse` and
  `Stacks.LineBundle.Situation.pullbackInverseIso`: the pullback `q^*(L^{⊗ -1})` of the inverse of
  the line bundle of a situation, and **the identification
  `(q^*L)^{⊗ -1} ≅ q^*(L^{⊗ -1})`** of the module the tautological section lives in with it.
* `Stacks.LineBundle.fibreCoordinate`: **the fibre coordinate of `L(M)`, as a global section of
  `q^*M`.**

## Implementation notes

The two steps are [Stacks, Tag 01CD] for the inverse and the involutivity of the inverse, and
both are available: `Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso` is
`q^*(N^{⊗ -1}) ≅ (q^*N)^{⊗ -1}`, applied at `N = L`, and
`Stacks.PullbackTensorIso.tensorPowerNegOneNegOneIso` is `M ≅ (M^{⊗ -1})^{⊗ -1}`, pulled back
along `q`. Neither is an induction on the exponent.

**Spellings.** The tensor powers of [Stacks, Tag 01CU] are written here as
`Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf
(Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y)`, which is the spelling
`pullbackTensorPowerNegOneIso` is stated at, while
`Stacks.LineBundle.Situation.pullbackInverse` is written at
`Y.sheaf.obj Y.ringCatSheaf.property` and `AlgebraicGeometry.Scheme.Modules.pullback` rather than
`Stacks.ProjBundleInverseBaseChange.pullbackFunctor`. The two spellings are definitionally equal
— `Situation.pullbackInverse_eq` records that, by `rfl` — but instance search does not cross
between them, so the three invertibility and equivalence instances a tensor power needs are
supplied explicitly below at the `presheaf` spelling, and the invertibility of `M^{⊗ -1}` that
`inverseSituation` has to carry is produced inside it rather than by instance search.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)


universe u

namespace Stacks.LineBundle

/-! ### Invertibility at the `presheaf` spelling -/

section Spelling

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

/-- An invertible module is invertible in the `Stacks` spelling of invertibility at the
`presheaf` spelling of the structure sheaf, which is the one the tensor powers of Tag 01CU and
the base change of the inverse are stated at. -/
instance isInvertible_stacks_presheaf :
    Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheaf_structureRingPresheaf Y) M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM

/-- Tensoring by an invertible module is an autoequivalence, with the coefficient sheaf used
by the integer tensor-power construction. -/
instance isEquivalence_tensorRightFunctor_presheaf :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨Y.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ Y.presheaf
        (forget₂ CommRingCat RingCat)
        (isSheaf_structureRingPresheaf Y)⟩).flip.obj M).IsEquivalence :=
  _root_.Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor Y.presheaf
    (isSheaf_structureRingPresheaf Y) M

/-- Tensoring by the pullback of an invertible module is an autoequivalence, at the `presheaf`
spelling and for the `Stacks.ProjBundleInverseBaseChange.pullbackFunctor` spelling of the
pullback. -/
instance isEquivalence_tensorRightFunctor_pullback_presheaf {X : Scheme.{u}} {f : X ⟶ Y} :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) (isSheaf_structureRingPresheaf X)⟩).flip.obj
          ((Stacks.ProjBundleInverseBaseChange.pullbackFunctor f).obj M)).IsEquivalence :=
  haveI := Stacks.ProjBundleInverseBaseChange.isInvertible_pullbackFunctor_obj f M
  _root_.Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor X.presheaf
    (isSheaf_structureRingPresheaf X) ((Stacks.ProjBundleInverseBaseChange.pullbackFunctor f).obj M)

end Spelling

/-! ### The inverse of the line bundle of a situation, pulled back -/

variable (D : Situation.{u})

/-- **The pullback `q^*(L^{⊗ -1})` of the inverse of the line bundle to the total space.** -/
def Situation.basePullbackInverse : D.totalSpace.Modules :=
  (Stacks.ProjBundleInverseBaseChange.pullbackFunctor D.totalSpaceToBase).obj
    (_root_.Stacks.SheafOfModules.TensorPower.tensorPower D.X.presheaf
      (isSheaf_structureRingPresheaf D.X) D.L (-1))

/-- The inverse `(q^*L)^{⊗ -1}` of the pullback, read at the spelling the base change of the
inverse is stated at. True by `rfl`. -/
theorem Situation.pullbackInverse_eq :
    D.pullbackInverse =
      _root_.Stacks.SheafOfModules.TensorPower.tensorPower D.totalSpace.presheaf
        (isSheaf_structureRingPresheaf D.totalSpace)
        ((Stacks.ProjBundleInverseBaseChange.pullbackFunctor D.totalSpaceToBase).obj D.L) (-1) :=
  rfl

/-- **The module the tautological section lives in is the pullback of the inverse**:
`(q^*L)^{⊗ -1} ≅ q^*(L^{⊗ -1})`. This is [Stacks, Tag 01CD] for the inverse, read backwards. -/
def Situation.pullbackInverseIso : D.pullbackInverse ≅ D.basePullbackInverse :=
  (Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso
    D.totalSpaceToBase D.L).symm

/-- **The tautological section of the total space of a line bundle, read as a global section of
the pullback `q^*(L^{⊗ -1})` of the inverse.** -/
def Situation.tautologicalSectionBase : Γ(D.basePullbackInverse, ⊤) :=
  PresheafOfModules.Hom.app D.pullbackInverseIso.hom.val (op ⊤) D.tautologicalSection

/-! ### The line bundle of an invertible module, and its fibre coordinate -/

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The inverse `M^{⊗ -1}` of an invertible module, as a situation.** Its total space is the
line bundle `L(M) = \underline{\Spec}(\Sym(M^{⊗ -1}))` of [Stacks, Tag 01M2] whose fibre
coordinate is a section of `M`. -/
def inverseSituation : Situation.{u} :=
  haveI hS : Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheaf_structureRingPresheaf Y) M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (_root_.Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf
        (isSheaf_structureRingPresheaf Y) M (-1)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (@_root_.Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _ _ Y.presheaf
        (isSheaf_structureRingPresheaf Y) _ _ M hS (-1))
  { X := Y
    S := Y
    f := CategoryTheory.CategoryStruct.id Y
    L := _root_.Stacks.SheafOfModules.TensorPower.tensorPower Y.presheaf
      (isSheaf_structureRingPresheaf Y) M (-1) }

include hM in
/-- **The line bundle `L(M)` of an invertible module `M`**: the total space of `M^{⊗ -1}`. -/
def lineBundleSpace : Scheme.{u} := (inverseSituation Y M).totalSpace

include hM in
/-- **The structure morphism `q : L(M) ⟶ Y` of the line bundle of an invertible module.** -/
def lineBundleProj : lineBundleSpace Y M ⟶ Y := (inverseSituation Y M).totalSpaceToBase

include hM in
/-- The pullback of `M` to the line bundle `L(M)`, at the spelling the involutivity of the
inverse produces. -/
def lineBundlePullback : (lineBundleSpace Y M).Modules :=
  (Stacks.ProjBundleInverseBaseChange.pullbackFunctor (lineBundleProj Y M)).obj M

include hM in
/-- **The fibre coordinate of `L(M)` lives in `q^*M`**: the pullback of the inverse of `M^{⊗ -1}`
is the pullback of `M`, by the involutivity of the inverse. -/
def lineBundlePullbackIso :
    (inverseSituation Y M).basePullbackInverse ≅ lineBundlePullback Y M :=
  haveI : Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheaf_structureRingPresheaf Y) M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM
  (Stacks.ProjBundleInverseBaseChange.pullbackFunctor (lineBundleProj Y M)).mapIso
    (Stacks.PullbackTensorIso.tensorPowerNegOneNegOneIso Y.presheaf
      (isSheaf_structureRingPresheaf Y) M).symm

include hM in
/-- **The fibre coordinate of the line bundle `L(M)` of an invertible module `M`, as a global
section of `q^*M`.** Over an affine open `V = Spec B` of `Y` on which `M^{⊗ -1}` is trivialized
by `z`, the preimage `q^{-1}V` is `Spec B[z]` and this section is the coordinate `z`. -/
def fibreCoordinate : Γ(lineBundlePullback Y M, ⊤) :=
  PresheafOfModules.Hom.app (lineBundlePullbackIso Y M).hom.val (op ⊤)
    (inverseSituation Y M).tautologicalSectionBase

end Stacks.LineBundle

end
