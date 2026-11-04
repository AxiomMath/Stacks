module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleBraidingSelf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# The symmetric powers of an invertible sheaf of modules are its tensor powers

Let `O` be a sheaf of commutative rings on a site and let `L` be an invertible sheaf of
`O`-modules. The symmetric algebra of a sheaf of modules is the quotient of its tensor algebra
by the commutators of degree-one local sections, and for an invertible `L` there is nothing to
divide out: the two pure tensors `s ⊗ u` and `u ⊗ s` of local sections of `L` already agree in
`L ⊗_O L`, because the symmetry constraint of an invertible sheaf with itself is the identity.
This file turns that one geometric input into the identification `Symⁿ L ≅ L^{⊗ n}` in every
degree.

The route is purely through the universal properties. A tensor algebra is universal for *all*
degree-one generators, hence a fortiori for the commuting ones, so a tensor algebra whose own
generator commutes *is* a symmetric algebra; two graded algebras universal for the same
property are canonically isomorphic in every degree, and the canonical isomorphism is the
quotient map `T(L) ⟶ Sym(L)` by uniqueness. No trivializing cover appears, and no
compatibility of symmetric powers with restriction to an open is needed.

## Main definitions

* `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorSymmetricPieceIso`: the degreewise
  comparison `Tⁿ F ≅ Symⁿ F` for a package of algebras whose degree-one sections commute.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricPowerIsoTensorPower`:
  **`Symⁿ F ≅ F^{⊗ n}`** for such a package.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricGeneratorIso`: `F ≅ Sym¹ F`, the
  degree-one case, identified with the degree-one generator of the symmetric algebra.
* `Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible`: **the symmetric power of
  an invertible sheaf of modules is its tensor power.**

## Main results

* `SheafOfModules.GradedAlgebra.IsTensorAlgebra.isSymmetricAlgebra`: a tensor algebra whose
  degree-one local sections commute is a symmetric algebra.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.isIso_tensorToSymmetric_app`: the canonical
  quotient map from the tensor algebra to the symmetric algebra is then an isomorphism in every
  degree.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.pairwiseCommutes_tensorGenerator`: the
  degree-one sections of the tensor algebra commute as soon as the pure tensors of local
  sections are symmetric in the tensor square.
* `Stacks.SheafOfModules.tensorSheafificationUnit_comm_of_isInvertible`: **the pure tensors of
  two local sections of an invertible sheaf of modules agree after exchanging the factors.**
* `Stacks.SheafOfModules.pairwiseCommutes_tensorGenerator_of_isInvertible` and
  `Stacks.SheafOfModules.isIso_tensorToSymmetric_app_of_isInvertible`: the two preceding
  statements combined for an invertible sheaf of modules.

## Implementation notes

The exchange of pure tensors is read off `Stacks.SheafOfModules.tensorProductBraiding_self`
through `Stacks.SheafOfModules.tensorSections_braidingAt`, which evaluates the symmetry
constraint on the section determined by a pair of local sections. That constraint is stated for
the tensor product sheaf built over a presheaf of commutative rings together with a proof that
it is a sheaf of rings, while the package of algebras is indexed by a sheaf of commutative
rings. The two descriptions of the base agree definitionally — `CategoryTheory.Sheaf.toRingCat`
is a structure literal whose underlying presheaf is the composite with the forgetful functor,
which is what the other spelling is too — so the sheaf condition is supplied as the second
component of that literal and nothing has to be transported.

The degree-two computation uses the `tensorPieceIso_mul_left` field of the package at `n = 0`,
where the cast between the degrees `1 + 1` and `2` it carries is a cast along a reflexivity
proof and therefore disappears; the statement is given the uncast form and accepted by
definitional unfolding.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t a v u w

namespace SheafOfModules

/-- An isomorphism of sheaves of modules is injective on the sections over every object. -/
theorem injective_iso_hom_val_app {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{t}} {M N : SheafOfModules.{a} R} (e : M ≅ N) (U : Cᵒᵖ) :
    Function.Injective (ConcreteCategory.hom (e.hom.val.app U)) := by
  have h : ∀ z : M.val.obj U, ConcreteCategory.hom (e.inv.val.app U)
      (ConcreteCategory.hom (e.hom.val.app U) z) = z := fun z =>
    congrArg (fun f : M ⟶ M => ConcreteCategory.hom (f.val.app U) z) e.hom_inv_id
  exact fun x y hxy => (h x).symm.trans ((congrArg _ hxy).trans (h y))

namespace GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : SheafOfModules.{a} R} {A : GradedAlgebra.{t, a} R}

/-- **A tensor algebra whose degree-one local sections commute is a symmetric algebra.** The
tensor algebra is universal for every degree-one generator, hence in particular for the
commuting ones, and the only thing to check is that its own generator commutes. -/
theorem IsTensorAlgebra.isSymmetricAlgebra {ι : M ⟶ A.piece 1} (hA : IsTensorAlgebra A ι)
    (hc : PairwiseCommutes ι) : IsSymmetricAlgebra A ι :=
  ⟨hc, fun B κ _ => hA.2 B κ trivial⟩

end GradedAlgebra

namespace TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)

/-- **The degree-one sections of the tensor algebra commute as soon as the pure tensors of
local sections of `F` are symmetric** in the tensor square of `F`: multiplying two degree-one
generators is tensor concatenation. -/
theorem pairwiseCommutes_tensorGenerator
    (hbr : ∀ (U : Cᵒᵖ) (s u : F.val.obj U),
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val F.val)).app U (s ⊗ₜ[Osharp.obj.obj U] u) =
        ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
            Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val F.val)).app U (u ⊗ₜ[Osharp.obj.obj U] s)) :
    GradedAlgebra.PairwiseCommutes A.tensorGenerator := by
  intro U s u
  have key : ∀ x y : F.val.obj U,
      (A.tensorPieceIso 2).hom.val.app U
          ((A.tensor.mul 1 1).app U (A.tensorGenerator.val.app U x)
            ((A.tensorPieceIso 1).inv.val.app U y)) =
        ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
            Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val F.val)).app U
          (x ⊗ₜ[Osharp.obj.obj U] y) :=
    fun x y => A.tensorPieceIso_mul_left 0 U x y
  rw [← A.tensorGenerator_eq] at key
  exact injective_iso_hom_val_app (A.tensorPieceIso 2) U
    ((key s u).trans ((hbr U s u).trans (key u s).symm))

variable (hc : GradedAlgebra.PairwiseCommutes A.tensorGenerator)

include hc

/-- **The tensor algebra of a sheaf of modules whose degree-one sections commute is its
symmetric algebra**, carrying the same degree-one generator. -/
theorem isSymmetricAlgebra_tensor :
    GradedAlgebra.IsSymmetricAlgebra A.tensor A.tensorGenerator :=
  A.tensor_isTensorAlgebra.isSymmetricAlgebra hc

/-- **The degreewise comparison `Tⁿ F ≅ Symⁿ F`** between the tensor algebra and the symmetric
algebra of a sheaf of modules whose degree-one sections commute: both are universal for
commuting degree-one generators. -/
noncomputable def tensorSymmetricPieceIso (n : ℤ) : A.tensor.piece n ≅ A.symmetric.piece n :=
  (A.isSymmetricAlgebra_tensor hc).pieceIso A.symmetric_isSymmetricAlgebra n

/-- The comparison of the tensor algebra with the symmetric algebra is the canonical quotient
map: both extend the degree-one generator, and such an extension is unique. -/
theorem tensorSymmetricPieceIso_hom (n : ℤ) :
    (A.tensorSymmetricPieceIso hc n).hom = A.tensorToSymmetric.app n :=
  congrArg (fun g : GradedAlgebra.UnitalHom A.tensor A.symmetric => g.app n)
    ((A.isSymmetricAlgebra_tensor hc).isUniversal.desc_unique _ _ _
      A.tensorToSymmetric_extends).symm

/-- **The canonical quotient map from the tensor algebra to the symmetric algebra of a sheaf of
modules whose degree-one sections commute is an isomorphism in every degree.** -/
theorem isIso_tensorToSymmetric_app (n : ℤ) : IsIso (A.tensorToSymmetric.app n) := by
  rw [← A.tensorSymmetricPieceIso_hom hc n]
  infer_instance

/-- **`F ≅ Sym¹ F`** for a sheaf of modules whose degree-one tensor sections commute: the
degree-one piece of the tensor algebra is `F`, and it is carried onto the degree-one piece of the
symmetric algebra by the quotient map. -/
noncomputable def symmetricGeneratorIso : F ≅ A.symmetric.piece 1 :=
  (A.tensorPieceIso 1).symm ≪≫ A.tensorSymmetricPieceIso hc 1

/-- The identification of `F` with the degree-one symmetric power is the degree-one generator of
the symmetric algebra. -/
theorem symmetricGeneratorIso_hom :
    (A.symmetricGeneratorIso hc).hom = A.symmetricGenerator := by
  have h : (A.symmetricGeneratorIso hc).hom =
      (A.tensorPieceIso 1).inv ≫ (A.tensorSymmetricPieceIso hc 1).hom := rfl
  rw [h, A.tensorSymmetricPieceIso_hom hc, ← A.tensorGenerator_eq]
  exact A.tensorToSymmetric_extends

/-- **`Symⁿ F ≅ F^{⊗ n}`** for a sheaf of modules whose degree-one tensor sections commute: the
symmetric power is the degree-`n` piece of the tensor algebra, which is the `n`-fold tensor
power. -/
noncomputable def symmetricPowerIsoTensorPower (n : ℕ) :
    A.symmetricPower n ≅ tensorPower J F n :=
  (A.tensorSymmetricPieceIso hc (n : ℤ)).symm ≪≫ A.tensorPieceIso n

end TensorExteriorSymmetricAlgebras

end SheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (toRingCat J Osharp))
  [IsInvertible Osharp.obj (toRingCat J Osharp).property L]

/-- **The pure tensors of two local sections of an invertible sheaf of modules agree after
exchanging the factors.** The symmetry constraint of an invertible sheaf with itself is the
identity, and it exchanges the two sections determining a section of the tensor square. -/
theorem tensorSheafificationUnit_comm_of_isInvertible (U : Cᵒᵖ) (s u : L.val.obj U) :
    ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
        Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj L.val L.val)).app U
        (s ⊗ₜ[Osharp.obj.obj U] u) =
      ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
          Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj L.val L.val)).app U
        (u ⊗ₜ[Osharp.obj.obj U] s) := by
  have h := tensorSections_braidingAt Osharp.obj (toRingCat J Osharp).property U L L s u
  rw [tensorProductBraiding_self Osharp.obj (toRingCat J Osharp).property L] at h
  exact h

/-- **The degree-one sections of the tensor algebra of an invertible sheaf of modules
commute.** -/
theorem pairwiseCommutes_tensorGenerator_of_isInvertible
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J L) :
    _root_.SheafOfModules.GradedAlgebra.PairwiseCommutes A.tensorGenerator :=
  A.pairwiseCommutes_tensorGenerator (tensorSheafificationUnit_comm_of_isInvertible Osharp L)

/-- **The canonical quotient map from the tensor algebra of an invertible sheaf of modules to
its symmetric algebra is an isomorphism in every degree.** -/
theorem isIso_tensorToSymmetric_app_of_isInvertible
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J L) (n : ℤ) :
    IsIso (A.tensorToSymmetric.app n) :=
  A.isIso_tensorToSymmetric_app (pairwiseCommutes_tensorGenerator_of_isInvertible Osharp L A) n

/-- **The symmetric power of an invertible sheaf of modules is its tensor power:**
`Symⁿ L ≅ L^{⊗ n}` for every `n`, with no trivializing cover and no finiteness hypothesis. -/
noncomputable def symmetricPowerIsoTensorPowerOfIsInvertible
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J L) (n : ℕ) :
    A.symmetricPower n ≅ _root_.SheafOfModules.tensorPower J L n :=
  A.symmetricPowerIsoTensorPower (pairwiseCommutes_tensorGenerator_of_isInvertible Osharp L A) n

end Stacks.SheafOfModules

end
