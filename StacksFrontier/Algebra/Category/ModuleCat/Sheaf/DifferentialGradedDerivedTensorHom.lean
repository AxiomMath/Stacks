module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforwardHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoMultiplicative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomFunctorAdjunction

/-!
# The derived internal hom is right adjoint to the derived tensor product

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of differential graded `O`-algebras
and let `N` be a differential graded `(A, B)`-bimodule. Then the derived internal hom

`RSheafHom_B(N, -) : D(B, d) ⟶ D(A, d)`

is right adjoint to the derived tensor product

`- ⊗^L_A N : D(A, d) ⟶ D(B, d)`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyTensorFunctor` is `K(- ⊗_A N)` and
  `SheafOfModules.DifferentialGradedModule.homotopySheafHomFunctor` is
  `K(SheafHom^dg_B(N, -))`, the functors that the tensor product and the internal hom induce on
  the homotopy categories.
* `SheafOfModules.DifferentialGradedModule.homotopyTensorSheafHomAdjunction` is the resulting
  adjunction `K(- ⊗_A N) ⊣ K(SheafHom^dg_B(N, -))` of homotopy categories.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_adjunction_derivedTensor_derivedSheafHom`: the
  derived internal hom is right adjoint to the derived tensor product.

## Implementation notes

**The two underived functors are hypotheses.** Neither the tensor product nor the internal hom
of sheaves of differential graded modules can be written down by a formula over a general ringed
site, so both are used here through the carriers the development already has:
`SheafOfModules.TensorFunctorData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedTensor.lean`, a functor
`- ⊗_A N : Mod^dg(A, d) ⥤ Mod^dg(B, d)` every value of which *is* a tensor product
(`SheafOfModules.IsTensorProduct`) and whose action on morphisms is `x ⊗ y ↦ f x ⊗ y`, and
`SheafOfModules.SheafHomFunctorData` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPushforwardHom.lean`, a functor
`SheafHom^dg_B(N, -) : Mod^dg(B, d) ⥤ Mod^dg(A, d)` every value of which *is* an internal hom
(`SheafOfModules.IsSheafHom`) and whose action on morphisms is `q ↦ g ∘ q`. So the statement
below does say which two functors are being derived.

**Only the internal hom needs its homotopy extension assumed.** Descending the adjunction needs
each of the two functors to carry homotopic morphisms to homotopic morphisms. For the tensor
product that is *proved* in this development, as
`SheafOfModules.TensorFunctorData.preservesHomotopic` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackTensor.lean`, the
homotopy `h ⊗ 1` being given on local sections by `x ⊗ y ↦ h x ⊗ y`; so no hypothesis is needed
on that side. For the internal hom the development has no such construction and carries the
homotopy `q ↦ h ∘ q` as the datum
`SheafOfModules.SheafHomFunctorData.HomotopyExtension`, which is therefore a hypothesis here.

**The derived categories are the development's own.** `D(A, d)` is
`SheafOfModules.DifferentialGradedModule.derivedCategory`, the localization of the homotopy
category of right differential graded `A`-modules at the quasi-isomorphisms, with localization
functor `SheafOfModules.DifferentialGradedModule.toDerivedCategory`. So no derived category is
data and no model has to be matched up across the two sides of the adjunction. The general
theorem about deriving adjoints needs the quasi-isomorphisms to admit a left, resp. right,
calculus of fractions, exactly as the source's setting
[Stacks, Tag 0FNC](https://stacks.math.columbia.edu/tag/0FNC) does; over a ringed site that is
[Stacks, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4),
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` and
`...quasiIsomorphisms_hasRightCalculusOfFractions`, which rest on the triangulated structure of
[Stacks, Tag 0FS7] on `K(Mod(A, d))`. Both are instances, so they are found by
instance resolution and appear nowhere in the statement. This is why the base here is a ringed
site, as in the source, rather than an arbitrary sheaf of rings on a site.

**The two derived functors are parameters, as in the source.** In the source `RSheafHom_B(N, -)`
and `- ⊗^L_A N` are introduced beforehand as the right derived extension of
`SheafHom^dg_B(N, -)` and the left derived extension of `- ⊗_A N`; the lemma formalized here is
the statement that these two functors are adjoint. Accordingly both are parameters, together
with their canonical comparison maps
`β : K(SheafHom^dg_B(N, -)) ⋙ Q_A ⟶ Q_B ⋙ RSheafHom_B(N, -)` and
`α : Q_A ⋙ (- ⊗^L_A N) ⟶ K(- ⊗_A N) ⋙ Q_B`, and the hypotheses say that they *are* those
derived extensions in the sense of [Stacks, Tag 05S9]: at every object the ind-object, resp.
pro-object, computing the derived value is essentially constant with the prescribed value and
the comparison maps as its coprojections, resp. projections. No Kan extension property and no
absoluteness is assumed, because the source assumes none.

**Existence of an adjunction, not an equality of functors.** The conclusion is the existence of
an adjunction `- ⊗^L_A N ⊣ RSheafHom_B(N, -)` whose unit and counit are compatible with `α`, `β`
and the adjunction of homotopy categories, which is what pins it down; only existence is
asserted, as in the general theorem, since the uniqueness argument is a separate statement of
the source.

The two functors on the homotopy categories and the adjunction between them are built over an
arbitrary sheaf of rings on an arbitrary site; only the statement of the tag is over a ringed
site. The universes of the homogeneous components of the two algebras and of the bimodule, and
of the module components on the `A`-side and on the `B`-side, are independent; the two algebras
share a sheaf of rings and a component universe because the bimodule relates them.

## References

* [Stacks Project, Tag 0FTQ](https://stacks.math.columbia.edu/tag/0FTQ)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t a m n z v u

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### Tensor product and internal hom on the homotopy categories -/

section HomotopyTensorHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} {N : DifferentialGradedBimodule.{t, a, z} A B}

/-- The functor `K(- ⊗_A N) : K(Mod(A, d)) ⥤ K(Mod(B, d))` induced on the homotopy categories by
a tensor product functor `- ⊗_A N`. It exists because tensoring a homotopy `h` with `N` is again
a homotopy, namely `x ⊗ y ↦ h x ⊗ y`. -/
def homotopyTensorFunctor (T : TensorFunctorData.{t, a, m, z, n} A B N) :
    HomotopyCategory.{t, a, m} A ⥤ HomotopyCategory.{t, a, n} B :=
  HomotopyCategory.descend T.functor T.preservesHomotopic

/-- The functor `K(SheafHom^dg_B(N, -)) : K(Mod(B, d)) ⥤ K(Mod(A, d))` induced on the homotopy
categories by an internal hom functor with a differential graded extension. -/
def homotopySheafHomFunctor {S : SheafHomFunctorData.{t, a, m, n, z} N}
    (ES : S.HomotopyExtension) :
    HomotopyCategory.{t, a, n} B ⥤ HomotopyCategory.{t, a, m} A :=
  HomotopyCategory.descend S.functor ES.preservesHomotopic

/-- The adjunction `K(- ⊗_A N) ⊣ K(SheafHom^dg_B(N, -))` of homotopy categories, descended from
the tensor-hom adjunction `- ⊗_A N ⊣ SheafHom^dg_B(N, -)` of right differential graded modules
of [Stacks, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS). -/
noncomputable def homotopyTensorSheafHomAdjunction
    (T : TensorFunctorData.{t, a, m, z, n} A B N)
    {S : SheafHomFunctorData.{t, a, m, n, z} N} (ES : S.HomotopyExtension) :
    homotopyTensorFunctor T ⊣ homotopySheafHomFunctor ES :=
  HomotopyCategory.descendAdjunction (tensorSheafHomAdjunction T S) ES.preservesHomotopic
    T.preservesHomotopic

end HomotopyTensorHom

/-! ### The derived internal hom is right adjoint to the derived tensor product -/

section DerivedAdjunction

open CategoryTheory.Limits

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A B : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {N : DifferentialGradedBimodule.{u, a, z} A B}

/-- The derived internal hom is right adjoint to the derived tensor product.

Let `(C, O)` be a ringed site, let `A` and `B` be sheaves of differential graded `O`-algebras
and let `N` be a differential graded `(A, B)`-bimodule. Let `RSheafHom_B(N, -)` be the right
derived extension of the internal hom functor `SheafHom^dg_B(N, -)` and `- ⊗^L_A N` the left
derived extension of the tensor product functor `- ⊗_A N`, each between the derived categories
`D(A, d)` and `D(B, d)`, with their canonical comparison maps `β` and `α`. Then `- ⊗^L_A N` is
left adjoint to `RSheafHom_B(N, -)`, by an adjunction whose unit and counit are compatible with
`α`, `β` and the adjunction `K(- ⊗_A N) ⊣ K(SheafHom^dg_B(N, -))`.

The tensor product `- ⊗_A N` and the internal hom `SheafHom^dg_B(N, -)` are the two functors of
[Stacks, Tag 0FRM] and [Stacks, Tag 0FRN], given through the universal properties that define
them. -/
theorem exists_adjunction_derivedTensor_derivedSheafHom
    [HasSheafify X.J AddCommGrpCat.{m}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify X.J AddCommGrpCat.{n}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{n}]
    (T : TensorFunctorData.{u, a, m, z, n} A B N)
    {S : SheafHomFunctorData.{u, a, m, n, z} N} (ES : S.HomotopyExtension)
    (RSheafHom : derivedCategory.{u, a, n} B ⥤ derivedCategory.{u, a, m} A)
    (β : homotopySheafHomFunctor ES ⋙ toDerivedCategory.{u, a, m} A ⟶
      toDerivedCategory.{u, a, n} B ⋙ RSheafHom)
    (Ltensor : derivedCategory.{u, a, m} A ⥤ derivedCategory.{u, a, n} B)
    (α : toDerivedCategory.{u, a, m} A ⋙ Ltensor ⟶
      homotopyTensorFunctor T ⋙ toDerivedCategory.{u, a, n} B)
    (hRSheafHom : ∀ K : HomotopyCategory.{u, a, n} B,
      ∃ (c : Cocone (MorphismProperty.Under.forget (quasiIsomorphisms.{u, a, n} B) ⊤ K ⋙
            Under.forget K ⋙ homotopySheafHomFunctor ES ⋙ toDerivedCategory.{u, a, m} A))
          (_ : (homotopySheafHomFunctor ES ⋙
            toDerivedCategory.{u, a, m} A).IsRightDerivedValueAt
              (quasiIsomorphisms.{u, a, n} B) K c)
          (e : c.pt ≅ RSheafHom.obj ((toDerivedCategory.{u, a, n} B).obj K)),
        ∀ q : (quasiIsomorphisms.{u, a, n} B).Under ⊤ K,
          c.ι.app q ≫ e.hom ≫ RSheafHom.map ((toDerivedCategory.{u, a, n} B).map q.hom) =
            β.app q.right)
    (hLtensor : ∀ M : HomotopyCategory.{u, a, m} A,
      ∃ (d : Cone (MorphismProperty.Over.forget (quasiIsomorphisms.{u, a, m} A) ⊤ M ⋙
            Over.forget M ⋙ homotopyTensorFunctor T ⋙ toDerivedCategory.{u, a, n} B))
          (_ : (homotopyTensorFunctor T ⋙
            toDerivedCategory.{u, a, n} B).IsLeftDerivedValueAt
              (quasiIsomorphisms.{u, a, m} A) M d)
          (e : Ltensor.obj ((toDerivedCategory.{u, a, m} A).obj M) ≅ d.pt),
        ∀ j : (quasiIsomorphisms.{u, a, m} A).Over ⊤ M,
          Ltensor.map ((toDerivedCategory.{u, a, m} A).map j.hom) ≫ e.hom ≫ d.π.app j =
            α.app j.left) :
    ∃ adj' : Ltensor ⊣ RSheafHom,
      (∀ M : HomotopyCategory.{u, a, m} A,
          adj'.unit.app ((toDerivedCategory.{u, a, m} A).obj M) ≫ RSheafHom.map (α.app M) =
            (toDerivedCategory.{u, a, m} A).map
                ((homotopyTensorSheafHomAdjunction T ES).unit.app M) ≫
              β.app ((homotopyTensorFunctor T).obj M)) ∧
        (∀ K : HomotopyCategory.{u, a, n} B,
          Ltensor.map (β.app K) ≫ adj'.counit.app ((toDerivedCategory.{u, a, n} B).obj K) =
            α.app ((homotopySheafHomFunctor ES).obj K) ≫
              (toDerivedCategory.{u, a, n} B).map
                ((homotopyTensorSheafHomAdjunction T ES).counit.app K)) :=
  Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
    (homotopyTensorSheafHomAdjunction T ES) (quasiIsomorphisms.{u, a, n} B)
    (quasiIsomorphisms.{u, a, m} A) (toDerivedCategory.{u, a, n} B)
    (toDerivedCategory.{u, a, m} A) RSheafHom β Ltensor α hRSheafHom hLtensor

end DerivedAdjunction

end DifferentialGradedModule

end SheafOfModules

end
