module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans
public import StacksFrontier.Homology.Devissage.CompactGenerationOfDiagrams

/-!
# The dévissage along a projective compact separating family, at any chosen model

Let `A` be an abelian category, with its morphisms in a universe `v`, which is Grothendieck
abelian relative to `v`, has countable products and has those products exact, and let `S` be a
separating family, indexed by a type in `Type v`, of objects of `A` that are projective and
compact. A morphism `τ : F ⟶ G` of exact direct-sum-preserving functors out of the unbounded
derived category `D(A)` which is compatible with the shift is an isomorphism as soon as it is
invertible on each `S i` placed in degree zero.

The objects `S i` placed in degree zero compactly generate `D(A)`: they are compact by
`StacksDraft.Perfect.isCompactObject_derived_single` and they are a weak triangulated generator by
`Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating`. The dévissage is
then `StacksDraft.CompactDevissage.isIso_of_isCompactlyGenerated`.

The cell presentation of
`CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` tests compactness
at the *hom* universe of the triangulated category, so the dévissage can only be run at a model of
`D(A)` whose morphisms also live in `Type v`; at `CategoryTheory.HasDerivedCategory.standard` they
live one level higher, where `HasCoproducts` indexed by `Type v` fails. The second statement below
removes that restriction from the *conclusion*, exactly as
`StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` does for a category of
diagrams: `τ` is invertible precisely when its whiskering by the comparison equivalence with the
[Stacks, Tag 079Q] model is, and there the cell presentation does apply.

## Main results

* `StacksDraft.CompactDevissage.isIso_of_isIso_app_single` — the dévissage at a model whose
  morphisms live in `Type v`.
* `StacksDraft.CompactDevissage.isIso_of_isIso_app_single_anyModel` — the dévissage at an
  arbitrary chosen model, `CategoryTheory.HasDerivedCategory.standard` included.
* `StacksDraft.CompactDevissage.natIsoOfIsIsoAppSingle` — the resulting natural isomorphism.

## Implementation notes

This is the coefficient-free form of the two statements of
`StacksFrontier.Homology.Devissage.CompactGenerationOfDiagramsAnyModel`, which are its instances at
a category of diagrams with the free diagrams on the representables as the family; the generating
family there is supplied by `CategoryTheory.Presheaf.isSeparating`,
`Stacks.CategoryHomology.freeYonedaProjective` and
`CategoryTheory.Presheaf.isCompactObject_freeYoneda`. The other instance is a category of
presheaves of modules with the free presheaves of modules on the representables as the family,
which is what the dévissage of [Stacks, Tag 08RX] from the generators `j_{W!}𝒪_W` to an arbitrary
object of `D(Mod(𝒪))` runs on.

The three instance precautions of the diagram form are load-bearing here too: every class of the
ambient model is fixed before the second model is introduced, the additivity of the shift functors
is supplied by name because `(n : ℤ)` is an explicit binder and a local hypothesis is therefore not
an instance candidate, and the two `Pretriangulated` instances are introduced with `let` rather
than `have` because `Pretriangulated` carries data.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor CategoryTheory.ObjectProperty
open StacksDraft.DerivedModel

universe uA v u u' v' w

namespace StacksDraft.CompactDevissage

open StacksDraft.NatTransDevissage

section ProjectiveSeparators

variable {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D'] [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/-- **The dévissage along a projective compact separating family, at a locally small model.** A
morphism of exact direct-sum-preserving functors out of `D(A)` is an isomorphism as soon as it is
invertible on every member of a separating family of projective compact objects placed in degree
zero.

The hypothesis `[HasDerivedCategory.{v} A]` asks the morphisms of the model to live in the
universe `v` of the morphisms of `A`, which is what the cell presentation needs; such a model
exists by `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`. For an arbitrary model
use `isIso_of_isIso_app_single_anyModel`. -/
theorem isIso_of_isIso_app_single [HasDerivedCategory.{v} A]
    {ι : Type v} (S : ι → A) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{v} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    {F G : DerivedCategory A ⥤ D'}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ i, IsIso (τ.app ((DerivedCategory.singleFunctor A 0).obj (S i)))) : IsIso τ := by
  classical
  let : HasCoproducts.{v} A := fun J ↦ inferInstance
  have : HasCoproducts.{v} (DerivedCategory A) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory A
  exact isIso_of_isCompactlyGenerated τ
    (fun i ↦ (DerivedCategory.singleFunctor A 0).obj (S i))
    (fun i ↦ by
      have := hcomp i
      exact StacksDraft.Perfect.isCompactObject_derived_single _ 0)
    (Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating _ hS) hτ

/-- **The dévissage along a projective compact separating family at an arbitrary chosen model**,
`CategoryTheory.HasDerivedCategory.standard` included.

The cell presentation behind the dévissage cannot be run at the standard model, where the hom
universe of `D(A)` is above the universe `v` indexing its direct sums. It does not have to be:
`τ` is invertible exactly when its whiskering by the comparison equivalence with the
[Stacks, Tag 079Q] model is, and there the previous statement applies. -/
theorem isIso_of_isIso_app_single_anyModel [h : HasDerivedCategory.{w} A]
    {ι : Type v} (S : ι → A) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{v} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    {F G : DerivedCategory A ⥤ D'}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ i, IsIso (τ.app ((DerivedCategory.singleFunctor A 0).obj (S i)))) : IsIso τ := by
  -- the ambient model's classes are fixed FIRST; a second model in scope makes them
  -- unsynthesizable, and `Pretriangulated` carries data so it must be a `let`
  let t1 := @DerivedCategory.instPretriangulated A _ _ h
  let h₂ := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{v} A
  let t2 := @DerivedCategory.instPretriangulated A _ _ h₂
  let e := modelEquiv h h₂
  have hadd1 : ∀ n : ℤ, (shiftFunctor (@DerivedCategory A _ _ h) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt _ _ _ h n
  have hadd2 : ∀ n : ℤ, (shiftFunctor (@DerivedCategory A _ _ h₂) n).Additive :=
    fun n => @DerivedCategory.instAdditiveShiftFunctorInt _ _ _ h₂ n
  let hcs := StacksDraft.Perfect.derivedEquivalenceCommShift h h₂
  have hetri := StacksDraft.Perfect.derivedEquivalence_isTriangulated h h₂
  let hinvcs := e.commShiftInverse ℤ
  let hecs := e.commShift_of_functor ℤ
  have hetri2 := Equivalence.IsTriangulated.mk' e hetri
  have hinvtri : e.inverse.IsTriangulated := inferInstance
  have hτ' : IsIso (Functor.whiskerLeft e.inverse τ) :=
    isIso_of_isIso_app_single S hcomp hS _ fun i ↦ isIso_app_of_iso τ
      ((modelInverseCompQIso h h₂).app ((CochainComplex.singleFunctor A 0).obj (S i))).symm (hτ i)
  have hall : ∀ X, IsIso (τ.app X) := by
    intro X
    have h1 : IsIso ((Functor.whiskerLeft e.inverse τ).app (e.functor.obj X)) := inferInstance
    exact isIso_app_of_iso τ (e.unitIso.app X).symm h1
  exact NatIso.isIso_of_isIso_app τ

/-- The natural isomorphism produced by the dévissage along a projective compact separating family
at an arbitrary chosen model. -/
def natIsoOfIsIsoAppSingle [h : HasDerivedCategory.{w} A]
    {ι : Type v} (S : ι → A) [∀ i, Projective (S i)]
    (hcomp : ∀ i, IsCompactObject.{v} (S i))
    (hS : (ObjectProperty.ofObj S).IsSeparating)
    {F G : DerivedCategory A ⥤ D'}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) G]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
    (hτ : ∀ i, IsIso (τ.app ((DerivedCategory.singleFunctor A 0).obj (S i)))) : F ≅ G :=
  have := isIso_of_isIso_app_single_anyModel S hcomp hS τ hτ
  asIso τ

end ProjectiveSeparators

end StacksDraft.CompactDevissage

end
