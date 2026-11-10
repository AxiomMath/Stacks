module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraUniversalTransport
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulSelfExtAlgebraDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyModelIso

/-!
# The self-Ext algebra of a Koszul-regular quotient, over the quotient, on a K-injective model

`Stacks.RegularSequence.KoszulChainData.extSelfAlgebra` is the self-Ext algebra of a
Koszul-regular quotient as a sheaf of graded `O_X`-algebras: the composition-product algebra of
the Koszul cochain complex, descended along `O♯ ⟶ O♯/𝓘 = O_X`. The model comparison
`Stacks.SheafOfModules.extSelfComparisonIsoOfStrictlyPerfect` identifies that composition-product
algebra with `Stacks.SheafOfModules.extSelfGradedAlgebra`, whose pieces are the Ext sheaves
themselves and whose multiplication is read off a K-injective representative — but it does so
**over `O♯`**, before the descent of scalars.

This file pushes that comparison through the descent. The pieces of
`extSelfGradedAlgebra Rc I A ε` are annihilated by the sheaf of ideals, because the comparison
identifies them degreewise with the pieces of the Koszul algebra, which are; so the K-injective
model descends too, and the descended comparison is an isomorphism of sheaves of graded
`O_X`-algebras. The whole exterior-algebra conclusion then transfers: the comparison map

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X)) ⟶ Ext^i_{O♯}(O_X, O_X)`

of the **K-injective** model is an isomorphism in every degree whenever that of the Koszul model
is.

## Main definitions

* `Stacks.RegularSequence.KoszulChainData.extSelfAlgebraOfKInjective`: the self-Ext algebra of
  the quotient over the quotient, with the multiplication of a K-injective model.
* `Stacks.RegularSequence.KoszulChainData.extSelfAlgebraModelIso`: the descended model
  comparison, an isomorphism of sheaves of graded `O_X`-algebras.
* `Stacks.RegularSequence.KoszulChainData.extComparisonOfKInjective`: the comparison map of
  Stacks 0BQY for the K-injective model.

## Main statements

* `Stacks.RegularSequence.KoszulChainData.smul_extSelfGradedAlgebra_piece_eq_zero`: the pieces of
  the K-injective model are annihilated by the sheaf of ideals.
* `Stacks.RegularSequence.KoszulChainData.isExteriorAlgebra_extSelfAlgebraOfKInjective` and
  `Stacks.RegularSequence.KoszulChainData.isIso_extComparisonOfKInjective`: the exterior-algebra
  property and the invertibility of the comparison transfer from the Koszul model to the
  K-injective one.

## Implementation notes

**The descent of the comparison is the general functoriality, not a computation.**
`SheafOfModules.GradedAlgebra.UnitalHom.descend` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDescentHom` descends any unital
homomorphism between two annihilated sheaves of graded algebras, by fullness of restriction of
scalars along a locally surjective morphism of sheaves of rings; nothing about Ext sheaves enters.
So the only input special to this situation is the annihilation of the pieces of the K-injective
model, and that is transported along the degreewise isomorphism by
`Stacks.RegularSequence.KoszulChainData.smul_eq_zero_of_iso`.

**The invertibility of the descended comparison is supplied positionally.** The ring sheaf of the
graded algebras compared by `Stacks.SheafOfModules.extSelfComparison` and the source of
`Stacks.Sites.quotientRingHom` along which they are descended are the same sheaf of rings by
`rfl`, but each is reached through a plain definition, so instance search does not identify them:
the `[IsIso (g.app n)]` argument of
`SheafOfModules.GradedAlgebra.UnitalHom.isIso_descend_app` is therefore handed
`Stacks.SheafOfModules.isIso_extSelfComparison_app` by name rather than left to be synthesised.
The statement is unchanged.

**Changing the generator costs an application of `comp_iso`.** The exterior-algebra property is
stated for the identity of the degree-one piece, so transporting it along an isomorphism of
algebras changes not only the algebra but the module the generator comes out of.
`SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso` moves the universal property with the
generator `𝟙 ≫ ψ.app 1`, which is a generator out of the *old* degree-one piece, and
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso` precomposes with its inverse to land
back on the identity of the new one.

**What this does and does not say about [Stacks, Tag 0BQY].** It closes the descent of scalars
that the implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyModelIso` record as
missing: the comparison of the two models is now available over the quotient, where the tag's
comparison map lives, and the conclusion is available for the model whose pieces are the Ext
sheaves with the composition product of a K-injective representative rather than of the Koszul
complex. It does **not** identify that multiplication with
`Stacks.SheafOfModules.sheafExtProduct`, the derived composition product, which is the remaining
half of the first gap the 0BQY caveat names; and it does not glue the local statements. No
declaration here carries the 0BQY attribute.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex Stacks.ChainComplex

universe u

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.Sites Stacks.SheafOfModules Stacks.RegularSequence

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (Opens.grothendieckTopology ↥X) CommRingCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ) [QuasiIso K.augmentation]
  (I : CochainComplex (StructureSheafModules Rc) ℤ) [I.IsKInjective]
  (κ : cochain Rc K ⟶ I) [QuasiIso κ]
  (hbdd : {i : ℤ | ¬ IsZero ((cochain Rc K).X i)}.Finite)
  (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) ((cochain Rc K).X i))
  (D : DerivedCategory (StructureSheafModules Rc)) (ε : DerivedCategory.Q.obj I ≅ D)

include K κ hbdd hterm in
/-- **Every piece of the K-injective model of the self-Ext algebra is annihilated by the sheaf
of ideals.** The model comparison identifies it degreewise with the corresponding piece of the
Koszul model, where the annihilation is
`Stacks.RegularSequence.KoszulChainData.smul_homologyPiece_eq_zero`. -/
theorem smul_extSelfGradedAlgebra_piece_eq_zero (n : ℤ) (Y : (Opens ↥X)ᵒᵖ)
    (a : (structureSheaf Rc).obj.obj Y)
    (ha : a ∈ RingHom.ker ((quotientRingHom (quotientIdeal Rc φ)).hom.app Y).hom)
    (m : ((extSelfGradedAlgebra Rc I D ε).piece n).val.obj Y) : a • m = 0 :=
  let := isIso_homologyMap_targetComparison Rc (cochain Rc K) I κ hbdd hterm
  have := isIso_extSelfComparison_app Rc (cochain Rc K) I κ D ε n
  smul_eq_zero_of_iso Rc (asIso ((extSelfComparison Rc (cochain Rc K) I κ D ε).app n))
    (smul_homologyPiece_eq_zero Rc K n Y a ha) m

/-- **The self-Ext algebra of a Koszul-regular quotient over the quotient, with the
multiplication of a K-injective model.** Its pieces are the Ext sheaves
`Ext^n_{O♯}(O_X, O_X)` read as `O_X`-modules, and its multiplication is the composition product
of `SheafHom^•(I, I)` for a K-injective representative `I` of the quotient. -/
def extSelfAlgebraOfKInjective :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  SheafOfModules.GradedAlgebra.descend (quotientRingHom (quotientIdeal Rc φ))
    (extSelfGradedAlgebra Rc I D ε)
    (smul_extSelfGradedAlgebra_piece_eq_zero Rc K I κ hbdd hterm D ε)

/-- **The two models of the self-Ext algebra agree over the quotient.** The model comparison
`Stacks.SheafOfModules.extSelfComparison`, which is an isomorphism of sheaves of graded
`O♯`-algebras, descended along `O♯ ⟶ O_X` by
`SheafOfModules.GradedAlgebra.UnitalHom.descend`. -/
def extSelfAlgebraModelComparison :
    SheafOfModules.GradedAlgebra.UnitalHom
      (extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε) (extSelfAlgebra Rc K) :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  letI := isIso_homologyMap_targetComparison Rc (cochain Rc K) I κ hbdd hterm
  (extSelfComparison Rc (cochain Rc K) I κ D ε).descend
    (quotientRingHom (quotientIdeal Rc φ))
    (smul_extSelfGradedAlgebra_piece_eq_zero Rc K I κ hbdd hterm D ε)
    (smul_homologyPiece_eq_zero Rc K)

/-- Each graded piece of the model comparison `extSelfAlgebraModelComparison` is an isomorphism
of `O_X`-modules. -/
instance isIso_extSelfAlgebraModelComparison_app (n : ℤ) :
    IsIso ((extSelfAlgebraModelComparison Rc K I κ hbdd hterm D ε).app n) :=
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      (quotientRingHom (quotientIdeal Rc φ)).hom :=
    isLocallySurjective_quotientRingHom_idealOfHom φ
  letI := isIso_homologyMap_targetComparison Rc (cochain Rc K) I κ hbdd hterm
  @SheafOfModules.GradedAlgebra.UnitalHom.isIso_descend_app _ _ _ _ _
    (quotientRingHom (quotientIdeal Rc φ)) inferInstance _ _
    (smul_extSelfGradedAlgebra_piece_eq_zero Rc K I κ hbdd hterm D ε)
    (smul_homologyPiece_eq_zero Rc K) (extSelfComparison Rc (cochain Rc K) I κ D ε) n
    (isIso_extSelfComparison_app Rc (cochain Rc K) I κ D ε n)

/-- **The two models of the self-Ext algebra are isomorphic as sheaves of graded
`O_X`-algebras.** This is the descent of scalars that
`Stacks.SheafOfModules.extSelfComparisonIsoOfStrictlyPerfect` left over `O♯`. -/
def extSelfAlgebraModelIso :
    extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε ≅ extSelfAlgebra Rc K where
  hom := (extSelfAlgebraModelComparison Rc K I κ hbdd hterm D ε).toHom
  inv := (extSelfAlgebraModelComparison Rc K I κ hbdd hterm D ε).inverse.toHom
  hom_inv_id := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    simp
  inv_hom_id := by
    refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
    simp

/-- **The K-injective model is an exterior algebra on its degree-one piece as soon as the Koszul
model is.** The universal property moves along the inverse of the descended model comparison by
`SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`, which lands on the generator
`ψ.app 1` out of the Koszul model's degree-one piece; precomposing with its inverse by
`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso` returns the identity generator. -/
theorem isExteriorAlgebra_extSelfAlgebraOfKInjective
    (h : SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
      (𝟙 ((extSelfAlgebra Rc K).piece 1))) :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra
      (extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε)
      (𝟙 ((extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε).piece 1)) := by
  have hc : ∀ n : ℤ, IsIso ((extSelfAlgebraModelComparison Rc K I κ hbdd hterm D ε).app n) :=
    fun n => inferInstance
  set ψ := (extSelfAlgebraModelComparison Rc K I κ hbdd hterm D ε).inverse with hψ
  have hψiso : ∀ n : ℤ, IsIso (ψ.app n) := fun n => by
    rw [hψ, SheafOfModules.GradedAlgebra.UnitalHom.inverse_app]
    infer_instance
  have hgen0 : SheafOfModules.GradedAlgebra.SquareZero
      (A := extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε) (ψ.app 1) := by
    intro U s
    refine Eq.trans (ψ.map_mul 1 1 U s s).symm ?_
    have h0 : ((extSelfAlgebra Rc K).mul 1 1).app U s s = 0 := h.1 U s
    exact Eq.trans (congrArg (fun z => (ψ.app (1 + 1)).val.app U z) h0) (map_zero _)
  have hgen := SheafOfModules.GradedAlgebra.squareZero_comp
    (𝟙 ((extSelfAlgebra Rc K).piece 1)) hgen0
  have huniv := h.isUniversal.ofDegreewiseIso ψ hgen
  have hcomp := SheafOfModules.GradedAlgebra.IsExteriorAlgebra.comp_iso huniv
    (inv (ψ.app 1)) inferInstance
  have hid : inv (ψ.app 1) ≫ 𝟙 ((extSelfAlgebra Rc K).piece 1) ≫ ψ.app 1 =
      𝟙 ((extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε).piece 1) := by
    rw [Category.id_comp, IsIso.inv_hom_id]
  rw [hid] at hcomp
  exact hcomp

/-- **The exterior algebra over `O_X` of the first self-Ext sheaf**, as the degree-one piece of
the K-injective model presents it. -/
def extSelfExteriorAlgebraOfKInjective :=
  SheafOfModules.algebras (Opens.grothendieckTopology ↥X)
    ((extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε).piece 1)

/-- **The comparison map of Stacks 0BQY for the K-injective model**, in every degree:

`⋀ⁱ_{O_X}(Ext^1_{O♯}(O_X, O_X)) ⟶ Ext^i_{O♯}(O_X, O_X)`,

where the target algebra is the one whose multiplication is the composition product of a
K-injective representative. -/
def extComparisonOfKInjective
    (h : SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
      (𝟙 ((extSelfAlgebra Rc K).piece 1))) (i : ℤ) :=
  ((extSelfExteriorAlgebraOfKInjective Rc K I κ hbdd hterm D ε).exterior_isExteriorAlgebra.desc
    (extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε)
    (𝟙 ((extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε).piece 1))
    (isExteriorAlgebra_extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε h).1).app i

/-- **The comparison of Stacks 0BQY for the K-injective model is an isomorphism in every
degree**, whenever the Koszul model is an exterior algebra on its degree-one piece. -/
theorem isIso_extComparisonOfKInjective
    (h : SheafOfModules.GradedAlgebra.IsExteriorAlgebra (extSelfAlgebra Rc K)
      (𝟙 ((extSelfAlgebra Rc K).piece 1))) (i : ℤ) :
    IsIso (extComparisonOfKInjective Rc K I κ hbdd hterm D ε h i) :=
  ((extSelfExteriorAlgebraOfKInjective Rc K I κ hbdd hterm
      D ε).exterior_isExteriorAlgebra.isUniversal.pieceIso
    (isExteriorAlgebra_extSelfAlgebraOfKInjective Rc K I κ hbdd hterm D ε h).isUniversal
    i).isIso_hom

end Stacks.RegularSequence.KoszulChainData

end
