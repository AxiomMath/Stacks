module

public import StacksFrontier.CategoryTheory.Monoidal.CommGrpCommutingSquare
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.AbelianSheafStalk
public import StacksFrontier.CategoryTheory.Equivalence.ConjugateSquare

/-!
# Restriction of a discrete action along a continuous homomorphism

Let `φ : G →ₜ* H` be a continuous homomorphism of topological groups. Restricting the action
along `φ` carries a continuous `H`-set to a continuous `G`-set and a discrete `H`-module to a
discrete `G`-module, because it changes neither the underlying object nor its topology. This
file records those two functors and shows that the dictionary identifying discrete modules with
the commutative group objects in continuous sets commutes with them.

## Main definitions

* `AlgebraicGeometry.ContinuousGSet.res` — restriction of a continuous `H`-set along `φ`.
* `CategoryTheory.ContinuousGAddCommGrp.res` — restriction of a discrete `H`-module along `φ`.

## Main results

* `AlgebraicGeometry.ContinuousGSet.res_comp_ι` and
  `CategoryTheory.ContinuousGAddCommGrp.res_comp_ι` — both are the restriction functor
  `CategoryTheory.ContAction.res` of all continuous actions, read on the discrete ones.
* `CategoryTheory.resCommGrpContinuousGSetEquivalenceSquare` — **restriction commutes with the
  dictionary of discrete modules and commutative group objects in continuous sets**: the square
  of `CategoryTheory.commGrpContinuousGSetEquivalence` against restriction commutes.

## Implementation notes

Restriction of an action leaves the underlying object alone, so the two functors are lifts of
`CategoryTheory.ContAction.res` to the full subcategory of discrete objects and both comparisons
with it hold on the nose. The same is true of the comparison with the presheaf picture of an
action: a continuous `G`-set read as a presheaf on the one-object category of `G`
(`CategoryTheory.gsetPresheaf`) is restricted along `φ` by precomposing with
`CategoryTheory.SingleObj.mapHom φ`, and likewise for a discrete module.

That reduces the square of `commGrpContinuousGSetEquivalence` to two general facts. The first is
that a commuting square of braided functors induces one on commutative group objects,
`CategoryTheory.Functor.mapCommGrpSquare`, applied to the comparison of restriction with
precomposition. The second is that reading internal commutative group operations sectionwise
commutes with precomposition, which is
`Stacks.Sites.AbelianPullback.precompInternalIso` conjugated by the dictionary
`CategoryTheory.presheafAbelianEquivalence` of abelian presheaves with commutative group objects
in presheaves of sets; the conjugation is
`CategoryTheory.Equivalence.conjugateSquare`. The square itself is then checked after the fully
faithful `CategoryTheory.gmodulePresheaf`, where
`CategoryTheory.externalGModule_comp_gmodulePresheaf` turns both legs into those two.

## References

* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

attribute [local instance] discreteForget₂Type discreteForget₂AddCommGrpCat
  cartesianMonoidalContinuousGSet braidedContinuousGSet

namespace AlgebraicGeometry

variable {G H : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H)

/-- **Restriction of a continuous `H`-set along a continuous homomorphism `φ : G →ₜ* H`.** The
underlying set is unchanged, so it is again discrete. -/
public def ContinuousGSet.res : ContinuousGSet.{u, w} H ⥤ ContinuousGSet.{u, w} G where
  obj X := ⟨(ContAction.res (Type w) φ).obj X.obj, X.property⟩
  map f := ObjectProperty.homMk ((ContAction.res (Type w) φ).map f.hom)

/-- Restriction of continuous `H`-sets is the restriction of all continuous actions of `H`. -/
public theorem ContinuousGSet.res_comp_ι :
    ContinuousGSet.res.{w} φ ⋙ ObjectProperty.ι _ =
      (ObjectProperty.ι _ : ContinuousGSet.{u, w} H ⥤ ContAction (Type w) H) ⋙
        ContAction.res (Type w) φ := rfl

/-- Restriction of continuous `H`-sets leaves the underlying set alone. -/
public theorem ContinuousGSet.res_comp_forget :
    ContinuousGSet.res.{w} φ ⋙ ContinuousGSet.forget.{u, w} G =
      ContinuousGSet.forget.{u, w} H := rfl

/-- Restriction of continuous `H`-sets, read as a presheaf on the one-object category of the
group, is precomposition with the induced functor of one-object categories. -/
public theorem ContinuousGSet.res_comp_gsetPresheaf :
    ContinuousGSet.res.{w} φ ⋙ gsetPresheaf.{u, w} (G := G) =
      gsetPresheaf.{u, w} (G := H) ⋙
        (Functor.whiskeringLeft (SingleObj G) (SingleObj H) (Type w)).obj
          (SingleObj.mapHom G H φ.toMonoidHom) := rfl

/-- Restriction of continuous `H`-sets preserves finite products: it leaves the underlying sets
alone, and they are what the finite products of continuous sets are computed on. -/
public instance ContinuousGSet.res_preservesFiniteProducts :
    PreservesFiniteProducts (ContinuousGSet.res.{w} φ) :=
  letI : PreservesFiniteProducts (ContinuousGSet.res.{w} φ ⋙ ContinuousGSet.toAction G) :=
    { preserves := fun n ↦
        have hforget : PreservesLimitsOfShape (Discrete (Fin n))
            (ContinuousGSet.forget.{u, w} H) := inferInstance
        Action.preservesLimitsOfShape_of_preserves _ hforget }
  letI hff : (ContinuousGSet.toAction.{u, w} G).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  letI := hff.full
  letI := hff.faithful
  letI : ReflectsFiniteProducts (ContinuousGSet.toAction.{u, w} G) :=
    { reflects := fun _ ↦ inferInstance }
  preservesFiniteProducts_of_reflects_of_preserves _ (ContinuousGSet.toAction G)

end AlgebraicGeometry

namespace CategoryTheory

variable {G H : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  (φ : G →ₜ* H)

/-- **Restriction of a discrete `H`-module along a continuous homomorphism `φ : G →ₜ* H`.** The
underlying abelian group is unchanged, so its topology is again discrete. -/
public def ContinuousGAddCommGrp.res :
    ContinuousGAddCommGrp.{u, w} H ⥤ ContinuousGAddCommGrp.{u, w} G where
  obj X := ⟨(ContAction.res AddCommGrpCat.{w} φ).obj X.obj, X.property⟩
  map f := ObjectProperty.homMk ((ContAction.res AddCommGrpCat.{w} φ).map f.hom)

/-- Restriction of discrete `H`-modules is the restriction of all continuous actions of `H` on
abelian groups. -/
public theorem ContinuousGAddCommGrp.res_comp_ι :
    ContinuousGAddCommGrp.res.{w} φ ⋙ ObjectProperty.ι _ =
      (ObjectProperty.ι _ : ContinuousGAddCommGrp.{u, w} H ⥤ ContAction AddCommGrpCat.{w} H) ⋙
        ContAction.res AddCommGrpCat.{w} φ := rfl

/-- Restriction of discrete `H`-modules, read as an abelian presheaf on the one-object category
of the group, is precomposition with the induced functor of one-object categories. -/
public theorem ContinuousGAddCommGrp.res_comp_gmodulePresheaf :
    ContinuousGAddCommGrp.res.{w} φ ⋙ gmodulePresheaf.{u, w} (G := G) =
      gmodulePresheaf.{u, w} (G := H) ⋙
        (Functor.whiskeringLeft (SingleObj G) (SingleObj H) AddCommGrpCat.{w}).obj
          (SingleObj.mapHom G H φ.toMonoidHom) := rfl

/-- Reading internal commutative group operations of presheaves sectionwise commutes with
precomposition along a functor: the dictionary of
`CategoryTheory.presheafAbelianEquivalence` conjugates
`Stacks.Sites.AbelianPullback.precompInternalIso`. -/
public def abelianPresheavesPrecompSquare {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) :
    letI : ((Functor.whiskeringLeft C D (Type w)).obj F).Braided := .ofChosenFiniteProducts _
    Sites.AbelianSheaf.abelianPresheaves ⋙
        (Functor.whiskeringLeft C D AddCommGrpCat.{w}).obj F ≅
      ((Functor.whiskeringLeft C D (Type w)).obj F).mapCommGrp ⋙
        Sites.AbelianSheaf.abelianPresheaves := by
  letI : ((Functor.whiskeringLeft C D (Type w)).obj F).Braided := .ofChosenFiniteProducts _
  exact Equivalence.conjugateSquare (presheafAbelianEquivalence.{w} (C := D))
    (presheafAbelianEquivalence.{w} (C := C))
    (Stacks.Sites.AbelianPullback.precompInternalIsoOfUniverses.{_, _, w} F).symm

/-- **Restriction commutes with the dictionary identifying discrete modules with the commutative
group objects in continuous sets.** For a continuous homomorphism `φ : G →ₜ* H`, restricting a
commutative group object in continuous `H`-sets along `φ` and reading its operations as a
discrete `G`-module is the same as reading them as a discrete `H`-module and restricting. -/
public def resCommGrpContinuousGSetEquivalenceSquare :
    letI : (AlgebraicGeometry.ContinuousGSet.res.{w} φ).Braided := .ofChosenFiniteProducts _
    (AlgebraicGeometry.ContinuousGSet.res.{w} φ).mapCommGrp ⋙
        (commGrpContinuousGSetEquivalence.{u, w} (G := G)).functor ≅
      (commGrpContinuousGSetEquivalence.{u, w} (G := H)).functor ⋙
        ContinuousGAddCommGrp.res.{w} φ := by
  letI : (AlgebraicGeometry.ContinuousGSet.res.{w} φ).Braided := .ofChosenFiniteProducts _
  letI : (gsetPresheaf.{u, w} (G := G)).Braided := .ofChosenFiniteProducts _
  letI : (gsetPresheaf.{u, w} (G := H)).Braided := .ofChosenFiniteProducts _
  letI : ((Functor.whiskeringLeft (SingleObj G) (SingleObj H) (Type w)).obj
      (SingleObj.mapHom G H φ.toMonoidHom)).Braided := .ofChosenFiniteProducts _
  letI := (gmodulePresheafFullyFaithful.{u, w} (G := G)).full
  letI := (gmodulePresheafFullyFaithful.{u, w} (G := G)).faithful
  exact Functor.fullyFaithfulCancelRight (gmodulePresheaf.{u, w} (G := G))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight
        (Functor.mapCommGrpSquare
          (eqToIso (AlgebraicGeometry.ContinuousGSet.res_comp_gsetPresheaf.{w} φ)))
        Sites.AbelianSheaf.abelianPresheaves ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (gsetPresheaf.{u, w} (G := H)).mapCommGrp
        (abelianPresheavesPrecompSquare.{w} (SingleObj.mapHom G H φ.toMonoidHom)).symm ≪≫
      (Functor.associator _ _ _).symm)

end CategoryTheory

end
