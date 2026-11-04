module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Normal
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# From the base change map of sheaves of sets to that of abelian sheaves

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes. There are two underived base change comparisons attached to
it on the small étale sites: `Stacks.EtaleCohomology.smallEtaleSetBaseChange`, the map
`g^{-1} f_* ⟶ f'_* (g')^{-1}` on sheaves of sets, and
`Stacks.EtaleCohomology.etaleAbelianBaseChange`, the same map on abelian sheaves. This file proves
that the second is an isomorphism as soon as the first is, at every coefficient universe
`max (u + 1) v`.

Both comparisons are mates along the two horizontal inverse-image/direct-image adjunctions of the
comparison of the two composite direct images around the square: for sheaves of sets this is the
definition, and for abelian sheaves it is
`Stacks.EtaleCohomology.etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso`. The two
comparisons of composite direct images are restriction of sections along the same isomorphisms of
base change functors, so they agree after forgetting the group structure, and composition with the
forgetful functor reflects isomorphisms.
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` then transports
invertibility from the mate at set coefficients to the mate at abelian coefficients; its remaining
input is that forgetting the group structure commutes with inverse image,
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_eq_mateEquiv_symm_univ` — the base change map of
  sheaves of sets is the horizontal mate of the comparison of composite direct images, with the
  common composite around the square carried as a named morphism.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isIso_smallEtaleSetBaseChange_general` —
  **the abelian base change map is invertible if the base change map of sheaves of sets is.**

## Implementation notes

The finite case `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_unconditional`
carries out the same transport, but from the size-bounded small étale site of a big étale site,
where its input Stacks 0959 is stated. Here both comparisons live on the small étale sites of the
schemes themselves, and the transport is stated at every coefficient universe `max (u + 1) v`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- Transport along an equality of the composite: the comparison of direct images along `f' ≫ g`
followed by transport to a named composite `P` is the named-composite comparison at `P`. -/
private lemma eqToHom_comp_smallEtalePushforwardComp'_inv (P : X' ⟶ Y) (hP : P = f' ≫ g) :
    eqToHom (congrArg (fun k : X' ⟶ Y ↦ (smallEtaleBaseChange k).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X')) hP) ≫
      (smallEtalePushforwardCompIso.{u, v} f' g).inv =
      (smallEtalePushforwardComp' f' g P hP (Type (max (u + 1) v))).inv := by
  subst hP
  have h : smallEtaleBaseChangeComp' f' g (f' ≫ g) rfl = smallEtaleBaseChangeComp f' g :=
    Iso.ext (by simp [smallEtaleBaseChangeComp'])
  simp only [eqToHom_refl, Category.id_comp, smallEtalePushforwardComp', h]
  rfl

/-- **The base change map of sheaves of sets is the horizontal mate of the comparison of the two
composite direct images around the square**, with the common composite `P` named. -/
theorem smallEtaleSetBaseChange_eq_mateEquiv_symm_univ (h : g' ≫ f = f' ≫ g) (P : X' ⟶ Y)
    (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g) :
    smallEtaleSetBaseChange.{u, v} g' f' f g h =
      (mateEquiv (smallEtaleInverseImageAdjunction.{u, v} g')
          (smallEtaleInverseImageAdjunction.{u, v} g)).symm
        (TwoSquare.mk _ _ _ _
          ((smallEtalePushforwardComp' g' f P hP₁ (Type (max (u + 1) v))).hom ≫
            (smallEtalePushforwardComp' f' g P hP₂ (Type (max (u + 1) v))).inv)) := by
  subst hP₁
  have h₁ : smallEtaleBaseChangeComp' g' f (g' ≫ f) rfl = smallEtaleBaseChangeComp g' f :=
    Iso.ext (by simp [smallEtaleBaseChangeComp'])
  have e₁ : (smallEtalePushforwardComp' g' f (g' ≫ f) rfl (Type (max (u + 1) v))).hom =
      (smallEtalePushforwardCompIso.{u, v} g' f).hom := by
    simp only [smallEtalePushforwardComp', h₁]
    rfl
  rw [e₁, ← eqToHom_comp_smallEtalePushforwardComp'_inv.{u, v} g f' (g' ≫ f) hP₂]
  rfl

/-- Composition with the forgetful functor of abelian groups, on abelian sheaves of the small
étale site of a scheme. -/
private abbrev forgetSheaf (S : Scheme.{u}) :
    Sheaf (smallEtaleTopology S) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (smallEtaleTopology S) (Type (max (u + 1) v)) :=
  sheafCompose (smallEtaleTopology S) (forget AddCommGrpCat.{max (u + 1) v})

/-- The comparison of inverse image with forgetting the group structure, along `k`. -/
private abbrev pullbackForget {S T : Scheme.{u}} (k : T ⟶ S) :
    TwoSquare (forgetSheaf.{u, v} S) (etaleAbelianInverseImage.{u, v} k)
      (smallEtaleInverseImage.{u, v} k) (forgetSheaf.{u, v} T) :=
  coefficientPullbackTwoSquare (smallEtaleBaseChange k) (smallEtaleTopology S)
    (smallEtaleTopology T) (forget AddCommGrpCat.{max (u + 1) v})

/-- Direct image commutes with forgetting the group structure on the nose. -/
private abbrev pushforwardForget {S T : Scheme.{u}} (k : T ⟶ S) :
    etaleAbelianDirectImage.{u, v} k ⋙ forgetSheaf.{u, v} S ⟶
      forgetSheaf.{u, v} T ⋙ (smallEtaleBaseChange k).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) :=
  𝟙 _

/-- The same identification read in the other direction. -/
private abbrev pushforwardForget' {S T : Scheme.{u}} (k : T ⟶ S) :
    forgetSheaf.{u, v} T ⋙ (smallEtaleBaseChange k).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S) (smallEtaleTopology T) ⟶
      etaleAbelianDirectImage.{u, v} k ⋙ forgetSheaf.{u, v} S :=
  𝟙 _

/-- The comparison of inverse image with forgetting the group structure is invertible. -/
private lemma isIso_pullbackForget {S T : Scheme.{u}} (k : T ⟶ S) :
    IsIso (pullbackForget.{u, v} k).natTrans :=
  have := preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ.{u, v} k
  isIso_coefficientPullbackTwoSquare (smallEtaleBaseChange k) (smallEtaleTopology S)
    (smallEtaleTopology T) (forget AddCommGrpCat.{max (u + 1) v})

/-- The mate of the comparison `pullbackForget` is the comparison of direct images. -/
private lemma mateEquiv_pullbackForget {S T : Scheme.{u}} (k : T ⟶ S) :
    mateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} k)
      (smallEtaleInverseImageAdjunction.{u, v} k) (pullbackForget.{u, v} k) =
        coefficientPushforwardTwoSquare (smallEtaleBaseChange k) (smallEtaleTopology S)
          (smallEtaleTopology T) (forget AddCommGrpCat.{max (u + 1) v}) :=
  have := preservesLeftKanExtensions_forget_smallEtaleBaseChange_univ.{u, v} k
  mateEquiv_coefficientPullbackTwoSquare _ _ _ _

/-- **The abelian base change map is invertible if the base change map of sheaves of sets is.**
For a commutative square `g' ≫ f = f' ≫ g` of schemes, if the comparison
`g^{-1} f_* ⟶ f'_* (g')^{-1}` of sheaves of sets on the small étale sites is an isomorphism, so is
the comparison of abelian sheaves, at the same coefficient universe `max (u + 1) v`. -/
theorem isIso_etaleAbelianBaseChange_of_isIso_smallEtaleSetBaseChange_general (h : g' ≫ f = f' ≫ g)
    (hset : IsIso (smallEtaleSetBaseChange.{u, v} g' f' f g h)) :
    IsIso (etaleAbelianBaseChange.{u, v} f g g' f' h) := by
  rw [smallEtaleSetBaseChange_eq_mateEquiv_symm_univ.{u, v} f g g' f' h (g' ≫ f) rfl h] at hset
  rw [etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, v} f g g' f' h
    (g' ≫ f) rfl h]
  have := isIso_pullbackForget.{u, v} g'
  have := isIso_pullbackForget.{u, v} g
  have : IsIso (pushforwardForget.{u, v} f) := by
    show IsIso (𝟙 _); infer_instance
  have : IsIso (pushforwardForget'.{u, v} f') := by
    show IsIso (𝟙 _); infer_instance
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g')
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (smallEtaleInverseImageAdjunction.{u, v} g') (smallEtaleInverseImageAdjunction.{u, v} g)
    (pullbackForget.{u, v} g') (pullbackForget.{u, v} g)
    (pushforwardForget.{u, v} f) (pushforwardForget'.{u, v} f')
    (TwoSquare.mk _ _ _ _ ((etaleAbelianDirectImageCompIso'.{u, v} g' f (g' ≫ f) rfl).hom ≫
      (etaleAbelianDirectImageCompIso'.{u, v} f' g (g' ≫ f) h).inv))
    (TwoSquare.mk _ _ _ _
      ((smallEtalePushforwardComp' g' f (g' ≫ f) rfl (Type (max (u + 1) v))).hom ≫
        (smallEtalePushforwardComp' f' g (g' ≫ f) h (Type (max (u + 1) v))).inv)) ?_
  rw [mateEquiv_pullbackForget, mateEquiv_pullbackForget]
  refine TwoSquare.ext _ _ fun F => ?_
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  rfl

end Stacks.EtaleCohomology

end
