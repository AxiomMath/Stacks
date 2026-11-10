module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryFactorshQuotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.DerivedCategory

/-!
# The composition comparisons of degreewise derived functors, read on homotopy categories

An exact functor `F` between abelian categories acts on unbounded derived categories degreewise,
by `CategoryTheory.Functor.mapDerivedCategory`, and that action admits two comparisons with the
localization functors: `CategoryTheory.Functor.mapDerivedCategoryFactors` over
`DerivedCategory.Q`, and `CategoryTheory.Functor.mapDerivedCategoryFactorsh` over
`DerivedCategory.Qh`. The isomorphism

`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso :
  F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory`

attached to an isomorphism `e : F ⋙ G ≅ H` of exact functors is built over `DerivedCategory.Q`,
by lifting through that localization. A proof that identifies a transformation of derived
categories with a right derived functor of a functor on the *homotopy* category — the situation of
`Stacks.DerivedFunctor.exactDerivedDesc`, whose defining factorization is stated at an object
`DerivedCategory.Qh.obj J` — therefore cannot use `mapDerivedCategoryCompIsoOfCompIso` directly: the
two constructions live over different localization functors, and nothing relates them.

This file relates them. It evaluates `mapDerivedCategoryCompIsoOfCompIso` at an object of the
derived
category coming from the homotopy category, in the vocabulary of `mapDerivedCategoryFactorsh` and
of `CategoryTheory.Functor.mapHomotopyCategoryCompIso`, and it records the companion statement for
the degreewise transformation `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp`: the degreewise
action of a transformation `F ⟶ P ⋙ (G ⋙ H)` assembled from `F ⟶ P ⋙ F'` and `F' ⟶ G ⋙ H` is the
composite of their two degreewise actions. Together these turn a commuting square of comparison
isomorphisms of derived functors into a degreewise statement about complexes.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q`: the value of the composition
  isomorphism at the image of a cochain complex, in terms of `mapDerivedCategoryFactors`.
* `CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh`: the value of the composition
  isomorphism at the image of an object of the homotopy category, in terms of
  `mapDerivedCategoryFactorsh` and `mapHomotopyCategoryCompIso`.
* `CategoryTheory.Functor.mapDerivedCategoryCompIso_inv_app_Qh`: the same for the inverse of the
  composition isomorphism.
* `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app`: the degreewise action of a
  transformation `F ⟶ G ⋙ H` is, at an object, the localization of the degreewise action of that
  transformation on complexes.
* `Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_comp_whiskerLeft`: the degreewise action of a
  composite transformation is the composite of the two degreewise actions.

## Implementation notes

Every object of the homotopy category of cochain complexes is the quotient of the complex
representing it, so the statement over `DerivedCategory.Qh` at an arbitrary object `J` follows
from the statement at `(HomotopyCategory.quotient _ _).obj J.as`, which is how it is proved here.

The two localization functors are compared only through the isomorphism
`DerivedCategory.quotientCompQhIso`, never through the definition of `DerivedCategory.Qh`: that
definition is not exposed, so the fact that `DerivedCategory.Qh` is the lift of
`DerivedCategory.Q` along the quotient functor — hence that the components of
`DerivedCategory.quotientCompQhIso` are identities — is not available here. The proof instead
conjugates the statement over `DerivedCategory.Q` by that isomorphism and cancels the two copies
of each of its components. The crossings this needs for a single functor are
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app_quotient_obj`, its inverse half and
`CategoryTheory.Functor.Qh_map_quotient_map`, in
`StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryFactorshQuotient`.

One object of a derived category has several definitionally equal but syntactically distinct
spellings — `(HomotopyCategory.quotient _ _ ⋙ DerivedCategory.Qh).obj K` against
`DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)`, or
`(F.mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj K)` against
`(HomotopyCategory.quotient _ _).obj ((F.mapHomologicalComplex _).obj K)`. A composite whose
consecutive factors use different spellings is well typed and yet invisible to the keyed matching
of `rw` and `simp`. The cancellation is therefore carried out on a composite written out in a
single spelling, and only afterwards are the conjugated factors recognised as the comparisons over
`DerivedCategory.Qh`; that last step is an explicit `congrArg₂` term, which is checked up to
definitional equality and so is indifferent to the spelling.

The two declarations compared here are not in Mathlib:
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso` is stated in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion` and
`Stacks.DerivedFunctor.mapHomotopyCategoryOfComp` in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale`, which is why a file about general
homological algebra imports two files about schemes. Nothing about schemes is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

omit [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂] in
/-- At the image of a cochain complex under `HomotopyCategory.quotient`, the localization by
`DerivedCategory.Qh` of the comparison of homotopy categories attached to `e : F ⋙ G ≅ H` is the
localization by `DerivedCategory.Q` of the comparison of categories of complexes attached to `e`,
read through `DerivedCategory.quotientCompQhIso`: the former comparison is the quotient of the
latter. -/
private lemma Qh_map_mapHomotopyCategoryCompIso_hom_app_quotient_obj
    {F : C₁ ⥤ C₂} [F.Additive] {G : C₂ ⥤ C₃} [G.Additive] {H : C₁ ⥤ C₃} [H.Additive]
    (e : F ⋙ G ≅ H) (K : CochainComplex C₁ ℤ) :
    (DerivedCategory.quotientCompQhIso C₃).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
          (DerivedCategory.quotientCompQhIso C₃).inv.app
            ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) :=
  (Qh_map_quotient_map _).symm

variable {F : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {G : C₂ ⥤ C₃} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {H : C₁ ⥤ C₃} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

section CompIsoQ

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- At the image of a cochain complex `K` under `DerivedCategory.Q`, the composition isomorphism
attached to `e : F ⋙ G ≅ H` is assembled from the comparisons of the degreewise actions of `F`,
of `G` and of `H` with `DerivedCategory.Q`, and from the comparison of categories of complexes
attached to `e`. The composition isomorphism is the untwisted comparison followed by the
degreewise change of functor, and this is the composite of the two values already recorded on the
image of `DerivedCategory.Q`, the two copies of the comparison for `F ⋙ G` cancelling. -/
theorem mapDerivedCategoryCompIso_hom_app_Q (e : F ⋙ G ≅ H) (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
            H.mapDerivedCategoryFactors.inv.app K := by
  change ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).inv ≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso (F ⋙ G) H e).hom).app
      (DerivedCategory.Q.obj K) = _
  rw [NatTrans.comp_app,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl

end CompIsoQ

/-- The value of the composition isomorphism at the image under `DerivedCategory.Qh` of the
quotient of a cochain complex: `mapDerivedCategoryCompIso_hom_app_Q` conjugated by
`DerivedCategory.quotientCompQhIso`, with the three conjugated factors recognised as the
comparisons over `DerivedCategory.Qh`. -/
private lemma mapDerivedCategoryCompIso_hom_app_Qh_quotient_obj (e : F ⋙ G ≅ H)
    (K : CochainComplex C₁ ℤ) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
                ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K)) ≫
            H.mapDerivedCategoryFactorsh.inv.app
              ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) := by
  have hL : (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso C₁).hom.app K)) ≫
        ((Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.app (DerivedCategory.Q.obj K) ≫
          H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).inv.app K)) := by
    have nat := (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.naturality
      ((DerivedCategory.quotientCompQhIso C₁).hom.app K)
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, nat, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have hExp : (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) =
      G.mapDerivedCategory.map
          (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
            F.mapDerivedCategoryFactors.hom.app K ≫
              (DerivedCategory.quotientCompQhIso C₂).inv.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₂).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            G.mapDerivedCategoryFactors.hom.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
              (DerivedCategory.quotientCompQhIso C₃).inv.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                  G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
          ((DerivedCategory.quotientCompQhIso C₃).hom.app
                ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
                  G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
              DerivedCategory.Q.map
                  ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
                (DerivedCategory.quotientCompQhIso C₃).inv.app
                  ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
            ((DerivedCategory.quotientCompQhIso C₃).hom.app
                  ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
                H.mapDerivedCategoryFactors.inv.app K ≫
                  H.mapDerivedCategory.map
                    ((DerivedCategory.quotientCompQhIso C₁).inv.app K)) := by
    have hcancel : F.mapDerivedCategoryFactors.hom.app K ≫
        𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
        F.mapDerivedCategoryFactors.hom.app K := Category.comp_id _
    refine hL.trans ?_
    rw [mapDerivedCategoryCompIso_hom_app_Q]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, hcancel,
      ← CategoryTheory.Functor.map_comp_assoc]
  exact hExp.trans (congrArg₂ (· ≫ ·)
    (congrArg G.mapDerivedCategory.map
      (mapDerivedCategoryFactorsh_hom_app_quotient_obj F K))
    (congrArg₂ (· ≫ ·)
      (mapDerivedCategoryFactorsh_hom_app_quotient_obj G
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      (congrArg₂ (· ≫ ·)
        (Qh_map_mapHomotopyCategoryCompIso_hom_app_quotient_obj e K)
        (mapDerivedCategoryFactorsh_inv_app_quotient_obj H K))))

/-- At the image of an object `J` of the homotopy category of cochain complexes under
`DerivedCategory.Qh`, the composition isomorphism attached to `e : F ⋙ G ≅ H` is assembled from
the comparisons of the degreewise actions of `F`, of `G` and of `H` with `DerivedCategory.Qh`, and
from the comparison of homotopy categories attached to `e`.

This is the form in which the composition isomorphism meets a right derived functor of a functor
on the homotopy category, such as `Stacks.DerivedFunctor.exactDerivedDesc`, whose defining
factorization `Stacks.DerivedFunctor.exactDerivedDesc_fac_app` is stated at such an object. -/
theorem mapDerivedCategoryCompIso_hom_app_Qh (e : F ⋙ G ≅ H)
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso e).hom.app (DerivedCategory.Qh.obj J) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫
        G.mapDerivedCategoryFactorsh.hom.app
            ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app J) ≫
            H.mapDerivedCategoryFactorsh.inv.app J :=
  mapDerivedCategoryCompIso_hom_app_Qh_quotient_obj e J.as

/-- The inverse of the composition isomorphism at the image of an object `J` of the homotopy
category of cochain complexes under `DerivedCategory.Qh`: the inverse of the composite in
`mapDerivedCategoryCompIso_hom_app_Qh`, factor by factor in the opposite order. -/
theorem mapDerivedCategoryCompIso_inv_app_Qh (e : F ⋙ G ≅ H)
    (J : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso e).inv.app (DerivedCategory.Qh.obj J) =
      H.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app J) ≫
          G.mapDerivedCategoryFactorsh.inv.app
              ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.inv.app J) := by
  have hiso : (Functor.mapDerivedCategoryCompIsoOfCompIso e).app (DerivedCategory.Qh.obj J) =
      G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactorsh.app J) ≪≫
        G.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≪≫
          DerivedCategory.Qh.mapIso
              ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).app J) ≪≫
            (H.mapDerivedCategoryFactorsh.app J).symm :=
    Iso.ext (mapDerivedCategoryCompIso_hom_app_Qh e J)
  refine (congrArg Iso.inv hiso).trans ?_
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end CategoryTheory.Functor

namespace Stacks.DerivedFunctor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂]
  {A₃ : Type u₃} [Category.{v₃} A₃] [Abelian A₃]
  {A₄ : Type u₄} [Category.{v₄} A₄] [Abelian A₄]

/-- The comparison of homotopy categories attached to the identity isomorphism of a composite of
additive functors is the identity: it is the quotient of an identity. -/
private lemma mapHomotopyCategoryCompIso_refl_inv_app (G : A₂ ⥤ A₃) (H : A₃ ⥤ A₄) [G.Additive]
    [H.Additive] (X : HomotopyCategory A₂ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H)) (ComplexShape.up ℤ)).inv.app X =
      𝟙 _ := by
  change (HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- The degreewise action of a transformation `τ : F ⟶ G ⋙ H` is, at an object of the homotopy
category, the localization of the degreewise action of `τ` on the representing complex: the
comparison of the action of a composite with the composite of the actions, which the definition
inserts, is an identity. -/
theorem mapHomotopyCategoryOfComp_app (F : A₁ ⥤ A₃) [F.Additive] (G : A₁ ⥤ A₂) [G.Additive]
    (H : A₂ ⥤ A₃) [H.Additive] (τ : F ⟶ G ⋙ H)
    (X : HomotopyCategory A₁ (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryOfComp F G H τ).app X =
      (HomotopyCategory.quotient A₃ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app X.as) := by
  unfold mapHomotopyCategoryOfComp
  rw [NatTrans.comp_app, mapHomotopyCategoryCompIso_refl_inv_app]
  exact Category.comp_id _

/-- The degreewise action of a composite transformation is the composite of the two degreewise
actions. Given `σ : F ⟶ P ⋙ F'` and `τ : F' ⟶ G ⋙ H`, the transformation
`σ ≫ Functor.whiskerLeft P τ : F ⟶ (P ⋙ G) ⋙ H` acts on homotopy categories as the action of `σ`,
followed by the action of `τ` after `P`, followed by the comparison identifying the action of
`P ⋙ G` with the composite of the actions of `P` and of `G`.

This is what splits the degreewise comparison appearing in
`Stacks.DerivedFunctor.exactDerivedDesc_fac_app` when the transformation being descended is
assembled in two steps. -/
theorem mapHomotopyCategoryOfComp_comp_whiskerLeft (F : A₁ ⥤ A₄) [F.Additive] (P : A₁ ⥤ A₂)
    [P.Additive] (F' : A₂ ⥤ A₄) [F'.Additive] (G : A₂ ⥤ A₃) [G.Additive] (H : A₃ ⥤ A₄)
    [H.Additive] (σ : F ⟶ P ⋙ F') (τ : F' ⟶ G ⋙ H) :
    mapHomotopyCategoryOfComp F (P ⋙ G) H (σ ≫ Functor.whiskerLeft P τ) =
      mapHomotopyCategoryOfComp F P F' σ ≫
        Functor.whiskerLeft (P.mapHomotopyCategory (ComplexShape.up ℤ))
          (mapHomotopyCategoryOfComp F' G H τ) ≫
        Functor.whiskerRight
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (ComplexShape.up ℤ)).hom
          (H.mapHomotopyCategory (ComplexShape.up ℤ)) := by
  ext X
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    mapHomotopyCategoryOfComp_app, mapHomotopyCategoryOfComp_app, mapHomotopyCategoryOfComp_app]
  have key :
      (NatTrans.mapHomologicalComplex (σ ≫ Functor.whiskerLeft P τ)
          (ComplexShape.up ℤ)).app X.as =
        (NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app X.as ≫
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
              ((P.mapHomotopyCategory (ComplexShape.up ℤ)).obj X).as ≫
            (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.as)))) :=
    HomologicalComplex.hom_ext _ _ fun i => by
      change σ.app (X.as.X i) ≫ τ.app (P.obj (X.as.X i)) =
        σ.app (X.as.X i) ≫ τ.app (P.obj (X.as.X i)) ≫ H.map (𝟙 (G.obj (P.obj (X.as.X i))))
      simp
  have whisker : (H.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ G)) (ComplexShape.up ℤ)).hom.app X) =
        (HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map
          ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj X.as)))) := rfl
  rw [whisker]
  exact (congrArg (HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map key).trans
    (((HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map_comp _ _).trans
      (congrArg ((HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ (ComplexShape.up ℤ)).app X.as) ≫ ·)
        ((HomotopyCategory.quotient A₄ (ComplexShape.up ℤ)).map_comp _ _)))

end Stacks.DerivedFunctor

end
