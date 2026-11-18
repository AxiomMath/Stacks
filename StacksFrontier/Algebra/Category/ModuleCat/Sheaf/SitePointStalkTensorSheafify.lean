module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorSheafifyLocallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionForKFlatness

/-!
# The stalk criterion for K-flatness on a ringed site with enough points

Let `(C, J)` be a site, `Φ` a point of it, and `O` a sheaf of commutative rings on `C`. The stalk
at `Φ` of the tensor product of two sheaves of `O`-modules is the tensor product of the stalks
(`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso`), and its
consequence is that part (2) of Stacks 0DEN holds with no extra hypothesis.

## Main definitions

* `Stacks.SheafOfModules.SitePointStalkSheafify.stalkTensorData`: the datum
  `Stacks.Sheaves.KFlatStalkCriterion.StalkTensorData`, i.e. Stacks 03EL at one point of the site
  in the shape `CategoryTheory.Functor.mapBifunctorTotalIso` consumes.

## Main results

* `Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`: **part (2) of Stacks 0DEN with
  no extra hypothesis.** On a ringed site whose underlying site has enough points, a complex of
  `O`-modules whose stalk at every point is K-flat is itself K-flat.

## Implementation notes

`Stacks.SheafOfModules.Tensor.sheafTensor` sheafifies with the sealed
`Stacks.SheafOfModules.Tensor.sheafification`, so the isomorphism of `stalkTensorData` is
`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso`, which passes from
the sealed sheafification to Mathlib's. `stalkSheafTensorIso_naturality_left` is its naturality in
the left-hand variable, the companion of
`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso_naturality_right`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u v w

namespace Stacks.SheafOfModules.SitePointStalkSheafify

section Ring

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{u}) (R : Sheaf J RingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

end Ring

/-! ### Naturality in the left-hand variable of the stalk of a tensor product -/

section Naturality

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- `Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso` is natural in
the left-hand variable, as
`Stacks.SheafOfModules.SitePointStalkSheafify.LocallySmall.stalkSheafTensorIso_naturality_right`
is in the right-hand one. -/
lemma stalkSheafTensorIso_naturality_left
    {A A' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f : A ⟶ A')
    (B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.sheafModuleFiberOfCommRing Φ O).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).map f).app B) ≫
        (LocallySmall.stalkSheafTensorIso Φ O A' B).hom =
      (LocallySmall.stalkSheafTensorIso Φ O A B).hom ≫
        ((curriedTensor (ModuleCat.{w} (Stacks.ringFiber Φ O.obj))).map
          ((Stacks.sheafModuleFiberOfCommRing Φ O).map f)).app
            ((Stacks.sheafModuleFiberOfCommRing Φ O).obj B) := by
  have he := (Functor.whiskerRight (eqToHom (Stacks.SheafOfModules.Tensor.sheafification_def O))
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
      Stacks.presheafModuleFiberOfCommRing Φ O.obj)).naturality_assoc
      (((curriedTensor (PresheafOfModules.{w}
        (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).map f.val).app B.val)
      (LocallySmall.tensorSheafifyIso Φ O A'.val B.val).hom
  rw [LocallySmall.stalkSheafTensorIso_hom, LocallySmall.stalkSheafTensorIso_hom]
  -- `apply` checks this composite, stated over `presheafModuleFiberOfCommRing`, against the goal
  -- once; `exact` would check it twice.
  apply he.trans ((congrArg (_ ≫ ·)
    (LocallySmall.tensorSheafifyIso_naturality_left Φ O (φ := f.val) B.val)).trans
      (Category.assoc _ _ _).symm)

end Naturality

/-! ### Stacks 03EL as the datum Stacks 0DEN consumes -/

section CommRing

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{u}) (O : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- **Stacks 03EL at one point of the site, in the shape the stalk criterion for K-flatness
consumes**: the stalk at `Φ` of `A ⊗_O B` is `A_Φ ⊗_{O_Φ} B_Φ`, naturally in `A` and `B`. -/
noncomputable def stalkTensorData : Stacks.Sheaves.KFlatStalkCriterion.StalkTensorData O Φ where
  iso := LocallySmall.stalkSheafTensorIso Φ O
  naturality_left f B := stalkSheafTensorIso_naturality_left Φ O f B
  naturality_right A {_ _} g := LocallySmall.stalkSheafTensorIso_naturality_right Φ O A g

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

/-- **Stacks 0DEN, part (2), with no extra hypothesis.** On a ringed site whose underlying site
has enough points, a complex of `O`-modules whose stalk at every point is a K-flat complex of
modules over the stalk of `O` is itself K-flat.

This is `Stacks.Sheaves.KFlatStalkCriterion.kFlat_of_stalks` with its
`Stacks.Sheaves.KFlatStalkCriterion.StalkTensorData` argument supplied by `stalkTensorData`. -/
@[stacks 0DEN "part (2)"]
theorem kFlat_of_stalks (hJ : J.HasConservativeFamily.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : ∀ Ψ : J.Point.{u},
      CochainComplex.KFlat.{u, u} (Stacks.Sheaves.KFlatStalkCriterion.stalkComplex O Ψ K)) :
    Stacks.SheafOfModules.IsKFlat O K :=
  Stacks.Sheaves.KFlatStalkCriterion.kFlat_of_stalks O hJ (fun Ψ => stalkTensorData Ψ O) K hK

end Tensor

end CommRing

end Stacks.SheafOfModules.SitePointStalkSheafify

end
