module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposUnitorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplexAssociatorOnRingedTopoi

/-!
# The site-presented pullback of sheaves of modules is a monoidal functor

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites. The pullback of sheaves of modules attached to that presentation,
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, is a monoidal functor for the tensor
product `Stacks.SheafOfModules.Tensor.sheafTensor` on either side, with tensorator the comparison
of Stacks 03EL.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackToposMonoidal`: the pullback `f.pullbackTopos` is
  monoidal for `SheafOfModules.monoidalCategorySheafTensor` on each side.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposMonoidal_δ`: the oplax tensorator of
  `pullbackToposMonoidal` is `pullbackToposTensorMap`, the comparison out of which the
  identification of total tensor complexes behind Stacks 07A4 is built.

## Implementation notes

The coherence is not proved here. The pullback along the four-field presentation
`modulesHomOfSiteHom f hmos` is monoidal for `sheafTensor` by
`Stacks.Sheaves.DerivedPullback.pullbackModulesMonoidalSheafTensor`: the coherence of Stacks 03EL,
`Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal`, stated for the strict monoidal
structure of Tag 01CA, conjugated by the monoidal identity functors
`Stacks.Sheaves.DerivedPullback.idCoreMonoidalSheafTensorToStrict` on the source and
`SheafOfModules.idMonoidalStrictToSheafTensor` on the target. Both of those identity functors have
`Iso.refl` as tensorator, so transporting along `pullbackModulesSiteIso` gives
`pullbackToposMonoidal`, and `pullbackToposMonoidal_δ` holds by unfolding.
None of the structures is an instance, following the files they come from.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Stacks.Sheaves.DerivedPullback

universe u

/-- The identity functor applied to an identity, followed by a morphism and an identity, is that
morphism. Stated with every object a variable, so that it applies across the two spellings of
the structure sheaf at which the identities below are written. -/
private lemma map_id_comp_comp_id {C D : Type*} [Category C] [Category D] (G : C ⥤ D) (X : C)
    {Z : D} (d : G.obj X ⟶ Z) : G.map (𝟙 X) ≫ d ≫ 𝟙 Z = d := by
  simp

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **The site-presented pullback of sheaves of modules is monoidal for `sheafTensor`**:
`pullbackModulesMonoidalSheafTensor` transported along the identification
`pullbackModulesSiteIso` of the two pullbacks. -/
@[instance_reducible]
def pullbackToposMonoidal :
    @Functor.Monoidal _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor X.O) f.pullbackTopos :=
  letI := _root_.SheafOfModules.monoidalCategorySheafTensor Y.O
  letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.O
  letI := pullbackModulesMonoidalSheafTensor (modulesHomOfSiteHom f hmos)
  Functor.Monoidal.transport (pullbackModulesSiteIso f hmos)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- The oplax tensorator of the monoidal identity functor from the strict structure of Tag 01CA
to the structure whose tensor product is `sheafTensor` is the identity. -/
private theorem δ_idMonoidalStrictToSheafTensor
    (P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    @Functor.OplaxMonoidal.δ _ _ (Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)) _ _
      (_root_.SheafOfModules.monoidalCategorySheafTensor X.O) (𝟭 _)
      (_root_.SheafOfModules.idMonoidalStrictToSheafTensor X.O).toOplaxMonoidal P Q = 𝟙 _ :=
  rfl

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)] in
/-- **The tensorator of the site-presented pullback is the comparison of Stacks 03EL**: the oplax
tensorator of `pullbackToposMonoidal` is `pullbackToposTensorMap`, the comparison out of which
the identification of total tensor complexes behind Stacks 07A4 is built. -/
theorem pullbackToposMonoidal_δ
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor Y.O
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.O
    letI := pullbackToposMonoidal f hmos
    Functor.OplaxMonoidal.δ f.pullbackTopos A B = pullbackToposTensorMap f hmos A B := by
  let := _root_.SheafOfModules.monoidalCategorySheafTensor Y.O
  let := _root_.SheafOfModules.monoidalCategorySheafTensor X.O
  let := pullbackModulesMonoidalSheafTensor (modulesHomOfSiteHom f hmos)
  rw [pullbackToposMonoidal, Functor.Monoidal.transport_δ, pullbackToposTensorMap]
  refine congrArg (_ ≫ ·) (congrArg₂ (· ≫ ·) ?_ ?_)
  · change (modulesHomOfSiteHom f hmos).pullbackModules.map
          (@Functor.OplaxMonoidal.δ _ _ (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O) _ _
            (Stacks.SheafOfModules.Strict.monoidalCategory Y.O.obj
              (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.O)) (𝟭 _)
            (@Functor.CoreMonoidal.toMonoidal _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Y.O) _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory Y.O.obj
          (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.O)) _
        (idCoreMonoidalSheafTensorToStrict Y.O)).toOplaxMonoidal A B) ≫
        (@Functor.OplaxMonoidal.δ _ _ (Stacks.SheafOfModules.Strict.monoidalCategory Y.O.obj
              (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.O)) _ _
            (Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
              (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O))
            (modulesHomOfSiteHom f hmos).pullbackModules
            (Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal
              (modulesHomOfSiteHom f hmos)).toOplaxMonoidal A B ≫
          @Functor.OplaxMonoidal.δ _ _ (Stacks.SheafOfModules.Strict.monoidalCategory X.O.obj
              (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.O)) _ _
            (_root_.SheafOfModules.monoidalCategorySheafTensor X.O) (𝟭 _)
            (_root_.SheafOfModules.idMonoidalStrictToSheafTensor X.O).toOplaxMonoidal _ _) = _
    rw [δ_idMonoidalStrictToSheafTensor]
    exact map_id_comp_comp_id _ _ _
  · rfl

end Stacks.Sheaves.DerivedPullback

end
