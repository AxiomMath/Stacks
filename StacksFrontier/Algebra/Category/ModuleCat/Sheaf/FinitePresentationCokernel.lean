module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Basic.Finite.Sum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresentationUnderFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
import StacksCore.Tactic.StacksAttribute

/-!
# Cokernels of maps from finite-type sheaves of modules

Let `R` be a sheaf of rings on a topological space, `F` a sheaf of `R`-modules of finite
presentation and `G` a sheaf of `R`-modules of finite type. The cokernel of any morphism `G ⟶ F`
is again of finite presentation.

Finite presentation is a local condition, so the proof may work over the members of a cover and
reduce twice: first to the case where `F` carries a finite presentation outright, then, using
local generators of `G`, to the case where the source is a finite free module. In that case the
cokernel is computed from a presentation: writing `F` as the cokernel of a map between finite
free modules and `G` through a finite free module, the map
`R^{σ} ⊕ R^{P} ⟶ F` assembled from `G ⟶ F` and from the generators of `F` is an epimorphism,
its kernel is of finite type (Stacks 01BP), and projecting that kernel to the second summand
gives a map whose cokernel is the cokernel of `G ⟶ F` — this last identification is
`cokernel_kernel_projection_iso`, a purely abelian-category statement. The cokernel of a
finite-type module into a finite free one is of finite presentation
(`isFinitePresentation_cokernel_finiteType_to_free`), which closes the induction.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_cokernel`: the cokernel of a morphism from a sheaf
  of modules of finite type to one of finite presentation is of finite presentation.

## Implementation notes

The structure sheaf is an arbitrary sheaf of rings `R` on the site of opens of a topological
space, so no commutativity is assumed. The cokernel is the categorical cokernel in
`SheafOfModules R`.

## References

* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP), the kernel of an
  epimorphism from a finite free module.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v₁ u₁

namespace Stacks.SheafOfModules

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

private noncomputable def cokernel_kernel_projection_iso
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {A B F Q : C} (f : A ⟶ F) (e : B ⟶ F) [Epi e]
    (α : Q ≅ A ⨿ B) :
    let θ : Q ⟶ F := α.hom ≫ coprod.desc f e
    let p : kernel θ ⟶ B := kernel.ι θ ≫ α.hom ≫ coprod.desc 0 (𝟙 B)
    cokernel p ≅ cokernel f := by
  classical
  dsimp
  let θ : Q ⟶ F := α.hom ≫ coprod.desc f e
  let pr : A ⨿ B ⟶ B := coprod.desc 0 (𝟙 B)
  let p : kernel θ ⟶ B := kernel.ι θ ≫ α.hom ≫ pr
  have : Epi (coprod.desc f e) := epi_of_epi_fac (coprod.inr_desc f e)
  have : Epi θ := by
    dsimp [θ]
    infer_instance
  let g : B ⟶ cokernel f := e ≫ cokernel.π f
  have hc : (coprod.desc f e) ≫ cokernel.π f = pr ≫ g := by
    apply coprod.hom_ext <;> simp [pr, g]
  have hp : p ≫ g = 0 := by
    calc
      p ≫ g = (kernel.ι θ ≫ α.hom) ≫ (pr ≫ g) := by simp [p, Category.assoc]
      _ = (kernel.ι θ ≫ θ) ≫ cokernel.π f := by
        rw [← hc]
        simp only [θ, Category.assoc]
      _ = 0 := by simp
  have : Epi g := by
    dsimp [g]
    infer_instance
  have H : IsColimit (CokernelCofork.ofπ g hp) := by
    apply CokernelCofork.IsColimit.ofπ' g hp
    intro T t ht
    let h : Q ⟶ T := α.hom ≫ coprod.desc 0 t
    have hpr : coprod.desc 0 t = pr ≫ t := by
      apply coprod.hom_ext <;> simp [pr]
    have hh : kernel.ι θ ≫ h = 0 := by
      dsimp [h, p] at *
      rw [hpr]
      simpa [Category.assoc] using ht
    let w : F ⟶ T := Abelian.epiDesc θ h hh
    have hw : θ ≫ w = h := Abelian.comp_epiDesc θ h hh
    have hfw : f ≫ w = 0 := by
      simpa only [θ, h, Category.assoc, Iso.inv_hom_id_assoc, coprod.inl_desc_assoc,
        coprod.inl_desc] using coprod.inl ≫= α.inv ≫= hw
    have hew : e ≫ w = t := by
      simpa only [θ, h, Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc_assoc,
        coprod.inr_desc] using coprod.inr ≫= α.inv ≫= hw
    refine ⟨cokernel.desc f w hfw, ?_⟩
    simp [g, hew]
  exact (cokernelIsCokernel p).coconePointUniqueUpToIso H

private theorem isFinitePresentation_cokernel_free_of_generators
    {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K : SheafOfModules.{u} R} (σ : K.GeneratingSections) [σ.IsFiniteType]
    {I : Type u} [Finite I] (p : K ⟶ SheafOfModules.free I) :
    (cokernel p).IsFinitePresentation := by
  let f : SheafOfModules.free σ.I ⟶ SheafOfModules.free I := σ.π ≫ p
  let g : SheafOfModules.free I ⟶ cokernel p := cokernel.π p
  have H : f ≫ g = 0 := by simp [f, g]
  have H' : IsColimit (CokernelCofork.ofπ g H) := by
    apply isCokernelEpiComp (c := CokernelCofork.ofπ (cokernel.π p) (cokernel.condition p))
      (cokernelIsCokernel p) σ.π
    rfl
  let P := SheafOfModules.presentationOfIsCokernelFree f g H H'
  have : P.IsFinite := ⟨⟨inferInstanceAs (Finite I)⟩, ⟨inferInstanceAs (Finite σ.I)⟩⟩
  exact SliceFinite.isFinitePresentation_of_presentation P

private theorem isFinitePresentation_cokernel_finiteType_to_free
    {C : Type u} [Category.{u} C] [HasPullbacks C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {K : SheafOfModules.{u} R} [K.IsFiniteType]
    {I : Type u} [Finite I] (p : K ⟶ SheafOfModules.free I) :
    (cokernel p).IsFinitePresentation := by
  classical
  obtain ⟨q, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData K
  refine (isFinitePresentation_iff_exists_cover_isFinitePresentation (cokernel p)).2
    ⟨_, q.X, q.coversTop, fun i ↦ ?_⟩
  let T := SheafOfModules.pushforward (𝟙 (R.over (q.X i)))
  let e : SheafOfModules.free I (R := R.over (q.X i)) ≅
      T.obj (SheafOfModules.free I (R := R)) :=
    SheafOfModules.mapFreeIso T I (Iso.refl _)
  let p' : T.obj K ⟶ SheafOfModules.free I (R := R.over (q.X i)) :=
    T.map p ≫ e.inv
  have : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType i
  let _ : HasBinaryProducts (Over (q.X i)) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  have : (cokernel p').IsFinitePresentation :=
    isFinitePresentation_cokernel_free_of_generators (q.generators i) p'
  let z : (cokernel p).over (q.X i) ≅ cokernel p' :=
    (PreservesCokernel.iso T p).trans <|
      cokernel.mapIso (T.map p) p' (Iso.refl _) e.symm (by simp [p'])
  exact (SheafOfModules.isFinitePresentation (R.over (q.X i))).prop_of_iso z.symm inferInstance

private theorem isFinitePresentation_cokernel_of_presentation
    {C : Type u} [Category.{u} C] [HasPullbacks C] [HasBinaryProducts C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
    [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X Y Z, HasSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
    [∀ X Y Z, (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (P : F.Presentation) [P.IsFinite]
    [G.IsFiniteType] (φ : G ⟶ F) :
    (cokernel φ).IsFinitePresentation := by
  classical
  obtain ⟨q, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData G
  refine (isFinitePresentation_iff_exists_cover_isFinitePresentation (cokernel φ)).2
    ⟨_, q.X, q.coversTop, fun i ↦ ?_⟩
  let T := SheafOfModules.pushforward (𝟙 (R.over (q.X i)))
  let P' : (T.obj F).Presentation := P.map T (Iso.refl _)
  have : P'.IsFinite := presentation_map_isFinite T (Iso.refl _) P
  let _ : HasBinaryProducts (Over (q.X i)) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let _ : ∀ (V : Over (q.X i)) (Z : Over V), PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor ((R.over (q.X i)).over V) Z) := fun V _ ↦
    let : HasBinaryProducts (Over V) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    inferInstance
  have : (T.obj F).IsFinitePresentation :=
    SliceFinite.isFinitePresentation_of_presentation (C := Over (q.X i))
      (Rs := R.over (q.X i)) (M := T.obj F) P'
  let σ := q.generators i
  have : σ.IsFiniteType := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType i
  let f : SheafOfModules.free σ.I ⟶ T.obj F := σ.π ≫ T.map φ
  let e : SheafOfModules.free P'.generators.I ⟶ T.obj F := P'.generators.π
  let α : SheafOfModules.free (R := R.over (q.X i)) (σ.I ⊕ P'.generators.I) ≅
      SheafOfModules.free (R := R.over (q.X i)) σ.I ⨿
        SheafOfModules.free (R := R.over (q.X i)) P'.generators.I :=
    (SheafOfModules.freeSumIso (R := R.over (q.X i)) σ.I P'.generators.I).symm
  let θ := α.hom ≫ coprod.desc f e
  have : Epi (coprod.desc f e) := epi_of_epi_fac (coprod.inr_desc f e)
  have : Epi θ := epi_comp α.hom (coprod.desc f e)
  have : (kernel θ).IsFiniteType :=
    LocalKernel.kernel_isFiniteType_of_epi_from_finite_free θ
  let p : kernel θ ⟶ SheafOfModules.free (R := R.over (q.X i)) P'.generators.I :=
    kernel.ι θ ≫ α.hom ≫ coprod.desc 0 (𝟙 _)
  have : (cokernel p).IsFinitePresentation :=
    isFinitePresentation_cokernel_finiteType_to_free (p := p)
  let z : cokernel p ≅ T.obj (cokernel φ) :=
    (cokernel_kernel_projection_iso f e α).trans <|
      (cokernelEpiComp σ.π (T.map φ)).trans (PreservesCokernel.iso T φ).symm
  exact (SheafOfModules.isFinitePresentation (R.over (q.X i))).prop_of_iso z inferInstance

/-- The cokernel of a morphism from a finite type sheaf of modules to a finitely presented sheaf
of modules is finitely presented. -/
@[stacks 0H96, instance]
theorem isFinitePresentation_cokernel {F G : SheafOfModules.{u} R} (φ : G ⟶ F)
    [F.IsFinitePresentation] [G.IsFiniteType] :
    (cokernel φ).IsFinitePresentation := by
  classical
  obtain ⟨q, _⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  refine (isFinitePresentation_iff_exists_cover_isFinitePresentation (cokernel φ)).2
    ⟨_, q.X, q.coversTop, fun i ↦ ?_⟩
  let T := SheafOfModules.pushforward (𝟙 (R.over (q.X i)))
  let φ' : T.obj G ⟶ T.obj F := T.map φ
  have : (T.obj G).IsFiniteType := isFiniteType_over_of_isFiniteType (q.X i)
  have : (cokernel φ').IsFinitePresentation :=
    isFinitePresentation_cokernel_of_presentation (q.presentation i) φ'
  let z : cokernel φ' ≅ T.obj (cokernel φ) := (PreservesCokernel.iso T φ).symm
  exact (SheafOfModules.isFinitePresentation (R.over (q.X i))).prop_of_iso z inferInstance

end Stacks.SheafOfModules

end
