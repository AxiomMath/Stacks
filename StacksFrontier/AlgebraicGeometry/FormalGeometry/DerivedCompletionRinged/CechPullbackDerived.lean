module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionUnitIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulKFlat
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPullbackDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite

/-!
# The derived inverse image of an extended alternating Čech complex

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, let `t_1, …, t_r` be global
sections of `𝒪` and let `g_1, …, g_r` be global sections of `𝒪'` with `g_i = f^♯(t_i)`. Then

`Lf^*Č(𝒪, t_1, …, t_r) ≅ Č(𝒪', g_1, …, g_r)` in `D(𝒪')`.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyLE_extendedAlternatingCech`: the extended alternating
  Čech complex on `r` sections is concentrated in degrees `≤ r`.
* `AlgebraicGeometry.RingedSite.isFlat_extendedAlternatingCech_X`: its terms are flat.
* `AlgebraicGeometry.RingedSite.isKFlat_extendedAlternatingCech`: it is K-flat.
* `AlgebraicGeometry.RingedSite.derivedPullbackExtendedAlternatingCechIso`:
  `Lf^*Č(𝒪, t) ≅ Č(𝒪', g)` in `D(𝒪')`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] hasFiniteBiproducts_sheafOfModules
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

section KFlat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (t : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The extended alternating Čech complex on `r` global sections is concentrated in degrees
`≤ r`. -/
theorem isStrictlyLE_extendedAlternatingCech :
    (extendedAlternatingCech X t).IsStrictlyLE (r : ℤ) :=
  (CochainComplex.isStrictlyLE_iff (extendedAlternatingCech X t) (r : ℤ)).2
    fun _ hi ↦ isZero_extendedAlternatingCech_X_of_lt X t hi

/-- The terms of the extended alternating Čech complex are flat `𝒪`-modules. -/
theorem isFlat_extendedAlternatingCech_X (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((extendedAlternatingCech X t).X i) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.O
    ((HomologicalComplex.eval (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) i).mapIso
      ((colimit.isColimit (koszulPowerSystem X t)).coconePointUniqueUpToIso
        (isColimitKoszulCechComplexCocone X t)))
    (Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X X.O (koszulPowerSystem X t)
      (fun n q ↦ isFlat_of_isFiniteFreeSummand X ((koszulPowerComplex X t n).X q)
        (isFiniteFreeSummand_koszulPowerComplex_X X t n q)) i)

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The extended alternating Čech complex on any global sections `t_1, …, t_r` is K-flat. -/
theorem isKFlat_extendedAlternatingCech :
    Stacks.SheafOfModules.IsKFlat X.O (extendedAlternatingCech X t) :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O (extendedAlternatingCech X t)
    ⟨(r : ℤ), isStrictlyLE_extendedAlternatingCech X t⟩
    (isFlat_extendedAlternatingCech_X X t)

end KFlat

section Derived

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

include hg in
/-- The derived inverse image of the extended alternating Čech complex on the sections
`t_1, …, t_r` is the extended alternating Čech complex on their images `g_1, …, g_r`:
`Lf^*Č(𝒪, t_1, …, t_r) ≅ Č(𝒪', g_1, …, g_r)`. -/
def derivedPullbackExtendedAlternatingCechIso :
    (derivedPullback.{u} f.toRingedToposSiteHom).obj
        (DerivedCategory.Q.obj (extendedAlternatingCech Y t)) ≅
      DerivedCategory.Q.obj (extendedAlternatingCech X g) :=
  Stacks.Sheaves.DerivedPullback.flatPullbackIso f.toRingedToposSiteHom f.isMorphismOfSites
      (extendedAlternatingCech Y t) (isKFlat_extendedAlternatingCech Y t)
      (isFlat_extendedAlternatingCech_X Y t) ≪≫
    DerivedCategory.Q.mapIso (pullbackExtendedAlternatingCechIso f t g hg)

end Derived

end AlgebraicGeometry.RingedSite

end
