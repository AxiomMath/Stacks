module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.Algebra.Homology.BifunctorLinear
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedLinear
public import StacksFrontier.CategoryTheory.Functor.Derived.Linear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-!
# Linearity of the derived functors of schemes over a ring

Let `R` be a commutative ring and let `f : X ⟶ Y` be a morphism of schemes over `Spec R`. The
categories of `𝒪_X`- and `𝒪_Y`-modules are `R`-linear (`AlgebraicGeometry.modulesLinear`), hence
so are their derived categories. This file shows that the derived direct image `Rf_*` and the
derived pullback `Lf^*` are `R`-linear functors.

Both are total derived functors of `R`-linear functors along the localization of the homotopy
category at the quasi-isomorphisms: `Rf_*` is the right derived functor of `f_*` and `Lf^*` the
left derived functor of `f^*`, read on the homotopy category and composed with the localization.
The underived functors are `R`-linear (`AlgebraicGeometry.over_pushforward_linear`,
`AlgebraicGeometry.over_pullback_linear`), the induced functors on homotopy categories are
`R`-linear, and a derived functor of an `R`-linear functor is `R`-linear
(`CategoryTheory.Functor.linear_of_isRightDerivedFunctor`,
`CategoryTheory.Functor.linear_of_isLeftDerivedFunctor`).

## Main results

* `AlgebraicGeometry.derivedPushforward_linear`: `Rf_*` is `R`-linear.
* `AlgebraicGeometry.derivedPullback_linear`: `Lf^*` is `R`-linear.
* `AlgebraicGeometry.derivedTensor_flip_obj_linear`: `- ⊗^𝐋 K` is `R`-linear.
* `AlgebraicGeometry.fourierMukai_linear`: the Fourier-Mukai functor `Φ_M` of a kernel on
  `A ×_R B` is `R`-linear.
* `AlgebraicGeometry.isPerfect_fourierMukai_obj`: for `A ⟶ Spec R` flat, proper and of finite
  presentation and `B` Noetherian, `Φ_M` of a perfect kernel carries perfect objects to perfect
  objects; `AlgebraicGeometry.perfectFourierMukaiOver` is the induced `R`-linear exact functor
  `D_perf(𝒪_A) ⥤ D_perf(𝒪_B)`.

## Implementation notes

Everything is read at `CategoryTheory.HasDerivedCategory.standard`, the model at which
`AlgebraicGeometry.fourierMukai` is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R] {X Y : Over (Spec (.of R))} (f : X ⟶ Y)

/-- **The derived direct image along a morphism of schemes over `Spec R` is `R`-linear.** -/
theorem derivedPushforward_linear :
    letI : Linear R (SheafOfModules (structureSheafRing X.left.toRingedSpace)) :=
      modulesLinear R X
    letI : Linear R (SheafOfModules (structureSheafRing Y.left.toRingedSpace)) :=
      modulesLinear R Y
    (derivedPushforward f.left.toLRSHom.toShHom).Linear R := by
  let : Linear R (SheafOfModules (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear R X
  let : Linear R (SheafOfModules (structureSheafRing Y.left.toRingedSpace)) :=
    modulesLinear R Y
  have : (RingedSpaceModuleAdjunction.modulePushforward f.left.toLRSHom.toShHom).Linear R :=
    over_pushforward_linear R f
  exact Functor.linear_of_isRightDerivedFunctor R
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (derivedPushforward f.left.toLRSHom.toShHom)
    ((pushforwardToDerivedCategory f.left.toLRSHom.toShHom).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))

/-- **The derived pullback along a morphism of schemes over `Spec R` is `R`-linear.** -/
theorem derivedPullback_linear :
    letI : Linear R (SheafOfModules (structureSheafRing X.left.toRingedSpace)) :=
      modulesLinear R X
    letI : Linear R (SheafOfModules (structureSheafRing Y.left.toRingedSpace)) :=
      modulesLinear R Y
    (derivedPullback f.left.toLRSHom.toShHom).Linear R := by
  let : Linear R (SheafOfModules (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear R X
  let : Linear R (SheafOfModules (structureSheafRing Y.left.toRingedSpace)) :=
    modulesLinear R Y
  have : (RingedSpaceModuleAdjunction.modulePullback f.left.toLRSHom.toShHom).Linear R :=
    over_pullback_linear R f
  exact Functor.linear_of_isLeftDerivedFunctor R
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (derivedPullback f.left.toLRSHom.toShHom)
    ((pullbackOnHomotopy f.left.toLRSHom.toShHom).totalLeftDerivedCounit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))

/-! ### The derived tensor product -/

section Tensor

variable (Z : Over (Spec (.of R)))

/-- **Tensoring on the right with a fixed module sheaf on an `R`-scheme is `R`-linear**: it is
isomorphic to tensoring on the left (`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`), which
is `R`-linear by `AlgebraicGeometry.tensorLeft_linear`. -/
theorem sheafTensor_flip_obj_linear (M : SheafOfModules.{u} (ringSheaf Z.left)) :
    letI := modulesLinear R Z
    (show Z.left.Modules ⥤ Z.left.Modules from
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Z.left.presheaf, Z.left.IsSheaf⟩).flip.obj M).Linear R := by
  let := modulesLinear R Z
  have := tensorLeft_linear R Z M
  exact Functor.linear_of_iso _
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding
      (⟨Z.left.presheaf, Z.left.IsSheaf⟩ :
        Sheaf (Opens.grothendieckTopology Z.left) CommRingCat)).app
        (show SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
          (⟨Z.left.presheaf, Z.left.IsSheaf⟩ : Sheaf (Opens.grothendieckTopology Z.left)
            CommRingCat)) from M))

/-- **The derived tensor product with a fixed object of `D(𝒪_Z)`, `- ⊗^𝐋 K`, is `R`-linear**,
for a scheme `Z` over `Spec R`. Replacing `K` by a K-flat complex `L`, the functor `- ⊗^𝐋 L` is
the functor induced on the derived category by the total tensor complex `Tot(- ⊗ L)`, through
the K-flat comparison of [Stacks, Tag 06YU] on the right; that total complex is `R`-linear in its
first variable because the tensor product of modules is, and a functor induced along a linear
localization is linear exactly when the functor it is induced by is
(`CategoryTheory.Localization.functor_linear_iff`). -/
theorem derivedTensor_flip_obj_linear (K : DerivedCategory Z.left.Modules) :
    letI : Linear R (Stacks.DerivedTensor.RingedSite.Modules Z.left.toRingedSpace.sheaf) :=
      modulesLinear R Z
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      Z.left.toRingedSpace.sheaf).flip.obj K).Linear R := by
  let : Linear R (Stacks.DerivedTensor.RingedSite.Modules Z.left.toRingedSpace.sheaf) :=
    modulesLinear R Z
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Z.left.toRingedSpace.sheaf
  obtain ⟨L, p, hL, -, hp, -⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution
    Z.left.toRingedSpace.sheaf (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let e : DerivedCategory.Q.obj L ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have : ∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Z.left.toRingedSpace.sheaf).flip.obj M).Linear R :=
    fun M => sheafTensor_flip_obj_linear R Z M
  let F := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    Z.left.toRingedSpace.sheaf).map₂HomologicalComplex (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj L ⋙ DerivedCategory.Q
  have := HomologicalComplex.linear_map₂HomologicalComplex_flip_obj R
    (c₁ := ComplexShape.up ℤ) (c₂ := ComplexShape.up ℤ)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.left.toRingedSpace.sheaf)
    (ComplexShape.up ℤ) L
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) F
      (T.tensor.flip.obj (DerivedCategory.Q.obj L)) :=
    ⟨NatIso.ofComponents (fun K' => T.comparisonRight K' L hL) (fun {K' K''} f => by
      have h := T.comparisonRight_naturality f (𝟙 L) hL hL
      simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
      exact h)⟩
  have : (T.tensor.flip.obj (DerivedCategory.Q.obj L)).Linear R :=
    (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) R F
      (T.tensor.flip.obj (DerivedCategory.Q.obj L))).1 inferInstance
  exact Functor.linear_of_iso _ (T.tensor.flip.mapIso e)

end Tensor

/-! ### The Fourier-Mukai functor -/

/-- The fibre product `A ×_R B` of two schemes over `Spec R`, as a scheme over `Spec R`. -/
abbrev overPullback (A B : Over (Spec (.of R))) : Over (Spec (.of R)) :=
  Over.mk (pullback.fst A.hom B.hom ≫ A.hom)

/-- **The Fourier-Mukai functor of a kernel on `A ×_R B` is `R`-linear**, for schemes `A` and
`B` over `Spec R`: it is the composite of the derived pullback along the first projection, the
derived tensor product with the kernel and the derived direct image along the second projection,
each of which is `R`-linear. -/
theorem fourierMukai_linear (A B : Over (Spec (.of R)))
    (M : DerivedCategory (pullback A.hom B.hom).Modules) :
    letI : Linear R A.left.Modules := modulesLinear R A
    letI : Linear R B.left.Modules := modulesLinear R B
    (fourierMukai A.hom B.hom M).Linear R := by
  let : Linear R A.left.Modules := modulesLinear R A
  let : Linear R B.left.Modules := modulesLinear R B
  let : Linear R (pullback A.hom B.hom).Modules := modulesLinear R (overPullback R A B)
  have h₁ : (fourierMukaiPullback A.hom B.hom).Linear R := derivedPullback_linear R
    (Over.homMk (pullback.fst A.hom B.hom) rfl : overPullback R A B ⟶ A)
  have h₃ : (fourierMukaiPushforward A.hom B.hom).Linear R := derivedPushforward_linear R
    (Over.homMk (pullback.snd A.hom B.hom) pullback.condition.symm : overPullback R A B ⟶ B)
  have h₂ : (fourierMukaiTensor A.hom B.hom M).Linear R :=
    derivedTensor_flip_obj_linear R (overPullback R A B) M
  exact Functor.instLinearComp (F := fourierMukaiPullback A.hom B.hom)
    (G := fourierMukaiTensor A.hom B.hom M ⋙ fourierMukaiPushforward A.hom B.hom)

/-! ### The induced functor on perfect complexes -/

section Perfect

open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

/-- **A Fourier-Mukai functor with perfect kernel preserves perfect objects**, for a first factor
flat, proper and of finite presentation and a Noetherian second factor: `L pr_1^*E` is perfect,
so is its derived tensor product with the kernel ([Stacks, Tag 09J5]), and `pr₂`, a base change of
the first factor, is flat, proper and of finite presentation, so [Stacks, Tag 0B6G] applies. -/
theorem isPerfect_fourierMukai_obj {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsNoetherian Y]
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    {M : DerivedCategory (pullback f g).Modules}
    (hM : IsPerfect (X := (pullback f g).toRingedSpace) M)
    {E : DerivedCategory X.Modules} (hE : IsPerfect (X := X.toRingedSpace) E) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g M).obj E) := by
  have i1 : Flat (pullback.snd f g) := inferInstance
  have i2 : IsProper (pullback.snd f g) := inferInstance
  have i3 : LocallyOfFinitePresentation (pullback.snd f g) := inferInstance
  have h1 : IsPerfect (X := (pullback f g).toRingedSpace) ((fourierMukaiPullback f g).obj E) :=
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ E hE
  have h2 := isPerfect_dtenR _ _ h1 hM
  exact isPerfect_dpush_of_perfect_of_isProper (pullback.snd f g) _ h2

variable (A B : Over (Spec (.of R))) [Flat A.hom] [IsProper A.hom]
  [LocallyOfFinitePresentation A.hom] [IsNoetherian B.left]
  {M : DerivedCategory (pullback A.hom B.hom).Modules}
  (hM : IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) M)

/-- **The Fourier-Mukai functor `Φ_M : D_perf(𝒪_A) ⥤ D_perf(𝒪_B)`** of a perfect kernel, for `A`
flat, proper and of finite presentation over `Spec R` and `B` Noetherian. -/
abbrev perfectFourierMukaiOver : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left :=
  fourierMukaiOn A.hom B.hom M _ _ (fun E => isPerfect_fourierMukai_obj A.hom B.hom hM E.property)

/-- The Fourier-Mukai functor on perfect complexes is `R`-linear. -/
theorem perfectFourierMukaiOver_linear :
    letI : Linear R A.left.Modules := modulesLinear R A
    letI : Linear R B.left.Modules := modulesLinear R B
    (perfectFourierMukaiOver R A B hM).Linear R := by
  let : Linear R A.left.Modules := modulesLinear R A
  let : Linear R B.left.Modules := modulesLinear R B
  have := fourierMukai_linear R A B M
  exact ⟨fun {E E'} φ r => (ObjectProperty.ι _).map_injective (by
    show (fourierMukai A.hom B.hom M).map ((ObjectProperty.ι _).map (r • φ)) =
      (ObjectProperty.ι _).map (r • (perfectFourierMukaiOver R A B hM).map φ)
    rw [Functor.map_smul, Functor.map_smul, Functor.map_smul]
    rfl)⟩

end Perfect

end AlgebraicGeometry
