module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct image along an affine morphism computes the derived direct image

For an affine morphism of schemes `f : X ⟶ Y`, a complex of quasi-coherent `𝒪_X`-modules
computes its own derived direct image: `f_* K = Rf_* K`.

No acyclicity hypothesis is needed, because affineness supplies it. The higher direct images of
a quasi-coherent module along an affine morphism vanish ([Stacks, Tag 01XC]), so every
quasi-coherent module is right acyclic for `f_*`, and [Stacks, Tag 0G9N] applies to the complex.

## Main results

* `AlgebraicGeometry.rightAcyclic_pushforward_of_isAffineHom`: a quasi-coherent module is right
  acyclic for direct image along an affine morphism.
* `AlgebraicGeometry.isIso_pushforwardToRightDerived_of_isAffine`: a complex of quasi-coherent
  modules computes the right derived direct image along an affine morphism.

## Implementation notes

The equality in the source is expressed by `CategoryTheory.Functor.ComputesRightDerived`: the
right derived direct image is defined at the complex, and the canonical map from its termwise
direct image to that value is an isomorphism. This records the canonical character of the
identification without choosing a global derived functor.

The target derived category is an arbitrary model `[HasDerivedCategory Y.Modules]`, while
[Stacks, Tag 0G9N] and [Stacks, Tag 01XC] are stated in the standard one. The two are
identified by the uniqueness of localizations, which is why the proof carries a transported copy
`RFstd`, `αstd` of the chosen right derived functor.

## References

* [Stacks Project, Tag 0G9R](https://stacks.math.columbia.edu/tag/0G9R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A quasi-coherent module is right acyclic for direct image along an affine morphism.** The
higher direct images of a quasi-coherent module along an affine morphism vanish
([Stacks, Tag 01XC]), and direct image is left exact, so the acyclicity criterion applies. -/
@[ega "II 5.2.2" "a ⇒ c, a ⇒ c'", ega "III 1.3.2"]
theorem rightAcyclic_pushforward_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pushforward f).rightAcyclic M := by
  have hfin : PreservesFiniteLimits (Scheme.Modules.pushforward f) := inferInstance
  refine (((Scheme.Modules.pushforward f).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    M).2 hfin).mpr fun i hi => ?_
  exact Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f M i hi

end Standard

/-- **Stacks Project, Tag 0G9R.** Let `f : X ⟶ Y` be an affine morphism of schemes and let `K`
be a complex of quasi-coherent `𝒪_X`-modules. Then `f_* K = Rf_* K`: the right derived direct
image is defined at `K` and the canonical map from the termwise direct image to it is an
isomorphism. -/
@[stacks 0G9R]
theorem isIso_pushforwardToRightDerived_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory Y.Modules]
    (K : HomologicalComplex X.Modules (ComplexShape.up ℤ))
    (hK : ∀ i, (K.X i).IsQuasicoherent) :
    ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).ComputesRightDerived
        (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K) := by
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  let G := (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh (C := Y.Modules)
  let W := HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
  let Q := HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh (C := X.Modules)
  obtain ⟨hG, hGiso⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      G (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)
  let : G.HasPointwiseRightDerivedFunctor W := hG
  let RF := G.totalRightDerived L W
  let α := G.totalRightDerivedUnit L W
  let Qhg := DerivedCategory.Qh (C := Y.Modules)
  let P := (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)
  let : HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _
  let Qhs := DerivedCategory.Qh (C := Y.Modules)
  let E := Localization.uniq Qhg Qhs (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))
  let Gstd := P ⋙ Qhs
  let eG : G ⋙ E.functor ≅ Gstd :=
    Functor.associator P Qhg E.functor ≪≫
      Functor.isoWhiskerLeft P (Localization.compUniqFunctor Qhg Qhs
        (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)))
  let RFstd := RF ⋙ E.functor
  let αtrans := Functor.whiskerRight α E.functor ≫ (Functor.associator L RF E.functor).hom
  have htrans : RFstd.IsRightDerivedFunctor αtrans W := by
    dsimp [RFstd, αtrans]
    infer_instance
  let eα := Functor.associator L RF E.functor
  let αstd : Gstd ⟶ L ⋙ RFstd := eG.symm.hom ≫ αtrans
  have hcomm : αtrans ≫ Functor.whiskerLeft L (Iso.refl RFstd).hom = eG.hom ≫ αstd := by
    change αtrans ≫ Functor.whiskerLeft L (𝟙 RFstd) = eG.hom ≫ αstd
    rw [Functor.whiskerLeft_id']
    simp [αstd]
  have hkanstd : RFstd.IsLeftKanExtension αstd :=
    (Functor.isLeftKanExtension_iff_of_iso₂ αtrans αstd eG (Iso.refl RFstd) hcomm).mp
      ((Functor.isRightDerivedFunctor_iff_isLeftKanExtension RFstd αtrans W).mp htrans)
  have : RFstd.IsRightDerivedFunctor αstd W :=
    (Functor.isRightDerivedFunctor_iff_isLeftKanExtension RFstd αstd W).mpr hkanstd
  have hacyclic : ∀ n : ℤ, (Scheme.Modules.pushforward f).rightAcyclic (K.X n) := fun n =>
    have := hK n
    rightAcyclic_pushforward_of_isAffineHom f (K.X n)
  have hα : IsIso (α.app (Q.obj K)) := by
    have : IsSeparated f := IsSeparated.of_isAffineHom f
    have hcomp : IsIso (eG.symm.hom.app (Q.obj K) ≫
        E.functor.map (α.app (Q.obj K)) ≫ eα.hom.app (Q.obj K)) :=
      isIso_to_rightDerived_of_termwise_acyclic f K hK hacyclic RFstd αstd
    have : IsIso (E.functor.map (α.app (Q.obj K))) :=
      (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hcomp)
    exact isIso_of_fully_faithful E.functor _
  refine (Functor.computesRightDerived_iff_isIso_app G L RF W α (Q.obj K) ?_).2 hα
  intro Z
  obtain ⟨K', rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  refine ⟨Q.obj ((Stacks.Injectives.kInjectiveResolutionFunctor X.Modules).obj K'),
    Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K'), ?_, ?_⟩
  · change HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
      (Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K'))
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso X.Modules K'
  · exact hGiso L RF α _ inferInstance

end AlgebraicGeometry

end
