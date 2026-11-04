module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealKernelIso
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaSections

/-!
# The projection-formula map at the first-order thickening, on the unit section

Let `(T, J, δ)` be a divided power scheme over a scheme `Y`, let `T'` be the first-order
universal thickening of [Stacks, Tag 07J2] with projection `p₀ : T' ⟶ T`, and let `N` be a sheaf
of `𝒪_T`-modules.  `Crystalline.firstOrderThickeningProjectionFormulaMap` is the comparison
morphism

`Φ_N : N ⊗_{𝒪_T} p₀_* 𝒪_{T'} ⟶ p₀_*(p₀^* N)`

of [Stacks, Tag 0FZE] at `p₀` and `𝒪_{T'}`.  Its source contains the summand `N ⊗_{𝒪_T} 𝒪_T`
cut out by the comorphism `g ↦ (g, 0)` of `p₀`, which is
`Crystalline.firstOrderThickeningInlSheaf`, and this module computes `Φ_N` on it: through the
right unitor it is the unit of `p₀^* ⊣ p₀_*`.  On local sections the identity reads
`x ⊗ r ↦ (r, 0) · p₀^* x`, which at `r = 1` is the normalisation `x ⊗ 1 ↦ p₀^* x`.

## Main results

* `Crystalline.inlSheaf_whiskerRight_comp_projectionFormulaMap` — the identity in the form the
  computation produces, with the two tensor factors in the order
  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` is stated in: the comorphism
  of `p₀` tensored on the right with `N`, followed by the projection-formula morphism and by the
  direct image of the left unitor, is the left unitor followed by the unit of `p₀^* ⊣ p₀_*`.
* `Crystalline.whiskerLeft_inlSheaf_comp_firstOrderThickeningProjectionFormulaMap` — the same
  identity for `Crystalline.firstOrderThickeningProjectionFormulaMap`, whose source has the two
  factors in the other order: the comorphism of `p₀` tensored on the left with `N`, followed by
  that map, is the right unitor followed by the unit of `p₀^* ⊣ p₀_*`.
* `Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient_whiskerLeft_inlSheaf'` —
  the normalisation statement about the comparison of the two middle terms of [Stacks, Tag 07J6]
  that `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison` takes as its
  `hnorm` argument, obtained from the result above through the reduction
  `Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient_whiskerLeft_inlSheaf`.
* `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison_of_isIso` and
  `Crystalline.GlobalCrystallineSituation.firstOrderKernelIsoOfIsIso` — the identification
  `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(i^* : p₀_* F_{T'} ⟶ F_T)` of [Stacks, Tag 07J6] with that
  `hnorm` argument discharged, so that only local quasi-coherence of `F` and the invertibility
  of the comparison map of [Stacks, Tag 07IQ] at `p₀` are left as inputs.

## Implementation notes

The proof has a formal half and a half about sections.  The formal half is the passage between
the two orders of the tensor factors: the braiding is natural
(`CategoryTheory.BraidedCategory.braiding_naturality_right`), and the braiding followed by the
left unitor is the right unitor (`CategoryTheory.braiding_leftUnitor`), so the two statements
above differ by an isomorphism which cancels.

The half about sections is checked on the sheafification-unit images of pure tensors of
sections, which determine a morphism out of a tensor product of sheaves of modules
(`PresheafOfModules.sheafification_hom_ext` together with
`PresheafOfModules.tensorObj_hom_ext`).  Over an open `W` both sides send `r ⊗ x` to
`(r, 0) · p₀^* x`: on the left by the description of a tensor of morphisms on a pure tensor
(`Stacks.RingedSpace.tensorSheaf_map_unit_tmul`), the canonicality clause of the
projection-formula morphism
(`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul`, which is
`a ⊗ b ↦ a ⊗ p₀^* b`) and the left unitor on sections; on the right because the unit of
`p₀^* ⊣ p₀_*` is semilinear, `Stacks.RingedSpace.pullbackUnit_smul`.  The unitors of the
monoidal structure in play have a description on sections only through
`Stacks.RingedSpace.leftUnitor_sheafTensor_eq`, which identifies them with
`Stacks.RingedSpace.tensorSheafUnitLeftIso`; that identification is the only place where the
re-seating of the monoidal structure is visible.

Several spellings of one object occur along the chain — `AlgebraicGeometry.Scheme.Modules.pullback`
against `RingedSpaceModuleAdjunction.modulePullback`, `AlgebraicGeometry.Scheme.ringCatSheaf`
against `Stacks.RingedSpace.structureRingSheaf` — and all of them agree by `rfl`.  Each
intermediate step is therefore stated with the spelling the *next* step needs and proved by
`exact`, which crosses the difference, so that the final `rw` chain matches syntactically.

Nothing in this module carries a `@[stacks]` attribute.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline

attribute [local instance] monoidalCategorySchemeModules braidedCategorySchemeModules

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose TopCat.Sheaf AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Presheaf.IsSheaf

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y) (N : T.scheme.Modules)

/-- **The projection-formula morphism of [Stacks, Tag 0FZE] at `p₀` and `𝒪_{T'}`, read on the
summand cut out by the comorphism `g ↦ (g, 0)` of `p₀`.**  That comorphism tensored on the right
with `N`, followed by the projection-formula morphism
`p₀_* 𝒪_{T'} ⊗ N ⟶ p₀_*(𝒪_{T'} ⊗ p₀^* N)` and by the direct image of the left unitor, is the
left unitor followed by the unit of `p₀^* ⊣ p₀_*`.

On the sheafification-unit image of a pure tensor `r ⊗ x` over an open `W` of `T` both sides are
`(r, 0) · p₀^* x`; the chain is described in the implementation notes of the module. -/
theorem inlSheaf_whiskerRight_comp_projectionFormulaMap :
    (firstOrderThickeningInlSheaf T Y f ▷ N) ≫
        Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
            (firstOrderThickeningProjHom T Y f)
            (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N ≫
          (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).map
            (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom =
      (λ_ N).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (firstOrderThickeningProjHom T Y f)).unit.app N := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun W r x => ?_)
  have hlu : ∀ (Z : Scheme.{u}) (M : Z.Modules), (λ_ M).hom =
      (Stacks.RingedSpace.tensorSheafUnitLeftIso Z.toRingedSpace M).hom := fun _ _ =>
    Stacks.RingedSpace.leftUnitor_sheafTensor_eq _ _
  have a1 : PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f ▷ N).val W
        (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)) (𝟙
            (Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (T.scheme.toRingedSpace).presheaf)
            ((SheafOfModules.unit
            (Stacks.RingedSpace.structureRingSheaf T.scheme.toRingedSpace))).val (N).val)) W
                (r ⊗ₜ x)) =
      PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)) (𝟙
          (Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (T.scheme.toRingedSpace).presheaf)
          (((RingedSpaceModuleAdjunction.modulePushforward
            (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).obj
              (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf))).val
                  (N).val)) W
        (PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f).val W r ⊗ₜ x) := by
    have hmap := Stacks.RingedSpace.tensorSheaf_map_unit_tmul T.scheme.toRingedSpace
      (firstOrderThickeningInlSheaf T Y f) (𝟙 N) W r x
    exact Eq.trans (PresheafOfModules.hom_congr_apply
      (congrArg (fun k => SheafOfModules.Hom.val k)
        ((Stacks.SheafOfModules.Tensor.sheafTensor_map_app T.scheme.toRingedSpace.sheaf
            (firstOrderThickeningInlSheaf T Y f) N).trans
          (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map T.scheme.toRingedSpace.sheaf
            (firstOrderThickeningInlSheaf T Y f) (𝟙 N)).symm)) W _) hmap
  have a2 := Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_unit_tmul
    (firstOrderThickeningProjHom T Y f)
    (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N W
    (PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f).val W r) x
  have a3 : PresheafOfModules.Hom.app
        (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
        (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf
            ((firstOrderThickeningScheme T Y f).toRingedSpace)) (𝟙
            (Stacks.RingedSpace.structureRingSheaf
            ((firstOrderThickeningScheme T Y f).toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O :=
            ((firstOrderThickeningScheme T Y f).toRingedSpace).presheaf) ((SheafOfModules.unit
            (firstOrderThickeningScheme T Y f).ringCatSheaf)).val
            (((RingedSpaceModuleAdjunction.modulePullback
              (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).obj N)).val))
          ((RingedSpaceModuleAdjunction.opensMap
            (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
          (PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f).val W r ⊗ₜ
            Stacks.RingedSpace.pullbackUnit
              (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x)) =
      (show ToType ((Stacks.RingedSpace.structureRingSheaf
            (firstOrderThickeningScheme T Y f).toRingedSpace).obj.obj
          ((RingedSpaceModuleAdjunction.opensMap
            (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)) from
        PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f).val W r) •
        Stacks.RingedSpace.pullbackUnit
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x := by
    rw [hlu]
    exact Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul
      (firstOrderThickeningScheme T Y f).toRingedSpace
      ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)
      ((RingedSpaceModuleAdjunction.opensMap
        (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
      (PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f).val W r)
      (Stacks.RingedSpace.pullbackUnit
        (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W x)
  have a4 := Stacks.RingedSpace.tensorSheafUnitLeftIso_hom_tensorSheafUnit_tmul
    T.scheme.toRingedSpace N W r x
  have a5 := Stacks.RingedSpace.pullbackUnit_smul
    (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W r x
  have hsharp : Stacks.RingedSpace.sharp
        (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom W r =
      PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f).val W r := rfl
  show PresheafOfModules.Hom.app
        (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom.val
        ((RingedSpaceModuleAdjunction.opensMap
          (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom).op.obj W)
        (PresheafOfModules.Hom.app
          (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
            (firstOrderThickeningProjHom T Y f)
            (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N).val W
          (PresheafOfModules.Hom.app (firstOrderThickeningInlSheaf T Y f ▷ N).val W
            (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)) (𝟙
                (Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)).obj)).unit.app
                (PresheafOfModules.tensorObj (O := (T.scheme.toRingedSpace).presheaf)
                ((SheafOfModules.unit
                (Stacks.RingedSpace.structureRingSheaf T.scheme.toRingedSpace))).val (N).val)) W
              (r ⊗ₜ x)))) =
      Stacks.RingedSpace.pullbackUnit
        (firstOrderThickeningProjHom T Y f).toLRSHom.toShHom N W
        (PresheafOfModules.Hom.app (λ_ N).hom.val W
          (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)) (𝟙
              (Stacks.RingedSpace.structureRingSheaf (T.scheme.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (T.scheme.toRingedSpace).presheaf)
              ((SheafOfModules.unit
              (Stacks.RingedSpace.structureRingSheaf T.scheme.toRingedSpace))).val (N).val)) W
                  (r ⊗ₜ x)))
  rw [a1, a2, a3, hlu, a4, a5, hsharp]

/-- **The projection-formula map at the first-order universal thickening, on the summand
`N ⊗_{𝒪_T} 𝒪_T`.**  The comorphism `g ↦ (g, 0)` of `p₀`, tensored on the left with `N` and
followed by `Crystalline.firstOrderThickeningProjectionFormulaMap`, is the right unitor followed
by the unit of `p₀^* ⊣ p₀_*`.

On local sections both sides send the pure tensor `x ⊗ r` to `(r, 0) · p₀^* x`; at `r = 1` this
is the normalisation `x ⊗ 1 ↦ p₀^* x` of the morphism of [Stacks, Tag 0FZE].

`Crystalline.firstOrderThickeningProjectionFormulaMap` begins with the braiding, so this is
`Crystalline.inlSheaf_whiskerRight_comp_projectionFormulaMap` conjugated by it: the braiding is
natural, and the braiding followed by the left unitor is the right unitor. -/
theorem whiskerLeft_inlSheaf_comp_firstOrderThickeningProjectionFormulaMap :
    (N ◁ firstOrderThickeningInlSheaf T Y f) ≫
        firstOrderThickeningProjectionFormulaMap T Y f N =
      (ρ_ N).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction
          (firstOrderThickeningProjHom T Y f)).unit.app N := by
  have hbr : (N ◁ firstOrderThickeningInlSheaf T Y f) ≫
      (β_ N (firstOrderThickeningUnitRestriction T Y f)).hom =
        (β_ N (schemeUnitModule T.scheme)).hom ≫ (firstOrderThickeningInlSheaf T Y f ▷ N) :=
    BraidedCategory.braiding_naturality_right N _
  have hun : (β_ N (schemeUnitModule T.scheme)).hom ≫ (λ_ N).hom = (ρ_ N).hom :=
    braiding_leftUnitor N
  show (N ◁ firstOrderThickeningInlSheaf T Y f) ≫
      (β_ N (firstOrderThickeningUnitRestriction T Y f)).hom ≫
        (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap
            (firstOrderThickeningProjHom T Y f)
            (SheafOfModules.unit (firstOrderThickeningScheme T Y f).ringCatSheaf) N ≫
          (Scheme.Modules.pushforward (firstOrderThickeningProjHom T Y f)).map
            (λ_ ((Scheme.Modules.pullback (firstOrderThickeningProjHom T Y f)).obj N)).hom) = _
  rw [← Category.assoc, hbr, Category.assoc,
    inlSheaf_whiskerRight_comp_projectionFormulaMap T Y f N, ← Category.assoc, hun]

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}
  (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-- **The normalisation statement that
`Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison` takes as its `hnorm`
argument.**  It is the reduction
`Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient_whiskerLeft_inlSheaf` applied
to `Crystalline.whiskerLeft_inlSheaf_comp_firstOrderThickeningProjectionFormulaMap`. -/
theorem firstOrderTensorToAmbient_whiskerLeft_inlSheaf' :
    (Thickening.ambientSchemeModule M A ◁
        firstOrderThickeningInlSheaf A.thickening.target S.S.scheme A.toBase.hom) ≫
          firstOrderTensorToAmbient M A =
      (ρ_ (Thickening.ambientSchemeModule M A)).hom ≫ firstOrderAmbientInclMap M A :=
  firstOrderTensorToAmbient_whiskerLeft_inlSheaf M A
    (whiskerLeft_inlSheaf_comp_firstOrderThickeningProjectionFormulaMap _ _ _ _)

/-- **The identification of [Stacks, Tag 07J6] with the normalisation input removed**: the
canonical morphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ ker(i^* : p₀_* F_{T'} ⟶ F_T)` is an isomorphism for
every `F` whose comparison map of [Stacks, Tag 07IQ] at `p₀`, read between sheaves of modules on
the ambient schemes, is invertible.

This is `Crystalline.GlobalCrystallineSituation.isIso_firstOrderKernelComparison` with its
`hnorm` argument supplied by
`Crystalline.GlobalCrystallineSituation.firstOrderTensorToAmbient_whiskerLeft_inlSheaf'`. -/
theorem isIso_firstOrderKernelComparison_of_isIso
    (hc : IsIso (ambientSchemeCrystalComparison M A)) :
    IsIso (firstOrderKernelComparison M A) :=
  isIso_firstOrderKernelComparison M A hc
    (firstOrderTensorToAmbient_whiskerLeft_inlSheaf' M A)

/-- **The isomorphism `F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(i^*)` of [Stacks, Tag 07J6]**, with the
normalisation input removed; its underlying morphism is the canonical one
`Crystalline.GlobalCrystallineSituation.firstOrderKernelComparison`. -/
def firstOrderKernelIsoOfIsIso
    (hc : IsIso (ambientSchemeCrystalComparison M A)) :
    firstOrderThickeningTensorDifferentials A.thickening.target S.S.scheme A.toBase.hom
        (Thickening.ambientSchemeModule M A) ≅
      firstOrderAmbientKernel M A :=
  firstOrderKernelIso M A hc (firstOrderTensorToAmbient_whiskerLeft_inlSheaf' M A)

/-- The isomorphism of
`Crystalline.GlobalCrystallineSituation.firstOrderKernelIsoOfIsIso` is the canonical
morphism. -/
theorem firstOrderKernelIsoOfIsIso_hom
    (hc : IsIso (ambientSchemeCrystalComparison M A)) :
    (firstOrderKernelIsoOfIsIso M A hc).hom = firstOrderKernelComparison M A := rfl

end GlobalCrystallineSituation

end Crystalline

end

end
