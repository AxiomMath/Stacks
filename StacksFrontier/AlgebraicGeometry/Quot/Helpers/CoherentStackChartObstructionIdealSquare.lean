module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartObstructionNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentIdentification
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare

/-!
# The deformation data of `Coh_{X/B}` over a chart, from the ideal-square compatibility

Let `x = (Spec A, ℱ)` be an object of `Coh_{X/B}` over a chart, with `Y` final and `X → B` flat.
The obstruction classes `o(A' → A) ∈ Ext²_{X_A}(ℱ, ℱ ⊗ f^*Ĩ)` of Stacks 08VW, part (1)
(`AlgebraicGeometry.Space.CoherentSituation.chartObstruction`) are functorial along a surjection
`A₁' → A₂'` of square-zero thickenings of `A` (Stacks 0CYE) as soon as the map
`λ : f̃₁^*t̃₁^*𝒥̃₁ ⟶ f̃₂^*t̃₂^*𝒥̃₂` of the pulled-back ideals of the relative squares
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`) satisfies the ideal-square
compatibility at the test maps `Spec A ⊂ Spec Aₖ'` and `Spec A₂' ⟶ Spec A₁'`
(`AlgebraicGeometry.Space.CoherentSituation.TestRelativeIdealSquareCompatible`). With the
naturality of the tangent identification
(`AlgebraicGeometry.Space.CoherentSituation.chartTangentEquiv`) this gives the deformation data
`AlgebraicGeometry.Space.CoherentSituation.ChartObstructionData`.

## Main definitions

* `CoherentSituation.TestRelativeIdealSquareCompatible`: the ideal-square compatibility of `λ`
  at the test maps of a morphism of square-zero thickenings.

## Main results

* `CoherentSituation.relativeSquareIdealMap_thickeningTestMap`: `λ` at the test maps, in the
  spelling of `CoherentSituation.extGroupMap_obstructionTransport`.
* `CoherentSituation.extGroupMap_chartObstructionStd_of_relativeIdealSquare`: along a surjection
  of square-zero thickenings satisfying the ideal-square compatibility, the map `I₁ ⟶ I₂` carries
  `o(A₁' → A)` to `o(A₂' → A)`.
* `CoherentSituation.nonempty_chartObstructionData_of_relativeIdealSquare`: the deformation data
  of `x` exists, given the naturality of the tangent identification and the ideal-square
  compatibility at the test maps of surjections.

## Implementation notes

`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` and
`AlgebraicGeometry.Space.CoherentSituation.extGroupMap_obstructionTransport` carry different
instance proofs for the sheaf compositions of the small étale sites; the kernel comparison of the
two spellings of `λ` needs `maxHeartbeats 400000` (300000 does not suffice).

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation.Artin
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **The ideal-square compatibility at the test maps of a morphism of square-zero thickenings**:
for `f : A₁' → A₂'` over `A`, the map `λ` of the pulled-back ideals of the relative squares of
`Spec A ⊂ Spec A₁'` and `Spec A ⊂ Spec A₂'` is compatible with `Spec A₂' ⟶ Spec A₁'`. -/
abbrev TestRelativeIdealSquareCompatible (hY : IsTerminal D.Y) (hflat : IsFlat B S hS D.f.hom)
    {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
    {x : CoherentObject D}
    (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {T₁ : SquareZeroThickening A B S hS toS hA A₁} {T₂ : SquareZeroThickening A B S hS toS hA A₂}
    (f : SquareZeroThickening.Hom T₁ T₂) : Prop :=
  RelativeIdealSquareCompatible (D.thickeningTestMap hY x hx T₁) (D.thickeningTestMap hY x hx T₂)
    (D.thickeningTestSchemeMap hY f)
    (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂)
    (D.isFlat_projection_of_isFlat hflat _) (D.isFlat_projection_of_isFlat hflat _)
    (relativeSquareIdealMap (D.thickeningTestMap hY x hx T₁) (D.thickeningTestMap hY x hx T₂)
      (D.thickeningTestSchemeMap hY f)
      (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f)
      (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
      (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))

variable {D} (hY : IsTerminal D.Y) (hflat : IsFlat B S hS D.f.hom)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]

set_option maxHeartbeats 400000 in
-- The kernel comparison of the two spellings of `λ` (different instance proofs); 300000 fails.
/-- **`λ` at the test maps of a morphism of square-zero thickenings**, in the spelling of
`AlgebraicGeometry.Space.CoherentSituation.extGroupMap_obstructionTransport`. -/
theorem relativeSquareIdealMap_thickeningTestMap
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {T₁ : SquareZeroThickening A B S hS toS hA A₁} {T₂ : SquareZeroThickening A B S hS toS hA A₂}
    (f : SquareZeroThickening.Hom T₁ T₂) :
    relativeSquareIdealMap (D.thickeningTestMap hY x hx T₁) (D.thickeningTestMap hY x hx T₂)
      (D.thickeningTestSchemeMap hY f)
      (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f)
      (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
      (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂) =
      (relativeSquareTestIdealIso hY hx T₁).hom ≫
        ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).map
          (thickeningIdealMap (D.thickeningTestMap hY x hx T₁).left
            (D.thickeningTestMap hY x hx T₂).left (D.thickeningTestSchemeMap hY f).left
            (left_comp_left_eq_of_comp_eq (D.thickeningTestSchemeMap hY f)
              (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f))
            (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₁)
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
            (isFirstOrderThickening_range_yoneda_map B S hS _
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁))
            (isIso_toRange_testSchemeMap (D.thickeningTestMap hY x hx T₂)
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
            (isFirstOrderThickening_range_yoneda_map B S hS _
              (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂)) ≫
        (relativeSquareTestIdealIso hY hx T₂).inv := by
  unfold relativeSquareIdealMap relativeSquareTestIdealIso
    QuotientSituation.testSchemeBasePullbackIdeal Deformation.ToposThickening.basePullbackIdeal
    QuotientSituation.testSchemeFirstOrderThickening
  with_reducible rfl

/-- **The functoriality of the obstruction classes over a chart** (Stacks 0CYE at the test maps):
along a surjection `f : A₁' → A₂'` of square-zero thickenings of `A`, the map `I₁ ⟶ I₂` carries
`o(A₁' → A)` to `o(A₂' → A)`, given the ideal-square compatibility of `λ` at the test maps. -/
theorem extGroupMap_chartObstructionStd_of_relativeIdealSquare
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    {T₁ : SquareZeroThickening A B S hS toS hA A₁} {T₂ : SquareZeroThickening A B S hS toS hA A₂}
    (f : SquareZeroThickening.Hom T₁ T₂) (hf : Function.Surjective f.ringHom)
    (H : D.TestRelativeIdealSquareCompatible hY hflat hx f) :
    D.extGroupMap x (D.chartRingEquiv x hx) f.kernelMap 2 (D.chartObstructionStd hY hflat hx T₁) =
      D.chartObstructionStd hY hflat hx T₂ := by
  let : ∀ {A' : Type u} [CommRing A'] (T : SquareZeroThickening A B S hS toS hA A'),
      HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx T))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O))) :=
    fun _ => HasExt.standard _
  let : ∀ {A' : Type u} [CommRing A'] (T : SquareZeroThickening A B S hS toS hA A'),
      HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS
      (D.relativeSquareSituation.space (D.thickeningTestScheme hY T))).O)) :=
    fun _ => HasExt.standard _
  let := HasExt.standard (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)
  let : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  let : EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (EnoughInjectives (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  have e₁ := extGroupMap_obstructionTransport hY hx f
    (thickeningObstructionOnBase.{u + 1, u + 1} (D.thickeningTestMap hY x hx T₁)
      (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
      (D.isFlat_projection_of_isFlat hflat _))
  have e₂ := thickeningObstructionOnBase_eq_comp_of_idealSquareCompatible.{u + 1, u + 1}
    (D.thickeningTestMap hY x hx T₁) (D.thickeningTestMap hY x hx T₂)
    (D.thickeningTestSchemeMap hY f)
    (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY f)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₁)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx T₂)
    (isFirstOrderThickening_thickeningTestSchemeMap hY f hf)
    (D.isFlat_projection_of_isFlat hflat _) (D.isFlat_projection_of_isFlat hflat _) _ H
  have e₃ : ∀ {A' : Type u} [CommRing A'] (T : SquareZeroThickening A B S hS toS hA A'),
      D.chartObstructionStd hY hflat hx T =
      (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) T.kernel 2).symm
        ((thickeningObstructionOnBase.{u + 1, u + 1} (D.thickeningTestMap hY x hx T)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx T)
          (D.isFlat_projection_of_isFlat hflat _)).comp
          (Abelian.Ext.mk₀ (chartObstructionCoefficientIso hY hx T).hom) (add_zero 2)) :=
    fun _ => rfl
  have hlam := relativeSquareIdealMap_thickeningTestMap hY hx f
  rw [hlam] at e₂
  rw [e₃ T₁, e₃ T₂, e₂]
  exact e₁


variable (hRS : SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2)

/-- **The deformation data of an object of `Coh_{X/B}` over a chart**, with `X → B` flat, from
the naturality of the tangent identification
(`AlgebraicGeometry.Space.CoherentSituation.chartTangentEquiv`) along surjections of modules and
the ideal-square compatibility of `λ` at the test maps of surjections of square-zero
thickenings. -/
theorem nonempty_chartObstructionData_of_relativeIdealSquare
    (hτ : ∀ {M N : SiteModule A B} (f : M ⟶ N), Function.Surjective f.hom →
      ∀ (t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
        hRS).functor.obj M),
      chartTangentEquiv hY hx N hflat hRS ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p
        x hx (coherentCFG D).2 hRS).functor.map f t) =
        D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1 (chartTangentEquiv hY hx M hflat hRS t))
    (hH : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
      (T₁ : SquareZeroThickening A B S hS toS hA A₁) (T₂ : SquareZeroThickening A B S hS toS hA A₂)
      (f : SquareZeroThickening.Hom T₁ T₂), Function.Surjective f.ringHom →
        D.TestRelativeIdealSquareCompatible hY hflat hx f) :
    Nonempty (D.ChartObstructionData toS hA x hx hRS) :=
  D.nonempty_chartObstructionData hY hflat hx hRS (fun M => chartTangentEquiv hY hx M hflat hRS) hτ
    (by
      intro A₁ A₂ _ _ T₁ T₂ f hf
      exact extGroupMap_chartObstructionStd_of_relativeIdealSquare hY hflat hx f hf
        (hH A₁ A₂ T₁ T₂ f hf))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] in
/-- The map `A[M] → A[N]` of a surjection of modules `M ⟶ N` is surjective. -/
theorem surjective_squareZeroModuleThickeningHom_ringHom {M N : SiteModule A B} (f : M ⟶ N)
    (hf : Function.Surjective f.hom) :
    Function.Surjective (squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS) (hA := hA)
      f).ringHom := fun z => by
  obtain ⟨m, hm⟩ := hf z.snd
  exact ⟨TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr m,
    TrivSqZeroExt.ext (by simp [squareZeroModuleThickeningHom])
      (by simpa [squareZeroModuleThickeningHom] using hm)⟩

end AlgebraicGeometry.Space.CoherentSituation

end
