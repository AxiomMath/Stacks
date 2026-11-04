module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangent
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenVersalityObstruction

/-!
# The deformation data of an object of `Coh_{X/B}` over a chart

This file packages the obstruction classes of Stacks 08VW, part (1), for an object `x` of
`Coh_{X/B}` over a chart (`AlgebraicGeometry.Space.CoherentSituation.chartObstruction`) into the
deformation data `AlgebraicGeometry.Space.CoherentSituation.ChartObstructionData` used by the
second proof of Stacks 08WA, given the tangent identification and the functoriality of the
obstruction classes along surjections of thickenings.

This module is a helper and carries no `@[stacks]` attribute.
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
  (hY : IsTerminal D.Y) (hflat : IsFlat B S hS D.f.hom)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  (hRS : SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2)

/-- The obstruction class of a square-zero thickening, with the standard `Ext` groups. -/
def chartObstructionStd {A' : Type u} [CommRing A']
    (T : Deformation.Artin.SquareZeroThickening A B S hS toS hA A') :
    D.extGroup x (D.chartRingEquiv x hx) T.kernel 2 :=
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx T))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS
      (D.relativeSquareSituation.space (D.thickeningTestScheme hY T))).O))
  haveI := HasExt.standard (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)
  chartObstruction hY hx T hflat

/-- **The deformation data of an object of `Coh_{X/B}` over a chart**, from a tangent
identification natural along surjections and the functoriality of the obstruction classes along
surjections of square-zero thickenings. -/
theorem nonempty_chartObstructionData
    (τ : ∀ M : SiteModule A B,
      ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
        hRS).functor.obj M : Type _) ≃ D.extGroup x (D.chartRingEquiv x hx) M.obj 1)
    (hτ : ∀ {M N : SiteModule A B} (f : M ⟶ N), Function.Surjective f.hom →
      ∀ (t : (tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
        hRS).functor.obj M),
      τ N ((tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx (coherentCFG D).2
        hRS).functor.map f t) = D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1 (τ M t))
    (hob : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
      (T₁ : SquareZeroThickening A B S hS toS hA A₁)
      (T₂ : SquareZeroThickening A B S hS toS hA A₂) (f : SquareZeroThickening.Hom T₁ T₂),
      Function.Surjective f.ringHom →
        D.extGroupMap x (D.chartRingEquiv x hx) f.kernelMap 2
          (D.chartObstructionStd hY hflat hx T₁) = D.chartObstructionStd hY hflat hx T₂) :
    Nonempty (D.ChartObstructionData toS hA x hx hRS) :=
  ⟨{ τ := τ
     τ_natural := hτ
     ob := fun _ _ T => D.chartObstructionStd hY hflat hx T
     ob_eq_zero_iff := fun _ _ T => by
       have := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
         ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
           (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx T))).toToposHom).obj
             (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))
       have := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
         (smallEtaleRingedTopos B S hS
           (D.relativeSquareSituation.space (D.thickeningTestScheme hY T))).O))
       have := HasExt.standard (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)
       exact nonempty_fiber_iff_chartObstruction_eq_zero hY hx T hflat
     ob_natural := hob }⟩

end AlgebraicGeometry.Space.CoherentSituation

end
