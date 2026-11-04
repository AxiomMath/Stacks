module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionCover
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionGlueData

/-!
# The glued functor of Gabriel–Rosenberg reconstruction

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence. In [Stacks, Tag 0GPJ] a quasi-compact open
`U i ⊆ X` is matched with an open `V i ⊆ Y` and a functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_{V i})`. When the
`U i` cover `X` and the `V i` are affine, these local functors glue to a single functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.exists_gluedQuasicoherentFunctor_restrictIso`: if the `U i` cover `X` and
  the `V i` are affine, there is a functor `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` whose restriction to each
  `V i` is isomorphic to the local functor `AlgebraicGeometry.ReconstructionGlue.chartFunctor`.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The glued functor -/

section Glue

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  {ι : Type u} (U : ι → X.Opens) [∀ i, CompactSpace (U i).toScheme] (V : ι → Y.Opens)
  (Z : ι → Set X) (T : ι → Set Y)
  (hcorr : ∀ (i : ι) (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory),
    quasicoherentSupportedOn X (Z i) E ↔ quasicoherentSupportedOn Y (T i) (e.functor.obj E))
  (hUZ : ∀ i, (U i : Set X) = (Z i)ᶜ) (hVT : ∀ i, (V i : Set Y) = (T i)ᶜ)
  (hV : ∀ i, IsCompact (V i : Set Y))

include hcorr hUZ hVT hV

/-- **The local functors of [Stacks, Tag 0GPJ] glue to a single functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`.** If the quasi-compact opens `U i` cover `X` and the matched opens
`V i` are affine, there is a functor `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` whose restriction to each `V i`
is isomorphic to the local functor `AlgebraicGeometry.ReconstructionGlue.chartFunctor e U V i`. -/
theorem exists_gluedQuasicoherentFunctor_restrictIso (hUcover : IsOpenCover U)
    (hVaff : ∀ i, IsAffineOpen (V i)) :
    ∃ F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory,
      ∀ i, Nonempty ((F ⋙ (Stacks.AlgebraicGeometry.ModuleNatTransGlue.quasicoherent Y).ι) ⋙
        Scheme.Modules.restrictFunctor ((V i).ι) ≅ ReconstructionGlue.chartFunctor e U V i) :=
  have hU : TopologicalSpace.IsOpenCover fun i => ((V i).ι).opensRange :=
    isOpenCover_opensRange_of_supportedCorrespondence e U V Z T hcorr hUZ hVT hUcover
  ⟨ReconstructionGlue.gluedQuasicoherentFunctor e U V Z T hcorr hUZ hVT hV hU hVaff,
    fun i => ⟨ReconstructionGlue.gluedRestrictIso e U V Z T hcorr hUZ hVT hV hU i⟩⟩

end Glue

end AlgebraicGeometry

end
