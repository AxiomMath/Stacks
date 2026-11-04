module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedSchemeDescentDatum

/-!
# The quasi-coherent module on the underlying scheme of a descent datum of a represented family

Let `f i : T i ⟶ U` be an fpqc covering family of the big fppf category over a scheme `S`, let
`D` be a descent datum for quasi-coherent modules of Stacks 04W3 relative to the family of
representable algebraic spaces it represents, and let
`AlgebraicGeometry.Space.QuasiCoherentDescent.reprSchemeDatum` be its transport to a descent
datum for `AlgebraicGeometry.modulePullbackPseudofunctor` restricted along
`AlgebraicGeometry.BigFppfOver.toScheme`. By the effectivity of fpqc descent for quasi-coherent
modules (Stacks 023T), the readings of `D` on the underlying schemes are the pullbacks of one
quasi-coherent module on the scheme underlying `U`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent`
  `.isEquivalence_restrictDescentData_representedFamily`: restriction of descent data for the
  pullback pseudofunctor along `AlgebraicGeometry.BigFppfOver.toScheme` is an equivalence at a
  family of the big fppf category over `S`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isEffective_iso_reprSchemeDatum` and
  `…_of_isCovering`: the readings of a descent datum of a represented fpqc family on the
  underlying schemes come from an effective quasi-coherent descent datum of the underlying family
  of schemes, hence from one quasi-coherent module on the scheme underlying the target.

## Implementation notes

Since restriction along `AlgebraicGeometry.BigFppfOver.toScheme` is an equivalence,
`reprSchemeDatum` is the restriction of a descent datum for the pullback pseudofunctor over
arbitrary schemes, whose components are quasi-coherent. The conclusion is the effectivity of that
datum, in the sense of `AlgebraicGeometry.QuasicoherentDescentData.IsEffective`.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace QuasiCoherentDescent

section Represented

variable {I : Type v} {U : BigFppfOver B S hS} (T : I → BigFppfOver B S hS)
  (f : ∀ i, T i ⟶ U)

/-- Restriction of descent data for the pullback pseudofunctor along
`AlgebraicGeometry.BigFppfOver.toScheme` is an equivalence at a family of the big fppf category
over `S`. -/
public theorem isEquivalence_restrictDescentData_representedFamily :
    (Pseudofunctor.restrictDescentData modulePullbackPseudofunctor
      (BigFppfOver.toScheme B S hS) f).IsEquivalence :=
  Pseudofunctor.isEquivalence_restrictDescentData modulePullbackPseudofunctor
    (BigFppfOver.toScheme B S hS)
    (fun i j => BigFppfOver.siteFibreProduct B S hS (f i) (f j))
    (fun i j => BigFppfOver.isPullback_map_siteFibreProduct B S hS (f i) (f j))
    (fun i j k => BigFppfOver.siteFibreProduct₃ B S hS (f i) (f j) (f k))
    (fun i j k => (BigFppfOver.siteFibreProduct₃ B S hS (f i) (f j) (f k)).isPullback₂.map
      (BigFppfOver.toScheme B S hS))

variable (D : DescentDatum B S hS (representedFamily B S hS T) (representedFamilyMap B S hS T f))

/-- The readings of a descent datum of a represented fpqc family on the underlying schemes come
from an effective quasi-coherent descent datum of the underlying family of schemes: the
transported datum `AlgebraicGeometry.Space.QuasiCoherentDescent.reprSchemeDatum` is the
restriction of a quasi-coherent descent datum isomorphic to the canonical descent datum of a
quasi-coherent module on the scheme underlying `U`. -/
public theorem exists_isEffective_iso_reprSchemeDatum
    (hcov : (PreZeroHypercover.mk I (fun i => (BigFppfOver.toScheme B S hS).obj (T i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i))).presieve₀ ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ D₀ : QuasicoherentDescentData (fun i => (BigFppfOver.toScheme B S hS).map (f i)),
      D₀.IsEffective ∧ Nonempty ((Pseudofunctor.restrictDescentData
        modulePullbackPseudofunctor (BigFppfOver.toScheme B S hS) f).obj D₀.obj ≅
          reprSchemeDatum B S hS T f D) := by
  have := isEquivalence_restrictDescentData_representedFamily B S hS T f
  obtain ⟨D₁, ⟨e⟩⟩ : ∃ D₁, Nonempty ((Pseudofunctor.restrictDescentData
      modulePullbackPseudofunctor (BigFppfOver.toScheme B S hS) f).obj D₁ ≅
        reprSchemeDatum B S hS T f D) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  have hqc : ∀ i, (D₁.obj i).IsQuasicoherent := fun i =>
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent _)
      (Pseudofunctor.DescentData.objIso e i).symm
      (isQuasicoherent_representedZariskiModule B S hS (U := T i) (D.F i) (D.quasicoherent i))
  exact ⟨⟨D₁, hqc⟩, QuasicoherentDescentData.isEffective_fpqcPrecoverage _ hcov _, ⟨e⟩⟩

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isEffective_iso_reprSchemeDatum`
with its covering hypothesis given by the fpqc condition on the represented family. -/
public theorem exists_isEffective_iso_reprSchemeDatum_of_isCovering
    (hf : Topology.IsCovering .fpqc B S hS (fun i => yoneda.obj (T i))
      (fun i => yoneda.map (f i))) :
    ∃ D₀ : QuasicoherentDescentData (fun i => (BigFppfOver.toScheme B S hS).map (f i)),
      D₀.IsEffective ∧ Nonempty ((Pseudofunctor.restrictDescentData
        modulePullbackPseudofunctor (BigFppfOver.toScheme B S hS) f).obj D₀.obj ≅
          reprSchemeDatum B S hS T f D) :=
  exists_isEffective_iso_reprSchemeDatum B S hS T f D
    (isFpqcCovering_yoneda_of_isCovering B S hS T U f hf)

end Represented

end QuasiCoherentDescent

end AlgebraicGeometry.Space

end
