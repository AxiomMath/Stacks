module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleTargetChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.RingTheory.Flat.AdicFiltration

/-!
# Flatness over an affine Noetherian base above `V(I)`, on the étale charts

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `X` be an algebraic space locally
of finite presentation over `S = Spec A`, with a module `F` which is quasi-coherent and of finite
type on the étale scheme charts.  This file proves that if, at every point `u` of an étale scheme
chart `U` of `X` lying over `V(I)`, the module stalk `M = (F|_U)_u` has `M / IⁿM` flat over
`A / Iⁿ` for every `n ≥ 1`, then the locus where `F` is flat over `S` — which is open by
Stacks 05WV — contains the inverse image of `V(I)` under `X → S`.

This is the body of the proof of Stacks 08VP: the source reduces to an affine chart and applies
Stacks 0523 there, which is what is done here, chart by chart.  The statement of Stacks 08VP
itself, whose hypothesis is flatness of the pullback `F_n` of `F` to `X_n = S_n ×_S X` over
`S_n = Spec (A / Iⁿ)`, is
`AlgebraicGeometry.Space.preimage_zeroLocus_subset_flatLocus_of_isFlatOver_adicFibre` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAdicThickeningsFibre.lean`, which reads that
hypothesis on the charts and concludes by the result below.

## Main definitions

* `AlgebraicGeometry.baseRingStalkHom`: for a scheme over `Spec A`, the canonical homomorphism
  from `A` to the local ring at a point, through which the base ring acts on every stalk.
* `AlgebraicGeometry.Space.chartToAffineBase`: the structure morphism of an étale scheme chart
  of an algebraic space over `Spec A`, as a morphism of schemes to `Spec A`.
* `AlgebraicGeometry.Space.affineBaseChartDiagram`: the commuting square of étale scheme charts
  formed by a chart of `X`, the base `Spec A` as a chart of itself, and that structure morphism.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_flat_quotient_pow`: the affine step of the source's proof,
  for a scheme over `Spec A`.  If the local ring `M = F_x` of a module of finite type satisfies
  that `M/IⁿM` is flat over `A/Iⁿ` for every `n ≥ 1`, and `x` lies over `V(I)`, then `F` is flat
  over `Spec A` at `x`.
* `AlgebraicGeometry.Space.mem_flatLocus_of_flat_quotient_pow`: the same conclusion at a point
  of an étale scheme chart of an algebraic space over `Spec A`.
* `AlgebraicGeometry.Space.preimage_zeroLocus_subset_flatLocus`: the flat locus of `F` over
  `Spec A` contains the inverse image of `V(I)` under `X → Spec A`, under the chartwise
  hypothesis above.

## Implementation notes

**The hypothesis is asked only above `V(I)`.**  The affine step uses the stalk at a single point
lying over `V(I)`, so that is all the hypothesis asks.  Away from `V(I)` the quotient `M / IⁿM`
vanishes anyway, `I` generating the unit ideal of the local ring there.

**Coherence of `F`** is read as quasi-coherence and finite type on the étale scheme charts, which
is the convention of `AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`
of Stacks 05WV and of Stacks 0DLR in
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFiniteTypeModuleLocus.lean`.  Finite type on charts is
what gives the chart stalks their finiteness, `Stacks.StalkFiniteType.finite_stalk`, and
quasi-coherence on charts is what makes the flat locus independent of the chart of the base, so
that the square of charts the proof uses may be taken to have `Spec A` itself as its chart of
the base.  Both follow from coherence in the sense of Stacks 07UA, which is how the statement of
Stacks 08VP supplies them.

**Why the affine step needs no further input.**  Over `Spec A` the local ring of the base at the
image point is the localisation `A_𝔭`, so flatness over it is flatness over `A` for a module on
which `A` acts through `A_𝔭`; that is `Module.flat_iff_of_isLocalization`.  Flatness over `A`
itself is Stacks 0523, `Module.Flat.of_flat_quotient_pow`, applied with the Noetherian local
ring `𝒪_{U, u}` as the intermediate ring and the stalk as its own localisation at the maximal
ideal.  Noetherianity of `𝒪_{U, u}` comes from `A` by
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, and `I · 𝒪_{U, u}` lies in the
maximal ideal exactly because `u` lies over `V(I)`.  No étale local ring and no geometric point
occurs.

The module universe is the universe of the structure rings, as it must be for
`AlgebraicGeometry.Space.restrictToChart` to land in the modules of a chart, which is where the
flat locus of Stacks 0DLR is stated.

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### The affine step: a scheme over `Spec A` -/

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-- **The base ring acting on a local ring of a scheme over `Spec A`.**  For `g : X ⟶ Spec A`
and `x` a point of `X`, the composite of the germ map `A ⟶ 𝒪_{Spec A, g x}` with the stalk map
of `g`. -/
def baseRingStalkHom (g : X ⟶ Spec (.of A)) (x : X) :
    CommRingCat.of A ⟶ X.presheaf.stalk x :=
  StructureSheaf.toStalk A (g.base x) ≫ g.stalkMap x

/-- **The affine step of Stacks 08VP.**  Let `A` be Noetherian, let `I ⊆ A` be an ideal, let
`g : X ⟶ Spec A` be locally of finite type and let `F` be an `𝒪_X`-module of finite type.  If
`x` is a point of `X` lying over `V(I)` and the stalk `M = F_x`, an `A`-module through
`AlgebraicGeometry.baseRingStalkHom`, has `M/IⁿM` flat over `A/Iⁿ` for every `n ≥ 1`, then `F`
is flat over `Spec A` at `x` in the sense of Stacks 08KT.

This is the case the source reduces to by passing to an étale covering, and the ring-theoretic
input is Stacks 0523. -/
theorem isFlatOverAt_of_flat_quotient_pow [IsNoetherianRing A] (I : Ideal A)
    (g : X ⟶ Spec (.of A)) [LocallyOfFiniteType g] (F : X.Modules) [F.IsFiniteType] (x : X)
    (hx : I ≤ (g.base x).asIdeal)
    (hflat : ∀ n : ℕ,
      letI : Module A (F.presheaf.stalk x) :=
        Module.compHom _ (baseRingStalkHom g x).hom
      Module.Flat (A ⧸ I ^ (n + 1))
        (F.presheaf.stalk x ⧸ (I ^ (n + 1) • (⊤ : Submodule A (F.presheaf.stalk x))))) :
    IsFlatOverAt g.toLRSHom.toShHom F x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  let : Algebra A (X.presheaf.stalk x) := (baseRingStalkHom g x).hom.toAlgebra
  let : Module A (F.presheaf.stalk x) := Module.compHom _ (baseRingStalkHom g x).hom
  have : IsScalarTower A (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  -- The base ring `A` acts on the local ring `A_𝔭` of the base at the image point.
  have := (g.base x).isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk (g.base x)) :=
    StructureSheaf.stalkAlgebra A (g.base x)
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (g.base x)) (g.base x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (g.base x)
  -- `x` lies over `V(I)`, so the image of `I` lies in the maximal ideal of `𝒪_{X, x}`.
  have hmax : I.map (algebraMap A (X.presheaf.stalk x)) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 : algebraMap A ((Spec (.of A)).presheaf.stalk (g.base x)) a ∈
        IsLocalRing.maximalIdeal ((Spec (.of A)).presheaf.stalk (g.base x)) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a).2 (hx ha)
    have h2 := IsLocalRing.map_maximalIdeal_le (g.stalkMap x).hom
      (Ideal.mem_map_of_mem (g.stalkMap x).hom h1)
    exact h2
  -- Stacks 0523, with `𝒪_{X, x}` as the intermediate ring and the stalk as its own
  -- localisation at the maximal ideal.
  have hA : Module.Flat A (F.presheaf.stalk x) := by
    let : IsLocalization.AtPrime (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
      IsLocalization.self fun _ hy => IsLocalRing.notMem_maximalIdeal.mp hy
    let : IsLocalizedModule.AtPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (LinearMap.id : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) := by
      change IsLocalizedModule (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).primeCompl
        (LinearMap.id : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x)
      exact isLocalizedModule_id (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).primeCompl
        (F.presheaf.stalk x) (X.presheaf.stalk x)
    exact Module.Flat.of_flat_quotient_pow I (F.presheaf.stalk x) hflat
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) hmax (F.presheaf.stalk x) LinearMap.id
  -- Flatness over `A` is flatness over the local ring `A_𝔭` of the base at the image point.
  let : Module ((Spec (.of A)).presheaf.stalk (g.base x)) (F.presheaf.stalk x) :=
    Module.compHom _ (g.stalkMap x).hom
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk (g.base x)) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  change Module.Flat ((Spec (.of A)).presheaf.stalk (g.base x)) (F.presheaf.stalk x)
  rw [Module.flat_iff_of_isLocalization ((Spec (.of A)).presheaf.stalk (g.base x))
    (g.base x).asIdeal.primeCompl]
  exact hA

namespace Space

/-! ### The global statement over `Spec A` -/

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}

/-- **The structure morphism of an étale scheme chart to the affine base.**  Every object of the
big fppf category over `Spec A` comes with a morphism to `Spec A`; this is that morphism for the
chart scheme of an étale chart. -/
def chartToAffineBase (U : SmallEtale B (Spec (.of A)) hA X) :
    etaleChartScheme B (Spec (.of A)) hA U ⟶ Spec (.of A) :=
  (BigFppfOver.toScheme B (Spec (.of A)) hA).map
    (Over.homMk U.obj.left.hom : U.obj.left ⟶ baseObject A B hA)

/-- **The square of charts over the base itself.**  The base is an étale chart of itself
(`AlgebraicGeometry.Space.selfChart`), and the structure morphism of a chart of `X` makes a
commuting square of étale scheme charts over the structure morphism of `X`.  The square commutes
because `Spec A` is the terminal object of the big fppf category over itself, so there is only
one morphism of presheaves into the presheaf it represents. -/
@[reducible]
def affineBaseChartDiagram (f : X ⟶ yoneda.obj (baseObject A B hA))
    (U : SmallEtale B (Spec (.of A)) hA X) :
    ChartDiagram B (Spec (.of A)) hA X (yoneda.obj (baseObject A B hA)) f where
  U := U
  V := selfChart B (Spec (.of A)) hA (baseObject A B hA)
  g := Over.homMk U.obj.left.hom
  comm := by
    ext W s
    exact Limits.IsTerminal.hom_ext Over.mkIdTerminal _ _

variable (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **Flatness above `V(I)` at a point of an étale scheme chart.**  Let `A` be Noetherian and
`X` locally of finite presentation over `Spec A`, with `F` quasi-coherent and of finite type on
the charts.  A point `u` of an étale scheme chart `U` of `X` whose image in `Spec A` lies in
`V(I)`, and whose module stalk `M` has `M / I^{n+1} M` flat over `A / I^{n+1}` for every `n`,
determines a point of the flat locus of `F` over `Spec A`.

Flatness is tested on the square of charts `AlgebraicGeometry.Space.affineBaseChartDiagram`, whose
chart of the base is `Spec A` itself; that this is no loss is
`AlgebraicGeometry.Space.flatLocus_restrictToChart_eq`, which needs quasi-coherence of the
restriction of `F` to `U`. -/
theorem mem_flatLocus_of_flat_quotient_pow [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA))
    (hf : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX)
    (hqc : IsQuasicoherentOnCharts B (Spec (.of A)) hA hX F)
    (hft : IsFiniteTypeOnCharts B (Spec (.of A)) hA hX F)
    (U : SmallEtale B (Spec (.of A)) hA X) (u : etaleChartScheme B (Spec (.of A)) hA U)
    (hu : I ≤ ((chartToAffineBase A B hA U).base u).asIdeal)
    (hflat : ∀ n : ℕ,
      letI : Module A ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u) :=
        Module.compHom _ (baseRingStalkHom (chartToAffineBase A B hA U) u).hom
      Module.Flat (A ⧸ I ^ (n + 1))
        ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u ⧸
          (I ^ (n + 1) • (⊤ : Submodule A
            ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u))))) :
    pointOfEtaleChart B (Spec (.of A)) hA U u ∈ flatLocus B (Spec (.of A)) hA hX f F := by
  refine ⟨affineBaseChartDiagram A B hA f U, u, rfl, ?_⟩
  have : LocallyOfFinitePresentation (chartToAffineBase A B hA U) :=
    locallyOfFinitePresentation_chartDiagram B (Spec (.of A)) hA hf
      (affineBaseChartDiagram A B hA f U)
  have : LocallyOfFiniteType (chartToAffineBase A B hA U) := inferInstance
  have := hqc U
  have := hft U
  exact isFlatOverAt_of_flat_quotient_pow I (chartToAffineBase A B hA U)
    (chartModule B (Spec (.of A)) hA hX F U) u hu hflat

/-- **The flat locus contains the inverse image of `V(I)`, under a chartwise hypothesis.**  Let
`A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `X` be an algebraic space locally of
finite presentation over `S = Spec A`, with an `𝒪_X`-module `F` which is quasi-coherent and of
finite type on the étale scheme charts.  If at every point `u` of an étale scheme chart `U` of
`X` lying over `V(I)` the module stalk `M = (F|_U)_u` has `M / I^{n+1} M` flat over
`A / I^{n+1}` for every `n`, then the locus where `F` is flat over `S` contains the inverse image
of `V(I)` under `X → S`.

The locus is `AlgebraicGeometry.Space.flatLocus`, and it is open by Stacks 05WV,
`AlgebraicGeometry.Space.isOpen_flatLocus_of_isFinitePresentationOnCharts`.  This is the step of
the proof of Stacks 08VP after the reduction to the charts; Stacks 08VP itself is
`AlgebraicGeometry.Space.preimage_zeroLocus_subset_flatLocus_of_isFlatOver_adicFibre`. -/
theorem preimage_zeroLocus_subset_flatLocus [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA))
    (hf : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX)
    (hqc : IsQuasicoherentOnCharts B (Spec (.of A)) hA hX F)
    (hft : IsFiniteTypeOnCharts B (Spec (.of A)) hA hX F)
    (hflat : ∀ (U : SmallEtale B (Spec (.of A)) hA X)
      (u : etaleChartScheme B (Spec (.of A)) hA U),
      I ≤ ((chartToAffineBase A B hA U).base u).asIdeal → ∀ n : ℕ,
      letI : Module A ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u) :=
        Module.compHom _ (baseRingStalkHom (chartToAffineBase A B hA U) u).hom
      Module.Flat (A ⧸ I ^ (n + 1))
        ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u ⧸
          (I ^ (n + 1) • (⊤ : Submodule A
            ((chartModule B (Spec (.of A)) hA hX F U).presheaf.stalk u))))) :
    (fun x => pointsToScheme B (Spec (.of A)) hA (baseObject A B hA)
        (pointsMap B (Spec (.of A)) hA X f x)) ⁻¹'
      PrimeSpectrum.zeroLocus (I : Set A) ⊆
      flatLocus B (Spec (.of A)) hA hX f F := by
  intro x hx
  obtain ⟨d, u, hdu⟩ := exists_chartDiagram_pointOfEtaleChart B (Spec (.of A)) hA hX
    (isAlgebraicSpace_yoneda B (Spec (.of A)) hA (baseObject A B hA)) f x
  subst hdu
  -- the image of `u` in `Spec A` is the image of the point of `|X|`, so it lies in `V(I)`
  have himg : pointsToScheme B (Spec (.of A)) hA (baseObject A B hA)
      (pointsMap B (Spec (.of A)) hA X f (pointOfEtaleChart B (Spec (.of A)) hA d.U u)) =
      (chartToAffineBase A B hA d.U).base u := by
    rw [← pointOfEtaleChart_map_g B (Spec (.of A)) hA (affineBaseChartDiagram A B hA f d.U) u]
    change pointsToScheme B (Spec (.of A)) hA (baseObject A B hA)
        (pointsMap B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA))
          (𝟙 (yoneda.obj (baseObject A B hA)))
          ((pointsEquivScheme B (Spec (.of A)) hA (baseObject A B hA)).symm
            ((chartToAffineBase A B hA d.U).base u))) = (chartToAffineBase A B hA d.U).base u
    rw [pointsMap_id]
    exact (pointsEquivScheme B (Spec (.of A)) hA (baseObject A B hA)).apply_symm_apply _
  have hu : I ≤ ((chartToAffineBase A B hA d.U).base u).asIdeal := by
    have h2 : (I : Set A) ⊆ (pointsToScheme B (Spec (.of A)) hA (baseObject A B hA)
        (pointsMap B (Spec (.of A)) hA X f
          (pointOfEtaleChart B (Spec (.of A)) hA d.U u))).asIdeal := hx
    rw [himg] at h2
    exact fun a ha => h2 ha
  exact mem_flatLocus_of_flat_quotient_pow A I B hA hX f hf F hqc hft d.U u hu (hflat d.U u hu)

end Space

end AlgebraicGeometry

end
