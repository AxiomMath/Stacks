module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Dualizing complexes on algebraic spaces (Stacks 0E4X, 0E4Y, 0E4Z)

Let `X` be a locally Noetherian algebraic space over a scheme `S` contained in a big fppf site
`B`, and let `K` be an object of `D_QCoh(𝒪_X)`. Stacks 0E4X calls an object of `D_QCoh` of the
small étale site of a locally Noetherian scheme `U` a dualizing complex when it is `ε^*ω_U` for a
dualizing complex `ω_U` on `U` (Stacks 0A87), `ε^*` being the equivalence of Stacks 071Q. Stacks
0E4Y says that `K|_U` is such a dualizing complex for *every* étale morphism `h_U ⟶ X` with `U` a
scheme exactly when it is one for *one* surjective such morphism, and Stacks 0E4Z defines a
dualizing complex on `X` by these equivalent conditions.

## Main definitions

* `AlgebraicGeometry.Space.IsDualizingOnRepresented` — **Stacks 0E4X**: an object `M` of
  `D(𝒪_{h_U})`, the derived category of the small étale site of the scheme of `U`, is a dualizing
  complex when `M ≅ ε^*ω` for a dualizing complex `ω` on that scheme.
* `AlgebraicGeometry.Space.IsDualizingRestriction` — the restriction `K|_U` of `K` along an étale
  chart `h_U ⟶ X` is a dualizing complex on `U` in that sense.
* `AlgebraicGeometry.Space.IsDualizingComplexOnSpace` — **Stacks 0E4Z**: `K` is a dualizing complex
  on `X` when `K|_U` is one for every étale chart.
* `AlgebraicGeometry.Space.IsDualizingOnChart` and `AlgebraicGeometry.Space.IsDualizingComplex` — an
  earlier presentation of the same notion, through a family of complexes on the Zariski sites of
  the charts standing in for the restrictions of `K`, together with the compatibilities such a
  family of restrictions has. It is kept beside the notion on `D_QCoh(𝒪_X)` for its consumers.

## Main results

* `AlgebraicGeometry.Space.isLocallyNoetherian_of_etaleChart` — the scheme under an étale chart of
  a locally Noetherian algebraic space is locally Noetherian, by Stacks 03E8.
* `AlgebraicGeometry.Space.forall_isDualizingOnChart_iff_exists_surjective` — **Stacks 0E4Y**, both
  implications, for an object `K` of `D_QCoh(𝒪_X)`.

## Implementation notes

**The restriction and `ε^*`.** `K|_U` is the étale pullback of `K` along the chart, on derived
categories (`AlgebraicGeometry.Space.representedChartDerivedRestriction`); the small étale site of
`h_U` is that of the scheme of `U`, and `ε^*` is
`AlgebraicGeometry.Space.representedDerivedAssociatedModule`. Both are in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedAssociatedModuleEtalePullback.lean`, together with
the two facts the proof uses about them: `ε^*` commutes with étale pullback
(`AlgebraicGeometry.Space.representedDerivedAssociatedModulePullbackIso`), and, by Stacks 071Q,
every object with quasi-coherent cohomology is `ε^*` of one (`exists_representedDerivedAssociatedModule_iso`)
while `ε^*` reflects isomorphisms there (`nonempty_iso_of_representedDerivedAssociatedModule_iso`).

**The proof of 0E4Y.** Given a surjective étale chart `φ : h_U ⟶ X` with `K|_U ≅ ε^*ω_U` and an
arbitrary étale chart `ψ : h_V ⟶ X`, the fibre product `h_U ×_X h_V` is represented by an object
`W`, with an étale projection `q : W ⟶ U` and a surjective étale projection `r : W ⟶ V`. Then
`K|_W ≅ ε^*(q^*ω_U)` and `q^*ω_U` is dualizing, by the ascent half of Stacks 0E4N
(`Stacks.Duality.isDualizingComplex_derivedPullback_of_syntomic`). By Stacks 071Q,
`K|_V ≅ ε^*ω_V` for some `ω_V` with quasi-coherent cohomology; then `ε^*(r^*ω_V) ≅ K|_W`, so
`r^*ω_V ≅ q^*ω_U` because `ε^*` reflects isomorphisms, and `ω_V` is dualizing by the descent half
of Stacks 0E4N along the flat surjection `r`
(`Stacks.Duality.isDualizingComplex_of_isDualizingComplex_derivedPullback`).

The chart `ψ` is relatively representable because the diagonal of `X` is, so the fibre product
`h_U ×_X h_V` is represented by an object `W` of the site; the projection `W ⟶ U` is étale as a
represented base change of `ψ`, the projection `W ⟶ V` is surjective and étale as a represented
base change of `φ`, and `W ⟶ X` is again an étale chart by Stacks 03EC. Local Noetherianity of
`U`, `V` and `W` is the hypothesis `hN` read on those charts through Stacks 03E8.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0E4N](https://stacks.math.columbia.edu/tag/0E4N)
* [Stacks Project, Tag 0E4X](https://stacks.math.columbia.edu/tag/0E4X)
* [Stacks Project, Tag 0E4Y](https://stacks.math.columbia.edu/tag/0E4Y)
* [Stacks Project, Tag 0E4Z](https://stacks.math.columbia.edu/tag/0E4Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback AlgebraicGeometry.pullback_additive

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The scheme under an étale chart of an algebraic space whose charts are locally Noetherian
is itself locally Noetherian. This is the every-chart form of Stacks 03E8 at local
Noetherianity, which is étale local on schemes. -/
theorem isLocallyNoetherian_of_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
  ((exists_atlas_iff_forall_etale B S hS X
    (fun T : Scheme.{u} => IsLocallyNoetherian T) hX).mp hN) U φ hφ

/-- A complex on the scheme under an étale chart `φ : h_U ⟶ X` of a locally Noetherian
algebraic space `X` is a *dualizing complex* when it is one in the sense of Stacks 0A87. The
local Noetherianity of the chart scheme comes from that of `X` by Stacks 03E8. -/
def IsDualizingOnChart (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (M : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules) : Prop :=
  letI := isLocallyNoetherian_of_etaleChart B S hS X hX hN U φ hφ
  Stacks.Duality.IsDualizingComplex M

/-- **The dualizing complexes on the small étale site of a scheme (Stacks 0E4X).** Let `U` be an
object of the big fppf site over `S` whose scheme is locally Noetherian, so that the algebraic
space `h_U` it represents has the small étale site of that scheme as its small étale site. An
object `M` of `D(𝒪_{h_U})` is a *dualizing complex* when `M = ε^*ω` for a dualizing complex `ω`
on the scheme in the sense of Stacks 0A87, where `ε^*` is the associated-module functor on derived
categories, `AlgebraicGeometry.Space.representedDerivedAssociatedModule`. -/
def IsDualizingOnRepresented (U : BigFppfOver B S hS)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) : Prop :=
  ∃ ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules,
    Stacks.Duality.IsDualizingComplex ω ∧
      Nonempty (M ≅ (representedDerivedAssociatedModule B S hS U).obj ω)

/-- The restriction `K|_U` of an object `K` of `D(𝒪_X)` to an étale scheme chart `φ : h_U ⟶ X` of
a locally Noetherian algebraic space is a dualizing complex on `U`, in the sense of Stacks 0E4X
(`AlgebraicGeometry.Space.IsDualizingOnRepresented`). The restriction is the étale pullback of
`K` along the chart, `AlgebraicGeometry.Space.representedChartDerivedRestriction`. -/
def IsDualizingRestriction (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : DerivedCategory (Modules.{u, u} B S hS X hX))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) : Prop :=
  letI := isLocallyNoetherian_of_etaleChart B S hS X hX hN U φ hφ
  IsDualizingOnRepresented B S hS U
    ((representedChartDerivedRestriction B S hS hX U φ (isEtale_of_presheaf_etale B S hS hφ)).obj K)

/-- For an étale chart `ψ : h_V ⟶ X` and a surjective étale chart `φ : h_U ⟶ X`, the fibre
product `U ×_X V` is represented by some `W` with an étale projection `q` to `U` and a surjective
étale projection `r` to `V`, and `W ⟶ X` is an étale chart. -/
private theorem exists_etale_surjective_fibre_product
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ U) (r : W ⟶ V),
      yoneda.map r ≫ ψ = yoneda.map q ≫ φ ∧ Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map r) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map r) ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) (yoneda.map q ≫ φ) := by
  classical
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hψRep : yoneda.relativelyRepresentable ψ :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).mp
      hX.diagonal_representable ψ
  let p := hψRep.fst φ
  let q := hψRep.snd φ
  have hpull := hψRep.isPullback φ
  let r : hψRep.pullback φ ⟶ V := yoneda.preimage p
  have hrMap : yoneda.map r = p := yoneda.map_preimage p
  have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map q) := hψ.property φ p q hpull
  exact ⟨_, q, r, by rw [hrMap]; exact hpull.w, hqEtale,
    hφ.property ψ (yoneda.map q) r (by simpa [hrMap] using hpull.flip),
    hφs.property ψ (yoneda.map q) r (by simpa [hrMap] using hpull.flip),
    etale_comp_of_scheme B S hS q φ hqEtale hφ⟩

/-- The ascent-and-descent step of Stacks 0E4Y: dualizing on a surjective étale chart `h_U ⟶ X`
implies dualizing on every étale chart `h_V ⟶ X`, through `U ×_X V`, by Stacks 0E4N and the
equivalence of Stacks 071Q on the schemes of the three charts. -/
private theorem isDualizingRestriction_of_surjective
    (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X hX)
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hφs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hdual : IsDualizingRestriction B S hS X hX hN K.obj U φ hφ)
    (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X)
    (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ) :
    IsDualizingRestriction B S hS X hX hN K.obj V ψ hψ := by
  classical
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨W, q, r, hw, hqEtale, hrEtale, hrSurj, hχ⟩ :=
    exists_etale_surjective_fibre_product B S hS X hX U φ hφ hφs V ψ hψ
  let _ : IsLocallyNoetherian (T.obj U) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN U φ hφ
  let _ : IsLocallyNoetherian (T.obj V) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN V ψ hψ
  let _ : IsLocallyNoetherian (T.obj W) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN _ _ hχ
  have := hrEtale
  have := hrSurj
  have := hqEtale
  have hqφ : IsEtale B S hS (representedSpaceMap B S hS q).hom :=
    isEtale_schemeSpaceMap B S hS _ q hqEtale
  have hrφ : IsEtale B S hS (representedSpaceMap B S hS r).hom :=
    isEtale_schemeSpaceMap B S hS _ r hrEtale
  have hφE := isEtale_of_presheaf_etale B S hS hφ
  have hψE := isEtale_of_presheaf_etale B S hS hψ
  have hχE := isEtale_of_presheaf_etale B S hS hχ
  have hχE' : IsEtale B S hS (yoneda.map r ≫ ψ) := hw ▸ hχE
  have hres : ∀ (a b : yoneda.obj W ⟶ X) (ha : IsEtale B S hS a)
      (hb : IsEtale B S hS b), a = b →
      Nonempty (representedChartDerivedRestriction B S hS hX _ a ha ≅
        representedChartDerivedRestriction B S hS hX _ b hb) := by
    rintro a _ ha hb rfl
    exact ⟨Iso.refl _⟩
  obtain ⟨ωU, hωU, ⟨eU⟩⟩ := hdual
  -- the restriction to `U ×_X V` through `U`
  have hqcU := Stacks.Duality.isQuasicoherent_homology_of_isDualizingComplex hωU
  let eW₁ := (representedChartDerivedRestrictionCompIso B S hS hX φ hφE q hqφ hχE).app K.obj ≪≫
    (representedDerivedPullback B S hS q hqφ).mapIso eU ≪≫
    (representedDerivedAssociatedModulePullbackIso B S hS q hqφ).app ωU
  have hW : Stacks.Duality.IsDualizingComplex
      ((derivedPullback (T.map q).toLRSHom.toShHom).obj ωU) :=
    Stacks.Duality.isDualizingComplex_derivedPullback_of_syntomic (T.map q)
      (@syntomic_of_etale _ _ (T.map q) hqEtale) ωU hqcU hωU
  -- the restriction to `V`, which lies in `D_QCoh`
  have hKV := derivedQuasicoherent_etaleModulePullback B S hS
    (ObjectProperty.homMk ψ : (⟨yoneda.obj V, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS V⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hψE K.obj K.property
  obtain ⟨ωV, hqcV, ⟨eV⟩⟩ :=
    exists_representedDerivedAssociatedModule_iso B S hS V
      ((representedChartDerivedRestriction B S hS hX V ψ hψE).obj K.obj) hKV
  let eW₂ := (representedChartDerivedRestrictionCompIso B S hS hX ψ hψE r hrφ hχE').app K.obj ≪≫
    (representedDerivedPullback B S hS r hrφ).mapIso eV.symm ≪≫
    (representedDerivedAssociatedModulePullbackIso B S hS r hrφ).app ωV
  obtain ⟨eχ⟩ := hres _ _ hχE' hχE hw
  have hqcW : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      ((derivedPullback (T.map r).toLRSHom.toShHom).obj ωV)).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent _).prop_of_iso
      (((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (Scheme.Modules.pullback (T.map r)) i).app ωV).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso
          ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory (T.map r)).app ωV).symm)
      (Stacks.Modules.isQuasicoherent_pullback (T.map r) _ (hqcV i))
  obtain ⟨e⟩ := nonempty_iso_of_representedDerivedAssociatedModule_iso B S hS _
    _ _ hqcW
    (Stacks.Duality.isQuasicoherent_homology_of_isDualizingComplex hW)
    (eW₂.symm ≪≫ (eχ.app K.obj) ≪≫ eW₁)
  exact ⟨ωV, Stacks.Duality.isDualizingComplex_of_isDualizingComplex_derivedPullback
    (T.map r) ωV hqcV (Stacks.Duality.isDualizingComplex_of_iso e.symm hW), ⟨eV.symm⟩⟩

/-- **Stacks Project, Tag 0E4Y.** Let `X` be a locally Noetherian algebraic space over `S` and
let `K` be an object of `D_QCoh(𝒪_X)`. Then the restriction `K|_U` is a dualizing complex on `U`,
in the sense of Stacks 0E4X, for every étale morphism `h_U ⟶ X` with `U` a scheme if and only if
it is one for some surjective such morphism.

The ascent from `U` to `U ×_X V` and the descent from there to `V` are Stacks 0E4N, applied to the
dualizing complex `ω_U` with `K|_U = ε^*ω_U` and to the complex `ω_V` with `K|_V = ε^*ω_V` that
Stacks 071Q provides; the two pullbacks to `U ×_X V` agree because `ε^*` commutes with étale
pullback and is fully faithful on `D_QCoh`. -/
@[stacks 0E4Y]
theorem forall_isDualizingOnChart_iff_exists_surjective
    (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X hX) :
    (∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
        (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) φ),
        IsDualizingRestriction B S hS X hX hN K.obj U φ hφ) ↔
      ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
        (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) φ),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) φ ∧
          IsDualizingRestriction B S hS X hX hN K.obj U φ hφ := by
  constructor
  · intro h
    obtain ⟨U, φ, hφs, hφe⟩ := hX.exists_atlas
    exact ⟨U, φ, hφe, hφs, h U φ hφe⟩
  · rintro ⟨U, φ, hφ, hφs, hdual⟩ V ψ hψ
    exact isDualizingRestriction_of_surjective B S hS X hX hN K U φ hφ hφs hdual V ψ hψ

/-- **Stacks Project, Tag 0E4Z.** An object of `D_QCoh(𝒪_X)` on a locally Noetherian algebraic
space `X` over `S` is a *dualizing complex* when its restriction to every étale scheme chart of
`X` is a dualizing complex on that chart, in the sense of Stacks 0A87.

This is the chart-family formulation, written before the restriction of an object of `D(𝒪_X)` to
a chart was available: the object is presented by a family `L` of complexes on the Zariski sites
of the charts, `quasicoherent` and `pullback_compat` are what membership in `D_QCoh(𝒪_X)` says
about the family of its restrictions, and `isDualizingOnChart` is the every-chart condition of
Stacks 0E4Y. The notion phrased on an object of `D_QCoh(𝒪_X)` itself is
`AlgebraicGeometry.Space.IsDualizingComplexOnSpace`. -/
@[stacks 0E4Z "the every-chart condition of 0E4Y; the restrictions of K to the etale scheme \
charts of X are the family L"]
structure IsDualizingComplex (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (L : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ →
      DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules) : Prop where
  /-- Every cohomology sheaf of every member of the family is quasi-coherent. -/
  quasicoherent : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ) (i : ℤ),
    ((DerivedCategory.homologyFunctor
      ((BigFppfOver.toScheme B S hS).obj U).Modules i).obj (L U φ hφ)).IsQuasicoherent
  /-- A morphism `a : U ⟶ V` of étale charts identifies `L U φ hφ` with the derived pullback of
  `L V ψ hψ` along `a`. -/
  pullback_compat : ∀ (U V : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (ψ : yoneda.obj V ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) ψ) (a : U ⟶ V), yoneda.map a ≫ ψ = φ →
    Nonempty ((derivedPullback
        ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).obj (L V ψ hψ) ≅
      L U φ hφ)
  /-- The restriction to every étale scheme chart of `X` is a dualizing complex on that chart. -/
  isDualizingOnChart : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ),
    IsDualizingOnChart B S hS X hX hN U φ hφ (L U φ hφ)

/-- A dualizing complex on a locally Noetherian algebraic space is dualizing on some surjective
étale scheme chart, an algebraic space having such a chart. This is the direction of Stacks
0E4Y that needs only the existence of an atlas. -/
theorem IsDualizingComplex.exists_surjective_isDualizingOnChart
    {hX : IsAlgebraicSpace B S hS X}
    {hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)}
    {L : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ →
      DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (hL : IsDualizingComplex B S hS X hX hN L) :
    ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
      (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ ∧
        IsDualizingOnChart B S hS X hX hN U φ hφ (L U φ hφ) := by
  obtain ⟨U, φ, hφs, hφe⟩ := hX.exists_atlas
  exact ⟨U, φ, hφe, hφs, hL.isDualizingOnChart U φ hφe⟩

/-- A family of complexes on the Zariski sites of the étale scheme charts of a locally Noetherian
algebraic space `X`, with the compatibilities of a family of restrictions, which is dualizing on
one surjective étale scheme chart is a dualizing complex on `X` in the chart-family sense of
`AlgebraicGeometry.Space.IsDualizingComplex`. The argument is the one of Stacks 0E4Y: the ascent
and descent of Stacks 0E4N through `U ×_X V`, the family supplying the comparison of the two
pullbacks to `U ×_X V`. -/
theorem IsDualizingComplex.of_exists_surjective_isDualizingOnChart
    {hX : IsAlgebraicSpace B S hS X}
    {hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T)}
    {L : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ →
      DerivedCategory ((BigFppfOver.toScheme B S hS).obj U).Modules}
    (hLqc : ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
      (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ) (i : ℤ),
      ((DerivedCategory.homologyFunctor
        ((BigFppfOver.toScheme B S hS).obj U).Modules i).obj (L U φ hφ)).IsQuasicoherent)
    (hLres : ∀ (U V : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X) (ψ : yoneda.obj V ⟶ X)
      (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ)
      (hψ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) ψ) (a : U ⟶ V), yoneda.map a ≫ ψ = φ →
      Nonempty ((derivedPullback
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).obj (L V ψ hψ) ≅
        L U φ hφ))
    (h : ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
      (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) φ ∧
        IsDualizingOnChart B S hS X hX hN U φ hφ (L U φ hφ)) :
    IsDualizingComplex B S hS X hX hN L := by
  refine ⟨hLqc, hLres, ?_⟩
  classical
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, φ, hφ, hφs, hdual⟩ := h
  intro V ψ hψ
  obtain ⟨W, q, r, hw, hqEtale, hrEtale, hrSurj, hχ⟩ :=
    exists_etale_surjective_fibre_product B S hS X hX U φ hφ hφs V ψ hψ
  let _ : IsLocallyNoetherian (T.obj U) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN U φ hφ
  let _ : IsLocallyNoetherian (T.obj V) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN V ψ hψ
  let _ : IsLocallyNoetherian (T.obj W) :=
    isLocallyNoetherian_of_etaleChart B S hS X hX hN _ _ hχ
  have := hrEtale
  have := hrSurj
  obtain ⟨eU⟩ := hLres W U (yoneda.map q ≫ φ) φ hχ hφ q rfl
  obtain ⟨eV⟩ := hLres W V (yoneda.map q ≫ φ) ψ hχ hψ r
    hw
  have hW : Stacks.Duality.IsDualizingComplex (L _ _ hχ) :=
    Stacks.Duality.isDualizingComplex_of_iso eU
      (Stacks.Duality.isDualizingComplex_derivedPullback_of_syntomic (T.map q)
        (@syntomic_of_etale _ _ (T.map q) hqEtale) (L U φ hφ) (hLqc U φ hφ) hdual)
  exact Stacks.Duality.isDualizingComplex_of_isDualizingComplex_derivedPullback
    (T.map r) (L V ψ hψ) (hLqc V ψ hψ)
    (Stacks.Duality.isDualizingComplex_of_iso eV.symm hW)

/-- **Stacks Project, Tag 0E4Z.** An object `K` of `D_QCoh(𝒪_X)` on a locally Noetherian algebraic
space `X` over `S` is a *dualizing complex* when it satisfies the equivalent conditions of Stacks
0E4Y: its restriction `K|_U` to every étale morphism `h_U ⟶ X` with `U` a scheme is a dualizing
complex on `U` in the sense of Stacks 0E4X, that is `K|_U = ε^*ω_U` for a dualizing complex `ω_U`
on `U` (`AlgebraicGeometry.Space.IsDualizingRestriction`). By
`AlgebraicGeometry.Space.forall_isDualizingOnChart_iff_exists_surjective` it is enough to ask this
for one surjective such morphism. -/
@[stacks 0E4Z]
def IsDualizingComplexOnSpace (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS X hX) : Prop :=
  ∀ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ),
    IsDualizingRestriction B S hS X hX hN K.obj U φ hφ

end AlgebraicGeometry.Space

end
