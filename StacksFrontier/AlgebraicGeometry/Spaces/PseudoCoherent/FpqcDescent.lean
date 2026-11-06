module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.RepresentedZariski
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullbackComputation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescentKFlat
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
import StacksCore.Tactic.StacksAttribute

/-!
# `m`-pseudo-coherence descends along fpqc coverings of algebraic spaces

Let `{f_i : X_i ⟶ X}` be an fpqc covering of algebraic spaces over a scheme `S`, let `E` be an
object of `D_QCoh(𝒪_X)` and let `m` be an integer. Stacks 0DL1: `E` is `m`-pseudo-coherent if
and only if every derived pullback `Lf_i^*E` is.

`m`-pseudo-coherence is Stacks 08FT on the small étale ringed site of an algebraic space and
`Lf^*` is `AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`, the derived pullback of
Stacks 06YY along the morphism of small étale ringed topoi of Stacks 03G8.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_smallEtaleDerivedModulePullback`: derived
  pullback along any morphism of algebraic spaces preserves `m`-pseudo-coherence of an object of
  `D_QCoh` (Stacks 08H4 for this situation).
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_isFpqcCovering_representable`: the descent
  for an fpqc covering whose members have scheme sources.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_iff_forall_derivedPullback_of_isFpqcCovering`:
  **Stacks 0DL1**.

## The argument

It is the source's. Pseudo-coherence on an algebraic space is local for the étale topology
(`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherent/EtaleLocality.lean`), so it may be checked
on the algebraic spaces `h_V` represented by the étale charts `V`. On `h_V` an object `G` of
`D_QCoh` is `ε^*ω` for `ω ∈ D_QCoh(𝒪_V)` (Stacks 071Q), represented by a K-flat complex `K`, and
`G` is `m`-pseudo-coherent exactly when `K` is, on the scheme `V` (Stacks 08HE,
`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherent/RepresentedZariski.lean`). Derived pullback
along a morphism `h_r` of represented spaces commutes with `ε^*` on such `K`
(`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherent/DerivedPullbackComputation.lean`).

* *Pullback.* For `f : Y ⟶ X` the charts `W` of `Y` whose composite with `f` factors through an
  étale chart `V` of `X` by a morphism `r` of schemes cover `Y` (Stacks 03M0), and there
  `(Lf^*E)|_W ≅ Lr^*(E|_V)`; the case of schemes, Stacks 09U7 (`Lr^*` preserves
  `m`-pseudo-coherence), applies.
* *Descent.* Stacks 0419 refines the covering by members with scheme sources `T_i`, and the
  derived pullbacks to the `T_i` stay `m`-pseudo-coherent by the first point. For a chart `V` of
  `X`, the fibre products `V ×_X T_i` are represented by schemes `W_i` and `{W_i ⟶ V}` is an fpqc
  covering of schemes (Stacks 03MS); the case of schemes, Stacks 09UE, gives
  `m`-pseudo-coherence of `E|_V`.

## References

* [Stacks Project, Lemma 76.54.1 (0DL1)](https://stacks.math.columbia.edu/tag/0DL1)
* [Stacks Project, Lemma 36.12.4 (09UE)](https://stacks.math.columbia.edu/tag/09UE)
* [Stacks Project, Tag 09U7](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 21.45.3 (08H4)](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Lemma 73.9.5 (0419)](https://stacks.math.columbia.edu/tag/0419)
* [Stacks Project, Tag 03MS](https://stacks.math.columbia.edu/tag/03MS)
* [Stacks Project, Lemma 75.4.2 (071Q)](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Lemma 75.13.2 (08HE)](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe d u v

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Pseudo-coherence read on representatives -/

/-- Restriction to a chart is left exact on the small étale ringed site of an algebraic space. -/
local instance overFunctorPreservesFiniteLimits (X : AlgebraicSpaces B S hS)
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction to a chart is right exact on the small étale ringed site of an algebraic
space. -/
local instance overFunctorPreservesFiniteColimits (X : AlgebraicSpaces B S hS)
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FpqcDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An object of `D(𝒪_X)` is `m`-pseudo-coherent exactly when a complex representing it is. -/
private theorem isPseudoCoherentFrom_iff_of_iso {X : AlgebraicSpaces B S hS}
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    {K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ}
    {E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (e : DerivedCategory.Q.obj K ≅ E)
    (m : ℤ) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m ↔
      RingedSite.IsPseudoCoherentComplexFrom.{u + 1, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2) K m :=
  RingedSite.isPseudoCoherentFrom_iff_isPseudoCoherentComplexFrom _ e m

/-- `m`-pseudo-coherence of an object of `D(𝒪_X)` is invariant under isomorphism. -/
private theorem isPseudoCoherentFrom_of_iso {X : AlgebraicSpaces B S hS}
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    {E E' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} {m : ℤ}
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m) (e : E ≅ E') :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E' m :=
  RingedSite.isPseudoCoherentFrom_of_iso _ m h e.symm

/-- **Pseudo-coherence of `ε^*K` on a represented algebraic space is pseudo-coherence of `K` on
its scheme**, for any model of the derived category. -/
theorem isPseudoCoherentFrom_representedAssociatedModule_iff (T : BigFppfOver B S hS)
    [HasDerivedCategory.{d}
      (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))]
    (K : CochainComplex ((BigFppfOver.toScheme B S hS).obj T).Modules ℤ) (m : ℤ) :
    (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherentFrom
        (DerivedCategory.Q.obj (((representedAssociatedModule B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
        m ↔
      RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
        (X := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace) K m :=
  (isPseudoCoherentFrom_iff_of_iso B S hS
    (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) (Iso.refl _) m).trans
    (isPseudoCoherentComplexFrom_representedAssociatedModule_iff B S hS T K m)

/-! The rest of the file uses the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback` of Stacks 06YY and the derived
associated-module functor `AlgebraicGeometry.Space.representedDerivedAssociatedModule` of
Stacks 071Q, which are constructed at the standard derived categories. -/

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

/-- Derived pullbacks along equal morphisms agree. -/
private theorem nonempty_smallEtaleDerivedModulePullback_iso_of_eq {X Y : AlgebraicSpaces B S hS}
    {a b : X ⟶ Y} (h : a = b) (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS a).obj E ≅
      (smallEtaleDerivedModulePullback B S hS b).obj E) := by
  subst h
  exact ⟨Iso.refl _⟩

/-! ### Étale locality, on the derived category -/

/-- **Derived pullback along an étale morphism preserves `m`-pseudo-coherence.** -/
theorem isPseudoCoherentFrom_smallEtaleDerivedModulePullback_of_isEtale
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom
      ((smallEtaleDerivedModulePullback B S hS f).obj E) m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_iso_etaleModulePullback B S hS f hf K
  let e' := e.symm ≪≫ (smallEtaleDerivedModulePullback B S hS f).mapIso eK
  exact (isPseudoCoherentFrom_iff_of_iso B S hS e' m).2
    (isPseudoCoherentComplexFrom_etaleModulePullback B S hS f hf K m hK)

/-- **`m`-pseudo-coherence of an object of `D(𝒪_X)` can be checked on charts.** If every chart
`U` of `X` admits a covering `{V ⟶ U}` such that the derived pullback of `E` to each algebraic
space `V` is `m`-pseudo-coherent, then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_charts {X : AlgebraicSpaces B S hS}
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (m : ℤ)
    (h : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C, ∃ T : Presieve U,
      Sieve.generate T ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U ∧
        ∀ ⦃V : (smallEtaleRingedSite B S hS X.1 X.2).C⦄ (f : V ⟶ U), T f →
          (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1
              (chartSpace B S hS X V).2).IsPseudoCoherentFrom
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m := by
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  refine (isPseudoCoherentFrom_iff_of_iso B S hS eK m).2
    (isPseudoCoherentComplexFrom_of_charts B S hS K m fun U => ?_)
  obtain ⟨T, hT, hdata⟩ := h U
  refine ⟨T, hT, fun V f hf => ?_⟩
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_iso_etaleModulePullback B S hS
    (chartToSpace B S hS X V) (isEtale_chartToSpace B S hS X V) K
  exact (isPseudoCoherentFrom_iff_of_iso B S hS e.symm m).1
    (isPseudoCoherentFrom_of_iso B S hS (hdata f hf)
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).mapIso eK.symm))

/-- Derived pullbacks along morphisms with `a ≫ f = b ≫ g` preserve `m`-pseudo-coherence in the
same way. -/
private theorem isPseudoCoherentFrom_derivedPullback_of_comp_eq {X Y Z W : AlgebraicSpaces B S hS}
    {a : W ⟶ Y} {f : Y ⟶ X} {b : W ⟶ Z} {g : Z ⟶ X} (h : a ≫ f = b ≫ g)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) {m : ℤ}
    (h₁ : (smallEtaleRingedSite B S hS W.1 W.2).IsPseudoCoherentFrom
      ((smallEtaleDerivedModulePullback B S hS b).obj
        ((smallEtaleDerivedModulePullback B S hS g).obj E)) m) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPseudoCoherentFrom
      ((smallEtaleDerivedModulePullback B S hS a).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj E)) m := by
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_iso_of_eq B S hS h.symm E
  exact isPseudoCoherentFrom_of_iso B S hS h₁
    ((((smallEtaleDerivedPullbackData B S hS).compIso b g).app E).symm ≪≫ e ≪≫
      ((smallEtaleDerivedPullbackData B S hS).compIso a f).app E)

/-! ### Represented algebraic spaces -/

/-- An object of `D_QCoh` of a represented algebraic space `h_T` is `ε^*` of a K-flat complex
with flat terms and quasi-coherent cohomology on the scheme `T`: Stacks 071Q followed by a
K-flat resolution (Stacks 06YF). -/
theorem exists_kFlatComplex_representedAssociatedModule_iso (T : BigFppfOver B S hS)
    (G : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (hG : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) G) :
    ∃ K : CochainComplex (SheafOfModules.{u}
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace)) ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex
          ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace.sheaf) (K.X i)) ∧
        (∀ i : ℤ, (K.homology i).IsQuasicoherent) ∧
        Nonempty (DerivedCategory.Q.obj (((representedAssociatedModule B S hS T
          (isAlgebraicSpace_yoneda B S hS T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
            G) := by
  obtain ⟨ω, hω, ⟨eω⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T G hG
  obtain ⟨K, k, hK, hKf, hk, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution
    ((BigFppfOver.toScheme B S hS).obj T).toRingedSpace (DerivedCategory.Q.objPreimage ω)
  have := hk
  let eK : DerivedCategory.Q.obj K ≅ ω :=
    asIso (DerivedCategory.Q.map k) ≪≫ DerivedCategory.Q.objObjPreimageIso ω
  refine ⟨K, hK, hKf, fun i => (SheafOfModules.isQuasicoherent _).prop_of_iso
    (((DerivedCategory.homologyFunctor _ i).mapIso eK).symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app K) (hω i), ⟨?_⟩⟩
  exact ((representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategoryFactors.app K).symm ≪≫
    (representedDerivedAssociatedModule B S hS T).mapIso eK ≪≫ eω

/-- **Derived pullback along a morphism of represented algebraic spaces preserves
`m`-pseudo-coherence of an object of `D_QCoh`.** This is the case of schemes, Stacks 09U7, read on
the small étale sites. -/
theorem isPseudoCoherentFrom_derivedPullback_representedSpaceMap {T' T : BigFppfOver B S hS}
    (q : T' ⟶ T)
    (G : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (hG : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) G) (m : ℤ)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).IsPseudoCoherentFrom G m) :
    haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS q)
    (smallEtaleRingedSite B S hS (yoneda.obj T')
      (isAlgebraicSpace_yoneda B S hS T')).IsPseudoCoherentFrom
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS q)).obj G) m := by
  have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
    (representedSpaceMap B S hS q)
  obtain ⟨K, hK, hKf, -, ⟨eG⟩⟩ := exists_kFlatComplex_representedAssociatedModule_iso B S hS T G hG
  let r := ((BigFppfOver.toScheme B S hS).map q).toLRSHom.toShHom
  have h₁ := (isPseudoCoherentFrom_representedAssociatedModule_iff B S hS T K m).1
    (isPseudoCoherentFrom_of_iso B S hS (X := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
      h eG.symm)
  have h₂ := Scheme.Hom.isPseudoCoherentFrom_derivedPullback ((BigFppfOver.toScheme B S hS).map q)
    (DerivedCategory.Q.obj K) m ⟨K, h₁, ⟨Iso.refl _⟩⟩
  have h₃ := RingedSpace.isPseudoCoherentComplexFrom_of_iso _ m h₂ _
    (Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat r K hK).symm
  have h₄ := (isPseudoCoherentFrom_representedAssociatedModule_iff B S hS T' _ m).2 h₃
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso B S hS q
    K hK hKf
  exact isPseudoCoherentFrom_of_iso B S hS (X := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
    (isPseudoCoherentFrom_of_iso B S hS (X := ⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩)
      h₄ e.symm)
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS q)).mapIso eG)

/-! ### Pullback preserves pseudo-coherence -/

/-- **Derived pullback preserves `m`-pseudo-coherence of an object of `D_QCoh`** (Stacks 08H4 for
the derived pullback along a morphism of algebraic spaces). Let `f : Y ⟶ X` be a morphism of
algebraic spaces and let `E` be an object of `D(𝒪_X)` with quasi-coherent cohomology which is
`m`-pseudo-coherent. Then `Lf^*E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_smallEtaleDerivedModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E)
    (m : ℤ) (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom
      ((smallEtaleDerivedModulePullback B S hS f).obj E) m := by
  have key : ∀ W : (smallEtaleRingedSite B S hS Y.1 Y.2).C, HasAffineChartDiagram B S hS f W →
      (smallEtaleRingedSite B S hS (chartSpace B S hS Y W).1
        (chartSpace B S hS Y W).2).IsPseudoCoherentFrom
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj
            ((smallEtaleDerivedModulePullback B S hS f).obj E)) m := by
    intro W hW
    obtain ⟨-, V, q, hq, -⟩ := hW
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS q)
    have hfac : chartToSpace B S hS Y W ≫ f =
        representedSpaceMap B S hS q ≫ chartToSpace B S hS X V :=
      (chartSpaceMapOver_comp_chartToSpace B S hS f q hq).symm
    let G := (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E
    have hG := isPseudoCoherentFrom_smallEtaleDerivedModulePullback_of_isEtale B S hS _
      (isEtale_chartToSpace B S hS X V) E m h
    have hGq := derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS X V) E hE
    have h₁ := isPseudoCoherentFrom_derivedPullback_representedSpaceMap B S hS q G hGq m hG
    exact isPseudoCoherentFrom_derivedPullback_of_comp_eq B S hS hfac E h₁
  refine isPseudoCoherentFrom_of_charts B S hS _ m fun U =>
    ⟨fun Z _ => ∃ i, Nonempty (Z ⟶ affineChartDiagramCharts B S hS f i), ?_, ?_⟩
  · exact (smallEtaleRingedSite B S hS Y.1 Y.2).J.superset_covering
      (fun _ g hg => ⟨_, 𝟙 _, g, hg, Category.id_comp g⟩)
      (coversTop_affineChartDiagramCharts B S hS f U)
  · rintro V a ⟨⟨W, hW⟩, ⟨b⟩⟩
    have h₁ := isPseudoCoherentFrom_smallEtaleDerivedModulePullback_of_isEtale B S hS
      (chartMap B S hS Y b) (isEtale_chartMap B S hS Y b) _ m (key W hW)
    obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_iso_of_eq B S hS
      (chartMap_comp_chartToSpace B S hS Y b) ((smallEtaleDerivedModulePullback B S hS f).obj E)
    exact isPseudoCoherentFrom_of_iso B S hS h₁
      ((((smallEtaleDerivedPullbackData B S hS).compIso (chartMap B S hS Y b)
        (chartToSpace B S hS Y W)).app _).symm ≪≫ e)

/-! ### Descent -/

/-- **The case of schemes, on a represented algebraic space.** Let `{r_i : W_i ⟶ V}` be a family
of morphisms of the big fppf site whose underlying morphisms of schemes form an fpqc covering, and
let `G` be an object of `D_QCoh` of `h_V`. If every `Lr_i^*G` is `m`-pseudo-coherent, then so is
`G`. This is Stacks 09UE, read on the small étale sites. -/
theorem isPseudoCoherentFrom_of_fpqcPrecoverage_representedSpaceMap {I : Type v}
    {V : BigFppfOver B S hS} {W : I → BigFppfOver B S hS} (r : ∀ i, W i ⟶ V)
    (hr : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (W i))
      (fun i => (BigFppfOver.toScheme B S hS).map (r i)) ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj V))
    (G : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)))
    (hG : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V)).O))) G) (m : ℤ)
    (h : ∀ i,
      haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
        (representedSpaceMap B S hS (r i))
      (smallEtaleRingedSite B S hS (yoneda.obj (W i))
        (isAlgebraicSpace_yoneda B S hS (W i))).IsPseudoCoherentFrom
          ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (r i))).obj G) m) :
    (smallEtaleRingedSite B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V)).IsPseudoCoherentFrom G m := by
  obtain ⟨K, hK, hKf, hKq, ⟨eG⟩⟩ :=
    exists_kFlatComplex_representedAssociatedModule_iso B S hS V G hG
  have hi : ∀ i, RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom
      (X := ((BigFppfOver.toScheme B S hS).obj (W i)).toRingedSpace)
      (((RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map (r i)).toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) m := by
    intro i
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS (r i))
    obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_representedAssociatedModule_iso B S hS
      (r i) K hK hKf
    exact (isPseudoCoherentFrom_representedAssociatedModule_iff B S hS (W i) _ m).1
      (isPseudoCoherentFrom_of_iso B S hS
        (X := ⟨yoneda.obj (W i), isAlgebraicSpace_yoneda B S hS (W i)⟩) (h i)
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (r i))).mapIso
          eG.symm ≪≫ e))
  have h₃ := Stacks.Cohomology.PseudoCoherence.FpqcDescent.isPseudoCoherentComplexFrom_of_fpqc_kFlat
    _ _ hr K hK hKq m hi
  exact isPseudoCoherentFrom_of_iso B S hS (X := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    ((isPseudoCoherentFrom_representedAssociatedModule_iff B S hS V K m).2 h₃) eG

/-- **Descent of `m`-pseudo-coherence along an fpqc covering with scheme sources.** Let
`{g_i : h_{Z_i} ⟶ X}` be an fpqc covering of an algebraic space `X` by algebraic spaces
represented by objects `Z_i` of the big fppf site, and let `E` be an object of `D(𝒪_X)` with
quasi-coherent cohomology. If every `Lg_i^*E` is `m`-pseudo-coherent, then so is `E`. -/
theorem isPseudoCoherentFrom_of_isFpqcCovering_representable {I : Type v}
    {X : AlgebraicSpaces B S hS} {Z : I → BigFppfOver B S hS}
    (g : ∀ i, (⟨yoneda.obj (Z i), isAlgebraicSpace_yoneda B S hS (Z i)⟩ : AlgebraicSpaces B S hS) ⟶
      X)
    (hg : IsFpqcCovering B S hS fun i => (g i).hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E)
    (m : ℤ)
    (h : ∀ i,
      haveI := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS (g i)
      (smallEtaleRingedSite B S hS (yoneda.obj (Z i))
        (isAlgebraicSpace_yoneda B S hS (Z i))).IsPseudoCoherentFrom
          ((smallEtaleDerivedModulePullback B S hS (g i)).obj E) m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_charts B S hS E m fun U => ⟨⊤, ?_, fun V _ _ => ?_⟩
  · rw [Sieve.generate_top]
    exact (smallEtaleRingedSite B S hS X.1 X.2).J.top_mem U
  let φ := chartToSpace B S hS X V
  have hGq := derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS φ E hE
  have hrep : ∀ i, yoneda.relativelyRepresentable (g i).hom := fun i =>
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X.obj)).mp
      X.property.diagonal_representable (g i).hom
  let W : I → BigFppfOver B S hS := fun i => (hrep i).pullback φ.hom
  let r : ∀ i, W i ⟶ (SmallEtale.toOver B S hS X.1).obj V := fun i => (hrep i).snd φ.hom
  let s : ∀ i, (⟨yoneda.obj (W i), isAlgebraicSpace_yoneda B S hS (W i)⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj (Z i), isAlgebraicSpace_yoneda B S hS (Z i)⟩ :=
    fun i => ObjectProperty.homMk ((hrep i).fst φ.hom)
  have hsq : ∀ i, representedSpaceMap B S hS (r i) ≫ φ = s i ≫ g i := fun i =>
    ObjectProperty.hom_ext _ ((hrep i).isPullback φ.hom).w.symm
  have hcov : Presieve.ofArrows (fun i => (BigFppfOver.toScheme B S hS).obj (W i))
      (fun i => (BigFppfOver.toScheme B S hS).map (r i)) ∈
        Scheme.fpqcPrecoverage
          ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)) := by
    have h₁ := isFpqcCovering_pullback B S hS g φ hg
    have h₂ := isFpqcCovering_isoComp B S hS
      (fun i => ((hrep i).isPullback φ.hom).isoPullback.hom)
      (fun i => pullback.snd (g i).hom φ.hom) h₁
    have h₃ : (fun i => ((hrep i).isPullback φ.hom).isoPullback.hom ≫
        pullback.snd (g i).hom φ.hom) = fun i => yoneda.map (r i) :=
      funext fun i => IsPullback.isoPullback_hom_snd _
    rw [h₃] at h₂
    exact isFpqcCovering_yoneda_of_isCovering B S hS W _ r
      ⟨isAlgebraicSpace_yoneda B S hS _, fun i => isAlgebraicSpace_yoneda B S hS _, h₂⟩
  have key : ∀ i,
      have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
        (representedSpaceMap B S hS (r i))
      (smallEtaleRingedSite B S hS (yoneda.obj (W i))
        (isAlgebraicSpace_yoneda B S hS (W i))).IsPseudoCoherentFrom
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS (r i))).obj
          ((smallEtaleDerivedModulePullback B S hS φ).obj E)) m := by
    intro i
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS
      (representedSpaceMap B S hS (r i))
    have := hasLeftDerivedFunctor_smallEtaleModulePullbackOnHomotopy B S hS (g i)
    have h₁ := isPseudoCoherentFrom_smallEtaleDerivedModulePullback B S hS (s i) _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS (g i) E hE) m (h i)
    exact isPseudoCoherentFrom_derivedPullback_of_comp_eq B S hS (hsq i) E h₁
  exact isPseudoCoherentFrom_of_fpqcPrecoverage_representedSpaceMap B S hS r hcov _ hGq m key

/-! ### Stacks 0DL1 -/

/-- **Stacks 0DL1.** Let `{f_i : X_i ⟶ X}` be an fpqc covering of algebraic spaces over a scheme
`S`, let `E` be an object of `D_QCoh(𝒪_X)` and let `m` be an integer. Then `E` is
`m`-pseudo-coherent if and only if each `Lf_i^*E` is `m`-pseudo-coherent.

The forward implication is
`AlgebraicGeometry.Space.isPseudoCoherentFrom_smallEtaleDerivedModulePullback`. For the converse,
Stacks 0419 refines the covering by morphisms `e_i : T_i ⟶ X_i` out of schemes of the site with
`{e_i ≫ f_i}` again an fpqc covering; `L(e_i ≫ f_i)^*E ≅ Le_i^*(Lf_i^*E)` (Stacks 0D6D) is
`m`-pseudo-coherent by the forward implication, as `Lf_i^*E` has quasi-coherent cohomology
(Stacks 08F4), and
`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_isFpqcCovering_representable` applies. -/
@[stacks 0DL1]
theorem isPseudoCoherentFrom_iff_forall_derivedPullback_of_isFpqcCovering {I : Type v}
    {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) n).obj E).IsQuasicoherentOnSite)
    (m : ℤ) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m ↔
      ∀ i, (smallEtaleRingedSite B S hS (Xi i).1 (Xi i).2).IsPseudoCoherentFrom
        ((smallEtaleDerivedModulePullback B S hS (f i)).obj E) m := by
  refine ⟨fun h i => isPseudoCoherentFrom_smallEtaleDerivedModulePullback B S hS (f i) E hE m h,
    fun h => ?_⟩
  obtain ⟨Z, e, -, hcov⟩ := exists_fpqc_scheme_refinement B S hS X.2 (fun i => (Xi i).2)
    (fun i => (f i).hom) hf
  let ι : ∀ i, (⟨yoneda.obj (Z i), isAlgebraicSpace_yoneda B S hS (Z i)⟩ :
      AlgebraicSpaces B S hS) ⟶ Xi i := fun i => ObjectProperty.homMk (e i)
  refine isPseudoCoherentFrom_of_isFpqcCovering_representable B S hS (fun i => ι i ≫ f i) hcov E hE
    m fun i => ?_
  exact isPseudoCoherentFrom_of_iso B S hS
    (isPseudoCoherentFrom_smallEtaleDerivedModulePullback B S hS (ι i) _
      (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS (f i) E hE) m (h i))
    (((smallEtaleDerivedPullbackData B S hS).compIso (ι i) (f i)).app E).symm

end StandardModel

end AlgebraicGeometry.Space
