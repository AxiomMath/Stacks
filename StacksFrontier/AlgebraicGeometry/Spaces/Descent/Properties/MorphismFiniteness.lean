module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FppfRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.FlatDescentSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Descent of finiteness properties along a surjection of fppf sheaves

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S` and suppose that
`f` is surjective as a map of fppf sheaves. Then flatness, local finite type and local finite
presentation all descend from the composite `f ≫ g` to `g`.

Each of the three properties is tested on the squares of étale scheme charts of a morphism of
algebraic spaces, so the descent reduces to the corresponding statement for schemes, namely
that each of the three properties descends from a composite of scheme morphisms whose first
factor is refined by an fppf covering. The reduction itself is independent of the property and
is isolated as
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_of_locallySurjective`.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_of_locallySurjective` descends any
  property of scheme morphisms which descends along fppf refinements.
* `AlgebraicGeometry.Space.isFlat_of_comp_of_locallySurjective`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp_of_locallySurjective` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp_of_locallySurjective` are the
  three instances of it.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_commonFppfDescentSituation` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_commonFppfDescentSituation`
  specialise the last two to a commutative triangle whose first morphism is surjective, flat
  and locally of finite presentation, which is the shape in which the descent is used.

## Implementation notes

Surjectivity of a morphism of sheaves is Mathlib's
`CategoryTheory.Presheaf.IsLocallySurjective` for the topology of the big fppf site of `S`.
Given a square of étale charts `a` of `Y` and `b` of `Z` over `h`, the fibre product of `a`
with `f` is an algebraic space, and an atlas `Q` of it provides an étale chart of `X` lying
over `a`. The covering of `U` refining the image sieve of `a` is produced by
`AlgebraicGeometry.BigFppfOver.exists_isCovering_of_mem_topology`; refining it further by the
atlas of each fibre product exhibits the scheme morphism `Q ⟶ U` as refined by an fppf
covering, which is what the scheme-level descent statements take as input.

A morphism of algebraic spaces which is surjective, flat and locally of finite presentation is
a one-member fppf covering of its target, hence surjective as a morphism of fppf sheaves by
`AlgebraicGeometry.Space.isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation`;
this is what turns the two finiteness statements into Stacks 0AHC.

## References

* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 0AHC](https://stacks.math.columbia.edu/tag/0AHC)
* [Stacks Project, Tag 0469](https://stacks.math.columbia.edu/tag/0469)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- For a morphism `f` of algebraic spaces which is surjective as a morphism of fppf sheaves, a
morphism `a` from a scheme `U` to its target, and an étale surjective atlas `atlasT` of the fibre
product of `a` and `f`, the induced scheme morphism to `U` is refined by an fppf covering of
`U`. -/
theorem exists_fppf_refinement_of_isLocallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f)
    {U Q : BigFppfOver B S hS} (a : yoneda.obj U ⟶ Y) (atlasT : yoneda.obj Q ⟶ pullback a f)
    (hatlasTSurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) atlasT)
    (hqX : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) atlasT) :
    ∃ 𝒰 : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage ((BigFppfOver.toScheme B S hS).obj U),
      Nonempty (𝒰.toPreZeroHypercover.Hom (PreZeroHypercover.singleton.{u + 1, u, u + 1}
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (atlasT ≫ pullback.fst a f))))) := by
  let Tsch : BigFppfOver B S hS ⥤ Scheme.{u} := BigFppfOver.toScheme B S hS
  let qUsite : Q ⟶ U := yoneda.preimage (atlasT ≫ pullback.fst a f)
  let aElem : Y.obj (Opposite.op U) := yonedaEquiv a
  obtain ⟨E, hE, hEimage⟩ :=
    BigFppfOver.exists_isCovering_of_mem_topology B S hS (hf.imageSieve_mem aElem)
  let coverU : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage (Tsch.obj U) := by
    have hFppf : AlgebraicGeometry.IsFppfCovering
        ⟨(BigFppfOver.forget B S hS).obj U, E.map (BigFppfOver.forget B S hS)⟩ :=
      B.isFppfCovering_of_isCovering hE
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff] at hFppf
    refine ⟨E.map Tsch, ?_⟩
    simpa [Tsch, PreZeroHypercover.map, PreZeroHypercover.presieve₀] using hFppf
  choose xiElem hxi using hEimage
  let xi : (i : E.I₀) → yoneda.obj (E.X i) ⟶ X :=
    fun i => (yonedaEquiv (X := E.X i) (F := X)).symm (xiElem i)
  have htri (i : E.I₀) : yoneda.map (E.f i) ≫ a = xi i ≫ f := by
    apply (yonedaEquiv (X := E.X i) (F := Y)).injective
    rw [← yonedaEquiv_naturality a (E.f i), yonedaEquiv_comp]
    simpa [aElem, xi] using (hxi i).symm
  let mi : (i : E.I₀) → yoneda.obj (E.X i) ⟶ pullback a f :=
    fun i => pullback.lift (yoneda.map (E.f i)) (xi i) (htri i)
  let li : (i : E.I₀) → yoneda.obj (hqX.rep.pullback (mi i)) ⟶ yoneda.obj Q :=
    fun i => hqX.rep.fst (mi i)
  let ri : (i : E.I₀) → hqX.rep.pullback (mi i) ⟶ E.X i := fun i => hqX.rep.snd (mi i)
  have hAtlasPB (i : E.I₀) :
      IsPullback (li i) (yoneda.map (ri i)) atlasT (mi i) := by
    simpa [li, ri] using hqX.rep.isPullback (mi i)
  let localCover (i : E.I₀) :
      Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage (Tsch.obj (E.X i)) := by
    have : Etale (Tsch.map (ri i)) := hqX.property (mi i) (li i) (ri i) (hAtlasPB i)
    have : Surjective (Tsch.map (ri i)) := hatlasTSurj.property (mi i) (li i) (ri i) (hAtlasPB i)
    refine ⟨PreZeroHypercover.singleton (Tsch.map (ri i)), ?_⟩
    simpa only [PreZeroHypercover.presieve₀_singleton] using
      Scheme.Hom.singleton_mem_fppfPrecoverage (Tsch.map (ri i))
  have hfactor' (i : E.I₀) : yoneda.preimage (li i) ≫ qUsite = ri i ≫ E.f i := by
    apply yoneda.map_injective
    simpa [mi, qUsite, Category.assoc, pullback.lift_fst] using
      congrArg (· ≫ pullback.fst a f) (hAtlasPB i).w
  refine ⟨coverU.bind localCover, ⟨{
    s₀ := fun _ => PUnit.unit
    h₀ := fun ij => Tsch.map (yoneda.preimage (li ij.1))
    w₀ := fun ij => ?_ }⟩⟩
  show Tsch.map (yoneda.preimage (li ij.1)) ≫ Tsch.map qUsite =
    Tsch.map (ri ij.1) ≫ Tsch.map (E.f ij.1)
  simpa only [Functor.map_comp] using congrArg Tsch.map (hfactor' ij.1)

/-- A property of morphisms of schemes which descends from a composite to its second factor
whenever the first factor is refined by an fppf covering descends, in the chart sense of
Stacks 03MJ, from a composite of morphisms of algebraic spaces to its second factor whenever
the first factor is surjective as a morphism of fppf sheaves. -/
theorem holdsOnEveryEtaleChart_of_comp_of_locallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hdesc : ∀ {A B' C : Scheme.{u}} (f : A ⟶ B') (g : B' ⟶ C),
      P (f ≫ g) →
      (∃ 𝒰 : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage B',
        Nonempty (𝒰.toPreZeroHypercover.Hom
          (PreZeroHypercover.singleton.{u + 1, u, u + 1} f))) → P g)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : HoldsOnEveryEtaleChart B S hS P (f ≫ g))
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    HoldsOnEveryEtaleChart B S hS P g := by
  let Tsch : BigFppfOver B S hS ⥤ Scheme.{u} := BigFppfOver.toScheme B S hS
  let Et : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tsch
  have : Et.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : Et.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : Et.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Et
  have : Et.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Et
  intro U V a b h hUa hVb hab
  obtain ⟨Q, atlasT, hatlasTSurj, hatlasTEtale⟩ := (isAlgebraicSpace_pullback B S hS a f
    (isAlgebraicSpace_yoneda B S hS U) hX hY).exists_atlas
  let qUsite : Q ⟶ U := yoneda.preimage (atlasT ≫ pullback.fst a f)
  have hQtoX : Et.presheaf (atlasT ≫ pullback.snd a f) :=
    MorphismProperty.comp_mem Et.presheaf atlasT (pullback.snd a f) hatlasTEtale
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback a f) hUa)
  have hchart :
      yoneda.map (qUsite ≫ h) ≫ b = (atlasT ≫ pullback.snd a f) ≫ f ≫ g := by
    simp only [Functor.map_comp, Category.assoc, hab,
      show yoneda.map qUsite = atlasT ≫ pullback.fst a f by simp [qUsite],
      pullback.condition_assoc]
  exact hdesc (Tsch.map qUsite) (Tsch.map h)
    (hfg Q V (atlasT ≫ pullback.snd a f) b (qUsite ≫ h) hQtoX hVb hchart)
    (exists_fppf_refinement_of_isLocallySurjective B S hS hf a atlasT hatlasTSurj hatlasTEtale)

/-- **Stacks 06NR.** Flatness of a composite of morphisms of algebraic spaces descends to the
second factor when the first factor is surjective as a morphism of fppf sheaves. -/
@[stacks 06NR "flatness"]
theorem isFlat_of_comp_of_locallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsFlat B S hS (f ≫ g))
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    IsFlat B S hS g :=
  holdsOnEveryEtaleChart_of_comp_of_locallySurjective B S hS
    (@Flat.{u} : MorphismProperty Scheme.{u})
    (fun f' g' hcomp hcover ↦
      have : Flat (f' ≫ g') := hcomp
      flat_of_comp_of_fppf_refinement f' g' hcover) hX hY f g hfg hf

/-- **Stacks 06NR.** Local finite type of a composite of morphisms of algebraic spaces
descends to the second factor when the first factor is surjective as a morphism of fppf
sheaves. -/
@[stacks 06NR "locally finite type"]
theorem isLocallyOfFiniteType_of_comp_of_locallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsLocallyOfFiniteType B S hS (f ≫ g))
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    IsLocallyOfFiniteType B S hS g :=
  holdsOnEveryEtaleChart_of_comp_of_locallySurjective B S hS
    (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (fun f' g' hcomp hcover ↦
      have : LocallyOfFiniteType (f' ≫ g') := hcomp
      locallyOfFiniteType_of_comp_of_fppf_refinement f' g' hcover) hX hY f g hfg hf

/-- **Stacks 06NR.** Local finite presentation of a composite of morphisms of algebraic spaces
descends to the second factor when the first factor is surjective as a morphism of fppf
sheaves. -/
@[stacks 06NR "locally finite presentation"]
theorem isLocallyOfFinitePresentation_of_comp_of_locallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsLocallyOfFinitePresentation B S hS (f ≫ g))
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f) :
    IsLocallyOfFinitePresentation B S hS g :=
  holdsOnEveryEtaleChart_of_comp_of_locallySurjective B S hS
    (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (fun f' g' hcomp hcover ↦
      have : LocallyOfFinitePresentation (f' ≫ g') := hcomp
      locallyOfFinitePresentation_of_comp_of_fppf_refinement f' g' hcover) hX hY f g hfg hf

/-- **Stacks 0AHC**, the case of local finite type. In a commutative triangle `X ⟶ Y ⟶ B` of
algebraic spaces whose first morphism is surjective, flat and locally of finite presentation,
if `X ⟶ B` is locally of finite type then so is `Y ⟶ B`. -/
@[stacks 0AHC "the case of local finite type", ega "IV 11.3.16" "locally of finite type"]
theorem isLocallyOfFiniteType_of_commonFppfDescentSituation
    (T : CommonFppfDescentSituation.{u}) (hp : IsLocallyOfFiniteType T.site T.S T.hS T.p) :
    IsLocallyOfFiniteType T.site T.S T.hS T.q :=
  isLocallyOfFiniteType_of_comp_of_locallySurjective T.site T.S T.hS
    T.algebraicSpaceX T.algebraicSpaceY T.algebraicSpaceB T.f T.q
    (by simpa only [T.p_eq] using hp)
    (isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation T.site T.S T.hS
      T.algebraicSpaceX T.algebraicSpaceY T.f T.surjective_f T.flat_f
      T.locallyOfFinitePresentation_f)

/-- **Stacks 0AHC**, the case of local finite presentation. In a commutative triangle
`X ⟶ Y ⟶ B` of algebraic spaces whose first morphism is surjective, flat and locally of finite
presentation, if `X ⟶ B` is locally of finite presentation then so is `Y ⟶ B`. -/
@[stacks 0AHC "the case of local finite presentation",
  ega "IV 11.3.16" "loc. fin. presentation",
  sga "4 IV 8.5.5" "partial"]
theorem isLocallyOfFinitePresentation_of_commonFppfDescentSituation
    (T : CommonFppfDescentSituation.{u})
    (hp : IsLocallyOfFinitePresentation T.site T.S T.hS T.p) :
    IsLocallyOfFinitePresentation T.site T.S T.hS T.q :=
  isLocallyOfFinitePresentation_of_comp_of_locallySurjective T.site T.S T.hS
    T.algebraicSpaceX T.algebraicSpaceY T.algebraicSpaceB T.f T.q
    (by simpa only [T.p_eq] using hp)
    (isLocallySurjective_of_surjective_flat_locallyOfFinitePresentation T.site T.S T.hS
      T.algebraicSpaceX T.algebraicSpaceY T.f T.surjective_f T.flat_f
      T.locallyOfFinitePresentation_f)

end AlgebraicGeometry.Space

end
