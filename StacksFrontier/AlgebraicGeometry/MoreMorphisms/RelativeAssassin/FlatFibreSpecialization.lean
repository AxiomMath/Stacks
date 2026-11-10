module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ValuationBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ValuationClosedFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative associated points at generic points of the fibres of a closure

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and `F` a quasi-coherent
`𝒪_X`-module of finite type. Let `y` be a point of `Ass_{X/S}(F)` and `Y` the reduced closed
subscheme supported on the closure of `y`. For `s` a point of `S` and `ξ` a generic point of an
irreducible component of the fibre of `Y` over `s`, if `F` is flat over `S` at the image `x` of
`ξ` in `X`, then `x` again lies in `Ass_{X/S}(F)`.

The point is reduced to the case of a valuation base: a base change along the spectrum of a
valuation ring reproduces the whole configuration with the image of `y` over the generic point
and the image of `ξ` over the closed point, and there
`Stacks.RelativeAssassin.mem_relativeAssassin_of_isGenericPoint_closedFibre` applies.

Applied to a component of the fibre of that closure over a point `s` whose fibre `X_s` the
closure meets, this is the criterion for purity of Tag 05L3: a relative associated point which
specializes into `X_s`, along which `F` is flat over `S`, specializes to a point of `X_s`
associated to the restriction `F_s`.

## Main results

* `Stacks.RelativeAssassin.exists_valuation_base_change_associated_flat`
* `Stacks.RelativeAssassin.mem_relativeAssassin_of_isGenericPoint_fibre_closure`
* `Stacks.RelativeAssassin.exists_specializes_mem_associatedPoints_fibre`

## Implementation notes

The base change is the one of `ValuationBaseChange.lean`; what is added to it here is that the
two conditions carried by the original configuration survive it. Flatness ascends because it is
stable under arbitrary base change of modules. For the relative assassin the criterion of Tag
05DC asks, beyond membership of the image, that the point of the residue-field tensor product
attached to the lift be a generic point of an irreducible component of its spectrum; that is
checked by showing the corresponding prime is minimal, which comes from the lift being a generic
point of a component of the generic fibre of the base-changed closure — a generalization of it
inside that spectrum is carried into the closure and must therefore be the point itself.

The descent at the end is the other direction of the same criterion, which needs no genericity:
a relative associated point of the pulled-back module has its image in `Ass_{X/S}(F)`.

## References

* [Stacks Project, Tag 0GSI](https://stacks.math.columbia.edu/tag/0GSI)
* [Stacks Project, Tag 05L3](https://stacks.math.columbia.edu/tag/05L3)
* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
* [EGA IV, Proposition 12.1.1.5]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeAssassin

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent, at
the spelling `Scheme.Modules.pullback` rather than the ringed-space `modulePullback`. -/
theorem isQuasicoherent_pullbackObj {X Z : Scheme.{u}} (p : Z ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback p).obj F).IsQuasicoherent := by
  have hF : F.IsQuasicoherent := inferInstance
  change ((modulePullback p.toLRSHom.toShHom).obj F).IsQuasicoherent
  exact @SheafOfModules.modulePullback_isQuasicoherent _ _ p.toLRSHom.toShHom F hF

/-- If `η` is a generic point of an irreducible component of the fibre over `t` of the pullback
`Y ×_X (X ×_S W) ⟶ W` of a closed subscheme `Y` of `X`, and the image of `η` in `X` lies in `Y`,
then the point of the residue-field tensor product attached to the image `y'` of `η` in
`X ×_S W` is a generic point of an irreducible component of its spectrum. -/
theorem exists_isGenericPoint_specOfPoint_of_fibre_comap
    {X S W : Scheme.{u}} (f : X ⟶ S) (g : W ⟶ S) (Y : X.IdealSheafData) (t : W)
    (η : ((Y.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g).fiber t)
    (hη : closure ({η} : Set (((Y.comap (pullback.fst f g)).subschemeι ≫
        pullback.snd f g).fiber t)) ∈
      irreducibleComponents (((Y.comap (pullback.fst f g)).subschemeι ≫
        pullback.snd f g).fiber t))
    (hy : pullback.fst f g ((Y.comap (pullback.fst f g)).subschemeι
      (((Y.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g).fiberι t η)) ∈ Y.support) :
    ∃ C ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint
        ((Y.comap (pullback.fst f g)).subschemeι
          (((Y.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g).fiberι t η))).tensor),
      IsGenericPoint (Scheme.Pullback.SpecOfPoint ((Y.comap (pullback.fst f g)).subschemeι
        (((Y.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g).fiberι t η))) C := by
  let p := pullback.fst f g
  let q := pullback.snd f g
  let Z : (pullback f g).IdealSheafData := Y.comap p
  let j : Z.subscheme ⟶ pullback f g := Z.subschemeι
  let y' := j ((j ≫ q).fiberι t η)
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint y'
  let P : Spec T.tensor := Scheme.Pullback.SpecOfPoint y'
  have hxSupport (r : Spec T.tensor) : T.SpecTensorTo r ∈ Z.support := by
    rw [Scheme.IdealSheafData.support_comap]
    change p (T.SpecTensorTo r) ∈ Y.support
    rw [T.fst_SpecTensorTo_apply]
    exact hy
  have hηNoGen {w : (j ≫ q).fiber t} (hw : w ⤳ η) : w = η :=
    (hw.antisymm (specializes_iff_closure_subset.2
      (hη.2 isIrreducible_singleton.closure hw.closure_subset))).eq
  have hmin : P.asIdeal ∈ minimalPrimes T.tensor := by
    refine ⟨⟨P.2, bot_le⟩, fun Q hQ hQP => ?_⟩
    let r : Spec T.tensor := ⟨Q, hQ.1⟩
    have hrP : r ⤳ P := (PrimeSpectrum.le_iff_specializes r P).mp hQP
    let xr := T.SpecTensorTo r
    obtain ⟨zr, hzr⟩ : xr ∈ Set.range j := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hxSupport r
    have hpoint : T.SpecTensorTo P = y' := Scheme.Pullback.SpecTensorTo_SpecOfPoint y'
    have hxrspec : xr ⤳ y' := by simpa [xr, hpoint] using hrP.map T.SpecTensorTo.continuous
    have hzrspec : zr ⤳ (j ≫ q).fiberι t η := by
      apply j.isEmbedding.isInducing.specializes_iff.mp
      simpa [hzr] using hxrspec
    have hzrbase : (j ≫ q) zr = t := by
      rw [Scheme.Hom.comp_apply, hzr]
      exact (T.snd_SpecTensorTo_apply r).trans
        (Stacks.ClosedFibreGenericPoint.apply_fiberι_comp q j t η)
    obtain ⟨w, hwι⟩ : zr ∈ Set.range ((j ≫ q).fiberι t) :=
      ((j ≫ q).range_fiberι t).ge hzrbase
    have hwη : w ⤳ η :=
      ((j ≫ q).fiberι t).isEmbedding.isInducing.specializes_iff.mp (by rw [hwι]; exact hzrspec)
    have hxrEq : xr = y' := by rw [← hzr, ← hwι, hηNoGen hwη]
    have hrEq : r = P := by
      have hpair : (⟨T, r⟩ : Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) = ⟨T, P⟩ :=
        (Scheme.Pullback.carrierEquiv (f := f) (g := g)).symm.injective
          (hxrEq.trans hpoint.symm)
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
    exact (congrArg PrimeSpectrum.asIdeal hrEq).ge
  have hcomp : closure ({P} : Set (Spec T.tensor)) ∈ irreducibleComponents (Spec T.tensor) := by
    let P' : PrimeSpectrum T.tensor := P
    change closure ({P'} : Set (PrimeSpectrum T.tensor)) ∈
      irreducibleComponents (PrimeSpectrum T.tensor)
    rw [PrimeSpectrum.closure_singleton]
    refine PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr ?_
    rw [P'.2.radical]
    exact hmin
  exact ⟨closure ({P} : Set (Spec T.tensor)), hcomp, isGenericPoint_closure⟩

/-- **A valuation-ring base change preserving a relative associated point and flatness.** In the
configuration of a point `y` of `Ass_{X/S}(F)`, the reduced closed subscheme `Y` supported on
its closure, and a generic point `ξ` of an irreducible component of the fibre of `Y` over `s`
whose image `x` is a point of flatness of `F` over `S`, the valuation-ring base change through
`ξ` carries `y` to a point of the relative assassin of the pulled-back module and `x` to a point
of flatness of it. -/
theorem exists_valuation_base_change_associated_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent]
    (y : X) (hy : y ∈ Stacks.Divisors.relativeAssassin f F)
    (Y : X.IdealSheafData)
    (hY : Y = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)))
    (s : S) (x : X)
    (ξ : (Y.subschemeι ≫ f).fiber s)
    (hξ : closure ({ξ} : Set ((Y.subschemeι ≫ f).fiber s)) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber s))
    (hx : Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ) = x)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (g : Spec (.of A) ⟶ S),
      g (genericPoint (Spec (.of A))) = f y ∧
      g (closedPoint A) = s ∧
      (let X' := (pullback f g : Scheme.{u})
       let p : X' ⟶ X := pullback.fst f g
       let q : X' ⟶ Spec (.of A) := pullback.snd f g
       let Z : X'.IdealSheafData := Y.comap p
       let j : Z.subscheme ⟶ X' := Z.subschemeι
       ∃ η : (j ≫ q).fiber (genericPoint (Spec (.of A))),
         closure ({η} : Set ((j ≫ q).fiber (genericPoint (Spec (.of A))))) ∈
           irreducibleComponents ((j ≫ q).fiber (genericPoint (Spec (.of A)))) ∧
         p (j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)) = y ∧
         (let y' : X' := j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)
          let Y' : X'.IdealSheafData :=
            Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y'} : Set X'))
          IsIntegral Y'.subscheme ∧
          y' ∈ Stacks.Divisors.relativeAssassin q ((Scheme.Modules.pullback p).obj F) ∧
          ∃ ξ' : (Y'.subschemeι ≫ q).fiber (closedPoint A),
            closure ({ξ'} : Set ((Y'.subschemeι ≫ q).fiber (closedPoint A))) ∈
              irreducibleComponents ((Y'.subschemeι ≫ q).fiber (closedPoint A)) ∧
            p (Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι (closedPoint A) ξ')) = x ∧
            IsFlatOverAt q.toLRSHom.toShHom ((Scheme.Modules.pullback p).obj F)
              (Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι (closedPoint A) ξ')))) := by
  classical
  obtain ⟨A, hA, hDom, hVal, g, hg, hgs, η, hη, hpy, hInt, ξ', hξ', hpx⟩ :=
    Stacks.RelativeAssassin.exists_valuation_base_change_generic_component f y Y hY s x ξ hξ hx
  let : CommRing A := hA
  let : IsDomain A := hDom
  let : ValuationRing A := hVal
  let X' := pullback f g
  let p : X' ⟶ X := pullback.fst f g
  let q : X' ⟶ Spec (.of A) := pullback.snd f g
  let Z : X'.IdealSheafData := Y.comap p
  let j : Z.subscheme ⟶ X' := Z.subschemeι
  let y' : X' := j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)
  let Y' : X'.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y'} : Set X'))
  have hAssoc : y' ∈ Stacks.Divisors.relativeAssassin q
      ((Scheme.Modules.pullback p).obj F) := by
    rw [AlgebraicGeometry.mem_relativeAssassin_pullback_iff]
    refine ⟨?_, exists_isGenericPoint_specOfPoint_of_fibre_comap f g Y _ η hη ?_⟩
    · change p y' ∈ Stacks.Divisors.relativeAssassin f F
      rw [hpy]
      exact hy
    · change p y' ∈ Y.support
      rw [hpy, hY]
      exact Stacks.ClosedFibreGenericPoint.mem_support_vanishingIdeal_closure y
  have hflat'' := @AlgebraicGeometry.modulePullback_isFlatOverAt
    X S (Spec (.of A)) X' f g p q (IsPullback.of_hasPullback f g) F
    (inferInstance : F.IsQuasicoherent)
    (Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι (closedPoint A) ξ')) (by rw [hpx]; exact hflat)
  exact ⟨A, hA, hDom, hVal, g, hg, hgs, η, hη, hpy, hInt, hAssoc, ξ', hξ', hpx, hflat''⟩

/-- **Relative associated points at generic points of the fibres of a closure.** Let
`f : X ⟶ S` be locally of finite type, `F` a quasi-coherent finite type `𝒪_X`-module and `y` a
point of `Ass_{X/S}(F)`. Let `Y` be the reduced closed subscheme supported on the closure of `y`
and let `ξ` be a generic point of an irreducible component of the fibre of `Y` over a point `s`
of `S`. If `F` is flat over `S` at the image of `ξ` in `X`, that image lies in
`Ass_{X/S}(F)`. -/
@[stacks 0GSI "the relative assassin conclusion",
  ega "IV 12.1.1.4" "z ∈ Ass(F_y)",
  ega "IV 12.1.1.5" "z ∈ Ass(F_y)"]
theorem mem_relativeAssassin_of_isGenericPoint_fibre_closure
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ Stacks.Divisors.relativeAssassin f F)
    (Y : X.IdealSheafData)
    (hY : Y = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)))
    (s : S) (ξ : (Y.subschemeι ≫ f).fiber s)
    (hξ : closure ({ξ} : Set ((Y.subschemeι ≫ f).fiber s)) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber s))
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F
      (Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ))) :
    Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ)
      ∈ Stacks.Divisors.relativeAssassin f F := by
  obtain ⟨A, hAcomm, hAdomain, hAvaluation, g, hgeneric, hclosed, hdata⟩ :=
    exists_valuation_base_change_associated_flat f F y hy Y hY s
      (Y.subschemeι ((Y.subschemeι ≫ f).fiberι s ξ)) ξ hξ rfl hflat
  let : CommRing A := hAcomm
  let : IsDomain A := hAdomain
  let : ValuationRing A := hAvaluation
  obtain ⟨η, hηcomp, hpy, hrest⟩ := hdata
  let X' := pullback f g
  let p : X' ⟶ X := pullback.fst f g
  let q : X' ⟶ Spec (.of A) := pullback.snd f g
  let Z : X'.IdealSheafData := Y.comap p
  let j : Z.subscheme ⟶ X' := Z.subschemeι
  let y' : X' := j ((j ≫ q).fiberι (genericPoint (Spec (.of A))) η)
  let Y' : X'.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y'} : Set X'))
  obtain ⟨hY'integral, hy', ξ', hξ'comp, hpx, hflat'⟩ := hrest
  let x' : X' := Y'.subschemeι ((Y'.subschemeι ≫ q).fiberι (closedPoint A) ξ')
  have hy'generic : q y' = genericPoint (Spec (.of A)) :=
    Stacks.ClosedFibreGenericPoint.apply_fiberι_comp q j (genericPoint (Spec (.of A))) η
  let : ((Scheme.Modules.pullback p).obj F).IsQuasicoherent := isQuasicoherent_pullbackObj p F
  have hx' : x' ∈ Stacks.Divisors.relativeAssassin q ((Scheme.Modules.pullback p).obj F) :=
    mem_relativeAssassin_of_isGenericPoint_closedFibre q ((Scheme.Modules.pullback p).obj F)
      y' hy' hy'generic Y' rfl ξ' hξ'comp hflat'
  have hbase := (AlgebraicGeometry.mem_relativeAssassin_pullback_iff f g F x').mp hx'
  rw [hpx] at hbase
  exact hbase.1

/-- **Stacks Project, Tag 05L3: a criterion for purity.** Let `f : X ⟶ S` be locally of finite
type and `F` a quasi-coherent `𝒪_X`-module of finite type which is flat over `S` at every point
of the fibre `X_s`. A point of `Ass_{X/S}(F)` which specializes to some point of `X_s`
specializes to a point of `X_s` associated to the restriction of `F` to `X_s`. -/
@[stacks 05L3]
theorem exists_specializes_mem_associatedPoints_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hflat : ∀ t : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s t))
    {x' : X} (hx' : x' ∈ Stacks.Divisors.relativeAssassin f F)
    (hmeets : ∃ t : f.fiber s, x' ⤳ f.fiberι s t) :
    ∃ x : f.fiber s, x' ⤳ f.fiberι s x ∧
      x ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
  classical
  have hover : ∀ w : f.fiber s, f (f.fiberι s w) = s := fun w => (f.range_fiberι s).le ⟨w, rfl⟩
  obtain ⟨t, ht⟩ := hmeets
  obtain ⟨Y, hY⟩ : ∃ Y : X.IdealSheafData,
      Y = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x'} : Set X)) := ⟨_, rfl⟩
  -- The reduced closed subscheme `Y` on the closure of `x'` has that closure as its points.
  have hrange : Set.range Y.subschemeι = closure ({x'} : Set X) :=
    Y.range_subschemeι.trans (by rw [hY]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  -- The fibre of `Y ⟶ S` over `s` is nonempty, since the closure of `x'` meets `X_s`.
  obtain ⟨y, hy⟩ : f.fiberι s t ∈ Set.range Y.subschemeι := by
    rw [hrange]
    exact ht.mem_closure
  have hgy : (Y.subschemeι ≫ f) y = s := by
    rw [Scheme.Hom.comp_apply, hy]
    exact hover t
  -- Take the generic point of a component of that fibre through the meeting point.
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({((Y.subschemeι ≫ f).fiberHomeo s).symm ⟨y, hgy⟩} :
      Set ((Y.subschemeι ≫ f).fiber s))) isIrreducible_singleton.closure
  have hcomp : closure ({hC.1.genericPoint} : Set ((Y.subschemeι ≫ f).fiber s)) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber s) := by
    rwa [hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)]
  -- Its image in `X` is a point of `X_s`, at which `F` is flat over `S` by hypothesis.
  have hfs : f (Y.subschemeι ((Y.subschemeι ≫ f).fiberι s hC.1.genericPoint)) = s :=
    Stacks.ClosedFibreGenericPoint.apply_fiberι_comp f Y.subschemeι s _
  obtain ⟨x, hx⟩ : Y.subschemeι ((Y.subschemeι ≫ f).fiberι s hC.1.genericPoint) ∈
      Set.range (f.fiberι s) := (f.range_fiberι s).ge hfs
  have hηrel : Y.subschemeι ((Y.subschemeι ≫ f).fiberι s hC.1.genericPoint)
      ∈ Stacks.Divisors.relativeAssassin f F :=
    mem_relativeAssassin_of_isGenericPoint_fibre_closure f F x' hx' Y hY s
      hC.1.genericPoint hcomp (by rw [← hx]; exact hflat x)
  refine ⟨x, specializes_iff_mem_closure.mpr ?_, ?_⟩
  · rw [hx, ← hrange]
    exact Set.mem_range_self _
  · exact (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin f F s x).mpr
      (by rw [hx]; exact hηrel)

end Stacks.RelativeAssassin

end
