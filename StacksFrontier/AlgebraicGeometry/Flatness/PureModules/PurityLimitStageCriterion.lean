module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageBaseChange

/-!
# The purity criterion in the form of a neighbourhood of the base point

Tag 05L4 characterizes purity of `ℱ` along `X_s` by a containment condition on the relative
assassin of `ℱ ×_S S'` over the points of an elementary étale neighbourhood `(S', s')` of
`(S, s)` which specialize to `s'`. The proof that purity passes to a finite stage in Tag 05MA
uses that characterization in a different shape: purity holds if and only if the *fibrewise
containment locus*

`E = {y ∈ S' | Ass((ℱ ×_S S')_y) ⊆ W}`

contains an open neighbourhood of `s'`, where `W` is the image of the chart `X' ⟶ X ×_S S'`.
The implication from purity uses that `E` is locally constructible, which is Tag 05KR, together
with Tag 05LW; the implication towards purity needs no constructibility at all, because a point
specializing to `s'` lies in every open neighbourhood of `s'`.

That shape is what descends along an inverse limit: a containment of opens descends, whereas a
condition quantified over specializations does not.

## Main definitions

* `AlgebraicGeometry.chartContainmentLocus` is the locus `E` above.

## Main results

* `AlgebraicGeometry.associatedPoints_fiber_subset_preimage_iff_forall_relativeAssassin`
  rewrites the fibrewise containment condition at `y` as a condition on the relative assassin,
  which is the form stable under the comparison isomorphisms between chosen pullbacks.
* `AlgebraicGeometry.mem_relativeAssassin_isoOver_iff`: the relative assassin of the pullback of
  a module along an isomorphism of schemes over the base is the inverse image of the relative
  assassin of the module.
* `AlgebraicGeometry.isPureAlong_of_isOpen_subset_chartContainmentLocus`: purity along `X_s`
  follows from an open neighbourhood of `s'` inside the fibrewise containment locus.
* `AlgebraicGeometry.chartContainmentLocus_mem_nhds_of_isPureAlong`: conversely, purity along
  `X_s` makes the fibrewise containment locus a neighbourhood of `s'`, given that it is locally
  constructible.

## Implementation notes

The two implications are stated separately rather than as one `Iff` because they have different
hypotheses: only the direction *from* purity needs local constructibility of the locus, which is
Tag 05KR and is not available in this library. Both take the data of the chart produced by Tags
05KW and 05K6 — an elementary étale neighbourhood `(S', s')`, an étale `g : X' ⟶ X` over `S'`,
purity of `g^*ℱ` along `X'_{s'}` and the covering condition on the fibre — in exactly the shape
in which `AlgebraicGeometry.isPureAlong_iff_relativeAssassin_specializing_mem_range` consumes
it.

## References

* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 05L4](https://stacks.math.columbia.edu/tag/05L4)
* [Stacks Project, Tag 05LW](https://stacks.math.columbia.edu/tag/05LW)
* [Stacks Project, Tag 05MA](https://stacks.math.columbia.edu/tag/05MA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The fibrewise containment condition as a condition on the relative assassin -/

/-- The associated points of the restriction of `G` to the fibre of `p` over `y` all lie in the
inverse image of `U` exactly when every point of the relative assassin of `G` lying over `y`
lies in `U`. -/
public theorem associatedPoints_fiber_subset_preimage_iff_forall_relativeAssassin
    {P B : Scheme.{u}} (p : P ⟶ B) (G : P.Modules) (U : Set P) (y : B) :
    Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (p.fiberι y)).obj G) ⊆
        p.fiberι y ⁻¹' U ↔
      ∀ x : P, x ∈ Stacks.Divisors.relativeAssassin p G → p x = y → x ∈ U := by
  refine ⟨fun h x hx hxy => ?_, fun h z hz => h _
    ((Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin p G y z).mp hz)
    (Scheme.Hom.apply_fiberι p y z)⟩
  have hz : p.fiberι y ((p.fiberHomeo y).symm ⟨x, hxy⟩) = x := p.fiberι_fiberHomeo_symm _ _
  exact hz ▸ h ((Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin p G y
    ((p.fiberHomeo y).symm ⟨x, hxy⟩)).mpr (by rwa [hz]))

/-- Along an isomorphism of schemes over the base, the relative assassin of the pullback of a
module is the inverse image of the relative assassin of the module. -/
public theorem mem_relativeAssassin_isoOver_iff {Z Z' B : Scheme.{u}} (e : Z ≅ Z')
    (h : Z' ⟶ B) [LocallyOfFiniteType h] (G : Z'.Modules) [G.IsQuasicoherent] (z : Z) :
    z ∈ Stacks.Divisors.relativeAssassin (e.hom ≫ h)
        ((Scheme.Modules.pullback e.hom).obj G) ↔
      e.hom z ∈ Stacks.Divisors.relativeAssassin h G := by
  refine ⟨fun hz => mem_relativeAssassin_map_of_isIso e.hom h G hz, fun hz => ?_⟩
  have hcomp : e.inv ≫ e.hom ≫ h = h := by
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hmod : (Scheme.Modules.pullback e.inv).obj
      ((Scheme.Modules.pullback e.hom).obj G) ≅ G :=
    (Scheme.Modules.pullbackComp e.inv e.hom).app G ≪≫
      eqToIso (by rw [e.inv_hom_id]) ≪≫ (Scheme.Modules.pullbackId Z').app G
  have hzz : e.inv (e.hom z) = z := by simp
  have hGz : ((Scheme.Modules.pullback e.hom).obj G).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent Z.toRingedSpace Z'.toRingedSpace
      e.hom.toLRSHom.toShHom G (show G.IsQuasicoherent from inferInstance)
  have hstart : e.hom z ∈ Stacks.Divisors.relativeAssassin (e.inv ≫ e.hom ≫ h)
      ((Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj G)) := by
    rwa [relativeAssassin_eq_of_moduleIso (e.inv ≫ e.hom ≫ h) hmod, hcomp]
  have hback := mem_relativeAssassin_map_of_isIso (e := e.inv) (h := e.hom ≫ h)
    ((Scheme.Modules.pullback e.hom).obj G) hstart
  rwa [hzz] at hback

/-! ### The fibrewise containment locus of a chart -/

/-- The fibrewise containment locus of the chart: the set of points of the elementary étale
neighbourhood over which every associated point of the fibre of `ℱ ×_S S'` lies in the image of
`X' ⟶ X ×_S S'`. -/
public def chartContainmentLocus {X S X' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {s : S} (U : EtaleNeighborhood S s) (p : X' ⟶ U.scheme) (g : X' ⟶ X)
    (hcomm : g ≫ f = p ≫ U.toBase) : Set U.scheme :=
  {y : U.scheme | Stacks.Divisors.associatedPoints
    ((Scheme.Modules.pullback ((pullback.snd f U.toBase).fiberι y)).obj
      ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)) ⊆
    (pullback.snd f U.toBase).fiberι y ⁻¹' Set.range ⇑(pullback.lift g p hcomm)}

/-- Membership of the fibrewise containment locus, as a condition on the relative assassin. -/
public theorem mem_chartContainmentLocus_iff {X S X' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    {s : S} (U : EtaleNeighborhood S s) (p : X' ⟶ U.scheme) (g : X' ⟶ X)
    (hcomm : g ≫ f = p ≫ U.toBase) (y : U.scheme) :
    y ∈ chartContainmentLocus f F U p g hcomm ↔
      ∀ x : (pullback f U.toBase : Scheme.{u}),
        x ∈ Stacks.Divisors.relativeAssassin (pullback.snd f U.toBase)
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) →
          pullback.snd f U.toBase x = y → x ∈ Set.range ⇑(pullback.lift g p hcomm) :=
  associatedPoints_fiber_subset_preimage_iff_forall_relativeAssassin _ _ _ y

/-! ### The two implications of the criterion -/

/-- **The sufficiency half of the criterion.** If the fibrewise containment locus of the chart
contains an open neighbourhood of the distinguished point of the elementary étale
neighbourhood, then `ℱ` is pure along `X_s`.

No constructibility is needed: a point specializing to `s'` lies in every open set containing
`s'`. -/
public theorem isPureAlong_of_isOpen_subset_chartContainmentLocus
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (p : X' ⟶ U.scheme) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure' : IsPureAlong
      ({ S := U.scheme
         X := X'
         f := p
         F := (Scheme.Modules.pullback g).obj F
         s := U.point } : PrePureSituation.{u}))
    (hcover : ∀ z : (pullback.snd f U.toBase).fiber U.point,
      z ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback ((pullback.snd f U.toBase).fiberι U.point)).obj
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)) →
        ∃ y : X', pullback.lift g p hcomm y =
          (pullback.snd f U.toBase).fiberι U.point z)
    (V : Set U.scheme) (hVopen : IsOpen V) (hVmem : U.point ∈ V)
    (hV : V ⊆ chartContainmentLocus f F U p g hcomm) :
    IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) :=
  (isPureAlong_iff_relativeAssassin_specializing_mem_range f F s U hU p g hcomm
    hflat hpure' hcover).mpr fun x hxass hxspec =>
      (mem_chartContainmentLocus_iff f F U p g hcomm _).mp
        (hV (hxspec.mem_open hVopen hVmem)) x hxass rfl

/-- **The necessity half of the criterion.** If `ℱ` is pure along `X_s` and the fibrewise
containment locus of the chart is locally constructible — which is Tag 05KR — then that locus
is a neighbourhood of the distinguished point of the elementary étale neighbourhood. -/
public theorem chartContainmentLocus_mem_nhds_of_isPureAlong
    {X S X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (s : S) (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (p : X' ⟶ U.scheme) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : X' ⟶ X) [Etale g] (hcomm : g ≫ f = p ≫ U.toBase)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x))
    (hpure' : IsPureAlong
      ({ S := U.scheme
         X := X'
         f := p
         F := (Scheme.Modules.pullback g).obj F
         s := U.point } : PrePureSituation.{u}))
    (hcover : ∀ z : (pullback.snd f U.toBase).fiber U.point,
      z ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback ((pullback.snd f U.toBase).fiberι U.point)).obj
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)) →
        ∃ y : X', pullback.lift g p hcomm y =
          (pullback.snd f U.toBase).fiberι U.point z)
    (hE : IsLocallyConstructible (chartContainmentLocus f F U p g hcomm))
    (hpure : IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u})) :
    chartContainmentLocus f F U p g hcomm ∈ 𝓝 U.point := by
  refine mem_nhds_of_isLocallyConstructible_of_specializes_subset hE fun y hy =>
    (mem_chartContainmentLocus_iff f F U p g hcomm y).mpr fun x hx hxy => ?_
  exact (isPureAlong_iff_relativeAssassin_specializing_mem_range f F s U hU p g hcomm
    hflat hpure' hcover).mp hpure x hx (hxy ▸ hy)

end AlgebraicGeometry

end
