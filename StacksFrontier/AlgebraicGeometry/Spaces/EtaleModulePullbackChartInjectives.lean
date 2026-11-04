module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionPreservesInjectivesEssentiallySmall
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of modules to an étale chart preserves injectives

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `W` be
an étale scheme chart of `X`.  Pullback of `𝒪_X`-modules along the structure morphism of `W` is
restriction of sheaves of modules to the localization of the small étale site of `X` at `W`,
read through the comparison equivalence of Stacks 04M0.  Restriction to a localized site
preserves injective objects (Stacks 03F3, part (1)), and so does an equivalence; therefore
pullback along the structure morphism of a chart carries injective `𝒪_X`-modules to injective
`𝒪_W`-modules.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback_chartToSpace`:
  **Stacks 03F3, part (1), at the small étale site of an algebraic space.** Pullback of
  `𝒪_X`-modules along the structure morphism of an étale scheme chart preserves injective
  objects.  This is the input that the higher-direct-image clause of Stacks 03LX carries as a
  hypothesis.
* `AlgebraicGeometry.Space.SmallEtale.coverPreserving_chartLocalizationInverse` and
  `AlgebraicGeometry.Space.SmallEtale.isContinuous_chartLocalizationInverse`: the inverse of the
  comparison equivalence of Stacks 04M0 is cover preserving, hence continuous, for the
  localization of the small étale topology at the chart and the small étale topology of the
  chart.
* `AlgebraicGeometry.Space.chartLocalizationModuleEquivalence`: the `𝒪_X`-modules on the
  localized site and the `𝒪_W`-modules on the small étale site of the chart are equivalent.

## Implementation notes

The proof is a factorization.  By `AlgebraicGeometry.Space.chartLocalization_comp_forget` the
functor of sites along which the pullback restricts sections is the comparison functor of
Stacks 04M0 followed by the projection of the slice, so the pullback is the composite of
`SheafOfModules.overFunctor` with restriction along the comparison equivalence.  No change of
scalars occurs on either leg, and `SheafOfModules.pushforwardComp` is
`CategoryTheory.Iso.refl`, so the composite and the pullback agree on the nose; the agreement is
used one module at a time, which is why the main theorem is proved from the constructor of
`CategoryTheory.Functor.PreservesInjectiveObjects` rather than by composing the two
preservation statements — comparing the two *functors* exhausts the definitional unfolder.
The first factor preserves injectives by
`Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall`,
instantiated at the small étale site of `X`, whose objects lie one universe above its morphisms;
the second is an equivalence by `SheafOfModules.pushforwardPushforwardEquivalence`, whose two
coherence conditions hold on the nose since the unit and the counit of the comparison are the
identity on underlying objects of the big fppf site, which is all that the structure sheaf of
global regular functions sees.

`SheafOfModules.pushforwardPushforwardEquivalence` needs continuity of *both* functors of the
comparison equivalence.  Only continuity of the comparison functor itself is available, so
cover preservation of the inverse is proved here, by checking it on the generating families of
the localized topology: a covering family of the slice is a covering family of charts after
forgetting the structure morphism, and the inverse comparison leaves the underlying objects of
the big fppf site unchanged.  Continuity then follows from representable flatness of a right
adjoint.

As elsewhere in this directory, the hypotheses of the general statements have to be restated at
the reduced spelling of the site: instance search does not unfold the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, nor the passage from
`AlgebraicGeometry.Space.chartSpace` to the represented presheaf.  The chart of
`AlgebraicGeometry.Space.chartLocalizationModuleEquivalence` is taken in the underlying category
of the ringed site rather than in `AlgebraicGeometry.Space.SmallEtale` for the same kind of
reason: the objects of `CategoryTheory.Over W` live in the maximum of the two universes of the
site, and stating the slice over an object of the latter collapses that maximum, after which the
`CategoryTheory.Category` instance of the slice is no longer matched.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SmallEtale

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (X : SmallEtale B S hS F)

/-- The inverse of the comparison functor of Stacks 04M0 is an equivalence of categories. -/
instance isEquivalence_chartLocalizationInverse :
    (chartLocalizationInverse B S hS F X).IsEquivalence :=
  (chartLocalizationEquivalence B S hS F X).isEquivalence_inverse

/-- The inverse of the comparison functor of Stacks 04M0 is cover preserving for the
localization of the small étale topology of `F` at the chart `X` and the small étale topology of
the chart: a covering family of the slice is a covering family of étale charts of `F` after
forgetting the structure morphism to `X`, and the inverse comparison leaves the underlying
objects of the big fppf site of `S` unchanged. -/
theorem coverPreserving_chartLocalizationInverse :
    CoverPreserving ((topology B S hS F).over X)
      (topology B S hS (yoneda.obj ((toOver B S hS F).obj X)))
      (chartLocalizationInverse B S hS F X) := by
  rw [over_topology_eq B S hS F X]
  refine coverPreserving_of_generators (chartLocalizationInverse B S hS F X) _ _ ?_
  intro A R hR
  change R.map (Over.forget X) ∈ precoverage B S hS F ((Over.forget X).obj A) at hR
  obtain ⟨E, hEeq, hE⟩ := (mem_precoverage_iff B S hS F
    (X := (Over.forget X).obj A) (R := R.map (Over.forget X))).mp hR
  have hΨscheme : chartLocalizationInverse B S hS F X ⋙
      toSchemes B S hS (yoneda.obj ((toOver B S hS F).obj X)) =
      Over.forget X ⋙ toSchemes B S hS F :=
    Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)
  let E' : PreZeroHypercover.{u + 1} A :=
    { I₀ := E.I₀
      X i := Over.mk (E.f i ≫ A.hom)
      f i := Over.homMk (E.f i) (by simp) }
  have hsub : E'.presieve₀ ≤ R := by
    intro Z f hf
    obtain ⟨i⟩ := hf
    have hi : (R.map (Over.forget X)) (E.f i) := by
      rw [hEeq]
      exact E.presieve₀_f i
    obtain ⟨T, hT, g, hg, hfac⟩ := Presieve.map_iff.mp hi
    obtain ⟨T₀, tHom, rfl⟩ := T.mk_surjective
    obtain rfl : T₀ = E.X i := by simpa using hT
    have hglef : g.left = E.f i := by simpa using hfac
    obtain rfl : tHom = E.f i ≫ A.hom := by simpa [hglef] using (Over.w g).symm
    simpa [(Over.OverMorphism.ext hglef : g = E'.f i)] using hg
  have hE' : (E'.map (chartLocalizationInverse B S hS F X)).presieve₀ ∈
      precoverage B S hS (yoneda.obj ((toOver B S hS F).obj X))
        ((chartLocalizationInverse B S hS F X).obj A) := by
    refine (mem_precoverage_iff B S hS (yoneda.obj ((toOver B S hS F).obj X))
      (X := (chartLocalizationInverse B S hS F X).obj A)
      (R := (E'.map (chartLocalizationInverse B S hS F X)).presieve₀)).2
      ⟨E'.map (chartLocalizationInverse B S hS F X), rfl, ?_⟩
    have hmap : (E'.map (chartLocalizationInverse B S hS F X)).map
        (toSchemes B S hS (yoneda.obj ((toOver B S hS F).obj X))) =
        E.map (toSchemes B S hS F) := by
      show E'.map (chartLocalizationInverse B S hS F X ⋙
        toSchemes B S hS (yoneda.obj ((toOver B S hS F).obj X))) = _
      cases hΨscheme
      rfl
    show B.etaleCovering ⟨(toSchemes B S hS (yoneda.obj ((toOver B S hS F).obj X))).obj
        ((chartLocalizationInverse B S hS F X).obj A),
      (E'.map (chartLocalizationInverse B S hS F X)).map
        (toSchemes B S hS (yoneda.obj ((toOver B S hS F).obj X)))⟩
    rw [hmap]
    exact hE
  have hle : Sieve.generate (E'.presieve₀.map (chartLocalizationInverse B S hS F X)) ≤
      Sieve.generate (R.map (chartLocalizationInverse B S hS F X)) := by
    rw [Sieve.generate_map_eq_functorPushforward, Sieve.generate_map_eq_functorPushforward]
    exact Sieve.functorPushforward_monotone _ A (Sieve.generate_mono hsub)
  rw [← Sieve.generate_map_eq_functorPushforward]
  refine GrothendieckTopology.superset_covering _ hle ?_
  simpa [PreZeroHypercover.presieve₀_map] using (Precoverage.generate_mem_toGrothendieck hE')

/-- The inverse of the comparison functor of Stacks 04M0 is continuous for the localization of
the small étale topology of `F` at the chart and the small étale topology of the chart, so
restriction along it carries sheaves to sheaves. -/
instance isContinuous_chartLocalizationInverse :
    (chartLocalizationInverse B S hS F X).IsContinuous
      ((topology B S hS F).over X)
      (topology B S hS (yoneda.obj ((toOver B S hS F).obj X))) := by
  have : (chartLocalizationInverse B S hS F X).IsRightAdjoint :=
    (chartLocalizationEquivalence B S hS F X).isRightAdjoint_inverse
  exact Functor.isContinuous_iff_coverPreserving.2
    (coverPreserving_chartLocalizationInverse B S hS F X)

end SmallEtale

variable (X : AlgebraicSpaces B S hS)

/-- `AlgebraicGeometry.Space.SmallEtale.isContinuous_chartLocalizationInverse` phrased for the
algebraic space `AlgebraicGeometry.Space.chartSpace` represented by the chart, which is the form
typeclass search can use: the two statements are definitionally equal, but the passage from
`chartSpace B S hS X W` to the represented presheaf unfolds
`AlgebraicGeometry.Space.chartOver`, which instance search does not do. -/
instance isContinuous_chartLocalizationInverse_chartSpace (W : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationInverse B S hS X.1 W).IsContinuous
      ((SmallEtale.topology B S hS X.1).over W)
      (SmallEtale.topology B S hS (chartSpace B S hS X W).1) :=
  SmallEtale.isContinuous_chartLocalizationInverse B S hS X.1 W

/-- The comparison equivalence of Stacks 04M0 at an étale scheme chart `W` of `X`, read on
sheaves of modules: the `𝒪_X`-modules on the localization of the small étale site of `X` at `W`
are the `𝒪_W`-modules on the small étale site of the chart.

Both functors are restriction of sections along the comparison functors, with no change of
scalars: the structure sheaf of global regular functions only sees the underlying object of the
big fppf site of `S`, which the comparison leaves unchanged. -/
noncomputable def chartLocalizationModuleEquivalence
    (W : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    SheafOfModules.{u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).over W) ≌
      Modules.{u, u} B S hS (chartSpace B S hS X W).1 (chartSpace B S hS X W).2 := by
  let E : SmallEtale B S hS (chartSpace B S hS X W).1 ≌ Over W :=
    SmallEtale.chartLocalizationEquivalence B S hS X.1 W
  have hc1 : E.functor.IsContinuous
      (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).J
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over W) :=
    isContinuous_chartLocalization_chartSpace B S hS X W
  have hc2 : E.inverse.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over W)
      (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).J :=
    isContinuous_chartLocalizationInverse_chartSpace B S hS X W
  let RX := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
  let RW := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
    (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).O)
  let φ : RW ⟶ (E.functor.sheafPushforwardContinuous RingCat.{u}
      (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1 (chartSpace B S hS X W).2).J
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over W)).obj (RX.over W) := 𝟙 _
  let ψ : RX.over W ⟶ (E.inverse.sheafPushforwardContinuous RingCat.{u}
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over W)
      (smallEtaleRingedSite B S hS (chartSpace B S hS X W).1
        (chartSpace B S hS X W).2).J).obj RW := 𝟙 _
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) (RX.over W).obj =
      ψ.hom ≫ E.inverse.op.whiskerLeft φ.hom := by
    ext : 2
    exact rfl
  have H₂ : φ.hom ≫ E.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RW.obj = 𝟙 RW.obj := by
    ext : 2
    exact rfl
  exact SheafOfModules.pushforwardPushforwardEquivalence.{u} E φ ψ H₁ H₂

/-- **Stacks 03F3, part (1), at the small étale site of an algebraic space.** Pullback of
`𝒪_X`-modules along the structure morphism of an étale scheme chart `W` of an algebraic space
`X` carries injective `𝒪_X`-modules to injective `𝒪_W`-modules.

Indeed that pullback is restriction to the localization of the small étale site of `X` at `W`,
which preserves injectives because its left adjoint, extension by zero, preserves
monomorphisms, followed by the equivalence of Stacks 04M0 on sheaves of modules. -/
@[stacks 03F3 "part (1), at the small étale site of an algebraic space",
  sga "4 V 4.11" "1) injective, etale site"]
theorem preservesInjectiveObjects_etaleModulePullback_chartToSpace
    (W : SmallEtale B S hS X.1) :
    (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)).PreservesInjectiveObjects := by
  have hinj : (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) W).PreservesInjectiveObjects :=
    Stacks.Cohomology.Localization.preservesInjectiveObjects_overFunctor_of_essentiallySmall
      (SmallEtale.topology B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) W
  have := (chartLocalizationModuleEquivalence B S hS X W).isEquivalence_functor
  exact ⟨fun {M} hM => (Functor.injective_obj_of_injective
    (chartLocalizationModuleEquivalence B S hS X W).functor (hinj.injective_obj hM) :)⟩

end AlgebraicGeometry.Space

end
