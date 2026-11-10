module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBijectivePropagation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafIsoOverSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Isomorphisms of quasi-coherent algebras over a quasi-compact open subspace

The proof of [Stacks, Tag 0GUM] asks that a stage `𝒜ᵢ` of a colimit presentation of a
quasi-coherent algebra `𝒜` agree with `𝒜` over a quasi-compact open subspace `V` of the algebraic
space `F`, and it checks this on a single affine étale chart: `V` is quasi-compact, so it has an
affine scheme `U` étale and surjective over it, and a morphism of quasi-coherent modules which is
an isomorphism over `U` is one over `V`.  This file proves the two halves of that argument and
their combination for algebra sheaves.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_affine_ofObjects_mem_of_isOpenImmersion`: a
  quasi-compact open subspace `V` of an algebraic space `F` has an affine étale chart `U` of `F`
  lying in `V` such that every étale chart of `F` lying in `V` is covered by the charts mapping
  to `U`.
* `AlgebraicGeometry.Space.bijective_val_app_of_ofObjects_mem`: a morphism of `𝒪_F`-modules
  cartesian on affine charts which is bijective on the sections over an affine chart `U` is
  bijective on the sections over every affine chart covered by the charts mapping to `U`.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIsoOver_of_bijective_of_ofObjects_mem`: a morphism of
  quasi-coherent algebra sheaves which is bijective on the sections over such a chart `U` of `V`
  is an isomorphism over `V`.

## Implementation notes

The chart `U` of the first result is an affine scheme `U₀` with an étale surjection
`a : U₀ ⟶ V`, composed with the inclusion of `V`, which is étale.  The surjection is
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover`, `V`
being an algebraic space because its inclusion is representable.  An étale chart `W` of `F`
lying in `V` factors through `V`, and the base change of `a` along that factorization is an
étale surjection onto `W` which maps to `U`; its one-element family covers `W`, exactly as in
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`.

The descent of bijectivity uses a finite jointly faithfully flat family of affine charts inside
the covering sieve (`AlgebraicGeometry.Space.exists_finite_affine_faithfullyFlat_pi_le`).  Over
each member, which maps to `U`, the morphism is bijective by
`AlgebraicGeometry.Space.bijective_val_app_of_bijective_of_cartesian`.  Surjectivity over `W` is
the joint detection of images
`AlgebraicGeometry.Space.jointlyDetectsRange_of_isCartesianOnAffineCharts`, and injectivity is
`AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span` for the empty family: a section
whose restrictions to the members all vanish is zero.

## References

* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### A single affine chart covering a quasi-compact open subspace -/

/-- **A quasi-compact open subspace has a single affine étale chart covering it.**  For an open
subspace `V` of an algebraic space `F` which is quasi-compact, there is an étale chart `U` of `F`
with affine underlying scheme, lying in `V`, such that every étale chart `W` of `F` lying in `V`
is covered, in the small étale site of `F`, by the charts mapping to `U`.

The chart is an affine scheme étale and surjective over `V`, composed with the inclusion of `V`;
over a chart `W` lying in `V`, the base change of the surjection along the factorization of `W`
through `V` is an étale surjection onto `W` mapping to `U`. -/
theorem SmallEtale.exists_affine_ofObjects_mem_of_isOpenImmersion
    (hF : IsAlgebraicSpace B S hS F) (V : Subfunctor F)
    (hV : IsOpenImmersion B S hS V.ι) (hVqc : IsQuasiCompactSpace B S hS V.toFunctor) :
    ∃ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) ∧
        Subfunctor.range U.obj.hom ≤ V ∧
        ∀ W : SmallEtale B S hS F, Subfunctor.range W.obj.hom ≤ V →
          Sieve.ofObjects (fun _ : PUnit.{u + 2} => U) W ∈ SmallEtale.topology B S hS F W := by
  have hValg : IsAlgebraicSpace B S hS V.toFunctor :=
    AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS V.ι hV.rep hF
  obtain ⟨U₀, a, hU₀, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS V.toFunctor hValg).1
      hVqc
  have hetP := (isEtale_iff_presheaf_of_yoneda B S hS a).1 het
  have hcomp : IsEtale B S hS (a ≫ V.ι) := fun T φ hφ => by
    rw [← Category.assoc]
    exact isEtale_of_isOpenImmersion B S hS hV T (φ ≫ a) (het T φ hφ)
  let U : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (a ≫ V.ι), (isEtale_iff_presheaf_of_yoneda B S hS _).1 hcomp⟩
  refine ⟨U, hU₀, ?_, fun W hW => ?_⟩
  · rintro T _ ⟨x, rfl⟩
    exact (a.app T x).2
  have hrep : yoneda.relativelyRepresentable a := hetP.rep
  -- The factorization of `W` through `V`, and the base change of `a` along it.
  set w : yoneda.obj W.obj.left ⟶ V.toFunctor := Subfunctor.lift W.obj.hom hW with hwdef
  set P := hrep.pullback w
  set q : P ⟶ W.obj.left := hrep.snd w
  set p : P ⟶ U₀ := hrep.fst' w with hp
  have hw : yoneda.map p ≫ a = yoneda.map q ≫ w := by
    rw [hp, Functor.relativelyRepresentable.map_fst']
    exact hrep.w w
  have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    hetP.property w (hrep.fst w) (hrep.snd w) (hrep.isPullback w)
  have hqSurj : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    hsurj.property w (hrep.fst w) (hrep.snd w) (hrep.isPullback w)
  -- The base change is an étale chart of `F`, over `W` and over `U`.
  set Vc : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map q ≫ W.obj.hom),
      etale_comp_of_scheme B S hS q W.obj.hom hqEtale W.property⟩
  set c : Vc ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk q rfl)
  have hpU : yoneda.map p ≫ (a ≫ V.ι) = yoneda.map q ≫ W.obj.hom := by
    rw [← Category.assoc, hw, Category.assoc, hwdef, Subfunctor.lift_ι]
  set b : Vc ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p hpU)
  have hpre : Presieve.singleton c ∈ SmallEtale.precoverage B S hS F W := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact B.singleton_mem_etalePrecoverage _ hqSurj hqEtale
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hpre)
  rintro Z f ⟨T, h, k, ⟨⟩, rfl⟩
  exact ⟨PUnit.unit, ⟨h ≫ b⟩⟩

variable {B S hS F} {hF : IsAlgebraicSpace B S hS F}

/-! ### Descent of bijectivity along the charts mapping to one affine chart -/

/-- **A morphism of `𝒪_F`-modules cartesian on affine charts which is bijective on the sections
over an affine chart `U` is bijective on the sections over every affine chart `W` covered by the
charts mapping to `U`.**

The covering sieve of `W` contains a finite family of affine charts whose chart restrictions are
jointly faithfully flat; each member maps to `U`, so the morphism is bijective over it
(`AlgebraicGeometry.Space.bijective_val_app_of_bijective_of_cartesian`).  Surjectivity over `W`
then descends by `AlgebraicGeometry.Space.jointlyDetectsRange_of_isCartesianOnAffineCharts`, and
injectivity by `AlgebraicGeometry.Space.mem_span_of_forall_restrict_mem_span` applied to the
empty family, which says that a section of the source over `W` restricting to zero on every
member is zero. -/
theorem bijective_val_app_of_ofObjects_mem {G H : Modules.{u, u} B S hS F hF} (q : G ⟶ H)
    (hG : IsCartesianOnAffineCharts G) (hH : IsCartesianOnAffineCharts H)
    {U W : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (hUW : Sieve.ofObjects (fun _ : PUnit.{u + 2} => U) W ∈ SmallEtale.topology B S hS F W)
    (hq : Function.Bijective (q.val.app (op U))) :
    Function.Bijective (q.val.app (op W)) := by
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW hUW
  have hz : ∀ i, Function.Bijective (q.val.app (op (z i))) := fun i => by
    obtain ⟨_, ⟨ρ⟩⟩ := hzT i
    exact bijective_val_app_of_bijective_of_cartesian B S hS F hF q hG hH hU (hzaff i) ρ hq
  refine ⟨?_, fun y => ?_⟩
  · refine (injective_iff_map_eq_zero (q.val.app (op W)).hom).2 fun x hx => ?_
    have hres : ∀ i, chartRestrictLinear G (φ i) x = 0 := fun i => by
      apply (hz i).1
      have e := PresheafOfModules.naturality_apply q.val (φ i).op x
      change q.val.app (op (z i)) (G.val.map (φ i).op x) = q.val.app (op (z i)) 0
      rw [map_zero]
      refine e.trans ?_
      change H.val.map (φ i).op ((q.val.app (op W)).hom x) = 0
      rw [hx]
      exact (H.val.map (φ i).op).hom.map_zero
    have hmem := mem_span_of_forall_restrict_mem_span G hG hW φ hzaff hff
      (Empty.elim : Empty → G.val.obj (op W)) (x := x) fun i => by
        rw [hres i]
        exact Submodule.zero_mem _
    rwa [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hmem
  · exact jointlyDetectsRange_of_isCartesianOnAffineCharts q hG hH hW φ hzaff hff y
      fun i => (hz i).2 _

/-! ### Isomorphisms of quasi-coherent algebra sheaves over a subspace -/

/-- **A morphism of quasi-coherent algebra sheaves which is bijective on the sections over one
affine chart `U` covering a subfunctor `V` is an isomorphism over `V`.**  Here `U` covers `V` in
the sense that every étale chart of `F` lying in `V` is covered by the charts mapping to `U`;
`AlgebraicGeometry.Space.SmallEtale.exists_affine_ofObjects_mem_of_isOpenImmersion` supplies such
a chart for a quasi-compact open subspace.

The underlying modules are quasi-coherent, hence cartesian on affine charts by Stacks 03DX(2)
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`), so
`AlgebraicGeometry.Space.bijective_val_app_of_ofObjects_mem` makes the morphism bijective over
every affine chart lying in `V`. -/
theorem AlgebraSheaf.isIsoOver_of_bijective_of_ofObjects_mem
    {A₁ A₂ : AlgebraSheaf.{u, u} B S hS F hF} (h₁ : A₁.IsQuasicoherent)
    (h₂ : A₂.IsQuasicoherent) (a : A₁ ⟶ A₂) {V : Subfunctor F} {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hUcov : ∀ W : SmallEtale B S hS F, Subfunctor.range W.obj.hom ≤ V →
      Sieve.ofObjects (fun _ : PUnit.{u + 2} => U) W ∈ SmallEtale.topology B S hS F W)
    (ha : Function.Bijective (a.right.hom.app (op U)).hom) :
    AlgebraSheaf.IsIsoOver V a :=
  AlgebraSheaf.isIsoOver_of_bijective fun W hW hWV =>
    bijective_val_app_of_ofObjects_mem (AlgebraSheaf.underlyingModuleMap a)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ h₁)
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ h₂) hU hW
      (hUcov W hWV) ha

end AlgebraicGeometry.Space

end
