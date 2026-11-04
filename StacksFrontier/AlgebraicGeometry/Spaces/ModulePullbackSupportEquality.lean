module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedMinimalSupport

/-!
# Stacks 07TZ part (3): the support of a pullback is the inverse image of the support

Let `g : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` and let `F` be a
quasi-coherent `𝒪_X`-module of finite type.  Then

`Supp(g^* F) = |g|^{-1}(Supp(F))`.

This is the support clause of Stacks 07TZ part (3); the finite-type clause of the same part is
the already available `AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`.

The proof is the one the source gives, and it runs entirely at geometric points.  The stalk
formula for a pullback

`(g^* F)_{ȳ} ≅ 𝒪_{X', ȳ} ⊗_{𝒪_{X, g ∘ ȳ}} F_{g ∘ ȳ}`

is `AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`, the base-change clause of
Stacks 05VQ, which carries no hypotheses at all.  One inclusion needs nothing else: a tensor
product with a zero factor is zero, so a nonzero stalk of `g^* F` forces a nonzero stalk of `F`
at the image geometric point, and the support of Stacks 04KA is defined by nonvanishing at
*some* geometric point above the given point.  The other inclusion is Nakayama: the stalk
`F_{g ∘ ȳ}` is a finite module over `𝒪_{X, g ∘ ȳ}`, the homomorphism of étale local rings of
Stacks 04NG is local, and base change of a nonzero finite module along a local homomorphism of
local rings is nonzero (`Stacks.Support.nontrivial_tensorProduct_of_isLocalHom`).  Here
quasi-coherence of `F` is used twice: once to know that *every* geometric point above a point
of the support detects it, which is the first equivalence of part (2), and once for the
finiteness of the stalk.

## Main results

* `AlgebraicGeometry.Space.span_range_chartRestrictLinear_of_span_eq_top`: finitely many sections
  generating the sections over an affine étale chart still generate after restriction to an
  affine étale chart over it.
* `AlgebraicGeometry.Space.module_finite_geometricModuleStalk`: the stalk of a quasi-coherent
  module of finite type at a geometric point is a finite module over the étale local ring.
* `AlgebraicGeometry.Space.nontrivial_extendScalars_of_isLocalHom`: the local input, read at
  the categorical extension of scalars.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq` is **Stacks 07TZ, part (3)**.

## Implementation notes

The finiteness of the geometric stalk was recorded as missing in four places of this
development (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion`,
`StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleNoetherianFibreCriterion` and
`StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAdicThickenings`).  It is proved here without
the chartwise comparison of Tag 060Q those notes point at, by spanning the stalk directly:
finitely many sections generate the sections over an *affine* small étale neighbourhood
(`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`), every element of the
stalk is the germ of a section over some neighbourhood, and a common affine refinement of that
neighbourhood and the chosen one rewrites the section as a combination of the restrictions of
the generators, because the base-change comparison between affine charts is surjective for a
quasi-coherent module.  Germs of those combinations are combinations of the germs of the
generators, so the germs of the generators span.

The statement is at module universe `m = u`, that is for
`AlgebraicGeometry.Space.Modules.{u, u}`, because both the first equivalence of part (2) and
the finiteness of the sections over an affine chart are available only there.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

/-! ### The local input, at the categorical extension of scalars -/

/-- **Base change of a nonzero finite module along a local homomorphism of local rings is
nonzero**, read at `ModuleCat.extendScalars`.

This is `Stacks.Support.nontrivial_tensorProduct_of_isLocalHom` with the ring homomorphism in
the bare form the stalk formula of Stacks 05VQ produces it, and with the two factors of the
tensor product in the order `ModuleCat.extendScalars` uses. -/
@[ega "0 1.7.5" "Nakayama step"]
theorem nontrivial_extendScalars_of_isLocalHom {R T : Type v} [CommRing R] [CommRing T]
    (φ : R →+* T) (M : ModuleCat.{v} R) [IsLocalRing R] [IsLocalRing T] [IsLocalHom φ]
    [Module.Finite R M] [Nontrivial M] :
    Nontrivial ((ModuleCat.extendScalars φ).obj M) := by
  let : Algebra R T := φ.toAlgebra
  have : IsLocalHom (algebraMap R T) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  exact (TensorProduct.comm R M T).toEquiv.nontrivial_congr.1
    (Stacks.Support.nontrivial_tensorProduct_of_isLocalHom (R := R) (S := T) (M := M))

/-- A module whose extension of scalars is nonzero is nonzero. -/
theorem nontrivial_of_nontrivial_extendScalars {R T : Type v} [CommRing R] [CommRing T]
    (φ : R →+* T) (M : ModuleCat.{v} R)
    (h : Nontrivial ((ModuleCat.extendScalars φ).obj M)) : Nontrivial M := by
  let : Algebra R T := φ.toAlgebra
  exact Stacks.Support.nontrivial_of_nontrivial_tensorProduct
    ((TensorProduct.comm R M T).toEquiv.nontrivial_congr.2 h)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Generators of the sections survive restriction between affine charts -/

/-- **Finitely many generating sections over an affine étale chart generate, after restriction,
the sections over any affine étale chart above it.**

The base-change comparison of `AlgebraicGeometry.Space.sectionsBaseChange` is surjective
between affine charts for a module cartesian on affine charts, so by
`AlgebraicGeometry.Space.chartBaseChange_surjective_iff_span_eq_top` the restrictions of *all*
the sections over the larger chart span; and the restriction of a section is a combination of
the restrictions of the generators because restriction is semilinear. -/
theorem span_range_chartRestrictLinear_of_span_eq_top {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) (hcart : IsCartesianOnAffineCharts F)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U) (hU : IsAffine (chartScheme U))
    (hV : IsAffine (chartScheme V)) {n : ℕ} (s : Fin n → F.val.obj (op U))
    (hs : Submodule.span (chartRing B S hS X.1 X.2 U) (Set.range s) = ⊤) :
    Submodule.span (chartRing B S hS X.1 X.2 V)
      (Set.range fun i => chartRestrictLinear F f (s i)) = ⊤ := by
  let _ := chartAlgebra (hF := X.2) f
  let _ := chartSectionsModule F f
  have := chartSections_isScalarTower F f
  set T := Submodule.span (chartRing B S hS X.1 X.2 V)
    (Set.range fun i => chartRestrictLinear F f (s i))
  have hmem (x : F.val.obj (op U)) : chartRestrictLinear F f x ∈ T := by
    have hx : x ∈ Submodule.span (chartRing B S hS X.1 X.2 U) (Set.range s) := by
      rw [hs]; exact Submodule.mem_top
    have hfx := Submodule.apply_mem_span_image_of_mem_span (chartRestrictLinear F f) hx
    rw [← Set.range_comp'] at hfx
    exact Submodule.span_le_restrictScalars (chartRing B S hS X.1 X.2 U) _ _ hfx
  refine top_unique ?_
  rw [← (chartBaseChange_surjective_iff_span_eq_top F f).1 (hcart U V hU hV f).2]
  exact Submodule.span_le.2 (Set.range_subset_iff.2 hmem)

/-! ### Finiteness of the stalk at a geometric point -/

/-- **The stalk of a quasi-coherent module of finite type at a geometric point is a finite
module over the étale local ring.**

Choose an affine small étale neighbourhood `N₀` of the geometric point; the sections of `F`
over it form a finite module over `𝒪_X(N₀)` by
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`, so finitely many
sections `s_1, …, s_n` generate them.  Their germs span the stalk: an element of the stalk is
the germ of a section `t` over some neighbourhood `M`, a common affine refinement `Q` of `M`
and `N₀` exists, and over `Q` the restriction of `t` is an `𝒪_X(Q)`-combination of the
restrictions of the `s_i` by
`AlgebraicGeometry.Space.span_range_chartRestrictLinear_of_span_eq_top`; taking germs turns that
combination into a combination of the germs of the `s_i`, since the germ map is semilinear
along `AlgebraicGeometry.Space.etaleLocalRingGerm` and compatible with restriction. -/
theorem module_finite_geometricModuleStalk (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (x : GeometricPoint B S hS X.1) :
    Module.Finite (etaleLocalRing B S hS X.1 x) (geometricModuleStalk B S hS X x F) := by
  classical
  have hcofil := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  obtain ⟨N⟩ := (IsCofiltered.nonempty : Nonempty (SmallEtaleNeighborhood x))
  obtain ⟨N₀, -, hN₀⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x N
  have hcart : IsCartesianOnAffineCharts F :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F hqc
  have : Module.Finite (chartRing B S hS X.1 X.2 N₀.chart) (F.val.obj (op N₀.chart)) :=
    module_finite_sections_of_isFiniteTypeOnSite F hqc hft N₀.chart hN₀
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin
    (R := chartRing B S hS X.1 X.2 N₀.chart) (M := F.val.obj (op N₀.chart))
  have hspan : Submodule.span (etaleLocalRing B S hS X.1 x)
      (Set.range fun i => geometricModuleStalkGerm B S hS X x F N₀ (s i)) = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨M, t, rfl⟩ := geometricModuleStalkGerm_jointly_surjective B S hS X x F z
    obtain ⟨P, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs M N₀
    obtain ⟨Q, q, hQ⟩ := exists_smallEtaleNeighborhoodHom_isAffine B S hS X x P
    have hrest := span_range_chartRestrictLinear_of_span_eq_top B S hS F hcart
      (q ≫ p₂).hom hN₀ hQ s hs
    have ht : chartRestrictLinear F (q ≫ p₁).hom t ∈
        Submodule.span (chartRing B S hS X.1 X.2 Q.chart)
          (Set.range fun i => chartRestrictLinear F (q ≫ p₂).hom (s i)) := by
      rw [hrest]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    have hgerm : geometricModuleStalkGerm B S hS X x F Q
          (chartRestrictLinear F (q ≫ p₁).hom t) =
        geometricModuleStalkGerm B S hS X x F M t :=
      geometricModuleStalkGerm_map B S hS X x F (q ≫ p₁) t
    rw [← hgerm, ← hc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [geometricModuleStalkGerm_smul, chartRestrictLinear_apply,
      geometricModuleStalkGerm_map B S hS X x F (q ≫ p₂) (s i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range _)⟩

/-! ### The support of a pullback -/

variable {X' X : AlgebraicSpaces B S hS}

/-- **Stacks 07TZ, part (3).** Let `g : X' ⟶ X` be a morphism of algebraic spaces over `S` and
let `F` be a quasi-coherent `𝒪_X`-module of finite type.  Then the support of the pullback
`g^* F` of Stacks 03LU is the inverse image of the support of `F`:

`Supp(g^* F) = |g|^{-1}(Supp(F))`.

The pullback is again of finite type by Stacks 03DO,
`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`, which is the other clause of this
part of the tag.

At a geometric point `ȳ` of `X'` the stalk of the pullback is the base change
`(g^* F)_{ȳ} ≅ 𝒪_{X', ȳ} ⊗_{𝒪_{X, g ∘ ȳ}} F_{g ∘ ȳ}` of the stalk of `F` at the image
geometric point, by `AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`.  One inclusion
is `AlgebraicGeometry.Space.nontrivial_of_nontrivial_extendScalars`, which needs no
hypotheses.  The other is `AlgebraicGeometry.Space.nontrivial_extendScalars_of_isLocalHom`: the
stalk of `F` is a finite module over the étale local ring, the homomorphism of étale local
rings of Stacks 04NG is local, and the image geometric point detects the support because `F` is
quasi-coherent (the first equivalence of part (2)). -/
@[stacks 07TZ "part (3): the stalk of a pullback at a geometric point, and the equality of \
supports"]
theorem supportOfSheaf_modulePullback_eq (g : X' ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F) :
    supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) =
      pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) := by
  ext pt
  rw [Set.mem_preimage, mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X' _ pt,
    mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F _]
  have hiso := fun ybar => (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
    (geometricModuleStalkPullbackIso B S hS g ybar F).hom)).nontrivial_congr
  constructor
  · rintro ⟨ybar, rfl, hnt⟩
    exact ⟨geometricPointMap g.hom ybar, geometricPointMap_image g.hom ybar,
      nontrivial_of_nontrivial_extendScalars (etaleLocalRingMap X'.2 g.hom ybar) _
        ((hiso ybar).1 hnt)⟩
  · rintro ⟨xbar, hxb, hntx⟩
    obtain ⟨ybar, rfl⟩ := exists_geometricRepresentative B S hS X'.1 pt
    have : IsLocalRing (etaleLocalRing B S hS X'.1 ybar) :=
      isLocalRing_etaleLocalRing B S hS X'.1 X'.2 ybar
    have : IsLocalRing (etaleLocalRing B S hS X.1 (geometricPointMap g.hom ybar)) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 (geometricPointMap g.hom ybar)
    have : IsLocalHom (etaleLocalRingMap X'.2 g.hom ybar) :=
      isLocalHom_etaleLocalRingMap B S hS X'.2 X.2 g.hom ybar
    have : Module.Finite (etaleLocalRing B S hS X.1 (geometricPointMap g.hom ybar))
        (geometricModuleStalk B S hS X (geometricPointMap g.hom ybar) F) :=
      module_finite_geometricModuleStalk B S hS X F hqc hft (geometricPointMap g.hom ybar)
    have : Nontrivial (geometricModuleStalk B S hS X (geometricPointMap g.hom ybar) F) :=
      (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X F
        (geometricPointMap g.hom ybar) _ (geometricPointMap_image g.hom ybar)).1
        ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X F _).2
          ⟨xbar, hxb, hntx⟩)
    exact ⟨ybar, rfl, (hiso ybar).2
      (nontrivial_extendScalars_of_isLocalHom (etaleLocalRingMap X'.2 g.hom ybar) _)⟩

end AlgebraicGeometry.Space

end
