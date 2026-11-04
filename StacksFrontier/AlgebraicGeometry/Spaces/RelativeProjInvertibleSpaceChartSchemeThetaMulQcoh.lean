module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeThetaMulRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSquareQcoh

/-!
# The scheme factor of the chart maps of `θ` of Stacks 0D2Z is multiplicative (quasi-coherent)

Let `w : W ⟶ U(ψ)` be a scheme point of the open subspace `U(ψ)` of Stacks 0D2Z.  The middle
factor of the chart map `χ_w` of `θ` (`…InvertibleTwistingRestriction.chartMap`) is the module
attached (Stacks 03DX (2)) to the map `θ` of [Stacks, Tag 01O9] on `W` read along the section
`c_w : W ⟶ W ×_Y Proj_Y(𝒜)` (`…InvertibleTwistingRestriction.chartSchemeTheta`).  Its
multiplicativity on the schemes is
`…InvertibleTwistingRestriction.pullbackTensorIso_inv_comp_map_mulSheaf_comp_chartTheta`; this
file carries it to the quasi-coherent modules on `W`, which is the hypothesis `hQ` of
`…InvertibleTwistingRestriction.representedTensorChartMul_comp_chartSchemeTheta_of_qcoh`, and
discharges that hypothesis.

## Main results

* `AlgebraicGeometry.Space.quasicoherentPullbackMul_comp_eq_of_heq`: the gluing of a
  multiplicative square of quasi-coherent modules from its scheme-level form
  (`…GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq`), at free variables, the
  underlying modules of the quasi-coherent objects given by equations and the underlying morphisms
  heterogeneously equal to the scheme-level ones.
* `…InvertibleTwistingRestriction.quasicoherentPullbackMul_comp_chartSchemeTheta`: **`θ` at a
  scheme point is multiplicative, as morphisms of quasi-coherent modules on `W`**.
* `…InvertibleTwistingRestriction.representedTensorChartMul_comp_chartSchemeTheta`: **the middle
  factor of the chart map is multiplicative at the represented level**, with no hypothesis: the
  hypothesis `hm` of `AlgebraicGeometry.Space.mul_of_factor_squares` for the chart maps.
* `…InvertibleTwistingRestriction.modulePullback_map_thetaSourceMul_comp_chartMap`: **the chart
  maps are multiplicative**, with no hypothesis: the hypothesis `h` of
  `AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom` for the chart maps.

## Implementation notes

The quasi-coherent objects of the gluing lemma are written `⟨N n, _⟩` and `⟨K n, _⟩` with the
modules `N n`, `K n` variables, identified with their scheme-level values by equations which the
lemma substitutes; the underlying morphisms are related to the scheme-level ones by heterogeneous
equations.  At the instance the modules are read off the quasi-coherent objects of
`…chartSchemeTheta` by unification, the equations are `rfl`, and the value of
`…chartSchemeTheta` is `…InvertibleTwistingRestriction.chartSchemeTheta_hom_heq`, which reads it in
the spelling of `…GradedPowerMap`; so no two spellings of a whole composite are compared.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (isInvertible_of_isInvertibleModule)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective



namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section MulGlue

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {W F : BigFppfOver B S hS}
  (c : W ⟶ F)

set_option maxHeartbeats 400000 in
-- eliminating the heterogeneous equalities and matching the scheme-level square unfolds
-- large quasi-coherent module terms, which exceeds the default heartbeat limit
/-- **The multiplicative square of the scheme factor of a chart map, as morphisms of
quasi-coherent modules, from its scheme-level form.**  For a morphism `c : W ⟶ F` of the site, a
homomorphism `θ` of [Stacks, Tag 01O9] on `W` (`P`, read along a right inverse `g` of
`U(ψ) ⊆ W`), and `t : F ⟶ Proj(𝒜)` with `c ≫ t = ρ = g ≫ r`: quasi-coherent modules
`⟨N n, _⟩` on `F` and `⟨K n, _⟩` on `W` with `N n = t^*𝒪(n)` and `K n = ℒ^{⊗ n}`, a multiplication
`U` of the first, morphisms `z_n` and a multiplication `ν` of the second whose underlying morphisms
are heterogeneously equal to the multiplication of `t^*(⨁_n 𝒪(n))`, to
`c^*t^*𝒪(n) ≅ (c ≫ t)^*𝒪(n) = ρ^*𝒪(n) ⟶ ℒ^{⊗ n}` and to the multiplication of `⨁_n ℒ^{⊗ n}`,
satisfy the multiplicative square; the scheme-level square is
`…GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq`.  The scheme `Proj(𝒜)`, the
twists, `ρ` and the modules are variables tied to the spelling of `…GradedPowerMap` by equations,
so that an instance reads them off its own data.  At free variables. -/
theorem quasicoherentPullbackMul_comp_eq_of_heq {S' : Scheme.{u}}
    {A : SheafGradedAlgebra.{u} S'} {f' : (BigFppfOver.toScheme B S hS).obj W ⟶ S'}
    (P : GradedPowerMap A f') (g : (BigFppfOver.toScheme B S hS).obj W ⟶ P.coveringOpen.toScheme)
    (hg : g ≫ P.coveringOpen.ι = 𝟙 _) {Pj : Scheme.{u}} (eP : Pj = (relativeProj A).scheme)
    {t : (BigFppfOver.toScheme B S hS).obj F ⟶ Pj} {ρ : (BigFppfOver.toScheme B S hS).obj W ⟶ Pj}
    (h : (BigFppfOver.toScheme B S hS).map c ≫ t = ρ)
    (eρ : HEq ρ (g ≫ P.globalMorphism (relativeProj A)))
    {Gt : Stacks.AlgebraicGeometry.RelativeProjTwists.SchemeGradedAlgebra Pj}
    (eG : HEq Gt (GradedPowerMap.twD A).algebra) {M : ℤ → Pj.Modules}
    (eM : HEq M (fun n => (GradedPowerMap.twD A).algebra.piece n))
    {Z : ℤ → ((BigFppfOver.toScheme B S hS).obj W).Modules}
    (eZ : Z = fun n => tensorPowerModule _ P.L n)
    {Θ : ∀ n : ℤ, (Scheme.Modules.pullback ρ).obj (M n) ⟶ Z n}
    (hΘ : ∀ n : ℤ, HEq (Θ n) (P.thetaOnSection g hg n))
    {N : ℤ → ((BigFppfOver.toScheme B S hS).obj F).Modules}
    (hq : ∀ n : ℤ, SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj F).ringCatSheaf (N n))
    (eN : N = fun n => (Scheme.Modules.pullback t).obj (Gt.piece n))
    {K : ℤ → ((BigFppfOver.toScheme B S hS).obj W).Modules}
    (hK : ∀ n : ℤ, SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf (K n))
    (eK : K = Z) (i j : ℤ)
    {U : quasicoherentTensorObj B S hS F ⟨N i, hq i⟩ ⟨N j, hq j⟩ ⟶ ⟨N (i + j), hq (i + j)⟩}
    (hU : HEq U.hom (SheafOfModules.GradedAlgebra.mulSheaf
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pbAlgS t Gt) i j))
    (z : ∀ n : ℤ, quasicoherentPullbackObj B S hS c ⟨N n, hq n⟩ ⟶ ⟨K n, hK n⟩)
    (hz : ∀ n : ℤ, HEq (z n).hom
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map c) t).hom.app (M n) ≫
        (Scheme.Modules.pullbackCongr h).hom.app (M n) ≫ Θ n))
    {ν : quasicoherentTensorObj B S hS W ⟨K i, hK i⟩ ⟨K j, hK j⟩ ⟶ ⟨K (i + j), hK (i + j)⟩}
    (hν : haveI := isInvertible_of_isInvertibleModule (L := P.L)
      HEq ν.hom (SheafOfModules.GradedAlgebra.mulSheaf (laurent P.L) i j)) :
    ((quasicoherentPullbackTensorIso B S hS c ⟨N i, hq i⟩ ⟨N j, hq j⟩).inv ≫
      quasicoherentPullbackMap B S hS c U) ≫ z (i + j) =
      quasicoherentTensorHom B S hS W (z i) (z j) ≫ ν := by
  subst eP
  obtain rfl := eq_of_heq eρ
  obtain rfl := eq_of_heq eG
  obtain rfl := eq_of_heq eM
  subst eZ eN eK
  have hz' := fun n => eq_of_heq (hz n)
  exact comp_comp_eq_comp_of_hom_eq _ _ _ _ _
    (P.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq g hg _ t h rfl hΘ i j)
    (ObjectProperty.homMk_hom _)
    ((ObjectProperty.homMk_hom _).trans
      (congrArg (Scheme.Modules.pullback _).map (eq_of_heq hU)))
    (hz' (i + j))
    ((ObjectProperty.homMk_hom _).trans (map_app_comp_obj_map_congr _ (hz' i) (hz' j)))
    (eq_of_heq hν)

end MulGlue

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] modulesMonoidalCategory

section Chart

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤)

/-- **`θ` at a scheme point `w` of `U(ψ)` is multiplicative, as morphisms of quasi-coherent
modules on `W`** (Stacks 0D2Z): the comparison of Stacks 03EL along the section
`c_w : W ⟶ W ×_Y Proj_Y(𝒜)`, followed by the pullback along `c_w` of the multiplication of the
twists of Stacks 01NR and by `…InvertibleTwistingRestriction.chartSchemeTheta` in degree `i + j`,
is the tensor product of `…chartSchemeTheta` in degrees `i` and `j` followed by the
multiplication of the Laurent algebra `⨁_d (w^*ℒ)^{⊗ d}`.  This is
`…GradedPowerMap.pullbackTensorIso_inv_comp_map_mulSheaf_comp_of_heq` at `θ` of the restriction
`x^*ψ`, read through `AlgebraicGeometry.Space.quasicoherentPullbackMul_comp_eq_of_heq`, with
`…chartSchemeTheta` read by `…InvertibleTwistingRestriction.chartSchemeTheta_hom_heq`. -/
theorem quasicoherentPullbackMul_comp_chartSchemeTheta (i j : ℤ) :
    ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.twistPieceQcoh W (x ≫ f.hom) i)
        (s.twistPieceQcoh W (x ≫ f.hom) j)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.twistPieceMul W (x ≫ f.hom) i j)) ≫
      chartSchemeTheta s f L ψ x hx (i + j) =
    quasicoherentTensorHom s.site s.base s.containsBase W (chartSchemeTheta s f L ψ x hx i)
        (chartSchemeTheta s f L ψ x hx j) ≫
      pointLaurentPieceMul L W x i j := by
  refine quasicoherentPullbackMul_comp_eq_of_heq (B := s.site) (S := s.base)
    (hS := s.containsBase) _ (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x))
    ((ofUnitalHom s f L ψ).chartLift x hx) ((ofUnitalHom s f L ψ).chartLift_ι x hx) ?eP
    ((ofUnitalHom s f L ψ).toScheme_map_chartSection_comp_toRelativeProj x hx) ?eρ
    (Gt := Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra W (x ≫ f.hom)))
    ?eG ?eM ?eZ
    (fun n => heq_of_eq (InvertibleTwistingRestriction.chartTheta.eq_1 _ x hx n)) _ ?eN _ ?eK i j
    ?hU (fun n => chartSchemeTheta s f L ψ x hx n)
    (fun n => chartSchemeTheta_hom_heq n x hx) ?hν
  case eP => exact rfl
  case eN => exact rfl
  case eK => exact rfl
  case eZ => exact rfl
  case hU => exact heq_of_eq ((congrArg (·.hom)
    (RelativeProjSituation.twistPieceMul.eq_1 s W (x ≫ f.hom) i j)).trans
      (ObjectProperty.homMk_hom _))
  case hν => exact (heq_of_eq (pointLaurentPieceMul_hom L W x i j)).trans HEq.rfl
  all_goals exact HEq.rfl

end Chart

section Represented

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)

/-- **`θ` at a scheme point `w : W ⟶ U(ψ)` is multiplicative, as morphisms of quasi-coherent
modules on `W`**: `…quasicoherentPullbackMul_comp_chartSchemeTheta` at the underlying scheme point
of `X`, in exactly the form of the hypothesis `hQ` of
`…InvertibleTwistingRestriction.representedTensorChartMul_comp_chartSchemeTheta_of_qcoh`. -/
theorem quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint (i j : ℤ) :
    ((quasicoherentPullbackTensorIso s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) i)
          (s.twistPieceQcoh W (locusPoint w ≫ f.hom) j)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceMul W (locusPoint w ≫ f.hom) i j)) ≫
        chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) (i + j) =
      quasicoherentTensorHom s.site s.base s.containsBase W
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) i)
          (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) j) ≫
        pointLaurentPieceMul L W (locusPoint w) i j :=
  quasicoherentPullbackMul_comp_chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) i j

/-- **The middle factor of the chart map of `θ` is multiplicative** (Stacks 0D2Z): the hypothesis
`hm` of `AlgebraicGeometry.Space.mul_of_factor_squares` for the chart maps,
`…InvertibleTwistingRestriction.representedTensorChartMul_comp_chartSchemeTheta_of_qcoh` with its
hypothesis discharged by
`…InvertibleTwistingRestriction.quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint`. -/
theorem representedTensorChartMul_comp_chartSchemeTheta (i j : ℤ) :
    type_of% (representedTensorChartMul_comp_chartSchemeTheta_of_qcoh w i j
      (quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint w i j)) :=
  representedTensorChartMul_comp_chartSchemeTheta_of_qcoh w i j
    (quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint w i j)

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The chart maps of `θ` are multiplicative** (Stacks 0D2Z), with no hypothesis: the hypothesis
`h` of `AlgebraicGeometry.Space.mul_comp_pointFamilyDescendedHom` for
`…InvertibleTwistingRestriction.chartMap`,
`…InvertibleTwistingRestriction.modulePullback_map_thetaSourceMul_comp_chartMap_of_qcoh` with its
hypothesis discharged by
`…InvertibleTwistingRestriction.quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint`. -/
theorem modulePullback_map_thetaSourceMul_comp_chartMap (i j : ℤ) :
    type_of% (modulePullback_map_thetaSourceMul_comp_chartMap_of_qcoh w Px i j
      (quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint w i j)) :=
  modulePullback_map_thetaSourceMul_comp_chartMap_of_qcoh w Px i j
    (quasicoherentPullbackMul_comp_chartSchemeTheta_locusPoint w i j)

end Represented

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
