module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricEvaluationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceChartModels
public import StacksFrontier.Homology.Tor.IndependenceEvaluation

/-!
# Tor independence of algebraic spaces gives Tor independence of a diagram of schemes

Condition (4) of Stacks 08IQ asks for *one* commutative diagram
```
U ⟶ W ⟵ V
↓    ↓    ↓
X ⟶ B ⟵ Y
```
with `U`, `V`, `W` schemes, étale vertical arrows, `W ⟶ B` surjective and `U`, `V` étale and
surjective over the fibre products, in which `U` and `V` are Tor independent over `W` *in the
sense of Stacks 08IA*, that is on their ordinary local rings.  That condition implies condition
(1) — Tor independence of `X` and `Y` over `B` on étale local rings — by
`AlgebraicGeometry.Space.torIndependent_of_torIndependent_scheme_diagram`.  This file proves the
converse: condition (1) implies condition (4).

The diagram is the atlas tower: a scheme chart `W ⟶ B` of the base, then scheme charts of the
two fibre products `X ×_B W` and `Y ×_B W`.  Over such a diagram condition (2) of Stacks 08IQ
gives Tor independence of the three *étale* local rings, and the work is to deduce Tor
independence of the ordinary local rings.  By Stacks 0FXV that is a question about the rings of
sections over a triple of affine opens, and by Stacks 08HX about the localizations of
`Tor_i^{Γ(W, W')}(Γ(U, U'), Γ(V, V'))` at every prime `𝔰` of `Γ(U, U') ⊗_{Γ(W, W')} Γ(V, V')`.
The prime `𝔰` produces an algebraically closed field `Ω` — an algebraic closure of its residue
field, in the site by Stacks 000R — and a pair of geometric points of `U` and `V` over `Ω` with
the same image in `W`, namely the morphisms of schemes `Spec Ω ⟶ U`, `Spec Ω ⟶ V` that the two
evaluations `Γ(U, U') → Ω` and `Γ(V, V') → Ω` define.  Tor independence of the étale local rings
at that pair, descended to the `Type u` models of
`StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceChartModels`, is then fed to Stacks 08HW
through `RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_eval`: the three
models are flat lifts of the three rings of sections, and `𝔰` is the contraction of the kernel of
the evaluation of the models in `Ω`.

## Main results

* `AlgebraicGeometry.Space.torIndependent_scheme_of_torIndependent_yoneda`: Tor independence of
  two representable algebraic spaces over a third, Stacks 08IP, gives Tor independence of the
  three schemes in the sense of Stacks 08IA.  This is the converse of
  `AlgebraicGeometry.Space.torIndependent_yoneda_of_torIndependent_scheme`.
* `AlgebraicGeometry.Space.exists_torIndependent_scheme_diagram_of_torIndependent` is Stacks
  08IQ, condition (1) implies condition (4).

## Implementation notes

The three evaluations `Γ(U, U') → Ω`, `Γ(V, V') → Ω`, `Γ(W, W') → Ω` are the composites of the
evaluation `ε` of the tensor product with the two inclusions and with the structure map; the
three morphisms of schemes they define agree over `W` because the two composites
`Γ(W, W') → Γ(U, U') → Ω` and `Γ(W, W') → Γ(V, V') → Ω` are both `ε ∘ algebraMap`, which is
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec` away from the agreement of the two
morphisms.  Both geometric points are taken over the *same* structure morphism to the base, so
their images in `W` are literally the geometric point of the common composite and no transport
along an equality of structure morphisms appears; see
`AlgebraicGeometry.Space.geometricPointOfSpecHom`.

The asymmetry that remains is that the two models of the étale local ring of the base — one at
the image of the first point, one at the image of the second — are two different rings, equal
only propositionally.  The whole comparison is run over the first of them, and the flatness of
the second factor is transported along
`AlgebraicGeometry.Space.yonedaChartSHCongrEquiv` by
`RingHom.Flat.tensorProduct_lift_congr_base`.  Transporting the *type* instead is not available:
the two are equal by `congrArg` of an equality of geometric points, and such an equality of
types cannot be substituted.

The proof is split into three steps so that no single declaration carries the whole instance
burden: `subsingleton_localizedModule_torObj_of_evalHoms` takes the three morphisms of schemes
and the two evaluation identities as hypotheses and does the algebra,
`subsingleton_localizedModule_torObj_of_evalRingHom` builds those morphisms from the evaluation,
and `AlgebraicGeometry.Space.torIndependent_scheme_of_torIndependent_yoneda` builds the field
and the evaluation from the prime.

## References

* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 08IP](https://stacks.math.columbia.edu/tag/08IP)
* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [Stacks Project, Tag 08HX](https://stacks.math.columbia.edu/tag/08HX)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_torIndep :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_torIndep
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_torIndep B S hS).has_limit _

/-- The geometric evaluation of the étale local ring of a representable space is compatible with
the map on étale local rings induced by a morphism of the site. -/
private theorem geometricEval_etaleLocalRingMap_yoneda {U₀ W₀ : BigFppfOver B S hS}
    (uw : U₀ ⟶ W₀) (ubar : GeometricPoint B S hS (yoneda.obj U₀)) (y) :
    geometricEval B S hS (yoneda.obj U₀) ubar
      (etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map uw) ubar y) =
      geometricEval B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map uw) ubar) y :=
  DFunLike.congr_fun (geometricEval_comp_yoneda B S hS uw ubar
    (etaleLocalRingMap_isEtaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀)
      (yoneda.map uw) ubar)) y

/-- **The vanishing of Stacks 08HX at a prime realized by a pair of geometric points.**  Given
morphisms of schemes `σU : Spec Ω ⟶ U`, `σV : Spec Ω ⟶ V` over a common structure morphism to
the base whose composites into `W` agree, landing in the three affine opens and restricting
sections to the two halves of an evaluation `ε` of the tensor product, the localization of
`Tor_i^{Γ(W, W')}(Γ(U, U'), Γ(V, V'))` at the kernel of `ε` vanishes.

The two morphisms are the two geometric points at which Tor independence of the étale local
rings is read; the three `Type u` models of those rings are flat lifts of the three rings of
sections by Stacks 08HV, and Stacks 08HW descends the vanishing. -/
private theorem subsingleton_localizedModule_torObj_of_evalHoms
    {U₀ V₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    (h : TorIndependent (isAlgebraicSpace_yoneda B S hS U₀) (isAlgebraicSpace_yoneda B S hS V₀)
      (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map uw) (yoneda.map vw))
    {U' : (siteScheme B S hS U₀).Opens} (hU' : IsAffineOpen U')
    {V' : (siteScheme B S hS V₀).Opens} (hV' : IsAffineOpen V')
    {W' : (siteScheme B S hS W₀).Opens} (hW' : IsAffineOpen W')
    (hUW : U' ≤ (BigFppfOver.toScheme B S hS).map uw ⁻¹ᵁ W')
    (hVW : V' ≤ (BigFppfOver.toScheme B S hS).map vw ⁻¹ᵁ W')
    [Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')]
    [Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS V₀, V')]
    (halgU : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS U₀, U') r =
      (((BigFppfOver.toScheme B S hS).map uw).appLE W' U' hUW).hom r)
    (halgV : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS V₀, V') r =
      (((BigFppfOver.toScheme B S hS).map vw).appLE W' V' hVW).hom r)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω)))
    (ε : ↥Γ(siteScheme B S hS U₀, U') ⊗[↥Γ(siteScheme B S hS W₀, W')]
      ↥Γ(siteScheme B S hS V₀, V') →+* Ω)
    (tb : Spec (.of Ω) ⟶ S)
    (σU : Spec (.of Ω) ⟶ siteScheme B S hS U₀)
    (σV : Spec (.of Ω) ⟶ siteScheme B S hS V₀)
    (σW : Spec (.of Ω) ⟶ siteScheme B S hS W₀)
    (hσU : σU ≫ B.inclusion.map U₀.hom = tb)
    (hσV : σV ≫ B.inclusion.map V₀.hom = tb)
    (hσW : σW ≫ B.inclusion.map W₀.hom = tb)
    (hUeq : σU ≫ (BigFppfOver.toScheme B S hS).map uw = σW)
    (hVeq : σV ≫ (BigFppfOver.toScheme B S hS).map vw = σW)
    (hleU : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ≤ σU ⁻¹ᵁ U')
    (hleV : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ≤ σV ⁻¹ᵁ V')
    (hevU : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
        ((σU.appLE U' ⊤ hleU).hom a) =
      ε (a ⊗ₜ[↥Γ(siteScheme B S hS W₀, W')] (1 : ↥Γ(siteScheme B S hS V₀, V'))))
    (hevV : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
        ((σV.appLE V' ⊤ hleV).hom c) =
      ε ((1 : ↥Γ(siteScheme B S hS U₀, U')) ⊗ₜ[↥Γ(siteScheme B S hS W₀, W')] c))
    (i : ℕ) (hi : 0 < i)
    (sp : Ideal (↥Γ(siteScheme B S hS U₀, U') ⊗[↥Γ(siteScheme B S hS W₀, W')]
      ↥Γ(siteScheme B S hS V₀, V'))) [sp.IsPrime] (hsp : sp = RingHom.ker ε) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
      ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
      ↥Γ(siteScheme B S hS V₀, V') i
    Subsingleton (LocalizedModule sp.primeCompl
      (TorChangeOfRings.torObj ↥Γ(siteScheme B S hS W₀, W') i
        ↥Γ(siteScheme B S hS U₀, U') ↥Γ(siteScheme B S hS V₀, V'))) := by
  subst hsp
  -- the two geometric points and their common image
  set ubar := geometricPointOfSpecHom B S hS U₀ hΩ tb σU hσU with hubardef
  set vbar := geometricPointOfSpecHom B S hS V₀ hΩ tb σV hσV with hvbardef
  have hpt : geometricPointMap (yoneda.map uw) ubar =
      geometricPointMap (yoneda.map vw) vbar :=
    (geometricPointMap_geometricPointOfSpecHom_of_eq B S hS uw hΩ tb σU hσU σW hUeq hσW).trans
      (geometricPointMap_geometricPointOfSpecHom_of_eq B S hS vw hΩ tb σV hσV σW
        hVeq hσW).symm
  have hu : chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar) ∈ U' :=
    hleU trivial
  have hv : chartPoint B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar) ∈ V' :=
    hleV trivial
  -- the two evaluations are the geometric evaluations at the two points
  have hevalU : ∀ a : ↥Γ(siteScheme B S hS U₀, U'),
      geometricEval B S hS (yoneda.obj U₀) ubar
        (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj U₀)
          (isAlgebraicSpace_yoneda B S hS U₀) (yonedaIdentityNeighborhood U₀ ubar)
          (((siteScheme B S hS U₀).presheaf.germ U' _ hu).hom a)) =
      ε (a ⊗ₜ[↥Γ(siteScheme B S hS W₀, W')] (1 : ↥Γ(siteScheme B S hS V₀, V'))) := fun a =>
    (geometricEval_chartLocalRingToEtaleLocalRing_germ B S hS
      (isAlgebraicSpace_yoneda B S hS U₀) (yonedaIdentityNeighborhood U₀ ubar) U' hu
      hleU a).trans (hevU a)
  have hevalV : ∀ c : ↥Γ(siteScheme B S hS V₀, V'),
      geometricEval B S hS (yoneda.obj V₀) vbar
        (chartLocalRingToEtaleLocalRing B S hS (yoneda.obj V₀)
          (isAlgebraicSpace_yoneda B S hS V₀) (yonedaIdentityNeighborhood V₀ vbar)
          (((siteScheme B S hS V₀).presheaf.germ V' _ hv).hom c)) =
      ε ((1 : ↥Γ(siteScheme B S hS U₀, U')) ⊗ₜ[↥Γ(siteScheme B S hS W₀, W')] c) := fun c =>
    (geometricEval_chartLocalRingToEtaleLocalRing_germ B S hS
      (isAlgebraicSpace_yoneda B S hS V₀) (yonedaIdentityNeighborhood V₀ vbar) V' hv
      hleV c).trans (hevV c)
  -- the transports along the equality of the two images in the base
  have h₁ : yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map uw) ubar) =
      yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map vw) vbar) :=
    congrArg (fun z : GeometricPoint B S hS (yoneda.obj W₀) =>
      (show CommRingCat.{u} from yonedaChartLocalRing B S hS W₀ z)) hpt
  have h₂ : etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map uw) ubar) =
      etaleLocalRing B S hS (yoneda.obj W₀) (geometricPointMap (yoneda.map vw) vbar) :=
    congrArg (etaleLocalRing B S hS (yoneda.obj W₀)) hpt
  have hw₁₂ : ((BigFppfOver.toScheme B S hS).map uw).base
        (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar)) =
      ((BigFppfOver.toScheme B S hS).map vw).base
        (chartPoint B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar)) :=
    congrArg (fun z : GeometricPoint B S hS (yoneda.obj W₀) =>
      (show ↥(siteScheme B S hS W₀) from
        chartPoint B S hS (yoneda.obj W₀) (yonedaIdentityNeighborhood W₀ z))) hpt
  -- the local-ring structures on the four étale local rings
  have : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS U₀) ubar
  have : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS V₀) vbar
  have : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj W₀)
      (geometricPointMap (yoneda.map uw) ubar)) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS W₀) _
  have : IsLocalRing ↥(etaleLocalRing B S hS (yoneda.obj W₀)
      (geometricPointMap (yoneda.map vw) vbar)) :=
    isLocalRing_etaleLocalRing B S hS _ (isAlgebraicSpace_yoneda B S hS W₀) _
  -- the structure maps of the `Type u` models
  let := yonedaChartSHAlgebra B S hS uw ubar
  let := yonedaChartSHAlgebra B S hS vw vbar
  let := yonedaChartSHAlgebraCongr B S hS uw vw hpt
  have hlocW₁ : IsLocalHom
      (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)).toRingHom :=
    isLocalHom_ringEquiv _
  have hlocW₂ : IsLocalHom
      (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map vw) vbar)).toRingHom :=
    isLocalHom_ringEquiv _
  have hlocA : IsLocalHom (yonedaChartSHEquiv B S hS U₀ ubar).symm.toRingHom :=
    isLocalHom_ringEquiv _
  have hlocC : IsLocalHom (yonedaChartSHEquiv B S hS V₀ vbar).symm.toRingHom :=
    isLocalHom_ringEquiv _
  have hlocφ := isLocalHom_etaleLocalRingMap B S hS (isAlgebraicSpace_yoneda B S hS U₀)
    (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map uw) ubar
  have hlocψ := isLocalHom_etaleLocalRingMap B S hS (isAlgebraicSpace_yoneda B S hS V₀)
    (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map vw) vbar
  have hlocEq : IsLocalHom ((eqToHom h₂).hom) :=
    isLocalHom_ringEquiv ((eqToIso h₂).commRingCatIsoToRingEquiv)
  have : IsLocalHom (algebraMap
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
      (yonedaChartSH B S hS U₀ ubar)) := RingHom.isLocalHom_comp _ _
  have : IsLocalHom (algebraMap
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
      (yonedaChartSH B S hS V₀ vbar)) := RingHom.isLocalHom_comp _ _
  have : IsLocalHom (algebraMap
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
      (yonedaChartSH B S hS V₀ vbar)) := RingHom.isLocalHom_comp _ _
  -- the algebra structures over the rings of sections, source side
  let : Algebra ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))).comp
      ((siteScheme B S hS W₀).presheaf.germ W'
        (((BigFppfOver.toScheme B S hS).map uw).base
          (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar)))
        (hUW hu)).hom).toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS U₀, U') (yonedaChartSH B S hS U₀ ubar) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS U₀ ubar)
        (yonedaChartSH B S hS U₀ ubar)).comp
      ((siteScheme B S hS U₀).presheaf.germ U'
        (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ ubar))
        hu).hom).toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS W₀, W') (yonedaChartSH B S hS U₀ ubar) :=
    ((algebraMap ↥Γ(siteScheme B S hS U₀, U') (yonedaChartSH B S hS U₀ ubar)).comp
      (algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS U₀, U'))).toAlgebra
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
      (yonedaChartSH B S hS U₀ ubar) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
      (yonedaChartSH B S hS U₀ ubar) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      Eq.trans
        (congrArg (algebraMap ↥(yonedaChartLocalRing B S hS U₀ ubar)
            (yonedaChartSH B S hS U₀ ubar))
          ((congrArg ((siteScheme B S hS U₀).presheaf.germ U' _ hu).hom (halgU r)).trans
            (germ_stalkMap_appLE_apply ((BigFppfOver.toScheme B S hS).map uw) hUW hu r).symm))
        (algebraMap_yonedaChartSH_comp B S hS uw ubar _).symm
  have hA := flat_tensorProduct_lift_yonedaChart B S hS uw ubar hU' hW' hUW hu halgU
    (fun _ => rfl) (fun _ => rfl)
  -- the algebra structures over the rings of sections, second side
  let : Algebra ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar)) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))).comp
      ((siteScheme B S hS W₀).presheaf.germ W'
        (((BigFppfOver.toScheme B S hS).map vw).base
          (chartPoint B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar)))
        (hVW hv)).hom).toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS V₀, V') (yonedaChartSH B S hS V₀ vbar) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS V₀ vbar)
        (yonedaChartSH B S hS V₀ vbar)).comp
      ((siteScheme B S hS V₀).presheaf.germ V'
        (chartPoint B S hS (yoneda.obj V₀) (yonedaIdentityNeighborhood V₀ vbar))
        hv).hom).toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS W₀, W') (yonedaChartSH B S hS V₀ vbar) :=
    ((algebraMap ↥Γ(siteScheme B S hS V₀, V') (yonedaChartSH B S hS V₀ vbar)).comp
      (algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS V₀, V'))).toAlgebra
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS V₀, V')
      (yonedaChartSH B S hS V₀ vbar) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
      (yonedaChartSH B S hS V₀ vbar) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      Eq.trans
        (congrArg (algebraMap ↥(yonedaChartLocalRing B S hS V₀ vbar)
            (yonedaChartSH B S hS V₀ vbar))
          ((congrArg ((siteScheme B S hS V₀).presheaf.germ V' _ hv).hom (halgV r)).trans
            (germ_stalkMap_appLE_apply ((BigFppfOver.toScheme B S hS).map vw) hVW hv r).symm))
        (algebraMap_yonedaChartSH_comp B S hS vw vbar _).symm
  have hC₂ := flat_tensorProduct_lift_yonedaChart B S hS vw vbar hV' hW' hVW hv halgV
    (fun _ => rfl) (fun _ => rfl)
  have he₁₂ : ∀ r : ↥Γ(siteScheme B S hS W₀, W'),
      yonedaChartSHCongrEquiv B S hS uw vw hpt
          (algebraMap ↥Γ(siteScheme B S hS W₀, W')
            (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) r) =
        algebraMap ↥Γ(siteScheme B S hS W₀, W')
          (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar)) r := fun r =>
    (yonedaChartSHCongrEquiv_algebraMap B S hS uw vw hpt h₁
      (((siteScheme B S hS W₀).presheaf.germ W' _ (hUW hu)).hom r)).trans
      (congrArg (algebraMap
        ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar)))
        (eqToHom_stalk_germ hw₁₂ (hUW hu) (hVW hv) r))
  have he₁₂' := algebraMap_yonedaChartSHCongrEquiv B S hS uw vw hpt
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
      (yonedaChartSH B S hS V₀ vbar) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply ↥Γ(siteScheme B S hS W₀, W')
          (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
          (yonedaChartSH B S hS V₀ vbar) r).trans
        ((congrArg (algebraMap (yonedaChartSH B S hS W₀
            (geometricPointMap (yoneda.map vw) vbar))
            (yonedaChartSH B S hS V₀ vbar)) (he₁₂ r)).symm.trans
          (he₁₂' (algebraMap ↥Γ(siteScheme B S hS W₀, W')
            (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) r)))
  have hC : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS V₀, V')
        (yonedaChartSH B S hS V₀ vbar))
      (IsScalarTower.toAlgHom ↥Γ(siteScheme B S hS W₀, W')
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
        (yonedaChartSH B S hS V₀ vbar)) fun _ _ => Commute.all _ _).toRingHom :=
    RingHom.Flat.tensorProduct_lift_congr_base
      (yonedaChartSHCongrEquiv B S hS uw vw hpt) he₁₂ he₁₂' hC₂
  -- flatness of the base change on the base
  have hR' := flat_algebraMap_yonedaChartSH B S hS W₀
    (geometricPointMap (yoneda.map uw) ubar) hW' (hUW hu) (fun _ => rfl)
  -- the descent of Tor independence to the `Type u` models
  have hTorSmall := torIndependent_yonedaChartSH B S hS uw vw h ubar vbar hpt
  -- the geometric evaluations of the two models in the field of the geometric points
  let : Algebra (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) Ω :=
    (((geometricEval B S hS (yoneda.obj U₀) ubar).comp
      (yonedaChartSHEquiv B S hS U₀ ubar).toRingHom).comp
      (algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
        (yonedaChartSH B S hS U₀ ubar))).toAlgebra
  have hevU := geometricEval_etaleLocalRingMap_yoneda B S hS uw ubar
  have hevV := geometricEval_etaleLocalRingMap_yoneda B S hS vw vbar
  have hcompat : ∀ r, geometricEval B S hS (yoneda.obj V₀) vbar
        ((yonedaChartSHEquiv B S hS V₀ vbar)
          (algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
            (yonedaChartSH B S hS V₀ vbar) r)) =
      algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) Ω r := by
    intro r
    refine Eq.trans (congrArg (geometricEval B S hS (yoneda.obj V₀) vbar)
      ((yonedaChartSHEquiv B S hS V₀ vbar).apply_symm_apply _)) ?_
    refine Eq.trans (hevV _) ?_
    refine Eq.trans (geometricEval_eqToHom_cast B S hS hpt
      (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map uw) ubar) r) Ω rfl rfl) ?_
    exact ((congrArg (geometricEval B S hS (yoneda.obj U₀) ubar)
      ((yonedaChartSHEquiv B S hS U₀ ubar).apply_symm_apply _)).trans (hevU _)).symm
  exact RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_eval
    ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U') ↥Γ(siteScheme B S hS V₀, V')
    (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
    (yonedaChartSH B S hS U₀ ubar) (yonedaChartSH B S hS V₀ vbar)
    hR' hA hC hTorSmall ε
    { ((geometricEval B S hS (yoneda.obj U₀) ubar).comp
        (yonedaChartSHEquiv B S hS U₀ ubar).toRingHom) with commutes' := fun _ => rfl }
    { ((geometricEval B S hS (yoneda.obj V₀) vbar).comp
        (yonedaChartSHEquiv B S hS V₀ vbar).toRingHom) with commutes' := hcompat }
    hevalU hevalV i hi

/-- The evaluation of the sections over an affine open of `X` along a morphism out of a spectrum
composes with `f` to the evaluation of the sections over an affine open of `Y`. -/
private theorem spec_comp_fromSpec_comp_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U : X.Opens}
    (hU : IsAffineOpen U) {W : Y.Opens} (hW : IsAffineOpen W) (hUW : U ≤ f ⁻¹ᵁ W)
    {R : CommRingCat.{u}} (εA : Γ(X, U) ⟶ R) (εR : Γ(Y, W) ⟶ R)
    (hmap : f.appLE W U hUW ≫ εA = εR) :
    Spec.map εA ≫ hU.fromSpec ≫ f = Spec.map εR ≫ hW.fromSpec := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hW hU hUW, ← Category.assoc, ← Spec.map_comp, hmap]

/-- A morphism of the big fppf site over `S` is compatible with the structure maps to `S`. -/
private theorem comp_inclusion_map_eq_of_comp_eq {U₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀)
    {T : Scheme.{u}} {σU : T ⟶ siteScheme B S hS U₀} {σW : T ⟶ siteScheme B S hS W₀}
    (hUeq : σU ≫ (BigFppfOver.toScheme B S hS).map uw = σW) :
    σU ≫ B.inclusion.map U₀.hom = σW ≫ B.inclusion.map W₀.hom := by
  have : (BigFppfOver.toScheme B S hS).map uw ≫ B.inclusion.map W₀.hom =
      B.inclusion.map U₀.hom := by
    rw [show (BigFppfOver.toScheme B S hS).map uw = B.inclusion.map uw.left from rfl,
      ← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w uw)
  rw [← hUeq, Category.assoc, this]

/-- **The vanishing of Stacks 08HX at a prime presented as the kernel of an evaluation.**  The
same statement with the three morphisms of schemes constructed from the evaluation: each of the
three rings of sections evaluates in `Ω`, and
`AlgebraicGeometry.IsAffineOpen.fromSpec` turns each evaluation into a morphism out of
`Spec Ω`.  The two composites into `W` agree because both are the evaluation of the structure
map of the tensor product. -/
private theorem subsingleton_localizedModule_torObj_of_evalRingHom
    {U₀ V₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    (h : TorIndependent (isAlgebraicSpace_yoneda B S hS U₀) (isAlgebraicSpace_yoneda B S hS V₀)
      (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map uw) (yoneda.map vw))
    {U' : (siteScheme B S hS U₀).Opens} (hU' : IsAffineOpen U')
    {V' : (siteScheme B S hS V₀).Opens} (hV' : IsAffineOpen V')
    {W' : (siteScheme B S hS W₀).Opens} (hW' : IsAffineOpen W')
    (hUW : U' ≤ (BigFppfOver.toScheme B S hS).map uw ⁻¹ᵁ W')
    (hVW : V' ≤ (BigFppfOver.toScheme B S hS).map vw ⁻¹ᵁ W')
    [Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')]
    [Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS V₀, V')]
    (halgU : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS U₀, U') r =
      (((BigFppfOver.toScheme B S hS).map uw).appLE W' U' hUW).hom r)
    (halgV : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS V₀, V') r =
      (((BigFppfOver.toScheme B S hS).map vw).appLE W' V' hVW).hom r)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω)))
    (ε : ↥Γ(siteScheme B S hS U₀, U') ⊗[↥Γ(siteScheme B S hS W₀, W')]
      ↥Γ(siteScheme B S hS V₀, V') →+* Ω)
    (i : ℕ) (hi : 0 < i)
    (sp : Ideal (↥Γ(siteScheme B S hS U₀, U') ⊗[↥Γ(siteScheme B S hS W₀, W')]
      ↥Γ(siteScheme B S hS V₀, V'))) [sp.IsPrime] (hsp : sp = RingHom.ker ε) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
      ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
      ↥Γ(siteScheme B S hS V₀, V') i
    Subsingleton (LocalizedModule sp.primeCompl
      (TorChangeOfRings.torObj ↥Γ(siteScheme B S hS W₀, W') i
        ↥Γ(siteScheme B S hS U₀, U') ↥Γ(siteScheme B S hS V₀, V'))) := by
  -- the evaluations of the three rings of sections
  set εA : ↥Γ(siteScheme B S hS U₀, U') →+* Ω :=
    ε.comp Algebra.TensorProduct.includeLeftRingHom with hεAdef
  set εC : ↥Γ(siteScheme B S hS V₀, V') →+* Ω :=
    ε.comp (Algebra.TensorProduct.includeRight :
      ↥Γ(siteScheme B S hS V₀, V') →ₐ[↥Γ(siteScheme B S hS W₀, W')] _).toRingHom with hεCdef
  set εR : ↥Γ(siteScheme B S hS W₀, W') →+* Ω :=
    ε.comp (algebraMap ↥Γ(siteScheme B S hS W₀, W')
      (↥Γ(siteScheme B S hS U₀, U') ⊗[↥Γ(siteScheme B S hS W₀, W')]
        ↥Γ(siteScheme B S hS V₀, V'))) with hεRdef
  -- the three morphisms of schemes they define
  set σU : Spec (.of (Ω)) ⟶ siteScheme B S hS U₀ :=
    Spec.map (CommRingCat.ofHom εA) ≫ hU'.fromSpec with hσUdef
  set σV : Spec (.of (Ω)) ⟶ siteScheme B S hS V₀ :=
    Spec.map (CommRingCat.ofHom εC) ≫ hV'.fromSpec with hσVdef
  set σW : Spec (.of (Ω)) ⟶ siteScheme B S hS W₀ :=
    Spec.map (CommRingCat.ofHom εR) ≫ hW'.fromSpec with hσWdef
  have hUeq : σU ≫ (BigFppfOver.toScheme B S hS).map uw = σW := by
    refine spec_comp_fromSpec_comp_map _ hU' hW' hUW _ _ ?_
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    change εA ((((BigFppfOver.toScheme B S hS).map uw).appLE W' U' hUW).hom r) = εR r
    rw [← halgU]
    exact congrArg ε (Algebra.TensorProduct.algebraMap_apply r).symm
  have hVeq : σV ≫ (BigFppfOver.toScheme B S hS).map vw = σW := by
    refine spec_comp_fromSpec_comp_map _ hV' hW' hVW _ _ ?_
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    change εC ((((BigFppfOver.toScheme B S hS).map vw).appLE W' V' hVW).hom r) = εR r
    rw [← halgV]
    refine congrArg ε ?_
    change (1 : ↥Γ(siteScheme B S hS U₀, U')) ⊗ₜ[↥Γ(siteScheme B S hS W₀, W')]
        (algebraMap ↥Γ(siteScheme B S hS W₀, W')
          ↥Γ(siteScheme B S hS V₀, V') r) =
      algebraMap ↥Γ(siteScheme B S hS W₀, W') _ r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact subsingleton_localizedModule_torObj_of_evalHoms B S hS uw vw h hU' hV' hW' hUW hVW
    halgU halgV hΩ ε (σW ≫ B.inclusion.map W₀.hom) σU σV σW
    (comp_inclusion_map_eq_of_comp_eq B S hS uw hUeq)
    (comp_inclusion_map_eq_of_comp_eq B S hS vw hVeq) rfl
    hUeq hVeq (by rw [hσUdef]; exact le_preimage_of_comp_fromSpec hU' _)
    (by rw [hσVdef]; exact le_preimage_of_comp_fromSpec hV' _)
    (fun a => ΓSpecIso_hom_appLE_fromSpec hU' (CommRingCat.ofHom εA) a)
    (fun c => ΓSpecIso_hom_appLE_fromSpec hV' (CommRingCat.ofHom εC) c) i hi
    sp hsp

/-- **Tor independence of representable algebraic spaces gives Tor independence of the
schemes.**  Let `U ⟶ W ⟵ V` be morphisms of the big fppf site of `S`.  If the algebraic spaces
they represent are Tor independent over the one `W` represents in the sense of Stacks 08IP, that
is on their étale local rings, then the schemes underlying `U` and `V` are Tor independent over
the scheme underlying `W` in the sense of Stacks 08IA, that is on their ordinary local rings.

By Stacks 0FXV this is a statement about the rings of sections over a triple of affine opens,
and by Stacks 08HX about the localization of the Tor modules at every prime of
`Γ(U, U') ⊗_{Γ(W, W')} Γ(V, V')`.  Such a prime gives an algebraically closed field — an
algebraic closure of its residue field, contained in the site by Stacks 000R — and the
evaluation whose kernel it is.

This is the converse of
`AlgebraicGeometry.Space.torIndependent_yoneda_of_torIndependent_scheme`. -/
theorem torIndependent_scheme_of_torIndependent_yoneda
    {U₀ V₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    (h : TorIndependent (isAlgebraicSpace_yoneda B S hS U₀) (isAlgebraicSpace_yoneda B S hS V₀)
      (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map uw) (yoneda.map vw)) :
    AlgebraicGeometry.TorIndependent ((BigFppfOver.toScheme B S hS).map uw)
      ((BigFppfOver.toScheme B S hS).map vw) := by
  refine ((AlgebraicGeometry.torIndependent_tfae _ _).out 2 1).mp ?_
  intro U' hU' V' hV' W' hW' hUW hVW
  let : Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U') :=
    (((BigFppfOver.toScheme B S hS).map uw).appLE W' U' hUW).hom.toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS V₀, V') :=
    (((BigFppfOver.toScheme B S hS).map vw).appLE W' V' hVW).hom.toAlgebra
  show Algebra.TorIndependent ↥Γ(siteScheme B S hS W₀, W')
    ↥Γ(siteScheme B S hS U₀, U') ↥Γ(siteScheme B S hS V₀, V')
  refine (RingTheory.TorIndependence.torIndependent_iff_isZero_tor _ _ _).mp ?_
  refine ((RingTheory.TorIndependence.torIndependent_localizations_tfae
    ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
    ↥Γ(siteScheme B S hS V₀, V')).out 3 1).mp ?_
  intro i hi sp
  -- the algebraically closed field realizing the prime
  have hΩ := BigFppfSite.contains_spec_algebraicClosure_residueField_tensorProduct B
    (BigFppfSite.contains_spec_of_mk_lt_cutoff B
      (((siteScheme B S hS U₀).mk_sections_le_size ⟨U', hU'⟩).trans_lt U₀.left.property))
    (BigFppfSite.contains_spec_of_mk_lt_cutoff B
      (((siteScheme B S hS V₀).mk_sections_le_size ⟨V', hV'⟩).trans_lt V₀.left.property))
    sp.asIdeal
  set ε : ↥Γ(siteScheme B S hS U₀, U') ⊗[↥Γ(siteScheme B S hS W₀, W')]
      ↥Γ(siteScheme B S hS V₀, V') →+* AlgebraicClosure sp.asIdeal.ResidueField :=
    (algebraMap sp.asIdeal.ResidueField
      (AlgebraicClosure sp.asIdeal.ResidueField)).comp
      (algebraMap _ sp.asIdeal.ResidueField) with hεdef
  have hker : sp.asIdeal = RingHom.ker ε := by
    refine (Ideal.ext fun x => ?_).symm
    have h1 : ε x = 0 ↔ algebraMap _ sp.asIdeal.ResidueField x = 0 :=
      map_eq_zero_iff _ (algebraMap sp.asIdeal.ResidueField
        (AlgebraicClosure sp.asIdeal.ResidueField)).injective
    rw [RingHom.mem_ker, h1, Ideal.algebraMap_residueField_eq_zero]
  exact subsingleton_localizedModule_torObj_of_evalRingHom B S hS uw vw h hU' hV' hW' hUW hVW
    (fun _ => rfl) (fun _ => rfl) hΩ ε i hi sp.asIdeal hker

/-- A chosen scheme atlas of an algebraic space is étale and surjective. -/
private theorem exists_atlas_isEtale_isSurjective {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ (W₀ : BigFppfOver B S hS) (c : yoneda.obj W₀ ⟶ F), IsEtale B S hS c ∧
      IsSurjective B S hS c := by
  obtain ⟨W₀, c, hcS, hcE⟩ := hF.exists_atlas
  exact ⟨W₀, c, (isEtale_iff_presheaf_of_yoneda B S hS c).2 hcE,
    isSurjective_of_presheafSurjective B S hS c hcS⟩

/-- The first projection of the fibre product of an algebraic space with an étale atlas of the
base is étale. -/
private theorem isEtale_pullback_fst {X Bs : AlgebraicSpaces B S hS} (fX : X ⟶ Bs)
    {W₀ : BigFppfOver B S hS} (c : yoneda.obj W₀ ⟶ Bs.1) (hc : IsEtale B S hS c) :
    IsEtale B S hS (pullback.fst fX.hom c) := by
  set PXsp : AlgebraicSpaces B S hS := ⟨pullback fX.hom c,
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS fX.hom c X.2
      (isAlgebraicSpace_yoneda B S hS W₀) Bs.2⟩
  set Wsp : AlgebraicSpaces B S hS := ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩
  have hsq : IsPullback (ObjectProperty.homMk (pullback.snd fX.hom c) : PXsp ⟶ Wsp)
      (ObjectProperty.homMk (pullback.fst fX.hom c) : PXsp ⟶ X)
      (ObjectProperty.homMk c : Wsp ⟶ Bs) fX := by
    apply IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    exact (IsPullback.of_hasPullback _ _).flip
  exact isEtale_of_isPullback B S hS _ _ _ _ hsq hc

/-- **Stacks 08IQ, (1) ⟹ (4).**  Let `X` and `Y` be algebraic spaces over an algebraic space
`Bs` which are Tor independent over `Bs`.  Then there is a commutative diagram
```
U ⟶ W ⟵ V
↓    ↓    ↓
X ⟶ Bs ⟵ Y
```
in which `U`, `V` and `W` are *schemes*, the vertical arrows are étale, `W ⟶ Bs` is surjective,
`U` and `V` are étale and surjective over the fibre products `X ×_{Bs} W` and `Y ×_{Bs} W`, and
`U` and `V` are Tor independent over `W` in the sense of Stacks 08IA — that is, on their
*ordinary* local rings.  This is the existence asserted by condition (4).

The diagram is the atlas tower: a scheme chart `W ⟶ Bs` of the base, then scheme charts of the
two fibre products, which are algebraic spaces.  Condition (2) of Stacks 08IQ gives Tor
independence of the étale local rings over that diagram, and
`AlgebraicGeometry.Space.torIndependent_scheme_of_torIndependent_yoneda` turns it into Tor
independence of the ordinary local rings.  The converse implication is
`AlgebraicGeometry.Space.torIndependent_of_torIndependent_scheme_diagram`. -/
@[stacks 08IQ "(1) => (4)"]
theorem exists_torIndependent_scheme_diagram_of_torIndependent
    {Bs X Y : AlgebraicSpaces B S hS} (fX : X ⟶ Bs) (gY : Y ⟶ Bs)
    (h : TorIndependent X.2 Y.2 Bs.2 fX.hom gY.hom) :
    ∃ (U₀ V₀ W₀ : BigFppfOver B S hS) (PX PY : AlgebraicSpaces B S hS)
      (c : yoneda.obj W₀ ⟶ Bs.1) (a : yoneda.obj U₀ ⟶ X.1) (uw : U₀ ⟶ W₀)
      (b : yoneda.obj V₀ ⟶ Y.1) (vw : V₀ ⟶ W₀)
      (pX : PX ⟶ X) (pW : PX.1 ⟶ yoneda.obj W₀) (qY : PY ⟶ Y) (qW : PY.1 ⟶ yoneda.obj W₀)
      (u' : yoneda.obj U₀ ⟶ PX.1) (v' : yoneda.obj V₀ ⟶ PY.1),
      IsPullback pX.hom pW fX.hom c ∧ IsPullback qY.hom qW gY.hom c ∧
        u' ≫ pX.hom = a ∧ u' ≫ pW = yoneda.map uw ∧ v' ≫ qY.hom = b ∧
        v' ≫ qW = yoneda.map vw ∧
        IsEtale B S hS c ∧ IsSurjective B S hS c ∧
        IsEtale B S hS a ∧ IsEtale B S hS b ∧
        IsEtale B S hS u' ∧ IsSurjective B S hS u' ∧
        IsEtale B S hS v' ∧ IsSurjective B S hS v' ∧
        AlgebraicGeometry.TorIndependent ((BigFppfOver.toScheme B S hS).map uw)
          ((BigFppfOver.toScheme B S hS).map vw) := by
  obtain ⟨W₀, c, hcEtale, hcSurj⟩ := exists_atlas_isEtale_isSurjective B S hS Bs.2
  have hPX : IsAlgebraicSpace B S hS (pullback fX.hom c) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS fX.hom c X.2
      (isAlgebraicSpace_yoneda B S hS W₀) Bs.2
  have hPY : IsAlgebraicSpace B S hS (pullback gY.hom c) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS gY.hom c Y.2
      (isAlgebraicSpace_yoneda B S hS W₀) Bs.2
  have sqX : IsPullback (pullback.fst fX.hom c) (pullback.snd fX.hom c) fX.hom c :=
    IsPullback.of_hasPullback _ _
  have sqY : IsPullback (pullback.fst gY.hom c) (pullback.snd gY.hom c) gY.hom c :=
    IsPullback.of_hasPullback _ _
  obtain ⟨U₀, u', hu'Etale, hu'Surj⟩ := exists_atlas_isEtale_isSurjective B S hS hPX
  obtain ⟨V₀, v', hv'Etale, hv'Surj⟩ := exists_atlas_isEtale_isSurjective B S hS hPY
  have haEtale : IsEtale B S hS (u' ≫ pullback.fst fX.hom c) :=
    isEtale_comp B S hS hu'Etale (isEtale_pullback_fst B S hS fX c hcEtale)
  have hbEtale : IsEtale B S hS (v' ≫ pullback.fst gY.hom c) :=
    isEtale_comp B S hS hv'Etale (isEtale_pullback_fst B S hS gY c hcEtale)
  have hsq1 : yoneda.map (yoneda.preimage (u' ≫ pullback.snd fX.hom c)) ≫ c =
      (u' ≫ pullback.fst fX.hom c) ≫ fX.hom := by
    rw [yoneda.map_preimage, Category.assoc, Category.assoc, sqX.w]
  have hsq2 : yoneda.map (yoneda.preimage (v' ≫ pullback.snd gY.hom c)) ≫ c =
      (v' ≫ pullback.fst gY.hom c) ≫ gY.hom := by
    rw [yoneda.map_preimage, Category.assoc, Category.assoc, sqY.w]
  have hUV := (torIndependent_iff_forall_etale_diagram B S hS fX gY).mp h
    ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩
    ⟨yoneda.obj V₀, isAlgebraicSpace_yoneda B S hS V₀⟩
    ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩
    (ObjectProperty.homMk (u' ≫ pullback.fst fX.hom c))
    (ObjectProperty.homMk (v' ≫ pullback.fst gY.hom c))
    (ObjectProperty.homMk c)
    (ObjectProperty.homMk (yoneda.map (yoneda.preimage (u' ≫ pullback.snd fX.hom c))))
    (ObjectProperty.homMk (yoneda.map (yoneda.preimage (v' ≫ pullback.snd gY.hom c))))
    haEtale hbEtale hcEtale hsq1 hsq2
  exact ⟨U₀, V₀, W₀, ⟨pullback fX.hom c, hPX⟩, ⟨pullback gY.hom c, hPY⟩, c,
    u' ≫ pullback.fst fX.hom c, yoneda.preimage (u' ≫ pullback.snd fX.hom c),
    v' ≫ pullback.fst gY.hom c, yoneda.preimage (v' ≫ pullback.snd gY.hom c),
    ObjectProperty.homMk (pullback.fst fX.hom c), pullback.snd fX.hom c,
    ObjectProperty.homMk (pullback.fst gY.hom c), pullback.snd gY.hom c, u', v',
    sqX, sqY, rfl, (yoneda.map_preimage _).symm, rfl, (yoneda.map_preimage _).symm,
    hcEtale, hcSurj, haEtale, hbEtale, hu'Etale, hu'Surj, hv'Etale, hv'Surj,
    torIndependent_scheme_of_torIndependent_yoneda B S hS
      (yoneda.preimage (u' ≫ pullback.snd fX.hom c))
      (yoneda.preimage (v' ≫ pullback.snd gY.hom c)) hUV⟩

end AlgebraicGeometry.Space

end
