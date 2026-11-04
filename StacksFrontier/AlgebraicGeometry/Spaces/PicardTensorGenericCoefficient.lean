module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkGeneratingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTensorGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedGlobalSections

/-!
# The coefficient of Stacks 0EPR of a product of two meromorphic sections

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let `ℒ` and
`𝒩` be invertible `𝒪_X`-modules with regular meromorphic sections `s` and `t`, and let `Z ⊂ X` be
a prime divisor with generic point `ξ`.  This file computes the coefficient of Stacks 0EPR of the
global product `s ⊗ t` at `ξ`:

`coeff(s ⊗ t) = (unit of 𝒪_{U, u}) · coeff(s) · coeff(t)`.

The unit is unavoidable:
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkTrivialisation` picks a generator of `ℒ`, one of
`𝒩` and one of `ℒ ⊗ 𝒩` at `ξ` by three independent choices, and the product of the first two is
*some* free generator of `ℒ ⊗ 𝒩`, so it differs from the third by a unit.

Over a chart `V` of `X` through `ξ` over which both modules are free, `s` is `a · e`, `t` is
`b · f` and `s ⊗ t` is `(a b) · (e ⊗ f)`
(`AlgebraicGeometry.Space.eval_meromorphicSectionTensor_eq_tmul`). Pulling each presentation back
along `j : Spec(𝒪_{U, u}) ⟶ X` over the base change of `V`
(`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram`) turns the coefficient into
its image under the chartwise pullback `j^♯`, which is a ring homomorphism, so the coefficient of
the product is the product of the coefficients there; and over the charts of a covering sieve each
inverse image of a generator is again a free generator
(`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`), which is what
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul` reads against
the generator chosen at `ξ`, up to a unit. Intersecting the three sieves and refining to an affine
member through a point over the closed point of `Spec(𝒪_{U, u})`, the three identities hold over
one chart; the unit is then descended back to `𝒪_{U, u}` by
`AlgebraicGeometry.exists_isUnit_eq_appTop_of_isUnit_of_flat`, which is legitimate because the
coefficients of `s` and of `t` are units of the meromorphic functions there
(`AlgebraicGeometry.Space.PrimeDivisor.isUnit_genericStalkCoefficient`).

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_mem_range_pointsMap_of_mem_topology`: a covering
  sieve of a chart whose image contains a point of `|X|` has a member whose image contains it.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict`:
  the coefficient of Stacks 0EPR of a meromorphic section presented over `V` as `a · e` is, over
  the charts of a covering sieve of the base change of `V`, a unit times the pullback of `a`.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_eq_algebraMap_of_chart`: unit-ness of a
  meromorphic function on `Spec(𝒪_{U, u})` descends from an affine chart through a point over the
  closed point.
* `Space.PrimeDivisor.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor`: the identity
  above.

## Implementation notes

Two statements here generalise statements proved only in a special case:

* `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict`
  generalises
  `AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_eval_eq_one_tmul_genericStalkBaseChange` from
  the coefficient `1` — which is what generation of the module by the section gives — to an
  arbitrary coefficient, and folds in the comparison with the generator chosen at `ξ`.  The
  coefficient `1` is exactly what the *product* does not have.
* `AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_eq_algebraMap_of_chart` generalises
  `Space.PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_chart` from the
  coefficient of a meromorphic section to an arbitrary meromorphic function on
  `Spec(𝒪_{U, u})`; the function descended here is a *ratio* of coefficients and is not the
  coefficient of any section.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve of a chart whose image contains a point of `|X|` has a member whose image
contains it.**  A covering sieve is jointly surjective on the points of the underlying schemes
(`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`), and the point of `|X|`
determined by a point of the scheme of a chart does not change when the latter is pushed along a
morphism of charts (`AlgebraicGeometry.Space.chartSchemeToPoints_map`). -/
theorem SmallEtale.exists_mem_range_pointsMap_of_mem_topology
    (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1) {T : Sieve V}
    (hT : T ∈ SmallEtale.topology B S hS X.1 V) (x : points B S hS X.1)
    (hmem : x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V)) V.obj.hom)) :
    ∃ (W : SmallEtale B S hS X.1) (k : W ⟶ V), T k ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.obj.hom) := by
  rw [← range_chartSchemeToPoints B S hS X V] at hmem
  obtain ⟨p, hp⟩ := hmem
  obtain ⟨W, k, hk, q, hq⟩ := (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1 T).1 hT p
  refine ⟨W, k, hk, ?_⟩
  rw [← range_chartSchemeToPoints B S hS X W]
  exact ⟨q, ((chartSchemeToPoints_map B S hS X.1 k q).symm.trans
    (congrArg (chartSchemeToPoints B S hS X.1 V) hq)).trans hp⟩

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

include hX in
/-- **The coefficient of Stacks 0EPR of a section presented as `a · e` is a unit times the
pullback of `a`, over the charts of a covering sieve.**  Let `e` be a family of free generators
of `ℒ` over the charts over an étale chart `V` of `X`, compatible with restriction, and let the
meromorphic section `σ` be `a · e` over `V`.  Then over the charts of a covering sieve of the base
change of `V` to `Spec(𝒪_{U, u})` the restriction of the coefficient of `σ` against the generator
chosen at `ξ` is a unit of the regular functions times the image of `a` under the chartwise
pullback `j^♯`.

The pullback of the presentation along the cartesian square defining the base change is
`j^♯(a) ⊗ (j^*e)` (`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram` and
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf_tmul`); over the charts of a
covering sieve `j^*e` is a free generator
(`AlgebraicGeometry.Space.exists_sieve_bijective_smul_modulePullbackChartSection`), and the
comparison of two free generators at `ξ` is
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_eq_mul_of_eval_eq_smul`.

This is
`AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_eval_eq_one_tmul_genericStalkBaseChange` with
the coefficient `1` replaced by an arbitrary `a` and the comparison folded in. -/
theorem PrimeDivisor.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict
    (M : Modules.{u, u} B S hS X hX) (hM : IsInvertibleModule (B := B) ⟨X, hX⟩ M)
    (σ : MeromorphicSection.{u, u} B S hS X hX M) (V : SmallEtale B S hS X)
    (e : (W : SmallEtale B S hS X) → (W ⟶ V) → M.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k)
    (a : (meromorphicChartSheaf B S hS X hX).obj.obj (op V))
    (hpres : σ.eval (op V) = toMeromorphicSectionSheaf B S hS X hX M V
      (a ⊗ₜ[chartRing B S hS X hX V] e V (𝟙 V) :
        (meromorphicSectionModule B S hS X hX M).obj (op V))) :
    ∃ T : Sieve (Z.genericStalkBaseChangeChart B S hS hX hdec V),
      T ∈ SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkBaseChangeChart B S hS hX hdec V) ∧
        ∀ ⦃Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1⦄
          (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V), T ι →
            ∃ (v : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                (Z.genericStalkSpace B S hS hX hdec).2 Q)ˣ)
              (c : (meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)),
              c = ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                      (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom
                    (chartMeromorphicPullbackHom B S hS
                      (Z.genericStalkMorphism B S hS hX hdec)
                      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
                      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) a) ∧
                ((Stacks.SheafOfModules.Tensor.ringSheaf
                    (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
                        (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
                      (ι ≫ chartToIdEtaleChart B S hS
                        (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom
                    (Z.genericStalkCoefficient B S hS hX hdec M hM σ) =
                  algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                      (Z.genericStalkSpace B S hS hX hdec).2 Q)
                    ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
                      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q))
                    (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
                      (Z.genericStalkSpace B S hS hX hdec).2 Q) * c := by
  set jm := Z.genericStalkMorphism B S hS hX hdec with hjm
  set hj := Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec with hhj
  set d := Z.genericStalkBaseChangeDiagram B S hS hX hdec V with hd
  -- the pullback of the presentation over the base-changed chart itself
  have hEid : modulePullbackChartSectionRestrict B S hS jm M d (e d.V (𝟙 d.V)) (𝟙 d.U) =
      (modulePullbackChartFMap B S hS jm M).app d (e d.V (𝟙 d.V)) :=
    CategoryTheory.congr_fun
      (((modulePullback B S hS jm).obj M).val.presheaf.map_id (op d.U))
      ((modulePullbackChartFMap B S hS jm M).app d (e d.V (𝟙 d.V)))
  have hvalue : (pullbackMeromorphicSection B S hS jm M hj σ).eval (op d.U) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 ((modulePullback B S hS jm).obj M) d.U
        ((chartMeromorphicPullbackHom B S hS jm hj d a) ⊗ₜ[chartRing B S hS
            (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 d.U]
          modulePullbackChartSectionRestrict B S hS jm M d (e d.V (𝟙 d.V)) (𝟙 d.U) :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS jm).obj M)).obj (op d.U)) := by
    refine Eq.trans (pullbackMeromorphicSection_eval_chartDiagram B S hS jm M hj σ d
      (a ⊗ₜ[chartRing B S hS X hX d.V] e d.V (𝟙 d.V) :
        (meromorphicSectionModule B S hS X hX M).obj (op d.V)) hpres) ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
      ((modulePullback B S hS jm).obj M) d.U) ?_
    refine Eq.trans (chartPullbackMeromorphicSectionsSheaf_tmul B S hS jm M hj d a
      (e d.V (𝟙 d.V))) ?_
    exact congrArg (fun z : ((modulePullback B S hS jm).obj M).val.obj (op d.U) ↦
      ((chartMeromorphicPullbackHom B S hS jm hj d a) ⊗ₜ[chartRing B S hS
          (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 d.U] z :
        (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          ((modulePullback B S hS jm).obj M)).obj (op d.U))) hEid.symm
  have hEcompat : ∀ (W₁ W₂ : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
      (k₁ : W₁ ⟶ d.U) (g : W₂ ⟶ W₁),
      (((modulePullback B S hS jm).obj M).val.map g.op).hom
          (modulePullbackChartSectionRestrict B S hS jm M d (e d.V (𝟙 d.V)) k₁) =
        modulePullbackChartSectionRestrict B S hS jm M d (e d.V (𝟙 d.V)) (g ≫ k₁) :=
    fun _ _ k₁ g ↦ modulePullbackChartSectionRestrict_map B S hS jm M d (e d.V (𝟙 d.V)) k₁ g
  have hXrestrict := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS jm).obj M) (pullbackMeromorphicSection B S hS jm M hj σ) d.U
    (fun W₁ k₁ ↦ modulePullbackChartSectionRestrict B S hS jm M d (e d.V (𝟙 d.V)) k₁)
    hEcompat (chartMeromorphicPullbackHom B S hS jm hj d a) hvalue
  obtain ⟨T, hT, hTbij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS jm M
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM) d e hecompat hebij
  refine ⟨T, hT, fun Q ι hι ↦ ?_⟩
  obtain ⟨v, hv⟩ := Z.genericStalkCoefficient_eq_mul_of_eval_eq_smul B S hS hX hdec M hM σ Q
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V))
    (modulePullbackChartSectionRestrict B S hS jm M d (e d.V (𝟙 d.V)) (𝟙 Q ≫ ι))
    (hTbij ι hι Q (𝟙 Q)) _ (hXrestrict Q ι)
  exact ⟨v, _, rfl, hv⟩

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt hN in
/-- **A meromorphic function on `Spec(𝒪_{U, u})` is the image of a unit as soon as it is one on a
chart.**  If the restriction of `c` to an *affine* chart `W` of `Spec(𝒪_{U, u})` carrying a point
over the closed point is the image of a unit regular function on `W`, then `c` is the image of a
unit of `𝒪_{U, u}`.  Flatness of `W` over `Spec(𝒪_{U, u})` is not a hypothesis: a chart is étale.

This is
`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_eq_algebraMap_genericStalkCoefficient_of_chart`
with the coefficient of Stacks 0EPR of a meromorphic section replaced by an arbitrary meromorphic
function, which is what a *ratio* of such coefficients needs. -/
theorem PrimeDivisor.exists_isUnit_eq_algebraMap_of_chart
    (c : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)))
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec)
    (hWaff : IsAffine (smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W))
    (w : smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W)
    (hw : (Z.genericStalkChartMap B S hS hX hdec W k).base w =
      IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec))
    (v : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj (op W))
    (hv : IsUnit v)
    (hres : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.map k.op).hom c =
      ((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).hom.app (op W)).hom v) :
    ∃ b : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)), IsUnit b ∧
      c = algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) b := by
  have := Z.flat_genericStalkChartMap B S hS hX hdec W k
  have := hWaff
  refine AlgebraicGeometry.exists_isUnit_eq_appTop_of_isUnit_of_flat
    (Z.genericStalkRing B S hS hX hdec)
    (smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1 W)
    (Z.genericStalkChartMap B S hS hX hdec W k) w hw
    (algK := Z.genericStalkMeromorphicAlgebra B S hS hX hdec)
    (fracK := Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN)
    (algKO := ((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).hom.app (op W)).hom.toAlgebra)
    (fracKO := isFractionRing_meromorphicFunctionSheaf_obj B S hS
      (Z.genericStalkSpace B S hS hX hdec)
      (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace B S hS hX hdec
        hInt)
      (Z.hasLocallyFiniteIrreducibleComponents_genericStalkSpace B S hS hX hdec hN) W hWaff)
    (((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.map k.op).hom) (fun b ↦ ?_) hv hres
  exact congrArg (fun φ : (structurePresheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1).obj (op (Z.genericStalkChart B S hS hX hdec)) ⟶
      (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op W) ↦ φ.hom b)
    ((toMeromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).hom.naturality k.op).symm

/-! ### The coefficient of the product -/

/-- **The pure algebra of the comparison.**  Three elements of a commutative ring presented as a
unit times a factor, with the first factor the product of the other two, have the first equal to
a unit times the product of the other two — the unit being the product of the three units of the
presentations, two of them inverted.

The three presentations are the readings of the coefficients of Stacks 0EPR of `s ⊗ t`, of `s` and
of `t` against the generators chosen at `ξ`, over a chart of `Spec(𝒪_{U, u})`; this is stated over
abstract rings because the rings of meromorphic functions in question carry several
definitionally equal spellings and no arithmetic should depend on which one is written. -/
private theorem mul_inv_eq_algebraMap_of_eq_mul {R A : Type u} [CommRing R] [CommRing A]
    (ψ : R →+* A) (uL uN uP : Rˣ) (cL cN pc sc tc cv cvi : A)
    (hp : pc = ψ (uP : R) * (cL * cN)) (hs : sc = ψ (uL : R) * cL)
    (ht : tc = ψ (uN : R) * cN) (hcv : cv = sc * tc) (hinv : cv * cvi = 1) :
    pc * cvi = ψ ((uP * (uL * uN)⁻¹ : Rˣ) : R) := by
  subst hp hs ht hcv
  have hstep : ψ ((uP * (uL * uN)⁻¹ : Rˣ) : R) *
      ((ψ (uL : R) * cL) * (ψ (uN : R) * cN)) = ψ (uP : R) * (cL * cN) := by
    have h1 : ψ ((uP * (uL * uN)⁻¹ : Rˣ) : R) * ((ψ (uL : R) * cL) * (ψ (uN : R) * cN)) =
        ψ ((uP * (uL * uN)⁻¹ : Rˣ) : R) * (ψ (uL : R) * ψ (uN : R)) * (cL * cN) := by ring
    rw [h1, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul]
    exact congrArg (fun z : Rˣ ↦ ψ (z : R) * (cL * cN)) (inv_mul_cancel_right uP (uL * uN))
  have h2 : ψ (uP : R) * (cL * cN) * cvi =
      ψ ((uP * (uL * uN)⁻¹ : Rˣ) : R) * (((ψ (uL : R) * cL) * (ψ (uN : R) * cN)) * cvi) := by
    rw [← hstep]
    ring
  rw [h2, hinv, mul_one]

/-- A family of free generators over `V'` restricts along `h : V ⟶ V'` to one over `V`. -/
private theorem exists_generator_family_of_hom (M : Modules.{u, u} B S hS X hX)
    {V V' : SmallEtale B S hS X} (h : V ⟶ V') (e₀ : (W : SmallEtale B S hS X) → (W ⟶ V') →
      M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V') (g : W' ⟶ W),
      (M.val.map g.op).hom (e₀ W k) = e₀ W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS X) (k : W ⟶ V'),
      Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e₀ W k) :
    ∃ e : (W : SmallEtale B S hS X) → (W ⟶ V) → M.val.obj (op W),
      (∀ (W W' : SmallEtale B S hS X) (k : W ⟶ V) (g : W' ⟶ W),
          (M.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
        ∀ (W : SmallEtale B S hS X) (k : W ⟶ V),
          Function.Bijective fun r : chartRing B S hS X hX W ↦ r • e W k :=
  ⟨fun W k ↦ e₀ W (k ≫ h),
    fun W W' k g ↦ (hcompat W W' (k ≫ h) g).trans (congrArg (e₀ W') (Category.assoc g k h).symm),
    fun W k ↦ hbij W (k ≫ h)⟩

include hX hInt hN in
/-- **The coefficient of Stacks 0EPR of a product of two regular meromorphic sections is a unit
times the product of the coefficients.**  This is the content of Stacks 0EPV at the generic point
of a prime divisor, for the product `s ⊗ t` of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionTensorGlobal.lean`.

The unit is there because the generator chosen at `ξ` for `ℒ ⊗ 𝒩` and the product of the
generators chosen for `ℒ` and for `𝒩` are two free generators of one invertible module.

Over a chart `V` of `X` through `ξ` over which both modules are free, `s ⊗ t` is `(a b) · (e ⊗ f)`
(`AlgebraicGeometry.Space.eval_meromorphicSectionTensor_eq_tmul`), and the three presentations are
read against the generators chosen at `ξ` by
`AlgebraicGeometry.Space.PrimeDivisor.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict`
over the charts of three covering sieves of the base change of `V`.  The chartwise pullback `j^♯`
is a ring homomorphism, so the coefficient of the product is the product of the two over a member
of all three sieves; refining to an affine member through a point over the closed point of
`Spec(𝒪_{U, u})`, the resulting unit is descended by
`AlgebraicGeometry.Space.PrimeDivisor.exists_isUnit_eq_algebraMap_of_chart`.  The element
descended is the *ratio* of the coefficient of the product by the product of the coefficients,
which is legitimate because those are units
(`AlgebraicGeometry.Space.PrimeDivisor.isUnit_genericStalkCoefficient`). -/
theorem PrimeDivisor.exists_isUnit_genericStalkCoefficient_meromorphicSectionTensor
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS),
      localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X)
    (L N : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hNinv : IsInvertibleModule (B := B) ⟨X, hX⟩ N)
    (hLqc : L.IsQuasicoherentOnSite) (hNqc : N.IsQuasicoherentOnSite)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    (t : MeromorphicSection.{u, u} B S hS X hX N)
    (hsreg : IsRegularMeromorphicSection.{u, u} B S hS X hX L s)
    (htreg : IsRegularMeromorphicSection.{u, u} B S hS X hX N t) :
    ∃ w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)), IsUnit w ∧
      Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
            (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) =
        algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) w *
          (Z.genericStalkCoefficient B S hS hX hdec L hL s *
            Z.genericStalkCoefficient B S hS hX hdec N hNinv t) := by
  -- a chart of `X` through `ξ` over which both modules are free
  obtain ⟨V₀, hV₀⟩ := exists_isSurjective_chart B S hS (⟨X, hX⟩ : AlgebraicSpaces B S hS)
  obtain ⟨I₁, V₁, κ₁, hcov₁, hgen₁⟩ := exists_generator_cover_smul_of_isInvertible B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) V₀
  obtain ⟨I₂, V₂, κ₂, hcov₂, hgen₂⟩ := exists_generator_cover_smul_of_isInvertible B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) N
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hNinv) V₀
  obtain ⟨V, θ, hθ, hmem⟩ := SmallEtale.exists_mem_range_pointsMap_of_mem_topology B S hS
    (⟨X, hX⟩ : AlgebraicSpaces B S hS) V₀
    ((SmallEtale.topology B S hS X).intersection_covering hcov₁ hcov₂)
    (Z.genericPoint B S hS X) (hV₀ (Z.genericPoint B S hS X))
  obtain ⟨i₁, h₁, -⟩ := (Sieve.mem_ofArrows_iff V₁ κ₁ θ).1 hθ.1
  obtain ⟨i₂, h₂, -⟩ := (Sieve.mem_ofArrows_iff V₂ κ₂ θ).1 hθ.2
  obtain ⟨e₀, he₀compat, he₀bij⟩ := hgen₁ i₁
  obtain ⟨f₀, hf₀compat, hf₀bij⟩ := hgen₂ i₂
  obtain ⟨e, hecompat, hebij⟩ := exists_generator_family_of_hom B S hS hX L h₁ e₀ he₀compat he₀bij
  obtain ⟨f, hfcompat, hfbij⟩ := exists_generator_family_of_hom B S hS hX N h₂ f₀ hf₀compat hf₀bij
  -- the coefficients of the two sections over `V`, and the presentation of the product
  obtain ⟨a, ha⟩ := (bijective_toMeromorphicSectionSheaf_tmul B S hS X hX L V e hecompat
    hebij).2 (s.eval (op V))
  obtain ⟨b, hb⟩ := (bijective_toMeromorphicSectionSheaf_tmul B S hS X hX N V f hfcompat
    hfbij).2 (t.eval (op V))
  have hP := eval_meromorphicSectionTensor_eq_tmul B S hS hX hwa hfin L N s t hLqc hNqc V
    e f hecompat hfcompat a b ha.symm hb.symm
  -- the three covering sieves of the base change of `V`
  obtain ⟨TL, hTL, hTLspec⟩ := Z.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict
    B S hS hX hdec L hL s V e hecompat hebij a ha.symm
  obtain ⟨TN, hTN, hTNspec⟩ := Z.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict
    B S hS hX hdec N hNinv t V f hfcompat hfbij b hb.symm
  obtain ⟨TP, hTP, hTPspec⟩ := Z.exists_sieve_isUnit_mul_genericStalkCoefficient_restrict
    B S hS hX hdec (picardTensorModule B S hS hX L N)
    (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
    (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) V
    (fun W k ↦ tensorChartSection B S hS hX L N W (e W k) (f W k))
    (fun W W' k g ↦ tensorChartSection_restrict_family B S hS hX L N V e f hecompat hfcompat
      W k W' g)
    (fun W k ↦ bijective_smul_tensorChartSection B S hS hX L N V e f hecompat hebij hfcompat
      hfbij W k)
    (a * b) hP
  -- an affine member of all three through a point over the closed point
  obtain ⟨p₀, hp₀⟩ := Z.exists_mem_range_genericStalkBaseChangeChart B S hS hX hdec V hmem
  obtain ⟨Q, ι, hι, hQaff, w₀, hw₀⟩ := SmallEtale.exists_affine_mem_range_of_mem_topology
    B S hS (Z.genericStalkSpace B S hS hX hdec).1
    ((SmallEtale.topology B S hS (Z.genericStalkSpace B S hS hX hdec).1).intersection_covering
      ((SmallEtale.topology B S hS
        (Z.genericStalkSpace B S hS hX hdec).1).intersection_covering hTL hTN) hTP) p₀
  obtain ⟨vL, cL, hcL, hvL⟩ := hTLspec ι hι.1.1
  obtain ⟨vN, cN, hcN, hvN⟩ := hTNspec ι hι.1.2
  obtain ⟨vP, cP, hcP, hvP⟩ := hTPspec ι hι.2
  -- the coefficient of the product is the product of the coefficients, `j^♯` being a ring map
  have hcPmul : cP = cL * cN := by
    refine hcP.trans (Eq.trans (congrArg (((meromorphicChartSheaf B S hS
        (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom)
      (map_mul (chartMeromorphicPullbackHom B S hS
        (Z.genericStalkMorphism B S hS hX hdec)
        (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V)) a b)) ?_)
    refine Eq.trans (map_mul (((meromorphicChartSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom) _ _) ?_
    exact (congrArg (fun z ↦ z * ((meromorphicChartSheaf B S hS
            (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.map ι.op).hom
          (chartMeromorphicPullbackHom B S hS (Z.genericStalkMorphism B S hS hX hdec)
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
            (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) b))
        hcL.symm).trans (congrArg (fun z ↦ cL * z) hcN.symm)
  -- the coefficients of `s` and of `t` at `ξ` are units
  obtain ⟨cu, hcu⟩ : ∃ cu : ((meromorphicFunctionSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)))ˣ,
      (cu : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))) =
        Z.genericStalkCoefficient B S hS hX hdec L hL s *
          Z.genericStalkCoefficient B S hS hX hdec N hNinv t :=
    ⟨(Z.isUnit_genericStalkCoefficient B S hS hX hdec L hL hInt hN s hsreg).unit *
        (Z.isUnit_genericStalkCoefficient B S hS hX hdec N hNinv hInt hN t htreg).unit, by
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]⟩
  -- the ratio becomes the image of a unit on the chart
  have hcuv : (((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
        (ι ≫ chartToIdEtaleChart B S hS
          (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom)
        (cu : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))) =
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom)
          (Z.genericStalkCoefficient B S hS hX hdec L hL s) *
        (((Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
            (ι ≫ chartToIdEtaleChart B S hS
              (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom)
          (Z.genericStalkCoefficient B S hS hX hdec N hNinv t) :=
    (congrArg (((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
        (ι ≫ chartToIdEtaleChart B S hS
          (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom) hcu).trans
      (map_mul (((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom) _ _)
  have hinv : (((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
        (ι ≫ chartToIdEtaleChart B S hS
          (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom)
        (cu : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))) *
      (((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom)
        ((cu⁻¹ : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec)))ˣ) :
          (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) = 1 :=
    ((map_mul (((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
            (ι ≫ chartToIdEtaleChart B S hS
              (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom) _ _).symm.trans
        (congrArg (((Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
            (ι ≫ chartToIdEtaleChart B S hS
              (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom)
          cu.mul_inv)).trans
      (map_one (((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom))
  have hratio := mul_inv_eq_algebraMap_of_eq_mul
    (algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q)
      ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q)))
    vL vN vP cL cN _ _ _ _ _ (hvP.trans (congrArg (fun z ↦
      algebraMap (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q)
        ((meromorphicChartSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj (op Q))
        (vP : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 Q) * z) hcPmul)) hvL hvN hcuv hinv
  -- the descent to `Spec(𝒪_{U, u})`
  obtain ⟨w, hwU, hw⟩ := Z.exists_isUnit_eq_algebraMap_of_chart B S hS hX hdec hInt hN
    (Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
        (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) *
      ((cu⁻¹ : ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec)))ˣ) :
        (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))))
    Q (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) hQaff
    w₀ (by
      have hcomp : Z.genericStalkChartMap B S hS hX hdec Q
            (ι ≫ chartToIdEtaleChart B S hS
              (Z.genericStalkBaseChangeChart B S hS hX hdec V)) =
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS
              (Z.genericStalkSpace B S hS hX hdec).1).map ι) ≫
            (BigFppfOver.toScheme B S hS).map (yoneda.preimage
              (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom) :=
        Functor.map_comp (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1 ⋙
          BigFppfOver.toScheme B S hS) ι _
      rw [hcomp]
      exact (congrArg ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom)) hw₀).trans hp₀)
    ((vP * (vL * vN)⁻¹ : (chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q)ˣ) :
      chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 Q)
    (Units.isUnit _)
    (Eq.trans (map_mul (((Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
        (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map
          (ι ≫ chartToIdEtaleChart B S hS
            (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom) _ _) hratio)
  refine ⟨w, hwU, ?_⟩
  have hsplit : Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
        (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
        (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) =
      (Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
            (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) *
          ((cu⁻¹ : ((meromorphicFunctionSheaf B S hS
              (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
                (op (Z.genericStalkChart B S hS hX hdec)))ˣ) :
            (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
                (op (Z.genericStalkChart B S hS hX hdec)))) *
        (cu : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))) :=
    (mul_one _).symm.trans ((congrArg (fun z ↦
        Z.genericStalkCoefficient B S hS hX hdec (picardTensorModule B S hS hX L N)
            (isInvertibleModule_picardTensorModule B S hS hX L N hL hNinv)
            (meromorphicSectionTensor B S hS hX hwa hfin L N s t hLqc hNqc) * z)
      cu.inv_mul.symm).trans (mul_assoc _ _ _).symm)
  exact (hsplit.trans (congrArg (fun z ↦ z *
      (cu : (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec)))) hw)).trans
    (congrArg (fun z ↦ algebraMap ((structurePresheaf B S hS
          (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)))
        ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
            (op (Z.genericStalkChart B S hS hX hdec))) w * z) hcu)
end AlgebraicGeometry.Space

end
