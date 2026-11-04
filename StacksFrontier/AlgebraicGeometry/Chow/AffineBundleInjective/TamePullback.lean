module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.BundleCyclePullback
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureSummandIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainBoundaryCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainLocalization
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorKSymbolTransport
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.DiscreteValuationRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tame-symbol differential commutes with pulling back along an affine-space bundle

Let `(S, δ)` be the base situation of chapter 42, let `q : E ⟶ B` be an affine-space bundle of
rank `m` between schemes locally of finite type over `S`, and let `θ` be a locally finite Milnor
K₂-chain on `B` at the points of relative dimension `k + 2`. Pulling `θ` back along `q`
(`Stacks.Chow.bundleChainPullback`) puts the class at `β` on the generic point `γ_β` of the fibre
over `β`. This file proves that the first differential of Stacks 0GU9
(`Stacks.Chow.pointwiseMilnorBoundary`) commutes with that pullback on the preimage of a set `T`
of points of `B`, provided the local rings `𝒪_{closure {β}, w}` at the points `w ∈ T` of relative
dimension `k + 1` are discrete valuation rings.

Fix a point `γ'` of `q⁻¹ T` of relative dimension `k + m + 1` and a point `β` carrying `θ` with
`γ_β ⇝ γ'`. Counting dimensions leaves two cases.

* **Horizontal**, `q γ' = β`. A nonzero element of `κ(β)` is the value of a unit germ at
  `q γ' = β`, whose pullback restricted to `closure {γ_β}` is a unit at `γ'`; the tame symbol
  kills pure symbols of units, so the contribution vanishes.
* **Vertical**, `w = q γ' ≠ β`. Then `γ'` is the generic point of the fibre over `w`. The map
  `q` induces a local homomorphism `D = 𝒪_{closure {β}, w} → D' = 𝒪_{closure {γ_β}, γ'}`
  compatible with `κ(β) → κ(γ_β)` on fraction fields and with `κ(w) → κ(γ')` on residue
  fields. The flat pullback multiplicity of `q` at `γ'` is one, so the maximal ideal of
  `𝒪_{B, w}` generates that of `𝒪_{E, γ'}`, and hence that of `D` generates that of `D'`. So
  `D'` is a discrete valuation ring with the same uniformizer as the discrete valuation ring
  `D`, orders of vanishing agree, and the formula of Stacks 02Q6 shows that the tame symbol of
  `D'` on the image of a pair is the image of the tame symbol of `D`.

## Main results

* `Stacks.Chow.tameSymbol_map_eq_of_map_maximalIdeal` — for a local homomorphism of discrete
  valuation rings `D → D'` with `𝔪_D D' = 𝔪_{D'}`, the tame symbols are compatible.
* `Stacks.Chow.milnorKTwoTameSymbol_milnorKTransport_of_map_maximalIdeal` — the same on Milnor
  K₂.
* `Stacks.Chow.pointClosureStalkHom` — the local homomorphism
  `𝒪_{closure {q x}, q x'} → 𝒪_{closure {x}, x'}` induced by `q`.
* `Stacks.Chow.pointClosureMilnorBoundary_milnorKTransport_eq_zero_of_eq` and
  `Stacks.Chow.pointClosureMilnorBoundary_milnorKTransport` — the horizontal and the vertical
  local statements.
* `Stacks.Chow.milnorChainRestrict_pointwiseMilnorBoundary_bundleChainPullback` — **the tame
  symbol differential commutes with pullback along an affine-space bundle**, on `q⁻¹ T`.

## Implementation notes

The vertical case is an instance of the behaviour of the tame symbol under a flat local
homomorphism with closed fibre of length one (Stacks 0EPG with `m = 1`), but flatness is not used
here: the only input is that the
maximal ideal is extended, which makes the local ring upstairs a discrete valuation ring with the
same uniformizer, and both tame symbols are then computed by Stacks 02Q6. The map
`Stacks.Chow.pointClosureStalkHom` is built by descending the pullback of germs through the
surjective restriction to the closure of a point, so no morphism between the two closures is
formed.

## References

* [Stacks Project, Tag 02Q6](https://stacks.math.columbia.edu/tag/02Q6)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.Chow

/-! ### Tame symbols along a local homomorphism with `𝔪_D D' = 𝔪_{D'}` -/

section Algebra

/-- A nonzero fraction written as a unit of a discrete valuation ring times an integral power of
a uniformizer has order of vanishing equal to that power. -/
private theorem ordInt_eq_of_eq_units_smul_zpow {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {π : A} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) {n : ℤ} {u : Aˣ}
    (h : x = u • (algebraMap A K π) ^ n) :
    ordInt A x hx = n := by
  have hfrac : Ring.ordFrac A (K := K) x = WithZero.exp n := by
    subst h
    rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      Ring.ordFrac_of_isUnit u.isUnit, Ring.ordFrac_irreducible (K := K) hπ, one_mul,
      ← WithZero.exp_zsmul]
    simp
  have hu : WithZero.unzero ((hx.isUnit.map (Ring.ordFrac A)).ne_zero) =
      Multiplicative.ofAdd n := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, hfrac, WithZero.exp_eq_coe_ofAdd]
  unfold ordInt
  rw [hu]
  simp

variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
  {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]
  {D' : Type*} [CommRing D'] [IsDomain D'] [IsNoetherianRing D'] [IsLocalRing D']
  {K' : Type*} [Field K'] [Algebra D' K'] [IsFractionRing D' K']
  (φ : D →+* D')

/-- **A one-dimensional Noetherian local domain whose maximal ideal is extended from a discrete
valuation ring is a discrete valuation ring**: its maximal ideal is generated by the image of a
uniformizer. -/
@[ega "II 7.1.6" "special case"]
theorem isDiscreteValuationRing_of_map_maximalIdeal (hdim' : ringKrullDim D' = 1)
    (hφ : (maximalIdeal D).map φ = maximalIdeal D') : IsDiscreteValuationRing D' := by
  have hfield : ¬ IsField D' := fun h ↦ by
    have := ringKrullDim_eq_zero_of_isField h
    rw [hdim'] at this
    exact one_ne_zero this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  have key : (maximalIdeal D').IsPrincipal := by
    refine ⟨⟨φ π, ?_⟩⟩
    rw [← hφ, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
      Set.image_singleton]
  exact ((IsDiscreteValuationRing.TFAE D' hfield).out 1 5).mpr key

variable [IsDiscreteValuationRing D']

omit [IsNoetherianRing D'] in
/-- The image of a uniformizer generates the maximal ideal, so it is a uniformizer. -/
theorem irreducible_map_of_map_maximalIdeal (hφ : (maximalIdeal D).map φ = maximalIdeal D')
    {π : D} (hπ : Irreducible π) : Irreducible (φ π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hφ,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
    Set.image_singleton]

variable (σ : K →+* K') (hσ : ∀ d, σ (algebraMap D K d) = algebraMap D' K' (φ d))

include hσ in
/-- **The order of vanishing is unchanged** along a homomorphism of discrete valuation rings
which carries a uniformizer to a uniformizer. -/
theorem ordInt_map_eq_of_map_maximalIdeal (hφ : (maximalIdeal D).map φ = maximalIdeal D')
    (x : Kˣ) : ordInt D' (σ x) ((map_ne_zero σ).mpr x.ne_zero) = ordInt D (x : K) x.ne_zero := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨n, u, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (x := (x : K)) x.ne_zero
  rw [ordInt_eq_of_eq_units_smul_zpow hπ x.ne_zero hx]
  refine ordInt_eq_of_eq_units_smul_zpow (irreducible_map_of_map_maximalIdeal φ hφ hπ) _
    (u := Units.map (φ : D →* D') u) ?_
  rw [hx, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, hσ, hσ, Units.smul_def,
    Algebra.smul_def, Units.coe_map]
  rfl

include hσ in
/-- **The tame symbol along a local homomorphism of discrete valuation rings with `𝔪 D' = 𝔪'`.**
Both symbols are given by the formula of Stacks 02Q6, the orders of vanishing agree, and the
representing unit of `D` is carried to a representing unit of `D'`. -/
theorem tameSymbol_map_eq_of_map_maximalIdeal [IsLocalHom φ]
    (hφ : (maximalIdeal D).map φ = maximalIdeal D') (hdim : ringKrullDim D = 1)
    (hdim' : ringKrullDim D' = 1) (x y : Kˣ) :
    tameSymbol (K := K') hdim' (Units.map (σ : K →* K') x) (Units.map (σ : K →* K') y) =
      Units.map (ResidueField.map φ : ResidueField D →* ResidueField D')
        (tameSymbol (K := K) hdim x y) := by
  have hx := ordInt_map_eq_of_map_maximalIdeal φ σ hσ hφ x
  have hy := ordInt_map_eq_of_map_maximalIdeal φ σ hσ hφ y
  obtain ⟨w, hw⟩ := exists_unit_algebraMap_eq_zpow_div_zpow (A := D) x y
  have hw' : algebraMap D' K' ((Units.map (φ : D →* D') w : D'ˣ) : D') =
      ((Units.map (σ : K →* K') x : K'ˣ) : K') ^
          (ordInt D' ((Units.map (σ : K →* K') y : K'ˣ) : K') (Units.ne_zero _)) /
        ((Units.map (σ : K →* K') y : K'ˣ) : K') ^
          (ordInt D' ((Units.map (σ : K →* K') x : K'ˣ) : K') (Units.ne_zero _)) := by
    show algebraMap D' K' (φ w) = σ x ^ ordInt D' (σ y) ((map_ne_zero σ).mpr y.ne_zero) /
      σ y ^ ordInt D' (σ x) ((map_ne_zero σ).mpr x.ne_zero)
    rw [hx, hy, ← hσ, hw, map_div₀, map_zpow₀, map_zpow₀]
  have h1 := tameSymbol_eq_negOnePow_mul_residue (A := D') (Units.map (σ : K →* K') x)
    (Units.map (σ : K →* K') y) (Units.map (φ : D →* D') w) hw'
  have h2 := tameSymbol_eq_negOnePow_mul_residue (A := D) x y w hw
  apply Units.ext
  refine h1.trans ?_
  show _ = ResidueField.map φ ((tameSymbol (K := K) hdim x y : (ResidueField D)ˣ) :
    ResidueField D)
  rw [h2, map_mul, ResidueField.map_residue]
  congr 1
  have e : ordInt D' ((Units.map (σ : K →* K') x : K'ˣ) : K') (Units.ne_zero _) *
      ordInt D' ((Units.map (σ : K →* K') y : K'ˣ) : K') (Units.ne_zero _) =
      ordInt D (x : K) x.ne_zero * ordInt D (y : K) y.ne_zero := by
    show ordInt D' (σ x) ((map_ne_zero σ).mpr x.ne_zero) *
      ordInt D' (σ y) ((map_ne_zero σ).mpr y.ne_zero) = _
    rw [hx, hy]
  rw [e, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_neg,
    Units.val_one, Units.val_neg, Units.val_one, map_neg, map_one]

end Algebra

/-! ### The same statements on Milnor K₂ -/

section MilnorAlgebra

variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  {K : Type u} [Field K] [Algebra D K] [IsFractionRing D K]
  {D' : Type u} [CommRing D'] [IsDomain D'] [IsNoetherianRing D'] [IsLocalRing D']
  {K' : Type u} [Field K'] [Algebra D' K'] [IsFractionRing D' K']

/-- In degree one, transport of Milnor K-theory along a homomorphism of fields is the map of unit
groups. -/
theorem milnorKTransport_symm_milnorKTheoryOneAddEquiv {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    (ψ : k₁ →+* k₂) (t : k₁ˣ) :
    milnorKTransport ψ 1 ((milnorKTheoryOneAddEquiv k₁).symm (Additive.ofMul t)) =
      (milnorKTheoryOneAddEquiv k₂).symm (Additive.ofMul (Units.map (ψ : k₁ →* k₂) t)) := by
  apply (milnorKTheoryOneAddEquiv k₂).injective
  rw [milnorKTheoryOneAddEquiv_milnorKTransport, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, milnorKUnitsMap_ofMul]

/-- **The Milnor K₂ boundary along a local homomorphism of discrete valuation rings with
`𝔪 D' = 𝔪'`** is the boundary downstairs followed by the map of residue fields. -/
theorem milnorKTwoTameSymbol_milnorKTransport_of_map_maximalIdeal [IsDiscreteValuationRing D]
    [IsDiscreteValuationRing D'] (φ : D →+* D') [IsLocalHom φ] (σ : K →+* K')
    (hσ : ∀ d, σ (algebraMap D K d) = algebraMap D' K' (φ d))
    (hφ : (maximalIdeal D).map φ = maximalIdeal D') (hdim : ringKrullDim D = 1)
    (hdim' : ringKrullDim D' = 1) (α : MilnorKTheory K 2) :
    milnorKTwoTameSymbol (K := K') hdim' (milnorKTransport σ 2 α) =
      milnorKTransport (ResidueField.map φ) 1 (milnorKTwoTameSymbol (K := K) hdim α) := by
  induction α using milnorKTwo_induction with
  | h0 => rw [map_zero, map_zero, map_zero, map_zero]
  | hsymb f g =>
      rw [milnorKTransport_milnorKTwoPureSymbol, milnorKTwoTameSymbol_pureSymbol,
        milnorKTwoTameSymbol_pureSymbol, milnorKTransport_symm_milnorKTheoryOneAddEquiv,
        tameSymbol_map_eq_of_map_maximalIdeal φ σ hσ hφ hdim hdim']
  | hadd a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- **The Milnor K₂ boundary kills what comes from units.** If every nonzero element of `K` is
carried by `σ` to the image of a unit of `D'`, the boundary of `D'` vanishes on the transport
along `σ` of every class of `K₂ᴹ(K)`. -/
theorem milnorKTwoTameSymbol_milnorKTransport_eq_zero (σ : K →+* K')
    (hσ : ∀ f : Kˣ, ∃ v : D'ˣ, σ f = algebraMap D' K' v) (hdim' : ringKrullDim D' = 1)
    (α : MilnorKTheory K 2) :
    milnorKTwoTameSymbol (K := K') hdim' (milnorKTransport σ 2 α) = 0 := by
  induction α using milnorKTwo_induction with
  | h0 => rw [map_zero, map_zero]
  | hsymb f g =>
      obtain ⟨u, hu⟩ := hσ f
      obtain ⟨v, hv⟩ := hσ g
      rw [milnorKTransport_milnorKTwoPureSymbol]
      exact milnorKTwoTameSymbol_pureSymbol_eq_zero_of_eq_algebraMap_units hdim' hu hv
  | hadd a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

/-- Degree-one transports along a commutative square of fields, one side of which is made of
ring equivalences, commute. -/
theorem milnorKOneTransport_milnorKTransport_of_comp_eq {k₁ k₂ k₃ k₄ : Type u} [Field k₁]
    [Field k₂] [Field k₃] [Field k₄] (e₁ : k₁ ≃+* k₂) (e₂ : k₃ ≃+* k₄) (f : k₁ →+* k₃)
    (g : k₂ →+* k₄) (h : e₂.toRingHom.comp f = g.comp e₁.toRingHom) (y : MilnorKTheory k₁ 1) :
    milnorKOneTransport e₂ (milnorKTransport f 1 y) =
      milnorKTransport g 1 (milnorKOneTransport e₁ y) := by
  rw [← milnorKTransport_eq_milnorKOneTransport, ← milnorKTransport_eq_milnorKOneTransport,
    ← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply, milnorKTransport_comp,
    milnorKTransport_comp]
  exact congrArg (fun ψ ↦ milnorKTransport ψ 1 y) h

end MilnorAlgebra


/-! ### The local rings of the closures of a point and of its image -/

section Geometry

attribute [local instance] isIntegral_integralComponentAt

section Restrict

variable {X : Scheme.{u}} (x : X) {x' : X} (h : x' ∈ closure ({x} : Set X))

/-- The restriction of germs at `x'` to the integral closed subscheme `closure {x}`: the stalk
map of its closed immersion at `x'`, a surjective local homomorphism. -/
def pointClosureRestrict :
    X.presheaf.stalk x' →+* (integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h) :=
  ((integralComponentAt x).subschemeι.stalkMap (pointClosurePoint x h)).hom

/-- The restriction to a closed subscheme is surjective on stalks. -/
theorem pointClosureRestrict_surjective : Function.Surjective (pointClosureRestrict x h) :=
  SurjectiveOnStalks.stalkMap_surjective _ _

/-- The restriction to a closed subscheme is a local homomorphism. -/
instance isLocalHom_pointClosureRestrict : IsLocalHom (pointClosureRestrict x h) :=
  inferInstanceAs (IsLocalHom ((integralComponentAt x).subschemeι.stalkMap
    (pointClosurePoint x h)).hom)

/-- The restriction of a germ, read in the function field `κ(x)` of `closure {x}`, is the value
at `x` of the germ specialized to `x`. -/
theorem pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict (hx : x ⤳ x')
    (s : X.presheaf.stalk x') :
    pointClosureFunctionFieldEquiv x
        (algebraMap _ (integralComponentAt x).subscheme.functionField
          (pointClosureRestrict x (specializes_iff_mem_closure.mp hx) s)) =
      X.residue x ((X.presheaf.stalkSpecializes hx).hom s) :=
  pointClosureFunctionFieldEquiv_algebraMap_stalkMap x
    (pointClosurePoint x (specializes_iff_mem_closure.mp hx)) hx s

/-- The restriction of a germ, read in the residue field of `closure {x}` at `x'` and identified
with `κ(x')`, is the value of the germ at `x'`. -/
theorem pointClosureResidueFieldEquiv_residue_pointClosureRestrict (s : X.presheaf.stalk x') :
    pointClosureResidueFieldEquiv x h (residue _ (pointClosureRestrict x h s)) =
      X.residue x' s :=
  pointClosureResidueFieldEquiv_residue x (pointClosurePoint x h) h s

end Restrict

variable {E B : Scheme.{u}} (q : E ⟶ B) {x x' : E} (hx : x ⤳ x')

/-- **A germ downstairs, pulled back and restricted to `closure {x}`, read in `κ(x)`**, is the
image under `κ(q x) → κ(x)` of its value at `q x`. -/
theorem pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict_stalkMap
    (s : B.presheaf.stalk (q.base x')) :
    pointClosureFunctionFieldEquiv x
        (algebraMap _ (integralComponentAt x).subscheme.functionField
          (pointClosureRestrict x (specializes_iff_mem_closure.mp hx) ((q.stalkMap x').hom s))) =
      q.residueFieldMap x (B.residue (q.base x)
        ((B.presheaf.stalkSpecializes (hx.map q.continuous)).hom s)) := by
  refine (pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict x hx
    ((q.stalkMap x').hom s)).trans ?_
  exact (congrArg (fun a ↦ E.residue x a)
    (Scheme.Hom.stalkSpecializes_stalkMap_apply q x x' hx s)).symm

/-- The germs at `q x'` pulled back along `q` and restricted to `closure {x}`. -/
def pointClosureStalkPullback :
    B.presheaf.stalk (q.base x') →+* (integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hx)) :=
  (pointClosureRestrict x (specializes_iff_mem_closure.mp hx)).comp (q.stalkMap x').hom

/-- A germ at `q x'` vanishing on `closure {q x}` pulls back to a germ vanishing on
`closure {x}`: both are detected in the function fields, and `κ(q x) → κ(x)` is injective. -/
theorem ker_pointClosureRestrict_le_ker_pointClosureStalkPullback :
    RingHom.ker (pointClosureRestrict (q.base x)
        (specializes_iff_mem_closure.mp (hx.map q.continuous))) ≤
      RingHom.ker (pointClosureStalkPullback q hx) := by
  intro s hs
  rw [RingHom.mem_ker] at hs ⊢
  apply (pointClosureFunctionFieldEquiv x).injective.comp
    (IsFractionRing.injective ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hx)))
      (integralComponentAt x).subscheme.functionField)
  refine (pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict_stalkMap q hx s).trans ?_
  have h0 := pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict (q.base x)
    (hx.map q.continuous) s
  rw [hs, map_zero, map_zero] at h0
  rw [Function.comp_apply, map_zero, map_zero, ← h0, map_zero]

/-- **The local homomorphism `𝒪_{closure {q x}, q x'} → 𝒪_{closure {x}, x'}`** induced by `q`:
the pullback of germs descends through the restriction to `closure {q x}`. -/
def pointClosureStalkHom :
    (integralComponentAt (q.base x)).subscheme.presheaf.stalk
        (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous))) →+*
      (integralComponentAt x).subscheme.presheaf.stalk
        (pointClosurePoint x (specializes_iff_mem_closure.mp hx)) :=
  (pointClosureRestrict (q.base x)
      (specializes_iff_mem_closure.mp (hx.map q.continuous))).liftOfSurjective
    (pointClosureRestrict_surjective _ _)
    ⟨pointClosureStalkPullback q hx, ker_pointClosureRestrict_le_ker_pointClosureStalkPullback q hx⟩

/-- `pointClosureStalkHom` sends the restriction of a germ to the restriction of its pullback. -/
theorem pointClosureStalkHom_pointClosureRestrict (s : B.presheaf.stalk (q.base x')) :
    pointClosureStalkHom q hx (pointClosureRestrict (q.base x)
        (specializes_iff_mem_closure.mp (hx.map q.continuous)) s) =
      pointClosureStalkPullback q hx s :=
  RingHom.liftOfSurjective_comp_apply _ _ _ s

/-- `pointClosureStalkHom` after the restriction to `closure {q x}` is the pullback of germs. -/
theorem pointClosureStalkHom_comp :
    (pointClosureStalkHom q hx).comp (pointClosureRestrict (q.base x)
        (specializes_iff_mem_closure.mp (hx.map q.continuous))) =
      pointClosureStalkPullback q hx :=
  RingHom.ext (pointClosureStalkHom_pointClosureRestrict q hx)

/-- `pointClosureStalkHom` is a local homomorphism: a germ whose pullback is a unit at `x'` is a
unit at `q x'`. -/
instance isLocalHom_pointClosureStalkHom : IsLocalHom (pointClosureStalkHom q hx) := by
  refine ⟨fun d hd ↦ ?_⟩
  obtain ⟨s, rfl⟩ := pointClosureRestrict_surjective (q.base x)
    (specializes_iff_mem_closure.mp (hx.map q.continuous)) d
  rw [pointClosureStalkHom_pointClosureRestrict] at hd
  have h1 : IsUnit ((q.stalkMap x').hom s) :=
    isUnit_of_map_unit (pointClosureRestrict x (specializes_iff_mem_closure.mp hx)) _ hd
  exact (isUnit_of_map_unit (q.stalkMap x').hom _ h1).map _

/-- **`pointClosureStalkHom` is compatible with `κ(q x) → κ(x)` on the function fields.** -/
theorem pointClosureFunctionFieldEquiv_algebraMap_pointClosureStalkHom
    (d : (integralComponentAt (q.base x)).subscheme.presheaf.stalk
        (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous)))) :
    pointClosureFunctionFieldEquiv x
        (algebraMap _ (integralComponentAt x).subscheme.functionField
          (pointClosureStalkHom q hx d)) =
      q.residueFieldMap x (pointClosureFunctionFieldEquiv (q.base x)
        (algebraMap _ (integralComponentAt (q.base x)).subscheme.functionField d)) := by
  obtain ⟨s, rfl⟩ := pointClosureRestrict_surjective (q.base x)
    (specializes_iff_mem_closure.mp (hx.map q.continuous)) d
  rw [pointClosureStalkHom_pointClosureRestrict, pointClosureStalkPullback, RingHom.comp_apply,
    pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict_stalkMap q hx s,
    pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict (q.base x)
      (hx.map q.continuous) s]

/-- **`pointClosureStalkHom` is compatible with `κ(q x') → κ(x')` on the residue fields.** -/
theorem pointClosureResidueFieldEquiv_map_pointClosureStalkHom
    (r : ResidueField ((integralComponentAt (q.base x)).subscheme.presheaf.stalk
        (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous))))) :
    pointClosureResidueFieldEquiv x (specializes_iff_mem_closure.mp hx)
        (ResidueField.map (pointClosureStalkHom q hx) r) =
      q.residueFieldMap x' (pointClosureResidueFieldEquiv (q.base x)
        (specializes_iff_mem_closure.mp (hx.map q.continuous)) r) := by
  obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨s, rfl⟩ := pointClosureRestrict_surjective (q.base x)
    (specializes_iff_mem_closure.mp (hx.map q.continuous)) d
  rw [ResidueField.map_residue, pointClosureStalkHom_pointClosureRestrict,
    pointClosureStalkPullback, RingHom.comp_apply,
    pointClosureResidueFieldEquiv_residue_pointClosureRestrict,
    pointClosureResidueFieldEquiv_residue_pointClosureRestrict]
  rfl

/-- **The maximal ideal is extended along `pointClosureStalkHom`** as soon as it is extended
along the stalk map `𝒪_{B, q x'} → 𝒪_{E, x'}`. -/
theorem map_maximalIdeal_pointClosureStalkHom
    (hlen : (maximalIdeal (B.presheaf.stalk (q.base x'))).map (q.stalkMap x').hom =
      maximalIdeal (E.presheaf.stalk x')) :
    (maximalIdeal _).map (pointClosureStalkHom q hx) = maximalIdeal _ := by
  rw [← map_maximalIdeal_of_surjective _ (pointClosureRestrict_surjective (q.base x)
      (specializes_iff_mem_closure.mp (hx.map q.continuous))),
    Ideal.map_map, pointClosureStalkHom_comp, pointClosureStalkPullback, ← Ideal.map_map, hlen,
    map_maximalIdeal_of_surjective _ (pointClosureRestrict_surjective _ _)]

/-! ### The local components of the first differential along `q` -/

variable (C : ChowSituation.{u}) (sE : E ⟶ C.S) [LocallyOfFiniteType sE]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB]

/-- **Horizontal points contribute nothing.** If `x ⤳ x'` and `x'` lies over the same point
`q x` as `x`, then the local component of the first differential at `x'` vanishes on every class
pulled back from `κ(q x)`: a nonzero element of `κ(q x)` is the value of a unit germ at `q x' =
q x`, whose pullback to `closure {x}` is a unit at `x'`, and the boundary kills pure symbols of
units. -/
theorem pointClosureMilnorBoundary_milnorKTransport_eq_zero_of_eq
    (hq : q.base x' = q.base x)
    (hdim : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hx))) = 1)
    (α : MilnorKTheory (B.residueField (q.base x)) 2) :
    pointClosureMilnorBoundary C sE x (specializes_iff_mem_closure.mp hx) hdim
      (milnorKTransport (q.residueFieldMap x).hom 2 α) = 0 := by
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ sE)
  let := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (pointClosurePoint x (specializes_iff_mem_closure.mp hx))
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (pointClosurePoint x (specializes_iff_mem_closure.mp hx))
  have hunits : ∀ f : (B.residueField (q.base x))ˣ, ∃ v :
      ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hx)))ˣ,
      (q.residueFieldMap x).hom (f : B.residueField (q.base x)) =
        algebraMap _ (E.residueField x) (v : (integralComponentAt x).subscheme.presheaf.stalk
          (pointClosurePoint x (specializes_iff_mem_closure.mp hx))) := by
    intro f
    obtain ⟨s₀, hs₀⟩ := IsLocalRing.residue_surjective (f : B.residueField (q.base x))
    have hs₀u : IsUnit s₀ := (residue_ne_zero_iff_isUnit s₀).mp (by rw [hs₀]; exact f.ne_zero)
    have hle : q.base x' ⤳ q.base x := by rw [hq]
    set s := (B.presheaf.stalkSpecializes hle).hom s₀ with hs
    have hsu : IsUnit s := hs₀u.map _
    have hback : (B.presheaf.stalkSpecializes (hx.map q.continuous)).hom s = s₀ := by
      rw [hs]
      simp
    refine ⟨(hsu.map ((pointClosureRestrict x (specializes_iff_mem_closure.mp hx)).comp
      (q.stalkMap x').hom)).unit, ?_⟩
    rw [IsUnit.unit_spec]
    refine Eq.trans ?_ (pointClosureFunctionFieldEquiv_algebraMap_pointClosureRestrict_stalkMap
      q hx s).symm
    rw [hback, ← hs₀]
    rfl
  exact (congrArg (milnorKOneTransport (pointClosureResidueFieldEquiv x
    (specializes_iff_mem_closure.mp hx)))
    (milnorKTwoTameSymbol_milnorKTransport_eq_zero (q.residueFieldMap x).hom hunits hdim α)).trans
    (map_zero _)

/-- **Vertical points: the local component of the first differential commutes with `q`.** Let
`x ⤳ x'` with `𝒪_{closure {q x}, q x'}` a discrete valuation ring, and suppose the maximal ideal
of `𝒪_{B, q x'}` generates that of `𝒪_{E, x'}`. Then `𝒪_{closure {x}, x'}` is a discrete
valuation ring with the same uniformizer, and the local component at `x'` of a class pulled back
from `κ(q x)` is the pullback along `κ(q x') → κ(x')` of the local component at `q x'`. -/
theorem pointClosureMilnorBoundary_milnorKTransport
    (hdimE : ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hx))) = 1)
    (hdimB : ringKrullDim ((integralComponentAt (q.base x)).subscheme.presheaf.stalk
      (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous)))) = 1)
    (hdvr : IsDiscreteValuationRing ((integralComponentAt (q.base x)).subscheme.presheaf.stalk
      (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous)))))
    (hlen : (maximalIdeal (B.presheaf.stalk (q.base x'))).map (q.stalkMap x').hom =
      maximalIdeal (E.presheaf.stalk x'))
    (α : MilnorKTheory (B.residueField (q.base x)) 2) :
    pointClosureMilnorBoundary C sE x (specializes_iff_mem_closure.mp hx) hdimE
        (milnorKTransport (q.residueFieldMap x).hom 2 α) =
      milnorKTransport (q.residueFieldMap x').hom 1
        (pointClosureMilnorBoundary C sB (q.base x)
          (specializes_iff_mem_closure.mp (hx.map q.continuous)) hdimB α) := by
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x).subschemeι ≫ sE)
  let : IsLocallyNoetherian (integralComponentAt (q.base x)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt (q.base x)).subschemeι ≫ sB)
  let := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (pointClosurePoint x (specializes_iff_mem_closure.mp hx))
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv x)
    (pointClosurePoint x (specializes_iff_mem_closure.mp hx))
  let := stalkAlgebraOfFunctionFieldEquiv (pointClosureFunctionFieldEquiv (q.base x))
    (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous)))
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv
    (pointClosureFunctionFieldEquiv (q.base x))
    (pointClosurePoint (q.base x) (specializes_iff_mem_closure.mp (hx.map q.continuous)))
  have hm := map_maximalIdeal_pointClosureStalkHom q hx hlen
  have : IsDiscreteValuationRing ((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x (specializes_iff_mem_closure.mp hx))) :=
    isDiscreteValuationRing_of_map_maximalIdeal (pointClosureStalkHom q hx) hdimE hm
  have key := milnorKTwoTameSymbol_milnorKTransport_of_map_maximalIdeal
    (pointClosureStalkHom q hx) (q.residueFieldMap x).hom
    (fun d ↦ (pointClosureFunctionFieldEquiv_algebraMap_pointClosureStalkHom q hx d).symm)
    hm hdimB hdimE α
  have hres : ((pointClosureResidueFieldEquiv x
      (specializes_iff_mem_closure.mp hx)).toRingHom.comp
        (ResidueField.map (pointClosureStalkHom q hx))) =
      (q.residueFieldMap x').hom.comp (pointClosureResidueFieldEquiv (q.base x)
        (specializes_iff_mem_closure.mp (hx.map q.continuous))).toRingHom :=
    RingHom.ext fun r ↦ pointClosureResidueFieldEquiv_map_pointClosureStalkHom q hx r
  show milnorKOneTransport (pointClosureResidueFieldEquiv x (specializes_iff_mem_closure.mp hx))
      (milnorKTwoTameSymbol hdimE (milnorKTransport (q.residueFieldMap x).hom 2 α)) =
    milnorKTransport (q.residueFieldMap x').hom 1 (milnorKOneTransport
      (pointClosureResidueFieldEquiv (q.base x)
        (specializes_iff_mem_closure.mp (hx.map q.continuous)))
      (milnorKTwoTameSymbol hdimB α))
  rw [key]
  exact milnorKOneTransport_milnorKTransport_of_comp_eq _ _ _ _ hres _

end Geometry

/-! ### Pulling the first differential back along an affine-space bundle -/

section Bundle

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {E B : Scheme.{u}} (sE : E ⟶ C.S) [LocallyOfFiniteType sE]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (q : E ⟶ B) (hbase : q ≫ sB = sE) {m : ℕ}
  (hb : IsAffineSpaceBundle q m)

include hbase hb in
/-- **At the generic point of a fibre the maximal ideal is extended.** The flat pullback
multiplicity there is one, and it is the colength of the extended maximal ideal. -/
theorem map_maximalIdeal_stalkMap_of_isAffineSpaceBundle {x' : E}
    (hx' : relativeDimension C.dimensionFunction sE x' =
      relativeDimension C.dimensionFunction sB (q.base x') + m) :
    (maximalIdeal (B.presheaf.stalk (q.base x'))).map (q.stalkMap x').hom =
      maximalIdeal (E.presheaf.stalk x') := by
  have := locallyOfFiniteType_of_isAffineSpaceBundle q m hb
  have hw := flatPullbackWeight_eq_one_of_isAffineSpaceBundle C sE sB q hbase hb hx'
  rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sE q _ x'
    (exists_genericPoints_comap_integralComponentAt C sE sB q hbase m
      (relativeDimension_of_isAffineSpaceBundle q m hb) x' hx') rfl] at hw
  have hl : Module.length (E.presheaf.stalk x') (E.presheaf.stalk x' ⧸
      (maximalIdeal (B.presheaf.stalk (q.base x'))).map (q.stalkMap x').hom) = 1 :=
    (ENat.toNat_eq_iff one_ne_zero).mp (by exact_mod_cast hw)
  rwa [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at hl

include hbase hb in
/-- **The generic point of a fibre specializes to every point over a specialization of its
image.** The inverse image of `closure {q x}` is integral, and its generic point is `x`. -/
theorem specializes_of_specializes_base_of_isAffineSpaceBundle {x e : E}
    (hx : relativeDimension C.dimensionFunction sE x =
      relativeDimension C.dimensionFunction sB (q.base x) + m)
    (he : q.base x ⤳ q.base e) : x ⤳ e := by
  set W := integralComponentAt (q.base x) with hW
  have : IsIntegral (W.comap q).subscheme :=
    isIntegral_of_isAffineSpaceBundle (comapRestrict W q) m
      (isAffineSpaceBundle_comapRestrict q hb W)
  have hmem : ∀ e' : E, e' ∈ Set.range (W.comap q).subschemeι.base ↔
      q.base e' ∈ closure ({q.base x} : Set B) := fun e' ↦ by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap, Set.mem_preimage, hW,
      coe_support_integralComponentAt]
  obtain ⟨z, hz⟩ := (hmem x).2 (subset_closure rfl)
  obtain ⟨z', hz'⟩ := (hmem e).2 (specializes_iff_mem_closure.mp he)
  set g := (W.comap q).subschemeι.base (genericPoint (W.comap q).subscheme) with hg
  have hgx : g ⤳ x := by
    rw [← hz]
    exact (genericPoint_specializes z).map (W.comap q).subschemeι.continuous
  have hge : g ⤳ e := by
    rw [← hz']
    exact (genericPoint_specializes z').map (W.comap q).subschemeι.continuous
  have hqg : q.base g = q.base x :=
    ((hgx.map q.continuous).antisymm
      (specializes_iff_mem_closure.mpr ((hmem g).1 ⟨_, rfl⟩))).eq
  exact (specializes_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sE sB q hbase hb hx
    hqg).trans hge

include hbase hb in
/-- **The contribution of the generic point of the fibre over `β` at the generic point of the
fibre over `q x'`** is the pullback of the contribution of `β` at `q x'`. -/
theorem pointwiseMilnorBoundaryTerm_bundleChainPullback_of_mem (k : ℤ) (T : Set B)
    (θ : PointwiseKTwoGroup C sB k)
    (hdvr : ∀ β : pointsOfDimension C sB (k + 2), θ.1 β ≠ 0 → ∀ w ∈ T,
      ∀ hw : (β : B) ⤳ w, relativeDimension C.dimensionFunction sB w = k + 1 →
        IsDiscreteValuationRing ((integralComponentAt β.1).subscheme.presheaf.stalk
          (pointClosurePoint β.1 (specializes_iff_mem_closure.mp hw))))
    (x : pointsOfDimension C sE (k + m + 2)) (β : pointsOfDimension C sB (k + 2))
    (hxβ : q.base x.1 = β.1) (x' : pointsOfDimension C sE (k + m + 1)) (hT : q.base x'.1 ∈ T)
    (hw : q.base x'.1 ∈ pointsOfDimension C sB (k + 1)) :
    pointwiseMilnorBoundaryTerm C sE (k + m)
        (bundleChainPullback C sE sB q hbase hb (k + 2) (k + m + 2) (by ring) 2 θ) x x' =
      milnorKTransport (q.residueFieldMap x'.1).hom 1
        (pointwiseMilnorBoundaryTerm C sB k θ β ⟨q.base x'.1, hw⟩) := by
  obtain ⟨b, hbm⟩ := β
  change q.base x.1 = b at hxβ
  subst hxβ
  have hxE := (mem_pointsOfDimension C sE).mp x.2
  have hx'E := (mem_pointsOfDimension C sE).mp x'.2
  have hxB := (mem_pointsOfDimension C sB).mp hbm
  have hx'B := (mem_pointsOfDimension C sB).mp hw
  have hxdim : relativeDimension C.dimensionFunction sE x.1 =
      relativeDimension C.dimensionFunction sB (q.base x.1) + m := by
    rw [hxE, hxB]
    ring
  have hx'dim : relativeDimension C.dimensionFunction sE x'.1 =
      relativeDimension C.dimensionFunction sB (q.base x'.1) + m := by
    rw [hx'E, hx'B]
    ring
  by_cases hs : x.1 ⤳ x'.1
  · have hsB : q.base x.1 ⤳ q.base x'.1 := hs.map q.continuous
    have hdimE := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one C sE hs
      (by rw [hxE, hx'E]; ring)
    have hdimB := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one C sB hsB
      (by rw [hxB, hx'B]; ring)
    rw [pointwiseMilnorBoundaryTerm_of_specializes C sE (k + m) _ x x' hs hdimE,
      pointwiseMilnorBoundaryTerm_of_specializes C sB k θ ⟨q.base x.1, hbm⟩ ⟨q.base x'.1, hw⟩ hsB
        hdimB,
      bundleChainPullback_apply_of_mem C sE sB q hbase hb _ θ x hbm]
    by_cases hθ : θ.1 ⟨q.base x.1, hbm⟩ = 0
    · rw [hθ, map_zero, map_zero, map_zero, map_zero]
    · exact pointClosureMilnorBoundary_milnorKTransport q hs C sE sB hdimE hdimB
        (hdvr ⟨q.base x.1, hbm⟩ hθ _ hT hsB hx'B)
        (map_maximalIdeal_stalkMap_of_isAffineSpaceBundle C sE sB q hbase hb hx'dim) _
  · rw [pointwiseMilnorBoundaryTerm_of_not_specializes C sE (k + m) _ x x' hs,
      pointwiseMilnorBoundaryTerm_of_not_specializes C sB k θ ⟨q.base x.1, hbm⟩ ⟨q.base x'.1, hw⟩
        (fun h ↦ hs (specializes_of_specializes_base_of_isAffineSpaceBundle C sE sB q hbase hb
          hxdim h)),
      map_zero]

include hbase hb in
/-- **Nothing is contributed at a point which is not the generic point of a fibre over a point
of relative dimension `k + 1`**: a point of the pulled-back chain specializing to it lies over
the same point, and horizontal contributions vanish. -/
theorem pointwiseMilnorBoundaryTerm_bundleChainPullback_eq_zero (k : ℤ)
    (θ : PointwiseKTwoGroup C sB k) (x : pointsOfDimension C sE (k + m + 2))
    (x' : pointsOfDimension C sE (k + m + 1))
    (hw : q.base x'.1 ∉ pointsOfDimension C sB (k + 1)) :
    pointwiseMilnorBoundaryTerm C sE (k + m)
        (bundleChainPullback C sE sB q hbase hb (k + 2) (k + m + 2) (by ring) 2 θ) x x' = 0 := by
  by_cases hΘ : (bundleChainPullback C sE sB q hbase hb (k + 2) (k + m + 2) (by ring) 2 θ).1 x = 0
  · exact pointwiseMilnorBoundaryTerm_of_eq_zero C sE (k + m) _ hΘ x'
  obtain ⟨hmem, -⟩ :=
    relativeDimension_eq_add_of_bundleChainPullback_ne_zero C sE sB q hbase hb _ θ hΘ
  by_cases hs : x.1 ⤳ x'.1
  · have hsB : q.base x.1 ⤳ q.base x'.1 := hs.map q.continuous
    have hxE := (mem_pointsOfDimension C sE).mp x.2
    have hx'E := (mem_pointsOfDimension C sE).mp x'.2
    have hxB := (mem_pointsOfDimension C sB).mp hmem
    have h1 := relativeDimension_le_of_specializes C sB hsB
    have h2 := relativeDimension_le_add_of_isAffineSpaceBundle C sE sB q hbase hb x'.1
    have h4 : relativeDimension C.dimensionFunction sB (q.base x'.1) ≠ k + 1 :=
      fun h ↦ hw ((mem_pointsOfDimension C sB).mpr h)
    have heq : q.base x'.1 = q.base x.1 := by
      by_contra hne
      have := relativeDimension_lt_of_specializes C sB hsB (Ne.symm hne)
      omega
    have hdimE := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one C sE hs
      (by rw [hxE, hx'E]; ring)
    rw [pointwiseMilnorBoundaryTerm_of_specializes C sE (k + m) _ x x' hs hdimE,
      bundleChainPullback_apply_of_mem C sE sB q hbase hb _ θ x hmem]
    exact pointClosureMilnorBoundary_milnorKTransport_eq_zero_of_eq q hs C sE heq hdimE _
  · exact pointwiseMilnorBoundaryTerm_of_not_specializes C sE (k + m) _ x x' hs

attribute [local instance] isIntegral_integralComponentAt in
include hbase hb in
/-- **The tame-symbol differential commutes with pulling back along an affine-space bundle**,
on the preimage of any set `T` of points of `B` at which the local rings of the closures of the
points of the chain are discrete valuation rings. At the generic point of the fibre over a point
`w ∈ T` of relative dimension `k + 1` the contribution of the generic point of the fibre over `β`
is the pullback of the contribution of `β` at `w`, because the local ring upstairs is a discrete
valuation ring with the same uniformizer; every other point of `q⁻¹ T` receives only horizontal
contributions, which vanish. -/
theorem milnorChainRestrict_pointwiseMilnorBoundary_bundleChainPullback (k : ℤ) (T : Set B)
    (θ : PointwiseKTwoGroup C sB k)
    (hdvr : ∀ β : pointsOfDimension C sB (k + 2), θ.1 β ≠ 0 → ∀ w ∈ T,
      ∀ hw : (β : B) ⤳ w, relativeDimension C.dimensionFunction sB w = k + 1 →
        IsDiscreteValuationRing ((integralComponentAt β.1).subscheme.presheaf.stalk
          (pointClosurePoint β.1 (specializes_iff_mem_closure.mp hw)))) :
    milnorChainRestrict C sE (q.base ⁻¹' T) (k + m + 1) 1
        (pointwiseMilnorBoundary C sE (k + m)
          (bundleChainPullback C sE sB q hbase hb (k + 2) (k + m + 2) (by ring) 2 θ)) =
      bundleChainPullback C sE sB q hbase hb (k + 1) (k + m + 1) (by ring) 1
        (milnorChainRestrict C sB T (k + 1) 1 (pointwiseMilnorBoundary C sB k θ)) := by
  refine Subtype.ext (funext fun x' ↦ ?_)
  by_cases hT : x'.1 ∈ q.base ⁻¹' T
  · rw [milnorChainRestrict_apply_of_mem _ hT, pointwiseMilnorBoundary_apply,
      pointwiseMilnorBoundaryCoeff]
    by_cases hw : q.base x'.1 ∈ pointsOfDimension C sB (k + 1)
    · rw [bundleChainPullback_apply_of_mem C sE sB q hbase hb _ _ x' hw,
        milnorChainRestrict_apply_of_mem (T := T) (x := ⟨q.base x'.1, hw⟩) _
          (show q.base x'.1 ∈ T from hT),
        pointwiseMilnorBoundary_apply, pointwiseMilnorBoundaryCoeff,
        AddMonoidHom.map_finsum (milnorKTransport (q.residueFieldMap x'.1).hom 1)
          (finite_support_pointwiseMilnorBoundaryTerm C sB k θ ⟨q.base x'.1, hw⟩)]
      choose g hg using fun β : pointsOfDimension C sB (k + 2) ↦
        exists_relativeDimension_eq_add_of_isAffineSpaceBundle C sE sB q hbase hb β.1
      let G : pointsOfDimension C sB (k + 2) → pointsOfDimension C sE (k + m + 2) := fun β ↦
        ⟨g β, by
          rw [mem_pointsOfDimension, (hg β).2.1, (mem_pointsOfDimension C sB).mp β.2]
          ring⟩
      have hGinj : Function.Injective G := fun β β' h ↦ Subtype.ext (by
        rw [← (hg β).1, ← (hg β').1]
        exact congrArg (fun z : pointsOfDimension C sE (k + m + 2) ↦ q.base z.1) h)
      rw [finsum_eq_finsum_of_injective G hGinj _ ?_]
      · exact finsum_congr fun β ↦ pointwiseMilnorBoundaryTerm_bundleChainPullback_of_mem C sE sB
          q hbase hb k T θ hdvr (G β) β (hg β).1 x' hT hw
      · intro x hx
        by_contra hne
        have hΘ : (bundleChainPullback C sE sB q hbase hb (k + 2) (k + m + 2) (by ring) 2 θ).1 x
            ≠ 0 := fun h0 ↦ hne (pointwiseMilnorBoundaryTerm_of_eq_zero C sE (k + m) _ h0 x')
        obtain ⟨hmem, -⟩ :=
          relativeDimension_eq_add_of_bundleChainPullback_ne_zero C sE sB q hbase hb _ θ hΘ
        refine hx ⟨⟨q.base x.1, hmem⟩, Subtype.ext ?_⟩
        refine eq_of_relativeDimension_eq_add_of_isAffineSpaceBundle C sE sB q hbase hb
          (hg _).1 ?_ ?_
        · rw [(hg _).2.1, (hg _).1]
        · rw [(mem_pointsOfDimension C sE).mp x.2, (mem_pointsOfDimension C sB).mp hmem]
          ring
    · rw [bundleChainPullback_apply_of_notMem C sE sB q hbase hb _ _ x' hw]
      exact (finsum_congr fun x ↦ pointwiseMilnorBoundaryTerm_bundleChainPullback_eq_zero C sE sB
        q hbase hb k θ x x' hw).trans finsum_zero
  · rw [milnorChainRestrict_apply_of_notMem _ hT]
    by_cases hw : q.base x'.1 ∈ pointsOfDimension C sB (k + 1)
    · rw [bundleChainPullback_apply_of_mem C sE sB q hbase hb _ _ x' hw,
        milnorChainRestrict_apply_of_notMem (T := T) (x := ⟨q.base x'.1, hw⟩) _
          (show q.base x'.1 ∉ T from hT), map_zero]
    · rw [bundleChainPullback_apply_of_notMem C sE sB q hbase hb _ _ x' hw]

end Bundle

end Stacks.Chow

end
