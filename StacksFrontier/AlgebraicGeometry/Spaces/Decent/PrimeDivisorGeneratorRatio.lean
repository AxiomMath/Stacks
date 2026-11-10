module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicChartFunctionField
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionSheafGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial

/-!
# The ratio of a meromorphic section against a generator over a trivialising chart

Let `F` be an algebraic space over a scheme `S` and let `L` be an `𝒪_F`-module which is
isomorphic to `𝒪_F`. Then `L` has a free generator over every étale chart of `F`, compatibly
with restriction, and the sections of the sheaf `𝒦_F(L)` of meromorphic sections over a chart
are exactly the multiples of that generator by meromorphic functions.

## Main results

* `AlgebraicGeometry.Space.exists_generator_smul_of_iso_unit`: an `𝒪_F`-module isomorphic to
  `𝒪_F` has a free generator over every chart, compatibly with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The ring of meromorphic functions over an étale chart, read through the ring sheaf of the
meromorphic ringed site and read through the sheaf `𝒦_F` of commutative rings of Stacks 0EN3, is
one and the same ring; this is the identity, in the shape instance search can use. -/
def meromorphicChartRingEquiv (V : SmallEtale B S hS F) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS F hF).O).obj.obj
        (op V) ≃+*
      ((meromorphicFunctionSheaf B S hS F hF).obj.obj (op V)) :=
  RingEquiv.refl _

/-- **A module isomorphic to the structure sheaf has a free generator over every chart.** The
generator is the global section of `L` corresponding to the isomorphism, so its compatibility
with restriction is the compatibility of a section, and freeness over a chart is bijectivity of
the isomorphism there. -/
theorem exists_generator_smul_of_iso_unit (L : Modules.{u, u} B S hS F hF)
    (φ : L ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (V : SmallEtale B S hS F) :
    ∃ e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W),
      (∀ (W W' : SmallEtale B S hS F) (k : W ⟶ V) (g : W' ⟶ W),
          (L.val.map g.op).hom (e W k) = e W' (g ≫ k)) ∧
      ∀ (W : SmallEtale B S hS F) (k : W ⟶ V),
        Function.Bijective fun r : chartRing B S hS F hF W ↦ r • e W k := by
  set e : (W : SmallEtale B S hS F) → (W ⟶ V) → L.val.obj (op W) :=
    fun W _ ↦ (L.unitHomEquiv φ.inv).val (op W) with he
  refine ⟨e, ?_, ?_⟩
  · intro W W' k g
    exact PresheafOfModules.sections_property (M := L.val) (L.unitHomEquiv φ.inv) g.op
  · intro W k
    have hsmul : (fun r : chartRing B S hS F hF W ↦ r • e W k) =
        fun r : chartRing B S hS F hF W ↦ (φ.inv.val.app (op W)).hom r := by
      funext r
      have h1 : e W k = (φ.inv.val.app (op W)).hom (1 : chartRing B S hS F hF W) := rfl
      rw [h1, ← (φ.inv.val.app (op W)).hom.map_smul r (1 : chartRing B S hS F hF W)]
      exact congrArg (φ.inv.val.app (op W)).hom
        ((smul_eq_mul (α := chartRing B S hS F hF W) r 1).trans (mul_one r))
    rw [hsmul]
    refine Function.bijective_iff_has_inverse.2
      ⟨(φ.hom.val.app (op W)).hom, fun x ↦ ?_, fun y ↦ ?_⟩
    · have h := congrArg (fun ψ ↦ ψ.val.app (op W)) φ.inv_hom_id
      exact ConcreteCategory.congr_hom h x
    · have h := congrArg (fun ψ ↦ ψ.val.app (op W)) φ.hom_inv_id
      exact ConcreteCategory.congr_hom h y

/-! ### The trivialisation at the generic point of a prime divisor -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-- **An invertible `𝒪_X`-module pulled back to `Spec(𝒪_{U, u})` is the structure sheaf**, where
`(U, u)` is the chosen affine elementary étale neighbourhood of the generic point of a prime
divisor: this is the triviality of the Picard group of the local ring `𝒪_{U, u}`. -/
theorem PrimeDivisor.nonempty_iso_unit_genericStalkPullback (L : Modules.{u, u} B S hS X hX)
    (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L) :
    Nonempty ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2).O)) :=
  nonempty_iso_unit_of_isInvertibleModule_of_forall_eq_top B S hS
    (Z.genericStalkSpec B S hS hX hdec) rfl
    (IsLocalRing.closedPoint (Z.genericStalkRing B S hS hX hdec))
    (forall_eq_top_of_mem_of_isLocalRing (Z.genericStalkRing B S hS hX hdec))
    (Z.genericStalkSpace B S hS hX hdec).2 _
    (modulePullbackInvertible (Z.genericStalkMorphism B S hS hX hdec) L hL)

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)

/-- `Spec(𝒪_{U, u})` as the identity chart of the algebraic space it represents. -/
abbrev PrimeDivisor.genericStalkChart :
    SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1 :=
  idEtaleChart B S hS (Z.genericStalkSpec B S hS hX hdec)

/-- The chosen trivialisation of the pullback of an invertible `𝒪_X`-module to
`Spec(𝒪_{U, u})`. -/
def PrimeDivisor.genericStalkTrivialisation :
    (modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2).O) :=
  (Z.nonempty_iso_unit_genericStalkPullback B S hS hX hdec L hL).some

/-- **The generator `s_ξ`.** The free generator of the pullback of `ℒ` to `Spec(𝒪_{U, u})` over
every chart of it, read off from the chosen trivialisation. -/
def PrimeDivisor.genericStalkGenerator :
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1) →
      (W ⟶ Z.genericStalkChart B S hS hX hdec) →
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.obj (op W) :=
  (exists_generator_smul_of_iso_unit B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _
    (Z.genericStalkTrivialisation B S hS hX hdec L hL)
    (Z.genericStalkChart B S hS hX hdec)).choose

/-- The generator of the pullback of `ℒ` is compatible with restriction. -/
theorem PrimeDivisor.genericStalkGenerator_compat
    (W W' : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) (g : W' ⟶ W) :
    (((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.map g.op).hom
        (Z.genericStalkGenerator B S hS hX hdec L hL W k) =
      Z.genericStalkGenerator B S hS hX hdec L hL W' (g ≫ k) :=
  (exists_generator_smul_of_iso_unit B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _
    (Z.genericStalkTrivialisation B S hS hX hdec L hL)
    (Z.genericStalkChart B S hS hX hdec)).choose_spec.1 W W' k g

/-- The generator of the pullback of `ℒ` freely generates it over every chart. -/
theorem PrimeDivisor.bijective_smul_genericStalkGenerator
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    Function.Bijective fun r : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 W ↦
      r • Z.genericStalkGenerator B S hS hX hdec L hL W k :=
  (exists_generator_smul_of_iso_unit B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 _
    (Z.genericStalkTrivialisation B S hS hX hdec L hL)
    (Z.genericStalkChart B S hS hX hdec)).choose_spec.2 W k

/-- **The sections of `𝒦(j^*ℒ)` over a chart of `Spec(𝒪_{U, u})` are the multiples of the
generator by meromorphic functions.** This is the module analogue of Stacks 0EN6, part (2) at
the generator `s_ξ`.

The chart is arbitrary, not the identity chart of `Spec(𝒪_{U, u})`: the generator
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkGenerator` restricts to a free generator over
every chart over the identity one, which is all
`AlgebraicGeometry.Space.bijective_toMeromorphicSectionSheaf_tmul` asks for, applied to the
family reindexed along `k`. Uniqueness of the coefficient over a chart that is *not* the
identity one is what reading a presentation transported from an étale chart of `X` needs. -/
theorem PrimeDivisor.bijective_genericStalkTmul
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    Function.Bijective fun a : (Stacks.SheafOfModules.Tensor.ringSheaf (meromorphicRingedSite B S hS
        (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).O).obj.obj (op W) ↦
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) W
        (a ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2 W]
          Z.genericStalkGenerator B S hS hX hdec L hL W k :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
              (op W)) := by
  have h := bijective_toMeromorphicSectionSheaf_tmul B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2 _ W
    (fun W' (g : W' ⟶ W) ↦ Z.genericStalkGenerator B S hS hX hdec L hL W' (g ≫ k))
    (fun W₁ W₂ k₁ g ↦
      (Z.genericStalkGenerator_compat B S hS hX hdec L hL W₁ W₂ (k₁ ≫ k) g).trans
        (congrArg (Z.genericStalkGenerator B S hS hX hdec L hL W₂)
          (Category.assoc g k₁ k).symm))
    fun W₁ k₁ ↦ Z.bijective_smul_genericStalkGenerator B S hS hX hdec L hL W₁ (k₁ ≫ k)
  simpa only [Category.id_comp] using h

/-! ### The hypotheses of Stacks 0EN6 on `Spec(𝒪_{U, u})` -/

variable (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hInt in
/-- `𝒪_{U, u}` is reduced, being a local ring of a scheme étale over a reduced algebraic
space. -/
theorem PrimeDivisor.isReduced_genericStalkRing :
    _root_.IsReduced ↥(Z.genericStalkRing B S hS hX hdec) :=
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme) :=
    Z.isReduced_chart B S hS hX hInt (Z.genericChart B S hS hX hdec)
  isReduced_stalk_of_isReduced _ _

include hN in
/-- `𝒪_{U, u}` is Noetherian, being a local ring of a locally Noetherian scheme. -/
theorem PrimeDivisor.isNoetherianRing_genericStalkRing :
    IsNoetherianRing ↥(Z.genericStalkRing B S hS hX hdec) :=
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme) :=
    Z.isLocallyNoetherian_chart B S hS hX hN (Z.genericChart B S hS hX hdec)
  inferInstance

include hInt in
/-- `Spec(𝒪_{U, u})` is reduced, étale-locally on the algebraic space it represents. -/
theorem PrimeDivisor.hasEtaleLocalProperty_isReduced_genericStalkSpace :
    HasEtaleLocalProperty B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (fun T : Scheme.{u} ↦ IsReduced T) :=
  have := Z.isReduced_genericStalkRing B S hS hX hdec hInt
  hasEtaleLocalProperty_of_representable B S hS _ _ (Z.genericStalkSpec B S hS hX hdec)
    (Iso.refl _) (inferInstanceAs (IsReduced (Spec (Z.genericStalkRing B S hS hX hdec))))

include hN in
/-- `Spec(𝒪_{U, u})` is locally Noetherian, étale-locally on the algebraic space it
represents. -/
theorem PrimeDivisor.hasEtaleLocalProperty_isLocallyNoetherian_genericStalkSpace :
    HasEtaleLocalProperty B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
  have := Z.isNoetherianRing_genericStalkRing B S hS hX hdec hN
  hasEtaleLocalProperty_of_representable B S hS _ _ (Z.genericStalkSpec B S hS hX hdec)
    (Iso.refl _)
    (inferInstanceAs (IsLocallyNoetherian (Spec (Z.genericStalkRing B S hS hX hdec))))

include hInt in
/-- **Hypothesis (a) of Stacks 0EN6 on `Spec(𝒪_{U, u})`.** Every weakly associated point of
`Spec(𝒪_{U, u})` has codimension zero, the ring being reduced. -/
theorem PrimeDivisor.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace :
    ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS (Z.genericStalkSpace B S hS hX hdec),
      localRingDimension B S hS z = 0 := fun _ hz => by
  rwa [weaklyAssociatedPointsOfSpace_eq_setOf_localRingDimension_eq_zero B S hS _
    (Z.hasEtaleLocalProperty_isReduced_genericStalkSpace B S hS hX hdec hInt)] at hz

include hN in
/-- **Hypothesis (b) of Stacks 0EN6 on `Spec(𝒪_{U, u})`.** The irreducible components of
`Spec(𝒪_{U, u})` are locally finite, the ring being Noetherian. -/
theorem PrimeDivisor.hasLocallyFiniteIrreducibleComponents_genericStalkSpace :
    HasLocallyFiniteIrreducibleComponents B S hS (Z.genericStalkSpace B S hS hX hdec).1 :=
  hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS _
    (Z.genericStalkSpace B S hS hX hdec).2
    (Z.hasEtaleLocalProperty_isLocallyNoetherian_genericStalkSpace B S hS hX hdec hN)

/-! ### The coefficient of a meromorphic section against the generator -/

/-- The chart `Spec(𝒪_{U, u})` is affine. -/
theorem PrimeDivisor.isAffine_genericStalkChart :
    IsAffine (smallEtaleScheme B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkChart B S hS hX hdec)) :=
  inferInstanceAs (IsAffine (Spec (Z.genericStalkRing B S hS hX hdec)))

/-- **The coefficient `s / s_ξ` over the chart `Spec(𝒪_{U, u})`.** The pullback of a
meromorphic section `t` of `ℒ` to `Spec(𝒪_{U, u})` is `a · s_ξ` for exactly one meromorphic
function `a` there, and this is that `a`. -/
def PrimeDivisor.genericStalkCoefficient (t : MeromorphicSection.{u, u} B S hS X hX L) :
    (meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)) :=
  (Equiv.ofBijective _ (Z.bijective_genericStalkTmul B S hS hX hdec L hL
    (Z.genericStalkChart B S hS hX hdec) (𝟙 (Z.genericStalkChart B S hS hX hdec)))).symm
    ((pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval
        (op (Z.genericStalkChart B S hS hX hdec)))

/-- **The defining property of the coefficient**: the pullback of `t` to `Spec(𝒪_{U, u})` is the
coefficient times the generator `s_ξ`. -/
theorem PrimeDivisor.genericStalkCoefficient_spec (t : MeromorphicSection.{u, u} B S hS X hX L) :
    (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval
        (op (Z.genericStalkChart B S hS hX hdec)) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
        (Z.genericStalkChart B S hS hX hdec)
        (Z.genericStalkCoefficient B S hS hX hdec L hL t ⊗ₜ[chartRing B S hS
            (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
            (Z.genericStalkChart B S hS hX hdec)]
          Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
            (𝟙 (Z.genericStalkChart B S hS hX hdec)) :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
              (op (Z.genericStalkChart B S hS hX hdec))) :=
  ((Equiv.ofBijective _ (Z.bijective_genericStalkTmul B S hS hX hdec L hL
    (Z.genericStalkChart B S hS hX hdec)
    (𝟙 (Z.genericStalkChart B S hS hX hdec)))).apply_symm_apply _).symm

/-- **The defining property of the coefficient, read over any chart of `Spec(𝒪_{U, u})`.** Over
a chart `W` of `Spec(𝒪_{U, u})` the pullback of `t` is the *restriction* of the coefficient
times the generator `s_ξ` there.

`AlgebraicGeometry.Space.PrimeDivisor.genericStalkCoefficient_spec` is this at the identity
chart, which is where the coefficient is defined; the general chart is what reading a
presentation transported from an étale chart `V` of `X` needs, since `Spec(𝒪_{U, u})` need not
map into `V` and the two are compared only over a common chart. Both the coefficient and the
generator restrict — the generator by
`AlgebraicGeometry.Space.PrimeDivisor.genericStalkGenerator_compat` — so the presentation
does. -/
theorem PrimeDivisor.genericStalkCoefficient_spec_restrict
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (W : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericStalkChart B S hS hX hdec) :
    (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
          (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval (op W) =
      toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) W
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
              (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
                (Z.genericStalkSpace B S hS hX hdec).2).O).obj.map k.op).hom
            (Z.genericStalkCoefficient B S hS hX hdec L hL t)) ⊗ₜ[chartRing B S hS
            (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2 W]
          Z.genericStalkGenerator B S hS hX hdec L hL W k :
          (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2
            ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
              (op W)) :=
  eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
    (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
      (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t)
    (Z.genericStalkChart B S hS hX hdec)
    (Z.genericStalkGenerator B S hS hX hdec L hL)
    (Z.genericStalkGenerator_compat B S hS hX hdec L hL)
    (Z.genericStalkCoefficient B S hS hX hdec L hL t)
    (Z.genericStalkCoefficient_spec B S hS hX hdec L hL t) W k

/-! ### From the meromorphic functions on `Spec(𝒪_{U, u})` to `Q(𝒪^h_{X, ξ})` -/

/-- The algebra structure of the meromorphic functions over the chart `Spec(𝒪_{U, u})` over its
regular functions.  This is `AlgebraicGeometry.Space.chartMeromorphicFunctionAlgebra` at that
chart of `Spec(𝒪_{U, u})`. -/
abbrev PrimeDivisor.genericStalkMeromorphicAlgebra :
    Algebra ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec))) :=
  chartMeromorphicFunctionAlgebra B S hS (Z.genericStalkSpace B S hS hX hdec)
    (Z.genericStalkChart B S hS hX hdec)

attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra

include hInt hN in
/-- **Stacks 0EN6, part (2) at `Spec(𝒪_{U, u})`.** The meromorphic functions over the affine
chart `Spec(𝒪_{U, u})` are the total ring of fractions of its regular functions. -/
theorem PrimeDivisor.isFractionRing_genericStalkMeromorphic :
    IsFractionRing ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec)))
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec))) :=
  isFractionRing_meromorphicFunctionSheaf_obj B S hS (Z.genericStalkSpace B S hS hX hdec)
    (Z.localRingDimension_eq_zero_of_mem_weaklyAssociated_genericStalkSpace B S hS hX hdec hInt)
    (Z.hasLocallyFiniteIrreducibleComponents_genericStalkSpace B S hS hX hdec hN)
    (Z.genericStalkChart B S hS hX hdec) (Z.isAffine_genericStalkChart B S hS hX hdec)

/-- The comparison of the global sections of a spectrum with the ring carries nonzerodivisors
to nonzerodivisors, being a ring isomorphism. -/
private theorem mem_nonZeroDivisors_ΓSpecIso_hom {R : CommRingCat.{u}} {y : ↥Γ(Spec R, ⊤)}
    (hy : y ∈ (↥Γ(Spec R, ⊤))⁰) : (Scheme.ΓSpecIso R).hom.hom y ∈ (↥R)⁰ := by
  rw [← MulEquivClass.map_nonZeroDivisors (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv]
  exact Submonoid.mem_map_of_mem _ hy

/-- The regular functions on the chart `Spec(𝒪_{U, u})` map to the henselian local ring at the
generic point of the prime divisor: they are `𝒪_{U, u}` itself, which maps there by Stacks
0EMY. -/
def PrimeDivisor.genericStalkSectionsToHenselian :
    ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
        (op (Z.genericStalkChart B S hS hX hdec))) →+*
      ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      (Z.genericChart B S hS hX hdec)).comp
    (Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom

/-- The map from the regular functions on `Spec(𝒪_{U, u})` into the henselian local ring at the
generic point of the prime divisor carries nonzerodivisors to nonzerodivisors: it is the
structure map of a henselization read through an isomorphism. -/
theorem PrimeDivisor.genericStalkSectionsToHenselian_mem_nonZeroDivisors
    {y : ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec)))}
    (hy : y ∈ (((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))))⁰) :
    Z.genericStalkSectionsToHenselian B S hS hX hdec y ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ := by
  have : IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
    henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  exact stalkToHenselianLocalRing_mem_nonZeroDivisors B S hS hX hdec Z
    (Z.genericChart B S hS hX hdec) (mem_nonZeroDivisors_ΓSpecIso_hom hy)

include hInt hN in
/-- **The meromorphic functions on `Spec(𝒪_{U, u})` map to `Q(𝒪^h_{X, ξ})`.** They are the total
ring of fractions of `𝒪_{U, u}` by Stacks 0EN6, part (2), and `𝒪_{U, u} → 𝒪^h_{X, ξ}` carries
nonzerodivisors to nonzerodivisors. -/
def PrimeDivisor.genericStalkMeromorphicToGeneric :
    ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec))) →+*
      Z.genericTotalFractionRing B S hS hX hdec :=
  haveI := Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN
  IsLocalization.lift
    (M := (((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))))⁰)
    (g := (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec)).comp
      (Z.genericStalkSectionsToHenselian B S hS hX hdec))
    fun y ↦ IsLocalization.map_units (Z.genericTotalFractionRing B S hS hX hdec)
      ⟨Z.genericStalkSectionsToHenselian B S hS hX hdec (y : _),
        Z.genericStalkSectionsToHenselian_mem_nonZeroDivisors B S hS hX hdec y.2⟩

include hInt hN in
/-- On a *regular* function the map above is the composite `𝒪_{U, u} → 𝒪^h_{X, ξ} →
Q(𝒪^h_{X, ξ})`, being the localization lift of exactly that composite. -/
theorem PrimeDivisor.genericStalkMeromorphicToGeneric_algebraMap
    (w : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))) :
    Z.genericStalkMeromorphicToGeneric B S hS hX hdec hInt hN
        (algebraMap ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
            (op (Z.genericStalkChart B S hS hX hdec)))
          ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
              (op (Z.genericStalkChart B S hS hX hdec))) w) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec)
        (Z.genericStalkSectionsToHenselian B S hS hX hdec w) :=
  have := Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN
  IsLocalization.lift_eq _ w

/-! ### Regularity makes the coefficient a unit -/

/-- **Multiplication by the coefficient is injective for a regular meromorphic section.** The
pullback of a regular meromorphic section is regular by Stacks 0ENC, part (2), and over the
chart `Spec(𝒪_{U, u})` multiplication by it is multiplication of the coefficient. -/
theorem PrimeDivisor.injective_mul_genericStalkCoefficient
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) :
    Function.Injective fun r : (meromorphicFunctionSheaf B S hS
        (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec)) ↦
      r * Z.genericStalkCoefficient B S hS hX hdec L hL t := by
  have hreg := isRegularMeromorphicSection_pullbackMeromorphicSection B S hS
    (Z.genericStalkMorphism B S hS hX hdec)
    (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL) t ht
  have h := hreg (Z.genericStalkChart B S hS hX hdec)
  have key : ∀ r : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).O).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)),
      r • (pullbackMeromorphicSection B S hS (Z.genericStalkMorphism B S hS hX hdec) L
            (Z.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec) t).eval
          (op (Z.genericStalkChart B S hS hX hdec)) =
        toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
          (Z.genericStalkChart B S hS hX hdec)
          ((r * (meromorphicChartRingEquiv B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2
              (Z.genericStalkChart B S hS hX hdec)).symm
                (Z.genericStalkCoefficient B S hS hX hdec L hL t)) ⊗ₜ[chartRing B S hS
              (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
              (Z.genericStalkChart B S hS hX hdec)]
            Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
              (𝟙 (Z.genericStalkChart B S hS hX hdec)) :
            (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
              (Z.genericStalkSpace B S hS hX hdec).2
              ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
                (op (Z.genericStalkChart B S hS hX hdec))) := by
    intro r
    refine Eq.trans (congrArg (fun z ↦ r • z)
      (Z.genericStalkCoefficient_spec B S hS hX hdec L hL t)) ?_
    refine Eq.trans (toMeromorphicSectionSheaf_smul B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2 _
      (Z.genericStalkChart B S hS hX hdec) r _).symm ?_
    exact congrArg (toMeromorphicSectionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 _ (Z.genericStalkChart B S hS hX hdec))
      (meromorphicSectionModule_smul_tmul B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2 _ (Z.genericStalkChart B S hS hX hdec) _ r
        ((meromorphicChartRingEquiv B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          (Z.genericStalkChart B S hS hX hdec)).symm
            (Z.genericStalkCoefficient B S hS hX hdec L hL t)) _ rfl)
  set E := meromorphicChartRingEquiv B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec) with hE
  intro r r' hrr'
  have hmul : E.symm r * E.symm (Z.genericStalkCoefficient B S hS hX hdec L hL t) =
      E.symm r' * E.symm (Z.genericStalkCoefficient B S hS hX hdec L hL t) := by
    rw [← map_mul E.symm, ← map_mul E.symm]
    exact congrArg E.symm hrr'
  refine E.symm.injective (h ((((key (E.symm r)).trans ?_).trans (key (E.symm r')).symm)))
  refine congrArg (fun z ↦ toMeromorphicSectionSheaf B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2 _
      (Z.genericStalkChart B S hS hX hdec)
      (z ⊗ₜ[chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkChart B S hS hX hdec)]
        Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
          (𝟙 (Z.genericStalkChart B S hS hX hdec)) :
        (meromorphicSectionModule B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)).obj
            (op (Z.genericStalkChart B S hS hX hdec)))) ?_
  exact hmul

/-- The coefficient of a regular meromorphic section is a nonzerodivisor of the meromorphic
functions on `Spec(𝒪_{U, u})`. -/
theorem PrimeDivisor.mem_nonZeroDivisors_genericStalkCoefficient
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) :
    Z.genericStalkCoefficient B S hS hX hdec L hL t ∈
      ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
          (op (Z.genericStalkChart B S hS hX hdec)))⁰ := by
  have hinj := Z.injective_mul_genericStalkCoefficient B S hS hX hdec L hL t ht
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx ↦ hinj ?_, fun x hx ↦ hinj ?_⟩
  · exact (((mul_comm x _).trans hx).trans (zero_mul _).symm)
  · exact (hx.trans (zero_mul _).symm)

include hInt hN in
/-- **The coefficient of a regular meromorphic section is a unit.** It is a nonzerodivisor of a
total ring of fractions, and a nonzerodivisor of a total ring of fractions is a unit. -/
theorem PrimeDivisor.isUnit_genericStalkCoefficient
    (t : MeromorphicSection.{u, u} B S hS X hX L)
    (ht : IsRegularMeromorphicSection.{u, u} B S hS X hX L t) :
    IsUnit (Z.genericStalkCoefficient B S hS hX hdec L hL t) := by
  have := Z.isFractionRing_genericStalkMeromorphic B S hS hX hdec hInt hN
  have h := Z.mem_nonZeroDivisors_genericStalkCoefficient B S hS hX hdec L hL t ht
  rwa [IsFractionRing.nonZeroDivisors_eq_isUnit
    ((structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec)))
    ((meromorphicFunctionSheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2).obj.obj
        (op (Z.genericStalkChart B S hS hX hdec)))] at h

end AlgebraicGeometry.Space

end
