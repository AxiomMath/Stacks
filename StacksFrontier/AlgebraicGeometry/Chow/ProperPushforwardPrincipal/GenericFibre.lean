module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.NormalizationDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocusSpreadOut
public import StacksCore.Tactic.StacksAttribute

/-!
# The generic fibre of a dominant morphism of integral schemes

Let `π : V ⟶ T` be a dominant morphism of integral schemes and let `η` be the generic point of
`T`. The generic fibre `V_η = V ×_T Spec κ(η)` is integral, the inclusion `V_η ⟶ V` is dominant,
and that inclusion is an isomorphism on every local ring and preserves codimension.

For a proper dominant morphism `π : V ⟶ T` of integral schemes with `dim_δ(V) = dim_δ(T) + 1` and
a nonzero rational function `f` on `V`, it follows that

  `∑_{x ↦ η} ord_x(f) · [κ(x) : κ(η)] = 0`,

and hence that proper pushforward of cycles respects rational equivalence.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.genericFiberPoint`: the point of the generic fibre lying under
  the generic point of the source.

## Main results

* `AlgebraicGeometry.isIso_stalkMap_of_flat_of_surjectiveOnStalks`: a flat morphism with
  surjective stalk maps is an isomorphism on local rings.
* `AlgebraicGeometry.isIso_stalkMap_fiberι_genericPoint'`,
  `AlgebraicGeometry.coheight_fiberι_genericPoint`: the inclusion of the generic fibre is an
  isomorphism on local rings and preserves codimension.
* `AlgebraicGeometry.isIntegral_fiber_genericPoint`,
  `AlgebraicGeometry.isDominant_fiberι_genericPoint`: the generic fibre of a dominant morphism
  of integral schemes is integral, and its inclusion is dominant.
* `Stacks.Chow.residueTrdeg_of_surjective_residueFieldMap_comp`,
  `Stacks.Chow.residueTrdeg_comp_of_surjective_residueFieldMap`: the transcendence degree of a
  residue-field extension does not change along a factor that is surjective on residue fields.
* `Stacks.Chow.genericFibreDegreeVanishes`: the degree of a principal divisor along the generic
  fibre of a proper dominant morphism of integral schemes of relative dimension one vanishes.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`: proper
  pushforward of cycles carries cycles rationally equivalent to zero to cycles rationally
  equivalent to zero.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Flat morphisms that are surjective on local rings -/

/-- A flat surjective local homomorphism of local rings is bijective. -/
theorem bijective_of_flat_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (hflat : φ.Flat)
    (hsurj : Function.Surjective φ) : Function.Bijective φ := by
  let _ : Algebra R S := φ.toAlgebra
  have : Module.Flat R S := hflat
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom φ›
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := R) (B := S)
  exact ⟨FaithfulSMul.algebraMap_injective R S, hsurj⟩

/-- A flat morphism that is surjective on local rings is an isomorphism on local rings. -/
theorem isIso_stalkMap_of_flat_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [SurjectiveOnStalks f] (x : X) : IsIso (f.stalkMap x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_of_flat_of_surjective (f.stalkMap x).hom (Flat.stalkMap f x)
      (SurjectiveOnStalks.stalkMap_surjective f x))

/-! ### The local rings of a generic fibre -/

variable {X Y : Scheme.{u}}

/-- For an integral scheme `Y`, the morphism to `Y` from the spectrum of the residue field at its
generic point is flat. -/
instance flat_fromSpecResidueField_genericPoint (Y : Scheme.{u}) [IsIntegral Y] :
    Flat (Y.fromSpecResidueField (genericPoint Y)) := by
  refine Flat.of_stalkMap _ fun x ↦ RingHom.Flat.of_isField ?_ _
  rw [Scheme.fromSpecResidueField_apply]
  exact Field.toIsField Y.functionField

/-- The inclusion of the fibre over the generic point of an integral scheme is flat. -/
instance flat_fiberι_genericPoint (f : X ⟶ Y) [IsIntegral Y] :
    Flat (f.fiberι (genericPoint Y)) :=
  inferInstanceAs (Flat (pullback.fst f (Y.fromSpecResidueField (genericPoint Y))))

/-- The inclusion of the generic fibre is an isomorphism on the local ring at every point of the
generic fibre. -/
theorem isIso_stalkMap_fiberι_genericPoint' (f : X ⟶ Y) [IsIntegral Y]
    (x : f.fiber (genericPoint Y)) : IsIso ((f.fiberι (genericPoint Y)).stalkMap x) :=
  isIso_stalkMap_of_flat_of_surjectiveOnStalks (f.fiberι (genericPoint Y)) x

/-- The inclusion of the generic fibre preserves the codimension of points. -/
theorem coheight_fiberι_genericPoint (f : X ⟶ Y) [IsIntegral Y]
    (x : f.fiber (genericPoint Y)) :
    coheight ((f.fiberι (genericPoint Y)).base x) = coheight x := by
  have _ := isIso_stalkMap_fiberι_genericPoint' f x
  have h : ((coheight ((f.fiberι (genericPoint Y)).base x) : ℕ∞) : WithBot ℕ∞) =
      ((coheight x : ℕ∞) : WithBot ℕ∞) := by
    rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
    exact Order.krullDim_eq_of_orderIso (PrimeSpectrum.comapEquiv
      (asIso (Scheme.Hom.stalkMap (f.fiberι (genericPoint Y)) x)).commRingCatIsoToRingEquiv)
  exact_mod_cast h

/-! ### The generic fibre of a dominant morphism of integral schemes -/

/-- The point of the generic fibre of a dominant morphism of integral schemes that lies under the
generic point of the source. -/
def Scheme.Hom.genericFiberPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f.fiber (genericPoint Y) :=
  (f.fiberHomeo (genericPoint Y)).symm
    ⟨genericPoint X, ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)⟩

/-- The inclusion of the generic fibre maps `AlgebraicGeometry.Scheme.Hom.genericFiberPoint` to
the generic point of the source. -/
@[simp]
theorem Scheme.Hom.fiberι_genericFiberPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] :
    (f.fiberι (genericPoint Y)).base f.genericFiberPoint = genericPoint X :=
  f.fiberι_fiberHomeo_symm _ _

/-- Every point of the generic fibre is a specialization of
`AlgebraicGeometry.Scheme.Hom.genericFiberPoint`. -/
theorem specializes_genericFiberPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (z : f.fiber (genericPoint Y)) : f.genericFiberPoint ⤳ z := by
  refine ((f.fiberι (genericPoint Y)).isEmbedding.isInducing.specializes_iff).mp ?_
  rw [Scheme.Hom.fiberι_genericFiberPoint]
  exact genericPoint_specializes _

/-- The generic fibre of a dominant morphism of integral schemes is irreducible. -/
instance irreducibleSpace_fiber_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] : IrreducibleSpace (f.fiber (genericPoint Y)) := by
  refine { toNonempty := ⟨f.genericFiberPoint⟩, toPreirreducibleSpace := ⟨?_⟩ }
  rintro u v hu hv ⟨a, -, hau⟩ ⟨b, -, hbv⟩
  exact ⟨f.genericFiberPoint, Set.mem_univ _,
    (specializes_genericFiberPoint f a).mem_open hu hau,
    (specializes_genericFiberPoint f b).mem_open hv hbv⟩

/-- The generic fibre of a morphism from a reduced scheme to an integral scheme is reduced. -/
instance isReduced_fiber_genericPoint (f : X ⟶ Y) [IsReduced X] [IsIntegral Y] :
    IsReduced (f.fiber (genericPoint Y)) := by
  have hst : ∀ z : f.fiber (genericPoint Y),
      _root_.IsReduced ((f.fiber (genericPoint Y)).presheaf.stalk z) := by
    intro z
    have _ := isIso_stalkMap_fiberι_genericPoint' f z
    set e := (asIso (Scheme.Hom.stalkMap (f.fiberι (genericPoint Y)) z)).commRingCatIsoToRingEquiv
    refine ⟨fun x hx ↦ ?_⟩
    have h0 := _root_.IsReduced.eq_zero (e.symm x) (hx.map e.symm.toRingHom)
    simpa using congrArg e h0
  exact @isReduced_of_isReduced_stalk _ hst

/-- The generic fibre of a dominant morphism of integral schemes is integral. -/
instance isIntegral_fiber_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    IsIntegral (f.fiber (genericPoint Y)) :=
  @isIntegral_of_irreducibleSpace_of_isReduced _ (isReduced_fiber_genericPoint f) inferInstance

/-- The inclusion of the generic fibre of a dominant morphism of integral schemes is dominant. -/
instance isDominant_fiberι_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    IsDominant (f.fiberι (genericPoint Y)) := by
  refine ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_forall fun x ↦ ?_)⟩
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (f.fiberι (genericPoint Y)).base := by
    rintro y rfl
    exact ⟨f.genericFiberPoint, Scheme.Hom.fiberι_genericFiberPoint f⟩
  have hmono := closure_mono hsub
  rw [genericPoint_closure X] at hmono
  exact hmono (Set.mem_univ x)

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### Transcendence degrees through a factor that is bijective on residue fields -/

/-- The residue transcendence degree is additive along a composite (Stacks 030H for the tower
`κ(p (i x)) ⊆ κ(i x) ⊆ κ(x)`). -/
private theorem residueTrdeg_comp_eq_add {X' X Y : Scheme.{u}} (i : X' ⟶ X) (p : X ⟶ Y)
    (x : X') : residueTrdeg (i ≫ p) x = residueTrdeg p (i.base x) + residueTrdeg i x := by
  let _ : Algebra (Y.residueField (p.base (i.base x))) (X.residueField (i.base x)) :=
    (p.residueFieldMap (i.base x)).hom.toAlgebra
  let _ : Algebra (X.residueField (i.base x)) (X'.residueField x) :=
    (i.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (Y.residueField (p.base (i.base x))) (X'.residueField x) :=
    ((i ≫ p).residueFieldMap x).hom.toAlgebra
  let _ : IsScalarTower (Y.residueField (p.base (i.base x))) (X.residueField (i.base x))
      (X'.residueField x) := IsScalarTower.of_algebraMap_eq fun a ↦
    congrArg (fun φ : Y.residueField (p.base (i.base x)) →+* X'.residueField x ↦ φ a)
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp i p x))
  have _ : FaithfulSMul (Y.residueField (p.base (i.base x))) (X.residueField (i.base x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have _ : FaithfulSMul (X.residueField (i.base x)) (X'.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  exact (trdeg_add_eq (Y.residueField (p.base (i.base x))) (X.residueField (i.base x))
    (A := X'.residueField x)).symm

/-- A morphism that is surjective on the residue field at `x` has residue transcendence degree
zero there. -/
private theorem residueTrdeg_eq_zero_of_surjective_residueFieldMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (hf : Function.Surjective (f.residueFieldMap x).hom) :
    residueTrdeg f x = 0 :=
  let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  trdeg_zero_of_surjective_algebraMap _ _ hf

/-- If `i` is surjective on the residue field at `x`, then the residue-field extension of `i ≫ p`
at `x` has the same transcendence degree as that of `p` at `i.base x`. -/
theorem residueTrdeg_of_surjective_residueFieldMap_comp {X' X Y : Scheme.{u}} (i : X' ⟶ X)
    (p : X ⟶ Y) (x : X') (hi : Function.Surjective (i.residueFieldMap x).hom) :
    residueTrdeg (i ≫ p) x = residueTrdeg p (i.base x) := by
  rw [residueTrdeg_comp_eq_add, residueTrdeg_eq_zero_of_surjective_residueFieldMap i x hi, add_zero]

/-- If `j` is surjective on the residue field at `p.base x`, then the residue-field extension of
`p ≫ j` at `x` has the same transcendence degree as that of `p` at `x`. -/
theorem residueTrdeg_comp_of_surjective_residueFieldMap {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (j : Y ⟶ Z) (x : X) (hj : Function.Surjective (j.residueFieldMap (p.base x)).hom) :
    residueTrdeg (p ≫ j) x = residueTrdeg p x := by
  rw [residueTrdeg_comp_eq_add, residueTrdeg_eq_zero_of_surjective_residueFieldMap j (p.base x) hj,
    zero_add]

/-- A morphism that is surjective on stalks is bijective on residue fields. -/
private theorem bijective_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Bijective (f.residueFieldMap x).hom :=
  have := isIso_residueFieldMap_of_surjectiveOnStalks f x
  ConcreteCategory.bijective_of_isIso _

/-! ### The degree of a principal divisor on a generic fibre -/

/-- For a proper dominant morphism `π : V ⟶ T` of integral schemes locally of finite type over
the base with `dim_δ(V) = n` and `dim_δ(T) = n - 1`, and for a nonzero rational function `f` on
`V`,

  `∑_{x ↦ η} ord_x(f) · [κ(x) : κ(η)] = 0`

where `η` is the generic point of `T`. -/
theorem genericFibreDegreeVanishes : GenericFibreDegreeVanishes.{u} := by
  intro C V T sT hsT π hπ hπd hVi hTi hVN n hdimV hdimT f hf
  set η : T := genericPoint T
  set W : Scheme.{u} := π.fiber η
  set ι : W ⟶ V := π.fiberι η
  set c : W ⟶ AlgebraicGeometry.Spec (.of (T.residueField η)) :=
    π.fiberToSpecResidueField η
  have _ : IsProper c := inferInstanceAs (IsProper (pullback.snd π (T.fromSpecResidueField η)))
  have _ : IsIntegral W := inferInstanceAs (IsIntegral (π.fiber (genericPoint T)))
  have _ : IsDominant ι := inferInstanceAs (IsDominant (π.fiberι (genericPoint T)))
  have _ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian c
  have hstalk : ∀ z : W, IsIso (ι.stalkMap z) := fun z ↦
    isIso_stalkMap_fiberι_genericPoint' π z
  have hres : ∀ z : W, Function.Bijective (ι.residueFieldMap z).hom :=
    bijective_residueFieldMap_of_surjectiveOnStalks ι
  have hco : ∀ z : W, coheight (ι.base z) = coheight z := fun z ↦
    coheight_fiberι_genericPoint π z
  have hgenι : ι.base (genericPoint W) = genericPoint V :=
    ((tfae_isDominant_of_isIntegral ι).out 1 2).mp (inferInstance : IsDominant ι)
  have hgenπ : π.base (genericPoint V) = η :=
    ((tfae_isDominant_of_isIntegral π).out 1 2).mp (inferInstance : IsDominant π)
  have hVgen : relativeDimension C.dimensionFunction (π ≫ sT) (genericPoint V) = n :=
    WithBotTop.coe_injective
      ((schemeDeltaDimension_eq_genericPoint C (π ≫ sT)).symm.trans hdimV)
  have hTgen : relativeDimension C.dimensionFunction sT η = n - 1 :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sT).symm.trans hdimT)
  have hadd := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sT π (genericPoint V)
  rw [hVgen, hgenπ, hTgen] at hadd
  have hr : Cardinal.toNat (residueTrdeg π (genericPoint V)) = 1 := by omega
  have hfrom : ∀ z : W, Function.Bijective
      ((T.fromSpecResidueField η).residueFieldMap (c.base z)).hom := fun z ↦
    bijective_residueFieldMap_of_surjectiveOnStalks _ _
  have hrc : residueTrdeg c (genericPoint W) = residueTrdeg π (genericPoint V) := by
    rw [← residueTrdeg_comp_of_surjective_residueFieldMap c (T.fromSpecResidueField η)
      (genericPoint W) (hfrom _).2,
      show c ≫ T.fromSpecResidueField η = ι ≫ π from (π.fiber_fac η).symm,
      residueTrdeg_of_surjective_residueFieldMap_comp ι π (genericPoint W)
        (hres (genericPoint W)).2, hgenι]
  have hrelc : relativeDimension (fieldChowSituation (T.residueField η)).dimensionFunction c
      (genericPoint W) = 1 := by
    change (fieldChowSituation (T.residueField η)).dimensionFunction (c.base (genericPoint W)) +
      (Cardinal.toNat (residueTrdeg c (genericPoint W)) : ℤ) = 1
    rw [fieldChowSituation_dimensionFunction_eq_zero, hrc, hr]
    norm_num
  have hgenW : IsGenericPoint (genericPoint W) (Set.univ : Set W) :=
    (IrreducibleSpace.isIrreducible_univ W).isGenericPoint_genericPoint isClosed_univ
  have hdimW : topologicalKrullDim W = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_relativeDimension_toNat
      (fieldChowSituation (T.residueField η)) (fun _ _ ↦ rfl) c (𝟙 W) (genericPoint W) hgenW,
      show ((𝟙 W) : W ⟶ W).base (genericPoint W) = genericPoint W from rfl, hrelc]
    simp
  let _ : W.Over (AlgebraicGeometry.Spec (.of (T.residueField η))) := ⟨c⟩
  have hdown : (W ↘ AlgebraicGeometry.Spec (.of (T.residueField η))) = c := rfl
  have _ : IsVariety (T.residueField η)
      (W ↘ AlgebraicGeometry.Spec (.of (T.residueField η))) := by
    rw [hdown]; exact { }
  have _ : IsCurve (T.residueField η)
      (W ↘ AlgebraicGeometry.Spec (.of (T.residueField η))) :=
    { toIsVariety := inferInstance, topologicalKrullDim_eq_one := hdimW }
  have _ : IsProper (W ↘ AlgebraicGeometry.Spec (.of (T.residueField η))) := by
    rw [hdown]; infer_instance
  set g : W.functionField := dominantFunctionFieldMap ι f with hg
  have hgne : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero_iff _ (RingHom.injective (dominantFunctionFieldMap ι))).2 hf
  have hzero : (∑ᶠ z : W, W.ord g z * (c.residueDegree z : ℤ)) = 0 :=
    principalDivisorDegree_eq_zero (T.residueField η) W g hgne
  have hdeg : ∀ z : W, c.residueDegree z = π.residueDegree (ι.base z) := by
    intro z
    rw [← residueDegree_comp_of_bijective_residueFieldMap c (T.fromSpecResidueField η) z (hfrom z),
      show c ≫ T.fromSpecResidueField η = ι ≫ π from (π.fiber_fac η).symm,
      residueDegree_of_bijective_residueFieldMap_comp ι π z (hres z)]
  have hordz : ∀ z : W, W.ord g z = V.ord f (ι.base z) := fun z ↦
    ord_dominantFunctionFieldMap_of_isIso_stalkMap ι (hstalk (genericPoint W)) z (hstalk z)
      (hco z) f
  rw [show π.base ⁻¹' {η} = Set.range ι.base from (π.range_fiberι η).symm,
    finsum_mem_range (ι.isEmbedding.injective)]
  refine Eq.trans (finsum_congr fun z ↦ ?_) hzero
  rw [← hordz z, hdeg z]

/-! ### Proper pushforward and rational equivalence -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)

include hp

/-- Proper pushforward of `k`-cycles along a proper morphism over the base carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero. -/
@[stacks 02S2 "pushforward kills rational equivalence"]
theorem properPushforwardFactorsThroughRationalEquivalence_of_isProper (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k :=
  properPushforwardFactorsThroughRationalEquivalence_of_genericFibreDegreeVanishes C sX sY p hp
    genericFibreDegreeVanishes.{u} k

end Stacks.Chow

end
