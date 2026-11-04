module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Length.RingEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# The action on cycles is compatible with flat base change and with flat pullback

Let `C = (S, δ)` be a base situation for Chow homology, let `f : X ⟶ Y` be a morphism of schemes
locally of finite type over `S`, let `α` be a family of `r`-cycles on the fibres of `X / Y` and
let `β ∈ Z_e(Y)`. The action `α ∩ β ∈ Z_{r + e}(X)` is `Stacks.Chow.cap`. This file proves the
two compatibilities of Tag 0H68.

For flat base change: in the situation of Tag 0FVG, with `Y' = Y ×_S S'`, let `α'` be the base
change of `α` along `Y' ⟶ Y` and `β' = g^*β ∈ Z_{e + c}(Y')` the base change of `β`. Then
`α' ∩ β'` is the base change of `α ∩ β`, under the canonical identification of `X ×_Y Y'` with
`X' = X ×_S S'`.

For flat pullback: if `g : Y' ⟶ Y` is flat, locally of finite type and of relative dimension
`c`, if `α'` is the base change of `α` along `g` and `β'` the flat pullback of `β`, then
`α' ∩ β'` is the flat pullback of `α ∩ β` along `X ×_Y Y' ⟶ X`.

## Main results

* `Stacks.Chow.cap_baseChange` — compatibility of `α ∩ β` with flat base change.
* `Stacks.Chow.cap_flatPullback` — compatibility of `α ∩ β` with flat pullback.
* `Stacks.Chow.flatPullbackWeight_eq_fiberStalkLength` — the multiplicity entering all three
  pullback operations is the length of the local ring of the scheme-theoretic fibre.
* `Stacks.Chow.length_stalk_fiber_mul_restrictedFiberMap` — that length is multiplicative in a
  cartesian square.

## Implementation notes

Every notion the statement compares already exists and is reused rather than redefined: the
action is `Stacks.Chow.cap`, the base change of a family of cycles on fibres is
`Stacks.Chow.baseChangeFamily`, the base change of a cycle along a change of base scheme is
`Stacks.Chow.baseChangeCyclePullback`, and flat pullback of a cycle is
`Stacks.Chow.flatPullback`.

The proof identifies the multiplicity occurring in each of the three pullback operations with
the length of the local ring of a scheme-theoretic fibre: the multiplicity is a coefficient of
the fundamental cycle of the inverse image of the reduced closure of a point, and the local ring
of that inverse image is the local ring of the fibre, both being the quotient of the local ring
upstairs by the extended maximal ideal of the local ring downstairs. Those lengths are
multiplicative in a cartesian square, which is the content of the lemma; the remaining work is
the dimension bookkeeping that decides when a multiplicity is nonzero, and it is done with Tag
02FX and both parts of Tag 02FY.

Both halves are stated with the canonical pullbacks, so no scheme is chosen. In the
flat-pullback half this puts both sides on `X ×_Y Y'`; the two δ-dimension indices
`r + (e + c)` and `(r + e) + c` are equal integers but not syntactically equal, so the two
sides are compared inside the ambient group of all cycles, of which the groups `Z_k(-)` are
subgroups. In the base-change half the family side lives on `X ×_Y (Y ×_S S')` and the cycle
side on `X ×_S S'`; `CategoryTheory.Limits.pullbackRightPullbackFstIso` is the canonical
isomorphism between them over `X`, and the equality of cycles is the equality of their
coefficients along it. Since a cycle is an integer-valued function with locally finite support
on the points of the scheme and the comparison is an isomorphism, that coefficient identity is
the asserted equality of cycles.

## References

* [Stacks Project, Tag 0H68](https://stacks.math.columbia.edu/tag/0H68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### Lengths of local rings of fibres -/

/-- The length of the local ring of a scheme at a point, over itself. -/
private abbrev stalkLength (X : Scheme.{u}) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)

/-- The length of the local ring of the scheme-theoretic fibre of `f` through `x` at the point
of that fibre determined by `x`. -/
private abbrev fiberLength {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ∞ :=
  stalkLength (f.fiber (f x)) (f.asFiber x)

/-- At a point which is not the generic point of an irreducible component the local ring has
infinite length: a finite length would make it artinian, hence of Krull dimension zero, and a
point of coheight zero is maximal for specialization. -/
private theorem stalkLength_eq_top_of_notMem_genericPoints {X : Scheme.{u}} (x : X)
    (hx : x ∉ genericPoints X) : stalkLength X x = ⊤ := by
  by_contra h
  have hfin := Module.length_ne_top_iff.mp h
  have : IsArtinianRing (X.presheaf.stalk x) := (isArtinianRing_iff_isFiniteLength _).mpr hfin
  have hdim := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (X.presheaf.stalk x))
  rw [ringKrullDim_stalk_eq_coheight] at hdim
  have hc : Order.coheight x = 0 := le_antisymm (by exact_mod_cast hdim) zero_le
  exact hx (mem_genericPoints_of_isMax (Order.coheight_eq_zero.mp hc))

/-- The multiplicity of an irreducible component of a closed subscheme is the length of the
local ring of that subscheme at the generic point: the stalk map of a closed immersion is
surjective, so the lengths over the two local rings agree. -/
private theorem componentMultiplicity_eq_stalkLength {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : genericPoints Z) :
    componentMultiplicity i z = ((stalkLength Z z.1).toNat : ℤ) := by
  let _ : Module (X.presheaf.stalk (i z.1)) (Z.presheaf.stalk z.1) :=
    Module.compHom _ (i.stalkMap z.1).hom
  let _ : Algebra (X.presheaf.stalk (i z.1)) (Z.presheaf.stalk z.1) :=
    (i.stalkMap z.1).hom.toAlgebra
  unfold componentMultiplicity
  congr 2
  exact Module.length_eq_of_surjective (M := Z.presheaf.stalk z.1) (i.stalkMap_surjective z.1)

/-- The coefficient of the fundamental cycle of a closed subscheme at the image of a point of
that subscheme of the prescribed relative dimension is the length of the local ring of the
subscheme there — including when the point is not a generic point, in which case both sides
vanish, the length being infinite. -/
private theorem closedSubschemeCycleCoeff_eq_stalkLength (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ) (z : Z)
    (hdim : relativeDimension C.dimensionFunction sX (i z) = k) :
    closedSubschemeCycleCoeff C sX i k (i z) = ((stalkLength Z z).toNat : ℤ) := by
  classical
  by_cases hz : z ∈ genericPoints Z
  · have h := cycleAssociatedToClosedSubscheme_apply C sX i k ⟨z, hz⟩ hdim
    change closedSubschemeCycleCoeff C sX i k (i z) = _ at h
    rw [h, componentMultiplicity_eq_stalkLength]
  · rw [stalkLength_eq_top_of_notMem_genericPoints z hz]
    have hnone : ¬ ∃ ξ : genericPoints Z,
        i ξ.1 = i z ∧ relativeDimension C.dimensionFunction sX (i z) = k := by
      rintro ⟨ξ, hξ, -⟩
      exact hz (i.isClosedEmbedding.injective hξ ▸ ξ.2)
    simp [closedSubschemeCycleCoeff, hnone]

/-- A point lies on the scheme-theoretic inverse image of the reduced closure of its image. -/
private theorem mem_support_comap_integralComponentAt {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    x ∈ ((integralComponentAt (g x)).comap g).support := by
  rw [Scheme.IdealSheafData.support_comap]
  change g x ∈ ((integralComponentAt (g x)).support : Set Y)
  rw [coe_support_integralComponentAt]
  exact subset_closure (Set.mem_singleton _)

/-- The local ring at a point of the scheme-theoretic inverse image of a closed subscheme whose
ideal sheaf has the maximal ideal as its stalk below is the local ring of the scheme-theoretic
fibre: both are the quotient of `𝒪_{X,x}` by the ideal generated by the maximal ideal of
`𝒪_{Y,g x}`. -/
private theorem stalkLength_subscheme_comap {X Y : Scheme.{u}} (g : X ⟶ Y)
    (I : Y.IdealSheafData) (ξ : (I.comap g).subscheme)
    (hI : AlgebraicGeometry.IdealSheafData.stalk I (g ((I.comap g).subschemeι ξ)) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (g ((I.comap g).subschemeι ξ)))) :
    stalkLength (I.comap g).subscheme ξ =
      fiberLength g ((I.comap g).subschemeι ξ) := by
  have hker : RingHom.ker (((I.comap g).subschemeι.stalkMap ξ).hom) =
      Ideal.map (g.stalkMap ((I.comap g).subschemeι ξ)).hom
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g ((I.comap g).subschemeι ξ)))) := by
    rw [AlgebraicGeometry.IdealSheafData.ker_stalkMap_subschemeι_eq_stalk,
      AlgebraicGeometry.IdealSheafData.stalk_comap, hI]
  have e : ((X.presheaf.stalk ((I.comap g).subschemeι ξ)) ⧸
      RingHom.ker (((I.comap g).subschemeι.stalkMap ξ).hom)) ≃+*
      ((I.comap g).subscheme.presheaf.stalk ξ) :=
    RingHom.quotientKerEquivOfSurjective ((I.comap g).subschemeι.stalkMap_surjective ξ)
  rw [hker] at e
  exact Module.length_eq_of_ringEquiv
    (e.symm.trans (quotientStalkEquivFiberStalk g ((I.comap g).subschemeι ξ)))

/-- **Stacks 02RB, as a length.** The flat pullback multiplicity at a point of the prescribed
relative dimension is the length of the local ring of the scheme-theoretic fibre through that
point, and it vanishes off that relative dimension. -/
theorem flatPullbackWeight_eq_fiberStalkLength (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (g : X ⟶ Y) (k : ℤ) (x : X) :
    flatPullbackWeight C sX g k x =
      if relativeDimension C.dimensionFunction sX x = k then
        ((Module.length ((g.fiber (g x)).presheaf.stalk (g.asFiber x))
          ((g.fiber (g x)).presheaf.stalk (g.asFiber x))).toNat : ℤ)
      else 0 := by
  classical
  split_ifs with hdim
  · let ξ : ((integralComponentAt (g x)).comap g).subscheme :=
      ⟨x, mem_support_comap_integralComponentAt g x⟩
    have hξ : ((integralComponentAt (g x)).comap g).subschemeι ξ = x := rfl
    have hlen : stalkLength ((integralComponentAt (g x)).comap g).subscheme ξ =
        fiberLength g x :=
      stalkLength_subscheme_comap g (integralComponentAt (g x)) ξ
        (idealSheafStalk_integralComponentAt_self (g x))
    have hcoeff := closedSubschemeCycleCoeff_eq_stalkLength C sX
      ((integralComponentAt (g x)).comap g).subschemeι k ξ hdim
    change closedSubschemeCycleCoeff C sX ((integralComponentAt (g x)).comap g).subschemeι k x =
      ((stalkLength ((integralComponentAt (g x)).comap g).subscheme ξ).toNat : ℤ) at hcoeff
    rw [hlen] at hcoeff
    exact hcoeff
  · exact flatPullbackWeight_eq_zero_of_relativeDimension_ne C sX g k x hdim

/-! ### Multiplicativity of the length of the local ring of a fibre -/

/-- **Stacks 02M1, read on local rings of schemes.** Along a flat morphism the length of the
local ring upstairs is the length of the local ring downstairs times the length of the local
ring of the fibre through the point. -/
private theorem stalkLength_eq_mul_fiberLength_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : X) :
    stalkLength X x = stalkLength Y (f x) * fiberLength f x := by
  let R := Y.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let _ : Algebra R A := (f.stalkMap x).hom.toAlgebra
  have _ : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have _ : Module.Flat R A := Flat.stalkMap f x
  have hq : Module.length A (A ⧸ extendedMaximalIdeal R A) = fiberLength f x := by
    rw [Module.length_eq_of_surjective (R := A ⧸ extendedMaximalIdeal R A) (S := A)
      (M := A ⧸ extendedMaximalIdeal R A) Ideal.Quotient.mk_surjective]
    exact Module.length_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)
  have h := length_baseChange_eq_length_mul_length_quotient R A R
  rwa [(Algebra.TensorProduct.rid R A A).toLinearEquiv.length_eq, hq, eq_comm] at h

/-- If the base ring maps onto a field `B` and the tensor product `A ⊗ B` maps to a
localization `C` of it by a map which is local on the left factor, then `C` is the quotient of
`A` by the ideal generated by the maximal ideal of the base: the tensor product is already
`A / 𝔪A` and the localization adds nothing because every element of the tensor product becomes
a unit. -/
private theorem tensor_localization_equiv_quotient
    (R A B C : Type*) [CommRing R] [IsLocalRing R] [CommRing A] [Field B]
    [CommRing C] [Algebra R A] [Algebra R B]
    (hB : Function.Surjective (algebraMap R B))
    (φ : A ⊗[R] B →+* C)
    [IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom)]
    (hφ : letI : Algebra (A ⊗[R] B) C := φ.toAlgebra
      ∃ M : Submonoid (A ⊗[R] B), IsLocalization M C) :
    Nonempty ((A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ≃+* C) := by
  let eB : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₐ[R] B :=
    (Ideal.quotientEquivAlgOfEq R
      (IsLocalRing.ker_eq_maximalIdeal (algebraMap R B) hB).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B) hB)
  let eT : (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ≃ₐ[A] A ⊗[R] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (IsLocalRing.maximalIdeal R)).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eB)
  have _ : IsLocalHom φ := ⟨fun t ht => by
    obtain ⟨a, rfl⟩ := Algebra.TensorProduct.includeLeft_surjective R A hB t
    exact (isUnit_of_map_unit (φ.comp Algebra.TensorProduct.includeLeftRingHom) a ht).map
      Algebra.TensorProduct.includeLeftRingHom⟩
  let _ : Algebra (A ⊗[R] B) C := φ.toAlgebra
  obtain ⟨M, _⟩ := hφ
  let eL : (A ⊗[R] B) ≃ₐ[A ⊗[R] B] C := IsLocalization.atUnits _ M fun t ht =>
    isUnit_of_map_unit φ t (IsLocalization.map_units C ⟨t, ht⟩)
  exact ⟨eT.toRingEquiv.trans eL.toRingEquiv⟩

/-- Every local ring of the spectrum of a residue field is a field: the space is a single point
and the scheme is reduced and irreducible. -/
private theorem isField_stalk_spec_residueField {W : Scheme.{u}} (w : W)
    (pt : ↥(Spec (W.residueField w))) :
    IsField ↥((Spec (W.residueField w)).presheaf.stalk pt) := by
  have hsub : ∀ c z : ↥(Spec (W.residueField w)), c = z := fun c z =>
    Subsingleton.elim (α := PrimeSpectrum _) c z
  have he : closure ({pt} : Set ↥(Spec (W.residueField w))) = Set.univ :=
    Set.eq_univ_of_forall fun z => (hsub pt z) ▸ subset_closure (Set.mem_singleton pt)
  refine isField_stalk_of_closure_mem_irreducibleComponents (Spec (W.residueField w)) pt
    ⟨isIrreducible_singleton.closure, fun t _ _ => ?_⟩
  rw [he]
  exact Set.subset_univ t

/-- The local ring of a fibre product along a morphism which is surjective on stalks and whose
source has a field as its local ring at the point is the local ring of the scheme-theoretic
fibre of the other leg. -/
private theorem stalkLength_pullback_fieldStalk {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    [SurjectiveOnStalks g] (p : (pullback f g : Scheme.{u}))
    (hT : IsField ↥(T.presheaf.stalk ((pullback.snd f g).base p))) :
    stalkLength (pullback f g : Scheme.{u}) p = fiberLength f ((pullback.fst f g).base p) := by
  let x := (pullback.fst f g).base p
  let b := (pullback.snd f g).base p
  let h : (pullback.fst f g ≫ f).base p = (pullback.snd f g ≫ g).base p :=
    congrArg (fun k : (pullback f g : Scheme.{u}) ⟶ Y => k.base p) pullback.condition
  let R := Y.presheaf.stalk ((pullback.fst f g ≫ f).base p)
  let A := X.presheaf.stalk x
  let B := T.presheaf.stalk b
  let D := (pullback f g : Scheme.{u}).presheaf.stalk p
  let _ : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra R B := ((eqToHom (congrArg Y.presheaf.stalk h)) ≫ g.stalkMap b).hom.toAlgebra
  let _ : Field B := hT.toField
  have _ : IsIso (eqToHom (congrArg Y.presheaf.stalk h)) :=
    inferInstanceAs (IsIso (eqToIso (congrArg Y.presheaf.stalk h)).hom)
  have hB : Function.Surjective (algebraMap R B) :=
    (g.stalkMap_surjective b).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg Y.presheaf.stalk h))).2
  obtain ⟨φ, hleft, -, hloc⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g p
  have _ : IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom) := by
    rw [hleft]
    infer_instance
  obtain ⟨e⟩ := tensor_localization_equiv_quotient R A B D hB φ hloc
  have hq : Module.length (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) = fiberLength f x :=
    Module.length_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)
  exact (Module.length_eq_of_ringEquiv e).symm.trans hq

/-- The same statement for an arbitrary cartesian square. -/
private theorem stalkLength_isPullback_fieldStalk {P X Y T : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y) [SurjectiveOnStalks g]
    (hsq : IsPullback a b f g) (p : P) (hT : IsField ↥(T.presheaf.stalk (b.base p))) :
    stalkLength P p = fiberLength f (a.base p) := by
  have he : stalkLength (pullback f g : Scheme.{u}) (hsq.isoPullback.hom.base p) =
      stalkLength P p :=
    Module.length_eq_of_ringEquiv
      (asIso (hsq.isoPullback.hom.stalkMap p)).commRingCatIsoToRingEquiv
  have hp : (pullback.fst f g).base (hsq.isoPullback.hom.base p) = a.base p :=
    congrArg (fun q : P ⟶ X => q.base p) hsq.isoPullback_hom_fst
  have hps : (pullback.snd f g).base (hsq.isoPullback.hom.base p) = b.base p :=
    congrArg (fun q : P ⟶ T => q.base p) hsq.isoPullback_hom_snd
  rw [← he, stalkLength_pullback_fieldStalk f g _ (hps ▸ hT), hp]

/-- **The multiplicativity of fibre lengths in a cartesian square.** In a fibre product diagram
the length of the local ring of the fibre of the left-hand vertical map is the length of the
local ring of the fibre of the right-hand vertical map, times the length of the local ring of
the fibre of the induced morphism of horizontal fibres. -/
theorem length_stalk_fiber_mul_restrictedFiberMap
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (fU : U ⟶ V)
    (j : U ⟶ X) (i : V ⟶ Y) (h : IsPullback j fU f i) (x : U) :
    Module.length ((j.fiber (j x)).presheaf.stalk (j.asFiber x))
        ((j.fiber (j x)).presheaf.stalk (j.asFiber x)) =
      Module.length ((i.fiber (i (fU x))).presheaf.stalk (i.asFiber (fU x)))
          ((i.fiber (i (fU x))).presheaf.stalk (i.asFiber (fU x))) *
        Module.length
          (((restrictedFiberMap f fU j i h.w (fU x)).fiber
            (restrictedFiberMap f fU j i h.w (fU x) (fU.asFiber x))).presheaf.stalk
              ((restrictedFiberMap f fU j i h.w (fU x)).asFiber (fU.asFiber x)))
          (((restrictedFiberMap f fU j i h.w (fU x)).fiber
            (restrictedFiberMap f fU j i h.w (fU x) (fU.asFiber x))).presheaf.stalk
              ((restrictedFiberMap f fU j i h.w (fU x)).asFiber (fU.asFiber x))) := by
  let y := fU x
  let n := restrictedFiberMap f fU j i h.w y
  let z := n (fU.asFiber x)
  let a := (f.fiber (i y)).fromSpecResidueField z
  let s := f.fiberToSpecResidueField (i y)
  let t := i.fiberToSpecResidueField (i y)
  let k := Spec.map (i.residueFieldMap y)
  have hn : IsPullback n (fU.fiberToSpecResidueField y) s k :=
    isPullback_fiberToSpecResidueField_of_isPullback h y
  let Q := pullback t (a ≫ s)
  let q₁ : Q ⟶ i.fiber (i y) := pullback.fst _ _
  let q₂ : Q ⟶ Spec ((f.fiber (i y)).residueField z) := pullback.snd _ _
  let b : n.fiber z ⟶ Spec (V.residueField y) :=
    n.fiberι z ≫ fU.fiberToSpecResidueField y
  have houter : IsPullback (n.fiberToSpecResidueField z) b (a ≫ s) k :=
    ((IsPullback.of_hasPullback n a).paste_horiz hn.flip).flip
  have hw : (b ≫ i.asFiberHom y) ≫ t = n.fiberToSpecResidueField z ≫ (a ≫ s) := by
    simpa only [t, k, Category.assoc, Scheme.Hom.asFiberHom_fiberToSpecResidueField]
      using houter.w.symm
  let q : n.fiber z ⟶ Q := pullback.lift (b ≫ i.asFiberHom y)
    (n.fiberToSpecResidueField z) hw
  have hq : IsPullback q b q₁ (i.asFiberHom y) :=
    .of_right (h₁₂ := q₂) (h₂₂ := t) (by simpa only [q, q₂, t, k, pullback.lift_snd,
        Scheme.Hom.asFiberHom_fiberToSpecResidueField] using houter)
      (pullback.lift_fst ..) (IsPullback.of_hasPullback t (a ≫ s)).flip
  have hab : (q₂ ≫ a ≫ f.fiberι (i y)) ≫ f = (q₁ ≫ i.fiberι (i y)) ≫ i := by
    simp only [Category.assoc, Scheme.Hom.fiber_fac]
    change q₂ ≫ a ≫ s ≫ Y.fromSpecResidueField (i y) =
      q₁ ≫ t ≫ Y.fromSpecResidueField (i y)
    simpa only [Category.assoc] using
      congrArg (· ≫ Y.fromSpecResidueField (i y)) (pullback.condition (f := t) (g := a ≫ s)).symm
  let v : Q ⟶ U := h.lift (q₂ ≫ a ≫ f.fiberι (i y)) (q₁ ≫ i.fiberι (i y)) hab
  have hv : IsPullback v q₂ j (a ≫ f.fiberι (i y)) := by
    apply IsPullback.of_right (h₁₂ := fU) (h₂₂ := f)
    · have H := (IsPullback.of_hasPullback t (a ≫ s)).paste_horiz
        (IsPullback.of_hasPullback i (Y.fromSpecResidueField (i y)))
      convert H using 1
      · exact h.lift_snd ..
      · simp only [Category.assoc, Scheme.Hom.fiber_fac]
        rfl
    · exact h.lift_fst ..
    · exact h.flip
  have hqv : q ≫ v = n.fiberι z ≫ fU.fiberι y := by
    apply h.hom_ext
    · simp only [Category.assoc, v, IsPullback.lift_fst]
      rw [← Category.assoc q q₂,
        show q ≫ q₂ = n.fiberToSpecResidueField z from pullback.lift_snd ..]
      rw [← Category.assoc, ← n.fiber_fac z, Category.assoc]
      exact congrArg (n.fiberι z ≫ ·) (restrictedFiberMap_fiberι f fU j i h.w y)
    · simp only [Category.assoc, v, IsPullback.lift_snd]
      rw [← Category.assoc q q₁, show q ≫ q₁ = b ≫ i.asFiberHom y from pullback.lift_fst ..]
      simp only [Category.assoc, Scheme.Hom.asFiberHom_fiberι]
      exact (Category.assoc ..).trans (congrArg (n.fiberι z ≫ ·) (fU.fiber_fac y).symm)
  have htflat : Flat (a ≫ s) := by
    apply Flat.of_stalkMap
    intro w
    apply RingHom.Flat.of_isField
    apply isField_stalk_of_closure_mem_irreducibleComponents
    have he : closure ({(a ≫ s) w} : Set (Spec (Y.residueField (i y)))) = Set.univ :=
      Set.eq_univ_of_forall fun c => (Subsingleton.elim ((a ≫ s) w) c) ▸
        subset_closure (Set.mem_singleton _)
    rw [he, irreducibleComponents_eq_singleton]
    exact Set.mem_singleton _
  have _ : Flat q₁ := inferInstanceAs (Flat (pullback.fst t (a ≫ s)))
  let p := n.asFiber (fU.asFiber x)
  have hp : v (q p) = x := by
    change (q ≫ v) p = x
    rw [hqv]
    change fU.fiberι y (n.fiberι (n (fU.asFiber x)) (n.asFiber (fU.asFiber x))) = x
    simp [y]
  have hp₁ : q₁ (q p) = i.asFiber y := by
    change (q ≫ q₁) p = _
    rw [show q ≫ q₁ = b ≫ i.asFiberHom y from pullback.lift_fst ..]
    simp
  have _ : IsPreimmersion a :=
    inferInstanceAs (IsPreimmersion ((f.fiber (i y)).fromSpecResidueField z))
  have _ : IsPreimmersion (a ≫ f.fiberι (i y)) := inferInstance
  have _ : IsPreimmersion (i.asFiberHom y) := inferInstance
  have hQ := stalkLength_isPullback_fieldStalk v q₂ j (a ≫ f.fiberι (i y)) hv (q p)
    (isField_stalk_spec_residueField z (q₂ (q p)))
  have hP := stalkLength_isPullback_fieldStalk q b q₁ (i.asFiberHom y) hq p
    (isField_stalk_spec_residueField y (b p))
  have hmul := stalkLength_eq_mul_fiberLength_of_flat q₁ (q p)
  change stalkLength Q (q p) = stalkLength (i.fiber (i y)) (q₁ (q p)) *
    fiberLength q₁ (q p) at hmul
  change stalkLength Q (q p) = fiberLength j (v (q p)) at hQ
  change stalkLength (n.fiber z) p = fiberLength q₁ (q p) at hP
  rw [← hP, hQ, hp, hp₁] at hmul
  exact hmul


/-! ### Dimension bookkeeping -/

/-- A local ring of finite length has Krull dimension zero: it is artinian. -/
private theorem ringKrullDim_stalk_eq_zero_of_stalkLength_ne_top (X : Scheme.{u}) (x : X)
    (hx : stalkLength X x ≠ ⊤) : ringKrullDim (X.presheaf.stalk x) = 0 := by
  have : IsArtinianRing (X.presheaf.stalk x) :=
    (isArtinianRing_iff_isFiniteLength _).mpr (Module.length_ne_top_iff.mp hx)
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- The morphism of fibres attached to a commutative square of the Chow vocabulary is the one of
the fibre-dimension vocabulary. -/
private theorem restrictedFiberMap_eq_fiberMap {X Y U V : Scheme.{u}} (f : X ⟶ Y) (fU : U ⟶ V)
    (j : U ⟶ X) (i : V ⟶ Y) (h : j ≫ f = fU ≫ i) (t : V) :
    restrictedFiberMap f fU j i h t = AlgebraicGeometry.fiberMap fU j i f h t := rfl

/-- The multiplicativity of fibre lengths in a cartesian square, read on natural numbers. -/
private theorem fiberLength_toNat_mul {X Y U V : Scheme.{u}} (f : X ⟶ Y) (fU : U ⟶ V)
    (j : U ⟶ X) (i : V ⟶ Y) (h : IsPullback j fU f i) (x : U) :
    (fiberLength j x).toNat =
      (fiberLength i (fU x)).toNat *
        (fiberLength (restrictedFiberMap f fU j i h.w (fU x)) (fU.asFiber x)).toNat := by
  have h0 : fiberLength j x =
      fiberLength i (fU x) *
        fiberLength (restrictedFiberMap f fU j i h.w (fU x)) (fU.asFiber x) :=
    length_stalk_fiber_mul_restrictedFiberMap f fU j i h x
  rw [h0, ENat.toNat_mul]

/-- **Stacks 0FVH, pointwise.** In the flat base-change situation, at a point of the base change
whose fibre has a local ring of finite nonzero length the two relative dimension functions
differ by the shift `c`. -/
private theorem relativeDimension_baseChange_eq (B : FlatBaseChangeSituation.{u})
    {X X' : Scheme.{u}} (s : X ⟶ B.base.S) [LocallyOfFiniteType s]
    (s' : X' ⟶ B.baseChange.S) (j : X' ⟶ X) (h : IsPullback j s' s B.g) (x : X')
    (hx : (fiberLength j x).toNat ≠ 0) :
    relativeDimension B.baseChange.dimensionFunction s' x =
      relativeDimension B.base.dimensionFunction s (j x) + B.c := by
  have hmul := fiberLength_toNat_mul s s' j B.g h x
  have hg : (fiberLength B.g (s' x)).toNat ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at hmul
    exact hx hmul
  have hn : (fiberLength (restrictedFiberMap s s' j B.g h.w (s' x)) (s'.asFiber x)).toNat ≠ 0 := by
    intro hn
    rw [hn, mul_zero] at hmul
    exact hx hmul
  have hgen : B.g.asFiber (s' x) ∈ genericPoints (B.g.fiber (B.g (s' x))) := by
    by_contra H
    refine hg ?_
    have := stalkLength_eq_top_of_notMem_genericPoints (B.g.asFiber (s' x)) H
    rw [show fiberLength B.g (s' x) = ⊤ from this]
    rfl
  have _ : QuasiSober (B.g ⁻¹' {B.g (s' x)} : Set B.baseChange.S) :=
    (B.g.fiberHomeo (B.g (s' x))).symm.isOpenEmbedding.quasiSober
  let sPt : (B.g ⁻¹' {B.g (s' x)} : Set B.baseChange.S) := ⟨s' x, rfl⟩
  have hsub : sPt ∈ genericPoints (B.g ⁻¹' {B.g (s' x)} : Set B.baseChange.S) := by
    have h1 := mem_genericPoints_of_generalizingMap
      (B.g.fiberHomeo (B.g (s' x))).isOpenEmbedding.generalizingMap hgen
    have h2 : (B.g.fiberHomeo (B.g (s' x))) (B.g.asFiber (s' x)) = sPt := by
      apply Subtype.ext
      simp [sPt, Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
    rwa [h2] at h1
  have hd := B.dimensionFunction_eq_add (B.g (s' x)) ⟨sPt, hsub⟩
  have hz : ringKrullDim
      (((AlgebraicGeometry.fiberMap s' j B.g s h.w (s' x)).fiber
          (AlgebraicGeometry.fiberMap s' j B.g s h.w (s' x) (s'.asFiber x))).presheaf.stalk
        ((AlgebraicGeometry.fiberMap s' j B.g s h.w (s' x)).asFiber (s'.asFiber x))) = 0 :=
    ringKrullDim_stalk_eq_zero_of_stalkLength_ne_top _ _ (fun H => hn (by
      rw [show fiberLength (restrictedFiberMap s s' j B.g h.w (s' x)) (s'.asFiber x) = ⊤ from H]
      rfl))
  have ht0 := AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_trdeg_eq h x
  rw [hz, zero_add] at ht0
  have ht : (Cardinal.toNat (letI := (s'.residueFieldMap x).hom.toAlgebra
        Algebra.trdeg (B.baseChange.S.residueField (s' x)) (X'.residueField x))) =
      Cardinal.toNat (letI := (s.residueFieldMap (j x)).hom.toAlgebra
        Algebra.trdeg (B.base.S.residueField (s (j x))) (X.residueField (j x))) := by
    simpa only [Cardinal.toNat_toENat] using congrArg ENat.toNat (WithBot.coe_injective ht0)
  have hp : s (j x) = B.g (s' x) := congrArg (fun q : X' ⟶ B.base.S => q x) h.w
  unfold relativeDimension
  dsimp only
  rw [ht, hd, ← hp]
  omega

/-- **Stacks 02JW along a flat morphism of relative dimension `c`.** At a point whose fibre has
a local ring of finite nonzero length, relative dimension grows by exactly `c`. -/
private theorem relativeDimension_comp_eq_of_relativeDimension (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ C.S) [LocallyOfFiniteType s] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (c : ℕ) (hf : AlgebraicGeometry.RelativeDimension f c) (x : X)
    (hx : (fiberLength f x).toNat ≠ 0) :
    letI : LocallyOfFiniteType (f ≫ s) := inferInstance
    relativeDimension C.dimensionFunction (f ≫ s) x =
      relativeDimension C.dimensionFunction s (f x) + (c : ℤ) := by
  have _ : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField (f x)))
    infer_instance
  obtain ⟨he, hd⟩ := hf (f x) ⟨f.asFiber x⟩
  have hdAt := AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional
    (Y.residueField (f x)) (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) he hd (f.asFiber x)
  have hz := ringKrullDim_stalk_eq_zero_of_stalkLength_ne_top (f.fiber (f x)) (f.asFiber x)
    (fun H => hx (by rw [show fiberLength f x = ⊤ from H]; rfl))
  have hformula :=
    AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f x
  dsimp only at hformula
  rw [hdAt, hz, zero_add] at hformula
  have ht : Cardinal.toNat (residueTrdeg f x) = c := by
    have h1 := (congrArg ENat.toNat (WithBot.coe_injective hformula)).symm
    simp only [Cardinal.toNat_toENat, ENat.toNat_natCast] at h1
    exact h1
  rw [relativeDimension_comp_eq_add_trdeg, ht]


/-! ### The three pullback operations as a coefficient times a fibre length -/

/-- A point carrying a nonzero coefficient of a `k`-cycle has relative dimension `k`. -/
private theorem relativeDimension_of_cycleGroup_apply_ne_zero (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ) (c : CycleGroup C sX k)
    (x : X) (hx : c.1 x ≠ 0) : relativeDimension C.dimensionFunction sX x = k :=
  (mem_cyclesOfDimension_iff_forall_point C sX k c.1).1 c.2 x hx

/-- A coefficient times a multiplicity which is only counted in the right relative dimension:
the condition is automatic when both factors are nonzero. -/
private theorem mul_ite_natCast_eq_mul {P : Prop} [Decidable P] (a : ℤ) (n : ℕ)
    (h : a ≠ 0 → n ≠ 0 → P) : a * (if P then (n : ℤ) else 0) = a * n := by
  by_cases ha : a = 0
  · rw [ha, zero_mul, zero_mul]
  by_cases hn : n = 0
  · simp [hn]
  rw [ite_eq_left (h ha hn)]

/-- **Stacks 02RB.** The coefficient of a flat pullback is the coefficient downstairs times the
length of the local ring of the fibre. -/
private theorem flatPullback_apply_eq_mul_fiberLength (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX) (c : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f c) (k : ℤ) (β : CycleGroup C sY k) (x : X) :
    (flatPullback C sX sY f hbase c hf k β).1 x = β.1 (f x) * ((fiberLength f x).toNat : ℤ) := by
  classical
  change flatPullbackCoeff C sX sY f c k β x = _
  unfold flatPullbackCoeff
  rw [flatPullbackWeight_eq_fiberStalkLength]
  refine mul_ite_natCast_eq_mul _ _ fun hβ hl => ?_
  have hd := relativeDimension_comp_eq_of_relativeDimension C sY f c hf x hl
  rw [hbase, relativeDimension_of_cycleGroup_apply_ne_zero C sY k β (f x) hβ] at hd
  exact hd

/-- **Stacks 0FVI.** The coefficient of the base change of a cycle along a change of the base
scheme is the coefficient downstairs times the length of the local ring of the fibre. -/
private theorem baseChangeCyclePullback_apply_eq_mul_fiberLength
    (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (s : X ⟶ B.base.S) [LocallyOfFiniteType s] (k : ℤ)
    (β : CycleGroup B.base s k) (x : (pullback s B.g : Scheme.{u})) :
    (baseChangeCyclePullback B s k β).1 x =
      β.1 (pullback.fst s B.g x) * ((fiberLength (pullback.fst s B.g) x).toNat : ℤ) := by
  classical
  change baseChangeCycleCoeff B s k β x = _
  unfold baseChangeCycleCoeff
  rw [flatPullbackWeight_eq_fiberStalkLength]
  refine mul_ite_natCast_eq_mul _ _ fun hβ hl => ?_
  have hd := relativeDimension_baseChange_eq B s (pullback.snd s B.g) (pullback.fst s B.g)
    (IsPullback.of_hasPullback s B.g) x hl
  rwa [relativeDimension_of_cycleGroup_apply_ne_zero B.base s k β _ hβ] at hd

/-- The coefficient of a family of cycles on fibres read at a point of the total space does not
depend on which fibre the point is viewed in. -/
private theorem family_apply_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {r : ℕ} (α : FamilyOfCycles f r) (y : Y) (x : f.fiber y) :
    (α y : AlgebraicCycle (f.fiber y) ℤ) x =
      (α (f (f.fiberι y x)) :
        AlgebraicCycle (f.fiber (f (f.fiberι y x))) ℤ) (f.asFiber (f.fiberι y x)) := by
  have hy : f (f.fiberι y x) = y := (f.fiberHomeo y x).2
  generalize hz : f.fiberι y x = z at *
  cases hy
  congr 1
  apply (f.fiberHomeo _).injective
  apply Subtype.ext
  simp only [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber, hz]

/-- The coefficient of a family of cycles on fibres at the image of a point under the morphism of
fibres attached to a square is the coefficient at the corresponding point of the total space. -/
private alias family_apply_restrictedFiberMap :=
  Stacks.Chow.familyOfCycles_restrictedFiberMap_asFiber

/-- **Stacks 0H4N.** The fibrewise coefficient of a base-changed family of cycles is the
coefficient of the original family at the image point times the length of the local ring of the
fibre of the induced morphism of fibres. -/
private theorem baseChangeFamily_apply_eq_mul_fiberLength {X Y V : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (i : V ⟶ Y) {r : ℕ} (α : FamilyOfCycles f r)
    (x : (pullback f i : Scheme.{u})) :
    (baseChangeFamily f i r α ((pullback.snd f i).base x) :
        AlgebraicCycle ((pullback.snd f i).fiber ((pullback.snd f i).base x)) ℤ)
        ((pullback.snd f i).asFiber x) =
      (α (f ((pullback.fst f i).base x)) :
            AlgebraicCycle (f.fiber (f ((pullback.fst f i).base x))) ℤ)
          (f.asFiber ((pullback.fst f i).base x)) *
        ((fiberLength (restrictedFiberMap f (pullback.snd f i) (pullback.fst f i) i
          pullback.condition ((pullback.snd f i).base x))
          ((pullback.snd f i).asFiber x)).toNat : ℤ) := by
  classical
  set t := (pullback.snd f i).base x with ht
  set N := restrictedFiberMap f (pullback.snd f i) (pullback.fst f i) i pullback.condition t
    with hN
  set x' := (pullback.snd f i).asFiber x with hx'
  have hα : (α (f ((pullback.fst f i).base x)) :
        AlgebraicCycle (f.fiber (f ((pullback.fst f i).base x))) ℤ)
        (f.asFiber ((pullback.fst f i).base x)) =
      (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ) (N x') :=
    (family_apply_restrictedFiberMap f (pullback.snd f i) (pullback.fst f i) i
      pullback.condition α x).symm
  rw [baseChangeFamily_apply, hα]
  have hfold : closedSubschemeCycleCoeff (fieldChowSituation ↥(V.residueField t))
      ((pullback.snd f i).fiberToSpecResidueField t)
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({N x'} : Set (f.fiber (i t))))).comap N).subschemeι) (r : ℤ) x' =
      flatPullbackWeight (fieldChowSituation ↥(V.residueField t))
        ((pullback.snd f i).fiberToSpecResidueField t) N (r : ℤ) x' := rfl
  rw [hfold, flatPullbackWeight_eq_fiberStalkLength]
  refine mul_ite_natCast_eq_mul _ _ fun hz hl => ?_
  have hd : relativeDimension
      (fieldChowSituation ↥(Y.residueField (i t))).dimensionFunction
      (f.fiberToSpecResidueField (i t)) (N x') = (r : ℤ) :=
    (mem_cyclesOfDimension_iff_forall_point _ _ _ _).1 (α (i t)).2 _ hz
  have hlft : LocallyOfFiniteType
      (show f.fiber (i t) ⟶ (residueFieldBaseChangeSituation i t).base.S from
        f.fiberToSpecResidueField (i t)) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField (i t)))
    infer_instance
  have hdim := relativeDimension_baseChange_eq (residueFieldBaseChangeSituation i t)
    (f.fiberToSpecResidueField (i t)) ((pullback.snd f i).fiberToSpecResidueField t) N
    (isPullback_restrictedFiberMap_baseChange f i t) x' hl
  rw [residueFieldBaseChangeSituation_c, add_zero] at hdim
  exact hdim.trans hd

/-- Reading the length of the local ring of a fibre at a point of the fibre agrees with reading
it at the canonical point of the fibre through the image of that point. -/
private theorem stalkLength_fiber_at {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (p : f.fiber y) :
    stalkLength (f.fiber y) p = fiberLength f (f.fiberι y p) := by
  have hy : f (f.fiberι y p) = y := (f.fiberHomeo y p).2
  generalize hx : f.fiberι y p = x at *
  cases hy
  have hp : p = f.asFiber x := by
    apply (f.fiberι _).isEmbedding.injective
    simpa using hx
  rw [hp]

/-- The length of the local ring of a fibre is unchanged by an isomorphism over the target. -/
private theorem fiberLength_iso {X X' Y : Scheme.{u}} (e : X ≅ X') (f : X ⟶ Y) (f' : X' ⟶ Y)
    (he : e.hom ≫ f' = f) (x : X) : fiberLength f' (e.hom x) = fiberLength f x := by
  let m : f.fiber (f x) ⟶ f'.fiber (f x) :=
    pullback.map _ _ _ _ e.hom (𝟙 _) (𝟙 _) (by simpa using he.symm) (by simp)
  have _ : IsIso m := inferInstanceAs (IsIso (pullback.map _ _ _ _ _ _ _ _ _))
  have hm : m ≫ f'.fiberι (f x) = f.fiberι (f x) ≫ e.hom := pullback.lift_fst ..
  have hx : f'.fiberι (f x) (m (f.asFiber x)) = e.hom x := by
    change (m ≫ f'.fiberι (f x)) (f.asFiber x) = _
    rw [hm]
    simp
  rw [← hx, ← stalkLength_fiber_at]
  exact Module.length_eq_of_ringEquiv
    (asIso (m.stalkMap (f.asFiber x))).commRingCatIsoToRingEquiv


/-! ### The two compatibilities -/

/-- **Stacks Project, Tag 0H68.** Forming `α ∩ β` is compatible with flat pullback: if
`g : Y' ⟶ Y` is flat, locally of finite type and of relative dimension `c`, if `α'` is the base
change of the family `α` along `g` and `β'` the flat pullback of `β`, then the cycle `α' ∩ β'` on
`X ×_Y Y'` is the flat pullback of `α ∩ β` along `X ×_Y Y' ⟶ X`. -/
@[stacks 0H68 "compatibility with flat pullback"]
theorem cap_flatPullback (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g] (c : ℕ)
    (hg : AlgebraicGeometry.RelativeDimension g c) (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles f r) (β : CycleGroup C sY e) :
    letI : LocallyOfFiniteType (f ≫ sY) := inferInstance
    letI : LocallyOfFiniteType (g ≫ sY) := inferInstance
    letI : LocallyOfFiniteType (pullback.snd f g ≫ g ≫ sY) := inferInstance
    (cap C (g ≫ sY) (pullback.snd f g) (baseChangeFamily f g r α)
          (flatPullback C (g ≫ sY) sY g rfl c hg e β) :
        AlgebraicCycle (pullback f g : Scheme.{u}) ℤ) =
      (flatPullback C (pullback.snd f g ≫ g ≫ sY) (f ≫ sY) (pullback.fst f g)
          (by rw [← Category.assoc, pullback.condition, Category.assoc]) c
          (AlgebraicGeometry.RelativeDimension.of_isPullback
            ((IsPullback.of_hasPullback f g).flip) hg) ((r : ℤ) + e) (cap C sY f α β) :
        AlgebraicCycle (pullback f g : Scheme.{u}) ℤ) := by
  classical
  let : LocallyOfFiniteType (f ≫ sY) := inferInstance
  let : LocallyOfFiniteType (g ≫ sY) := inferInstance
  let : LocallyOfFiniteType (pullback.snd f g ≫ g ≫ sY) := inferInstance
  ext w
  have hpoint : g ((pullback.snd f g).base w) = f ((pullback.fst f g).base w) :=
    (congrArg (fun q : (pullback f g : Scheme.{u}) ⟶ Y => q.base w) pullback.condition).symm
  have hmul := fiberLength_toNat_mul f (pullback.snd f g) (pullback.fst f g) g
    (IsPullback.of_hasPullback f g) w
  have hcap : (cap C sY f α β).1 ((pullback.fst f g).base w) =
      β.1 (f ((pullback.fst f g).base w)) *
        (α (f ((pullback.fst f g).base w)) :
          AlgebraicCycle (f.fiber (f ((pullback.fst f g).base w))) ℤ)
          (f.asFiber ((pullback.fst f g).base w)) := rfl
  rw [flatPullback_apply_eq_mul_fiberLength C (pullback.snd f g ≫ g ≫ sY) (f ≫ sY)
      (pullback.fst f g) _ c _ ((r : ℤ) + e) (cap C sY f α β) w, hcap, cap_apply]
  simp only [capCoeff]
  have hβpt : β.1 (g ((pullback.snd f g).base w)) =
      β.1 (f ((pullback.fst f g).base w)) := congrArg (fun y : Y => β.1 y) hpoint
  rw [flatPullback_apply_eq_mul_fiberLength C (g ≫ sY) sY g rfl c hg e β
      ((pullback.snd f g).base w),
    baseChangeFamily_apply_eq_mul_fiberLength f g α w, hβpt, hmul, Nat.cast_mul]
  ring

/-- **Stacks Project, Tag 0H68.** Forming `α ∩ β` is compatible with flat base change: in the
situation of Tag 0FVG, with `α'` the base change of the family `α` along `Y' = Y ×_S S' ⟶ Y` and
`β' = g^*β ∈ Z_{e + c}(Y')` the base change of `β`, the cycle `α' ∩ β'` is the base change of
`α ∩ β`, read along the canonical isomorphism of `X ×_Y Y'` with `X' = X ×_S S'`. -/
@[stacks 0H68 "compatibility with flat base change"]
theorem cap_baseChange (B : FlatBaseChangeSituation.{u}) {X Y : Scheme.{u}}
    (sY : Y ⟶ B.base.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (r : ℕ) (e : ℤ) (α : FamilyOfCycles f r) (β : CycleGroup B.base sY e)
    (w : (pullback f (pullback.fst sY B.g) : Scheme.{u})) :
    letI : LocallyOfFiniteType (f ≫ sY) := inferInstance
    letI : LocallyOfFiniteType (pullback.snd sY B.g) := inferInstance
    letI : LocallyOfFiniteType (pullback.snd f (pullback.fst sY B.g)) := inferInstance
    (cap B.baseChange (pullback.snd sY B.g) (pullback.snd f (pullback.fst sY B.g))
          (baseChangeFamily f (pullback.fst sY B.g) r α)
          (baseChangeCyclePullback B sY e β) :
        AlgebraicCycle (pullback f (pullback.fst sY B.g) : Scheme.{u}) ℤ) w =
      (baseChangeCyclePullback B (f ≫ sY) ((r : ℤ) + e) (cap B.base sY f α β) :
        AlgebraicCycle (pullback (f ≫ sY) B.g : Scheme.{u}) ℤ)
        ((pullbackRightPullbackFstIso sY B.g f).hom.base w) := by
  classical
  let : LocallyOfFiniteType (f ≫ sY) := inferInstance
  let : LocallyOfFiniteType (pullback.snd sY B.g) := inferInstance
  let : LocallyOfFiniteType (pullback.snd f (pullback.fst sY B.g)) := inferInstance
  have hpoint : (pullback.fst sY B.g)
        ((pullback.snd f (pullback.fst sY B.g)).base w) =
      f ((pullback.fst f (pullback.fst sY B.g)).base w) :=
    (congrArg
      (fun q : (pullback f (pullback.fst sY B.g) : Scheme.{u}) ⟶ Y => q.base w)
      pullback.condition).symm
  have hmul := fiberLength_toNat_mul f (pullback.snd f (pullback.fst sY B.g))
    (pullback.fst f (pullback.fst sY B.g)) (pullback.fst sY B.g)
    (IsPullback.of_hasPullback f (pullback.fst sY B.g)) w
  have hfst : (pullback.fst (f ≫ sY) B.g).base
      ((pullbackRightPullbackFstIso sY B.g f).hom.base w) =
      (pullback.fst f (pullback.fst sY B.g)).base w :=
    congrArg (fun q : (pullback f (pullback.fst sY B.g) : Scheme.{u}) ⟶ X => q.base w)
      (pullbackRightPullbackFstIso_hom_fst sY B.g f)
  have hiso : fiberLength (pullback.fst (f ≫ sY) B.g)
        ((pullbackRightPullbackFstIso sY B.g f).hom.base w) =
      fiberLength (pullback.fst f (pullback.fst sY B.g)) w :=
    fiberLength_iso (pullbackRightPullbackFstIso sY B.g f)
      (pullback.fst f (pullback.fst sY B.g)) (pullback.fst (f ≫ sY) B.g)
      (pullbackRightPullbackFstIso_hom_fst sY B.g f) w
  have hcap : (cap B.base sY f α β).1 ((pullback.fst f (pullback.fst sY B.g)).base w) =
      β.1 (f ((pullback.fst f (pullback.fst sY B.g)).base w)) *
        (α (f ((pullback.fst f (pullback.fst sY B.g)).base w)) :
          AlgebraicCycle (f.fiber (f ((pullback.fst f (pullback.fst sY B.g)).base w))) ℤ)
          (f.asFiber ((pullback.fst f (pullback.fst sY B.g)).base w)) := rfl
  rw [baseChangeCyclePullback_apply_eq_mul_fiberLength B (f ≫ sY) ((r : ℤ) + e)
      (cap B.base sY f α β) ((pullbackRightPullbackFstIso sY B.g f).hom.base w),
    hfst, hiso, hcap, cap_apply]
  simp only [capCoeff]
  have hβpt : β.1 ((pullback.fst sY B.g)
        ((pullback.snd f (pullback.fst sY B.g)).base w)) =
      β.1 (f ((pullback.fst f (pullback.fst sY B.g)).base w)) :=
    congrArg (fun y : Y => β.1 y) hpoint
  rw [baseChangeCyclePullback_apply_eq_mul_fiberLength B sY e β
      ((pullback.snd f (pullback.fst sY B.g)).base w),
    baseChangeFamily_apply_eq_mul_fiberLength f (pullback.fst sY B.g) α w, hβpt, hmul,
    Nat.cast_mul]
  ring

end Stacks.Chow

end
