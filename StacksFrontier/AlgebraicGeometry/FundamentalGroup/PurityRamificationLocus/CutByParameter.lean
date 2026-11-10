module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.EtaleLocus
public import StacksFrontier.Deformation.RingedSpaceThickening.FlatCriterion
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay

/-!
# Cutting the base of a morphism by one parameter

Let `f : X ⟶ Spec A` and let `t ∈ A`. This file studies the base change of `f` along the closed
immersion `Spec (A ⧸ (t)) ⟶ Spec A`: at a point `z` of the base change lying over `x ∈ X`, the
image of `t` in `𝒪_{X,x}` is killed, and when that image is a nonzerodivisor the local ring of
the base change at `z` has dimension one less than `𝒪_{X,x}`.

The map `A →+* 𝒪_{X,x}` through which `t` acts is
`AlgebraicGeometry.toStalkStalkMap`, the composite of the canonical map from `A` to the stalk of
`Spec A` at `f x` with the stalk map of `f`.

## Main results

* `AlgebraicGeometry.toStalkStalkMap`: the structure map `A →+* 𝒪_{X,x}` of a scheme over `Spec A`.
* `AlgebraicGeometry.baseToStalk_injective_of_etaleAt_generization`: over a domain, étaleness at
  some generization of `x` makes `A →+* 𝒪_{X,x}` injective.
* `AlgebraicGeometry.ringKrullDim_stalk_pullback_quotient_add_one`: the dimension of the local
  ring drops by exactly one when the base is cut by a parameter whose image is a nonzerodivisor.
* `AlgebraicGeometry.exists_regular_parameter_notMem_sq_map_ne_zero`: a regular local ring of
  positive dimension has a parameter outside the square of the maximal ideal whose image under an
  injective ring map is nonzero.

## Implementation notes

The dimension drop is proved by identifying the local ring of the base change at `z` with
`𝒪_{X,x} ⧸ (t)`. That identification comes from a pushout square of rings — `A ⧸ (t)` and
`𝒪_{X,x}` over `A`, with `𝒪_{X,x} ⧸ (t)` as pushout, the kernel of the right-hand map being the
image of the kernel of the left-hand one
(`AlgebraicGeometry.RingedSpaceThickening.ring_isPushout_of_surjective_of_ker_eq_map`) — whose
`Spec` is cartesian; comparing it with the defining cartesian square of the base change exhibits
`Spec (𝒪_{X,x} ⧸ (t))` as a flat preimmersion into the base change hitting `z` at its closed
point, so the stalk there is `𝒪_{X,x} ⧸ (t)`. Mathlib's dimension drop for a quotient by a
nonzerodivisor of the maximal ideal then gives the drop.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For a scheme `X` over `Spec A`, the structure map `A →+* 𝒪_{X,x}`. -/
noncomputable abbrev toStalkStalkMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) : A →+* X.presheaf.stalk x :=
  (StructureSheaf.toStalk A (f x) ≫ f.stalkMap x).hom

/-- The structure maps to the local rings are compatible with generization. -/
theorem baseToStalk_specializes {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) {x z : X} (h : z ⤳ x) :
    (X.presheaf.stalkSpecializes h).hom.comp (toStalkStalkMap f x) = toStalkStalkMap f z := by
  have h1 := f.stalkSpecializes_stalkMap z x h
  have h2 : StructureSheaf.toStalk A (f x) ≫
      (Spec (.of A)).presheaf.stalkSpecializes (f.base.hom.map_specializes h) =
      StructureSheaf.toStalk A (f z) :=
    StructureSheaf.toStalk_stalkSpecializes (f.base.hom.map_specializes h)
  have key : (StructureSheaf.toStalk A (f x) ≫ f.stalkMap x) ≫
      X.presheaf.stalkSpecializes h = StructureSheaf.toStalk A (f z) ≫ f.stalkMap z :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ StructureSheaf.toStalk A (f x) ≫ m) h1.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ f.stalkMap z) h2)))
  exact congrArg CommRingCat.Hom.hom key

/-- The structure map of a scheme over `Spec A` is compatible with a morphism of such schemes. -/
theorem baseToStalk_comp {A : Type u} [CommRing A] {X Z : Scheme.{u}} (j : Z ⟶ X)
    (f : X ⟶ Spec (.of A)) (z : Z) :
    (j.stalkMap z).hom.comp (toStalkStalkMap f (j z)) = toStalkStalkMap (j ≫ f) z := by
  simp only [toStalkStalkMap, Scheme.Hom.stalkMap_comp]
  rfl

/-- The structure map for a base changed along a ring map is the composite with that map. -/
theorem baseToStalk_specMap {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (φ : A →+* B) (x : X) :
    toStalkStalkMap (f ≫ Spec.map (CommRingCat.ofHom φ)) x = (toStalkStalkMap f x).comp φ := by
  have he : StructureSheaf.toStalk A ((Spec.map (CommRingCat.ofHom φ)) (f x)) ≫
      (Spec.map (CommRingCat.ofHom φ)).stalkMap (f x) =
      CommRingCat.ofHom φ ≫ StructureSheaf.toStalk B (f x) :=
    stalkMap_toStalk (CommRingCat.ofHom φ) (f x)
  have hcomp : (f ≫ Spec.map (CommRingCat.ofHom φ)).stalkMap x =
      (Spec.map (CommRingCat.ofHom φ)).stalkMap (f x) ≫ f.stalkMap x :=
    Scheme.Hom.stalkMap_comp f (Spec.map (CommRingCat.ofHom φ)) x
  have key : StructureSheaf.toStalk A ((Spec.map (CommRingCat.ofHom φ)) (f x)) ≫
      (f ≫ Spec.map (CommRingCat.ofHom φ)).stalkMap x =
      CommRingCat.ofHom φ ≫ (StructureSheaf.toStalk B (f x) ≫ f.stalkMap x) :=
    (congrArg
      (fun m ↦ StructureSheaf.toStalk A ((Spec.map (CommRingCat.ofHom φ)) (f x)) ≫ m)
      hcomp).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m ↦ m ≫ f.stalkMap x) he).trans (Category.assoc _ _ _)))
  exact congrArg CommRingCat.Hom.hom key

/-- `Spec` of the structure map `A →+* 𝒪_{X,x}` is the canonical morphism from the spectrum of
the local ring, followed by the structure morphism. -/
theorem specMap_baseToStalk {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (x : X) :
    Spec.map (CommRingCat.ofHom (toStalkStalkMap f x)) = X.fromSpecStalk x ≫ f := by
  have h1 := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  have h2 := Spec.fromSpecStalk_eq' (CommRingCat.of A) (f x)
  have h3 : Spec.map (StructureSheaf.toStalk A (f x) ≫ f.stalkMap x) =
      Spec.map (f.stalkMap x) ≫ Spec.map (StructureSheaf.toStalk A (f x)) :=
    Spec.map_comp _ _
  exact h3.trans
    ((congrArg (fun m ↦ Spec.map (f.stalkMap x) ≫ m) h2).symm.trans h1)

/-- Over a domain, the structure map `A →+* 𝒪_{X,x}` is injective at a point of étaleness: the
stalk map of an étale morphism is faithfully flat, hence injective, and the canonical map from
`A` to the local ring of `Spec A` is injective because the complement of a prime consists of
nonzerodivisors. -/
theorem baseToStalk_injective_of_etaleAt {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) (hx : EtaleAt f x) :
    Function.Injective (toStalkStalkMap f x) := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp hx
  let xU : U.toScheme := ⟨x, hxU⟩
  let g := U.ι ≫ f
  have _ : Etale g := hU
  let _ : Algebra ((Spec (.of A)).presheaf.stalk (g xU)) (U.toScheme.presheaf.stalk xU) :=
    (g.stalkMap xU).hom.toAlgebra
  have _ : Module.Flat ((Spec (.of A)).presheaf.stalk (g xU))
      (U.toScheme.presheaf.stalk xU) := Flat.stalkMap g xU
  have _ : IsLocalHom (algebraMap ((Spec (.of A)).presheaf.stalk (g xU))
      (U.toScheme.presheaf.stalk xU)) := g.prop xU
  have _ : Module.FaithfullyFlat ((Spec (.of A)).presheaf.stalk (g xU))
      (U.toScheme.presheaf.stalk xU) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hg : Function.Injective (g.stalkMap xU).hom :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (inferInstance : Module.FaithfullyFlat ((Spec (.of A)).presheaf.stalk (g xU))
        (U.toScheme.presheaf.stalk xU))).injective
  have _ : (g xU).asIdeal.IsPrime := (g xU).isPrime
  let _ : Algebra A ((Spec (.of A)).presheaf.stalk (g xU)) :=
    (StructureSheaf.toStalk A (g xU)).hom.toAlgebra
  have _ : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (g xU)) (g xU).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (g xU)
  have hA : Function.Injective (StructureSheaf.toStalk A (g xU)).hom := by
    change Function.Injective (algebraMap A ((Spec (.of A)).presheaf.stalk (g xU)))
    exact IsLocalization.injective _ ((g xU).asIdeal.primeCompl_le_nonZeroDivisors)
  have hinj : Function.Injective (toStalkStalkMap g xU) := hg.comp hA
  rw [← baseToStalk_comp U.ι f xU] at hinj
  exact Function.Injective.of_comp (f := (U.ι.stalkMap xU).hom) hinj

/-- Over a domain, the structure map `A →+* 𝒪_{X,x}` is injective as soon as the morphism is
étale at some generization of `x`: the structure maps are compatible with generization. -/
theorem baseToStalk_injective_of_etaleAt_generization {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {x z : X} (h : z ⤳ x) (hz : EtaleAt f z) :
    Function.Injective (toStalkStalkMap f x) := by
  have hinj := baseToStalk_injective_of_etaleAt f z hz
  rw [← baseToStalk_specializes f h] at hinj
  exact Function.Injective.of_comp (f := (X.presheaf.stalkSpecializes h).hom) hinj

/-- Cutting the base by `t` kills the image of `t` in the local rings of the base change. -/
theorem baseToStalk_pullback_quotient_eq_zero {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (t : A)
    (x : (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {t})))) : Scheme.{u})) :
    (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {t}))))).stalkMap x
        (toStalkStalkMap f ((pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {t})))) : _ ⟶ X) x) t) = 0 := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t})))
  let j : pullback f q ⟶ X := pullback.fst f q
  change (j.stalkMap x).hom.comp (toStalkStalkMap f (j x)) t = 0
  rw [baseToStalk_comp, pullback.condition, baseToStalk_specMap]
  simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton t)), map_zero]

/-- **The dimension drop under cutting the base by one parameter.** If the image of `t` in
`𝒪_{X,x}` is a nonzerodivisor, then the local ring of `X ×_{Spec A} Spec (A ⧸ (t))` at a point
over `x` has dimension one less than `𝒪_{X,x}`. -/
theorem ringKrullDim_stalk_pullback_quotient_add_one {A : Type u} [CommRing A] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ Spec (.of A)) (t : A)
    (z : (pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {t})))) : Scheme.{u}))
    (hnz : toStalkStalkMap f ((pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {t})))) : _ ⟶ X) z) t ∈
      nonZeroDivisors (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {t})))) : _ ⟶ X) z))) :
    ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {t}))))).presheaf.stalk z) + 1 =
      ringKrullDim (X.presheaf.stalk ((pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {t})))) : _ ⟶ X) z)) := by
  let I := Ideal.span {t}
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let j : pullback f q ⟶ X := pullback.fst f q
  let x := j z
  let R : Type u := X.presheaf.stalk x
  let φ : A →+* R := toStalkStalkMap f x
  let J := Ideal.span {φ t}
  have ht : φ t ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.maximalIdeal_comap (j.stalkMap z).hom, Ideal.mem_comap,
      show (j.stalkMap z).hom (φ t) = 0 from baseToStalk_pullback_quotient_eq_zero f t z]
    exact Ideal.zero_mem _
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr ht)
  have _ : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have _ : IsLocalRing (R ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hIJ : I ≤ Ideal.comap φ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_singleton (φ t)))
  let ψ := Ideal.quotientMap J φ hIJ
  let p : Spec (.of (R ⧸ J)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let b : Spec (.of (R ⧸ J)) ⟶ Spec (.of (A ⧸ I)) :=
    Spec.map (CommRingCat.ofHom ψ)
  have hpo : IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom ψ) (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    apply RingedSpaceThickening.ring_isPushout_of_surjective_of_ker_eq_map
    · ext a
      rfl
    · exact Ideal.Quotient.mk_surjective
    · exact Ideal.Quotient.mk_surjective
    · simp only [CommRingCat.hom_ofHom, Ideal.mk_ker, I, J, Ideal.map_span,
        Set.image_singleton]
  have hout : IsPullback p b (X.fromSpecStalk x ≫ f) q := by
    have h := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
    change IsPullback p b (Spec.map (CommRingCat.ofHom φ)) q at h
    simpa only [φ, specMap_baseToStalk] using h
  let k : Spec (.of (R ⧸ J)) ⟶ pullback f q :=
    pullback.lift (p ≫ X.fromSpecStalk x) b (by simpa only [Category.assoc] using hout.w)
  have hk : k ≫ j = p ≫ X.fromSpecStalk x := pullback.lift_fst _ _ _
  have hk' : IsPullback k p j (X.fromSpecStalk x) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f q) (h₂₂ := f) (v₁₃ := q) ?_ hk ?_
    · simpa only [k, pullback.lift_snd] using hout.flip
    · exact (IsPullback.of_hasPullback f q).flip
  have _ : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  have _ : Flat k := MorphismProperty.of_isPullback hk'.flip inferInstance
  have _ : IsPreimmersion k := MorphismProperty.of_isPullback hk'.flip inferInstance
  have _ : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hc : k (IsLocalRing.closedPoint (R ⧸ J)) = z := by
    refine j.isEmbedding.injective ?_
    have _ : IsLocalHom (Ideal.Quotient.mk J) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hp : p (IsLocalRing.closedPoint (R ⧸ J)) = IsLocalRing.closedPoint R :=
      Spec_closedPoint
    calc j (k (IsLocalRing.closedPoint (R ⧸ J)))
        = (X.fromSpecStalk x) (p (IsLocalRing.closedPoint (R ⧸ J))) :=
          congrArg (fun m : Spec (.of (R ⧸ J)) ⟶ X ↦ m (IsLocalRing.closedPoint (R ⧸ J))) hk
      _ = (X.fromSpecStalk x) (IsLocalRing.closedPoint R) :=
          congrArg (fun y ↦ (X.fromSpecStalk x) y) hp
      _ = x := X.fromSpecStalk_closedPoint
  have _ : IsIso (k.stalkMap (IsLocalRing.closedPoint (R ⧸ J))) :=
    isIso_stalkMap_of_flat_isPreimmersion k (IsLocalRing.closedPoint (R ⧸ J))
  have heq : ringKrullDim ((pullback f q).presheaf.stalk z) = ringKrullDim (R ⧸ J) := by
    rw [← hc]
    have e := (asIso (k.stalkMap (IsLocalRing.closedPoint (R ⧸ J)))).commRingCatIsoToRingEquiv
    exact e.ringKrullDim.trans
      (stalkClosedPointIso (.of (R ⧸ J))).commRingCatIsoToRingEquiv.ringKrullDim
  change ringKrullDim ((pullback f q).presheaf.stalk z) + 1 = ringKrullDim R
  rw [heq]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnz ht

/-- A regular local ring of positive dimension has an element of the maximal ideal outside its
square whose image under an injective ring map is nonzero. -/
theorem exists_regular_parameter_notMem_sq_map_ne_zero {A R : Type u} [CommRing A]
    [IsRegularLocalRing A] [CommRing R] (φ : A →+* R) (hφ : Function.Injective φ)
    (hpos : ringKrullDim A ≠ 0) :
    ∃ t : A, t ∈ IsLocalRing.maximalIdeal A ∧
      t ∉ (IsLocalRing.maximalIdeal A) ^ 2 ∧ φ t ≠ 0 := by
  obtain ⟨t, ht, ht2⟩ := IsConcreteLE.exists_of_lt
    (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hpos)
  exact ⟨t, ht, ht2, fun hzero ↦ ht2 ((hφ (hzero.trans φ.map_zero.symm)) ▸ Ideal.zero_mem _)⟩

end AlgebraicGeometry

end
