module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeObjects
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMap

/-!
# Base change of smooth lifts

Let `f : S ⟶ S'` be a morphism of affine divided power bases, `A' = Γ(S', ⊤) → A = Γ(S, ⊤)`, with
divided power ideals `I'` and `I`, and let `g : X ⟶ X'` be such that `X = X' ×_{S'₀} S₀`
(`IsPullback g S.toClosedFiber S'.toClosedFiber (closedFiberMap f)`). For an affine open `U'` of
`X'` with a smooth lift `B'` over `A'`
(`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`),
`A ⊗_{A'} B'` is a smooth lift over `A` of the affine open `g⁻¹ U' = U' ×_{S'₀} S₀` of `X`
(`CechEnvelope.SmoothLift.baseChange`). This is the cover of `X` the base change theorem
[Stacks, Tag 07MU] uses for `X = X' ×_{S'₀} S₀`: the base change of a cover of `X'` by charts
with smooth lifts.

## The proof

The ring `(A ⊗_{A'} B') / I` is the pushout of `B' / I'B' ← A' / I' → A / I` in commutative rings
(`CechEnvelope.isPushout_reducedTensor`), for any ideals with `I' A ⊆ I`. Since `S` and `S'` are
affine, `Γ(S₀) = A / I` and `Γ(S'₀) = A' / I'` (`CechEnvelope.closedFiberSectionsEquiv`), and
`Γ(U') = B' / I'B'` is part of the smooth lift. On the other hand `g⁻¹ U' = U' ×_{S'₀} S₀` is a
fibre product of affine schemes, so `Γ(g⁻¹ U')` is the pushout of `Γ(U') ← Γ(S'₀) → Γ(S₀)`
(`CechEnvelope.isPushout_sections`). The two pushouts of one span are isomorphic, compatibly with
the maps from `A` (`CechEnvelope.baseChangeSectionsIso_sourceToBase`).

## Main results

* `CechEnvelope.isPushout_reducedTensor` — `(A ⊗_{A'} B') / I` is a pushout.
* `CechEnvelope.closedFiberSectionsEquiv` — `Γ(S₀, ⊤) ≅ A / I`.
* `CechEnvelope.isAffine_preimage`, `CechEnvelope.isPushout_sections` — `g⁻¹ U'` is affine with
  `Γ(g⁻¹ U') = Γ(U') ⊗_{Γ(S'₀)} Γ(S₀)`.
* **`CechEnvelope.SmoothLift.baseChange`** — the base change of a smooth lift.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

section Algebra

variable {A' A B' : Type u} [CommRing A'] [CommRing A] [CommRing B'] [Algebra A' A]
  [Algebra A' B'] (I' : Ideal A') (I : Ideal A)

/-- The reduction `(A ⊗_{A'} B') / I (A ⊗_{A'} B')`. -/
abbrev reducedTensor : Type u :=
  (A ⊗[A'] B') ⧸ I.map (algebraMap A (A ⊗[A'] B'))

variable {I' I}

/-- The two ring maps `A' → A ⊗_{A'} B'` agree. -/
theorem includeRight_comp_algebraMap :
    (Algebra.TensorProduct.includeRight (R := A') (A := A) (B := B')).toRingHom.comp
        (algebraMap A' B') =
      (algebraMap A (A ⊗[A'] B')).comp (algebraMap A' A) := by
  ext a
  simp [Algebra.algebraMap_eq_smul_one]

/-- If `I'A ⊆ I`, the image of `I'B'` in `A ⊗_{A'} B'` lies in `I (A ⊗_{A'} B')`. -/
theorem map_includeRight_le (hI : I'.map (algebraMap A' A) ≤ I) :
    (I'.map (algebraMap A' B')).map
        (Algebra.TensorProduct.includeRight (R := A') (A := A) (B := B')).toRingHom ≤
      I.map (algebraMap A (A ⊗[A'] B')) := by
  rw [Ideal.map_map, includeRight_comp_algebraMap, ← Ideal.map_map]
  exact Ideal.map_mono hI

/-- `B' / I'B' ⟶ (A ⊗_{A'} B') / I`, `b ↦ 1 ⊗ b`. -/
def reducedTensorLeft (hI : I'.map (algebraMap A' A) ≤ I) :
    B' ⧸ I'.map (algebraMap A' B') →+* reducedTensor (A' := A') (B' := B') I :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp
      (Algebra.TensorProduct.includeRight (R := A') (A := A) (B := B')).toRingHom) (by
      intro b hb
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact map_includeRight_le hI (Ideal.mem_map_of_mem _ hb))

/-- `A / I ⟶ (A ⊗_{A'} B') / I`, `a ↦ a ⊗ 1`. -/
def reducedTensorRight : A ⧸ I →+* reducedTensor (A' := A') (B' := B') I :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (algebraMap A (A ⊗[A'] B'))) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha)

variable (I' I) in
/-- The map `A' / I' ⟶ B' / I'B'`. -/
abbrev quotientMapLeft : A' ⧸ I' →+* B' ⧸ I'.map (algebraMap A' B') :=
  Ideal.quotientMap _ (algebraMap A' B') Ideal.le_comap_map

/-- The map `A' / I' ⟶ A / I`. -/
abbrev quotientMapRight (hI : I'.map (algebraMap A' A) ≤ I) : A' ⧸ I' →+* A ⧸ I :=
  Ideal.quotientMap I (algebraMap A' A) (Ideal.map_le_iff_le_comap.1 hI)

/-- `reducedTensorLeft` sends the class of `b` to the class of `1 ⊗ b`. -/
@[simp]
theorem reducedTensorLeft_mk (hI : I'.map (algebraMap A' A) ≤ I) (b : B') :
    reducedTensorLeft (A := A) hI (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ (1 ⊗ₜ b) :=
  rfl

/-- `reducedTensorRight` sends the class of `a` to the class of `a ⊗ 1`. -/
@[simp]
theorem reducedTensorRight_mk (a : A) :
    reducedTensorRight (A' := A') (B' := B') (I := I) (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (a ⊗ₜ 1) :=
  rfl

section Desc

variable {T : Type u} [CommRing T]

variable (A') in
/-- The `A'`-algebra structure on `T` through `A' → A / I → T`. -/
abbrev descAlgebra (y : A ⧸ I →+* T) : Algebra A' T :=
  ((y.comp (Ideal.Quotient.mk I)).comp (algebraMap A' A)).toAlgebra

variable (A') in
/-- `A → T`, as a map of `A'`-algebras. -/
def descLeft (y : A ⧸ I →+* T) : letI := descAlgebra A' y; A →ₐ[A'] T :=
  letI := descAlgebra A' y
  { y.comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }

/-- `B' → T`, as a map of `A'`-algebras. -/
def descRight (hI : I'.map (algebraMap A' A) ≤ I) (x : B' ⧸ I'.map (algebraMap A' B') →+* T)
    (y : A ⧸ I →+* T) (hxy : x.comp (quotientMapLeft I') = y.comp (quotientMapRight hI)) :
    letI := descAlgebra A' y; B' →ₐ[A'] T :=
  letI := descAlgebra A' y
  { x.comp (Ideal.Quotient.mk _) with
    commutes' := fun a => RingHom.congr_fun hxy (Ideal.Quotient.mk I' a) }

/-- The map `A ⊗_{A'} B' → T` out of the two legs. -/
def descTensor (hI : I'.map (algebraMap A' A) ≤ I) (x : B' ⧸ I'.map (algebraMap A' B') →+* T)
    (y : A ⧸ I →+* T) (hxy : x.comp (quotientMapLeft I') = y.comp (quotientMapRight hI)) :
    A ⊗[A'] B' →+* T :=
  letI := descAlgebra A' y
  (Algebra.TensorProduct.lift (descLeft A' y) (descRight hI x y hxy)
    (fun _ _ => Commute.all _ _)).toRingHom

/-- `descTensor` sends `a ⊗ b` to the product of `y` at the class of `a` and `x` at the class of
`b`. -/
theorem descTensor_tmul (hI : I'.map (algebraMap A' A) ≤ I)
    (x : B' ⧸ I'.map (algebraMap A' B') →+* T) (y : A ⧸ I →+* T)
    (hxy : x.comp (quotientMapLeft I') = y.comp (quotientMapRight hI)) (a : A) (b : B') :
    descTensor hI x y hxy (a ⊗ₜ b) = y (Ideal.Quotient.mk I a) * x (Ideal.Quotient.mk _ b) :=
  rfl

/-- **The map out of `(A ⊗_{A'} B') / I`** determined by its two legs. -/
def reducedTensorDesc (hI : I'.map (algebraMap A' A) ≤ I)
    (x : B' ⧸ I'.map (algebraMap A' B') →+* T) (y : A ⧸ I →+* T)
    (hxy : x.comp (quotientMapLeft I') = y.comp (quotientMapRight hI)) :
    reducedTensor (A' := A') (B' := B') I →+* T :=
  Ideal.Quotient.lift _ (descTensor hI x y hxy) (by
    have : I.map (algebraMap A (A ⊗[A'] B')) ≤ RingHom.ker (descTensor hI x y hxy) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change descTensor hI x y hxy (a ⊗ₜ 1) = 0
      rw [descTensor_tmul, (Ideal.Quotient.eq_zero_iff_mem).2 ha, map_zero, zero_mul]
    exact fun a ha => this ha)

/-- `reducedTensorDesc` restricts to `x` on `B' / I'B'`. -/
theorem reducedTensorDesc_comp_left (hI : I'.map (algebraMap A' A) ≤ I)
    (x : B' ⧸ I'.map (algebraMap A' B') →+* T) (y : A ⧸ I →+* T)
    (hxy : x.comp (quotientMapLeft I') = y.comp (quotientMapRight hI)) :
    (reducedTensorDesc hI x y hxy).comp (reducedTensorLeft hI) = x := by
  ext b
  change y (Ideal.Quotient.mk I 1) * x (Ideal.Quotient.mk _ b) = _
  rw [map_one, map_one, one_mul]
  rfl

/-- `reducedTensorDesc` restricts to `y` on `A / I`. -/
theorem reducedTensorDesc_comp_right (hI : I'.map (algebraMap A' A) ≤ I)
    (x : B' ⧸ I'.map (algebraMap A' B') →+* T) (y : A ⧸ I →+* T)
    (hxy : x.comp (quotientMapLeft I') = y.comp (quotientMapRight hI)) :
    (reducedTensorDesc hI x y hxy).comp reducedTensorRight = y := by
  ext a
  change y (Ideal.Quotient.mk I a) * x (Ideal.Quotient.mk _ 1) = _
  rw [map_one, map_one, mul_one]
  rfl

/-- Two maps out of `(A ⊗_{A'} B') / I` agreeing on the two legs are equal. -/
theorem reducedTensor_hom_ext (hI : I'.map (algebraMap A' A) ≤ I)
    {m m' : reducedTensor (A' := A') (B' := B') I →+* T}
    (h₁ : m.comp (reducedTensorLeft hI) = m'.comp (reducedTensorLeft hI))
    (h₂ : m.comp reducedTensorRight = m'.comp reducedTensorRight) : m = m' := by
  refine Ideal.Quotient.ringHom_ext (Algebra.TensorProduct.ringHom_ext ?_ ?_)
  · ext a
    exact RingHom.congr_fun h₂ (Ideal.Quotient.mk I a)
  · ext b
    exact RingHom.congr_fun h₁ (Ideal.Quotient.mk (I'.map (algebraMap A' B')) b)

end Desc

/-- **`(A ⊗_{A'} B') / I` is the pushout of `B' / I'B' ← A' / I' → A / I`** in commutative rings,
for ideals `I' ⊆ A'` and `I ⊆ A` with `I'A ⊆ I`. -/
theorem isPushout_reducedTensor (hI : I'.map (algebraMap A' A) ≤ I) :
    IsPushout (CommRingCat.ofHom (quotientMapLeft (B' := B') I'))
      (CommRingCat.ofHom (quotientMapRight hI))
      (CommRingCat.ofHom (reducedTensorLeft (A := A) (B' := B') hI))
      (CommRingCat.ofHom (reducedTensorRight (A' := A') (B' := B') (I := I))) := by
  have w : CommRingCat.ofHom (quotientMapLeft (B' := B') I') ≫
        CommRingCat.ofHom (reducedTensorLeft (A := A) (B' := B') hI) =
      CommRingCat.ofHom (quotientMapRight hI) ≫
        CommRingCat.ofHom (reducedTensorRight (A' := A') (B' := B') (I := I)) := by
    ext a
    change reducedTensorLeft hI (Ideal.Quotient.mk _ (algebraMap A' B' a)) =
      reducedTensorRight (Ideal.Quotient.mk _ (algebraMap A' A a))
    rw [reducedTensorLeft_mk, reducedTensorRight_mk]
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun
      (includeRight_comp_algebraMap (A' := A') (A := A) (B' := B')) a)
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
    (PushoutCocone.IsColimit.mk w (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · exact CommRingCat.ofHom (reducedTensorDesc hI s.inl.hom s.inr.hom
      (congrArg CommRingCat.Hom.hom s.condition))
  · exact CommRingCat.hom_ext (reducedTensorDesc_comp_left _ _ _ _)
  · exact CommRingCat.hom_ext (reducedTensorDesc_comp_right _ _ _ _)
  · refine CommRingCat.hom_ext (reducedTensor_hom_ext hI ?_ ?_)
    · rw [CommRingCat.hom_ofHom, reducedTensorDesc_comp_left]
      exact congrArg CommRingCat.Hom.hom h₁
    · rw [CommRingCat.hom_ofHom, reducedTensorDesc_comp_right]
      exact congrArg CommRingCat.Hom.hom h₂

end Algebra

/-! ### The closed fibre of an affine divided power base -/

section ClosedFiber

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]

/-- The closed fibre `S₀` of an affine divided power base is affine. -/
instance isAffine_closedFiber : IsAffine (DividedPowerScheme.closedFiber S.S) :=
  isAffine_of_isAffineHom (DividedPowerScheme.closedFiberι S.S)

/-- The map `A = Γ(S, ⊤) → Γ(S₀, ⊤)`. -/
abbrev closedFiberSectionsMap :
    ↥(baseSectionsRing S) →+* Γ(DividedPowerScheme.closedFiber S.S, ⊤) :=
  (DividedPowerScheme.closedFiberι S.S).appTop.hom

/-- The map `Γ(S, ⊤) → Γ(S₀, ⊤)` is surjective. -/
theorem surjective_closedFiberSectionsMap : Function.Surjective (closedFiberSectionsMap S) :=
  (DividedPowerScheme.closedFiberι S.S).app_surjective ⊤ (isAffineOpen_top _)

/-- The kernel of `Γ(S, ⊤) → Γ(S₀, ⊤)` is the divided power ideal `I`. -/
theorem ker_closedFiberSectionsMap :
    RingHom.ker (closedFiberSectionsMap S) = (baseSectionsRing S).ideal :=
  ((DividedPowerScheme.ideal_obj_eq_ker_ideal_closedFiberι S.S
    ⟨⊤, isAffineOpen_top _⟩).trans (Scheme.Hom.ker_apply _ _)).symm

/-- **`Γ(S₀, ⊤) = A / I`** for an affine divided power base `S` with `A = Γ(S, ⊤)`. -/
def closedFiberSectionsEquiv :
    Γ(DividedPowerScheme.closedFiber S.S, ⊤) ≃+*
      ↥(baseSectionsRing S) ⧸ (baseSectionsRing S).ideal :=
  ((RingHom.quotientKerEquivOfSurjective (surjective_closedFiberSectionsMap S)).symm).trans
    (Ideal.quotEquivOfEq (ker_closedFiberSectionsMap S))

/-- `closedFiberSectionsEquiv` sends the restriction of `a ∈ A` to the class of `a` in `A / I`. -/
@[simp]
theorem closedFiberSectionsEquiv_apply (a : baseSectionsRing S) :
    closedFiberSectionsEquiv S (closedFiberSectionsMap S a) = Ideal.Quotient.mk _ a := by
  rw [closedFiberSectionsEquiv, RingEquiv.trans_apply,
    show (RingHom.quotientKerEquivOfSurjective (surjective_closedFiberSectionsMap S)).symm
      (closedFiberSectionsMap S a) = Ideal.Quotient.mk _ a from (RingEquiv.symm_apply_eq _).2 rfl,
    Ideal.quotEquivOfEq_mk]

/-- The inverse of `closedFiberSectionsEquiv` sends the class of `a` to its restriction. -/
private theorem closedFiberSectionsEquiv_symm_mk (a : baseSectionsRing S) :
    (closedFiberSectionsEquiv S).symm (Ideal.Quotient.mk _ a) = closedFiberSectionsMap S a :=
  (RingEquiv.symm_apply_eq _).2 (closedFiberSectionsEquiv_apply S a).symm

end ClosedFiber

/-! ### Base change of a smooth lift -/

section BaseChange

variable {S S' : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
  (f : S.S ⟶ S'.S)

/-- The ring map `A' = Γ(S', ⊤) → A = Γ(S, ⊤)`, on the divided power rings of global sections. -/
abbrev baseSectionsRingHom : ↥(baseSectionsRing S') →+* ↥(baseSectionsRing S) :=
  SmallSite.baseChangeRingHom f

/-- `A` as an `A'`-algebra. -/
abbrev baseSectionsAlgebra : Algebra ↥(baseSectionsRing S') ↥(baseSectionsRing S) :=
  (baseSectionsRingHom f).toAlgebra

omit [IsAffine S.S.scheme] [IsAffine S'.S.scheme] in
/-- The closed fibre map on global sections is the base ring map modulo the ideals. -/
theorem closedFiberMap_appTop_closedFiberSectionsMap (a : baseSectionsRing S') :
    (DividedPowerScheme.closedFiberMap f).appTop.hom (closedFiberSectionsMap S' a) =
      closedFiberSectionsMap S (baseSectionsRingHom f a) := by
  have h := congrArg (fun k => k.appTop.hom a)
    (DividedPowerScheme.closedFiberMap_comp_closedFiberι f)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at h
  exact h

/-- The divided power ideal `I'` of `A'` maps into the divided power ideal `I` of `A`. -/
theorem map_ideal_le :
    letI := baseSectionsAlgebra f
    (baseSectionsRing S').ideal.map (algebraMap (baseSectionsRing S') (baseSectionsRing S)) ≤
      (baseSectionsRing S).ideal := by
  let := baseSectionsAlgebra f
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← ker_closedFiberSectionsMap, RingHom.mem_ker]
  change closedFiberSectionsMap S (baseSectionsRingHom f a) = 0
  have ha' : closedFiberSectionsMap S' a = 0 := by
    rw [← RingHom.mem_ker, ker_closedFiberSectionsMap]
    exact ha
  rw [← closedFiberMap_appTop_closedFiberSectionsMap, ha', map_zero]

variable {f} {g : S.X ⟶ S'.X}
  (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
  (U' : S'.X.Opens)

omit [IsAffine S.S.scheme] [IsAffine S'.S.scheme] in
include hpb in
/-- The square `g⁻¹ U' ⟶ U' ⟶ S'₀`, `g⁻¹ U' ⟶ S₀ ⟶ S'₀` is cartesian. -/
theorem isPullback_restrict :
    IsPullback (g ∣_ U') ((g ⁻¹ᵁ U').ι ≫ S.toClosedFiber) (U'.ι ≫ S'.toClosedFiber)
      (DividedPowerScheme.closedFiberMap f) :=
  (isPullback_morphismRestrict g U').paste_vert hpb

include hpb in
/-- The preimage of an affine open of `X'` in `X = X' ×_{S'₀} S₀` is affine. -/
theorem isAffine_preimage [IsAffine U'] : IsAffine (g ⁻¹ᵁ U') :=
  IsAffine.of_isPullback (isPullback_restrict hpb U')

include hpb in
/-- **`Γ(g⁻¹ U') = Γ(U') ⊗_{Γ(S'₀)} Γ(S₀)`**, as a pushout of commutative rings. -/
theorem isPushout_sections [IsAffine U'] :
    IsPushout (U'.ι ≫ S'.toClosedFiber).appTop (DividedPowerScheme.closedFiberMap f).appTop
      (g ∣_ U').appTop ((g ⁻¹ᵁ U').ι ≫ S.toClosedFiber).appTop :=
  have := isAffine_preimage hpb U'
  isPushout_appTop_of_isPullback (isPullback_restrict hpb U')

variable {U'} [IsAffine U'] (L' : SmoothLift S' U'.ι)

omit [IsAffine U'] in
/-- The algebraic pushout `(A ⊗_{A'} B') / I`, read on the span `Γ(U') ← Γ(S'₀) → Γ(S₀)`. -/
theorem isPushout_reducedTensor_sections :
    letI := baseSectionsAlgebra f
    IsPushout (U'.ι ≫ S'.toClosedFiber).appTop (DividedPowerScheme.closedFiberMap f).appTop
      (L'.equiv.toCommRingCatIso.hom ≫
        CommRingCat.ofHom (reducedTensorLeft (A := ↥(baseSectionsRing S)) (map_ideal_le f)))
      ((closedFiberSectionsEquiv S).toCommRingCatIso.hom ≫
        CommRingCat.ofHom (reducedTensorRight (A' := ↥(baseSectionsRing S')) (B' := L'.ring)
          (I := (baseSectionsRing S).ideal))) := by
  let := baseSectionsAlgebra f
  refine (isPushout_reducedTensor (A' := ↥(baseSectionsRing S')) (A := ↥(baseSectionsRing S))
    (B' := L'.ring) (map_ideal_le f)).of_iso (closedFiberSectionsEquiv S').symm.toCommRingCatIso
    L'.equiv.symm.toCommRingCatIso (closedFiberSectionsEquiv S).symm.toCommRingCatIso
    (Iso.refl _) ?_ ?_ ?_ ?_
  · ext a
    change L'.equiv.symm (Ideal.Quotient.mk _ (algebraMap _ _ a)) =
      (U'.ι ≫ S'.toClosedFiber).appTop.hom ((closedFiberSectionsEquiv S').symm
        (Ideal.Quotient.mk _ a))
    rw [closedFiberSectionsEquiv_symm_mk S', RingEquiv.symm_apply_eq]
    exact (L'.equiv_sourceToBase a).symm
  · ext a
    change (closedFiberSectionsEquiv S).symm (Ideal.Quotient.mk _ (baseSectionsRingHom f a)) =
      (DividedPowerScheme.closedFiberMap f).appTop.hom ((closedFiberSectionsEquiv S').symm
        (Ideal.Quotient.mk _ a))
    rw [closedFiberSectionsEquiv_symm_mk S', closedFiberMap_appTop_closedFiberSectionsMap,
      RingEquiv.symm_apply_eq, closedFiberSectionsEquiv_apply]
  · ext x
    change _ = reducedTensorLeft (map_ideal_le f) (L'.equiv (L'.equiv.symm x))
    rw [RingEquiv.apply_symm_apply]
    rfl
  · ext x
    change _ = reducedTensorRight ((closedFiberSectionsEquiv S)
      ((closedFiberSectionsEquiv S).symm x))
    rw [RingEquiv.apply_symm_apply]
    rfl

include hpb in
/-- **`Γ(g⁻¹ U') ≅ (A ⊗_{A'} B') / I`**: both are pushouts of `Γ(U') ← Γ(S'₀) → Γ(S₀)`. -/
def baseChangeSectionsIso :
    letI := baseSectionsAlgebra f
    Γ((g ⁻¹ᵁ U').toScheme, ⊤) ≅
      CommRingCat.of (reducedTensor (A' := ↥(baseSectionsRing S')) (B' := L'.ring)
        (baseSectionsRing S).ideal) :=
  (isPushout_sections hpb U').isoIsPushout _ _ (isPushout_reducedTensor_sections L')

include hpb in
/-- `baseChangeSectionsIso` is compatible with the maps from `A`: the image of `a ∈ A` in
`Γ(g⁻¹ U')` goes to the class of `a ⊗ 1`. -/
theorem baseChangeSectionsIso_sourceToBase (a : baseSectionsRing S) :
    letI := baseSectionsAlgebra f
    (baseChangeSectionsIso hpb L').hom.hom
        ((sourceToBase (overSituation S (g ⁻¹ᵁ U').ι)).appTop.hom a) =
      Ideal.Quotient.mk _ (algebraMap (baseSectionsRing S) (↥(baseSectionsRing S) ⊗[
        ↥(baseSectionsRing S')] L'.ring) a) := by
  let := baseSectionsAlgebra f
  have h := congrArg (fun k => k.hom (closedFiberSectionsMap S a))
    (IsPushout.inr_isoIsPushout_hom _ _ (isPushout_sections hpb U')
      (isPushout_reducedTensor_sections L'))
  refine h.trans ?_
  change reducedTensorRight (closedFiberSectionsEquiv S (closedFiberSectionsMap S a)) = _
  rw [closedFiberSectionsEquiv_apply]
  rfl

include hpb in
/-- **The base change of a smooth lift.** For `X = X' ×_{S'₀} S₀` and a smooth lift `B'` of an
affine open `U'` of `X'` over `A' = Γ(S', ⊤)`, the smooth `A`-algebra `A ⊗_{A'} B'` is a smooth
lift of the affine open `g⁻¹ U' = U' ×_{S'₀} S₀` of `X` over `A = Γ(S, ⊤)`. -/
def SmoothLift.baseChange : SmoothLift S (g ⁻¹ᵁ U').ι :=
  letI := baseSectionsAlgebra f
  haveI := L'.smooth
  { ring := ↥(baseSectionsRing S) ⊗[↥(baseSectionsRing S')] L'.ring
    smooth := inferInstance
    equiv := (baseChangeSectionsIso hpb L').commRingCatIsoToRingEquiv
    equiv_sourceToBase := baseChangeSectionsIso_sourceToBase hpb L' }

end BaseChange

end Crystalline.GlobalCrystallineSituation.CechEnvelope
