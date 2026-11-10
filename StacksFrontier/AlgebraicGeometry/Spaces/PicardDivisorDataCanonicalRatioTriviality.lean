module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorCanonicalRatio

/-!
# The claim of Stacks 0EPX is not a statement about arbitrary meromorphic sections

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`. The claim
of Stacks 0EPX — a regular meromorphic section of an invertible `𝒪_X`-module whose Weil divisor
vanishes trivializes the module — is carried as the hypothesis `htriv` of
`AlgebraicGeometry.Space.PicardDivisorData.injective_picardToWeilDivisorClassGroup`, where it is
stated for an *arbitrary* meromorphic section. This file shows that that hypothesis is still
refutable at the constructed ratio `s / s_ξ` of Stacks 0EPR, and so must carry regularity of the
section.

The reason is the `else` branch of `AlgebraicGeometry.Space.PrimeDivisor.canonicalLocalRatio`:
the ratio is a *unit* of `Q(𝒪^h_{X, ξ})`, so when `s / s_ξ` fails to be a unit the construction
returns `1`. The zero section is such a case — its ratio is `0` — so every order of vanishing of
the zero section is zero, and `htriv` applied to it asks that every invertible `𝒪_X`-module be
trivial.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_zero` and
  `AlgebraicGeometry.Space.PrimeDivisor.canonicalLocalRatio_zero`: the canonical ratio of the
  zero section is `0`, hence the unit it is read as is `1`.
* `AlgebraicGeometry.Space.orderOfVanishingSection_canonicalLocalRatio_zero`: every order of
  vanishing of the zero section at the canonical ratio is zero.
* `AlgebraicGeometry.Space.eq_zero_of_htriv_canonicalLocalRatioFamily` and
  `AlgebraicGeometry.Space.not_htriv_canonicalLocalRatioFamily`: **the hypothesis `htriv` of
  Stacks 0EPX, read at the canonical ratio, implies `Pic(X) = 0`**, and therefore fails on any
  such `X` with a nonzero Picard class. Constructing the ratio is not enough: `htriv` has to
  assume the section regular.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPX](https://stacks.math.columbia.edu/tag/0EPX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule
attribute [local instance] PrimeDivisor.genericStalkMeromorphicAlgebra
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The global pullback of Stacks 0ENC, part (1) carries the zero meromorphic section to the
zero meromorphic section.** It is additive, and a group homomorphism kills zero. -/
theorem pullbackMeromorphicSection_eval_zero {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (hf : PullbacksMeromorphicSections B S hS f.hom)
    (U : SmallEtale B S hS Y.1) :
    (pullbackMeromorphicSection B S hS f M hf 0).eval (op U) = 0 :=
  left_eq_add.mp
    (pullbackMeromorphicSection_eval_add B S hS f M hf 0 0 0 (fun _ => by simp) U)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (W : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

/-- **The canonical ratio of the zero section is zero.** The coefficient of the zero section
against the generator is zero, and the map into `Q(𝒪^h_{X, ξ})` is a ring homomorphism. -/
theorem PrimeDivisor.canonicalGenericRatio_zero :
    W.canonicalGenericRatio B S hS hX hdec L hL hInt hN 0 = 0 := by
  have hzero := pullbackMeromorphicSection_eval_zero B S hS
    (W.genericStalkMorphism B S hS hX hdec) L
    (W.pullbacksMeromorphicSections_genericStalkMorphism B S hS hX hdec)
    (W.genericStalkChart B S hS hX hdec)
  have h := W.canonicalGenericRatio_smul B S hS hX hdec L hL hInt hN 0 0 0
    (by rw [hzero, smul_zero])
  rwa [map_zero, zero_mul] at h

variable [∀ V : PrimeDivisor B S hS X,
  Nontrivial ↥(V.genericHenselianLocalRing B S hS hX hdec)]

/-- **The canonical ratio of the zero section is read as the unit `1`.** The ratio itself is
zero, which is not a unit of `Q(𝒪^h_{X, ξ})`, so the construction falls back on `1`. -/
theorem PrimeDivisor.canonicalLocalRatio_zero :
    W.canonicalLocalRatio B S hS hX hdec L hL hInt hN 0 = 1 := by
  refine dite_eq_right fun h => zero_ne_one (α := W.genericTotalFractionRing B S hS hX hdec) ?_
  rw [W.canonicalGenericRatio_zero B S hS hX hdec L hL hInt hN] at h
  exact isUnit_zero_iff.mp h

variable [∀ V : PrimeDivisor B S hS X,
  IsNoetherianRing ↥(V.genericHenselianLocalRing B S hS hX hdec)]
variable [∀ V : PrimeDivisor B S hS X,
  Ring.KrullDimLE 1 ↥(V.genericHenselianLocalRing B S hS hX hdec)]

/-- **Every order of vanishing of the zero section at the canonical ratio is zero**, the ratio
being read as the unit `1`. -/
theorem orderOfVanishingSection_canonicalLocalRatio_zero :
    orderOfVanishingSection.{u, u} B S hS hX hdec W L 0
      (W.canonicalLocalRatio B S hS hX hdec L hL hInt hN) = 0 :=
  orderOfVanishingSection_eq_zero_of_isUnit.{u, u} B S hS hX hdec W L 0
    (W.canonicalLocalRatio B S hS hX hdec L hL hInt hN) (v := 1) isUnit_one (by
      rw [W.canonicalLocalRatio_zero B S hS hX hdec L hL hInt hN]
      simp)

include hInt hN in
/-- **The hypothesis `htriv` of Stacks 0EPX, read at the canonical ratio `s / s_ξ` of Stacks
0EPR, implies `Pic(X) = 0`.** It is stated for an arbitrary meromorphic section, and the zero
section has all its orders of vanishing zero, so it asks that every invertible `𝒪_X`-module be
trivial. Constructing the ratio does not repair this: `htriv` has to assume the section
regular. -/
theorem eq_zero_of_htriv_canonicalLocalRatioFamily
    (htriv : ∀ (L : Modules.{u, u} B S hS X hX)
      (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (t : MeromorphicSection.{u, u} B S hS X hX L),
      (∀ V : PrimeDivisor B S hS X,
          orderOfVanishingSection.{u, u} B S hS hX hdec V L t
            (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN V) = 0) →
        picardClass (B := B) ⟨X, hX⟩ L hL = 0)
    (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) :
    x = 0 := by
  obtain ⟨N, hN', rfl⟩ := exists_picardClass (B := B) ⟨X, hX⟩ x
  exact htriv N hN' 0 fun V =>
    orderOfVanishingSection_canonicalLocalRatio_zero B S hS hX hdec V N hN' hInt hN

include hInt hN in
/-- On such an `X` with a nonzero Picard class the hypothesis `htriv` of Stacks 0EPX fails at
the canonical ratio. -/
theorem not_htriv_canonicalLocalRatioFamily
    (x : picardGroup (B := B) (S := S) (hS := hS) ⟨X, hX⟩) (hx : x ≠ 0) :
    ¬ ∀ (L : Modules.{u, u} B S hS X hX)
      (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
      (t : MeromorphicSection.{u, u} B S hS X hX L),
      (∀ V : PrimeDivisor B S hS X,
          orderOfVanishingSection.{u, u} B S hS hX hdec V L t
            (canonicalLocalRatioFamily B S hS hX hdec L hL hInt hN V) = 0) →
        picardClass (B := B) ⟨X, hX⟩ L hL = 0 :=
  fun htriv => hx (eq_zero_of_htriv_canonicalLocalRatioFamily B S hS hX hdec hInt hN htriv x)

end AlgebraicGeometry.Space

end
