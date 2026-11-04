module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting

/-!
# Stacks 0FBY for a fundamental class, through any class characterized by the rule of Stacks 0B78

The statements of `StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting`, made for an
arbitrary bivariant class `φ ∈ A^{-d}(X ×_S Z ⟶ Z)` with `Stacks.Chow.IsBivariantFlatPullback φ`
for the base change `pr_Z : X ×_S Z ⟶ Z` of the structure morphism of `X`, in place of the class
`Stacks.Chow.flatPullbackBivariantClass` built from Stacks 02RG and 0B71. The proofs use only the
cap operation of `φ`, so they apply in particular to
`Stacks.Chow.flatPullbackBivariantClassOfInvertible`, over the Gysin system of an invertible
module, where `φ` exists with nothing assumed.

## Main results

* `Stacks.Chow.isBivariantFlatPullback_snd_cap_heq_chowExteriorProduct`,
  `Stacks.Chow.isBivariantFlatPullback_snd_cap_id_heq_exteriorProductOnTarget` — clause (1) of
  Stacks 0B0R: `φ` caps as the exterior product with `[X]`.
* `Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass_of_isBivariantFlatPullback` —
  **Stacks 0FBY** for the fundamental class of an integral scheme flat over the base:
  `[X] × (c ∩ β) = c ∩ ([X] × β)`.

## References

* [Stacks Project, Tag 0FBY](https://stacks.math.columbia.edu/tag/0FBY)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Main

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX]
  [IsIntegral X] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (u : Y ⟶ Z) [LocallyOfFiniteType u]
  (p : ℤ) (d : ℕ) (hfp : FlatPullbackDescends C) (m : ℤ)

/-- **Clause (1) of Stacks 0B0R for the base change of `X` to `Z`.** Let the base be the spectrum
of a field, let `X` be integral and flat over it of relative dimension `d`, and let
`pr_Z : X ×_S Z ⟶ Z` be the base change of the structure morphism of `X` along `sZ`. The
class `φ` characterized by the rule of **Stacks 0B78** for `pr_Z`, an element of
`A^{-d}(X ×_S Z ⟶ Z)`, caps at a
test scheme `g : T ⟶ Z` as the exterior product with the fundamental class `[X]`:

  `c ∩ γ = [X] × γ`   in   `CH_{d+k}(X ×_S T)`,

the class on the left living a priori on `(X ×_S Z) ×_Z T` and being read on `X ×_S T` through
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`.

The cap operation is a flat pullback along the base change `(X ×_S Z) ×_Z T ⟶ T` of `pr_Z`, by
`Stacks.Chow.IsBivariantFlatPullback.cap_heq`; that morphism is the base change `X ×_S T ⟶ T` of
the structure morphism of `X` read on another presentation of the same fibre product, so the two
flat pullbacks agree by the isomorphism case of Stacks 02RG,
`Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`; and the latter flat pullback is the exterior
product with `[X]` by
`Stacks.Chow.chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct`. -/
theorem isBivariantFlatPullback_snd_cap_heq_chowExteriorProduct {T : Scheme.{u}} (g : T ⟶ Z)
    [LocallyOfFiniteType g] (k : ℤ) (γ : chowGroup C (g ≫ sZ) k)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    {φ : BivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl (-(d : ℤ))}
    (hφ : IsBivariantFlatPullback C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
      (relativeDimension_pullbackSnd sX hfr sZ) hfp φ) :
    chowPushforwardOfIso C (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ))
        (pullback.fst sX (g ≫ sZ) ≫ sX) (pullbackLeftPullbackSndIso sX sZ g).hom
        (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ g) (k - -(d : ℤ))
        (φ.cap g k γ) ≍
      chowExteriorProduct C hδ sX (g ≫ sZ) (d : ℤ) k
        (TensorProduct.tmul ℤ (fundamentalChowClass C sX (d : ℤ)) γ) := by
  have hcap := hφ.cap_heq g k γ
  have hsq : pullback.snd (pullback.snd sX sZ) g ≫ 𝟙 T =
      (pullbackLeftPullbackSndIso sX sZ g).hom ≫ pullback.snd sX (g ≫ sZ) := by
    simp
  have hiso := flatPullbackChow_chowPushforwardOfIso C (g ≫ sZ)
    (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ)) (g ≫ sZ)
    (pullback.fst sX (g ≫ sZ) ≫ sX) (𝟙 T) (Category.id_comp (g ≫ sZ))
    (pullbackLeftPullbackSndIso sX sZ g).hom
    (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ g)
    (pullback.snd (pullback.snd sX sZ) g) (pullbackSnd_comp_structureMorphism rfl g)
    (pullback.snd sX (g ≫ sZ)) pullback.condition.symm hsq d
    (relativeDimension_pullbackSnd (pullback.snd sX sZ) (relativeDimension_pullbackSnd sX hfr sZ) g)
    (relativeDimension_pullbackSnd sX hfr (g ≫ sZ)) k (hfp _ _ _ _ d _ k) (hfp _ _ _ _ d _ k) γ
  rw [chowPushforwardOfIso_id] at hiso
  have hprod := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX (g ≫ sZ)
    d (relativeDimension_pullbackSnd sX hfr (g ≫ sZ)) hd k
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_descends C hfp sX
      (g ≫ sZ) k)
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_descends C hfp
      (g ≫ sZ) sX (d : ℤ))
    (hfp _ _ _ _ d _ k) γ
  refine HEq.trans (chowPushforwardOfIso_heq_congr C
    (pullback.fst (pullback.snd sX sZ) g ≫ (pullback.snd sX sZ ≫ sZ))
    (pullback.fst sX (g ≫ sZ) ≫ sX) (pullbackLeftPullbackSndIso sX sZ g).hom
    (pullbackLeftPullbackSndIso_hom_comp_structureMorphism sX sZ g)
    (by ring : k - -(d : ℤ) = k + (d : ℤ)) _ _ hcap) ?_
  rw [← hiso, ← hprod]
  exact (chowGroupDegreeEquiv_heq C (pullback.fst sX (g ≫ sZ) ≫ sX) (add_comm k (d : ℤ)) _).symm

/-- **Clause (1) of Stacks 0B0R at the identity test scheme, collapsed.** The cap product of the
flat-pullback class of Stacks 0B78 for `pr_Z : X ×_S Z ⟶ Z` against `β ∈ CH_m(Z)` at the test
scheme `𝟙 Z`, a class on `(X ×_S Z) ×_Z Z`, is the exterior product `[X] × β` once that fibre
product is collapsed onto `X ×_S Z`.

This is the same statement as
`Stacks.Chow.isBivariantFlatPullback_snd_cap_heq_chowExteriorProduct` for `g = 𝟙 Z`, except that
the collapse is read as the identification `(X ×_S Z) ×_Z Z ≅ X ×_S Z` rather than as
`(X ×_S Z) ×_Z Z ≅ X ×_S (Z ×_Z Z)`; the right-hand side is therefore
`Stacks.Chow.exteriorProductOnTarget`, the exterior product presented on the structure morphism of
`X ×_S Z` that makes it a test scheme over `Z`, which is the presentation
`Stacks.Chow.capExteriorProduct` consumes. -/
theorem isBivariantFlatPullback_snd_cap_id_heq_exteriorProductOnTarget (β : chowGroup C sZ m)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    {φ : BivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl (-(d : ℤ))}
    (hφ : IsBivariantFlatPullback C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
      (relativeDimension_pullbackSnd sX hfr sZ) hfp φ) :
    chowPushforwardOfIso C
        (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
        (pullback.snd sX sZ ≫ sZ) (pullbackIdIso (pullback.snd sX sZ)).inv
        (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ))
        (m - -(d : ℤ))
        (φ.cap (𝟙 Z) m
          (chowGroupCongr C (Category.id_comp sZ).symm m β)) ≍
      exteriorProductOnTarget C hδ sX sZ (d : ℤ) m
        (fundamentalChowClass C sX (d : ℤ)) β := by
  have hrelZ : AlgebraicGeometry.RelativeDimension (pullback.snd sX sZ) d :=
    relativeDimension_pullbackSnd sX hfr sZ
  have hcap := hφ.cap_heq (𝟙 Z) m
    (chowGroupCongr C (Category.id_comp sZ).symm m β)
  have hcollapse : (pullbackIdIso (pullback.snd sX sZ)).inv ≫ (pullback.fst sX sZ ≫ sX) =
      pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ) := by
    rw [pullbackIdIso_inv_comp, pullback.condition]
  have hsq : pullback.snd (pullback.snd sX sZ) (𝟙 Z) ≫ 𝟙 Z =
      (pullbackIdIso (pullback.snd sX sZ)).inv ≫ pullback.snd sX sZ := by
    rw [pullbackIdIso_inv_comp, ← pullback.condition]
  have hiso := flatPullbackChow_chowPushforwardOfIso C (𝟙 Z ≫ sZ)
    (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ)) sZ
    (pullback.fst sX sZ ≫ sX) (𝟙 Z) rfl (pullbackIdIso (pullback.snd sX sZ)).inv hcollapse
    (pullback.snd (pullback.snd sX sZ) (𝟙 Z)) (pullbackSnd_comp_structureMorphism rfl (𝟙 Z))
    (pullback.snd sX sZ) pullback.condition.symm hsq d
    (relativeDimension_pullbackSnd (pullback.snd sX sZ) hrelZ (𝟙 Z)) hrelZ m
    (hfp _ _ _ _ d _ m) (hfp _ _ _ _ d _ m) (chowGroupCongr C (Category.id_comp sZ).symm m β)
  rw [chowPushforwardOfIso_chowGroupCongr_source C sZ (Category.id_comp sZ).symm (𝟙 Z)
      (Category.id_comp sZ) rfl m β, chowPushforwardOfIso_id] at hiso
  have hprod := chowGroupDegreeEquiv_flatPullbackChowSnd_eq_chowExteriorProduct C hδ sX sZ d
    hrelZ hd m
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_descends C hfp sX sZ m)
    (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_descends C hfp sZ sX
      (d : ℤ))
    (hfp _ _ _ _ d _ m) β
  refine HEq.trans (chowPushforwardOfIso_heq_congr C
    (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
    (pullback.snd sX sZ ≫ sZ) (pullbackIdIso (pullback.snd sX sZ)).inv
    (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ))
    (by ring : m - -(d : ℤ) = m + (d : ℤ)) _ _ hcap) ?_
  rw [← chowGroupCongr_chowPushforwardOfIso_target C
      (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ (pullback.snd sX sZ ≫ sZ))
      (pullback.condition (f := sX) (g := sZ)) (pullbackIdIso (pullback.snd sX sZ)).inv hcollapse
      (pullbackIdIso_inv_comp (pullback.snd sX sZ) (pullback.snd sX sZ ≫ sZ)) (m + (d : ℤ)) _,
    ← hiso]
  refine HEq.trans (chowGroupCongr_heq C (pullback.condition (f := sX) (g := sZ))
    (m + (d : ℤ)) _) ?_
  refine HEq.trans (chowGroupDegreeEquiv_heq C (pullback.fst sX sZ ≫ sX)
    (add_comm m (d : ℤ)) _).symm ?_
  rw [hprod]
  exact (chowGroupCongr_heq C (pullback.condition (f := sX) (g := sZ)) ((d : ℤ) + m) _).symm

include hfp in
/-- **Stacks 0FBY for a fundamental class**, in the case in which the structure morphism of `Y` is
presented as `u ≫ sZ`.

This is the whole content; the general statement
`Stacks.Chow.commutesExteriorProductCapAt_fundamentalChowClass` follows by substituting the
equality `u ≫ sZ = sY`, which is what makes `c` a class for `u` in the indices
`Stacks.Chow.BivariantCommute` consumes. -/
private theorem commutesExteriorProductCapAt_fundamentalChowClass_comp_of_isBivariantFlatPullback
    (c : BivariantClass C G (u ≫ sZ) sZ u rfl p) (β : chowGroup C sZ m)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    {φ : BivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl (-(d : ℤ))}
    (hφ : IsBivariantFlatPullback C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
      (relativeDimension_pullbackSnd sX hfr sZ) hfp φ) :
    exteriorProductCap C hδ G sX (u ≫ sZ) sZ u rfl p c (d : ℤ) m
        (fundamentalChowClass C sX (d : ℤ)) β =
      capExteriorProduct C hδ G sX (u ≫ sZ) sZ u rfl p c (d : ℤ) m
        (fundamentalChowClass C sX (d : ℤ)) β := by
  have hcomm := bivariantCommute_of_isBivariantFlatPullback C G sZ (pullback.snd sX sZ) u d
    (relativeDimension_pullbackSnd sX hfr sZ) hfp p c φ hφ (𝟙 Z) m
    (chowGroupCongr C (Category.id_comp sZ).symm m β)
  have key := congrArg (chowPushforwardOfIso C
    (pullback.fst u (pullback.fst (pullback.snd sX sZ) (𝟙 Z) ≫ pullback.snd sX sZ) ≫ (u ≫ sZ))
    (pullback.fst sX (u ≫ sZ) ≫ sX) (iteratedExteriorCapIso sX sZ u)
    (iteratedExteriorCapIso_comp_structureMorphism sX sZ u) ((m - p) - -(d : ℤ))) hcomm
  have hprod := isBivariantFlatPullback_snd_cap_heq_chowExteriorProduct C hδ G sX sZ d hfp u
    (m - p) (c.capTarget C G (u ≫ sZ) sZ u rfl p m β) hfr hd hφ
  have hfst := iteratedExteriorCapIso_bivariantIteratedCap_fst C G sX sZ u p (-(d : ℤ)) m
    φ c β
  have hsnd := iteratedExteriorCapIso_bivariantIteratedCap_snd C G sX sZ u p (-(d : ℤ)) m
    φ c β
  have hcollapse := BivariantClass.cap_heq_congr c (pullback.snd sX sZ)
    (by ring : m - -(d : ℤ) = (d : ℤ) + m) _ _
    (isBivariantFlatPullback_snd_cap_id_heq_exteriorProductOnTarget C hδ G sX sZ d hfp m β hfr
      hd hφ)
  have hpush := chowPushforwardOfIso_heq_congr C
    (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (pullback.fst sX (u ≫ sZ) ≫ sX)
    (exteriorCapIso sX sZ u rfl).hom (exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl)
    (by ring : (m - -(d : ℤ)) - p = ((d : ℤ) + m) - p) _ _ hcollapse
  have htarget := chowPushforwardOfIso_heq_congr C
    (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ)) (pullback.fst sX (u ≫ sZ) ≫ sX)
    (exteriorCapIso sX sZ u rfl).hom (exteriorCapIso_hom_comp_structureMorphism sX sZ u rfl)
    (by ring : (d : ℤ) + (m - p) = ((d : ℤ) + m) - p) _ _
    (chowGroupDegreeEquiv_heq C (pullback.fst u (pullback.snd sX sZ) ≫ (u ≫ sZ))
      (by omega : (d : ℤ) + m - p = (d : ℤ) + (m - p))
      (c.cap (pullback.snd sX sZ) ((d : ℤ) + m)
        (exteriorProductOnTarget C hδ sX sZ (d : ℤ) m
          (fundamentalChowClass C sX (d : ℤ)) β)))
  exact eq_of_heq (hprod.symm.trans ((heq_of_eq (hfst.symm.trans key)).trans
    (hsnd.trans (hpush.trans htarget.symm))))

end Main

section Statement

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
  (G : GysinSystem C) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX]
  [IsIntegral X] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (u : Y ⟶ Z) [LocallyOfFiniteType u] (hu : u ≫ sZ = sY) (p : ℤ) (d : ℕ)
  (hfp : FlatPullbackDescends C) (m : ℤ)

include hfp in
/-- **Stacks 0FBY for the fundamental class of an integral scheme flat over the base.** Let the
base be the spectrum of a field, let `X` be integral and flat over it of relative dimension `d`,
let `u : Y ⟶ Z` be a morphism of schemes locally of finite type over the base and let
`c ∈ A^p(Y ⟶ Z)` be a bivariant class. Then for every `β ∈ CH_m(Z)`

  `[X] × (c ∩ β) = c ∩ ([X] × β)`

in `CH_{d + (m - p)}(X ×_S Y)`, where `[X] ∈ CH_d(X)` is the fundamental class of `X` and the two
sides are read through the canonical identifications of `Stacks.Chow.exteriorProductCap` and
`Stacks.Chow.capExteriorProduct`.

The first variable is a fundamental class and not a general `α ∈ CH_n(X)`; see the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting` for what the general
case needs and for why it is unavailable here.

The proof replaces `[X] × -` by the cap operation of the flat-pullback class of Stacks 0B78 for
the structure morphism of `X`, whose base change to `Z` is the flat-pullback class for
`pr_Z : X ×_S Z ⟶ Z`, and that class commutes with `c` by the smooth half of Stacks 0FF6. The
commuting identity is then instantiated at the test scheme `𝟙 Z` and both of its sides are
transported to `X ×_S Y`. -/
theorem commutesExteriorProductCapAt_fundamentalChowClass_of_isBivariantFlatPullback
    (c : BivariantClass C G sY sZ u hu p)
    (hfr : AlgebraicGeometry.RelativeDimension sX d)
    (hd : relativeDimension C.dimensionFunction sX (genericPoint X) = (d : ℤ))
    {φ : BivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl (-(d : ℤ))}
    (hφ : IsBivariantFlatPullback C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl d
      (relativeDimension_pullbackSnd sX hfr sZ) hfp φ) :
    CommutesExteriorProductCapAt C hδ G sX sY sZ u hu p c (d : ℤ) m
      (fundamentalChowClass C sX (d : ℤ)) := by
  subst hu
  intro β
  exact commutesExteriorProductCapAt_fundamentalChowClass_comp_of_isBivariantFlatPullback C hδ G sX
    sZ u p d hfp m c β hfr hd hφ

end Statement

end Stacks.Chow

end
