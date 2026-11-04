module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AffineLineGeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstFailureInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.AffineLineCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.DegreeOneLocalVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.Extension

/-!
# Smooth base change for torsion sheaves annihilated by an invertible integer

This file assembles the second proof of the smooth base change theorem (Stacks, Theorem 0EYU)
for sheaves annihilated by an integer `n` invertible on the base. Stacks 0F08 reduces `BC(f, n, q)`
for the projection of the affine line to the vanishing of `R^r h_*(ℤ/dℤ)`, `r ≥ 1`, in a
normalized diagram over an affine integral normal scheme with algebraically closed function
field; the reduction of Stacks 054L, 0EZR and 0EZS carries the affine line to every smooth
morphism.

The vanishing in degrees `r ≥ 2` is
`Stacks.EtaleCohomology.SmoothBaseChange.isZero_rightDerived_affineLine_of_two_le`; the vanishing
in degree one is the proposition `AffineLineFirstVanishing`, proved from Stacks 03SC (6) and Stacks
0EZJ as `Stacks.EtaleCohomology.SmoothBaseChange.affineLineFirstVanishing`.

## Main definitions

* `Stacks.EtaleCohomology.SmoothBaseChange.AffineLineFirstVanishing` — the vanishing of
  `R^1 h_*(ℤ/dℤ)` in a normalized diagram over the affine line.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.affineLineFirstVanishing` — the vanishing in degree
  one, from the named arguments `CurveCohomologyAlgClosedInvariance` (03SC (6)) and
  `GaloisCoversExtendFromGenericFiber` (0EZJ).
* `Stacks.EtaleCohomology.SmoothBaseChange.not_normalFailureDiagram_affineLine` — no normalized
  counterexample of Stacks 0F08 exists for the affine line.
* `Stacks.EtaleCohomology.SmoothBaseChange.baseChangeAllDegrees_of_smooth'` — `BC(f, n, q)` in
  every degree for a smooth `f` and `n` invertible on the base.

## References

* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **The vanishing of `R^1 h_*(ℤ/dℤ)` over the affine line**, in the normalized diagram of
Stacks 0F08:
```
𝔸¹_T  ←--  X'  ←-h-  Y
  |        |f'       |e
  T   ←s-  S'  ←-g-  Spec K
```
with both squares cartesian, `S'` affine, integral and normal with algebraically closed function
field, `K` algebraically closed, `Spec K ⟶ S'` dominant and `d` positive and invertible on
`S'`. This is the case `q = 1` of the second proof of Stacks 0EYU. -/
def AffineLineFirstVanishing : Prop :=
  ∀ ⦃T S' X' Y : Scheme.{u}⦄ (s : S' ⟶ T) (p : X' ⟶ 𝔸(ULift.{u} (Fin 1); T)) (f' : X' ⟶ S')
    (_ : IsPullback p f' (𝔸(ULift.{u} (Fin 1); T) ↘ T) s) [IsAffine S'] [IsIntegral S']
    (_ : IsNormalDomain Γ(S', ⊤)) [IsAlgClosed S'.functionField]
    (K : Type u) [Field K] [IsAlgClosed K] (g : Spec (.of K) ⟶ S') [IsDominant g],
    ∀ (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)), IsPullback h e f' g →
    ∀ d : ℕ, 0 < d → IsUnit ((d : ℤ) : Γ(S', ⊤)) →
      IsZero (((smallEtalePushforwardAb h).rightDerived 1).obj
        ((smallEtalePullbackAb e).obj (FirstFailureDiagram.constantZMod (Spec (.of K)) d)))

/-- **The vanishing of `R¹ h_*(ℤ/dℤ)` over the affine line**, the case `q = 1` of the second
proof of Stacks 0EYU, from Stacks 03SC (6) and Stacks 0EZJ.

`R¹ h_*(ℤ/dℤ)` is the sheafification of `V ↦ H¹(V ×_{X'} Y, ℤ/dℤ)` (Stacks 072W), so it suffices
that every class over `V ×_{X'} Y` dies on an étale covering of `V`. Read through an injective
presentation of `ℤ/dℤ`, such a class is a section of the cokernel, and it dies where that section
lifts. Around every point of `V`, after an étale refinement, `V ⟶ S'` is a smooth morphism with
geometrically connected fibres and a section over an open subscheme of `S'` (Stacks 0EY4, 09Z9);
there the class comes from the geometric generic fibre by 03SC (6), is killed by a finite étale
Galois cover of it of order dividing `d`, which extends to a finite étale cover by 0EZJ. -/
theorem affineLineFirstVanishing (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0EZJ : GaloisCoversExtendFromGenericFiber.{u}) : AffineLineFirstVanishing.{u} := by
  intro T S' X' Y s p f' hp _ _ hnorm _ K _ _ g _ h e sq d hd hdunit
  let G₀ := (smallEtalePullbackAb e).obj (FirstFailureDiagram.constantZMod (Spec (.of K)) d)
  let IP : InjectivePresentation G₀ := Classical.arbitrary _
  let Sh := ShortComplex.mk IP.f (cokernel.π IP.f) (cokernel.condition IP.f)
  have hS : Sh.ShortExact := { exact := ShortComplex.exact_cokernel IP.f }
  have : Injective Sh.X₂ := IP.injective
  let eG : Sh.X₁ ≅ FirstFailureDiagram.constantZMod Y d :=
    (smallEtalePullbackAbIsoInverseImage e).app _ ≪≫
      (etaleAbelianInverseImageConstantIso.{u, 0} e).app _
  refine
    Cohomology.SheafifiedHigherDirectImage.isZero_rightDerived_one_pushforward_of_lift.{u + 1}
      (smallEtaleBaseChange h) hS (fun V c => ?_)
  choose Z b hv i hi using fun v : V.left =>
    exists_lift_through_point h03SC6 h0EZJ hp hnorm sq hS d hd hdunit eG c v
  refine ⟨Sieve.ofArrows Z b, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun v => Set.mem_iUnion.2 ⟨v, hv v⟩
  · intro V' k hk
    obtain ⟨v, k', rfl⟩ := Sieve.ofArrows.exists hk
    refine ⟨Sh.X₂.obj.map ((smallEtaleBaseChange h).map k').op (i v), ?_⟩
    rw [NatTrans.naturality_apply, hi v, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← op_comp, ← Functor.map_comp]

/-- A sheaf all of whose sections are annihilated by a positive integer is a torsion sheaf. -/
theorem torsionSheafProperty_of_nsmul_eq_zero {C : Type*} [Category* C]
    {J : GrothendieckTopology C} (F : Sheaf J Ab.{u + 1}) {d : ℕ} (hd : 0 < d)
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), (d : ℤ) • x = 0) :
    Stacks.Torsion.torsionSheafProperty J F := by
  intro U x
  refine ⟨⊤, J.top_mem U, fun V f _ => ⟨d, hd, ?_⟩⟩
  simpa only [natCast_zsmul] using hF (op V) (F.obj.map f.op x)

/-- **No normalized counterexample of Stacks 0F08 exists for the affine line.** For `n` invertible
on `T` and `r ≥ 1`, the higher direct image `R^r h_*(ℤ/dℤ)` of a normalized diagram over
`𝔸¹_T ⟶ T` vanishes: in degree one by `AffineLineFirstVanishing`, and in degrees at least two by
Stacks 03SC, part (2). -/
theorem not_normalFailureDiagram_affineLine (h03SC2 : AffineCurveCohomologyVanishing.{u})
    (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {T : Scheme.{u}} {n : ℤ} (hn : IsUnit (n : Γ(T, ⊤)))
    (r : ℕ) (hr : 1 ≤ r) :
    ¬ FirstFailureDiagram.NormalFailureDiagram (𝔸(ULift.{u} (Fin 1); T) ↘ T) n r := by
  rintro ⟨S', X', Y, haff, hint, hnorm, hfun, s, p, f', hp, K, hK, hKcl, g, hdom, h, e, sq, d,
    hd, hnz⟩
  have hdunit : IsUnit ((d : ℤ) : Γ(S', ⊤)) := by
    obtain ⟨k, hk⟩ := hd
    refine isUnit_of_mul_isUnit_left (y := (k : Γ(S', ⊤))) ?_
    rw [← Int.cast_mul, ← hk]
    exact isUnit_intCast_of_hom s hn
  have hdpos : 0 < d := Nat.pos_of_ne_zero <| by
    rintro rfl
    simp at hdunit
  apply hnz
  obtain rfl | hr2 : r = 1 ∨ 2 ≤ r := by omega
  · exact affineLineFirstVanishing h03SC6
      (fun _ _ f _ _ _ _ _ _ _ _ σ hσ G _ _ hG Z z hz =>
        exists_finiteEtaleGaloisCover_extending_genericFiber h0BMA h0EYD f σ hσ G hG Z z hz)
      s p f' hp hnorm K g h e sq d hdpos hdunit
  · exact isZero_rightDerived_affineLine_of_two_le hp sq h03SC2 _
      (torsionSheafProperty_of_nsmul_eq_zero _ hdpos fun U x =>
        zsmul_pullbackAb_eq_zero e _ (d : ℤ)
          (FirstFailureDiagram.zsmul_constantZMod_eq_zero _ d dvd_rfl) U.unop x) r hr2

/-- **`BC(f, n, q)` in every degree for a smooth morphism**, for `n` invertible on the base: the
reduction to the affine line (Stacks 054L, 0EZR, 0EZS) and the induction on the degree (Stacks
0EYS, 0F08) over the affine line. -/
theorem baseChangeAllDegrees_of_smooth' (h0EYS : FlatReducedFibresBaseChange.{u})
    (h0EZR : EtaleLocalHigherBaseChange.{u}) (h0EZS : HigherBaseChangePaste.{u})
    (h0F08 : FirstFailureNormalization.{u}) (h03SC2 : AffineCurveCohomologyVanishing.{u})
    (h03SC6 : CurveCohomologyAlgClosedInvariance.{u})
    (h0BMA : PurityAtRegularLocalRings.{u})
    (h0EYD : ∀ S : Stacks.FundamentalGroup.CodimensionOnePullbackSetup.{u},
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne S.U.ι S.f →
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne (pullback.fst S.g S.U.ι)
        S.pulledBackCover)
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] {n : ℤ}
    (hn : IsUnit (n : Γ(S, ⊤))) : BaseChangeAllDegrees f n := by
  refine baseChangeAllDegrees_of_smooth h0EZR h0EZS (fun T hT => ?_) f hn
  have : Smooth (𝔸(ULift.{u} (Fin 1); T) ↘ T) := affineSpace_smooth_over
  exact baseChangeAllDegrees_of_not_normalFailureDiagram h0EYS h0F08 _ n
    (not_normalFailureDiagram_affineLine h03SC2 h03SC6 h0BMA h0EYD hT)

end Stacks.EtaleCohomology.SmoothBaseChange

end
