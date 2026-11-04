module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicAlgebraization.FormalObjectIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.NeighbourhoodSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceTruncations
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian

/-!
# Sections of an infinitesimal neighbourhood over a quotient of a complete local ring

Let `W` be a locally Noetherian formal algebraic space with reduction `i : W_red ⟶ W`, let
`(R, 𝔪)` be a Noetherian complete local `S`-algebra and `L ⊆ 𝔪` an ideal. The `k`-th
infinitesimal neighbourhood `W_k` of `W_red` is an algebraic space, so by Stacks 0AQH (in the
form `AlgebraicGeometry.FormalSpace.existsUnique_section_of_compatible_truncations`, applied to
the complete local ring `R/L`) a compatible family of sections of `W_k` over the truncations
`Spec((R/L)/𝔪ⁿ⁺¹)` is the restriction of a unique section over `Spec(R/L)`. This is the step
"applying Formal Spaces, Lemma 0AQH to algebraize this to a morphism `Spec(R/Iⁿ) ⟶ W_n`" of the
proof of Stacks 0GI8.

## Main results

* `Ideal.iInf_sup_maximalIdeal_pow`: every ideal of a Noetherian local ring is closed in the
  `𝔪`-adic topology (Krull).
* `IsLocalRing.map_mk_maximalIdeal`: the maximal ideal of `R/L` is the image of `𝔪`.
* `AlgebraicGeometry.FormalSpace.existsUnique_reductionNeighbourhood_quotientTruncations`: the
  statement above.

## References

* [Stacks Project, Tag 0GI8](https://stacks.math.columbia.edu/tag/0GI8)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

/-- **Krull.** In a Noetherian local ring every ideal `J` is the intersection of the ideals
`J + 𝔪ⁿ`. -/
theorem Ideal.iInf_sup_maximalIdeal_pow {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (J : Ideal R) : ⨅ n : ℕ, J ⊔ maximalIdeal R ^ n = J := by
  refine le_antisymm (fun x hx => ?_) (le_iInf fun n => le_sup_left)
  have h0 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
  have hmem : Ideal.Quotient.mk J x ∈ (⨅ i : ℕ, maximalIdeal R ^ i • ⊤ : Submodule R (R ⧸ J)) := by
    refine Submodule.mem_iInf _ |>.2 fun n => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (Submodule.mem_iInf _ |>.1 hx n)
    have : Ideal.Quotient.mk J (a + b) = b • (1 : R ⧸ J) := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, Algebra.smul_def]
      simp
    rw [this]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  rw [h0, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.1 hmem


/-- The maximal ideal of a quotient `R/L` of a local ring by an ideal `L ⊆ 𝔪` is the image of
`𝔪`. -/
theorem IsLocalRing.map_mk_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {L : Ideal R}
    [IsLocalRing (R ⧸ L)] (hL : L ≤ maximalIdeal R) :
    Ideal.map (Ideal.Quotient.mk L) (maximalIdeal R) = maximalIdeal (R ⧸ L) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) fun x hx => ?_
  · rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : R ⧸ L)
    have h : a * b - 1 ∈ L := Ideal.Quotient.eq_zero_iff_mem.1 <| by
      rw [map_sub, map_mul, hb, ← hu, Units.mul_inv, map_one, sub_self]
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2
      (by simpa using sub_mem (Ideal.mul_mem_right b _ ha) (hL h)))
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ <| (mem_maximalIdeal _).2 <| mem_nonunits_iff.2 fun ha =>
      (mem_maximalIdeal _).1 hx (ha.map _)

namespace AlgebraicGeometry.FormalSpace

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Objects

variable (hS) (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) (L : Ideal A.R)

include hA in
/-- `Spec(R/L)` lies in the site. -/
theorem contains_spec_quotientBase : B.Contains (Spec (.of (A.R ⧸ L))) :=
  contains_spec_quotient B (A.contains_spec_of_contains_truncation hA) L

/-- The structure morphism `Spec(R/L) ⟶ Spec R ⟶ S`. -/
abbrev quotientBaseStr : Spec (.of (A.R ⧸ L)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L)) ≫ A.toS

/-- `Spec(R/L)`, as an object of the site. -/
abbrev quotientBase : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj
    (quotientOver B S hS A.toS (A.contains_spec_of_contains_truncation hA) L)

/-- The closed immersion `Spec(R/L) ⟶ Spec R`. -/
abbrev quotientBaseToChart :
    quotientBase hS A hA L ⟶
      affineOver B S hS (A.contains_spec_of_contains_truncation hA) A.toS :=
  Space.quotientToAffineOver B S hS A.toS (A.contains_spec_of_contains_truncation hA) L

/-- The ideal `𝔪ⁿ⁺¹(R/L)` of the `n`-th truncation of `R/L`. -/
abbrev quotientBaseStage (n : ℕ) : Ideal (A.R ⧸ L) :=
  Ideal.map (Ideal.Quotient.mk L) (maximalIdeal A.R ^ (n + 1))

/-- The `n`-th truncation `Spec((R/L)/𝔪ⁿ⁺¹)` of `R/L`, as an object of the site. -/
abbrev quotientTruncation (n : ℕ) : BigFppfOver B S hS :=
  (BigAffineFppf.inclusion B S hS).obj (quotientOver B S hS (quotientBaseStr A L)
    (contains_spec_quotientBase A hA L) (quotientBaseStage A L n))

/-- The closed immersion `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/L)`. -/
abbrev quotientTruncationι (n : ℕ) : quotientTruncation hS A hA L n ⟶ quotientBase hS A hA L :=
  Space.quotientToAffineOver B S hS (quotientBaseStr A L) (contains_spec_quotientBase A hA L)
    (quotientBaseStage A L n)

/-- `𝔪ⁿ⁺²(R/L) ⊆ 𝔪ⁿ⁺¹(R/L)`. -/
theorem quotientBaseStage_succ_le (n : ℕ) :
    quotientBaseStage A L (n + 1) ≤ quotientBaseStage A L n :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))

/-- The closed immersion between successive truncations of `R/L`. -/
abbrev quotientTruncationSucc (n : ℕ) :
    quotientTruncation hS A hA L n ⟶ quotientTruncation hS A hA L (n + 1) :=
  (BigAffineFppf.inclusion B S hS).map (quotientOverTransition B S hS (quotientBaseStr A L)
    (contains_spec_quotientBase A hA L) (quotientBaseStage_succ_le A L n))

/-- The closed immersions `Spec((R/L)/𝔪ⁿ⁺¹) ⟶ Spec(R/L)` commute with the transition maps
between successive truncations. -/
theorem quotientTruncationSucc_comp_ι (n : ℕ) :
    quotientTruncationSucc hS A hA L n ≫ quotientTruncationι hS A hA L (n + 1) =
      quotientTruncationι hS A hA L n :=
  Space.quotientOverTransition_comp_quotientToAffineOver B S hS _ _ _

end Objects

variable {W Wred : FppfSheaf B S hS} {i : Wred ⟶ W}

/-- **Sections of `W_j` over `Spec(R/L)` are determined by, and exist for, compatible families on
the truncations `Spec((R/L)/𝔪ⁿ⁺¹)`** (Stacks 0AQH for the algebraic space `W_j`). -/
theorem existsUnique_reductionNeighbourhood_quotientTruncations
    (hW : IsLocallyNoetherian B S hS W) (hred : IsReduction B S hS W Wred i)
    (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) {L : Ideal A.R}
    (hL : L ≤ maximalIdeal A.R) (j : ℕ)
    (z : ∀ n, (reductionNeighbourhood i j).toFunctor.obj (op (quotientTruncation hS A hA L n)))
    (hz : ∀ n, (reductionNeighbourhood i j).toFunctor.map (quotientTruncationSucc hS A hA L n).op
      (z (n + 1)) = z n) :
    ∃! y : (reductionNeighbourhood i j).toFunctor.obj (op (quotientBase hS A hA L)),
      ∀ n, (reductionNeighbourhood i j).toFunctor.map (quotientTruncationι hS A hA L n).op y =
        z n := by
  classical
  have hR : IsNoetherianCompleteLocalRing A.R := ⟨A.noetherian, inferInstance, A.complete⟩
  have hRL := quotient_isNoetherianCompleteLocalRing hR L
    (fun h => (maximalIdeal.isMaximal A.R).ne_top (top_le_iff.1 (h ▸ hL)))
  let : IsLocalRing (A.R ⧸ L) := hRL.isLocal
  have hmax := IsLocalRing.map_mk_maximalIdeal hL
  have hJ : ∀ n, quotientBaseStage A L n = maximalIdeal (A.R ⧸ L) ^ (n + 1) := fun n => by
    rw [quotientBaseStage, Ideal.map_pow, hmax]
  obtain ⟨F', hF', ⟨e⟩⟩ := Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS
    (isAlgebraicSpaceULift_reductionNeighbourhood hW hred j)
  let x : ∀ n, F'.obj (op (quotientTruncation hS A hA L n)) := fun n => (e.inv.app _ (z n)).down
  have hinv : ∀ {U V : BigFppfOver B S hS} (g : U ⟶ V) a,
      F'.map g.op (e.inv.app (op V) a).down =
        (e.inv.app (op U) ((reductionNeighbourhood i j).toFunctor.map g.op a)).down :=
    fun g a => by exact (congrArg ULift.down (e.inv.naturality_apply g.op a)).symm
  have hx : ∀ n, F'.map (quotientTruncationSucc hS A hA L n).op (x (n + 1)) = x n := fun n =>
    (hinv _ _).trans (by rw [hz n])
  obtain ⟨y', hy', huniq⟩ := existsUnique_section_of_compatible_truncations hRL
    (quotientBaseStage A L)
    (fun n => (hJ n).le.trans (Ideal.pow_le_self (Nat.succ_ne_zero n)))
    (fun n => quotientBaseStage_succ_le A L n)
    (fun n => ⟨n + 1, (hJ n).ge⟩)
    (fun k => ⟨k, (hJ k).le.trans (Ideal.pow_le_pow_right (Nat.le_succ k))⟩)
    hF' (quotientBase hS A hA L) (Iso.refl _) (quotientTruncation hS A hA L) (fun _ => Iso.refl _)
    (quotientTruncationι hS A hA L)
    (fun n => by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
    (quotientTruncationSucc hS A hA L) (quotientTruncationSucc_comp_ι hS A hA L) x hx
  have hnat : ∀ {U V : BigFppfOver B S hS} (g : U ⟶ V) (a : F'.obj (op V)),
      e.hom.app (op U) (ULift.up (F'.map g.op a) : ULift.{u + 1} (F'.obj (op U))) =
        (reductionNeighbourhood i j).toFunctor.map g.op
          (e.hom.app (op V) (ULift.up a : ULift.{u + 1} (F'.obj (op V)))) :=
    fun g a => e.hom.naturality_apply g.op (ULift.up a : ULift.{u + 1} (F'.obj _))
  refine ⟨e.hom.app _ (ULift.up.{u + 1} y'), fun n => ?_, fun y₂ hy₂ => ?_⟩
  · rw [← hnat, hy' n]
    exact (e.app _).inv_hom_id_apply _
  · rw [← huniq (e.inv.app _ y₂).down fun n => (hinv _ _).trans (by rw [hy₂ n])]
    exact ((e.app _).inv_hom_id_apply _).symm

end AlgebraicGeometry.FormalSpace

end
