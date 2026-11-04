module

public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# The Kummer class of the diagonal of a smooth relative curve

Let `f : X ⟶ S` be separated and smooth of relative dimension one and `n` invertible on
`X ×_S X`. The diagonal `Δ ⊆ X ×_S X` is an effective Cartier divisor
(`Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal`), so it has a class `[𝒪(Δ)]` in the
Picard group, and its Kummer coboundary is a class

`c_Δ = δ[𝒪(Δ)] ∈ H²(X ×_S X, μ_n)`

(`Stacks.Kummer.diagonalKummerClass`). On the fibre of the second projection over a geometric
point `x̄ : Spec Ω ⟶ X`, which is the geometric fibre `C = X_{f(x̄)}`, the diagonal cuts out the
`Ω`-point `x̄` of `C`, so the restriction of `c_Δ` is the Kummer class of a point, and for `C` a
smooth proper curve over an algebraically closed field its trace is `deg 𝒪(x̄) = 1`
(`Stacks.Kummer.smoothProperCurveTrace_diagonalKummerClass`). In particular the restriction of
`c_Δ` generates `H²(C, μ_n) ≅ ℤ/n`.

## Main definitions

* `Stacks.Kummer.diagonalKummerClass`: the class `δ[𝒪(Δ)] ∈ H²(X ×_S X, μ_n)`.
* `Stacks.Kummer.fibreDiagonalPoint`: the point `x̄` of the geometric fibre over `x̄`.

## Main results

* `Stacks.Kummer.isPullback_fibreDiagonalPoint`: the diagonal meets the geometric fibre exactly
  in that point.
* `Stacks.Kummer.diagonalIdeal_comap_fibre`: the restriction of the ideal of the diagonal to the
  geometric fibre is the ideal of the point.
* `Stacks.Kummer.smoothProperCurveTrace_diagonalKummerClass`: the trace of the restriction of
  `c_Δ` to a geometric fibre is `1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Kummer

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section Class

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {n : ℕ} (hn0 : n ≠ 0) (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤)))

/-- **The Kummer class of the diagonal** of a smooth relative curve `f : X ⟶ S`: the Kummer
coboundary `δ[𝒪(Δ)] ∈ H²(X ×_S X, μ_n)` of the class in `Pic(X ×_S X) = H¹(X ×_S X, 𝐆_m)` of
the effective Cartier divisor `Δ`. -/
def diagonalKummerClass :
    Sheaf.H.{u + 1, u + 1} (rootsOfUnitySheaf.{u, u + 1} (pullback f f) n) 2 :=
  haveI := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
  kummerδ.{u + 1, u, u + 1} (pullback f f) hn0 hY 1
    ((etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} (pullback f f)).symm
      (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f)))

/-- `c_Δ` is the Yoneda product of the class of `𝒪(Δ)` in `H¹(X ×_S X, 𝐆_m)` with the extension
class of the Kummer sequence. -/
theorem diagonalKummerClass_eq :
    haveI := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
    diagonalKummerClass f hn0 hY =
      ((etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} (pullback f f)).symm
        (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f))).comp
        (kummerSequence_shortExact.{u, u + 1} (pullback f f) hn0 hY).extClass rfl :=
  rfl

end Class

section Fibre

variable {S X : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)

/-- **The point `x̄` of the geometric fibre over `x̄`**: the fibre of the second projection
`X ×_S X ⟶ X` over `x̄ : Spec Ω ⟶ X` is `Spec Ω ×_X (X ×_S X)`, and `(x̄, x̄)` is an `Ω`-point
of it, a section of the structure morphism. -/
def fibreDiagonalPoint : Spec (.of Ω) ⟶ pullback x (pullback.snd f f) :=
  pullback.lift (𝟙 _) (x ≫ Stacks.Hilbert.diag f) (by
    rw [Category.id_comp, Category.assoc, Stacks.Hilbert.diag_snd, Category.comp_id])

/-- The point `x̄` of the geometric fibre is a section of its structure morphism. -/
@[reassoc (attr := simp)]
theorem fibreDiagonalPoint_fst : fibreDiagonalPoint f x ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The image of the point `x̄` of the geometric fibre in `X ×_S X` is `(x̄, x̄)`. -/
@[reassoc (attr := simp)]
theorem fibreDiagonalPoint_snd :
    fibreDiagonalPoint f x ≫ pullback.snd _ _ = x ≫ Stacks.Hilbert.diag f :=
  pullback.lift_snd _ _ _

/-- **The diagonal meets the geometric fibre over `x̄` exactly in the point `x̄`.** -/
theorem isPullback_fibreDiagonalPoint :
    IsPullback (fibreDiagonalPoint f x) x (pullback.snd x (pullback.snd f f))
      (Stacks.Hilbert.pointGraph (Over.mk f) (Over.mk f) (𝟙 _)) := by
  rw [Stacks.Hilbert.pointGraph_id_eq]
  have key : ∀ s : PullbackCone (pullback.snd x (pullback.snd f f)) (Stacks.Hilbert.diag f),
      s.snd = s.fst ≫ pullback.fst _ _ ≫ x := fun s => by
    have h := congrArg (fun m => m ≫ pullback.snd f f) s.condition
    simp only [Category.assoc, Stacks.Hilbert.diag_snd, Category.comp_id] at h
    rw [← h, pullback.condition]
  refine ⟨⟨fibreDiagonalPoint_snd f x⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => s.fst ≫ pullback.fst _ _) ?_ ?_ ?_⟩⟩
  · intro s
    refine pullback.hom_ext ?_ ?_
    · simp
    · rw [Category.assoc, Category.assoc, fibreDiagonalPoint_snd, s.condition, key s]
      simp only [Category.assoc]
  · intro s
    rw [Category.assoc, key s]
  · intro s m hm1 _
    rw [← hm1, Category.assoc, fibreDiagonalPoint_fst, Category.comp_id]

/-- **The restriction of the ideal of the diagonal to the geometric fibre over `x̄` is the ideal
of the point `x̄`.** -/
theorem diagonalIdeal_comap_fibre [IsSeparated f] :
    (Stacks.Hilbert.diagonalIdeal f).comap (pullback.snd x (pullback.snd f f)) =
      (fibreDiagonalPoint f x).ker := by
  have h := isPullback_fibreDiagonalPoint f x
  rw [Stacks.Hilbert.diagonalIdeal, Stacks.Hilbert.pointIdeal,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst]

/-- **The restriction of the diagonal to a geometric fibre is an effective Cartier divisor**: the
diagonal is a relative effective Cartier divisor over the second factor (Tag 056Q). -/
theorem isPullbackDefined_fibre_diagonalIdeal [IsSeparated f] [SmoothOfRelativeDimension 1 f] :
    Stacks.Divisors.IsPullbackDefined (pullback.snd x (pullback.snd f f))
      (Stacks.Hilbert.diagonalIdeal f) := by
  have hrel := Stacks.Hilbert.isRelativeEffectiveCartierDivisor_diagonalIdeal f
  have : Flat ((Stacks.Hilbert.diagonalIdeal f).subschemeι ≫ pullback.snd f f) := hrel.2
  exact AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback (pullback.snd f f) x
    (Stacks.Hilbert.diagonalIdeal f) hrel.1

/-- The point `x̄` of the geometric fibre is a closed point. -/
theorem isClosed_range_fibreDiagonalPoint :
    IsClosed (Set.range (fibreDiagonalPoint f x)) := by
  have : IsClosedImmersion (fibreDiagonalPoint f x) :=
    isClosedImmersion_of_comp_eq_id (pullback.fst x (pullback.snd f f)) _
      (fibreDiagonalPoint_fst f x)
  exact (fibreDiagonalPoint f x).isClosedEmbedding.isClosed_range

/-- The point `x̄` of the geometric fibre is the whole range of its section. -/
private theorem range_fibreDiagonalPoint (p : Spec (.of Ω)) :
    Set.range (fibreDiagonalPoint f x) = {fibreDiagonalPoint f x p} := by
  ext y
  refine ⟨fun ⟨p', hp'⟩ => ?_, fun hy => ⟨p, hy.symm⟩⟩
  rw [← hp', Subsingleton.elim p' p]
  rfl

/-- The point `x̄` of the geometric fibre, as a closed point. -/
def fibreDiagonalClosedPoint (p : Spec (.of Ω)) :
    Stacks.Zeta.ClosedPoint (pullback x (pullback.snd f f)) :=
  ⟨fibreDiagonalPoint f x p, by
    have h : Set.range (fibreDiagonalPoint f x) = {fibreDiagonalPoint f x p} := by
      ext y
      refine ⟨fun ⟨p', hp'⟩ => ?_, fun hy => ⟨p, hy.symm⟩⟩
      rw [← hp', Subsingleton.elim p' p]
      rfl
    rw [← h]
    exact isClosed_range_fibreDiagonalPoint f x⟩

/-- The ideal of the point `x̄` of the geometric fibre is the ideal of the reduced closed point. -/
theorem ker_fibreDiagonalPoint (p : Spec (.of Ω)) :
    (fibreDiagonalPoint f x).ker = Stacks.Zeta.pointIdeal (fibreDiagonalClosedPoint f x p) := by
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, Stacks.Zeta.pointIdeal]
  congr 1
  refine TopologicalSpace.Closeds.ext ?_
  change closure _ = {_}
  rw [(isClosed_range_fibreDiagonalPoint f x).closure_eq, range_fibreDiagonalPoint f x p]
  rfl

end Fibre

section Trace

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
  [IsCurve Ω (pullback.fst x (pullback.snd f f))] [Smooth (pullback.fst x (pullback.snd f f))]
  [IsProper (pullback.fst x (pullback.snd f f))]
  {n : ℕ} (hn : IsUnit (n : Ω)) (hn0 : n ≠ 0) (hY : IsUnit ((n : ℕ) : Γ(pullback f f, ⊤)))

/-- Equal effective Cartier divisors have equal classes in the Picard group. -/
theorem picardClass_congr {Z : Scheme.{u}} {D D' : Z.IdealSheafData} (h : D = D')
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsEffectiveCartierDivisor D'] :
    Stacks.Divisors.picardClass D = Stacks.Divisors.picardClass D' := by
  subst h
  rfl

/-- **The Kummer class of the diagonal restricts to a generator on every geometric fibre**: its
restriction to the fibre `C` of the second projection over `x̄ : Spec Ω ⟶ X`, `Ω` algebraically
closed, is the Kummer class of the point `x̄` of `C`, whose trace is `deg 𝒪(x̄) = 1`. -/
theorem smoothProperCurveTrace_diagonalKummerClass :
    smoothProperCurveTrace (pullback.fst x (pullback.snd f f)) hn
      (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1}
        (pullback.snd x (pullback.snd f f)) n 2 (diagonalKummerClass f hn0 hY)) = 1 := by
  have hΔ := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal f
  have hC := isUnit_globalSections (pullback.fst x (pullback.snd f f)) hn
  have hsq := Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass.{u, u + 1, u + 1}
    (pullback.snd x (pullback.snd f f)) hn0 hY 1 2 rfl
    ((etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} (pullback f f)).symm
      (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f)))
  have h1 : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1}
      (pullback.snd x (pullback.snd f f)) n 2 (diagonalKummerClass f hn0 hY) =
      kummerδ.{u + 1, u, u + 1} _ (neZero_of_isUnit hn) hC 1
        (Sheaf.H.map (multiplicativeInverseImageComparison.{u, u + 1}
          (pullback.snd x (pullback.snd f f))) 1
          (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
            (pullback.snd x (pullback.snd f f)) _ 1
            ((etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} (pullback f f)).symm
              (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f))))) := by
    rw [Stacks.EtaleCohomology.rootsOfUnityPullbackMap_apply, diagonalKummerClass_eq, hsq]
    rfl
  rw [h1, smoothProperCurveTrace_kummerδ, etaleH1MultiplicativeAddEquivPicard_naturality,
    AddEquiv.apply_symm_apply]
  have hD := isPullbackDefined_fibre_diagonalIdeal f x
  have h2 := Stacks.Zeta.schemePullbackClass_picardClass_comap (pullback.snd x (pullback.snd f f))
    (Stacks.Hilbert.diagonalIdeal f) hD
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      ((Stacks.Hilbert.diagonalIdeal f).comap (pullback.snd x (pullback.snd f f))) := hD
  have := Stacks.Zeta.isEffectiveCartierDivisor_pointIdeal (pullback.fst x (pullback.snd f f))
    (fibreDiagonalClosedPoint f x p)
  have h3 : Stacks.Divisors.picardClass
      ((Stacks.Hilbert.diagonalIdeal f).comap (pullback.snd x (pullback.snd f f))) =
      Stacks.Zeta.pointClass (pullback.fst x (pullback.snd f f)) (fibreDiagonalClosedPoint f x p) :=
    picardClass_congr ((diagonalIdeal_comap_fibre f x).trans (ker_fibreDiagonalPoint f x p))
  show ((Stacks.Picard.picardDegree (pullback.fst x (pullback.snd f f)) _
    (Stacks.Picard.schemePullbackClass (pullback.snd x (pullback.snd f f))
      (Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal f))) : ℤ) : ZMod n) = 1
  rw [h2, h3, Stacks.Zeta.picardDegree_pointClass]
  simp

end Trace

end Stacks.Kummer

end
