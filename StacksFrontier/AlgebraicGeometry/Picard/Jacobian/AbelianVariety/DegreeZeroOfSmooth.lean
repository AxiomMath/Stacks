module

public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.AbelMap
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.AbelMapCriterion
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.ChartTranslates
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.DegreeSurjective

/-!
# The degree-zero part of a smooth Picard scheme of a curve is an abelian variety of dimension `g`

Let `X` be a smooth projective curve of genus `g` over an algebraically closed field `k`, let `P`
represent its Picard functor, with the group law `Stacks.PicardFunctor.representingGrpObj`, and
let `H₀ ⊆ P` be an open subgroup scheme whose `k`-points are the classes of degree zero. Granted
that `H₀` is smooth of relative dimension `g` over `k`, it is an abelian variety of dimension
`g`. This is the Abel-map half of the proof of [Stacks, Tag 0BA0]:

* the Hilbert scheme `Hilb^g_{X/k}` is proper and irreducible (c20-mc's
  `Stacks.Hilbert.isProper_smooth_irreducible_dim_of_represents`, [Stacks, Tag 0B9I]);
* the Abel map `γ_g : Hilb^g_{X/k} ⟶ P`, followed by right translation by the inverse of the
  `k`-point `γ_g(D₀)` of a divisor `D₀` of degree `g`, sends `D₀` to the identity, so lands in
  `H₀` (which is open and closed);
* every `k`-point of `H₀` is hit: a class `L` of degree zero gives `L + [D₀]` of degree `g`, which
  is `[𝒪(D)]` for an effective divisor `D` of degree `g` by Riemann-Roch;
* `AlgebraicGeometry.OpenSubgroupScheme.isAbelianVariety_carrier_of_closedPoints` concludes.

## Main results

* `Stacks.PicardFunctor.isAbelianVariety_and_dimension_eq_genus_of_smoothOfRelativeDimension`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable {B : BigFppfSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}
  (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  {g : B.obj hX ⟶ B.obj hk} [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]

/-- The `k`-point of the representing scheme attached to a morphism from the terminal test
scheme, read on underlying schemes: it is the underlying morphism of schemes of that morphism. -/
theorem left_toMul_ofSchemeAddEquivRepresentingPoints {P : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk g).RepresentableBy P) (t : terminalTest B hk ⟶ P) :
    letI := representingGrpObj R
    (Additive.toMul (ofSchemeAddEquivRepresentingPoints k g R
      ((ofSchemeAddEquivPicardFunctorOfCurve B hX k g).symm (R.homEquiv t)))).left =
        ((BigFppfOver.toOver B (Spec (.of k)) hk).map t).left := by
  let := representingGrpObj R
  simp only [ofSchemeAddEquivRepresentingPoints, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  set q := (representingPointsAddEquiv R).symm (R.homEquiv t)
  have h1 : representingPointsAddEquiv R q = R.homEquiv t := AddEquiv.apply_symm_apply _ _
  have h2 : R.homEquiv ((fullyFaithfulToOver B hk).preimage
      ((Over.homMk (𝟙 _) (by
        change 𝟙 (Spec (.of k)) ≫ 𝟙 (Spec (.of k)) = B.inclusion.map (𝟙 (B.obj hk))
        rw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl) :
        (BigFppfOver.toOver B (Spec (.of k)) hk).obj (terminalTest B hk) ⟶
          𝟙_ (Over (Spec (.of k)))) ≫ q.toMul)) = R.homEquiv t := h1
  have h3 := congrArg (fun s => ((BigFppfOver.toOver B (Spec (.of k)) hk).map s).left)
    (R.homEquiv.injective h2)
  simp only [Functor.FullyFaithful.map_preimage, Over.comp_left] at h3
  exact h3

/-- **Stacks Project, Tag 0BA0, the degree-zero component, granted smoothness of the Picard
scheme.** Let `X` be a smooth projective curve of genus `g` over an algebraically closed field
`k`, `P` a scheme of the big fppf site representing its Picard functor, with the group law of
`Stacks.PicardFunctor.representingGrpObj`, and `H₀` an open subgroup scheme of it, smooth of
relative dimension `g` over `k`, whose `k`-points are exactly the classes of degree zero. Let `Hb`
represent `Hilb^g_{X/k}`, the Hilbert functors of all degrees being representable. Then `H₀` is
an abelian variety of dimension `g`. -/
theorem isAbelianVariety_and_dimension_eq_genus_of_smoothOfRelativeDimension
    {P Hb : BigFppfOver B (Spec (.of k)) hk} (R : (picardFunctor B hX hk g).RepresentableBy P)
    (hall : ∀ e : ℕ, ∃ H : Over (Spec (.of k)),
      Nonempty (Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g)) H e))
    (hHb : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map g))
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb) (genus (B.inclusion.map g)))
    (hdim : topologicalKrullDim X ≤ 1)
    (H₀ : letI := representingGrpObj R
      OpenSubgroupScheme (Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P)))
    (hH₀ : letI := representingGrpObj R
      ∀ x : 𝟙_ (Over (Spec (.of k))) ⟶ (BigFppfOver.toOver B (Spec (.of k)) hk).obj P,
        (∃ y, y ≫ H₀.ι.hom.hom = x) ↔
          Stacks.Picard.ofSchemeDegree k (B.inclusion.map g) hdim
            ((ofSchemeAddEquivRepresentingPoints k g R).symm (Additive.ofMul x)) = 0)
    (hsmooth : SmoothOfRelativeDimension (genus (B.inclusion.map g)) H₀.carrier.X.hom) :
    IsAbelianVariety k H₀.carrier.X ∧
      Stacks.Groupoids.abelianVarietyDimension H₀.carrier.X = genus (B.inclusion.map g) := by
  let := representingGrpObj R
  set f := B.inclusion.map g
  let G : Grp (Over (Spec (.of k))) := Grp.mk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj P)
  set abel := abelMap R hHb
  set e := ofSchemeAddEquivPicardFunctorOfCurve B hX k g
  set ψ := ofSchemeAddEquivRepresentingPoints k g R
  have : IsProper f := inferInstance
  obtain ⟨hprop, -, hirr, -, -⟩ :=
    Stacks.Hilbert.isProper_smooth_irreducible_dim_of_represents f hall hHb
  have : SmoothOfRelativeDimension (genus f) H₀.carrier.X.hom := hsmooth
  have := hprop
  have := hirr
  -- a divisor `D₀` of degree `g`
  obtain ⟨c₀, hc₀⟩ : ∃ c : Stacks.Picard.ofScheme X,
      Stacks.Picard.ofSchemeDegree k f hdim c = (genus f : ℤ) :=
    Stacks.Picard.surjective_ofSchemeDegree k f hdim (genus f : ℤ)
  obtain ⟨D₀, hD₀⟩ := exists_comp_abelMap_eq R hHb hdim le_rfl c₀ hc₀
  set y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ G.X := Additive.toMul (ψ c₀)
  have hy₀ : y₀.left = ((BigFppfOver.toOver B (Spec (.of k)) hk).map (D₀ ≫ abel)).left := by
    rw [← left_toMul_ofSchemeAddEquivRepresentingPoints k R (D₀ ≫ abel), hD₀]
  -- the translated Abel map
  set τ := rightTranslationIso G (y₀ ≫ GrpObj.inv)
  set a : ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb).left ⟶ G.X.left :=
    ((BigFppfOver.toOver B (Spec (.of k)) hk).map abel ≫ τ.hom).left
  have ha : a ≫ G.X.hom = ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb).hom :=
    Over.w ((BigFppfOver.toOver B (Spec (.of k)) hk).map abel ≫ τ.hom)
  -- right translation on rational points
  have htrans : ∀ p : 𝟙_ (Over (Spec (.of k))) ⟶ G.X, p ≫ τ.hom = p * y₀⁻¹ := by
    intro p
    simp [τ, rightTranslationIso, GrpObj.mulRight, comp_lift_assoc, Hom.mul_def, Hom.inv_def]
  -- the point of `Hb` over a morphism from the terminal test scheme
  set pt : (terminalTest B hk ⟶ Hb) → ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb).left :=
    fun D => ((BigFppfOver.toOver B (Spec (.of k)) hk).map D).left (IsLocalRing.closedPoint k)
  have hpt : ∀ (D : terminalTest B hk ⟶ Hb),
      a (pt D) = ((Additive.toMul (ψ (e.symm (R.homEquiv (D ≫ abel))))) * y₀⁻¹).left
        (IsLocalRing.closedPoint k) := by
    intro D
    have h : ((Additive.toMul (ψ (e.symm (R.homEquiv (D ≫ abel))))) ≫ τ.hom).left =
        ((BigFppfOver.toOver B (Spec (.of k)) hk).map D).left ≫ a := by
      rw [Over.comp_left, left_toMul_ofSchemeAddEquivRepresentingPoints k R (D ≫ abel),
        Functor.map_comp, Over.comp_left]
      exact Category.assoc _ _ _
    rw [← htrans, h]
    rfl
  have hconn : ConnectedSpace ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb).left :=
    @IrreducibleSpace.connectedSpace _ _ hirr
  refine @OpenSubgroupScheme.isAbelianVariety_carrier_of_closedPoints k _ G H₀ (genus f)
    hsmooth _ hconn ((BigFppfOver.toOver B (Spec (.of k)) hk).obj Hb).hom hprop a ha
    (pt D₀) ?_ ?_
  · -- `D₀` goes to the identity
    rw [hpt, hD₀, _root_.mul_inv_cancel]
    refine ⟨((η[H₀.carrier.X] : 𝟙_ (Over (Spec (.of k))) ⟶ H₀.carrier.X)).left
      (IsLocalRing.closedPoint k), ?_⟩
    have h1 : (η[H₀.carrier.X] : 𝟙_ (Over (Spec (.of k))) ⟶ H₀.carrier.X) ≫ H₀.ι.hom.hom =
        (1 : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) := by
      rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    exact congrArg (fun φ => φ.left (IsLocalRing.closedPoint k)) h1
  · -- every closed point of `H₀` is hit
    intro y hy
    have : Smooth H₀.carrier.X.hom := SmoothOfRelativeDimension.smooth (genus f) _
    set x := pointOfClosedPoint H₀.carrier.X.hom y hy
    set xO : 𝟙_ (Over (Spec (.of k))) ⟶ H₀.carrier.X :=
      Over.homMk x (pointOfClosedPoint_comp H₀.carrier.X.hom y hy)
    set x' := xO ≫ H₀.ι.hom.hom
    have hdeg := (hH₀ x').1 ⟨xO, rfl⟩
    obtain ⟨D, hD⟩ := exists_comp_abelMap_eq R hHb hdim le_rfl
      (ψ.symm (Additive.ofMul x') + c₀) (by rw [map_add, hdeg, hc₀, zero_add])
    refine ⟨pt D, ?_⟩
    rw [hpt, hD, map_add, AddEquiv.apply_symm_apply]
    change (x' * y₀ * y₀⁻¹).left _ = _
    rw [_root_.mul_inv_cancel_right]
    change (H₀.ι.hom.hom.left) (x (IsLocalRing.closedPoint k)) = _
    exact congrArg _ (pointOfClosedPoint_apply H₀.carrier.X.hom y hy _)

end Stacks.PicardFunctor

end
