module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.FiniteType
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ZeroSchemeVanishing
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinateChart
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorTrivialization

/-!
# The two-variable chart of the ambient space of Tag 0F97

Let `Y` be a scheme and let `L₁`, `L₂` be invertible `𝒪_Y`-modules. The ambient space of
[Stacks, Tag 0F97] is the fibre product `T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` of the two line
bundles of [Stacks, Tag 01M2], with structure morphism `q : T ⟶ Y`; it carries the two fibre
coordinates `z₁` and `z₂`, global sections of `q^*L₁` and `q^*L₂`. This file produces the
**affine chart in two variables** of the tag's own proof: every point of `Y` has an affine open
neighbourhood `V` over which `q^{-1}V` is affine with
`Γ(T, q^{-1}V) = Γ(Y, V)[z₁, z₂]`, the comorphism of `q` being the inclusion of constants.

## Main results

* `Stacks.Chow.TensorZeroScheme.exists_ambientTwoVariableChart`: **the two-variable chart**, at
  an arbitrary point of `Y`, with the two coordinate ideals.
* `Stacks.Chow.TensorZeroScheme.isAffineOpen_preimage_totalProj`: the preimage of an affine open
  of `Y` under `q` is affine.
* `Stacks.Chow.isPushout_mvPolyIncl`: the two-variable polynomial ring is the pushout of two
  one-variable polynomial rings over the base ring.
* `Stacks.Chow.TensorZeroScheme.isPushout_appLE_totalSpace`: over an affine open `V` of `Y`
  whose two line-bundle preimages are affine, the sections of the structure sheaf of `T` over
  `q^{-1}V` are the pushout of the sections of the two line bundles.
* `Stacks.Chow.TensorZeroScheme.exists_twoVariableChart_of_charts`: **the chart over a
  prescribed affine open**, from a one-variable chart of each line bundle there.
* `Stacks.Chow.TensorZeroScheme.zeroScheme_coord₁_eq` and `zeroScheme_coord₂_eq`: the zero
  scheme of the `i`-th fibre coordinate on `T` is the zero scheme of the pullback along the
  `i`-th projection of the `i`-th line bundle's fibre coordinate. For the second coordinate this
  is the instance at `Stacks.Chow.TensorZeroScheme.secondProj_comp` of `zeroScheme_coord₂Of_eq`,
  proved for a variable equality.
* `Stacks.Chow.TensorZeroScheme.zeroScheme_coord₁_ideal` and `zeroScheme_coord₂_ideal`: **the
  two coordinate ideals over a prescribed affine open**, as the images under the two
  projections of the local equations of the two line bundles' fibre coordinates.
* `Stacks.LineBundle.exists_fibreCoordinateTrivialization`: the fibre coordinate of a line
  bundle is the variable of a *prescribed* polynomial chart.

## Implementation notes

The chart is obtained by pushing out, not by writing down a tensor product: the restriction of
the defining cartesian square of `T` to an affine open of `Y` is cartesian with affine corners,
so `AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen` turns it into a pushout square of
rings; `Stacks.LineBundle.Situation.exists_chartEquiv` identifies the two upper corners with
one-variable polynomial rings over `Γ(Y, V)`; and `Stacks.Chow.isPushout_mvPolyIncl` says that
the pushout of that span is the two-variable polynomial ring. The comparison of two pushout
squares over the same span, `CategoryTheory.IsPushout.isoIsPushout`, is the chart.

*Why the two coordinate clauses are not symmetric.* The chart lives over `q^{-1}V`, which is by
definition the *first* projection's preimage of `q₁^{-1}V` and only *equal*, by
`CategoryTheory.Limits.pullback.condition`, to the second projection's preimage of `q₂^{-1}V`.
So the second coordinate's local equation has to be computed on an affine open strictly inside
the second projection's preimage, which is why
`Stacks.Divisors.zeroScheme_ideal_pullbackGlobalSections` is stated for an arbitrary such open
rather than for the preimage itself (where it would be
`Stacks.Divisors.pullbackTrivialization_resTop` together with
`Stacks.Divisors.zeroScheme_ideal_of_trivialization`).

*Why the line bundles' charts are passed in rather than produced.* Both
`Stacks.LineBundle.exists_fibreCoordinateTrivialization` and
`Stacks.Chow.TensorZeroScheme.exists_twoVariableChart_of_charts` take the affine open and the
chart as inputs: the tag needs *one* open trivializing *two* line bundles, so neither may be
chosen by a construction that sees only one of them. The intersection of the four trivializing
opens, refined to an affine open of `AlgebraicGeometry.Scheme.isBasis_affineOpens`, is taken in
`exists_ambientTwoVariableChart` alone.

*How the second coordinate's zero scheme is reached.* `Stacks.Chow.TensorZeroScheme.coord₂`
carries a transport along `Stacks.Chow.TensorZeroScheme.secondProj_comp`, and a zero scheme does
not see it, the transport being an isomorphism of the ambient module
(`Stacks.Chow.TensorZeroScheme.pullbackCongrIso`). But the transport is an `eqToHom`, so at the
*concrete* equality `secondProj_comp` any definitional comparison across it makes the kernel
reduce an `Eq.rec` between pullbacks along two morphisms that agree only propositionally, and
that reduction does not terminate. So `zeroScheme_coord₂Of_eq` is proved for a *variable*
equality, where the `Eq.rec` is stuck at once, and `zeroScheme_coord₂_eq` is its instance at
`secondProj_comp`; nothing is left to check there but the unfolding of `coord₂`. The
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.Basic` describe the
same hazard.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LineBundle (lineBundleProj)

universe u

@[expose] public noncomputable section

namespace Stacks.Chow

/-! ### Two one-variable polynomial rings push out to a two-variable one -/

/-- The inclusion of a polynomial ring in one variable into a polynomial ring in two variables
sending the variable to the `i`-th variable. -/
def mvPolyIncl (B : Type u) [CommRing B] (i : Fin 2) :
    MvPolynomial (Fin 1) B →+* MvPolynomial (Fin 2) B :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun _ => MvPolynomial.X i

/-- `mvPolyIncl B i` fixes the constants. -/
@[simp]
theorem mvPolyIncl_C (B : Type u) [CommRing B] (i : Fin 2) (b : B) :
    mvPolyIncl B i (MvPolynomial.C b) = MvPolynomial.C b :=
  MvPolynomial.eval₂Hom_C _ _ b

/-- `mvPolyIncl B i` carries the variable to the `i`-th variable. -/
@[simp]
theorem mvPolyIncl_X (B : Type u) [CommRing B] (i : Fin 2) (j : Fin 1) :
    mvPolyIncl B i (MvPolynomial.X j) = MvPolynomial.X i :=
  MvPolynomial.eval₂Hom_X' _ _ j

/-- **The polynomial ring in two variables is the pushout of two polynomial rings in one
variable over the coefficient ring.** A pair of ring maps out of `B[z]` agreeing on `B` is a
single ring map out of `B[x, y]`, by the universal property of a polynomial ring. -/
theorem isPushout_mvPolyIncl (B : CommRingCat.{u}) :
    IsPushout (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := B)))
      (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := B)))
      (CommRingCat.ofHom (mvPolyIncl B 0)) (CommRingCat.ofHom (mvPolyIncl B 1)) := by
  have hw : CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := B)) ≫
      CommRingCat.ofHom (mvPolyIncl B 0) =
      CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := B)) ≫
        CommRingCat.ofHom (mvPolyIncl B 1) := by
    ext b
    simp
  refine ⟨⟨hw⟩, ⟨PushoutCocone.IsColimit.mk hw (fun s => CommRingCat.ofHom
    (MvPolynomial.eval₂Hom (RingHom.comp s.inl.hom (MvPolynomial.C (σ := Fin 1) (R := B)))
      ![s.inl.hom (MvPolynomial.X 0), s.inr.hom (MvPolynomial.X 0)]))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_)⟩⟩
  · refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_))
    · simp
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp
  · have hcond := congrArg CommRingCat.Hom.hom s.condition
    refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_))
    · have : (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := B)) ≫ s.inl).hom b =
          (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := B)) ≫ s.inr).hom b :=
        congrArg (fun φ : B →+* s.pt => φ b) hcond
      simpa using this
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp
  · have hm₁' := congrArg CommRingCat.Hom.hom hm₁
    have hm₂' := congrArg CommRingCat.Hom.hom hm₂
    refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun b => ?_) (fun i => ?_))
    · have := congrArg (fun φ : MvPolynomial (Fin 1) B →+* s.pt => φ (MvPolynomial.C b)) hm₁'
      simpa using this
    · match i with
      | 0 =>
        have := congrArg (fun φ : MvPolynomial (Fin 1) B →+* s.pt =>
          φ (MvPolynomial.X (0 : Fin 1))) hm₁'
        simpa using this
      | 1 =>
        have := congrArg (fun φ : MvPolynomial (Fin 1) B →+* s.pt =>
          φ (MvPolynomial.X (0 : Fin 1))) hm₂'
        simpa using this

/-- An isomorphism out of the two-variable polynomial ring, which restricts along `mvPolyIncl B i`
to a chart of `R` composed with `g`, sends the `i`-th variable to the image of the chart's
variable under `g`. -/
private theorem hom_variable_of_comp_eq {B R T : CommRingCat.{u}}
    (ψ : R ≃+* MvPolynomial (Fin 1) B) (g : R ⟶ T)
    (e : CommRingCat.of (MvPolynomial (Fin 2) B) ≅ T) (i : Fin 2)
    (h : CommRingCat.ofHom (mvPolyIncl B i) ≫ e.hom = ψ.toCommRingCatIso.inv ≫ g) :
    e.hom.hom (MvPolynomial.X i) = g.hom (ψ.symm (MvPolynomial.X 0)) := by
  have h0 := congrArg (fun φ : CommRingCat.of (MvPolynomial (Fin 1) B) ⟶ T =>
    φ.hom (MvPolynomial.X (0 : Fin 1))) h
  simpa using h0

end Stacks.Chow

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

include h₁ h₂ in
/-- **The preimage of an affine open of the base under the structure morphism of the ambient
space of Tag 0F97 is affine**, because that structure morphism is an affine morphism. -/
theorem isAffineOpen_preimage_totalProj (V : Y.affineOpens) :
    IsAffineOpen (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) :=
  have := isAffineHom_totalProj Y L₁ L₂
  V.2.preimage (totalProj Y L₁ L₂)

include h₁ h₂ in
/-- The preimage of an affine open of the base under the structure morphism of the ambient space
is the preimage of the first line bundle's chart under the first projection. -/
theorem preimage_totalProj_eq_firstProj (V : Y.Opens) :
    totalProj Y L₁ L₂ ⁻¹ᵁ V = firstProj Y L₁ L₂ ⁻¹ᵁ (lineBundleProj Y L₁ ⁻¹ᵁ V) := rfl

include h₁ h₂ in
/-- The preimage of an affine open of the base under the structure morphism of the ambient space
is the preimage of the second line bundle's chart under the second projection. -/
theorem preimage_totalProj_eq_secondProj (V : Y.Opens) :
    totalProj Y L₁ L₂ ⁻¹ᵁ V = secondProj Y L₁ L₂ ⁻¹ᵁ (lineBundleProj Y L₂ ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, secondProj_comp]

include h₁ h₂ in
/-- **The sections of the ambient space over the preimage of an affine open form the pushout of
the sections of the two line bundles over their preimages.** The defining cartesian square of
the fibre product restricts to a cartesian square over the affine open, whose three other
corners are affine, and a cartesian square of affine schemes is a pushout square of rings. -/
theorem isPushout_appLE_totalSpace (V : Y.affineOpens) :
    IsPushout ((lineBundleProj Y L₁).appLE (V.1 : Y.Opens)
        (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) le_rfl)
      ((lineBundleProj Y L₂).appLE (V.1 : Y.Opens)
        (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens)) le_rfl)
      ((firstProj Y L₁ L₂).appLE (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))
        (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (le_of_eq (preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens))))
      ((secondProj Y L₁ L₂).appLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (le_of_eq (preimage_totalProj_eq_secondProj Y L₁ L₂ (V.1 : Y.Opens)))) := by
  have hpb : IsPullback (firstProj Y L₁ L₂) (secondProj Y L₁ L₂) (lineBundleProj Y L₁)
      (lineBundleProj Y L₂) := IsPullback.of_hasPullback _ _
  have hUY : totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens) =
      firstProj Y L₁ L₂ ⁻¹ᵁ (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) ⊓
        secondProj Y L₁ L₂ ⁻¹ᵁ (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens)) := by
    rw [← preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens),
      ← preimage_totalProj_eq_secondProj Y L₁ L₂ (V.1 : Y.Opens), inf_idem]
  exact (AlgebraicGeometry.isIso_pushoutSection_iff hpb le_rfl le_rfl hUY).mp
    (AlgebraicGeometry.isIso_pushoutSection_of_isAffineOpen hpb le_rfl le_rfl hUY V.2
      (Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y L₂ V)
      (Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y L₁ V))

include h₁ h₂ in
/-- **The two-variable chart of the ambient space, from a one-variable chart of each line
bundle.** Over an affine open `V` of the base carrying a polynomial chart of each of the two
line bundles, the sections of the structure sheaf of the ambient space over `q^{-1}V` form a
polynomial ring in two variables over `Γ(Y, V)`, with the comorphism of `q` the inclusion of
constants and with the two variables the images of the two one-variable variables under the two
projections. -/
theorem exists_twoVariableChart_of_charts (V : Y.affineOpens)
    (ψ₁ : Γ(Stacks.LineBundle.lineBundleSpace Y L₁,
        lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
      MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens)))
    (hψ₁ : ∀ s : Γ(Y, (V.1 : Y.Opens)),
      ψ₁ (((lineBundleProj Y L₁).app (V.1 : Y.Opens)).hom s) = MvPolynomial.C s)
    (ψ₂ : Γ(Stacks.LineBundle.lineBundleSpace Y L₂,
        lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
      MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens)))
    (hψ₂ : ∀ s : Γ(Y, (V.1 : Y.Opens)),
      ψ₂ (((lineBundleProj Y L₂).app (V.1 : Y.Opens)).hom s) = MvPolynomial.C s) :
    ∃ ψ : Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
        MvPolynomial (Fin 2) Γ(Y, (V.1 : Y.Opens)),
      (∀ s : Γ(Y, (V.1 : Y.Opens)),
          ψ (((totalProj Y L₁ L₂).app (V.1 : Y.Opens)).hom s) = MvPolynomial.C s) ∧
        ψ.symm (MvPolynomial.X 0) =
          ((firstProj Y L₁ L₂).appLE (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))
              (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
              (le_of_eq (preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens)))).hom
            (ψ₁.symm (MvPolynomial.X 0)) ∧
        ψ.symm (MvPolynomial.X 1) =
          ((secondProj Y L₁ L₂).appLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
              (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
              (le_of_eq (preimage_totalProj_eq_secondProj Y L₁ L₂ (V.1 : Y.Opens)))).hom
            (ψ₂.symm (MvPolynomial.X 0)) := by
  have hc₁ : (lineBundleProj Y L₁).appLE (V.1 : Y.Opens)
      (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) le_rfl =
      (lineBundleProj Y L₁).app (V.1 : Y.Opens) :=
    Scheme.Hom.appLE_preimage_self _ _
  have hc₂ : (lineBundleProj Y L₂).appLE (V.1 : Y.Opens)
      (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens)) le_rfl =
      (lineBundleProj Y L₂).app (V.1 : Y.Opens) :=
    Scheme.Hom.appLE_preimage_self _ _
  have hgeo' : IsPushout
      (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := Γ(Y, (V.1 : Y.Opens)))))
      (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 1) (R := Γ(Y, (V.1 : Y.Opens)))))
      (ψ₁.toCommRingCatIso.inv ≫ (firstProj Y L₁ L₂).appLE
        (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))
        (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (le_of_eq (preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens))))
      (ψ₂.toCommRingCatIso.inv ≫ (secondProj Y L₁ L₂).appLE
        (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (le_of_eq (preimage_totalProj_eq_secondProj Y L₁ L₂ (V.1 : Y.Opens)))) := by
    refine (isPushout_appLE_totalSpace Y L₁ L₂ V).of_iso (Iso.refl _)
      ψ₁.toCommRingCatIso ψ₂.toCommRingCatIso (Iso.refl _) ?_ ?_ ?_ ?_
    · refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
      simpa [hc₁] using hψ₁ s
    · refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
      simpa [hc₂] using hψ₂ s
    all_goals rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  have hql : (lineBundleProj Y L₁).appLE (V.1 : Y.Opens)
        (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) le_rfl ≫
      (firstProj Y L₁ L₂).appLE (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))
        (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
        (le_of_eq (preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens))) =
      (totalProj Y L₁ L₂).app (V.1 : Y.Opens) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_preimage_self _ _
  refine ⟨(((isPushout_mvPolyIncl Γ(Y, (V.1 : Y.Opens))).isoIsPushout _ _
    hgeo').commRingCatIsoToRingEquiv).symm, fun s => ?_, ?_, ?_⟩
  · have h0 := congrArg (fun φ : CommRingCat.of (MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens))) ⟶
        Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) =>
        φ.hom (MvPolynomial.C s))
      ((isPushout_mvPolyIncl Γ(Y, (V.1 : Y.Opens))).inl_isoIsPushout_hom _ _ hgeo')
    have hs : ψ₁.symm (MvPolynomial.C s) =
        (((lineBundleProj Y L₁).appLE (V.1 : Y.Opens)
          (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) le_rfl).hom s) := by
      rw [hc₁, RingEquiv.symm_apply_eq]
      exact (hψ₁ s).symm
    have hcomp := congrArg (fun φ : Γ(Y, (V.1 : Y.Opens)) ⟶
      Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) => φ.hom s) hql
    rw [RingEquiv.symm_apply_eq]
    simp only at h0 hcomp ⊢
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, mvPolyIncl_C, RingEquiv.toCommRingCatIso_inv,
      RingEquiv.coe_toRingHom, hs] at h0
    exact hcomp.symm.trans h0.symm
  · exact hom_variable_of_comp_eq ψ₁ _ _ 0
      ((isPushout_mvPolyIncl Γ(Y, (V.1 : Y.Opens))).inl_isoIsPushout_hom _ _ hgeo')
  · exact hom_variable_of_comp_eq ψ₂ _ _ 1
      ((isPushout_mvPolyIncl Γ(Y, (V.1 : Y.Opens))).inr_isoIsPushout_hom _ _ hgeo')

end Stacks.Chow.TensorZeroScheme

namespace Stacks.LineBundle

/-! ### The fibre coordinate chart over a prescribed affine open -/

variable (Y : Scheme.{u}) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The fibre coordinate is the variable of a prescribed polynomial chart.** Given an affine
open `V` of the base trivializing `M`, and a polynomial chart `ψ` of the line bundle over `V`
whose variable generates the kernel of the comorphism of the zero section and is a
nonzerodivisor — which is what `Stacks.LineBundle.Situation.exists_chartEquiv` produces from a
trivialization of `M^{⊗ -1}` over `V` — some trivialization of `Γ(q^* M, q^{-1}V)` carries the
fibre coordinate to the variable.

This is the second half of `Stacks.LineBundle.exists_fibreCoordinateChart`, with the chart as an
input rather than an output. [Stacks, Tag 0F97] needs one affine open trivializing *two* line
bundles, so the open — and with it the chart — may not be chosen by the construction. The chart
itself is not taken apart here, and in particular the module `M^{⊗ -1}` is never named: naming
it in a statement is what the implementation notes of
`StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.FibreCoordinateChart` record as the spelling at
which instance search fails for a *concrete* situation. -/
theorem exists_fibreCoordinateTrivialization (V : Y.affineOpens)
    (heM : Nonempty (Γ(M, (V.1 : Y.Opens)) ≃ₗ[Γ(Y, (V.1 : Y.Opens))] Γ(Y, (V.1 : Y.Opens))))
    (ψ : Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
      MvPolynomial (Fin 1) Γ(Y, (V.1 : Y.Opens)))
    (hψker : RingHom.ker ((inverseSituation Y M).zeroSectionChartMap V).hom =
      Ideal.span {ψ.symm (MvPolynomial.X 0)})
    (hψreg : ∀ t : Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)),
      ψ.symm (MvPolynomial.X 0) * t = 0 → t = 0) :
    ∃ e : Γ(lineBundlePullback Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)) ≃ₗ[
          Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens))]
        Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens)),
      e ((lineBundlePullback Y M).presheaf.map (homOfLE le_top).op (fibreCoordinate Y M)) =
        ψ.symm (MvPolynomial.X 0) := by
  have hqc : M.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible M
  have hzs : AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
        (fibreCoordinate Y M) = (inverseSituation Y M).zeroSection.ker :=
    (zeroScheme_fibreCoordinate Y M).trans
      ((zeroScheme_tautologicalSectionBase (inverseSituation Y M)).trans
        (inverseSituation Y M).zeroScheme_tautologicalSectionBase_eq_ker_zeroSection)
  have hideal : (AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
        (fibreCoordinate Y M)).ideal
          ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens),
            isAffineOpen_preimage_lineBundleProj Y M V⟩ =
      Ideal.span {ψ.symm (MvPolynomial.X 0)} :=
    Eq.trans
      (congrArg (fun I : AlgebraicGeometry.Scheme.IdealSheafData (lineBundleSpace Y M) =>
          I.ideal ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens),
            isAffineOpen_preimage_lineBundleProj Y M V⟩) hzs)
      ((((inverseSituation Y M).zeroSection.ker_apply
            ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens),
              isAffineOpen_preimage_lineBundleProj Y M V⟩).trans
          ((inverseSituation Y M).ker_zeroSectionChartMap_eq V).symm).trans hψker)
  obtain ⟨e₀⟩ := Stacks.Modules.nonempty_linearEquiv_sections_pullback (lineBundleProj Y M) M
    V.2 (isAffineOpen_preimage_lineBundleProj Y M V) heM
  have hA : (AlgebraicGeometry.zeroScheme (lineBundleSpace Y M) (lineBundlePullback Y M)
        (fibreCoordinate Y M)).ideal
          ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens),
            isAffineOpen_preimage_lineBundleProj Y M V⟩ =
      Ideal.span {e₀ ((lineBundlePullback Y M).presheaf.map (homOfLE le_top).op
        (fibreCoordinate Y M))} :=
    Stacks.Divisors.zeroScheme_ideal_of_trivialization (lineBundleSpace Y M)
      (lineBundlePullback Y M) (fibreCoordinate Y M)
      ⟨lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens), isAffineOpen_preimage_lineBundleProj Y M V⟩
      e₀ _ rfl
  obtain ⟨c, hc⟩ := exists_unit_of_span_eq
    (e₀ ((lineBundlePullback Y M).presheaf.map (homOfLE le_top).op (fibreCoordinate Y M)))
    (ψ.symm (MvPolynomial.X 0)) hψreg (hA.symm.trans hideal)
  refine ⟨e₀.trans (LinearEquiv.smulOfUnit c⁻¹), ?_⟩
  show ((c⁻¹ : _ˣ) : Γ(lineBundleSpace Y M, lineBundleProj Y M ⁻¹ᵁ (V.1 : Y.Opens))) •
    e₀ ((lineBundlePullback Y M).presheaf.map (homOfLE le_top).op (fibreCoordinate Y M)) = _
  rw [smul_eq_mul, hc]
  exact Units.inv_mul_cancel_left c _

end Stacks.LineBundle

namespace Stacks.Chow.TensorZeroScheme

variable (Y : Scheme.{u}) (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]

/-! ### The two fibre coordinates as pulled-back fibre coordinates -/

include h₁ h₂ in
/-- **The zero scheme of the first fibre coordinate is the zero scheme of the pullback along the
first projection of the fibre coordinate of the first line bundle.** The two sections differ by
the contraction `Stacks.Divisors.pullbackCompIso` of an iterated pullback, which is an
isomorphism of the ambient module and therefore does not move the zero scheme. -/
theorem zeroScheme_coord₁_eq :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂) =
      Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (firstProj Y L₁ L₂)).obj
          (Stacks.LineBundle.lineBundlePullback Y L₁))
        (pullbackGlobalSections (firstProj Y L₁ L₂)
          (Stacks.LineBundle.lineBundlePullback Y L₁)
          (Stacks.LineBundle.fibreCoordinate Y L₁)) :=
  (AlgebraicGeometry.zeroScheme_eq_of_iso
    (Stacks.Divisors.pullbackCompIso (firstProj Y L₁ L₂) (lineBundleProj Y L₁) L₁) rfl).symm

include h₁ h₂ in
/-- **The zero scheme of the second fibre coordinate, transported along an arbitrary equality,
is the zero scheme of the pullback along the second projection of the fibre coordinate of the
second line bundle.** Two isomorphisms of the ambient module separate the two sections — the
contraction `Stacks.Divisors.pullbackCompIso` of an iterated pullback and the transport
`pullbackCongrIso` — and a zero scheme sees neither.

The equality transported along is the parameter of `Stacks.Chow.TensorZeroScheme.coord₂Of`:
`pullbackCongrHom` is an `eqToHom`, and at the concrete equality
`Stacks.Chow.TensorZeroScheme.secondProj_comp` deciding a definitional equality across it makes
the kernel reduce an `Eq.rec` between pullbacks along morphisms that agree only propositionally,
which does not terminate. With the equality a variable the reduction is stuck at once, and
`zeroScheme_coord₂_eq` below is the instance at `secondProj_comp`, where only the unfolding of
`coord₂` into `coord₂Of` is left to check. -/
theorem zeroScheme_coord₂Of_eq {m : totalSpace Y L₁ L₂ ⟶ Y}
    (hm : secondProj Y L₁ L₂ ≫ lineBundleProj Y L₂ = m) :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback m).obj L₂) (coord₂Of Y L₁ L₂ hm) =
      Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (secondProj Y L₁ L₂)).obj
          (Stacks.LineBundle.lineBundlePullback Y L₂))
        (pullbackGlobalSections (secondProj Y L₁ L₂)
          (Stacks.LineBundle.lineBundlePullback Y L₂)
          (Stacks.LineBundle.fibreCoordinate Y L₂)) :=
  ((AlgebraicGeometry.zeroScheme_eq_of_iso
        (Stacks.Divisors.pullbackCompIso (secondProj Y L₁ L₂) (lineBundleProj Y L₂) L₂)
        rfl).trans
      (AlgebraicGeometry.zeroScheme_eq_of_iso (pullbackCongrIso hm L₂) rfl)).symm

include h₁ h₂ in
/-- **The zero scheme of the second fibre coordinate is the zero scheme of the pullback along the
second projection of the fibre coordinate of the second line bundle**, the instance of
`zeroScheme_coord₂Of_eq` at `Stacks.Chow.TensorZeroScheme.secondProj_comp`. -/
theorem zeroScheme_coord₂_eq :
    Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂) =
      Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
        ((Scheme.Modules.pullback (secondProj Y L₁ L₂)).obj
          (Stacks.LineBundle.lineBundlePullback Y L₂))
        (pullbackGlobalSections (secondProj Y L₁ L₂)
          (Stacks.LineBundle.lineBundlePullback Y L₂)
          (Stacks.LineBundle.fibreCoordinate Y L₂)) :=
  zeroScheme_coord₂Of_eq Y L₁ L₂ (secondProj_comp Y L₁ L₂)

/-! ### The two coordinate ideals on the two-variable chart -/

include h₁ h₂ in
/-- **The local equation of the first fibre coordinate on the two-variable chart.** Over an
affine open `V` of the base carrying a trivialization `e₁` of the pullback of `L₁` to the first
line bundle, the ideal of `Z(z₁)` on `q^{-1}V` is generated by the image under the comorphism of
the first projection of the local equation `e₁ (z|_{q₁^{-1}V})` of the first line bundle's fibre
coordinate. -/
theorem zeroScheme_coord₁_ideal (V : Y.affineOpens)
    (e₁ : Γ(Stacks.LineBundle.lineBundlePullback Y L₁,
          lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens)) ≃ₗ[
        Γ(Stacks.LineBundle.lineBundleSpace Y L₁, lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))]
      Γ(Stacks.LineBundle.lineBundleSpace Y L₁, lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))) :
    (Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂)).ideal
        ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), isAffineOpen_preimage_totalProj Y L₁ L₂ V⟩ =
      Ideal.span {((firstProj Y L₁ L₂).appLE (lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens))
          (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (le_of_eq (preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens)))).hom
        (e₁ ((Stacks.LineBundle.lineBundlePullback Y L₁).presheaf.map (homOfLE le_top).op
          (Stacks.LineBundle.fibreCoordinate Y L₁)))} :=
  (congrArg (fun I : (totalSpace Y L₁ L₂).IdealSheafData =>
      I.ideal ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens),
        isAffineOpen_preimage_totalProj Y L₁ L₂ V⟩)
    (zeroScheme_coord₁_eq Y L₁ L₂)).trans
    (Stacks.Divisors.zeroScheme_ideal_pullbackGlobalSections (firstProj Y L₁ L₂)
      (Stacks.LineBundle.lineBundlePullback Y L₁)
      ⟨lineBundleProj Y L₁ ⁻¹ᵁ (V.1 : Y.Opens),
        Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y L₁ V⟩
      ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), isAffineOpen_preimage_totalProj Y L₁ L₂ V⟩
      (le_of_eq (preimage_totalProj_eq_firstProj Y L₁ L₂ (V.1 : Y.Opens))) e₁
      (Stacks.LineBundle.fibreCoordinate Y L₁))

include h₁ h₂ in
/-- **The local equation of the second fibre coordinate on the two-variable chart.** The
asymmetry of the fibre product shows here: the chart is the preimage of `V` under `q`, which is
the *first* projection's preimage of `q₁^{-1}V`, and is only equal to the second projection's
preimage of `q₂^{-1}V`; that is why
`Stacks.Divisors.zeroScheme_ideal_pullbackGlobalSections` is stated for an arbitrary affine open
inside the preimage. -/
theorem zeroScheme_coord₂_ideal (V : Y.affineOpens)
    (e₂ : Γ(Stacks.LineBundle.lineBundlePullback Y L₂,
          lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens)) ≃ₗ[
        Γ(Stacks.LineBundle.lineBundleSpace Y L₂, lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))]
      Γ(Stacks.LineBundle.lineBundleSpace Y L₂, lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))) :
    (Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
          ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂)).ideal
        ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), isAffineOpen_preimage_totalProj Y L₁ L₂ V⟩ =
      Ideal.span {((secondProj Y L₁ L₂).appLE (lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens))
          (le_of_eq (preimage_totalProj_eq_secondProj Y L₁ L₂ (V.1 : Y.Opens)))).hom
        (e₂ ((Stacks.LineBundle.lineBundlePullback Y L₂).presheaf.map (homOfLE le_top).op
          (Stacks.LineBundle.fibreCoordinate Y L₂)))} :=
  (congrArg (fun I : (totalSpace Y L₁ L₂).IdealSheafData =>
      I.ideal ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens),
        isAffineOpen_preimage_totalProj Y L₁ L₂ V⟩)
    (zeroScheme_coord₂_eq Y L₁ L₂)).trans
    (Stacks.Divisors.zeroScheme_ideal_pullbackGlobalSections (secondProj Y L₁ L₂)
      (Stacks.LineBundle.lineBundlePullback Y L₂)
      ⟨lineBundleProj Y L₂ ⁻¹ᵁ (V.1 : Y.Opens),
        Stacks.LineBundle.isAffineOpen_preimage_lineBundleProj Y L₂ V⟩
      ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), isAffineOpen_preimage_totalProj Y L₁ L₂ V⟩
      (le_of_eq (preimage_totalProj_eq_secondProj Y L₁ L₂ (V.1 : Y.Opens))) e₂
      (Stacks.LineBundle.fibreCoordinate Y L₂))

/-! ### The two-variable chart at a point -/

include h₁ h₂ in
/-- **The two-variable chart of the ambient space of [Stacks, Tag 0F97].** Every point of `Y`
has an affine open neighbourhood `V` such that the inverse image `q^{-1}V` of `V` in the ambient
space `T = Tot(L₁^{⊗ -1}) ×_Y Tot(L₂^{⊗ -1})` is affine, the ring of sections of `T` there is a
polynomial ring in two variables over `Γ(Y, V)` with the comorphism of `q` the inclusion of
constants, and the two fibre coordinates cut out there exactly the two variables.

This is the chart the proof of the tag works on: it is what presents `p^{-1}V` as
`Spec Γ(Y, V)[z₁, z₂]/(z₁z₂ - f)`. The affine open is found by intersecting four trivializing
opens — one for each of `L₁`, `L₂`, `L₁^{⊗ -1}` and `L₂^{⊗ -1}` — and refining to an affine
open of the base of the topology; the first two give the two fibre coordinates their local
equations and the last two give the two one-variable charts that
`Stacks.Chow.TensorZeroScheme.exists_twoVariableChart_of_charts` pushes out.

The trivializations `u₁` of `L₁` and `u₂` of `L₂` over `V` are returned along with the chart:
the same open has to trivialize both modules for the section `s` of `L₁ ⊗ L₂` to have a local
equation on it, and that local equation is what the local model degenerates along. -/
theorem exists_ambientTwoVariableChart (y : Y) :
    ∃ V : Y.affineOpens, y ∈ V.1 ∧
      ∃ (hW : IsAffineOpen (totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)))
        (_ : Γ(L₁, (V.1 : Y.Opens)) ≃ₗ[Γ(Y, (V.1 : Y.Opens))] Γ(Y, (V.1 : Y.Opens)))
        (_ : Γ(L₂, (V.1 : Y.Opens)) ≃ₗ[Γ(Y, (V.1 : Y.Opens))] Γ(Y, (V.1 : Y.Opens)))
        (ψ : Γ(totalSpace Y L₁ L₂, totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens)) ≃+*
              MvPolynomial (Fin 2) Γ(Y, (V.1 : Y.Opens))),
        (∀ s : Γ(Y, (V.1 : Y.Opens)),
            ψ (((totalProj Y L₁ L₂).app (V.1 : Y.Opens)).hom s) = MvPolynomial.C s) ∧
        (Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
              ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₁) (coord₁ Y L₁ L₂)).ideal
            ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), hW⟩ =
          Ideal.span {ψ.symm (MvPolynomial.X 0)} ∧
        (Stacks.Divisors.zeroScheme (totalSpace Y L₁ L₂)
              ((Scheme.Modules.pullback (totalProj Y L₁ L₂)).obj L₂) (coord₂ Y L₁ L₂)).ideal
            ⟨totalProj Y L₁ L₂ ⁻¹ᵁ (V.1 : Y.Opens), hW⟩ =
          Ideal.span {ψ.symm (MvPolynomial.X 1)} := by
  have hv₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.LineBundle.inverseSituation Y L₁).L :=
    (Stacks.LineBundle.inverseSituation Y L₁).invertible
  have hv₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property
      (Stacks.LineBundle.inverseSituation Y L₂).L :=
    (Stacks.LineBundle.inverseSituation Y L₂).invertible
  obtain ⟨O₁, hyO₁, hO₁⟩ := Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv Y
    (Stacks.LineBundle.inverseSituation Y L₁).L y
  obtain ⟨O₂, hyO₂, hO₂⟩ := Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv Y
    (Stacks.LineBundle.inverseSituation Y L₂).L y
  obtain ⟨O₃, hyO₃, hO₃⟩ :=
    Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv Y L₁ y
  obtain ⟨O₄, hyO₄, hO₄⟩ :=
    Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv Y L₂ y
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((O₁ ⊓ O₂ ⊓ O₃ ⊓ O₄ : Y.Opens) : Set Y) from ⟨⟨⟨hyO₁, hyO₂⟩, hyO₃⟩, hyO₄⟩)
    (O₁ ⊓ O₂ ⊓ O₃ ⊓ O₄ : Y.Opens).isOpen
  obtain ⟨eN₁⟩ := hO₁ V (hVU.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  obtain ⟨eN₂⟩ := hO₂ V (hVU.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  obtain ⟨ψ₁, hψ₁C, hψ₁ker, hψ₁reg⟩ :=
    (Stacks.LineBundle.inverseSituation Y L₁).exists_chartEquiv ⟨V, hVaff⟩ eN₁
  obtain ⟨ψ₂, hψ₂C, hψ₂ker, hψ₂reg⟩ :=
    (Stacks.LineBundle.inverseSituation Y L₂).exists_chartEquiv ⟨V, hVaff⟩ eN₂
  obtain ⟨u₁⟩ := hO₃ V (hVU.trans (inf_le_left.trans inf_le_right))
  obtain ⟨u₂⟩ := hO₄ V (hVU.trans inf_le_right)
  obtain ⟨e₁, he₁⟩ := Stacks.LineBundle.exists_fibreCoordinateTrivialization Y L₁ ⟨V, hVaff⟩
    ⟨u₁⟩ ψ₁ hψ₁ker hψ₁reg
  obtain ⟨e₂, he₂⟩ := Stacks.LineBundle.exists_fibreCoordinateTrivialization Y L₂ ⟨V, hVaff⟩
    ⟨u₂⟩ ψ₂ hψ₂ker hψ₂reg
  obtain ⟨ψ, hψC, hψ₀, hψ₁⟩ :=
    exists_twoVariableChart_of_charts Y L₁ L₂ ⟨V, hVaff⟩ ψ₁ hψ₁C ψ₂ hψ₂C
  refine ⟨⟨V, hVaff⟩, hyV, isAffineOpen_preimage_totalProj Y L₁ L₂ ⟨V, hVaff⟩, u₁, u₂, ψ, hψC,
    ?_, ?_⟩
  · rw [zeroScheme_coord₁_ideal Y L₁ L₂ ⟨V, hVaff⟩ e₁, he₁, hψ₀]
  · rw [zeroScheme_coord₂_ideal Y L₁ L₂ ⟨V, hVaff⟩ e₂, he₂, hψ₁]

end Stacks.Chow.TensorZeroScheme

end
