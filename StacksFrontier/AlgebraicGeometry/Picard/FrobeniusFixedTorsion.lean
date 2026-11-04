module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.FrobeniusFixed
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.PicardGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.Picard.CurvePicardTorsionFinite
public import StacksFrontier.AlgebraicGeometry.Picard.WeilPairing
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The Frobenius-fixed torsion of the Picard group of a curve over `𝔽̄_q` is finite

Let `Y` be a smooth proper geometrically irreducible curve over a finite field `k`, let `K` be an
algebraic closure of `k` and let `σ` be the pullback along `id_Y × Spec(F)` on `Pic(Y_K)`, `F` the
Frobenius of `K/k`. **The torsion classes of `Pic(Y_K)` fixed by `σ` form a finite set**; in
particular the `σ`-fixed `ℓⁿ`-torsion is bounded independently of `n`. This is the input `hfix`
of `Stacks.Picard.eq_zero_of_smul_eigen_of_weilPairing`.

The argument is the one of the source's proof that `Pic(Y_K)^σ = Pic(Y)` and that `Pic⁰(Y)` is
finite, arranged so that no Brauer group appears:

* a `σ`-fixed class is fixed by all of `Gal(K/k)` (`Stacks.Picard.galoisFixed_of_frobenius_fixed`);
* a closed point `x` of `Y` gives a finite stage `E ⊆ K`, the image of `κ(x)`, over which the base
  change `Y_E` has an `E`-rational point; `Y_K = (Y_E)_K`
  (`Stacks.Picard.stageBaseChangeIso`), compatibly with the Galois twists, so the class is a
  `Gal(K/E)`-fixed class of `Pic((Y_E)_K)`, which by Tag 0CDT
  (`Stacks.Picard.bijOn_schemePullbackClass_galoisFixedClasses`) is pulled back from a class of
  `Pic(Y_E)`, torsion if the given class is (pullback is injective);
* the torsion of `Pic(Y_E)` is finite (`Stacks.Picard.finite_setOf_isOfFinAddOrder`), `Y_E` being
  again a smooth proper curve over the finite field `E`.

## Main results

* `Stacks.Picard.frobeniusPicardHom`: `σ` as an additive endomorphism of `Pic(Y_K)`.
* `Stacks.Picard.finite_setOf_frobenius_fixed_isOfFinAddOrder`: the finiteness.
* `Stacks.Picard.exists_natCard_ker_frobeniusPicardHom_sub_id_le`: the bound in the shape of the
  `hfix` hypothesis of `Stacks.Picard.eq_zero_of_smul_eigen_of_weilPairing`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))

/-- **The Frobenius on the Picard group of `Y_{k̄}`**: pullback along `id_Y × Spec(F)`, `F` the
Frobenius `x ↦ x ^ q` of the algebraic closure. -/
def frobeniusPicardHom :
    ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y) →+
      ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y) :=
  schemePullbackClassHom
    (galoisTwist k (AlgebraicClosure k) Y
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)))

/-- `frobeniusPicardHom Y` sends a class `z` to its pullback along the Galois twist of `Y_{k̄}` by
the Frobenius of `k̄/k`. -/
theorem frobeniusPicardHom_apply (z : ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) :
    frobeniusPicardHom Y z = schemePullbackClass
      (galoisTwist k (AlgebraicClosure k) Y
        (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))) z := rfl

variable [IsProper Y.hom] [Smooth Y.hom] [GeometricallyIrreducible Y.hom] [IsCurve k Y.hom]

omit [Fintype k] [IsProper Y.hom] [GeometricallyIrreducible Y.hom] in
/-- The curve `Y` acquires a rational point over some finite stage `E ⊆ k̄`: the image of
the residue field of a closed point. -/
private theorem exists_finiteDimensional_stageOver_section :
    ∃ E : IntermediateField k (AlgebraicClosure k), FiniteDimensional k E ∧
      ∃ pt : Spec (.of E) ⟶ (stageOver Y E).left, pt ≫ (stageOver Y E).hom = 𝟙 _ := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y.left)).exists_closed_singleton Set.univ_nonempty
  let : Algebra k (Y.left.residueField x) := (fieldToResidue Y.hom x).hom.toAlgebra
  have : Module.Finite k (Y.left.residueField x) :=
    Module.finite_of_finrank_pos (Stacks.EtaleCohomology.residueDegree_pos Y.hom x hx)
  let φ : Y.left.residueField x →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  set E : IntermediateField k (AlgebraicClosure k) := φ.fieldRange
  let σE : Y.left.residueField x ⟶ CommRingCat.of E :=
    CommRingCat.ofHom φ.equivFieldRange.toAlgHom.toRingHom
  have hσE : fieldToResidue Y.hom x ≫ σE = CommRingCat.ofHom (algebraMap k E) := by
    ext c
    exact congrArg Subtype.val (φ.equivFieldRange.toAlgHom.commutes c)
  exact ⟨E, LinearEquiv.finiteDimensional φ.equivFieldRange.toLinearEquiv,
    pullback.lift (Spec.map σE ≫ Y.left.fromSpecResidueField x) (𝟙 _)
      (by rw [Category.id_comp, (Stacks.EtaleCohomology.fromSpecResidueField_comp_eq_iff
        Y.hom E x σE).2 hσE]), pullback.lift_snd _ _ _⟩

/-- A smooth geometrically irreducible curve is geometrically integral. -/
private theorem geometricallyIntegral_of_smooth_of_geometricallyIrreducible
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyIrreducible f] :
    GeometricallyIntegral f :=
  have := geometricallyReduced_of_smooth f
  .of_geometricallyReduced_of_geometricallyIrreducible f

omit [Fintype k] in
/-- The torsion of `Pic(Y_E)` is finite for a finite stage `E ⊆ k̄`: `Y_E` is again a smooth
proper curve over the finite field `E`. -/
private theorem finite_setOf_isOfFinAddOrder_stageOver [Finite k]
    (E : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k E] :
    {w : ofScheme (stageOver Y E).left | IsOfFinAddOrder w}.Finite := by
  have : Finite E := Module.finite_of_finite k
  have := geometricallyIntegral_of_smooth_of_geometricallyIrreducible Y.hom
  set pE : (stageOver Y E).left ⟶ Spec (.of E) := (stageOver Y E).hom
  have : IsProper pE := inferInstanceAs (IsProper (pullback.snd Y.hom (spectrumMap k E)))
  have : Smooth pE := inferInstanceAs (Smooth (pullback.snd Y.hom (spectrumMap k E)))
  have : GeometricallyIntegral pE :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd Y.hom (spectrumMap k E)))
  have : IsIntegral (stageOver Y E).left := GeometricallyIntegral.isIntegral_of_subsingleton pE
  have : IsCurve E pE :=
    { topologicalKrullDim_eq_one :=
        (topologicalKrullDim_baseChange k E (pullback.fst Y.hom (spectrumMap k E)) pE Y.hom
          (IsPullback.of_hasPullback Y.hom (spectrumMap k E))).trans
          (IsCurve.topologicalKrullDim_eq_one Y.hom) }
  exact finite_setOf_isOfFinAddOrder pE

/-- **The Frobenius-fixed torsion classes of `Pic(Y_{k̄})` form a finite set**, for a smooth proper
geometrically irreducible curve `Y` over a finite field `k`. -/
theorem finite_setOf_frobenius_fixed_isOfFinAddOrder :
    {z | frobeniusPicardHom Y z = z ∧ IsOfFinAddOrder z}.Finite := by
  classical
  obtain ⟨E, _, pt, hpt⟩ := exists_finiteDimensional_stageOver_section Y
  set K := AlgebraicClosure k
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have := geometricallyIntegral_of_smooth_of_geometricallyIrreducible Y.hom
  have : IsGalois E K := IsGalois.tower_top_of_isGalois k E K
  have : CompactSpace (stageOver Y E).left := compactSpace_stage Y E
  have : QuasiSeparatedSpace (stageOver Y E).left := quasiSeparatedSpace_stage Y E
  have hbij := bijOn_schemePullbackClass_galoisFixedClasses E K (stageOver Y E)
    (isIso_appTop_stage Y (isIso_globalSections_of_geometricallyIntegral k Y.hom) E) pt hpt
  set e := stageBaseChangeIso Y E
  let pr := pullback.fst (stageOver Y E).hom (spectrumMap E K)
  refine ((finite_setOf_isOfFinAddOrder_stageOver Y E).image fun w =>
    schemePullbackClass e.hom (schemePullbackClass pr w)).subset ?_
  rintro z ⟨hzσ, hz⟩
  set u := schemePullbackClass e.inv z
  have hu : u ∈ galoisFixedClasses E K (stageOver Y E) := by
    intro τ
    have hcomm : galoisTwist E K (stageOver Y E) τ ≫ e.inv =
        e.inv ≫ galoisTwist k K Y (τ.restrictScalars k) := by
      rw [Iso.eq_inv_comp, ← Category.assoc,
        ← galoisTwist_restrictScalars_comp_stageBaseChangeIso_hom, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [schemePullbackClass_comp, hcomm, ← schemePullbackClass_comp,
      galoisFixed_of_frobenius_fixed Y z hzσ]
  obtain ⟨w, -, hw⟩ := hbij.surjOn hu
  refine ⟨w, ?_, ?_⟩
  · obtain ⟨n, hn, hnz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hz
    have h₂ : n • u = 0 :=
      (map_nsmul (schemePullbackClassHom e.inv) n z).symm.trans (by rw [hnz, map_zero])
    have key : schemePullbackClassHom pr (n • w) = schemePullbackClassHom pr 0 := by
      rw [map_nsmul, map_zero]
      exact (congrArg (n • ·) hw).trans h₂
    show IsOfFinAddOrder w
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2
      ⟨n, hn, hbij.injOn (Set.mem_univ _) (Set.mem_univ _) key⟩
  · show schemePullbackClass e.hom (schemePullbackClass pr w) = z
    rw [hw, schemePullbackClass_comp, Iso.hom_inv_id, schemePullbackClass_id]

/-- **The `σ`-fixed `ℓⁿ`-torsion of `Pic(Y_{k̄})` is bounded independently of `n`**, in the shape
of the hypothesis `hfix` of `Stacks.Picard.eq_zero_of_smul_eigen_of_weilPairing`: the kernel of
`σ - 1` on the `ℓⁿ`-torsion embeds into the finite set of `σ`-fixed torsion classes. -/
theorem exists_natCard_ker_frobeniusPicardHom_sub_id_le (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    ∃ C : ℕ, ∀ n, Nat.card (torsionByRestrict (frobeniusPicardHom Y) ((ℓ : ℤ) ^ n) -
      AddMonoidHom.id (Submodule.torsionBy ℤ
        (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n))).ker ≤ C := by
  have := (finite_setOf_frobenius_fixed_isOfFinAddOrder Y).to_subtype
  refine ⟨Nat.card {z | frobeniusPicardHom Y z = z ∧ IsOfFinAddOrder z}, fun n => ?_⟩
  refine Nat.card_le_card_of_injective
    (fun a => ⟨(a.1 : ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)), ?_, ?_⟩)
    fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :))
  · have h := (AddMonoidHom.mem_ker).1 a.2
    have h3 : torsionByRestrict (frobeniusPicardHom Y) ((ℓ : ℤ) ^ n) a.1 = a.1 :=
      sub_eq_zero.1 h
    exact congrArg Subtype.val h3
  · refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ ^ n, pow_pos (Nat.pos_of_ne_zero hℓ) n, ?_⟩
    have h := (Submodule.mem_torsionBy_iff _ _).1 a.1.2
    generalize ((a.1 : Submodule.torsionBy ℤ
        (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n)) :
          ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) = x at h ⊢
    rwa [← Nat.cast_pow, natCast_zsmul] at h

end Stacks.Picard

end
