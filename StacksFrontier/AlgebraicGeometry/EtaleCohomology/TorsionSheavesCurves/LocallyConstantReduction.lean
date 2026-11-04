module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.TraceDegreeSmallEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsRetract
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteEtaleCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleFiltrationTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleLiftLocallyConstant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Lemma 03SD: extension by zero of a locally constant `F_ℓ`-sheaf

Lemma 03SD of the source: in Situation 0A52 with `X` reduced, for an open immersion
`j : U ⟶ X`, a prime `ℓ` and a finite locally constant sheaf `G` of `F_ℓ`-vector spaces on
`U_étale`, statements (1) -- (8) hold for `j_! G`.

## Main results

* `Stacks.EtaleCohomology.curveStatements_extensionByZero_forgetZMod_of_primeToEll`: Lemma
  03SD, granted Lemma 0A5B for the constant sheaf on smooth curves and the conclusion of Lemma
  0A3R for `G`.
* `Stacks.EtaleCohomology.curveStatements_extensionByZero_of_isFiniteLocallyConstant`: Lemma 03SD
  in the source's form, granted Lemma 0A5B for `Z/ℓ` only; Lemma 0A3R is supplied by its
  unconditional form
  `Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_relSeries_constantRankOneStep`.

## Implementation notes

**No `@[stacks 03SD]` attribute**: Lemma 0A5B for `Z/ℓ` on smooth curves enters as the explicit
hypothesis `CurveStatementsConstantOnSmoothCurves`. The hypotheses of the source on `G` (local
constancy) and on `U` (connectedness) are exactly the hypotheses under which Lemma 0A3R supplies
the filtration, and are not used otherwise.

The proof is the one of the source. The finite étale cover `f : V ⟶ U` of degree `d` prime to
`ℓ` from Lemma 0A3R makes `G` a direct summand of `f_* f^{-1} G` through the trace
(`Stacks.EtaleCohomology.exists_unit_comp_eq_nsmul_of_finiteEtale`, `d` being invertible on
`G`), so `j_! G` is a direct summand of `j_! f_* f^{-1} G`; Zariski's Main Theorem and Tag 0GJ1
identify the latter with `f̄_* j'_! f^{-1} G` for a finite `f̄ : Y ⟶ X` with `Y` reduced; Lemma
0A5D reduces to `j'_! f^{-1} G` on `Y`, which carries the filtration of Lemma 0A3R and so is the
last step of Lemma 03SD
(`Stacks.EtaleCohomology.curveStatements_extensionByZero_of_hasConstantFiltration`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- In a preadditive category, an object killed by `ℓ` is killed by `a • ·` exactly as by its
residue modulo `ℓ`. -/
theorem nsmul_id_eq_mod_nsmul_id {C : Type*} [Category C] [Preadditive C] {A : C} {ℓ : ℕ}
    (h : ℓ • 𝟙 A = 0) (a : ℕ) : a • 𝟙 A = (a % ℓ) • 𝟙 A := by
  conv_lhs => rw [← Nat.mod_add_div a ℓ]
  rw [add_nsmul, mul_comm, mul_nsmul', h, nsmul_zero, add_zero]

/-- **The unit of a finite étale cover of degree prime to `ℓ` is split on a sheaf killed by
`ℓ`** (Section 03SH). -/
theorem exists_unit_comp_eq_id_of_finiteEtale {S T : Scheme.{u}} (f : T ⟶ S) [IsFinite f]
    [Etale f] {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : ¬ ℓ ∣ d)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : ℓ • 𝟙 G = 0) :
    ∃ r : (etaleAbelianDirectImage.{u, 0} f).obj ((etaleAbelianInverseImage.{u, 0} f).obj G) ⟶ G,
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app G ≫ r = 𝟙 G := by
  obtain ⟨r, hr⟩ := exists_unit_comp_eq_nsmul_of_finiteEtale f d G
  have : Fact (1 < ℓ) := ⟨hℓ.one_lt⟩
  have hcop : d.Coprime ℓ := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hd)
  set d' := ((d : ZMod ℓ)⁻¹).val
  have hd' : d * d' % ℓ = 1 := by
    rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one d hcop,
      ZMod.val_one]
  refine ⟨d' • r, ?_⟩
  rw [Preadditive.comp_nsmul, hr, smul_smul, nsmul_id_eq_mod_nsmul_id hG, mul_comm, hd',
    one_nsmul]

/-- A scheme of finite type over a compact locally Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_quasiCompact {X S : Scheme.{u}} (π : X ⟶ S)
    [LocallyOfFiniteType π] [QuasiCompact π] [CompactSpace S] [IsLocallyNoetherian S] :
    IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  exact ⟨⟩

/-- **Stacks Project, Lemma 03SD, granted Lemma 0A5B for `Z/ℓ` and the conclusion of Lemma
0A3R.** Let `X` be a reduced separated scheme of finite type and dimension at most one over an
algebraically closed field `k`, `j : U ⟶ X` an open immersion, `ℓ` a prime and `G` a sheaf of
`F_ℓ`-vector spaces on `U_étale` admitting a finite étale `f : V ⟶ U` of degree prime to `ℓ`
with `f^{-1}G` filtered by copies of `Z/ℓZ` (the conclusion of Lemma 0A3R for `G`, verbatim).
If statements (1) -- (8) hold for `Z/ℓ` on every smooth curve over `k`, they hold for `j_! G`. -/
theorem curveStatements_extensionByZero_forgetZMod_of_primeToEll {k : Type u} [Field k]
    [IsAlgClosed k] {ℓ : ℕ} (hℓ : ℓ.Prime) {X U : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (j : U ⟶ X) [IsOpenImmersion j]
    (hbase : CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ)))
    (h0A3R : ∃ (T : Scheme.{u}) (f : T ⟶ U) (d : ℕ), IsFinite f ∧ Etale f ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
      ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ f).obj G)),
        IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow) :
    CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj ((forgetZMod ℓ U).obj G)) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType_quasiCompact π
  obtain ⟨V, f, d, _, _, _, hd, n, hfil⟩ :=
    exists_finiteEtale_hasConstantFiltration_of_primeToEll G h0A3R
  set G₀ := (forgetZMod ℓ U).obj G
  set E := AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))
  have hE : Nonempty (E ≃+ ZMod ℓ) := ⟨AddEquiv.ulift⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Finite E := Finite.of_equiv _ AddEquiv.ulift.toEquiv.symm
  have hℓG : ℓ • 𝟙 G₀ = 0 := nsmul_id_forgetZMod_eq_zero ℓ U G
  -- the trace splits `G₀ ⟶ f_* f^{-1} G₀`
  set K := (etaleAbelianInverseImage.{u, 0} f).obj G₀
  obtain ⟨r, hr⟩ := exists_unit_comp_eq_id_of_finiteEtale f hℓ hd G₀ hℓG
  -- the finite extension `f̄ : Y ⟶ X`
  have : IsReduced U := isReduced_of_isOpenImmersion j
  have : IsReduced V := isReduced_of_etale f
  obtain ⟨Y, fb, j', _, _, hY, hw, ⟨e⟩⟩ := exists_isFinite_extensionByZero_directImage_iso j f
  have hdimY : topologicalKrullDim Y ≤ 1 := (topologicalKrullDim_le_of_isIntegralHom fb).trans hdim
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType_quasiCompact (fb ≫ π)
  -- the statements upstairs, for `j'_! K`
  have hL : CurveStatements.{u, 0, u + 1} (fb ≫ π) ((extensionByZero.{u, 0} j').obj K) :=
    curveStatements_extensionByZero_of_hasConstantFiltration hℓ E hE (fb ≫ π) hdimY j' hbase n
      K hfil
  have hcL : IsConstructibleOnEveryBigSite ((extensionByZero.{u, 0} j').obj K) :=
    isConstructibleOnEveryBigSite_extensionByZero_of_hasConstantFiltration j' E n K hfil
  have hℓL : ℓ • 𝟙 ((extensionByZero.{u, 0} j').obj K) = 0 :=
    nsmul_id_eq_zero_map _ (nsmul_id_eq_zero_map _ hℓG)
  -- the statements for `M = j_! f_* K ≅ f̄_* j'_! K`
  set M := (extensionByZero.{u, 0} j).obj ((etaleAbelianDirectImage.{u, 0} f).obj K)
  have hM : CurveStatements.{u, 0, u + 1} π M :=
    (CurveStatements.directImage_of_nsmul_eq_zero π fb hℓ hℓL hcL hL).of_iso (e.app K).symm
  have hℓM : ℓ • 𝟙 M = 0 :=
    nsmul_id_eq_zero_map _ (nsmul_id_eq_zero_map _ (nsmul_id_eq_zero_map _ hℓG))
  -- finiteness of the cohomology of `M`, computed upstairs
  let B := BigEtaleSite.containing Y
  have hYB : B.Contains Y := BigEtaleSite.contains_containing Y
  have hfin : ∀ q, Finite (Sheaf.H.{u + 1} ((extensionByZero.{u, 0} j').obj K) q) →
      Finite (Sheaf.H.{u + 1} M q) := fun q h ↦
    have : Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} fb).obj
        ((extensionByZero.{u, 0} j').obj K)) q) :=
      Finite.of_injective _ (etaleCohomologyDirectImageMap_bijective.{u, 0, u + 1} fb _ q).1
    @Finite.of_injective _ _ this _ (injective_sheafH_comp_mk₀_of_retract (e.app K).hom
      (e.app K).inv (e.app K).hom_inv_id q)
  refine CurveStatements.of_retract_of_finite
    ((extensionByZero.{u, 0} j).map ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app G₀))
    ((extensionByZero.{u, 0} j).map r)
    (by rw [← Functor.map_comp, hr]; exact CategoryTheory.Functor.map_id _ _) hℓ
    (nsmul_id_eq_zero_map _ hℓG) hℓM (fun htor q ↦ ?_) (fun hπ q ↦ ?_) hM
  · rcases coprime_ringExpChar_or_isZero k (S := X) hℓ with hcop | hz
    · exact hfin q (hL.finite_of_isPrimeToCharacteristicTorsion B hYB (hcL B hYB)
        (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos hcop hℓL) q)
    · have : Subsingleton (Sheaf.H.{u + 1} M q) := subsingleton_sheafH_of_isZero (hz M hℓM htor) q
      exact @Finite.of_subsingleton _ this
  · exact hfin q (hL.finite_of_isProper B hYB inferInstance (hcL B hYB) q)

/-- **The statement of Tag 0A3R, without its dictionary hypothesis**, for sheaves of
`F_ℓ`-vector spaces at the coefficient universe `u + 1`: every finite type locally constant sheaf
of `F_ℓ`-modules on the small étale site of a connected scheme becomes, after a finite étale cover
of degree prime to `ℓ`, a successive extension of copies of `Z/ℓZ`. This is the conclusion of
`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_constantFiltration` (Tag 0A3R) for every
such sheaf; it is the one input of the dévissage of Theorem 03SC that this library does not yet
prove unconditionally. -/
def PrimeToEllFiltrationStatement (ℓ : ℕ) : Prop :=
  ∀ (S : Scheme.{u}) [ConnectedSpace S]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))),
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology F →
      ∃ (T : Scheme.{u}) (f : T ⟶ S) (d : ℕ), IsFinite f ∧ Etale f ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d ∧ ¬ ℓ ∣ d ∧
        ∃ X : RelSeries (ConstantRankOneStep.{0} ℓ ((smallEtalePullbackZMod.{0} ℓ f).obj F)),
          IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow

/-- **Stacks Project, Lemma 03SD, granted Lemma 0A5B for `Z/ℓ`.** Let `X` be a reduced separated
scheme of finite type and dimension at most one over an algebraically closed field `k`,
`j : U ⟶ X` an open immersion with `U` connected, `ℓ` a prime and `G` a finite locally constant
abelian sheaf on `U_étale` killed by `ℓ` (a finite locally constant sheaf of `F_ℓ`-vector spaces).
If statements (1) -- (8) hold for `Z/ℓ` on every smooth curve over `k`, they hold for `j_! G`.
Tag 0A3R enters through its unconditional form
`Stacks.EtaleCohomology.exists_primeToEll_finiteEtale_relSeries_constantRankOneStep`. -/
theorem curveStatements_extensionByZero_of_isFiniteLocallyConstant {k : Type u} [Field k]
    [IsAlgClosed k] {ℓ : ℕ} (hℓ : ℓ.Prime) {X U : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (j : U ⟶ X) [IsOpenImmersion j] [ConnectedSpace U]
    (G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant U.smallEtaleTopology G] (hℓG : ℓ • 𝟙 G = 0)
    (hbase : CurveStatementsConstantOnSmoothCurves k (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))) :
    CurveStatements.{u, 0, u + 1} π ((extensionByZero.{u, 0} j).obj G) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType_quasiCompact π
  exact (curveStatements_extensionByZero_forgetZMod_of_primeToEll hℓ π hdim j hbase
    (zmodLift G hℓG) (exists_primeToEll_finiteEtale_relSeries_constantRankOneStep hℓ _
      (isFiniteTypeLocallyConstant_zmodLift G hℓG))).of_iso
    ((extensionByZero.{u, 0} j).mapIso (forgetZModZmodLiftIso G hℓG))

end Stacks.EtaleCohomology

end
