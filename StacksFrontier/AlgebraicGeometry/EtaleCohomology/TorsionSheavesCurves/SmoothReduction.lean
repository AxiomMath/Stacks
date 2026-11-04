module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsClopen
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Lemma 03SG: extension by zero of `Z/ℓ` on a smooth scheme of dimension at most one

Lemma 03SG of the source: in Situation 0A52 with `X` smooth, for an open immersion `j : U ⟶ X`
and a prime `ℓ`, statements (1) -- (8) hold for `j_! Z/ℓ`. The source's proof: `X` is a finite
disjoint union of smooth curves and points; on a curve `U` is empty or dense, and Lemmas 0A5B and
0GJA apply.

## Main results

* `Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_smooth`: Lemma 03SG,
  granted Lemma 0A5B for the constant sheaf on smooth curves, which is the hypothesis
  `Stacks.EtaleCohomology.CurveStatementsConstantOnSmoothCurves`.
* `Stacks.EtaleCohomology.curveStatements_extensionByZero_constantSheaf_of_irreducible`: the case
  of an irreducible `X`.
* `Stacks.EtaleCohomology.isConstructibleOnEveryBigSite_constantSheaf` and
  `Stacks.EtaleCohomology.isConstructibleOnEveryBigSite_extensionByZero_constantSheaf`: a finite
  constant sheaf and its extension by zero from an open of a Noetherian scheme are constructible.
* `Stacks.EtaleCohomology.exists_integral_isCompl_cover`: a normal Noetherian scheme is a finite
  disjoint union of integral open and closed subschemes (from Tag 033M).

## Implementation notes

**No `@[stacks 03SG]` attribute.** Lemma 0A5B, on which 03SG rests, is not yet proved in the
library; it enters as the explicit hypothesis `CurveStatementsConstantOnSmoothCurves k E`, so
the result is a reduction and is not registered.

The zero-dimensional components need no input: on a finite scheme over a separably closed field
every sheaf satisfies the statements (`Stacks.EtaleCohomology.curveStatements_of_finite`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace Order

universe u

namespace Stacks.EtaleCohomology

/-- A constant sheaf with finite value is finite locally constant: the identity covers every
object, and the restriction of a constant sheaf to a slice is constant. -/
theorem isFiniteLocallyConstant_constantSheaf {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ (U : C) (G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      (Over.forget U).op.HasPointwiseRightKanExtension G]
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant J
      ((constantSheaf J AddCommGrpCat.{u + 1}).obj M) where
  exists_finite_cover U :=
    ⟨PUnit, fun _ ↦ U, fun _ ↦ 𝟙 U, by
      refine J.superset_covering (fun V f _ ↦ ?_) (J.top_mem U)
      exact ⟨U, f, 𝟙 U, ⟨PUnit.unit⟩, by simp⟩, fun _ ↦
      ⟨M, inferInstance,
        ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso J AddCommGrpCat.{u + 1} U).app M⟩⟩⟩

/-- **A finite constant sheaf is constructible**, with respect to every ambient big étale site:
across the equivalence of the size-bounded small étale site with Mathlib's it is again a finite
constant sheaf, which is finite locally constant. -/
theorem isConstructibleOnEveryBigSite_constantSheaf (S : Scheme.{u})
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    IsConstructibleOnEveryBigSite
      ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) := by
  intro B hS _ _
  have : ∀ T : (S.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B S hS).op) AddCommGrpCat.{u + 1} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ ↦ inferInstance⟩
  have hT' : IsTerminal ((SmallEtale.toEtaleSite B S hS).obj (SmallEtale.final B S hS)) :=
    MorphismProperty.Over.mkIdTerminal _ _
  have e := (equivCommuteConstant' (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}
    S.smallEtaleTopology (SmallEtale.toEtaleSite B S hS) (SmallEtale.finalIsTerminal B S hS)
    hT').app M
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (B.obj S hS).obj (B.obj S hS).property)
      ((SmallEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}).inverse.obj
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M)) :=
    Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso _ e
      (isFiniteLocallyConstant_constantSheaf (SmallEtale.topology B S hS) M)
  exact isConstructibleAbelianSheaf_of_isFiniteLocallyConstant B (B.obj S hS) _

section Components

/-- **A normal Noetherian scheme is a finite disjoint union of integral open and closed
subschemes** (Tag 033M): a finite family of pairwise disjoint opens, each integral, each with an
open complement, covering the scheme. -/
theorem exists_integral_isCompl_cover (X : Scheme.{u}) [IsNoetherian X] [IsNormal X] :
    ∃ (ι : Type u) (_ : Finite ι) (Z W : ι → X.Opens),
      (∀ i, IsIntegral (Z i : Scheme.{u})) ∧ (∀ i, IsCompl (Z i) (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (Z i) (Z j)) ∧ (∀ x : X, ∃ i, x ∈ Z i) := by
  classical
  obtain ⟨ι, hι, Y, _, hY, ⟨e⟩⟩ := (isNormal_iff_exists_iso_finite_coproduct_integral_normal X).1
    inferInstance
  let Z : ι → X.Opens := fun i ↦ (Sigma.ι Y i ≫ e.inv).opensRange
  have hdisj : Pairwise fun i j ↦ Disjoint (Z i) (Z j) := fun i j hij ↦ by
    show Disjoint (Z i) (Z j)
    rw [disjoint_iff]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and, Z,
      Scheme.Hom.mem_opensRange]
    rintro ⟨a, rfl⟩ ⟨b, hb⟩
    have h : (Sigma.ι Y j).base b = (Sigma.ι Y i).base a := by
      have h := congrArg e.hom.base hb
      rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, Category.comp_id] at h
    exact (disjoint_opensRange_sigmaι Y j i (Ne.symm hij)).le_bot (show
      (Sigma.ι Y j).base b ∈ ((Sigma.ι Y j).opensRange ⊓ (Sigma.ι Y i).opensRange : _) from
      ⟨⟨b, rfl⟩, ⟨a, h.symm⟩⟩)
  have hcov : ∀ x : X, ∃ i, x ∈ Z i := fun x ↦ by
    obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Y).surjective (e.hom.base x)
    refine ⟨i, y, ?_⟩
    rw [sigmaMk_mk] at hy
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
    rw [hy, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  refine ⟨ι, hι, Z, fun i ↦ ⨆ j : {j // j ≠ i}, Z j, fun i ↦ ?_, fun i ↦ ⟨?_, ?_⟩, hdisj, hcov⟩
  · have := hY i
    have : Nonempty (Z i : Scheme.{u}) :=
      ⟨(Sigma.ι Y i ≫ e.inv).isoOpensRange.hom.base (Nonempty.some IsIntegral.nonempty)⟩
    exact isIntegral_of_isOpenImmersion (Sigma.ι Y i ≫ e.inv).isoOpensRange.inv
  · rw [disjoint_iSup_iff]
    exact fun j ↦ hdisj (Ne.symm j.2)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨j, hj⟩ := hcov x
    by_cases h : j = i
    · subst h
      exact Or.inl hj
    · exact Or.inr (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j, h⟩, hj⟩)

/-- In a Kolmogorov irreducible quasi-sober space, a Krull dimension not at least one forces
a single point: every point is a specialization of the generic point, and a strict one would give
a chain of length one. -/
theorem subsingleton_of_not_one_le_topologicalKrullDim {T : Type*} [TopologicalSpace T]
    [T0Space T] [QuasiSober T] [IrreducibleSpace T]
    (h : ¬ (1 : WithBot ℕ∞) ≤ topologicalKrullDim T) :
    Subsingleton T := by
  suffices hη : ∀ x : T, x = genericPoint T from ⟨fun x y ↦ (hη x).trans (hη y).symm⟩
  intro x
  by_contra hne
  apply h
  let c : T → IrreducibleCloseds T := fun a =>
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : c x < c (genericPoint T) := by
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp
      ((genericPoint_spec T).specializes (Set.mem_univ x))) fun hEq ↦ hne ?_
    exact (t0Space_iff_inseparable T).mp ‹_› _ _
      (inseparable_iff_closure_eq.mpr (congrArg IrreducibleCloseds.carrier hEq))
  have : ((1 : ℕ) : WithBot ℕ∞) ≤ krullDim (IrreducibleCloseds T) :=
    le_krullDim_iff.mpr ⟨RelSeries.singleton _ _ |>.snoc _ hlt, rfl⟩
  exact_mod_cast this

end Components

section Torsion

/-- A constant sheaf whose value is cyclic of order `ℓ` is killed by `ℓ`. -/
theorem nsmul_id_constantSheaf_eq_zero (S : Scheme.{u}) {ℓ : ℕ} (E : AddCommGrpCat.{u + 1})
    (hE : Nonempty (E ≃+ ZMod ℓ)) :
    ℓ • 𝟙 ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) = 0 := by
  refine nsmul_id_eq_zero_map _ ?_
  obtain ⟨e⟩ := hE
  ext x
  apply e.injective
  simp [map_nsmul]

/-- A sheaf killed by a prime `ℓ` is either `ℓ`-power torsion with `ℓ` the exponential
characteristic, or of torsion prime to the exponential characteristic. -/
theorem isPrimePowerTorsion_or_isPrimeToCharacteristicTorsion_of_nsmul_eq_zero
    (k : Type*) [Field k] {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F : Sheaf J AddCommGrpCat.{u + 1}} {ℓ : ℕ} (hℓ : ℓ.Prime) (hF : ℓ • 𝟙 F = 0) :
    Stacks.Torsion.IsPrimePowerTorsion J (ringExpChar k) F ∨
      Stacks.Torsion.IsPrimeToCharacteristicTorsion J (ringExpChar k) F := by
  by_cases hℓp : ℓ = ringExpChar k
  · exact Or.inl (hℓp ▸ isPrimePowerTorsion_of_nsmul_eq_zero hF)
  · refine Or.inr (isPrimeToCharacteristicTorsion_of_nsmul_eq_zero hℓ.pos ?_ hF)
    rcases expChar_is_prime_or_one k (ringExpChar k) with hp | h1
    · exact (Nat.coprime_primes hℓ hp).mpr hℓp
    · exact h1 ▸ Nat.coprime_one_right ℓ

end Torsion

section Extension

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j] (E : AddCommGrpCat.{u + 1})

/-- The extension by zero of a constant sheaf on an open `V` is the extension by zero of the
restriction to `V` of the constant sheaf: restriction carries constant sheaves to constant
sheaves. -/
def extensionByZeroConstantSheafIso :
    (extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) ≅
      (extensionByZero.{u, 0} j).obj ((etaleRestriction.{u, 0} j).obj
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) :=
  (extensionByZero.{u, 0} j).mapIso
    (((etaleAbelianInverseImageConstantIso.{u, 0} j).app E).symm ≪≫
      (etaleAbelianInverseImageRestrictionIso.{u, 0} j).app _)

/-- **The extension by zero of a finite constant sheaf from an open of a Noetherian scheme is
constructible**, with respect to every ambient big étale site (Tags 03S8 (2) and 095M, remark (b)
of the proof of Tag 0GJA). -/
theorem isConstructibleOnEveryBigSite_extensionByZero_constantSheaf [IsNoetherian S] [Finite E] :
    IsConstructibleOnEveryBigSite ((extensionByZero.{u, 0} j).obj
      ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) :=
  IsConstructibleOnEveryBigSite.of_iso (extensionByZeroConstantSheafIso j E).symm
    fun B hS _ _ ↦ isConstructibleEtaleAbelianSheaf_extensionByZero_etaleRestriction B hS j _
      (isConstructibleOnEveryBigSite_constantSheaf S E B hS)

/-- The extension by zero from an empty scheme is zero. -/
theorem isZero_extensionByZero_of_isEmpty [IsEmpty V]
    (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsZero ((extensionByZero.{u, 0} j).obj G) :=
  (extensionByZero.{u, 0} j).map_isZero (isZero_of_forall_isZero_sections.{u, 0} _ fun W ↦
    isZero_sections_of_isEmpty.{u, 0} _ W ⟨fun x ↦ IsEmpty.false (α := V) (W.hom.base x)⟩)

/-- **The restriction to `Y` of the extension by zero of a constant sheaf from `V` is the
extension by zero of the constant sheaf from `V ×_S Y`** (Tag 03S6 and the inverse image of a
constant sheaf). -/
def inverseImageExtensionByZeroConstantSheafIso {Y : Scheme.{u}} (f : Y ⟶ S) :
    (etaleAbelianInverseImage.{u, 0} f).obj ((extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) ≅
      (extensionByZero.{u, 0} (pullback.snd j f)).obj
        ((constantSheaf (pullback j f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj E) :=
  ((extensionByZeroBaseChangeIso.{u, 0} j f).app _).symm ≪≫
    (extensionByZero.{u, 0} (pullback.snd j f)).mapIso
      ((etaleAbelianInverseImageConstantIso.{u, 0} (pullback.fst j f)).app E)

end Extension

section Smooth

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} (hℓ : ℓ.Prime) (E : AddCommGrpCat.{u + 1})
  (hE : Nonempty (E ≃+ ZMod ℓ))

variable (k) in
/-- **The base case of the dévissage, Lemma 0A5B for `E`**: statements (1) -- (8) of Situation
0A52 hold for the constant sheaf with value `E` on every smooth curve over `k`. Lemma 03SG and
everything after it in the proof of Theorem 03SC are deduced from it. -/
def CurveStatementsConstantOnSmoothCurves : Prop :=
  ∀ (C : Scheme.{u}) (g : C ⟶ Spec (.of k)) [IsCurve k g] [Smooth g],
    CurveStatements.{u, 0, u + 1} g
      ((constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)

/-- A scheme quasi-compact and locally of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_of_quasiCompact {X : Scheme.{u}}
    {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] [QuasiCompact π] :
    IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian π
  have := QuasiCompact.compactSpace_of_compactSpace π
  ⟨⟩

/-- An abelian group isomorphic to `ZMod ℓ` for a prime `ℓ` is finite. -/
private theorem finite_of_nonempty_addEquiv_zmod {ℓ : ℕ} (hℓ : ℓ.Prime)
    {E : AddCommGrpCat.{u + 1}} (hE : Nonempty (E ≃+ ZMod ℓ)) : Finite E :=
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  hE.elim fun e ↦ Finite.of_equiv _ e.toEquiv.symm

include hℓ hE in
/-- **Lemma 03SG for an irreducible `X`.** Either `X` is a point, where every sheaf satisfies the
statements, or `X` is a smooth curve, where they hold for the constant sheaf by Lemma 0A5B and
pass to its extension by zero from a nonempty, hence dense, open by Lemma 0GJA. -/
theorem curveStatements_extensionByZero_constantSheaf_of_irreducible {X V : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [Smooth π]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) (j : V ⟶ X) [IsOpenImmersion j]
    (hbase : CurveStatementsConstantOnSmoothCurves k E) :
    CurveStatements.{u, 0, u + 1} π
      ((extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) := by
  have := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have := finite_of_nonempty_addEquiv_zmod hℓ hE
  by_cases h1 : (1 : WithBot ℕ∞) ≤ topologicalKrullDim X
  · have : IsReduced X := isReduced_of_smooth_of_isAffine π
    have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
    have : IsVariety k π := ⟨⟩
    have : IsCurve k π := ⟨le_antisymm hdim h1⟩
    rcases isEmpty_or_nonempty V with hV | hV
    · exact CurveStatements.of_isZero π (isZero_extensionByZero_of_isEmpty j _)
    have hj : Dense (Set.range j.base) :=
      j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
    refine CurveStatements.of_iso (extensionByZeroConstantSheafIso j E).symm ?_
    exact curveStatements_extensionByZero_of_curveStatements_of_dense.{u, 0, u + 1} π hdim j hj _
      (fun B hX _ _ ↦ isConstructibleOnEveryBigSite_constantSheaf X E B hX)
      (isPrimePowerTorsion_or_isPrimeToCharacteristicTorsion_of_nsmul_eq_zero k hℓ
        (nsmul_id_constantSheaf_eq_zero _ E hE))
      (hbase X π)
  · have := subsingleton_of_not_one_le_topologicalKrullDim h1
    exact curveStatements_of_finite π _

include hℓ hE in
/-- **Stacks Project, Lemma 03SG, granted Lemma 0A5B for the constant sheaf.** Let `X` be a
smooth separated scheme of finite type and dimension at most one over an algebraically closed
field `k`, let `j : V ⟶ X` be an open immersion and `E` cyclic of prime order `ℓ`. If statements
(1) -- (8) of Situation 0A52 hold for the constant sheaf `E` on every smooth curve over `k`, they
hold for `j_! E`.

`X` is normal, hence the finite disjoint union of its integral open and closed subschemes
(Tag 033M); on each of them the restriction of `j_! E` is again an extension by zero of the
constant sheaf, for which the irreducible case applies; the pieces are reassembled by
`Stacks.EtaleCohomology.CurveStatements.of_finite_isCompl_cover`. -/
theorem curveStatements_extensionByZero_constantSheaf_of_smooth {X V : Scheme.{u}}
    (π : X ⟶ Spec (.of k)) [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π] [Smooth π]
    (hdim : topologicalKrullDim X ≤ 1) (j : V ⟶ X) [IsOpenImmersion j]
    (hbase : CurveStatementsConstantOnSmoothCurves k E) :
    CurveStatements.{u, 0, u + 1} π
      ((extensionByZero.{u, 0} j).obj
        ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj E)) := by
  have := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have := finite_of_nonempty_addEquiv_zmod hℓ hE
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal X := isNormal_of_smooth π
  obtain ⟨ι, _, Z, W, hint, hZW, hdisj, hcov⟩ := exists_integral_isCompl_cover X
  have hnoeth : ∀ i, IsNoetherian (Z i : Scheme.{u}) := fun i ↦
    have : TopologicalSpace.NoetherianSpace (Z i : Scheme.{u}) :=
      TopologicalSpace.NoetherianSpace.set (Z i : Set X)
    ⟨⟩
  refine CurveStatements.of_finite_isCompl_cover (π := π) hℓ Z W hZW hdisj hcov _
    (nsmul_id_eq_zero_map _ (nsmul_id_constantSheaf_eq_zero V E hE)) (fun i ↦ ?_) (fun i ↦ ?_)
  · have := hnoeth i
    exact (isConstructibleOnEveryBigSite_extensionByZero_constantSheaf _ E).of_iso
      (inverseImageExtensionByZeroConstantSheafIso j E (Z i).ι).symm
  · have := hnoeth i
    have := hint i
    refine CurveStatements.of_iso (inverseImageExtensionByZeroConstantSheafIso j E (Z i).ι).symm ?_
    exact curveStatements_extensionByZero_constantSheaf_of_irreducible hℓ E hE ((Z i).ι ≫ π)
      ((topologicalKrullDim_subspace_le X (Z i : Set X)).trans hdim) _ hbase

end Smooth

end Stacks.EtaleCohomology

end
