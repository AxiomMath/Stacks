module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerFibrePower
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerTorsion
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSymmetricPower
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# The cycle computation of Voevodsky nilpotence along the symmetric power

This file specialises
`Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_normChern` to the data of
the source: `X` a smooth proper geometrically irreducible curve over an algebraically closed field
`k`, `H d` representing the Hilbert functors of points of `X`, `π : Xⁿ ⟶ Hₙ` the symmetric power
map of Stacks 0B9G (`Stacks.Hilbert.symmetricPowerMap`), and `𝒩 = Norm_π(pr_{i₀}^*ℒ)`. Every
hypothesis of the general statement other than the torsion of `c₁(𝒩)ⁿ ∩ [Hₙ]` is discharged:

* the fibre power of the smash power is identified with `∏ᶜ` by
  `Stacks.Chow.smashFibrePowerIso`;
* the Picard relation `[π^*𝒩] = (n-1)! • ∑ᵢ [prᵢ^*ℒ]` is
  `Stacks.SheafOfModules.pullbackPicardClass_normInvertible_symmetricPowerMap`, transported along
  that identification;
* `X` is a curve (`Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one`), Noetherian, and carries
  an ample invertible module (Stacks 09ND, `exists_isAmple_of_topologicalKrullDim_le_one`);
* `dim_δ Hₙ ≤ n`, because `π` is finite locally free of positive degree, hence surjective and
  dimension preserving (`Stacks.Chow.schemeDeltaDimension_le_of_isFiniteLocallyFreeOfRank`).

## Main results

* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_symmetricPowerNorm`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0B9G](https://stacks.math.columbia.edu/tag/0B9G)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Dimension along a finite locally free morphism -/

/-- A finite locally free morphism is finite, flat and locally of finite presentation. -/
private theorem isFinite_flat_locallyOfFinitePresentation_of_isFiniteLocallyFreeOfRank
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] :
    IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f :=
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f d)

/-- A finite locally free morphism of positive degree is surjective. -/
theorem surjective_of_isFiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) {d : ℕ}
    (hd : 0 < d) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] : Surjective f := by
  have h := isFinite_flat_locallyOfFinitePresentation_of_isFiniteLocallyFreeOfRank f d
  have : IsFinite f := h.1
  have : Flat f := h.2.1
  refine f.one_le_finrank_iff_surjective.mp fun y => ?_
  rw [(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f d).mp inferInstance y]
  exact hd

/-- **The target of a finite locally free morphism of positive degree is locally of finite type
over the base when its source is.** Local finite type descends along the surjective flat
morphism of finite presentation (Stacks 02KL). -/
theorem locallyOfFiniteType_of_isFiniteLocallyFreeOfRank_comp {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (q : Y ⟶ S) {d : ℕ} (hd : 0 < d) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    [LocallyOfFiniteType (f ≫ q)] : LocallyOfFiniteType q := by
  have h := isFinite_flat_locallyOfFinitePresentation_of_isFiniteLocallyFreeOfRank f d
  have : Flat f := h.2.1
  have : LocallyOfFinitePresentation f := h.2.2
  have : Surjective f := surjective_of_isFiniteLocallyFreeOfRank f hd
  exact locallyOfFiniteType_of_comp_of_fppf f q

/-- **Delta-dimension does not grow along a finite locally free morphism of positive degree.**
If `π : T ⟶ H` is finite locally free of degree `d > 0` over the base and `dim_δ T ≤ n`, then
`dim_δ H ≤ n`: `π` is surjective and preserves the delta-dimension of points. -/
theorem schemeDeltaDimension_le_of_isFiniteLocallyFreeOfRank (C : ChowSituation.{u})
    {T H : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (sH : H ⟶ C.S)
    [LocallyOfFiniteType sH] (π : T ⟶ H) {d : ℕ} (hd : 0 < d)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d] (hπ : π ≫ sH = sT) {n : ℤ}
    (hT : schemeDeltaDimension C sT ≤ (n : EInt)) :
    schemeDeltaDimension C sH ≤ (n : EInt) := by
  have : LocallyOfFiniteType π :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank π d
  have hsurj := (surjective_of_isFiniteLocallyFreeOfRank π hd).surj
  have congr : ∀ {Z : Scheme.{u}} (a b : Z ⟶ C.S) [LocallyOfFiniteType a]
      [LocallyOfFiniteType b], a = b → schemeDeltaDimension C a = schemeDeltaDimension C b := by
    rintro Z a b _ _ rfl; rfl
  have hT' : schemeDeltaDimension C (𝟙 T ≫ sT) ≤ (n : EInt) :=
    (congr _ _ (Category.id_comp sT)).trans_le hT
  have hH := schemeDeltaDimension_le_of_forall_relativeDimension_le C sH (𝟙 H) (k := n)
    fun h => by
      obtain ⟨t, rfl⟩ := hsurj h
      have h1 := relativeDimension_eq_of_relativeDimension_zero C sT sH π hπ
        (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank π d) t
      have h2 := relativeDimension_le_of_schemeDeltaDimension_le C sT (𝟙 T) hT' t
      exact h1 ▸ h2
  exact (congr _ _ (Category.id_comp sH)).symm.trans_le hH

/-! ### A smooth proper geometrically irreducible curve -/

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIrreducible f]

omit [IsProper f] in
include f in
/-- A smooth proper geometrically irreducible scheme over a field is integral. -/
theorem isIntegral_of_smooth_of_geometricallyIrreducible : IsIntegral X := by
  have : Subsingleton (Spec (.of k)) := by
    change Subsingleton (PrimeSpectrum k)
    exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField k)
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth f

omit [IsProper f] in
include f in
/-- A smooth proper geometrically irreducible scheme of relative dimension one over a field has
dimension one. -/
theorem topologicalKrullDim_eq_one_of_smoothOfRelativeDimension_one :
    topologicalKrullDim X = 1 := by
  have := isIntegral_of_smooth_of_geometricallyIrreducible f
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f

/-- A smooth proper geometrically irreducible scheme of relative dimension one over a field is a
curve. -/
theorem isCurve_of_smoothOfRelativeDimension_one : IsCurve k f :=
  have := isIntegral_of_smooth_of_geometricallyIrreducible f
  { topologicalKrullDim_eq_one := topologicalKrullDim_eq_one_of_smoothOfRelativeDimension_one f }

omit [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f] in
include f in
/-- A scheme proper over a field is Noetherian. -/
theorem isNoetherian_of_isProper : IsNoetherian X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  {}

include f in
/-- **A proper curve over a field carries an ample invertible module**, Stacks 09ND. -/
theorem exists_isAmple_of_smoothOfRelativeDimension_one :
    ∃ (A : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X A), Stacks.Ample.IsAmple X A := by
  have := isIntegral_of_smooth_of_geometricallyIrreducible f
  have := isNoetherian_of_isProper f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨A, hA, hamp⟩ := StacksTag09NX.exists_isAmple_of_topologicalKrullDim_le_one X
    (topologicalKrullDim_eq_one_of_smoothOfRelativeDimension_one f).le
  exact ⟨A, hA, Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple X A hamp⟩

end Curve

/-! ### The symmetric power -/

section SymmetricPower

open Stacks.Hilbert Nat
open scoped Stacks.AlgebraicGeometry.AmpleLimit

attribute [local instance] SmashPowerData.finiteType

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [SmoothOfRelativeDimension 1 X.hom]
  [IsProper X.hom] {H : ℕ → Over (Spec (.of k))}
  (hH : ∀ d, RepresentsHilbertFunctorOfRank X (H d) d)

include hH in
/-- The target `Hₙ` of the symmetric power map is locally of finite type over `k`: local finite
type descends along the finite locally free surjection `π : Xⁿ ⟶ Hₙ`. -/
theorem locallyOfFiniteType_hilbert_hom (n : ℕ) : LocallyOfFiniteType (H n).hom := by
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : LocallyOfFiniteType ((symmetricPowerMap hH n).left ≫ (H n).hom) := by
    rw [Over.w]; infer_instance
  exact locallyOfFiniteType_of_isFiniteLocallyFreeOfRank_comp (symmetricPowerMap hH n).left
    (H n).hom (factorial_pos n)

/-- **The norm sheaf `𝒩 = Norm_π(pr_{i₀}^*ℒ)` of Stacks 0FH9** on `Hₙ`, for the canonical norm
of Tag 0BD2 along the symmetric power map `π : Xⁿ ⟶ Hₙ`. -/
def symmetricPowerNorm (n : ℕ) (i₀ : Fin n) (L : X.left.Modules) : (H n).left.Modules :=
  Stacks.Divisors.normInvertible (symmetricPowerMap hH n).left
    (Stacks.Divisors.finiteLocallyFreeNormOfRank (symmetricPowerMap hH n).left n !
      (factorial_pos n)).1.toMorphismNormMap
    ((Scheme.Modules.pullback (Pi.π (fun _ : Fin n => X) i₀).left).obj L)

/-- The norm sheaf is invertible. -/
theorem isInvertible_symmetricPowerNorm (n : ℕ) (i₀ : Fin n) (L : X.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.left.sheaf.obj X.left.ringCatSheaf.property
      L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible (H n).left.sheaf.obj
      (H n).left.ringCatSheaf.property (symmetricPowerNorm hH n i₀ L) := by
  have hpb : AlgebraicGeometry.SheafOfModules.IsInvertible
      (∏ᶜ fun _ : Fin n => X).left.sheaf.obj (∏ᶜ fun _ : Fin n => X).left.ringCatSheaf.property
      ((Scheme.Modules.pullback (Pi.π (fun _ : Fin n => X) i₀).left).obj L) := inferInstance
  unfold symmetricPowerNorm
  exact Stacks.Divisors.isInvertible_normInvertible (symmetricPowerMap hH n).left _ _
    (Stacks.Divisors.hasTrivializingTargetCover_of_isFinite_of_isInvertible
      (symmetricPowerMap hH n).left _ hpb)

variable [GeometricallyIrreducible X.hom]

/-- **The cycle computation of Stacks 0FH9 in the curve case, along the symmetric power.** Let
`k` be algebraically closed, `X` a smooth proper geometrically irreducible curve over `k`, `H d`
representing the Hilbert functors of points of `X`, `x`, `x'` rational points, and `ℒ` invertible
on `X` with `c₁(ℒ) ∩ [X] = [x] - [x']` (for instance `𝒪_X(x - x')`,
`Stacks.Chow.exists_invCap_capOnChow_fundamentalChowClass_eq_pointDifference`). Let
`𝒩 = Norm_π(pr_{i₀}^*ℒ)` along the symmetric power map `π : Xⁿ ⟶ Hₙ`. If `c₁(𝒩)ⁿ ∩ [Hₙ]` is
torsion in `CH_0(Hₙ)`, then the smash power `([x] - [x'])^{×n}` is torsion in `CH_0(Xⁿ)`. -/
theorem isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_symmetricPowerNorm
    [IsAlgClosed k] (x x' : Spec (.of k) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    (hx' : x' ≫ X.hom = 𝟙 _) (L : X.left.Modules)
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.left.sheaf.obj
      X.left.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) X.hom L).capOnChow (fieldChowSituation k) X.hom 0
      (fundamentalChowClass (fieldChowSituation k) X.hom (0 + 1)) =
        pointDifference k X.hom x x' hx hx')
    (n : ℕ) (i₀ : Fin n) :
    letI := locallyOfFiniteType_hilbert_hom hH n
    letI := isInvertible_symmetricPowerNorm hH n i₀ L
    IsOfFinAddOrder (iteratedChernCapOnChow (fieldChowSituation k) (H n).hom
        (List.ofFn fun _ : Fin n => invCap (fieldChowSituation k) (H n).hom
          (symmetricPowerNorm hH n i₀ L)) 0
        (fundamentalChowClass (fieldChowSituation k) (H n).hom
          (0 + ((List.ofFn fun _ : Fin n => invCap (fieldChowSituation k) (H n).hom
            (symmetricPowerNorm hH n i₀ L)).length : ℤ)))) →
      IsOfFinAddOrder (smashPointDifference k X.hom x x' hx hx' n).cycle := by
  intro htors
  have := locallyOfFiniteType_hilbert_hom hH n
  have := isInvertible_symmetricPowerNorm hH n i₀ L
  have hint := isIntegral_of_smooth_of_geometricallyIrreducible X.hom
  have hdim := topologicalKrullDim_eq_one_of_smoothOfRelativeDimension_one X.hom
  have := isNoetherian_of_isProper X.hom
  have hvar : IsVariety k X.hom := {}
  obtain ⟨A, hAinv, hA⟩ := exists_isAmple_of_smoothOfRelativeDimension_one X.hom
  -- the map `π' = e ≫ π : Xⁿ ⟶ Hₙ` from the smash power's fibre power
  set e := smashFibrePowerIso k X x x' hx hx' n
  set π' := e.hom.left ≫ (symmetricPowerMap hH n).left with hπ'def
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank π' n ! :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp ((Over.forget _).mapIso e) _
      inferInstance
  have hπ' : π' ≫ (H n).hom = (smashPointDifference k X.hom x x' hx hx' n).Y.hom := by
    rw [hπ'def, Category.assoc, Over.w, Over.w]
  -- `dim_δ Hₙ ≤ n`
  obtain ⟨hvarY, hdimY⟩ := isVariety_smashPointDifference k X.hom x x' hx hx' 1
    (by rw [hdim]; rfl) n
  have hdimT : schemeDeltaDimension (fieldChowSituation k)
      (smashPointDifference k X.hom x x' hx hx' n).Y.hom ≤ ((n : ℤ) : EInt) :=
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq _
      (n := n) (by rw [hdimY, mul_one])).le
  have hdimH := schemeDeltaDimension_le_of_isFiniteLocallyFreeOfRank (fieldChowSituation k)
    _ (H n).hom π' (factorial_pos n) hπ' hdimT
  -- the Picard relation, transported along `e`
  have hpic : Stacks.SheafOfModules.pullbackPicardClass π' (symmetricPowerNorm hH n i₀ L)
      (isInvertible_symmetricPowerNorm hH n i₀ L) =
      (n - 1) ! • ∑ i, Stacks.SheafOfModules.pullbackPicardClass
        (smashProjection k X.hom x x' hx hx' n i) L hLinv := by
    have h0 := Stacks.SheafOfModules.pullbackPicardClass_normInvertible_symmetricPowerMap hH n
      i₀ L hLinv (fun i => (Scheme.Modules.pullback (Pi.π (fun _ : Fin n => X) i).left).obj L)
      (fun i => (inferInstance : AlgebraicGeometry.SheafOfModules.IsInvertible
        (∏ᶜ fun _ : Fin n => X).left.sheaf.obj (∏ᶜ fun _ : Fin n => X).left.ringCatSheaf.property
        ((Scheme.Modules.pullback (Pi.π (fun _ : Fin n => X) i).left).obj L)))
      (fun _ => rfl)
    have hNs : Stacks.SheafOfModules.IsInvertible (H n).left.presheaf (H n).left.ringCatIsSheaf
        (symmetricPowerNorm hH n i₀ L) := isInvertible_symmetricPowerNorm hH n i₀ L
    have hpb := Stacks.RingedSpace.modulePullback_isInvertible
      (symmetricPowerMap hH n).left.toLRSHom.toShHom (symmetricPowerNorm hH n i₀ L)
    have h0' : Stacks.SheafOfModules.pullbackPicardClass (symmetricPowerMap hH n).left
        (symmetricPowerNorm hH n i₀ L) hNs =
        (n - 1) ! • ∑ i, Stacks.SheafOfModules.pullbackPicardClass
          (Pi.π (fun _ : Fin n => X) i).left L hLinv := h0
    have step : Stacks.SheafOfModules.pullbackPicardClass π' (symmetricPowerNorm hH n i₀ L)
        (isInvertible_symmetricPowerNorm hH n i₀ L) =
        Stacks.SheafOfModules.pullbackPicardHom e.hom.left
          (Stacks.SheafOfModules.pullbackPicardClass (symmetricPowerMap hH n).left
            (symmetricPowerNorm hH n i₀ L) hNs) :=
      (Stacks.SheafOfModules.pullbackPicardClass_comp e.hom.left (symmetricPowerMap hH n).left
        (symmetricPowerNorm hH n i₀ L) hNs hpb).trans
        (Stacks.SheafOfModules.pullbackPicardHom_picardClass e.hom.left _ hpb).symm
    rw [step, h0', map_nsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Stacks.SheafOfModules.IsInvertible X.left.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.left.IsSheaf) L :=
      hLinv
    have hi := Stacks.SheafOfModules.pullbackPicardClass_comp e.hom.left
      (Pi.π (fun _ : Fin n => X) i).left L hLinv
      (Stacks.RingedSpace.modulePullback_isInvertible _ L)
    refine ((Stacks.SheafOfModules.pullbackPicardHom_picardClass e.hom.left _
      (Stacks.RingedSpace.modulePullback_isInvertible _ L)).trans hi.symm).trans ?_
    rw [smashFibrePowerIso_hom_left_comp_π]
  exact isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_normChern k X.hom hdim A hA x x'
    hx hx' L hL n (H n).hom hdimH π' (d := n !) hπ' (symmetricPowerNorm hH n i₀ L) (n - 1) !
    (factorial_ne_zero _) hpic htors

end SymmetricPower

end Stacks.Chow

end
