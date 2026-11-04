module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPicardPullbackVanishing
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.SurjectiveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower

/-!
# The curve case of Voevodsky nilpotence, given the factorization through `Pic^n`

The last step of the curve case of Stacks 0FH9: the norm sheaf `𝒩 = Norm_π(pr_{i₀}^*ℒ)` on
`Sⁿ(X) = Hₙ` is pulled back from a scheme `P` of dimension `g < n` (in the source,
`P = Pic^n_{X/k}` of dimension `g`, with `𝒩 = f^*ℳ` by the projective space bundle formula), so
`c₁(𝒩)ⁿ ∩ [Hₙ] = 0` by Stacks 0FDX
(`Stacks.Chow.iteratedChernCapOnChow_replicate_eq_zero_of_pullbackPicardClass`), and the smash
power is torsion by
`Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_symmetricPowerNorm`.

## What is required of `P`

`P` is locally of finite type over `k`, Noetherian, of topological dimension at most `g`, and
carries an ample invertible module `A`; the morphism `u : Hₙ ⟶ P` is over `k` and
`[𝒩] = u^*[ℳ]` in `Pic(Hₙ)` for an invertible `ℳ` on `P`.

## Main results

* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_pullbackPicardClass_symmetricPowerNorm` —
  the factorization through a Noetherian `P` with an ample module.
* `Stacks.Chow.isOfFinAddOrder_smashPointDifference_of_flat_pullbackPicardClass_symmetricPowerNorm`
  — the factorization through a flat `f : Hₙ ⟶ P` of relative dimension `n - g`, with nothing
  required of `P` beyond local finite type over `k` and `dim P ≤ g`.
* `isOfFinAddOrder_smashPointDifference_of_surjective_pullbackPicardClass_symmetricPowerNorm`
  — the same with `dim P ≤ g` replaced by surjectivity of `f`; `P` is only locally of finite
  type.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Hilbert
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [SmoothOfRelativeDimension 1 X.hom]
  [IsProper X.hom] [GeometricallyIrreducible X.hom] {H : ℕ → Over (Spec (.of k))}
  (hH : ∀ d, RepresentsHilbertFunctorOfRank X (H d) d)

/-- **The curve case of Stacks 0FH9, given the factorization through a scheme of dimension
`g < n`.** Let `k` be algebraically closed, `X` a smooth proper geometrically irreducible curve
over `k`, `H d` representing its Hilbert functors of points, `x`, `x'` rational points and `ℒ`
invertible on `X` with `c₁(ℒ) ∩ [X] = [x] - [x']`. Let `𝒩 = Norm_π(pr_{i₀}^*ℒ)` on `Hₙ`. If
`[𝒩] = u^*[ℳ]` for a morphism `u : Hₙ ⟶ P` over `k` to a Noetherian scheme `P` locally of
finite type over `k`, of dimension at most `g < n` and carrying an ample invertible module, and
an invertible `ℳ` on `P`, then the smash power `([x] - [x'])^{×n}` is torsion in `CH_0(Xⁿ)`. -/
theorem isOfFinAddOrder_smashPointDifference_of_pullbackPicardClass_symmetricPowerNorm
    [IsAlgClosed k] (x x' : Spec (.of k) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    (hx' : x' ≫ X.hom = 𝟙 _) (L : X.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.left.sheaf.obj
      X.left.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) X.hom L).capOnChow (fieldChowSituation k) X.hom 0
      (fundamentalChowClass (fieldChowSituation k) X.hom (0 + 1)) =
        pointDifference k X.hom x x' hx hx')
    (n : ℕ) (i₀ : Fin n) {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP]
    [IsNoetherian P] (A : P.Modules) [Stacks.Ample.IsInvertibleModule P A]
    (hA : Stacks.Ample.IsAmple P A) (g : ℕ) (hdim : topologicalKrullDim P ≤ (g : WithBot ℕ∞))
    (hn : g < n) (f : (H n).left ⟶ P) (hf : f ≫ sP = (H n).hom) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass f M hM =
      (H n).left.picardClass (symmetricPowerNorm hH n i₀ L)
        (isInvertible_symmetricPowerNorm hH n i₀ L)) :
    IsOfFinAddOrder (smashPointDifference k X.hom x x' hx hx' n).cycle := by
  have := locallyOfFiniteType_hilbert_hom hH n
  have := isInvertible_symmetricPowerNorm hH n i₀ L
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sP) := by rw [hf]; infer_instance
    exact LocallyOfFiniteType.of_comp (f := f) (g := sP) this
  refine isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_symmetricPowerNorm hH x x' hx hx'
    L hL n i₀ ?_
  rw [iteratedChernCapOnChow_replicate_eq_zero_of_pullbackPicardClass (fieldChowSituation k)
    (H n).hom sP A hA g hdim f hf M _ hNM hn]
  exact IsOfFinAddOrder.zero

omit [AlgebraicGeometry.GeometricallyIrreducible X.hom] in
include hH in
/-- A morphism over `k` from `Hₙ` to a scheme locally of finite type over `k` is locally of
finite type. -/
theorem locallyOfFiniteType_of_comp_eq_hilbert_hom (n : ℕ) {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP] (f : (H n).left ⟶ P)
    (hf : f ≫ sP = (H n).hom) : LocallyOfFiniteType f := by
  have := locallyOfFiniteType_hilbert_hom hH n
  have : LocallyOfFiniteType (f ≫ sP) := by rw [hf]; infer_instance
  exact LocallyOfFiniteType.of_comp (f := f) (g := sP) this

/-- **The curve case of Stacks 0FH9, given a flat factorization through a scheme of dimension
`g < n`.** As `isOfFinAddOrder_smashPointDifference_of_pullbackPicardClass_symmetricPowerNorm`,
but with no hypothesis on `P` beyond local finite type over `k` and `dim P ≤ g`: instead the
morphism `f : Hₙ ⟶ P` over `k` is flat of relative dimension `r` with `g + r = n` (in the source
the Abel map `Sⁿ(X) ⟶ Pic^n_{X/k}`, a projective bundle with fibres `ℙ^{n-g}`). If
`[𝒩] = f^*[ℳ]` in `Pic(Hₙ)` for an invertible `ℳ` on `P`, the smash power `([x] - [x'])^{×n}` is
torsion in `CH_0(Xⁿ)`. -/
theorem isOfFinAddOrder_smashPointDifference_of_flat_pullbackPicardClass_symmetricPowerNorm
    [IsAlgClosed k] (x x' : Spec (.of k) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    (hx' : x' ≫ X.hom = 𝟙 _) (L : X.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.left.sheaf.obj
      X.left.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) X.hom L).capOnChow (fieldChowSituation k) X.hom 0
      (fundamentalChowClass (fieldChowSituation k) X.hom (0 + 1)) =
        pointDifference k X.hom x x' hx hx')
    (n : ℕ) (i₀ : Fin n) {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP]
    (g r : ℕ) (hdim : topologicalKrullDim P ≤ (g : WithBot ℕ∞)) (hgr : g + r = n) (hn : g < n)
    (f : (H n).left ⟶ P) [Flat f] (hf : f ≫ sP = (H n).hom)
    (hrel : letI := locallyOfFiniteType_of_comp_eq_hilbert_hom hH n sP f hf
      AlgebraicGeometry.RelativeDimension f r) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass f M hM =
      (H n).left.picardClass (symmetricPowerNorm hH n i₀ L)
        (isInvertible_symmetricPowerNorm hH n i₀ L)) :
    IsOfFinAddOrder (smashPointDifference k X.hom x x' hx hx' n).cycle := by
  have := locallyOfFiniteType_hilbert_hom hH n
  have := isInvertible_symmetricPowerNorm hH n i₀ L
  have := locallyOfFiniteType_of_comp_eq_hilbert_hom hH n sP f hf
  refine isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_symmetricPowerNorm hH x x' hx hx'
    L hL n i₀ ?_
  rw [iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat (fieldChowSituation k)
    (fun _ _ => rfl) (H n).hom sP g r n hdim hgr hn f hf hrel M _ hNM]
  exact IsOfFinAddOrder.zero

include hH in
/-- **`dim_δ Hₙ ≤ n`**: the symmetric power map `Xⁿ ⟶ Hₙ` is finite locally free of degree
`n! > 0`, hence surjective and dimension preserving, and `Xⁿ` is a variety of dimension `n`. -/
theorem schemeDeltaDimension_hilbert_hom_le [IsAlgClosed k] (x : Spec (.of k) ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 _) (n : ℕ) :
    letI := locallyOfFiniteType_hilbert_hom hH n
    schemeDeltaDimension (fieldChowSituation k) (H n).hom ≤ ((n : ℤ) : EInt) := by
  have := locallyOfFiniteType_hilbert_hom hH n
  have hint := isIntegral_of_smooth_of_geometricallyIrreducible X.hom
  have hdim := topologicalKrullDim_eq_one_of_smoothOfRelativeDimension_one X.hom
  have hvar : IsVariety k X.hom := {}
  set e := smashFibrePowerIso k X x x hx hx n
  set π' := e.hom.left ≫ (symmetricPowerMap hH n).left with hπ'def
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank π' n.factorial :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp ((Over.forget _).mapIso e) _
      inferInstance
  have hπ' : π' ≫ (H n).hom = (smashPointDifference k X.hom x x hx hx n).Y.hom := by
    rw [hπ'def, Category.assoc, Over.w, Over.w]
  obtain ⟨hvarY, hdimY⟩ := isVariety_smashPointDifference k X.hom x x hx hx 1
    (by rw [hdim]; rfl) n
  have hdimT : schemeDeltaDimension (fieldChowSituation k)
      (smashPointDifference k X.hom x x hx hx n).Y.hom ≤ ((n : ℤ) : EInt) :=
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq _
      (n := n) (by rw [hdimY, mul_one])).le
  exact schemeDeltaDimension_le_of_isFiniteLocallyFreeOfRank (fieldChowSituation k)
    _ (H n).hom π' (Nat.factorial_pos n) hπ' hdimT

/-- **The curve case of Stacks 0FH9, given a flat surjective factorization with fibres of
dimension `r ≥ 1`.** As
`isOfFinAddOrder_smashPointDifference_of_flat_pullbackPicardClass_symmetricPowerNorm`, but with
nothing required of `P` beyond local finite type over `k`, for `f` surjective with fibres
equidimensional of dimension `r`. In the source `f` is the Abel map `Sⁿ(X) ⟶ Pic^n_{X/k}`, a
projective bundle with fibres `ℙ^{n-g}`. -/
theorem isOfFinAddOrder_smashPointDifference_of_surjective_pullbackPicardClass_symmetricPowerNorm
    [IsAlgClosed k] (x x' : Spec (.of k) ⟶ X.left) (hx : x ≫ X.hom = 𝟙 _)
    (hx' : x' ≫ X.hom = 𝟙 _) (L : X.left.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.left.sheaf.obj
      X.left.ringCatSheaf.property L]
    (hL : (invCap (fieldChowSituation k) X.hom L).capOnChow (fieldChowSituation k) X.hom 0
      (fundamentalChowClass (fieldChowSituation k) X.hom (0 + 1)) =
        pointDifference k X.hom x x' hx hx')
    (n : ℕ) (i₀ : Fin n) {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [LocallyOfFiniteType sP]
    (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) (f : (H n).left ⟶ P) [Flat f]
    (hf : f ≫ sP = (H n).hom) (hsurj : Function.Surjective f.base)
    (hrel : letI := locallyOfFiniteType_of_comp_eq_hilbert_hom hH n sP f hf
      AlgebraicGeometry.RelativeDimension f r) (M : P.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (hNM : Stacks.SheafOfModules.pullbackPicardClass f M hM =
      (H n).left.picardClass (symmetricPowerNorm hH n i₀ L)
        (isInvertible_symmetricPowerNorm hH n i₀ L)) :
    IsOfFinAddOrder (smashPointDifference k X.hom x x' hx hx' n).cycle := by
  have := locallyOfFiniteType_hilbert_hom hH n
  have := isInvertible_symmetricPowerNorm hH n i₀ L
  have := locallyOfFiniteType_of_comp_eq_hilbert_hom hH n sP f hf
  have hP := schemeDeltaDimension_le_sub_of_surjective_of_relativeDimension (fieldChowSituation k)
    (H n).hom sP f hf hsurj r hrel (schemeDeltaDimension_hilbert_hom_le hH x hx n)
  have hP' : schemeDeltaDimension (fieldChowSituation k) sP ≤ (((n - r : ℕ) : ℤ) : EInt) := by
    rwa [Nat.cast_sub hrn]
  refine isOfFinAddOrder_smashPointDifference_of_isOfFinAddOrder_symmetricPowerNorm hH x x' hx hx'
    L hL n i₀ ?_
  rw [iteratedChernCapOnChow_replicate_fundamental_eq_zero_of_flat_of_schemeDeltaDimension_le
    (fieldChowSituation k) (fun _ _ => rfl) (H n).hom sP (n - r) r n hP' (Nat.sub_add_cancel hrn)
    (by omega) f hf hrel M _ hNM]
  exact IsOfFinAddOrder.zero

end Stacks.Chow

end
