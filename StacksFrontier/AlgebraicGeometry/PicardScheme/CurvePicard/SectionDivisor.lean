module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFlatFamily
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorDegreeSum

/-!
# The zero scheme of a fibrewise nonvanishing section on a family of curves

Let `X` be a geometrically irreducible smooth proper curve over a field `k`, `T` a scheme over
`k` and `L` an invertible module on `X_T`. If a global section `s` of `L` is nonzero on every
fibre `X_t`, its zero scheme `D = Z(s)` is a relative effective Cartier divisor on `X_T / T`
which is finite locally free over `T`; and if every fibre of `L` has `H⁰` of dimension one and
vanishing `H¹`, then `D` has degree `g`, the genus of `X`. This is the claim in the proof of
[Stacks, Tag 0B9X].

## Main results

* `Stacks.PicardCurve.isRelativeEffectiveCartierDivisor_zeroScheme`.
* `Stacks.PicardCurve.isFiniteLocallyFreeOfRank_zeroScheme`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Divisors (IsEffectiveCartierDivisor IsRelativeEffectiveCartierDivisor)
open Stacks.FibreCohomology (fibreCohomology)

universe u

namespace Stacks.PicardCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {T XT : Scheme.{u}} (a : T ⟶ Spec (.of k)) (gT : XT ⟶ X) (fT : XT ⟶ T)
  (hT : IsPullback gT fT f a)

/-- The `k`-algebra structure on a residue field of a scheme over `k`. -/
abbrev residueAlgebra (t : T) : Algebra k (T.residueField t) :=
  (Spec.preimage (T.fromSpecResidueField t ≫ a)).hom.toAlgebra

include hT in
/-- The fibre of `X_T` over a point `t` is the base change of `X` to `κ(t)`. -/
theorem isPullback_fiber (t : T) :
    letI := residueAlgebra a t
    IsPullback (fT.fiberι t ≫ gT) (fT.fiberToSpecResidueField t) f
      (Spec.map (CommRingCat.ofHom (algebraMap k (T.residueField t)))) := by
  let := residueAlgebra a t
  have h : Spec.map (CommRingCat.ofHom (algebraMap k (T.residueField t))) =
      T.fromSpecResidueField t ≫ a := Spec.map_preimage _
  exact h ▸ (IsPullback.of_hasPullback fT (T.fromSpecResidueField t)).paste_horiz hT

variable [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]

omit [GeometricallyIrreducible f] [Smooth f] [IsProper f] in
include hT in
/-- A base change of a curve is surjective onto the base. -/
theorem surjective_of_isPullback : Surjective fT := by
  have : IsIntegral X := inferInstance
  have : Surjective f := ⟨fun y => by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact ⟨x, Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  exact MorphismProperty.of_isPullback hT inferInstance

omit [IsCurve k f] [IsProper f] in
include hT in
/-- Every fibre `X_t` of a base change of a curve is an integral scheme. -/
theorem isIntegral_fiber (t : T) : IsIntegral (fT.fiber t) :=
  let := residueAlgebra a t
  Stacks.AbelMap.isIntegral_of_isPullback (K := T.residueField t) f _ _
    (isPullback_fiber f a gT fT hT t)

variable (L : XT.Modules) [SheafOfModules.IsInvertible XT.sheaf.obj XT.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (hs : ∀ t : T, pullbackGlobalSections (fT.fiberι t) L s ≠ 0)

omit [IsCurve k f] [IsProper f] in
include hT hs in
/-- **The fibres of the zero scheme of a fibrewise nonvanishing section are effective Cartier
divisors**, the fibres being integral. -/
theorem isEffectiveCartierDivisor_comap_fiberι (t : T) :
    IsEffectiveCartierDivisor ((zeroScheme XT L s).comap (fT.fiberι t)) :=
  have := isIntegral_fiber f a gT fT hT t
  isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero (fT.fiberι t) L s (hs t)

omit [IsCurve k f] [GeometricallyIrreducible f] [IsProper f] in
include hT in
/-- A base change of a curve is flat. -/
theorem flat_of_isPullback : Flat fT := MorphismProperty.of_isPullback hT inferInstance

omit [IsCurve k f] [GeometricallyIrreducible f] [IsProper f] in
include hT in
/-- A base change of a curve is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_isPullback : LocallyOfFinitePresentation fT :=
  MorphismProperty.of_isPullback hT inferInstance

omit [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] in
include hT in
/-- A base change of a curve is proper. -/
theorem isProper_of_isPullback : IsProper fT := MorphismProperty.of_isPullback hT inferInstance

omit [GeometricallyIrreducible f] [IsProper f] in
include hT in
/-- A base change of a curve is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isPullback : SmoothOfRelativeDimension 1 fT :=
  have : SmoothOfRelativeDimension 1 f :=
    AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve k f
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hT inferInstance

omit [IsCurve k f] [IsProper f] in
include hT hs in
/-- **The zero scheme of a fibrewise nonvanishing section is a relative effective Cartier
divisor** ([Stacks, Tag 062Y]). -/
theorem isRelativeEffectiveCartierDivisor_zeroScheme :
    IsRelativeEffectiveCartierDivisor fT (zeroScheme XT L s) :=
  have := flat_of_isPullback f a gT fT hT
  have := locallyOfFinitePresentation_of_isPullback f a gT fT hT
  Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres fT _
    (isLocallyPrincipal_zeroScheme XT L s)
    (isEffectiveCartierDivisor_comap_fiberι f a gT fT hT L s hs)

include hT hs in
/-- **The zero scheme of a fibrewise nonvanishing section is finite locally free over the
base** ([Stacks, Tag 0B9D]). -/
theorem isFiniteLocallyFree_zeroScheme :
    Stacks.Morphisms.IsFiniteLocallyFree ((zeroScheme XT L s).subschemeι ≫ fT) :=
  have := smoothOfRelativeDimension_one_of_isPullback f a gT fT hT
  have := isProper_of_isPullback f a gT fT hT
  (isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper fT _).2
    (isRelativeEffectiveCartierDivisor_zeroScheme f a gT fT hT L s hs)

include hT hs in
/-- **The fibre of the zero scheme has the degree of the fibre of the module**: if
`χ(X_t, L_t) = d + 1 - g` then the fibre at `t` of `Z(s)` is finite locally free of degree `d`
over `κ(t)` (Riemann-Roch on the integral curve `X_t`). -/
theorem isFiniteLocallyFreeOfRank_comap_fiberι (t : T) (d : ℕ)
    (hχ : (Module.finrank (T.residueField t) (fibreCohomology fT L t 0) : ℤ) -
      Module.finrank (T.residueField t) (fibreCohomology fT L t 1) = d + 1 - genus f) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (((zeroScheme XT L s).comap (fT.fiberι t)).subschemeι ≫ fT.fiberToSpecResidueField t) d := by
  let := residueAlgebra a t
  let K : Type u := T.residueField t
  let fZ : fT.fiber t ⟶ Spec (.of K) := fT.fiberToSpecResidueField t
  have hZ : IsPullback (fT.fiberι t ≫ gT) fZ f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    isPullback_fiber f a gT fT hT t
  have := Stacks.AbelMap.isProper_of_isPullback f _ fZ hZ
  have := Stacks.AbelMap.isIntegral_of_isPullback f _ fZ hZ
  have := Stacks.AbelMap.isIso_globalSections_of_isPullback f _ fZ hZ
  have hdim : topologicalKrullDim (fT.fiber t) ≤ 1 :=
    (Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback f _ fZ hZ).le
  set Lt := (Scheme.Modules.pullback (fT.fiberι t)).obj L
  have : SheafOfModules.IsInvertible (fT.fiber t).presheaf (fT.fiber t).ringCatSheaf.2 Lt :=
    inferInstanceAs (SheafOfModules.IsInvertible (fT.fiber t).sheaf.obj
      (fT.fiber t).ringCatSheaf.property Lt)
  set D := (zeroScheme XT L s).comap (fT.fiberι t)
  have hD : IsEffectiveCartierDivisor D :=
    isEffectiveCartierDivisor_comap_fiberι f a gT fT hT L s hs t
  have hdeg : invertibleCurveDegree K fZ hdim Lt = d := by
    rw [invertibleCurveDegree_eq_sub_of_isZero K fZ hdim Lt
      (isZero_cohomologyOverField_of_two_le' K fZ hdim Lt)
      (isZero_cohomologyOverField_of_two_le' K fZ hdim _),
      finrank_cohomologyOverField_unit_zero_eq_one fZ,
      ← genus_eq_finrank_cohomologyOverField_unit_one' K fZ, genus_baseChange k K _ fZ f hZ]
    change (Module.finrank (T.residueField t) (fibreCohomology fT L t 0) : ℤ) -
      Module.finrank (T.residueField t) (fibreCohomology fT L t 1) - _ = _
    rw [hχ]
    ring
  have hst : (Stacks.Divisors.sectionsOfTop Lt (pullbackGlobalSections (fT.fiberι t) L s)).eval
      (op ⊤) ≠ 0 := by
    rw [Stacks.Divisors.sectionsOfTop_eval_top]
    exact hs t
  have hdegΓ := invertibleCurveDegree_eq_finrank_globalSections_zeroScheme K fZ hdim Lt _ hst D
    (by
      rw [Stacks.Divisors.sectionsOfTop_eval_top]
      exact Stacks.Divisors.zeroScheme_pullback (fT.fiberι t) L s)
  have hrank := isFiniteLocallyFreeOfRank_divisorSubscheme K fZ hdim D
  let : Algebra K Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ fZ).appTop).hom.toAlgebra
  rw [hdeg] at hdegΓ
  rwa [show Module.finrank K Γ(D.subscheme, ⊤) = d by exact_mod_cast hdegΓ.symm] at hrank

/-- **A finite locally free morphism whose fibres all have degree `d` has degree `d`.** -/
theorem isFiniteLocallyFreeOfRank_of_fibres {Y S : Scheme.{u}} (g : Y ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree g] (d : ℕ)
    (h : ∀ s : S, ∃ (Y' : Scheme.{u}) (g' : Y' ⟶ Spec (S.residueField s)) (q : Y' ⟶ Y),
      IsPullback q g' g (S.fromSpecResidueField s) ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank g' d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d := by
  obtain ⟨_, _, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).1
      inferInstance
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g d).2 fun s => ?_
  obtain ⟨Y', g', q, hsq, hg'⟩ := h s
  obtain ⟨_, _, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g').1
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d)
  let y : Spec (S.residueField s) := IsLocalRing.closedPoint (S.residueField s)
  have h₂ : g'.finrank y = g.finrank (S.fromSpecResidueField s y) :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq y
  rw [Scheme.fromSpecResidueField_apply] at h₂
  exact h₂.symm.trans
    ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g' d).1 hg' y)

include hT hs in
/-- **The zero scheme of a fibrewise nonvanishing section has the degree of the fibres**: if
`χ(X_t, L_t) = d + 1 - g` for every `t`, then `Z(s)` is finite locally free of degree `d` over
`T`. -/
theorem isFiniteLocallyFreeOfRank_zeroScheme (d : ℕ)
    (hχ : ∀ t : T, (Module.finrank (T.residueField t) (fibreCohomology fT L t 0) : ℤ) -
      Module.finrank (T.residueField t) (fibreCohomology fT L t 1) = d + 1 - genus f) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((zeroScheme XT L s).subschemeι ≫ fT) d := by
  have := isFiniteLocallyFree_zeroScheme f a gT fT hT L s hs
  refine isFiniteLocallyFreeOfRank_of_fibres _ d fun t => ?_
  have hsq : IsPullback (fT.fiberι t) (fT.fiberToSpecResidueField t) fT
      (T.fromSpecResidueField t) := IsPullback.of_hasPullback _ _
  obtain ⟨q, hq⟩ := exists_isPullback_subschemeι_baseChange hsq (zeroScheme XT L s)
  exact ⟨_, _, q, hq, isFiniteLocallyFreeOfRank_comap_fiberι f a gT fT hT L s hs t d (hχ t)⟩

end Stacks.PicardCurve
