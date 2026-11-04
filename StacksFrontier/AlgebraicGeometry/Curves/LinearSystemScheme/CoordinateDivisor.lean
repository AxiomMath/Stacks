module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.CurveFacts
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ZeroSchemeCoordinates
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeFieldExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# The divisor of a coordinate section on a base change of a curve

Let `X` be a smooth projective curve over an algebraically closed field `k`, `L` an invertible
`𝒪_X`-module and `w₀, …, wₙ` a basis of `Γ(X, L)`. For a `k`-scheme `T` and functions
`c₀, …, cₙ` on `T` generating the unit ideal, the coordinate section `s = Σⱼ q^*(cⱼ) · p^*(wⱼ)`
of `p^* L` on `X_T = X ×_k T` is nonzero on every fibre of `q : X_T ⟶ T`. Over an affine `T` its
zero scheme is therefore a relative effective Cartier divisor ([Stacks, Tag 062Y]), finite locally
free over `T` ([Stacks, Tag 0B9D]).

## Main definitions

* `Stacks.LinearSystemScheme.coordDivisor`: the zero scheme of the coordinate section.

## Main results

* `Stacks.LinearSystemScheme.coordSection_ne_zero_of_isPullback`: a coordinate section with
  a nonzero coordinate is nonzero, over an affine base flat over the base of a cartesian square.
* `Stacks.LinearSystemScheme.isRelativeEffectiveCartierDivisor_coordDivisor` and
  `Stacks.LinearSystemScheme.isFiniteLocallyFree_coordDivisor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange

universe u

namespace Stacks.LinearSystemScheme

/-- **A coordinate section with a nonzero coordinate is nonzero**, for a cartesian square over
affine bases with a flat bottom edge and a basis of the sections. -/
theorem coordSection_ne_zero_of_isPullback {X Y T S : Scheme.{u}} {g : T ⟶ S} {iX : X ⟶ S}
    {p : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback p q iX g) [IsAffine S] [IsAffine T] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] (L : X.Modules) [L.IsQuasicoherent] {n : ℕ}
    (w : letI := baseModule iX L ⊤; Module.Basis (Fin n) Γ(S, ⊤) Γ(L, ⊤))
    (c : Fin n → Γ(T, ⊤)) (hc : c ≠ 0) : coordSection p q L w c ≠ 0 := by
  intro h0
  have h00 : coordSection p q L w 0 = 0 := by simp [coordSection]
  exact hc ((coordSection_bijective H L w).1 (h0.trans h00.symm))

/-- Functions generating the unit ideal do not all vanish at a point. -/
theorem residue_coords_ne_zero {T : Scheme.{u}} {n : ℕ} (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (t : T) :
    (fun j => (T.fromSpecResidueField t).appTop (c j)) ≠ 0 := by
  set ρ := T.fromSpecResidueField t
  intro h0
  have hcov := iSup_basicOpen_of_span_eq_top (X := T) ⊤ (Set.range c) hc
  have ht : t ∈ (⊤ : T.Opens) := trivial
  rw [← hcov] at ht
  simp only [TopologicalSpace.Opens.mem_iSup, Set.mem_range, exists_prop] at ht
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := ht
  have hpre : ρ ⁻¹ᵁ T.basicOpen (c j) =
      (Spec (.of (T.residueField t))).basicOpen (ρ.appTop (c j)) :=
    Scheme.preimage_basicOpen_top ρ (c j)
  have hz : ρ.appTop (c j) = 0 := congrFun h0 j
  rw [hz, Scheme.basicOpen_zero] at hpre
  have : (IsLocalRing.closedPoint (T.residueField t)) ∈ ρ ⁻¹ᵁ T.basicOpen (c j) := by
    show ρ _ ∈ T.basicOpen (c j)
    rw [show ρ (IsLocalRing.closedPoint (T.residueField t)) = t from
      Scheme.fromSpecResidueField_apply t _]
    exact hj
  rwa [hpre] at this

/-- The fibre of a base change `X ×_S T ⟶ T` over `t` is the base change of `X` along
`Spec κ(t) ⟶ S`. -/
theorem isPullback_fiberι_comp_fst {X T S : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (t : T) :
    IsPullback ((pullback.snd f g).fiberι t ≫ pullback.fst f g)
      ((pullback.snd f g).fiberToSpecResidueField t) f (T.fromSpecResidueField t ≫ g) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback f g)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (L : X.Modules) [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] {n : ℕ}
  (w : letI := baseModule f L ⊤; Module.Basis (Fin n) Γ(Spec (.of k), ⊤) Γ(L, ⊤))
  {T : Scheme.{u}} (g : T ⟶ Spec (.of k))

/-- **The divisor of a coordinate section**: the zero scheme of `Σⱼ q^*(cⱼ) · p^*(wⱼ)` on
`X ×_k T`. -/
def coordDivisor (c : Fin n → Γ(T, ⊤)) : (pullback f g).IdealSheafData :=
  zeroScheme (pullback f g) ((Scheme.Modules.pullback (pullback.fst f g)).obj L)
    (coordSection (pullback.fst f g) (pullback.snd f g) L w c)

/-- The inverse image of `coordDivisor` in the fibre over `t` is the zero scheme of the
coordinate section with coordinates the residues of `c` at `t`. -/
theorem comap_fiberι_coordDivisor (c : Fin n → Γ(T, ⊤)) (t : T) :
    (coordDivisor k f L w g c).comap ((pullback.snd f g).fiberι t) =
      zeroScheme _ ((Scheme.Modules.pullback
        ((pullback.snd f g).fiberι t ≫ pullback.fst f g)).obj L)
      (coordSection ((pullback.snd f g).fiberι t ≫ pullback.fst f g)
        ((pullback.snd f g).fiberToSpecResidueField t) L w
        (fun j => (T.fromSpecResidueField t).appTop (c j))) := by
  rw [coordDivisor, comap_zeroScheme_coordSection, (pullback.snd f g).fiber_fac t,
    coordSection_comp]

/-- A smooth projective curve over `k` with an invertible module is quasi-coherent, compact,
quasi-separated and geometrically integral. -/
private theorem curve_instances [IsAlgClosed k] [IsProjectiveVariety k f] :
    L.IsQuasicoherent ∧ CompactSpace X ∧ QuasiSeparatedSpace X ∧ GeometricallyIntegral f :=
  ⟨isQuasicoherent_of_isInvertible L, (quasiCompact_iff_compactSpace f).mp inferInstance,
    (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance, geometricallyIntegral k f⟩

variable [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]

include k f in
omit [IsAlgClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] in
/-- An invertible module on a smooth projective curve over `k` is quasi-coherent. -/
theorem isQuasicoherent_of_curve : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L

include k f in
omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
/-- The underlying space of a smooth projective curve over `k` is compact. -/
theorem compactSpace_of_curve : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance

include k f in
omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
/-- The underlying space of a smooth projective curve over `k` is quasi-separated. -/
theorem quasiSeparatedSpace_of_curve : QuasiSeparatedSpace X :=
  (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance

omit [IsCurve k f] [Smooth f] in
/-- **The divisor of a unimodular coordinate section is cut out on every fibre by a nonzero
section**: its inverse image in every fibre of `X ×_k T ⟶ T` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_comap_fiberι_coordDivisor (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (t : T) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((coordDivisor k f L w g c).comap ((pullback.snd f g).fiberι t)) := by
  obtain ⟨_, _, _, _⟩ := curve_instances k f L
  rw [comap_fiberι_coordDivisor]
  exact isEffectiveCartierDivisor_zeroScheme_of_ne_zero _ _
    (coordSection_ne_zero_of_isPullback (isPullback_fiberι_comp_fst f g t) L w _
      (residue_coords_ne_zero c hc t))

omit [IsCurve k f] in
/-- **The divisor of a unimodular coordinate section is a relative effective Cartier divisor**
over `T` ([Stacks, Tag 062Y]). -/
theorem isRelativeEffectiveCartierDivisor_coordDivisor (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.snd f g)
      (coordDivisor k f L w g c) :=
  Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres _ _
    (isLocallyPrincipal_zeroScheme _ _ _)
    (isEffectiveCartierDivisor_comap_fiberι_coordDivisor k f L w g c hc)

omit [IsCurve k f] in
/-- The divisor of a unimodular coordinate section is an effective Cartier divisor on `X ×_k T`. -/
theorem isEffectiveCartierDivisor_coordDivisor (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    Stacks.Divisors.IsEffectiveCartierDivisor (coordDivisor k f L w g c) :=
  (isRelativeEffectiveCartierDivisor_coordDivisor k f L w g c hc).1

/-- **The divisor of a unimodular coordinate section is finite locally free over `T`**
([Stacks, Tag 0B9D]). -/
theorem isFiniteLocallyFree_coordDivisor (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    Stacks.Morphisms.IsFiniteLocallyFree
      ((coordDivisor k f L w g c).subschemeι ≫ pullback.snd f g) := by
  have : SmoothOfRelativeDimension 1 f := Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f
  have : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback f g) ‹_›
  exact (isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper _ _).mpr
    (isRelativeEffectiveCartierDivisor_coordDivisor k f L w g c hc)

/-- **Over a field the zero scheme of a nonzero section of an invertible module has rank the
degree of the module.** -/
theorem isFiniteLocallyFreeOfRank_zeroScheme_of_field {K : Type u} [Field K] {F : Scheme.{u}}
    (Q : F ⟶ Spec (.of K)) [IsProper Q] [IsIntegral F] (hdimF : topologicalKrullDim F ≤ 1)
    (M : F.Modules) [hM : SheafOfModules.IsInvertible F.sheaf.obj F.ringCatSheaf.property M]
    (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) {d : ℕ}
    (hd : @invertibleCurveDegree K _ F Q _ hdimF M hM = d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((zeroScheme F M σ).subschemeι ≫ Q) d := by
  have hZ : Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme F M σ) :=
    isEffectiveCartierDivisor_zeroScheme_of_ne_zero M σ hσ
  have hfin : IsFinite ((zeroScheme F M σ).subschemeι ≫ Q) :=
    isFinite_divisorSubscheme K Q hdimF (zeroScheme F M σ)
  have hreg := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection F M
    (Stacks.Divisors.sectionsOfTop M σ)).mp (by
      rw [Stacks.Divisors.sectionsOfTop_eval_top]
      exact hZ)
  have hdeg := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme K Q hdimF M
    (Stacks.Divisors.sectionsOfTop M σ) hreg
  rw [Stacks.Divisors.sectionsOfTop_eval_top] at hdeg
  let : Algebra K Γ((zeroScheme F M σ).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ ((zeroScheme F M σ).subschemeι ≫ Q).appTop).hom.toAlgebra
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_of_specTarget _ d rfl]
  have hfr := finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K
    ((zeroScheme F M σ).subschemeι ≫ Q)
  refine ⟨?_, ?_⟩
  · have h1 := ((zeroScheme F M σ).subschemeι ≫ Q).finite_appTop
    have h2 : ((Scheme.ΓSpecIso (.of K)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2
    exact (RingHom.Finite.comp h1 h2 : RingHom.Finite _)
  · have : (Module.finrank K Γ((zeroScheme F M σ).subscheme, ⊤) : ℤ) = d := by
      rw [← hfr, ← hdeg, hd]
    exact_mod_cast this

omit [IsCurve k f] [Smooth f] in
/-- **Over a field point of `Spec k` the divisor of a nonzero coordinate section has rank the
degree of `L`**, for any cartesian square `F = X ×_k K`. -/
theorem isFiniteLocallyFreeOfRank_zeroScheme_coordSection_field {K : Type u} [Field K]
    {F : Scheme.{u}} {P : F ⟶ X} {Q : F ⟶ Spec (.of K)} {m : Spec (.of K) ⟶ Spec (.of k)}
    (H : IsPullback P Q f m) (c : Fin n → Γ(Spec (.of K), ⊤)) (hc : c ≠ 0)
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (hd : @invertibleCurveDegree k _ X f _ hdim L
      (by exact ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›) = d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((zeroScheme F ((Scheme.Modules.pullback P).obj L) (coordSection P Q L w c)).subschemeι ≫ Q)
      d := by
  let : Algebra k K := (Spec.fullyFaithful.preimage m).unop.hom.toAlgebra
  have hm : Spec.map (CommRingCat.ofHom (algebraMap k K)) = m := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    exact Spec.fullyFaithful.map_preimage m
  rw [← hm] at H
  obtain ⟨_, _, _, hgi⟩ := curve_instances k f L
  have : IsProper Q := MorphismProperty.of_isPullback H inferInstance
  have : IsIntegral F := hgi.geometrically_isIntegral _ _ _ H
  have hdimF : topologicalKrullDim F ≤ 1 :=
    (topologicalKrullDim_baseChange k K P Q f H).trans_le hdim
  refine isFiniteLocallyFreeOfRank_zeroScheme_of_field Q hdimF _ _
    (coordSection_ne_zero_of_isPullback H L w c hc) ?_
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›
  have : SheafOfModules.IsInvertible F.presheaf F.ringCatSheaf.2
      ((Scheme.Modules.pullback P).obj L) :=
    Stacks.Divisors.pullback_isInvertible P L
  exact ((invertibleCurveDegree_eq_curveDegree_one K Q hdimF _).trans
    ((curveDegree_baseChange_field k K P Q f H hdim L 1).trans
      (invertibleCurveDegree_eq_curveDegree_one k f hdim L).symm)).trans hd

/-- **The divisor of a unimodular coordinate section has degree `deg L` over `T`.** -/
theorem isFiniteLocallyFreeOfRank_coordDivisor (c : Fin n → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (hd : @invertibleCurveDegree k _ X f _ hdim L
      (by exact ‹SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L›) = d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((coordDivisor k f L w g c).subschemeι ≫ pullback.snd f g) d := by
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1
      (isFiniteLocallyFree_coordDivisor k f L w g c hc)
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq]
  intro t
  have hbig := IsPullback.paste_vert
    (Stacks.Bertini.isPullback_subschemeι_comap (coordDivisor k f L w g c)
      ((pullback.snd f g).fiberι t)).flip
    (IsPullback.of_hasPullback (pullback.snd f g) (T.fromSpecResidueField t))
  have hrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (((coordDivisor k f L w g c).comap ((pullback.snd f g).fiberι t)).subschemeι ≫
        (pullback.snd f g).fiberToSpecResidueField t) d := by
    rw [comap_fiberι_coordDivisor]
    exact isFiniteLocallyFreeOfRank_zeroScheme_coordSection_field k f L w
      (isPullback_fiberι_comp_fst f g t) _
      (residue_coords_ne_zero c hc t) hdim hd
  obtain ⟨hfin', hflat', -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).1
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d (h := hrank))
  have h1 := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ d).1 hrank
    (IsLocalRing.closedPoint (T.residueField t))
  have h2 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hbig
    (IsLocalRing.closedPoint (T.residueField t))
  exact (congrArg _ (Scheme.fromSpecResidueField_apply t _)).symm.trans (h2.symm.trans h1)

end Stacks.LinearSystemScheme

end
