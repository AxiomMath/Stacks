module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDPushforwardGluing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDCechOneVanishing
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusSheafMap
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge

/-!
# Multiplication by `c` kills the first cohomology, through the Frobenius

This is the cohomological core of the Frobenius route to [Stacks, Tag 0B4U]. Let `π : Y ⟶ X` be a
finite surjective morphism of normal integral schemes, with `Y` a normal modification of the
spectrum of a two-dimensional Noetherian normal local domain `A` (a `VanishingSituation`), such
that `p`-th powers of rational functions of `Y` are rational functions of `X` and
`H¹(X, 𝒪_X) = 0`. Suppose that over the part `W` of `X` lying under the punctured spectrum of `A`
multiplication by a global function `c` factors through the Frobenius: there is an additive map
`θ` of the function field of `X`, realized on the sections of `𝒪_X` over opens of `W`, with
`c y = ∑ᵢ βᵢ θ(bᵢ yᵖ)`. Then multiplication by `c` sends every cocycle of an injective resolution
of `π_* 𝒪_Y` to a coboundary, that is, `c` kills `H¹(X, π_* 𝒪_Y) = H¹(Y, 𝒪_Y)`.

## Main results

* `AlgebraicGeometry.PuncturedRestriction.exists_d_eq_restrict_of_isAffineOpen`: a cocycle of an
  injective resolution of a quasi-coherent module has primitives on affine opens.
* `AlgebraicGeometry.PuncturedRestriction.exists_d_eq_smulE_of_frobenius`: the statement above.

## Implementation notes

Take primitives `eₐ` of the cocycle on an affine open cover; their differences `sₐ_b` are
sections of `π_* 𝒪_Y`, and their `p`-th powers form a Čech cocycle of `𝒪_X`, which is a coboundary
`uₐ - u_b` because `H¹(X, 𝒪_X) = 0` (`exists_eq_sub_of_cocycle`). Over `W` the sections
`τₐ = ∑ᵢ βᵢ θ(bᵢ uₐ)` satisfy `τₐ - τ_b = c sₐ_b`, so the corrected primitives `c eₐ - τₐ` of `c z`
glue over `W` (`exists_d_eq_of_cech`); together with the primitives `c eₐ` on the cover, the polar
lemma glues them to a global primitive (`exists_d_eq_of_local_primitives_pushforward`). No duality
theory is used.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.PuncturedRestriction

section Primitives

variable {X : Scheme.{u}}

local notation "𝒪" => structureSheafRing X.toLocallyRingedSpace.toRingedSpace

/-- A cocycle of an injective resolution of a quasi-coherent module has a primitive on every
affine open. -/
theorem exists_d_eq_restrict_of_isAffineOpen {F : SheafOfModules.{u} 𝒪}
    (hF : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F)
    (I : InjectiveResolution F) (z : (secF 𝒪 ⊤).obj (I.cocomplex.X 1))
    (hz : (secF 𝒪 ⊤).map (I.cocomplex.d 1 2) z = 0) {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ e : (secF 𝒪 U).obj (I.cocomplex.X 0),
      (secF 𝒪 U).map (I.cocomplex.d 0 1) e = (secRestrict 𝒪 (le_top : U ≤ ⊤)).app _ z := by
  have : F.IsQuasicoherent := hF
  set K := secCx 𝒪 I ⊤
  let z' : K.cycles 1 := (K.sc 1).abCyclesIso.inv ⟨z, by
    change (K.d 1 ((ComplexShape.up ℕ).next 1)) z = 0
    rw [CochainComplex.next ℕ 1]
    exact hz⟩
  have hz' : K.iCycles 1 z' = z :=
    (K.sc 1).abCyclesIso_inv_apply_iCycles _
  have : Subsingleton (((secF 𝒪 U).rightDerived 1).obj F) :=
    AddCommGrpCat.subsingleton_of_isZero
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F U hU 1 one_pos)
  obtain ⟨e, he⟩ := exists_d_eq_restrict 𝒪 I (le_top : U ≤ ⊤) z' (by
    set v := HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (secRestrict 𝒪 (le_top : U ≤ ⊤)) _).app
        I.cocomplex) 1 (K.homologyπ 1 z')
    have h0 : (I.isoRightDerivedObj (secF 𝒪 U) 1).inv v = 0 := Subsingleton.elim _ _
    exact (ConcreteCategory.congr_hom (I.isoRightDerivedObj (secF 𝒪 U) 1).inv_hom_id v).symm.trans
      ((congrArg (I.isoRightDerivedObj (secF 𝒪 U) 1).hom h0).trans (map_zero _)))
  exact ⟨e, he.trans (by rw [hz'])⟩

/-- The differences of primitives of a cocycle on a family of opens come from sections of the
resolved module, and these form a Čech cocycle. -/
theorem exists_ι₀_eq_sub_of_primitives {M : SheafOfModules.{u} 𝒪} (I : InjectiveResolution M)
    (z : (secF 𝒪 ⊤).obj (I.cocomplex.X 1)) {J : Type u} (U : J → X.Opens)
    (e : ∀ a, (secF 𝒪 (U a)).obj (I.cocomplex.X 0))
    (he : ∀ a, (secF 𝒪 (U a)).map (I.cocomplex.d 0 1) (e a) =
      (secRestrict 𝒪 (le_top : U a ≤ ⊤)).app _ z) :
    ∃ s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj M,
      (∀ a b, (secF 𝒪 _).map (ι₀ I) (s a b) = (secRestrict 𝒪 inf_le_left).app _ (e a) -
        (secRestrict 𝒪 inf_le_right).app _ (e b)) ∧
      ∀ a b c,
        (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
            U a ⊓ U b ⊓ U c ≤ U a ⊓ U b)).app _ (s a b) +
          (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            U a ⊓ U b ⊓ U c ≤ U b ⊓ U c)).app _ (s b c) =
        (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            U a ⊓ U b ⊓ U c ≤ U a ⊓ U c)).app _ (s a c) := by
  have hexact := fun O : X.Opens => exact_mono_secF_ι₀ I O
  have hs : ∀ a b, ∃ t : (secF 𝒪 (U a ⊓ U b)).obj M,
      (secF 𝒪 _).map (ι₀ I) t = (secRestrict 𝒪 inf_le_left).app _ (e a) -
        (secRestrict 𝒪 inf_le_right).app _ (e b) := by
    intro a b
    refine (ShortComplex.ab_exact_iff _).mp (hexact (U a ⊓ U b)).1 _ ?_
    change (secF 𝒪 _).map (I.cocomplex.d 0 1) (_ - _) = 0
    rw [map_sub, ← secRestrict_app_map, ← secRestrict_app_map, he, he, secRestrict_app_comp,
      secRestrict_app_comp, sub_self]
  choose s hs using hs
  refine ⟨s, hs, fun a b c => (AddCommGrpCat.mono_iff_injective _).mp (hexact _).2 ?_⟩
  rw [map_add, ← secRestrict_app_map, ← secRestrict_app_map, ← secRestrict_app_map, hs, hs,
    hs]
  simp only [map_sub, secRestrict_app_comp]
  abel

end Primitives

section Frobenius

variable (V : VanishingSituation.{u}) {X : Scheme.{u}} (π : V.X ⟶ X) [IsIntegral X]
  [IsIntegral V.X] [IsFinite π] [Surjective π] [IsNormal X] [IsNormal V.X]

local notation "𝒪" => structureSheafRing X.toLocallyRingedSpace.toRingedSpace

/-- The sections of `𝒪_X` form commutative rings, in the spelling of `structureSheafRing`. -/
instance commRingStructureSheafRingObj (U : X.Opensᵒᵖ) : CommRing ((𝒪).obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

variable (X) in
/-- Multiplication by a global function, as an endomorphism of the identity of `𝒪_X`-modules. -/
abbrev smulE (c : Γ(X, ⊤)) : End (𝟭 (SheafOfModules.{u} 𝒪)) :=
  Stacks.SheafOfModules.terminalSectionToEnd 𝒪 ⊤ isTerminalTop c

omit [IsIntegral X] [IsIntegral V.X] [IsFinite π] [Surjective π] [IsNormal X] [IsNormal V.X] in
/-- Multiplication by a global function of `X` on sections of `π_* 𝒪_Y`. -/
theorem toΓY_smulEnd (c : Γ(X, ⊤)) {U : X.Opens} (s : (secF 𝒪 U).obj (pushUnit V π)) :
    toΓY V π ((secF 𝒪 U).map ((smulE X c).app _) s) =
      π.app U (X.presheaf.map (homOfLE le_top).op c) * toΓY V π s := by
  have h : (isTerminalTop.from U) = homOfLE le_top := Subsingleton.elim _ _
  rw [← h]
  rfl

omit [IsIntegral X] [IsNormal X] in
/-- Maps of `𝒪`-modules commute with multiplication by a global function on sections. -/
theorem secF_map_smulEnd_comm (c : Γ(X, ⊤)) {A B : SheafOfModules.{u} 𝒪} (f : A ⟶ B)
    {U : X.Opens} (s : (secF 𝒪 U).obj A) :
    (secF 𝒪 U).map f ((secF 𝒪 U).map ((smulE X c).app A) s) =
      (secF 𝒪 U).map ((smulE X c).app B) ((secF 𝒪 U).map f s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  have h := (smulE X c).naturality f
  simp only [Functor.id_map] at h
  rw [h]

omit [IsIntegral X] [IsNormal X] in
/-- The augmentation commutes with multiplication by a global function. -/
theorem secF_map_ι₀_smulEnd (c : Γ(X, ⊤)) {M : SheafOfModules.{u} 𝒪}
    (I : InjectiveResolution M) {U : X.Opens} (s : (secF 𝒪 U).obj M) :
    (secF 𝒪 U).map (ι₀ I) ((secF 𝒪 U).map ((smulE X c).app M) s) =
      (secF 𝒪 U).map ((smulE X c).app _) ((secF 𝒪 U).map (ι₀ I) s) :=
  secF_map_smulEnd_comm c (ι₀ I) s

omit [IsIntegral X] [IsNormal X] in
/-- The differentials commute with multiplication by a global function. -/
theorem secF_map_d_smulEnd (c : Γ(X, ⊤)) {M : SheafOfModules.{u} 𝒪}
    (I : InjectiveResolution M) {U : X.Opens} (i j : ℕ) (s : (secF 𝒪 U).obj (I.cocomplex.X i)) :
    (secF 𝒪 U).map (I.cocomplex.d i j) ((secF 𝒪 U).map ((smulE X c).app _) s) =
      (secF 𝒪 U).map ((smulE X c).app _) ((secF 𝒪 U).map (I.cocomplex.d i j) s) :=
  secF_map_smulEnd_comm c (I.cocomplex.d i j) s

omit [IsIntegral X] [IsNormal X] in
/-- Restriction commutes with multiplication by a global function. -/
theorem secRestrict_smulEnd (c : Γ(X, ⊤)) {M : SheafOfModules.{u} 𝒪} {U U' : X.Opens}
    (h : U' ≤ U) (s : (secF 𝒪 U).obj M) :
    (secRestrict 𝒪 h).app M ((secF 𝒪 U).map ((smulE X c).app M) s) =
      (secF 𝒪 U').map ((smulE X c).app M) ((secRestrict 𝒪 h).app M s) :=
  secRestrict_app_map 𝒪 h _ s

end Frobenius

section Core

open SeparableGoUp

variable (V : VanishingSituation.{u}) {X : Scheme.{u}} (π : V.X ⟶ X) [IsIntegral X]
  [IsIntegral V.X] [IsFinite π] [Surjective π] [IsNormal X] [IsNormal V.X]

local notation "𝒪" => structureSheafRing X.toLocallyRingedSpace.toRingedSpace

omit [IsFinite π] [IsNormal X] [IsNormal V.X] in
/-- The generic point of `X` lies in the part `W` of `X` under the punctured spectrum. -/
theorem genericPoint_mem_of_preimage_eq {W : X.Opens}
    (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum) : genericPoint X ∈ W := by
  rw [← map_genericPoint π]
  change genericPoint V.X ∈ π ⁻¹ᵁ W
  rw [hW]
  exact apply_genericPoint_ne_closedPoint V.dimension_two V.f V.modification

/-- The correction `∑ᵢ βᵢ Θ(bᵢ u)` over `U ⊓ W` of a section `u` of `𝒪_X` over `U`. -/
def frobeniusCorrection (W : X.Opens) {n : ℕ} (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(V.X, ⊤))
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U)) {U : X.Opens}
    (u : (secF 𝒪 U).obj (SheafOfModules.unit 𝒪)) : (secF 𝒪 (U ⊓ W)).obj (pushUnit V π) :=
  ((∑ i, resTop V.X (π ⁻¹ᵁ (U ⊓ W)) (β i) *
    π.app (U ⊓ W) (Θ (U ⊓ W) (resTop X (U ⊓ W) (b i) *
      X.presheaf.map (homOfLE inf_le_left).op u))) : Γ(V.X, π ⁻¹ᵁ (U ⊓ W)))

omit [IsFinite π] [IsNormal X] [IsNormal V.X] in
/-- The generic germ of a correction `∑ᵢ βᵢ Θ(bᵢ u)` is `∑ᵢ βᵢ θ(bᵢ u)`. -/
theorem germ_frobeniusCorrection (W : X.Opens) {n : ℕ} (b : Fin n → Γ(X, ⊤))
    (β : Fin n → Γ(V.X, ⊤)) (θ : X.functionField →+ X.functionField)
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U))
    (hΘ : ∀ (U : X.Opens), U ≤ W → ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
      X.presheaf.germ U (genericPoint X) hU (Θ U a) =
        θ (X.presheaf.germ U (genericPoint X) hU a))
    {U : X.Opens} (u : (secF 𝒪 U).obj (SheafOfModules.unit 𝒪)) {O : X.Opens} (hO : O ≤ U ⊓ W)
    (hηO : genericPoint X ∈ O) :
    V.X.presheaf.germ (π ⁻¹ᵁ O) (genericPoint V.X) (genericPoint_mem_preimage π O hηO)
        (toΓY V π ((secRestrict 𝒪 hO).app _ (frobeniusCorrection V π W b β Θ u))) =
      ∑ i, V.X.presheaf.germ ⊤ (genericPoint V.X) trivial (β i) *
        dominantFunctionFieldMap π (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) *
          X.presheaf.germ U (genericPoint X) (hO hηO).1 u)) := by
  have hηa : genericPoint X ∈ U ⊓ W := hO hηO
  rw [toΓY_res, TopCat.Presheaf.germ_res_apply]
  change V.X.presheaf.germ _ _ _ (∑ i : Fin n, _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, germ_resTop, germ_app π (U ⊓ W) hηa, hΘ _ inf_le_right _ hηa, map_mul,
    germ_resTop, TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) _ hηa u]

omit [IsNormal V.X] in
/-- If the Frobenius of `t` is the difference `u - u'`, the corrections of `u` and `u'` differ
by `c t`. -/
theorem sub_frobeniusCorrection (p : ℕ) [Fact p.Prime] [CharP X.functionField p]
    (hpow : ∀ y : V.X.functionField, ∃ k : X.functionField,
      dominantFunctionFieldMap π k = y ^ p)
    {W : X.Opens} (hηW : genericPoint X ∈ W)
    (c : Γ(X, ⊤)) {n : ℕ} (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(V.X, ⊤))
    (θ : X.functionField →+ X.functionField)
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U))
    (hΘ : ∀ (U : X.Opens), U ≤ W → ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
      X.presheaf.germ U (genericPoint X) hU (Θ U a) =
        θ (X.presheaf.germ U (genericPoint X) hU a))
    (hid : ∀ (k : X.functionField) (y : V.X.functionField), dominantFunctionFieldMap π k = y ^ p →
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial c) * y =
        ∑ i, V.X.presheaf.germ ⊤ (genericPoint V.X) trivial (β i) *
          dominantFunctionFieldMap π (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) * k)))
    {U U' : X.Opens} (hη : genericPoint X ∈ U ⊓ U')
    (u : (secF 𝒪 U).obj (SheafOfModules.unit 𝒪)) (u' : (secF 𝒪 U').obj (SheafOfModules.unit 𝒪))
    (t : (secF 𝒪 (U ⊓ U')).obj (pushUnit V π))
    (hu : (frobeniusApp π p hpow (U ⊓ U') (toΓY V π t) :
        (secF 𝒪 (U ⊓ U')).obj (SheafOfModules.unit 𝒪)) =
      (secRestrict 𝒪 inf_le_left).app _ u - (secRestrict 𝒪 inf_le_right).app _ u') :
    (secRestrict 𝒪 (inf_le_left : (U ⊓ W) ⊓ (U' ⊓ W) ≤ U ⊓ W)).app _
        (frobeniusCorrection V π W b β Θ u) -
      (secRestrict 𝒪 (inf_le_right : (U ⊓ W) ⊓ (U' ⊓ W) ≤ U' ⊓ W)).app _
        (frobeniusCorrection V π W b β Θ u') =
      (secF 𝒪 _).map ((smulE X c).app (pushUnit V π)) ((secRestrict 𝒪
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (U ⊓ W) ⊓ (U' ⊓ W) ≤ U ⊓ U')).app _ t) := by
  set O := (U ⊓ W) ⊓ (U' ⊓ W)
  have hηO : genericPoint X ∈ O := ⟨⟨hη.1, hηW⟩, ⟨hη.2, hηW⟩⟩
  have hR := toΓY_smulEnd V π c ((secRestrict 𝒪
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        O ≤ U ⊓ U')).app _ t)
  change toΓY V π _ = toΓY V π _
  refine Eq.trans ?_ hR.symm
  refine sections_ext (X := V.X) _ _ fun _ => ?_
  rw [toΓY_sub, map_sub, germ_frobeniusCorrection V π W b β θ Θ hΘ u inf_le_left hηO,
    germ_frobeniusCorrection V π W b β θ Θ hΘ u' inf_le_right hηO, map_mul, germ_app π O hηO,
    germ_resTop, toΓY_res, TopCat.Presheaf.germ_res_apply]
  set k := X.presheaf.germ (U ⊓ U') (genericPoint X) hη (frobeniusApp π p hpow _
    (toΓY V π t)) with hk
  have hkp : dominantFunctionFieldMap π k = germY π (U ⊓ U') hη (toΓY V π t) ^ p :=
    germ_frobeniusApp π p hpow _ hη _
  have hku : k = X.presheaf.germ U (genericPoint X) hη.1 u -
      X.presheaf.germ U' (genericPoint X) hη.2 u' := by
    rw [hk, hu]
    have e : ∀ {A : X.Opens} (h : U ⊓ U' ≤ A) (v : (secF 𝒪 A).obj (SheafOfModules.unit 𝒪)),
        X.presheaf.germ (U ⊓ U') (genericPoint X) hη
          ((secRestrict 𝒪 h).app _ v : Γ(X, U ⊓ U')) = X.presheaf.germ A _ (h hη) v :=
      fun h v => TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) _ hη v
    rw [← e inf_le_left u, ← e inf_le_right u']
    exact map_sub (X.presheaf.germ (U ⊓ U') (genericPoint X) hη).hom _ _
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub, ← map_sub, ← mul_sub (X.presheaf.germ ⊤ (genericPoint X) trivial _)]
  rw [← hku]
  exact (hid k _ hkp).symm

omit [IsIntegral X] [IsFinite π] [IsNormal X] in
/-- Primitives of `c z` on a cover glue to a global primitive, once corrections over the part `W`
under the punctured spectrum differ by `c` times the differences of the primitives of `z`. -/
theorem exists_d_eq_smulE_of_corrections (W : X.Opens)
    (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum) (c : Γ(X, ⊤))
    (I : InjectiveResolution (pushUnit V π)) (z : (secF 𝒪 ⊤).obj (I.cocomplex.X 1))
    {J : Type u} (U : J → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j)
    (e : ∀ a, (secF 𝒪 (U a)).obj (I.cocomplex.X 0))
    (he : ∀ a, (secF 𝒪 (U a)).map (I.cocomplex.d 0 1) (e a) =
      (secRestrict 𝒪 (le_top : U a ≤ ⊤)).app _ z)
    (s : ∀ a b, (secF 𝒪 (U a ⊓ U b)).obj (pushUnit V π))
    (hs : ∀ a b, (secF 𝒪 _).map (ι₀ I) (s a b) = (secRestrict 𝒪 inf_le_left).app _ (e a) -
      (secRestrict 𝒪 inf_le_right).app _ (e b))
    (τ : ∀ a, (secF 𝒪 (U a ⊓ W)).obj (pushUnit V π))
    (hτ : ∀ a a', (secRestrict 𝒪 (inf_le_left : (U a ⊓ W) ⊓ (U a' ⊓ W) ≤ U a ⊓ W)).app _
        (τ a) - (secRestrict 𝒪 (inf_le_right : (U a ⊓ W) ⊓ (U a' ⊓ W) ≤ U a' ⊓ W)).app _ (τ a') =
      (secF 𝒪 _).map ((smulE X c).app (pushUnit V π)) ((secRestrict 𝒪
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          (U a ⊓ W) ⊓ (U a' ⊓ W) ≤ U a ⊓ U a')).app _ (s a a'))) :
    ∃ ε : (secF 𝒪 ⊤).obj (I.cocomplex.X 0),
      (secF 𝒪 ⊤).map (I.cocomplex.d 0 1) ε = (secF 𝒪 ⊤).map ((smulE X c).app _) z := by
  let ce : ∀ a, (secF 𝒪 (U a)).obj (I.cocomplex.X 0) := fun a =>
    (secF 𝒪 (U a)).map ((smulE X c).app _) (e a)
  have hce : ∀ a, (secF 𝒪 (U a)).map (I.cocomplex.d 0 1) (ce a) =
      (secRestrict 𝒪 (le_top : U a ≤ ⊤)).app _ ((secF 𝒪 ⊤).map ((smulE X c).app _) z) :=
    fun a => (secF_map_d_smulEnd c I 0 1 (e a)).trans
      ((congrArg ((secF 𝒪 (U a)).map ((smulE X c).app _)) (he a)).trans
        (secRestrict_smulEnd c le_top z).symm)
  obtain ⟨εW, hεW⟩ := exists_d_eq_of_cech I (O := W) (fun a => U a ⊓ W) (fun a => inf_le_right)
    (fun x hx => (hU x).elim fun j hj => Opens.mem_iSup.mpr ⟨j, ⟨hj, hx⟩⟩)
    ((secRestrict 𝒪 (le_top : W ≤ ⊤)).app _ ((secF 𝒪 ⊤).map ((smulE X c).app _) z))
    (fun a => (secRestrict 𝒪 (inf_le_left : U a ⊓ W ≤ U a)).app _ (ce a))
    (fun a => (secRestrict_app_map 𝒪 inf_le_left (I.cocomplex.d 0 1) (ce a)).symm.trans
      ((congrArg ((secRestrict 𝒪 inf_le_left).app _) (hce a)).trans
        ((secRestrict_app_comp 𝒪 _ _ _ _).trans (secRestrict_app_comp 𝒪 _ _ _ _).symm)))
    τ (fun a a' => by
      refine (congrArg _ (hτ a a')).trans ?_
      refine (secF_map_ι₀_smulEnd c I _).trans ?_
      refine (congrArg ((secF 𝒪 _).map ((smulE X c).app _))
        (secRestrict_app_map 𝒪 _ (ι₀ I) (s a a')).symm).trans ?_
      rw [hs, map_sub, secRestrict_app_comp, secRestrict_app_comp, map_sub]
      simp only [ce, Functor.id_obj]
      rw [secRestrict_smulEnd, secRestrict_smulEnd, secRestrict_smulEnd, secRestrict_smulEnd,
        secRestrict_app_comp, secRestrict_app_comp])
  exact exists_d_eq_of_local_primitives_pushforward V π I W hW
    (fun o : Option J => o.elim W U) (fun x => (hU x).elim fun j hj => ⟨some j, hj⟩) none rfl
    ((secF 𝒪 ⊤).map ((smulE X c).app _) z)
    (fun | none => εW | some a => ce a) (fun | none => hεW | some a => hce a)

/-- **The core of the Frobenius argument for [Stacks, Tag 0B4U].** Let `π : Y ⟶ X` be finite and
surjective with `X` normal and `H¹(X, 𝒪_X) = 0`, let `Kᵖ`-powers control `L`, and suppose that on
the part `W` of `X` over the punctured spectrum multiplication by `c` factors through the
Frobenius: there is an additive `θ` on the function field of `X`, preserving the sections of
`𝒪_X` over the opens of `W`, with `c y = ∑ᵢ βᵢ θ(bᵢ yᵖ)` for `y` in the function field of `Y`.
Then `c` kills every cocycle of an injective resolution of `π_* 𝒪_Y` up to a coboundary. -/
theorem exists_d_eq_smulE_of_frobenius (p : ℕ) [Fact p.Prime] [CharP X.functionField p]
    (hpow : ∀ y : V.X.functionField, ∃ k : X.functionField,
      dominantFunctionFieldMap π k = y ^ p)
    (hH : IsZero (Hgroup 𝒪 ⊤ 1 (SheafOfModules.unit 𝒪)))
    (W : X.Opens) (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum)
    (c : Γ(X, ⊤)) {n : ℕ} (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(V.X, ⊤))
    (θ : X.functionField →+ X.functionField)
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U))
    (hΘ : ∀ (U : X.Opens), U ≤ W → ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
      X.presheaf.germ U (genericPoint X) hU (Θ U a) =
        θ (X.presheaf.germ U (genericPoint X) hU a))
    (hid : ∀ (k : X.functionField) (y : V.X.functionField), dominantFunctionFieldMap π k = y ^ p →
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial c) * y =
        ∑ i, V.X.presheaf.germ ⊤ (genericPoint V.X) trivial (β i) *
          dominantFunctionFieldMap π (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) * k)))
    (I : InjectiveResolution (pushUnit V π)) (z : (secF 𝒪 ⊤).obj (I.cocomplex.X 1))
    (hz : (secF 𝒪 ⊤).map (I.cocomplex.d 1 2) z = 0) :
    ∃ ε : (secF 𝒪 ⊤).obj (I.cocomplex.X 0),
      (secF 𝒪 ⊤).map (I.cocomplex.d 0 1) ε = (secF 𝒪 ⊤).map ((smulE X c).app _) z := by
  classical
  have hFqc : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (pushUnit V π) :=
    ProperCoherentFiniteType.isQuasicoherent_pushforward π _
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit V.X)
  have hcov : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hUa hxU using hcov
  choose e he using fun x => exists_d_eq_restrict_of_isAffineOpen hFqc I z hz (hUa x)
  obtain ⟨s, hs, hscoc⟩ := exists_ι₀_eq_sub_of_primitives I z U e he
  have hηX : ∀ (O : X.Opens) (x : X), x ∈ O → genericPoint X ∈ O := fun O x hx =>
    ((genericPoint_spec X).mem_open_set_iff O.isOpen).mpr ⟨x, trivial, hx⟩
  let frob : ∀ {O : X.Opens}, (secF 𝒪 O).obj (pushUnit V π) →
      (secF 𝒪 O).obj (SheafOfModules.unit 𝒪) := fun {O} t =>
    (frobeniusApp π p hpow O (toΓY V π t) : Γ(X, O))
  have frob_res : ∀ {O O' : X.Opens} (h : O' ≤ O) (t : (secF 𝒪 O).obj (pushUnit V π)),
      (secRestrict 𝒪 h).app (SheafOfModules.unit 𝒪) (frob t) =
        frob ((secRestrict 𝒪 h).app _ t) := fun {O O'} h t =>
    (frobeniusApp_res π p hpow (homOfLE h) (toΓY V π t)).symm
  have frob_add : ∀ {O : X.Opens} (t t' : (secF 𝒪 O).obj (pushUnit V π)),
      frob (t + t') = frob t + frob t' := fun {O} t t' =>
    frobeniusApp_add π p hpow O (toΓY V π t) (toΓY V π t')
  have hq : ∀ a b c',
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          U a ⊓ U b ⊓ U c' ≤ U a ⊓ U b)).app _ (frob (s a b)) +
        (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          U a ⊓ U b ⊓ U c' ≤ U b ⊓ U c')).app _ (frob (s b c')) =
      (secRestrict 𝒪 (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          U a ⊓ U b ⊓ U c' ≤ U a ⊓ U c')).app _ (frob (s a c')) := fun a b c' => by
    rw [frob_res, frob_res, frob_res, ← frob_add, hscoc]
  obtain ⟨u, hu⟩ := exists_eq_sub_of_cocycle 𝒪 hH U (fun x => ⟨x, hxU x⟩)
    (fun a b => frob (s a b)) hq
  exact exists_d_eq_smulE_of_corrections V π W hW c I z U (fun x => ⟨x, hxU x⟩) e he s hs
    (fun a => frobeniusCorrection V π W b β Θ (u a)) fun a a' =>
      sub_frobeniusCorrection V π p hpow (genericPoint_mem_of_preimage_eq V π hW) c b β θ Θ hΘ
        hid ⟨hηX _ a (hxU a), hηX _ a' (hxU a')⟩ (u a) (u a') (s a a') (hu a a')

end Core

section Module

open SeparableGoUp

variable (V : VanishingSituation.{u}) {X : Scheme.{u}} (π : V.X ⟶ X) [IsIntegral X]
  [IsIntegral V.X] [IsFinite π] [Surjective π] [IsNormal X] [IsNormal V.X]

local notation "𝒪" => structureSheafRing X.toLocallyRingedSpace.toRingedSpace

/-- The sections of `𝒪_X` form commutative rings, in the spelling of `Scheme.ringCatSheaf`. -/
local instance commRingRingCatSheafObj' (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- Multiplication by `c` acts by zero on `H¹(X, π_* 𝒪_Y)` computed by `Hfunctor`, under the
hypotheses of `exists_d_eq_smulE_of_frobenius`. -/
theorem hfunctor_map_smulE_pushUnit_eq_zero (p : ℕ) [Fact p.Prime] [CharP X.functionField p]
    (hpow : ∀ y : V.X.functionField, ∃ k : X.functionField,
      dominantFunctionFieldMap π k = y ^ p)
    (hH : IsZero (Hgroup (structureSheafRing X.toLocallyRingedSpace.toRingedSpace) ⊤ 1
      (SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))))
    (W : X.Opens) (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum)
    (c : Scheme.sectionsRing X) {n : ℕ} (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(V.X, ⊤))
    (θ : X.functionField →+ X.functionField)
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U))
    (hΘ : ∀ (U : X.Opens), U ≤ W → ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
      X.presheaf.germ U (genericPoint X) hU (Θ U a) =
        θ (X.presheaf.germ U (genericPoint X) hU a))
    (hid : ∀ (k : X.functionField) (y : V.X.functionField), dominantFunctionFieldMap π k = y ^ p →
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial c) * y =
        ∑ i, V.X.presheaf.germ ⊤ (genericPoint V.X) trivial (β i) *
          dominantFunctionFieldMap π (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) * k)))
    (y : Hgroup 𝒪 ⊤ 1 (pushUnit V π)) :
    (Hfunctor 𝒪 ⊤ 1).map ((smulE X c).app (pushUnit V π)) y = 0 := by
  let I : InjectiveResolution (pushUnit V π) := InjectiveResolution.of _
  have hι : I.ι ≫ Stacks.Cohomology.endComplex (smulE X c) I.cocomplex =
      (CochainComplex.single₀ _).map ((smulE X c).app _) ≫ I.ι := by
    apply (CochainComplex.fromSingle₀Equiv _ _).injective
    apply Subtype.ext
    simp only [CochainComplex.fromSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
      Stacks.Cohomology.endComplex_f]
    exact (smulE X c).naturality (I.ι.f 0)
  change ((secF 𝒪 ⊤).rightDerived 1).map ((smulE X c).app _) y = 0
  refine (congrArg (fun k => (ConcreteCategory.hom k) y)
    (Functor.rightDerived_map_eq (secF 𝒪 ⊤) 1 _ (P := I) (Q := I)
      (Stacks.Cohomology.endComplex (smulE X c) I.cocomplex) hι)).trans ?_
  set w := (I.isoRightDerivedObj (secF 𝒪 ⊤) 1).hom y
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective
    ((secCx 𝒪 I ⊤).homologyπ 1)).mp inferInstance w
  set r := ((secF 𝒪 ⊤).mapHomologicalComplex _).map
    (Stacks.Cohomology.endComplex (smulE X c) I.cocomplex)
  have hπ : HomologicalComplex.homologyMap r 1 ((secCx 𝒪 I ⊤).homologyπ 1 z) =
      (secCx 𝒪 I ⊤).homologyπ 1 (HomologicalComplex.cyclesMap r 1 z) :=
    congrArg (fun k => k z) (HomologicalComplex.homologyπ_naturality r 1)
  have hdz : (secF 𝒪 ⊤).map (I.cocomplex.d 1 2) ((secCx 𝒪 I ⊤).iCycles 1 z) = 0 :=
    congrArg (fun k => k z) ((secCx 𝒪 I ⊤).iCycles_d 1 2)
  obtain ⟨ε, hε⟩ :=
    exists_d_eq_smulE_of_frobenius V π p hpow hH W hW c b β θ Θ hΘ hid I _ hdz
  have hzero : (secCx 𝒪 I ⊤).homologyπ 1 (HomologicalComplex.cyclesMap r 1 z) = 0 :=
    (homologyπ_one_eq_zero_iff _ _).mpr ⟨ε, hε.trans
      (congrArg (fun k => k z) (HomologicalComplex.cyclesMap_i r 1)).symm⟩
  change (I.isoRightDerivedObj (secF 𝒪 ⊤) 1).inv
    (HomologicalComplex.homologyMap r 1 w) = 0
  rw [← hz, hπ, hzero]
  exact map_zero (I.isoRightDerivedObj (secF 𝒪 ⊤) 1).inv.hom

/-- **Multiplication by `c` kills `H¹(X, π_* 𝒪_Y)`**, as a module over `Γ(X, 𝒪_X)`, under the
hypotheses of `exists_d_eq_smulE_of_frobenius`. -/
theorem smul_rightDerived_pushUnit_eq_zero (p : ℕ) [Fact p.Prime] [CharP X.functionField p]
    (hpow : ∀ y : V.X.functionField, ∃ k : X.functionField,
      dominantFunctionFieldMap π k = y ^ p)
    (hH : IsZero (Hgroup (structureSheafRing X.toLocallyRingedSpace.toRingedSpace) ⊤ 1
      (SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))))
    (W : X.Opens) (hW : π ⁻¹ᵁ W = V.preimagePuncturedSpectrum)
    (c : Scheme.sectionsRing X) {n : ℕ} (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(V.X, ⊤))
    (θ : X.functionField →+ X.functionField)
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U))
    (hΘ : ∀ (U : X.Opens), U ≤ W → ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
      X.presheaf.germ U (genericPoint X) hU (Θ U a) =
        θ (X.presheaf.germ U (genericPoint X) hU a))
    (hid : ∀ (k : X.functionField) (y : V.X.functionField), dominantFunctionFieldMap π k = y ^ p →
      dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial c) * y =
        ∑ i, V.X.presheaf.germ ⊤ (genericPoint V.X) trivial (β i) *
          dominantFunctionFieldMap π (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) * k)))
    (x : ((Scheme.sectionsFunctor X).rightDerived 1).obj (pushUnit V π)) :
    c • x = 0 := by
  refine (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply X c 1 _ x).symm.trans ?_
  let F : X.Modules := pushUnit V π
  let φ := (Scheme.smulEnd X c).app F
  let e := (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
    X.ringCatSheaf ⊤ 1).app F
  -- the vanishing in the abelian-group model, in the `structureSheafRing` spelling
  have h0 : e.hom (((Scheme.sectionsFunctor X).rightDerived 1).map φ x) = 0 :=
    (rightDerivedEvaluationForgetIso_naturality_apply φ 1 x).trans
      (hfunctor_map_smulE_pushUnit_eq_zero V π p hpow hH W hW c b β θ Θ hΘ hid _)
  exact (ConcreteCategory.congr_hom e.hom_inv_id _).symm.trans
    ((congrArg e.inv h0).trans (map_zero _))

end Module

end AlgebraicGeometry.PuncturedRestriction

end
