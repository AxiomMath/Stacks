module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingNormalForm
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US

/-!
# Stacks 0FEY from Stacks 0FEG

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `X` be a regular
scheme of finite type over `S` with affine diagonal and `δ_{X/S}` bounded. Lemma 0FEY states that

  `K_0(Vect(X)) ⊗ 𝐐 ⟶ A^*(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,   `α ↦ ch(α) ∩ [X]`,

is an isomorphism. Its proof is Proposition 0FEW for `X = Y` (Remark 0FEU), whose two conditions
are (1) the image of a coherent module supported in `δ`-dimension `≤ j` lies in degrees `≤ j`,
and (2) for an integral closed subscheme `Z ⊆ X` of `δ`-dimension `k` the degree `k` part of the
image of `[𝒪_Z]` is `[Z]`. The source reduces (2) to an open neighbourhood `V` of the generic
point `ξ` of `Z` on which `Z ∩ V ⟶ V` is cut out by a regular sequence, and concludes with
Lemma 0FEH, the consequence on the fundamental class of the formula of Lemma 0FEG for the
localized Chern classes of `i_*𝒪_Z`.

This file carries out that argument from the conclusion of Lemma 0FEG, taken as a hypothesis.

* **The neighbourhood.** The local ring `𝒪_{X, ξ}` is regular, hence a domain, so `ξ` lies on a
  single irreducible component of `X` and has an irreducible open neighbourhood. Inside it, an
  affine open `V ∋ ξ` on which `Z ∩ V ⟶ V` is regular of codimension `r = dim 𝒪_{X, ξ}`; every
  point of `V` specializes from the generic point of `V`, of `δ`-dimension `δ(ξ) + r`, so all
  irreducible components of `V` have that `δ`-dimension.
* **`𝒪_Z` restricted to `V`.** Restriction to an open is exact, and `(i_*𝒪_Z)|_V = i'_*𝒪_{Z ∩ V}`
  for `i' : Z ∩ V ⟶ V`; so the base change of the situation `Z ⟶ X`, `𝒪_Z[0]` of Situation 0GUJ
  to `V` has the localized Chern classes of `i'_*𝒪_{Z ∩ V}`, both being the restrictions of those
  of `Z ⟶ X` (Stacks 0FB3).
* **Codimension `r ≥ 1`.** Lemma 0FEH (3), (4) for `Z ∩ V ⟶ V`.
* **Codimension `0`.** Then `ξ` is the generic point of `V` and `Z ∩ V = V`; the degree `δ(ξ)`
  part of `ch(Z ∩ V ⟶ V, 𝒪) ∩ [V]` is `P_0 ∩ [V]`, which by Stacks 0FB4 is the rank of `𝒪_V`,
  that is `1`, capped with `[V]`.

## Main results

* `Stacks.Chow.LocalizedSituation.isRegularImmersionChernFormula_pullback` — the conclusion
  of Stacks 0FEG for `i'_*𝒪_{Z'}` gives it for a base change `Lf^*E ≅ i'_*𝒪_{Z'}[0]`.
* `Stacks.Chow.LocalizedSituation.hasFundamentalDegreePart_of_isIso` — the codimension `0`
  case of Stacks 0FEH (3), (4).
* `Stacks.Chow.isDiagonalOnIntegralNear_of_isRegularImmersionChernFormula` — the local form of
  condition (2) of the proof of Stacks 0FEW at every point, given Stacks 0FEG.
* `Stacks.Chow.bijective_rationalChernCharacterCapFundamentalClass_of_chernFormula` — Stacks 0FEY,
  given Stacks 0FEG.

## Implementation notes

The conclusion of Lemma 0FEG enters as a hypothesis, for the structure sheaf `i_*𝒪_Z` of every
regular closed immersion `i : Z ⟶ Y` of codimension `r ≥ 1` into a quasi-compact scheme `Y`
locally of finite type over the base, the situation being
`Stacks.Chow.regularImmersionStructureSheafSituation`; that is the lemma restricted to its first
finiteness alternative. The source's formula `(-1)^{r-1}(r-1)!` presupposes `r ≥ 1`; the points of
`X` of codimension `0`, which Lemma 0FEH does not cover, are treated directly.

"Finite type over `S`" is read as locally of finite type with `X` Noetherian, which over the
locally Noetherian base is the same as quasi-compact. Only the lower bound of `δ_{X/S}` is used,
an upper bound holding on every Noetherian `X`.

Nothing here carries the attribute for Tag 0FEY: that sits on the unconditional form
`Stacks.Chow.bijective_rationalChernCharacterCapFundamentalClass`, in
`StacksFrontier/AlgebraicGeometry/Chow/RationalIntersection/RationalIntersectionProduct.lean`,
which is this file's theorem applied to Stacks 0FEG
(`Stacks.Chow.isRegularImmersionChernFormula_of_compactSpace`). That file cannot be imported
here, since the proof of Stacks 0FEG imports this one.

## References

* [Stacks Project, Tag 0FEY](https://stacks.math.columbia.edu/tag/0FEY)
* [Stacks Project, Tag 0FEW](https://stacks.math.columbia.edu/tag/0FEW)
* [Stacks Project, Tag 0FEH](https://stacks.math.columbia.edu/tag/0FEH)
* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0FB4](https://stacks.math.columbia.edu/tag/0FB4)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 00NQ](https://stacks.math.columbia.edu/tag/00NQ)
* [Stacks Project, Tag 063I](https://stacks.math.columbia.edu/tag/063I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open scoped TensorProduct

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The structure sheaf of a closed subscheme, restricted to an open -/

section Restriction

variable {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (v : U ⟶ X) [IsOpenImmersion v]

/-- **`(i_*𝒪_Z)[0]` restricts to an open `U ⊆ X` as `(i'_*𝒪_{Z ∩ U})[0]`**, for a closed
immersion `i : Z ⟶ X`, an open immersion `v : U ⟶ X` and the base change
`i' : Z ×_X U ⟶ U`. The derived pullback along `v` is the ordinary one, `v^*` being exact, and
`v^*i_*𝒪_Z ≅ i'_*(𝒪_Z|_{Z ×_X U}) ≅ i'_*𝒪_{Z ×_X U}` because the ideal of `Z ×_X U` is the
pulled-back ideal of `Z`. -/
def derivedPullbackSinglePushforwardUnitIso :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback v.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      (DerivedCategory.singleFunctor U.Modules 0).obj
        ((Scheme.Modules.pushforward (pullback.snd i v)).obj
          (SheafOfModules.unit (pullback i v).ringCatSheaf)) :=
  AlgebraicGeometry.derivedPullbackSingleIsoOfPreservesHomology v.toLRSHom.toShHom _ ≪≫
    (DerivedCategory.singleFunctor U.Modules 0).mapIso
      ((AlgebraicGeometry.baseChangeIsoOfKernelAnnihilates (IsPullback.of_hasPullback i v).flip.w
          (AlgebraicGeometry.kernelAnnihilatesPullbackPushforward_of_isPullback
            (IsPullback.of_hasPullback i v).flip)).app (SheafOfModules.unit Z.ringCatSheaf) ≪≫
        (Scheme.Modules.pushforward (pullback.snd i v)).mapIso
          (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso
            (pullback.fst i v).toLRSHom.toShHom))

end Restriction


/-! ### An irreducible neighbourhood and its dimension -/

section Irreducible

/-- A nonempty open subset of an irreducible set is irreducible. -/
private theorem isIrreducible_of_isOpen_of_subset {X : Type*} [TopologicalSpace X] {W U : Set X}
    {x : X} (hW : IsIrreducible W) (hU : IsOpen U) (hsub : U ⊆ W) (hx : x ∈ U) :
    IsIrreducible U :=
  ⟨⟨x, hx⟩, hW.isPreirreducible.open_subset hU hsub⟩

/-- **A point with integral local ring has an irreducible open neighbourhood**, in a scheme whose
underlying space is Noetherian. The generizations of `x` are the image of `Spec 𝒪_{X, x}`, which
is irreducible, so `x` lies on a single irreducible component of `X`; the complement of the
finitely many other components is the neighbourhood. -/
theorem exists_isIrreducible_opens_of_isDomain_stalk {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (x : X) [IsDomain (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIrreducible (U : Set X) := by
  have hG : IsIrreducible {y : X | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ
      (PrimeSpectrum (X.presheaf.stalk x))).image _ (X.fromSpecStalk x).continuous.continuousOn
  set W := closure {y : X | y ⤳ x}
  have hW : IsIrreducible W := hG.closure
  have hcomp : ∀ W' ∈ irreducibleComponents X, x ∈ W' → W' = W := by
    intro W' hW' hx
    have hcl := isClosed_of_mem_irreducibleComponents W' hW'
    have hgen := hW'.1.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hgen
    have hsp : hW'.1.genericPoint ⤳ x := hgen.specializes hx
    have hsub : W' ⊆ W := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (subset_closure hsp)) isClosed_closure
    exact (hW'.2 hW hsub).antisymm' hsub
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).subset
    (Set.sep_subset (irreducibleComponents X) fun W' => x ∉ W')
  set B := ⋃ W' ∈ {W' ∈ irreducibleComponents X | x ∉ W'}, W'
  have hB : IsClosed B := hfin.isClosed_biUnion fun W' hW' =>
    isClosed_of_mem_irreducibleComponents W' hW'.1
  have hxB : x ∉ B := by
    intro h
    obtain ⟨W', hW', hxW'⟩ := Set.mem_iUnion₂.1 h
    exact hW'.2 hxW'
  have hsub : Bᶜ ⊆ W := by
    intro y hy
    obtain ⟨W', hW', hyW'⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    by_cases hx : x ∈ W'
    · exact hcomp W' hW' hx ▸ hyW' rfl
    · exact absurd (Set.mem_biUnion (x := W')
        (show W' ∈ {W' ∈ irreducibleComponents X | x ∉ W'} from ⟨hW', hx⟩) (hyW' rfl)) hy
  exact ⟨⟨Bᶜ, hB.isOpen_compl⟩, hxB,
    isIrreducible_of_isOpen_of_subset hW hB.isOpen_compl hsub hxB⟩

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

omit [LocallyOfFiniteType sX] in
/-- On an irreducible open `V`, every generic point of an irreducible component of `V` has the
`δ`-dimension of the generic point of `V`: `V` is its only irreducible component. -/
theorem relativeDimension_eq_of_mem_irreducibleComponents_opens {V : X.Opens}
    (hV : IsIrreducible (V : Set X)) {W : Set V.toScheme}
    (hW : W ∈ irreducibleComponents V.toScheme) {w : V.toScheme}
    (hw : IsGenericPoint w (closure W)) :
    relativeDimension C.dimensionFunction (V.ι ≫ sX) w =
      relativeDimension C.dimensionFunction sX hV.genericPoint := by
  have hgV := hV.isGenericPoint_genericPoint_closure
  have hmem : hV.genericPoint ∈ (V : Set X) :=
    (hgV.mem_open_set_iff V.isOpen).2 ⟨w.1, subset_closure w.2, w.2⟩
  have : IrreducibleSpace V.toScheme := isIrreducible_iff_irreducibleSpace.mp hV
  have hWu : W = Set.univ :=
    (Set.subset_univ W).antisymm (hW.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ W))
  have h1 : w ⤳ (⟨hV.genericPoint, hmem⟩ : V.toScheme) :=
    hw.specializes (by rw [hWu, closure_univ]; trivial)
  have h2 : (V.ι w : X) ⤳ hV.genericPoint := h1.map V.ι.continuous
  have h3 : hV.genericPoint ⤳ (V.ι w : X) := hgV.specializes (subset_closure w.2)
  rw [relativeDimension_comp_isOpenImmersion, (h2.antisymm h3).eq]

/-- **The local ring at a point of an irreducible open `V` has dimension `δ(η) - δ(x)`**, `η`
the generic point of `V`. -/
theorem ringKrullDim_stalk_eq_of_isIrreducible {V : X.Opens} (hV : IsIrreducible (V : Set X))
    {x : X} (hx : x ∈ V) :
    ringKrullDim (X.presheaf.stalk x) =
      ((((relativeDimension C.dimensionFunction sX hV.genericPoint -
        relativeDimension C.dimensionFunction sX x).toNat : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have h := ringKrullDim_stalk_eq_toNat_sub_relativeDimension C (V.ι ≫ sX)
    (n := relativeDimension C.dimensionFunction sX hV.genericPoint)
    (fun W => relativeDimension_eq_of_mem_irreducibleComponents_opens C sX hV W.2
      (W.2.1.isGenericPoint_genericPoint_closure)) (⟨x, hx⟩ : V.toScheme)
  have e2 : relativeDimension C.dimensionFunction (V.ι ≫ sX) (⟨x, hx⟩ : V.toScheme) =
      relativeDimension C.dimensionFunction sX x :=
    relativeDimension_comp_isOpenImmersion _ _ _ _
  rw [e2] at h
  rw [← h]
  exact ringKrullDim_eq_of_ringEquiv
    (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv.symm

/-- The generic point of an irreducible open `V` has `δ`-dimension at least that of any point of
`V`. -/
theorem relativeDimension_le_genericPoint {V : X.Opens} (hV : IsIrreducible (V : Set X))
    {x : X} (hx : x ∈ V) :
    relativeDimension C.dimensionFunction sX x ≤
      relativeDimension C.dimensionFunction sX hV.genericPoint :=
  relativeDimension_le_of_mem_closure C sX
    (hV.isGenericPoint_genericPoint_closure.def ▸ subset_closure hx)

end Irreducible

/-! ### The localized classes of a base change, against `i'_*𝒪_{Z'}` -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) {X' : Scheme.{u}} (f : X' ⟶ S.X)
  [LocallyOfFiniteType f] [Perfect (Limits.pullback.snd S.i f)]
  (hX' : CompactSpace X' ∨ ∀ T ∈ irreducibleComponents X', IsCompact T)
  (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj S.E ≅
    (DerivedCategory.singleFunctor X'.Modules 0).obj
      ((Scheme.Modules.pushforward (Limits.pullback.snd S.i f)).obj
        (SheafOfModules.unit (Limits.pullback S.i f).ringCatSheaf)))
  (h : S.IsZeroOnComplement)

include e in
/-- **The localized Chern classes of a base change do not see the identification of `Lf^*E`.**
In Situation 0GUJ with `E|_{X ∖ Z}` zero, let `f : X' ⟶ X` be locally of finite type with
`i' : Z' = Z ×_X X' ⟶ X'` perfect, and suppose `Lf^*E ≅ i'_*𝒪_{Z'}[0]`. Then
`c_t(Z' ⟶ X', Lf^*E) = c_t(Z' ⟶ X', i'_*𝒪_{Z'})` for every `t ≥ 1`: both are the restriction of
`c_t(Z ⟶ X, E)` (Stacks 0FB3), the second through the morphism of graph constructions attached to
the isomorphism (`Stacks.Chow.exists_lift_graphBlowupToBase_and_iso`). -/
theorem localizedChernClassOfIsZero_pullback_eq {t : ℕ}
    (ht : 0 < t) :
    localizedChernClassOfIsZero (S := S.pullback f) h.pullback ht =
      localizedChernClassOfIsZero (S := pushforwardStructureSheafSituation S.base (f ≫ S.a)
          (Limits.pullback.snd S.i f) hX' 0)
        (isZeroOnComplement_pushforwardStructureSheafSituation S.base (f ≫ S.a)
          (Limits.pullback.snd S.i f) hX' 0) ht := by
  set R := pushforwardStructureSheafSituation S.base (f ≫ S.a) (Limits.pullback.snd S.i f) hX' 0
  have hR := isZeroOnComplement_pushforwardStructureSheafSituation S.base (f ≫ S.a)
    (Limits.pullback.snd S.i f) hX' 0
  obtain ⟨k, hk, ⟨eQ⟩⟩ := exists_lift_graphBlowupToBase_and_iso S.a f S.E S.perfect R.E
    R.perfect e
  have h1 := (S.withDegree h t).bivariantRestriction_localizedChern f
    (S.isFiniteLocallyFreeOfRankLTOnComplement_withDegree h ht)
  have h2 := bivariantRestriction_graphChernClass_of_iso S.base S.a f S.E S.perfect R.E R.perfect
    S.i k hk eQ (S.withDegree h t).graphSubschemeι (R.withDegree hR t).graphSubschemeι
    (S.withDegree h t).isFiniteLocallyFree_graphObjectRestrictHomology
    (R.withDegree hR t).isFiniteLocallyFree_graphObjectRestrictHomology
    S.hasDefinedChernClasses_graphObject R.hasDefinedChernClasses_graphObject t
    (S.withDegree h t).mem_range_graphSubschemeι (R.withDegree hR t).mem_range_graphSubschemeι
    ((S.withDegree h t).finiteLocallyFreeRank_graphSubscheme_lt
      (S.isFiniteLocallyFreeOfRankLTOnComplement_withDegree h ht))
    ((R.withDegree hR t).finiteLocallyFreeRank_graphSubscheme_lt
      (R.isFiniteLocallyFreeOfRankLTOnComplement_withDegree hR ht))
  exact h1.symm.trans h2

variable {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim (Limits.pullback.snd S.i f) r)

include e in
/-- **Stacks 0FEG for `i'_*𝒪_{Z'}` gives it for `Lf^*E`.** In Situation 0GUJ with `E|_{X ∖ Z}`
zero, let `f : X' ⟶ X` be locally of finite type with `Lf^*E ≅ i'_*𝒪_{Z'}[0]`, where
`i' : Z' = Z ×_X X' ⟶ X'` is regular of codimension `r ≥ 1`. If the conclusion of Stacks 0FEG
holds for `i'_*𝒪_{Z'}`, it holds for the base change `Z' ⟶ X'`, `Lf^*E` of Situation 0GUJ: the
localized Chern classes of the two agree
(`Stacks.Chow.LocalizedSituation.localizedChernClassOfIsZero_pullback_eq`). -/
theorem isRegularImmersionChernFormula_pullback (hr : 0 < r)
    (hF : (regularImmersionStructureSheafSituation S.base (f ≫ S.a) (Limits.pullback.snd S.i f)
      hreg hX' 0).IsRegularImmersionChernFormula
        (isZeroOnComplement_regularImmersionStructureSheafSituation S.base (f ≫ S.a)
          (Limits.pullback.snd S.i f) hreg hX' 0) hreg hr) :
    (S.pullback f).IsRegularImmersionChernFormula h.pullback hreg hr :=
  ⟨fun t ht htr => (S.localizedChernClassOfIsZero_pullback_eq
      f hX' e h ht).trans (hF.1 t ht htr),
    (S.localizedChernClassOfIsZero_pullback_eq f hX' e h
      hr).trans hF.2⟩

end LocalizedSituation

/-! ### Codimension zero -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) (h : S.IsZeroOnComplement) [IsIso S.i]
  (e : S.E ≅ (DerivedCategory.singleFunctor S.X.Modules 0).obj
    ((Scheme.Modules.pushforward S.i).obj (SheafOfModules.unit S.Z.ringCatSheaf)))

include e in
/-- **`E|_Z` has rank one when `Z ⟶ X` is an isomorphism and `E ≅ i_*𝒪_Z[0]`**: then
`Li^*E ≅ i^*i_*𝒪_Z[0] ≅ 𝒪_Z[0]`, whose derived-fibre Euler characteristic is `1`. -/
theorem perfectRank_derivedPullback_eq_one_of_isIso :
    perfectRank ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        S.i.toLRSHom.toShHom).obj S.E)
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ S.perfect) =
      LocallyConstant.const S.Z 1 := by
  have := Stacks.ClosedImmersion.full_pushforward S.i
  have := Stacks.ClosedImmersion.faithful_pushforward S.i
  have hcounit : IsIso (Scheme.Modules.pullbackPushforwardAdjunction S.i).counit := inferInstance
  have e₂ : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      S.i.toLRSHom.toShHom).obj S.E ≅
        (DerivedCategory.singleFunctor S.Z.Modules 0).obj (SheafOfModules.unit S.Z.ringCatSheaf) :=
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback S.i.toLRSHom.toShHom).mapIso e ≪≫
      AlgebraicGeometry.derivedPullbackSingleIsoOfPreservesHomology S.i.toLRSHom.toShHom _ ≪≫
      (DerivedCategory.singleFunctor S.Z.Modules 0).mapIso
        ((asIso (Scheme.Modules.pullbackPushforwardAdjunction S.i).counit).app
          (SheafOfModules.unit S.Z.ringCatSheaf))
  have hpc := DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback S.i.toLRSHom.toShHom _ S.perfect)
  have hpc' : RingedSpace.IsPseudoCoherent (X := S.Z.toRingedSpace)
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit S.Z.ringCatSheaf)) := by
    obtain ⟨P, hP, ⟨v⟩⟩ := hpc
    exact ⟨P, hP, ⟨v ≪≫ e₂⟩⟩
  have hr : SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := StrictlyPerfect.structureSheafOfRings
        (S.Z.toRingedSpace.restrict (⊤ : S.Z.Opens).isOpenEmbedding))
      ((RingedSpace.PseudoCoherence.restrictModules S.Z.toRingedSpace ⊤).obj
        (SheafOfModules.unit S.Z.ringCatSheaf)) 1 :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict S.Z ⊤).app _ ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (⊤ : S.Z.Opens).ι).app _ ≪≫
        RingedSpaceModuleAdjunction.modulePullbackObjUnitIso
          (⊤ : S.Z.Opens).ι.toLRSHom.toShHom).symm)
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit _)
  ext z
  refine (perfectRank_apply _ _ z).trans ?_
  refine (congrFun (DerivedFibreBetti.chiDerivedFibre_congr _ _ hpc' e₂) z).trans ?_
  exact DerivedFibreBetti.chiDerivedFibre_singleFunctor_eq_of_restrict S.Z _ hpc' ⊤ 1 hr z trivial

include e in
/-- **Stacks 0FEH (3), (4) in codimension `0`.** In Situation 0GUJ with `E|_{X ∖ Z}` zero, let
`i : Z ⟶ X` be an isomorphism, `E ≅ i_*𝒪_Z[0]`, and let every irreducible component of `X` have
`δ`-dimension `k`. Then the degree `k` part of `ch(Z ⟶ X, E) ∩ [X]` is `[Z]_k`.

Only `P_0 ∩ [X]_k` contributes, `[X]_m` vanishing for `m ≠ k`; by Stacks 0FB4
(`Stacks.Chow.LocalizedSituation.localizedPowerSum_cap_chowPush`), applied to
`[X]_k = i_*[Z]_k`, it is `r(E|_Z) ∩ [Z]_k`, and the rank of `E|_Z ≅ 𝒪_Z[0]` is `1`. -/
theorem hasFundamentalDegreePart_of_isIso (k : ℤ)
    (hpure : ∀ W : irreducibleComponents S.X, deltaDimension S.base S.a
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set S.X) W.2⟩ = k) (N : ℕ) :
    S.HasFundamentalDegreePart h N k := by
  have hpure' : ∀ W : irreducibleComponents S.X, deltaDimension S.base (𝟙 S.X ≫ S.a)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set S.X) W.2⟩ = k := fun W => by
    simpa using hpure W
  have hEZ := S.hasDefinedChernClasses_E.derivedPullback S.i
  have hrank := S.perfectRank_derivedPullback_eq_one_of_isIso e
  unfold HasFundamentalDegreePart capFundamentalClassDegreePart
  rw [Finset.sum_eq_single 0]
  · dsimp only
    rw [Nat.factorial_zero, Nat.cast_one, inv_one]
    congr 1
    have key : ∀ (m : ℤ) (hm : m = k) (hm' : m - ((0 : ℕ) : ℤ) = k),
        chowGroupDegreeEquiv S.base _ hm' ((S.localizedPowerSum h 0).cap (𝟙 S.X) m
          (fundamentalChowClass S.base (𝟙 S.X ≫ S.a) m)) =
        fundamentalChowClass S.base (pullback.fst S.i (𝟙 S.X) ≫ (S.i ≫ S.a)) k := by
      intro m hm hm'
      subst hm
      have hpush : fundamentalChowClass S.base (𝟙 S.X ≫ S.a) m =
          chowPush S.base (pullback.fst S.i (𝟙 S.X) ≫ (S.i ≫ S.a)) (𝟙 S.X ≫ S.a)
            (pullback.snd S.i (𝟙 S.X)) (pullbackSnd_comp_structureMorphism rfl (𝟙 S.X)) m
            (fundamentalChowClass S.base (pullback.fst S.i (𝟙 S.X) ≫ (S.i ≫ S.a)) m) :=
        (chowPushforwardOfIso_fundamentalChowClass S.base _ _ (pullback.snd S.i (𝟙 S.X))
          (pullbackSnd_comp_structureMorphism rfl (𝟙 S.X)) m).symm
      rw [hpush, S.localizedPowerSum_cap_chowPush h 0 (𝟙 S.X) m]
      have h1 : perfectPowerSumComponent S.base (S.i ≫ S.a) hEZ 0 =
          (1 : TotalChowClass S.base (S.i ≫ S.a)) 0 := by
        show perfectPowerSum S.base _ hEZ 0 0 = _
        rw [perfectPowerSum_zero_eq_ofLocallyConstant S.base _ hEZ
          (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _ S.perfect), hrank,
          TotalChowClass.ofLocallyConstant_const, Int.cast_one]
      rw [h1, TotalChowClass.one_apply_zero]
      refine eq_of_heq ((chowGroupDegreeEquiv_heq S.base _ hm' _).trans
        ((BivariantClass.idRule_bivariantClassDegreeCongr _ _ _ _ _ _ _ _).trans
          (idRule_bivariantIdentityClassOfInvertible_heq _ _ _ _ _)))
    exact key _ (by push_cast; ring) _
  · intro p _ hp
    rw [fundamentalChowClass_eq_zero_of_deltaDimension_eq S.base _ hpure' (by omega), map_zero,
      map_zero, TensorProduct.tmul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h0

end LocalizedSituation

/-! ### Condition (2) of the proof of Stacks 0FEW near a point, from Stacks 0FEG -/

section Near

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Condition (2) of the proof of Stacks 0FEW near a point, given Stacks 0FEG.** Let `X` be
regular and Noetherian, locally of finite type over the base, and assume the conclusion of
Stacks 0FEG for the structure sheaf of every regular closed immersion of positive codimension into
a quasi-compact scheme locally of finite type over the base. Then at every point `ξ` the degree
`δ(ξ)` part of `ch(Z_ξ ⟶ X, 𝒪_{Z_ξ}[0]) ∩ [V]` is `[Z_ξ ∩ V]` for some open `V ∋ ξ`
(`Stacks.Chow.IsDiagonalOnIntegralNear`).

The open `V` is affine and irreducible, with `Z_ξ ∩ V ⟶ V` regular of codimension
`r = dim 𝒪_{X, ξ}` (Stacks 00NQ, 063I); all of `V` has `δ`-dimension `δ(ξ) + r`. For `r ≥ 1` this
is Stacks 0FEH (3), (4)
(`Stacks.Chow.LocalizedSituation.hasFundamentalDegreePart_of_isRegularImmersionChernFormula`)
for the base change of `𝒪_{Z_ξ}[0]` to `V`, which is `𝒪_{Z_ξ ∩ V}[0]`
(`Stacks.Chow.LocalizedSituation.isRegularImmersionChernFormula_pullback`); for `r = 0`,
`ξ` is the generic point of `V` and `Z_ξ ∩ V = V`
(`Stacks.Chow.LocalizedSituation.hasFundamentalDegreePart_of_isIso`). -/
theorem isDiagonalOnIntegralNear_of_isRegularImmersionChernFormula [IsNoetherian X]
    (hX : AlgebraicGeometry.IsRegular X)
    (h0FEG : ∀ {Z Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [CompactSpace Y]
      (i : Z ⟶ Y) [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r)
      (hr : 0 < r),
      (regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›)
        0).IsRegularImmersionChernFormula
          (isZeroOnComplement_regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›) 0)
          hreg hr)
    (ξ : X) :
    IsDiagonalOnIntegralNear C sX ξ := by
  intro K eK
  obtain ⟨-, hstalk⟩ := ((AlgebraicGeometry.isRegular_tfae X).out 1 2).mp hX
  have := hstalk ξ
  have : IsDomain (X.presheaf.stalk ξ) := IsRegularLocalRing.isDomain _
  set I := integralComponentAt ξ
  set δ := fun x : X => relativeDimension C.dimensionFunction sX x
  obtain ⟨U, hξU, hU⟩ := exists_isIrreducible_opens_of_isDomain_stalk ξ
  set r := (δ hU.genericPoint - δ ξ).toNat with hrdef
  have hrU := ringKrullDim_stalk_eq_of_isIrreducible C sX hU hξU
  have hr : ringKrullDim (X.presheaf.stalk ξ) = r := by
    rw [hrU]
    rfl
  obtain ⟨V₀, -, hξV₀, hV₀⟩ :=
    exists_isAffineOpen_isRegularClosedImmersionOfCodim_integralComponentAt hX ξ r hr
  set V : X.Opens := V₀ ⊓ U
  have hξV : ξ ∈ V := ⟨hξV₀, hξU⟩
  have hV : IsIrreducible (V : Set X) :=
    isIrreducible_of_isOpen_of_subset hU V.isOpen inf_le_right hξV
  have hδV : δ hV.genericPoint = δ ξ + r := by
    have h1 := ringKrullDim_stalk_eq_of_isIrreducible C sX hV hξV
    rw [hrU] at h1
    have h2 : (δ hU.genericPoint - δ ξ).toNat = (δ hV.genericPoint - δ ξ).toNat := by
      exact_mod_cast h1
    have h3 := relativeDimension_le_genericPoint C sX hU hξU
    have h4 := relativeDimension_le_genericPoint C sX hV hξV
    simp only [δ] at h2 hrdef ⊢
    omega
  -- the regular immersion over `V`
  have hreg : IsRegularClosedImmersionOfCodim (pullback.snd I.subschemeι V.ι) r := by
    set ι : V.toScheme ⟶ V₀.toScheme := X.homOfLE inf_le_left
    have hι : ι ≫ V₀.ι = V.ι := X.homOfLE_ι _
    have hP := IsPullback.of_hasPullback V₀.ι I.subschemeι
    have H := (IsPullback.of_hasPullback I.subschemeι V.ι).flip
    have hreg₀ := hV₀ (pullback.fst V₀.ι I.subschemeι) (pullback.snd V₀.ι I.subschemeι) hP
    set a : pullback I.subschemeι V.ι ⟶ pullback V₀.ι I.subschemeι :=
      pullback.lift (pullback.snd I.subschemeι V.ι ≫ ι) (pullback.fst I.subschemeι V.ι) (by
        rw [Category.assoc, hι]; exact H.w)
    have sq : IsPullback a (pullback.snd I.subschemeι V.ι) (pullback.fst V₀.ι I.subschemeι) ι := by
      refine IsPullback.of_right (h₁₂ := pullback.snd V₀.ι I.subschemeι) (v₁₃ := I.subschemeι)
        (h₂₂ := V₀.ι) ?_ (pullback.lift_fst _ _ _) hP.flip
      rw [pullback.lift_snd, hι]
      exact H.flip
    exact IsRegularClosedImmersionOfCodim.of_isPullback sq hreg₀
  refine ⟨V, hξV, fun N hN => ?_⟩
  set S := integralComponentLocalizedSituation C sX ξ K eK
  have hS := isZeroOnComplement_integralComponentLocalizedSituation C sX ξ K eK
  have hpure : ∀ W : irreducibleComponents V.toScheme, deltaDimension C (V.ι ≫ sX)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set V.toScheme) W.2⟩ = δ ξ + r := by
    intro W
    have hg := W.2.1.isGenericPoint_genericPoint_closure
    have hg' := hg
    rw [(isClosed_of_mem_irreducibleComponents (W : Set V.toScheme) W.2).closure_eq] at hg'
    rw [deltaDimension_eq_of_isGenericPoint C _ _ W.2.1.genericPoint hg',
      relativeDimension_eq_of_mem_irreducibleComponents_opens C sX hV W.2 hg]
    exact hδV
  have hrN : r ≤ N := by
    have := hN hV.genericPoint
    simp only [δ] at hδV
    omega
  have e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      V.ι.toLRSHom.toShHom).obj S.E ≅ (DerivedCategory.singleFunctor V.toScheme.Modules 0).obj
        ((Scheme.Modules.pushforward (pullback.snd I.subschemeι V.ι)).obj
          (SheafOfModules.unit (pullback I.subschemeι V.ι).ringCatSheaf)) :=
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback V.ι.toLRSHom.toShHom).mapIso eK ≪≫
      derivedPullbackSinglePushforwardUnitIso I.subschemeι V.ι
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · have hgV := hV.isGenericPoint_genericPoint_closure
    have hηξ : hV.genericPoint = ξ := by
      by_contra hne
      have hmem : ξ ∈ closure {hV.genericPoint} := hgV.def ▸ subset_closure hξV
      have := relativeDimension_lt_of_mem_closure_of_ne C sX hmem (Ne.symm hne)
      simp only [δ, h0] at hδV
      omega
    have hsub : (V : Set X) ⊆ closure {ξ} := fun x hx => hηξ ▸ hgV.def ▸ subset_closure hx
    have : AlgebraicGeometry.IsReduced X := isReduced_of_isRegular hX
    have : Surjective (pullback.snd I.subschemeι V.ι) := ⟨fun v => by
      have : v ∈ Set.range (pullback.snd I.subschemeι V.ι) := by
        rw [Scheme.Pullback.range_snd, Set.mem_preimage, Scheme.IdealSheafData.range_subschemeι,
          coe_support_integralComponentAt]
        exact hsub (by rw [← V.range_ι]; exact ⟨v, rfl⟩)
      exact this⟩
    have : IsIso (pullback.snd I.subschemeι V.ι) := isIso_of_isClosedImmersion_of_surjective _
    exact (S.pullback V.ι).hasFundamentalDegreePart_of_isIso hS.pullback e _
      (fun W => (hpure W).trans (by simp [δ, h0])) N
  · have := perfect_of_isRegularImmersion _ hreg.isRegularImmersion
    have hF := S.isRegularImmersionChernFormula_pullback V.ι (Or.inl inferInstance) e hS hreg hpos
      (h0FEG (V.ι ≫ sX) _ hreg hpos)
    exact LocalizedSituation.hasFundamentalDegreePart_of_isRegularImmersionChernFormula _ _
      hreg hpos hF (δ ξ + r) hpure N hrN _ rfl

end Near

/-! ### Stacks 0FEY from Stacks 0FEG -/

section Bijective

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]

/-- **Stacks 0FEY, given Stacks 0FEG.** Let `X` be a regular scheme of finite type over the base
(that is, locally of finite type and Noetherian), with affine diagonal and `δ_{X/S}` bounded
below. If the conclusion of Stacks 0FEG holds for the structure sheaf of every regular closed
immersion of positive codimension into a quasi-compact scheme locally of finite type over the
base, then

  `K_0(Vect(X)) ⊗ 𝐐 ⟶ A^*(X) ⊗ 𝐐 ⟶ CH_*(X) ⊗ 𝐐`,   `α ↦ ch(α) ∩ [X]`,

is bijective.

By Proposition 0FEW (`Stacks.Chow.bijective_liftBaseChange`) on `K'_0(X) = K_0(Vect(X))` it
suffices to check its two conditions:
`Stacks.Chow.isDimensionTriangular_coherentChernCharacterCapFundamentalClass` and, through
`Stacks.Chow.isDiagonalOnIntegral_coherentChernCharacterCapFundamentalClass_of_near`,
`Stacks.Chow.isDiagonalOnIntegralNear_of_isRegularImmersionChernFormula`. -/
theorem bijective_rationalChernCharacterCapFundamentalClass_of_chernFormula
    (h0FEG : ∀ {Z Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [CompactSpace Y]
      (i : Z ⟶ Y) [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r)
      (hr : 0 < r),
      (regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›)
        0).IsRegularImmersionChernFormula
          (isZeroOnComplement_regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›) 0)
          hreg hr)
    (hX : AlgebraicGeometry.IsRegular X)
    (hδ : BddBelow (Set.range (relativeDimension C.dimensionFunction sX))) :
    Function.Bijective (rationalChernCharacterCapFundamentalClass C sX) := by
  obtain ⟨lo, hlo⟩ := hδ
  have hlo' : ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x := fun x => hlo ⟨x, rfl⟩
  rw [← bijective_liftBaseChange_coherentChernCharacterCapFundamentalClass_iff C sX hX]
  exact bijective_liftBaseChange _
    (isDimensionTriangular_coherentChernCharacterCapFundamentalClass C sX hX)
    (isDiagonalOnIntegral_coherentChernCharacterCapFundamentalClass_of_near C sX hX lo hlo'
      fun ξ => isDiagonalOnIntegralNear_of_isRegularImmersionChernFormula C sX hX h0FEG ξ)
    lo hlo'

/-- **Stacks 0FEY, given Stacks 0FEG, as bijectivity of `α ↦ ch(α) ∩ [X]` read through the cap
product operator** `Stacks.Chow.rationalChernCharacterCap`: the form in which the rational
intersection product of Section 0FEX is built. -/
theorem bijective_flip_rationalChernCharacterCap_of_chernFormula
    (h0FEG : ∀ {Z Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [CompactSpace Y]
      (i : Z ⟶ Y) [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r)
      (hr : 0 < r),
      (regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›)
        0).IsRegularImmersionChernFormula
          (isZeroOnComplement_regularImmersionStructureSheafSituation C sY i hreg (Or.inl ‹_›) 0)
          hreg hr)
    (hX : AlgebraicGeometry.IsRegular X)
    (hδ : BddBelow (Set.range (relativeDimension C.dimensionFunction sX))) :
    Function.Bijective ((rationalChernCharacterCap C sX).flip (rationalFundamentalClass C sX)) := by
  have he : (rationalChernCharacterCap C sX).flip (rationalFundamentalClass C sX) =
      rationalChernCharacterCapFundamentalClass C sX :=
    LinearMap.ext fun x => (rationalChernCharacterCapFundamentalClass_apply C sX x).symm
  rw [he]
  exact bijective_rationalChernCharacterCapFundamentalClass_of_chernFormula C sX h0FEG hX hδ

end Bijective

end Stacks.Chow

end
