module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTraceShortExact
public import StacksFrontier.Homology.KFlat.BifunctorTruncationGE
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The core of the trace formula for bounded complexes

Let `j : X ⟶ X̄` be a compactification of a scheme `X` over a finite field `k`. The vanishing of
`Tr(π_X^* | RΓ_c(X_k̄, -))` (`Stacks.EtaleCohomology.CompactSupportTraceVanishes`) on a sheaf `F`
placed in degree `0` implies it on `F` placed in any degree `a`, and the vanishing on the terms of
a bounded complex, each placed in its own degree, implies it on the complex.

The first is the short exact sequence `0 → F[-a] → cone(𝟙) → F[-a][1] → 0` with acyclic middle
term, together with `F[-a][1] ≅ F[-(a - 1)]`, and the two out of three property of the vanishing
(`Stacks.EtaleCohomology.CompactSupportTraceVanishes.of_shortExact₁` and `…₃`); the second is the
brutal truncation sequence `0 → σ^{≥a+1}K → K → σ^{≤a}K → 0`, by induction on the length of `K`.
Applied to the pieces of the good open of a curve this gives
`Stacks.EtaleCohomology.CurveTraceCore` for bounded complexes with terms locally constant with
finite projective values (Step 3 of [Stacks, Tag 03UG]: the trace formula for a complex follows
from the trace formula for its terms).

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there.

## Main results

* `Stacks.EtaleCohomology.CompactSupportTraceVanishes.singleDegreePlus_of_zero`
* `Stacks.EtaleCohomology.CompactSupportTraceVanishes.of_bounded`
* `Stacks.EtaleCohomology.compactSupportTraceVanishes_of_curveTraceCore_of_bounded`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

section Standard

attribute [local instance] HasDerivedCategory.standard

variable {Λ : Type} [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] {kbar : Type u}
  [Field kbar] [Algebra k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p]
  {hcard : Fintype.card k = p ^ q} {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {J : CompactificationOf (Over.mk f)}

/-- A sheaf placed in degree `a`, as a bounded below complex. -/
abbrev singleDegreePlus (F : EtaleModules.{u, 0} Λ X) (a : ℤ) :
    CochainComplex.Plus (EtaleModules.{u, 0} Λ X) :=
  ⟨(CochainComplex.singleFunctor _ a).obj F, ⟨a, inferInstance⟩⟩

/-- **Shifting a sheaf by one degree**: the trace vanishes on `F[-a]` exactly when it vanishes on
`F[-(a - 1)]`, through the short exact sequence `0 → F[-a] → cone(𝟙) → F[-a][1] → 0`. -/
theorem CompactSupportTraceVanishes.singleDegreePlus_iff (F : EtaleModules.{u, 0} Λ X) (a : ℤ) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J (singleDegreePlus F a) ↔
      CompactSupportTraceVanishes Λ kbar p q hcard f J (singleDegreePlus F (a - 1)) := by
  let K := (CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ X) a).obj F
  let S := CochainComplex.mappingCone.triangleRotateShortComplex (𝟙 K)
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting (𝟙 K) n).shortExact
  let eSh : S.X₃ ≅ (CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ X) (a - 1)).obj F :=
    ((CochainComplex.singleFunctors (EtaleModules.{u, 0} Λ X)).shiftIso 1 (a - 1) a
      (by omega)).app F
  have h₁ : CochainComplex.plus _ S.X₁ := (show CochainComplex.plus _ K from ⟨a, inferInstance⟩)
  have h₃ : CochainComplex.plus _ S.X₃ :=
    (CochainComplex.plus _).prop_of_iso eSh.symm ⟨a - 1, inferInstance⟩
  have h₂ : CochainComplex.plus _ S.X₂ := CochainComplex.plus_X₂_of_shortExact hS h₁ h₃
  have hv₂ : CompactSupportTraceVanishes Λ kbar p q hcard f J ⟨S.X₂, h₂⟩ :=
    CompactSupportTraceVanishes.of_acyclic _ (Stacks.Injectives.mappingCone_id_acyclic K)
  let e₃ : (⟨S.X₃, h₃⟩ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) ≅
      singleDegreePlus F (a - 1) :=
    ObjectProperty.isoMk _ eSh
  exact ⟨fun hv₁ => (CompactSupportTraceVanishes.of_shortExact₃ hS h₁ h₂ h₃ hv₁ hv₂).of_iso e₃,
    fun hv₃ => CompactSupportTraceVanishes.of_shortExact₁ hS h₁ h₂ h₃ hv₂ (hv₃.of_iso e₃.symm)⟩

/-- **The vanishing in degree `0` gives it in every degree.** -/
theorem CompactSupportTraceVanishes.singleDegreePlus_of_zero (F : EtaleModules.{u, 0} Λ X)
    (h : CompactSupportTraceVanishes Λ kbar p q hcard f J (singleDegreePlus F 0)) (a : ℤ) :
    CompactSupportTraceVanishes Λ kbar p q hcard f J (singleDegreePlus F a) := by
  have iff := CompactSupportTraceVanishes.singleDegreePlus_iff (f := f) (J := J) (kbar := kbar)
    (hcard := hcard) F
  induction a using Int.induction_on with
  | zero => exact h
  | succ i hi =>
    exact (iff _).2 (by simpa using hi)
  | pred i hi => exact (iff _).1 hi

/-- **The vanishing on a bounded complex from the vanishing on its terms.** Let `P` be a property
of sheaves, invariant under isomorphism, such that the trace vanishes on `M` placed in any degree
whenever `P M`. Then it vanishes on every complex concentrated in degrees `[a, b]` whose terms
there satisfy `P`: by induction on `b - a` along the brutal truncation sequences. -/
theorem CompactSupportTraceVanishes.of_bounded (P : EtaleModules.{u, 0} Λ X → Prop)
    (hPiso : ∀ {M M' : EtaleModules.{u, 0} Λ X}, (M ≅ M') → P M → P M')
    (hP : ∀ (M : EtaleModules.{u, 0} Λ X) (n : ℤ), P M →
      CompactSupportTraceVanishes Λ kbar p q hcard f J (singleDegreePlus M n)) :
    ∀ (N : ℕ) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a : ℤ),
      (∀ n, n < a → IsZero (K.obj.X n)) → (∀ n, a + N < n → IsZero (K.obj.X n)) →
      (∀ n, a ≤ n → n ≤ a + N → P (K.obj.X n)) →
      CompactSupportTraceVanishes Λ kbar p q hcard f J K := by
  -- a complex concentrated in one degree
  have hconc : ∀ (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a : ℤ),
      (∀ n, n ≠ a → IsZero (L.obj.X n)) → P (L.obj.X a) →
        CompactSupportTraceVanishes Λ kbar p q hcard f J L := fun L a hL hPa =>
    (hP _ a hPa).of_iso (ObjectProperty.isoMk _
      (CategoryTheory.Functor.isoSingleFunctorObj L.obj a hL)).symm
  intro N
  induction N with
  | zero =>
    intro K a hlo hhi hK
    exact hconc K a (fun n hn => by
      rcases lt_or_gt_of_ne hn with h | h
      · exact hlo n h
      · exact hhi n (by simpa using h)) (hK a le_rfl (by simp))
  | succ N ih =>
    intro K a hlo hhi hK
    let S := StacksDraft.StupidTruncation.stupidTruncGELEShortComplex K.obj (a + 1)
    have hS : S.ShortExact :=
      StacksDraft.StupidTruncation.stupidTruncGELEShortComplex_shortExact K.obj (a + 1)
    have hz₁ : ∀ n, n < a + 1 → IsZero (S.X₁.X n) := fun n hn =>
      CochainComplex.isZero_of_isStrictlyGE
        (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))) (a + 1) n hn
    have hz₃ : ∀ n, a + 1 - 1 < n → IsZero (S.X₃.X n) := fun n hn =>
      CochainComplex.isZero_of_isStrictlyLE
        (K.obj.stupidTrunc (ComplexShape.embeddingUpIntLE (a + 1 - 1))) (a + 1 - 1) n hn
    have eGE : ∀ n, a + 1 ≤ n → (S.X₁.X n ≅ K.obj.X n) := fun n hn =>
      StacksDraft.StupidTruncation.stupidTruncGEXIso K.obj (a + 1) n hn
    have eLE : ∀ n, n ≤ a → (S.X₃.X n ≅ K.obj.X n) := fun n hn =>
      StacksDraft.StupidTruncation.stupidTruncLEXIso K.obj (a + 1 - 1) n (by omega)
    have h₁ : CochainComplex.plus _ S.X₁ :=
      ⟨a + 1, (CochainComplex.isStrictlyGE_iff _ _).2 hz₁⟩
    have h₃ : CochainComplex.plus _ S.X₃ :=
      ⟨a, (CochainComplex.isStrictlyGE_iff _ _).2 fun n hn =>
        IsZero.of_iso (hlo n hn) (eLE n hn.le)⟩
    refine CompactSupportTraceVanishes.of_shortExact₂ hS h₁ K.property h₃ ?_ ?_
    · refine ih ⟨S.X₁, h₁⟩ (a + 1) hz₁ (fun n hn => ?_) (fun n hn hn' => ?_)
      · exact IsZero.of_iso (hhi n (by omega)) (eGE n (by omega))
      · exact hPiso (eGE n hn).symm (hK n (by omega) (by omega))
    · refine hconc ⟨S.X₃, h₃⟩ a (fun n hn => ?_) ?_
      · rcases lt_or_gt_of_ne hn with h | h
        · exact IsZero.of_iso (hlo n h) (eLE n h.le)
        · exact hz₃ n (by omega)
      · exact hPiso (eLE a le_rfl).symm (hK a le_rfl (by omega))

/-- **The core on an open piece, for a bounded complex.** Under the hypotheses of
`Stacks.EtaleCohomology.compactSupportTraceVanishes_of_curveTraceCore`, for a complex `K` on `X`
concentrated in degrees `[a, a + N]` whose terms there are locally constant with finite projective
values on every open subscheme of `Z`, the trace vanishes on `RΓ_c(V_k̄, K|_V)` for every open
subscheme `V ⟶ X` with image `Z` and every compactification of `V`. -/
theorem compactSupportTraceVanishes_of_curveTraceCore_of_bounded [IsAlgClosed kbar] [CharP kbar p]
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType fX] [IsSeparated fX] (Z : X.Opens) [IsIntegral Z] [IsAffine Z]
    (hZdim : topologicalKrullDim Z = 1) [Smooth (Z.ι ≫ fX)]
    (hZrat : IsEmpty (rationalPoints (Z.ι ≫ fX)))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (a : ℤ) (N : ℕ)
    (hlo : ∀ n, n < a → IsZero (K.obj.X n)) (hhi : ∀ n, a + N < n → IsZero (K.obj.X n))
    (hF : ∀ n, a ≤ n → n ≤ a + N → ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e],
      Set.range e.base ⊆ Z → Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        V.smallEtaleTopology ((etaleModuleRestriction.{u, 0} Λ e).obj (K.obj.X n)))
    (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e] (he : Set.range e.base = Z)
    (g : V ⟶ Spec (.of k)) (hg : g = e ≫ fX) (J : CompactificationOf (Over.mk g)) :
    CompactSupportTraceVanishes Λ kbar p q hcard g J
      ((etaleModuleRestriction.{u, 0} Λ e).mapCochainComplexPlus.obj K) := by
  let P : EtaleModules.{u, 0} Λ V → Prop := fun M => ∃ F : EtaleModules.{u, 0} Λ X,
    (∀ (V' : Scheme.{u}) (e' : V' ⟶ X) [IsOpenImmersion e'], Set.range e'.base ⊆ Z →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ V'.smallEtaleTopology
        ((etaleModuleRestriction.{u, 0} Λ e').obj F)) ∧
      Nonempty (M ≅ (etaleModuleRestriction.{u, 0} Λ e).obj F)
  refine CompactSupportTraceVanishes.of_bounded P
    (fun {M M'} φ ⟨F, hF, ⟨ψ⟩⟩ => ⟨F, hF, ⟨φ.symm ≪≫ ψ⟩⟩) (fun M n ⟨F, hFl, ⟨ψ⟩⟩ => ?_) N _ a
    (fun n hn => Functor.map_isZero (etaleModuleRestriction.{u, 0} Λ e) (hlo n hn))
    (fun n hn => Functor.map_isZero (etaleModuleRestriction.{u, 0} Λ e) (hhi n hn))
    (fun n hn hn' => ⟨K.obj.X n, hF n hn hn', ⟨Iso.refl _⟩⟩)
  refine CompactSupportTraceVanishes.singleDegreePlus_of_zero M ?_ n
  exact (compactSupportTraceVanishes_of_curveTraceCore hcore fX Z hZdim hZrat F hFl V e he g hg
    J).of_iso ((singlePlusFunctorCompMapCochainComplexPlusIso
      (etaleModuleRestriction.{u, 0} Λ e)).app F ≪≫
      ObjectProperty.isoMk _ ((CochainComplex.singleFunctor _ 0).mapIso ψ.symm))

end Standard

end Stacks.EtaleCohomology

end
