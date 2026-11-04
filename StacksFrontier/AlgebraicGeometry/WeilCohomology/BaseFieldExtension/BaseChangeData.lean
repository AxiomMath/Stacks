module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Divisor
public import StacksFrontier.AlgebraicGeometry.PicardGroup.PullbackHom

/-!
# Data over `k'` read as data over `k`

Let `k'/k` be a field extension and `𝔇'` data (D0), (D1), (D2') for `(k', F')`. Composing with
the base change `X ↦ X_{k'}` gives data (D0), (D1), (D2') for `(k, F')`:
`X ↦ (H')^*(X_{k'})`, with `c₁(ℒ) = c₁^{H'}(ℒ_{k'})`. This is the auxiliary data through which
the proof of Tag 0FVT compares the cohomological Chern characters of `𝔇` and `𝔇'`: both
`α ↦ ch^{H'}(α_{k'})` and the image of `ch^H` are cohomological Chern characters of it, so they
agree by the uniqueness in Tag 0FIE. If `𝔇'` satisfies (A1)–(A4), so does this data.

## Main definitions

* `Stacks.WeilCohomology.FirstChernClassData.baseChangeData`: the data
  `X ↦ (H')^*(X_{k'})` over `k`.

## Main results

* `Stacks.WeilCohomology.pullbackPicardHom_picardClassOf`: pullback of Picard classes, at the
  spelling of `picardClassOf`.
* `coproductAxiom_baseChangeData`, `pullbackAxiom_baseChangeData`,
  `projectiveBundleAxiom_baseChangeData`, `divisorAxiom_baseChangeData`: (A1)–(A4) for it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

/-- **`φ^*` on Picard classes**, at the spelling `picardClassOf`: it sends the class of `ℒ` to the
class of `φ^*ℒ`. -/
theorem pullbackPicardHom_picardClassOf {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    Stacks.SheafOfModules.pullbackPicardHom f (picardClassOf Y L hL) =
      picardClassOf X ((Scheme.Modules.pullback f).obj L) (isInvertible_pullback_obj f L hL) := by
  unfold picardClassOf
  exact (Stacks.SheafOfModules.pullbackPicardHom_picardClass f L _).trans
    ((Scheme.picardClass_eq_iff _ _ _ _ _).2
      ⟨((Stacks.ProjectiveBundleQuotients.pullbackIso f).app L).symm⟩)

namespace FirstChernClassData

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F' : Type w'} [Field F'] (𝔇' : FirstChernClassData k' F')

/-- **The data `X ↦ (H')^*(X_{k'})` over `k`**: data (D0), (D1), (D2') for `(k', F')` composed
with the base change of smooth projective schemes along `k'/k`, with first Chern class
`c₁(ℒ) = c₁^{H'}(ℒ_{k'})`. -/
abbrev baseChangeData : FirstChernClassData k F' where
  tate := 𝔇'.tate
  finrank_tate := 𝔇'.finrank_tate
  H X := 𝔇'.H ((baseChange k k').obj X)
  grade X := 𝔇'.grade ((baseChange k k').obj X)
  graded_comm X := 𝔇'.graded_comm _
  pull f := 𝔇'.pull ((baseChange k k').map f)
  pull_id X := by rw [CategoryTheory.Functor.map_id]; exact 𝔇'.pull_id _
  pull_comp f g := by rw [CategoryTheory.Functor.map_comp]; exact 𝔇'.pull_comp _ _
  pull_grade f := 𝔇'.pull_grade _
  c₁ X := (𝔇'.c₁ ((baseChange k k').obj X)).comp
    (Stacks.SheafOfModules.pullbackPicardHom (baseChangeProj X))
  c₁_mem X L := 𝔇'.c₁_mem _ _

variable {k}

/-- The first Chern class of the base-changed data: `c₁(ℒ) = c₁^{H'}(ℒ_{k'})`. -/
theorem baseChangeData_c₁_picardClassOf (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L : ((toScheme k).obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible ((toScheme k).obj X).presheaf
      ((toScheme k).obj X).ringCatSheaf.2 L) :
    (𝔇'.baseChangeData k).c₁ X (picardClassOf _ L hL) =
      𝔇'.c₁ ((baseChange k k').obj X)
        (picardClassOf _ ((Scheme.Modules.pullback (baseChangeProj X)).obj L)
          (isInvertible_pullback_obj _ L hL)) :=
  congrArg (𝔇'.c₁ _) (pullbackPicardHom_picardClassOf _ L hL)

/-- The powers of a class of the base-changed data are its powers for `𝔇'`. -/
theorem baseChangeData_twistPow (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : tateTwist F' 𝔇'.tate (𝔇'.H ((baseChange k k').obj X)) 1) (n : ℕ) :
    (𝔇'.baseChangeData k).twistPow X x n = 𝔇'.twistPow ((baseChange k k').obj X) x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show tateCup _ _ _ _ _ _ ((𝔇'.baseChangeData k).twistPow X x n) x =
      tateCup _ _ _ _ _ _ (𝔇'.twistPow _ x n) x
    rw [ih]

/-- The exponential of the base-changed data is the exponential of `𝔇'`. -/
theorem baseChangeData_expTw (X : (SmoothProjectiveScheme k).FullSubcategory)
    (x : tateTwist F' 𝔇'.tate (𝔇'.H ((baseChange k k').obj X)) 1) :
    (𝔇'.baseChangeData k).expTw X x = 𝔇'.expTw ((baseChange k k').obj X) x := by
  funext n
  show ((n.factorial : F')⁻¹) • (𝔇'.baseChangeData k).twistPow X x n = _
  rw [baseChangeData_twistPow]
  rfl

/-- **(A1)** for the base-changed data. -/
theorem coproductAxiom_baseChangeData (h : 𝔇'.CoproductAxiom) :
    (𝔇'.baseChangeData k).CoproductAxiom :=
  ⟨fun _ hX => h.1 _ (isEmpty_baseChange hX),
    fun _ _ _ i j hc => h.2 _ _ _ _ _ (nonempty_isColimit_baseChange i j hc)⟩

/-- **(A2)** for the base-changed data. -/
theorem pullbackAxiom_baseChangeData (h : 𝔇'.PullbackAxiom) :
    (𝔇'.baseChangeData k).PullbackAxiom := by
  intro X Y f L hL
  rw [baseChangeData_c₁_picardClassOf, baseChangeData_c₁_picardClassOf]
  show 𝔇'.pullTw ((baseChange k k').map f) 1 _ = _
  rw [h]
  exact congrArg (𝔇'.c₁ _) (picardClassOf_eq_of_iso _ _ _ _ _
    (FieldExtensionComparison.pullbackBaseChangeIso (k' := k') f L))

/-- **(A3)** for the base-changed data. -/
theorem projectiveBundleAxiom_baseChangeData (hA2 : 𝔇'.PullbackAxiom)
    (hA3 : 𝔇'.ProjectiveBundleAxiom) : (𝔇'.baseChangeData k).ProjectiveBundleAxiom := by
  intro X E r hE
  have := hE
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (baseChangeModule (k' := k') X E) (r + 1)
  apply (𝔇'.baseChangeData k).bijective_bundleFormula_of_bijective_bundleFormulaU
  set e := bundleBaseChangeIso (k' := k') X E r
  set X' := (baseChange k k').obj X
  have hU : (𝔇'.baseChangeData k).bundleClassU X E r =
      𝔇'.κ _ 1 (𝔇'.c₁ _ (picardClassOf _
        ((Scheme.Modules.pullback (baseChangeProj (bundle X E r))).obj (Stacks.Chow.bundleTwist E))
        (isInvertible_pullback_obj _ _ (Stacks.Chow.isInvertible_bundleTwist E)))) :=
    congrArg (𝔇'.κ _ 1) (baseChangeData_c₁_picardClassOf 𝔇' _ _ _)
  have hξ : 𝔇'.pull e.hom ((𝔇'.baseChangeData k).bundleClassU X E r) =
      𝔇'.bundleClassU X' (baseChangeModule X E) r := by
    rw [hU, ← FirstChernClassData.κ_pullTw]
    unfold FirstChernClassData.bundleClassU FirstChernClassData.bundleClass
    congr 1
    exact (hA2 _ _ _).trans
      (congrArg _ (picardClassOf_eq_of_iso _ _ _ _ _ (bundleBaseChangeTwistIso X E r)))
  have hcomp : ∀ a : Fin (r + 1) → 𝔇'.H X',
      𝔇'.pull e.hom ((𝔇'.baseChangeData k).bundleFormulaU X E r a) =
        ∑ i : Fin (r + 1), 𝔇'.bundleClassU X' (baseChangeModule X E) r ^ (i : ℕ) *
          𝔇'.pull (bundleProj X' (baseChangeModule X E) r) (a i) := by
    intro a
    rw [FirstChernClassData.bundleFormulaU_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hξ]
    show _ * 𝔇'.pull e.hom (𝔇'.pull ((baseChange k k').map (bundleProj X E r)) (a i)) = _
    rw [← AlgHom.comp_apply, ← 𝔇'.pull_comp, bundleBaseChangeIso_hom_bundleProj]
  have hb : Bijective (fun a : Fin (r + 1) → 𝔇'.H X' =>
      𝔇'.pull e.hom ((𝔇'.baseChangeData k).bundleFormulaU X E r a)) := by
    simp only [hcomp]
    exact 𝔇'.bijective_bundleFormulaU hA3 X' (baseChangeModule X E) r
  exact (Bijective.of_comp_iff' (𝔇'.bijective_pull_of_iso e) _).mp hb

/-- **(A4)** for the base-changed data. -/
theorem divisorAxiom_baseChangeData (hA4 : 𝔇'.DivisorAxiom) :
    (𝔇'.baseChangeData k).DivisorAxiom := by
  intro X Y i D hD e he a ha
  have := hD
  have hD' : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (baseChangeProj (k' := k') X)) :=
    Stacks.Divisors.isPullbackDefined_of_flat _ D hD
  have : Stacks.Divisors.IsPullbackDefined (baseChangeProj (k' := k') X) D := hD'
  have hc : (𝔇'.baseChangeData k).c₁ X (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.isInvertible_divisorSheaf D)) =
      𝔇'.c₁ _ (picardClassOf _ (Stacks.Divisors.divisorSheaf (D.comap (baseChangeProj X)))
        (Stacks.Divisors.isInvertible_divisorSheaf _)) :=
    (baseChangeData_c₁_picardClassOf 𝔇' _ _ _).trans (congrArg _ (picardClassOf_eq_of_iso _ _ _ _ _
      (Stacks.Divisors.invertibleSheafPullbackIso (baseChangeProj X) D)))
  rw [hc]
  exact hA4 _ _ ((baseChange k k').map i) _ hD' (baseChangeSubschemeIso i D e he)
    (baseChangeSubschemeIso_hom_ι i D e he) a ha

end FirstChernClassData

end Stacks.WeilCohomology
