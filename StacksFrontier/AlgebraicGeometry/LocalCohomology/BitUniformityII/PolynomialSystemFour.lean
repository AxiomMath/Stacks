module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PowerSeriesConstantCoeffQuotients
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictSystemFour
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp
public import StacksFrontier.Homology.Tor.IndependenceFlatModule
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange

/-!
# The standard example of system (4) in Stacks 0GA5

Let `A` be a ring, `g₁, …, g_r ∈ A`, and `M` a complex of `A`-modules.  The standard example of
the system (4) of [Stacks, Tag 0GA5] takes `P = ℤ[x₁, …, x_r]`, the map `P → A` with
`xᵢ ↦ gᵢ`, and `J = (x₁, …, x_r)`.  The source asserts that then
`M ⊗ᴸ_P P/Jⁿ = M ⊗ᴸ_{A[x]} A[x]/(x)ⁿ`, and that this reduces the example to the cases discussed
before, so that the system (4) is strictly pro-isomorphic to the system (2).

The coefficient ring is an arbitrary commutative ring `R₀` with `A` an `R₀`-algebra; the source's
case is `R₀ = ℤ` (or `ULift ℤ`, when the rings live in a universe other than `0`).

## Main definitions

* `Stacks.LocalCohomology.UniformityII.changeOfRingsPolyIso`: `M ⊗ᴸ_{R₀[x]} -` is derived base
  change to `A[x]` followed by `M ⊗ᴸ_{A[x]} -`.
* `Stacks.LocalCohomology.UniformityII.derivedBaseChangeQuotientSystemIso`:
  `A[x] ⊗ᴸ_{R₀[x]} R₀[x]/Jⁿ = A[x]/(x)ⁿ`, because `R₀[x]` and the quotients `R₀[x]/Jⁿ` are flat
  over `R₀` and `A[x] = A ⊗_{R₀} R₀[x]`.
* `Stacks.LocalCohomology.UniformityII.polynomialSystemFourIso`: **`M ⊗ᴸ_P P/Jⁿ ≅
  M ⊗ᴸ_{A[x]} A[x]/(x)ⁿ`**, as inverse systems in `D(A)`.

## Main results

* `Stacks.LocalCohomology.UniformityII.nonempty_proIso_polynomialSystemFour_systemTwo`: **for
  `A` Noetherian, the system (4) of the standard example is strictly pro-isomorphic to the
  system (2)**, since `A[x] → A` is surjective, hence finite.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.InverseSequence

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace Stacks.LocalCohomology.UniformityII

universe u

variable (R₀ : Type u) [CommRing R₀] {A : Type u} [CommRing A] [Algebra R₀ A] {r : ℕ}
  (g : Fin r → A)

/-- The quotient `R₀[x]/Jⁿ`, viewed as an `R₀`-module by restriction of scalars, is flat. -/
theorem flat_restrict_quotient (n : ℕ) :
    Module.Flat R₀ ((ModuleCat.restrictScalars (algebraMap R₀ (MvPolynomial (Fin r) R₀))).obj
      (ModuleCat.of (MvPolynomial (Fin r) R₀)
        (MvPolynomial (Fin r) R₀ ⧸ MvPolynomial.idealOfVars (Fin r) R₀ ^ n))) := by
  have := Stacks.MvPowerSeries.flat_quotient_pow_idealOfVars (Fin r) R₀ n
  let e : (MvPolynomial (Fin r) R₀ ⧸ MvPolynomial.idealOfVars (Fin r) R₀ ^ n) ≃ₗ[R₀]
      ((ModuleCat.restrictScalars (algebraMap R₀ (MvPolynomial (Fin r) R₀))).obj
      (ModuleCat.of (MvPolynomial (Fin r) R₀)
        (MvPolynomial (Fin r) R₀ ⧸ MvPolynomial.idealOfVars (Fin r) R₀ ^ n))) :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => (algebraMap_smul (MvPolynomial (Fin r) R₀) c x).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Flat.of_linearEquiv e.symm

/-- The counit of derived extension of scalars along `R₀[x] → A[x]` is invertible at
`(R₀[x]/Jⁿ)[0]`. -/
theorem isIso_comparison_quotient (n : ℕ) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
      (algebraMap (MvPolynomial (Fin r) R₀) (MvPolynomial (Fin r) A))).comparison.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin r) R₀)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin r) R₀)
          (MvPolynomial (Fin r) R₀ ⧸ MvPolynomial.idealOfVars (Fin r) R₀ ^ n)))) :=
  RingTheory.TorIndependence.isIso_comparison_single_of_flat (B := A)
    RingTheory.TorIndependence.torIndependent_of_flat_left _ (flat_restrict_quotient R₀ n)

/-- `R₀[x] → A`, `xᵢ ↦ gᵢ`. -/
noncomputable abbrev polyEval : MvPolynomial (Fin r) R₀ →+* A :=
  (MvPolynomial.aeval g : MvPolynomial (Fin r) R₀ →ₐ[R₀] A).toRingHom

/-- `A[x] → A`, `xᵢ ↦ gᵢ`. -/
noncomputable abbrev polyEvalBase : MvPolynomial (Fin r) A →+* A :=
  (MvPolynomial.aeval g : MvPolynomial (Fin r) A →ₐ[A] A).toRingHom

/-- `R₀[x] → A[x]`, the coefficientwise map. -/
noncomputable abbrev polyMap : MvPolynomial (Fin r) R₀ →+* MvPolynomial (Fin r) A :=
  algebraMap (MvPolynomial (Fin r) R₀) (MvPolynomial (Fin r) A)

/-- Evaluating `A[x] → A` at `g` after the coefficientwise map `R₀[x] → A[x]` is evaluating
`R₀[x] → A` at `g`. -/
theorem polyEvalBase_comp_polyMap :
    (polyEvalBase g).comp (polyMap R₀ (A := A) (r := r)) = polyEval R₀ g :=
  MvPolynomial.ringHom_ext
    (fun c => by
      change MvPolynomial.aeval g (MvPolynomial.map (algebraMap R₀ A) (MvPolynomial.C c)) =
        MvPolynomial.aeval g (MvPolynomial.C c)
      simp)
    fun i => by
      change MvPolynomial.aeval g (MvPolynomial.map (algebraMap R₀ A) (MvPolynomial.X i)) =
        MvPolynomial.aeval g (MvPolynomial.X i)
      simp

variable (M : CochainComplex (ModuleCat.{u} A) ℤ)

/-- The derived tensor products over `A` with `M` of the change-of-rings constructions along
two ring maps agree: both are total left derived functors of `- ⊗_A M`. -/
noncomputable def changeOfRingsTensorIso {P P' : Type u} [CommRing P] [CommRing P'] (f : P →+* A)
    (f' : P' →+* A) :
    (changeOfRings f M).G ≅ (changeOfRings f' M).G := by
  haveI := (changeOfRings f M).isLeftDerivedG
  haveI := (changeOfRings f' M).isLeftDerivedG
  exact Functor.leftDerivedUnique _ _ (changeOfRings f M).alphaG (changeOfRings f' M).alphaG
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))

/-- **The derived change of rings along a composite.**  For ring maps `a : R → S`, `b : S → A`
and `c = b ∘ a`, the derived change of rings `M ⊗ᴸ_R -` along `c` is derived extension of scalars
along `a` followed by the derived change of rings `M ⊗ᴸ_S -` along `b`. -/
noncomputable def changeOfRingsCompIso {R S : Type u} [CommRing R] [CommRing S] (a : R →+* S)
    (b : S →+* A) (c : R →+* A) (h : b.comp a = c) :
    (changeOfRings c M).F ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars a).functor ⋙
        (changeOfRings b M).F := by
  let T₀ := changeOfRings c M
  let T₁ := changeOfRings b M
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars a
  let D₀ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars c
  haveI := D.isLeftDerived
  haveI := D₀.isLeftDerived
  haveI := T₀.isLeftDerivedB
  haveI := T₁.isLeftDerivedB
  haveI := T₀.isLeftDerivedG
  haveI := T₁.isLeftDerivedG
  let c₀ : DerivedCategory.Q ⋙ D₀.functor ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} c ⋙ DerivedCategory.Q :=
    D₀.comparison
  haveI : D₀.functor.IsLeftDerivedFunctor c₀
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
    D₀.isLeftDerived
  let eB₀ : T₀.B ≅ D₀.functor := Functor.leftDerivedUnique _ _ T₀.alphaB c₀
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
  let b₁ : DerivedCategory.Q ⋙ T₁.B ⟶
      CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral b :=
    T₁.alphaB
  haveI : T₁.B.IsLeftDerivedFunctor b₁
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)) :=
    T₁.isLeftDerivedB
  let eB : D.functor ⋙ T₁.B ≅ D₀.functor :=
    StacksDraft.DerivedExtensionScalarsModelComp.compModelIso _ _ D.functor D.comparison T₁.B
      b₁ _ h
  let eG : T₀.G ≅ T₁.G := changeOfRingsTensorIso M _ _
  exact T₀.changeOfRings ≪≫ Functor.isoWhiskerRight (eB₀ ≪≫ eB.symm) T₀.G ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D.functor (Functor.isoWhiskerLeft T₁.B eG ≪≫ T₁.changeOfRings.symm)

/-- The derived change of rings along `R₀[x] → A` is derived extension of scalars along
`R₀[x] → A[x]` followed by the derived change of rings along `A[x] → A`. -/
noncomputable def changeOfRingsPolyIso :
    (changeOfRings (polyEval R₀ g) M).F ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
        (polyMap R₀ (A := A) (r := r))).functor ⋙ (changeOfRings (polyEvalBase g) M).F :=
  changeOfRingsCompIso M _ _ _ (polyEvalBase_comp_polyMap R₀ g)

/-- The image of the ideal `(x₁, …, x_r)` under a ring map is spanned by the images of the `xᵢ`. -/
private theorem map_idealOfVars_eq_span {S T : Type u} [CommRing S] [CommRing T]
    (f : MvPolynomial (Fin r) S →+* T) :
    (MvPolynomial.idealOfVars (Fin r) S).map f = Ideal.span (Set.range fun i => f (.X i)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  rfl

/-- The ideal `(x₁, …, x_r)` of `R₀[x]` maps to the ideal `(x₁, …, x_r)` of `A[x]`. -/
theorem idealOfVars_map_polyMap :
    (MvPolynomial.idealOfVars (Fin r) R₀).map (polyMap R₀ (A := A) (r := r)) =
      MvPolynomial.idealOfVars (Fin r) A := by
  rw [map_idealOfVars_eq_span, MvPolynomial.idealOfVars]
  simp

/-- The ideal `(x₁, …, x_r)` of `A[x]` maps to `(g₁, …, g_r)` under `xᵢ ↦ gᵢ`. -/
theorem idealOfVars_map_polyEvalBase :
    (MvPolynomial.idealOfVars (Fin r) A).map (polyEvalBase g) = Ideal.span (Set.range g) := by
  rw [map_idealOfVars_eq_span]
  simp

/-- `A[x] → A`, `xᵢ ↦ gᵢ`, is surjective, hence finite. -/
theorem polyEvalBase_finite : (polyEvalBase g).Finite :=
  RingHom.Finite.of_surjective _ fun a => ⟨MvPolynomial.C a, by simp⟩

/-- The derived base change of the system of quotients `R₀[x]/Jⁿ⁺¹` along `R₀[x] → A[x]` is the
system of quotients `A[x]/(x)ⁿ⁺¹`. -/
noncomputable def derivedBaseChangeQuotientSystemIso :
    quotientSingleSystem (MvPolynomial.idealOfVars (Fin r) R₀) ⋙ DerivedCategory.Q ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (polyMap R₀ (A := A) (r := r))).functor ≅
      quotientSingleSystem (MvPolynomial.idealOfVars (Fin r) A) ⋙ DerivedCategory.Q := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
    (polyMap R₀ (A := A) (r := r))
  let S₀ := quotientSingleSystem (MvPolynomial.idealOfVars (Fin r) R₀)
  haveI : ∀ n, IsIso ((Functor.whiskerLeft S₀ D.comparison).app n) := fun n =>
    isIso_comparison_quotient R₀ (A := A) (r := r) (n.unop + 1)
  haveI : IsIso (Functor.whiskerLeft S₀ D.comparison) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft S₀ D.comparison) ≪≫
    Functor.isoWhiskerRight (extendQuotientSingleSystemIso (polyMap R₀ (A := A) (r := r))
      (MvPolynomial.idealOfVars (Fin r) R₀) (MvPolynomial.idealOfVars (Fin r) A)
      (idealOfVars_map_polyMap R₀).symm) DerivedCategory.Q

/-- **`M ⊗ᴸ_P P/Jⁿ = M ⊗ᴸ_{A[x]} A[x]/(x)ⁿ`.**  Let `P = R₀[x₁, …, x_r]` (the source takes
`R₀ = ℤ`; at a universe `u` other than `0` one takes `R₀ = ULift ℤ`), let `P → A` send `xᵢ` to
`gᵢ`, and `J = (x₁, …, x_r)`.  Then the system (4) `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` is isomorphic, as an
inverse system in `D(A)`, to the system `n ↦ M ⊗ᴸ_{A[x]} A[x]/(x)ⁿ⁺¹`, i.e. to the system (4)
for `A[x] → A`, `xᵢ ↦ gᵢ`. -/
@[stacks 0GA5 "the standard example: `M ⊗ᴸ_P P/Jⁿ = M ⊗ᴸ_{A[x]} A[x]/(x)ⁿ` for \
`P = ℤ[x₁, …, x_r]`"]
noncomputable def polynomialSystemFourIso :
    systemFour (polyEval R₀ g) M (MvPolynomial.idealOfVars (Fin r) R₀) ≅
      systemFour (polyEvalBase g) M (MvPolynomial.idealOfVars (Fin r) A) :=
  Functor.isoWhiskerLeft
      (quotientSingleSystem (MvPolynomial.idealOfVars (Fin r) R₀) ⋙ DerivedCategory.Q)
      (changeOfRingsPolyIso R₀ g M) ≪≫
    Functor.isoWhiskerRight (derivedBaseChangeQuotientSystemIso R₀ (A := A) (r := r))
      (changeOfRings (polyEvalBase g) M).F

/-- In the situation of `polynomialSystemFourIso`, with `A` Noetherian and `I = (g₁, …, g_r)`,
the system (4) `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` for `P = R₀[x₁, …, x_r]` is strictly pro-isomorphic to the
system (2) `n ↦ M ⊗ᴸ_A A/Iⁿ⁺¹`. -/
@[stacks 0GA5 "the standard example `P = ℤ[x₁, …, x_r]`: the system (4) is strictly \
pro-isomorphic to the system (2), by reduction to the finite map `A[x] → A`"]
theorem nonempty_proIso_polynomialSystemFour_systemTwo [IsNoetherianRing A] :
    Nonempty (proObj (systemFour (polyEval R₀ g) M (MvPolynomial.idealOfVars (Fin r) R₀)) ≅
      proObj (systemTwo (polyEval R₀ g) M (Ideal.span (Set.range g)))) := by
  let e₂ : systemTwo (polyEvalBase g) M (Ideal.span (Set.range g)) ≅
      systemTwo (polyEval R₀ g) M (Ideal.span (Set.range g)) :=
    Functor.isoWhiskerLeft (quotientSingleSystem (Ideal.span (Set.range g)) ⋙ DerivedCategory.Q)
      (changeOfRingsTensorIso M (polyEvalBase g) (polyEval R₀ g))
  have h₁ := isIso_proHom_of_hasUniformInverses _ (HasUniformInverses.of_isIso
    (polynomialSystemFourIso R₀ g M).hom)
  have h₂ := isIso_proHom_systemFourToTwo (polyEvalBase g) M (polyEvalBase_finite g)
    (MvPolynomial.idealOfVars (Fin r) A) (Ideal.span (Set.range g))
    (idealOfVars_map_polyEvalBase g).symm
  have h₃ := isIso_proHom_of_hasUniformInverses _ (HasUniformInverses.of_isIso e₂.hom)
  exact ⟨@asIso _ _ _ _ _ h₁ ≪≫ @asIso _ _ _ _ _ h₂ ≪≫ @asIso _ _ _ _ _ h₃⟩

end Stacks.LocalCohomology.UniformityII

end
