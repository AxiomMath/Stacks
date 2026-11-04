module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedClassifyingMap
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertBoundedImage
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertSpaceNoetherian

/-!
# Stacks 0E96, with only the universal family of `Hilb^P_{ℙⁿ_ℤ/ℤ}` left

**Stacks 0E96.** Let `n ≥ 1`, let `P` be a numerical polynomial and let `T ⊆ |𝒫olarized|` be a
set of points each of which is represented, over some field `k`, by a polarized proper scheme
`(X, ℒ)` such that (1) the Hilbert polynomial of `ℒ` on `X` is `P`, and (2) there is a closed
immersion `i : X → ℙⁿ_k` with `i^*𝒪(1) ≅ ℒ`. Then `T` is a Noetherian topological space.

Three of the four results the source's proof cites are discharged here, leaving one:

* the algebraicity of `𝒫olarized` (Quot, Theorem 0D4X) is **not needed**
  (`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertBoundedImage.lean`);
* the properness of `H = Hilb^{P, 𝒪(1)}_{ℙⁿ_ℤ/ℤ}` over `Spec(ℤ)` (Stacks 0DPH) is **available**,
  in the only form the proof uses it, from Stacks 0DPA at `r = 1`
  (`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertSpaceNoetherian.lean`);
* the passage from a family over `H` to the 1-morphism `H → 𝒫olarized` it classifies
  (Stacks 0E94) is **the 2-Yoneda lemma**, Stacks 004B
  (`StacksFrontier/AlgebraicGeometry/Quot/PolarizedClassifyingMap.lean`);
* **what is left is the universal family itself** (Stacks 0D3W): the polarized family
  `(Z, 𝒪(1)|_Z)` over `H` attached to the universal element of `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`, together with
  the statement that every polarized scheme over a field satisfying conditions (1) and (2) admits
  a morphism of polarized families to it. That is the single hypothesis of
  `AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily`.

**Which tag is which.** In the source's proof Stacks 0D3W (Quot, Lemma 99.9.3) is the step that
turns the identity of `H` into the closed subspace `Z ⊆ ℙⁿ_H`, and Stacks 0E94 (Quot, Lemma
99.14.4) is the step that turns the pair `(Z → H, 𝒪(1)|_Z)` into the 1-morphism
`H → 𝒫olarized`. Only the first is still owed here. The second is not: it is the 2-Yoneda route
above, and Stacks 0E94 is in any case already registered, on
`AlgebraicGeometry.PolarizedOverSpace.polarizedBaseChange_isEquivalence`
(`StacksFrontier/AlgebraicGeometry/Quot/PolarizedOverSpaceEquivalence.lean`). Stacks 0D3W is
registered too, on `AlgebraicGeometry.Space.morEquivSpaceHilbertFamilyOfScheme`
(`StacksFrontier/AlgebraicGeometry/Quot/HilbertFunctorPoints.lean`), but at the spelling of the
Hilbert presheaf `Hilb_{X/Y}` of a morphism of algebraic spaces with `F = 𝒪_X`, which is not yet
identified with `AlgebraicGeometry.ProjectiveQuot.hilbertFunctor n 1 P` — the functor on
submodules `K ⊆ 𝒪^{⊕ 1}` that `huniv`'s `U₀` represents. Neither registration therefore
discharges `huniv` as it stands.

## Main results

* `AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily`:
  **Stacks 0E96 from the universal family of `Hilb^P_{ℙⁿ_ℤ/ℤ}`.**

## Implementation notes

No tag attribute is placed here: `huniv` stands for Stacks 0D3W, which the Stacks project
proves, so a registration on this statement would be conditional. It is discharged, and Stacks
0E96 registered on the resulting hypothesis-free statement, in
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertBoundedUnconditional.lean`.

**What discharging `huniv` requires.** The universal element of `Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` over `H` is a
submodule `K ⊆ 𝒪` on `ℙⁿ_H` whose quotient is flat over `H` and of finite presentation
(`AlgebraicGeometry.ProjectiveQuot.hilbertFamilies`), not a closed subscheme. Reading `K` as a
quasi-coherent sheaf of ideals of `𝒪_{ℙⁿ_H}` and feeding it to Stacks 01QQ is done in
`StacksFrontier/AlgebraicGeometry/Quot/ProjectiveQuotIdealSheaf.lean`
(`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_ker_eq_idealOfFamily_of_mem`), and
the resulting `Z → H` is flat and of finite presentation — the flatness-and-finite-presentation
half of the dictionary of Stacks 0D00, read on `ℙⁿ_H` — in
`StacksFrontier/AlgebraicGeometry/Quot/ProjectiveQuotClosedSubschemeFlat.lean`
(`AlgebraicGeometry.ProjectiveQuot.exists_isClosedImmersion_flat_finitePresentation_of_mem`). So
the polarized family `x₀` itself exists:
`AlgebraicGeometry.exists_polarizedFamily_base_eq_universalHilbertFamily` of
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertUniversalFamily.lean`. The rest of `huniv`
is its mapping property, which needs two further steps: that the fibrewise Hilbert polynomial of
the quotient is the Hilbert polynomial of `𝒪(1)|_Z` on the fibres of `Z → H`, and that the
construction commutes with base change, which is what makes a field-valued point of `H` with
Hilbert polynomial `P` a family mapping to the universal one. Those are
`AlgebraicGeometry.hilbertFamilies_of_polarizedHilbertFunction` and
`AlgebraicGeometry.ProjectiveQuot.isPullback_subschemeOfFamily_baseChange`, and
`AlgebraicGeometry.exists_universalPolarizedFamily_hilbertFunctor` assembles `huniv` from
them.

## References

* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0E94](https://stacks.math.columbia.edu/tag/0E94)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {T : C}

/-- **A morphism lies over a morphism of the terminal slice as soon as it lies over the underlying
morphism.** This is the object half of
`CategoryTheory.Functor.IsFiberedInGroupoids.sliceAtTerminal`, as a statement about a single
morphism: the two structure morphisms to the terminal object agree, so the square of a lift in the
slice is the square of its underlying lift. -/
theorem isHomLift_sliceAtTerminal {p : 𝒮 ⥤ C} (hT : IsTerminal T) {x y : 𝒮} {V W : Over T}
    (v : V ⟶ W) (φ : x ⟶ y) (hv : p.IsHomLift v.left φ) :
    (p.sliceAtTerminal hT).IsHomLift v φ := by
  have := hv
  refine IsHomLift.of_fac' _ v φ
    (p.sliceAtTerminal_obj_eq hT (IsHomLift.domain_eq p v.left φ))
    (p.sliceAtTerminal_obj_eq hT (IsHomLift.codomain_eq p v.left φ)) ?_
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
    sliceAtTerminal_map_left]
  exact IsHomLift.fac' p v.left φ

/-- **A morphism lies over its own image, read between any two objects equal to the images of its
source and target.** The two `eqToHom`s are the transports along those equalities; after
substituting them away this is the defining instance
`CategoryTheory.Functor.IsHomLift.map`. -/
theorem isHomLift_eqToHom_map_eqToHom {p : 𝒮 ⥤ C} {x y : 𝒮} (φ : x ⟶ y) {R S : C}
    (hR : p.obj x = R) (hS : p.obj y = S) :
    p.IsHomLift (eqToHom hR.symm ≫ p.map φ ≫ eqToHom hS) φ := by
  subst hR
  subst hS
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **Stacks 0E96, from the universal family of `Hilb^P_{ℙⁿ_ℤ/ℤ}`.** Let `n ∈ ℕ`, let `P ∈ ℚ[t]`
and let `T ⊆ |𝒫olarized|` be a set of points each represented over a field by a polarized proper
scheme `(X, ℒ)` satisfying conditions (1) and (2) of Stacks 0E96
(`AlgebraicGeometry.IsHilbertPolarizedOver`). Then `T` is a Noetherian topological space.

The single hypothesis `huniv` is the universal family of `H = Hilb^P_{ℙⁿ_ℤ/ℤ}` (Stacks 0D3W): for
an object `U₀` of the site whose represented presheaf is the Hilbert functor, a polarized family
`x₀` over `U₀` such that every closed subscheme `Z ⊆ ℙⁿ_k`, flat and of finite presentation over a
field `k` and with `𝒪(1)|_Z` of Hilbert polynomial `P`, admits a morphism of polarized families
`(Z, 𝒪(1)|_Z) ⟶ x₀`.

The rest of the source's proof is discharged: such a `U₀` exists and its space of points is a
Noetherian topological space
(`AlgebraicGeometry.exists_noetherianSpace_points_yoneda_iso_hilbertFunctor`, from Stacks 0DPA at
`r = 1`); `x₀` names a 1-morphism `𝒮_{U₀} → 𝒫olarized` by 2-Yoneda
(`AlgebraicGeometry.polarizedClassifyingMap`), whose value at a field-valued point of `U₀` maps to
every base change of `x₀` along that point
(`AlgebraicGeometry.nonempty_hom_polarizedClassifyingMap_obj`); and the conclusion follows with no
local Noetherianity of `|𝒫olarized|`, hence with no algebraicity of `𝒫olarized`
(`AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_noetherianSpace_points`). The
source's `n ≥ 1` and the numericality of `P` are not needed. -/
theorem noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily
    (hT : IsTerminal (B.obj hS)) (n : ℕ) (P : Polynomial ℚ)
    (huniv : ∀ U₀ : BigFppfOver B S hS,
      (yoneda.obj U₀ ⋙ uliftFunctor.{u + 1} ≅
        (BigFppfOver.toScheme B S hS).op ⋙ ProjectiveQuot.hilbertFunctor.{u} n 1 P) →
      ∃ x₀ : PolarizedFamily B, ∃ _ : x₀.base = U₀.left,
        ∀ (U : B.Schemes) (k : Type u) [Field k] (e : B.inclusion.obj U ≅ Spec (.of k))
          {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U))
          [IsClosedImmersion i]
          (hfl : Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
          (hfp : FinitePresentation
            (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))),
          (∀ d : ℤ, (polarizedHilbertFunction (hilbertPolarizedFamily n U i hfl hfp) k e d : ℚ) =
            P.eval (d : ℚ)) →
          Nonempty (hilbertPolarizedFamily n U i hfl hfp ⟶ x₀))
    (T : Set (Stack.points B S hS (polarizedStackUnconditional B hS hT).val
      (polarizedStackUnconditional B hS hT).property))
    (hTP : ∀ ξ ∈ T, ∃ p, Stack.pointClass B S hS _ _ p = ξ ∧
      IsHilbertPolarizedPoint B hS hT n P p) :
    letI := Stack.pointTopology B S hS (polarizedStackUnconditional B hS hT)
    NoetherianSpace T := by
  obtain ⟨U₀, hnoeth, ⟨eH⟩⟩ :=
    exists_noetherianSpace_points_yoneda_iso_hilbertFunctor B hS hT n P
  obtain ⟨x₀, hx₀, hmod⟩ := huniv U₀ eH
  refine noetherianSpace_of_isHilbertPolarizedPoint_of_noetherianSpace_points B hS hT n P
    (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀) hnoeth
    (polarizedClassifyingMap B hS hT U₀ x₀ hx₀) ?_ T hTP
  intro U k _ e Z i _ hfl hfp hP
  obtain ⟨ψ⟩ := hmod U k e i hfl hfp hP
  have hk : B.Contains (Spec (CommRingCat.of k)) := by
    have hU : (B.inclusion.obj U).size < B.cutoff := U.property
    rwa [Scheme.size_congr e] at hU
  let f : B.obj hk ⟶ U := ObjectProperty.homMk e.inv
  obtain ⟨w, χ, hχ⟩ := polarizedProjection_existsLift_unconditional f
    (hilbertPolarizedFamily n U i hfl hfp) rfl
  have := hχ
  have hw : (polarizedProjection B).obj w = B.obj hk :=
    IsHomLift.domain_eq (polarizedProjection B) f χ
  refine ⟨{ carrier := k
            contained := hk
            toBase := e.inv ≫ B.inclusion.map (hT.from U)
            value := Over.homMk
              (eqToHom hw.symm ≫ (polarizedProjection B).map (χ ≫ ψ) ≫ eqToHom hx₀)
              (hT.hom_ext _ _) }, ?_⟩
  exact (nonempty_hom_polarizedClassifyingMap_obj B hS hT U₀ x₀ hx₀ _ (χ ≫ ψ)
    (Functor.isHomLift_sliceAtTerminal hT _ (χ ≫ ψ)
      (Functor.isHomLift_eqToHom_map_eqToHom (χ ≫ ψ) hw hx₀))).map fun a => a ≫ χ

end AlgebraicGeometry

end
