module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseOpen
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartInputs
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalRigidity

/-!
# Relative dualizing complexes on an affine chart

Let `f : X ⟶ S` be flat and locally of finite presentation, and let `U ⊆ X`, `V ⊆ S` be affine
opens with `U ⊆ f⁻¹(V)`; write `U = Spec(A)` and `V = Spec(R)`. The first step of the proof of
Stacks 0E2X produces a relative dualizing complex `(K_U, ξ_U)` for `U` over `S`: take a relative
dualizing complex `K_A` for `R → A` (Stacks 0E2F), let `K_U` be the complex of quasi-coherent
sheaves it determines (Stacks 06Z0), and argue backwards through the proof of Stacks 0E2U to get
`ξ_U`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isRelativeDualizingComplex_chart`: **the chart step of
  Stacks 0E2X** — for `U ⊆ X`, `V ⊆ S` affine with `U ⊆ f⁻¹(V)` and every diagonal open of
  `U ⟶ S`, a relative dualizing complex for `U` over `S` exists.
* `AlgebraicGeometry.Scheme.Hom.exists_isRelativeDualizingComplex_of_isAffine`: the same for a
  flat, locally finitely presented morphism of affine schemes.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_isIso_diagonalAction`: if
  `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`, some `ξ` defines an isomorphism
  `Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`.

## Implementation notes

The rigidity step is an argument with morphisms only. `Hom(Δ_*𝒪_X, L pr₁^*K|_W)` is free of rank
one over `End(Δ_*𝒪_X) = Γ(X, 𝒪_X)` by the adjunction of Stacks 0A76, and so is
`Hom(Δ_*𝒪_X, R SheafHom(Δ_*𝒪_X, L pr₁^*K|_W))` by Stacks 0A77; the map `ξ ↦` (the map `ξ`
defines) is `Γ(X, 𝒪_X)`-linear with a linear left inverse (the unit law of `Δ_*𝒪_X`), so it is
multiplication by a unit and carries a generator to an isomorphism
(`CategoryTheory.isIso_of_leftInverse_of_generator`).

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model at
which `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex` is stated.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Lemma 47.27.5 (Tag 0E2F)](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
open scoped TensorProduct

universe u

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

/-- **Rigidity of the diagonal condition.** If `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]` and `ξ` is a
free generator of `Hom(Δ_*𝒪_X, L pr₁^*K|_W)` over `End(Δ_*𝒪_X)`, then `ξ` defines an
isomorphism `Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`. -/
theorem DiagonalOpen.isIso_diagonalAction_of_generator {X S : Scheme.{u}} {f : X ⟶ S}
    (D : DiagonalOpen f) (K : DerivedCategory X.Modules)
    (h : Nonempty (D.diagonalExactSupport K ≅ structureSingle X))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hgen : ∀ ζ : D.diagonalObject ⟶ D.derivedPullbackProj K,
      ∃ x : D.diagonalObject ⟶ D.diagonalObject, ζ = x ≫ ξ)
    (huniq : ∀ x y : D.diagonalObject ⟶ D.diagonalObject, x ≫ ξ = y ≫ ξ → x = y) :
    IsIso (D.diagonalAction K ξ) := by
  obtain ⟨τ⟩ := D.nonempty_diagonalObject_iso_derivedSheafHom K h
  exact D.isIso_diagonalAction_of_iso_of_generator K τ ξ hgen huniq

/-- **The generator of the adjunction defines an isomorphism.** If
`e : R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`, then the transpose `ξ` of `e⁻¹` under the adjunction
`Δ_* ⊣ R ℰom(𝒪_X, -)` of Stacks 0A76 defines an isomorphism
`Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`, which is the remark after Stacks 0E2T read
through Stacks 0A77. -/
theorem DiagonalOpen.isIso_diagonalAction_diagonalGenerator {X S : Scheme.{u}} {f : X ⟶ S}
    (D : DiagonalOpen f) (K : DerivedCategory X.Modules)
    (e : D.diagonalExactSupport K ≅ structureSingle X) :
    IsIso (D.diagonalAction K (D.diagonalGenerator K e)) :=
  D.isIso_diagonalAction_of_generator K ⟨e⟩ _ (D.diagonalGenerator_spec K e).1
    (D.diagonalGenerator_spec K e).2

/-- If `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`, some `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` defines an
isomorphism `Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`. -/
theorem DiagonalOpen.exists_isIso_diagonalAction {X S : Scheme.{u}} {f : X ⟶ S}
    (D : DiagonalOpen f) (K : DerivedCategory X.Modules)
    (h : Nonempty (D.diagonalExactSupport K ≅ structureSingle X)) :
    ∃ ξ : D.diagonalObject ⟶ D.derivedPullbackProj K, IsIso (D.diagonalAction K ξ) :=
  let ⟨e⟩ := h
  ⟨D.diagonalGenerator K e, D.isIso_diagonalAction_diagonalGenerator K e⟩

variable {X S : Scheme.{u}}

/-- **Relative dualizing complexes exist for a morphism of affine schemes**, relative to any open
`W ⊆ X ×_S X` through which the diagonal factors as a closed immersion: the first step of the
proof of Stacks 0E2X, with `K = K_A^~` for a relative dualizing complex `K_A` of
`Γ(S, ⊤) → Γ(X, ⊤)` (Stacks 0E2F). -/
theorem exists_isRelativeDualizingComplex_of_isAffine (g : X ⟶ S) [IsAffine X] [IsAffine S]
    [Flat g] [LocallyOfFinitePresentation g] (D : DiagonalOpen g) :
    ∃ (K : DerivedCategory X.Modules) (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K),
      IsRelativeDualizingComplex g
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace g.base)) D K ξ := by
  obtain ⟨K, hK, hE⟩ := exists_isPerfectRelativeTo_diagonalExactSupport_iso g D
  obtain ⟨ξ, hξ⟩ := D.exists_isIso_diagonalAction K hE
  refine ⟨K, ξ, ?_⟩
  have h1 : IsPerfectRelativeTo g
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace g.base)) K := hK
  constructor
  · exact h1
  · exact hξ

/-- **Stacks 0E2X, chart existence.** Let `f : X ⟶ S` be flat and locally of finite
presentation, and let `U ⊆ X`, `V ⊆ S` be affine opens with `U ⊆ f⁻¹(V)`. For every open
`W ⊆ U ×_S U` through which the diagonal of `f|_U : U ⟶ S` factors as a closed immersion, there is
a relative dualizing complex `(K_U, ξ_U)` for `U` over `S` relative to `W`, in the sense of
Stacks 0E2T: `K_U` is the complex attached by Stacks 06Z0 to a relative dualizing complex for
`Γ(S, V) → Γ(X, U)` (Stacks 0E2F), and `ξ_U` comes from arguing backwards through the proof of
Stacks 0E2U. Being `V`-perfect is being `S`-perfect, and `U ×_V U = U ×_S U`.

`S`-perfectness is read at the derived tensor product of Stacks 06YU on the open subspaces of
`(U, f|_U⁻¹𝒪_S)`, as in Stacks 0DI2 and Stacks 0E2U. -/
theorem exists_isRelativeDualizingComplex_chart {Y : Scheme.{u}} (f : Y ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] {U : Y.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) (D' : DiagonalOpen (U.ι ≫ f)) :
    ∃ (K : DerivedCategory (OXMod.{u, u} U.toScheme.toRingedSpace))
      (ξ : D'.diagonalObject ⟶ D'.derivedPullbackProj K),
      IsRelativeDualizingComplex (U.ι ≫ f)
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace (U.ι ≫ f).base)) D' K ξ := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let g := f.resLE V U hUV
  suffices H : ∀ (h : U.toScheme ⟶ S) (hh : g ≫ V.ι = h) [Flat h] [LocallyOfFinitePresentation h]
      (D' : DiagonalOpen h), ∃ (K : DerivedCategory (OXMod.{u, u} U.toScheme.toRingedSpace))
        (ξ : D'.diagonalObject ⟶ D'.derivedPullbackProj K),
        IsRelativeDualizingComplex h
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
            (RingedSpace.inverseImage S.toRingedSpace h.base)) D' K ξ from
    H _ (Scheme.Hom.resLE_comp_ι f hUV) D'
  rintro h rfl _ _ D'
  obtain ⟨K, ξ, hK⟩ := exists_isRelativeDualizingComplex_of_isAffine g D'.ofComp
  exact ⟨K, DiagonalOpen.exists_isRelativeDualizingComplex_of_ofComp _ _ D' K ξ hK
    ((isPerfectRelativeTo_baseOpen_iff g V.ι rfl K).2 hK.isPerfectRelativeTo)⟩

end AlgebraicGeometry.Scheme.Hom

end StandardModel

end
