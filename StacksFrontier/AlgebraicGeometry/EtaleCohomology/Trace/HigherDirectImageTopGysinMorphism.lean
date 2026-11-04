module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFunctoriality
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The Gysin morphism of the top higher direct image along an étale divisor

Let `g : U ⟶ V` be smooth of relative dimension one and affine over a finite field `k`, with `V`
smooth over `k`, and let `i : Z ⟶ U` be a closed immersion with `Z = V(f)` for a function `f` on
`U`, such that `π = g ∘ i : Z ⟶ V` is finite étale and `Z` meets every positive-dimensional
irreducible component of every geometric fibre of `g`. For a lisse `G` on `U` with `R² g_! G`
lisse, cohomological purity along `Z` gives the Gysin morphism
`φ : (π_* i⁻¹ G)(-1) ⟶ R² g_! G`, which is surjective on the rational stalks at the closed points.
For a family `R` in the role of `Rʳ g_!`, this is stated as one proposition: there are a lisse
`A` (the twist `(π_* i⁻¹ G)(-1)`, whose Frobenius traces are `#κ(w) ^ m` times those of
`π_* i⁻¹ G`) and a morphism `A ⟶ R² g_! G` surjective on rational stalks at closed points.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`: the proposition
  that the Gysin morphism of `R² g_!` along an étale divisor exists and is surjective on the
  rational stalks at the closed points.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Gysin morphism of `R² g_!` along an étale divisor, surjective on stalks**: for
`g : U ⟶ V` smooth of relative dimension one and affine over a finite field `k` of characteristic
`p ≠ ℓ`, `V` smooth over `k`, a closed immersion `i : Z ⟶ U` with `Z = V(f)` and `π = g ∘ i` finite
étale, `Z` meeting every irreducible component with two points of every geometric fibre of `g`, and
`G` lisse on `U` with `R² g_! G` lisse, there are a lisse `A` on `V` and `φ : A ⟶ R² g_! G`
surjective on the rational stalks at the closed points, with
`Tr(π_w ^ m | A) = #κ(w) ^ m · Tr(π_w ^ m | π_* i⁻¹ G)` for `m ≥ 1`. -/
def LAdicSheaf.HigherDirectImageTopGysinMorphismInput
    (R : LAdicSheaf.HigherDirectImageFamily B ℓ) : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    Fintype.card k = p ^ n → ℓ ≠ p → ∀ (U V Z : B.Scheme)
    [IsNoetherian U.1] [IsNoetherian V.1] [IsNoetherian Z.1] (g : U ⟶ V)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] [SmoothOfRelativeDimension 1 (B.inclusion.map g)]
    [IsAffineHom (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
    (i : Z ⟶ U) [IsClosedImmersion (B.inclusion.map i)] (π : Z ⟶ V)
    [IsFinite (B.inclusion.map π)] [Etale (B.inclusion.map π)], i ≫ g = π →
    ∀ f : Γ(B.inclusion.obj U, ⊤),
      Set.range (B.inclusion.map i).base = (B.inclusion.obj U).zeroLocus {f} →
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ B.inclusion.obj V),
      ∀ C : Set (Limits.pullback (B.inclusion.map g) w : Scheme.{u}),
        C ∈ irreducibleComponents _ → (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
        (C ∩ (Limits.pullback.fst (B.inclusion.map g) w).base ⁻¹'
          Set.range (B.inclusion.map i).base).Nonempty) →
    ∀ (fV : V.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fV] [Smooth fV]
      (G : LAdicSheaf.{u, u + 1} B U ℓ), G.IsLisse → (R g jg G 2).IsLisse →
    ∃ (A : LAdicSheaf.{u, u + 1} B V ℓ) (φ : A ⟶ R g jg G 2), A.IsLisse ∧
      (∀ w : closedPoints V.1,
        Function.Surjective (LAdicSheaf.rationalStalkMap φ (geometricPointAt V.1 w.1))) ∧
      ∀ (hF : ∀ m, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (m + 1)))
          (SmallEtale.topology B Z.1 Z.property) ((LAdicSheaf.inverseImage i G).level m))
        (w : closedPoints V.1) (m : ℕ), 1 ≤ m →
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V ℓ A w.1
            (finite_residueField fV w.1 w.2) ^ m) =
          (Nat.card (V.1.residueField w.1) : ℚ_[ℓ]) ^ m *
            LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B V ℓ
              (SmallEtale.LAdicSheaf.directImage π (LAdicSheaf.inverseImage i G) hF) w.1
              (finite_residueField fV w.1 w.2) ^ m)

end Stacks.EtaleCohomology

end
