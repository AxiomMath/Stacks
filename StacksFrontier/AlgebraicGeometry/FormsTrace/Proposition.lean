module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.DegreeZero
public import StacksFrontier.AlgebraicGeometry.FormsTrace.Main
public import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeTrace
import StacksCore.Tactic.StacksAttribute

/-!
# Trace maps on de Rham complexes: Stacks, Proposition 0FLC

Let `f : Y ⟶ X` be a finite syntomic morphism of schemes. The maps
`Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` of Lemma 0FLB (`AlgebraicGeometry.Scheme.Hom.formsTrace`)
define a map of complexes `f_*Ω^•_{Y/ℤ} ⟶ Ω^•_{X/ℤ}`, with the properties

1. in degree `0` it is `Trace_f : f_*𝒪_Y ⟶ 𝒪_X`,
2. `Θ(ω ∧ η) = ω ∧ Θ(η)` for `ω` in `Ω^•_{X/ℤ}` and `η` in `f_*Ω^•_{Y/ℤ}`,
3. if `f` is a morphism over a base scheme `S`, then `Θ` induces a map of complexes
   `f_*Ω^•_{Y/S} ⟶ Ω^•_{X/S}`.

The de Rham differentials are those of `AlgebraicGeometry.Scheme.Hom.deRhamComplex`, and a map
of complexes is read on local sections: `Θ^{p+1}(dη) = d Θ^p(η)` for every open `U` of `X` and
every `η ∈ Γ(Ω^p_{Y/ℤ}, f⁻¹U)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formsTrace_isComplexMap`: **Stacks, Proposition 0FLC.**

## References

* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f)

/-- The maps `Θ^p_{Y/X}` are those of Lemma 0FLB. -/
theorem formsTrace_eq_formsTraceRule (p : ℕ) : f.formsTrace hf p = formsTraceRule f hf p :=
  rfl

/-- **Stacks, Proposition 0FLC.** Let `f : Y ⟶ X` be a finite syntomic morphism of schemes. The
maps `Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` of Lemma 0FLB (`formsTrace`, the rule
`formsTraceRule` of `existsUnique_formsTraceRule`) define a map of complexes
`f_*Ω^•_{Y/ℤ} ⟶ Ω^•_{X/ℤ}`: on every open `U` of `X`, `Θ^{p+1}(dη) = d Θ^p(η)`. Moreover:

1. in degree `0` it is `Trace_f : f_*𝒪_Y ⟶ 𝒪_X`, through `Ω^0 ≅ 𝒪` on both sides;
2. `Θ(ω ∧ η) = ω ∧ Θ(η)` for local sections `ω` of `Ω^q_{X/ℤ}` and `η` of `f_*Ω^p_{Y/ℤ}`
   (`ω` acting on `f_*Ω^•_{Y/ℤ}` through `f^*`);
3. if `f` is a morphism over a base scheme `S`, i.e. for every `g : X ⟶ S`, the maps `Θ^p_{Y/X}`
   induce maps `f_*Ω^p_{Y/S} ⟶ Ω^p_{X/S}` (compatible with `Θ^p_{Y/X}` through the canonical
   surjections `Ω^p_{·/ℤ} → Ω^p_{·/S}`) forming a map of complexes. -/
@[stacks 0FLC]
theorem formsTrace_isComplexMap :
    haveI := AlgebraicGeometry.flat hf
    haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
    -- a map of complexes
    (∀ (p : ℕ) (U : X.Opens) (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)),
      (f.formsTrace hf (p + 1)).app U
          ((Y.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ U)) η) =
        (X.toSpecZ.deRhamComplex.d p (p + 1)).val.app (op U) ((f.formsTrace hf p).app U η)) ∧
    -- (1) degree zero is the trace
    f.formsTrace hf 0 ≫ (relativeDifferentialFormsZeroIso X.toSpecZ).hom =
      (Scheme.Modules.pushforward f).map (relativeDifferentialFormsZeroIso Y.toSpecZ).hom ≫
        f.finiteTrace ∧
    -- (2) linearity over the forms of `X`
    (∀ (q p : ℕ) (U : X.Opens) (ω : Γ(absoluteDifferentialForms X q, U))
      (η : Γ(absoluteDifferentialForms Y p, f ⁻¹ᵁ U)),
      (f.formsTrace hf (q + p)).app U
          ((eqToHom (congrArg (absoluteDifferentialForms Y) (Nat.cast_add q p).symm)).val.app
            (op (f ⁻¹ᵁ U)) (((absoluteDifferentialFormsAlgebra Y).mul q p).app (op (f ⁻¹ᵁ U))
              (f.absoluteFormsPullback q U ω) η)) =
        (eqToHom (congrArg (absoluteDifferentialForms X) (Nat.cast_add q p).symm)).val.app (op U)
          (((absoluteDifferentialFormsAlgebra X).mul q p).app (op U) ω
            ((f.formsTrace hf p).app U η))) ∧
    -- (3) the relative version over a base
    (∀ {S : Scheme.{u}} (g : X ⟶ S), ∃ ΘS : ∀ p : ℕ,
        (Scheme.Modules.pushforward f).obj (relativeDifferentialForms (f ≫ g) p) ⟶
          relativeDifferentialForms g p,
      (∀ p : ℕ, (Scheme.Modules.pushforward f).map ((f ≫ g).absoluteToRelativeFormsMap p) ≫
          ΘS p = f.formsTrace hf p ≫ g.absoluteToRelativeFormsMap p) ∧
      ∀ (p : ℕ) (U : X.Opens) (η : Γ(relativeDifferentialForms (f ≫ g) p, f ⁻¹ᵁ U)),
        (ΘS (p + 1)).app U (((f ≫ g).deRhamComplex.d p (p + 1)).val.app (op (f ⁻¹ᵁ U)) η) =
          (g.deRhamComplex.d p (p + 1)).val.app (op U) ((ΘS p).app U η)) :=
  ⟨formsTrace_deRhamComplex_d f hf, formsTrace_zero f hf, formsTrace_mul_absoluteFormsPullback f hf,
    fun g => ⟨f.relativeFormsTrace g hf,
      fun p => relativeFormsTrace_comp_formsTrace (f := f) (g := g) (p := p) hf,
      fun p U η => relativeFormsTrace_deRhamComplex_d (f := f) (g := g) (p := p) hf U η⟩⟩

end AlgebraicGeometry.Scheme.Hom
