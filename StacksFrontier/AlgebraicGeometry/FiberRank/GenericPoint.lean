module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Length
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre rank of a coherent module at the generic point of an integral scheme

On an integral scheme the local ring at the generic point is the function field, so every
module over it is free and its dimension is the fibre rank of Stacks Tag 05P2. For a coherent
module that dimension is finite, and it is additive along a short exact sequence. These are the
two facts a dévissage argument over an integral curve needs about the generic rank, and the
statement of Stacks Tag 0AYV mentions the first of them.

## Main results

* `AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent`: the stalk of a coherent module
  at any point is a finite module over the local ring there.
* `AlgebraicGeometry.Scheme.Modules.free_stalk_genericPoint`: on an integral scheme the stalk at
  the generic point is free, the local ring there being a field.
* `AlgebraicGeometry.Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk`: on an integral
  scheme the fibre rank of a module of finite type at the generic point is the dimension of its
  stalk there over the function field.
* `AlgebraicGeometry.Scheme.Modules.fiberRank_genericPoint_add_of_shortExact`: on an integral
  scheme the fibre rank at the generic point is additive along a short exact sequence of
  coherent modules.

## Implementation notes

Finiteness is `SheafOfModules.finite_stalk`, which holds for every module of finite type on any
ringed space and needs no dévissage, no Noetherian hypothesis and no integrality: a finite type
module has finitely many generators on a neighbourhood of the point, and their germs span the
stalk. Coherence enters only through
`SheafOfModules.IsCoherent.isFiniteType`. In particular none of the results below is restricted
to a Noetherian scheme.

Exactness of the stalk sequence is
`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`, which produces the two stalk
maps as `𝒪_{X,x}`-linear maps together with injectivity, exactness and surjectivity; additivity
of the dimension is then read off `Module.length`, which is `Module.finrank` over a field and is
additive along an exact sequence of modules by `Module.length_eq_add_of_exact`. Over the generic
point of an integral scheme the local ring is `AlgebraicGeometry.Scheme.functionField`, a field,
which is what makes the three stalks free and finite-dimensional at once.

The coherence class used is the root `SheafOfModules.IsCoherent`, which is the constant
`F.IsCoherent` resolves to throughout the curve and Euler-characteristic development, and **not**
`Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent`; the two are distinct constants and
neither discharges the other by instance search.

The `Module` structure on a stalk is not a global instance, so every statement carries it as a
`letI`, exactly as `AlgebraicGeometry.Scheme.Modules.fiberRank` and
`SheafOfModules.finite_stalk` do.

**No Stacks attribute is attached here.** Tag 0AYV asserts the Euler-characteristic formula
`χ(X, ℰ ⊗ ℱ) = r · deg(ℰ) + n · χ(X, ℱ)` on a proper curve, and Tag 05P2 asserts the
equivalence of five conditions for finite local freeness; the results below are inputs to the
first and consequences of neither, so none of them is a tagged statement.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Over a field the dimension is additive along a short exact sequence, read off the additivity
of `Module.length`. Stated at abstract types, with no scheme in sight, so that the stalk
spellings are never unfolded here. -/
@[sga "6 I 6.0" "(ii), special case"]
private theorem finrank_eq_add_of_exact (K M₁ M₂ M₃ : Type u) [Field K]
    [AddCommGroup M₁] [Module K M₁] [Module.Finite K M₁]
    [AddCommGroup M₂] [Module K M₂] [Module.Finite K M₂]
    [AddCommGroup M₃] [Module K M₃] [Module.Finite K M₃]
    (f : M₁ →ₗ[K] M₂) (g : M₂ →ₗ[K] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Module.finrank K M₂ = Module.finrank K M₁ + Module.finrank K M₃ := by
  have h : (Module.finrank K M₂ : ℕ∞) =
      (Module.finrank K M₁ : ℕ∞) + Module.finrank K M₃ := by
    rw [← Module.length_eq_finrank K M₂, ← Module.length_eq_finrank K M₁,
      ← Module.length_eq_finrank K M₃]
    exact Module.length_eq_add_of_exact f g hf hg hfg
  exact_mod_cast h

/-- **The stalk of a coherent module is a finite module over the local ring at the point.**
Coherence is used only through finiteness of type; no Noetherian hypothesis and no integrality
are needed. -/
theorem finite_stalk_of_isCoherent {X : Scheme.{u}} (F : X.Modules) [hF : F.IsCoherent] (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  have : F.IsFiniteType := hF.isFiniteType
  _root_.SheafOfModules.finite_stalk X.sheaf F x

/-- **On an integral scheme the stalk at the generic point is free**, the local ring there being
the function field. -/
theorem free_stalk_genericPoint {X : Scheme.{u}} [IsIntegral X] (F : X.Modules) :
    letI : Module (X.presheaf.stalk (genericPoint X)) (F.presheaf.stalk (genericPoint X)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val (genericPoint X)
    Module.Free (X.presheaf.stalk (genericPoint X)) (F.presheaf.stalk (genericPoint X)) := by
  let A := ToType (X.presheaf.stalk (genericPoint X))
  let M := ToType (F.presheaf.stalk (genericPoint X))
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (genericPoint X)
  let : Field A := inferInstanceAs (Field X.functionField)
  exact Module.Free.of_divisionRing A M

/-- **On an integral scheme the fibre rank at the generic point is the dimension of the stalk
there.** The residue field at the generic point of an integral scheme is the local ring itself,
so the base change defining the fibre rank changes nothing. -/
theorem fiberRank_genericPoint_eq_finrank_stalk {X : Scheme.{u}} [IsIntegral X]
    (F : X.Modules) [F.IsFiniteType] :
    letI : Module (X.presheaf.stalk (genericPoint X)) (F.presheaf.stalk (genericPoint X)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val (genericPoint X)
    fiberRank F (genericPoint X) =
      Module.finrank (X.presheaf.stalk (genericPoint X))
        (F.presheaf.stalk (genericPoint X)) :=
  fiberRank_eq_finrank_stalk F (genericPoint X) (free_stalk_genericPoint F)

open Stacks.SheafOfModules.FlatShortExact in
/-- **On an integral scheme the fibre rank at the generic point is additive along a short exact
sequence of coherent modules.** This is the rank half of hypothesis (1) of the dévissage of
Stacks Tag 01YI, as the proof of Stacks Tag 0AYV uses it. -/
@[sga "6 I 6.0" "(ii), special case"]
theorem fiberRank_genericPoint_add_of_shortExact {X : Scheme.{u}} [IsIntegral X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [h₁ : S.X₁.IsCoherent] [h₂ : S.X₂.IsCoherent] [h₃ : S.X₃.IsCoherent] :
    fiberRank S.X₂ (genericPoint X) =
      fiberRank S.X₁ (genericPoint X) + fiberRank S.X₃ (genericPoint X) := by
  have t₁ : S.X₁.IsFiniteType := h₁.isFiniteType
  have t₂ : S.X₂.IsFiniteType := h₂.isFiniteType
  have t₃ : S.X₃.IsFiniteType := h₃.isFiniteType
  rw [fiberRank_genericPoint_eq_finrank_stalk S.X₁,
    fiberRank_genericPoint_eq_finrank_stalk S.X₂,
    fiberRank_genericPoint_eq_finrank_stalk S.X₃]
  obtain ⟨f, g, hf, hfg, hg⟩ :=
    stalkShortExact (X := X.toRingedSpace) S hS (genericPoint X)
  let K := ToType (X.presheaf.stalk (genericPoint X))
  let : Field K := inferInstanceAs (Field X.functionField)
  let (E : X.Modules) : Module K (abStalk (X := X.toRingedSpace) E (genericPoint X)) :=
    stalkModule E (genericPoint X)
  have fin : ∀ E : X.Modules, E.IsFiniteType →
      Module.Finite K (abStalk (X := X.toRingedSpace) E (genericPoint X)) := fun E _ =>
    _root_.SheafOfModules.finite_stalk X.sheaf E (genericPoint X)
  have := fin _ t₁
  have := fin _ t₂
  have := fin _ t₃
  exact finrank_eq_add_of_exact K (abStalk (X := X.toRingedSpace) S.X₁ (genericPoint X))
    (abStalk (X := X.toRingedSpace) S.X₂ (genericPoint X))
    (abStalk (X := X.toRingedSpace) S.X₃ (genericPoint X)) f g hf hg hfg

end AlgebraicGeometry.Scheme.Modules
