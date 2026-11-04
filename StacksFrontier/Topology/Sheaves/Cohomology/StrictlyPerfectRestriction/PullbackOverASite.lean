module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Geometry.RingedSpace.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

@[expose] public section

/-
# Problem Description

Stacks Tag 09U6, Lemma 20.46.4 (Section 20.46 "Strictly perfect complexes",
Chapter 20 "Cohomology of Sheaves").

Let $f : (X, \mathcal{O}_X) \to (Y, \mathcal{O}_Y)$ be a morphism of ringed spaces,
with associated pullback functor
$$ f^* : \mathrm{Mod}(\mathcal{O}_Y) \to \mathrm{Mod}(\mathcal{O}_X), \qquad
   f^* \mathcal{G} = f^{-1}\mathcal{G} \otimes_{f^{-1}\mathcal{O}_Y} \mathcal{O}_X, $$
extended termwise to complexes. The pullback functor is additive and right exact.

Main definitions:
* (Finite free) An $\mathcal{O}_X$-module $\mathcal{E}$ is *finite free* if
  $\mathcal{E} \cong \mathcal{O}_X^{\oplus n}$ for some $n \geq 0$.
* (Direct summand) $\mathcal{E}$ is a *direct summand* of $\mathcal{M}$ if there are
  morphisms $i : \mathcal{E} \to \mathcal{M}$, $p : \mathcal{M} \to \mathcal{E}$ with
  $p \circ i = \mathrm{id}_{\mathcal{E}}$ (a retract).
* (Strictly perfect, Def 20.46.1 / tag 08C4) A complex $\mathcal{E}^\bullet$ of
  $\mathcal{O}_X$-modules is *strictly perfect* if $\mathcal{E}^i = 0$ for all but
  finitely many $i$, and each $\mathcal{E}^i$ is a direct summand of a finite free
  $\mathcal{O}_X$-module.

Main statement: if $\mathcal{F}^\bullet$ is a strictly perfect complex of
$\mathcal{O}_Y$-modules, then $f^* \mathcal{F}^\bullet$ is a strictly perfect complex
of $\mathcal{O}_X$-modules.

## Modeling notes

We use Mathlib's actual notions of ringed spaces and sheaves of modules:

* `AlgebraicGeometry.RingedSpace` is `SheafedSpace CommRingCat`. The category
  `Mod(O_X)` of $\mathcal{O}_X$-modules is `SheafOfModules X.ringCatSheaf`, where
  `X.ringCatSheaf` is the structure sheaf of `X` regarded as a `RingCat`-valued
  sheaf (via `forget₂ CommRingCat RingCat`). This matches Mathlib's
  `AlgebraicGeometry.Scheme.Modules`.
* The pullback functor `f^* : Mod(O_Y) ⥤ Mod(O_X)` is the genuine
  `SheafOfModules.pullback` associated to the comparison ring morphism
  `O_Y ⟶ f_* O_X` extracted from `f.c`. This mirrors `Scheme.Modules.pullback`,
  but for an arbitrary morphism of ringed spaces.
* The structure sheaf `O_X` itself is the unit module `SheafOfModules.unit`, and
  the finite free module `O_X^{⊕ n}` is `SheafOfModules.free (Fin n)`.
* A complex of $\mathcal{O}_X$-modules is a `HomologicalComplex` for the cochain
  complex shape `ComplexShape.up ℤ`, and the termwise pullback is
  `(pullback f).mapHomologicalComplex _`.
-/

open CategoryTheory TopologicalSpace Limits


noncomputable section

namespace Stacks.Cohomology.StrictlyPerfectPullback

/-- The pushforward of sheaves of modules along a morphism of ringed spaces is a
right adjoint, with `pullbackPushforwardAdjunction` as the adjunction. Instance
search does not find this through the `Opens.map`/`sheafPushforwardContinuous`
layers of `ringCatSheaf`, so the adjunction supplies it here. -/
noncomputable instance pushforwardIsRightAdjoint
    {X Y : AlgebraicGeometry.RingedSpace.{0, 0}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{0} (toRingCatSheafHom f)).IsRightAdjoint :=
  (pullbackPushforwardAdjunction f).isRightAdjoint

/-- The pullback functor `f^* : Mod(O_Y) ⥤ Mod(O_X)` is a left adjoint, by the same
adjunction; this is what makes it preserve zero morphisms, hence extend termwise to
complexes via `Functor.mapHomologicalComplex`. -/
noncomputable instance pullback_isLeftAdjoint
    {X Y : AlgebraicGeometry.RingedSpace.{0, 0}} (f : X ⟶ Y) :
    (_root_.pullback f).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction f).isLeftAdjoint

/-- For any continuous map `g`, the inverse-image functor on opens `Opens.map g` is
final: each comma category `StructuredArrow U (Opens.map g)` is cofiltered (it is the
poset of opens `V` of the source with `U ≤ g⁻¹ V`, closed under binary meets and
containing the whole space), hence connected. -/
instance opensMap_final {X Y : TopCat} (g : X ⟶ Y) : (Opens.map g).Final := by
  constructor
  intro U
  have : Nonempty (StructuredArrow U (Opens.map g)) :=
    ⟨StructuredArrow.mk (Y := ⊤) (homOfLE le_top)⟩
  have : IsCofilteredOrEmpty (StructuredArrow U (Opens.map g)) :=
    ⟨fun A B => ⟨StructuredArrow.mk (Y := A.right ⊓ B.right) (homOfLE (le_inf A.hom.le B.hom.le)),
        StructuredArrow.homMk (homOfLE inf_le_left), StructuredArrow.homMk (homOfLE inf_le_right),
        trivial⟩,
      fun A _ _ _ => ⟨A, 𝟙 A, by
        congr 1; exact StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)⟩⟩
  have : IsCofiltered (StructuredArrow U (Opens.map g)) := IsCofiltered.mk
  exact IsCofiltered.isConnected _

-- Main Definition(s)

/-- **Definition 1 (Finite free module).** An `O_X`-module `E` is *finite free* if
it is isomorphic to `O_X^{⊕ n} = SheafOfModules.free (Fin n)` for some `n ≥ 0`.
Here `SheafOfModules.free (Fin n)` is the free `O_X`-module on `n` generators,
i.e. the direct sum of `n` copies of the structure sheaf `O_X`. -/
def IsFiniteFree {X : AlgebraicGeometry.RingedSpace.{0, 0}} (E : Modules X) : Prop :=
  ∃ n : ℕ, Nonempty (E ≅ SheafOfModules.free (Fin n))

/-- **Definition 2 (Direct summand).** An `O_X`-module `E` is a *direct summand* of
an `O_X`-module `M` if there are `O_X`-module morphisms `i : E → M`, `p : M → E`
with `p ∘ i = id_E`, i.e. `E` is a retract of `M`. (Equivalently there exists `E'`
with `M ≅ E ⊕ E'`.) -/
def IsDirectSummand {X : AlgebraicGeometry.RingedSpace.{0, 0}} (E M : Modules X) : Prop :=
  Nonempty (Retract E M)

/-- An `O_X`-module `E` is a direct summand of *some* finite free `O_X`-module.
This is the condition imposed termwise in the definition of "strictly perfect". -/
def IsDirectSummandOfFiniteFree {X : AlgebraicGeometry.RingedSpace.{0, 0}} (E : Modules X) : Prop :=
  ∃ M : Modules X, IsFiniteFree M ∧ IsDirectSummand E M

/-- **Definition 3 (Strictly perfect complex, Tag 08C4 / Def 20.46.1).** A cochain
complex `E^•` (indexed by `ℤ`) of `O_X`-modules is *strictly perfect* if:
(1) `E^i` is zero for all but finitely many `i ∈ ℤ`, and
(2) for every `i ∈ ℤ`, the term `E^i` is a direct summand of a finite free
`O_X`-module. -/
structure IsStrictlyPerfect {X : AlgebraicGeometry.RingedSpace.{0, 0}}
    (E : HomologicalComplex (Modules X) (ComplexShape.up ℤ)) : Prop where
  /-- Condition (1): only finitely many terms are nonzero. -/
  finite_support : {i : ℤ | ¬ IsZero (E.X i)}.Finite
  /-- Condition (2): each term is a direct summand of a finite free module. -/
  termwise : ∀ i : ℤ, IsDirectSummandOfFiniteFree (E.X i)

-- Main Statement(s)

/-- **Stacks Tag 09U6, Lemma 20.46.4.** Let `f : (X, O_X) → (Y, O_Y)` be a morphism
of ringed spaces, with pullback functor `f^* : Mod(O_Y) ⥤ Mod(O_X)`. If `F^•` is a
strictly perfect complex of `O_Y`-modules, then `f^* F^•` (the termwise pullback of
`F^•`) is a strictly perfect complex of `O_X`-modules. -/
@[stacks 09U6]
theorem pullback_isStrictlyPerfect {X Y : AlgebraicGeometry.RingedSpace.{0, 0}} (f : X ⟶ Y)
    (F : HomologicalComplex (Modules Y) (ComplexShape.up ℤ))
    (hF : IsStrictlyPerfect F) :
    IsStrictlyPerfect
      (((_root_.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) := by
  refine ⟨hF.finite_support.subset fun i hi hzero => hi ?_, fun i => ?_⟩
  · rw [Functor.mapHomologicalComplex_obj_X]
    exact (_root_.pullback f).map_isZero hzero
  · obtain ⟨M, ⟨n, ⟨e⟩⟩, ⟨r⟩⟩ := hF.termwise i
    rw [Functor.mapHomologicalComplex_obj_X]
    exact ⟨(_root_.pullback f).obj M,
      ⟨n, ⟨(_root_.pullback f).mapIso e ≪≫
        SheafOfModules.pullbackObjFreeIso (toRingCatSheafHom f) (Fin n)⟩⟩,
      ⟨r.map (_root_.pullback f)⟩⟩

end Stacks.Cohomology.StrictlyPerfectPullback
end
