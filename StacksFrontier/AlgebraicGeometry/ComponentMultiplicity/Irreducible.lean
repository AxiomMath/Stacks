module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeInduction.Unconditional
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.Modules.UnitStalk
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYW] for an irreducible scheme of dimension one

The second paragraph of the proof of [Stacks, Tag 0AYW] treats an irreducible proper `X` of
dimension one over a field `k`. Writing `C = X_red` for its reduction, `ℐ` for the ideal of `C`
and `e` for the least exponent with `ℐ^{e+1} = 0`, it induces on `e`: at each step `ℱ = ℐ^e` is a
coherent module on `C`, `X'` is the closed subscheme cut out by `ℐ^e`, and the short exact
sequence

`0 ⟶ ℱ ⟶ 𝒪_X ⟶ 𝒪_{X'} ⟶ 0`

splits the degree as `deg(ℰ) = r·deg(ℰ|_C) + deg(ℰ|_{X'})`, with `r` the rank of `ℱ` at the
generic point.

This file puts that step in the shape the tag's conclusion is stated in. Two things happen.
First, `C` is taken to be the reduced one-dimensional component
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent X ξ` at the generic point, which is
`X_red` for irreducible `X`; the hypothesis `[AlgebraicGeometry.IsCurve k (j ≫ f)]` that
`AlgebraicGeometry.curveDegree_eq_mul_of_shortExact_pushforward_of_isCurve` carries is then a
*theorem*, `Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`, and
disappears, as do local Noetherianity, the two dimension bounds and all five coherence
hypotheses. Second, the degree on `C` becomes
`Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree`, so the conclusion is literally the
summand of the tag.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.ComponentDegrees`.

* `finsum_componentMultiplicity_mul_of_irreducibleSpace` — on an irreducible scheme of dimension
  one the locally finite sum of the tag has a single term, at the generic point, **with** its
  multiplicity weight. This is the unreduced companion of `finsum_componentDegree_of_isIntegral`,
  which collapses the weight to one and so needs `[IsReduced X]`.
* `curveDegree_eq_mul_componentDegree_of_shortExact` — the inductive step at the reduced
  component: from the short exact sequence, the length identity `m = r + m'` and the inductive
  hypothesis `deg(ℰ|_{X'}) = m'·deg(ℰ|_C)`, the equation `deg(ℰ) = m·deg(ℰ|_C)` with `deg(ℰ|_C)`
  read as `componentDegree`.
* `curveDegree_eq_finsum_componentDegree_of_irreducibleSpace` — the component formula of
  [Stacks, Tag 0AYW] for an irreducible `X` of dimension one, from the same three inputs.
* `AlgebraicGeometry.length_stalk_add_of_shortExact` — the length of a stalk is additive along a
  short exact sequence of modules on a scheme.
* `componentMultiplicity_eq_add_of_shortExact` — half of the source's length identity: from the
  same short exact sequence, `m(ξ)` is the sum of the stalk lengths of `j_*ℱ` and of `i_*𝒪_{X'}`
  at `ξ`.
* `AlgebraicGeometry.length_stalk_pushforward_unit_of_isClosedImmersion` — the second of those
  stalk lengths is the length of `𝒪_{X',w}` over itself, i.e. the source's `m'`.
* `componentMultiplicity_eq_add_length_stalk_of_shortExact` — the two together:
  `m(ξ) = length (j_*ℱ)_ξ + length 𝒪_{X',w}`.
* `AlgebraicGeometry.length_stalk_pushforward_of_isClosedImmersion` — the stalk length of a
  direct image along a closed immersion is the stalk length upstairs, for an arbitrary module.
* `AlgebraicGeometry.length_stalk_eq_fiberRank_of_isField` — at a point whose local ring is a
  field the stalk length of a module of finite type is its fibre rank.
* `length_stalk_pushforward_reducedComponent_eq_fiberRank` — the two together identify the first
  summand above with the source's `r`, the fibre rank of `ℱ` at the generic point of the
  component, the local ring of the *reduced* component there being a field.
* `componentMultiplicity_eq_fiberRank_add_of_shortExact` — **the source's `m = r + m'` in full**,
  with nothing of the identity left as a hypothesis.
* `curveDegree_eq_componentMultiplicity_mul_of_shortExact` — the inductive step with that
  identity discharged: the `hm` binder of `curveDegree_eq_mul_componentDegree_of_shortExact` is
  gone, and what remains of the second paragraph of the tag is the short exact sequence and the
  induction.

## Implementation notes

**What is discharged here, and from what.** `[AlgebraicGeometry.IsLocallyNoetherian X]` comes
from `[IsProper f]` through `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, and on
the two closed subschemes through
`AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`; the coherence of `ℰ` and of the two
structure sheaves is [Stacks, Tag 01XZ], by
`AlgebraicGeometry.isCoherent_of_isFiniteLocallyFreeOfRank` and
`Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent`; the coherence of the two
restrictions of `ℰ` is `AlgebraicGeometry.isCoherent_pullback`. The dimension bound on the
component is `topologicalKrullDim_reducedComponent_le` and the one on `X'` is the inducing-map
bound along its closed immersion. Only the coherence of `ℱ` is irreducibly a hypothesis: `ℱ` is
an arbitrary module here.

**The generic point of the component needs an instance that is a theorem.**
`Stacks.AlgebraicGeometry.ComponentDegrees.isIntegral_reducedComponent` is not registered as an
instance, so `AlgebraicGeometry.genericPoint (reducedComponent X ξ)` cannot be written in a
statement without it; the length identity therefore appears under a `letI`, exactly as in
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponentι_genericPoint`.

**The stalk-length additivity is stated in the `AlgebraicGeometry` namespace**, not here: it is
about an arbitrary short exact sequence of modules on an arbitrary scheme and has nothing to do
with components. It generalizes the `private` `sheafMultiplicity_add_of_shortExact` of
`StacksFrontier/AlgebraicGeometry/Variety/NumericalIntersectionLeadingTerm.lean`, which the same
argument proves and which, being private, no second consumer can use. The exactness of the stalk
functor it rests on is
`Stacks.SheafOfModules.FlatShortExact.stalkShortExact`, and the identification of the stalk of
`𝒪_X` read as a module with the local ring is
`Stacks.UnitStalk.unitStalkLinearEquiv`.

**No `@[stacks 0AYW]` attribute is attached.** Of the three items the module docstring of
`StacksFrontier/AlgebraicGeometry/ComponentDegreeInduction/Basic.lean` lists above its step — the
short exact sequence `0 ⟶ ℐ^e ⟶ 𝒪_X ⟶ 𝒪_{X'} ⟶ 0`, the length identity `m = r + m'` and the
first paragraph of the proof — the second is now a theorem here,
`componentMultiplicity_eq_fiberRank_add_of_shortExact`, and so is the induction's own
substitution, `curveDegree_eq_componentMultiplicity_mul_of_shortExact`. What these statements
still carry beyond the source is the short exact sequence itself and the induction on `e`, and
nothing here says anything about the first paragraph. The tag's attributes stay on
`Stacks.AlgebraicGeometry.ComponentDegrees.curveDegree_eq_finsum_componentDegree` and its
siblings in `StacksFrontier/AlgebraicGeometry/ComponentMultiplicity/Devissage.lean`.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The length of a stalk is additive along a short exact sequence of modules on a scheme.**
The stalk functor on sheaves of modules is exact, so a short exact sequence `0 ⟶ ℱ ⟶ 𝒢 ⟶ ℋ ⟶ 0`
gives a short exact sequence of modules over the local ring at every point, and the length of a
module is additive there. -/
public theorem length_stalk_add_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (x : X) :
    Module.length (X.presheaf.stalk x) (S.X₂.presheaf.stalk x) =
      Module.length (X.presheaf.stalk x) (S.X₁.presheaf.stalk x) +
        Module.length (X.presheaf.stalk x) (S.X₃.presheaf.stalk x) := by
  obtain ⟨α, β, hinj, hex, hsurj⟩ :
      ∃ (α : S.X₁.presheaf.stalk x →ₗ[X.presheaf.stalk x] S.X₂.presheaf.stalk x)
        (β : S.X₂.presheaf.stalk x →ₗ[X.presheaf.stalk x] S.X₃.presheaf.stalk x),
        Function.Injective α ∧ Function.Exact α β ∧ Function.Surjective β :=
    Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS x
  exact Module.length_eq_add_of_exact α β hinj hsurj hex

/-- Stalk length of a direct image along a closed immersion, for an arbitrary module. -/
private theorem length_stalk_pushforward_aux {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (z : Z) :
    Module.length (X.presheaf.stalk (i z))
        (((Scheme.Modules.pushforward i).obj M).presheaf.stalk (i z)) =
      Module.length (Z.presheaf.stalk z) (M.presheaf.stalk z) := by
  let : Module (X.presheaf.stalk (i z)) (M.presheaf.stalk z) :=
    Module.compHom (M.presheaf.stalk z) (i.stalkMap z).hom
  have hbij := Stacks.Chow.bijective_stalkPushforwardComparison i M z
    (IsClosedImmersion.isClosedEmbedding i).isInducing
  let e : ((Scheme.Modules.pushforward i).obj M).presheaf.stalk (i z)
      ≃ₗ[X.presheaf.stalk (i z)] M.presheaf.stalk z :=
    { toFun := Stacks.Chow.stalkPushforwardComparison i M z
      map_add' := Stacks.Chow.stalkPushforwardComparison_add i M z
      map_smul' := Stacks.Chow.stalkPushforwardComparison_smul i M z
      invFun := Function.surjInv hbij.2
      left_inv := Function.leftInverse_surjInv hbij
      right_inv := Function.rightInverse_surjInv hbij.2 }
  rw [e.length_eq]
  exact length_restrictScalars_eq_of_surjective (X.presheaf.stalk (i z))
    (Z.presheaf.stalk z) (i.stalkMap z).hom (i.stalkMap_surjective z) (M.presheaf.stalk z)

/-- **The stalk length of `i_*𝒪_W` at a point of the image is the length of `𝒪_{W,w}` over
itself.** This is the source's `m'` in the second paragraph of [Stacks, Tag 0AYW]: the
multiplicity of the closed subscheme `W = X'`, read on `X` as the length of a stalk of `i_*𝒪_W`
rather than on `W`.

Two steps: `Stacks.Chow.length_stalk_pushforwardStructureSheaf` identifies the stalk of the
direct image with `𝒪_{W,w}` as a module over `𝒪_{X,i w}`, and the comorphism
`𝒪_{X,i w} ⟶ 𝒪_{W,w}` of a closed immersion is surjective, so the two rings have the same
submodules of it ([Stacks, Tag 00IX]). -/
public theorem length_stalk_pushforward_unit_of_isClosedImmersion {X W : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (w : W) :
    Module.length (X.presheaf.stalk (i w))
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit W.ringCatSheaf)).presheaf.stalk (i w)) =
      Module.length (W.presheaf.stalk w) (W.presheaf.stalk w) := by
  exact (length_stalk_pushforward_aux i _ w).trans
    (Stacks.UnitStalk.unitStalkLinearEquiv W w).length_eq.symm

/-- **The stalk length of a direct image along a closed immersion is the stalk length upstairs.**
For `i : Z ⟶ X` a closed immersion and `M` a module on `Z`, the stalk of `i_*M` at `i z` is the
stalk of `M` at `z`, and the lengths over `𝒪_{X,i z}` and over `𝒪_{Z,z}` agree because the
comorphism `𝒪_{X,i z} ⟶ 𝒪_{Z,z}` is surjective ([Stacks, Tag 00IX]).

This is `length_stalk_pushforward_unit_of_isClosedImmersion` for an arbitrary module in place of
the structure sheaf: the stalk comparison `Stacks.Chow.stalkPushforwardComparison` is already
built for an arbitrary module, only the identification of the stalk of `𝒪_Z` read as a module
with the local ring was specific to the unit. -/
public theorem length_stalk_pushforward_of_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (z : Z) :
    Module.length (X.presheaf.stalk (i z))
        (((Scheme.Modules.pushforward i).obj M).presheaf.stalk (i z)) =
      Module.length (Z.presheaf.stalk z) (M.presheaf.stalk z) :=
  length_stalk_pushforward_aux i M z

/-- **At a point whose local ring is a field, the stalk length of a module of finite type is its
fibre rank.** Over a field every module is free, so the stalk length is the rank of the stalk,
which is the fibre rank by
`AlgebraicGeometry.Scheme.Modules.fiberRank_eq_finrank_stalk`. -/
public theorem length_stalk_eq_fiberRank_of_isField {C : Scheme.{u}} (M : C.Modules)
    [M.IsFiniteType] (c : C) (hc : IsField (C.presheaf.stalk c)) :
    (Module.length (C.presheaf.stalk c) (M.presheaf.stalk c)).toNat =
      Scheme.Modules.fiberRank M c := by
  let : Field (C.presheaf.stalk c) := hc.toField
  let : Module.Finite (C.presheaf.stalk c) (M.presheaf.stalk c) :=
    SheafOfModules.finite_stalk C.sheaf M c
  rw [Module.length_eq_finrank,
    Scheme.Modules.fiberRank_eq_finrank_stalk M c (Module.Free.of_divisionRing _ _)]
  simp

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ComponentDegrees

/-- **On an irreducible scheme of dimension one the sum of Stacks Tag 0AYW has one term.** The
index set is the singleton of the generic point, so the sum is the multiplicity there times the
value there. Unlike `finsum_componentDegree_of_isIntegral` this keeps the weight, and so needs no
reducedness. -/
theorem finsum_componentMultiplicity_mul_of_irreducibleSpace (X : Scheme.{u})
    [IrreducibleSpace X] (hX1 : topologicalKrullDim (X : Type u) = 1)
    (g : genericPointsOne X → ℤ) :
    ∑ᶠ ξ : genericPointsOne X, (componentMultiplicity X ξ : ℤ) * g ξ =
      (componentMultiplicity X ⟨genericPoint (X : Type u),
            genericPoint_self_mem_genericPointsOne X hX1⟩ : ℤ) *
        g ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX1⟩ := by
  have huniq : ∀ ξ : genericPointsOne X,
      ξ = ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX1⟩ :=
    fun ξ => Subtype.ext (eq_genericPoint_of_mem_genericPointsOne X hX1 ξ)
  rw [finsum_eq_single _ ⟨genericPoint (X : Type u),
    genericPoint_self_mem_genericPointsOne X hX1⟩ fun x hx => absurd (huniq x) hx]

/-- **The inductive step of [Stacks, Tag 0AYW] at a reduced one-dimensional component.**

For `ξ` a generic point of a one-dimensional component of `X`, `i : X' ⟶ X` a closed immersion,
`ℱ` coherent on the component `C(ξ)` and a short exact sequence

`0 ⟶ j_*ℱ ⟶ 𝒪_X ⟶ i_*𝒪_{X'} ⟶ 0`

with `j` the closed immersion of `C(ξ)`, the source's length identity `m = r + m'` at the generic
point and its inductive hypothesis `deg(ℰ|_{X'}) = m'·deg(ℰ|_{C(ξ)})` give

`deg(ℰ) = m · deg(ℰ|_{C(ξ)})`,

the degree on the component read as
`Stacks.AlgebraicGeometry.ComponentDegrees.componentDegree`.

This is `AlgebraicGeometry.curveDegree_eq_mul_of_shortExact_pushforward_of_isCurve` with every
hypothesis that `[IsProper f]` already implies discharged, including its `[IsCurve k (j ≫ f)]`:
a reduced one-dimensional component of a scheme proper over a field *is* a curve, by
`Stacks.AlgebraicGeometry.ComponentDegrees.isCurve_reducedComponentι_comp`. -/
theorem curveDegree_eq_mul_componentDegree_of_shortExact (k : Type u) [Field k]
    {X W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (ξ : genericPointsOne X)
    (i : W ⟶ X) [IsClosedImmersion i]
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (F : (reducedComponent X ξ).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F)
    (α : (Scheme.Modules.pushforward (reducedComponentι X ξ)).obj F ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf)
    (β : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (m m' : ℕ)
    (hm : letI : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
      m = Scheme.Modules.fiberRank F (genericPoint (reducedComponent X ξ)) + m')
    (hind : @curveDegree k _ W (i ≫ f) _
          (le_trans (IsClosedImmersion.isClosedEmbedding i).isInducing.topologicalKrullDim_le hX)
          ((Scheme.Modules.pullback i).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) =
        (m' : ℤ) * componentDegree k f hX E rank ξ) :
    curveDegree k f hX E rank = (m : ℤ) * componentDegree k f hX E rank ξ := by
  have hLNX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hLNC : IsLocallyNoetherian (reducedComponent X ξ) :=
    isLocallyNoetherian_of_isClosedImmersion (reducedComponentι X ξ)
  have hLNW : IsLocallyNoetherian W := isLocallyNoetherian_of_isClosedImmersion i
  have hE : _root_.SheafOfModules.IsCoherent E := isCoherent_of_isFiniteLocallyFreeOfRank E rank
  have hOX : _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hOW : _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.unit W.ringCatSheaf) :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent W hLNW
  have hEC : _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback (reducedComponentι X ξ)).obj E) :=
    @isCoherent_pullback _ _ hLNC (reducedComponentι X ξ) E hE
  have hEW : _root_.SheafOfModules.IsCoherent ((Scheme.Modules.pullback i).obj E) :=
    @isCoherent_pullback _ _ hLNW i E hE
  have _ : IsProper (reducedComponentι X ξ ≫ f) := isProper_reducedComponentι_comp k f ξ
  have _ : IsCurve k (reducedComponentι X ξ ≫ f) := isCurve_reducedComponentι_comp k f ξ
  exact curveDegree_eq_mul_of_shortExact_pushforward_of_isCurve k f (reducedComponentι X ξ) i
    hX (topologicalKrullDim_reducedComponent_le X hX ξ)
    (le_trans (IsClosedImmersion.isClosedEmbedding i).isInducing.topologicalKrullDim_le hX)
    E rank F hF hE hOX hOW hEC hEW α β w hS m m' hm hind

/-- **[Stacks, Tag 0AYW] for an irreducible scheme of dimension one**, modulo the short exact
sequence, the length identity and the induction.

The index set of the tag's sum is the singleton of the generic point, and the single summand is
the conclusion of `curveDegree_eq_mul_componentDegree_of_shortExact` with
`m = componentMultiplicity X ξ`. -/
theorem curveDegree_eq_finsum_componentDegree_of_irreducibleSpace (k : Type u) [Field k]
    {X W : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (hX1 : topologicalKrullDim (X : Type u) = 1)
    (i : W ⟶ X) [IsClosedImmersion i]
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (F : (reducedComponent X ⟨genericPoint (X : Type u),
        genericPoint_self_mem_genericPointsOne X hX1⟩).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F)
    (α : (Scheme.Modules.pushforward (reducedComponentι X ⟨genericPoint (X : Type u),
          genericPoint_self_mem_genericPointsOne X hX1⟩)).obj F ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf)
    (β : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (m' : ℕ)
    (hm : letI : IsIntegral (reducedComponent X ⟨genericPoint (X : Type u),
          genericPoint_self_mem_genericPointsOne X hX1⟩) :=
        isIntegral_reducedComponent X _
      componentMultiplicity X ⟨genericPoint (X : Type u),
          genericPoint_self_mem_genericPointsOne X hX1⟩ =
        Scheme.Modules.fiberRank F (genericPoint (reducedComponent X
          ⟨genericPoint (X : Type u), genericPoint_self_mem_genericPointsOne X hX1⟩)) + m')
    (hind : @curveDegree k _ W (i ≫ f) _
          (le_trans (IsClosedImmersion.isClosedEmbedding i).isInducing.topologicalKrullDim_le hX)
          ((Scheme.Modules.pullback i).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) =
        (m' : ℤ) * componentDegree k f hX E rank ⟨genericPoint (X : Type u),
          genericPoint_self_mem_genericPointsOne X hX1⟩) :
    curveDegree k f hX E rank =
      ∑ᶠ ξ : genericPointsOne X,
        (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  rw [finsum_componentMultiplicity_mul_of_irreducibleSpace X hX1
    (componentDegree k f hX E rank)]
  exact curveDegree_eq_mul_componentDegree_of_shortExact k f hX _ i E rank F hF α β w hS _ m'
    hm hind

/-! ### Half of the source's length identity -/

/-- **The source's `m = r + m'`, with `r` and `m'` still read as stalk lengths.** At the generic
point `ξ` of a one-dimensional component, the short exact sequence
`0 ⟶ j_*ℱ ⟶ 𝒪_X ⟶ i_*𝒪_{X'} ⟶ 0` of the second paragraph of [Stacks, Tag 0AYW] gives

`m(ξ) = length (j_*ℱ)_ξ + length (i_*𝒪_{X'})_ξ`,

the lengths taken over the local ring `𝒪_{X,ξ}` whose own length is `m(ξ)`.

Both summands are automatically finite: their sum is the length of `𝒪_{X,ξ}`, which is finite by
`Stacks.AlgebraicGeometry.ComponentDegrees.length_stalk_ne_top`, so no finiteness hypothesis
appears. What the source still asks for, and this does not supply, is the identification of the
first summand with the fibre rank of `ℱ` at the generic point of the component and of the second
with the multiplicity `m'` of `X'`; each is a comparison of a stalk of a direct image with a
stalk on the subscheme, not a statement about the sequence. -/
theorem componentMultiplicity_eq_add_of_shortExact (k : Type u) [Field k]
    {X C W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X)
    (j : C ⟶ X) (i : W ⟶ X) (F : C.Modules)
    (α : (Scheme.Modules.pushforward j).obj F ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (β : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact) :
    componentMultiplicity X ξ =
      (Module.length (X.presheaf.stalk ξ.1)
          (((Scheme.Modules.pushforward j).obj F).presheaf.stalk ξ.1)).toNat +
        (Module.length (X.presheaf.stalk ξ.1)
          (((Scheme.Modules.pushforward i).obj
            (_root_.SheafOfModules.unit W.ringCatSheaf)).presheaf.stalk ξ.1)).toNat := by
  have hunit : Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1) =
      Module.length (X.presheaf.stalk ξ.1)
        ((Stacks.UnitStalk.unitModule X).presheaf.stalk ξ.1) :=
    (Stacks.UnitStalk.unitStalkLinearEquiv X ξ.1).length_eq
  have hadd := (hunit.trans
    (_root_.AlgebraicGeometry.length_stalk_add_of_shortExact hS ξ.1))
  have hne : Module.length (X.presheaf.stalk ξ.1) (X.presheaf.stalk ξ.1) ≠ ⊤ :=
    length_stalk_ne_top k f ξ
  rw [hadd] at hne
  exact (congrArg ENat.toNat hadd).trans
    (ENat.toNat_add (WithTop.add_ne_top.1 hne).1 (WithTop.add_ne_top.1 hne).2)

/-- **The source's `m = r + m'`, with only `r` left to identify.** Composing
`componentMultiplicity_eq_add_of_shortExact` with
`AlgebraicGeometry.length_stalk_pushforward_unit_of_isClosedImmersion` at a point `w` of `X'`
over `ξ` reads the second summand as the multiplicity `m'` of `X'` at `w`, computed on `X'`:

`m(ξ) = length (j_*ℱ)_ξ + length 𝒪_{X',w}`.

What is still owed is the first summand: that `length (j_*ℱ)_ξ` is the fibre rank of `ℱ` at the
generic point of the component, which holds because `ℱ` is a module on the *reduced* component,
whose local ring at its generic point is a field. -/
theorem componentMultiplicity_eq_add_length_stalk_of_shortExact (k : Type u) [Field k]
    {X C W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X)
    (j : C ⟶ X) (i : W ⟶ X) [IsClosedImmersion i] (F : C.Modules)
    (α : (Scheme.Modules.pushforward j).obj F ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (β : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (ww : W) (hww : (i ww : X) = ξ.1) :
    componentMultiplicity X ξ =
      (Module.length (X.presheaf.stalk ξ.1)
          (((Scheme.Modules.pushforward j).obj F).presheaf.stalk ξ.1)).toNat +
        (Module.length (W.presheaf.stalk ww) (W.presheaf.stalk ww)).toNat := by
  rw [componentMultiplicity_eq_add_of_shortExact k f ξ j i F α β w hS, ← hww,
    _root_.AlgebraicGeometry.length_stalk_pushforward_unit_of_isClosedImmersion i ww]

/-! ### The source's length identity in full -/

/-- **The local ring of a reduced one-dimensional component at its generic point is a field.**
The component is integral, so it is reduced, and its generic point is maximal for the
specialization order. -/
theorem isField_stalk_reducedComponent_genericPoint {X : Scheme.{u}} (ξ : genericPointsOne X) :
    letI : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
    IsField ((reducedComponent X ξ).presheaf.stalk (genericPoint (reducedComponent X ξ))) := by
  let : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
  refine _root_.AlgebraicGeometry.isField_stalk_of_isMax
    (isMax_of_mem_genericPoints _ ?_)
  rw [genericPoints_eq_singleton]
  exact Set.mem_singleton _

/-- **The remaining third of the source's length identity `m = r + m'`**: the stalk length of
`j_*ℱ` at `ξ` is the fibre rank `r` of `ℱ` at the generic point of the component.

Two steps: `AlgebraicGeometry.length_stalk_pushforward_of_isClosedImmersion` moves the length
from the direct image on `X` to `ℱ` on the component, and
`AlgebraicGeometry.length_stalk_eq_fiberRank_of_isField` computes it as the fibre rank, the
local ring of the *reduced* component at its generic point being a field. -/
theorem length_stalk_pushforward_reducedComponent_eq_fiberRank {X : Scheme.{u}}
    (ξ : genericPointsOne X) (F : (reducedComponent X ξ).Modules) [F.IsFiniteType] :
    letI : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
    (Module.length (X.presheaf.stalk ξ.1)
        (((Scheme.Modules.pushforward (reducedComponentι X ξ)).obj F).presheaf.stalk
          ξ.1)).toNat =
      Scheme.Modules.fiberRank F (genericPoint (reducedComponent X ξ)) := by
  let : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
  have h := _root_.AlgebraicGeometry.length_stalk_pushforward_of_isClosedImmersion
    (reducedComponentι X ξ) F (genericPoint (reducedComponent X ξ))
  rw [reducedComponentι_genericPoint X ξ] at h
  rw [h]
  exact _root_.AlgebraicGeometry.length_stalk_eq_fiberRank_of_isField F _
    (isField_stalk_reducedComponent_genericPoint ξ)

/-- **The source's `m = r + m'`, in full.** At the generic point `ξ` of a one-dimensional
component, the short exact sequence `0 ⟶ j_*ℱ ⟶ 𝒪_X ⟶ i_*𝒪_{X'} ⟶ 0` of the second paragraph of
[Stacks, Tag 0AYW] gives

`m(ξ) = r + m'`,

with `r` the fibre rank of `ℱ` at the generic point of the component and `m'` the multiplicity
of `X'` at a point `ww` over `ξ`. This is
`componentMultiplicity_eq_add_length_stalk_of_shortExact` with its first summand identified by
`length_stalk_pushforward_reducedComponent_eq_fiberRank`; nothing of the identity is left as a
hypothesis. -/
theorem componentMultiplicity_eq_fiberRank_add_of_shortExact (k : Type u) [Field k]
    {X W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (ξ : genericPointsOne X)
    (i : W ⟶ X) [IsClosedImmersion i] (F : (reducedComponent X ξ).Modules) [F.IsFiniteType]
    (α : (Scheme.Modules.pushforward (reducedComponentι X ξ)).obj F ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf)
    (β : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (ww : W) (hww : (i ww : X) = ξ.1) :
    letI : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
    componentMultiplicity X ξ =
      Scheme.Modules.fiberRank F (genericPoint (reducedComponent X ξ)) +
        (Module.length (W.presheaf.stalk ww) (W.presheaf.stalk ww)).toNat := by
  let : IsIntegral (reducedComponent X ξ) := isIntegral_reducedComponent X ξ
  rw [componentMultiplicity_eq_add_length_stalk_of_shortExact k f ξ
      (reducedComponentι X ξ) i F α β w hS ww hww,
    length_stalk_pushforward_reducedComponent_eq_fiberRank ξ F]

/-- **The inductive step of [Stacks, Tag 0AYW] with the source's length identity discharged.**

`curveDegree_eq_mul_componentDegree_of_shortExact` asks for the identity `m = r + m'` as the
hypothesis `hm`; here `m` is the multiplicity of the component and `m'` the multiplicity of `X'`
at a point over `ξ`, and the identity is a theorem,
`componentMultiplicity_eq_fiberRank_add_of_shortExact`. What is left is the short exact sequence
itself and the inductive hypothesis `hind`. -/
theorem curveDegree_eq_componentMultiplicity_mul_of_shortExact (k : Type u) [Field k]
    {X W : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hX : topologicalKrullDim X ≤ 1) (ξ : genericPointsOne X)
    (i : W ⟶ X) [IsClosedImmersion i]
    (E : X.Modules) (rank : ℕ)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    (F : (reducedComponent X ξ).Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (α : (Scheme.Modules.pushforward (reducedComponentι X ξ)).obj F ⟶
      _root_.SheafOfModules.unit X.ringCatSheaf)
    (β : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (_root_.SheafOfModules.unit W.ringCatSheaf))
    (w : α ≫ β = 0) (hS : (ShortComplex.mk α β w).ShortExact)
    (ww : W) (hww : (i ww : X) = ξ.1)
    (hind : @curveDegree k _ W (i ≫ f) _
          (le_trans (IsClosedImmersion.isClosedEmbedding i).isInducing.topologicalKrullDim_le hX)
          ((Scheme.Modules.pullback i).obj E) rank
          (_root_.AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback i E rank) =
        ((Module.length (W.presheaf.stalk ww) (W.presheaf.stalk ww)).toNat : ℤ) *
          componentDegree k f hX E rank ξ) :
    curveDegree k f hX E rank =
      (componentMultiplicity X ξ : ℤ) * componentDegree k f hX E rank ξ := by
  have : _root_.SheafOfModules.IsCoherent F := hF
  have : F.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  exact curveDegree_eq_mul_componentDegree_of_shortExact k f hX ξ i E rank F hF α β w hS
    (componentMultiplicity X ξ) _
    (componentMultiplicity_eq_fiberRank_add_of_shortExact k f ξ i F α β w hS ww hww) hind

end Stacks.AlgebraicGeometry.ComponentDegrees

end
