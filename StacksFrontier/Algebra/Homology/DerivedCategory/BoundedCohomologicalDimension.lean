module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The left derived functor on the unbounded derived category, in bounded homological dimension

Let `F : 𝒜 ⥤ ℬ` be a right exact functor of abelian categories. An object `X` of `𝒜` is
*left acyclic for `F`* if the complex `X[0]` computes `LF`, i.e. if `LF` is defined at `X[0]`
and the canonical map `LF(X[0]) ⟶ F(X)` is an isomorphism (Stacks 0157(4), 05SX), and
`L ^ n F` denotes the functor `X ↦ H ^ (-n) (LF (X[0]))`. Assume that every object of `𝒜` is
a quotient of an object which is left acyclic for `F`, and that `L ^ n F = 0` for some integer
`n ≥ 0`. Then

1. the left derived functor `LF : D(𝒜) ⥤ D(ℬ)` exists on the *whole* derived category,
2. every complex all of whose terms are left acyclic for `F` computes `LF`,
3. every complex is the target of a quasi-isomorphism from a complex all of whose terms are
   left acyclic for `F`,
4. for `E` in `D(𝒜)`: the map `H ^ i (LF (τ_{≤ a + n - 1} E)) ⟶ H ^ i (LF E)` is an isomorphism
   for `i ≤ a`, the map `H ^ i (LF E) ⟶ H ^ i (LF (τ_{≥ b} E))` is an isomorphism for `i ≥ b`,
   and if `E` lives in degrees `[a, b]` then `LF E` lives in degrees `[a - n + 1, b]`.

This is the dual of Stacks 07K7, and the argument is the dual of the one given there. Writing
`L ^ i F (X) = H ^ (-i) (LF (X[0]))` for the classical left derived functors, computed on
`D⁻(𝒜)`, the route has five steps.

* **Vanishing in all high degrees.** For `X : 𝒜` choose an epimorphism `Y ⟶ X` with `Y` left
  acyclic, and let `Z` be its kernel. The long exact sequence of `L ^ ∗ F` attached to
  `0 ⟶ Z ⟶ Y ⟶ X ⟶ 0` and the acyclicity of `Y` give `L ^ (m + 1) F (X) ≅ L ^ m F (Z)` for
  `m ≥ 1`; hence `L ^ n F = 0` propagates upwards and `L ^ m F = 0` for every `m ≥ n`.
* **Resolutions.** For every complex `K` there is a quasi-isomorphism `L ⟶ K` with all terms
  of `L` left acyclic (part (3) above). Rather than dualizing the construction of Stacks 07K6 —
  the function `d (X) = max ({0} ∪ {i | L ^ i F (X) ≠ 0})`, bounded by `n`, additive on direct
  sums, dropping by at most one along the kernel of an epimorphism from a left acyclic object —
  this is *derived* from part (2) of Stacks 07K7 for `F.op`, whose hypotheses at `F.op` are
  literally those of Stacks 07K8 at `F`, transported along the duality
  `(CochainComplex 𝒜 ℤ)ᵒᵖ ≌ CochainComplex 𝒜ᵒᵖ ℤ` of `CochainComplex.opEquivalence`.
* **Exactness on resolutions.** If `L ⟶ M` is a quasi-isomorphism between complexes of left
  acyclic objects, then `F (L) ⟶ F (M)` is a quasi-isomorphism: the cone `Q` of
  `σ_{≤ i + n + 1} L ⟶ σ_{≤ i + n + 1} M` is bounded above with homology concentrated in the two
  degrees `i + n + 1`, `i + n + 2`, so the spectral sequence of Stacks 015J and the vanishing of
  the first step confine `H ^ j (LF (Q))` to `i + 1 ≤ j ≤ i + n + 2`; comparing with
  `LF (σ_{≤ i + n + 1} L) = σ_{≤ i + n + 1} F (L)` on `D⁻` gives the isomorphism in degree `i`.
* **Existence.** The previous two steps are the hypotheses of Stacks 06XN, dualized, which
  yields parts (1) and (2).
* **Range of degrees.** Part (4)(a) is Stacks 05TC dualized, part (4)(b) is the computation of
  `LF` on a complex of left acyclic objects together with the stupid truncations, and part (4)(c)
  follows from (4)(a) and (4)(b) because `τ_{≤ a - 1} E = 0` and `τ_{≥ b + 1} E = 0` for `E`
  living in degrees `[a, b]`.

## Main results

* `CategoryTheory.Functor.hasLeftDerivedFunctor_of_isZero_leftDerived`: parts (1), (3), (2)
  and (4) of Stacks 07K8, in that order.

## Implementation notes

The derived functor is the one of Mathlib's localization theory: `LF : D(𝒜) ⥤ D(ℬ)` is a left
derived functor of `K(𝒜) ⥤ D(ℬ)`, `K ↦ F(K)`, along the localization functor
`Qh : K(𝒜) ⥤ D(𝒜)` at quasi-isomorphisms, so that part (1) is `Functor.HasLeftDerivedFunctor`
for that functor and that class of morphisms, and the assertion that a complex `K` *computes*
`LF` is that the counit `α : Qh(-) ⋙ LF ⟶ F(-)` of the derived functor is invertible at `K`.
Parts (2) and (4) are stated for an *arbitrary* left derived functor `(LF, α)` on `D(𝒜)`, not
for a chosen one; any two are uniquely isomorphic compatibly with their counits
(`Functor.leftDerivedUnique`), so this is the strongest reading and it does not depend on a
construction. This mirrors the form chosen for Stacks 07K7.

Left acyclicity (Stacks 0157(4)) refers to the derived functor on `D⁻(𝒜)`, which Mathlib does
not carry as a localization of `K⁻(𝒜)`; as recorded for Stacks 0157, the left derived functor of
`F` on `D⁻(𝒜)` is the right derived functor of `F.op` on `D⁺(𝒜ᵒᵖ)`, since passing to opposite
categories exchanges `K⁻(𝒜)` with `K⁺(𝒜ᵒᵖ)` and turns `H ^ i` into `H ^ (-i)`. Accordingly the
bounded above derived functor is taken as data on the opposite side — a functor
`LF' : D⁺(𝒜ᵒᵖ) ⥤ D⁺(ℬᵒᵖ)` with a unit `α'` making it a right derived functor of `F.op` along
`Qh : K⁺(𝒜ᵒᵖ) ⥤ D⁺(𝒜ᵒᵖ)` — rather than constructed: hypothesis (1) makes it exist (Stacks 05TA
applied to `F.op`), but the existence of `LF` on the unbounded `D(𝒜)` is part of the
*conclusion*, so nothing is available to construct it from here. Then `X` is left acyclic for `F`
exactly when `Xᵒᵖ[0]` computes the right derived functor of `F.op : K⁺(𝒜ᵒᵖ) ⥤ D⁺(ℬᵒᵖ)` in the sense
of Stacks 05SX (`CategoryTheory.Functor.ComputesRightDerived`), which is the source's definition
read through the duality, and `L ^ n F (X) = H ^ (-n) (LF (X[0]))` is `H ^ n (LF' (Xᵒᵖ[0]))` read
in `ℬᵒᵖ`, which is independent of the choice of `(LF', α')`. The class of left acyclic objects is
carried by the `ObjectProperty` `P`, which abbreviates that condition in the hypothesis and in
parts (2) and (3).

`F.Additive` is a consequence of right exactness
(`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts` followed by
`CategoryTheory.Functor.additive_of_preservesBinaryBiproducts`) and is assumed only because
`Functor.mapHomotopyCategory` and `Functor.mapHomotopyCategoryPlus` are stated for additive
functors, so instance search needs it; it is not an extra hypothesis on `F`.

Part (4)(c) is split into its two one-sided implications, `H ^ i (E) = 0` for `i < a` implies
`H ^ i (LF E) = 0` for `i < a - n + 1`, and `H ^ i (E) = 0` for `i > b` implies
`H ^ i (LF E) = 0` for `i > b`. This is what the source's `-∞ ≤ a ≤ b ≤ ∞` means: for `a = -∞`
only the upper bound is asserted and for `b = ∞` only the lower one, and the two implications
together are strictly stronger than the conjunction of the two hypotheses implying the
conjunction of the two conclusions. Boundedness of an object of `D(ℬ)` is Mathlib's
`DerivedCategory.IsGE` / `IsLE` for the canonical t-structure, which is exactly the vanishing of
homology outside the range (`DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`), and the
truncations `τ_{≤ a + n - 1}`, `τ_{≥ b}` of parts (4)(a) and (4)(b) are that t-structure's
`truncLE`, `truncGE` together with its canonical maps `truncLEι`, `truncGEπ`.

The deduction of part (4)(c) from parts (4)(a) and (4)(b) is separated off as
`isGE_obj_of_isGE` and `isLE_obj_of_isLE`, stated for an arbitrary functor
`LF : D(𝒜) ⥤ D(ℬ)` that preserves zero morphisms and taking the isomorphisms of (4)(a),
respectively (4)(b), as a hypothesis: no other property of a derived functor enters it. That
`LF` preserves zero morphisms needs neither the triangulated structure of `LF` nor a
resolution: a right Kan extension `LF` of a functor `Φ` preserving zero morphisms along any
functor `L : C ⥤ D` between categories with zero objects satisfies `LF (0) = 0`, because `0` is
initial in `D`, so that a natural transformation `(const D).obj Y ⟶ LF` is the same thing as a
morphism `Y ⟶ LF (0)`, while `0` is initial in `C` too, so that the transformation
`L ⋙ (const D).obj Y ⟶ Φ` it must restrict to is forced to be zero. This is
`isZero_obj_zero_of_isLeftDerivedFunctor`, and it is a statement about Kan extensions alone;
`preservesZeroMorphisms_of_isLeftDerivedFunctor` is its application here.

Passing a derived functor across the duality is `isLeftKanExtension_op`: the opposite of a left
derived functor `(LF, α)` of `Φ` along a localization functor `L` is a left Kan extension of
`Φ.op` along `L.op`, hence a right derived functor of `Φ.op`. Only the universal property enters
— a terminal object of the category of right extensions of `Φ` along `L` is an initial object of
the category of left extensions of `Φ.op` along `L.op` — which is the converse of
`isRightKanExtension_of_op`.

The duality with Stacks 07K7 is used where it is available at the level of complexes.
`CochainComplex.opEquivalence 𝒜 : (CochainComplex 𝒜 ℤ)ᵒᵖ ≌ CochainComplex 𝒜ᵒᵖ ℤ` and the
degreewise comparison `CochainComplex.quasiIsoAt_opEquivalence_functor_map_iff` (a
quasi-isomorphism in degree `n` on one side is one in degree `-n` on the other, both sides being
the same short complex read through `ShortComplex.opMap`) transport part (2) of Stacks 07K7 for
`F.op` to part (3) here; the data `(LF', α')` is already the data `(RF⁺, α⁺)` that Stacks 07K7
asks for at `F.op`, and `P.op` is its class of right acyclic objects, so no
comparison of derived functors is needed for that part. The remaining parts speak about the
unbounded derived categories `D(𝒜)`, `D(ℬ)` and their t-structures, and they use the dualities
`K(𝒜)ᵒᵖ ≌ K(𝒜ᵒᵖ)` and `D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` of
`StacksFrontier.Algebra.Homology.DerivedCategory.Opposite` together with the exchanges of homology,
of the two bounds and of the two truncations proved there. What those dualities do not come with
is a triangulated structure, and none is needed: the truncations are pinned by their universal
properties instead. Their compatibility with the localization functors `Qh` is
`homotopyOpEquivalenceFunctorCompQhIso`, and `homotopyOpEquivalenceFunctorCompMapQhIso` says
that they carry `K ↦ F(K)` to `K ↦ F.op(K)`; both are again comparisons of two liftings through
a localization.

## References

* [StacksProject 07K8](https://stacks.math.columbia.edu/tag/07K8)
* [StacksProject 07K7](https://stacks.math.columbia.edu/tag/07K7), the dual statement, whose
  proof is the one dualized here
* [StacksProject 07K6](https://stacks.math.columbia.edu/tag/07K6), the construction of
  resolutions by acyclic objects
* [StacksProject 06XN](https://stacks.math.columbia.edu/tag/06XN), the existence criterion
* [StacksProject 015J](https://stacks.math.columbia.edu/tag/015J), the spectral sequences
* [StacksProject 05TC](https://stacks.math.columbia.edu/tag/05TC), part (4)(a)
* [StacksProject 0157](https://stacks.math.columbia.edu/tag/0157), definition of left acyclic
* [StacksProject 05TA](https://stacks.math.columbia.edu/tag/05TA), existence of `LF` on `D⁻`
-/

@[expose] public section

open CategoryTheory Limits ZeroObject HomotopyCategory DerivedCategory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section KanExtension

/-- A left derived functor sends the zero object to a zero object, as soon as the functor being
derived preserves zero morphisms. Only the universal property of the right Kan extension is
used, so this holds for a right Kan extension along an arbitrary functor `L : C ⥤ D` between
categories with zero objects.

The point is that a natural transformation from a constant functor `(const D).obj Y ⟶ LF` is the
same thing as a morphism `Y ⟶ LF.obj 0`, because `0` is initial in `D`, while, `0` being initial
in `C` as well, the corresponding transformation `L ⋙ (const D).obj Y ⟶ Φ` is forced to be zero;
so `𝟙 (LF.obj 0)` and `0` have the same image under an injective map. -/
private lemma isZero_obj_zero_of_isLeftDerivedFunctor
    {C : Type u₁} {D : Type u₂} {H : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
    [Category.{v₃} H] [HasZeroMorphisms C] [HasZeroMorphisms H] [HasZeroObject C]
    [HasZeroObject D] {Φ : C ⥤ H} [Φ.PreservesZeroMorphisms] {L : C ⥤ D}
    (W : MorphismProperty C) [L.IsLocalization W] (LF : D ⥤ H) (α : L ⋙ LF ⟶ Φ)
    [LF.IsLeftDerivedFunctor α W] : IsZero (LF.obj 0) := by
  have hD : IsZero (0 : D) := isZero_zero D
  let mk : (LF.obj 0 ⟶ LF.obj 0) → ((Functor.const D).obj (LF.obj 0) ⟶ LF) := fun f =>
    { app := fun X => f ≫ LF.map (hD.to_ X)
      naturality := fun X Y g => by
        dsimp
        rw [Category.id_comp, Category.assoc, ← LF.map_comp]
        congr 2
        exact hD.eq_of_src _ _ }
  have key : mk (𝟙 _) = mk 0 := by
    refine Functor.leftDerived_ext LF α W _ _ _ ?_
    ext c
    have hnat := α.naturality (0 : (0 : C) ⟶ c)
    dsimp [mk] at hnat ⊢
    rw [Category.id_comp, Limits.zero_comp, Limits.zero_comp,
      show hD.to_ (L.obj c) = hD.to_ (L.obj 0) ≫ L.map (0 : (0 : C) ⟶ c) from
        hD.eq_of_src _ _, LF.map_comp, Category.assoc, hnat]
    simp
  have h := congrArg (fun t => NatTrans.app t 0) key
  dsimp [mk] at h
  rw [show hD.to_ (0 : D) = 𝟙 (0 : D) from hD.eq_of_src _ _] at h
  rw [IsZero.iff_id_eq_zero]
  simpa using h

end KanExtension
section Truncations

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- Part (4)(c) of Stacks 07K8, lower bound: if `H ^ i (LF (τ_{≤ a + n - 1} E)) ⟶ H ^ i (LF E)`
is an isomorphism whenever `i ≤ a`, then `LF` moves the lower end of the range of degrees in
which `E` lives by at most `n - 1` to the left. Only the vanishing of `LF` on zero objects is
used, so this is stated for an arbitrary functor preserving zero morphisms. -/
private lemma isGE_obj_of_isGE (LF : DerivedCategory A ⥤ DerivedCategory B)
    [LF.PreservesZeroMorphisms] (n : ℕ) (E : DerivedCategory A)
    (h4a : ∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E))))
    (a : ℤ) (hE : E.IsGE a) : (LF.obj E).IsGE (a - (n : ℤ) + 1) := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have : TStructure.t.IsGE E a := hE
  have : TStructure.t.IsGE E (i + (n : ℤ)) :=
    TStructure.t.isGE_of_ge E (i + (n : ℤ)) a (by omega)
  have hz : IsZero ((TStructure.t.truncLE (i + (n : ℤ) - 1)).obj E) :=
    TStructure.t.isZero_truncLE_obj_of_isGE _ (i + (n : ℤ)) (by omega) E
  have := h4a i i le_rfl
  exact (Functor.map_isZero _ (Functor.map_isZero LF hz)).of_iso
    (asIso ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((TStructure.t.truncLEι (i + (n : ℤ) - 1)).app E)))).symm

/-- Part (4)(c) of Stacks 07K8, upper bound: if `H ^ i (LF E) ⟶ H ^ i (LF (τ_{≥ b} E))` is an
isomorphism whenever `b ≤ i`, then `LF` does not move the upper end of the range of degrees in
which `E` lives. Only the vanishing of `LF` on zero objects is used, so this is stated for an
arbitrary functor preserving zero morphisms. -/
private lemma isLE_obj_of_isLE (LF : DerivedCategory A ⥤ DerivedCategory B)
    [LF.PreservesZeroMorphisms] (E : DerivedCategory A)
    (h4b : ∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((TStructure.t.truncGEπ b).app E))))
    (b : ℤ) (hE : E.IsLE b) : (LF.obj E).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have : TStructure.t.IsLE E b := hE
  have : TStructure.t.IsLE E (i - 1) := TStructure.t.isLE_of_le E b (i - 1) (by omega)
  have hz : IsZero ((TStructure.t.truncGE i).obj E) :=
    TStructure.t.isZero_truncGE_obj_of_isLE (i - 1) i (by omega) E
  have := h4b i i le_rfl
  exact (Functor.map_isZero _ (Functor.map_isZero LF hz)).of_iso
    (asIso ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((TStructure.t.truncGEπ i).app E))))

end Truncations

section Route

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
  (LF' : DerivedCategory.Plus Aᵒᵖ ⥤ DerivedCategory.Plus Bᵒᵖ)
  (α' : F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
    DerivedCategory.Plus.Qh ⋙ LF')
  [LF'.IsRightDerivedFunctor α' (HomotopyCategory.Plus.quasiIso Aᵒᵖ)]
  (P : ObjectProperty A)
  (hP : ∀ X : A, P X ↔ (F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
    (HomotopyCategory.Plus.quasiIso Aᵒᵖ)
    ((HomotopyCategory.Plus.singleFunctor Aᵒᵖ 0).obj (Opposite.op X)))
  (hepi : ∀ X : A, ∃ (Y : A) (p : Y ⟶ X) (_ : Epi p), P Y)
  (n : ℕ) (hn : ∀ X : A, IsZero ((DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).obj
    (LF'.obj ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (Opposite.op X)))))

omit [HasDerivedCategory A] [HasDerivedCategory B] in
include F LF' α' P hP hepi n hn in
/-- Stacks 07K7 for `F.op : 𝒜ᵒᵖ ⥤ ℬᵒᵖ`: the hypotheses of Stacks 07K8 for `F` are those of
Stacks 07K7 for `F.op`, with `P.op` the class of right acyclic objects for `F.op`. -/
private lemma op_conclusion_of_isZero_leftDerived :
    (F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso Aᵒᵖ (ComplexShape.up ℤ)) ∧
      (∀ K : CochainComplex Aᵒᵖ ℤ, ∃ (L : CochainComplex Aᵒᵖ ℤ) (f : K ⟶ L) (_ : QuasiIso f),
        ∀ i : ℤ, P (L.X i).unop) ∧
      ∀ (RF : DerivedCategory Aᵒᵖ ⥤ DerivedCategory Bᵒᵖ)
        (α : F.op.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso Aᵒᵖ (ComplexShape.up ℤ))],
        (∀ L : CochainComplex Aᵒᵖ ℤ, (∀ i : ℤ, P (L.X i).unop) →
            IsIso (α.app ((HomotopyCategory.quotient Aᵒᵖ (ComplexShape.up ℤ)).obj L))) ∧
          ∀ E : DerivedCategory Aᵒᵖ,
            (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor Bᵒᵖ i).map
                (RF.map ((TStructure.t.truncLEι a).app E)))) ∧
              (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor Bᵒᵖ i).map
                (RF.map ((TStructure.t.truncGEπ (b - (n : ℤ) + 1)).app E)))) ∧
                (∀ a : ℤ, E.IsGE a → (RF.obj E).IsGE a) ∧
                  ∀ b : ℤ, E.IsLE b → (RF.obj E).IsLE (b + (n : ℤ) - 1) := by
  have := Limits.preservesFiniteLimits_op F
  exact CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived F.op LF' α' P.op
    (fun X ↦ hP X.unop)
    (fun X ↦ by
      obtain ⟨Y, p, _, hY⟩ := hepi X.unop
      exact ⟨Opposite.op Y, p.op, inferInstance, hY⟩)
    n (fun X ↦ hn X.unop)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
include F LF' α' P hP hepi n hn in
/-- Part (2) of Stacks 07K8: every complex is the target of a quasi-isomorphism from a complex
all of whose terms are left acyclic for `F`. This is part (2) of Stacks 07K7 for `F.op`,
transported along the duality `(CochainComplex 𝒜 ℤ)ᵒᵖ ≌ CochainComplex 𝒜ᵒᵖ ℤ`: a
quasi-isomorphism `Kᵒᵖ ⟶ L'` with all terms of `L'` right acyclic for `F.op` is, read in `𝒜`, a
quasi-isomorphism from a complex of left acyclic objects to `K`. -/
private lemma exists_quasiIso_forall_mem (K : CochainComplex A ℤ) :
    ∃ (L : CochainComplex A ℤ) (f : L ⟶ K) (_ : QuasiIso f), ∀ i : ℤ, P (L.X i) := by
  obtain ⟨L', g, hg, hL'⟩ := (op_conclusion_of_isZero_leftDerived F LF' α' P hP hepi n hn).2.1
    ((CochainComplex.opEquivalence A).functor.obj (Opposite.op K))
  have := hg
  have key : (CochainComplex.opEquivalence A).functor.map
      (((CochainComplex.opEquivalence A).unitIso.hom.app (Opposite.op K) ≫
        (CochainComplex.opEquivalence A).inverse.map g).unop).op =
      g ≫ (CochainComplex.opEquivalence A).counitIso.inv.app L' := by
    simp
  refine ⟨_, ((CochainComplex.opEquivalence A).unitIso.hom.app (Opposite.op K) ≫
    (CochainComplex.opEquivalence A).inverse.map g).unop, ?_, fun i ↦ hL' (-i)⟩
  rw [← CochainComplex.quasiIso_opEquivalence_functor_map_iff, key]
  infer_instance

include F LF' α' P hP hepi n hn in
/-- Part (1) of Stacks 07K8: the left derived functor `LF : D(𝒜) ⥤ D(ℬ)` exists. This is
Stacks 06XN, dualized, applied to the resolutions of `exists_quasiIso_forall_mem` and to the
fact that `F` carries a quasi-isomorphism between complexes of left acyclic objects to a
quasi-isomorphism. -/
@[sga "4½ Etat_0 4.2.3.2" "partial"]
private lemma hasLeftDerivedFunctor :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have h := (op_conclusion_of_isZero_leftDerived F LF' α' P hP hepi n hn).1
  rw [Functor.hasRightDerivedFunctor_iff _ DerivedCategory.Qh _] at h
  rw [Functor.hasLeftDerivedFunctor_iff _ DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  refine hasRightKanExtension_of_op (hasLeftKanExtension_of_equivalence
    (homotopyOpEquivalence (C := A)) (derivedOpEquivalence (C := A))
    (derivedOpEquivalence (C := B)) ?_ ?_ h)
  · exact Functor.isoWhiskerLeft _ (homotopyOpEquivalenceFunctorCompQhIso (A := A)).symm ≪≫
      (homotopyOpEquivalence (C := A)).invFunIdAssoc DerivedCategory.Qh
  · exact Functor.isoWhiskerLeft _ (homotopyOpEquivalenceFunctorCompMapQhIso F).symm ≪≫
      (homotopyOpEquivalence (C := A)).invFunIdAssoc _

omit [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ] [PreservesFiniteColimits F] in
/-- A left derived functor of `F` on `D(𝒜)` preserves zero morphisms: it sends the zero object
to a zero object by `isZero_obj_zero_of_isLeftDerivedFunctor`, the functor being derived,
`K ↦ F(K)`, being additive. Preservation of zero morphisms is all that the range-of-degrees
statements need; a left derived functor is in fact a triangulated functor. -/
private lemma preservesZeroMorphisms_of_isLeftDerivedFunctor
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    LF.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    (isZero_obj_zero_of_isLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) LF α).isoZero

include F LF' α' P hP hepi n hn in
/-- Part (3) of Stacks 07K8: a complex all of whose terms are left acyclic for `F` computes
`LF`, i.e. the counit of any left derived functor of `F` on `D(𝒜)` is invertible there. -/
private lemma isIso_app_of_forall_mem
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (L : CochainComplex A ℤ) (hL : ∀ i : ℤ, P (L.X i)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) := by
  have := isRightDerivedFunctor_opLF F LF α
  have h1 := ((op_conclusion_of_isZero_leftDerived F LF' α' P hP hepi n hn).2.2 (opLF LF)
    (opAlphaTransport F LF α)).1
    ((CochainComplex.opEquivalence A).functor.obj (Opposite.op L)) (fun i ↦ hL (-i))
  rwa [isIso_opAlphaTransport_app_iff,
    NatTrans.isIso_app_iff_of_iso α (unopInverseObjQuotientIso L)] at h1

include F LF' α' P hP hepi n hn in
/-- Part (4)(a) of Stacks 07K8: `H ^ i (LF (τ_{≤ a + n - 1} E)) ⟶ H ^ i (LF E)` is an isomorphism
for `i ≤ a`. This is Stacks 05TC, dualized. -/
private lemma isIso_homologyFunctor_map_truncLEι
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E))) := by
  have := isRightDerivedFunctor_opLF F LF α
  obtain ⟨θ, hθ⟩ := exists_truncOpIso (a + (n : ℤ) - 1) E
  have h4b := (((op_conclusion_of_isZero_leftDerived F LF' α' P hP hepi n hn).2.2 (opLF LF)
    (opAlphaTransport F LF α)).2
    ((derivedOpEquivalence (C := A)).functor.obj (Opposite.op E))).2.1 (-a) (-i) (by omega)
  rw [show -a - (n : ℤ) + 1 = -(a + (n : ℤ) - 1) by ring, ← hθ, Functor.map_comp,
    Functor.map_comp] at h4b
  exact (isIso_homologyFunctor_map_opLF_map_iff LF i
    ((TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E)).1
    (IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor Bᵒᵖ (-i)).map
      ((opLF LF).map θ.hom)))

include F LF' α' P hP hepi n hn in
/-- Part (4)(b) of Stacks 07K8: `H ^ i (LF E) ⟶ H ^ i (LF (τ_{≥ b} E))` is an isomorphism for
`i ≥ b`. Represent `E` by a complex `L` of left acyclic objects; then `LF` is computed on `L`
and on its stupid truncations, and the two distinguished triangles
`H ^ b (L) [-b] ⟶ τ_{≤ b} L ⟶ τ_{≤ b - 1} L` and
`0 ⟶ τ_{≤ b} L ⟶ σ_{≤ b} L ⟶ Coim (L ^ b ⟶ L ^ {b + 1}) [-b] ⟶ 0`, together with the vanishing
of `L ^ m F` for `m ≥ n`, identify `H ^ i (LF E)` with `H ^ i (LF (τ_{≥ b} E))` for `i ≥ b`. -/
private lemma isIso_homologyFunctor_map_truncGEπ
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (E : DerivedCategory A) (b i : ℤ) (hb : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((TStructure.t.truncGEπ b).app E))) := by
  have := isRightDerivedFunctor_opLF F LF α
  obtain ⟨θ, hθ⟩ := exists_truncOpIso' b E
  have h4a := (((op_conclusion_of_isZero_leftDerived F LF' α' P hP hepi n hn).2.2 (opLF LF)
    (opAlphaTransport F LF α)).2
    ((derivedOpEquivalence (C := A)).functor.obj (Opposite.op E))).1 (-b) (-i) (by omega)
  refine (isIso_homologyFunctor_map_opLF_map_iff LF i ((TStructure.t.truncGEπ b).app E)).1 ?_
  rw [← hθ, Functor.map_comp, Functor.map_comp]
  infer_instance

end Route

section Solution

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ]

/-- **Stacks 07K8.** Let `F : 𝒜 ⥤ ℬ` be a right exact functor of abelian categories, let
`LF' : D⁺(𝒜ᵒᵖ) ⥤ D⁺(ℬᵒᵖ)` be a right derived functor of `F.op` with unit `α'` — this is the
left derived functor of `F` on the bounded above derived category `D⁻(𝒜)` — and let `P` be the
class of objects which are left acyclic for `F`, i.e. of those `X` such that `Xᵒᵖ[0]` computes
the right derived functor of `F.op` in the sense of Stacks 05SX. Assume that every object of
`𝒜` is a quotient of an object of `P`, and that `L ^ n F = H ^ (-n) (LF (- [0])) = 0` for
some `n : ℕ`. Then

1. the left derived functor `LF : D(𝒜) ⥤ D(ℬ)` exists,
2. every complex is the target of a quasi-isomorphism from a complex with terms in `P`,
3. every complex with terms in `P` computes `LF`, and
4. for every `E` in `D(𝒜)`, `H ^ i (LF (τ_{≤ a + n - 1} E)) ⟶ H ^ i (LF E)` is an isomorphism
   for `i ≤ a`, `H ^ i (LF E) ⟶ H ^ i (LF (τ_{≥ b} E))` is an isomorphism for `i ≥ b`, and `LF`
   shifts the range of degrees in which `E` lives by at most `n - 1` on the left. -/
@[stacks 07K8,
  sga "4½ Etat_0 3.1.9" "(2) left, σ=F-acyclics",
  sga "4½ Etat_0 4.2.3.2" "left case: Lf on D(A)"]
public theorem hasLeftDerivedFunctor_of_isZero_leftDerived
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (LF' : DerivedCategory.Plus Aᵒᵖ ⥤ DerivedCategory.Plus Bᵒᵖ)
    (α' : F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ LF')
    [LF'.IsRightDerivedFunctor α' (HomotopyCategory.Plus.quasiIso Aᵒᵖ)]
    (P : ObjectProperty A)
    (hP : ∀ X : A, P X ↔
      (F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso Aᵒᵖ)
      ((HomotopyCategory.Plus.singleFunctor Aᵒᵖ 0).obj (Opposite.op X)))
    (hepi : ∀ X : A, ∃ (Y : A) (p : Y ⟶ X) (_ : Epi p), P Y)
    (n : ℕ) (hn : ∀ X : A, IsZero ((DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).obj
      (LF'.obj ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (Opposite.op X))))) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      (∀ K : CochainComplex A ℤ, ∃ (L : CochainComplex A ℤ) (f : L ⟶ K) (_ : QuasiIso f),
        ∀ i : ℤ, P (L.X i)) ∧
      ∀ (LF : DerivedCategory A ⥤ DerivedCategory B)
        (α : DerivedCategory.Qh ⋙ LF ⟶
          F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
        [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))],
        (∀ L : CochainComplex A ℤ, (∀ i : ℤ, P (L.X i)) →
            IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))) ∧
          ∀ E : DerivedCategory A,
            (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor B i).map
                (LF.map ((TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E)))) ∧
              (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor B i).map
                (LF.map ((TStructure.t.truncGEπ b).app E)))) ∧
                (∀ a : ℤ, E.IsGE a → (LF.obj E).IsGE (a - (n : ℤ) + 1)) ∧
                  ∀ b : ℤ, E.IsLE b → (LF.obj E).IsLE b := by
  refine ⟨hasLeftDerivedFunctor F LF' α' P hP hepi n hn,
    fun K ↦ exists_quasiIso_forall_mem F LF' α' P hP hepi n hn K, fun LF α _ ↦ ⟨?_, ?_⟩⟩
  · exact fun L hL ↦ isIso_app_of_forall_mem F LF' α' P hP hepi n hn LF α L hL
  · intro E
    have := preservesZeroMorphisms_of_isLeftDerivedFunctor F LF α
    refine ⟨fun a i hi ↦ isIso_homologyFunctor_map_truncLEι F LF' α' P hP hepi n hn LF α E a i hi,
      fun b i hb ↦ isIso_homologyFunctor_map_truncGEπ F LF' α' P hP hepi n hn LF α E b i hb,
      fun a hEa ↦ isGE_obj_of_isGE LF n E
        (fun a' i hi ↦ isIso_homologyFunctor_map_truncLEι F LF' α' P hP hepi n hn LF α E a' i hi)
        a hEa,
      fun b hEb ↦ isLE_obj_of_isLE LF E
        (fun b' i hb ↦ isIso_homologyFunctor_map_truncGEπ F LF' α' P hP hepi n hn LF α E b' i hb)
        b hEb⟩

end Solution

end CategoryTheory.Functor

end
