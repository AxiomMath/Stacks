module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived categories

Let `A` be an abelian category, let `K(A) = HomotopyCategory A (ComplexShape.up ℤ)` be the
homotopy category of cochain complexes in `A`, let `Ac(A)` be its full subcategory of acyclic
complexes and `Qis(A)` its class of quasi-isomorphisms. The derived category `D(A)` is the
localization of `K(A)` at `Qis(A)`, equivalently the Verdier quotient `K(A)/Ac(A)`. This file
proves the four facts that make that description work.

The functor `H⁰ : K(A) ⥤ A` is homological, so `Ac(A) = Ker(H⁰)` is a strictly full saturated
triangulated subcategory of `K(A)` and `Qis(A)` — which is exactly the class of morphisms with
acyclic cone — is a saturated multiplicative system; the kernel of *any* localization of `K(A)`
at `Qis(A)` is `Ac(A)`, and every cohomology functor `Hⁿ` factors through it. The same holds
inside any triangulated subcategory `P` of `K(A)`, in particular inside the bounded homotopy
categories `K⁺(A)`, `K⁻(A)` and `Kᵇ(A)`, and there the localization can be identified: the
functors induced by `Qh : K(A) ⥤ D(A)` exhibit `D⁺(A)`, `D⁻(A)` and `Dᵇ(A)` as the localizations
of `K⁺(A)`, `K⁻(A)` and `Kᵇ(A)` at the quasi-isomorphisms. The input for essential surjectivity
is that a complex whose cohomology vanishes outside `[a, b]` is quasi-isomorphic to a bounded
one, by the canonical truncations.

## Main results

* `HomotopyCategory.isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq`: for a
  localization `L : K(A) ⥤ D` at the quasi-isomorphisms, `Ac(A)` is a strictly full saturated
  triangulated subcategory, `Qis(A)` is a saturated multiplicative system equal to `Ac(A).trW`,
  `Ker(L) = Ac(A)`, and each `Hⁿ` factors through `L`.
* `CochainComplex.exists_quasiIso_square_of_isGE_of_isLE`: a complex whose cohomology vanishes
  outside `[a, b]` fits into a commutative square of quasi-isomorphisms whose other three
  vertices are strictly bounded below by `a`, strictly bounded above by `b`, and both.
* `HomotopyCategory.isSaturated_subcategoryAcyclic_inverseImage_and_quasiIso_and_isLocalization`:
  the first statement for an arbitrary triangulated subcategory `P` of `K(A)` in place of `K(A)`,
  together with the identification of the three bounded localizations
  `K⁺(A) ⥤ D⁺(A)`, `K⁻(A) ⥤ D⁻(A)`, `Kᵇ(A) ⥤ Dᵇ(A)`.

## Implementation notes

`H⁰` is `HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0`, the functor through which
`H⁰ : Comp(A) ⥤ A` factors (`HomotopyCategory.homologyFunctorFactors`), and "homological" is
`CategoryTheory.Functor.IsHomological`: exactness in the middle of the image of every
distinguished triangle ([Stacks, Tag 0148]). Only `n = 0` is recorded, which is the source's
statement; the other `Hⁿ` are its shifts, and Mathlib carries the instance for every `n : ℤ`.

`Ac(A)` is `HomotopyCategory.subcategoryAcyclic A`, defined as the homological kernel of `H⁰`,
and `Qis(A)` is `HomotopyCategory.quasiIso A (ComplexShape.up ℤ)`. "Strictly full" is
`ObjectProperty.IsClosedUnderIsomorphisms`, "saturated" for a subcategory is
`ObjectProperty.IsSaturated` ([Stacks, Tag 05RB]) and "saturated multiplicative system" is
`MorphismProperty.IsSaturated` ([Stacks, Tag 05Q8]). The class corresponding to a subcategory
under [Stacks, Tag 05RL] is `ObjectProperty.trW`, the morphisms sitting in a distinguished
triangle whose third object lies in the subcategory, and the kernel of a functor is
`Functor.kernel`.

The quotient functor is never tied to a construction: both statements are made for an arbitrary
localization `L` at the quasi-isomorphisms, so they cover `DerivedCategory.Qh`, the Verdier
quotient by `Ac(A)` ([Stacks, Tag 05RI]) and every other model. The factorizations of `Hⁿ` are
asserted only to exist, a localization determining them up to a canonical isomorphism
(`CategoryTheory.Localization.liftNatIso`); the isomorphism is wrapped in `Nonempty` because it
is data while the clause is a proposition. Passing from `Hⁱ = H⁰(-⟦i⟧)`, the shape in which
[Stacks, Tag 05RM] provides them, to `Hⁿ` is the shift sequence of `H⁰`, `Functor.isoShift`.

For the truncation square the source's abelian category is weakened to the hypotheses of
Mathlib's truncation API — zero morphisms, a zero object and homology for every short complex —
under which `CochainComplex.isGE_iff_exists_quasiIso_isStrictlyGE` is already stated. Parts (1)
and (2) of [Stacks, Tag 05RV] are available in canonical form (`K.πTruncGE a` and `K.ιTruncLE b`
are quasi-isomorphisms with the prescribed strict bounds), so only the square is recorded; its
witnesses are the canonical truncations `τ_{≥ a}K`, `τ_{≤ b}K` and `τ_{≥ a}τ_{≤ b}K`, and it
commutes by naturality of `πTruncGE`. The vanishing hypotheses are `CochainComplex.IsGE` and
`IsLE` at explicit integers, and the conclusion pins the bounds of the three other vertices to
those same integers, which is sharper than the source's unquantified "bounded".

`K⁺(A)` is `HomotopyCategory.Plus A`; Mathlib has no name for `K⁻(A)` and `Kᵇ(A)`, which are
spelled, as in [Stacks, Tag 05RQ], as the full subcategories on the strict images along the
quotient functor of `CochainComplex.minus A`, resp. of
`CochainComplex.plus A ⊓ CochainComplex.minus A`.
On the derived side all three exist: `DerivedCategory.Plus`, `.Minus`, `.Bounded`, the full
subcategories of `D(A)` on the classes of the canonical t-structure. That the source's comparison
functor `Qis⁺(A)⁻¹K⁺(A) ⥤ D⁺(A)` is an equivalence is stated as `Functor.IsLocalization` for the
functor `K⁺(A) ⥤ D⁺(A)` itself, Mathlib's idiom for it; for `K⁺(A)` that functor is
`DerivedCategory.Plus.Qh`, and in the two other cases, where Mathlib has none, it is quantified
existentially and pinned by an isomorphism `F ⋙ ι ≅ ι ⋙ Qh`, which determines `F` up to a unique
isomorphism because `ι` is fully faithful.

Two facts about the full subcategory attached to `P : ObjectProperty C` are proved in the
generality in which they hold: its shift is computed strictly, `P.ι.obj (X⟦n⟧) = (P.ι.obj X)⟦n⟧`,
and if `Q ≤ P` are triangulated subcategories of `C` then the objects of `P` satisfying `Q` form
a triangulated subcategory of `P.FullSubcategory` — Mathlib's instance instead assumes the
pulled back property closed under isomorphisms, which neither `Kᵇ(A)` nor `HomotopyCategory.plus A`
is, being defined by a condition on a representative rather than up to homotopy equivalence.

For `K⁻(A)` the route Mathlib takes for `K⁺(A)` is followed: essential surjectivity from the
canonical truncations, full faithfulness from Verdier's criterion, the bounded above complexes
being left localizing with respect to the acyclic ones because a morphism from a complex that is
strictly `≤ n` to an acyclic complex `L` factors through the acyclic complex `τ_{≤ n}L`, again
strictly `≤ n`. For `Kᵇ(A)` the source's own deduction from the bounded above case is followed:
`Kᵇ(A)` is the full subcategory of `K⁻(A)` on the bounded below objects, and that subcategory is
right localizing with respect to the acyclic objects of `K⁻(A)`, a morphism from an acyclic
bounded above complex `K` to a complex that is strictly `≥ n` factoring through `τ_{≥ n}K`, which
is acyclic, strictly `≥ n` and still bounded above. The ambient category cannot be taken to be
`K(A)`: a morphism from a bounded complex to an acyclic one need not factor through a bounded
acyclic complex, neither canonical truncation of the target mapping to the target in the required
direction.

## References

* [Stacks project, Tag 05RS](https://stacks.math.columbia.edu/tag/05RS)
* [Stacks project, Tag 05RT](https://stacks.math.columbia.edu/tag/05RT)
* [Stacks project, Tag 05RV](https://stacks.math.columbia.edu/tag/05RV)
* [Stacks project, Tag 05RW](https://stacks.math.columbia.edu/tag/05RW)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w w' v v' u u'

/-! ### `H⁰` on the homotopy category is a homological functor -/

-- Mathlib's instance is the source's statement, for every `Hⁿ` and not only for `H⁰`.
add_to_stacks 05RS "Hⁿ : K(A) ⥤ A is homological"
  HomotopyCategory.instIsHomologicalIntUpHomologyFunctor

/-! ### The acyclic complexes and the quasi-isomorphisms in the homotopy category -/

namespace CategoryTheory.Functor

section

variable {C : Type u} {A : Type u'} [Category.{v} C] [Category.{v'} A]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C] [Abelian A]

/-- The kernel of a homological functor `H : C ⥤ A` on a triangulated category is a saturated
subcategory ([Stacks, Tag 05RB]): this is the clause of [Stacks, Tag 05RM] applied to the
canonical localization of `C` at `Ker(H).trW`, which the statement of 05RM asks for but this
conclusion does not mention. -/
private lemma isSaturated_homologicalKernel (H : C ⥤ A) [H.IsHomological] :
    H.homologicalKernel.IsSaturated :=
  (Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift H
    H.homologicalKernel.trW.Q).1.2.2

/-- The morphisms of a triangulated category whose cone lies in the kernel of a homological
functor `H` form a saturated multiplicative system ([Stacks, Tag 05Q8]): again the clause of
[Stacks, Tag 05RM] for the canonical localization of `C` at `Ker(H).trW`. -/
@[sga "4½ Etat_0 2.4.1" "partial"]
private lemma isSaturated_trW_homologicalKernel (H : C ⥤ A) [H.IsHomological] :
    H.homologicalKernel.trW.IsSaturated :=
  (Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift H
    H.homologicalKernel.trW.Q).2.1.1

end

end CategoryTheory.Functor

namespace HomotopyCategory

section

variable {A : Type u} {D : Type u'} [Category.{v} A] [Category.{v'} D] [Abelian A]

/-- The acyclic complexes form a saturated (thick) subcategory of `K(A)`: `Ac(A)` is the kernel
of the homological functor `H⁰`. -/
private lemma isSaturated_subcategoryAcyclic :
    (subcategoryAcyclic A).IsSaturated :=
  CategoryTheory.Functor.isSaturated_homologicalKernel
    (homologyFunctor A (ComplexShape.up ℤ) 0)

/-- The quasi-isomorphisms form a saturated multiplicative system on `K(A)`: they are the
morphisms whose cone lies in `Ac(A) = Ker(H⁰)`. -/
private lemma isSaturated_quasiIso :
    (quasiIso A (ComplexShape.up ℤ)).IsSaturated := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  exact CategoryTheory.Functor.isSaturated_trW_homologicalKernel
    (homologyFunctor A (ComplexShape.up ℤ) 0)

/-- A localization of `K(A)` at the quasi-isomorphisms is a localization at `Ac(A).trW`, the
class of morphisms with acyclic cone, the two classes being equal. -/
private lemma isLocalization_trW_subcategoryAcyclic
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (quasiIso A (ComplexShape.up ℤ))] :
    L.IsLocalization (subcategoryAcyclic A).trW := by
  rw [← quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- Every cohomology functor `Hⁿ : K(A) ⥤ A` factors through a localization `L` of `K(A)` at the
quasi-isomorphisms: `H⁰(-⟦n⟧)` does so by [Stacks, Tag 05RM], and `H⁰(-⟦n⟧) ≅ Hⁿ` because the
shift sequence of `H⁰` on `K(A)` is `n ↦ Hⁿ`. -/
@[sga "4½ Etat_0 3.1.6" "partial"]
private lemma exists_lift_homologyFunctor
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (quasiIso A (ComplexShape.up ℤ))] (n : ℤ) :
    ∃ H : D ⥤ A, Nonempty (L ⋙ H ≅ homologyFunctor A (ComplexShape.up ℤ) n) := by
  have : L.IsLocalization
      (homologyFunctor A (ComplexShape.up ℤ) 0).homologicalKernel.trW :=
    isLocalization_trW_subcategoryAcyclic L
  obtain ⟨H, ⟨e⟩⟩ :=
    (Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift
      (homologyFunctor A (ComplexShape.up ℤ) 0) L).2.2.2 n
  exact ⟨H, ⟨e ≪≫ (homologyFunctor A (ComplexShape.up ℤ) 0).isoShift n⟩⟩

/-- **Stacks 05RT.** Let `A` be an abelian category, let `K(A)` be the homotopy category of
cochain complexes in `A` and let `L : K(A) ⥤ D` be a localization of `K(A)` at the class of
quasi-isomorphisms. Then:

* the subcategory `Ac(A)` of acyclic complexes is a strictly full saturated triangulated
  subcategory of `K(A)`;
* the saturated multiplicative system corresponding to it under [Stacks, Tag 05RL], namely the
  class of morphisms whose cone is acyclic, is the class `Qis(A)` of quasi-isomorphisms;
* the kernel of `L` is `Ac(A)`;
* every cohomology functor `Hⁿ : K(A) ⥤ A` factors through `L`. -/
@[stacks 05RT,
  sga "4½ Etat_0 2.4.1" "case D = K(A), H = H^0",
  sga "4½ Etat_0 3.1.6" "H^i factors via D(A)",
  sga "4½ Etat_0 1.2.3" "(A)",
  sga "4½ Etat_0 4.2.3" "partial"]
public theorem isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq
    (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    ((HomotopyCategory.subcategoryAcyclic A).IsClosedUnderIsomorphisms ∧
        (HomotopyCategory.subcategoryAcyclic A).IsTriangulated ∧
        (HomotopyCategory.subcategoryAcyclic A).IsSaturated) ∧
      ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsSaturated ∧
        (HomotopyCategory.subcategoryAcyclic A).trW =
          HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      L.kernel = HomotopyCategory.subcategoryAcyclic A ∧
      ∀ n : ℤ, ∃ H : D ⥤ A,
        Nonempty (L ⋙ H ≅ HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n) := by
  have := isSaturated_subcategoryAcyclic (A := A)
  have := isLocalization_trW_subcategoryAcyclic L
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    ⟨isSaturated_quasiIso, (quasiIso_eq_trW_subcategoryAcyclic A).symm⟩,
    ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self.2 (subcategoryAcyclic A) L,
    exists_lift_homologyFunctor L⟩

end

end HomotopyCategory

/-! ### Complexes with bounded cohomology are quasi-isomorphic to bounded ones -/

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [CategoryWithHomology C] {K L : CochainComplex C ℤ}

omit [HasZeroObject C] in
/-- The degrees in which the cohomology of a cochain complex vanishes are unchanged by a
quasi-isomorphism: this is `HomologicalComplex.isSupported_iff_of_quasiIso` at the embedding
of `[a, ∞)`, of which `CochainComplex.IsGE a` is the `IsSupported` condition. -/
private lemma isGE_iff_of_quasiIso' (φ : K ⟶ L) [QuasiIso φ] (a : ℤ) :
    K.IsGE a ↔ L.IsGE a :=
  HomologicalComplex.isSupported_iff_of_quasiIso φ (ComplexShape.embeddingUpIntGE a)

/-- The canonical truncation above `a` of a quasi-isomorphism is a quasi-isomorphism. -/
private lemma quasiIso_truncGEMap' (φ : K ⟶ L) [QuasiIso φ] (a : ℤ) :
    QuasiIso (CochainComplex.truncGEMap φ a) :=
  (CochainComplex.quasiIso_truncGEMap_iff φ a).2 fun i _ ↦ (quasiIso_iff φ).1 ‹_› i

/-- **Stacks 05RV (3).** Let `K` be a cochain complex in an abelian category — or, as stated
here, in any category with zero morphisms, a zero object and homology — whose cohomology
vanishes in degrees `< a` and in degrees `> b`. Then there is a commutative square of
quasi-isomorphisms
```
  M ⟶ N
  ↓    ↓
  K ⟶ L
```
with `L` concentrated in degrees `≥ a`, `M` in degrees `≤ b`, and `N` in degrees `a ≤ n ≤ b`,
i.e. `N` bounded. Parts (1) and (2) of the source are the horizontal, resp. left vertical, map
alone, and are the quasi-isomorphisms `K.πTruncGE a`, resp. `K.ιTruncLE b`. -/
@[stacks 05RV]
public theorem exists_quasiIso_square_of_isGE_of_isLE
    (K : CochainComplex C ℤ) (a b : ℤ) [K.IsGE a] [K.IsLE b] :
    ∃ (L M N : CochainComplex C ℤ) (f : K ⟶ L) (g : M ⟶ K) (u : M ⟶ N) (v : N ⟶ L)
      (_ : QuasiIso f) (_ : QuasiIso g) (_ : QuasiIso u) (_ : QuasiIso v)
      (_ : L.IsStrictlyGE a) (_ : M.IsStrictlyLE b) (_ : N.IsStrictlyGE a)
      (_ : N.IsStrictlyLE b), g ≫ f = u ≫ v := by
  have : (K.truncLE b).IsGE a := (isGE_iff_of_quasiIso' (K.ιTruncLE b) a).2 inferInstance
  exact ⟨K.truncGE a, K.truncLE b, (K.truncLE b).truncGE a, K.πTruncGE a, K.ιTruncLE b,
    (K.truncLE b).πTruncGE a, CochainComplex.truncGEMap (K.ιTruncLE b) a, inferInstance,
    inferInstance, inferInstance, quasiIso_truncGEMap' _ a, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (HomologicalComplex.πTruncGE_naturality (K.ιTruncLE b) _).symm⟩

end

end CochainComplex

/-! ### The bounded homotopy categories and the bounded derived categories -/

namespace CategoryTheory.ObjectProperty

/-- The shift on the full subcategory attached to `P : ObjectProperty C` is computed strictly:
`P.ι.obj (X⟦n⟧)` is `(P.ι.obj X)⟦n⟧`, not merely isomorphic to it. -/
private lemma ι_obj_shift {C : Type*} [Category C] [HasShift C ℤ] (P : ObjectProperty C)
    [P.IsStableUnderShift ℤ] (X : P.FullSubcategory) (n : ℤ) :
    P.ι.obj (X⟦n⟧) = (P.ι.obj X)⟦n⟧ := by
  with_unfolding_all rfl

/-- A triangulated subcategory of a triangulated subcategory: if `Q ≤ P` are triangulated
subcategories of a pretriangulated category `C`, then the objects of `P` satisfying `Q` form a
triangulated subcategory of `P.FullSubcategory`. This is Mathlib's
`ObjectProperty.instIsTriangulatedInverseImage` for the inclusion `P.ι`, with the hypothesis that
`Q` be closed under isomorphisms traded for `Q ≤ P`: what that hypothesis is used for is to
correct the object produced by `Q.ext_of_isTriangulatedClosed₂'` up to isomorphism, and `Q ≤ P`
makes that object an object of `P.FullSubcategory`, where the correcting isomorphism lives. -/
private lemma isTriangulated_inverseImage_ι {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : ObjectProperty C) [P.IsTriangulated] [Q.IsTriangulated] (hQP : Q ≤ P) :
    (Q.inverseImage P.ι).IsTriangulated := by
  obtain ⟨Z, hZ, hZQ⟩ := Q.exists_prop_of_containsZero
  have : (Q.inverseImage P.ι).ContainsZero :=
    ⟨⟨Z, hQP _ hZQ⟩, IsZero.of_full_of_faithful_of_isZero P.ι _ hZ, hZQ⟩
  have : (Q.inverseImage P.ι).IsStableUnderShift ℤ :=
    ⟨fun n ↦ ⟨fun X hX ↦ by
      rw [ObjectProperty.prop_shift_iff, ObjectProperty.prop_inverseImage_iff, ι_obj_shift]
      exact Q.le_shift n _ hX⟩⟩
  have : (Q.inverseImage P.ι).IsTriangulatedClosed₂ :=
    ⟨fun T hT h₁ h₃ ↦ by
      obtain ⟨W, hW, ⟨e⟩⟩ := Q.ext_of_isTriangulatedClosed₂' (P.ι.mapTriangle.obj T)
        (P.ι.map_distinguished T hT) h₁ h₃
      exact ⟨⟨W, hQP _ hW⟩, hW, ⟨(ObjectProperty.fullyFaithfulι P).preimageIso e⟩⟩⟩
  exact { }

end CategoryTheory.ObjectProperty

namespace HomotopyCategory

section

variable {A : Type u} {D : Type u'} [Category.{v} A] [Category.{v'} D] [Abelian A]

set_option backward.defeqAttrib.useBackward true in
/-- The quasi-isomorphisms of a triangulated subcategory `P` of `K(A)` are the morphisms whose
cone is acyclic. This is `HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic` for `P`, and
generalizes `HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW`. -/
private lemma quasiIso_inverseImage_eq_trW
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ))) [P.IsTriangulated] :
    (quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι
      = ((subcategoryAcyclic A).inverseImage P.ι).trW := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := distinguished_cocone_triangle f
  have := (subcategoryAcyclic A).trW_iff_of_distinguished _ (P.ι.map_distinguished _ mem)
  rw [← quasiIso_eq_trW_subcategoryAcyclic] at this
  rwa [dsimp% ((subcategoryAcyclic A).inverseImage P.ι).trW_iff_of_distinguished _ mem]

/-- The acyclic objects of a triangulated subcategory `P` of `K(A)` are the kernel of the
homological functor `H⁰` restricted to `P`. -/
private lemma homologicalKernel_eq
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ))) [P.IsTriangulated] :
    (P.ι ⋙ homologyFunctor A (ComplexShape.up ℤ) 0).homologicalKernel
      = (subcategoryAcyclic A).inverseImage P.ι := by
  ext X
  exact forall_congr' fun n ↦ Iso.isZero_iff
    ((homologyFunctor A (ComplexShape.up ℤ) 0).mapIso ((P.ι.commShiftIso n).app X))

/-- A localization of a triangulated subcategory `P` of `K(A)` at the quasi-isomorphisms is a
localization at the class of morphisms with acyclic cone. -/
private lemma isLocalization_trW_inverseImage
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ))) [P.IsTriangulated]
    (L : P.FullSubcategory ⥤ D)
    [L.IsLocalization ((quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι)] :
    L.IsLocalization ((subcategoryAcyclic A).inverseImage P.ι).trW := by
  rw [← quasiIso_inverseImage_eq_trW]
  infer_instance

/-- **Clause 1 of Stacks 05RW.** For a triangulated subcategory `P` of `K(A)`, the acyclic
objects of `P` form a strictly full saturated triangulated subcategory, the quasi-isomorphisms
of `P` are the saturated multiplicative system it defines, and the kernel of a localization of
`P` at them is the subcategory of acyclic objects. This is [Stacks, Tag 05RM] for the
restriction to `P` of the homological functor `H⁰`, followed by [Stacks, Tag 05RL]. -/
private lemma isSaturated_and_kernel_eq
    (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ))) [P.IsTriangulated]
    (L : P.FullSubcategory ⥤ D)
    [L.IsLocalization ((quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι)] :
    (((subcategoryAcyclic A).inverseImage P.ι).IsClosedUnderIsomorphisms ∧
        ((subcategoryAcyclic A).inverseImage P.ι).IsTriangulated ∧
        ((subcategoryAcyclic A).inverseImage P.ι).IsSaturated) ∧
      (((quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι).IsSaturated ∧
        ((quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι).IsCompatibleWithTriangulation ∧
        ((subcategoryAcyclic A).inverseImage P.ι).trW =
          (quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι) ∧
      L.kernel = (subcategoryAcyclic A).inverseImage P.ι := by
  have hQis := quasiIso_inverseImage_eq_trW P
  have hker := homologicalKernel_eq P
  have hAc := isLocalization_trW_inverseImage P L
  have hH : L.IsLocalization
      (P.ι ⋙ homologyFunctor A (ComplexShape.up ℤ) 0).homologicalKernel.trW := by
    rwa [hker]
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, -⟩, -, -⟩ :=
    CategoryTheory.Functor.isSaturated_homologicalKernel_and_mem_trW_iff_and_exists_lift
      (P.ι ⋙ homologyFunctor A (ComplexShape.up ℤ) 0) L
  rw [hker] at h1 h2 h3 h4 h5
  rw [hQis]
  refine ⟨⟨h1, h2, h3⟩, ⟨h4, h5, rfl⟩, ?_⟩
  have := h1
  have := h2
  have := h3
  exact CategoryTheory.ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self.2 _ L

/-- The strict image of a property `P` of complexes contains the class of a complex `K` if and
only if `K` itself satisfies `P`, a class in the homotopy category having at most one
representative. This is `HomotopyCategory.plus_quotient_obj_iff` for an arbitrary `P`. -/
private lemma strictMap_quotient_obj_iff' {C : Type*} [Category* C] [Preadditive C] {ι : Type*}
    {c : ComplexShape ι} (P : ObjectProperty (HomologicalComplex C c))
    (K : HomologicalComplex C c) :
    P.strictMap (quotient C c) ((quotient C c).obj K) ↔ P K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  simp only [ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

variable (A) in
/-- `K⁻(A)`, the objects of `K(A)` represented by a bounded above complex; the mirror of
`HomotopyCategory.plus`. -/
private abbrev Kminus : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (CochainComplex.minus A).strictMap (quotient A (ComplexShape.up ℤ))

variable (A) in
/-- `Kᵇ(A)`, the objects of `K(A)` represented by a bounded complex. -/
private abbrev Kbounded : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  (CochainComplex.plus A ⊓ CochainComplex.minus A).strictMap (quotient A (ComplexShape.up ℤ))

/-- The bounded objects of `K(A)` are those that are both bounded below and bounded above. -/
private lemma Kbounded_iff (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    Kbounded A X ↔ plus A X ∧ Kminus A X := by
  obtain ⟨K : CochainComplex _ _, rfl⟩ := quotient_obj_surjective X
  constructor
  · intro hX
    obtain ⟨h₁, h₂⟩ := (strictMap_quotient_obj_iff' _ K).1 hX
    exact ⟨(plus_quotient_obj_iff K).2 h₁, (strictMap_quotient_obj_iff' _ K).2 h₂⟩
  · intro ⟨h₁, h₂⟩
    exact (strictMap_quotient_obj_iff' _ K).2
      ⟨(plus_quotient_obj_iff K).1 h₁, (strictMap_quotient_obj_iff' _ K).1 h₂⟩

/-- The bounded complexes are bounded above. -/
private lemma Kbounded_le_Kminus : Kbounded A ≤ Kminus A :=
  fun X hX ↦ ((Kbounded_iff X).1 hX).2

/-- A morphism out of a complex that is strictly `≤ n` factors through the canonical truncation
`τ_{≤ n}` of its target ([Stacks, Tag 05RV]), the complex level analogue of
`CategoryTheory.Triangulated.TStructure.liftTruncLE`. -/
private lemma exists_comp_ιTruncLE {K L : CochainComplex A ℤ} (n : ℤ) [K.IsStrictlyLE n]
    (φ : K ⟶ L) : ∃ ψ : K ⟶ L.truncLE n, ψ ≫ L.ιTruncLE n = φ :=
  ⟨inv (K.ιTruncLE n) ≫ CochainComplex.truncLEMap φ n, by
    rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]⟩

/-- A morphism into a complex that is strictly `≥ n` factors through the canonical truncation
`τ_{≥ n}` of its source ([Stacks, Tag 05RV]), the complex level analogue of
`CategoryTheory.Triangulated.TStructure.descTruncGE`. -/
private lemma exists_πTruncGE_comp {K L : CochainComplex A ℤ} (n : ℤ) [L.IsStrictlyGE n]
    (φ : K ⟶ L) : ∃ ψ : K.truncGE n ⟶ L, K.πTruncGE n ≫ ψ = φ :=
  ⟨CochainComplex.truncGEMap φ n ≫ inv (L.πTruncGE n), by
    rw [← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]⟩

/-- `K⁻(A)` is left `Ac(A)`-localizing in the sense of Verdier: a morphism from a bounded above
complex to an acyclic complex factors through an acyclic bounded above complex, namely through
the canonical truncation `τ_{≤ n}` of the target. This is the mirror of Mathlib's
`(HomotopyCategory.plus A).IsVerdierRightLocalizing (subcategoryAcyclic A)`. -/
private lemma isVerdierLeftLocalizing_Kminus :
    (Kminus A).IsVerdierLeftLocalizing (subcategoryAcyclic A) where
  fac {K L} φ hK hL := by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := quotient_obj_surjective L
    obtain ⟨n, _⟩ := (strictMap_quotient_obj_iff' _ K).1 hK
    obtain ⟨φ, rfl⟩ := (quotient _ _).map_surjective φ
    rw [quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    obtain ⟨ψ, hψ⟩ := exists_comp_ιTruncLE n φ
    exact ⟨(quotient _ _).obj (L.truncLE n), (quotient _ _).map ψ,
      (quotient _ _).map (L.ιTruncLE n),
      (strictMap_quotient_obj_iff' _ _).2 ⟨n, inferInstance⟩,
      (quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hL.truncLE _),
      by rw [← Functor.map_comp, hψ]⟩

/-- The bounded objects of `K⁻(A)` are right `Ac⁻(A)`-localizing in the sense of Verdier: a
morphism from an acyclic bounded above complex `K` to a bounded complex `L` which is strictly
`≥ n` factors through the canonical truncation `τ_{≥ n}K`, which is acyclic, strictly `≥ n`, and
still bounded above. -/
private lemma isVerdierRightLocalizing_plus_inverseImage_Kminus :
    ((plus A).inverseImage (Kminus A).ι).IsVerdierRightLocalizing
      ((subcategoryAcyclic A).inverseImage (Kminus A).ι) where
  fac {X Y} f hX hY := by
    obtain ⟨X, hXm⟩ := X
    obtain ⟨Y, hYm⟩ := Y
    obtain ⟨K : CochainComplex _ _, rfl⟩ := quotient_obj_surjective X
    obtain ⟨L : CochainComplex _ _, rfl⟩ := quotient_obj_surjective Y
    obtain ⟨m, _⟩ := (strictMap_quotient_obj_iff' _ K).1 hXm
    obtain ⟨n, _⟩ := (plus_quotient_obj_iff L).1 hY
    replace hX : subcategoryAcyclic A ((quotient A (ComplexShape.up ℤ)).obj K) := hX
    rw [quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hX
    obtain ⟨φ, hφ⟩ := (quotient A (ComplexShape.up ℤ)).map_surjective f.hom
    obtain ⟨ψ, hψ⟩ := exists_πTruncGE_comp n φ
    refine ⟨⟨(quotient _ _).obj (K.truncGE n),
        (strictMap_quotient_obj_iff' _ _).2 ⟨m, inferInstance⟩⟩,
      ObjectProperty.homMk ((quotient _ _).map (K.πTruncGE n)),
      ObjectProperty.homMk ((quotient _ _).map ψ),
      (plus_quotient_obj_iff _).2 ⟨n, inferInstance⟩,
      (quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hX.truncGE _),
      ObjectProperty.hom_ext _ ?_⟩
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.homMk_hom, ← Functor.map_comp, hψ, hφ]

/-- `Kᵇ(A)` is a triangulated subcategory of `K⁻(A)`: it is `Kᵇ(A) ≤ K⁻(A)`
([Stacks, Tag 05RQ]) seen inside `K⁻(A)`. -/
private lemma isTriangulated_plus_inverseImage_Kminus [(Kminus A).IsTriangulated] :
    ((plus A).inverseImage (Kminus A).ι).IsTriangulated := by
  have := (isTriangulated_minus_bounded A).2
  have h : (plus A).inverseImage (Kminus A).ι = (Kbounded A).inverseImage (Kminus A).ι := by
    ext X
    exact ⟨fun hX ↦ (Kbounded_iff _).2 ⟨hX, X.property⟩, fun hX ↦ ((Kbounded_iff _).1 hX).1⟩
  rw [h]
  exact CategoryTheory.ObjectProperty.isTriangulated_inverseImage_ι _ _ Kbounded_le_Kminus

/-- `Kᵇ(A)` is the full subcategory of `K⁻(A)` on the bounded below objects. -/
private def KboundedInKminusEquiv :
    ((plus A).inverseImage (Kminus A).ι).FullSubcategory ≌ (Kbounded A).FullSubcategory where
  functor := ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ ObjectProperty.ι _)
    (fun X ↦ (Kbounded_iff _).2 ⟨X.property, X.obj.property⟩)
  inverse := ObjectProperty.lift _
    (ObjectProperty.lift _ (ObjectProperty.ι _) (fun Y ↦ ((Kbounded_iff _).1 Y.property).2))
    (fun Y ↦ ((Kbounded_iff _).1 Y.property).1)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

section

variable [HasDerivedCategory.{w} A]

/-- A lift of `DerivedCategory.Qh` to a full subcategory `Q` of `D(A)` is essentially surjective
as soon as every object of `Q` is isomorphic to the image of a complex whose class in `K(A)`
satisfies `P`. -/
private lemma essSurj_lift {P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ))}
    {Q : ObjectProperty (DerivedCategory A)} (hPQ : ∀ ⦃X⦄, P X → Q (DerivedCategory.Qh.obj X))
    (h : ∀ Y : Q.FullSubcategory, ∃ K : CochainComplex A ℤ,
      P ((quotient A (ComplexShape.up ℤ)).obj K) ∧
        Nonempty (Y.obj ≅ DerivedCategory.Q.obj K)) :
    (Q.lift (P.ι ⋙ DerivedCategory.Qh) (fun X ↦ hPQ X.property)).EssSurj where
  mem_essImage Y := by
    obtain ⟨K, hK, ⟨e⟩⟩ := h Y
    exact ⟨⟨_, hK⟩, ⟨Q.ι.preimageIso ((DerivedCategory.quotientCompQhIso A).app K ≪≫ e.symm)⟩⟩

/-- The image under `Qh` of a bounded above complex lies in `D⁻(A)`. -/
private lemma mem_minus_Qh_obj {X : HomotopyCategory A (ComplexShape.up ℤ)} (hX : Kminus A X) :
    DerivedCategory.TStructure.t.minus (DerivedCategory.Qh.obj X) := by
  obtain ⟨K : CochainComplex _ _, rfl⟩ := quotient_obj_surjective X
  obtain ⟨n, _⟩ := (strictMap_quotient_obj_iff' _ K).1 hX
  exact ⟨n, DerivedCategory.TStructure.t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso A).symm.app K) n⟩

/-- The image under `Qh` of a bounded below complex lies in `D⁺(A)`. -/
private lemma mem_plus_Qh_obj {X : HomotopyCategory A (ComplexShape.up ℤ)} (hX : plus A X) :
    DerivedCategory.TStructure.t.plus (DerivedCategory.Qh.obj X) := by
  obtain ⟨K : CochainComplex _ _, rfl⟩ := quotient_obj_surjective X
  obtain ⟨n, _⟩ := (plus_quotient_obj_iff K).1 hX
  exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso
    ((DerivedCategory.quotientCompQhIso A).symm.app K) n⟩

/-- The image under `Qh` of a bounded complex lies in `Dᵇ(A)`. -/
private lemma mem_bounded_Qh_obj {X : HomotopyCategory A (ComplexShape.up ℤ)}
    (hX : Kbounded A X) :
    DerivedCategory.TStructure.t.bounded (DerivedCategory.Qh.obj X) :=
  ⟨mem_plus_Qh_obj ((Kbounded_iff X).1 hX).1, mem_minus_Qh_obj ((Kbounded_iff X).1 hX).2⟩

/-- The functor `K⁻(A) ⥤ D⁻(A)` induced by `DerivedCategory.Qh`, the mirror of
`DerivedCategory.Plus.Qh`. -/
private noncomputable def QhMinus : (Kminus A).FullSubcategory ⥤ DerivedCategory.Minus A :=
  DerivedCategory.TStructure.t.minus.lift ((Kminus A).ι ⋙ DerivedCategory.Qh)
    (fun X ↦ mem_minus_Qh_obj X.property)

/-- The functor `K⁻(A) ⥤ D⁻(A)` is induced by `DerivedCategory.Qh`, the mirror of
`DerivedCategory.Plus.QhCompιIsoιCompQh`. -/
private noncomputable def QhMinusCompιIso :
    QhMinus (A := A) ⋙ DerivedCategory.Minus.ι ≅ (Kminus A).ι ⋙ DerivedCategory.Qh := Iso.refl _

private instance essSurj_QhMinus : (QhMinus (A := A)).EssSurj :=
  essSurj_lift (P := Kminus A) (Q := DerivedCategory.TStructure.t.minus)
    (fun _ hX ↦ mem_minus_Qh_obj hX) (fun Y ↦ by
      obtain ⟨n, hn⟩ := Y.property
      have : DerivedCategory.TStructure.t.IsLE Y.obj n := hn
      obtain ⟨K, _, ⟨e⟩⟩ := Y.obj.exists_iso_Q_obj_of_isLE n
      exact ⟨K, (strictMap_quotient_obj_iff' _ K).2 ⟨n, inferInstance⟩, ⟨e⟩⟩)

/-- **Clause 2 of Stacks 05RW.** The functor `K⁻(A) ⥤ D⁻(A)` induced by `Qh` is a localization
at the quasi-isomorphisms. -/
private lemma isLocalization_QhMinus :
    (QhMinus (A := A)).IsLocalization
      ((quasiIso A (ComplexShape.up ℤ)).inverseImage (Kminus A).ι) := by
  have := (isTriangulated_minus_bounded A).1
  have := isVerdierLeftLocalizing_Kminus (A := A)
  rw [quasiIso_inverseImage_eq_trW]
  exact ((Kminus A).triangulatedLocalizerMorphism
    (subcategoryAcyclic A)).isLocalization_of_isLocalizedFullyFaithful QhMinusCompιIso.symm

/-- The functor `Kᵇ(A) ⥤ Dᵇ(A)` induced by `DerivedCategory.Qh`, the mirror of
`DerivedCategory.Plus.Qh`. -/
private noncomputable def QhBounded : (Kbounded A).FullSubcategory ⥤ DerivedCategory.Bounded A :=
  DerivedCategory.TStructure.t.bounded.lift ((Kbounded A).ι ⋙ DerivedCategory.Qh)
    (fun X ↦ mem_bounded_Qh_obj X.property)

/-- The functor `Kᵇ(A) ⥤ Dᵇ(A)` is induced by `DerivedCategory.Qh`. -/
private noncomputable def QhBoundedCompιIso :
    QhBounded (A := A) ⋙ DerivedCategory.Bounded.ι ≅ (Kbounded A).ι ⋙ DerivedCategory.Qh :=
  Iso.refl _

private instance essSurj_QhBounded : (QhBounded (A := A)).EssSurj :=
  essSurj_lift (P := Kbounded A) (Q := DerivedCategory.TStructure.t.bounded)
    (fun _ hX ↦ mem_bounded_Qh_obj hX) (fun Y ↦ by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Y.property
      have : DerivedCategory.TStructure.t.IsGE Y.obj a := ha
      have : DerivedCategory.TStructure.t.IsLE Y.obj b := hb
      obtain ⟨K, _, _, ⟨e⟩⟩ := Y.obj.exists_iso_Q_obj_of_isGE_of_isLE a b
      exact ⟨K, (strictMap_quotient_obj_iff' _ K).2 ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩, ⟨e⟩⟩)

/-- **Clause 3 of Stacks 05RW.** The functor `Kᵇ(A) ⥤ Dᵇ(A)` induced by `Qh` is a localization
at the quasi-isomorphisms.

The source deduces this from the bounded above case: it suffices that
`Qisᵇ(A)⁻¹Kᵇ(A) ⥤ Qis⁻(A)⁻¹K⁻(A)` be fully faithful, and the argument given for `K⁺(A)` applies
to complexes that are already bounded above. That argument is Verdier's criterion for the
bounded objects inside the ambient category `K⁻(A)`. -/
private lemma isLocalization_QhBounded :
    (QhBounded (A := A)).IsLocalization
      ((quasiIso A (ComplexShape.up ℤ)).inverseImage (Kbounded A).ι) := by
  have := (isTriangulated_minus_bounded A).1
  have := isTriangulated_plus_inverseImage_Kminus (A := A)
  have := isVerdierRightLocalizing_plus_inverseImage_Kminus (A := A)
  have := isLocalization_QhMinus (A := A)
  have h₂ := isLocalization_trW_inverseImage (Kminus A) (QhMinus (A := A))
  have h₁ : (KboundedInKminusEquiv.functor ⋙ QhBounded (A := A)).IsLocalization
      (((subcategoryAcyclic A).inverseImage (Kminus A).ι).inverseImage
        ((plus A).inverseImage (Kminus A).ι).ι).trW :=
    (ObjectProperty.triangulatedLocalizerMorphism _ _).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := QhMinus) (F := ObjectProperty.ιOfLE (fun _ hX ↦ hX.2)) (Iso.refl _)
  refine Functor.IsLocalization.of_equivalence_source
    (KboundedInKminusEquiv.functor ⋙ QhBounded (A := A))
    (((subcategoryAcyclic A).inverseImage (Kminus A).ι).inverseImage
      ((plus A).inverseImage (Kminus A).ι).ι).trW
    _ _ KboundedInKminusEquiv ?_ ?_ (Iso.refl _)
  · intro X Y f hf
    rw [ObjectProperty.inverseImage_trW_iff, ObjectProperty.inverseImage_trW_iff,
      ← quasiIso_eq_trW_subcategoryAcyclic] at hf
    exact MorphismProperty.le_isoClosure _ _ hf
  · intro X Y f hf
    rw [MorphismProperty.inverseImage_iff] at hf
    have h : IsIso (DerivedCategory.Bounded.ι.map ((QhBounded (A := A)).map f)) :=
      Localization.inverts DerivedCategory.Qh
        (quasiIso A (ComplexShape.up ℤ)) _ hf
    exact isIso_of_reflects_iso _ DerivedCategory.Bounded.ι

/-- **Stacks 05RW.** Let `A` be an abelian category. For every triangulated subcategory `P` of
the homotopy category `K(A)` — in particular for `K⁺(A)`, `K⁻(A)` and `Kᵇ(A)` — the acyclic
objects of `P` form a strictly full saturated triangulated subcategory `Ac_P` of `P`, the
quasi-isomorphisms `Qis_P` of `P` form a saturated multiplicative system compatible with the
triangulation which is the class `Ac_P.trW` corresponding to `Ac_P` under [Stacks, Tag 05RL],
and the kernel of any localization `L` of `P` at `Qis_P` is `Ac_P`. Moreover:

1. `DerivedCategory.Plus.Qh : K⁺(A) ⥤ D⁺(A)` is a localization at `Qis⁺(A)`, so that
   `K⁺(A)/Ac⁺(A) = Qis⁺(A)⁻¹K⁺(A) ⥤ D⁺(A)` is an equivalence;
2. the functor `K⁻(A) ⥤ D⁻(A)` induced by `Qh` is a localization at `Qis⁻(A)`;
3. the functor `Kᵇ(A) ⥤ Dᵇ(A)` induced by `Qh` is a localization at `Qisᵇ(A)`. -/
@[stacks 05RW]
public theorem isSaturated_subcategoryAcyclic_inverseImage_and_quasiIso_and_isLocalization :
    (∀ (P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ))) [P.IsTriangulated]
        (L : P.FullSubcategory ⥤ D)
        [L.IsLocalization ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι)],
      (((HomotopyCategory.subcategoryAcyclic A).inverseImage P.ι).IsClosedUnderIsomorphisms ∧
          ((HomotopyCategory.subcategoryAcyclic A).inverseImage P.ι).IsTriangulated ∧
          ((HomotopyCategory.subcategoryAcyclic A).inverseImage P.ι).IsSaturated) ∧
        (((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι).IsSaturated ∧
          ((HomotopyCategory.quasiIso A
            (ComplexShape.up ℤ)).inverseImage P.ι).IsCompatibleWithTriangulation ∧
          ((HomotopyCategory.subcategoryAcyclic A).inverseImage P.ι).trW =
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage P.ι) ∧
        L.kernel = (HomotopyCategory.subcategoryAcyclic A).inverseImage P.ι) ∧
    (DerivedCategory.Plus.Qh (C := A)).IsLocalization (HomotopyCategory.Plus.quasiIso A) ∧
    (∃ F : ((CochainComplex.minus A).strictMap
          (HomotopyCategory.quotient A (ComplexShape.up ℤ))).FullSubcategory ⥤
        DerivedCategory.Minus A,
      Nonempty (F ⋙ DerivedCategory.Minus.ι ≅
          ((CochainComplex.minus A).strictMap
            (HomotopyCategory.quotient A (ComplexShape.up ℤ))).ι ⋙ DerivedCategory.Qh) ∧
        F.IsLocalization ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
          ((CochainComplex.minus A).strictMap
            (HomotopyCategory.quotient A (ComplexShape.up ℤ))).ι)) ∧
    (∃ F : ((CochainComplex.plus A ⊓ CochainComplex.minus A).strictMap
          (HomotopyCategory.quotient A (ComplexShape.up ℤ))).FullSubcategory ⥤
        DerivedCategory.Bounded A,
      Nonempty (F ⋙ DerivedCategory.Bounded.ι ≅
          ((CochainComplex.plus A ⊓ CochainComplex.minus A).strictMap
            (HomotopyCategory.quotient A (ComplexShape.up ℤ))).ι ⋙ DerivedCategory.Qh) ∧
        F.IsLocalization ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
          ((CochainComplex.plus A ⊓ CochainComplex.minus A).strictMap
            (HomotopyCategory.quotient A (ComplexShape.up ℤ))).ι)) :=
  ⟨fun P _ L _ ↦ isSaturated_and_kernel_eq P L, inferInstance,
    ⟨QhMinus, ⟨QhMinusCompιIso⟩, isLocalization_QhMinus⟩,
    ⟨QhBounded, ⟨QhBoundedCompιIso⟩, isLocalization_QhBounded⟩⟩

end

end

end HomotopyCategory

/-! ### The bounded derived categories, described by vanishing of cohomology -/

section Bounded

open Triangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **Stacks 05RU.** The objects of the bounded below derived category `D^{+}(A)`, the full
subcategory `DerivedCategory.Plus C` of `D(A)` on the object property `plus` of the canonical
t-structure, are exactly the `X` with `H^n(X) = 0` for all `n ≪ 0`. -/
@[stacks 05RU "Ob(D^+(A)) = {X | H^n(X) = 0 for all n ≪ 0}", sga "6 I 1.1.5" "D^+ degree condition"]
public theorem plus_iff (X : DerivedCategory C) :
    (TStructure.t (C := C)).plus X ↔
      ∃ N : ℤ, ∀ n ≤ N, IsZero ((homologyFunctor C n).obj X) :=
  ⟨fun ⟨m, hm⟩ => ⟨m - 1, fun n hn => (isGE_iff X m).1 hm n (by omega)⟩,
    fun ⟨N, hN⟩ => ⟨N + 1, (isGE_iff X (N + 1)).2 fun i hi => hN i (by omega)⟩⟩

/-- **Stacks 05RU.** The objects of the bounded above derived category `D^{-}(A)`, the full
subcategory `DerivedCategory.Minus C` of `D(A)` on the object property `minus` of the canonical
t-structure, are exactly the `X` with `H^n(X) = 0` for all `n ≫ 0`. -/
@[stacks 05RU "Ob(D^-(A)) = {X | H^n(X) = 0 for all n ≫ 0}", sga "6 I 1.1.5" "D^- degree condition"]
public theorem minus_iff (X : DerivedCategory C) :
    (TStructure.t (C := C)).minus X ↔
      ∃ N : ℤ, ∀ n, N ≤ n → IsZero ((homologyFunctor C n).obj X) :=
  ⟨fun ⟨m, hm⟩ => ⟨m + 1, fun n hn => (isLE_iff X m).1 hm n (by omega)⟩,
    fun ⟨N, hN⟩ => ⟨N - 1, (isLE_iff X (N - 1)).2 fun i hi => hN i (by omega)⟩⟩

/-- **Stacks 05RU.** The objects of the bounded derived category `D^b(A)`, the full subcategory
`DerivedCategory.Bounded C` of `D(A)` on the object property `bounded` of the canonical
t-structure, are exactly the `X` with `H^n(X) = 0` for all `|n| ≫ 0`: a single bound in the
source's condition, against the two unrelated bounds of `bounded = plus ⊓ minus`. -/
@[stacks 05RU "Ob(D^b(A)) = {X | H^n(X) = 0 for all |n| ≫ 0}",
  sga "6 I 1.1.5" "D^b degree condition"]
public theorem bounded_iff (X : DerivedCategory C) :
    (TStructure.t (C := C)).bounded X ↔
      ∃ N : ℤ, ∀ n, N ≤ |n| → IsZero ((homologyFunctor C n).obj X) := by
  rw [TStructure.bounded, ObjectProperty.prop_inf_iff, plus_iff, minus_iff]
  constructor
  · rintro ⟨⟨N₁, h₁⟩, ⟨N₂, h₂⟩⟩
    refine ⟨max (-N₁) N₂, fun n hn => ?_⟩
    have := le_max_left (-N₁) N₂
    have := le_max_right (-N₁) N₂
    rcases abs_cases n with ⟨_, _⟩ | ⟨_, _⟩
    · exact h₂ n (by omega)
    · exact h₁ n (by omega)
  · rintro ⟨N, hN⟩
    refine ⟨⟨-|N|, fun n hn => hN n ?_⟩, ⟨|N|, fun n hn => hN n ?_⟩⟩ <;>
      rcases abs_cases n with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases N with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

end DerivedCategory

add_to_stacks 05RU "D(A), the derived category of an abelian category" DerivedCategory
add_to_sga "4 XVII 2.1.1" "more general" DerivedCategory
add_to_sga "4½ Etat_0 3.1.1" DerivedCategory
add_to_sga "4½ Etat_0 3.1.3" DerivedCategory
add_to_sga "4½ Rapport 4.1" DerivedCategory
add_to_sga "5 I App.1.1" DerivedCategory
add_to_sga "5 III 1.1" "more general" DerivedCategory
add_to_sga "5 IIIB 5.1" DerivedCategory
add_to_sga "5 IIIB 6.1" "more general" DerivedCategory
add_to_sga "6 I 1.1.5" "the derived fiber D(C_X)" DerivedCategory
add_to_sga "6 II 2.2.10" DerivedCategory
add_to_sga "6 II 2.3.2" DerivedCategory
add_to_sga "6 III 1.1" DerivedCategory
add_to_sga "6 III 5.1" DerivedCategory
add_to_sga "6 IV 2.1" "partial" DerivedCategory
add_to_stacks 05RU "H^0 : D(A) ⥤ A, and its shifts H^n" DerivedCategory.homologyFunctor
add_to_sga "4½ Etat_0 3.1.6" DerivedCategory.homologyFunctor
add_to_stacks 05RU "D^+(A), the bounded below derived category" DerivedCategory.Plus
add_to_sga "4 Vbis 1.3.8" DerivedCategory.Plus
add_to_sga "4 Vbis 2.4.1" DerivedCategory.Plus
add_to_sga "4½ Etat_0 3.1.1" DerivedCategory.Plus
add_to_sga "4½ Etat_0 3.1.3" DerivedCategory.Plus
add_to_sga "4½ Rapport 4.1" DerivedCategory.Plus
add_to_stacks 05RU "D^-(A), the bounded above derived category" DerivedCategory.Minus
add_to_sga "4½ Etat_0 3.1.2" DerivedCategory.Minus
add_to_sga "4½ Etat_0 3.1.3" DerivedCategory.Minus
add_to_sga "4½ Rapport 4.1" DerivedCategory.Minus
add_to_sga "6 I 1.1.5" "the fiber D⁻(C_X)" DerivedCategory.Minus
add_to_stacks 05RU "D^b(A), the bounded derived category" DerivedCategory.Bounded
add_to_sga "4½ Etat_0 3.1.2" DerivedCategory.Bounded
add_to_sga "4½ Etat_0 3.1.3" DerivedCategory.Bounded

end Bounded

end
