module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedSumIsProduct
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.AlgebraicGeometry.Duality.SpaltensteinCriterion.QuasicoherentTruncationConvergence
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Upper cohomological bounds under a total right derived functor

Let `X` be a scheme, let `F` be an additive functor out of the `𝒪_X`-modules which commutes with
countable products, and let `(RF, α)` be a total right derived functor of `F` on the whole
unbounded derived category `D(𝒪_X)`. Suppose the higher right derived functors `R^pF` vanish on
quasi-coherent modules in every degree `p ≥ N`. Then on a complex with quasi-coherent cohomology
`RF` raises an upper cohomological bound by at most `N - 1`, and the canonical comparison
`H^i(RF(E)) ⟶ H^i(RF(τ_{≥ b - N + 1}E))` is an isomorphism for `i ≥ b`.

Together with the two statements of
`StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/DerivedBounds.lean` — the lower bound
and the comparison `H^i(RF(τ_{≤ a}E)) ⟶ H^i(RF(E))` for `i ≤ a`, neither of which needs any
vanishing hypothesis — this completes the four assertions of [Stacks, Tag 08D4].

The argument is the source's `E = R\lim \tau_{\geq -n}E`. A complex with quasi-coherent
cohomology *is* the derived limit of the tower of its canonical truncations from below
([Stacks, Tag 08D3], proved as `AlgebraicGeometry.isIso_to_isDerivedLimit_truncGETower`);
`RF` carries that derived limit to a derived limit ([Stacks, Tag 08U1]); each truncation
`τ_{≥ -n}E` is bounded, so the bound for it follows by induction on its amplitude from the case
of a single module, where it is the vanishing hypothesis; and a derived limit of a tower with a
uniform upper bound `c` has upper bound `c + 1`, the countable products of the target being
exact. The two truncation comparisons are then read off the canonical truncation triangle
through the long exact homology sequence.

## Main results

* `CategoryTheory.Pretriangulated.isDerivedLimit_of_iso` — being a derived limit of a tower is
  invariant under isomorphism of the limit object.
* `Stacks.DerivedLimit.truncGETowerCone` — the canonical map `E ⟶ ∏ₙ τ_{≥ -n}E`, and
  `Stacks.DerivedLimit.truncGETowerCone_comp_diff`, that it is annihilated by the difference of
  the projections.
* `AlgebraicGeometry.isDerivedLimit_truncGETower` — **[Stacks, Tag 08D3]** in the form the limit
  argument consumes: a complex of `𝒪_X`-modules with quasi-coherent cohomology is a derived limit
  of the tower of its truncations from below.
* `Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj` — the upper bound for a single
  module, directly from the vanishing of the higher right derived functors.
* `Stacks.SmallDerivedCategory.isLE_obj_of_isGE_of_isLE` — the upper bound for a bounded object,
  by induction on its amplitude.
* `Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit` — a derived limit of a tower with a
  uniform upper bound `b` has upper bound `b + 1`.
* `Stacks.SmallDerivedCategory.isGE_of_isDerivedLimit` — the lower-bound companion: a derived
  limit of a tower with a uniform *lower* bound `b` has lower bound `b`, with no degree lost and
  with no exactness hypothesis on the products.
* `AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` — **[Stacks, Tag
  08D4], part (3), the upper
  bound.**
* `isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus`, in the
  `AlgebraicGeometry` namespace —
  **[Stacks, Tag 08D4], part (2).**

## Implementation notes

**The model of the derived category.** [Stacks, Tag 08D3] is available only at
`CategoryTheory.HasDerivedCategory.standard`, which is the model its own input — the local
convergence criterion of [Stacks, Tag 0D6P] — is stated at. The two statements of this file that
mention a scheme are therefore at that model as well, and the module category is spelled
`SheafOfModules X.ringCatSheaf`, which is the spelling of 08D3; the two statements of
`DerivedBounds.lean` are at a free `HasDerivedCategory` instance and in the
`AlgebraicGeometry.Scheme.Modules` spelling, so they specialize to this one. The two spellings
are definitionally equal but carry separately declared `Category`, `Preadditive` and `Abelian`
instances, which is why neither file is phrased in both.

Everything that does not mention a scheme is stated for an arbitrary abelian target category with
exact countable products, not for `AddCommGrpCat`: the application of this material to the derived
Spec–Γ equivalence needs it for the *module*-valued derived global sections
`AlgebraicGeometry.derivedGlobalSectionsOver`.

**One private copy superseded.**
`Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι` is a general statement about the
canonical `t`-structure of a derived category which the repository already holds once,
`private`, as `homologyMap_truncLEι_isIso` in
`StacksFrontier/Homology/DerivedComplete/CompletionSequencesComparison.lean`. It is restated here
rather than made public there because that copy carries transparency pragmas; one public copy
should eventually replace the two. The statement for the truncation from below is not restated
here: it is the public `DerivedCategory.isIso_homologyFunctor_map_truncGEπ` of
`StacksFrontier/CategoryTheory/Triangulated/OperationsOnFullSubcategories.lean`, which this file
imports. The same remark is recorded from the other side in the
implementation notes of `StacksFrontier/AlgebraicGeometry/DerivedQCoh/Inclusion.lean` for
`derivedHomologyCommIso`.

**No `backward` pragmas.** A direct proof of this material rewrites
`(Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩` into `(τ_{≥ -n}).obj E` inside a composite,
which is ill-typed at `implicit` transparency and needs
`backward.isDefEq.respectTransparency false`. The cure here is
`Stacks.DerivedLimit.truncGEπ_comp_truncGETower_map`: the one definitional step is isolated in a
lemma proved by `exact`, which elaborates at default transparency, and every consumer rewrites
with that lemma instead of with the unfolding.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CategoryTheory.Pretriangulated

/-- **Being a derived limit is invariant under isomorphism of the limit object.** If `K` is a
derived limit of the tower `F` and `K ≅ K'`, then `K'` is one too: transport the distinguished
triangle presenting `K` along the isomorphism. -/
theorem isDerivedLimit_of_iso {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] {K K' : D}
    (hK : IsDerivedLimit F K) (e : K ≅ K') : IsDerivedLimit F K' := by
  obtain ⟨p, δ, h⟩ := hK
  refine ⟨e.inv ≫ p, δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom, ?_⟩
  let T := Triangle.mk p
    (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) δ
  let T' := Triangle.mk (e.inv ≫ p)
    (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
    (δ ≫ (shiftFunctor D (1 : ℤ)).map e.hom)
  exact isomorphic_distinguished T h T'
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _)
      (by simp [T, T']) (by simp [T, T']) (by simp [T, T']))

end CategoryTheory.Pretriangulated

namespace Stacks.DerivedLimit

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- **The transition maps of the truncation tower are compatible with the truncation maps.**
Composing `E ⟶ τ_{≥ -(n+1)}E` with the transition map `τ_{≥ -(n+1)}E ⟶ τ_{≥ -n}E` of
`Stacks.DerivedLimit.truncGETower` gives `E ⟶ τ_{≥ -n}E`.

This is `CategoryTheory.Triangulated.TStructure.π_natTransTruncGEOfLE_app` read through
`Stacks.DerivedLimit.truncGETower_map_homOfLE_succ`; it is stated separately because the
identification of the tower's transition map with the comparison of truncations is the one
definitional step in the material below that a rewrite cannot perform. -/
theorem truncGEπ_comp_truncGETower_map (E : DerivedCategory A) (n : ℕ) :
    (DerivedCategory.TStructure.t.truncGEπ (-((n + 1 : ℕ) : ℤ))).app E ≫
        (truncGETower A E).map (homOfLE (Nat.le_succ n)).op =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := by
  rw [truncGETower_map_homOfLE_succ]
  exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ (by omega) E

variable (E : DerivedCategory A) [HasProduct fun n : ℕ ↦ (truncGETower A E).obj ⟨n⟩]

/-- The canonical map `E ⟶ ∏ₙ τ_{≥ -n}E` into the product of the truncation tower, whose `n`-th
component is the canonical map `E ⟶ τ_{≥ -n}E`. This is the cone that
[Stacks, Tag 08D3] asserts to exhibit `E` as the derived limit of the tower. -/
def truncGETowerCone : E ⟶ ∏ᶜ fun n : ℕ ↦ (truncGETower A E).obj ⟨n⟩ :=
  Pi.lift fun n ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E

/-- The `n`-th component of `Stacks.DerivedLimit.truncGETowerCone E` is the canonical map
`E ⟶ τ_{≥ -n}E`. -/
@[reassoc (attr := simp)]
theorem truncGETowerCone_comp_π (n : ℕ) :
    truncGETowerCone E ≫ Pi.π (fun n : ℕ ↦ (truncGETower A E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E :=
  Pi.lift_comp_π _ n

/-- **The canonical cone is annihilated by the difference of the projections.** This is the
cocycle condition which lets the canonical map `E ⟶ ∏ₙ τ_{≥ -n}E` be lifted through the
distinguished triangle presenting the derived limit of the tower. -/
theorem truncGETowerCone_comp_diff :
    truncGETowerCone E ≫ (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (truncGETower A E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ (truncGETower A E).obj ⟨n⟩) (n + 1) ≫
            (truncGETower A E).map (homOfLE (Nat.le_succ n)).op) = 0 := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [zero_comp, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, truncGETowerCone_comp_π,
    truncGETowerCone_comp_π_assoc]
  exact sub_eq_zero_of_eq (truncGEπ_comp_truncGETower_map E n).symm

end Stacks.DerivedLimit

namespace Stacks.SmallDerivedCategory

/-! ### The canonical truncations and an object property -/

section Truncation

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- **The canonical map from a truncation from above is invertible on cohomology below the cut.**
Dually to `DerivedCategory.isIso_homologyFunctor_map_truncGEπ`: the third vertex of
`τ_{≤ a}E ⟶ E ⟶ τ_{≥ a+1}E` lives in degrees `≥ a + 1`. -/
theorem isIso_homologyFunctor_map_truncLEι (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E
  have ht := DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E
  have : T.obj₃.IsGE (a + 1) := by
    show ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E).IsGE (a + 1)
    infer_instance
  have hz := T.obj₃.isZero_of_isGE (a + 1) i (by omega)
  have hz' := T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_epi_shift_map_mor₁_iff T ht i).2
      (hz.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_mono_shift_map_mor₁_iff
      T ht (i - 1) i (by omega)).2 (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor A i).map T.mor₁)

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]

/-- **A truncation from above inherits a property of the cohomology objects.** Above the cut the
cohomology of `τ_{≤ a}E` is that of `E`, below it the cohomology vanishes. -/
theorem prop_homologyFunctor_truncLE_obj (E : DerivedCategory A)
    (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E)) (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj E)) := by
  by_cases hi : i ≤ a
  · have := isIso_homologyFunctor_map_truncLEι E a i hi
    exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E))).symm (hE i)
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ a i (by omega))

/-- **A truncation from below inherits a property of the cohomology objects.** Dually to
`Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj`. -/
theorem prop_homologyFunctor_truncGE_obj (E : DerivedCategory A)
    (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E)) (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E)) := by
  by_cases hi : a ≤ i
  · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ a i hi E
    exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E))) (hE i)
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isGE _ a i (by omega))

end Truncation

/-! ### The upper bound on a single module and on a bounded object -/

section Single

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ]
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))

include hcomp in
/-- **The upper bound at a single module.** If the higher right derived functors `R^pF` vanish on
`M` in every degree `p > d`, then `R` carries the complex `M[-n]` concentrated in degree `n` to an
object living in degrees `≤ n + d`.

In degree zero this is the definition of `Functor.rightDerivedPlus` once `R` is identified with
the bounded below right derived functor of `F`, which
`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus` does; the general
degree follows because `R` commutes with the shift. -/
theorem isLE_obj_singleFunctor_obj (M : A) (d : ℤ)
    (hM : ∀ p : ℤ, d < p → IsZero ((F.rightDerivedPlus p).obj M)) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    F R β hcomp ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 (by
      show ((DerivedCategory.singleFunctor A 0).obj M).IsGE 0
      infer_instance)
  have hzero : (R.obj ((DerivedCategory.singleFunctor A 0).obj M)).IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro p hp
    exact (hM p hp).of_iso ((DerivedCategory.homologyFunctor B p).mapIso e)
  have hs : ((R.obj ((DerivedCategory.singleFunctor A 0).obj M))⟦-n⟧).IsLE (n + d) :=
    DerivedCategory.TStructure.t.isLE_shift
      (R.obj ((DerivedCategory.singleFunctor A 0).obj M)) d (-n) (n + d) (by omega)
  have hs' : DerivedCategory.TStructure.t.IsLE
      ((R ⋙ shiftFunctor (DerivedCategory B) (-n)).obj
        ((DerivedCategory.singleFunctor A 0).obj M)) (n + d) := hs
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((R.commShiftIso (-n)).app ((DerivedCategory.singleFunctor A 0).obj M)).symm ≪≫
      R.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M))
    (n + d)

end Single

section Bounded

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
  (d : ℤ)
  (hSingle : ∀ M, P M → ∀ n : ℤ,
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))

omit [P.ContainsZero] [R.CommShift ℤ] [R.IsTriangulated] in
include hSingle in
/-- **The upper bound at an object concentrated in one degree.** Such an object is a single
module placed in that degree, so this is the hypothesis `hSingle`. -/
theorem isLE_obj_of_isGE_of_isLE_self (E : DerivedCategory A)
    (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E))
    (b : ℤ) [E.IsGE b] [E.IsLE b] : (R.obj E).IsLE (b + d) := by
  obtain ⟨M, ⟨e⟩⟩ := E.exists_iso_singleFunctor_obj_of_isGE_of_isLE b
  have hM : P M := P.prop_of_iso
    ((DerivedCategory.homologyFunctor A b).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app M) (hE b)
  have := hSingle M hM b
  exact DerivedCategory.TStructure.t.isLE_of_iso (R.mapIso e.symm) (b + d)

/-- The upper bound `c ≥ b + d` for `R(E)` follows from the one for `R(τ_{≤ b-1}E)`, the third
vertex of the truncation triangle being concentrated in degree `b`. -/
private theorem isLE_obj_of_isLE_obj_truncLE
    (hSingle : ∀ M, P M → ∀ n : ℤ,
      (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))
    (E : DerivedCategory A) (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E))
    (b c : ℤ) (hc : b + d ≤ c) [E.IsLE b]
    (h₁ : (R.obj ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)).IsLE c) :
    (R.obj E).IsLE c := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E
  have ht := DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E
  have h₃ : (R.obj T.obj₃).IsLE c := by
    have : T.obj₃.IsGE b := by
      show ((DerivedCategory.TStructure.t.truncGE b).obj E).IsGE b
      infer_instance
    have : T.obj₃.IsLE b := by
      show ((DerivedCategory.TStructure.t.truncGE b).obj E).IsLE b
      infer_instance
    have := isLE_obj_of_isGE_of_isLE_self P R d hSingle T.obj₃
      (prop_homologyFunctor_truncGE_obj P E hE b) b
    exact DerivedCategory.TStructure.t.isLE_of_le _ (b + d) c hc
  exact DerivedCategory.TStructure.t.isLE₂ (R.mapTriangle.obj T) (R.map_distinguished T ht) c
    h₁ h₃

include hSingle in
/-- **The upper bound at a bounded object.** If `E` lives in degrees `[a, b]` and all its
cohomology objects satisfy `P`, then `R(E)` lives in degrees `≤ b + d`.

Induction on the amplitude `b - a`: the canonical truncation triangle
`τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` has a third vertex concentrated in degree `b`, handled by
`Stacks.SmallDerivedCategory.isLE_obj_of_isGE_of_isLE_self`, and a first vertex of smaller
amplitude whose cohomology still satisfies `P` by
`Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj`. -/
@[sga "6 I 2.13" "special case"]
theorem isLE_obj_of_isGE_of_isLE (E : DerivedCategory A)
    (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a b : ℤ) [E.IsGE a] [E.IsLE b] : (R.obj E).IsLE (b + d) := by
  suffices ∀ (m : ℕ) (E : DerivedCategory A)
      (_ : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E))
      (a b : ℤ), b < a + m → E.IsGE a → E.IsLE b → (R.obj E).IsLE (b + d) from
    this (b - a + 1).toNat E hE a b (by omega) inferInstance inferInstance
  intro m
  induction m with
  | zero =>
      intro E _ a b hab hGE hLE
      have hz : IsZero E := (IsZero.iff_id_eq_zero E).2
        (DerivedCategory.TStructure.t.zero (𝟙 E) b a (by omega))
      exact DerivedCategory.TStructure.t.isLE_of_iso (R.map_isZero hz).isoZero.symm (b + d)
  | succ m ih =>
      intro E hE a b hab hGE hLE
      have h₁ := ih _ (prop_homologyFunctor_truncLE_obj P E hE (b - 1)) a (b - 1) (by omega)
        inferInstance inferInstance
      exact isLE_obj_of_isLE_obj_truncLE P R d hSingle E hE b (b + d) le_rfl
        (DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + d) (b + d) (by omega))

end Bounded

/-! ### The upper bound at a derived limit -/

section Products

variable {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  [HasProductsOfShape ℕ (DerivedCategory B)]

/-- **A countable product of objects with a common upper bound has that upper bound.** The
cohomology of the product is the product of the cohomologies, the countable products of `B` being
exact ([Stacks, Tag 07KC] part (3)). -/
theorem isLE_pi (E : ℕ → DerivedCategory B) (b : ℤ) (hE : ∀ n, (E n).IsLE b) :
    (∏ᶜ E).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor E i
  apply IsZero.of_iso (Y := ∏ᶜ fun n ↦ (DerivedCategory.homologyFunctor B i).obj (E n))
  · rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro n
    exact (DerivedCategory.isZero_of_isLE (E n) b i hi).eq_of_tgt _ _
  · exact asIso (piComparison (DerivedCategory.homologyFunctor B i) E)

/-- **A derived limit of a tower with a common upper bound `b` has upper bound `b + 1`.** The
derived limit sits in a distinguished triangle whose other two vertices are the product of the
tower and its shift by `-1`, so it inherits the bound of the product up to one degree. -/
theorem isLE_of_isDerivedLimit (E : ℕᵒᵖ ⥤ DerivedCategory B) (L : DerivedCategory B)
    (hL : IsDerivedLimit E L) (b : ℤ) (hE : ∀ n : ℕ, (E.obj ⟨n⟩).IsLE b) :
    L.IsLE (b + 1) := by
  obtain ⟨p, δ, hT⟩ := hL
  have hp := isLE_pi (fun n : ℕ ↦ E.obj ⟨n⟩) b hE
  let T := Triangle.mk p (Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op) δ
  have hshift : ((∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)⟦(-1 : ℤ)⟧).IsLE (b + 1) :=
    DerivedCategory.TStructure.t.isLE_shift _ b (-1) (b + 1) (by omega)
  have : T.invRotate.obj₃.IsLE b := hp
  exact DerivedCategory.TStructure.t.isLE₂ T.invRotate (inv_rot_of_distTriang T hT) (b + 1)
    hshift (DerivedCategory.TStructure.t.isLE_of_le _ b (b + 1) (by omega))

end Products

/-! ### The lower bound at a derived limit -/

section ProductsBelow

/-- **A derived limit of a tower with a common lower bound `b` has that same lower bound.** The
derived limit sits in a distinguished triangle whose other two vertices are the product of the
tower and the shift of that product by `-1`, so it inherits the bound of the product.

No degree is lost here, in contrast to `Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit`: the
vertex which is shifted is shifted away from the bound, to `b + 1`. The exactness of the
countable products of the target is not needed either, a product of objects lying in degrees
`≥ b` lying in degrees `≥ b` for any `t`-structure
(`Stacks.ShiftedSum.isGE_of_isLimit_fan`, through the orthogonality criterion rather than
through the cohomology of the product).

A *uniform* bound on the tower is what makes this true: a derived limit of objects each of which
is bounded below need not be bounded below. -/
theorem isGE_of_isDerivedLimit {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (E : ℕᵒᵖ ⥤ DerivedCategory B) [HasProduct fun n : ℕ ↦ E.obj ⟨n⟩] (L : DerivedCategory B)
    (hL : IsDerivedLimit E L) (b : ℤ) (hE : ∀ n : ℕ, (E.obj ⟨n⟩).IsGE b) :
    L.IsGE b := by
  obtain ⟨p, δ, hT⟩ := hL
  have hp : (∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩).IsGE b :=
    Stacks.ShiftedSum.isGE_of_isLimit_fan (fun n : ℕ ↦ E.obj ⟨n⟩) _
      (productIsProduct fun n : ℕ ↦ E.obj ⟨n⟩) b hE
  let T := Triangle.mk p (Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op) δ
  have hshift : ((∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)⟦(-1 : ℤ)⟧).IsGE (b + 1) :=
    DerivedCategory.TStructure.t.isGE_shift _ b (-1) (b + 1) (by omega)
  have h₁ : T.invRotate.obj₁.IsGE (b + 1) := hshift
  have h₃ : T.invRotate.obj₃.IsGE b := hp
  exact DerivedCategory.TStructure.t.isGE₂ T.invRotate (inv_rot_of_distTriang T hT) b
    (DerivedCategory.TStructure.t.isGE_of_ge _ b (b + 1) (by omega)) h₃

end ProductsBelow

end Stacks.SmallDerivedCategory

/-! ### Stacks 08D4 for a scheme -/

namespace AlgebraicGeometry

open Stacks.DerivedLimit Stacks.SmallDerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- Quasi-coherence holds of a zero module: the free module on the empty index set is zero and is
quasi-coherent. -/
theorem containsZero_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero := by
  refine ⟨SheafOfModules.free (R := X.ringCatSheaf) (PEmpty : Type u), ?_, inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ (fun n ↦ n.elim)

/-- **[Stacks, Tag 08D3] as a derived limit.** An object of `D(𝒪_X)` whose cohomology sheaves are
all quasi-coherent is a derived limit of the tower `n ↦ τ_{≥ -n}E` of its canonical truncations
from below.

This repackages `AlgebraicGeometry.isIso_to_isDerivedLimit_truncGETower`, which says that the
canonical map from `E` into any derived limit of the tower is invertible: a derived limit `L`
exists because every `τ_{≥ -n}E` is bounded below ([Stacks, Tag 0BK7]), the canonical cone
`Stacks.DerivedLimit.truncGETowerCone` lifts through the triangle presenting `L` by
`Stacks.DerivedLimit.truncGETowerCone_comp_diff`, and that lift is invertible, so `E` is a
derived limit too. -/
theorem isDerivedLimit_truncGETower (X : Scheme.{u})
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent) :
    IsDerivedLimit (truncGETower (SheafOfModules.{u} X.ringCatSheaf) E) E := by
  obtain ⟨hprod, L, hL⟩ :=
    DerivedCategory.exists_isDerivedLimit_of_forall_isGE
      (truncGETower (SheafOfModules.{u} X.ringCatSheaf) E)
      (fun n ↦ ⟨-(n : ℤ), by
        rw [truncGETower_obj]
        infer_instance⟩)
  obtain ⟨p, δ, hT⟩ := hL
  obtain ⟨c, hc⟩ := (Triangle.mk p _ δ).coyoneda_exact₂ hT
    (truncGETowerCone E) (truncGETowerCone_comp_diff E)
  change truncGETowerCone E = c ≫ p at hc
  have hciso : IsIso c := isIso_to_isDerivedLimit_truncGETower X E hE L c p δ hT
    (fun n ↦ by rw [← Category.assoc, ← hc]; exact truncGETowerCone_comp_π E n)
  exact isDerivedLimit_of_iso _ ⟨p, δ, hT⟩ (asIso c).symm

section Bounds

variable (X : Scheme.{u}) {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  (F : SheafOfModules.{u} X.ringCatSheaf ⥤ B) [F.Additive]
  [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤ DerivedCategory B)
  (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor alpha
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))]

include F alpha in
/-- **Stacks Project, Tag 08D4, part (3), the upper bound.** Let `X` be a scheme, let `F` be an
additive functor out of the `𝒪_X`-modules which preserves countable products, and let `RF` be a
total right derived functor of `F` on `D(𝒪_X)`. Suppose the higher right derived functors `R^pF`
vanish on every quasi-coherent module in every degree `p ≥ N`. If an object `E` of `D(𝒪_X)` has
quasi-coherent cohomology sheaves and lives in degrees `≤ b`, then `RF(E)` lives in degrees
`≤ b + N - 1`.

The canonical truncation triangle `τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` reduces the claim to its third
vertex, concentrated in degree `b` and so covered by the vanishing hypothesis, and to its first
vertex, where the bound `b - 1 + N` — one worse, which is why the triangle is used — is supplied
by the `E = R\lim \tau_{\geq -n}E` argument: `E` is the derived limit of its truncations from
below ([Stacks, Tag 08D3]), `RF` carries that derived limit to a derived limit
([Stacks, Tag 08U1]), each `RF(τ_{≥ -n}E)` lives in degrees `≤ b + N - 1` because `τ_{≥ -n}E` is
bounded, and a derived limit of such a tower lives in degrees `≤ b + N`. -/
@[stacks 08D4 "part (3), upper bound"]
theorem isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus (N : ℕ)
    (hRF : ∀ M : SheafOfModules.{u} X.ringCatSheaf, M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + (N : ℤ) - 1) := by
  have hP := containsZero_isQuasicoherent X
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  have hcomp := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
    F RF alpha Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
  have : HasProductsOfShape ℕ (DerivedCategory B) :=
    Stacks.DerivedProducts.hasProductsOfShape_nat
  have hSingle : ∀ M : SheafOfModules.{u} X.ringCatSheaf,
      SheafOfModules.isQuasicoherent X.ringCatSheaf M → ∀ n : ℤ,
      (RF.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} X.ringCatSheaf) n).obj M)).IsLE (n + ((N : ℤ) - 1)) :=
    fun M hM n ↦ isLE_obj_singleFunctor_obj F RF alpha hcomp M ((N : ℤ) - 1)
      (fun p hp ↦ hRF M hM p (by omega)) n
  have hweak : ∀ (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)),
      (∀ i : ℤ, SheafOfModules.isQuasicoherent X.ringCatSheaf
          ((DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) i).obj K)) →
      ∀ c : ℤ, K.IsLE c → (RF.obj K).IsLE (c + (N : ℤ)) := by
    intro K hK c hc
    obtain ⟨p, hp⟩ := isDerivedLimit_truncGETower X K hK
    obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
      F RF alpha (truncGETower (SheafOfModules.{u} X.ringCatSheaf) K) K p hp
    have hlim' : IsDerivedLimit
        (truncGETower (SheafOfModules.{u} X.ringCatSheaf) K ⋙ RF) (RF.obj K) := ⟨_, δ, hδ⟩
    have hbound : ∀ n : ℕ,
        ((truncGETower (SheafOfModules.{u} X.ringCatSheaf) K ⋙ RF).obj ⟨n⟩).IsLE
          (c + ((N : ℤ) - 1)) := by
      intro n
      have hGE : ((truncGETower (SheafOfModules.{u} X.ringCatSheaf) K).obj
          ⟨n⟩).IsGE (-(n : ℤ)) := by
        rw [truncGETower_obj]
        infer_instance
      have hLE : ((truncGETower (SheafOfModules.{u} X.ringCatSheaf) K).obj ⟨n⟩).IsLE c := by
        rw [truncGETower_obj]
        infer_instance
      exact isLE_obj_of_isGE_of_isLE (SheafOfModules.isQuasicoherent X.ringCatSheaf) RF
        ((N : ℤ) - 1) hSingle _
        (by
          rw [truncGETower_obj]
          exact prop_homologyFunctor_truncGE_obj
            (SheafOfModules.isQuasicoherent X.ringCatSheaf) K hK (-(n : ℤ)))
        (-(n : ℤ)) c
    have h := isLE_of_isDerivedLimit
      (truncGETower (SheafOfModules.{u} X.ringCatSheaf) K ⋙ RF) (RF.obj K) hlim'
      (c + ((N : ℤ) - 1)) hbound
    convert h using 1
    omega
  have h₁ : (RF.obj ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)).IsLE
      (b + (N : ℤ) - 1) := by
    have h := hweak _ (prop_homologyFunctor_truncLE_obj
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E hcoh (b - 1)) (b - 1) inferInstance
    convert h using 1
    omega
  exact isLE_obj_of_isLE_obj_truncLE (SheafOfModules.isQuasicoherent X.ringCatSheaf) RF
    ((N : ℤ) - 1) hSingle E hcoh b (b + (N : ℤ) - 1) (by omega) h₁

include F alpha in
/-- **Stacks Project, Tag 08D4, part (2).** In the situation of
`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus`, the canonical
comparison
`H^i(RF(E)) ⟶ H^i(RF(τ_{≥ b - N + 1}E))` is an isomorphism for every `i ≥ b`.

Write `a = b - N + 1`. The canonical truncation triangle
`τ_{≤ a-1}E ⟶ E ⟶ τ_{≥ a}E` goes to a distinguished triangle under `RF`, which is exact; its
first vertex has `RF`-image in degrees `≤ a - 1 + N - 1 = b - 1` by part (3), so `H^i` and
`H^{i+1}` vanish there for `i ≥ b`, and the long exact homology sequence makes the second map
invertible on `H^i`. -/
@[stacks 08D4 "part (2)"]
theorem isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero_rightDerivedPlus
    (N : ℕ)
    (hRF : ∀ M : SheafOfModules.{u} X.ringCatSheaf, M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} X.ringCatSheaf) i).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ (b - (N : ℤ) + 1)).app E))) := by
  have hP := containsZero_isQuasicoherent X
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  set a := b - (N : ℤ) + 1 with ha
  let T := RF.mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory B) := RF.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) E)
  have hl : T.obj₁.IsLE (a - 1 + (N : ℤ) - 1) := by
    have hLE : ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E).IsLE (a - 1) :=
      inferInstance
    exact isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus X F RF alpha N hRF _
      (prop_homologyFunctor_truncLE_obj (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        E hE (a - 1)) (a - 1) hLE
  have hz := T.obj₁.isZero_of_isLE (a - 1 + (N : ℤ) - 1) i (by omega)
  have hz' := T.obj₁.isZero_of_isLE (a - 1 + (N : ℤ) - 1) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor B i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₂_iff T hT i).2
      (hz.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor B i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B i).map T.mor₂)

end Bounds

end AlgebraicGeometry

end
