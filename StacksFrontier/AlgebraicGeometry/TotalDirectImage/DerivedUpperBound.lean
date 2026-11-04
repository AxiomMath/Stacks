module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# Upper cohomological bounds under a total right derived functor

Let `F` be an additive functor out of an abelian category `A` and let `(R, β)` be a total right
derived functor of `F` on the whole unbounded derived category `D(A)`. If the higher right derived
functors `R ᵖ F` vanish from degree `N` onwards on the objects of a class `P`, and if `E` is an
object of `D(A)` all of whose cohomology objects lie in `P`, then `R` shifts an upper
cohomological bound on `E` by at most `N - 1`.

This is the upper half of [Stacks, Tag 08D4]; the lower half, which needs no vanishing hypothesis
at all, is `StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/DerivedBounds.lean`. The two
halves are genuinely different arguments. The lower one is a statement about a single K-injective
representative; this one needs `E` to be recovered from its truncations: over a scheme, with `P`
the quasi-coherent modules, that is [Stacks, Tag 08D3], proved in
`StacksFrontier/AlgebraicGeometry/TotalDirectImage/TruncationTower.lean`.

The argument is the one in the source, in three steps.

* On an object `M` of `P` placed in a single degree `n`, the bound is the vanishing hypothesis
  read through the comparison `H^m(R(M[n])) ≅ R ^{m-n} F(M)`.
* On a bounded object the bound follows by induction on the length of the range of degrees,
  splitting off one cohomology object at a time with the canonical truncation triangle.
* On an object bounded only above, `E` is a derived limit of its truncations `τ_{≥ -n} E`, each of
  which is bounded; a total right derived functor that preserves countable products carries that
  derived limit to a derived limit ([Stacks, Tag 08U1]), and a derived limit of objects in degrees
  `≤ c` lies in degrees `≤ c + 1`. That costs one degree, which is why the bounded statement is
  applied with `N - 1` and the unbounded one concludes with `N`.

## Main results

* `Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj_of_isZero_rightDerivedPlus`: the bound
  on an object concentrated in one degree.
* `Stacks.SmallDerivedCategory.isLE_obj_of_isGE`: the bound on a bounded object.
* `AlgebraicGeometry.isLE_rightDerivedFunctor_obj_addCommGrpCat`: **[Stacks, Tag 08D4] part (3),
  the upper bound**, for an abelian-group-valued functor.
* `AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_addCommGrpCat`:
  **[Stacks, Tag 08D4] part (2)**, likewise.

## Implementation notes

The hypothesis that `F` commutes with countable products is `PreservesLimitsOfShape (Discrete ℕ)`,
and is used only through [Stacks, Tag 08U1]; it is what makes the derived limit of the truncation
tower survive `R`.

The vanishing hypothesis is stated for Mathlib's bounded-below `Functor.rightDerivedPlus` indexed
by `ℤ`, as in the source, while the comparison with a single object is stated for the `ℕ`-indexed
`Functor.rightDerived`; `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` converts between
them.

Everything is stated at a free `HasDerivedCategory` instance, so each statement for a scheme
specializes both to `HasDerivedCategory.standard` and to the locally small model.

**Two names qualified.** `Stacks.SmallDerivedCategory.isLE_pi` and
`Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit` — general statements about countable
products and derived limits in a derived category — are taken from
`StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/UpperBounds.lean`, which holds them
publicly under those names; the copies that used to be repeated here are gone. Two further
`private` copies remain in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedAmplitude/UpperBounds.lean` and
`StacksFrontier/AlgebraicGeometry/Cohomology/QuasicoherentAmplitude.lean`. The two
scheme-level results carry the suffix `addCommGrpCat` because that file proves the same two
clauses of [Stacks, Tag 08D4] by the other route — the truncation-tower convergence at the
standard model, for an arbitrary abelian target — whereas the functor here is
abelian-group-valued; the two proofs are different and neither subsumes the other.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u

namespace DerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (E : DerivedCategory A) (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))

include hE in
/-- If every cohomology object of `E` lies in `P`, so does every cohomology object of a canonical
truncation from above of `E`: in the degrees it retains it is the cohomology of `E`, and above
them it is zero. -/
theorem prop_homologyFunctor_truncLE_obj (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj E)) := by
  by_cases hi : i ≤ a
  · have := Stacks.SmallDerivedCategory.isIso_homologyFunctor_map_truncLEι E a i hi
    exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E))).symm (hE i)
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ a i (by omega))

include hE in
/-- If every cohomology object of `E` lies in `P`, so does every cohomology object of a canonical
truncation from below of `E`. -/
theorem prop_homologyFunctor_truncGE_obj (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E)) := by
  by_cases hi : a ≤ i
  · have := isIso_homologyFunctor_map_truncGEπ a i hi E
    exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E))) (hE i)
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isGE _ a i (by omega))

end DerivedCategory

namespace Stacks.SmallDerivedCategory

section Single

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  [R.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

include β hres in
/-- **The bound on an object concentrated in a single degree.** If `R ᵖ F(M)` vanishes for every
`p ≥ N`, then `R` applied to `M` placed in degree `n` lies in degrees `≤ n + N - 1`.

This is the vanishing hypothesis read through the comparison `H^m(R(M[n])) ≅ R ^{m-n}F(M)` of
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`. -/
theorem isLE_obj_singleFunctor_obj_of_isZero_rightDerivedPlus (M : A) (N : ℕ)
    (hM : ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M)) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + (N : ℤ) - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m - n = (k : ℤ) :=
    ⟨(m - n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  refine IsZero.of_iso ?_
    (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso F R β hres M n m k hk)
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff F (m := (k : ℤ)) (n := k) rfl M).1
    (hM (k : ℤ) (by omega))

end Single

section Bounded

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
  (d : ℤ) (hSingle : ∀ M, P M → ∀ n : ℤ,
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))

omit [P.ContainsZero] [R.CommShift ℤ] [R.IsTriangulated] in
include hSingle in
/-- The bound on an object concentrated in a single degree, stated for an object of the derived
category rather than for a single object of `A`. -/
theorem isLE_obj_of_isGE_of_isLE_single (E : DerivedCategory A)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (b : ℤ) [E.IsGE b] [E.IsLE b] : (R.obj E).IsLE (b + d) := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E b
  have hM : P M := P.prop_of_iso
    ((DerivedCategory.homologyFunctor A b).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app M) (hE b)
  have := hSingle M hM b
  exact DerivedCategory.TStructure.t.isLE_of_iso (R.mapIso e.symm) (b + d)

/-- A triangulated functor bounds `E` above by `b + d` as soon as it bounds the two outer
vertices `τ_{≤ b-1}E` and `τ_{≥ b}E` of the canonical truncation triangle by `b + d`. -/
private theorem isLE_obj_of_isLE_truncLE_of_isLE_truncGE (E : DerivedCategory A) (b : ℤ)
    (h₁ : (R.obj ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)).IsLE (b + d))
    (h₃ : (R.obj ((DerivedCategory.TStructure.t.truncGE b).obj E)).IsLE (b + d)) :
    (R.obj E).IsLE (b + d) :=
  DerivedCategory.TStructure.t.isLE₂
    (R.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E))
    (R.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E))
    (b + d) h₁ h₃

include hSingle in
/-- **The bound on a bounded object.** An object of `D(A)` living in degrees `[a, b]`, all of whose
cohomology objects lie in `P`, has `R`-image in degrees `≤ b + d`.

The induction is on the length `b - a` of the range: the truncation triangle
`τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` has a shorter first vertex and a third vertex concentrated in the
single degree `b`. -/
theorem isLE_obj_of_isGE (E : DerivedCategory A)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a b : ℤ) [E.IsGE a] [E.IsLE b] : (R.obj E).IsLE (b + d) := by
  suffices h : ∀ (m : ℕ) (E : DerivedCategory A),
      (∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E)) →
      ∀ a b : ℤ, b < a + m → E.IsGE a → E.IsLE b → (R.obj E).IsLE (b + d) from
    h (b - a + 1).toNat E hE a b (by omega) inferInstance inferInstance
  intro m
  induction m with
  | zero =>
      intro E hE a b hab hGE hLE
      have hz : IsZero E := (IsZero.iff_id_eq_zero E).2
        (DerivedCategory.TStructure.t.zero (𝟙 E) b a (by omega))
      exact DerivedCategory.TStructure.t.isLE_of_iso (R.map_isZero hz).isoZero.symm (b + d)
  | succ m ih =>
      intro E hE a b hab hGE hLE
      have hge₁ : ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E).IsGE a := inferInstance
      have hle₁ : ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E).IsLE (b - 1) :=
        DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl
      have hge₃ : ((DerivedCategory.TStructure.t.truncGE b).obj E).IsGE b :=
        DerivedCategory.TStructure.t.isGE_truncGE_obj E b b le_rfl
      have h₁ := ih _ (DerivedCategory.prop_homologyFunctor_truncLE_obj P E hE (b - 1)) a (b - 1)
        (by omega) hge₁ hle₁
      exact isLE_obj_of_isLE_truncLE_of_isLE_truncGE R d E b
        (DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + d) (b + d) (by omega))
        (isLE_obj_of_isGE_of_isLE_single P R d hSingle _
          (DerivedCategory.prop_homologyFunctor_truncGE_obj P E hE b) b)

end Bounded

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

/-- A zero sheaf of modules on a scheme is quasi-coherent: it is presented by the empty family of
generators and the empty family of relations. -/
theorem isQuasicoherent_zero (X : Scheme.{u}) : (0 : X.Modules).IsQuasicoherent := by
  let G : (0 : X.Modules).GeneratingSections :=
    { I := PEmpty
      s := PEmpty.elim
      epi := (isZero_zero X.Modules).epi _ }
  have hfree : IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty) := by
    rw [IsZero.iff_id_eq_zero]
    exact Sigma.hom_ext _ _ fun n ↦ n.elim
  have : Mono G.π := hfree.mono _
  let Pres : (0 : X.Modules).Presentation :=
    { generators := G
      relations :=
        { I := PEmpty
          s := PEmpty.elim
          epi := (isZero_kernel_of_mono G.π).epi _ } }
  exact Pres.isQuasicoherent

/-- **Quasi-coherence as a property of the objects of `X.Modules`.** This is
`SheafOfModules.isQuasicoherent X.ringCatSheaf` read at the scheme-theoretic spelling of the
category of `𝒪_X`-modules, which is the spelling the statements of [Stacks, Tag 08D4] use. -/
def isQuasicoherentModules (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun M ↦ M.IsQuasicoherent

/-- Quasi-coherence is invariant under isomorphism. -/
instance isQuasicoherentModules_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (isQuasicoherentModules X).IsClosedUnderIsomorphisms where
  of_iso e hM := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hM

/-- The quasi-coherent sheaves of modules on a scheme contain a zero object. -/
instance isQuasicoherentModules_containsZero (X : Scheme.{u}) :
    (isQuasicoherentModules X).ContainsZero :=
  ⟨0, isZero_zero X.Modules, isQuasicoherent_zero X⟩

section Scheme

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})
  (F : X.Modules ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u})
  (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  (N : ℕ)
  (hRF : ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
    IsZero ((F.rightDerivedPlus p).obj M))

include F alpha hRF in
/-- **Stacks 08D4, part (3), the upper bound.** Let `X` be a scheme, let `F` be an additive
functor out of the `𝒪_X`-modules commuting with countable products, and let `(RF, alpha)` be a
total right derived functor of `F` on `D(𝒪_X)`. If `R ᵖ F` vanishes on quasi-coherent modules for
every `p ≥ N`, then `RF` carries an object with quasi-coherent cohomology lying in degrees `≤ b`
to one lying in degrees `≤ b + N - 1`.

The object is split by the truncation triangle at `b` into a part concentrated in degree `b` and a
part in degrees `≤ b - 1`. The second is handled by the derived limit of its truncation tower:
each stage is bounded, so the bounded statement applies with `N - 1`, [Stacks, Tag 08U1] carries
the derived limit through `RF`, and the derived limit costs the one further degree. -/
@[stacks 08D4 "part (3), upper bound"]
theorem isLE_rightDerivedFunctor_obj_addCommGrpCat (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + (N : ℤ) - 1) := by
  let P := isQuasicoherentModules X
  have hres : ∀ K : CochainComplex X.Modules ℤ, ∃ (I : CochainComplex X.Modules ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := fun K ↦
    ⟨(Stacks.Injectives.functorialKInjectiveResolution X.Modules).functor.obj K,
      (Stacks.Injectives.functorialKInjectiveResolution X.Modules).inclusion.app K,
      (Stacks.Injectives.functorialKInjectiveResolution X.Modules).isKInjective K,
      (Stacks.Injectives.functorialKInjectiveResolution X.Modules).quasiIso K⟩
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  have hSingle : ∀ M : X.Modules, P M → ∀ n : ℤ,
      (RF.obj ((DerivedCategory.singleFunctor X.Modules n).obj M)).IsLE (n + ((N : ℤ) - 1)) := by
    intro M hM n
    have h := Stacks.SmallDerivedCategory.isLE_obj_singleFunctor_obj_of_isZero_rightDerivedPlus
      F RF alpha hres M N
      (fun p hp ↦ hRF M hM p hp) n
    exact DerivedCategory.TStructure.t.isLE_of_le _ (n + (N : ℤ) - 1) (n + ((N : ℤ) - 1))
      (by omega)
  have _hprodnat : HasProductsOfShape ℕ (DerivedCategory AddCommGrpCat.{u}) :=
    Stacks.DerivedProducts.hasProductsOfShape_nat
  have hweak : ∀ (K : DerivedCategory X.Modules),
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent) →
      ∀ c : ℤ, K.IsLE c → (RF.obj K).IsLE (c + (N : ℤ)) := by
    intro K hK c hc
    obtain ⟨hprod, q, hq⟩ := exists_isDerivedLimit_truncGETower_of_isQuasicoherent X K hK
    have := hprod
    obtain ⟨hprod', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
      F RF alpha (Stacks.DerivedLimit.truncGETower X.Modules K) K q hq
    have := hprod'
    have hbound : ∀ n : ℕ,
        ((Stacks.DerivedLimit.truncGETower X.Modules K ⋙ RF).obj ⟨n⟩).IsLE
          (c + ((N : ℤ) - 1)) := by
      intro n
      have hge : ((Stacks.DerivedLimit.truncGETower X.Modules K).obj ⟨n⟩).IsGE (-(n : ℤ)) :=
        DerivedCategory.TStructure.t.isGE_truncGE_obj K (-(n : ℤ)) (-(n : ℤ)) le_rfl
      have hle : ((Stacks.DerivedLimit.truncGETower X.Modules K).obj ⟨n⟩).IsLE c :=
        inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K).IsLE c)
      exact Stacks.SmallDerivedCategory.isLE_obj_of_isGE P RF ((N : ℤ) - 1) hSingle _
        (DerivedCategory.prop_homologyFunctor_truncGE_obj P K hK (-(n : ℤ))) (-(n : ℤ)) c
    have h := Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit
      (Stacks.DerivedLimit.truncGETower X.Modules K ⋙ RF) (RF.obj K)
      ⟨_, δ, hδ⟩ (c + ((N : ℤ) - 1)) hbound
    exact DerivedCategory.TStructure.t.isLE_of_le _ (c + ((N : ℤ) - 1) + 1) (c + (N : ℤ))
      (by omega)
  have hle₁ : ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E).IsLE (b - 1) :=
    DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl
  have h₁ := hweak _ (DerivedCategory.prop_homologyFunctor_truncLE_obj P E hcoh (b - 1)) (b - 1)
    hle₁
  have h := Stacks.SmallDerivedCategory.isLE_obj_of_isLE_truncLE_of_isLE_truncGE RF
    ((N : ℤ) - 1) E b
    (DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + (N : ℤ)) (b + ((N : ℤ) - 1)) (by omega))
    (Stacks.SmallDerivedCategory.isLE_obj_of_isGE_of_isLE_single P RF ((N : ℤ) - 1)
      hSingle _ (DerivedCategory.prop_homologyFunctor_truncGE_obj P E hcoh b) b)
  exact DerivedCategory.TStructure.t.isLE_of_le _ (b + ((N : ℤ) - 1)) (b + (N : ℤ) - 1)
    (by omega)

include F alpha hRF in
/-- **Stacks 08D4, part (2).** With the hypotheses of the upper bound, in degrees at least `b` a
total right derived functor agrees on an object with quasi-coherent cohomology and on its
canonical truncation in degrees at least `b - N + 1`.

The truncation triangle at `a = b - N + 1` has first vertex in degrees `≤ a - 1`, so the upper
bound puts its `RF`-image in degrees `≤ a - 1 + N - 1 = b - 1`; the long exact homology sequence
then makes the second map invertible on `H^i` for every `i ≥ b`. -/
@[stacks 08D4 "part (2)"]
theorem isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_addCommGrpCat
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ (b - (N : ℤ) + 1)).app E))) := by
  let P := isQuasicoherentModules X
  let a : ℤ := b - (N : ℤ) + 1
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  let T := RF.mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj E)
  have ht : T ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) :=
    RF.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) E)
  have h₁ : T.obj₁.IsLE (a - 1 + (N : ℤ) - 1) :=
    isLE_rightDerivedFunctor_obj_addCommGrpCat X F RF alpha N hRF _
      (DerivedCategory.prop_homologyFunctor_truncLE_obj P E hcoh (a - 1)) (a - 1)
      (DerivedCategory.TStructure.t.isLE_truncLE_obj E (a - 1) (a - 1) le_rfl)
  have hz := DerivedCategory.isZero_of_isLE T.obj₁ (a - 1 + (N : ℤ) - 1) i (by dsimp [a]; omega)
  have hz' := DerivedCategory.isZero_of_isLE T.obj₁ (a - 1 + (N : ℤ) - 1) (i + 1)
    (by dsimp [a]; omega)
  have hmono : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequence_mono_shift_map_mor₂_iff
      T ht i).2 (hz.eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequence_epi_shift_map_mor₂_iff
      T ht i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map T.mor₂)

end Scheme

end AlgebraicGeometry

end
