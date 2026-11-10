module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerBridge
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGETower
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Right derived functors on complexes with quasi-coherent cohomology

Let `X` be a scheme and `F : Mod(𝒪_X) ⥤ ℬ` an additive functor into an abelian category with
exact countable products, which commutes with countable products. If the higher right derived
functors `R^p F` vanish from degree `N` onward *on quasi-coherent modules*, then a total right
derived functor `RF : D(𝒪_X) ⥤ D(ℬ)` has cohomological amplitude at most `N - 1` on the objects of
`D_QCoh(𝒪_X)`: it preserves a lower cohomological bound, and shifts an upper bound by at most
`N - 1`.

This is [Stacks, Tag 08D4]. Its abstract sibling is [Stacks, Tag 07K7]
(`CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived`), where the vanishing is
assumed on *every* object; here it is assumed only on the quasi-coherent ones, and the reduction
to that case is the content of the tag. An object `E` of `D(𝒪_X)` with quasi-coherent cohomology
is the derived limit of the tower `τ_{≥ -n}E` of its truncations from below ([Stacks, Tag 08D3],
`Stacks.TruncationTower.exists_isDerivedLimit_truncGETower_of_isQuasicoherent`); `RF` carries that
derived limit to a derived limit ([Stacks, Tag 08U1],
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`); each `τ_{≥ -n}E` is cohomologically
bounded with quasi-coherent cohomology, so the abstract dévissage bounds `RF(τ_{≥ -n}E)`; and a
derived limit of objects which are `≤ c` is `≤ c + 1`, which costs the one degree that the
two-step argument then recovers.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.QuasicoherentAmplitude.isGE_obj` — part (3), lower bound: `RF` preserves a lower
  cohomological bound on an object with quasi-coherent cohomology.
* `Stacks.QuasicoherentAmplitude.isLE_obj_of_isZero` — part (3), upper bound: `RF` shifts an
  upper cohomological bound by at most `N - 1`.
* `Stacks.QuasicoherentAmplitude.isIso_homology_map_truncLE` — part (1): in degrees `≤ a`, `RF`
  agrees on `E` and on `τ_{≤ a}E`.
* `Stacks.QuasicoherentAmplitude.isIso_homology_map_truncGE_of_isZero` — part (2): in degrees
  `≥ b`, `RF` agrees on `E` and on `τ_{≥ b - N + 1}E`.

Parts (1) and (3) lower bound need neither the product hypothesis on `F` nor the vanishing
hypothesis; they are stated without them.

## Implementation notes

*The target category is a variable, where the source states it at `AddCommGrp`.* The source's
`F` lands in abelian groups; everything here is proved for an arbitrary abelian `ℬ` with exact
countable products, of which `AddCommGrpCat.{u}` — the source's — and `ModuleCat.{u} A` are both
instances. The second is the one the affine derived Spec–Γ development needs, because
`AlgebraicGeometry.globalSectionsOver` is `ModuleCat A`-valued; the source's `AddCommGrp`-valued
statement does not apply to it.

*The derived category of `X.Modules` is the locally small one, and no model is pinned.*
`DerivedCategory X.Modules` resolves by instance search to
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the global instance of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`. That is the model the rest of the
derived Spec–Γ development lives at — see the module docstring of
`StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerAnyModel.lean`, which freed [Stacks, Tag
0D6M] from the standard model for exactly this reason — and it is the only model at which
[Stacks, Tag 08D3] is available here, so nothing below takes a `HasDerivedCategory X.Modules`
binder. Note that a file-level
`attribute [local instance] HasDerivedCategory.standard` is *inert* in this library: an
unprioritised file-level local instance loses to that global one, and `inferInstance`
resolves to `Scheme.Modules.hasDerivedCategory` with the attribute in scope.

*What the abstract dévissage is stated at.* The two-sided bound for a *bounded* object is proved
for an arbitrary `ObjectProperty` `P` closed under isomorphisms and containing the zero objects,
by induction on the length of the interval, splitting off one degree at a time with the
`τ_{≤ b-1} ⟶ E ⟶ τ_{≥ b}` triangle. Only `isLE_obj_of_quasicoherent` instantiates `P` at the
quasi-coherent modules, where `(SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero` is
found by synthesis.

*Where the tower's product comes from.* The instance
`HasProduct (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩)`
does **not** synthesize; it is produced by
`DerivedCategory.exists_isDerivedLimit_of_forall_isGE`, which builds it from the tower's terms
being bounded below, and then passed to [Stacks, Tag 08D3] by name. Likewise
`HasProductsOfShape ℕ (DerivedCategory ℬ)` does not synthesize and is supplied as a `let` from
`Stacks.DerivedProducts.hasProductsOfShape_derivedCategory`.

No `@[stacks]` attribute appears below; the covering set for Tag 08D4 is placed by the lead.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

universe u

namespace Stacks.QuasicoherentAmplitude

open ZeroObject

/-! ### The bounds for an arbitrary right derived functor between abelian categories -/

section DerivedBounds

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ R)
  (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
    IsIso (β.app ((HomotopyCategory.quotient A _).obj I)))

/-- If `β` is invertible at a K-injective complex `I`, then `Q(F(I)) ≅ R(Q(I))`. -/
private def kInjectiveComputationIso (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      R.obj (DerivedCategory.Q.obj I) :=
  have := hcomp I hI
  ((DerivedCategory.quotientCompQhIso B).app _).symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm ≪≫
    asIso (β.app ((HomotopyCategory.quotient A _).obj I)) ≪≫
    R.mapIso ((DerivedCategory.quotientCompQhIso A).app I)

include hcomp in
/-- **Part (3), lower bound, abstractly.** If the K-injective complexes compute `R`, then `R`
preserves a lower cohomological bound: a bounded below object is represented by a complex of
injectives in the same range, which is K-injective, so `R` of it is computed by applying `F`
termwise. -/
private lemma isGE_of_computing_kInjectives (E : DerivedCategory A) (a : ℤ)
    (hE : E.IsGE a) : (R.obj E).IsGE a := by
  obtain ⟨K, _, ⟨e⟩⟩ := E.exists_iso_Q_obj_of_isGE a
  obtain ⟨I, f, hf, hI, hIa⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K a
  have hKI := CochainComplex.isKInjective_of_injective I a
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (kInjectiveComputationIso F R β hcomp I hKI ≪≫
      R.mapIso ((asIso (DerivedCategory.Q.map f)).symm ≪≫ e.symm)) a

include hcomp in
/-- **The bound on a single module.** If `R^p F` vanishes above `d` on `M`, then `R` sends `M[-n]`
into degrees `≤ n + d`. The value of `R` on a bounded below object agrees with the value of the
bounded below right derived functor
(`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`), whose cohomology
is `R^p F`. -/
private lemma isLE_obj_single_of_vanishing [R.CommShift ℤ]
    (M : A) (d : ℤ)
    (hM : ∀ p : ℤ, d < p → IsZero ((F.rightDerivedPlus p).obj M)) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    F R β hcomp ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0 (by
      change ((DerivedCategory.singleFunctor A 0).obj M).IsGE 0
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

end DerivedBounds

/-! ### The canonical truncation comparisons, for an arbitrary abelian category -/

section Truncations

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- In a distinguished triangle, `Hⁱ(mor₂)` is invertible if `Hⁱ` and `Hⁱ⁺¹` of the first vertex
vanish. -/
private lemma isIso_homology_map_mor₂ (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (i : ℤ)
    (h₁ : IsZero ((DerivedCategory.homologyFunctor A i).obj T.obj₁))
    (h₁' : IsZero ((DerivedCategory.homologyFunctor A (i + 1)).obj T.obj₁)) :
    IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₂) := by
  have : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_mono_shift_map_mor₂_iff T hT i).2
      (h₁.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_epi_shift_map_mor₂_iff
      T hT i (i + 1) rfl).2 (h₁'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- In a distinguished triangle, `Hⁱ(mor₁)` is invertible if `Hⁱ` and `Hⁱ⁻¹` of the third vertex
vanish. -/
private lemma isIso_homology_map_mor₁ (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) (i : ℤ)
    (h₃ : IsZero ((DerivedCategory.homologyFunctor A i).obj T.obj₃))
    (h₃' : IsZero ((DerivedCategory.homologyFunctor A (i - 1)).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₁) := by
  have : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_epi_shift_map_mor₁_iff T hT i).2
      (h₃.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (i - 1) i (by omega)).2 (h₃'.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- `Hⁱ(E) ⟶ Hⁱ(τ_{≥ a}E)` is invertible for `i ≥ a`: the third vertex of the truncation
triangle is `≤ a - 1`, hence has no cohomology in degrees `i` and `i + 1`. -/
private lemma isIso_homology_truncGEπ (E : DerivedCategory A) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj E
  have ht := DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) E
  -- `T.obj₁` is `τ_{≤ a-1}E` by `rfl`; `inferInstanceAs` crosses that, instance search does not
  have : T.obj₁.IsLE (a - 1) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E).IsLE (a - 1))
  exact isIso_homology_map_mor₂ T ht i (T.obj₁.isZero_of_isLE (a - 1) i (by omega))
    (T.obj₁.isZero_of_isLE (a - 1) (i + 1) (by omega))

/-- `Hⁱ(τ_{≤ a}E) ⟶ Hⁱ(E)` is invertible for `i ≤ a`: the third vertex of the truncation
triangle is `≥ a + 1`, hence has no cohomology in degrees `i` and `i - 1`. -/
private lemma isIso_homology_truncLEι (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E
  have ht := DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E
  -- `T.obj₃` is `τ_{≥ a+1}E` by `rfl`; `inferInstanceAs` crosses that, instance search does not
  have : T.obj₃.IsGE (a + 1) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E).IsGE (a + 1))
  exact isIso_homology_map_mor₁ T ht i (T.obj₃.isZero_of_isGE (a + 1) i (by omega))
    (T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega))

end Truncations

/-! ### Truncations inherit a property of the cohomology objects -/

section CohomologyProperty

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (E : DerivedCategory A) (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E))

include hE in
/-- The cohomology objects of `τ_{≤ a}E` satisfy `P`: in degrees `≤ a` they are those of `E`, and
above `a` they vanish. -/
private lemma homology_truncLE_property (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj E)) := by
  by_cases hi : i ≤ a
  · have := isIso_homology_truncLEι E a i hi
    exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E))).symm (hE i)
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isLE _ a i (by omega))

include hE in
/-- The cohomology objects of `τ_{≥ a}E` satisfy `P`: in degrees `≥ a` they are those of `E`, and
below `a` they vanish. -/
private lemma homology_truncGE_property (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E)) := by
  by_cases hi : a ≤ i
  · have := isIso_homology_truncGEπ E a i hi
    exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E))) (hE i)
  · exact P.prop_of_isZero (DerivedCategory.isZero_of_isGE _ a i (by omega))

end CohomologyProperty

/-! ### The upper bound for a cohomologically bounded object, by dévissage -/

section UpperBounds

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
  (d : ℤ) (hSingle : ∀ M, P M → ∀ n : ℤ,
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))

omit [P.ContainsZero] [R.CommShift ℤ] [R.IsTriangulated] in
include hSingle in
/-- The bound for an object concentrated in one degree, which is then a shifted single object. -/
private lemma isLE_obj_of_pure (E : DerivedCategory A)
    (hE : ∀ i, P ((DerivedCategory.homologyFunctor A i).obj E))
    (b : ℤ) [E.IsGE b] [E.IsLE b] : (R.obj E).IsLE (b + d) := by
  obtain ⟨M, ⟨e⟩⟩ := E.exists_iso_singleFunctor_obj_of_isGE_of_isLE b
  have hM : P M := P.prop_of_iso
    ((DerivedCategory.homologyFunctor A b).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app M) (hE b)
  have := hSingle M hM b
  exact DerivedCategory.TStructure.t.isLE_of_iso (R.mapIso e.symm) (b + d)

/-- **One step of the dévissage.** If `R` of the two outer vertices of the truncation triangle
`τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` is `≤ c`, then so is `R E`. -/
private lemma isLE_obj_of_isLE_truncLE_truncGE (E : DerivedCategory A) (b c : ℤ)
    (h₁ : (R.obj ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)).IsLE c)
    (h₃ : (R.obj ((DerivedCategory.TStructure.t.truncGE b).obj E)).IsLE c) : (R.obj E).IsLE c :=
  DerivedCategory.TStructure.t.isLE₂
    (R.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E))
    (R.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E)) c h₁ h₃

include hSingle in
/-- **The dévissage.** The bound for an object living in a finite range of degrees, by induction on
the length of the range: split off the top degree with the `τ_{≤ b-1} ⟶ E ⟶ τ_{≥ b}` triangle,
apply the inductive hypothesis to `τ_{≤ b-1}` and `isLE_obj_of_pure` to `τ_{≥ b}`. -/
private lemma isLE_obj_of_bounded (E : DerivedCategory A)
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
      have h₁ : (R.obj ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)).IsLE (b - 1 + d) :=
        ih _ (homology_truncLE_property P E hE (b - 1)) a (b - 1) (by omega)
          (by infer_instance) (by infer_instance)
      have : ((DerivedCategory.TStructure.t.truncGE b).obj E).IsGE b := inferInstance
      have : ((DerivedCategory.TStructure.t.truncGE b).obj E).IsLE b := inferInstance
      have h₃ := isLE_obj_of_pure P R d hSingle _ (homology_truncGE_property P E hE b) b
      exact isLE_obj_of_isLE_truncLE_truncGE R E b (b + d)
        (DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + d) (b + d) (by omega)) h₃

end UpperBounds

/-! ### A derived limit of objects bounded above is bounded above, up to one degree -/

section DerivedLimit

/-- A countable product of objects which are `≤ b` is `≤ b`: cohomology commutes with countable
products in `D(B)` when they are exact in `B`, by `Stacks07KC`. -/
private lemma isLE_product {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] [HasProductsOfShape ℕ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasProductsOfShape ℕ (DerivedCategory B)]
    (E : ℕ → DerivedCategory B) (b : ℤ) (hE : ∀ n, (E n).IsLE b) :
    (∏ᶜ E).IsLE b := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor E i
  refine IsZero.of_iso ?_ (asIso (piComparison (DerivedCategory.homologyFunctor B i) E))
  rw [IsZero.iff_id_eq_zero]
  exact Pi.hom_ext _ _ fun n ↦ (DerivedCategory.isZero_of_isLE (E n) b i hi).eq_of_tgt _ _

/-- **A derived limit costs one degree.** A derived limit of a tower of objects which are all
`≤ b` is `≤ b + 1`: it sits in a triangle whose other two vertices are the product of the tower,
which is `≤ b`, and that product shifted by `-1`, which is `≤ b + 1`. -/
private lemma isLE_of_isDerivedLimit {B : Type*} [Category B] [Abelian B]
    [HasDerivedCategory B] [HasProductsOfShape ℕ B]
    [HasExactLimitsOfShape (Discrete ℕ) B]
    [HasProductsOfShape ℕ (DerivedCategory B)]
    (E : ℕᵒᵖ ⥤ DerivedCategory B) (L : DerivedCategory B)
    (hL : IsDerivedLimit E L) (b : ℤ) (hE : ∀ n : ℕ, (E.obj ⟨n⟩).IsLE b) :
    L.IsLE (b + 1) := by
  obtain ⟨p, δ, hT⟩ := hL
  have hp := isLE_product (fun n : ℕ ↦ E.obj ⟨n⟩) b hE
  let T := Triangle.mk p (Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op) δ
  have hshift : ((∏ᶜ fun n : ℕ ↦ E.obj ⟨n⟩)⟦(-1 : ℤ)⟧).IsLE (b + 1) :=
    DerivedCategory.TStructure.t.isLE_shift _ b (-1) (b + 1) (by omega)
  have : T.invRotate.obj₃.IsLE b := hp
  exact DerivedCategory.TStructure.t.isLE₂ T.invRotate (inv_rot_of_distTriang T hT) (b + 1)
    hshift (DerivedCategory.TStructure.t.isLE_of_le _ b (b + 1) (by omega))

end DerivedLimit

/-! ### The upper bound on `D_QCoh`, through the truncation tower -/

/-- **Part (3), upper bound, with the hypotheses of Tag 08D4.** `RF` shifts an upper cohomological
bound by at most `N - 1` on an object with quasi-coherent cohomology.

The dévissage of `isLE_obj_of_bounded` only reaches the cohomologically *bounded* objects; this is
the reduction of the general case to those, and it is the content of the tag. Write `E` as the
derived limit of the tower `τ_{≥ -n}E` of its truncations from below ([Stacks, Tag 08D3]); `RF`
carries that to a derived limit ([Stacks, Tag 08U1]); each `τ_{≥ -n}E` is bounded with
quasi-coherent cohomology, so `RF(τ_{≥ -n}E)` is `≤ c + N - 1`; a derived limit costs one degree,
giving `≤ c + N` — which is one too many. The missing degree is recovered by running that weaker
bound on the two halves of the `τ_{≤ b-1} ⟶ E ⟶ τ_{≥ b}` triangle: the lower half is `≤ b - 1`
and so lands at `≤ b + N - 1`, and the upper half is bounded, so the sharp bound applies to it
directly. -/
private lemma isLE_obj_of_quasicoherent {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
    (X : Scheme.{u})
    (F : X.Modules ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (R : DerivedCategory X.Modules ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (N : ℕ)
    (hv : ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
      IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory X.Modules)
    (hE : ∀ i, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (b : ℤ) (hLE : E.IsLE b) : (R.obj E).IsLE (b + N - 1) := by
  -- the ascription is load-bearing: `SheafOfModules.isQuasicoherent X.ringCatSheaf` has type
  -- `ObjectProperty (SheafOfModules X.ringCatSheaf)`, and `HasDerivedCategory` is keyed on
  -- `X.Modules`, so without it every use below demands
  -- `HasDerivedCategory (SheafOfModules X.ringCatSheaf)`, which does not synthesize
  let P : ObjectProperty X.Modules := SheafOfModules.isQuasicoherent X.ringCatSheaf
  -- and its two class instances by name: instance search does not unfold a `let`-bound `P`
  let : P.IsClosedUnderIsomorphisms :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms
  let : P.ContainsZero :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero
  let := Functor.IsRightDerivedFunctor.commShift R α
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F R α
  have hcomp := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective F R α
    (fun K ↦ Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso K)
  have hSingle : ∀ M, P M → ∀ n : ℤ,
      (R.obj ((DerivedCategory.singleFunctor X.Modules n).obj M)).IsLE (n + ((N : ℤ) - 1)) :=
    fun M hM n ↦ isLE_obj_single_of_vanishing F R α hcomp M ((N : ℤ) - 1)
      (fun p hp ↦ hv M hM p (by omega)) n
  let : HasProductsOfShape ℕ (DerivedCategory B) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  -- the weaker bound, one degree off, for an arbitrary object with quasi-coherent cohomology
  have hweak (K : DerivedCategory X.Modules)
      (hK : ∀ i, P ((DerivedCategory.homologyFunctor X.Modules i).obj K))
      (c : ℤ) (hc : K.IsLE c) : (R.obj K).IsLE (c + N) := by
    obtain ⟨hprod, _, _⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE
      (DerivedLimit.truncGETower X.Modules K)
      (fun n ↦ ⟨-(n : ℤ), by rw [DerivedLimit.truncGETower_obj]; infer_instance⟩)
    let := hprod
    obtain ⟨p, δ₀, hp_triangle, _⟩ :=
      Stacks.TruncationTower.exists_isDerivedLimit_truncGETower_of_isQuasicoherent X K hK
    obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
      (F := F) (RF := R) (α := α) (DerivedLimit.truncGETower X.Modules K) K p
      ⟨δ₀, hp_triangle⟩
    let := hp'
    have hlim' : IsDerivedLimit (DerivedLimit.truncGETower X.Modules K ⋙ R) (R.obj K) :=
      ⟨_, δ, hδ⟩
    have hbound (n : ℕ) : (R.obj ((DerivedLimit.truncGETower X.Modules K).obj ⟨n⟩)).IsLE
        (c + ((N : ℤ) - 1)) := by
      apply isLE_obj_of_bounded P R ((N : ℤ) - 1) hSingle _
        (homology_truncGE_property P K hK (-(n : ℤ))) (-(n : ℤ)) c
    have h := isLE_of_isDerivedLimit (DerivedLimit.truncGETower X.Modules K ⋙ R) (R.obj K)
      hlim' (c + ((N : ℤ) - 1)) hbound
    convert h using 1
    omega
  -- recover the missing degree from the two halves of the truncation triangle at `b`
  have : ((DerivedCategory.TStructure.t.truncGE b).obj E).IsGE b := inferInstance
  have : ((DerivedCategory.TStructure.t.truncGE b).obj E).IsLE b := inferInstance
  have h₁ := hweak _ (homology_truncLE_property P E hE (b - 1)) (b - 1) inferInstance
  have h₃ := isLE_obj_of_pure P R ((N : ℤ) - 1) hSingle _ (homology_truncGE_property P E hE b) b
  exact isLE_obj_of_isLE_truncLE_truncGE R E b (b + N - 1)
    (DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + N) _ (by omega))
    (DerivedCategory.TStructure.t.isLE_of_le _ (b + ((N : ℤ) - 1)) _ (by omega))

/-! ### Tag 08D4 -/

/-- **[Stacks, Tag 08D4] part (3), lower bound.** A total right derived functor preserves a lower
cohomological bound on a complex with quasi-coherent cohomology.

No product hypothesis on `F` and no vanishing hypothesis are needed: the K-injective complexes
compute any total right derived functor out of a Grothendieck abelian category, and a bounded
below object is represented by a K-injective complex in the same range. -/
@[stacks 08D4 "part (3), lower bound"]
theorem isGE_obj {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (X : Scheme.{u})
    (F : X.Modules ⥤ B) [F.Additive]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory B)
    (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsGE a) : (RF.obj E).IsGE a :=
  -- `hcoh` is part of the tag's statement and is not needed for this half; it is retained so that
  -- the statement is the tag's, and is kept rather than removed
  have _hcoh := hcoh
  isGE_of_computing_kInjectives F RF alpha
    (Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective F RF alpha
      (fun K ↦ Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso K)) E a hE

/-- **[Stacks, Tag 08D4] part (3), upper bound.** If the higher derived functors vanish from degree
`N` onward on quasi-coherent modules, a total right derived functor shifts an upper cohomological
bound by at most `N - 1`. -/
@[stacks 08D4 "part (3), upper bound"]
theorem isLE_obj_of_isZero {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
    (X : Scheme.{u})
    (F : X.Modules ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory B)
    (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (N : ℕ)
    (hRF : ∀ (M : X.Modules), M.IsQuasicoherent → ∀ (p : ℤ), (N : ℤ) ≤ p →
      IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + (N : ℤ) - 1) :=
  isLE_obj_of_quasicoherent X F RF alpha N hRF E hcoh b hE

/-- **[Stacks, Tag 08D4] part (1).** A total right derived functor agrees in degrees at most `a` on
a complex with quasi-coherent cohomology and its canonical truncation in degrees at most `a`.

The third vertex of the truncation triangle at `a` is `≥ a + 1`, so by part (3) lower bound its
image under `RF` has no cohomology in degrees `i` and `i - 1` for `i ≤ a`, and the long exact
sequence makes the comparison both mono and epi. -/
@[stacks 08D4 "part (1)"]
theorem isIso_homology_map_truncLE {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B]
    (X : Scheme.{u})
    (F : X.Modules ⥤ B) [F.Additive]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory B)
    (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (E : DerivedCategory X.Modules)
    (hE : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι a).app E))) := by
  let := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  have hcomp := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective F RF alpha
    (fun K ↦ Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso K)
  -- `hE` is part of the tag's statement and is not needed for this part; retained so that the
  -- statement is the tag's, and is kept rather than removed
  have _hE := hE
  let T := RF.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E)
  have ht : T ∈ distTriang (DerivedCategory B) :=
    RF.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hg : T.obj₃.IsGE (a + 1) :=
    isGE_of_computing_kInjectives F RF alpha hcomp
      ((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E) (a + 1) inferInstance
  exact isIso_homology_map_mor₁ T ht i (T.obj₃.isZero_of_isGE (a + 1) i (by omega))
    (T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega))

/-- **[Stacks, Tag 08D4] part (2).** If the higher derived functors vanish from degree `N` onward
on quasi-coherent modules, then in degrees at least `b` a total right derived functor agrees on a
complex with quasi-coherent cohomology and its canonical truncation in degrees at least
`b - N + 1`.

The first vertex of the truncation triangle at `a = b - N + 1` is `≤ a - 1`, so by part (3) upper
bound its image under `RF` is `≤ a - 1 + N - 1 = b - 1`, hence has no cohomology in degrees `i`
and `i + 1` for `i ≥ b`. -/
@[stacks 08D4 "part (2)"]
theorem isIso_homology_map_truncGE_of_isZero {B : Type*} [Category* B] [Abelian B]
    [HasDerivedCategory B] [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
    (X : Scheme.{u})
    (F : X.Modules ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory B)
    (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (N : ℕ)
    (hRF : ∀ (M : X.Modules), M.IsQuasicoherent → ∀ (p : ℤ), (N : ℤ) ≤ p →
      IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory X.Modules)
    (hE : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ (b - (N : ℤ) + 1)).app E))) := by
  let := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  -- `P` and its instances at the `X.Modules` spelling; see `isLE_obj_of_quasicoherent`
  let P : ObjectProperty X.Modules := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let : P.IsClosedUnderIsomorphisms :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms
  let : P.ContainsZero :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero
  let a := b - (N : ℤ) + 1
  let T := RF.mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory B) := RF.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) E)
  have hLE₁ : ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E).IsLE (a - 1) := inferInstance
  have hl : T.obj₁.IsLE (a - 1 + N - 1) :=
    isLE_obj_of_quasicoherent X F RF alpha N hRF _
      (homology_truncLE_property P E hE (a - 1))
      (a - 1) hLE₁
  exact isIso_homology_map_mor₂ T hT i
    (T.obj₁.isZero_of_isLE (a - 1 + N - 1) i (by dsimp [a]; omega))
    (T.obj₁.isZero_of_isLE (a - 1 + N - 1) (i + 1) (by dsimp [a]; omega))

end Stacks.QuasicoherentAmplitude

end
