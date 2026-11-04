module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationTower
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.SpaltensteinCriterion.QuasicoherentTruncationConvergence
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Upper cohomological bounds under a total right derived functor

Let `X` be a scheme and let `F` be an additive functor from the `𝒪_X`-modules to abelian groups
which commutes with countable products. Suppose the higher right derived functors `R^pF` vanish
in degrees `p ≥ N` on quasi-coherent modules. Then a total right derived functor `RF` of `F`
moves the upper end of the range of degrees in which an object with quasi-coherent cohomology
lives by at most `N - 1`, and the canonical comparison
`H^i(RF(E)) ⟶ H^i(RF(τ_{≥ b - N + 1}E))` is an isomorphism for `i ≥ b`.

These are the two *upper* halves of Stacks 08D4. The two lower halves — the comparison
`H^i(RF(τ_{≤ a}E)) ⟶ H^i(RF(E))` for `i ≤ a` and the preservation of a lower bound — need no
vanishing hypothesis and are
`AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncLEι` and
`AlgebraicGeometry.isGE_rightDerivedFunctor_obj`.

The argument is the one of the source. An object `E` with quasi-coherent cohomology is the
derived limit of the tower of its canonical truncations `τ_{≥ -n}E` (Stacks 08D3), and `RF`
carries that derived limit to a derived limit because `F` preserves countable products
(Stacks 08U1). A bounded object with quasi-coherent cohomology is built out of finitely many
shifted quasi-coherent modules, on each of which the vanishing hypothesis bounds `RF` above by
`N - 1`; so every term of the tower is bounded above by `c + N - 1` once `E` is, and a derived
limit of objects bounded above by `b` is bounded above by `b + 1` — the extra `1` coming from the
shift in the defining triangle. Combining the two gives the bound `c + N` for the tower, and
splitting `E` into `τ_{≤ b-1}E` and its pure top piece removes the loss.

## Main results

* `AlgebraicGeometry.isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero` —
  **Stacks 08D4, part (2)**: the upper truncation comparison.
* `AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero` — **Stacks 08D4, part (3), the
  upper bound**: `RF` shifts an upper cohomological bound by at most `N - 1`.

## Implementation notes

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, the model at which the
convergence statement Stacks 08D3 is available.

An object of `D_QCoh(𝒪_X)` is presented by an explicit hypothesis that each of its cohomology
sheaves is quasi-coherent. The higher derived functors in the vanishing hypothesis are the
bounded-below right derived functors `CategoryTheory.Functor.rightDerivedPlus`, `RF` is an
arbitrary total right derived functor of `F`, and the comparison morphism is the image under `RF`,
and then under cohomology, of the canonical truncation morphism.

The auxiliary statements about a class of objects stable under isomorphism and containing the
zero object are phrased with a bare predicate `A → Prop` together with those two closure
properties as hypotheses, rather than with `CategoryTheory.ObjectProperty` and its typeclasses:
`AlgebraicGeometry.Scheme.Modules` and `SheafOfModules` of the structure sheaf are interchangeable
spellings of one category, but only up to unfolding a definition, which instance search does not
do.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open Stacks.SmallDerivedCategory

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Generic upper bounds for a total right derived functor -/

/-- A total right derived functor computed by the K-injective complexes sends a module placed in
degree `-n` to an object in degrees `≤ n + d`, as soon as the higher derived functors of the
functor vanish on that module in degrees `> d`. -/
private theorem isLE_obj_single_of_vanishing {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive]
    (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ]
    (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hcomp : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (M : A) (d : ℤ)
    (hM : ∀ p : ℤ, d < p → IsZero ((F.rightDerivedPlus p).obj M)) (n : ℤ) :
    (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d) := by
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    F R β hcomp ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0
    (inferInstanceAs (((DerivedCategory.singleFunctor A 0).obj M).IsGE 0))
  have hzero : (R.obj ((DerivedCategory.singleFunctor A 0).obj M)).IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro p hp
    exact (hM p hp).of_iso ((DerivedCategory.homologyFunctor B p).mapIso e)
  have : DerivedCategory.TStructure.t.IsLE
      ((R ⋙ shiftFunctor (DerivedCategory B) (-n)).obj
        ((DerivedCategory.singleFunctor A 0).obj M)) (n + d) :=
    DerivedCategory.TStructure.t.isLE_shift
      (R.obj ((DerivedCategory.singleFunctor A 0).obj M)) d (-n) (n + d) (by omega)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((R.commShiftIso (-n)).app ((DerivedCategory.singleFunctor A 0).obj M)).symm ≪≫
      R.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M))
    (n + d)

/-- If the first vertex of a distinguished triangle is in degrees `≤ c`, the second map is an
isomorphism on cohomology in degrees `> c`. -/
private theorem isIso_homology_map_mor₂_of_isLE {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (T : Triangle (DerivedCategory A)) (ht : T ∈ distTriang _)
    (c i : ℤ) [T.obj₁.IsLE c] (hi : c < i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map T.mor₂) := by
  have : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_mono_shift_map_mor₂_iff T ht i).2
      ((T.obj₁.isZero_of_isLE c i hi).eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_epi_shift_map_mor₂_iff
      T ht i (i + 1) rfl).2 ((T.obj₁.isZero_of_isLE c (i + 1) (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Above the truncation degree, the canonical projection to a truncation from below is an
isomorphism on cohomology. -/
theorem isIso_homology_truncGE {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (E : DerivedCategory A) (a i : ℤ) (hi : a ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E)) := by
  have h : a - 1 + 1 = a := by omega
  have : ((DerivedCategory.TStructure.t.triangleLEGE (a - 1) a h).obj E).obj₁.IsLE (a - 1) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E).IsLE (a - 1))
  exact isIso_homology_map_mor₂_of_isLE _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a h E) (a - 1) i
    (by omega)

/-- Below the truncation degree, the canonical inclusion of a truncation from above is an
isomorphism on cohomology. -/
theorem isIso_homology_truncLE {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE a (a + 1) rfl).obj E
  have ht := DerivedCategory.TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E
  have : T.obj₃.IsGE (a + 1) :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncGE (a + 1)).obj E).IsGE (a + 1))
  have : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_epi_shift_map_mor₁_iff T ht i).2
      ((T.obj₃.isZero_of_isGE (a + 1) i (by omega)).eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor A i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor A 0).homologySequence_mono_shift_map_mor₁_iff
      T ht (i - 1) i (by omega)).2
        ((T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)).eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor A i).map T.mor₁)

/-- A class of objects stable under isomorphism and containing the zero objects is inherited by
the cohomology of a truncation from above. -/
private theorem homology_truncLE_property {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (P : A → Prop)
    (hPiso : ∀ M M' : A, (M ≅ M') → P M → P M') (hPzero : ∀ M : A, IsZero M → P M)
    (E : DerivedCategory A) (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj E)) := by
  by_cases hi : i ≤ a
  · have := isIso_homology_truncLE E a i hi
    exact hPiso _ _ (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncLEι a).app E))).symm (hE i)
  · exact hPzero _ (DerivedCategory.isZero_of_isLE _ a i (by omega))

/-- A class of objects stable under isomorphism and containing the zero objects is inherited by
the cohomology of a truncation from below. -/
private theorem homology_truncGE_property {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] (P : A → Prop)
    (hPiso : ∀ M M' : A, (M ≅ M') → P M → P M') (hPzero : ∀ M : A, IsZero M → P M)
    (E : DerivedCategory A) (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a i : ℤ) :
    P ((DerivedCategory.homologyFunctor A i).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E)) := by
  by_cases hi : a ≤ i
  · have := isIso_homology_truncGE E a i hi
    exact hPiso _ _ (asIso ((DerivedCategory.homologyFunctor A i).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app E))) (hE i)
  · exact hPzero _ (DerivedCategory.isZero_of_isGE _ a i (by omega))

/-- A functor bounded above by `d` on the objects of a class, applied to an object concentrated
in a single degree `b` whose cohomology lies in that class, lands in degrees `≤ b + d`. -/
private theorem isLE_obj_of_pure {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (P : A → Prop) (hPiso : ∀ M M' : A, (M ≅ M') → P M → P M')
    (R : DerivedCategory A ⥤ DerivedCategory B) (d : ℤ)
    (hSingle : ∀ M : A, P M → ∀ n : ℤ,
      (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))
    (E : DerivedCategory A) (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (b : ℤ) (hGE : E.IsGE b) (hLE : E.IsLE b) : (R.obj E).IsLE (b + d) := by
  obtain ⟨M, ⟨e⟩⟩ := E.exists_iso_singleFunctor_obj_of_isGE_of_isLE b
  have hM : P M := hPiso _ _ ((DerivedCategory.homologyFunctor A b).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app M) (hE b)
  have := hSingle M hM b
  exact DerivedCategory.TStructure.t.isLE_of_iso (R.mapIso e.symm) (b + d)

/-- An exact functor bounded above by `d` on the objects of a class, applied to a bounded object
whose cohomology lies in that class, moves the upper bound by at most `d`.

The bounded object is split by the canonical truncation triangles into the finitely many pure
pieces to which `AlgebraicGeometry.isLE_obj_of_pure` applies. -/
@[sga "6 I 2.13" "special case"]
private theorem isLE_obj_of_bounded {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (P : A → Prop) (hPiso : ∀ M M' : A, (M ≅ M') → P M → P M')
    (hPzero : ∀ M : A, IsZero M → P M)
    (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated] (d : ℤ)
    (hSingle : ∀ M : A, P M → ∀ n : ℤ,
      (R.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + d))
    (E : DerivedCategory A) (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a b : ℤ) (hGE : E.IsGE a) (hLE : E.IsLE b) : (R.obj E).IsLE (b + d) := by
  suffices h : ∀ (m : ℕ) (K : DerivedCategory A)
      (_ : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj K)) (a' b' : ℤ),
      b' < a' + m → K.IsGE a' → K.IsLE b' → (R.obj K).IsLE (b' + d) from
    h (b - a + 1).toNat E hE a b (by omega) hGE hLE
  intro m
  induction m with
  | zero =>
      intro K _ a' b' hab hGE' hLE'
      have hz : IsZero K := (IsZero.iff_id_eq_zero K).2
        (DerivedCategory.TStructure.t.zero (𝟙 K) b' a' (by omega))
      exact DerivedCategory.TStructure.t.isLE_of_iso (R.map_isZero hz).isoZero.symm (b' + d)
  | succ m ih =>
      intro K hK a' b' hab hGE' hLE'
      let T := (DerivedCategory.TStructure.t.triangleLEGE (b' - 1) b' (by omega)).obj K
      have h₁ : (R.mapTriangle.obj T).obj₁.IsLE (b' - 1 + d) :=
        ih _ (homology_truncLE_property P hPiso hPzero K hK (b' - 1)) a' (b' - 1) (by omega)
          inferInstance inferInstance
      have h₃ : (R.mapTriangle.obj T).obj₃.IsLE (b' + d) :=
        isLE_obj_of_pure P hPiso R d hSingle _
          (homology_truncGE_property P hPiso hPzero K hK b') b' inferInstance inferInstance
      exact DerivedCategory.TStructure.t.isLE₂ (R.mapTriangle.obj T)
        (R.map_distinguished T
          (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b' - 1) b' (by omega) K))
        (b' + d)
        (DerivedCategory.TStructure.t.isLE_of_le _ (b' - 1 + d) (b' + d) (by omega)) h₃

/-! ### The tower of truncations of a complex with quasi-coherent cohomology -/

/-- The tower of canonical truncations from below of an object of `D(𝒪_X)` has a product in
`D(𝒪_X)`: each of its terms is bounded below. -/
private theorem hasProduct_truncGETower (X : Scheme.{u}) (E : DerivedCategory X.Modules) :
    HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩ := by
  obtain ⟨hp, -⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE
    (Stacks.DerivedLimit.truncGETower X.Modules E)
    (fun n ↦ ⟨-(n : ℤ), inferInstanceAs
      (((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E).IsGE (-(n : ℤ)))⟩)
  exact hp

/-- **Stacks 08D3**, with the category of `𝒪_X`-modules spelled as
`AlgebraicGeometry.Scheme.Modules`.

This is `AlgebraicGeometry.isIso_to_isDerivedLimit_truncGETower` verbatim. The two spellings of
the category are interchangeable up to unfolding `AlgebraicGeometry.Scheme.Modules`, so the
restatement is discharged by the original; stating it once keeps that unfolding out of the
proofs below, where it would otherwise have to happen inside instance search. -/
private theorem isIso_to_isDerivedLimit_truncGETower_modules (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    [hp : HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩]
    (L : DerivedCategory X.Modules) (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower X.Modules E).map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang (DerivedCategory X.Modules))
    (hc : ∀ n : ℕ, c ≫ p ≫ Pi.π (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c :=
  @isIso_to_isDerivedLimit_truncGETower X E hE hp L c p δ hL hc

/-- A complex of `𝒪_X`-modules with quasi-coherent cohomology is a derived limit of the tower of
its canonical truncations from below, the canonical truncation maps being the structural
projections.

This is Stacks 08D3 turned from a statement about an arbitrary presentation of the derived limit
into the Milnor triangle based at `E` itself. -/
private theorem isDerivedLimit_truncGETower_modules (X : Scheme.{u}) (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩] :
    IsDerivedLimit (Stacks.DerivedLimit.truncGETower X.Modules E) E := by
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower X.Modules E)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
    (fun n ↦ by
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) E)
    (isIso_to_isDerivedLimit_truncGETower_modules X E hE)
  exact ⟨_, δ, hδ⟩

/-! ### Quasi-coherence as a class of `𝒪_X`-modules -/

/-- Quasi-coherence of `𝒪_X`-modules is stable under isomorphism. -/
theorem isQuasicoherent_of_iso (X : Scheme.{u}) (M M' : X.Modules) (e : M ≅ M')
    (hM : M.IsQuasicoherent) : M'.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hM

/-- A zero `𝒪_X`-module is quasi-coherent. -/
theorem isQuasicoherent_of_isZero (X : Scheme.{u}) (M : X.Modules) (hM : IsZero M) :
    M.IsQuasicoherent :=
  isQuasicoherent_of_iso X 0 M hM.isoZero.symm (AlgebraicGeometry.isQuasicoherent_zero X)

/-- The cohomology of a truncation from above of a complex with quasi-coherent cohomology is
quasi-coherent. -/
theorem isQuasicoherent_homology_truncLE (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (a i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj E)).IsQuasicoherent :=
  homology_truncLE_property (fun M : X.Modules ↦ M.IsQuasicoherent) (isQuasicoherent_of_iso X)
    (isQuasicoherent_of_isZero X) E hE a i

/-- The cohomology of a truncation from below of a complex with quasi-coherent cohomology is
quasi-coherent. -/
theorem isQuasicoherent_homology_truncGE (X : Scheme.{u})
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (a i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E)).IsQuasicoherent :=
  homology_truncGE_property (fun M : X.Modules ↦ M.IsQuasicoherent) (isQuasicoherent_of_iso X)
    (isQuasicoherent_of_isZero X) E hE a i

/-! ### Stacks 08D4 -/

/-- **Stacks 08D4, part (3), the upper bound**, in the form the two public statements below use.
If the higher derived functors of `F` vanish in degrees `≥ N` on quasi-coherent modules, a total
right derived functor of `F` carries an object with quasi-coherent cohomology living in degrees
`≤ b` to an object living in degrees `≤ b + N - 1`.

First a weaker bound `c + N` is proved for any such object: it is the derived limit of the tower
of its truncations from below (`AlgebraicGeometry.isDerivedLimit_truncGETower`), `RF` carries
that derived limit to a derived limit because `F` preserves countable products (Stacks 08U1),
each term of the tower is bounded and so bounded above by `c + N - 1` after applying `RF`
(`AlgebraicGeometry.isLE_obj_of_bounded`), and a derived limit loses one degree
(`AlgebraicGeometry.isLE_of_isDerivedLimit`). Splitting `E` by the canonical truncation triangle
at `b` then recovers the sharp bound: the weaker estimate at `b - 1` and the pure-piece estimate
at `b` both give `b + N - 1`. -/
private theorem isLE_obj_of_quasicoherent (X : Scheme.{u})
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
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
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (b : ℤ) (hLE : E.IsLE b) : (R.obj E).IsLE (b + N - 1) := by
  let _ := Functor.IsRightDerivedFunctor.commShift R α
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F R α
  have hcomp := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective F R α
    Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
  have hSingle : ∀ M : X.Modules, M.IsQuasicoherent → ∀ n : ℤ,
      (R.obj ((DerivedCategory.singleFunctor X.Modules n).obj M)).IsLE (n + ((N : ℤ) - 1)) :=
    fun M hM n ↦ isLE_obj_single_of_vanishing F R α hcomp M ((N : ℤ) - 1)
      (fun p hp ↦ hv M hM p (by omega)) n
  have : HasProductsOfShape ℕ (DerivedCategory B) :=
    Stacks.DerivedProducts.hasProductsOfShape_nat
  have hweak : ∀ (K : DerivedCategory X.Modules),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
      ∀ c : ℤ, K.IsLE c → (R.obj K).IsLE (c + N) := by
    intro K hK c hc
    have := hasProduct_truncGETower X K
    obtain ⟨p, hp_triangle⟩ := isDerivedLimit_truncGETower_modules X K hK
    obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
      (F := F) (RF := R) (α := α) (Stacks.DerivedLimit.truncGETower X.Modules K) K p hp_triangle
    have hbound : ∀ n : ℕ,
        ((Stacks.DerivedLimit.truncGETower X.Modules K ⋙ R).obj ⟨n⟩).IsLE
          (c + ((N : ℤ) - 1)) := fun n ↦
      isLE_obj_of_bounded (fun M : X.Modules ↦ M.IsQuasicoherent)
        (isQuasicoherent_of_iso X) (isQuasicoherent_of_isZero X) R ((N : ℤ) - 1) hSingle _
        (isQuasicoherent_homology_truncGE X K hK (-(n : ℤ))) (-(n : ℤ)) c inferInstance
        inferInstance
    have h := isLE_of_isDerivedLimit (Stacks.DerivedLimit.truncGETower X.Modules K ⋙ R)
      (R.obj K) ⟨_, δ, hδ⟩ (c + ((N : ℤ) - 1)) hbound
    exact DerivedCategory.TStructure.t.isLE_of_le _ (c + ((N : ℤ) - 1) + 1) (c + N) (by omega)
  let T := (DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E
  have h₁ : (R.mapTriangle.obj T).obj₁.IsLE (b + N - 1) := by
    have h : (R.mapTriangle.obj T).obj₁.IsLE (b - 1 + N) :=
      hweak ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E)
        (isQuasicoherent_homology_truncLE X E hE (b - 1)) (b - 1) inferInstance
    exact DerivedCategory.TStructure.t.isLE_of_le _ (b - 1 + N) (b + N - 1) (by omega)
  have h₃ : (R.mapTriangle.obj T).obj₃.IsLE (b + N - 1) := by
    have h : (R.mapTriangle.obj T).obj₃.IsLE (b + ((N : ℤ) - 1)) :=
      isLE_obj_of_pure (fun M : X.Modules ↦ M.IsQuasicoherent)
        (isQuasicoherent_of_iso X) R ((N : ℤ) - 1) hSingle _
        (isQuasicoherent_homology_truncGE X E hE b) b inferInstance inferInstance
    exact DerivedCategory.TStructure.t.isLE_of_le _ (b + ((N : ℤ) - 1)) (b + N - 1) (by omega)
  exact DerivedCategory.TStructure.t.isLE₂ (R.mapTriangle.obj T)
    (R.map_distinguished T
      (DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E))
    (b + N - 1) h₁ h₃

section Scheme

variable (X : Scheme.{u}) {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  [HasProductsOfShape ℕ B] [HasExactLimitsOfShape (Discrete ℕ) B]
  (F : X.Modules ⥤ B) [F.Additive]
  [PreservesLimitsOfShape (Discrete ℕ) F]
  (RF : DerivedCategory X.Modules ⥤ DerivedCategory B)
  (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]

include F alpha in
/-- **Stacks 08D4, part (2).** Let `F` be an additive functor from the `𝒪_X`-modules of a scheme
to abelian groups which commutes with countable products, and suppose `R^pF` vanishes on
quasi-coherent modules for `p ≥ N`. Then for an object `E` of `D(𝒪_X)` with quasi-coherent
cohomology the canonical map `H^i(RF(E)) ⟶ H^i(RF(τ_{≥ b - N + 1}E))` is an isomorphism for
`i ≥ b`.

The canonical truncation triangle `τ_{≤ a-1}E ⟶ E ⟶ τ_{≥ a}E` at `a = b - N + 1` is carried by
`RF` to a distinguished triangle, `RF` being exact. Its first vertex lies in degrees
`≤ a - 1 + N - 1 = b - 1` by part (3)'s upper bound, so `H^i` and `H^{i+1}` vanish on it for
`i ≥ b`, and the long exact homology sequence makes the second map invertible on `H^i`. -/
theorem isIso_homologyFunctor_map_rightDerivedFunctor_truncGEπ_of_isZero
    (N : ℕ)
    (hRF : ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
      IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory X.Modules)
    (hE : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (RF.map ((DerivedCategory.TStructure.t.truncGEπ (b - (N : ℤ) + 1)).app E))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  let a := b - (N : ℤ) + 1
  let T := RF.mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLEGE (a - 1) a (by omega)).obj E)
  have hT : T ∈ distTriang (DerivedCategory B) := RF.map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (a - 1) a (by omega) E)
  have hl : T.obj₁.IsLE (a - 1 + N - 1) :=
    isLE_obj_of_quasicoherent X F RF alpha N hRF
      ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)
      (isQuasicoherent_homology_truncLE X E hE (a - 1)) (a - 1) inferInstance
  exact isIso_homology_map_mor₂_of_isLE T hT (a - 1 + N - 1) i (by dsimp [a]; omega)

include F alpha in
/-- **Stacks 08D4, part (3), the upper bound.** Let `F` be an additive functor from the
`𝒪_X`-modules of a scheme to abelian groups which commutes with countable products, and suppose
`R^pF` vanishes on quasi-coherent modules for `p ≥ N`. Then a total right derived functor of `F`
carries an object of `D(𝒪_X)` with quasi-coherent cohomology living in degrees `≤ b` to an object
living in degrees `≤ b + N - 1`. -/
theorem isLE_rightDerivedFunctor_obj_of_isZero
    (N : ℕ)
    (hRF : ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℤ, (N : ℤ) ≤ p →
      IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + (N : ℤ) - 1) :=
  isLE_obj_of_quasicoherent X F RF alpha N hRF E hcoh b hE

end Scheme

end AlgebraicGeometry

end
