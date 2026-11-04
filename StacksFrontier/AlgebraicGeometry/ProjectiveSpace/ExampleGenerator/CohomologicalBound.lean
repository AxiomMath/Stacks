module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.DegreewiseTwistVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.QuasiCoherentGenerator

/-!
# A cohomological bound on `ℙⁿ_A` from the twists `𝒪, 𝒪(-1), …, 𝒪(-n)`

Let `A` be a ring, `X = ℙⁿ_A = Proj A[T₀, …, Tₙ]` and `Z ∈ D_QCoh(𝒪_X)`. If every morphism
`𝒪_X(-d) ⟶ Z[j]` vanishes for `0 ≤ d ≤ n` and `j ≥ m`, then `Z ∈ D^{≤ m-1}`.

This is the quantitative form of [Stacks, Tag 0A9V]. The Koszul resolutions of [Stacks,
Tag 0BQS] exhibit every `𝒪_X(-N)`, `N ≥ 0`, as an iterated extension of the objects
`𝒪_X(-N+p)[1-p]`, `1 ≤ p ≤ n+1`; the objects `Y` with `Hom(Y, Z[j]) = 0` for all `j ≥ m` form a
class closed under extensions and under the shifts `[k]`, `k ≤ 0`, so every `𝒪_X(-N)` lies in
it. The degreewise form of [Stacks, Tag 0BQR],
`Stacks.AmpleNonvanishing.isZero_homology_of_hom_singleFunctor_eq_zero`, then kills `Hᵖ(Z)` for
each `p ≥ m`.

Everything is stated for an arbitrary model of the derived category.

## Main results

* `Stacks.AlgebraicGeometry.ExampleGenerator.singleFunctor_twistingSheaf_mem_leftOrthogonal`:
  every `𝒪_X(-N)`, `N ≥ 0`, is left orthogonal to the shifts `Z[j]`, `j ≥ m`, once the twists
  `𝒪_X(-d)`, `0 ≤ d ≤ n`, are.
* `Stacks.AlgebraicGeometry.ExampleGenerator.isLE_of_hom_singleFunctor_twistingSheaf_eq_zero`:
  the bound displayed above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjKoszulComplex
open StacksDraft.StupidTruncation
open HomologicalComplex

namespace Stacks.AlgebraicGeometry.ExampleGenerator

universe w u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (A : Type u) [CommRing A] (n : ℕ)

section Orthogonal

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, (shiftFunctor D k).Additive] [Pretriangulated D]

/-- The shifts `Z[j]` of an object `Z`, for `j ≥ m`. -/
def shiftsFrom (Z : D) (m : ℤ) : ObjectProperty D :=
  fun Y => ∃ j : ℤ, m ≤ j ∧ Nonempty (Y ≅ (shiftFunctor D j).obj Z)

/-- A morphism whose shift `[k]` vanishes after precomposing with an epimorphism is zero. -/
private theorem eq_zero_of_epi_comp_shift_map_eq_zero {C : Type*} [Category C] [HasShift C ℤ]
    [Preadditive C] [∀ k : ℤ, (shiftFunctor C k).Additive] {W X Y : C} (k : ℤ)
    (e : W ⟶ (shiftFunctor C k).obj X) [Epi e] (f : X ⟶ Y)
    (h : e ≫ (shiftFunctor C k).map f = 0) : f = 0 :=
  (Functor.map_eq_zero_iff _).1 ((cancel_epi e).1 (by rw [h, comp_zero]))

omit [HasZeroObject D] [Preadditive D] [∀ (k : ℤ), (shiftFunctor D k).Additive]
  [Pretriangulated D] in
/-- If `Y` is isomorphic to a shift `Z[j]` with `j ≥ m`, then so is `Y[k]` for every `k ≥ 0`. -/
theorem shiftsFrom_shift {Z : D} {m : ℤ} {Y : D} (hY : shiftsFrom Z m Y) (k : ℤ) (hk : 0 ≤ k) :
    shiftsFrom Z m ((shiftFunctor D k).obj Y) := by
  obtain ⟨j, hj, ⟨e⟩⟩ := hY
  exact ⟨j + k, by omega, ⟨(shiftFunctor D k).mapIso e ≪≫
    ((shiftFunctorAdd' D j k (j + k) rfl).app Z).symm⟩⟩

omit [HasZeroObject D] [Pretriangulated D] in
/-- An object left orthogonal to the shifts `Z[j]`, `j ≥ m`, stays so after a shift `[k]` with
`k ≤ 0`. -/
theorem shift_mem_leftOrthogonal_shiftsFrom {Z : D} {m : ℤ} {X : D}
    (hX : (shiftsFrom Z m).leftOrthogonal X) (k : ℤ) (hk : k ≤ 0) :
    (shiftsFrom Z m).leftOrthogonal ((shiftFunctor D k).obj X) := by
  intro Y f hY
  exact eq_zero_of_epi_comp_shift_map_eq_zero (-k)
    ((shiftFunctorCompIsoId D k (-k) (add_neg_cancel k)).inv.app X) f
    (hX _ (shiftsFrom_shift hY (-k) (by omega)))

omit [HasZeroObject D] [HasShift D ℤ] [∀ (k : ℤ), (shiftFunctor D k).Additive]
  [Pretriangulated D] in
/-- A left orthogonal class is closed under finite direct sums of copies of one object. -/
theorem constBiproduct_mem_leftOrthogonal [HasFiniteBiproducts D] (P : ObjectProperty D) {Y : D}
    (hY : P.leftOrthogonal Y) (J : Type) [Finite J] :
    P.leftOrthogonal (⨁ fun _ : J => Y) := by
  let _ := Fintype.ofFinite J
  intro W f hW
  refine biproduct.hom_ext' _ _ fun j => ?_
  rw [comp_zero]
  exact hY _ hW

end Orthogonal

variable {A n}

section Koszul

variable [HasDerivedCategory.{w} (Mods A n)]

/-- **One step of the quantitative Koszul descent.** If the `n + 1` twists
`𝒪_X(a+1), …, 𝒪_X(a+n+1)` are left orthogonal to every `Z[j]`, `j ≥ m`, so is `𝒪_X(a)`. The
Koszul complex at `a` is exact and concentrated in degrees `0, …, n+1`, and its stupid
filtration exhibits `𝒪_X(a)` as an iterated extension of the objects `𝒪_X(a+p)^{⊕}[1-p]`. -/
theorem singleFunctor_twistingSheaf_mem_leftOrthogonal_of_add (Z : DerivedCategory (Mods A n))
    (m a : ℤ)
    (h : ∀ p : ℕ, 0 < p → p ≤ n + 1 → (shiftsFrom Z m).leftOrthogonal
      ((DerivedCategory.singleFunctor (Mods A n) 0).obj
        (twistingSheaf (polyGrading A n) (a + (p : ℤ))))) :
    (shiftsFrom Z m).leftOrthogonal
      ((DerivedCategory.singleFunctor (Mods A n) 0).obj (twistingSheaf (polyGrading A n) a)) := by
  let K := koszulComplex A n a
  -- the bottom of the stupid filtration is `𝒪_X(a)` in degree zero
  let e₀ : stupidFiltration K 0 ≅
      (DerivedCategory.singleFunctor (Mods A n) 0).obj (twistingSheaf (polyGrading A n) a) :=
    (DerivedCategory.Q.mapIso (asIso (stupidTruncLEι K 0))).symm ≪≫
      DerivedCategory.Q.mapIso ((single (Mods A n) (.up ℤ) 0).mapIso
        (biproductUniqueIso (koszulFamily A n a 0) ≪≫
          eqToIso (congrArg (twistingSheaf (polyGrading A n)) (add_zero a)))) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (Mods A n) 0).app _).symm
  -- the top of the stupid filtration is the whole acyclic complex
  have htop : IsZero (stupidFiltration K (n + 1)) := by
    have hiso : K ≅ K.stupidTrunc (ComplexShape.embeddingUpIntLE ((n : ℤ) + 1)) :=
      asIso (K.πStupidTrunc (ComplexShape.embeddingUpIntLE ((n : ℤ) + 1)))
    have hac : IsZero (DerivedCategory.Q.obj K) :=
      DerivedCategory.isZero_Q_obj_of_acyclic _ (acyclic_koszulComplex A n a)
    have hz : IsZero (DerivedCategory.Q.obj
        (K.stupidTrunc (ComplexShape.embeddingUpIntLE (((n + 1 : ℕ) : ℤ))))) := by
      have he : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
      rw [he]
      exact hac.of_iso (DerivedCategory.Q.mapIso hiso.symm)
    exact hz
  refine (shiftsFrom Z m).leftOrthogonal.prop_of_iso e₀
    ((shiftsFrom Z m).leftOrthogonal.prop_of_isZero_of_stupidFiltration
      (U := stupidFiltration K)
      (B := fun p : ℕ => ((DerivedCategory.singleFunctor (Mods A n) 0).obj
        (K.X (p : ℤ)))⟦(1 - (p : ℤ) : ℤ)⟧)
      (n + 1) (fun p hp _ => exists_distTriang_stupidFiltration _ p hp) htop ?_)
  intro p hp hpM
  refine shift_mem_leftOrthogonal_shiftsFrom ?_ _ (by omega)
  refine (shiftsFrom Z m).leftOrthogonal.prop_of_iso
    (Functor.mapBiproduct (DerivedCategory.singleFunctor (Mods A n) 0)
      (koszulFamily A n a (p : ℤ))).symm ?_
  exact constBiproduct_mem_leftOrthogonal _ (h p hp hpM) (koszulIndex (n + 1) (p : ℤ))

/-- **The quantitative Koszul descent.** If the twists `𝒪_X(-d)`, `0 ≤ d ≤ n`, are left
orthogonal to every `Z[j]`, `j ≥ m`, then so is every `𝒪_X(-N)`, `N ≥ 0`. -/
theorem singleFunctor_twistingSheaf_mem_leftOrthogonal (Z : DerivedCategory (Mods A n)) (m : ℤ)
    (h : ∀ d : Fin (n + 1), (shiftsFrom Z m).leftOrthogonal
      ((DerivedCategory.singleFunctor (Mods A n) 0).obj
        (twistingSheaf (polyGrading A n) (-(d : ℤ)))))
    (N : ℕ) :
    (shiftsFrom Z m).leftOrthogonal
      ((DerivedCategory.singleFunctor (Mods A n) 0).obj
        (twistingSheaf (polyGrading A n) (-(N : ℤ)))) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases hN : N ≤ n
    · exact h ⟨N, by omega⟩
    · refine singleFunctor_twistingSheaf_mem_leftOrthogonal_of_add Z m _ fun p hp hpM => ?_
      have heq : -((N - p : ℕ) : ℤ) = -(N : ℤ) + (p : ℤ) := by
        rw [Nat.cast_sub (by omega : p ≤ N)]
        ring
      rw [← heq]
      exact ih (N - p) (by omega)

/-- `isLE_of_hom_singleFunctor_twistingSheaf_eq_zero` at the spelling `Mods A n`. -/
private theorem isLE_of_hom_singleFunctor_twistingSheaf_eq_zero_mods
    (Z : DerivedCategory (Mods A n))
    (hZ : ∀ i : ℤ, (SheafOfModules.isQuasicoherent (projRingSheaf (polyGrading A n)))
      ((DerivedCategory.homologyFunctor (Mods A n) i).obj Z))
    (m : ℤ) (h : ∀ (d : Fin (n + 1)) (j : ℤ), m ≤ j →
      ∀ f : (DerivedCategory.singleFunctor (Mods A n) 0).obj
          (twistingSheaf (polyGrading A n) (-(d : ℤ))) ⟶ (shiftFunctor _ j).obj Z, f = 0) :
    Z.IsLE (m - 1) := by
  have horth := singleFunctor_twistingSheaf_mem_leftOrthogonal Z m fun d Y f ⟨j, hj, ⟨e⟩⟩ => by
    rw [← cancel_mono e.hom, zero_comp]
    exact h d j hj _
  rw [DerivedCategory.isLE_iff]
  intro p hp
  let : HasDerivedCategory.{w} (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
    ‹HasDerivedCategory.{w} (Mods A n)›
  refine Stacks.AmpleNonvanishing.isZero_homology_of_hom_singleFunctor_eq_zero
    (AlgebraicGeometry.Proj (polyGrading A n)) (twistModule A n 1) (isAmple_twistModule_one A n)
    (fun M => ∃ N : ℕ, M = twistModule A n (-(N : ℤ))) ?_ Z hZ p ?_
  · intro F hqc hft
    obtain ⟨r, d, hd, φ, hφ⟩ := exists_epi_coproduct_twist_nonpos A n F hqc hft
    refine ⟨r, fun j => twistModule A n (d j), fun j => ⟨(d j).natAbs, ?_⟩, φ, hφ⟩
    have hdj : -((d j).natAbs : ℤ) = d j := by have := hd j; omega
    rw [hdj]
  · rintro M ⟨N, rfl⟩ f
    let g : (DerivedCategory.singleFunctor (Mods A n) p).obj
        (twistingSheaf (polyGrading A n) (-(N : ℤ))) ⟶ Z := f
    let e := ((DerivedCategory.singleFunctors (Mods A n)).shiftIso p 0 p (by ring)).app
      (twistingSheaf (polyGrading A n) (-(N : ℤ)))
    exact eq_zero_of_epi_comp_shift_map_eq_zero p e.inv g (horth N _ ⟨p, by omega, ⟨Iso.refl _⟩⟩)

end Koszul

/-- **A cohomological bound on `ℙⁿ_A`.** Let `Z ∈ D_QCoh(𝒪_X)` for `X = ℙⁿ_A`. If every
morphism `𝒪_X(-d) ⟶ Z[j]` is zero for `0 ≤ d ≤ n` and `j ≥ m`, then `Z ∈ D^{≤ m-1}`. -/
theorem isLE_of_hom_singleFunctor_twistingSheaf_eq_zero
    [hD : HasDerivedCategory.{w} (AlgebraicGeometry.Proj (polyGrading A n)).Modules]
    (Z : DerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)).Modules)
    (hZ : ∀ i : ℤ, (SheafOfModules.isQuasicoherent
      (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)
      ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.Proj (polyGrading A n)).Modules i).obj Z))
    (m : ℤ) (h : ∀ (d : Fin (n + 1)) (j : ℤ), m ≤ j →
      ∀ f : (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj (polyGrading A n)).Modules 0).obj
          (twistingSheaf (polyGrading A n) (-(d : ℤ))) ⟶ (shiftFunctor _ j).obj Z, f = 0) :
    Z.IsLE (m - 1) :=
  @isLE_of_hom_singleFunctor_twistingSheaf_eq_zero_mods A _ n hD Z hZ m h

end Stacks.AlgebraicGeometry.ExampleGenerator

end
