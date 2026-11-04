module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Nilpotent.Basic
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Derived complete objects and modules

Let `A` be a commutative ring, `I ⊆ A` an ideal and `D(A)` the derived category of `A`-modules.
Let `(Kₙ)` be an inverse system in `D(A)` such that for every `f ∈ I` and every `n` some power
`fᵉ` is zero on `Kₙ`. Then for every `K ∈ D(A)` the derived limit `Rlim (K ⊗ᴸ Kₙ)` is derived
complete with respect to `I`.

## Main definitions

* `oneSubSmulShift`: the endomorphism `(xₙ) ↦ (xₙ - f xₙ₊₁)` of `∏ₙ K`.
* `IsDerivedCompleteAt`: the condition `T(K, f) = 0`, derived completeness at a single element.
* `IsDerivedComplete`: `T(K, f) = 0` for every `f ∈ I`.
* `milnorMap`: the map `1 - shift : ∏ Dₙ ⟶ ∏ Dₙ` of a tower `(Dₙ)`.
* `IsMilnorTriangle`: the condition that the Milnor triangle `L → ∏ Dₙ → ∏ Dₙ → L⟦1⟧` of a
  tower is distinguished.
* `IsDerivedCompleteModule`: derived completeness of a module, that is, of the complex
  concentrated in degree zero at that module.

## Main results

* `isDerivedCompleteAt_of_isNilpotent`: if `f` acts nilpotently on `L`, then `T(L, f) = 0`.
* `isDerivedCompleteAt_pi`: `T(-, f) = 0` is stable under countable products.
* `isDerivedCompleteAt_of_distTriang`: if `T(-, f) = 0` holds for the second and third objects
  of a distinguished triangle, it holds for the first.
* `isDerivedComplete_of_isMilnorTriangle`: derived limits of the tower `(K ⊗ᴸ Kₙ)` are derived
  complete.
* `exists_isDerivedLimit_isZero_iff_isIso`: an inverse system has a zero derived limit exactly
  when its difference map is an isomorphism.
* `isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero`: `T(K, f) = 0` in the sense of
  Stacks 091S — the tower `⋯ →f K →f K` has a derived limit which is a zero object — agrees
  with `IsDerivedCompleteAt`.

## Implementation notes

The derived tensor product and the derived limit are modelled by their structural properties.
The functor `K ⊗ᴸ (-)` is replaced by an arbitrary additive `A`-linear endofunctor `F` of `D(A)`.
Being a derived limit of a tower is `CategoryTheory.Pretriangulated.IsDerivedLimit`: the object
sits in a distinguished triangle `L → ∏ Dₙ → ∏ Dₙ → L⟦1⟧` whose middle map is `1 - shift`, with
the tower presented as a functor `ℕᵒᵖ ⥤ D(A)` via `CategoryTheory.Functor.ofOpSequence`.
The condition `T(K, f) = 0` is defined as `oneSubSmulShift` being an isomorphism, one of the
equivalent characterisations of Stacks 091P. Countable products in `D(A)` are assumed via
`HasProductsOfShape ℕ`.
Derived completeness itself needs neither triangles nor `D(A)`, so it is stated for an arbitrary
`A`-linear preadditive category with countable products over a commutative semiring `A`.

## References

* [Stacks Project, Tag 091S](https://stacks.math.columbia.edu/tag/091S)
* [Stacks Project, Tag 091W](https://stacks.math.columbia.edu/tag/091W)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Linear

variable {A : Type*} [CommSemiring A]

/-- Powers of the action of a scalar on `K`: `(f • 𝟙 K)ᵉ = fᵉ • 𝟙 K`. -/
theorem smul_id_pow {C : Type*} [Category C] [Preadditive C] [Linear A C] (K : C) (f : A) (e : ℕ) :
    (f • (1 : End K)) ^ e = f ^ e • 𝟙 K := by
  rw [smul_pow, one_pow]
  rfl

/-- An additive `A`-linear functor preserves nilpotence of the action of `f`. -/
theorem isNilpotent_smul_id_map {C E : Type*} [Category C] [Category E] [Preadditive C]
    [Preadditive E] [Linear A C] [Linear A E] (F : C ⥤ E) [F.Additive] [F.Linear A] {L : C}
    {f : A} (hf : IsNilpotent (f • (1 : End L))) :
    IsNilpotent (f • (1 : End (F.obj L))) := by
  obtain ⟨e, he⟩ := hf
  rw [smul_id_pow] at he
  refine ⟨e, ?_⟩
  rw [smul_id_pow]
  have h1 : F.map (f ^ e • 𝟙 L) = f ^ e • 𝟙 (F.obj L) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  rw [he, Functor.map_zero] at h1
  exact h1.symm

/-- The Milnor map `1 - shift : ∏ Dₙ ⟶ ∏ Dₙ` of a tower `(Dₙ)` with transition maps
`t n : D (n+1) ⟶ D n`; its `n`-th component is `π n - (π (n+1) ≫ t n)`. -/
def milnorMap {C : Type*} [Category C] [Preadditive C] [HasProductsOfShape ℕ C] (D : ℕ → C)
    (t : ∀ n, D (n + 1) ⟶ D n) : (∏ᶜ D) ⟶ (∏ᶜ D) :=
  Pi.lift (fun n : ℕ => Pi.π D n - Pi.π D (n + 1) ≫ t n)

/-- The `n`-th component of the Milnor map of a tower. -/
@[simp]
theorem milnorMap_π {C : Type*} [Category C] [Preadditive C] [HasProductsOfShape ℕ C]
    (D : ℕ → C) (t : ∀ n, D (n + 1) ⟶ D n) (n : ℕ) :
    milnorMap D t ≫ Pi.π D n = Pi.π D n - Pi.π D (n + 1) ≫ t n := by
  rw [milnorMap, Pi.lift_π]

/-- The endomorphism `1 - f • shift` of `∏ₙ K`, that is, `(xₙ) ↦ (xₙ - f·xₙ₊₁)`. -/
def oneSubSmulShift {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] (K : C) (f : A) :
    (∏ᶜ fun _ : ℕ => K) ⟶ (∏ᶜ fun _ : ℕ => K) :=
  milnorMap (fun _ : ℕ => K) (fun _ => f • 𝟙 K)

/-- The `n`-th component of `oneSubSmulShift K f`. -/
@[simp]
theorem oneSubSmulShift_π {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] (K : C) (f : A) (n : ℕ) :
    oneSubSmulShift K f ≫ Pi.π (fun _ : ℕ => K) n
      = Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1) := by
  rw [oneSubSmulShift, milnorMap_π, Linear.comp_smul, Category.comp_id]

/-- For any morphism `g : L ⟶ M`, the endomorphisms `oneSubSmulShift L f` and
`oneSubSmulShift M f` are intertwined by `Pi.map (fun _ : ℕ => g)`. -/
theorem oneSubSmulShift_naturality {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {L M : C} (f : A) (g : L ⟶ M) :
    oneSubSmulShift L f ≫ Limits.Pi.map (fun _ : ℕ => g)
      = Limits.Pi.map (fun _ : ℕ => g) ≫ oneSubSmulShift M f := by
  apply Limits.Pi.hom_ext
  intro m
  simp [oneSubSmulShift, milnorMap, Limits.Pi.map,
    Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp, Linear.comp_smul,
    Category.assoc]

/-- An additive `A`-linear functor intertwines `oneSubSmulShift` with the product comparison map. -/
private theorem piComparison_comp_oneSubSmulShift_map {C E : Type*} [Category C] [Category E]
    [Preadditive C] [Preadditive E] [Linear A C] [Linear A E] [HasProductsOfShape ℕ C]
    [HasProductsOfShape ℕ E] (F : C ⥤ E) [F.Additive] [F.Linear A] (K : C) (f : A) :
    piComparison F (fun _ : ℕ => K) ≫ oneSubSmulShift (F.obj K) f
      = F.map (oneSubSmulShift K f) ≫ piComparison F (fun _ : ℕ => K) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, oneSubSmulShift_π, Preadditive.comp_sub, Linear.comp_smul,
    piComparison_comp_π, piComparison_comp_π, Category.assoc, piComparison_comp_π]
  rw [← F.map_comp, oneSubSmulShift_π, F.map_sub, Functor.Linear.map_smul]

/-- `oneSubSmulShift` is compatible with the shift functor: shifting `∏ₙ K` and comparing with
`∏ₙ K⟦1⟧` intertwines `oneSubSmulShift K⟦1⟧ f` with the shift of `oneSubSmulShift K f`. -/
theorem piComparison_comp_oneSubSmulShift {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] [HasShift C ℤ] [(shiftFunctor C (1 : ℤ)).Additive]
    [(shiftFunctor C (1 : ℤ)).Linear A] (K : C) (f : A) :
    piComparison (shiftFunctor C (1 : ℤ)) (fun _ : ℕ => K) ≫
        oneSubSmulShift ((shiftFunctor C (1 : ℤ)).obj K) f
      = (shiftFunctor C (1 : ℤ)).map (oneSubSmulShift K f) ≫
        piComparison (shiftFunctor C (1 : ℤ)) (fun _ : ℕ => K) :=
  piComparison_comp_oneSubSmulShift_map _ K f

/-- The condition `T(K,f) = 0`, where `T(K,f)` is the derived limit of the tower `⋯ →f K →f K`:
`K` is derived complete with respect to the single element `f`, expressed as
`oneSubSmulShift K f` being an isomorphism. -/
def IsDerivedCompleteAt {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] (K : C) (f : A) : Prop :=
  IsIso (oneSubSmulShift K f)

/-- `T(K,f) = 0` means exactly that `oneSubSmulShift K f` is an isomorphism. -/
theorem isDerivedCompleteAt_iff_isIso {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {K : C} {f : A} :
    IsDerivedCompleteAt K f ↔ IsIso (oneSubSmulShift K f) := Iff.rfl

/-- `K` is derived complete with respect to the ideal `I` if `T(K,f) = 0` for every `f ∈ I`. -/
@[stacks 091S "(1)"]
def IsDerivedComplete {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] (I : Ideal A) (K : C) : Prop :=
  ∀ f ∈ I, IsDerivedCompleteAt K f

/-- `K` is derived complete with respect to `I` exactly when `T(K,f) = 0` for every `f ∈ I`. -/
theorem isDerivedComplete_iff_forall_isDerivedCompleteAt {C : Type*} [Category C] [Preadditive C]
    [Linear A C] [HasProductsOfShape ℕ C] {I : Ideal A} {K : C} :
    IsDerivedComplete I K ↔ ∀ f ∈ I, IsDerivedCompleteAt K f := Iff.rfl

/-- If `f` acts nilpotently on `L`, then `T(L,f) = 0`. -/
theorem isDerivedCompleteAt_of_isNilpotent {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {L : C} {f : A} (hf : IsNilpotent (f • (1 : End L))) :
    IsDerivedCompleteAt L f := by
  obtain ⟨e, he⟩ := hf
  rw [smul_id_pow] at he
  rw [isDerivedCompleteAt_iff_isIso]
  set P : C := ∏ᶜ fun _ : ℕ => L
  set S : End P := Pi.lift (fun n : ℕ => f • Pi.π (fun _ : ℕ => L) (n + 1)) with hS
  have hSpi : ∀ m : ℕ, S ≫ Pi.π (fun _ : ℕ => L) m = f • Pi.π (fun _ : ℕ => L) (m + 1) := by
    intro m
    rw [hS, Pi.lift_π]
  have key : ∀ (k n : ℕ),
      (S ^ k) ≫ Pi.π (fun _ : ℕ => L) n = f ^ k • Pi.π (fun _ : ℕ => L) (n + k) := by
    intro k
    induction k with
    | zero =>
        intro n
        simp
    | succ k ih =>
        intro n
        have hpow : (S ^ (k + 1) : End P) = S ≫ (S ^ k) := by
          rw [pow_succ]; rfl
        rw [hpow, Category.assoc, ih n, Linear.comp_smul, hSpi]
        rw [smul_smul, pow_succ]
        rfl
  have hSe : (S ^ e : End P) = 0 := by
    apply Limits.limit.hom_ext
    intro j
    have hj : ∀ n : ℕ, (S ^ e) ≫ Pi.π (fun _ : ℕ => L) n = 0 := by
      intro n
      rw [key e n]
      have : f ^ e • Pi.π (fun _ : ℕ => L) (n + e)
          = Pi.π (fun _ : ℕ => L) (n + e) ≫ (f ^ e • 𝟙 L) := by
        rw [Linear.comp_smul, Category.comp_id]
      rw [this, he]
      simp
    simpa using hj j.as
  have hsplit : oneSubSmulShift L f = (1 : End P) - S := by
    apply Limits.limit.hom_ext
    intro j
    rw [oneSubSmulShift_π L f j.as]
    have h1 : (1 : End P) = 𝟙 P := rfl
    rw [Preadditive.sub_comp, h1, Category.id_comp, hSpi]
  have hnil : IsNilpotent S := ⟨e, hSe⟩
  have hunit : IsUnit ((1 : End P) - S) := hnil.isUnit_one_sub
  rw [← hsplit] at hunit
  exact (CategoryTheory.isUnit_iff_isIso (X := P) (oneSubSmulShift L f)).mp hunit

/-- If `T(D n, f) = 0` for every `n`, then `T(∏ₙ D n, f) = 0`. -/
theorem isDerivedCompleteAt_pi {C : Type*} [Category C] [Preadditive C] [Linear A C]
    [HasProductsOfShape ℕ C] {D : ℕ → C} {f : A} (hD : ∀ n, IsDerivedCompleteAt (D n) f) :
    IsDerivedCompleteAt (∏ᶜ D) f := by
  rw [isDerivedCompleteAt_iff_isIso]
  set X : C := ∏ᶜ (fun _ : ℕ => ∏ᶜ D)
  set Y : C := ∏ᶜ (fun n : ℕ => ∏ᶜ (fun _ : ℕ => D n))
  let ehom : X ⟶ Y :=
    Pi.lift (fun n : ℕ => Pi.lift (fun j : ℕ =>
      Pi.π (fun _ : ℕ => ∏ᶜ D) j ≫ Pi.π D n))
  let einv : Y ⟶ X :=
    Pi.lift (fun j : ℕ => Pi.lift (fun n : ℕ =>
      Pi.π (fun n : ℕ => ∏ᶜ (fun _ : ℕ => D n)) n ≫ Pi.π (fun _ : ℕ => D n) j))
  have hhi : ehom ≫ einv = 𝟙 X := by
    apply Limits.Pi.hom_ext
    intro j
    apply Limits.Pi.hom_ext
    intro n
    simp only [ehom, einv, Category.assoc, Category.id_comp, Limits.Pi.lift_π,
      Limits.Pi.lift_π_assoc]
  have hih : einv ≫ ehom = 𝟙 Y := by
    apply Limits.Pi.hom_ext
    intro n
    apply Limits.Pi.hom_ext
    intro j
    simp only [ehom, einv, Category.assoc, Category.id_comp, Limits.Pi.lift_π,
      Limits.Pi.lift_π_assoc]
  have : ∀ n : ℕ, IsIso (oneSubSmulShift (D n) f) := fun n =>
    isDerivedCompleteAt_iff_isIso.mp (hD n)
  let g : Y ⟶ Y := Limits.Pi.map (fun n : ℕ => oneSubSmulShift (D n) f)
  have : IsIso g := by
    apply Limits.Pi.map_isIso
  have hconj : oneSubSmulShift (∏ᶜ D) f = ehom ≫ g ≫ einv := by
    apply Limits.Pi.hom_ext
    intro j
    apply Limits.Pi.hom_ext
    intro n
    simp only [oneSubSmulShift, milnorMap, ehom, einv, g, Category.assoc,
      Limits.Pi.lift_π, Limits.Pi.lift_π_assoc,
      Limits.Pi.map_π_assoc,
      Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
      Linear.comp_smul, Category.comp_id]
  rw [hconj]
  have : IsIso ehom := ⟨einv, hhi, hih⟩
  have : IsIso einv := ⟨ehom, hih, hhi⟩
  infer_instance

universe u

/-- An additive `A`-linear functor preserving countable products preserves derived completeness
at a scalar. -/
theorem isDerivedCompleteAt_map {A : Type u} [CommRing A]
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear A C] [Linear A D] [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D]
    (F : C ⥤ D) [F.Additive] [F.Linear A] (K : C) (a : A)
    [PreservesLimit (Discrete.functor (fun _ : ℕ => K)) F]
    (hK : IsDerivedCompleteAt K a) : IsDerivedCompleteAt (F.obj K) a := by
  rw [isDerivedCompleteAt_iff_isIso] at hK ⊢
  let e := piComparison F (fun _ : ℕ => K)
  have he := piComparison_comp_oneSubSmulShift_map F K a
  have h1 : IsIso (F.map (oneSubSmulShift K a) ≫ e) := inferInstance
  rw [← he] at h1
  exact IsIso.of_isIso_comp_left e _

/-- Derived completeness is stable under shifts. -/
theorem isDerivedComplete_shift {A : Type u} [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsDerivedComplete I K) (n : ℤ) :
    IsDerivedComplete I (K⟦n⟧) := fun a ha =>
  isDerivedCompleteAt_map (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n) K a (hK a ha)

end Linear

section DerivedLimit

section

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- An inverse system has a derived limit which is a zero object exactly when its difference
map `(kₙ) ↦ (kₙ - fₙ₊₁(kₙ₊₁))` is an isomorphism. -/
theorem exists_isDerivedLimit_isZero_iff_isIso (F : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] :
    (∃ L : D, IsDerivedLimit F L ∧ IsZero L) ↔
      IsIso (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) := by
  constructor
  · rintro ⟨L, ⟨p, δ, hT⟩, hL⟩
    exact (Triangle.isZero₁_iff_isIso₂ _ hT).1 hL
  · intro h
    obtain ⟨L, p, δ, hT⟩ := exists_isDerivedLimit F
    exact ⟨L, ⟨p, δ, hT⟩, (Triangle.isZero₁_iff_isIso₂ _ hT).2 h⟩

end

variable {A : Type*} [CommSemiring A]

variable {D : Type*} [Category D] [Preadditive D] [Linear A D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasProductsOfShape ℕ D]

/-- `T(K,f) = 0` in the formulation of Stacks 091S — the tower with constant value `K` and
transition map multiplication by `f` has a derived limit which is a zero object — is exactly
derived completeness of `K` at `f`. -/
theorem isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero (K : D) (f : A) :
    IsDerivedCompleteAt K f ↔
      ∃ L : D, IsDerivedLimit (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) L ∧
        IsZero L := by
  have key : ∀ L : D,
      IsDerivedLimit (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) L →
      (IsZero L ↔ IsIso (oneSubSmulShift K f)) := by
    rintro L ⟨p, δ, hT⟩
    have h := Triangle.isZero₁_iff_isIso₂ _ hT
    simp only [Triangle.mk_obj₁, Triangle.mk_mor₂,
      Functor.ofOpSequence_map_homOfLE_succ] at h
    exact h
  constructor
  · intro h
    obtain ⟨L, hL⟩ :=
      exists_isDerivedLimit (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K))
    exact ⟨L, hL, (key L hL).mpr h⟩
  · rintro ⟨L, hL, hzero⟩
    exact (key L hL).mp hzero

/-- Derived completeness with respect to `I` in the formulation of Stacks 091S: for every
`f ∈ I` the tower `⋯ →f K →f K` has a derived limit which is a zero object. -/
theorem isDerivedComplete_iff_forall_exists_isDerivedLimit_isZero (I : Ideal A) (K : D) :
    IsDerivedComplete I K ↔
      ∀ f ∈ I, ∃ L : D,
        IsDerivedLimit (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) L ∧
          IsZero L :=
  forall₂_congr fun f _ => isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero K f

end DerivedLimit

section Module

universe v

variable {A : Type*} [CommRing A]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]

/-- An `A`-module is derived complete with respect to `I` when the corresponding object of
`D(A)`, concentrated in degree zero, is derived complete. -/
@[stacks 091S "(2)"]
def IsDerivedCompleteModule (I : Ideal A) (M : ModuleCat.{v} A) : Prop :=
  IsDerivedComplete I ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)

/-- A module is derived complete with respect to `I` exactly when the complex concentrated in
degree zero at that module is derived complete. -/
theorem isDerivedCompleteModule_iff_isDerivedComplete (I : Ideal A) (M : ModuleCat.{v} A) :
    IsDerivedCompleteModule I M ↔
      IsDerivedComplete I ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) :=
  Iff.rfl

end Module

section Triangulated

variable {A : Type*} [CommRing A]
  [HasProductsOfShape ℕ (DerivedCategory (ModuleCat A))]

/-- If the second and third objects of a distinguished triangle are derived complete at `f`, then
so is the first. -/
theorem isDerivedCompleteAt_of_distTriang {T : Triangle (DerivedCategory (ModuleCat A))}
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat A))) {f : A}
    (h₂ : IsDerivedCompleteAt T.obj₂ f) (h₃ : IsDerivedCompleteAt T.obj₃ f) :
    IsDerivedCompleteAt T.obj₁ f := by
  rw [isDerivedCompleteAt_iff_isIso]
  have hPTdist := productTriangle_distinguished (J := ℕ) (fun _ : ℕ => T) (fun _ => hT)
  let φ : productTriangle (fun _ : ℕ => T) ⟶ productTriangle (fun _ : ℕ => T) :=
    Triangle.homMk (productTriangle (fun _ : ℕ => T)) (productTriangle (fun _ : ℕ => T))
      (oneSubSmulShift T.obj₁ f) (oneSubSmulShift T.obj₂ f) (oneSubSmulShift T.obj₃ f)
      (by
        rw [productTriangle_mor₁]
        exact (oneSubSmulShift_naturality f _).symm)
      (by
        rw [productTriangle_mor₂]
        exact (oneSubSmulShift_naturality f _).symm)
      (by
        rw [productTriangle_mor₃]
        show (Limits.Pi.map (fun _ : ℕ => T.mor₃) ≫
            inv (piComparison (shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ))
              (fun _ : ℕ => T.obj₁))) ≫
              (shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ)).map
                (oneSubSmulShift T.obj₁ f)
          = oneSubSmulShift T.obj₃ f ≫
            (Limits.Pi.map (fun _ : ℕ => T.mor₃) ≫
              inv (piComparison (shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ))
                (fun _ : ℕ => T.obj₁)))
        set pc := piComparison (shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ))
          (fun _ : ℕ => T.obj₁)
        have hnat := oneSubSmulShift_naturality f T.mor₃
        have hshift' :
            oneSubSmulShift ((shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ)).obj T.obj₁) f
                ≫ inv pc
              = inv pc ≫ (shiftFunctor (DerivedCategory (ModuleCat A)) (1 : ℤ)).map
                  (oneSubSmulShift T.obj₁ f) := by
          rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
          exact piComparison_comp_oneSubSmulShift T.obj₁ f
        rw [Category.assoc, ← hshift', ← Category.assoc, ← hnat, Category.assoc])
  exact isIso₁_of_isIso₂₃ φ hPTdist hPTdist (isDerivedCompleteAt_iff_isIso.mp h₂)
    (isDerivedCompleteAt_iff_isIso.mp h₃)

/-- The Milnor triangle `L → ∏ Dₙ --(1 - shift)--> ∏ Dₙ → L⟦1⟧` of the tower `(Dₙ)` built from
`ι` and `δ` is distinguished; equivalently, `L` is a derived limit of `(Dₙ)` via `ι` and `δ`. -/
def IsMilnorTriangle (D : ℕ → DerivedCategory (ModuleCat A)) (t : ∀ n, D (n + 1) ⟶ D n)
    (L : DerivedCategory (ModuleCat A)) (ι : L ⟶ ∏ᶜ D) (δ : (∏ᶜ D) ⟶ L⟦(1 : ℤ)⟧) : Prop :=
  Triangle.mk ι (milnorMap D t) δ ∈ distinguishedTriangles

/-- Let `A` be a ring and `I ⊂ A` an ideal. Let `(Kₙ)` be an inverse system of objects of `D(A)`
(objects `Ksys n`, transition maps `Kt n : Ksys (n+1) ⟶ Ksys n`) such that for every `f ∈ I` and
every `n` the scalar `f` acts nilpotently on `Ksys n`. Let `F` be an additive `A`-linear
endofunctor of `D(A)`, standing for `K ⊗ᴸ (-)`. Then any derived limit `K'` of the tower
`(F.obj (Ksys n))` is derived complete with respect to `I`. -/
@[stacks 091W]
theorem
    isDerivedComplete_of_isMilnorTriangle (I : Ideal A) (Ksys : ℕ → DerivedCategory (ModuleCat A))
    (Kt : ∀ n, Ksys (n + 1) ⟶ Ksys n) (hnil : ∀ f ∈ I, ∀ n, IsNilpotent (f • (1 : End (Ksys n))))
    (F : DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A)) [F.Additive] [F.Linear A]
    (K' : DerivedCategory (ModuleCat A)) {ι : K' ⟶ ∏ᶜ fun n => F.obj (Ksys n)}
    {δ : (∏ᶜ fun n => F.obj (Ksys n)) ⟶ K'⟦(1 : ℤ)⟧}
    (hMilnor : IsMilnorTriangle (fun n => F.obj (Ksys n)) (fun n => F.map (Kt n)) K' ι δ) :
    IsDerivedComplete I K' := by
  intro f hf
  have hprod : IsDerivedCompleteAt (∏ᶜ fun n : ℕ => F.obj (Ksys n)) f :=
    isDerivedCompleteAt_pi fun n =>
      isDerivedCompleteAt_of_isNilpotent (isNilpotent_smul_id_map F (hnil f hf n))
  exact isDerivedCompleteAt_of_distTriang hMilnor hprod hprod

end Triangulated

end
