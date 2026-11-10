module

public import StacksFrontier.Homology.Tor.ProductNaturality
public import StacksFrontier.AlgebraicGeometry.Varieties.Kunneth

/-!
# The Künneth formula for the derived tensor product over a field, in canonical form

Let `R` be a field and let `K` and `L` be objects of `D(R)`. Tensoring cocycles gives the
cohomology product of [Stacks, Tag 068H],

`Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗^𝐋_R L)`,

which is `RingTheory.TorProducts.cohomologyTensorProduct`. This file proves that **the sum of
these products over all `i + j = n`,**

`⨁_{i + j = n} Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁿ(K ⊗^𝐋_R L)`,

**is bijective**, with no boundedness hypothesis on `K` or `L`. This is the canonical form of the
Künneth formula over a field; the library had it only in degree zero
(`CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero`) and, in every degree, as an
abstract isomorphism (`CochainComplex.Kunneth.nonempty_kunnethIso_of_field`).

## Main definitions

* `Stacks.WeilDeRham.crossProductCast`: the cohomology product of a pair of degrees `(i, j)`, read
  in a degree `n` with `i + j = n`.
* `Stacks.WeilDeRham.kunnethSum`: the sum of the cohomology products over `i + j = n`.

## Main results

* `Stacks.WeilDeRham.isKProjective_of_d_eq_zero`: a complex of projective modules with zero
  differentials is K-projective.
* `Stacks.WeilDeRham.bijective_kunnethSum`: **over a field the sum of the cohomology products
  in complementary degrees is bijective.**

## The argument

Over a field every complex receives a quasi-isomorphism from the complex of its cohomology
modules with zero differentials, and such a complex is K-projective and K-flat. The cohomology
product is natural along morphisms out of K-projective K-flat objects
(`RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective`) and is computed on
them by tensoring cocycles
(`TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective`). For two complexes with zero
differentials every cochain is a cocycle and no cochain is a nonzero coboundary, so the sum of
the products is the identification of the direct sum `⨁_{i + j = n} Eⁱ ⊗ Gʲ` with the degree-`n`
term of the total tensor complex.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 0FMB](https://stacks.math.columbia.edu/tag/0FMB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CochainComplex.DerivedTensor
open scoped TensorProduct DirectSum

universe u


namespace Stacks.WeilDeRham

/-! ### Complexes with zero differentials -/

section ZeroDifferential

variable {R : Type u} [CommRing R]

/-- **A complex of projective modules with zero differentials is K-projective.** A chain map
`f` to an acyclic complex `L` lands in the cocycles of `L`, which are the coboundaries; lifting
each `fⁱ` through `d : Lⁱ⁻¹ ⟶ Zⁱ(L)`, which the projectivity of the source allows, gives a
homotopy from `f` to zero, the differentials of the source being zero. -/
theorem isKProjective_of_d_eq_zero (E : CochainComplex (ModuleCat.{u} R) ℤ)
    (hd : ∀ i j, E.d i j = 0) (hE : ∀ i, Projective (E.X i)) : E.IsKProjective where
  nonempty_homotopy_zero {L} f hL := by
    have hlift : ∀ i : ℤ, ∃ h : E.X i ⟶ L.X (i - 1), h ≫ L.d (i - 1) i = f.f i := by
      intro i
      have hex : (L.sc' (i - 1) i (i + 1)).Exact :=
        (L.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)).1 (hL i)
      have hw : f.f i ≫ (L.sc' (i - 1) i (i + 1)).g = 0 := by
        change f.f i ≫ L.d i (i + 1) = 0
        rw [f.comm, hd, zero_comp]
      have := hE i
      exact ⟨hex.liftFromProjective (f.f i) hw, hex.liftFromProjective_comp (f.f i) hw⟩
    choose h hh using hlift
    refine ⟨{
      hom := fun i j => if hij : i = j + 1 then
        h i ≫ (L.XIsoOfEq (show i - 1 = j by omega)).hom else 0
      zero := fun i j hij => dite_eq_right (fun h' => hij (by simp [ComplexShape.up_Rel]; omega))
      comm := fun i => ?_ }⟩
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp), hd, zero_comp, zero_add,
      HomologicalComplex.zero_f, add_zero, dite_eq_left (show i = i - 1 + 1 by omega),
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id, hh]

/-- The tensor product of two complexes with zero differentials has zero differentials. -/
theorem tensorObj_d_eq_zero (C D : CochainComplex (ModuleCat.{u} R) ℤ)
    (hC : ∀ i j, C.d i j = 0) (hD : ∀ i j, D.d i j = 0) (i j : ℤ) :
    (HomologicalComplex.tensorObj C D).d i j = 0 := by
  change (HomologicalComplex.mapBifunctor C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).d i j = 0
  rw [HomologicalComplex.mapBifunctor.d_eq]
  have h₁ : HomologicalComplex.mapBifunctor.D₁ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) i j = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b _
    rw [HomologicalComplex.mapBifunctor.ι_D₁]
    by_cases ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a + 1, b) = j
    · rw [HomologicalComplex.mapBifunctor.d₁_eq C D _ _
        (ComplexShape.up_mk a (a + 1) (by simp)) b j ht]
      simp [hC]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' C D _ _
        (ComplexShape.up_mk a (a + 1) (by simp)) b j ht]
      simp
  have h₂ : HomologicalComplex.mapBifunctor.D₂ C D
      (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) i j = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b _
    rw [HomologicalComplex.mapBifunctor.ι_D₂]
    by_cases ht : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (a, b + 1) = j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq C D _ _ a
        (ComplexShape.up_mk b (b + 1) (by simp)) j ht]
      simp [hD]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' C D _ _ a
        (ComplexShape.up_mk b (b + 1) (by simp)) j ht]
      simp
  rw [h₁, h₂, zero_add]

/-- The inclusions of the summands `Eⁱ ⊗ Gʲ`, `i + j = n`, into the degree-`n` term of the total
tensor complex, assembled on the direct sum. -/
def tensorObjSum (E G : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}, TensorProduct R (E.X ij.1.1) (G.X ij.1.2)) →ₗ[R]
      (HomologicalComplex.tensorObj E G).X n :=
  DirectSum.toModule R _ _ fun ij =>
    (HomologicalComplex.ιTensorObj E G ij.1.1 ij.1.2 n ij.2).hom

/-- The inverse of `tensorObjSum`: the map out of the degree-`n` term of the total tensor complex
whose component on the summand `Eⁱ ⊗ Gʲ` is the inclusion into the direct sum. -/
def tensorObjSumInv (E G : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (HomologicalComplex.tensorObj E G).X n ⟶
      ModuleCat.of R (⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        TensorProduct R (E.X ij.1.1) (G.X ij.1.2)) :=
  HomologicalComplex.mapBifunctorDesc (fun i j h =>
    ModuleCat.ofHom (DirectSum.lof R {ij : ℤ × ℤ // ij.1 + ij.2 = n}
      (fun ij => TensorProduct R (E.X ij.1.1) (G.X ij.1.2)) ⟨(i, j), h⟩))

/-- On the summand `Eⁱ ⊗ Gʲ`, `tensorObjSumInv` is the inclusion of that summand into the
direct sum. -/
theorem ι_tensorObjSumInv (E G : CochainComplex (ModuleCat.{u} R) ℤ) (n i j : ℤ)
    (h : i + j = n) :
    HomologicalComplex.ιTensorObj E G i j n h ≫ tensorObjSumInv E G n =
      ModuleCat.ofHom (DirectSum.lof R {ij : ℤ × ℤ // ij.1 + ij.2 = n}
        (fun ij => TensorProduct R (E.X ij.1.1) (G.X ij.1.2)) ⟨(i, j), h⟩) :=
  HomologicalComplex.ι_mapBifunctorDesc _ i j h

/-- **The degree-`n` term of a total tensor complex is the direct sum of the `Eⁱ ⊗ Gʲ` with
`i + j = n`.** -/
theorem bijective_tensorObjSum (E G : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Bijective (tensorObjSum E G n) := by
  have h₁ : ∀ x, (tensorObjSumInv E G n).hom (tensorObjSum E G n x) = x := by
    intro x
    have : (tensorObjSumInv E G n).hom.comp (tensorObjSum E G n) = LinearMap.id := by
      refine DirectSum.linearMap_ext R fun ij => LinearMap.ext fun y => ?_
      obtain ⟨⟨i, j⟩, h⟩ := ij
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [tensorObjSum, DirectSum.toModule_lof]
      exact ConcreteCategory.congr_hom (ι_tensorObjSumInv E G n i j h) y
    exact LinearMap.congr_fun this x
  have h₂ : ∀ y, tensorObjSum E G n ((tensorObjSumInv E G n).hom y) = y := by
    intro y
    have : tensorObjSumInv E G n ≫ ModuleCat.ofHom (tensorObjSum E G n) = 𝟙 _ := by
      refine HomologicalComplex.mapBifunctor.hom_ext fun i j h => ?_
      have e := ι_tensorObjSumInv E G n i j h
      rw [Category.comp_id, ← Category.assoc]
      refine (congrArg (· ≫ ModuleCat.ofHom (tensorObjSum E G n)) e).trans ?_
      ext z
      change tensorObjSum E G n (DirectSum.lof R _ _ ⟨(i, j), h⟩ z) = _
      rw [tensorObjSum, DirectSum.toModule_lof]
    exact ConcreteCategory.congr_hom this y
  exact ⟨Function.LeftInverse.injective h₁, Function.RightInverse.surjective h₂⟩

end ZeroDifferential

/-! ### The sum of the cohomology products -/

section Sum

/- The objects below live in `D(R)` at the standard model: Tag 068H
(`RingTheory.TorProducts.cohomologyTensorProduct`) is stated there. Since `DObj R` now takes
the model as an argument, the binders name it; this file migrates after 068H. -/

variable {R : Type u} [CommRing R]

/-- **The cohomology product of [Stacks, Tag 068H] in the pair of degrees `(i, j)`, read in a
degree `n` with `i + j = n`.** -/
def crossProductCast (K L : @DObj R _ (HasDerivedCategory.standard _)) (i j n : ℤ) (h : i + j = n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K ⊗
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        (((canonicalDerivedTensorProductFunctor R).obj K).obj L) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (RingTheory.TorProducts.cohomologyTensorProduct K L i j).map ≫
    eqToHom (congrArg (fun m => (DerivedCategory.homologyFunctor (ModuleCat.{u} R) m).obj
      (((canonicalDerivedTensorProductFunctor R).obj K).obj L)) h)

/-- In the degree `i + j` itself, `crossProductCast` is the cohomology product. -/
theorem crossProductCast_rfl (K L : @DObj R _ (HasDerivedCategory.standard _)) (i j : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    crossProductCast K L i j (i + j) rfl =
      (RingTheory.TorProducts.cohomologyTensorProduct K L i j).map := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  rw [crossProductCast, eqToHom_refl, Category.comp_id]

/-- **The sum of the cohomology products over the pairs of degrees `(i, j)` with `i + j = n`**,

`⨁_{i + j = n} Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁿ(K ⊗^𝐋_R L)`. -/
def kunnethSum (K L : @DObj R _ (HasDerivedCategory.standard _)) (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (⨁ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n},
        TensorProduct R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.1).obj K)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.2).obj L)) →ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        (((canonicalDerivedTensorProductFunctor R).obj K).obj L) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  DirectSum.toModule R _ _ fun ij => (crossProductCast K L ij.1.1 ij.1.2 n ij.2).hom

/-- The sum of the cohomology products on a summand. -/
theorem kunnethSum_of (K L : @DObj R _ (HasDerivedCategory.standard _))
    (n : ℤ) (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n})
    (x : letI := @HasDerivedCategory.standard.{u, u + 1};
        TensorProduct R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.1).obj K)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.2).obj L)) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    kunnethSum K L n (DirectSum.lof R {ij : ℤ × ℤ // ij.1 + ij.2 = n}
        (fun ij => TensorProduct R
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.1).obj K)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.2).obj L)) ij x) =
      (crossProductCast K L ij.1.1 ij.1.2 n ij.2).hom x := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  unfold kunnethSum
  exact DirectSum.toModule_lof R (M := fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
    TensorProduct R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.1).obj K)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.2).obj L)) ij x

/-- Precomposing the sum of a family of maps out of a direct sum with the direct sum of a family
of maps of the summands is the sum of the composites. -/
theorem toModule_comp_mapRange {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {P : Type*} [AddCommGroup P] [Module R P]
    (f : ∀ i, N i →ₗ[R] P) (e : ∀ i, M i →ₗ[R] N i) :
    (DirectSum.toModule R ι P f).comp (DFinsupp.mapRange.linearMap e) =
      DirectSum.toModule R ι P (fun i => (f i).comp (e i)) := by
  refine DirectSum.linearMap_ext R fun i => LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  rw [DirectSum.toModule_lof]
  change DirectSum.toModule R ι P f (DFinsupp.mapRange.linearMap e (DFinsupp.single i x)) = _
  rw [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]
  exact DirectSum.toModule_lof R i (e i x)

/-- The direct sum of a family of bijective linear maps is bijective. -/
theorem bijective_mapRange {ι : Type*} {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (e : ∀ i, M i →ₗ[R] N i) (he : ∀ i, Function.Bijective (e i)) :
    Function.Bijective (DFinsupp.mapRange.linearMap e) :=
  (DFinsupp.mapRange.linearEquiv fun i => LinearEquiv.ofBijective (e i) (he i)).bijective

/-- If `f ∘ e = g ∘ a` componentwise, with `e`, `g` and `⨁ a` bijective, then `⨁ f` is bijective. -/
private theorem bijective_toModule_of_comp_mapRange {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {P S : Type*} [AddCommGroup P] [Module R P] [AddCommGroup S]
    [Module R S] (f : ∀ i, N i →ₗ[R] P) (a : ∀ i, M i →ₗ[R] S) (e : ∀ i, M i →ₗ[R] N i)
    (g : S →ₗ[R] P) (he : ∀ i, Function.Bijective (e i)) (hg : Function.Bijective g)
    (ha : Function.Bijective (DirectSum.toModule R ι S a))
    (h : ∀ i x, f i (e i x) = g (a i x)) : Function.Bijective (DirectSum.toModule R ι P f) := by
  refine (Function.Bijective.of_comp_iff _ (bijective_mapRange e he)).1 ?_
  have : (DirectSum.toModule R ι P f).comp (DFinsupp.mapRange.linearMap e) =
      g.comp (DirectSum.toModule R ι S a) := by
    rw [toModule_comp_mapRange]
    refine DirectSum.linearMap_ext R fun i => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
    exact h i x
  rw [← LinearMap.coe_comp, this]
  exact hg.comp ha

end Sum

/-! ### Over a field -/

section Field

variable {R : Type u} [Field R]

/-- Over a field every complex receives a quasi-isomorphism from a complex with zero
differentials: a section of each projection `Zⁱ(C) ⟶ Hⁱ(C)`, which exists because `Hⁱ(C)` is
free, followed by the inclusion of the cocycles. -/
theorem exists_zeroDifferential_quasiIso (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (E : CochainComplex (ModuleCat.{u} R) ℤ) (f : E ⟶ C), (∀ i j, E.d i j = 0) ∧ QuasiIso f := by
  classical
  have hproj : ∀ i : ℤ, Projective (C.homology i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (C.homology i))
  let E : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := fun i => C.homology i
      d := fun _ _ => 0
      shape := fun _ _ _ => rfl
      d_comp_d' := by intros; simp }
  let s (i : ℤ) := Projective.factorThru (𝟙 (C.homology i)) (C.homologyπ i)
  have hs (i : ℤ) : s i ≫ C.homologyπ i = 𝟙 _ := Projective.factorThru_comp _ _
  let f : E ⟶ C :=
    { f := fun i => s i ≫ C.iCycles i
      comm' := by intros; dsimp [E]; simp }
  refine ⟨E, f, fun _ _ => rfl, ?_⟩
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hi : IsIso (E.iCycles i) := E.isIso_iCycles _ _ rfl rfl
  have hp : IsIso (E.homologyπ i) := E.isIso_homologyπ _ _ rfl rfl
  have hc : HomologicalComplex.cyclesMap f i = E.iCycles i ≫ s i := by
    apply (cancel_mono (C.iCycles i)).1
    simp [HomologicalComplex.cyclesMap_i, f]
  have he : E.homologyπ i ≫ HomologicalComplex.homologyMap f i = E.iCycles i := by
    rw [HomologicalComplex.homologyπ_naturality, hc, Category.assoc, hs, Category.comp_id]
  have : IsIso (E.homologyπ i ≫ HomologicalComplex.homologyMap f i) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.homologyπ i) _

/-- Tensoring two threefold composites, in the shape the cohomology product is unfolded in. -/
theorem tensorHom_comp_three {C : Type*} [Category* C] [MonoidalCategory C]
    {X₁ Y₁ Z₁ W₁ X₂ Y₂ Z₂ W₂ T : C} (a₁ : X₁ ⟶ Y₁) (b₁ : Y₁ ⟶ Z₁) (c₁ : Z₁ ⟶ W₁)
    (a₂ : X₂ ⟶ Y₂) (b₂ : Y₂ ⟶ Z₂) (c₂ : Z₂ ⟶ W₂) (r : W₁ ⊗ W₂ ⟶ T) :
    ((a₁ ≫ b₁ ≫ c₁) ⊗ₘ (a₂ ≫ b₂ ≫ c₂)) ≫ r =
      (a₁ ⊗ₘ a₂) ≫ (b₁ ⊗ₘ b₂) ≫ (c₁ ⊗ₘ c₂) ≫ r := by
  simp

/-- Every module over a field is projective. -/
theorem projective_of_field (M : ModuleCat.{u} R) : Projective M :=
  ModuleCat.projective_of_free (Module.Free.chooseBasis R M)

variable (E G : CochainComplex (ModuleCat.{u} R) ℤ) (hE : ∀ i j, E.d i j = 0)
  (hG : ∀ i j, G.d i j = 0)

/-- For a complex with zero differentials, `Eⁱ` is its `i`-th cohomology in the derived
category. -/
def zeroDifferentialXIso (i : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    E.X i ≅ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (DerivedCategory.Q.obj E) :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  haveI := E.isIso_iCycles i (i + 1) (by simp) (hE _ _)
  haveI := E.isIso_homologyπ (i - 1) i (by simp) (hE _ _)
  (asIso (E.iCycles i)).symm ≪≫ asIso (E.homologyπ i) ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app E).symm

/-- The forward map of `zeroDifferentialXIso`: the inverse of the inclusion of the cycles, then
the projection to cohomology, then the identification of the cohomology of `E` with that of its
image in the derived category. -/
theorem zeroDifferentialXIso_hom (i : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    haveI :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  E.isIso_iCycles i (i + 1) (by simp) (hE _ _)
    (zeroDifferentialXIso E hE i).hom = inv (E.iCycles i) ≫ E.homologyπ i ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).inv.app E :
        E.homology i ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (DerivedCategory.Q.obj E)) :=
  rfl

/-- For a complex with zero differentials, the degree-`n` term is its `n`-th cohomology. -/
def zeroDifferentialXHomologyIso (n : ℤ) : E.X n ≅ E.homology n :=
  haveI := E.isIso_iCycles n (n + 1) (by simp) (hE _ _)
  haveI := E.isIso_homologyπ (n - 1) n (by simp) (hE _ _)
  (asIso (E.iCycles n)).symm ≪≫ asIso (E.homologyπ n)

/-- The cohomology of the derived tensor product of two complexes of vector spaces is the
cohomology of their total tensor complex. -/
def derivedTensorHomologyIso (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
        (((canonicalDerivedTensorProductFunctor R).obj (DerivedCategory.Q.obj E)).obj
          (DerivedCategory.Q.obj G)) ≅ (HomologicalComplex.tensorObj E G).homology n :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso
      ((canonicalDerivedTensorProduct R).comparison E G (CochainComplex.Kunneth.kFlat_of_field E)
        (CochainComplex.Kunneth.kFlat_of_field G)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app _

/-- The forward map of `derivedTensorHomologyIso`: the cohomology of the comparison map of the
derived tensor product, then the identification of the cohomology of the total tensor complex with
that of its image in the derived category. -/
theorem derivedTensorHomologyIso_hom (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (derivedTensorHomologyIso E G n).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((canonicalDerivedTensorProduct R).comparison E G
            (CochainComplex.Kunneth.kFlat_of_field E)
            (CochainComplex.Kunneth.kFlat_of_field G)).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.app
          (HomologicalComplex.tensorObj E G) :
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
            (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E G)) ⟶
              (HomologicalComplex.tensorObj E G).homology n) :=
  let := @HasDerivedCategory.standard.{u, u + 1}
  rfl

include hE hG in
/-- **The cohomology product of two complexes with zero differentials, on a summand**: through
the identifications of the terms with the cohomology, it is the inclusion of the summand
`Eⁱ ⊗ Gʲ` into the degree-`n` term of the total tensor complex. -/
theorem zeroDifferentialXIso_tensorHom_crossProductCast (i j n : ℤ) (h : i + j = n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((zeroDifferentialXIso E hE i).hom ⊗ₘ (zeroDifferentialXIso G hG j).hom) ≫
        crossProductCast (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G) i j n h =
      HomologicalComplex.ιTensorObj E G i j n h ≫
        (zeroDifferentialXHomologyIso _ (tensorObj_d_eq_zero E G hE hG) n).hom ≫
          (derivedTensorHomologyIso E G n).inv := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst h
  have := isKProjective_of_d_eq_zero E hE (fun _ => projective_of_field _)
  have := isKProjective_of_d_eq_zero G hG (fun _ => projective_of_field _)
  obtain ⟨z₀, hz₀⟩ := RingTheory.TorProducts.exists_tensorCycles E G i j
  have key := TorCrossProduct.cohomologyTensorProduct_map_eq_of_isKProjective E G
    (CochainComplex.Kunneth.kFlat_of_field E) (CochainComplex.Kunneth.kFlat_of_field G) i j z₀ hz₀
  have := E.isIso_iCycles i (i + 1) (by simp) (hE _ _)
  have := G.isIso_iCycles j (j + 1) (by simp) (hG _ _)
  have : IsIso ((E ⊗ G).iCycles (i + j)) :=
    (HomologicalComplex.tensorObj E G).isIso_iCycles (i + j) (i + j + 1) (by simp)
      (tensorObj_d_eq_zero E G hE hG _ _)
  have : IsIso ((E ⊗ G).homologyπ (i + j)) :=
    (HomologicalComplex.tensorObj E G).isIso_homologyπ (i + j - 1) (i + j) (by simp)
      (tensorObj_d_eq_zero E G hE hG _ _)
  have hz : (inv (E.iCycles i) ⊗ₘ inv (G.iCycles j)) ≫ z₀ =
      HomologicalComplex.ιTensorObj E G i j (i + j) rfl ≫ inv ((E ⊗ G).iCycles (i + j)) := by
    rw [← cancel_mono ((E ⊗ G).iCycles (i + j)), Category.assoc,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id, hz₀, ← Category.assoc,
      tensorHom_comp_tensorHom, IsIso.inv_hom_id, IsIso.inv_hom_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp]
  rw [← cancel_mono (derivedTensorHomologyIso E G (i + j)).hom, Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have key' := (inv (E.iCycles i) ⊗ₘ inv (G.iCycles j)) ≫= key
  refine Eq.trans ?_ (key'.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (E ⊗ G).homologyπ (i + j)) hz).trans ?_)))
  · rw [zeroDifferentialXIso_hom, zeroDifferentialXIso_hom, derivedTensorHomologyIso_hom,
      crossProductCast, eqToHom_refl, Category.comp_id]
    exact tensorHom_comp_three _ _ _ _ _ _ _
  · simp only [zeroDifferentialXHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Category.assoc]
    rfl

include hE hG in
/-- **The Künneth formula for two complexes with zero differentials**: the sum of the cohomology
products is bijective. -/
theorem bijective_kunnethSum_of_d_eq_zero (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    Function.Bijective (kunnethSum (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G) n) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  let e := fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
    TensorProduct.map (zeroDifferentialXIso E hE ij.1.1).hom.hom
      (zeroDifferentialXIso G hG ij.1.2).hom.hom
  have he : ∀ ij, Function.Bijective (e ij) := fun ij =>
    (TensorProduct.congr (zeroDifferentialXIso E hE ij.1.1).toLinearEquiv
      (zeroDifferentialXIso G hG ij.1.2).toLinearEquiv).bijective
  let g := ((zeroDifferentialXHomologyIso _ (tensorObj_d_eq_zero E G hE hG) n).hom ≫
    (derivedTensorHomologyIso E G n).inv).hom
  have hg : Function.Bijective g :=
    ((zeroDifferentialXHomologyIso _ (tensorObj_d_eq_zero E G hE hG) n) ≪≫
      (derivedTensorHomologyIso E G n).symm).toLinearEquiv.bijective
  refine bijective_toModule_of_comp_mapRange _ _ e g he hg (bijective_tensorObjSum E G n)
    fun ij x => ?_
  have := congrArg ModuleCat.Hom.hom
    (zeroDifferentialXIso_tensorHom_crossProductCast E G hE hG ij.1.1 ij.1.2 n ij.2)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_tensorHom] at this
  exact LinearMap.congr_fun this x

omit hE hG

/-- **The cohomology product is natural along morphisms out of a complex with zero differentials
over a field**, in the reading `crossProductCast` of the degrees. -/
theorem crossProductCast_naturality_of_d_eq_zero (hE : ∀ i j, E.d i j = 0)
    (hG : ∀ i j, G.d i j = 0) {K L : @DObj R _ (HasDerivedCategory.standard _)}
    (u : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory.Q.obj E ⟶ K)
    (v : letI := @HasDerivedCategory.standard.{u, u + 1};
        DerivedCategory.Q.obj G ⟶ L) (i j n : ℤ) (h : i + j = n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map v) ≫
        crossProductCast K L i j n h =
      crossProductCast (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G) i j n h ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (((canonicalDerivedTensorProductFunctor R).map u).app (DerivedCategory.Q.obj G) ≫
            ((canonicalDerivedTensorProductFunctor R).obj K).map v) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  subst h
  have := isKProjective_of_d_eq_zero E hE (fun _ => projective_of_field _)
  have := isKProjective_of_d_eq_zero G hG (fun _ => projective_of_field _)
  simp only [crossProductCast, eqToHom_refl, Category.comp_id]
  exact RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective E G
    (CochainComplex.Kunneth.kFlat_of_field E) (CochainComplex.Kunneth.kFlat_of_field G) u v i j

/-- Every object of `D(R)`, `R` a field, is isomorphic to the image of a complex with zero
differentials, in any model of `D(R)`. -/
theorem exists_zeroDifferential_iso [HasDerivedCategory (ModuleCat.{u} R)] (K : DObj R) :
    ∃ (E : CochainComplex (ModuleCat.{u} R) ℤ) (_ : ∀ i j, E.d i j = 0),
      Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨E, f, hE, hf⟩ := exists_zeroDifferential_quasiIso (DerivedCategory.Q.objPreimage K)
  have := hf
  exact ⟨E, hE, ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- **The Künneth formula over a field in canonical form.** For objects `K` and `L` of `D(R)`,
`R` a field, the sum of the cohomology products of [Stacks, Tag 068H]

`⨁_{i + j = n} Hⁱ(K) ⊗_R Hʲ(L) ⟶ Hⁿ(K ⊗^𝐋_R L)`

is bijective. -/
theorem bijective_kunnethSum (K L : @DObj R _ (HasDerivedCategory.standard _)) (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    Function.Bijective (kunnethSum K L n) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  obtain ⟨E, hE, ⟨eK⟩⟩ := exists_zeroDifferential_iso K
  obtain ⟨G, hG, ⟨eL⟩⟩ := exists_zeroDifferential_iso L
  let e := fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} =>
    TensorProduct.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.1).map eK.hom).hom
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.2).map eL.hom).hom
  have he : ∀ ij, Function.Bijective (e ij) := fun ij =>
    (TensorProduct.congr
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.1).mapIso eK).toLinearEquiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) ij.1.2).mapIso
        eL).toLinearEquiv).bijective
  let w := ((canonicalDerivedTensorProductFunctor R).map eK.hom).app (DerivedCategory.Q.obj G) ≫
    ((canonicalDerivedTensorProductFunctor R).obj K).map eL.hom
  have : IsIso w := by
    dsimp only [w]
    infer_instance
  have hw : Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map w).hom :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).mapIso (asIso w)).toLinearEquiv.bijective
  refine bijective_toModule_of_comp_mapRange _ _ e _ he hw
    (bijective_kunnethSum_of_d_eq_zero E G hE hG n) fun ij x => ?_
  have := congrArg ModuleCat.Hom.hom
    (crossProductCast_naturality_of_d_eq_zero E G hE hG eK.hom eL.hom ij.1.1 ij.1.2 n ij.2)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_tensorHom] at this
  exact LinearMap.congr_fun this x

/-- **The cohomology product is natural over a field**, along arbitrary morphisms of `D(R)`. -/
theorem crossProductCast_naturality {K K' L L' : @DObj R _ (HasDerivedCategory.standard _)}
    (u : K ⟶ K') (v : L ⟶ L')
    (i j n : ℤ) (h : i + j = n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map v) ≫
        crossProductCast K' L' i j n h =
      crossProductCast K L i j n h ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (((canonicalDerivedTensorProductFunctor R).map u).app L ≫
            ((canonicalDerivedTensorProductFunctor R).obj K').map v) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  obtain ⟨E, hE, ⟨eK⟩⟩ := exists_zeroDifferential_iso K
  obtain ⟨G, hG, ⟨eL⟩⟩ := exists_zeroDifferential_iso L
  have h₁ := crossProductCast_naturality_of_d_eq_zero E G hE hG eK.hom eL.hom i j n h
  have h₂ := crossProductCast_naturality_of_d_eq_zero E G hE hG (eK.hom ≫ u) (eL.hom ≫ v) i j n h
  have hT : ((canonicalDerivedTensorProductFunctor R).map (eK.hom ≫ u)).app
        (DerivedCategory.Q.obj G) ≫
      ((canonicalDerivedTensorProductFunctor R).obj K').map (eL.hom ≫ v) =
      (((canonicalDerivedTensorProductFunctor R).map eK.hom).app (DerivedCategory.Q.obj G) ≫
        ((canonicalDerivedTensorProductFunctor R).obj K).map eL.hom) ≫
        (((canonicalDerivedTensorProductFunctor R).map u).app L ≫
          ((canonicalDerivedTensorProductFunctor R).obj K').map v) := by
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [← Category.assoc (((canonicalDerivedTensorProductFunctor R).obj K).map eL.hom),
      NatTrans.naturality, Category.assoc]
  rw [← cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map eK.hom ⊗ₘ
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map eL.hom),
    ← Category.assoc, tensorHom_comp_tensorHom, ← Functor.map_comp, ← Functor.map_comp, h₂,
    hT, Functor.map_comp, reassoc_of% h₁]

end Field

/-! ### The same statements over a commutative ring which is a field

The statements below are those of the previous section for a commutative ring `R` together with
a proof that it is a field, rather than for a `Field` instance. They are what a consumer whose
ring carries a `CommRing` structure of its own (for instance the global sections of a ringed
space) applies: the field structure is introduced inside the proof, at a variable ring, so that it
never meets the consumer's ring structure. -/

section IsField

variable {R : Type u} [CommRing R] (hR : IsField R)

include hR in
/-- `Stacks.WeilDeRham.bijective_kunnethSum` for a commutative ring which is a field. -/
theorem bijective_kunnethSum_of_isField (K L : @DObj R _ (HasDerivedCategory.standard _)) (n : ℤ) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    Function.Bijective (kunnethSum K L n) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  let := hR.toField
  exact bijective_kunnethSum K L n

include hR in
/-- `Stacks.WeilDeRham.crossProductCast_naturality` for a commutative ring which is a field. -/
theorem crossProductCast_naturality_of_isField
    {K K' L L' : @DObj R _ (HasDerivedCategory.standard _)}
    (u : K ⟶ K') (v : L ⟶ L')
    (i j n : ℤ) (h : i + j = n) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map v) ≫
        crossProductCast K' L' i j n h =
      crossProductCast K L i j n h ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          (((canonicalDerivedTensorProductFunctor R).map u).app L ≫
            ((canonicalDerivedTensorProductFunctor R).obj K').map v) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  let := hR.toField
  exact crossProductCast_naturality u v i j n h

end IsField

end Stacks.WeilDeRham

end
