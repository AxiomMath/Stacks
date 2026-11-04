module

public import StacksFrontier.RingTheory.Koszul.PowerLift.KoszulTorsion
import all StacksFrontier.RingTheory.Koszul.PowerLift.KoszulTorsion
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Homology.KFlat.Bifunctor
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.RingTheory.Koszul.DerivedQuotientModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring a complex in a linear category with a Koszul complex

Let `A` be a commutative ring, let `𝒜` be an `A`-linear category with binary biproducts, let `K`
be a cochain complex in `𝒜` and let `x₁, …, x_r` be elements of `A`. The complex
`K ⊗_A Kos(x₁, …, x_r)` — the total complex of the bicomplex `K^p ⊗_A ⋀^q(A^r)` — makes sense in
`𝒜` although there is no tensor product of an object of `𝒜` with an `A`-module: it is the `r`-fold
iterated mapping cone of multiplication by the `x_i`, multiplication by `a ∈ A` on an object `X`
being the endomorphism `a • 𝟙 X` supplied by the `A`-linear structure. That is the definition used
here, `Stacks.KoszulCone.koszulTensor`.

The four properties of the construction are:

* an additive functor carrying `a • 𝟙` to `σ a • 𝟙` commutes with it
  (`Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso`, and
  `Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso_of_linear` for an `A`-linear
  functor into an `A`-linear category);
* each term is a finite biproduct of terms of `K` (`Stacks.KoszulCone.koszulTensorSuccXIso`), so
  injectivity of the terms of `K` is inherited
  (`Stacks.KoszulCone.injective_X_koszulTensor`) and so is a lower degree bound, shifted by `r`
  (`Stacks.KoszulCone.isStrictlyGE_koszulTensor`);
* it is acyclic as soon as one of the `x_i` is invertible
  (`Stacks.KoszulCone.acyclic_koszulTensor_of_isUnit`);
* over `ModuleCat A` it is the ordinary total tensor product of `K` with the cochain Koszul
  complex (`Stacks.KoszulCone.nonempty_tensorObj_seqCochainComplex_iso_koszulTensor`).

## Main definitions

* `Stacks.KoszulCone.koszulTensor` — the iterated mapping cone `K ⊗_A Kos(x₁, …, x_r)`.
* `Stacks.KoszulCone.koszulTensorSuccXIso` — the degreewise biproduct decomposition of one cone
  stage.

## Main results

* `Stacks.KoszulCone.injective_X_koszulTensor` and
  `Stacks.KoszulCone.isStrictlyGE_koszulTensor`.
* `Stacks.KoszulCone.acyclic_koszulTensor_of_isUnit`.
* `Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso`.
* `Stacks.KoszulCone.nonempty_tensorObj_seqCochainComplex_iso_koszulTensor`.

## Implementation notes

The recursion peels the *last* entry of the sequence, `koszulTensor (r + 1) x K` being the cone of
`x (Fin.last r) • 𝟙` on `koszulTensor r (Fin.init x) K`. That is the direction in which
[Stacks, Tag 0629] is available for the Koszul complex itself, so the comparison with the ordinary
tensor product is an induction with no reindexing.

The biproduct description of the terms is recorded one cone at a time:
`Stacks.KoszulCone.koszulTensorSuccXIso` identifies the degree-`i` term of a cone stage with the
binary biproduct of the degree-`(i+1)` and degree-`i` terms of the previous stage, and iterating it
writes every term of `K ⊗_A Kos(x₁, …, x_r)` as a biproduct of `2 ^ r` terms of `K`. The two
consequences actually used — injectivity of the terms and the lower degree bound — are the two
inductions over that decomposition recorded below.

Acyclicity is read through the mapping cone: a cone is acyclic exactly when the morphism is a
quasi-isomorphism (`CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone`). At the stage
belonging to an invertible `x_i` the morphism is an isomorphism, and at every later stage both its
source and its target are already acyclic, so it is a quasi-isomorphism for the trivial reason
that it acts between zero homology objects.

For the comparison with the ordinary tensor product, `Tot(K ⊗ -)` is the functor `TleftCochain K`
of `StacksFrontier/Homology/TensorComplex/ExactFunctor.lean`, which comes with the comparison
isomorphism `Tot(K ⊗ C(φ)) ≅ C(Tot(K ⊗ φ))` of [Stacks, Tag 06Y8]; the Koszul side of the
induction is [Stacks, Tag 0629] in the shape of a cochain mapping cone, which
`StacksFrontier/RingTheory/Koszul/PowerLift/KoszulTorsion.lean` already assembles out of
[Stacks, Tag 0628] and the commutation of extension by zero with cone formation. That assembly is
reached through `import all`, as that file itself reaches its own inputs, rather than reproved.

## References

* [Stacks Project, Tag 0628](https://stacks.math.columbia.edu/tag/0628)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
* [Stacks Project, Tag 06Y8](https://stacks.math.columbia.edu/tag/06Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe u v

namespace Stacks.KoszulCone

/-! ### Invertible scalars in a linear category -/

section Unit

variable {A : Type*} [CommRing A] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear A 𝒞]

/-- **An invertible scalar acts invertibly.** In an `A`-linear category the endomorphism
`a • 𝟙 X` is an isomorphism as soon as `a` is a unit of `A`. -/
theorem isIso_smul_id_of_isUnit (a : A) (ha : IsUnit a) (X : 𝒞) : IsIso (a • 𝟙 X) := by
  obtain ⟨u, rfl⟩ := ha
  refine ⟨⟨((u⁻¹ : Aˣ) : A) • 𝟙 X, ?_, ?_⟩⟩
  · rw [Linear.smul_comp, id_comp, smul_smul, Units.mul_inv, one_smul]
  · rw [Linear.smul_comp, id_comp, smul_smul, Units.inv_mul, one_smul]

end Unit

/-! ### Cones of equal and of isomorphic data -/

section Transport

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

/-- Equal morphisms have equal mapping cones. -/
def mappingConeEqIso {L L' : CochainComplex 𝒜 ℤ} {φ ψ : L ⟶ L'} (h : φ = ψ) :
    CochainComplex.mappingCone φ ≅ CochainComplex.mappingCone ψ :=
  eqToIso (by rw [h])

/-- Replacing the source and the target of a morphism by isomorphic complexes replaces its
mapping cone by an isomorphic one. -/
def mappingConeIsoOfIso {K₁ K₂ L₁ L₂ : CochainComplex 𝒜 ℤ} (a : K₁ ≅ K₂) (b : L₁ ≅ L₂)
    (φ : K₁ ⟶ L₁) :
    CochainComplex.mappingCone φ ≅ CochainComplex.mappingCone (a.inv ≫ φ ≫ b.hom) where
  hom := CochainComplex.mappingCone.map φ (a.inv ≫ φ ≫ b.hom) a.hom b.hom (by simp)
  inv := CochainComplex.mappingCone.map (a.inv ≫ φ ≫ b.hom) φ a.inv b.inv (by simp)
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id φ
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp]
    simpa using CochainComplex.mappingCone.map_id (a.inv ≫ φ ≫ b.hom)

variable {A : Type*} [CommRing A] [Linear A 𝒜]

/-- The cone of multiplication by a scalar depends on the complex only up to isomorphism. -/
def mappingConeSmulIso {L L' : CochainComplex 𝒜 ℤ} (e : L ≅ L') (a : A) :
    CochainComplex.mappingCone (a • 𝟙 L) ≅ CochainComplex.mappingCone (a • 𝟙 L') :=
  mappingConeIsoOfIso e e (a • 𝟙 L) ≪≫
    mappingConeEqIso (by rw [Linear.smul_comp, id_comp, Linear.comp_smul, Iso.inv_hom_id])

end Transport

/-! ### The construction -/

section Def

variable {A : Type*} [CommRing A] {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
  [HasBinaryBiproducts 𝒜] [Linear A 𝒜]

/-- **The complex `K ⊗_A Kos(x₁, …, x_r)`**, built as the `r`-fold iterated mapping cone of
multiplication by the entries of `x`: the empty sequence gives `K` back, and one more entry
replaces the complex by the cone of multiplication by that entry. -/
def koszulTensor : (r : ℕ) → (Fin r → A) → CochainComplex 𝒜 ℤ → CochainComplex 𝒜 ℤ
  | 0, _, K => K
  | (r + 1), x, K =>
      CochainComplex.mappingCone (x (Fin.last r) • 𝟙 (koszulTensor r (Fin.init x) K))

/-- For the empty sequence, `koszulTensor 0 x K` is `K` itself. -/
@[simp] theorem koszulTensor_zero (x : Fin 0 → A) (K : CochainComplex 𝒜 ℤ) :
    koszulTensor 0 x K = K := rfl

/-- For a sequence of length `r + 1`, `koszulTensor (r + 1) x K` is the mapping cone of
multiplication by the last entry of `x` on `koszulTensor r (Fin.init x) K`. -/
theorem koszulTensor_succ (r : ℕ) (x : Fin (r + 1) → A) (K : CochainComplex 𝒜 ℤ) :
    koszulTensor (r + 1) x K =
      CochainComplex.mappingCone (x (Fin.last r) • 𝟙 (koszulTensor r (Fin.init x) K)) := rfl

/-- **One cone stage of `K ⊗_A Kos(x)` is a binary biproduct of terms of the previous stage.**
Iterating this identification exhibits every term as a finite biproduct of terms of `K`. -/
def koszulTensorSuccXIso (r : ℕ) (x : Fin (r + 1) → A) (K : CochainComplex 𝒜 ℤ) (i : ℤ) :
    (koszulTensor (r + 1) x K).X i ≅
      (koszulTensor r (Fin.init x) K).X (i + 1) ⊞ (koszulTensor r (Fin.init x) K).X i :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    (x (Fin.last r) • 𝟙 (koszulTensor r (Fin.init x) K)) i (i + 1) rfl

/-- **The terms of `K ⊗_A Kos(x)` are injective when those of `K` are**, being finite biproducts
of them. -/
theorem injective_X_koszulTensor (K : CochainComplex 𝒜 ℤ) (hK : ∀ i, Injective (K.X i)) :
    ∀ (r : ℕ) (x : Fin r → A) (i : ℤ), Injective ((koszulTensor r x K).X i) := by
  intro r
  induction r with
  | zero => exact fun _ i => hK i
  | succ r ih =>
      intro x i
      have h₁ := ih (Fin.init x) (i + 1)
      have h₂ := ih (Fin.init x) i
      exact Injective.of_iso (koszulTensorSuccXIso r x K i).symm inferInstance

/-- **`K ⊗_A Kos(x₁, …, x_r)` vanishes in degrees below `m - r`** when `K` vanishes in degrees
below `m`: each cone stage lowers the bound by one. -/
theorem isZero_X_koszulTensor (K : CochainComplex 𝒜 ℤ) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.X i)) :
    ∀ (r : ℕ) (x : Fin r → A) (i : ℤ), i < m - r → IsZero ((koszulTensor r x K).X i) := by
  intro r
  induction r with
  | zero =>
      intro _ i hi
      exact hK i (by simpa using hi)
  | succ r ih =>
      intro x i hi
      refine IsZero.of_iso ?_ (koszulTensorSuccXIso r x K i)
      rw [biprod_isZero_iff]
      push_cast at hi
      exact ⟨ih (Fin.init x) (i + 1) (by omega), ih (Fin.init x) i (by omega)⟩

/-- **A lower degree bound for `K ⊗_A Kos(x₁, …, x_r)`**, shifted by the length of the
sequence. -/
theorem isStrictlyGE_koszulTensor (K : CochainComplex 𝒜 ℤ) (m : ℤ) [K.IsStrictlyGE m]
    (r : ℕ) (x : Fin r → A) :
    (koszulTensor r x K).IsStrictlyGE (m - r) := by
  have hK : ∀ i : ℤ, i < m → IsZero (K.X i) := fun i hi =>
    CochainComplex.isZero_of_isStrictlyGE K m i hi
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact isZero_X_koszulTensor K m hK r x i hi

end Def

/-! ### Acyclicity at an invertible entry -/

section Acyclic

variable {A : Type*} [CommRing A] {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [Linear A 𝒜]

/-- **`K ⊗_A Kos(x₁, …, x_r)` is acyclic as soon as one of the `x_i` is invertible.** At the cone
stage belonging to an invertible entry the morphism being coned is an isomorphism, and every later
stage cones a morphism between acyclic complexes. -/
@[ega "III 1.1.9" "H^•(f,M)=0 when (f)=A"]
theorem acyclic_koszulTensor_of_isUnit (K : CochainComplex 𝒜 ℤ) :
    ∀ (r : ℕ) (x : Fin r → A), (∃ i, IsUnit (x i)) → (koszulTensor r x K).Acyclic := by
  intro r
  induction r with
  | zero => exact fun _ h => h.elim fun i _ => i.elim0
  | succ r ih =>
      intro x h
      obtain ⟨i₀, hu⟩ := h
      have hq : QuasiIso (x (Fin.last r) • 𝟙 (koszulTensor r (Fin.init x) K)) := by
        rcases eq_or_ne i₀ (Fin.last r) with rfl | hne
        · have : IsIso (x (Fin.last r) • 𝟙 (koszulTensor r (Fin.init x) K)) :=
            isIso_smul_id_of_isUnit (x (Fin.last r)) hu _
          infer_instance
        · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hne
          have hac := ih (Fin.init x) ⟨j, hu⟩
          rw [quasiIso_iff]
          intro n
          rw [quasiIsoAt_iff_isIso_homologyMap]
          have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac n)
          exact h.isIso h _
      exact (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).1 hq

end Acyclic

/-! ### Additive functors -/

section Map

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B]
  {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasBinaryBiproducts 𝒜] [Linear A 𝒜]
  {ℬ : Type*} [Category ℬ] [Preadditive ℬ] [HasBinaryBiproducts ℬ] [Linear B ℬ]

/-- **An additive functor commutes with `- ⊗_A Kos(x)`.** The functor is only asked to carry
multiplication by `a ∈ A` to multiplication by `σ a`, which is what an `A`-linear functor into an
`A`-linear category does with `σ` the identity, and what evaluating a sheaf of modules on an open
set does with `σ` the restriction of a global scalar to that open set. -/
theorem nonempty_mapHomologicalComplex_koszulTensor_iso (G : 𝒜 ⥤ ℬ) [G.Additive] (σ : A → B)
    (hσ : ∀ (a : A) (Y : 𝒜), G.map (a • 𝟙 Y) = σ a • 𝟙 (G.obj Y)) :
    ∀ (r : ℕ) (x : Fin r → A) (K : CochainComplex 𝒜 ℤ),
      Nonempty ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (koszulTensor r x K) ≅
        koszulTensor r (σ ∘ x) ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  intro r
  induction r with
  | zero => exact fun _ _ => ⟨Iso.refl _⟩
  | succ r ih =>
      intro x K
      obtain ⟨e⟩ := ih (Fin.init x) K
      have hmap : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
            (x (Fin.last r) • 𝟙 (koszulTensor r (Fin.init x) K)) =
          σ (x (Fin.last r)) • 𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (koszulTensor r (Fin.init x) K)) := by
        ext j
        exact hσ _ _
      exact ⟨CochainComplex.mappingCone.mapHomologicalComplexIso _ G ≪≫
        mappingConeEqIso hmap ≪≫ mappingConeSmulIso e (σ (x (Fin.last r)))⟩

/-- **An additive `A`-linear functor between `A`-linear categories commutes with
`- ⊗_A Kos(x)`.** -/
theorem nonempty_mapHomologicalComplex_koszulTensor_iso_of_linear (G : 𝒜 ⥤ ℬ) [G.Additive]
    [Linear A ℬ] [G.Linear A] (r : ℕ) (x : Fin r → A) (K : CochainComplex 𝒜 ℤ) :
    Nonempty ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (koszulTensor r x K) ≅
      koszulTensor r x ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  nonempty_mapHomologicalComplex_koszulTensor_iso G id
    (fun a Y => by
      show G.map (a • 𝟙 Y) = a • 𝟙 (G.obj Y)
      rw [G.map_smul, G.map_id]) r x K

end Map

/-! ### Comparison with the ordinary tensor product over `ModuleCat A` -/

section ModuleCat

open CategoryTheory.MonoidalCategory

variable {A : Type u} [CommRing A]

/-- Exterior powers above the number of entries of the sequence vanish. -/
theorem isZero_X_seqComplex_of_gt {r : ℕ} (f : Fin r → A) (j : ℕ) (hj : r < j) :
    IsZero ((Koszul.seqComplex f).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  show Subsingleton (⋀[A]^j (Fin r → A))
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (fun i : Fin r => (Pi.basisFun A (Fin r)) i)
    (Pi.basisFun A (Fin r)).span_eq j
  simpa using hj

/-- Tensoring with a fixed complex carries multiplication by a scalar to multiplication by that
scalar. -/
theorem tensorHom_id_smul_id (C L : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    HomologicalComplex.tensorHom (𝟙 C) (a • 𝟙 L) =
      a • 𝟙 (HomologicalComplex.tensorObj C L) := by
  ext1 n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp [HomologicalComplex.ι_mapBifunctorMap]

/-- Tensoring with a fixed complex, as the functor `TleftCochain`, carries multiplication by a
scalar to multiplication by that scalar. -/
theorem tleftCochain_map_smul_id (C L : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) :
    (TleftCochain C).map (a • 𝟙 L) = a • 𝟙 ((TleftCochain C).obj L) :=
  tensorHom_id_smul_id C L a

/-- **The cochain Koszul complex of the empty sequence is the tensor unit.** -/
def seqCochainComplexEmptyIso (x : Fin 0 → A) :
    Koszul.seqCochainComplex x ≅ 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) := by
  let S := (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.down ℕ) 0).obj
    (ModuleCat.of A A)
  let e (n : ℕ) : (Koszul.seqComplex x).X n ≅ S.X n := by
    by_cases hn : n = 0
    · subst hn
      exact (exteriorPower.zeroEquiv A (Fin 0 → A)).toModuleIso ≪≫
        (HomologicalComplex.singleObjXSelf _ _ _).symm
    · exact (isZero_X_seqComplex_of_gt x n (by omega)).iso
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
  let eK : Koszul.seqComplex x ≅ S :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j hij
      exact (isZero_X_seqComplex_of_gt x i (by change j + 1 = i at hij; omega)).eq_of_src _ _)
  exact (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).mapIso eK ≪≫
    HomologicalComplex.extendSingleIso _ _ 0 0 rfl

/-- **Over `ModuleCat A` the iterated cone is the ordinary tensor product with the Koszul
complex.** This is [Stacks, Tag 0629] read for a general complex `C`: the cochain Koszul complex of
a sequence with one more entry is the cone of multiplication by that entry, and tensoring with `C`
commutes with cones. -/
theorem nonempty_tensorObj_seqCochainComplex_iso_koszulTensor :
    ∀ (r : ℕ) (x : Fin r → A) (C : CochainComplex (ModuleCat.{u} A) ℤ),
      Nonempty (HomologicalComplex.tensorObj C (Koszul.seqCochainComplex x) ≅
        koszulTensor r x C) := by
  intro r
  induction r with
  | zero =>
      intro x C
      exact ⟨(TleftCochain C).mapIso (seqCochainComplexEmptyIso x) ≪≫ ρ_ C⟩
  | succ r ih =>
      intro x C
      obtain ⟨e⟩ := ih (Fin.init x) C
      obtain ⟨eK⟩ := Stacks.Koszul.PowerLift.exists_iso_koszulCochain_snoc (Fin.init x)
        (x (Fin.last r))
      rw [Fin.snoc_init_self] at eK
      exact ⟨(TleftCochain C).mapIso eK ≪≫ TleftCochain_mappingCone_iso C _ ≪≫
        mappingConeEqIso (tleftCochain_map_smul_id C _ (x (Fin.last r))) ≪≫
        mappingConeSmulIso e (x (Fin.last r))⟩

end ModuleCat

end Stacks.KoszulCone

end
