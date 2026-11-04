module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.TensorDegreewiseSplit
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperatorPerfect
public import StacksFrontier.CategoryTheory.Monoidal.SwitchTrace
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatDerivedTensorBraiding
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorShift

/-!
# The second Adams operator on the `K`-group of a tensor triangulated subcategory of `D(A)`

Let `A` be a symmetric monoidal abelian category in which `2` is invertible and every complex
has a K-flat resolution, so that `D(A)` is symmetric monoidal under the derived tensor product
(`CochainComplex.KFlatMonoidal.derivedMonoidal`). Let `P` be a triangulated subcategory of
`D(A)`, closed under isomorphisms, under direct summands and under the derived tensor product.
For an object `L` of `P` the group `{±1}` acts on `L ⊗^L L` by switching the factors, and
`(L ⊗^L L)^+` and `(L ⊗^L L)^-` are the objects splitting the idempotents `(𝟙 ± σ)/2`. This file
constructs the additive endomorphism

`ψ² : K₀(P) ⟶ K₀(P)`,   `ψ²([L]) = [(L ⊗^L L)^+] - [(L ⊗^L L)^-]`,

and proves that it is well defined: the splittings exist, their classes do not depend on any
choice, and the value is additive along distinguished triangles.

## Main definitions

* `Stacks.SecondAdamsPerfect.derivedExactClass`: the function `K ↦ [Q(K)]` on complexes whose
  image lies in `P`, as an additive class in the sense of `Stacks.SecondAdamsPerfect.ExactClass`.
* `Stacks.SecondAdamsPerfect.kFlatSplitting`, `kFlatAntiSplitting`: for a K-flat complex `P`
  with `Q(P) ≅ L`, the splittings of `(𝟙 ± σ)/2` on `L ⊗^L L` cut out of `Tot(P ⊗ P)` by the
  invariants and the anti-invariants of the Koszul switch.
* `Stacks.SecondAdamsPerfect.secondAdamsValue`: the value `[(L ⊗^L L)^+] - [(L ⊗^L L)^-]`.
* `Stacks.SecondAdamsPerfect.secondAdams`: the additive endomorphism `ψ²` of `K₀(P)`.

## Main results

* `Stacks.SecondAdamsPerfect.secondAdamsValue_eq`: the value is `[s⁺] - [s⁻]` for *any*
  splittings `s⁺`, `s⁻` of the two idempotents.
* `Stacks.SecondAdamsPerfect.secondAdamsValue_distinguished`: **additivity along distinguished
  triangles.**
* `Stacks.SecondAdamsPerfect.secondAdams_cls`: `ψ²([L]) = [s⁺] - [s⁻]`.

## Implementation notes

The source ([Stacks, Tag 0FEK]) defines `ψ²` by the formula and says that "using exactness of
taking invariants and anti-invariants one can argue similarly to the proof of Lemma 0FEJ to show
that this is well defined". The argument is carried out on complexes. Every object of `D(A)` is
the image of a K-flat complex `P`, on which `L ⊗^L L` is the image of the total complex
`P ⊗ P` and the switch is the image of its Koszul symmetry
(`CochainComplex.KFlatMonoidal.derivedTensorIso_braiding`). On complexes the invariants are
kernels, and taking them is exact (`Stacks.SecondAdamsPerfect.invariantsShortComplex_shortExact`).
A distinguished triangle of `D(A)` is, up to isomorphism, the image of the degreewise split
short exact sequence `0 → K₁ → Cone(g) → K₀[1] → 0` of a map `g` of K-flat complexes, which
stays short exact after tensoring with any complex. The three-step filtration of [Stacks, Tag
0FEJ] then applies (`Stacks.SecondAdamsPerfect.switchTrace_tensorSquare`).

## References

* [Stacks Project, Tag 0FEK](https://stacks.math.columbia.edu/tag/0FEK)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated CochainComplex.KFlatBifunctor

universe w v u

namespace Stacks.SecondAdamsPerfect

/-! ### Splittings of idempotents: transport -/

namespace IdempotentSplitting

variable {C : Type*} [Category C]

/-- A splitting of an idempotent is a splitting of any equal endomorphism. -/
@[simps]
def ofEq {M : C} {e e' : M ⟶ M} (h : e = e') (s : IdempotentSplitting e) :
    IdempotentSplitting e' where
  obj := s.obj
  ι := s.ι
  π := s.π
  ι_π := s.ι_π
  π_ι := h ▸ s.π_ι

/-- A splitting of an idempotent transported along an isomorphism conjugating it. -/
@[simps]
def conj {M N : C} (φ : M ≅ N) {e : M ⟶ M} {e' : N ⟶ N} (h : φ.inv ≫ e ≫ φ.hom = e')
    (s : IdempotentSplitting e) : IdempotentSplitting e' where
  obj := s.obj
  ι := s.ι ≫ φ.hom
  π := φ.inv ≫ s.π
  ι_π := by simp [s.ι_π]
  π_ι := by rw [← h, Category.assoc, ← Category.assoc s.π, s.π_ι]

/-- The image of a splitting of an idempotent under a functor. -/
@[simps]
def map {D : Type*} [Category D] (F : C ⥤ D) {M : C} {e : M ⟶ M}
    (s : IdempotentSplitting e) : IdempotentSplitting (F.map e) where
  obj := F.obj s.obj
  ι := F.map s.ι
  π := F.map s.π
  ι_π := by rw [← F.map_comp, s.ι_π, F.map_id]
  π_ι := by rw [← F.map_comp, s.π_ι]

end IdempotentSplitting

/-- The invariants of an involution of an object of an abelian category in which `2` is
invertible split the invariant idempotent. -/
@[simps]
def invariantsSplitting {C : Type*} [Category C] [Abelian C] [∀ X : C, IsIso ((2 : ℤ) • 𝟙 X)]
    {V : C} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V) : IdempotentSplitting (invariantIdempotent τ) where
  obj := invariants τ
  ι := kernel.ι _
  π := invariantsπ τ hτ
  ι_π := ι_invariantsπ τ hτ
  π_ι := invariantsπ_ι τ hτ

/-! ### The additive class on complexes -/

section Generic

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

variable {A} in
/-- The image in `D(A)` of a biproduct of complexes is the biproduct of the images. -/
def mapBiprodIso (X Y : CochainComplex A ℤ) :
    DerivedCategory.Q.obj (X ⊞ Y) ≅ DerivedCategory.Q.obj X ⊞ DerivedCategory.Q.obj Y where
  hom := biprod.lift (DerivedCategory.Q.map biprod.fst) (DerivedCategory.Q.map biprod.snd)
  inv := biprod.desc (DerivedCategory.Q.map biprod.inl) (DerivedCategory.Q.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add,
      biprod.total, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [← Functor.map_comp]

variable (P : ObjectProperty (DerivedCategory A)) [P.IsTriangulated]

open Classical in
variable {P} in
/-- The class `[Q(K)]` of a complex whose image lies in `P`, and `0` otherwise. -/
def derivedClass (K : CochainComplex A ℤ) : K0 P.FullSubcategory :=
  if h : P (DerivedCategory.Q.obj K) then K0.cls ⟨DerivedCategory.Q.obj K, h⟩ else 0

variable {A} in
/-- `derivedClass` of a complex whose image lies in `P` is the class of that image. -/
theorem derivedClass_of_prop {K : CochainComplex A ℤ} (h : P (DerivedCategory.Q.obj K)) :
    derivedClass A (P := P) K = K0.cls ⟨DerivedCategory.Q.obj K, h⟩ :=
  dite_eq_left h

variable [P.IsClosedUnderIsomorphisms]

/-- `derivedClass` of a complex isomorphic in `D(A)` to an object of `P` is the class of that
object. -/
private theorem derivedClass_eq_cls_of_iso {K : CochainComplex A ℤ} {W : DerivedCategory A}
    (e : DerivedCategory.Q.obj K ≅ W) (hW : P W) :
    derivedClass A (P := P) K = K0.cls ⟨W, hW⟩ := by
  rw [derivedClass_of_prop P (P.prop_of_iso e.symm hW)]
  exact K0.cls_eq_of_iso (P.isoMk e)

variable {A} in
/-- `derivedClass` only depends on the image in `D(A)` up to isomorphism. -/
theorem derivedClass_eq_of_iso {K L : CochainComplex A ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    derivedClass A (P := P) K = derivedClass A (P := P) L := by
  by_cases h : P (DerivedCategory.Q.obj K)
  · have h' : P (DerivedCategory.Q.obj L) := P.prop_of_iso e h
    rw [derivedClass_eq_cls_of_iso A P e h', derivedClass_of_prop P h']
  · have h' : ¬ P (DerivedCategory.Q.obj L) := fun h' => h (P.prop_of_iso e.symm h')
    rw [derivedClass, derivedClass, dite_eq_right h, dite_eq_right h']

/-- **The additive class `K ↦ [Q(K)]`** on complexes whose image in `D(A)` lies in `P`. Short
exact sequences of complexes give distinguished triangles of `D(A)`, along which classes add,
and `P` has the two-out-of-three property along them. -/
def derivedExactClass (hsum : ∀ K L : DerivedCategory A, P (K ⊞ L) → P K) :
    ExactClass (CochainComplex A ℤ) (K0 P.FullSubcategory) where
  P K := P (DerivedCategory.Q.obj K)
  χ := derivedClass A
  of_iso e h := P.prop_of_iso (DerivedCategory.Q.mapIso e) h
  χ_eq_of_iso e := derivedClass_eq_of_iso P (DerivedCategory.Q.mapIso e)
  of_shortExact₁ _ hS h₂ h₃ :=
    P.ext_of_isTriangulatedClosed₁ _ (DerivedCategory.triangleOfSES_distinguished hS) h₂ h₃
  of_shortExact₂ _ hS h₁ h₃ :=
    P.ext_of_isTriangulatedClosed₂ _ (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃
  χ_shortExact S hS h₁ h₂ h₃ := by
    rw [derivedClass_of_prop P h₁, derivedClass_of_prop P h₂, derivedClass_of_prop P h₃]
    exact K0.cls_eq_add_of_distinguished_of_prop P h₁ h₂ h₃ _ _ _
      (DerivedCategory.triangleOfSES_distinguished hS)
  of_biprod_fst X Y h := hsum _ _ (P.prop_of_iso (mapBiprodIso X Y) h)

variable {A} in
/-- The difference `[Q(V^τ)] - [Q(V^{-τ})]` of the classes of the invariants and the
anti-invariants of an endomorphism of a complex. -/
def derivedTrace {V : CochainComplex A ℤ} (τ : V ⟶ V) : K0 P.FullSubcategory :=
  derivedClass A (P := P) (invariants τ) - derivedClass A (P := P) (invariants (-τ))

/-- `derivedTrace` is the trace of `derivedExactClass`. -/
theorem derivedTrace_eq_switchTrace (hsum : ∀ K L : DerivedCategory A, P (K ⊞ L) → P K)
    {V : CochainComplex A ℤ} (τ : V ⟶ V) :
    derivedTrace P τ = switchTrace (derivedExactClass A P hsum) τ :=
  rfl

variable [∀ X : A, IsIso ((2 : ℤ) • 𝟙 X)]

variable {A} in
/-- **`2` is invertible in `D(A)`** as soon as it is invertible in `A`. -/
instance isIso_two_smul_id_derivedCategory (M : DerivedCategory A) :
    IsIso ((2 : ℤ) • 𝟙 M) := by
  let e := DerivedCategory.Q.objObjPreimageIso M
  have h : (2 : ℤ) • 𝟙 M = e.inv ≫ DerivedCategory.Q.map ((2 : ℤ) • 𝟙 _) ≫ e.hom := by
    simp
  rw [h]
  infer_instance

variable {A} in
/-- A splitting of the invariant idempotent of an endomorphism `τD` of an object `W` of `D(A)`,
cut out of a complex `V` by the invariants of an involution `τ` of `V` whose image corresponds
to `τD` under an isomorphism `W ≅ Q(V)`. Its object is `Q(V^τ)`. -/
def derivedInvariantsSplitting {V : CochainComplex A ℤ} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V)
    {W : DerivedCategory A} (φ : W ≅ DerivedCategory.Q.obj V) (τD : W ⟶ W)
    (h : τD ≫ φ.hom = φ.hom ≫ DerivedCategory.Q.map τ) :
    IdempotentSplitting (invariantIdempotent τD) :=
  (((invariantsSplitting τ hτ).map DerivedCategory.Q).ofEq
    (Functor.map_invariantIdempotent DerivedCategory.Q τ)).conj φ.symm
    (invariantIdempotent_conj φ.symm (by
      rw [Iso.symm_hom, ← cancel_epi φ.hom, ← reassoc_of% h]
      simp))

end Generic

/-! ### The setting -/

section Monoidal

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [HasDerivedCategory.{w} A]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
    KFlat (curriedTensor A) P ∧ QuasiIso f)

/-! ### K-flat representatives -/

include hres in
/-- Every object of `D(A)` is the image of a K-flat complex. -/
theorem exists_kFlat_iso (M : DerivedCategory A) :
    ∃ K : CochainComplex A ℤ, KFlat (curriedTensor A) K ∧
      Nonempty (DerivedCategory.Q.obj K ≅ M) := by
  obtain ⟨K, p, hK, hp⟩ := hres (DerivedCategory.Q.objPreimage M)
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

include hres in
/-- Every morphism of `D(A)` is, up to isomorphism of arrows, the image of a morphism of K-flat
complexes: write it as a right fraction and resolve the source of the fraction. -/
theorem exists_kFlat_arrowIso {M N : DerivedCategory A} (f : M ⟶ N) :
    ∃ (K₀ K₁ : CochainComplex A ℤ) (g : K₀ ⟶ K₁), KFlat (curriedTensor A) K₀ ∧
      KFlat (curriedTensor A) K₁ ∧ Nonempty (Arrow.mk (DerivedCategory.Q.map g) ≅ Arrow.mk f) := by
  obtain ⟨K₁, hK₁, ⟨e₁⟩⟩ := exists_kFlat_iso A hres N
  let e₀ := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨X', s, hs, g₀, hfac⟩ := DerivedCategory.right_fac (e₀.hom ≫ f ≫ e₁.inv)
  obtain ⟨K₀, r, hK₀, hr⟩ := hres X'
  have : IsIso (DerivedCategory.Q.map r) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ r).2 hr
  have : IsIso (DerivedCategory.Q.map (r ≫ s)) := by
    rw [Functor.map_comp]
    infer_instance
  have h : e₀.hom ≫ f = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map g₀ ≫ e₁.hom := by
    rw [← reassoc_of% hfac]
    simp
  refine ⟨K₀, K₁, r ≫ g₀, hK₀, hK₁,
    ⟨Arrow.isoMk (asIso (DerivedCategory.Q.map (r ≫ s)) ≪≫ e₀) e₁ ?_⟩⟩
  simp [h]

include hres in
/-- Every distinguished triangle of `D(A)` is isomorphic to the image of the mapping cone
triangle of a morphism of K-flat complexes. -/
theorem exists_kFlat_triangleIso (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) :
    ∃ (K₀ K₁ : CochainComplex A ℤ) (g : K₀ ⟶ K₁), KFlat (curriedTensor A) K₀ ∧
      KFlat (curriedTensor A) K₁ ∧
      Nonempty (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g) ≅ T) := by
  obtain ⟨K₀, K₁, g, h₀, h₁, ⟨e⟩⟩ := exists_kFlat_arrowIso A hres T.mor₁
  obtain ⟨e', -, -⟩ := exists_iso_of_arrow_iso _ _
    (DerivedCategory.mappingCone_triangle_distinguished g) hT e
  exact ⟨K₀, K₁, g, h₀, h₁, ⟨e'⟩⟩

/-! ### The switch on a derived tensor square -/

variable [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [SymmetricCategory (CochainComplex A ℤ)]

/-- The isomorphism `L ⊗^L L ≅ Q(Tot(K ⊗ K))` attached to a K-flat complex `K` and an
isomorphism `Q(K) ≅ L`. -/
def tensorSquareIso {K : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    {L : DerivedCategory A} (a : DerivedCategory.Q.obj K ≅ L) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    L ⊗ L ≅ DerivedCategory.Q.obj (K ⊗ K) :=
  letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  (a.symm ⊗ᵢ a.symm) ≪≫ CochainComplex.KFlatMonoidal.derivedTensorIso A hres hK hK

variable (P : ObjectProperty (DerivedCategory A)) [P.IsClosedUnderIsomorphisms]
  (hsum : ∀ K L : DerivedCategory A, P (K ⊞ L) → P K)
  (htensor : letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    ∀ K L : DerivedCategory A, P K → P L → P (K ⊗ L))

include htensor in
/-- The total tensor product of two K-flat complexes whose images lie in `P` has its image in
`P`. -/
theorem prop_Q_obj_tensorObj {K K' : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (hK' : KFlat (curriedTensor A) K') (h : P (DerivedCategory.Q.obj K))
    (h' : P (DerivedCategory.Q.obj K')) : P (DerivedCategory.Q.obj (K ⊗ K')) := by
  let _ := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  exact P.prop_of_iso (CochainComplex.KFlatMonoidal.derivedTensorIso A hres hK hK')
    (htensor _ _ h h')

variable [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))]

/-- The isomorphism `L ⊗^L L ≅ Q(Tot(K ⊗ K))` carries the switch of `D(A)` to the image of the
switch of complexes. -/
theorem braiding_comp_tensorSquareIso {K : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) {L : DerivedCategory A}
    (a : DerivedCategory.Q.obj K ≅ L) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    (β_ L L).hom ≫ (tensorSquareIso A hres hK a).hom =
      (tensorSquareIso A hres hK a).hom ≫ DerivedCategory.Q.map (β_ K K).hom := by
  let _ := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  let _ := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  simp only [tensorSquareIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom]
  rw [← BraidedCategory.braiding_naturality_assoc,
    CochainComplex.KFlatMonoidal.derivedTensorIso_braiding A hres hK hK, Category.assoc]

variable [∀ X : A, IsIso ((2 : ℤ) • 𝟙 X)]

/-- **The invariants of the switch on `L ⊗^L L`**, cut out of `Tot(K ⊗ K)` for a K-flat complex
`K` with `Q(K) ≅ L`: a splitting of `(𝟙 + σ)/2` whose object is the image of the invariants of
the Koszul switch of `K ⊗ K`. -/
def kFlatSplitting {K : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    {L : DerivedCategory A} (a : DerivedCategory.Q.obj K ≅ L) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    IdempotentSplitting (invariantIdempotent ((β_ L L).hom : L ⊗ L ⟶ L ⊗ L)) :=
  letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  derivedInvariantsSplitting (β_ K K).hom (SymmetricCategory.symmetry K K)
    (tensorSquareIso A hres hK a) (β_ L L).hom (braiding_comp_tensorSquareIso A hres hK a)

/-- **The anti-invariants of the switch on `L ⊗^L L`**, cut out of `Tot(K ⊗ K)` for a K-flat
complex `K` with `Q(K) ≅ L`: a splitting of `(𝟙 - σ)/2` whose object is the image of the
anti-invariants of the Koszul switch of `K ⊗ K`. -/
def kFlatAntiSplitting {K : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    {L : DerivedCategory A} (a : DerivedCategory.Q.obj K ≅ L) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    IdempotentSplitting (antiInvariantIdempotent ((β_ L L).hom : L ⊗ L ⟶ L ⊗ L)) :=
  letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  (derivedInvariantsSplitting (-(β_ K K).hom) (by simp) (tensorSquareIso A hres hK a)
    (-(β_ L L).hom) (by simp [braiding_comp_tensorSquareIso A hres hK a])).ofEq
    (antiInvariantIdempotent_eq _).symm

include hres in
/-- **The invariants and the anti-invariants of the switch on `L ⊗^L L` exist.** -/
theorem nonempty_invariantsSplitting (L : DerivedCategory A) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    Nonempty (IdempotentSplitting (invariantIdempotent ((β_ L L).hom : L ⊗ L ⟶ L ⊗ L))) ∧
      Nonempty (IdempotentSplitting (antiInvariantIdempotent ((β_ L L).hom : L ⊗ L ⟶ L ⊗ L))) := by
  obtain ⟨K, hK, ⟨a⟩⟩ := exists_kFlat_iso A hres L
  exact ⟨⟨kFlatSplitting A hres hK a⟩, ⟨kFlatAntiSplitting A hres hK a⟩⟩

/-! ### The value of `ψ²` on an object -/

variable [P.IsTriangulated]

/-- **The value of `ψ²` computed from a K-flat model, through any splittings.** For a K-flat
complex `K` with `Q(K) ≅ L` and any splittings `s⁺`, `s⁻` of `(𝟙 ± σ)/2` on `L ⊗^L L` whose
objects lie in `P`, the trace of the Koszul switch of `K ⊗ K` is `[s⁺] - [s⁻]`. -/
theorem derivedTrace_eq {K : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    {L : DerivedCategory A} (a : DerivedCategory.Q.obj K ≅ L) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    ∀ (sp : IdempotentSplitting (invariantIdempotent ((β_ L L).hom : L ⊗ L ⟶ L ⊗ L)))
      (sm : IdempotentSplitting (antiInvariantIdempotent ((β_ L L).hom : L ⊗ L ⟶ L ⊗ L)))
      (hp : P sp.obj) (hm : P sm.obj),
      derivedTrace P (β_ K K).hom =
        K0.cls (⟨sp.obj, hp⟩ : P.FullSubcategory) - K0.cls (⟨sm.obj, hm⟩ : P.FullSubcategory) := by
  let _ := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  let _ := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  intro sp sm hp hm
  let ep : DerivedCategory.Q.obj (invariants (β_ K K).hom) ≅ sp.obj :=
    (kFlatSplitting A hres hK a).iso sp
  let em : DerivedCategory.Q.obj (invariants (-(β_ K K).hom)) ≅ sm.obj :=
    (kFlatAntiSplitting A hres hK a).iso sm
  rw [derivedTrace, derivedClass_eq_cls_of_iso A P ep hp, derivedClass_eq_cls_of_iso A P em hm]

/-- **The value `[(L ⊗^L L)^+] - [(L ⊗^L L)^-]` of `ψ²` on an object `L`**, computed from a
chosen K-flat model `K` of `L` as the trace of the Koszul switch of `Tot(K ⊗ K)`. By
`Stacks.SecondAdamsPerfect.secondAdamsValue_eq` it does not depend on that choice. -/
def secondAdamsValue (L : P.FullSubcategory) : K0 P.FullSubcategory :=
  derivedTrace P (β_ (exists_kFlat_iso A hres L.obj).choose
    (exists_kFlat_iso A hres L.obj).choose).hom

/-- **`ψ²(L) = [(L ⊗^L L)^+] - [(L ⊗^L L)^-]`** for any splittings of the two idempotents of the
switch whose objects lie in `P`. -/
theorem secondAdamsValue_eq (L : P.FullSubcategory) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    ∀ (sp : IdempotentSplitting
        (invariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)))
      (sm : IdempotentSplitting
        (antiInvariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)))
      (hp : P sp.obj) (hm : P sm.obj),
      secondAdamsValue A hres P L =
        K0.cls (⟨sp.obj, hp⟩ : P.FullSubcategory) - K0.cls (⟨sm.obj, hm⟩ : P.FullSubcategory) :=
  derivedTrace_eq A hres P (exists_kFlat_iso A hres L.obj).choose_spec.1
    (exists_kFlat_iso A hres L.obj).choose_spec.2.some

/-! ### Closure properties -/

omit [(kFlatQ (curriedTensor A)).IsLocalization (kFlatQuasiIso (curriedTensor A))]
  [(kFlatQLeft (curriedTensor A)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor A))] in
include hsum htensor in
/-- The invariants and the anti-invariants of the Koszul switch of `K ⊗ K` have their images
in `P`, for a K-flat complex `K` whose image lies in `P`. -/
theorem prop_Q_obj_invariants {K : CochainComplex A ℤ} (hK : KFlat (curriedTensor A) K)
    (h : P (DerivedCategory.Q.obj K)) (ε : ℤˣ) :
    P (DerivedCategory.Q.obj (invariants (ε • (β_ K K).hom))) :=
  (derivedExactClass A P hsum).P_invariants _
    (by rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
      one_smul, SymmetricCategory.symmetry])
    (prop_Q_obj_tensorObj A hres P htensor hK hK h h)

include hsum htensor in
/-- **The invariants of the switch on `L ⊗^L L` lie in `P`**, whichever splitting is taken. -/
theorem prop_invariantsSplitting_obj (L : P.FullSubcategory) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    ∀ s : IdempotentSplitting
      (invariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)), P s.obj := by
  let _ := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  let _ := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  intro s
  obtain ⟨K, hK, ⟨a⟩⟩ := exists_kFlat_iso A hres L.obj
  have h := prop_Q_obj_invariants A hres P hsum htensor hK (P.prop_of_iso a.symm L.property) 1
  rw [one_smul] at h
  exact P.prop_of_iso ((kFlatSplitting A hres hK a).iso s) h

include hsum htensor in
/-- **The anti-invariants of the switch on `L ⊗^L L` lie in `P`**, whichever splitting is
taken. -/
theorem prop_antiInvariantsSplitting_obj (L : P.FullSubcategory) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
    letI := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
    ∀ s : IdempotentSplitting
      (antiInvariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ L.obj ⊗ L.obj)),
      P s.obj := by
  let _ := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  let _ := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  intro s
  obtain ⟨K, hK, ⟨a⟩⟩ := exists_kFlat_iso A hres L.obj
  have h := prop_Q_obj_invariants A hres P hsum htensor hK (P.prop_of_iso a.symm L.property) (-1)
  rw [Units.neg_smul, one_smul] at h
  exact P.prop_of_iso ((kFlatAntiSplitting A hres hK a).iso s) h

include hsum htensor in
/-- The value of `ψ²` is the trace of the Koszul switch on *any* K-flat model. -/
theorem secondAdamsValue_eq_derivedTrace (L : P.FullSubcategory) {K : CochainComplex A ℤ}
    (hK : KFlat (curriedTensor A) K) (a : DerivedCategory.Q.obj K ≅ L.obj) :
    secondAdamsValue A hres P L = derivedTrace P (β_ K K).hom := by
  let _ := CochainComplex.KFlatMonoidal.derivedMonoidal A hres
  let _ := CochainComplex.KFlatMonoidal.derivedSymmetric A hres
  have hp := prop_invariantsSplitting_obj A hres P hsum htensor L (kFlatSplitting A hres hK a)
  have hm :=
    prop_antiInvariantsSplitting_obj A hres P hsum htensor L (kFlatAntiSplitting A hres hK a)
  rw [secondAdamsValue_eq A hres P L _ _ hp hm, derivedTrace_eq A hres P hK a _ _ hp hm]

variable [MonoidalPreadditive A]

/-! ### Additivity along distinguished triangles -/

include hsum htensor in
/-- **`ψ²` is additive along distinguished triangles of `P`**: for a distinguished triangle
`L₁ ⟶ L₂ ⟶ L₃ ⟶ L₁[1]`, `ψ²(L₂) = ψ²(L₁) + ψ²(L₃)`. The triangle is the image of the degreewise
split short exact sequence `0 → K₁ → Cone(g) → K₀[1] → 0` of a map `g` of K-flat complexes, and
the trace of the switch is additive along it by the three-step filtration of [Stacks, Tag 0FEJ]
(`Stacks.SecondAdamsPerfect.switchTrace_tensorSquare`). -/
theorem secondAdamsValue_distinguished (T : Triangle P.FullSubcategory)
    (hT : T ∈ distTriang P.FullSubcategory) :
    secondAdamsValue A hres P T.obj₂ =
      secondAdamsValue A hres P T.obj₁ + secondAdamsValue A hres P T.obj₃ := by
  obtain ⟨K₀, K₁, g, h₀, h₁, ⟨e⟩⟩ :=
    exists_kFlat_triangleIso A hres _ (inv_rot_of_distTriang _ (P.ι.map_distinguished T hT))
  let S := CochainComplex.mappingCone.triangleRotateShortComplex g
  let σ := CochainComplex.mappingCone.triangleRotateShortComplexSplitting g
  have hR : ∀ X, (S.map (tensorRight X)).ShortExact := fun X =>
    CochainComplex.shortExact_map_tensorRight_of_degreewiseSplit S σ X
  let e₁ : DerivedCategory.Q.obj S.X₁ ≅ T.obj₁.obj := Triangle.π₂.mapIso e
  let e₂ : DerivedCategory.Q.obj S.X₂ ≅ T.obj₂.obj := Triangle.π₃.mapIso e
  let e₃ : DerivedCategory.Q.obj S.X₃ ≅ T.obj₃.obj :=
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app K₀ ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (Triangle.π₁.mapIso e) ≪≫
      (shiftFunctorCompIsoId (DerivedCategory A) (-1 : ℤ) 1 (by norm_num)).app _
  have k₁ : KFlat (curriedTensor A) S.X₁ := h₁
  have k₃ : KFlat (curriedTensor A) S.X₃ :=
    (kFlatObjects (curriedTensor A)).prop_of_iso
      (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).app K₀).symm
      ((kFlatObjects (curriedTensor A)).le_shift (1 : ℤ)
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K₀) h₀)
  have k₂ : KFlat (curriedTensor A) S.X₂ := kFlat_X₂_of_degreewiseSplit (curriedTensor A) S σ k₁ k₃
  have p₁ : P (DerivedCategory.Q.obj S.X₁) := P.prop_of_iso e₁.symm T.obj₁.property
  have p₂ : P (DerivedCategory.Q.obj S.X₂) := P.prop_of_iso e₂.symm T.obj₂.property
  have p₃ : P (DerivedCategory.Q.obj S.X₃) := P.prop_of_iso e₃.symm T.obj₃.property
  have key := switchTrace_tensorSquare hR (derivedExactClass A P hsum)
    (prop_Q_obj_tensorObj A hres P htensor k₁ k₁ p₁ p₁)
    (prop_Q_obj_tensorObj A hres P htensor k₂ k₂ p₂ p₂)
    (prop_Q_obj_tensorObj A hres P htensor k₃ k₃ p₃ p₃)
    (prop_Q_obj_tensorObj A hres P htensor k₁ k₂ p₁ p₂)
    (prop_Q_obj_tensorObj A hres P htensor k₂ k₁ p₂ p₁)
  rwa [secondAdamsValue_eq_derivedTrace A hres P hsum htensor T.obj₂ k₂ e₂,
    secondAdamsValue_eq_derivedTrace A hres P hsum htensor T.obj₁ k₁ e₁,
    secondAdamsValue_eq_derivedTrace A hres P hsum htensor T.obj₃ k₃ e₃]

/-! ### The second Adams operator -/

/-- **The second Adams operator `ψ² : K₀(P) ⟶ K₀(P)`**, `[L] ↦ [(L ⊗^L L)^+] - [(L ⊗^L L)^-]`.
It is well defined because the value is additive along distinguished triangles
(`Stacks.SecondAdamsPerfect.secondAdamsValue_distinguished`). -/
def secondAdams : K0 P.FullSubcategory →+ K0 P.FullSubcategory :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift (secondAdamsValue A hres P)) fun x hx => by
    refine (AddSubgroup.closure_le
      (K := (FreeAbelianGroup.lift (secondAdamsValue A hres P)).ker)).2 ?_ hx
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      secondAdamsValue_distinguished A hres P hsum htensor T hT, sub_sub, sub_self]

/-- `ψ²` sends the class of an object to its value. -/
theorem secondAdams_cls (L : P.FullSubcategory) :
    secondAdams A hres P hsum htensor (K0.cls L) = secondAdamsValue A hres P L :=
  FreeAbelianGroup.lift_apply_of _ _

end Monoidal

end Stacks.SecondAdamsPerfect

end
