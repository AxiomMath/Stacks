module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessFlatTensor
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessSectionConservativity
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessHomCommutation
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DiagonalModelHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Derived Hom along a ring map, in tensor form

Let `Δ : S → A` be a homomorphism of commutative rings and let `N` be a bounded-above complex of
finite free `S`-modules representing `A`, restricted along `Δ`, in `D(S)`. Write
`N^∨ = Hom^•(N, S)` for its dual, a bounded-below complex of finite free `S`-modules. For a
complex `X` of `S`-modules bounded below the tensor--Hom comparison of [stacks 0BYM] is an
isomorphism `X ⊗_S N^∨ ≅ Hom^•(N, X)`, and `Hom^•(N, X)` computes `Δ_* Δ^!(X)`. For a section
`s` of `Δ` and a complex `M` of `A`-modules, the projection formula of [stacks 06Y1] then turns
`Hom^•(N, s^* M)`, restricted to `A` along `s`, into the tensor product `s_* N^∨ ⊗_A M` over `A`.

So the functor `M ↦ Δ^!(s^* M)` in which the defining condition of a relative dualizing complex
([stacks 0E2C]) is stated is, on bounded-below complexes, tensoring over `A` with a fixed complex.
This file records the consequences used in
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor`.

## Main definitions

* `Dualizing.TensorForm.dual`: the dual `Hom^•(N, S)` of a complex of `S`-modules.
* `Dualizing.TensorForm.thetaIso`: the isomorphism `X ⊗ N^∨ ≅ Hom^•(N, X)` for `X` bounded below.

## Main results

* `Dualizing.TensorForm.quasiIso_of_quasiIso_whiskerLeft`: a chain map `f` of bounded-below
  complexes of `A`-modules is a quasi-isomorphism as soon as `s_* N^∨ ◁ f` is one.
* `Dualizing.TensorForm.nonempty_restrictScalars_homComplex_iso`: `Hom^•(N, E)`, restricted to `A`
  along any section, represents `Δ^!(E)`.
* `Dualizing.TensorForm.exists_quasiIso_of_derivedHom_iso`: a condition `Δ^!(E) ≅ A` produces a
  quasi-isomorphism `A ⟶ s_*(N^∨ ⊗ E)` of complexes.
* `Dualizing.TensorForm.nonempty_iso_derivedHom_tensor`: for bounded-below `X` and `M` with
  `Δ^!(s^* X) ≅ A` and `Δ^!(s'^* M) ≅ A`, under a flatness condition, `X ≅ Δ^!(s'^* M ⊗ s^* X)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing.TensorForm

variable {A S : Type u} [CommRing A] [CommRing S]

/-- The dual `Hom^•(N, S)` of a complex of `S`-modules. -/
noncomputable abbrev dual (N : CochainComplex (ModuleCat.{u} S) ℤ) :
    CochainComplex (ModuleCat.{u} S) ℤ :=
  CochainComplex.HomComplexR S N (𝟙_ (CochainComplex (ModuleCat.{u} S) ℤ))

/-- If `N` is strictly concentrated in degrees `≤ d`, its dual is strictly concentrated in
degrees `≥ -d`. -/
lemma dual_isStrictlyGE (N : CochainComplex (ModuleCat.{u} S) ℤ) (d : ℤ) [N.IsStrictlyLE d] :
    (dual N).IsStrictlyGE (-d) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have : Subsingleton ((dual N).X i) := by
    refine ⟨fun z z' => ?_⟩
    change CochainComplex.HomComplex.Cochain _ _ i at z z'
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    by_cases hp : d < p
    · exact (N.isZero_of_isStrictlyLE d p hp).eq_of_src _ _
    · have hq : q ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  exact ModuleCat.isZero_of_subsingleton _

/-- The Hom-complex map induced by an isomorphism of targets is an isomorphism. -/
noncomputable def homCxMapIso (N : CochainComplex (ModuleCat.{u} S) ℤ)
    {X Y : CochainComplex (ModuleCat.{u} S) ℤ} (e : X ≅ Y) :
    CochainComplex.HomComplexR S N X ≅ CochainComplex.HomComplexR S N Y where
  hom := Stacks.HomComplex.TensorHomComparison.HomCxMap N N X Y (𝟙 N) e.hom
  inv := Stacks.HomComplex.TensorHomComparison.HomCxMap N N Y X (𝟙 N) e.inv
  hom_inv_id := by
    rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, Category.id_comp, e.hom_inv_id,
      Stacks.HomComplex.TensorHomComparison.HomCxMap_id]
  inv_hom_id := by
    rw [← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, Category.id_comp, e.inv_hom_id,
      Stacks.HomComplex.TensorHomComparison.HomCxMap_id]

section Theta

variable (N : CochainComplex (ModuleCat.{u} S) ℤ) (d : ℤ) [N.IsStrictlyLE d]
  [∀ i, Module.Finite S (N.X i)] [∀ i, Module.Projective S (N.X i)]

/-- **The tensor--Hom comparison at the dual.** For `X` bounded below,
`X ⊗ Hom^•(N, S) ≅ Hom^•(N, X)`. -/
noncomputable def thetaIso (X : CochainComplex (ModuleCat.{u} S) ℤ) (a : ℤ) [X.IsStrictlyGE a] :
    X ⊗ dual N ≅ CochainComplex.HomComplexR S N X :=
  have := Dualizing.FlatTensor.tensorUnit_isStrictlyGE (R := S) 0 le_rfl
  have := Stacks.DerivedTensorHomDiagonal.isIso_theta_of_boundedBelow X
    (𝟙_ (CochainComplex (ModuleCat.{u} S) ℤ)) N a 0 d
  asIso (Stacks.HomComplex.TensorHomComparison.theta X
      (𝟙_ (CochainComplex (ModuleCat.{u} S) ℤ)) N) ≪≫ homCxMapIso N (ρ_ X)

/-- The isomorphism `thetaIso` is natural in the bounded-below complex `X`. -/
lemma thetaIso_naturality {X X' : CochainComplex (ModuleCat.{u} S) ℤ} (a : ℤ)
    [X.IsStrictlyGE a] [X'.IsStrictlyGE a] (f : X ⟶ X') :
    f ▷ dual N ≫ (thetaIso N d X' a).hom = (thetaIso N d X a).hom ≫
      Stacks.HomComplex.TensorHomComparison.HomCxMap N N X X' (𝟙 N) f := by
  simp only [thetaIso, Iso.trans_hom, asIso_hom, homCxMapIso]
  rw [← reassoc_of% (Stacks.HomComplex.TensorHomComparison.theta_natural_K X X'
    (𝟙_ (CochainComplex (ModuleCat.{u} S) ℤ)) N f),
    ← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, Category.assoc,
    ← Stacks.HomComplex.TensorHomComparison.HomCxMap_comp, Category.id_comp,
    MonoidalCategory.rightUnitor_naturality]

end Theta

/-- A complex of `S`-modules whose Hom complex out of `N` is acyclic has no nonzero cohomology
classes of maps out of `N`. -/
lemma cohomologyClass_eq_zero_of_acyclic (N Y : CochainComplex (ModuleCat.{u} S) ℤ)
    (h : (CochainComplex.HomComplexR S N Y).Acyclic) (q : ℤ)
    (c : CochainComplex.HomComplex.CohomologyClass N Y q) : c = 0 := by
  have hex : (CochainComplex.HomComplex N Y).ExactAt q := by
    have := h q
    rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at this
    rwa [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  have : Subsingleton ((CochainComplex.HomComplex N Y).homology q) :=
    AddCommGrpCat.subsingleton_of_isZero
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)
  obtain ⟨x, rfl⟩ := (CochainComplex.HomComplex.homologyAddEquiv N Y q).surjective c
  rw [Subsingleton.elim x 0, map_zero]

/-- Extension of scalars of a complex strictly concentrated in degrees `≥ a` is strictly
concentrated in degrees `≥ a`. -/
lemma extendScalars_isStrictlyGE (s : A →+* S) (C : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ)
    [C.IsStrictlyGE a] : ((CochainComplex.extendScalars s).obj C).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi =>
    (ModuleCat.extendScalars s).map_isZero (C.isZero_of_isStrictlyGE a i hi)

/-- Restriction of scalars of a complex strictly concentrated in degrees `≥ a` is strictly
concentrated in degrees `≥ a`. -/
lemma restrictScalars_isStrictlyGE (s : A →+* S) (C : CochainComplex (ModuleCat.{u} S) ℤ) (a : ℤ)
    [C.IsStrictlyGE a] : ((CochainComplex.restrictScalars s).obj C).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi =>
    (ModuleCat.restrictScalars s).map_isZero (C.isZero_of_isStrictlyGE a i hi)

/-- The mapping cone of a map between complexes strictly concentrated in degrees `≥ a` is strictly
concentrated in degrees `≥ a - 1`. -/
lemma mappingCone_isStrictlyGE {X X' : CochainComplex (ModuleCat.{u} A) ℤ} (a : ℤ)
    [X.IsStrictlyGE a] [X'.IsStrictlyGE a] (f : X ⟶ X') :
    (CochainComplex.mappingCone f).IsStrictlyGE (a - 1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨X.isZero_of_isStrictlyGE a (i + 1) (by omega), X'.isZero_of_isStrictlyGE a i (by omega)⟩

/-- The tensor product of complexes strictly concentrated in degrees `≥ a` and `≥ b` is strictly
concentrated in degrees `≥ a + b`. -/
lemma tensor_isStrictlyGE (P Q : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [Q.IsStrictlyGE b] :
    CochainComplex.IsStrictlyGE (P ⊗ Q) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : Limits.IsZero (P.X p ⊗ Q.X q) := by
    by_cases hp : p < a
    · exact (tensorRight (Q.X q)).map_isZero (P.isZero_of_isStrictlyGE a p hp)
    · exact (tensorLeft (P.X p)).map_isZero
        (Q.isZero_of_isStrictlyGE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- A morphism of cochain complexes is a quasi-isomorphism exactly when its mapping cone is
acyclic. -/
lemma quasiIso_iff_acyclic_mappingCone {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic _).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

section Section

variable (Δ : S →+* A) (s : A →+* S)
  (N : CochainComplex (ModuleCat.{u} S) ℤ) (d : ℤ)
  [∀ i, Module.Finite S (N.X i)] [∀ i, Module.Free S (N.X i)]

/-- If `s_* N^∨ ⊗_A C` is acyclic for a bounded-below complex `C` of `A`-modules, then every
cohomology class of maps from `N` to the extension of scalars `s^* C` vanishes. -/
lemma cohomologyClass_eq_zero_of_acyclic_tensor [N.IsStrictlyLE d]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) [C.IsStrictlyGE a]
    (h : ((CochainComplex.restrictScalars s).obj (dual N) ⊗ C).Acyclic) (q : ℤ)
    (c : CochainComplex.HomComplex.CohomologyClass N
      ((CochainComplex.extendScalars s).obj C) q) : c = 0 := by
  have h1 : ((CochainComplex.restrictScalars s).obj
      (dual N ⊗ (CochainComplex.extendScalars s).obj C)).Acyclic :=
    h.of_iso (baseChangeTensorIso s C (dual N)).symm
  rw [CochainComplex.restrictScalars_acyclic_iff] at h1
  let := CochainComplex.Koszul.koszulSymmetric S
  have := extendScalars_isStrictlyGE s C a
  exact cohomologyClass_eq_zero_of_acyclic N _
    ((h1.of_iso (β_ _ _)).of_iso (thetaIso N d _ a)) q c

/-- **Conservativity of `Δ^! ∘ s^*`, in tensor form.** Let `Δ : S → A` have finitely generated
kernel, let `s` be a section of `Δ`, and let `N` be a bounded-above complex of finite free
`S`-modules representing `A`. A chain map `f` of bounded-below complexes of `A`-modules is a
quasi-isomorphism as soon as `s_* N^∨ ◁ f` is one. -/
theorem quasiIso_of_quasiIso_whiskerLeft [N.IsStrictlyLE d] (hs : Δ.comp s = RingHom.id A)
    (hker : (RingHom.ker Δ).FG)
    (eN : DerivedCategory.Q.obj N ≅ (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    {X X' : CochainComplex (ModuleCat.{u} A) ℤ} (a : ℤ) [X.IsStrictlyGE a] [X'.IsStrictlyGE a]
    (f : X ⟶ X') (hf : QuasiIso ((CochainComplex.restrictScalars s).obj (dual N) ◁ f)) :
    QuasiIso f := by
  have : ∀ i, Projective (N.X i) := fun i =>
    ModuleCat.projective_of_categoryTheory_projective (N.X i)
  let D := (CochainComplex.restrictScalars s).obj (dual N)
  rw [quasiIso_iff_acyclic_mappingCone]
  have hC : (D ⊗ CochainComplex.mappingCone f).Acyclic :=
    ((quasiIso_iff_acyclic_mappingCone (D ◁ f)).1 hf).of_iso
      (TleftCochain_mappingCone_iso D f).symm
  have := mappingCone_isStrictlyGE a f
  exact SectionConservativity.acyclic_of_isZero_derivedHom Δ s hs hker _
    (SectionConservativity.isZero_derivedHom_of_cohomologyClass_eq_zero Δ N d eN _
      (cohomologyClass_eq_zero_of_acyclic_tensor s N d _ (a - 1) hC))

omit [∀ i, Module.Finite S (N.X i)] in
/-- **`Hom^•(N, E)`, restricted along a section of `Δ`, represents `Δ^!(E)`.** -/
theorem nonempty_restrictScalars_homComplex_iso [N.IsStrictlyLE d]
    (hs : Δ.comp s = RingHom.id A)
    (eN : DerivedCategory.Q.obj N ≅ (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (E : CochainComplex (ModuleCat.{u} S) ℤ) :
    Nonempty (DerivedCategory.Q.obj
        ((CochainComplex.restrictScalars s).obj (CochainComplex.HomComplexR S N E)) ≅
      (derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj E)) := by
  have : ∀ i, Projective (N.X i) := fun i =>
    ModuleCat.projective_of_categoryTheory_projective (N.X i)
  let e₁ := (StacksDraft.DerivedHom.projectiveHomComparison (R := S)).iso N E d
  let e₂ := (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom S).mapIso
    (Iso.prod eN.op (Iso.refl (DerivedCategory.Q.obj E)))
  obtain ⟨e₃⟩ := nonempty_modelHomIsoRestrictScalarsDerivedHom.{u} Δ (DerivedCategory.Q.obj E)
  let e₄ := e₁.symm ≪≫ e₂.symm ≪≫ e₃
  exact ⟨((ModuleCat.restrictScalars.{u} s).mapDerivedCategoryFactors.app
      (CochainComplex.HomComplexR S N E)).symm ≪≫
    (ModuleCat.restrictScalars.{u} s).mapDerivedCategory.mapIso e₄ ≪≫
    (derivedRestrictScalarsSectionIso s Δ hs).app _⟩

/-- The monoidal unit of complexes of `A`-modules is K-projective. -/
lemma tensorUnit_isKProjective :
    (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).IsKProjective := by
  have : (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).IsStrictlyLE 0 := by
    change CochainComplex.IsStrictlyLE ((HomologicalComplex.single (ModuleCat.{u} A)
      (ComplexShape.up ℤ) 0).obj (𝟙_ (ModuleCat.{u} A))) 0
    infer_instance
  have : ∀ n, Projective ((𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      change Projective ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (𝟙_ (ModuleCat.{u} A)) |>.X 0)
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{u} A))).symm
        (ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} A))
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).projective
  exact CochainComplex.isKProjective_of_projective _ 0

/-- An isomorphism in `D(A)` out of the monoidal unit is induced by a quasi-isomorphism of
complexes. -/
lemma exists_quasiIso_of_iso (Z : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ≅
      DerivedCategory.Q.obj Z) :
    ∃ ι : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶ Z, QuasiIso ι := by
  have := tensorUnit_isKProjective (A := A)
  let κ := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective
    (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))
    ((HomotopyCategory.quotient _ _).obj Z)).surjective
      ((κ.app _).hom ≫ e.hom ≫ (κ.app Z).inv)
  obtain ⟨ι, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_surjective g
  refine ⟨ι, (DerivedCategory.isIso_Q_map_iff_quasiIso _ ι).1 ?_⟩
  have h' : DerivedCategory.Q.map ι = (κ.app _).inv ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map ι) ≫ (κ.app Z).hom := by
    rw [← cancel_epi (κ.app _).hom, Iso.hom_inv_id_assoc]
    exact (κ.hom.naturality ι).symm
  have : DerivedCategory.Q.map ι = e.hom := by
    rw [h', hg]
    simp
  rw [this]
  infer_instance

/-- **`s_*(N^∨ ⊗ E)` represents `Δ^!(E)`** for `E` bounded below. -/
private theorem nonempty_iso_restrictScalars_dual_tensor [N.IsStrictlyLE d]
    (hs : Δ.comp s = RingHom.id A)
    (eN : DerivedCategory.Q.obj N ≅ (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (E : CochainComplex (ModuleCat.{u} S) ℤ) (a : ℤ) [E.IsStrictlyGE a] :
    Nonempty (DerivedCategory.Q.obj ((CochainComplex.restrictScalars s).obj (dual N ⊗ E)) ≅
      (derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj E)) := by
  let := CochainComplex.Koszul.koszulSymmetric S
  obtain ⟨e⟩ := nonempty_restrictScalars_homComplex_iso Δ s N d hs eN E
  exact ⟨DerivedCategory.Q.mapIso ((CochainComplex.restrictScalars s).mapIso
    (β_ _ _ ≪≫ thetaIso N d E a)) ≪≫ e⟩

/-- **A condition `Δ^!(E) ≅ A` gives a quasi-isomorphism of complexes.** If `E` is bounded below
and `Δ^!(E) ≅ A[0]`, then for every section `s` of `Δ` there is a quasi-isomorphism from the
monoidal unit to `s_*(N^∨ ⊗ E)`. -/
theorem exists_quasiIso_of_derivedHom_iso [N.IsStrictlyLE d]
    (hs : Δ.comp s = RingHom.id A)
    (eN : DerivedCategory.Q.obj N ≅ (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (E : CochainComplex (ModuleCat.{u} S) ℤ) (a : ℤ) [E.IsStrictlyGE a]
    (hE : Nonempty ((derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj E) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :
    ∃ ι : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶
      (CochainComplex.restrictScalars s).obj (dual N ⊗ E), QuasiIso ι := by
  obtain ⟨e⟩ := nonempty_iso_restrictScalars_dual_tensor Δ s N d hs eN E a
  exact exists_quasiIso_of_iso _ (hE.some.symm ≪≫ e.symm)

/-- **The comparison.** Let `Δ : S → A` have finitely generated kernel, let `s`, `s'` be two
sections of `Δ` and let `N` be a bounded-above complex of finite free `S`-modules representing
`A`. Let `X` and `M` be bounded-below complexes of `A`-modules with `Δ^!(s^* X) ≅ A` and
`Δ^!(s'^* M) ≅ A`, and assume that `s_*(N^∨ ⊗ s'^* M)` has flat terms. Then
`X ≅ Δ^!(s'^* M ⊗ s^* X)` in `D(A)`. -/
theorem nonempty_iso_derivedHom_tensor [N.IsStrictlyLE d] (s' : A →+* S)
    (hs : Δ.comp s = RingHom.id A)
    (hker : (RingHom.ker Δ).FG)
    (eN : DerivedCategory.Q.obj N ≅ (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (X M : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) [X.IsStrictlyGE a] [M.IsStrictlyGE a]
    (hflat : ∀ n, Module.Flat A (((CochainComplex.restrictScalars s).obj
      (dual N ⊗ (CochainComplex.extendScalars s').obj M)).X n))
    (hX : Nonempty ((derivedHom.{u, u} Δ).obj
      (DerivedCategory.Q.obj ((CochainComplex.extendScalars s).obj X)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)))
    (hM : Nonempty ((derivedHom.{u, u} Δ).obj
      (DerivedCategory.Q.obj ((CochainComplex.extendScalars s').obj M)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :
    Nonempty (DerivedCategory.Q.obj X ≅ (derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj
      ((CochainComplex.extendScalars s').obj M ⊗ (CochainComplex.extendScalars s).obj X))) := by
  let Ex := (CochainComplex.extendScalars s).obj X
  let Em := (CochainComplex.extendScalars s').obj M
  let D := (CochainComplex.restrictScalars s).obj (dual N)
  let D' := (CochainComplex.restrictScalars s).obj (dual N ⊗ Em)
  have : Ex.IsStrictlyGE a := extendScalars_isStrictlyGE s X a
  have : Em.IsStrictlyGE a := extendScalars_isStrictlyGE s' M a
  have : (dual N).IsStrictlyGE (-d) := dual_isStrictlyGE N d
  have : D.IsStrictlyGE (-d) := restrictScalars_isStrictlyGE s _ _
  have : (Em ⊗ Ex).IsStrictlyGE (a + a) := tensor_isStrictlyGE (A := S) _ _ a a
  have : (dual N ⊗ Em).IsStrictlyGE (-d + a) := tensor_isStrictlyGE (A := S) _ _ (-d) a
  have : D'.IsStrictlyGE (-d + a) := restrictScalars_isStrictlyGE s _ _
  have : (D ⊗ X).IsStrictlyGE (-d + a) := tensor_isStrictlyGE _ _ (-d) a
  have : (D' ⊗ X).IsStrictlyGE (-d + a + a) := tensor_isStrictlyGE _ _ (-d + a) a
  have : (dual N ⊗ Ex).IsStrictlyGE (-d + a) := tensor_isStrictlyGE (A := S) _ _ (-d) a
  obtain ⟨ι, hι⟩ := exists_quasiIso_of_derivedHom_iso Δ s N d hs eN Em a hM
  obtain ⟨ι₀, hι₀⟩ := exists_quasiIso_of_derivedHom_iso Δ s N d hs eN Ex a hX
  let ι' : 𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ) ⟶ D ⊗ X :=
    ι₀ ≫ (baseChangeTensorIso s X (dual N)).hom
  have : QuasiIso ι' := inferInstance
  let b := min 0 (-d + a)
  have : (D ⊗ X).IsStrictlyGE b :=
    CochainComplex.isStrictlyGE_of_ge _ b (-d + a) (min_le_right _ _)
  have : ∀ n, Module.Flat A (D'.X n) := hflat
  have hcore := Dualizing.FlatTensor.quasiIso_core D D' X b (min_le_left _ _) ι ι'
  let f : X ⟶ D' ⊗ X := (λ_ X).inv ≫ ι ▷ X
  let c := min a (-d + a + a)
  have : X.IsStrictlyGE c := CochainComplex.isStrictlyGE_of_ge _ c a (min_le_left _ _)
  have : (D' ⊗ X).IsStrictlyGE c :=
    CochainComplex.isStrictlyGE_of_ge _ c (-d + a + a) (min_le_right _ _)
  have : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2
    (quasiIso_of_quasiIso_whiskerLeft Δ s N d hs hker eN c f hcore)
  let e₁ : D' ⊗ X ≅ (CochainComplex.restrictScalars s).obj (dual N ⊗ (Em ⊗ Ex)) :=
    (baseChangeTensorIso s X (dual N ⊗ Em)).symm ≪≫
      (CochainComplex.restrictScalars s).mapIso (α_ _ _ _)
  obtain ⟨e₂⟩ := nonempty_iso_restrictScalars_dual_tensor Δ s N d hs eN (Em ⊗ Ex) (a + a)
  exact ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.mapIso e₁ ≪≫ e₂⟩

end Section

section Flatness

open scoped TensorProduct

/-- A degree of the dual is the linear dual of a term of `N`. -/
noncomputable def dualXLinearEquiv (N : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    (dual N).X i ≃ₗ[S] Module.Dual S (N.X (-i)) :=
  let e : (dual N).X i ≃+ Module.Dual S (N.X (-i)) :=
    (CochainComplex.HomComplex.Cochain.toSingleEquiv (K := N)
      (X := 𝟙_ (ModuleCat.{u} S)) (p := -i) (q := 0) (n := i) (by omega)).trans
    ModuleCat.homAddEquiv
  { e with
    map_smul' := fun r z => by
      refine LinearMap.ext fun x => ?_
      simp only [e, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        CochainComplex.HomComplex.Cochain.toSingleEquiv, RingHom.id_apply]
      rfl }

/-- If the terms of `N` are finite free, every term of its dual is flat. -/
lemma flat_dual_X (N : CochainComplex (ModuleCat.{u} S) ℤ)
    [∀ i, Module.Finite S (N.X i)] [∀ i, Module.Free S (N.X i)] (i : ℤ) :
    Module.Flat S ((dual N).X i) :=
  Module.Flat.of_linearEquiv (dualXLinearEquiv N i)

/-- Flatness over the base of a tensor product over an algebra, of a module flat over the
algebra with a module flat over the base. -/
lemma flat_tensorProduct' {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (P Q : Type*) [AddCommGroup P] [AddCommGroup Q]
    [Module R P] [Module A P] [IsScalarTower R A P]
    [Module R Q] [Module A Q] [IsScalarTower R A Q]
    [Module.Flat A P] [Module.Flat R Q] : Module.Flat R (P ⊗[A] Q) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf
  let g := TensorProduct.AlgebraTensorModule.lTensor A Q f
  have hgP : Function.Injective (g.lTensor P) :=
    Module.Flat.lTensor_preserves_injective_linearMap g
      (Module.Flat.lTensor_preserves_injective_linearMap f hf)
  let eX := TensorProduct.AlgebraTensorModule.assoc R A A P Q X
  let eY := TensorProduct.AlgebraTensorModule.assoc R A A P Q Y
  have he : eY.toLinearMap.restrictScalars R ∘ₗ f.lTensor (P ⊗[A] Q) =
      (g.lTensor P).restrictScalars R ∘ₗ eX.toLinearMap.restrictScalars R := by
    refine TensorProduct.ext' fun z x => ?_
    induction z using TensorProduct.inductionOn with
    | tmul p q => rfl
    | add z z' hz hz' =>
        simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hz hz'
  intro x y h
  apply eX.injective
  apply hgP
  exact (LinearMap.congr_fun he x).symm.trans ((congrArg eY h).trans (LinearMap.congr_fun he y))

/-- **The terms of `s_*(N^∨ ⊗ Y)` are flat over `A`** when those of `s_* Y` are. -/
lemma flat_restrictScalars_dual_tensor_X (s : A →+* S) (N : CochainComplex (ModuleCat.{u} S) ℤ)
    [∀ i, Module.Finite S (N.X i)] [∀ i, Module.Free S (N.X i)]
    (Y : CochainComplex (ModuleCat.{u} S) ℤ)
    (hY : ∀ j, Module.Flat A ((ModuleCat.restrictScalars s).obj (Y.X j))) (n : ℤ) :
    Module.Flat A (((CochainComplex.restrictScalars s).obj (dual N ⊗ Y)).X n) := by
  classical
  let : Algebra A S := s.toAlgebra
  let U := ModuleCat.restrictScalars s
  let F : {pq : ℤ × ℤ // pq.1 + pq.2 = n} → ModuleCat.{u} S :=
    fun pq => (dual N).X pq.1.1 ⊗ Y.X pq.1.2
  have hF : ∀ j, Module.Flat A (U.obj (F j)) := by
    intro j
    have := flat_dual_X N j.1.1
    let _ : Module A (Y.X j.1.2) := (U.obj (Y.X j.1.2)).isModule
    let _ : Module A ((dual N).X j.1.1) := (U.obj ((dual N).X j.1.1)).isModule
    have : IsScalarTower A S (Y.X j.1.2) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : IsScalarTower A S ((dual N).X j.1.1) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Flat A (Y.X j.1.2) := hY j.1.2
    exact flat_tensorProduct' ((dual N).X j.1.1) (Y.X j.1.2)
  change Module.Flat A (U.obj (∐ F : ModuleCat.{u} S))
  have hds : Module.Flat A (U.obj (ModuleCat.of S (DirectSum _ fun j => (F j : Type u)))) :=
    (Module.Flat.directSum : Module.Flat A (DirectSum _ fun j => (U.obj (F j) : Type u)))
  exact Module.Flat.of_linearEquiv (U.mapIso (ModuleCat.coprodIsoDirectSum F)).toLinearEquiv

end Flatness

end Dualizing.TensorForm
