module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasicoherentChaotic
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The Čech complex of an object covering the final object

Let `(C, J)` be a site and `U` an object whose finite nonempty powers `U^{n+1}` exist. The Čech
complex of a presheaf `P` for `U` is `P(U) → P(U × U) → P(U × U × U) → ⋯`, the alternating
coface complex of `P` on the Čech nerve `[n] ↦ U^{n+1}` of `U` over the final object. No final
object of `C` is needed. When `U` covers the final object (`J.CoversTop`), this is the Čech
complex of the covering `{U → *}`.

* For an injective presheaf of modules the Čech complex is exact in positive degrees: it is the
  complex of maps out of the free Čech complex `R[Hom(-, U^{•+1})]`, which is exact in positive
  degrees because at each object `V` with a map `V ⟶ U` the simplicial set `Hom(V, U^{•+1})` is
  contractible (prepending a fixed map is an extra degeneracy), while at the other objects it is
  empty.
* For a sheaf of modules and `U` covering the final object, the restriction of global sections to
  `U` identifies them with the degree-zero Čech cocycles.

Both are stated for the Čech complex read as a complex of modules over a base ring `A` mapping to
the global sections of the structure sheaf.

## Main definitions

* `Stacks.CechTop.cechNerve`: the simplicial object `[n] ↦ U^{n+1}`.
* `Stacks.CechTop.cechComplex`: the Čech complex of a presheaf.
* `Stacks.CechTop.freeCechComplex`: the free Čech complex.
* `Stacks.CechTop.sectionsOverBase`, `Stacks.CechTop.cechFunctorOverBase`: sections of a sheaf of
  modules and its Čech complex, as `A`-modules; `Stacks.CechTop.globalSectionsOverBase` and
  `Stacks.CechTop.cechAugmentation`: the global sections and the augmentation.

## Main results

* `Stacks.CechTop.freeCechComplex_exactAt`: the free Čech complex is exact in positive degrees.
* `Stacks.CechTop.cechComplex_exactAt_of_injective`,
  `Stacks.CechTop.cechComplexOverBase_exactAt_of_injective`: the Čech complex of an injective
  module is exact in positive degrees.
* `Stacks.CechTop.isIso_kernelLift_cechAugmentation`: global sections are the degree-zero
  cocycles.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe u u'

namespace Stacks.CechTop

variable {C : Type u'} [Category.{u} C] (U : C)
  [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) => U)]

/-- The Čech nerve of an object over the final object: the simplicial object `[n] ↦ U^{n+1}`,
whose faces and degeneracies are induced by the corresponding maps of finite ordinals. It exists
as soon as the finite nonempty powers of `U` do; no final object is needed. -/
noncomputable def cechNerve : SimplicialObject C where
  obj n := ∏ᶜ fun _ : Fin (n.unop.len + 1) => U
  map f := Pi.lift fun i => Pi.π _ (f.unop.toOrderHom i)
  map_id n := by
    ext i
    simp
  map_comp f g := by
    ext i
    simp

/-- The map of the Čech nerve along `f`, followed by the `i`-th projection, is the projection
indexed by the image of `i` under `f`. -/
@[reassoc (attr := simp)]
theorem cechNerve_map_π {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (i : Fin (m.unop.len + 1)) :
    (cechNerve U).map f ≫ Pi.π _ i = Pi.π _ (f.unop.toOrderHom i) :=
  Pi.lift_comp_π _ _

/-! ### The free resolution of the final object -/

section Free

variable {V : C} (g₀ : V ⟶ U)

/-- The Čech nerve of `U` read through `Hom(V, -)`: the simplicial set `[n] ↦ Hom(V, U^{n+1})`,
augmented to a point. -/
noncomputable abbrev homCechNerve (V : C) : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augmentOfIsTerminal
    (cechNerve U ⋙ yoneda ⋙ (evaluation Cᵒᵖ (Type u)).obj (op V)) Types.isTerminalPUnit

/-- The simplicial structure maps of `Hom(V, U^{•+1})` are postcomposition with those of the
Čech nerve. -/
theorem homCechNerve_left_map_apply (V : C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (homCechNerve U V).left.obj n) :
    (homCechNerve U V).left.map f x = (x ≫ (cechNerve U).map f : V ⟶ _) := rfl

/-- The projections out of a term of the Čech nerve. -/
noncomputable abbrev cechπ (n : ℕ) (i : Fin (n + 1)) : (cechNerve U).obj (op ⦋n⦌) ⟶ U :=
  Pi.π (fun _ : Fin (⦋n⦌.len + 1) => U) i

/-- Two morphisms into `U^{n+1}` agreeing after every projection are equal. -/
theorem cechNerve_hom_ext {W : C} {n : ℕ} {f g : W ⟶ (cechNerve U).obj (op ⦋n⦌)}
    (h : ∀ i : Fin (n + 1), f ≫ cechπ U n i = g ≫ cechπ U n i) : f = g :=
  Pi.hom_ext _ _ h

/-- The map of the Čech nerve induced by `f : ⦋m⦌ ⟶ ⦋n⦌`, followed by the `i`-th projection, is
the projection indexed by `f i`. -/
@[reassoc (attr := simp)]
theorem cechNerve_map_cechπ {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (cechNerve U).map f.op ≫ cechπ U m i = cechπ U n (f.toOrderHom i) :=
  Pi.lift_comp_π _ _

/-- Prepending `g₀` to a tuple of morphisms `V ⟶ U`. -/
noncomputable def prepend (n : ℕ) (x : V ⟶ (cechNerve U).obj (op ⦋n⦌)) :
    V ⟶ (cechNerve U).obj (op ⦋n + 1⦌) :=
  Pi.lift (Fin.cases g₀ fun i => x ≫ cechπ U n i)

/-- The first component of `prepend U g₀ n x` is `g₀`. -/
@[reassoc (attr := simp)]
theorem prepend_π_zero (n : ℕ) (x : V ⟶ (cechNerve U).obj (op ⦋n⦌)) :
    prepend U g₀ n x ≫ cechπ U (n + 1) 0 = g₀ :=
  Pi.lift_comp_π _ _

/-- The `(i + 1)`-th component of `prepend U g₀ n x` is the `i`-th component of `x`. -/
@[reassoc (attr := simp)]
theorem prepend_π_succ (n : ℕ) (x : V ⟶ (cechNerve U).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    prepend U g₀ n x ≫ cechπ U (n + 1) i.succ = x ≫ cechπ U n i :=
  Pi.lift_comp_π _ _

/-- Dropping the last component of `prepend U g₀ 0 x` leaves the morphism `V ⟶ U^1` with
component `g₀`. -/
theorem prepend_δ_one (x : V ⟶ (cechNerve U).obj (op ⦋0⦌)) :
    prepend U g₀ 0 x ≫ (cechNerve U).map (SimplexCategory.δ (1 : Fin 2)).op =
      Pi.lift fun _ => g₀ := by
  refine cechNerve_hom_ext U fun i => ?_
  fin_cases i
  simp only [Category.assoc, cechNerve_map_cechπ]
  exact (prepend_π_zero U g₀ 0 x).trans (Pi.lift_comp_π (fun _ : Fin (⦋0⦌.len + 1) => g₀) _).symm

/-- Dropping the first component of `prepend U g₀ n x` recovers `x`. -/
theorem prepend_δ_zero (n : ℕ) (x : V ⟶ (cechNerve U).obj (op ⦋n⦌)) :
    prepend U g₀ n x ≫ (cechNerve U).map (SimplexCategory.δ (0 : Fin (n + 2))).op = x := by
  refine cechNerve_hom_ext U fun i => ?_
  simp only [Category.assoc, cechNerve_map_cechπ]
  exact prepend_π_succ U g₀ n x i

/-- Prepending `g₀` commutes with the faces: the face `δ (i + 1)` after prepending is prepending
after the face `δ i`. -/
theorem prepend_δ_succ (n : ℕ) (i : Fin (n + 2)) (x : V ⟶ (cechNerve U).obj (op ⦋n + 1⦌)) :
    prepend U g₀ (n + 1) x ≫ (cechNerve U).map (SimplexCategory.δ i.succ).op =
      prepend U g₀ n (x ≫ (cechNerve U).map (SimplexCategory.δ i).op) := by
  refine cechNerve_hom_ext U fun j => ?_
  simp only [Category.assoc, cechNerve_map_cechπ]
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.δ]
  | succ j => simp [SimplexCategory.δ, Fin.succ_succAbove_succ]

/-- Prepending `g₀` commutes with the degeneracies: the degeneracy `σ (i + 1)` after prepending
is prepending after the degeneracy `σ i`. -/
theorem prepend_σ_succ (n : ℕ) (i : Fin (n + 1)) (x : V ⟶ (cechNerve U).obj (op ⦋n⦌)) :
    prepend U g₀ n x ≫ (cechNerve U).map (SimplexCategory.σ i.succ).op =
      prepend U g₀ (n + 1) (x ≫ (cechNerve U).map (SimplexCategory.σ i).op) := by
  refine cechNerve_hom_ext U fun j => ?_
  simp only [Category.assoc, cechNerve_map_cechπ]
  induction j using Fin.cases with
  | zero => simp [SimplexCategory.σ]
  | succ j => simp [SimplexCategory.σ]

/-- A morphism `g₀ : V ⟶ U` contracts the simplicial set `[n] ↦ Hom(V, U^{n+1})`: prepending
`g₀` to a tuple is an extra degeneracy. -/
noncomputable def homCechNerveExtraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (homCechNerve U V) where
  s' := TypeCat.ofHom fun _ => (Pi.lift fun _ => g₀ : V ⟶ (cechNerve U).obj (op ⦋0⦌))
  s n := TypeCat.ofHom (prepend U g₀ n)
  s'_comp_ε := ConcreteCategory.hom_ext _ _ fun _ => rfl
  s₀_comp_δ₁ := ConcreteCategory.hom_ext _ _ fun x => prepend_δ_one U g₀ x
  s_comp_δ₀ n := ConcreteCategory.hom_ext _ _ fun x => prepend_δ_zero U g₀ n x
  s_comp_δ n i := ConcreteCategory.hom_ext _ _ fun x => prepend_δ_succ U g₀ n i x
  s_comp_σ n i := ConcreteCategory.hom_ext _ _ fun x => prepend_σ_succ U g₀ n i x

end Free

/-! ### The free Čech complex -/

section FreeComplex

variable (R : Cᵒᵖ ⥤ RingCat.{u})

/-- The free Čech complex of `U` with coefficients in a presheaf of rings `R`: the alternating
face complex of `[n] ↦ R[Hom(-, U^{n+1})]`. It resolves, in positive degrees, the free module on
the subpresheaf of the final presheaf generated by `U`. -/
noncomputable abbrev freeCechComplex : ChainComplex (PresheafOfModules.{u} R) ℕ :=
  AlternatingFaceMapComplex.obj (cechNerve U ⋙ yoneda ⋙ PresheafOfModules.free R)

/-- Evaluated at an object `V`, the free Čech complex is the alternating face complex of the free
`R(V)`-modules on `Hom(V, U^{n+1})`. -/
theorem evaluation_freeCechComplex (V : Cᵒᵖ) :
    ((PresheafOfModules.evaluation R V).mapHomologicalComplex _).obj (freeCechComplex U R) =
      AlternatingFaceMapComplex.obj
        ((homCechNerve U V.unop).left ⋙ ModuleCat.free (R.obj V)) :=
  Functor.congr_obj (map_alternatingFaceMapComplex (PresheafOfModules.evaluation R V)) _

/-- **The free Čech complex is exact in positive degrees.** At an object `V` admitting a morphism
to `U` the simplicial module it comes from is contractible; at any other object it vanishes. -/
theorem freeCechComplex_exactAt (n : ℕ) (hn : 0 < n) : (freeCechComplex U R).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff]
  refine ChaoticQCoh.exact_of_evaluation R _ fun V => ?_
  have h : (((PresheafOfModules.evaluation R V).mapHomologicalComplex _).obj
      (freeCechComplex U R)).ExactAt n := by
    rw [evaluation_freeCechComplex]
    rcases isEmpty_or_nonempty (V.unop ⟶ U) with hV | ⟨⟨g₀⟩⟩
    · refine HomologicalComplex.ExactAt.of_isZero ?_
      have : IsEmpty (V.unop ⟶ (cechNerve U).obj (op ⦋n⦌)) :=
        ⟨fun x => hV.false (x ≫ cechπ U n 0)⟩
      refine @ModuleCat.isZero_of_subsingleton _ _ _ ?_
      show Subsingleton ((V.unop ⟶ (cechNerve U).obj (op ⦋n⦌)) →₀ R.obj V)
      infer_instance
    · let ed := (homCechNerveExtraDegeneracy U g₀).map (ModuleCat.free (R.obj V))
      show (AlternatingFaceMapComplex.obj (SimplicialObject.Augmented.drop.obj
        (((SimplicialObject.Augmented.whiskering (Type u) (ModuleCat (R.obj V))).obj
          (ModuleCat.free (R.obj V))).obj (homCechNerve U V.unop)))).ExactAt n
      rw [exactAt_iff_of_quasiIsoAt ed.homotopyEquiv.hom n]
      exact HomologicalComplex.exactAt_single_obj _ _ _ _ (by omega)
  rwa [HomologicalComplex.exactAt_iff] at h

end FreeComplex

/-! ### The Čech complex of a presheaf, and its vanishing for an injective presheaf of modules -/

section Cech

variable {A : Type*} [Category* A] [Preadditive A]

/-- The Čech complex of a presheaf `P` for an object `U` covering the final object:
`P(U) → P(U × U) → P(U × U × U) → ⋯`, with the alternating sums of the restrictions along the
projections omitting one factor. -/
noncomputable abbrev cechComplex (P : Cᵒᵖ ⥤ A) : CochainComplex A ℕ :=
  AlternatingCofaceMapComplex.obj ((cechNerve U).rightOp ⋙ P)

/-- The differential of the Čech complex in degree `n` is the alternating sum of the restrictions
along the faces `U^{n+2} ⟶ U^{n+1}`. -/
theorem cechComplex_d (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplex U P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map ((cechNerve U).map (SimplexCategory.δ i).op).op := by
  simp [cechComplex, AlternatingCofaceMapComplex.obj, CosimplicialObject.δ]

end Cech

section Injective

variable (R : Cᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{u} R)

/-- Maps out of the free module on a representable are sections, additively. -/
noncomputable def freeYonedaAddEquiv (X : C) :
    ((PresheafOfModules.free R).obj (yoneda.obj X) ⟶ M) ≃+ M.obj (op X) where
  toEquiv := PresheafOfModules.freeYonedaEquiv
  map_add' _ _ := rfl

/-- The section attached to a map `ψ` out of `R[Hom(-, X)]` is the image of the generator `𝟙 X`. -/
theorem freeYonedaAddEquiv_apply {X : C}
    (ψ : (PresheafOfModules.free R).obj (yoneda.obj X) ⟶ M) :
    freeYonedaAddEquiv R M X ψ = ψ.app (op X) (ModuleCat.freeMk (𝟙 X)) := rfl

/-- Precomposing with the map of free modules induced by `f : X ⟶ Y` corresponds to restricting
sections along `f`. -/
theorem freeYonedaAddEquiv_free_map_comp {X Y : C} (f : X ⟶ Y)
    (ψ : (PresheafOfModules.free R).obj (yoneda.obj Y) ⟶ M) :
    freeYonedaAddEquiv R M X ((PresheafOfModules.free R).map (yoneda.map f) ≫ ψ) =
      M.presheaf.map f.op (freeYonedaAddEquiv R M Y ψ) := by
  have h := congrArg yonedaEquiv
    ((PresheafOfModules.freeAdjunction R).homEquiv_naturality_left (yoneda.map f) ψ)
  rw [PresheafOfModules.freeAdjunction_homEquiv, PresheafOfModules.freeAdjunction_homEquiv] at h
  exact h.trans (yonedaEquiv_naturality _ _).symm

private theorem ab_sum_apply {P Q : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → (P ⟶ Q)) (x : P) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, AddCommGrpCat.hom_add_apply, ih]

private theorem moduleCat_sum_apply {R : Type*} [Ring R] {P Q : ModuleCat.{u} R} {ι : Type*}
    (s : Finset ι) (f : ι → (P ⟶ Q)) (x : P) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    rfl

/-- Elementwise form of the Čech differential: the alternating sum of the restrictions. -/
private theorem cechComplex_d_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x : P.obj (op ((cechNerve U).obj (op ⦋n⦌)))) :
    (cechComplex U P).d n (n + 1) x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.map ((cechNerve U).map (SimplexCategory.δ i).op).op x := by
  rw [cechComplex_d]
  exact ab_sum_apply (P := P.obj (op ((cechNerve U).obj (op ⦋n⦌))))
    (Q := P.obj (op ((cechNerve U).obj (op ⦋n + 1⦌)))) Finset.univ _ _

/-- Elementwise, the Čech differential in degree zero is the difference of the two restrictions. -/
private theorem cechComplex_d_zero_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (x : P.obj (op ((cechNerve U).obj (op ⦋0⦌)))) :
    (cechComplex U P).d 0 1 x = P.map ((cechNerve U).map (SimplexCategory.δ 0).op).op x -
      P.map ((cechNerve U).map (SimplexCategory.δ 1).op).op x := by
  rw [cechComplex_d_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]
  rfl

/-- Under the identification of maps out of free modules on representables with sections, the
differential of the free Čech complex is the Čech differential. -/
theorem freeYonedaAddEquiv_d_comp (n : ℕ)
    (ψ : (freeCechComplex U R).X n ⟶ M) :
    freeYonedaAddEquiv R M _ ((freeCechComplex U R).d (n + 1) n ≫ ψ) =
      (cechComplex U M.presheaf).d n (n + 1) (freeYonedaAddEquiv R M _ ψ) := by
  rw [AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp, map_sum]
  refine Eq.trans ?_ (cechComplex_d_apply U M.presheaf n _).symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, map_zsmul]
  exact congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z)
    (freeYonedaAddEquiv_free_map_comp R M ((cechNerve U).map (SimplexCategory.δ i).op) ψ)

/-- **The Čech complex of an injective presheaf of modules is exact in positive degrees.** A
cocycle is a map out of the free Čech complex killing the boundaries, which extends, by
injectivity and exactness of the free Čech complex, along the next differential. -/
theorem cechComplex_exactAt_of_injective [Injective M] (n : ℕ) (hn : 0 < n) :
    (cechComplex U M.presheaf).ExactAt n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(cechComplex U M.presheaf).exactAt_iff' m (m + 1) (m + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro x hx
  let φ := (freeYonedaAddEquiv R M _).symm x
  have hφ : (freeCechComplex U R).d (m + 2) (m + 1) ≫ φ = 0 := by
    apply (freeYonedaAddEquiv R M _).injective
    have hx' : freeYonedaAddEquiv R M _ φ = x := (freeYonedaAddEquiv R M _).apply_symm_apply x
    rwa [freeYonedaAddEquiv_d_comp, map_zero, hx']
  have hS := freeCechComplex_exactAt U R (m + 1) (by omega)
  rw [(freeCechComplex U R).exactAt_iff' (m + 2) (m + 1) m (by simp) (by simp)] at hS
  let ψ : (freeCechComplex U R).X m ⟶ M := hS.descToInjective φ hφ
  have hψ : (freeCechComplex U R).d (m + 1) m ≫ ψ = φ := hS.comp_descToInjective φ hφ
  refine ⟨freeYonedaAddEquiv R M _ ψ, ?_⟩
  show (cechComplex U M.presheaf).d m (m + 1) (freeYonedaAddEquiv R M _ ψ) = x
  rw [← freeYonedaAddEquiv_d_comp, hψ]
  exact (freeYonedaAddEquiv R M _).apply_symm_apply x

end Injective

/-! ### Sections over a base ring, and the augmentation by global sections -/

section Site

open Stacks.Cohomology.SiteModules

variable {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* GlobalSectionRing O)

/-- The ring map from the base ring to the sections of the structure sheaf over an object. -/
noncomputable abbrev baseToSections (V : Cᵒᵖ) : A →+* O.obj.obj V :=
  (globalSectionEval O V).comp ρ

/-- The restriction maps of the structure sheaf commute with the maps from the base ring. -/
theorem map_baseToSections {V W : Cᵒᵖ} (f : V ⟶ W) (a : A) :
    O.obj.map f (baseToSections O ρ V a) = baseToSections O ρ W a :=
  (ρ a).2 f

/-- The sections over `V` of a sheaf of `O`-modules, as an `A`-module. -/
noncomputable abbrev sectionsOverBaseObj (M : SheafOfModules.{u} O) (V : Cᵒᵖ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (baseToSections O ρ V)).obj (M.val.obj V)

/-- The restriction maps of a sheaf of `O`-modules are linear over a base ring `A` mapping to the
global sections of `O`. -/
noncomputable def sectionsOverBaseMap (M : SheafOfModules.{u} O) {V W : Cᵒᵖ} (f : V ⟶ W) :
    sectionsOverBaseObj O ρ M V ⟶ sectionsOverBaseObj O ρ M W :=
  ModuleCat.ofHom (X := sectionsOverBaseObj O ρ M V) (Y := sectionsOverBaseObj O ρ M W)
    ({ toFun := fun (x : sectionsOverBaseObj O ρ M V) =>
          (M.val.map f (x : M.val.obj V) : sectionsOverBaseObj O ρ M W)
       map_add' := fun x y => map_add (M.val.map f).hom (x : M.val.obj V) (y : M.val.obj V)
       map_smul' := fun a x =>
        ((M.val.map f).hom.map_smul (baseToSections O ρ V a) (x : M.val.obj V)).trans
          (congrArg (fun r : O.obj.obj W => r • ((M.val.map f).hom (x : M.val.obj V) :
            M.val.obj W)) (map_baseToSections O ρ f a)) } :
      sectionsOverBaseObj O ρ M V →ₗ[A] sectionsOverBaseObj O ρ M W)

/-- The sections of a sheaf of `O`-modules, read as modules over a base ring `A` mapping to the
global sections of `O`. -/
noncomputable def sectionsOverBase (M : SheafOfModules.{u} O) : Cᵒᵖ ⥤ ModuleCat.{u} A where
  obj V := sectionsOverBaseObj O ρ M V
  map f := sectionsOverBaseMap O ρ M f
  map_id V := by
    ext x
    exact congrArg (fun g => (ConcreteCategory.hom g : _ → _) (x : M.val.obj V)) (M.val.map_id V)
  map_comp f g := by
    ext x
    exact M.val.map_comp_apply f g (x : M.val.obj _)

/-- `sectionsOverBase` as a functor of the module. -/
noncomputable def sectionsOverBaseFunctor : SheafOfModules.{u} O ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} A) where
  obj M := sectionsOverBase O ρ M
  map {M N} φ :=
    { app V := ModuleCat.ofHom (X := sectionsOverBaseObj O ρ M V)
        (Y := sectionsOverBaseObj O ρ N V)
        ({ toFun := fun (x : sectionsOverBaseObj O ρ M V) =>
              (φ.val.app V (x : M.val.obj V) : sectionsOverBaseObj O ρ N V)
           map_add' := fun x y => map_add (φ.val.app V).hom (x : M.val.obj V) (y : M.val.obj V)
           map_smul' := fun a x => (φ.val.app V).hom.map_smul _ (x : M.val.obj V) } :
          sectionsOverBaseObj O ρ M V →ₗ[A] sectionsOverBaseObj O ρ N V)
      naturality V W f := by
        ext x
        exact PresheafOfModules.naturality_apply φ.val f (x : M.val.obj V) }
  map_id M := rfl
  map_comp f g := rfl

/-- Taking sections over the base ring is additive in the module. -/
instance : (sectionsOverBaseFunctor O ρ).Additive where
  map_add := by
    intros
    ext
    rfl

/-- The Čech complex of a sheaf of `O`-modules for `U`, as a complex of `A`-modules. -/
noncomputable abbrev cechComplexOverBase (M : SheafOfModules.{u} O) :
    CochainComplex (ModuleCat.{u} A) ℕ :=
  cechComplex U (sectionsOverBase O ρ M)

/-- The differential of the Čech complex over the base ring is, elementwise, the Čech differential
of the underlying abelian presheaf. -/
theorem cechComplexOverBase_d_apply (M : SheafOfModules.{u} O) (n : ℕ)
    (x : (cechComplexOverBase U O ρ M).X n) :
    (cechComplexOverBase U O ρ M).d n (n + 1) x =
      (cechComplex U M.val.presheaf).d n (n + 1) (x : M.val.obj _) := by
  rw [cechComplex_d]
  refine (moduleCat_sum_apply (P := (sectionsOverBase O ρ M).obj (op ((cechNerve U).obj (op ⦋n⦌))))
    (Q := (sectionsOverBase O ρ M).obj (op ((cechNerve U).obj (op ⦋n + 1⦌)))) Finset.univ _ _).trans
    (Eq.trans ?_ (cechComplex_d_apply U M.val.presheaf n _).symm)
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (LinearMap.smul_apply _ _ _).trans rfl

/-- **The Čech complex over the base ring of an injective sheaf of modules is exact in positive
degrees**, when sheafification of abelian presheaves is available, so that an injective sheaf of
modules is injective as a presheaf of modules. -/
theorem cechComplexOverBase_exactAt_of_injective [HasSheafify J Ab.{u}]
    [J.WEqualsLocallyBijective Ab.{u}] (M : SheafOfModules.{u} O) [Injective M] (n : ℕ)
    (hn : 0 < n) : (cechComplexOverBase U O ρ M).ExactAt n := by
  have : Injective ((SheafOfModules.forget O).obj M) :=
    ModuleSheafCohomology.injective_forget_obj O M
  have h := cechComplex_exactAt_of_injective U O.obj ((SheafOfModules.forget O).obj M) n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at h
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := h x ((cechComplexOverBase_d_apply U O ρ M (m + 1) x).symm.trans hx)
  exact ⟨y, (cechComplexOverBase_d_apply U O ρ M m y).trans hy⟩

/-! ### The augmentation by global sections, over the base ring -/

/-- The Čech complex as a functor of the presheaf. -/
noncomputable abbrev cechFunctor (A' : Type*) [Category* A'] [Preadditive A'] :
    (Cᵒᵖ ⥤ A') ⥤ CochainComplex A' ℕ :=
  (Functor.whiskeringLeft _ _ A').obj (cechNerve U).rightOp ⋙ alternatingCofaceMapComplex A'

/-- Global sections of a sheaf of `O`-modules, as `A`-modules. -/
noncomputable abbrev globalSectionsOverBase :
    SheafOfModules.{u} O ⥤ ModuleCat.{max u' u} A :=
  globalSectionsFunctor.{u', u, u, u} O ⋙ ModuleCat.restrictScalars ρ

/-- The Čech complex over the base ring, in the universe of global sections. -/
noncomputable abbrev cechFunctorOverBase :
    SheafOfModules.{u} O ⥤ CochainComplex (ModuleCat.{max u u'} A) ℕ :=
  sectionsOverBaseFunctor O ρ ⋙ cechFunctor U (ModuleCat.{u} A) ⋙
    (ModuleCat.uliftFunctor.{u'} A).mapHomologicalComplex _

/-- The augmentation of the Čech complex by global sections, in degree zero. -/
noncomputable def cechAugmentation (M : SheafOfModules.{u} O) :
    (globalSectionsOverBase O ρ).obj M ⟶ ((cechFunctorOverBase U O ρ).obj M).X 0 :=
  ModuleCat.ofHom (X := (globalSectionsOverBase O ρ).obj M)
    (Y := ((cechFunctorOverBase U O ρ).obj M).X 0)
    { toFun := fun s => ULift.up (s.eval (op ((cechNerve U).obj (op ⦋0⦌))) :
        sectionsOverBaseObj O ρ M (op ((cechNerve U).obj (op ⦋0⦌))))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The augmentation sends a global section to its restriction to `U`. -/
theorem cechAugmentation_apply (M : SheafOfModules.{u} O) (s : M.sections) :
    cechAugmentation U O ρ M s = ULift.up (s.eval (op ((cechNerve U).obj (op ⦋0⦌)))) := rfl

/-- The differential of `cechFunctorOverBase` is, elementwise, the Čech differential of the
underlying abelian presheaf. -/
theorem cechFunctorOverBase_d_apply (M : SheafOfModules.{u} O) (n : ℕ)
    (x : M.val.obj (op ((cechNerve U).obj (op ⦋n⦌)))) :
    ((cechFunctorOverBase U O ρ).obj M).d n (n + 1) (ULift.up x) =
      ULift.up ((cechComplex U M.val.presheaf).d n (n + 1) x) :=
  congrArg ULift.up (cechComplexOverBase_d_apply U O ρ M n x)

/-- The augmentation is natural in the module. -/
theorem cechAugmentation_naturality {M N : SheafOfModules.{u} O} (φ : M ⟶ N) :
    (globalSectionsOverBase O ρ).map φ ≫ cechAugmentation U O ρ N =
      cechAugmentation U O ρ M ≫ ((cechFunctorOverBase U O ρ).map φ).f 0 := rfl

/-- The Čech differential kills the restriction of a global section. -/
theorem cechComplex_d_zero_eval (M : SheafOfModules.{u} O) (s : M.sections) :
    (cechComplex U M.val.presheaf).d 0 1 (s.eval (op ((cechNerve U).obj (op ⦋0⦌)))) = 0 := by
  refine (cechComplex_d_zero_apply U M.val.presheaf _).trans ?_
  exact sub_eq_zero.2 ((M.val.sections_property s _).trans (M.val.sections_property s _).symm)

/-- The augmentation followed by the first Čech differential is zero. -/
theorem cechAugmentation_comp_d (M : SheafOfModules.{u} O) :
    cechAugmentation U O ρ M ≫ ((cechFunctorOverBase U O ρ).obj M).d 0 1 = 0 := by
  ext s
  exact (cechFunctorOverBase_d_apply U O ρ M 0 _).trans
    (congrArg ULift.up (cechComplex_d_zero_eval U O M s))

/-! ### Degree zero: global sections -/

variable {U}

/-- The term of degree zero of the Čech nerve covers the final object as soon as `U` does. -/
theorem coversTop_cechNerve_zero (hU : J.CoversTop fun _ : Unit => U) :
    J.CoversTop fun _ : Unit => (cechNerve U).obj (op ⦋0⦌) := fun X =>
  J.superset_covering (by
    rintro Y g ⟨i, ⟨b⟩⟩
    exact ⟨(), ⟨b ≫ Pi.lift fun _ => 𝟙 U⟩⟩) (hU X)

/-- Two morphisms into the degree-zero term of the Čech nerve agreeing after its projection to
`U` are equal. -/
theorem cechNerve_zero_hom_ext {W : C} {f g : W ⟶ (cechNerve U).obj (op ⦋0⦌)}
    (h : f ≫ cechπ U 0 0 = g ≫ cechπ U 0 0) : f = g :=
  cechNerve_hom_ext U fun i => by fin_cases i; exact h

/-- A degree-zero cochain with vanishing Čech differential is compatible on all pairs of maps
into the degree-zero term. -/
theorem map_eq_of_cechComplex_d_zero (M : SheafOfModules.{u} O)
    (x : M.val.obj (op ((cechNerve U).obj (op ⦋0⦌))))
    (hx : (cechComplex U M.val.presheaf).d 0 1 x = 0) {Z : C}
    (f g : Z ⟶ (cechNerve U).obj (op ⦋0⦌)) :
    M.val.map f.op x = M.val.map g.op x := by
  let h : Z ⟶ (cechNerve U).obj (op ⦋1⦌) :=
    Pi.lift (Fin.cases (f ≫ cechπ U 0 0) fun _ => g ≫ cechπ U 0 0)
  have h₀ : h ≫ (cechNerve U).map (SimplexCategory.δ (0 : Fin 2)).op = g := by
    refine cechNerve_zero_hom_ext ?_
    rw [Category.assoc, cechNerve_map_cechπ]
    exact Pi.lift_comp_π _ _
  have h₁ : h ≫ (cechNerve U).map (SimplexCategory.δ (1 : Fin 2)).op = f := by
    refine cechNerve_zero_hom_ext ?_
    rw [Category.assoc, cechNerve_map_cechπ]
    exact Pi.lift_comp_π _ _
  replace hx := (cechComplex_d_zero_apply U M.val.presheaf x).symm.trans hx
  rw [← h₀, ← h₁, op_comp, op_comp, M.val.map_comp_apply, M.val.map_comp_apply]
  exact congrArg (M.val.map h.op) (sub_eq_zero.mp hx).symm

/-- **Degree-zero Čech cohomology for an object covering the final object is the module of
global sections**: restriction to the degree-zero term is injective, and its image is the kernel
of the first Čech differential. -/
theorem existsUnique_sections_eval_of_cechComplex_d_zero (hU : J.CoversTop fun _ : Unit => U)
    (M : SheafOfModules.{u} O) (x : M.val.obj (op ((cechNerve U).obj (op ⦋0⦌))))
    (hx : (cechComplex U M.val.presheaf).d 0 1 x = 0) :
    ∃! s : M.sections, s.eval (op ((cechNerve U).obj (op ⦋0⦌))) = x := by
  obtain ⟨s, hs, hu⟩ := Presheaf.FamilyOfElementsOnObjects.IsCompatible.existsUnique_section
    (x := fun _ : Unit => (x : (M.val.presheaf ⋙ forget Ab).obj (op ((cechNerve U).obj (op ⦋0⦌)))))
    (fun Z _ _ f g => map_eq_of_cechComplex_d_zero O M x hx f g) (coversTop_cechNerve_zero hU)
    (Presheaf.isSheaf_comp_of_isSheaf J M.val.presheaf (forget Ab.{u}) M.isSheaf)
  exact ⟨s, hs (), fun t ht => hu t fun _ => ht⟩

/-- For `U` covering the final object, the augmentation by global sections is a monomorphism. -/
theorem mono_cechAugmentation (hU : J.CoversTop fun _ : Unit => U) (M : SheafOfModules.{u} O) :
    Mono (cechAugmentation U O ρ M) := by
  rw [ModuleCat.mono_iff_injective]
  intro s t hst
  obtain ⟨r, -, hr⟩ := existsUnique_sections_eval_of_cechComplex_d_zero O hU M
    (s.eval (op ((cechNerve U).obj (op ⦋0⦌)))) (cechComplex_d_zero_eval U O M s)
  exact (hr s rfl).trans (hr t (congrArg ULift.down hst).symm).symm

/-- For `U` covering the final object, global sections, the degree-zero Čech cochains and the
degree-one Čech cochains form an exact sequence. -/
theorem exact_cechAugmentation (hU : J.CoversTop fun _ : Unit => U) (M : SheafOfModules.{u} O) :
    (ShortComplex.mk (cechAugmentation U O ρ M) (((cechFunctorOverBase U O ρ).obj M).d 0 1)
      (cechAugmentation_comp_d U O ρ M)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : (cechComplex U M.val.presheaf).d 0 1 x.down = 0 :=
    congrArg ULift.down ((cechFunctorOverBase_d_apply U O ρ M 0 x.down).symm.trans hx)
  obtain ⟨s, hs, -⟩ := existsUnique_sections_eval_of_cechComplex_d_zero O hU M x.down hx'
  exact ⟨s, congrArg ULift.up hs⟩

/-- **The augmentation identifies global sections with the degree-zero Čech cocycles**, for an
object covering the final object. -/
theorem isIso_kernelLift_cechAugmentation (hU : J.CoversTop fun _ : Unit => U)
    (M : SheafOfModules.{u} O) :
    IsIso (kernel.lift (((cechFunctorOverBase U O ρ).obj M).d 0 1) (cechAugmentation U O ρ M)
      (cechAugmentation_comp_d U O ρ M)) := by
  have := mono_cechAugmentation O ρ hU M
  have : Mono (kernel.lift (((cechFunctorOverBase U O ρ).obj M).d 0 1) (cechAugmentation U O ρ M)
      (cechAugmentation_comp_d U O ρ M)) := mono_of_mono_fac (kernel.lift_ι _ _ _)
  have : Epi (kernel.lift (((cechFunctorOverBase U O ρ).obj M).d 0 1) (cechAugmentation U O ρ M)
      (cechAugmentation_comp_d U O ρ M)) :=
    (ShortComplex.mk _ _ (cechAugmentation_comp_d U O ρ M)).exact_iff_epi_kernel_lift.1
      (exact_cechAugmentation O ρ hU M)
  exact isIso_of_mono_of_epi _

end Site

end Stacks.CechTop

end
