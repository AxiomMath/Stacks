module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientMateLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistCoefficient
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Comparisons of coefficient functors: composites, isomorphisms, and `Hom` out of a finitely
presented module

For a continuous functor of sites and left adjoints of direct image with coefficients in `A` and
`B`, every change of coefficients `Γ : A ⥤ B` preserving sheaves has a comparison
`L(Γ c) ⟶ Γ(L c)` (`Stacks.EtaleCohomology.sheafComposeCoefficientMate`).  This file shows:

* the comparison of a composite `Γ ⋙ Γ'` is the comparison of `Γ'` followed by `Γ'` of the
  comparison of `Γ`;
* invertibility of the comparison transfers along isomorphisms of coefficient functors, and
  descends along a second change of coefficients whose sheaf version reflects isomorphisms and
  whose comparison is invertible;
* for a finitely presented `R`-module `D`, the comparison of `N ↦ Hom_R(D, N)`, valued in abelian
  groups, is invertible as soon as that of restriction of scalars `R → ℤ` is and the left adjoint
  preserves finite limits: `Hom_R(D, -)` is an equalizer of finite products of restriction of
  scalars.

## Main results

* `Stacks.EtaleCohomology.coefficientMate_comp_app`: the comparison of a composite of coefficient
  functors.
* `Stacks.EtaleCohomology.isIso_sheafComposeCoefficientMate_of_iso`: invertibility of the
  comparison transfers along isomorphisms of coefficient functors.
* `Stacks.EtaleCohomology.isIso_coefficientMate_of_comp`: invertibility of the comparison descends
  along a second change of coefficients.
* `Stacks.EtaleCohomology.isIso_coefficientMate_sourceHomFunctor`: the comparison of `Hom_R(D, -)`
  is invertible for a finitely presented `D`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v

namespace Stacks.EtaleCohomology

section General

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  {A B B' : Type*} [Category* A] [Category* B] [Category* B']
  {LA : Sheaf J A ⥤ Sheaf K A} {LB : Sheaf J B ⥤ Sheaf K B} {LB' : Sheaf J B' ⥤ Sheaf K B'}
  (adjA : LA ⊣ uf.sheafPushforwardContinuous A J K)
  (adjB : LB ⊣ uf.sheafPushforwardContinuous B J K)
  (adjB' : LB' ⊣ uf.sheafPushforwardContinuous B' J K)

/-- **The comparison of a composite of coefficient functors** is the comparison of the second
followed by the second applied to the comparison of the first. -/
theorem coefficientMate_comp_app (Gf : A ⥤ B) (Gf' : B ⥤ B') [J.HasSheafCompose Gf]
    [K.HasSheafCompose Gf] [J.HasSheafCompose Gf'] [K.HasSheafCompose Gf']
    [J.HasSheafCompose (Gf ⋙ Gf')] [K.HasSheafCompose (Gf ⋙ Gf')] (c : Sheaf J A) :
    (sheafComposeCoefficientMate uf J K adjA adjB' (Gf ⋙ Gf')).app c =
      (sheafComposeCoefficientMate uf J K adjB adjB' Gf').app ((sheafCompose J Gf).obj c) ≫
        (sheafCompose K Gf').map
          ((sheafComposeCoefficientMate uf J K adjA adjB Gf).app c) := by
  let rhs : LB'.obj ((sheafCompose J (Gf ⋙ Gf')).obj c) ⟶
      (sheafCompose K (Gf ⋙ Gf')).obj (LA.obj c) :=
    (sheafComposeCoefficientMate uf J K adjB adjB' Gf').app ((sheafCompose J Gf).obj c) ≫
      (sheafCompose K Gf').map ((sheafComposeCoefficientMate uf J K adjA adjB Gf).app c)
  change _ = rhs
  apply (adjB'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← coefficientMate_unit]
  have h₁ := coefficientMate_unit uf J K adjA adjB Gf c
  have h₂ := coefficientMate_unit uf J K adjB adjB' Gf' ((sheafCompose J Gf).obj c)
  have h₃ : (sheafCompose J (Gf ⋙ Gf')).map (adjA.unit.app c) =
      (sheafCompose J Gf').map (adjB.unit.app ((sheafCompose J Gf).obj c)) ≫
        (uf.sheafPushforwardContinuous B' J K).map ((sheafCompose K Gf').map
          ((sheafComposeCoefficientMate uf J K adjA adjB Gf).app c)) :=
    (congrArg (sheafCompose J Gf').map h₁).trans ((sheafCompose J Gf').map_comp _ _)
  rw [h₃, h₂]
  exact (Category.assoc _ _ _).trans
    (congrArg (adjB'.unit.app _ ≫ ·) ((uf.sheafPushforwardContinuous B' J K).map_comp _ _).symm)

/-- **Invertibility of the comparison transfers along an isomorphism of coefficient
functors.** -/
theorem isIso_sheafComposeCoefficientMate_of_iso {Gf Gf' : A ⥤ B} [J.HasSheafCompose Gf]
    [K.HasSheafCompose Gf] [J.HasSheafCompose Gf'] [K.HasSheafCompose Gf'] (e : Gf ≅ Gf')
    (h : IsIso (sheafComposeCoefficientMate uf J K adjA adjB Gf)) :
    IsIso (sheafComposeCoefficientMate uf J K adjA adjB Gf') := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  have hn := sheafComposeCoefficientMate_naturality uf J K adjA adjB e.hom c
  have hi : IsIso ((sheafCompose_map J e.hom).app c) :=
    ⟨(sheafCompose_map J e.inv).app c, by
      rw [← NatTrans.comp_app, ← sheafCompose_comp, e.hom_inv_id, sheafCompose_id]; rfl, by
      rw [← NatTrans.comp_app, ← sheafCompose_comp, e.inv_hom_id, sheafCompose_id]; rfl⟩
  have hi' : IsIso ((sheafCompose_map K e.hom).app (LA.obj c)) :=
    ⟨(sheafCompose_map K e.inv).app (LA.obj c), by
      rw [← NatTrans.comp_app, ← sheafCompose_comp, e.hom_inv_id, sheafCompose_id]; rfl, by
      rw [← NatTrans.comp_app, ← sheafCompose_comp, e.inv_hom_id, sheafCompose_id]; rfl⟩
  have : IsIso (LB.map ((sheafCompose_map J e.hom).app c) ≫
      (sheafComposeCoefficientMate uf J K adjA adjB Gf').app c) := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_left (LB.map ((sheafCompose_map J e.hom).app c)) _

/-- **Invertibility of the comparison descends along a second change of coefficients** whose
comparison is invertible and whose sheaf version reflects isomorphisms. -/
theorem isIso_coefficientMate_of_comp (Gf : A ⥤ B) (Gf' : B ⥤ B') [J.HasSheafCompose Gf]
    [K.HasSheafCompose Gf] [J.HasSheafCompose Gf'] [K.HasSheafCompose Gf']
    [J.HasSheafCompose (Gf ⋙ Gf')] [K.HasSheafCompose (Gf ⋙ Gf')]
    [(sheafCompose K Gf').ReflectsIsomorphisms]
    (h : IsIso (sheafComposeCoefficientMate uf J K adjA adjB' (Gf ⋙ Gf')))
    (h' : IsIso (sheafComposeCoefficientMate uf J K adjB adjB' Gf')) :
    IsIso (sheafComposeCoefficientMate uf J K adjA adjB Gf) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  have h₁ : IsIso ((sheafComposeCoefficientMate uf J K adjA adjB' (Gf ⋙ Gf')).app c) :=
    inferInstance
  rw [coefficientMate_comp_app uf J K adjA adjB adjB'] at h₁
  have : IsIso ((sheafCompose K Gf').map
      ((sheafComposeCoefficientMate uf J K adjA adjB Gf).app c)) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((sheafComposeCoefficientMate uf J K adjB adjB' Gf').app _) _ inferInstance h₁
  exact isIso_of_reflects_iso _ (sheafCompose K Gf')

end General

section FinitePresentation

variable {C D : Type*} [Category* C] [Category* D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  (T : Type) [CommRing T] (A : Type) [Ring A] [Algebra T A]
  {LA : Sheaf J (ModuleCat.{v} A) ⥤ Sheaf K (ModuleCat.{v} A)}
  {LB : Sheaf J (ModuleCat.{v} T) ⥤ Sheaf K (ModuleCat.{v} T)}
  (adjA : LA ⊣ uf.sheafPushforwardContinuous (ModuleCat.{v} A) J K)
  (adjB : LB ⊣ uf.sheafPushforwardContinuous (ModuleCat.{v} T) J K)

/-- `Hom_A(Aⁿ, -)`, with `T` acting through `Aⁿ`. -/
abbrev freeHomFunctor (n : ℕ) : ModuleCat.{v} A ⥤ ModuleCat.{v} T :=
  sourceHomFunctor A T (ULift.{v} (Fin n → A))

/-- Restriction of scalars along `T → A`. -/
abbrev algebraRes : ModuleCat.{v} A ⥤ ModuleCat.{v} T :=
  ModuleCat.restrictScalars.{v} (algebraMap T A)

/-- The `j`-th basis vector of `Aⁿ`. -/
def freeBasisVec {n : ℕ} (j : Fin n) : ULift.{v} (Fin n → A) := ⟨Pi.single j 1⟩

/-- On a basis vector of `Aⁿ`, the action of `c : T` agrees with right multiplication by
`algebraMap T A c`. -/
lemma algebraMap_smul_freeBasisVec_comm {n : ℕ} (c : T) (j : Fin n) :
    (c • freeBasisVec A j : ULift.{v} (Fin n → A)) =
      (MulOpposite.op (algebraMap T A c) • freeBasisVec A j : ULift.{v} (Fin n → A)) := by
  ext i
  change c • (Pi.single j 1 : Fin n → A) i = (Pi.single j 1 : Fin n → A) i * algebraMap T A c
  rw [Algebra.smul_def, Algebra.commutes]

/-- Evaluation at the `j`-th basis vector, `Hom_A(Aⁿ, N) ⟶ N`. -/
def freeHomEval (n : ℕ) (j : Fin n) : freeHomFunctor T A n ⟶ algebraRes T A where
  app N := ModuleCat.ofHom (X := SourceHom A T (ULift.{v} (Fin n → A)) N)
      (Y := (algebraRes T A).obj N)
    { toFun := fun φ => φ.toLinearMap (freeBasisVec A j)
      map_add' := fun _ _ => rfl
      map_smul' := fun c φ => by
        change φ.toLinearMap (c • freeBasisVec A j) =
          algebraMap T A c • φ.toLinearMap (freeBasisVec A j)
        rw [← _root_.map_smul, algebraMap_smul] }
  naturality _ _ _ := rfl

/-- The diagram, over the discrete category on `Fin n`, constant at restriction of scalars. -/
abbrev freeHomDiagram (n : ℕ) : Discrete (Fin n) ⥤ (ModuleCat.{v} A ⥤ ModuleCat.{v} T) :=
  Discrete.functor fun _ => algebraRes T A

/-- Evaluation at the basis vectors, a cone over `freeHomDiagram`. -/
def freeHomCone (n : ℕ) : (Functor.const _).obj (freeHomFunctor T A n) ⟶ freeHomDiagram T A n :=
  Discrete.natTrans fun j => freeHomEval T A n j.as

omit [CommRing T] [Algebra T A] in
/-- A map out of `Aⁿ` is the sum of its values on the basis vectors weighted by the
coordinates. -/
lemma freeHom_apply_eq_sum {n : ℕ} {N : ModuleCat.{v} A}
    (φ : SourceHom A T (ULift.{v} (Fin n → A)) N) (d : ULift.{v} (Fin n → A)) :
    φ.toLinearMap d = ∑ j, d.down j • φ.toLinearMap (freeBasisVec A j) := by
  have hd : d = ∑ j, d.down j • freeBasisVec A j := by
    apply (ULift.moduleEquiv (R := A) (M := Fin n → A)).injective
    rw [_root_.map_sum]
    ext i
    simp [freeBasisVec, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hd]
  simp only [_root_.map_sum, _root_.map_smul]

/-- An element of a restriction of scalars along `T → A`, read in the module itself. -/
def algebraResElt {N : ModuleCat.{v} A} (x : (algebraRes.{v} T A).obj N) : N := x

/-- `algebraResElt` is additive. -/
lemma algebraResElt_add {N : ModuleCat.{v} A} (x y : (algebraRes.{v} T A).obj N) :
    algebraResElt T A (x + y) = algebraResElt T A x + algebraResElt T A y := rfl

/-- `algebraResElt` turns the action of `c : T` into that of `algebraMap T A c`. -/
lemma algebraResElt_smul {N : ModuleCat.{v} A} (c : T) (x : (algebraRes.{v} T A).obj N) :
    algebraResElt T A (c • x) = algebraMap T A c • algebraResElt T A x := rfl

/-- **`Hom_A(Aⁿ, N)` is the product of `n` copies of `N`.** -/
def isLimitFreeHomCone (n : ℕ) (N : ModuleCat.{v} A) :
    IsLimit (((evaluation _ _).obj N).mapCone (Cone.mk _ (freeHomCone T A n))) where
  lift s := ModuleCat.ofHom (X := s.pt) (Y := SourceHom A T (ULift.{v} (Fin n → A)) N)
    { toFun := fun x => SourceHom.ofLinearMap
        ((Fintype.linearCombination A (fun j => algebraResElt T A ((s.π.app ⟨j⟩).hom x))) ∘ₗ
          (ULift.moduleEquiv : ULift.{v} (Fin n → A) ≃ₗ[A] (Fin n → A)).toLinearMap)
      map_add' := fun x y => SourceHom.ext fun d => by
        change ∑ j, d.down j • algebraResElt T A ((s.π.app ⟨j⟩).hom (x + y)) =
          ∑ j, d.down j • algebraResElt T A ((s.π.app ⟨j⟩).hom x) +
            ∑ j, d.down j • algebraResElt T A ((s.π.app ⟨j⟩).hom y)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [_root_.map_add, algebraResElt_add, smul_add]
      map_smul' := fun c x => SourceHom.ext fun d => by
        change ∑ j, d.down j • algebraResElt T A ((s.π.app ⟨j⟩).hom (c • x)) =
          ∑ j, (c • d).down j • algebraResElt T A ((s.π.app ⟨j⟩).hom x)
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [_root_.map_smul, algebraResElt_smul]
        change d.down j • (algebraMap T A c • algebraResElt T A ((s.π.app ⟨j⟩).hom x)) =
          (c • d.down j) • algebraResElt T A ((s.π.app ⟨j⟩).hom x)
        rw [smul_smul, Algebra.smul_def, Algebra.commutes] }
  fac s j := by
    obtain ⟨j⟩ := j
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ∑ i, (freeBasisVec.{v} A j).down i • algebraResElt T A ((s.π.app ⟨i⟩).hom x) =
      (s.π.app ⟨j⟩).hom x
    rw [Finset.sum_eq_single j]
    · simp only [freeBasisVec, Pi.single_eq_same]
      exact one_smul A _
    · intro i _ hi
      simp [freeBasisVec, hi]
    · simp
  uniq s m hm := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => SourceHom.ext fun d => ?_)
    refine (freeHom_apply_eq_sum T A _ d).trans ?_
    change _ = ∑ j, d.down j • algebraResElt T A ((s.π.app ⟨j⟩).hom x)
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (d.down j • ·) (congrArg (fun f => ModuleCat.Hom.hom f x) (hm ⟨j⟩))

variable [PreservesFiniteLimits LB]
  [J.HasSheafCompose (algebraRes.{v} T A)] [K.HasSheafCompose (algebraRes.{v} T A)]

/-- **The comparison of `Hom_A(Aⁿ, -)` is invertible** when that of restriction of scalars is. -/
theorem isIso_coefficientMate_freeHomFunctor (n : ℕ)
    [J.HasSheafCompose (freeHomFunctor.{v} T A n)] [K.HasSheafCompose (freeHomFunctor.{v} T A n)]
    (hres : IsIso (sheafComposeCoefficientMate uf J K adjA adjB (algebraRes.{v} T A))) :
    IsIso (sheafComposeCoefficientMate uf J K adjA adjB (freeHomFunctor.{v} T A n)) := by
  have : ∀ i, J.HasSheafCompose ((freeHomDiagram.{v} T A n).obj i) :=
    fun _ => inferInstanceAs (J.HasSheafCompose (algebraRes.{v} T A))
  have : ∀ i, K.HasSheafCompose ((freeHomDiagram.{v} T A n).obj i) :=
    fun _ => inferInstanceAs (K.HasSheafCompose (algebraRes.{v} T A))
  exact isIso_coefficientMate_of_isLimit uf J K adjA adjB (freeHomDiagram.{v} T A n) _
    (freeHomCone.{v} T A n) (isLimitFreeHomCone.{v} T A n) fun _ => hres

section Presentation

variable {D' : Type v} [AddCommGroup D'] [Module A D'] [Module T D'] [IsScalarTower T A D']
  [SMulCommClass T A D']

variable {n m : ℕ} (f : (Fin n → A) →ₗ[A] D') (g : (Fin m → A) →ₗ[A] (Fin n → A))

/-- The presentation `Aⁿ ⟶ D'`, on `ULift`. -/
def presentationTop : ULift.{v} (Fin n → A) →ₗ[A] D' :=
  f ∘ₗ (ULift.moduleEquiv : ULift.{v} (Fin n → A) ≃ₗ[A] (Fin n → A)).toLinearMap

/-- The relations `Aᵐ ⟶ Aⁿ`, on `ULift`. -/
def presentationRel : ULift.{v} (Fin m → A) →ₗ[A] ULift.{v} (Fin n → A) :=
  (ULift.moduleEquiv : ULift.{v} (Fin n → A) ≃ₗ[A] (Fin n → A)).symm.toLinearMap ∘ₗ g ∘ₗ
    (ULift.moduleEquiv : ULift.{v} (Fin m → A) ≃ₗ[A] (Fin m → A)).toLinearMap

/-- The relation map `Hom_A(Aⁿ, -) ⟶ Hom_A(Aᵐ, -)`. -/
abbrev presentationRelMap : freeHomFunctor T A n ⟶ freeHomFunctor T A m :=
  sourceHomFunctorMap A T (presentationRel.{v} A g) (LinearMap.map_smul_of_tower _)

/-- The inclusion `Hom_A(D', -) ⟶ Hom_A(Aⁿ, -)`. -/
abbrev presentationIncl : sourceHomFunctor A T D' ⟶ freeHomFunctor T A n :=
  sourceHomFunctorMap A T (presentationTop.{v} A f) (LinearMap.map_smul_of_tower _)

variable (hfg : Function.Exact g f) (hf : Function.Surjective f)

include hfg in
/-- The inclusion `Hom_A(D', -) ⟶ Hom_A(Aⁿ, -)` followed by the relation map is zero. -/
lemma presentationIncl_comp_relMap :
    presentationIncl.{v} T A f ≫ presentationRelMap.{v} T A g =
      presentationIncl.{v} T A f ≫ 0 := by
  refine NatTrans.ext (funext fun N => ModuleCat.hom_ext (LinearMap.ext fun φ =>
    SourceHom.ext fun d => ?_))
  change φ.toLinearMap (f (g d.down)) = 0
  rw [hfg.apply_apply_eq_zero, _root_.map_zero]

/-- `Hom_A(D', -)` as the equalizer of the relation map and `0`. -/
def presentationFork :
    (Functor.const WalkingParallelPair).obj (sourceHomFunctor A T D') ⟶
      parallelPair (presentationRelMap.{v} T A g) 0 :=
  (Fork.ofι (presentationIncl.{v} T A f) (presentationIncl_comp_relMap T A f g hfg)).π

/-- The presentation `Aⁿ ⟶ D'` is surjective when `f` is. -/
lemma presentationTop_surjective (hf : Function.Surjective f) :
    Function.Surjective (presentationTop.{v} A f) :=
  hf.comp (ULift.moduleEquiv : ULift.{v} (Fin n → A) ≃ₗ[A] (Fin n → A)).surjective

include hf in
/-- Maps out of `D'` are determined on `Aⁿ`. -/
lemma presentationTop_ext {N : Type v} [AddCommGroup N] [Module A N] {ψ₁ ψ₂ : D' →ₗ[A] N}
    (h : ψ₁ ∘ₗ presentationTop.{v} A f = ψ₂ ∘ₗ presentationTop.{v} A f) : ψ₁ = ψ₂ := by
  ext d
  obtain ⟨x, rfl⟩ := presentationTop_surjective A f hf d
  exact LinearMap.congr_fun h x

include hfg in
/-- A map `Aⁿ → N` vanishing on the relations vanishes on the kernel of the presentation. -/
lemma ker_presentationTop_le {N : Type v} [AddCommGroup N] [Module A N]
    (φ : ULift.{v} (Fin n → A) →ₗ[A] N) (hφ : φ ∘ₗ presentationRel.{v} A g = 0) :
    LinearMap.ker (presentationTop.{v} A f) ≤ LinearMap.ker φ := by
  intro x hx
  obtain ⟨y, hy⟩ := (hfg x.down).1 hx
  have : presentationRel.{v} A g ⟨y⟩ = x := by
    ext i
    exact congrFun hy i
  rw [LinearMap.mem_ker, ← this]
  exact LinearMap.congr_fun hφ ⟨y⟩

include hfg hf in
/-- The factorization through `D'` of a map `Aⁿ → N` killing the relations. -/
def presentationFactor {N : Type v} [AddCommGroup N] [Module A N]
    (φ : ULift.{v} (Fin n → A) →ₗ[A] N) (hφ : φ ∘ₗ presentationRel.{v} A g = 0) :
    D' →ₗ[A] N :=
  (LinearMap.ker (presentationTop.{v} A f)).liftQ φ
      (ker_presentationTop_le A f g hfg φ hφ) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _
      (presentationTop_surjective A f hf)).symm.toLinearMap

include hfg hf in
/-- The factorization through `D'` of a map `Aⁿ → N`, composed with the presentation, is that
map. -/
lemma presentationFactor_comp {N : Type v} [AddCommGroup N] [Module A N]
    (φ : ULift.{v} (Fin n → A) →ₗ[A] N) (hφ : φ ∘ₗ presentationRel.{v} A g = 0) :
    presentationFactor A f g hfg hf φ hφ ∘ₗ presentationTop.{v} A f = φ := by
  refine LinearMap.ext fun x => ?_
  simp only [presentationFactor, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show (LinearMap.quotKerEquivOfSurjective _ (presentationTop_surjective A f hf)).symm
    (presentationTop.{v} A f x) = Submodule.Quotient.mk x from (LinearEquiv.symm_apply_eq _).2 rfl]
  exact Submodule.liftQ_apply _ _ _

include hfg hf in
/-- The factorization through `D'` of a sum of maps is the sum of their factorizations. -/
lemma presentationFactor_eq_add {N : Type v} [AddCommGroup N] [Module A N]
    {φ ψ₁ ψ₂ : ULift.{v} (Fin n → A) →ₗ[A] N} (hφ : φ ∘ₗ presentationRel.{v} A g = 0)
    (h₁ : ψ₁ ∘ₗ presentationRel.{v} A g = 0) (h₂ : ψ₂ ∘ₗ presentationRel.{v} A g = 0)
    (h : φ = ψ₁ + ψ₂) :
    presentationFactor A f g hfg hf φ hφ =
      presentationFactor A f g hfg hf ψ₁ h₁ + presentationFactor A f g hfg hf ψ₂ h₂ :=
  presentationTop_ext A f hf (by
    rw [LinearMap.add_comp, presentationFactor_comp, presentationFactor_comp,
      presentationFactor_comp, h])

include hfg hf in
/-- Factorization through `D'` commutes with precomposition by endomorphisms `u` of `D'` and
`u'` of `Aⁿ` intertwined by the presentation. -/
lemma presentationFactor_eq_comp {N : Type v} [AddCommGroup N] [Module A N]
    {φ ψ : ULift.{v} (Fin n → A) →ₗ[A] N} (u : D' →ₗ[A] D')
    (u' : ULift.{v} (Fin n → A) →ₗ[A] ULift.{v} (Fin n → A))
    (hu : u ∘ₗ presentationTop.{v} A f = presentationTop.{v} A f ∘ₗ u')
    (hφ : φ ∘ₗ presentationRel.{v} A g = 0) (hψ : ψ ∘ₗ presentationRel.{v} A g = 0)
    (h : φ = ψ ∘ₗ u') :
    presentationFactor A f g hfg hf φ hφ = presentationFactor A f g hfg hf ψ hψ ∘ₗ u :=
  presentationTop_ext A f hf (by
    rw [presentationFactor_comp, LinearMap.comp_assoc, hu, ← LinearMap.comp_assoc,
      presentationFactor_comp, h])

/-- The presentation `Aⁿ ⟶ D'` commutes with multiplication by `c : T`. -/
lemma presentationTop_smul (c : T) :
    smulLinearMap A c ∘ₗ presentationTop.{v} A f = presentationTop.{v} A f ∘ₗ smulLinearMap A c :=
  LinearMap.ext fun x => (LinearMap.map_smul_of_tower _ c x).symm

/-- For a cone over the relation map and `0` evaluated at `N`, each element of its leg to
`Hom_A(Aⁿ, N)` vanishes on the relations. -/
lemma presentationFork_w {N : ModuleCat.{v} A}
    (s : Cone (parallelPair (presentationRelMap.{v} T A g) 0 ⋙ (evaluation _ _).obj N))
    (x : s.pt) : ((s.π.app .zero).hom x).toLinearMap ∘ₗ presentationRel.{v} A g = 0 := by
  have h := (s.w WalkingParallelPairHom.left).trans (s.w WalkingParallelPairHom.right).symm
  exact congrArg (fun u : s.pt ⟶ (freeHomFunctor.{v} T A m).obj N => (u.hom x).toLinearMap) h

/-- **`Hom_A(D', N)` is the equalizer of the relation map and `0`.** -/
def isLimitPresentationFork (N : ModuleCat.{v} A) :
    IsLimit (((evaluation _ _).obj N).mapCone (Cone.mk _ (presentationFork T A f g hfg))) where
  lift s :=
    have hw := presentationFork_w T A g s
    ModuleCat.ofHom (X := s.pt) (Y := SourceHom A T D' N)
      { toFun := fun x => SourceHom.ofLinearMap
          (presentationFactor A f g hfg hf ((s.π.app .zero).hom x).toLinearMap (hw x))
        map_add' := fun x y => SourceHom.ext fun d => LinearMap.congr_fun
          (presentationFactor_eq_add A f g hfg hf (hw (x + y)) (hw x) (hw y)
            (by rw [_root_.map_add]; rfl)) d
        map_smul' := fun c x => SourceHom.ext fun d => LinearMap.congr_fun
          (presentationFactor_eq_comp A f g hfg hf (smulLinearMap A c) (smulLinearMap A c)
            (presentationTop_smul T A f c) (hw (c • x)) (hw x)
            (by rw [_root_.map_smul]; rfl)) d }
  fac s j := by
    cases j
    · refine ModuleCat.hom_ext (LinearMap.ext fun x => SourceHom.ext fun d => ?_)
      exact LinearMap.congr_fun
        (presentationFactor_comp A f g hfg hf _ (presentationFork_w T A g s x)) d
    · rw [← s.w WalkingParallelPairHom.left]
      refine ModuleCat.hom_ext (LinearMap.ext fun x => SourceHom.ext fun d => ?_)
      exact LinearMap.congr_fun
        (presentationFactor_comp A f g hfg hf _ (presentationFork_w T A g s x))
        (presentationRel.{v} A g d)
  uniq s m hm := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => SourceHom.ext fun d => ?_)
    have h := congrArg (fun u : s.pt ⟶ (freeHomFunctor.{v} T A n).obj N =>
      (u.hom x).toLinearMap) (hm .zero)
    exact LinearMap.congr_fun (presentationTop_ext A f hf (ψ₁ := (m.hom x).toLinearMap)
      (h.trans (presentationFactor_comp A f g hfg hf _ (presentationFork_w T A g s x)).symm)) d

end Presentation

/-- **The comparison of `Hom_A(D, -)` is invertible for a finitely presented `D`**, as soon as
that of restriction of scalars along `T → A` is: `Hom_A(D, -)` is an equalizer of finite products
of restriction of scalars. -/
theorem isIso_coefficientMate_sourceHomFunctor (D' : Type v) [AddCommGroup D'] [Module A D']
    [Module T D'] [IsScalarTower T A D'] [SMulCommClass T A D'] [Module.FinitePresentation A D']
    [J.HasSheafCompose (sourceHomFunctor.{v} A T D')]
    [K.HasSheafCompose (sourceHomFunctor.{v} A T D')]
    [∀ n, J.HasSheafCompose (freeHomFunctor.{v} T A n)]
    [∀ n, K.HasSheafCompose (freeHomFunctor.{v} T A n)]
    (hres : IsIso (sheafComposeCoefficientMate uf J K adjA adjB (algebraRes.{v} T A))) :
    IsIso (sheafComposeCoefficientMate uf J K adjA adjB
      (sourceHomFunctor.{v} A T D')) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' A D'
  have : ∀ i, J.HasSheafCompose ((parallelPair (presentationRelMap.{v} T A g) 0).obj i) := by
    rintro (_ | _)
    · exact inferInstanceAs (J.HasSheafCompose (freeHomFunctor.{v} T A n))
    · exact inferInstanceAs (J.HasSheafCompose (freeHomFunctor.{v} T A m))
  have : ∀ i, K.HasSheafCompose ((parallelPair (presentationRelMap.{v} T A g) 0).obj i) := by
    rintro (_ | _)
    · exact inferInstanceAs (K.HasSheafCompose (freeHomFunctor.{v} T A n))
    · exact inferInstanceAs (K.HasSheafCompose (freeHomFunctor.{v} T A m))
  refine isIso_coefficientMate_of_isLimit uf J K adjA adjB
    (parallelPair (presentationRelMap.{v} T A g) 0) _ (presentationFork T A f g hfg)
    (isLimitPresentationFork T A f g hfg hf) ?_
  rintro (_ | _)
  · exact isIso_coefficientMate_freeHomFunctor uf J K T A adjA adjB n hres
  · exact isIso_coefficientMate_freeHomFunctor uf J K T A adjA adjB m hres

end FinitePresentation

end Stacks.EtaleCohomology

end
