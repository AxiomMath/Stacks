module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.ConeSituation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomB

/-!
# Axiom (C) for sheaf differential graded modules

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. The
differential graded category of right differential graded `A`-modules satisfies axiom (C): every
closed degree-zero morphism `f : K ⟶ L` has a cone, the sequence `L ⟶ c(f) ⟶ K[1]` is an
admissible short exact sequence, and its connecting arrow `K[1] ⟶ L[1]` is `f[1]`. Together with
axioms (A) and (B) this is a `CategoryTheory.DGCategory.ConeSituation`, the input to the
triangulated structure on the homotopy category.

## Main results

* `SheafOfModules.DifferentialGradedModule.coneSituation`: the differential graded category of
  right differential graded modules admits cones, with the shifts of axiom (B).

## Implementation notes

The cone itself is the one constructed for tag 0FS5,
`SheafOfModules.DifferentialGradedModule.cone`, whose underlying complex is Mathlib's mapping
cone and whose projection targets the *fixed* shift
`SheafOfModules.DifferentialGradedModule.shift`. That the latter is also the degree-one shift of
axiom (B) is the field `shift_one` of
`SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB`, and it is what lets the cone
sequence be read as a sequence of the shifted objects of axiom (B); the statement below records
this by asking that the `shift` field of the cone situation be exactly
`(SheafOfModules.DifferentialGradedModule.shiftAxiomB A).axiomB`.

The splitting of the cone sequence in the underlying graded category is the degreewise direct-sum
decomposition of the mapping cone: the inclusion of the target and the projection to the shifted
source are closed of degree zero, while the two splittings are only homogeneous. The connecting
morphism is then computed degreewise, and the identification of it with the shift of the original
morphism is an equality of cochains of the underlying complexes.

## References

* [Stacks Project, Tag 0FS6](https://stacks.math.columbia.edu/tag/0FS6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex

namespace SheafOfModules.DifferentialGradedModule

universe u v w


private noncomputable def categoryHomOfActionLinear
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : Cochain M.complex N.complex n)
    (hf : IsActionLinear A f) :
    D.category.Hom (moduleObject A D M) (moduleObject A D N) n :=
  (Equiv.cast (D.homs M N n)).symm
    (⟨f, hf⟩ : HomogeneousMap A M N n)

private lemma underlyingCochain_d_eq_zero
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    {f : D.category.Hom (moduleObject A D M) (moduleObject A D N) 0}
    (hf : D.category.d f = 0)
    (hzero : (Equiv.cast (D.homs M N 1)
      (0 : D.category.Hom (moduleObject A D M) (moduleObject A D N) 1)).val = 0) :
    δ 0 1 (underlyingCochain A D f) = 0 := by
  have hd := eq_of_heq (D.differential M N 0 f)
  change (Equiv.cast (D.homs M N 1) (D.category.d f)).val =
    δ 0 1 (underlyingCochain A D f) at hd
  rw [hf] at hd
  rw [hzero] at hd
  simpa using hd.symm

private noncomputable def moduleHomOfCocycle
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (f : D.category.Cocycle (moduleObject A D M) (moduleObject A D N))
    (hzero : (Equiv.cast (D.homs M N 1)
      (0 : D.category.Hom (moduleObject A D M) (moduleObject A D N) 1)).val = 0) :
    DifferentialGradedModule.Hom M N := by
  let c := underlyingCochain A D f.1
  let hc : CochainComplex.HomComplex.Cocycle M.complex N.complex 0 :=
    CochainComplex.HomComplex.Cocycle.mk c 1 rfl
      (underlyingCochain_d_eq_zero D f.2 hzero)
  refine ⟨CochainComplex.HomComplex.Cocycle.homOf hc, ?_⟩
  intro n m U x a
  have h := (Equiv.cast (D.homs M N 0) f.1).property n n m (by omega) U x a
  have hc' := CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe hc
  have hv : ∀ k, (Cochain.ofHom (CochainComplex.HomComplex.Cocycle.homOf hc)).v
      k k (add_zero k) = c.v k k (add_zero k) :=
    fun k => Cochain.congr_v hc' k k (add_zero k)
  change ((Cochain.ofHom (CochainComplex.HomComplex.Cocycle.homOf hc)).v
      (n + m) (n + m) (add_zero (n + m))).val.app U ((M.mul n m).app U x a) =
    (N.mul n m).app U
      (((Cochain.ofHom (CochainComplex.HomComplex.Cocycle.homOf hc)).v
        n n (add_zero n)).val.app U x) a
  rw [hv, hv]
  exact eq_of_heq h

private lemma moduleHom_actionLinear
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {M N : DifferentialGradedModule.{u, v, w} A}
    (g : DifferentialGradedModule.Hom M N) :
    IsActionLinear A
      (Cochain.ofHom g.toHomologicalComplex) := by
  intro p q m hpq U x a
  obtain rfl : p = q := by omega
  simpa only [Cochain.ofHom_v, heq_eq_eq] using g.map_mul p m U x a

private noncomputable def categoryHomOfModuleHom
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (g : DifferentialGradedModule.Hom M N) :
    D.category.Hom (moduleObject A D M) (moduleObject A D N) 0 :=
  categoryHomOfActionLinear D (Cochain.ofHom g.toHomologicalComplex)
    (moduleHom_actionLinear g)

private lemma categoryHomOfActionLinear_cochain
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : Cochain M.complex N.complex n)
    (hf : IsActionLinear A f) :
    underlyingCochain A D (categoryHomOfActionLinear D f hf) = f := by
  simp only [underlyingCochain, moduleHomEquiv, categoryHomOfActionLinear,
    Equiv.apply_symm_apply]

private lemma categoryHomOfModuleHom_cochain
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (g : DifferentialGradedModule.Hom M N) :
    underlyingCochain A D (categoryHomOfModuleHom D g) =
      Cochain.ofHom g.toHomologicalComplex :=
  categoryHomOfActionLinear_cochain D _ _

private lemma moduleDGCategory_zero_underlyingCochain
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (M N : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    (Equiv.cast ((dgCategoryData A).homs M N n)
      (0 : (dgCategoryData A).category.Hom
        (moduleObject A (dgCategoryData A) M)
        (moduleObject A (dgCategoryData A) N) n)).val = 0 :=
  underlyingCochain_zero A _ M N n

private noncomputable def categoryCocycleOfModuleHom
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (g : DifferentialGradedModule.Hom M N)
    (hzero : (Equiv.cast (D.homs M N 1)
      (0 : D.category.Hom (moduleObject A D M) (moduleObject A D N) 1)).val = 0) :
    D.category.Cocycle (moduleObject A D M) (moduleObject A D N) := by
  refine ⟨categoryHomOfModuleHom D g, ?_⟩
  apply (Equiv.cast (D.homs M N 1)).injective
  apply Subtype.ext
  have hd := eq_of_heq (D.differential M N 0 (categoryHomOfModuleHom D g))
  change (Equiv.cast (D.homs M N 1)
      (D.category.d (categoryHomOfModuleHom D g))).val =
    δ 0 1 (underlyingCochain A D (categoryHomOfModuleHom D g)) at hd
  have hd' : (Equiv.cast (D.homs M N 1)
      (D.category.d (categoryHomOfModuleHom D g))).val = 0 := by
    simpa only [categoryHomOfModuleHom_cochain, δ_ofHom] using hd
  exact hd'.trans hzero.symm

private lemma categoryCocycleOfModuleHom_cochain
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (g : DifferentialGradedModule.Hom M N)
    (hzero : (Equiv.cast (D.homs M N 1)
      (0 : D.category.Hom (moduleObject A D M) (moduleObject A D N) 1)).val = 0) :
    underlyingCochain A D (categoryCocycleOfModuleHom D g hzero).1 =
      Cochain.ofHom g.toHomologicalComplex :=
  categoryHomOfModuleHom_cochain D g

private noncomputable def gradedProjectionCochain
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) : Cochain P.cone.complex L.complex 0 :=
  Cochain.ofHoms (fun n => (P.componentIso n).hom ≫ biprod.snd)

private lemma gradedProjectionCochain_actionLinear
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) :
    IsActionLinear A (gradedProjectionCochain P) := by
  intro p q m hpq U x a
  obtain rfl : p = q := by omega
  apply heq_of_eq
  simpa [gradedProjectionCochain, Cochain.ofHoms_v,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using
    P.action_second p m U x a

private noncomputable def gradedSectionCochain
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) :
    Cochain (shift K).complex P.cone.complex 0 := by
  let SP := shiftPackage K
  exact Cochain.ofHoms (fun n =>
    (eqToHom (congrArg (fun C : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ => C.X n)
      SP.shifted_complex) ≫ biprod.inl) ≫
        (P.componentIso n).inv)

private lemma sheafAddApply {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (a b : M ⟶ N)
    (U : X.Cᵒᵖ) (x : M.val.obj U) :
    (a + b).val.app U x = a.val.app U x + b.val.app U x := rfl

private lemma sheafZeroApply {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (U : X.Cᵒᵖ)
    (x : M.val.obj U) :
    (0 : M ⟶ N).val.app U x = 0 := rfl

private lemma eqToHom_sheaf_app_heq
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : M = N) (U : X.Cᵒᵖ) (x : M.val.obj U) :
    HEq x ((eqToHom h).val.app U x) := by
  cases h
  rfl

private lemma sheafBiprod_ext {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (U : X.Cᵒᵖ)
    {x y : (M ⊞ N).val.obj U}
    (h₁ : (biprod.fst : M ⊞ N ⟶ M).val.app U x =
      (biprod.fst : M ⊞ N ⟶ M).val.app U y)
    (h₂ : (biprod.snd : M ⊞ N ⟶ N).val.app U x =
    (biprod.snd : M ⊞ N ⟶ N).val.app U y) : x = y := by
  have h (z : (M ⊞ N).val.obj U) :=
    congrArg (fun t : M ⊞ N ⟶ M ⊞ N => t.val.app U z) (biprod.total (X := M) (Y := N))
  simp only [sheafAddApply (X := X), SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at h
  rw [← h x, ← h y, h₁, h₂]

/-- The first projection of a biproduct recovers the element injected by `biprod.inl`. -/
private lemma biprod_inl_fst_apply {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (U : X.Cᵒᵖ)
    (y : M.val.obj U) :
    (biprod.fst : M ⊞ N ⟶ M).val.app U ((biprod.inl : M ⟶ M ⊞ N).val.app U y) = y := by
  change ((biprod.inl ≫ biprod.fst : M ⟶ M).val.app U) y = y
  simp only [biprod.inl_fst, SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]

/-- The second projection of a biproduct kills the element injected by `biprod.inl`. -/
private lemma biprod_inl_snd_apply {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (U : X.Cᵒᵖ)
    (y : M.val.obj U) :
    (biprod.snd : M ⊞ N ⟶ N).val.app U ((biprod.inl : M ⟶ M ⊞ N).val.app U y) = 0 := by
  change ((biprod.inl ≫ biprod.snd : M ⟶ N).val.app U) y = 0
  simp only [biprod.inl_snd, sheafZeroApply (X := X)]

private noncomputable def shiftXIso
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (K : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :
    (shift K).complex.X n ≅ K.complex.X (n + 1) :=
  eqToIso (congrArg (fun C : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ => C.X n)
    (shiftPackage K).shifted_complex)

private lemma action_apply_heq
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {M M' P P' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {R : SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : M = M') (hP : P = P')
    (f : BilinearMap M R P) (g : BilinearMap M' R P')
    (U : X.Cᵒᵖ) (hf : HEq (f.app U) (g.app U))
    (x : M.val.obj U) (y : M'.val.obj U) (hx : HEq x y) (a : R.val.obj U) :
    HEq (f.app U x a) (g.app U y a) := by
  cases hM
  cases hP
  rw [eq_of_heq hf, eq_of_heq hx]

private lemma gradedSectionCochain_actionLinear
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) :
    IsActionLinear A (gradedSectionCochain P) := by
  let SP := shiftPackage K
  intro p q m hpq U x a
  obtain rfl : p = q := by omega
  apply heq_of_eq
  let s := (gradedSectionCochain P).v p p (add_zero p)
  let ep := congrArg
    (fun C : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ => C.X p)
    SP.shifted_complex
  let epm := congrArg
    (fun C : CochainComplex
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ => C.X (p + m))
    SP.shifted_complex
  let xp := ((eqToHom ep).val.app U) x
  have hs : (P.componentIso p).hom.val.app U (s.val.app U x) =
      (biprod.inl : K.complex.X (p + 1) ⟶
        K.complex.X (p + 1) ⊞ L.complex.X p).val.app U xp := by
    have hsMap : s ≫ (P.componentIso p).hom = eqToHom ep ≫ biprod.inl := by
      simp only [s, gradedSectionCochain, Cochain.ofHoms_v, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun morphism : (shift K).complex.X p ⟶
      K.complex.X (p + 1) ⊞ L.complex.X p => morphism.val.app U x) hsMap
  have hs1 : ((P.componentIso p).hom ≫ biprod.fst).val.app U (s.val.app U x) = xp := by
    change (biprod.fst : K.complex.X (p + 1) ⊞ L.complex.X p ⟶
      K.complex.X (p + 1)).val.app U ((P.componentIso p).hom.val.app U (s.val.app U x)) = xp
    rw [hs, biprod_inl_fst_apply]
  have hs2 : ((P.componentIso p).hom ≫ biprod.snd).val.app U (s.val.app U x) = 0 := by
    change (biprod.snd : K.complex.X (p + 1) ⊞ L.complex.X p ⟶
      L.complex.X p).val.app U ((P.componentIso p).hom.val.app U (s.val.app U x)) = 0
    rw [hs, biprod_inl_snd_apply]
  have hfirst : HEq
      (((P.componentIso (p + m)).hom ≫ biprod.fst).val.app U
        ((P.cone.mul p m).app U (s.val.app U x) a))
      ((K.mul (p + 1) m).app U xp a) := by
    simpa only [hs1] using (P.action_first p m U (s.val.app U x) a)
  have hsecond : ((P.componentIso (p + m)).hom ≫ biprod.snd).val.app U
      ((P.cone.mul p m).app U (s.val.app U x) a) = 0 := by
    have h := P.action_second p m U (s.val.app U x) a
    rw [hs2] at h
    simpa using h
  have hshift : HEq ((SP.shifted.mul p m).app U x a)
      ((K.mul (p + 1) m).app U xp a) := by
    apply action_apply_heq ep (epm.trans (congrArg K.complex.X (by omega)))
      (SP.shifted.mul p m) (K.mul (p + 1) m) U (SP.shifted_action p m U) x xp
      (eqToHom_sheaf_app_heq ep U x) a
  have hcoords :
      (P.componentIso (p + m)).hom.val.app U
          ((P.cone.mul p m).app U (s.val.app U x) a) =
        (biprod.inl : K.complex.X (p + m + 1) ⟶
          K.complex.X (p + m + 1) ⊞ L.complex.X (p + m)).val.app U
            (((eqToHom epm).val.app U)
                ((SP.shifted.mul p m).app U x a)) := by
    apply sheafBiprod_ext U
    · rw [biprod_inl_fst_apply]
      exact eq_of_heq (hfirst.trans (hshift.symm.trans (eqToHom_sheaf_app_heq epm U
        ((SP.shifted.mul p m).app U x a))))
    · rw [biprod_inl_snd_apply]
      exact hsecond
  have h := congrArg (fun z => (P.componentIso (p + m)).inv.val.app U z) hcoords
  have hcomp : ((eqToHom epm ≫ biprod.inl ≫ (P.componentIso (p + m)).inv).val.app U)
        ((SP.shifted.mul p m).app U x a) =
      ((biprod.inl ≫ (P.componentIso (p + m)).inv).val.app U)
        (((eqToHom epm).val.app U) ((SP.shifted.mul p m).app U x a)) := by
    rfl
  have hinv : ((P.componentIso (p + m)).inv.val.app U)
        (((P.componentIso (p + m)).hom.val.app U)
          ((P.cone.mul p m).app U (s.val.app U x) a)) =
      (P.cone.mul p m).app U (s.val.app U x) a := by
    have hi := congrArg (fun g => g.val.app U ((P.cone.mul p m).app U (s.val.app U x) a))
      (Iso.hom_inv_id (P.componentIso (p + m)))
    simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hi
  calc
    _ = ((biprod.inl ≫ (P.componentIso (p + m)).inv).val.app U)
        (((eqToHom epm).val.app U) ((SP.shifted.mul p m).app U x a)) := hcomp
    _ = ((P.componentIso (p + m)).inv.val.app U)
        (((biprod.inl : K.complex.X (p + m + 1) ⟶
          K.complex.X (p + m + 1) ⊞ L.complex.X (p + m)).val.app U)
          (((eqToHom epm).val.app U) ((SP.shifted.mul p m).app U x a))) := by
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.comp_apply]
    _ = ((P.componentIso (p + m)).inv.val.app U)
        (((P.componentIso (p + m)).hom.val.app U)
          ((P.cone.mul p m).app U (s.val.app U x) a)) := h.symm
    _ = (P.cone.mul p m).app U (s.val.app U x) a := hinv

private lemma conePackage_inclusion_coords
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) (n : ℤ) (U : X.Cᵒᵖ)
    (x : (L.complex.X n).val.obj U) :
    (((P.componentIso n).hom ≫ biprod.fst).val.app U)
      ((P.inclusion.toHomologicalComplex.f n).val.app U x) = 0 ∧
    (((P.componentIso n).hom ≫ biprod.snd).val.app U)
      ((P.inclusion.toHomologicalComplex.f n).val.app U x) = x := by
  rcases P with ⟨C, incl, proj, hC, iso, hIso, _, _, hIncl, _⟩
  cases C with
  | mk Cx mul assoc one leibniz =>
      dsimp at hC
      subst Cx
      dsimp only
      rw [eq_of_heq (hIso n), eq_of_heq hIncl]
      exact ⟨coneFirst_inr f n U x, coneSecond_inr f n U x⟩

private lemma complexHom_f_transport
    {C : Type*} [Category C] [HasZeroMorphisms C] {K L L' : CochainComplex C ℤ}
    (hL : L = L') (f : K ⟶ L) (g : K ⟶ L') (hf : HEq f g) (n : ℤ) :
    f.f n ≫ eqToHom (congrArg (fun T : CochainComplex C ℤ => T.X n) hL) = g.f n := by
  cases hL
  cases hf
  simp

private lemma cone_projection_f
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) (n : ℤ) :
    P.projection.toHomologicalComplex.f n =
      (P.componentIso n).hom ≫ biprod.fst ≫ (shiftXIso K n).inv := by
  apply (cancel_mono (shiftXIso K n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rcases P with ⟨⟨Cx, mul, assoc, one, leibniz⟩, incl, proj, hC, iso, hIso,
    hFirst, hSecond, hIncl, hProj⟩
  dsimp at hC
  subst Cx
  dsimp only
  rw [eq_of_heq (hIso n)]
  exact (complexHom_f_transport (shiftPackage K).shifted_complex
    proj.toHomologicalComplex _ hProj n).trans (coneProjection_f f n)

private lemma conePackage_projection_first
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) (n : ℤ) (U : X.Cᵒᵖ)
    (x : (P.cone.complex.X n).val.obj U) :
    HEq ((P.projection.toHomologicalComplex.f n).val.app U x)
      (((P.componentIso n).hom ≫ biprod.fst).val.app U x) := by
  have h := congrArg (fun g => g.val.app U x) (cone_projection_f P n)
  exact (heq_of_eq h).trans
    (eqToHom_sheaf_app_heq
      (congrArg (fun C : CochainComplex
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ => C.X n)
        (shiftPackage K).shifted_complex).symm U
      (((P.componentIso n).hom ≫ biprod.fst).val.app U x)).symm

private lemma cone_inclusion_f
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) (n : ℤ) :
    P.inclusion.toHomologicalComplex.f n = biprod.inr ≫ (P.componentIso n).inv := by
  apply (cancel_mono (P.componentIso n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply biprod.hom_ext
  · simp only [biprod.inr_fst]
    ext U x
    exact (conePackage_inclusion_coords P n U x).1
  · simp only [biprod.inr_snd]
    ext U x
    exact (conePackage_inclusion_coords P n U x).2

private lemma cone_section_v
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) (n : ℤ) :
    (gradedSectionCochain P).v n n (add_zero n) =
      (shiftXIso K n).hom ≫ biprod.inl ≫ (P.componentIso n).inv := by
  simp only [gradedSectionCochain, Cochain.ofHoms_v, shiftXIso, eqToIso.hom, Category.assoc]
  rfl

private lemma cone_d_second
    {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}
    (P : ConePackage f) (n : ℤ) :
    P.cone.complex.d n (n + 1) ≫ (P.componentIso (n + 1)).hom ≫ biprod.snd =
      (P.componentIso n).hom ≫ biprod.fst ≫ f.toHomologicalComplex.f (n + 1) +
      (P.componentIso n).hom ≫ biprod.snd ≫ L.complex.d n (n + 1) := by
  rcases P with ⟨C, incl, proj, hC, iso, hIso, _, _, _, _⟩
  cases C with
  | mk Cx mul assoc one leibniz =>
    dsimp at hC
    subst Cx
    obtain rfl : iso = fun n => coneComponentIso f n := funext fun n => eq_of_heq (hIso n)
    simpa only [coneComponentIso, HomologicalComplex.homotopyCofiber.fstX,
      ← coneSecond_eq, coneSecond, Category.assoc] using!
      HomologicalComplex.homotopyCofiber.d_sndX f.toHomologicalComplex n (n + 1) rfl

section ConeSequence

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
variable {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
variable {K L : DifferentialGradedModule.{u, v, w} A} {f : K ⟶ L}

private noncomputable abbrev coneA (P : ConePackage f) :=
  categoryCocycleOfModuleHom (dgCategoryData A) P.inclusion
    (moduleDGCategory_zero_underlyingCochain A _ _ 1)

private noncomputable abbrev coneB (P : ConePackage f) :=
  categoryCocycleOfModuleHom (dgCategoryData A) P.projection
    (moduleDGCategory_zero_underlyingCochain A _ _ 1)

private noncomputable abbrev conePi (P : ConePackage f) :=
  categoryHomOfActionLinear (dgCategoryData A)
    (gradedProjectionCochain P) (gradedProjectionCochain_actionLinear P)

private noncomputable abbrev coneS (P : ConePackage f) :=
  categoryHomOfActionLinear (dgCategoryData A)
    (gradedSectionCochain P) (gradedSectionCochain_actionLinear P)

private lemma moduleCochain_d
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (g : D.category.Hom (moduleObject A D M) (moduleObject A D N) n) :
    underlyingCochain A D (D.category.d g) =
      δ n (n + 1) (underlyingCochain A D g) :=
  eq_of_heq (D.differential M N n g)

private lemma moduleCochain_v_heq_of_heq
    (D : DGCategoryData.{u, v, w} A)
    {M N M' N' : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (hM : M = M') (hN : N = N')
    (g : D.category.Hom (moduleObject A D M) (moduleObject A D N) n)
    (g' : D.category.Hom (moduleObject A D M') (moduleObject A D N') n)
    (hg : HEq g g') (p q : ℤ) (h : p + n = q) :
    HEq ((underlyingCochain A D g).v p q h)
      ((underlyingCochain A D g').v p q h) := by
  cases hM
  cases hN
  cases hg
  rfl

/-- The two object transports cancel, in the direction opposite to
`SheafOfModules.DifferentialGradedModule.asObject_asModule`. -/
lemma asModule_asObject (M : DifferentialGradedModule.{u, v, w} A) :
    asModule A (asObject A M) = M :=
  (Equiv.cast (dgCategoryData A).objects).apply_symm_apply M

/-- The two readings of the cochain of a homogeneous morphism — the one indexed by the objects
of the differential graded category and the one indexed by the modules they transport to — have
the same components. -/
lemma asCochain_v_heq
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (g : (dgCategoryData A).category.Hom
      (moduleObject A (dgCategoryData A) M)
      (moduleObject A (dgCategoryData A) N) n)
    (p q : ℤ) (h : p + n = q) :
    HEq ((asCochain A g).v p q h)
      ((underlyingCochain A (dgCategoryData A) g).v p q h) := by
  unfold asCochain
  apply moduleCochain_v_heq_of_heq _ (asModule_asObject M) (asModule_asObject N)
  exact (cast_heq _ _).trans (cast_heq _ _)

private lemma cone_pi_a (P : ConePackage f) :
    (dgCategoryData A).category.comp rfl (conePi P) (coneA P).1 =
      (dgCategoryData A).category.id
        (moduleObject A (dgCategoryData A) L) := by
  apply underlyingCochain_injective
  rw [underlyingCochain_comp, underlyingCochain_id,
    categoryCocycleOfModuleHom_cochain, categoryHomOfActionLinear_cochain]
  apply Cochain.ext
  intro p q h
  obtain rfl : p = q := by omega
  simp [Cochain.comp_v _ _ _ p p p (by omega) (by omega),
    gradedProjectionCochain, cone_inclusion_f]

private lemma cone_b_s (P : ConePackage f) :
    (dgCategoryData A).category.comp rfl (coneB P).1 (coneS P) =
      (dgCategoryData A).category.id
        (moduleObject A (dgCategoryData A) (shift K)) := by
  apply underlyingCochain_injective
  rw [underlyingCochain_comp, underlyingCochain_id,
    categoryCocycleOfModuleHom_cochain, categoryHomOfActionLinear_cochain]
  apply Cochain.ext
  intro p q h
  obtain rfl : p = q := by omega
  simp [Cochain.comp_v _ _ _ p p p (by omega) (by omega),
    cone_section_v, cone_projection_f, Category.assoc]

private lemma cone_pi_s (P : ConePackage f) :
    (dgCategoryData A).category.comp rfl (conePi P) (coneS P) = 0 := by
  apply underlyingCochain_injective
  rw [underlyingCochain_comp, categoryHomOfActionLinear_cochain,
    categoryHomOfActionLinear_cochain]
  show _ = (Equiv.cast ((dgCategoryData A).homs _ _ 0) 0).val
  rw [moduleDGCategory_zero_underlyingCochain]
  apply Cochain.ext
  intro p q h
  obtain rfl : p = q := by omega
  simp [Cochain.comp_v _ _ _ p p p (by omega) (by omega),
    cone_section_v, gradedProjectionCochain, Category.assoc]

private lemma cone_b_a (P : ConePackage f) :
    (dgCategoryData A).category.comp rfl (coneB P).1 (coneA P).1 = 0 := by
  apply underlyingCochain_injective
  rw [underlyingCochain_comp, categoryCocycleOfModuleHom_cochain,
    categoryCocycleOfModuleHom_cochain]
  show _ = (Equiv.cast ((dgCategoryData A).homs _ _ 0) 0).val
  rw [moduleDGCategory_zero_underlyingCochain]
  apply Cochain.ext
  intro p q h
  obtain rfl : p = q := by omega
  simp [Cochain.comp_v _ _ _ p p p (by omega) (by omega),
    cone_inclusion_f, cone_projection_f, Category.assoc]

private lemma cone_hom_ext (P : ConePackage f)
    {M : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (g h : (dgCategoryData A).category.Hom
      (moduleObject A (dgCategoryData A) M)
      (moduleObject A (dgCategoryData A) P.cone) n)
    (hπ : (dgCategoryData A).category.comp (zero_add n) (conePi P) g =
      (dgCategoryData A).category.comp (zero_add n) (conePi P) h)
    (hb : (dgCategoryData A).category.comp (zero_add n) (coneB P).1 g =
      (dgCategoryData A).category.comp (zero_add n) (coneB P).1 h) :
    g = h := by
  apply underlyingCochain_injective
  apply Cochain.ext
  intro p q hpq
  apply (cancel_mono (P.componentIso q).hom).mp
  apply biprod.hom_ext
  · have he := congrArg (fun t =>
        (underlyingCochain A (dgCategoryData A) t).v p q hpq) hb
    simp only [underlyingCochain_comp, categoryCocycleOfModuleHom_cochain,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v, cone_projection_f,
      ← Category.assoc] at he
    exact (cancel_mono (shiftXIso K q).inv).mp he
  · have he := congrArg (fun t =>
        (underlyingCochain A (dgCategoryData A) t).v p q hpq) hπ
    simpa only [underlyingCochain_comp, categoryHomOfActionLinear_cochain,
      Cochain.comp_zero_cochain_v, gradedProjectionCochain, Cochain.ofHoms_v,
      Category.assoc] using he

private noncomputable def coneSequence (P : ConePackage f) :
    DGCategory.GradedSplitShortExact (A := (dgCategoryData A).category)
      (moduleObject A (dgCategoryData A) L)
      (moduleObject A (dgCategoryData A) P.cone)
      (moduleObject A (dgCategoryData A) (shift K)) where
  a := coneA P
  b := coneB P
  π := conePi P
  s := coneS P
  π_a := cone_pi_a P
  b_s := cone_b_s P
  π_s := cone_pi_s P
  a_π_add_s_b := by
    let D := (dgCategoryData A).category
    apply cone_hom_ext P
    · change D.comp rfl (conePi P)
        (D.comp rfl (coneA P).1 (conePi P) + D.comp rfl (coneS P) (coneB P).1) = _
      rw [D.comp_add_right, D.assoc rfl rfl rfl rfl, D.assoc rfl rfl rfl rfl,
        cone_pi_a, cone_pi_s, D.id_comp, D.comp_zero_left]
      simp only [add_zero]
      exact (D.comp_id _).symm
    · change D.comp rfl (coneB P).1
        (D.comp rfl (coneA P).1 (conePi P) + D.comp rfl (coneS P) (coneB P).1) = _
      rw [D.comp_add_right, D.assoc rfl rfl rfl rfl, D.assoc rfl rfl rfl rfl,
        cone_b_a, cone_b_s, D.comp_zero_left, D.id_comp]
      simp only [zero_add]
      exact (D.comp_id _).symm

section


private lemma cone_connecting_v (P : ConePackage f) (p : ℤ) :
    (underlyingCochain A (dgCategoryData A)
      (DGCategory.GradedSplitShortExact.connectingHom (coneSequence P))).v p (p + 1) rfl =
      (shiftXIso K p).hom ≫ f.toHomologicalComplex.f (p + 1) := by
  simp only [DGCategory.GradedSplitShortExact.connectingHom, coneSequence, underlyingCochain_comp,
    moduleCochain_d, categoryHomOfActionLinear_cochain, Cochain.comp_zero_cochain_v]
  rw [δ_v 0 (0 + 1) rfl (gradedSectionCochain P) p (p + 1) rfl
    p (p + 1) (by omega) rfl]
  simp only [cone_section_v, gradedProjectionCochain, Cochain.ofHoms_v,
    Preadditive.add_comp, Category.assoc, cone_d_second,
    Preadditive.comp_add, Iso.inv_hom_id_assoc, biprod.inl_fst_assoc,
    biprod.inl_snd_assoc, zero_comp, add_zero]
  simp [Units.smul_def, Category.assoc]

end

private lemma asCochain_v_transport
    {M N : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    {x y : (dgCategoryData A).category.Obj}
    (hx : moduleObject A (dgCategoryData A) M = x)
    (hy : moduleObject A (dgCategoryData A) N = y)
    (g : (dgCategoryData A).category.Hom
      (moduleObject A (dgCategoryData A) M)
      (moduleObject A (dgCategoryData A) N) n)
    (p q : ℤ) (h : p + n = q) :
    HEq ((asCochain.{u, v, w} A (hx ▸ hy ▸ g)).v p q h)
      ((underlyingCochain A (dgCategoryData A) g).v p q h) := by
  cases hx
  cases hy
  exact asCochain_v_heq g p q h

/-- A homogeneous morphism of the differential graded category of right differential graded
modules is determined by its underlying cochain. -/
lemma asCochain_injective
    {x y : (dgCategoryData A).category.Obj} {n : ℤ} :
    Function.Injective (asCochain A (M := x) (N := y) (k := n)) := by
  intro f g h
  unfold asCochain at h
  have hh := (Equiv.cast ((dgCategoryData A).homs
    (asModule A x) (asModule A y) n)).injective
      (Subtype.ext h)
  exact (Equiv.cast _).injective ((Equiv.cast _).injective hh)

/-- The chosen degree-one shift of tag 0FS5 is the degree-one shift of axiom (B), as an object
of the differential graded category. -/
lemma shiftObject_eq
    (SB : CanonicalShiftAxiomB.{u, v, w} A)
    (M : DifferentialGradedModule.{u, v, w} A) :
    moduleObject A (dgCategoryData A) (shift M) =
      (SB.axiomB.shiftFunctor 1).obj
        (moduleObject A (dgCategoryData A) M) :=
  (congrArg (asObject A) (SB.shift_one M).symm).trans (asObject_asModule A _)

private noncomputable def shiftedConeSequence
    (SB : CanonicalShiftAxiomB.{u, v, w} A)
    (P : ConePackage f) :
    DGCategory.GradedSplitShortExact (A := (dgCategoryData A).category)
      (moduleObject A (dgCategoryData A) L)
      (moduleObject A (dgCategoryData A) P.cone)
      ((SB.axiomB.shiftFunctor 1).obj
        (moduleObject A (dgCategoryData A) K)) :=
  shiftObject_eq SB K ▸ coneSequence P

/-- Transporting the third term of a graded split short exact sequence transports its
connecting morphism. -/
lemma connectingHom_transport
    {R : Type*} [CommRing R] {D : DGCategory R} {x y z z' : D.Obj}
    (h : z = z') (E : DGCategory.GradedSplitShortExact (A := D) x y z) :
    DGCategory.GradedSplitShortExact.connectingHom (h ▸ E) =
      h ▸ DGCategory.GradedSplitShortExact.connectingHom E := by
  cases h
  rfl

private lemma eqToHom_comp_heq {C : Type*} [Category C] {X X' Y : C}
    (h : X = X') (f : X' ⟶ Y) : HEq (eqToHom h ≫ f) f := by
  cases h
  simp

private lemma shiftedCone_connecting_v
    (SB : CanonicalShiftAxiomB.{u, v, w} A)
    (P : ConePackage f) (p : ℤ) :
    HEq ((asCochain A
      (DGCategory.GradedSplitShortExact.connectingHom (shiftedConeSequence SB P))).v p (p + 1) rfl)
      (f.toHomologicalComplex.f (p + 1)) := by
  unfold shiftedConeSequence
  rw [connectingHom_transport]
  exact (asCochain_v_transport (shiftObject_eq SB K) rfl
    (DGCategory.GradedSplitShortExact.connectingHom (coneSequence P)) p (p + 1) rfl).trans
      ((heq_of_eq (cone_connecting_v P p)).trans
        (eqToHom_comp_heq
          (congrArg (fun C : CochainComplex
              (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ => C.X p)
            (shiftPackage K).shifted_complex) _))

private lemma toShift_v
    (SB : CanonicalShiftAxiomB.{u, v, w} A)
    {x y : (dgCategoryData A).category.Obj}
    (g : (dgCategoryData A).category.Hom x y 1) (p : ℤ) :
    HEq ((asCochain A ((SB.axiomB.toShift 1 x y 0) g)).v
      p p (add_zero p))
      ((asCochain A g).v p (p + 1) rfl) := by
  obtain ⟨M, rfl⟩ :=
    (Equiv.cast (dgCategoryData A).objects.symm).surjective x
  obtain ⟨N, rfl⟩ :=
    (Equiv.cast (dgCategoryData A).objects.symm).surjective y
  exact SB.toShift_components 1 0 M N g p p (add_zero p)

private lemma shiftedCone_connecting
    (SB : CanonicalShiftAxiomB.{u, v, w} A)
    (g : (dgCategoryData A).category.Cocycle
      (moduleObject A (dgCategoryData A) K)
      (moduleObject A (dgCategoryData A) L))
    (P : ConePackage f)
    (hg : Cochain.ofHom f.toHomologicalComplex =
      underlyingCochain A (dgCategoryData A) g.1) :
    DGCategory.GradedSplitShortExact.connectingCocycle SB.axiomB (shiftedConeSequence SB P) =
      (SB.axiomB.shiftFunctor 1).mapCocycle g := by
  apply Subtype.ext
  apply asCochain_injective
  apply Cochain.ext
  intro p q hpq
  obtain rfl : p = q := by omega
  have hl := (toShift_v SB (DGCategory.GradedSplitShortExact.connectingHom
      (shiftedConeSequence SB P)) p).trans (shiftedCone_connecting_v SB P p)
  have hm := SB.shifted_map 1 0 K L g.1 p p (add_zero p)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, one_smul] at hm
  have hr := (asCochain_v_heq g.1 (p + 1) (p + 1) (add_zero _)).trans
    (heq_of_eq (by rw [← hg]))
  exact eq_of_heq (hl.trans (hm.trans hr).symm)

/-- Transporting the third term of a graded split short exact sequence transports its
connecting cocycle. -/
private lemma connectingCocycle_transport
    {R : Type*} [CommRing R] {D : DGCategory R} {x y z z' : D.Obj}
    (S : DGCategory.ShiftAxiomB D) (h : z = z')
    (E : DGCategory.GradedSplitShortExact (A := D) x y z) :
    HEq (DGCategory.GradedSplitShortExact.connectingCocycle S E)
      (DGCategory.GradedSplitShortExact.connectingCocycle S (h ▸ E)) := by
  cases h
  rfl

/-- **The cone of tag 0FS5 carries a graded split short exact sequence `L ⟶ c(f) ⟶ K[1]` whose
two maps are the canonical inclusion and projection and whose connecting arrow is `f[1]`.**

The sequence is the degreewise direct-sum decomposition of the mapping cone, and this is the
content of axiom (C) for the *concrete* cone:
`SheafOfModules.DifferentialGradedModule.coneSituation` asserts the same thing for a cone obtained
by choice, so it does not identify the sequence with this one. The two maps are pinned by their
underlying cochains, which determine them, and the connecting arrow is pinned up to the
identification of the chosen shift of `K` with the degree-one shift of axiom (B). -/
theorem exists_coneSequence (SB : CanonicalShiftAxiomB.{u, v, w} A) (P : ConePackage f)
    (g : (dgCategoryData A).category.Cocycle
      (moduleObject A (dgCategoryData A) K)
      (moduleObject A (dgCategoryData A) L))
    (hg : Cochain.ofHom f.toHomologicalComplex =
      underlyingCochain A (dgCategoryData A) g.1) :
    ∃ E : DGCategory.GradedSplitShortExact (A := (dgCategoryData A).category)
        (moduleObject A (dgCategoryData A) L)
        (moduleObject A (dgCategoryData A) P.cone)
        (moduleObject A (dgCategoryData A) (shift K)),
      underlyingCochain A (dgCategoryData A) E.a.1 =
          Cochain.ofHom P.inclusion.toHomologicalComplex ∧
        underlyingCochain A (dgCategoryData A) E.b.1 =
          Cochain.ofHom P.projection.toHomologicalComplex ∧
        HEq (DGCategory.GradedSplitShortExact.connectingCocycle SB.axiomB E)
          ((SB.axiomB.shiftFunctor 1).mapCocycle g) :=
  ⟨coneSequence P,
    categoryCocycleOfModuleHom_cochain (dgCategoryData A) P.inclusion
      (moduleDGCategory_zero_underlyingCochain A _ _ 1),
    categoryCocycleOfModuleHom_cochain (dgCategoryData A) P.projection
      (moduleDGCategory_zero_underlyingCochain A _ _ 1),
    (connectingCocycle_transport SB.axiomB (shiftObject_eq SB K) (coneSequence P)).trans
      (heq_of_eq (shiftedCone_connecting SB g P hg))⟩

private lemma moduleHomOfCocycle_cochain
    (D : DGCategoryData.{u, v, w} A)
    {M N : DifferentialGradedModule.{u, v, w} A}
    (g : D.category.Cocycle (moduleObject A D M) (moduleObject A D N))
    (hzero : (Equiv.cast (D.homs M N 1)
      (0 : D.category.Hom (moduleObject A D M) (moduleObject A D N) 1)).val = 0) :
    Cochain.ofHom (moduleHomOfCocycle D g hzero).toHomologicalComplex =
      underlyingCochain A D g.1 :=
  CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe _

end ConeSequence

/-- The differential graded category of right sheaf modules admits cones whose connecting
arrows are the shifts of the original morphisms, using the fixed axiom (B) shift. -/
@[stacks 0FS6]
theorem coneSituation {X : AlgebraicGeometry.RingedSite.{u, u, u}}
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ∃ S : DGCategory.ConeSituation
        (dgCategoryData.{u, v, w} A).category,
      S.shift = (shiftAxiomB A).axiomB := by
  let D := dgCategoryData.{u, v, w} A
  let SB := shiftAxiomB.{u, v, w} A
  have hcones : ∀ {x y : D.category.Obj} (g : D.category.Cocycle x y),
      ∃ c, ∃ E : DGCategory.GradedSplitShortExact (A := D.category)
        y c ((SB.axiomB.shiftFunctor 1).obj x),
      DGCategory.GradedSplitShortExact.connectingCocycle SB.axiomB E =
        (SB.axiomB.shiftFunctor 1).mapCocycle g := by
    intro x y g
    obtain ⟨K, rfl⟩ := (Equiv.cast D.objects.symm).surjective x
    obtain ⟨L, rfl⟩ := (Equiv.cast D.objects.symm).surjective y
    let hzero := moduleDGCategory_zero_underlyingCochain A K L 1
    let f := moduleHomOfCocycle D g hzero
    let P := conePackage f
    exact ⟨moduleObject A D P.cone, shiftedConeSequence SB P,
      shiftedCone_connecting SB g P (moduleHomOfCocycle_cochain D g hzero)⟩
  let zspec := hasZeroObject.{u, v, w} A
  refine ⟨{
    directSum := {
      zero := Classical.choose zspec
      zero_from := fun M n => ((Classical.choose_spec zspec).1 M n).2
      zero_to := fun M n => ((Classical.choose_spec zspec).2 M n).2
      binaryBiproduct := fun M N => hasBinaryBiproducts A M N }
    shift := SB.axiomB
    cone := fun g => Classical.choose (hcones g)
    coneSequence := fun g => Classical.choose (Classical.choose_spec (hcones g))
    cone_connecting := fun g => Classical.choose_spec (Classical.choose_spec (hcones g))
  }, rfl⟩

end SheafOfModules.DifferentialGradedModule

end
