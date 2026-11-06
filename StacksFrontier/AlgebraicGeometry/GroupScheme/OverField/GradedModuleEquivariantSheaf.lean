/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GradedModuleOfEquivariantModule

/-!
# The equivariant module attached to a graded module

Let `A` be an integer-graded commutative ring, let `X = Spec A` and let the multiplicative group
`𝐆ₘ` act on `X` through the grading. A graded `A`-module `M` makes the associated quasi-coherent
module `M~` into a `𝐆ₘ`-equivariant quasi-coherent `𝒪_X`-module: its descent morphism carries the
canonical pullback of a homogeneous section of degree `n` to the character `x ↦ xⁿ` of `𝐆ₘ` times
that section.

## Main definitions

* `AlgebraicGeometry.GmEquivariant.moduleOf` reads a module over `A` as a module over the
  coordinate ring of `Spec A`.
* `AlgebraicGeometry.GmEquivariant.gradedDescentMorphism` is the descent morphism
  `α : a^*M~ ⟶ pr^*M~` attached to a graded module.
* `AlgebraicGeometry.GmEquivariant.gradedModuleEquivariantSheaf` is the `𝐆ₘ`-equivariant
  quasi-coherent module `M~` attached to a graded module `M`.

## Main results

* `AlgebraicGeometry.GmEquivariant.gradedDescentMorphism_homogeneous`: on the canonical
  pullback of a homogeneous section of degree `n` the descent morphism is multiplication by
  the character `xⁿ`.
* `AlgebraicGeometry.GmEquivariant.gradedModuleEquivariantSheaf_module` and
  `AlgebraicGeometry.GmEquivariant.gradedModuleEquivariantSheaf_alpha` identify the underlying
  quasi-coherent module and the descent morphism of that equivariant module with `M~` and with
  `gradedDescentMorphism`.
* `AlgebraicGeometry.GmEquivariant.gradedDescentMorphism_cocycle` and
  `AlgebraicGeometry.GmEquivariant.gradedDescentMorphism_identity` are the cocycle law and the
  normalization along the unit section for that descent morphism.
* `AlgebraicGeometry.GmEquivariant.successiveAction_eq_reindexHom_of_eigensections` and
  `AlgebraicGeometry.GmEquivariant.identityAction_eq_id_of_eigensections`: for an arbitrary action,
  a descent morphism scaling a generating family of sections by characters satisfies the cocycle
  law and the normalization along the unit section.
* `AlgebraicGeometry.GmEquivariant.actionComposition_appTop_fst_appTop` and
  `AlgebraicGeometry.GmEquivariant.actionIdentity_appTop_fst_appTop`: a character of the acting
  group, pulled back to the scheme of arrows, is multiplicative on composable pairs and trivial
  along the unit section.
* `AlgebraicGeometry.GmEquivariant.gm_mul_appTop_laurent` and
  `AlgebraicGeometry.GmEquivariant.gm_one_appTop_laurent`: the Laurent monomial `xⁿ` is a
  character of `𝐆ₘ`.

## References

* [Stacks Project, Tag 0EKJ](https://stacks.math.columbia.edu/tag/0EKJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Stacks.Groupoids
open scoped DirectSum CategoryTheory.MonObj

universe u v w

namespace AlgebraicGeometry.GmEquivariant

attribute [local instance 100] ULift.algebra'

attribute [local implicit_reducible] CategoryTheory.OverClass.asOver

/-! ### The canonical pullback section, continued -/

/-- The canonical pullback section is natural in the module. -/
theorem pullbackSection_naturality {W Z : Scheme.{u}} (f : W ⟶ Z) {F H : Z.Modules}
    (a : F ⟶ H) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullback f).map a).app ⊤ (pullbackSection f F s) =
      pullbackSection f H (a.app ⊤ s) :=
  congrArg (fun k ↦ Scheme.Modules.Hom.app k ⊤ s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a).symm

/-- The canonical pullback section along a composite, compared with the two successive
pullback sections. -/
theorem pullbackSection_comp_inv {W Z Z' : Scheme.{u}}
    (f : W ⟶ Z) (g : Z ⟶ Z') (F : Z'.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app F).app ⊤ (pullbackSection (f ≫ g) F s) =
      pullbackSection f ((Scheme.Modules.pullback g).obj F) (pullbackSection g F s) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv F
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact (congrArg (fun k ↦ Scheme.Modules.Hom.app k ⊤ s) h).symm

/-- The two successive pullback sections, compared with the canonical pullback section along
the composite. -/
theorem pullbackSection_comp_hom {W Z Z' : Scheme.{u}}
    (f : W ⟶ Z) (g : Z ⟶ Z') (F : Z'.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app F).app ⊤
        (pullbackSection f ((Scheme.Modules.pullback g).obj F) (pullbackSection g F s)) =
      pullbackSection (f ≫ g) F s := by
  rw [← pullbackSection_comp_inv]
  change (((Scheme.Modules.pullbackComp f g).inv.app F ≫
    (Scheme.Modules.pullbackComp f g).hom.app F).app ⊤) _ = _
  simp

/-- The comparison of the pullbacks along two equal morphisms carries the canonical pullback
section to the canonical pullback section. -/
theorem pullbackSection_congr {W Z : Scheme.{u}} {f g : W ⟶ Z}
    (h : f = g) (F : Z.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app F).app ⊤ (pullbackSection f F s) =
      pullbackSection g F s := by
  subst g
  rfl

/-- The canonical pullback section along an identity morphism is the section itself. -/
theorem pullbackSection_id_hom (W : Scheme.{u}) (F : W.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackId W).hom.app F).app ⊤ (pullbackSection (𝟙 W) F s) = s := by
  have h := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W))
    (Scheme.Modules.pullbackId W).hom F
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun k ↦ Scheme.Modules.Hom.app k ⊤ s) h).symm

/-- A section, read as the canonical pullback section along an identity morphism. -/
theorem pullbackSection_id_inv (W : Scheme.{u}) (F : W.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackId W).inv.app F).app ⊤ s = pullbackSection (𝟙 W) F s := by
  conv_lhs => rw [← pullbackSection_id_hom W F s]
  change (((Scheme.Modules.pullbackId W).hom.app F ≫
    (Scheme.Modules.pullbackId W).inv.app F).app ⊤) _ = _
  simp

/-- Reindexing a descent morphism preserves the property of scaling a canonical pullback
section by a global function, the function being pulled back as well. -/
theorem reindexHom_eigensection {W Z Z' : Scheme.{u}} (f : W ⟶ Z) {g h : Z ⟶ Z'}
    {F : Z'.Modules}
    (a : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F)
    (s : Γ(F, ⊤)) (r : Γ(Z, ⊤))
    (ha : a.app ⊤ (pullbackSection g F s) = r • pullbackSection h F s) :
    (reindexHom f a).app ⊤ (pullbackSection (f ≫ g) F s) =
      f.appTop r • pullbackSection (f ≫ h) F s := by
  simp only [reindexHom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    pullbackSection_comp_inv]
  rw [pullbackSection_naturality f a, ha, pullbackSection_smul,
    Scheme.Modules.Hom.app_smul, pullbackSection_comp_hom]

/-- Reading a global function through a composite of morphisms over a base. -/
theorem appTop_comp_left {S : Scheme.{u}} {W Z Z' : Over S}
    (f : W ⟶ Z) (g : Z ⟶ Z') (r : Γ(Z'.left, ⊤)) :
    (f ≫ g).left.appTop r = f.left.appTop (g.left.appTop r) :=
  congr($(Scheme.Hom.comp_appTop f.left g.left) r)

/-- Chaining two known values of morphisms of modules on global sections. -/
theorem comp_app_of_eq {W : Scheme.{u}} {F H K : W.Modules}
    (a : F ⟶ H) (b : H ⟶ K) {s : Γ(F, ⊤)} {t : Γ(H, ⊤)} {v : Γ(K, ⊤)}
    (ha : a.app ⊤ s = t) (hb : b.app ⊤ t = v) : (a ≫ b).app ⊤ s = v :=
  (congrArg (fun x ↦ b.app ⊤ x) ha).trans hb

/-- A known value of a morphism of modules on global sections, rescaled. -/
private theorem app_smul_of_eq {W : Scheme.{u}} {F H : W.Modules}
    (a : F ⟶ H) (r : Γ(W, ⊤)) {s : Γ(F, ⊤)} {t : Γ(H, ⊤)}
    (ha : a.app ⊤ s = t) : a.app ⊤ (r • s) = r • t :=
  (a.app_smul r s).trans (congrArg (r • ·) ha)

/-! ### Morphisms out of the pullback of an associated module -/

/-- Two morphisms out of the pullback of an associated quasi-coherent module which agree on the
canonical pullback sections of global sections agree. -/
theorem pullback_tilde_ext {R : CommRingCat.{u}} {W : Scheme.{u}}
    (f : W ⟶ Spec R) (M : ModuleCat.{u} R) {N : W.Modules}
    {a b : (Scheme.Modules.pullback f).obj (tilde M) ⟶ N}
    (h : ∀ m : M, a.app ⊤ (pullbackSection f (tilde M) (tilde.toOpen M ⊤ m)) =
      b.app ⊤ (pullbackSection f (tilde M) (tilde.toOpen M ⊤ m))) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply (tilde.adjunction.homEquiv _ _).injective
  ext m
  exact h m

/-- The morphism out of the pullback of an associated quasi-coherent module transposing a
linear map to the global sections of the pushforward of the target. -/
noncomputable def pullbackTildeLift {R : CommRingCat.{u}} {W : Scheme.{u}}
    (f : W ⟶ Spec R) (M : ModuleCat.{u} R) (N : W.Modules)
    (a : M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj N)) :
    (Scheme.Modules.pullback f).obj (tilde M) ⟶ N :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    ((tilde.adjunction.homEquiv _ _).symm a)

/-- The transposed morphism takes the prescribed value on the canonical pullback section of a
global section. -/
theorem pullbackTildeLift_apply {R : CommRingCat.{u}} {W : Scheme.{u}}
    (f : W ⟶ Spec R) (M : ModuleCat.{u} R) (N : W.Modules)
    (a : M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj N)) (m : M) :
    (pullbackTildeLift f M N a).app ⊤
      (pullbackSection f (tilde M) (tilde.toOpen M ⊤ m)) = a m := by
  have h := (tilde.adjunction.homEquiv _ _).apply_symm_apply a
  have h' := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply
    ((tilde.adjunction.homEquiv _ _).symm a)
  rw [← h'] at h
  exact congrArg (fun k ↦ k m) h

/-! ### The cocycle law and the unit normalization on an eigensection -/

section Action

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

section


/-- Applying a descent morphism to the two arrows of a composable pair in succession, and
applying it to their composite, agree on a section which it scales by a global function of the
scheme of arrows which is multiplicative on composable pairs. -/
theorem successiveAction_apply_of_eigensection {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F)
    (s : Γ(F, ⊤)) (r : Γ((G ⊗ X).left, ⊤))
    (ha : α.app ⊤ (pullbackSection γ[G,X].left F s) =
      r • pullbackSection (snd G X).left F s)
    (hr : (Stacks.Groupoids.ActionGroupoid.composition G X).left.appTop r =
      (pullback.fst (snd G X) γ[G,X]).left.appTop r *
        (pullback.snd (snd G X) γ[G,X]).left.appTop r) :
    (successiveAction Y G X α).app ⊤
        (pullbackSection (Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G,X]).left F s) =
      (reindexHom (Stacks.Groupoids.ActionGroupoid.composition G X).left α).app ⊤
        (pullbackSection (Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G,X]).left F s) := by
  have h₀ := pullbackSection_congr
    (congrArg Over.Hom.left (actionComposition_target Y G X)) F s
  have h₁ := reindexHom_eigensection (pullback.fst (snd G X) γ[G,X]).left α s r ha
  have h₂ := app_smul_of_eq _ ((pullback.fst (snd G X) γ[G,X]).left.appTop r)
    (pullbackSection_congr (congrArg Over.Hom.left
      (pullback.condition : pullback.fst (snd G X) γ[G,X] ≫ snd G X =
        pullback.snd (snd G X) γ[G,X] ≫ γ[G,X])) F s)
  have h₃ := app_smul_of_eq _ ((pullback.fst (snd G X) γ[G,X]).left.appTop r)
    (reindexHom_eigensection (pullback.snd (snd G X) γ[G,X]).left α s r ha)
  have h₄ := app_smul_of_eq _ ((pullback.fst (snd G X) γ[G,X]).left.appTop r)
    (app_smul_of_eq _ ((pullback.snd (snd G X) γ[G,X]).left.appTop r)
      (pullbackSection_congr
        (congrArg Over.Hom.left (actionComposition_source Y G X).symm) F s))
  have h := comp_app_of_eq _ _ h₀ (comp_app_of_eq _ _ h₁
    (comp_app_of_eq _ _ h₂ (comp_app_of_eq _ _ h₃ h₄)))
  have hc := reindexHom_eigensection (Stacks.Groupoids.ActionGroupoid.composition G X).left α s r ha
  unfold successiveAction
  rw [h, ← mul_smul, ← hr]
  exact hc.symm

end

/-- A descent morphism which scales a section by a global function of the scheme of arrows
which is trivial along the unit section fixes that section. -/
theorem identityAction_apply_of_eigensection {F : X.left.Modules}
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F)
    (s : Γ(F, ⊤)) (r : Γ((G ⊗ X).left, ⊤))
    (ha : α.app ⊤ (pullbackSection γ[G,X].left F s) =
      r • pullbackSection (snd G X).left F s)
    (hr : (Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop r = 1) :
    (identityAction Y G X α).app ⊤ s = s := by
  have h₀ := pullbackSection_id_inv X.left F s
  have h₁ := pullbackSection_congr (actionIdentity_target_left Y G X).symm F s
  have h₂ := reindexHom_eigensection (Stacks.Groupoids.ActionGroupoid.identity G X).left α s r ha
  have h₃ := app_smul_of_eq _ ((Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop r)
    (pullbackSection_congr (actionIdentity_source_left Y G X) F s)
  have h₄ := app_smul_of_eq _ ((Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop r)
    (pullbackSection_id_hom X.left F s)
  have h := comp_app_of_eq _ _ h₀ (comp_app_of_eq _ _ h₁
    (comp_app_of_eq _ _ h₂ (comp_app_of_eq _ _ h₃ h₄)))
  exact h.trans (by rw [hr, one_smul])

section


/-- The cocycle law holds for a descent morphism which scales a generating family of sections
by global functions of the scheme of arrows which are multiplicative on composable pairs. -/
theorem successiveAction_eq_reindexHom_of_eigensections {F : X.left.Modules} {Idx : Type*}
    (s : Idx → Γ(F, ⊤)) (r : Idx → Γ((G ⊗ X).left, ⊤))
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F)
    (hext : ∀ {N : (pullback (snd G X) γ[G,X]).left.Modules}
      (a b : (Scheme.Modules.pullback
        (Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G,X]).left).obj F ⟶ N),
      (∀ i, a.app ⊤ (pullbackSection
          (Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G,X]).left F (s i)) =
        b.app ⊤ (pullbackSection
          (Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G,X]).left F (s i))) → a = b)
    (ha : ∀ i, α.app ⊤ (pullbackSection γ[G,X].left F (s i)) =
      r i • pullbackSection (snd G X).left F (s i))
    (hr : ∀ i, (Stacks.Groupoids.ActionGroupoid.composition G X).left.appTop (r i) =
      (pullback.fst (snd G X) γ[G,X]).left.appTop (r i) *
        (pullback.snd (snd G X) γ[G,X]).left.appTop (r i)) :
    successiveAction Y G X α =
      reindexHom (Stacks.Groupoids.ActionGroupoid.composition G X).left α :=
  hext _ _ fun i ↦
    successiveAction_apply_of_eigensection Y G X α (s i) (r i) (ha i) (hr i)

end

/-- The normalization along the unit section holds for a descent morphism which scales a
generating family of sections by global functions of the scheme of arrows which are trivial
along that section. -/
theorem identityAction_eq_id_of_eigensections {F : X.left.Modules} {Idx : Type*}
    (s : Idx → Γ(F, ⊤)) (r : Idx → Γ((G ⊗ X).left, ⊤))
    (α : (Scheme.Modules.pullback γ[G,X].left).obj F ⟶
      (Scheme.Modules.pullback (snd G X).left).obj F)
    (hext : ∀ a b : F ⟶ F, (∀ i, a.app ⊤ (s i) = b.app ⊤ (s i)) → a = b)
    (ha : ∀ i, α.app ⊤ (pullbackSection γ[G,X].left F (s i)) =
      r i • pullbackSection (snd G X).left F (s i))
    (hr : ∀ i, (Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop (r i) = 1) :
    identityAction Y G X α = 𝟙 F :=
  hext _ _ fun i ↦
    (identityAction_apply_of_eigensection Y G X α (s i) (r i) (ha i) (hr i)).trans (by simp)

/-- A character of the acting group, pulled back to the scheme of arrows, is multiplicative on
composable pairs. -/
theorem actionComposition_appTop_fst_appTop (r : Γ(G.left, ⊤))
    (hr : (MonObj.mul (X := G)).left.appTop r =
      (fst G G).left.appTop r * (snd G G).left.appTop r) :
    (Stacks.Groupoids.ActionGroupoid.composition G X).left.appTop ((fst G X).left.appTop r) =
      (pullback.fst (snd G X) γ[G,X]).left.appTop ((fst G X).left.appTop r) *
        (pullback.snd (snd G X) γ[G,X]).left.appTop ((fst G X).left.appTop r) := by
  have hcomp : Stacks.Groupoids.ActionGroupoid.composition G X ≫ fst G X =
      lift (pullback.fst (snd G X) γ[G,X] ≫ fst G X)
        (pullback.snd (snd G X) γ[G,X] ≫ fst G X) ≫ MonObj.mul (X := G) :=
    Stacks.Groupoids.ActionGroupoid.composition_fst G X
  have key : (Stacks.Groupoids.ActionGroupoid.composition G X ≫ fst G X).left.appTop r =
      (pullback.fst (snd G X) γ[G,X] ≫ fst G X).left.appTop r *
        (pullback.snd (snd G X) γ[G,X] ≫ fst G X).left.appTop r := by
    rw [hcomp, appTop_comp_left, hr, map_mul, ← appTop_comp_left, ← appTop_comp_left,
      lift_fst, lift_snd]
  simpa only [appTop_comp_left] using key

omit [ModObj G X] in
/-- A character of the acting group, pulled back to the scheme of arrows, is trivial along the
unit section of the action. -/
theorem actionIdentity_appTop_fst_appTop (r : Γ(G.left, ⊤))
    (hr : (MonObj.one (X := G)).left.appTop r = 1) :
    (Stacks.Groupoids.ActionGroupoid.identity G X).left.appTop ((fst G X).left.appTop r) = 1 := by
  have hcomp : Stacks.Groupoids.ActionGroupoid.identity G X ≫ fst G X =
      toUnit X ≫ MonObj.one (X := G) :=
    lift_fst (toUnit X ≫ MonObj.one (X := G)) (𝟙 X)
  have key : (Stacks.Groupoids.ActionGroupoid.identity G X ≫ fst G X).left.appTop r = 1 := by
    rw [hcomp, appTop_comp_left, hr, map_one]
  simpa only [appTop_comp_left] using key

end Action

/-! ### The character laws of the multiplicative group -/

section Characters

/-- Pulling back global functions along the two projections of an affine fibre product
multiplies the two tensor factors. -/
theorem pullbackSpecIso_appTop_tmul (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (s : S) (t : T) :
    (pullbackSpecIso R S T).hom.appTop
        ((Scheme.ΓSpecIso (.of (TensorProduct R S T))).inv (s ⊗ₜ[R] t)) =
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R T)))).appTop
            ((Scheme.ΓSpecIso (.of S)).inv s) *
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (Spec.map (CommRingCat.ofHom (algebraMap R T)))).appTop
            ((Scheme.ΓSpecIso (.of T)).inv t) := by
  have h : (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) = s ⊗ₜ[R] t := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← pullbackSpecIso_hom_fst R S T, ← pullbackSpecIso_hom_snd R S T,
    comp_specMap_appTop_inv, comp_specMap_appTop_inv, ← h, map_mul, map_mul]
  rfl

/-- The Laurent monomial `xⁿ` is a character of the multiplicative group: the multiplication,
read on global sections, sends it to the product of its two pullbacks. -/
theorem gm_mul_appTop_laurent (n : ℤ) :
    (MonObj.mul (X := gm.{u})).left.appTop
        ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
          (LaurentPolynomial.T n)) =
      (fst gm.{u} gm.{u}).left.appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
            (LaurentPolynomial.T n)) *
        (snd gm.{u} gm.{u}).left.appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
            (LaurentPolynomial.T n)) := by
  rw [mul_spec_asOver_spec_left]
  change (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
      (LaurentPolynomial (ULift.{u} ℤ))).hom.appTop
    ((Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ))).toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T n))) = _
  rw [specMap_appTop_inv]
  change (pullbackSpecIso (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
      (LaurentPolynomial (ULift.{u} ℤ))).hom.appTop
    ((Scheme.ΓSpecIso (.of (TensorProduct (ULift.{u} ℤ)
        (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial (ULift.{u} ℤ))))).inv
      (Coalgebra.comul (R := ULift.{u} ℤ)
        (LaurentPolynomial.T n : LaurentPolynomial (ULift.{u} ℤ)))) = _
  rw [LaurentPolynomial.comul_T]
  exact pullbackSpecIso_appTop_tmul (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ))
    (LaurentPolynomial (ULift.{u} ℤ)) (LaurentPolynomial.T n) (LaurentPolynomial.T n)

/-- The Laurent monomial `xⁿ` takes the value `1` at the unit of the multiplicative group. -/
theorem gm_one_appTop_laurent (n : ℤ) :
    (MonObj.one (X := gm.{u})).left.appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T n)) = 1 := by
  rw [one_spec_asOver_spec_left]
  change (Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom (ULift.{u} ℤ)
      (LaurentPolynomial (ULift.{u} ℤ))).toRingHom)).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
      (LaurentPolynomial.T n)) = 1
  rw [specMap_appTop_inv]
  change (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv
    (Coalgebra.counit (R := ULift.{u} ℤ)
      (LaurentPolynomial.T n : LaurentPolynomial (ULift.{u} ℤ))) = 1
  rw [LaurentPolynomial.counit_T, map_one]

end Characters

/-! ### The equivariant module attached to a graded module -/

section Graded

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubmonoidClass σ A]

/-- A module over `A`, read as a module over the coordinate ring of `Spec A`. -/
abbrev moduleOf (A : Type u) [CommRing A] (M : Type u) [AddCommGroup M] [Module A M] :
    ModuleCat.{u} (CommRingCat.of A) := ModuleCat.of A M

variable (𝒜 : ℤ → σ) [GradedRing 𝒜]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {τ : Type w} [SetLike τ M] [AddSubmonoidClass τ M]

/-- Two additive maps out of a graded module which agree on homogeneous elements agree. -/
private theorem eq_of_homogeneous (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ] {P : Type*}
    [AddCommGroup P] {F : Type*} [FunLike F M P] [AddMonoidHomClass F M P] (f g : F)
    (h : ∀ n (m : ℳ n), f (m : M) = g (m : M)) (m : M) : f m = g m := by
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | homogeneous m => exact h _ m

/-- Two morphisms out of the pullback of `M~` which agree on the canonical pullback sections of
the homogeneous global sections agree. -/
theorem pullback_tilde_homogeneous_ext (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    {W : Scheme.{u}} (f : W ⟶ Spec (.of A)) {N : W.Modules}
    {a b : (Scheme.Modules.pullback f).obj (tilde (moduleOf A M)) ⟶ N}
    (h : ∀ n (m : ℳ n), a.app ⊤ (pullbackSection f (tilde (moduleOf A M))
        (tilde.toOpen (moduleOf A M) ⊤ (m : M))) =
      b.app ⊤ (pullbackSection f (tilde (moduleOf A M))
        (tilde.toOpen (moduleOf A M) ⊤ (m : M)))) : a = b := by
  apply pullback_tilde_ext f (moduleOf A M)
  exact eq_of_homogeneous ℳ
    (tilde.adjunction.homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a)).hom
    (tilde.adjunction.homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ b)).hom h

/-- Two morphisms out of `M~` which agree on the homogeneous global sections agree. -/
theorem tilde_homogeneous_ext (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    {N : (Spec (.of A)).Modules} {a b : tilde (moduleOf A M) ⟶ N}
    (h : ∀ n (m : ℳ n), a.app ⊤ (tilde.toOpen (moduleOf A M) ⊤ (m : M)) =
      b.app ⊤ (tilde.toOpen (moduleOf A M) ⊤ (m : M))) : a = b := by
  apply (tilde.adjunction.homEquiv _ _).injective
  ext m
  exact eq_of_homogeneous ℳ ((tilde.adjunction.homEquiv _ _) a).hom
    ((tilde.adjunction.homEquiv _ _) b).hom (fun n m ↦ h n m) m

/-- The additive map carrying a global section of `M~` to the canonical pullback section of its
degree-`n` component, scaled by the `n`-th prescribed coefficient. -/
noncomputable def gradedSectionAddHom (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    {W : Scheme.{u}} (g : W ⟶ Spec (.of A)) (c : ℤ → Γ(W, ⊤)) :
    M →+ Γ((Scheme.Modules.pullback g).obj (tilde (moduleOf A M)), ⊤) :=
  let p : M →+ Γ((Scheme.Modules.pullback g).obj (tilde (moduleOf A M)), ⊤) :=
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      (tilde (moduleOf A M))).val.app (.op ⊤)).hom.toAddMonoidHom.comp
        (tilde.toOpen (moduleOf A M) ⊤).hom.toAddMonoidHom
  (DirectSum.toAddMonoid fun n ↦
    { toFun := fun m : ℳ n ↦ c n • p (m : M)
      map_zero' := by simp
      map_add' := by intros; simp [smul_add] }).comp
    (DirectSum.decomposeAddEquiv ℳ).toAddMonoidHom

/-- On a homogeneous section of degree `n`, the additive map above is the `n`-th coefficient
times the canonical pullback section. -/
theorem gradedSectionAddHom_homogeneous (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    {W : Scheme.{u}} (g : W ⟶ Spec (.of A)) (c : ℤ → Γ(W, ⊤)) {n : ℤ} (m : ℳ n) :
    gradedSectionAddHom ℳ g c (m : M) = c n • pullbackSection g (tilde (moduleOf A M))
      (tilde.toOpen (moduleOf A M) ⊤ (m : M)) := by
  simp only [gradedSectionAddHom, Functor.id_obj, Functor.comp_obj, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    DirectSum.decomposeAddEquiv_apply, DirectSum.decompose_coe, DirectSum.toAddMonoid_of,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rfl

/-- The canonical pullback section of a scalar multiple is the pulled-back scalar times the
canonical pullback section. -/
private theorem pullbackSection_toOpen_smul {W : Scheme.{u}} (g : W ⟶ Spec (.of A))
    (a : A) (m : M) :
    pullbackSection g (tilde (moduleOf A M)) (tilde.toOpen (moduleOf A M) ⊤ (a • m)) =
      g.appTop ((Scheme.ΓSpecIso (.of A)).inv a) •
        pullbackSection g (tilde (moduleOf A M)) (tilde.toOpen (moduleOf A M) ⊤ m) := by
  rw [map_smul]
  exact pullbackSection_smul g _ _ _

/-- The additive map above is semilinear for the twist of the `A`-action by the coefficients:
a homogeneous function of degree `i` acts through its image under `f`. -/
theorem gradedSectionAddHom_smul (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] {W : Scheme.{u}} (f g : W ⟶ Spec (.of A))
    (c : ℤ → Γ(W, ⊤)) (hc : ∀ i j, c (i + j) = c i * c j)
    (hf : ∀ i (a : 𝒜 i), f.appTop ((Scheme.ΓSpecIso (.of A)).inv (a : A)) =
      c i * g.appTop ((Scheme.ΓSpecIso (.of A)).inv (a : A))) (a : A) (m : M) :
    gradedSectionAddHom ℳ g c (a • m) =
      f.appTop ((Scheme.ΓSpecIso (.of A)).inv a) • gradedSectionAddHom ℳ g c m := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp [add_smul, ha, hb]
  | homogeneous a =>
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | add m k hm hk => simp [smul_add, hm, hk]
    | homogeneous m =>
      rw [gradedSectionAddHom_homogeneous ℳ g c
          (⟨(a : A) • (m : M), SetLike.GradedSMul.smul_mem a.2 m.2⟩ : ℳ (_ + _)),
        gradedSectionAddHom_homogeneous, pullbackSection_toOpen_smul, hc, hf]
      simp only [smul_smul]
      congr 1
      exact mul_right_comm _ _ _

/-- The `A`-linear map `m ↦ c_{deg m} · m` from `M` to the global sections of the pushforward
along `f` of the pullback along `g` of `M~`, for a multiplicative family of coefficients `c`
through which `f` and `g` differ on homogeneous functions. -/
noncomputable def gradedSectionLinearMap (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] {W : Scheme.{u}} (f g : W ⟶ Spec (.of A))
    (c : ℤ → Γ(W, ⊤)) (hc : ∀ i j, c (i + j) = c i * c j)
    (hf : ∀ i (a : 𝒜 i), f.appTop ((Scheme.ΓSpecIso (.of A)).inv (a : A)) =
      c i * g.appTop ((Scheme.ΓSpecIso (.of A)).inv (a : A))) :
    moduleOf A M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback g).obj (tilde (moduleOf A M)))) :=
  ConcreteCategory.ofHom (C := ModuleCat A)
    { toFun := fun m ↦ gradedSectionAddHom (A := A) ℳ g c m
      map_add' := (gradedSectionAddHom (A := A) ℳ g c).map_add
      map_smul' := fun a m ↦ gradedSectionAddHom_smul 𝒜 ℳ f g c hc hf a m }

variable (ℳ : ℤ → τ) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]

/-- **The descent morphism of the equivariant structure on `M~`.** It is the transpose of the
`A`-linear map sending a homogeneous section `m` of degree `n` to `xⁿ · m`, so it carries the
canonical pullback of `m` along the action to `xⁿ` times its canonical pullback along the
projection. -/
noncomputable def gradedDescentMorphism :
    (Scheme.Modules.pullback (gradedGmAction 𝒜).action.smul.left).obj
        (tilde (moduleOf A M)) ⟶
      (Scheme.Modules.pullback (snd gm.{u} (specAOver A)).left).obj (tilde (moduleOf A M)) :=
  pullbackTildeLift (gradedGmAction 𝒜).action.smul.left (moduleOf A M)
    ((Scheme.Modules.pullback (snd gm.{u} (specAOver A)).left).obj (tilde (moduleOf A M)))
    (gradedSectionLinearMap (A := A) (M := M) 𝒜 ℳ
      (gradedGmAction 𝒜).action.smul.left (snd gm.{u} (specAOver A)).left
      (laurentCoordinate A)
      (fun i j ↦ laurentCoordinate_add (A := A) i j)
      (fun i a ↦ action_appTop_eq_laurentCoordinate_mul 𝒜 i (a : A) a.2))

/-- On the canonical pullback of a homogeneous section of degree `n` along the action, the
descent morphism is multiplication by the character `xⁿ`. -/
@[stacks 0EKJ "the descent morphism on homogeneous sections"]
theorem gradedDescentMorphism_homogeneous {n : ℤ} (m : ℳ n) :
    (gradedDescentMorphism 𝒜 ℳ).app ⊤
        (pullbackSection (gradedGmAction 𝒜).action.smul.left (tilde (moduleOf A M))
          (tilde.toOpen (moduleOf A M) ⊤ (m : M))) =
      laurentCoordinate A n • pullbackSection (snd gm.{u} (specAOver A)).left
        (tilde (moduleOf A M)) (tilde.toOpen (moduleOf A M) ⊤ (m : M)) := by
  rw [gradedDescentMorphism, pullbackTildeLift_apply]
  exact gradedSectionAddHom_homogeneous (A := A) ℳ _ _ m

/-- The descent morphism attached to a graded module satisfies the cocycle law: applying it to
the two arrows of a composable pair in succession is applying it to their composite. -/
theorem gradedDescentMorphism_cocycle :
    @successiveAction _ base.{u} gm.{u} (specAOver A)
        AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
        (tilde (moduleOf A M)) (gradedDescentMorphism 𝒜 ℳ) =
      reindexHom (@Stacks.Groupoids.ActionGroupoid.composition _ _ _ gm.{u}
          (specAOver A) AlgebraicGeometry.instGrpObjSpecAsOverSpec
          (gradedGmAction 𝒜).action _).left
        (gradedDescentMorphism 𝒜 ℳ) :=
  @successiveAction_eq_reindexHom_of_eigensections _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
    (tilde (moduleOf A M)) (Σ n : ℤ, ℳ n)
    (fun m ↦ tilde.toOpen (moduleOf A M) ⊤ (m.2 : M))
    (fun m ↦ laurentCoordinate A m.1) (gradedDescentMorphism 𝒜 ℳ)
    (fun _ _ h ↦ pullback_tilde_homogeneous_ext ℳ _ fun n m ↦ h ⟨n, m⟩)
    (fun m ↦ gradedDescentMorphism_homogeneous 𝒜 ℳ m.2)
    (fun m ↦ @actionComposition_appTop_fst_appTop _ base.{u} gm.{u} (specAOver A)
      AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T m.1))
      (gm_mul_appTop_laurent m.1))

/-- The descent morphism attached to a graded module restricts to the identity along the unit
section of the action. -/
theorem gradedDescentMorphism_identity :
    @identityAction _ base.{u} gm.{u} (specAOver A)
        AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
        (tilde (moduleOf A M)) (gradedDescentMorphism 𝒜 ℳ) =
      𝟙 (tilde (moduleOf A M)) :=
  @identityAction_eq_id_of_eigensections _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
    (tilde (moduleOf A M)) (Σ n : ℤ, ℳ n)
    (fun m ↦ tilde.toOpen (moduleOf A M) ⊤ (m.2 : M))
    (fun m ↦ laurentCoordinate A m.1) (gradedDescentMorphism 𝒜 ℳ)
    (fun _ _ h ↦ tilde_homogeneous_ext ℳ fun n m ↦ h ⟨n, m⟩)
    (fun m ↦ gradedDescentMorphism_homogeneous 𝒜 ℳ m.2)
    (fun m ↦ @actionIdentity_appTop_fst_appTop _ base.{u} gm.{u} (specAOver A)
      AlgebraicGeometry.instGrpObjSpecAsOverSpec
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial (ULift.{u} ℤ)))).inv
        (LaurentPolynomial.T m.1))
      (gm_one_appTop_laurent m.1))

/-- Let `A` be a `ℤ`-graded ring and let `X = Spec A` carry the `𝐆ₘ`-action attached to the
grading. A graded `A`-module `M` makes the associated quasi-coherent module `M~` a
`𝐆ₘ`-equivariant quasi-coherent `𝒪_X`-module, whose descent morphism carries the canonical
pullback of a homogeneous section of degree `n` to `xⁿ` times that section. -/
@[stacks 0EKJ "graded_module_equivariant_sheaf"]
noncomputable def gradedModuleEquivariantSheaf : GradedEquivariantModule.{u} 𝒜 :=
  @EquivariantModule.mk _ base.{u} gm.{u} (specAOver A)
    AlgebraicGeometry.instGrpObjSpecAsOverSpec (gradedGmAction 𝒜).action
    (tilde (moduleOf A M)) (inferInstanceAs ((tilde (moduleOf A M)).IsQuasicoherent))
    (gradedDescentMorphism 𝒜 ℳ) (gradedDescentMorphism_cocycle 𝒜 ℳ)
    (gradedDescentMorphism_identity 𝒜 ℳ)

/-- The underlying quasi-coherent module of the equivariant module attached to a graded module
is `M~`. -/
@[stacks 0EKJ "underlying module"]
theorem gradedModuleEquivariantSheaf_module :
    underlyingModule 𝒜 (gradedModuleEquivariantSheaf 𝒜 ℳ) = tilde (moduleOf A M) :=
  rfl

/-- The descent morphism of the equivariant module attached to a graded module is
`gradedDescentMorphism`. -/
@[stacks 0EKJ "descent morphism"]
theorem gradedModuleEquivariantSheaf_alpha :
    descentMorphism 𝒜 (gradedModuleEquivariantSheaf 𝒜 ℳ) = gradedDescentMorphism 𝒜 ℳ :=
  rfl

end Graded

end AlgebraicGeometry.GmEquivariant

end
