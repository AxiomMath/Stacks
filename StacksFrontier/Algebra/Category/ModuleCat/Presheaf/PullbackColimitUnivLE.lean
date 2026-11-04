module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# The pullback of presheaves of modules along a functor, as a colimit, at larger universes

Let `F : C ⥤ D` be a functor and `R` a presheaf of commutative rings on `D`.  Restriction of
presheaves of modules along `F`, `PresheafOfModules.pushforward₀ F R`, has a left adjoint `L₀`,
computed objectwise by the colimit

`(L₀ A)(U) = colim_{(V, U ⟶ F V)} R(U) ⊗_{R(F V)} A(V)`

over the comma category `CostructuredArrow F.op U`.  `Stacks.PullbackColimit` builds this left
adjoint when the two categories are small and the rings, the modules and the morphisms all live in
one universe.  This file builds it with the universes of the two sites and of their morphisms
arbitrary, for `R` valued in `CommRingCat.{r}` and modules with sections in `Type (r + 1)`, the
index categories being `(r + 1)`-small (`UnivLE.{max u₁ v₂, r + 1}`).  That is the generality of
the big crystalline site, whose objects form a `Type (u + 1)` with morphisms in `Type u`, whose
structure sheaf has sections in `Type u` and whose modules have sections in `Type (u + 1)`.

Since Mathlib's `PresheafOfModules.pullback` along the identity of `F.op ⋙ R` is the left adjoint
of the same functor up to an identification of restriction of scalars along an identity,
`pullbackIdIso` identifies it with the colimit, and the sections of the pullback are therefore
described by germs of pure tensors.  When the index categories are filtered, `exists_ι_eq` and
`exists_map_eq_zero_of_ι_eq_zero` give the element calculus of a filtered colimit.

## Main definitions

* `Stacks.PullbackColimitUnivLE.diagram`: the diagram `(V, U ⟶ F V) ↦ R(U) ⊗_{R(F V)} A(V)`.
* `Stacks.PullbackColimitUnivLE.germ`: the image in the colimit of a pure tensor.
* `Stacks.PullbackColimitUnivLE.obj`: the colimit presheaf of modules.
* `Stacks.PullbackColimitUnivLE.colimitPullback`: the functor `L₀`, with
  `colimitPullbackAdjunction : L₀ ⊣ pushforward₀ F R`.
* `Stacks.PullbackColimitUnivLE.pullbackIdIso`: Mathlib's `PresheafOfModules.pullback` along the
  identity of `F.op ⋙ R` is `L₀`.

## Main results

* `Stacks.PullbackColimitUnivLE.hom_ext`: a morphism out of the colimit is determined by its values
  on the germs `1 ⊗ a`.
* `Stacks.PullbackColimitUnivLE.pullbackIdIso_hom_unit`: under `pullbackIdIso` the unit of the
  pullback is the germ of `1 ⊗ a` at the index `(V, 𝟙)`.
* `Stacks.PullbackColimitUnivLE.exists_ι_eq` and
  `Stacks.PullbackColimitUnivLE.exists_map_eq_zero_of_ι_eq_zero`: the filtered colimit calculus.

## References

* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 008T](https://stacks.math.columbia.edu/tag/008T)
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped TensorProduct ChangeOfRings

universe r v₁ v₂ u₁ u₂

namespace Stacks.PullbackColimitUnivLE

open PresheafOfModules

/-! ### Pure tensors in an extension of scalars -/

section BaseChange

variable {A A' B B' : Type r} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']

/-- The pure tensor `b ⊗ m` as an element of `(ModuleCat.extendScalars f).obj M`. -/
noncomputable def tmul (f : A →+* B) {M : ModuleCat.{r + 1} A} (b : B) (m : M) :
    (ModuleCat.extendScalars.{r, r, r + 1} f).obj M :=
  b ⊗ₜ[A, f] m

/-- A scalar acts on a pure tensor through its first factor. -/
lemma smul_tmul (f : A →+* B) {M : ModuleCat.{r + 1} A} (b b' : B) (m : M) :
    b • tmul f b' m = tmul f (b * b') m := rfl

/-- Two maps out of a base change agree as soon as they agree on the pure tensors `1 ⊗ m`. -/
lemma extendScalars_hom_ext (f : A →+* B) {M : ModuleCat.{r + 1} A}
    {N : ModuleCat.{r + 1} B} {x y : (ModuleCat.extendScalars.{r, r, r + 1} f).obj M ⟶ N}
    (h : ∀ m : M, x (tmul f 1 m) = y (tmul f 1 m)) : x = y :=
  ModuleCat.ExtendScalars.hom_ext h

/-- The unit of `ModuleCat.extendRestrictScalarsAdj`, read through `tmul`. -/
lemma adj_unit_apply (f : A →+* B) {M : ModuleCat.{r + 1} A} (m : M) :
    (ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} f).unit.app M m = tmul f 1 m := rfl

/-- The adjunction bijection of extension of scalars, evaluated on `1 ⊗ m`. -/
lemma homEquiv_apply_tmul (f : A →+* B) {M : ModuleCat.{r + 1} A}
    {N : ModuleCat.{r + 1} B} (x : (ModuleCat.extendScalars.{r, r, r + 1} f).obj M ⟶ N)
    (m : M) : (ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} f).homEquiv M N x m =
      x (tmul f 1 m) := rfl

/-- The inverse adjunction bijection of extension of scalars, on `1 ⊗ m`. -/
lemma homEquiv_symm_apply_tmul (f : A →+* B) {M : ModuleCat.{r + 1} A}
    {N : ModuleCat.{r + 1} B} (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} f).homEquiv M N).symm ψ (tmul f 1 m) =
      ψ m := by
  rw [← homEquiv_apply_tmul, Equiv.apply_symm_apply]

/-- A pure tensor is a scalar multiple of one with first factor `1`. -/
lemma tmul_eq_smul (f : A →+* B) {M : ModuleCat.{r + 1} A} (b : B) (m : M) :
    tmul f b m = b • tmul f 1 m := by
  rw [smul_tmul, mul_one]

/-- `m ↦ 1 ⊗ m` is additive. -/
lemma tmul_one_add (f : A →+* B) {M : ModuleCat.{r + 1} A} (m m' : M) :
    tmul f 1 (m + m') = tmul f 1 m + tmul f 1 m' :=
  map_add (ModuleCat.Hom.hom ((ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} f).unit.app M)) m m'

/-- `1 ⊗ (s • m) = f(s) ⊗ m`. -/
lemma tmul_one_smul (f : A →+* B) {M : ModuleCat.{r + 1} A} (s : A) (m : M) :
    tmul f 1 (s • m) = tmul f (f s) m := by
  have h : tmul f 1 (s • m) = f s • tmul f 1 m :=
    map_smul (ModuleCat.Hom.hom
      ((ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} f).unit.app M)) s m
  rw [h, smul_tmul, mul_one]

/-- A pure tensor is additive in its second factor. -/
lemma tmul_add (f : A →+* B) {M : ModuleCat.{r + 1} A} (b : B) (m m' : M) :
    tmul f b (m + m') = tmul f b m + tmul f b m' := by
  rw [tmul_eq_smul f b (m + m'), tmul_eq_smul f b m, tmul_eq_smul f b m', tmul_one_add,
    smul_add]

/-- A scalar of the base ring moves from the second factor of a pure tensor to the first. -/
lemma tmul_smul_right (f : A →+* B) {M : ModuleCat.{r + 1} A} (b : B) (s : A) (m : M) :
    tmul f b (s • m) = tmul f (b * f s) m := by
  rw [tmul_eq_smul f b (s • m), tmul_one_smul, smul_tmul]

/-- Base change of a semilinear map along a commuting square of ring homomorphisms, read as a
morphism between the base changes as `ModuleCat` objects: `b ⊗ m ↦ σ b ⊗ φ m`. -/
noncomputable def baseChangeMap (αV : A →+* B) (αW : A' →+* B') {ρ : A →+* A'} {σ : B →+* B'}
    (hα : ∀ a, σ (αV a) = αW (ρ a)) {M : ModuleCat.{r + 1} A} {M' : ModuleCat.{r + 1} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') :
    (ModuleCat.extendScalars.{r, r, r + 1} αV).obj M ⟶
      (ModuleCat.restrictScalars σ).obj ((ModuleCat.extendScalars.{r, r, r + 1} αW).obj M') := by
  letI : Module A B := Module.compHom B αV
  letI : Module A' B' := Module.compHom B' αW
  letI : SMulCommClass A B B := ⟨fun a b b' => by
    change αV a * (b * b') = b * (αV a * b'); ring⟩
  letI : SMulCommClass A' B' B' := ⟨fun a b b' => by
    change αW a * (b * b') = b * (αW a * b'); ring⟩
  let g : B ⊗[A] M →+ B' ⊗[A'] M' := TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun b => AddMonoidHom.mk' (fun m => σ b ⊗ₜ[A'] φ m)
        (by intro x y; simp [TensorProduct.tmul_add]))
      (by intro x y; ext m; simp [TensorProduct.add_tmul]))
    (by
      intro a b m
      change σ (αV a * b) ⊗ₜ[A'] φ m = σ b ⊗ₜ[A'] φ (a • m)
      rw [map_mul, hα, φ.map_smulₛₗ, ← TensorProduct.smul_tmul]
      rfl)
  have hg : ∀ (s : B) (x : B ⊗[A] M), g (s • x) = σ s • g x := fun s x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul b m =>
        change σ (s * b) ⊗ₜ[A'] φ m = σ s • (σ b ⊗ₜ[A'] φ m)
        rw [map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  exact ModuleCat.semilinearMapAddEquiv σ _ _
    { toFun := g
      map_add' := map_add g
      map_smul' := hg }

/-- `baseChangeMap` on a pure tensor. -/
lemma baseChangeMap_tmul (αV : A →+* B) (αW : A' →+* B') {ρ : A →+* A'} {σ : B →+* B'}
    (hα : ∀ a, σ (αV a) = αW (ρ a)) {M : ModuleCat.{r + 1} A} {M' : ModuleCat.{r + 1} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') (b : B) (m : M) :
    baseChangeMap αV αW hα φ (tmul αV b m) = tmul αW (σ b) (φ m) := rfl

/-- The base change of a semilinear map along a *triangle* of ring homomorphisms, read as a
morphism between the two base changes. -/
noncomputable def baseChangeHom (αV : A →+* B) (αW : A' →+* B) {ρ : A →+* A'}
    (hα : ∀ a, αV a = αW (ρ a)) {M : ModuleCat.{r + 1} A} {M' : ModuleCat.{r + 1} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') :
    (ModuleCat.extendScalars.{r, r, r + 1} αV).obj M ⟶
      (ModuleCat.extendScalars.{r, r, r + 1} αW).obj M' :=
  baseChangeMap αV αW (σ := RingHom.id B) hα φ ≫
    (ModuleCat.restrictScalarsId'App (RingHom.id B) rfl _).hom

/-- `baseChangeHom` on a pure tensor. -/
lemma baseChangeHom_tmul (αV : A →+* B) (αW : A' →+* B) {ρ : A →+* A'}
    (hα : ∀ a, αV a = αW (ρ a)) {M : ModuleCat.{r + 1} A} {M' : ModuleCat.{r + 1} A'}
    (φ : ↑M →ₛₗ[ρ] ↑M') (b : B) (m : M) :
    baseChangeHom αV αW hα φ (tmul αV b m) = tmul αW b (φ m) := rfl

end BaseChange

/-! ### Compatibility of the scalars -/

/-- The restriction map of `R` along an identity is the identity, on elements.  The index
object `(V, 𝟙 (F V))` carries the scalar map `R.map (𝟙 (F V))` rather than `RingHom.id`, so
this is needed wherever that object occurs. -/
lemma map_id_hom_apply {D : Type u₂} [Category.{v₂} D] (R : Dᵒᵖ ⥤ CommRingCat.{r}) (U : Dᵒᵖ)
    (s : ↑(R.obj U)) : (R.map (𝟙 U)).hom s = s := by
  rw [R.map_id]
  rfl

/-- The scalars of two terms of the diagram are compatible: a morphism `ψ : T ⟶ T'` of the
index category factors `R(U)` through `R(F T')`. -/
lemma scalars_comm {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (R : Dᵒᵖ ⥤ CommRingCat.{r}) {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T')
    (r : ↑(R.obj (F.op.obj T.left))) :
    (R.map T.hom).hom r = (R.map T'.hom).hom ((R.map (F.op.map ψ.left)).hom r) := by
  conv_lhs => rw [← CostructuredArrow.w ψ, R.map_comp]
  rfl

/-- The scalars of the terms of the diagram are compatible with a restriction in `U`. -/
lemma scalars_comm_restrict {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{r}) {U U' : Dᵒᵖ} (g : U ⟶ U')
    (T : CostructuredArrow F.op U) (r : ↑(R.obj (F.op.obj T.left))) :
    (R.map g).hom ((R.map T.hom).hom r) = (R.map (T.hom ≫ g)).hom r := by
  rw [R.map_comp]
  rfl

/-! ### The diagram -/

section Diagram

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{r})
  (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
  [UnivLE.{max u₁ v₂, r + 1}]

/-- The term `R(U) ⊗_{R(F V)} A(V)` of the colimit, at the object `T = (V, U ⟶ F V)` of the
index category. -/
noncomputable abbrev diagramObj {U : Dᵒᵖ} (T : CostructuredArrow F.op U) :
    ModuleCat.{r + 1} ↑(R.obj U) :=
  (ModuleCat.extendScalars.{r, r, r + 1} (R.map T.hom).hom).obj (A.obj T.left)

/-- The transition map of the colimit along a morphism of the index category: the base change
of a restriction map of `A`. -/
noncomputable def diagramMap
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T') :
    diagramObj F R A T ⟶ diagramObj F R A T' :=
  baseChangeHom (R.map T.hom).hom (R.map T'.hom).hom (scalars_comm F R ψ)
    (A.restrictₛₗ ψ.left)

omit [UnivLE.{max u₁ v₂, r + 1}] in
/-- `diagramMap` on a pure tensor. -/
lemma diagramMap_tmul
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T')
    (r : ↑(R.obj U)) (m : A.obj T.left) :
    diagramMap F R A ψ (tmul (R.map T.hom).hom r m)
      = tmul (R.map T'.hom).hom r (A.restrictₛₗ ψ.left m) := rfl

/-- The diagram `(V, U ⟶ F V) ↦ R(U) ⊗_{R(F V)} A(V)` over the index category
`CostructuredArrow F.op U`, whose colimit is the value at `U` of the left adjoint of
`PresheafOfModules.pushforward₀ F R`. -/
noncomputable def diagram (U : Dᵒᵖ) :
    CostructuredArrow F.op U ⥤ ModuleCat.{r + 1} ↑(R.obj U) where
  obj T := diagramObj F R A T
  map ψ := diagramMap F R A ψ
  map_id T := by
    refine extendScalars_hom_ext _ fun m => ?_
    change tmul (R.map T.hom).hom 1 (A.restrictₛₗ (𝟙 T.left) m)
        = tmul (R.map T.hom).hom 1 m
    rw [restrictₛₗ_id_apply]
  map_comp {T T' T''} ψ χ := by
    refine extendScalars_hom_ext _ fun m => ?_
    change tmul (R.map T''.hom).hom 1 (A.restrictₛₗ (ψ.left ≫ χ.left) m)
        = diagramMap F R A χ (diagramMap F R A ψ (tmul (R.map T.hom).hom 1 m))
    rw [diagramMap_tmul, diagramMap_tmul, restrictₛₗ_comp_apply]

omit [UnivLE.{max u₁ v₂, r + 1}] in
/-- The maps of the diagram on a pure tensor. -/
lemma diagram_map_tmul
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T')
    (r : ↑(R.obj U)) (m : A.obj T.left) :
    (diagram F R A U).map ψ (tmul (R.map T.hom).hom r m)
      = tmul (R.map T'.hom).hom r (A.restrictₛₗ ψ.left m) := rfl

/-! ### Germs -/

/-- The image in the colimit of the pure tensor `r ⊗ a`.  Every section of the colimit is a
sum of such germs, and `hom_ext` says that a morphism out of the colimit is determined by its
values on the germs `1 ⊗ a`. -/
noncomputable def germ
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) : ↑(colimit (diagram F R A U)) :=
  colimit.ι (diagram F R A U) T (tmul (R.map T.hom).hom r a)

/-- A scalar acts on a germ through its first factor. -/
lemma germ_smul
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r r' : ↑(R.obj U))
    (a : A.obj T.left) : r • germ F R A T r' a = germ F R A T (r * r') a :=
  (map_smul (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T)) r
    (tmul (R.map T.hom).hom r' a)).symm

/-- A germ is additive in its second factor. -/
lemma germ_add_right
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a a' : A.obj T.left) :
    germ F R A T r (a + a') = germ F R A T r a + germ F R A T r a' :=
  (congrArg (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T))
      (tmul_add (R.map T.hom).hom r a a')).trans
    (map_add (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T)) _ _)

/-- A scalar of the index ring moves from the second factor of a germ to the first. -/
lemma germ_smul_right
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (s : ↑(R.obj (F.op.obj T.left))) (a : A.obj T.left) :
    germ F R A T r (s • a) = germ F R A T (r * (R.map T.hom).hom s) a :=
  congrArg (ModuleCat.Hom.hom (colimit.ι (diagram F R A U) T))
    (tmul_smul_right (R.map T.hom).hom r s a)

/-- A germ may be re-indexed along any morphism of the index category. -/
lemma germ_map
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} {T T' : CostructuredArrow F.op U} (ψ : T ⟶ T') (r : ↑(R.obj U))
    (a : A.obj T.left) : germ F R A T r a = germ F R A T' r (A.restrictₛₗ ψ.left a) :=
  (ConcreteCategory.congr_hom (colimit.w (diagram F R A U) ψ)
    (tmul (R.map T.hom).hom r a)).symm

/-- Germs indexed by equal arrows agree. -/
lemma germ_congr
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U : Dᵒᵖ} {V : Cᵒᵖ} {h h' : F.op.obj V ⟶ U} (e : h = h') (r : ↑(R.obj U))
    (a : A.obj V) :
    germ F R A (CostructuredArrow.mk h) r a = germ F R A (CostructuredArrow.mk h') r a := by
  subst e
  rfl

/-- A morphism out of the colimit is determined by its values on the germs `1 ⊗ a`. -/
lemma hom_ext {U : Dᵒᵖ} {N : ModuleCat.{r + 1} ↑(R.obj U)}
    {x y : colimit (diagram F R A U) ⟶ N}
    (h : ∀ (T : CostructuredArrow F.op U) (a : A.obj T.left),
      x (germ F R A T 1 a) = y (germ F R A T 1 a)) : x = y := by
  refine colimit.hom_ext fun T => extendScalars_hom_ext _ fun a => ?_
  exact h T a

/-! ### The colimit as a presheaf of modules -/

/-- The cocone defining the restriction map of the colimit presheaf along `g : U ⟶ U'`. -/
noncomputable def restrictionCocone
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U U' : Dᵒᵖ} (g : U ⟶ U') : Cocone (diagram F R A U) where
  pt := (ModuleCat.restrictScalars (R.map g).hom).obj (colimit (diagram F R A U'))
  ι :=
    { app T :=
        baseChangeMap (R.map T.hom).hom (R.map (T.hom ≫ g)).hom (σ := (R.map g).hom)
            (ρ := RingHom.id _) (scalars_comm_restrict F R g T) LinearMap.id ≫
          (ModuleCat.restrictScalars (R.map g).hom).map
            (colimit.ι (diagram F R A U') (CostructuredArrow.mk (T.hom ≫ g)))
      naturality {T T'} ψ := by
        refine extendScalars_hom_ext _ fun a => ?_
        change germ F R A (CostructuredArrow.mk (T'.hom ≫ g)) ((R.map g).hom 1)
              (A.restrictₛₗ ψ.left a)
            = germ F R A (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom 1) a
        exact (germ_map F R A
          (CostructuredArrow.homMk (f := CostructuredArrow.mk (T.hom ≫ g))
            (f' := CostructuredArrow.mk (T'.hom ≫ g)) ψ.left
            (by
              change F.op.map ψ.left ≫ T'.hom ≫ g = T.hom ≫ g
              rw [← Category.assoc, CostructuredArrow.w ψ])) _ a).symm }

/-- The restriction map of the colimit presheaf along `g : U ⟶ U'`. -/
noncomputable def restrictionMap
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U U' : Dᵒᵖ} (g : U ⟶ U') :
    colimit (diagram F R A U) ⟶
      (ModuleCat.restrictScalars (R.map g).hom).obj (colimit (diagram F R A U')) :=
  colimit.desc _ (restrictionCocone F R A g)

/-- The restriction maps of the colimit presheaf on a germ. -/
lemma restrictionMap_germ
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U)
    (r : ↑(R.obj U)) (a : A.obj T.left) :
    restrictionMap F R A g (germ F R A T r a)
      = germ F R A (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom r) a :=
  ConcreteCategory.congr_hom (colimit.ι_desc (restrictionCocone F R A g) T)
    (tmul (R.map T.hom).hom r a)

/-- **The value of `L₀` on an object**: the presheaf of `R`-modules whose sections over `U`
are the colimit `colim_{V, U ⟶ F V} R(U) ⊗_{R(F V)} A(V)`. -/
noncomputable def obj : PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat) where
  obj U := colimit (diagram F R A U)
  map g := restrictionMap F R A g
  map_id U := by
    refine hom_ext F R A fun T a => ?_
    rw [restrictionMap_germ, map_one]
    exact germ_congr F R A (Category.comp_id T.hom) 1 a
  map_comp {U U' U''} g h := by
    refine hom_ext F R A fun T a => ?_
    change restrictionMap F R A (g ≫ h) (germ F R A T 1 a)
        = restrictionMap F R A h (restrictionMap F R A g (germ F R A T 1 a))
    rw [restrictionMap_germ, restrictionMap_germ, restrictionMap_germ, map_one, map_one,
      map_one]
    exact germ_congr F R A (Category.assoc T.hom g h).symm 1 a

/-- The restriction maps of the colimit presheaf on a germ. -/
lemma obj_map_germ
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    {U U' : Dᵒᵖ} (g : U ⟶ U') (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) :
    (obj F R A).map g (germ F R A T r a)
      = germ F R A (CostructuredArrow.mk (T.hom ≫ g)) ((R.map g).hom r) a :=
  restrictionMap_germ F R A g T r a

/-- **The restriction of a germ, at an arbitrary term.**  For `g : U ⟶ U'` and indices `(V, h)`
over `U` and `(V, h')` over `U'` with `h ≫ g = h'`, the restriction along `g` of the image of
`y` at `(V, h)` is the image at `(V, h')` of the base change of `y` along `R(g)`. -/
lemma obj_map_ι_mk {U U' : Dᵒᵖ} (g : U ⟶ U') {V : Cᵒᵖ} (h : F.op.obj V ⟶ U)
    (h' : F.op.obj V ⟶ U') (e : h ≫ g = h')
    (y : diagramObj F R A (CostructuredArrow.mk h)) :
    (obj F R A).map g (colimit.ι (diagram F R A U) (CostructuredArrow.mk h) y) =
      colimit.ι (diagram F R A U') (CostructuredArrow.mk h')
        (baseChangeMap (R.map h).hom (R.map h').hom (σ := (R.map g).hom) (ρ := RingHom.id _)
          (fun a ↦ by rw [← e, R.map_comp]; rfl) LinearMap.id y) := by
  subst e
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (restrictionCocone F R A g) (CostructuredArrow.mk h)) y

/-- **Re-indexing an element along a morphism of indices.** -/
lemma ι_mk_eq {U : Dᵒᵖ} {V V' : Cᵒᵖ} (h : F.op.obj V ⟶ U) (h' : F.op.obj V' ⟶ U) (ψ : V ⟶ V')
    (e : F.op.map ψ ≫ h' = h) (y : diagramObj F R A (CostructuredArrow.mk h)) :
    colimit.ι (diagram F R A U) (CostructuredArrow.mk h) y =
      colimit.ι (diagram F R A U) (CostructuredArrow.mk h')
        (diagramMap F R A (CostructuredArrow.homMk (f := CostructuredArrow.mk h)
          (f' := CostructuredArrow.mk h') ψ e) y) :=
  (ConcreteCategory.congr_hom (colimit.w (diagram F R A U)
    (CostructuredArrow.homMk (f := CostructuredArrow.mk h) (f' := CostructuredArrow.mk h') ψ e))
    y).symm

end Diagram

/-! ### The adjunction -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{r})
  [UnivLE.{max u₁ v₂, r + 1}]
  {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
  {M : PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The unit of the adjunction on sections: a section of `A` over `V`, read as a section of
`L₀ A` over `F V`. -/
noncomputable def unit (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
    (V : Cᵒᵖ) (a : A.obj V) : ↑(colimit (diagram F R A (F.op.obj V))) :=
  germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a

/-- `unit` is additive. -/
lemma unit_add
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (V : Cᵒᵖ) (a a' : A.obj V) :
    unit F R A V (a + a') = unit F R A V a + unit F R A V a' :=
  germ_add_right F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a a'

/-- `unit` is compatible with the scalar actions. -/
lemma unit_smul
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (V : Cᵒᵖ) (s : ↑(R.obj (F.op.obj V))) (a : A.obj V) :
    unit F R A V (s • a) = s • unit F R A V a := by
  have h1 : unit F R A V (s • a)
      = germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V)))
        (1 * (R.map (𝟙 (F.op.obj V))).hom s) a :=
    germ_smul_right F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 s a
  have h2 : (1 * (R.map (𝟙 (F.op.obj V))).hom s : ↑(R.obj (F.op.obj V))) = s * 1 := by
    rw [map_id_hom_apply, one_mul, mul_one]
  rw [h1, h2]
  exact (germ_smul F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) s 1 a).symm

/-- A germ is a scalar multiple of the germ with first factor `1`. -/
lemma germ_eq_smul_germ_one {U : Dᵒᵖ} (T : CostructuredArrow F.op U) (r : ↑(R.obj U))
    (a : A.obj T.left) : germ F R A T r a = r • germ F R A T 1 a := by
  rw [germ_smul, mul_one]

/-- **The germ of `1 ⊗ a` at `(V, h)` is the restriction along `h` of the unit at `a`.** -/
lemma germ_one_eq_map_unit {U : Dᵒᵖ} {V : Cᵒᵖ} (h : F.op.obj V ⟶ U) (a : A.obj V) :
    germ F R A (CostructuredArrow.mk h) 1 a = (obj F R A).map h (unit F R A V a) := by
  refine Eq.trans ?_ (obj_map_germ F R A h (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a).symm
  rw [map_one]
  exact germ_congr F R A (Category.id_comp h).symm 1 a

/-- The restriction of a unit is the unit at the restricted section. -/
lemma unit_restrict
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    {V V' : Cᵒᵖ} (g : V ⟶ V') (a : A.obj V) :
    (obj F R A).map (F.op.map g) (unit F R A V a) = unit F R A V' (A.restrictₛₗ g a) := by
  rw [unit, obj_map_germ, map_one]
  exact germ_map F R A
    (CostructuredArrow.homMk (f := CostructuredArrow.mk (𝟙 (F.op.obj V) ≫ F.op.map g))
      (f' := CostructuredArrow.mk (𝟙 (F.op.obj V'))) g
      (by
        show F.op.map g ≫ 𝟙 (F.op.obj V') = 𝟙 (F.op.obj V) ≫ F.op.map g
        rw [Category.comp_id, Category.id_comp])) 1 a

/-- The adjoint transpose of a morphism `L₀ A ⟶ M`. -/
noncomputable def toPushforward
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (x : obj F R A ⟶ M) :
    A ⟶ (pushforward₀OfCommRingCat F R).obj M where
  app V := ModuleCat.ofHom
    { toFun a := Hom.app x (F.op.obj V) (unit F R A V a)
      map_add' a a' := by rw [unit_add]; exact map_add _ _ _
      map_smul' s a := by rw [unit_smul]; exact map_smul _ _ _ }
  naturality {V V'} g := by
    ext a
    change Hom.app x (F.op.obj V') (unit F R A V' (A.restrictₛₗ g a))
        = M.restrictₛₗ (F.op.map g) (Hom.app x (F.op.obj V) (unit F R A V a))
    rw [← unit_restrict]
    exact naturality_apply x (F.op.map g) (unit F R A V a)

/-- `toPushforward_app` written out on elements. -/
lemma toPushforward_app_apply
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (x : obj F R A ⟶ M) (V : Cᵒᵖ) (a : A.obj V) :
    Hom.app (toPushforward F R x) V a = Hom.app x (F.op.obj V) (unit F R A V a) := rfl

/-- The component at `V` of a morphism `A ⟶ pushforward₀ F R M`, read as a map into
`M(F V)`.  The value of `Hom.app` carries the scalar ring in the `pushforward₀` spelling, and
rewriting through `M`'s own restriction maps needs it in `M`'s spelling. -/
noncomputable def pushforwardApp
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (V : Cᵒᵖ)
    (a : A.obj V) : M.obj (F.op.obj V) :=
  Hom.app u V a

omit [UnivLE.{max u₁ v₂, r + 1}] in
/-- `pushforwardApp` is compatible with restriction. -/
lemma pushforwardApp_restrict
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) {V V' : Cᵒᵖ}
    (g : V ⟶ V') (a : A.obj V) :
    pushforwardApp F R u V' (A.restrictₛₗ g a)
      = M.restrictₛₗ (F.op.map g) (pushforwardApp F R u V a) :=
  naturality_apply u g a

/-- The leg at `T` of the cocone defining the inverse adjoint transpose: the base change of
`u` over `V = T.left`, followed by restriction to `U`. -/
noncomputable def descLeg (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) {U : Dᵒᵖ}
    (T : CostructuredArrow F.op U) : diagramObj F R A T ⟶ M.obj U :=
  ((ModuleCat.extendRestrictScalarsAdj.{r + 1, r, r} (R.map T.hom).hom).homEquiv (A.obj T.left)
    (M.obj U)).symm (Hom.app u T.left ≫ M.map T.hom)

omit [UnivLE.{max u₁ v₂, r + 1}] in
/-- `descLeg` on a pure tensor. -/
lemma descLeg_tmul
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) {U : Dᵒᵖ}
    (T : CostructuredArrow F.op U) (a : A.obj T.left) :
    descLeg F R u T (tmul (R.map T.hom).hom 1 a)
      = M.restrictₛₗ T.hom (pushforwardApp F R u T.left a) :=
  homEquiv_symm_apply_tmul _ _ _

/-- The cocone out of which the inverse adjoint transpose is built: on the term
`R(U) ⊗_{R(F V)} A(V)` it is `r ⊗ a ↦ r • (u a)|_U`. -/
noncomputable def descCocone
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (U : Dᵒᵖ) :
    Cocone (diagram F R A U) where
  pt := M.obj U
  ι :=
    { app T := descLeg F R u T
      naturality {T T'} ψ := by
        refine extendScalars_hom_ext _ fun a => ?_
        change descLeg F R u T' (diagramMap F R A ψ (tmul (R.map T.hom).hom 1 a))
            = descLeg F R u T (tmul (R.map T.hom).hom 1 a)
        rw [diagramMap_tmul, descLeg_tmul, descLeg_tmul, pushforwardApp_restrict,
          ← restrictₛₗ_comp_apply, CostructuredArrow.w ψ] }

/-- The inverse adjoint transpose, objectwise. -/
noncomputable def descMap
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (U : Dᵒᵖ) :
    colimit (diagram F R A U) ⟶ M.obj U :=
  colimit.desc _ (descCocone F R u U)

/-- `descMap` on the germ of `1 ⊗ a`. -/
lemma descMap_germ
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) (U : Dᵒᵖ)
    (T : CostructuredArrow F.op U) (a : A.obj T.left) :
    descMap F R u U (germ F R A T 1 a)
      = M.restrictₛₗ T.hom (pushforwardApp F R u T.left a) :=
  (ConcreteCategory.congr_hom (colimit.ι_desc (descCocone F R u U) T)
    (tmul (R.map T.hom).hom 1 a)).trans (descLeg_tmul F R u T a)

/-- The inverse adjoint transpose of a morphism `A ⟶ pushforward₀ F R M`. -/
noncomputable def fromPushforward
    {A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)}
    (u : A ⟶ (pushforward₀OfCommRingCat F R).obj M) :
    obj F R A ⟶ M where
  app U := descMap F R u U
  naturality {U U'} g := by
    refine hom_ext F R A fun T a => ?_
    change descMap F R u U' ((obj F R A).map g (germ F R A T 1 a))
        = M.restrictₛₗ g (descMap F R u U (germ F R A T 1 a))
    rw [obj_map_germ, map_one, descMap_germ, descMap_germ]
    change M.restrictₛₗ (T.hom ≫ g) (pushforwardApp F R u T.left a)
        = M.restrictₛₗ g (M.restrictₛₗ T.hom (pushforwardApp F R u T.left a))
    rw [restrictₛₗ_comp_apply]

/-- **Extension of scalars and the filtered colimit are left adjoint to the pushforward of
presheaves of modules**, on hom sets: the bijection of the adjunction `L₀ ⊣ pushforward₀`. -/
noncomputable def homEquiv (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ _ _))
    (M : PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat)) :
    (obj F R A ⟶ M) ≃ (A ⟶ (pushforward₀OfCommRingCat F R).obj M) where
  toFun x := toPushforward F R x
  invFun u := fromPushforward F R u
  left_inv x := by
    refine PresheafOfModules.hom_ext fun U => hom_ext F R A fun T a => ?_
    change descMap F R (toPushforward F R x) U (germ F R A T 1 a) = Hom.app x U (germ F R A T 1 a)
    rw [descMap_germ]
    change M.restrictₛₗ T.hom (Hom.app x (F.op.obj T.left) (unit F R A T.left a))
        = Hom.app x U (germ F R A T 1 a)
    rw [show M.restrictₛₗ T.hom (Hom.app x (F.op.obj T.left) (unit F R A T.left a))
          = Hom.app x U ((obj F R A).map T.hom (unit F R A T.left a)) from
        (naturality_apply x T.hom (unit F R A T.left a)).symm,
      unit, obj_map_germ, map_one]
    exact congrArg (Hom.app x U) (germ_congr F R A (Category.id_comp T.hom) 1 a)
  right_inv u := by
    refine PresheafOfModules.hom_ext fun V => ?_
    ext a
    change descMap F R u (F.op.obj V) (germ F R A (CostructuredArrow.mk (𝟙 (F.op.obj V))) 1 a)
        = pushforwardApp F R u V a
    rw [descMap_germ]
    change M.restrictₛₗ (𝟙 (F.op.obj V)) (pushforwardApp F R u V a)
        = pushforwardApp F R u V a
    rw [restrictₛₗ_id_apply]

/-- The adjunction bijection is natural in the target. -/
lemma homEquiv_naturality (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ _ _))
    (M M' : PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat)) (g : M ⟶ M')
    (x : obj F R A ⟶ M) :
    homEquiv F R A M' (x ≫ g) = homEquiv F R A M x ≫ (pushforward₀OfCommRingCat F R).map g := by
  refine PresheafOfModules.hom_ext fun V => ?_
  rfl

/-- **`L₀`: the left adjoint of `PresheafOfModules.pushforward₀ F R`**, as the objectwise
filtered colimit `U ↦ colim_{V, U ⟶ F V} R(U) ⊗_{R(F V)} A(V)`. -/
noncomputable def colimitPullback :
    PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat) :=
  Adjunction.leftAdjointOfEquiv (G := pushforward₀OfCommRingCat F R) (homEquiv F R)
    (homEquiv_naturality F R)

/-- `colimitPullback` on objects. -/
lemma colimitPullback_obj
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)) :
    (colimitPullback F R).obj A = obj F R A := rfl

/-- **The adjunction `L₀ ⊣ pushforward₀ F R`.** -/
noncomputable def colimitPullbackAdjunction :
    colimitPullback F R ⊣ (pushforward₀OfCommRingCat F R :
      PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat) ⥤
        PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)) :=
  Adjunction.adjunctionOfEquivLeft (G := pushforward₀OfCommRingCat F R) (homEquiv F R)
    (homEquiv_naturality F R)

/-- The objectwise colimit is a left adjoint. -/
instance : (colimitPullback F R).IsLeftAdjoint :=
  (colimitPullbackAdjunction F R).isLeftAdjoint

/-- `pushforward₀ F R` is a right adjoint, the objectwise colimit being its left adjoint. -/
instance isRightAdjoint_pushforward₀ :
    (pushforward₀OfCommRingCat F R :
      PresheafOfModules.{r + 1} (R ⋙ forget₂ CommRingCat RingCat) ⥤
        PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)).IsRightAdjoint :=
  (colimitPullbackAdjunction F R).isRightAdjoint

/-- The objectwise colimit **is** the left adjoint of `pushforward₀ F R`, canonically. -/
noncomputable def colimitPullbackIsoLeftAdjoint :
    colimitPullback F R ≅ (pushforward₀OfCommRingCat F R).leftAdjoint :=
  Adjunction.leftAdjointUniq (colimitPullbackAdjunction F R) (Adjunction.ofIsRightAdjoint _)

end Adjunction


/-! ### Mathlib's pullback along an identity of presheaves of rings -/

section PullbackId

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{r}) [UnivLE.{max u₁ v₂, r + 1}]

/-- **The pushforward along the identity of `F.op ⋙ R` is `pushforward₀ F R`**: restriction of
scalars along an identity changes neither the sections nor the restriction maps. -/
noncomputable def pushforwardIdIso :
    PresheafOfModules.pushforward.{r + 1} (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat)) ≅
      pushforward₀OfCommRingCat F R :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk
      (fun V ↦ ModuleCat.restrictScalarsId'App _ rfl _)
      (fun _ _ _ ↦ by ext; rfl))
    (fun _ ↦ by ext; rfl)

/-- **The adjunction `L₀ ⊣ pushforward (𝟙 (F.op ⋙ R))`**, from `colimitPullbackAdjunction` and
`pushforwardIdIso`. -/
noncomputable def colimitPullbackIdAdjunction :
    colimitPullback F R ⊣
      PresheafOfModules.pushforward.{r + 1} (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat)) :=
  (colimitPullbackAdjunction F R).ofNatIsoRight (pushforwardIdIso F R).symm

variable [(PresheafOfModules.pushforward.{r + 1}
  (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat))).IsRightAdjoint]

/-- **Mathlib's pullback of presheaves of modules along the identity of `F.op ⋙ R` is the
objectwise colimit `L₀`**, canonically: both are left adjoint to the same functor. -/
noncomputable def pullbackIdIso :
    PresheafOfModules.pullback.{r + 1} (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat)) ≅
      colimitPullback F R :=
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction.{r + 1}
      (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat)))
    (colimitPullbackIdAdjunction F R)

/-- **The unit of the pullback, read in the colimit model**: under `pullbackIdIso`, the unit of
`PresheafOfModules.pullbackPushforwardAdjunction` carries a section `a` of `A` over `V` to the
germ of `1 ⊗ a` at the index `(V, 𝟙 (F V))`. -/
lemma pullbackIdIso_hom_unit
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (a : A.obj V) :
    Hom.app ((pullbackIdIso F R).hom.app A) (F.op.obj V)
        (Hom.app ((PresheafOfModules.pullbackPushforwardAdjunction.{r + 1}
          (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat))).unit.app A) V a) =
      unit F R A V a := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (PresheafOfModules.pullbackPushforwardAdjunction.{r + 1}
      (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat)))
    (colimitPullbackIdAdjunction F R) A
  exact congrArg (fun φ ↦ Hom.app φ V a) h

/-- `pullbackIdIso_hom_unit`, read through the inverse of `pullbackIdIso`. -/
lemma pullbackIdIso_inv_unit
    (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)) (V : Cᵒᵖ)
    (a : A.obj V) :
    Hom.app ((pullbackIdIso F R).inv.app A) (F.op.obj V) (unit F R A V a) =
      Hom.app ((PresheafOfModules.pullbackPushforwardAdjunction.{r + 1}
        (𝟙 (F.op ⋙ R ⋙ forget₂ CommRingCat RingCat))).unit.app A) V a := by
  rw [← pullbackIdIso_hom_unit]
  exact congrArg (fun φ ↦ Hom.app φ (F.op.obj V) _) (Iso.hom_inv_id_app (pullbackIdIso F R) A)

end PullbackId

/-! ### The filtered colimit calculus -/

section Filtered

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{r})
  (A : PresheafOfModules.{r + 1} ((F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat))
  [UnivLE.{max u₁ v₂, r + 1}]

/-- **The forgetful functor preserves the colimit of the diagram when its index category is
filtered**, `ModuleCat` having filtered colimits computed on underlying sets. -/
lemma preservesColimit_diagram [UnivLE.{v₁, r + 1}] (U : Dᵒᵖ)
    [IsFiltered (CostructuredArrow F.op U)] :
    PreservesColimit (diagram F R A U) (forget (ModuleCat.{r + 1} (R.obj U))) :=
  have : PreservesFilteredColimitsOfSize.{v₁, max u₁ v₂} (forget AddCommGrpCat.{r + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{r + 1, r + 1, v₁, max u₁ v₂} _
  have : PreservesColimit (diagram F R A U)
      (forget₂ (ModuleCat.{r + 1} (R.obj U)) AddCommGrpCat.{r + 1} ⋙
        forget AddCommGrpCat.{r + 1}) := inferInstance
  preservesColimit_of_natIso _
    (eqToIso (HasForget₂.forget_comp (C := ModuleCat.{r + 1} (R.obj U)) (D := AddCommGrpCat)))

variable {U : Dᵒᵖ} [PreservesColimit (diagram F R A U) (forget (ModuleCat.{r + 1} (R.obj U)))]

/-- **Every section of the colimit comes from a single index.** -/
lemma exists_ι_eq (x : ↑(colimit (diagram F R A U))) :
    ∃ (T : CostructuredArrow F.op U) (y : diagramObj F R A T),
      colimit.ι (diagram F R A U) T y = x :=
  Concrete.colimit_exists_rep (diagram F R A U) x

/-- **A section of a term of the diagram which vanishes in the colimit already vanishes at a
later index**, the index category being filtered. -/
lemma exists_map_eq_zero_of_ι_eq_zero [IsFiltered (CostructuredArrow F.op U)]
    {T : CostructuredArrow F.op U} (y : diagramObj F R A T)
    (hy : colimit.ι (diagram F R A U) T y = 0) :
    ∃ (T' : CostructuredArrow F.op U) (ψ : T ⟶ T'), diagramMap F R A ψ y = 0 := by
  have h : colimit.ι (diagram F R A U) T y = colimit.ι (diagram F R A U) T 0 := by
    rw [hy, map_zero]
  obtain ⟨T', ψ, ψ', hψ⟩ := Concrete.colimit_exists_of_rep_eq (diagram F R A U) y 0 h
  refine ⟨T', ψ, ?_⟩
  show (diagram F R A U).map ψ y = 0
  rw [hψ, map_zero]

end Filtered

end Stacks.PullbackColimitUnivLE
