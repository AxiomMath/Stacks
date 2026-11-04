module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic

/-! # δ-functors effaced one class at a time are universal

Stacks 010T says that a δ-functor `F : A ⥤ B` (Stacks 010Q) is universal (Stacks 010S) as soon
as every object `X` admits, in every positive degree `n`, a monomorphism `u : X ⟶ I` with
`Fⁿ(u) = 0`.  When `B` is a category of modules the same conclusion holds under the weaker
hypothesis that every *class* `x ∈ Fⁿ(X)` is killed by some monomorphism `u : X ⟶ I`, i.e.
`Fⁿ(u)(x) = 0`, the monomorphism being allowed to depend on the class.

This is the form of effaceability available on categories of *finite* objects.  For the
continuous cohomology of a profinite group `G` on finite discrete modules, or for the étale
cohomology of a curve with coefficients in finite locally constant sheaves, every class dies
after coinducing along a small enough open subgroup (resp. pulling back to a small enough finite
étale cover), but without a finiteness theorem no single coinduced module kills all classes at
once — and the coinduced module along *all* of `G` is not finite.

## The argument

Grothendieck's argument is run on elements.  For a short exact sequence `S` and a morphism
`η : Fⁿ ⟶ Gⁿ`, the extension of `η` to degree `n + 1` must send `δ_F(y)` to `δ_G(η y)`.  Every
class `x ∈ Fⁿ⁺¹(X)` is of this form for the cokernel sequence of a monomorphism killing `x`, and
the value does not depend on the choices: two short exact sequences starting at `X` in whose
connecting images `x` lies are both dominated by the cokernel sequence of
`biprod.lift S.f S'.f : X ⟶ S.X₂ ⊞ S'.X₂`, in whose connecting image `x` also lies
(`DeltaFunctor.ElementwiseEffaceable.δ_eq_δ_of_δ_eq_δ`).  Additivity and naturality follow from
the same comparison, applied to a common effacement of two classes and to the pushout of an
effacement along a morphism.

## Main definitions

* `CategoryTheory.DeltaFunctor.ElementwiseEffaceable`: every class in positive degree is killed by
  a monomorphism.

## Main results

* `CategoryTheory.DeltaFunctor.isUniversal_of_elementwiseEffaceable`: an elementwise effaceable
  δ-functor with values in modules is universal.
-/

@[expose] public noncomputable section

universe w v u u'

namespace CategoryTheory.DeltaFunctor

open Limits

variable {A : Type u} [Category.{v} A] [Abelian A] {R : Type u'} [Ring R]

/-- A δ-functor with values in `R`-modules is **elementwise effaceable** if every class
`x ∈ Fⁿ⁺¹(X)` is killed by some monomorphism `ι : X ⟶ I`, i.e. `Fⁿ⁺¹(ι)(x) = 0`. -/
class ElementwiseEffaceable (F : DeltaFunctor A (ModuleCat.{w} R)) : Prop where
  /-- Every class in positive degree is killed by a monomorphism. -/
  exists_mono {X : A} {n : ℕ} (x : (F.functor (n + 1)).obj X) :
    ∃ (I : A) (ι : X ⟶ I), Mono ι ∧ (F.functor (n + 1)).map ι x = 0

namespace ElementwiseEffaceable

variable {F G : DeltaFunctor A (ModuleCat.{w} R)}

/-- The short exact sequence `X → I → I/X` of a monomorphism. An `abbrev`, so that its terms are
reducibly `X`, `I` and `cokernel ι`. -/
abbrev effSeq {X I : A} (ι : X ⟶ I) : ShortComplex A :=
  ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)

/-- The sequence `X → I → I/X` of a monomorphism is short exact. -/
lemma shortExact_effSeq {X I : A} (ι : X ⟶ I) [Mono ι] : (effSeq ι).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι))
    inferInstance inferInstance

/-- A class killed by the first map of a short exact sequence is a connecting image. -/
lemma exists_δ_eq {S : ShortComplex A} (hS : S.ShortExact) {n : ℕ}
    (x : (F.functor (n + 1)).obj S.X₁) (hx : (F.functor (n + 1)).map S.f x = 0) :
    ∃ y, F.δ hS n y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (F.exact_δ₂ hS n) x hx

/-- A connecting image is killed by the first map of the short exact sequence. -/
lemma map_f_δ {S : ShortComplex A} (hS : S.ShortExact) {n : ℕ} (y : (F.functor n).obj S.X₃) :
    (F.functor (n + 1)).map S.f (F.δ hS n y) = 0 := by
  rw [← ConcreteCategory.comp_apply, F.δ_map_f]
  rfl

/-- The connecting morphism commutes with a morphism of short exact sequences, on elements. -/
private lemma δ_map_τ₃_apply (H : DeltaFunctor A (ModuleCat.{w} R)) {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ) (y : (H.functor n).obj S.X₃) :
    H.δ hT n ((H.functor n).map φ.τ₃ y) = (H.functor (n + 1)).map φ.τ₁ (H.δ hS n y) :=
  ConcreteCategory.congr_hom (H.δ_naturality hS hT φ n) y

variable {n : ℕ} (η : F.functor n ⟶ G.functor n)

/-- Naturality of `η` on elements. -/
private lemma app_map_apply {X Y : A} (f : X ⟶ Y) (x : (F.functor n).obj X) :
    η.app Y ((F.functor n).map f x) = (G.functor n).map f (η.app X x) :=
  ConcreteCategory.congr_hom (η.naturality f) x

/-- The value `δ_G(η y)` depends only on `δ_F(y)`. -/
lemma δ_eq_δ_of_δ_eq_same {S : ShortComplex A} (hS : S.ShortExact)
    {y y' : (F.functor n).obj S.X₃} (h : F.δ hS n y = F.δ hS n y') :
    G.δ hS n (η.app S.X₃ y) = G.δ hS n (η.app S.X₃ y') := by
  have h' : F.δ hS n (y - y') = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (F.exact_δ₁ hS n) _ h'
  have hzero : (F.functor n).map S.g ≫ η.app S.X₃ ≫ G.δ hS n = 0 := by
    rw [← Category.assoc, η.naturality, Category.assoc, G.map_g_δ, Limits.comp_zero]
  have := ConcreteCategory.congr_hom hzero z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  change (F.functor n).map S.g z = y - y' at hz
  rw [hz, map_sub, map_sub] at this
  exact sub_eq_zero.1 (this.trans (by rfl))

/-- `Fⁿ⁺¹(biprod.lift a b)` kills a class killed by `Fⁿ⁺¹(a)` and by `Fⁿ⁺¹(b)`. -/
lemma map_biprodLift_eq_zero {X Y Z : A} (a : X ⟶ Y) (b : X ⟶ Z) {m : ℕ}
    (x : (F.functor m).obj X) (ha : (F.functor m).map a x = 0) (hb : (F.functor m).map b x = 0) :
    (F.functor m).map (biprod.lift a b) x = 0 := by
  have := F.additive m
  rw [biprod.lift_eq, Functor.map_add, Functor.map_comp, Functor.map_comp]
  show ((F.functor m).map a ≫ (F.functor m).map biprod.inl).hom x +
    ((F.functor m).map b ≫ (F.functor m).map biprod.inr).hom x = 0
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  show (F.functor m).map biprod.inl ((F.functor m).map a x) +
    (F.functor m).map biprod.inr ((F.functor m).map b x) = 0
  rw [ha, hb, map_zero, map_zero, add_zero]

/-- The comparison of the values on a short exact sequence `S` and on the cokernel sequence of a
monomorphism `ι` out of `S.X₁`, when the same class lies in both connecting images.  This is the
core of the independence of all choices: both are dominated by the cokernel sequence of
`biprod.lift S.f ι`. -/
lemma δ_eq_δ_of_δ_eq {S : ShortComplex A} (hS : S.ShortExact) {I : A} (ι : S.X₁ ⟶ I) [Mono ι]
    {y : (F.functor n).obj S.X₃} {y' : (F.functor n).obj (cokernel ι)}
    (h : F.δ hS n y = F.δ (shortExact_effSeq ι) n y') :
    G.δ hS n (η.app S.X₃ y) = G.δ (shortExact_effSeq ι) n (η.app _ y') := by
  have := hS.mono_f
  let k : S.X₁ ⟶ S.X₂ ⊞ I := biprod.lift S.f ι
  have : Mono k := mono_of_mono_fac (biprod.lift_fst S.f ι)
  have hT := shortExact_effSeq k
  -- The two morphisms of short exact sequences out of the cokernel sequence of `k`.
  let φ : effSeq k ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := biprod.fst
      τ₃ := cokernel.desc k (biprod.fst ≫ S.g) (by rw [← Category.assoc, biprod.lift_fst, S.zero])
      comm₁₂ := by simp [k]
      comm₂₃ := by simp }
  let φ' : effSeq k ⟶ effSeq ι :=
    { τ₁ := 𝟙 _
      τ₂ := biprod.snd
      τ₃ := cokernel.desc k (biprod.snd ≫ cokernel.π ι)
        (by rw [← Category.assoc, biprod.lift_snd, cokernel.condition])
      comm₁₂ := by simp [k]
      comm₂₃ := by simp }
  -- The class is a connecting image for the cokernel sequence of `k`.
  obtain ⟨z, hz⟩ : ∃ z, F.δ hT n z = F.δ hS n y :=
    exists_δ_eq hT _ (map_biprodLift_eq_zero _ _ _ (map_f_δ hS y)
      (by rw [h]; exact map_f_δ (shortExact_effSeq ι) y'))
  -- Transport along `φ` and `φ'` by naturality of the connecting morphisms.
  have hFφ : F.δ hS n ((F.functor n).map φ.τ₃ z) = F.δ hS n y := by
    rw [← hz]; rw [δ_map_τ₃_apply F hT hS φ]; simp [φ]
  have hFφ' : F.δ (shortExact_effSeq ι) n ((F.functor n).map φ'.τ₃ z) =
      F.δ (shortExact_effSeq ι) n y' := by
    rw [← h, ← hz]; rw [δ_map_τ₃_apply F hT _ φ']; simp [φ']
  have hGφ : G.δ hS n (η.app S.X₃ ((F.functor n).map φ.τ₃ z)) =
      G.δ hT n (η.app _ z) := by
    rw [app_map_apply]; rw [δ_map_τ₃_apply G hT hS φ]; simp [φ]
  have hGφ' : G.δ (shortExact_effSeq ι) n (η.app _ ((F.functor n).map φ'.τ₃ z)) =
      G.δ hT n (η.app _ z) := by
    rw [app_map_apply]; rw [δ_map_τ₃_apply G hT _ φ']; simp [φ']
  rw [← δ_eq_δ_of_δ_eq_same η hS hFφ, ← δ_eq_δ_of_δ_eq_same η _ hFφ', hGφ, hGφ']

variable [F.ElementwiseEffaceable]

/-- A class `x` is the connecting image of a class on the cokernel of a monomorphism. -/
lemma exists_mono_δ_eq (X : A) (x : (F.functor (n + 1)).obj X) :
    ∃ (I : A) (ι : X ⟶ I) (_ : Mono ι) (y : (F.functor n).obj (cokernel ι)),
      F.δ (shortExact_effSeq ι) n y = x := by
  obtain ⟨I, ι, hι, hx⟩ := ElementwiseEffaceable.exists_mono (F := F) x
  obtain ⟨y, hy⟩ := exists_δ_eq (shortExact_effSeq ι) x hx
  exact ⟨I, ι, hι, y, hy⟩

/-- Two classes are connecting images of classes on the cokernel of one monomorphism: kill the
first, then kill the image of the second. -/
lemma exists_mono_δ_eq_δ_eq (X : A) (x x' : (F.functor (n + 1)).obj X) :
    ∃ (I : A) (ι : X ⟶ I) (_ : Mono ι) (y y' : (F.functor n).obj (cokernel ι)),
      F.δ (shortExact_effSeq ι) n y = x ∧
        F.δ (shortExact_effSeq ι) n y' = x' := by
  obtain ⟨I₁, ι₁, hι₁, hx⟩ := ElementwiseEffaceable.exists_mono (F := F) x
  obtain ⟨I₂, ι₂, hι₂, hx'⟩ :=
    ElementwiseEffaceable.exists_mono (F := F) ((F.functor (n + 1)).map ι₁ x')
  have hι := shortExact_effSeq (ι₁ ≫ ι₂)
  obtain ⟨y, hy⟩ := exists_δ_eq hι x (by
    show ((F.functor (n + 1)).map (ι₁ ≫ ι₂)) x = 0
    rw [Functor.map_comp, ConcreteCategory.comp_apply, hx, map_zero])
  obtain ⟨y', hy'⟩ := exists_δ_eq hι x' (by
    show ((F.functor (n + 1)).map (ι₁ ≫ ι₂)) x' = 0
    rw [Functor.map_comp, ConcreteCategory.comp_apply, hx'])
  exact ⟨I₂, ι₁ ≫ ι₂, inferInstance, y, y', hy, hy'⟩

/-- The extension of `η` to degree `n + 1`, as a function on classes: `δ_F(y) ↦ δ_G(η y)` for the
cokernel sequence of a chosen monomorphism killing the class. -/
def liftFun (X : A) (x : (F.functor (n + 1)).obj X) : (G.functor (n + 1)).obj X :=
  have h := exists_mono_δ_eq X x
  have := h.choose_spec.choose_spec.choose
  G.δ (shortExact_effSeq h.choose_spec.choose) n
    (η.app _ h.choose_spec.choose_spec.choose_spec.choose)

/-- The characterising property of `liftFun`: it sends `δ_F(y)` to `δ_G(η y)`, for every short
exact sequence. -/
lemma liftFun_δ {S : ShortComplex A} (hS : S.ShortExact) (y : (F.functor n).obj S.X₃) :
    liftFun η S.X₁ (F.δ hS n y) = G.δ hS n (η.app S.X₃ y) := by
  have h := exists_mono_δ_eq S.X₁ (F.δ hS n y)
  have := h.choose_spec.choose_spec.choose
  exact (δ_eq_δ_of_δ_eq η hS h.choose_spec.choose
    h.choose_spec.choose_spec.choose_spec.choose_spec.symm).symm

/-- `liftFun` is additive: two classes are effaced by one common monomorphism. -/
lemma liftFun_add (X : A) (x x' : (F.functor (n + 1)).obj X) :
    liftFun η X (x + x') = liftFun η X x + liftFun η X x' := by
  obtain ⟨I, ι, hι, y, y', rfl, rfl⟩ := exists_mono_δ_eq_δ_eq X x x'
  rw [← map_add, liftFun_δ η (shortExact_effSeq ι), liftFun_δ η (shortExact_effSeq ι) y,
    liftFun_δ η (shortExact_effSeq ι) y', map_add, map_add]

/-- `liftFun` commutes with scalar multiplication. -/
lemma liftFun_smul (X : A) (r : R) (x : (F.functor (n + 1)).obj X) :
    liftFun η X (r • x) = r • liftFun η X x := by
  obtain ⟨I, ι, hι, y, rfl⟩ := exists_mono_δ_eq X x
  rw [← map_smul, liftFun_δ η (shortExact_effSeq ι), liftFun_δ η (shortExact_effSeq ι) y,
    map_smul, map_smul]

/-- `liftFun` is natural: push an effacement out along the morphism. -/
lemma liftFun_naturality {X X' : A} (f : X ⟶ X') (x : (F.functor (n + 1)).obj X) :
    liftFun η X' ((F.functor (n + 1)).map f x) = (G.functor (n + 1)).map f (liftFun η X x) := by
  obtain ⟨I, ι, hι, y, rfl⟩ := exists_mono_δ_eq X x
  let ι' : X' ⟶ pushout ι f := pushout.inr ι f
  have hS := shortExact_effSeq ι
  have hS' := shortExact_effSeq ι'
  let φ : effSeq ι ⟶ effSeq ι' :=
    { τ₁ := f
      τ₂ := pushout.inl ι f
      τ₃ := cokernel.map ι ι' f (pushout.inl ι f) pushout.condition
      comm₁₂ := pushout.condition.symm
      comm₂₃ := by simp }
  rw [← δ_map_τ₃_apply F hS hS' φ n y, liftFun_δ η hS', liftFun_δ η hS,
    ← δ_map_τ₃_apply G hS hS' φ n, app_map_apply]

/-- The extension of `η : Fⁿ ⟶ Gⁿ` to degree `n + 1`, as a natural transformation. -/
def liftNatTrans : F.functor (n + 1) ⟶ G.functor (n + 1) where
  app X := ModuleCat.ofHom
    { toFun := liftFun η X
      map_add' := liftFun_add η X
      map_smul' := liftFun_smul η X }
  naturality X X' f := by
    ext x
    exact liftFun_naturality η f x

/-- The components of `liftNatTrans η` are `liftFun η`. -/
lemma liftNatTrans_app_apply (X : A) (x : (F.functor (n + 1)).obj X) :
    (liftNatTrans η).app X x = liftFun η X x :=
  rfl

/-- The extension is compatible with the connecting morphisms. -/
lemma δ_comp_liftNatTrans {S : ShortComplex A} (hS : S.ShortExact) :
    η.app S.X₃ ≫ G.δ hS n = F.δ hS n ≫ (liftNatTrans η).app S.X₁ := by
  ext y
  exact (liftFun_δ η hS y).symm

end ElementwiseEffaceable

namespace ElementwiseEffaceable

variable {F G : DeltaFunctor A (ModuleCat.{w} R)} [F.ElementwiseEffaceable]

/-- The extension of `t : F⁰ ⟶ G⁰` to a morphism of δ-functors, degree by degree. -/
def liftHom (t : F.functor 0 ⟶ G.functor 0) : F ⟶ G where
  app n := Nat.rec (motive := fun n ↦ F.functor n ⟶ G.functor n) t
    (fun _ η ↦ liftNatTrans η) n
  comm hS _ := δ_comp_liftNatTrans _ hS

end ElementwiseEffaceable

/-- **A δ-functor with values in modules that is effaced one class at a time is universal.**
This is Stacks 010T with the effacing monomorphism allowed to depend on the class. -/
theorem isUniversal_of_elementwiseEffaceable (F : DeltaFunctor A (ModuleCat.{w} R))
    [F.ElementwiseEffaceable] : F.IsUniversal where
  existsUnique G t := by
    -- Uniqueness: the connecting morphisms of effacements are surjective.
    refine ⟨ElementwiseEffaceable.liftHom t, rfl, fun γ hγ ↦ DeltaFunctor.hom_ext fun n ↦ ?_⟩
    induction n with
    | zero => exact hγ
    | succ n ih =>
      ext X x
      obtain ⟨I, ι, hι, y, rfl⟩ := ElementwiseEffaceable.exists_mono_δ_eq X x
      have hS := ElementwiseEffaceable.shortExact_effSeq ι
      rw [← ConcreteCategory.comp_apply, ← γ.comm hS n, ← ConcreteCategory.comp_apply,
        ← (ElementwiseEffaceable.liftHom t).comm hS n, ih]

end CategoryTheory.DeltaFunctor
