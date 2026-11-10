module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Derived inverse systems of modules

Let `(A_n)` be an inverse system of commutative rings indexed by `ℕ`, with transition maps
`f n : A (n+1) →+* A n`. Given objects `K n` of `D(A_n)` and morphisms
`φ n : K (n+1) ⟶ K n` in `D(A_{n+1})`, where `K n` is regarded as an object of `D(A_{n+1})` by
restriction of scalars along `f n`, there is an object `M` of the derived category of inverse
systems of modules together with isomorphisms `(Dcomp n).obj M ≅ K n` compatible with the
transition maps. The object `M` is not unique.

The inverse system of rings is the functor `Rfun A f : ℕᵒᵖ ⥤ RingCat`, and the category of
inverse systems of modules over it is `PresheafOfModules (Rfun A f)`: an object assigns to each
`n` an `A_n`-module `M_n` and to `op (n+1) ⟶ op n` an `A_{n+1}`-linear map from `M_{n+1}` to the
restriction of scalars of `M_n`.

## Main definitions

* `Rfun`: the inverse system of rings `(A_n)` as a functor `ℕᵒᵖ ⥤ RingCat`.
* `evalRestrictionNT`: the transition maps of inverse systems of modules, as a natural
  transformation from evaluation at `n+1` to restriction of scalars of evaluation at `n`.
* `Dcomp`: the functor `D(Mod(ℕ, (A_n))) ⥤ D(A_n)` induced by evaluation at `n`.
* `Drestr`: the functor `D(A_n) ⥤ D(A_{n+1})` induced by restriction of scalars along `f n`.
* `transitionNT`: the natural transformation `Dcomp (n+1) ⟶ Dcomp n ⋙ Drestr n` induced by
  `evalRestrictionNT`.
* `pomOfOpSeq`: the presheaf of modules over `ℕᵒᵖ` given by modules `N n` and transition maps
  `d n : N (n+1) ⟶ (N n)_{A_{n+1}}`.
* `dcompIsoOfQuasiIso`: the comparison isomorphism `(Dcomp n).obj (Q M0) ≅ K n` attached to
  quasi-isomorphisms from the evaluations of a complex `M0` to complexes representing the `K n`.

## Main results

* `exists_derivedObject_of_inverseSystem`: every inverse system `(K n, φ n)` in the derived
  categories `D(A_n)` lifts to
  an object of `D(Mod(ℕ, (A_n)))`.

## Implementation notes

Derived categories are the standard ones, `HasDerivedCategory.standard`. All modules live in the
common universe `max u v`, at least that of the rings, so that a single derived category
accommodates the modules over every `A n` at once.

## References

* [Stacks: Tag 091I](https://stacks.math.columbia.edu/tag/091I)
-/

open CategoryTheory Opposite Localization

namespace Stacks.InverseSystem.ModuleDerivedLift

universe u v

/-- The standard derived category of modules over a ring. -/
noncomputable instance instHasDerivedCategoryModuleCat (R : Type u) [Ring R] :
    HasDerivedCategory (ModuleCat.{max u v} R) := HasDerivedCategory.standard _

/-- The standard derived category of presheaves of modules over `ℕᵒᵖ`. -/
noncomputable instance instHasDerivedCategoryPresheafOfModules (R : ℕᵒᵖ ⥤ RingCat.{u}) :
    HasDerivedCategory (PresheafOfModules.{max u v} R) := HasDerivedCategory.standard _

variable (A : ℕ → Type u) [∀ n, CommRing (A n)] (f : ∀ n, A (n + 1) →+* A n)

/-- The inverse system of rings `(A_n)` as a functor `ℕᵒᵖ ⥤ RingCat`, sending the morphism
`op (n+1) ⟶ op n` to the transition map `f n`. -/
noncomputable def Rfun : ℕᵒᵖ ⥤ RingCat.{u} :=
  Functor.ofOpSequence (X := fun n => RingCat.of (A n)) (fun n => RingCat.ofHom (f n))

/-- The restriction natural transformation between evaluation functors at the level of
modules: evaluation at `n+1` maps to the restriction (along `f n`) of evaluation at `n`.
This encodes the `A_{n+1}`-linear transition maps of an inverse system of modules. -/
noncomputable def evalRestrictionNT (n : ℕ) :
    PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op (n + 1)) ⟶
      PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n) ⋙
          ModuleCat.restrictScalars.{max u v} (f n) := by
  have h : ((Rfun A f).map ((homOfLE (Nat.le_succ n)).op)).hom = f n := by
    unfold Rfun; rw [Functor.ofOpSequence_map_homOfLE_succ]; rfl
  have t := PresheafOfModules.restriction.{0, 0, u, max u v} (Rfun A f)
      ((homOfLE (Nat.le_succ n)).op)
  rw [h] at t
  exact t

/-- The functor `D(Mod(ℕ, (A_n))) ⥤ D(A_n)` induced by the exact evaluation functor at
index `n`. -/
noncomputable def Dcomp (n : ℕ) :
    DerivedCategory (PresheafOfModules.{max u v} (Rfun A f)) ⥤ DerivedCategory
        (ModuleCat.{max u v} (A n)) :=
  (PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapDerivedCategory

/-- The functor `D(A_n) ⥤ D(A_{n+1})` induced by the exact restriction-of-scalars functor along
`f n`. -/
noncomputable def Drestr (n : ℕ) :
    DerivedCategory (ModuleCat.{max u v} (A n)) ⥤ DerivedCategory
        (ModuleCat.{max u v} (A (n + 1))) :=
  (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory

/-- The transition natural transformation on derived categories
`Dcomp (n+1) ⟶ Dcomp n ⋙ Drestr n`.  For an object `M` of `D(Mod(N,(A_n)))`, the component
`(transitionNT n).app M` is the image in `D(A_{n+1})` of the transition map of `M`: the
morphism from the `(n+1)`-st component of `M` to the restriction of the `n`-th component.
It is obtained by lifting, through the localization defining the derived categories, the
module-level restriction natural transformation `evalRestrictionNT`. -/
noncomputable def transitionNT (n : ℕ) :
    Dcomp A f (n + 1) ⟶ Dcomp A f n ⋙ Drestr A f n := by
  unfold Dcomp Drestr
  letI liftcomp : Localization.Lifting (DerivedCategory.Q)
      (HomologicalComplex.quasiIso (PresheafOfModules.{max u v} (Rfun A f)) (ComplexShape.up ℤ))
      (((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)
          ⋙ DerivedCategory.Q) ⋙ (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory)
      ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory) :=
    Localization.Lifting.compRight DerivedCategory.Q _
      ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapHomologicalComplex
          (ComplexShape.up ℤ)
        ⋙ DerivedCategory.Q)
      ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapDerivedCategory)
      ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory)
  exact Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{max u v} (Rfun A f)) (ComplexShape.up ℤ))
    ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
        (op (n + 1))).mapHomologicalComplex _
      ⋙ DerivedCategory.Q)
    (((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapHomologicalComplex _ ⋙
        DerivedCategory.Q)
      ⋙ (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory)
    ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op (n + 1))).mapDerivedCategory)
    ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory)
    ((Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (evalRestrictionNT.{u, v} A f n) (ComplexShape.up ℤ))
        DerivedCategory.Q) ≫
      Functor.whiskerLeft
        ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
            (op n)).mapHomologicalComplex _)
        ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors).inv)

/-- The morphism `φ n`, transported along the isomorphisms `κ`, is a right fraction: there are a
complex `Lc` of `A_{n+1}`-modules, a quasi-isomorphism `σ : Lc ⟶ Kc (n+1)` and a chain map
`τ : Lc ⟶ (Kc n)_{A_{n+1}}` with `Q(τ) = Q(σ) ≫ κ (n+1) ≫ φ n ≫ (Drestr n).map (κ n)⁻¹`, up to
the isomorphism `mapDerivedCategoryFactors` identifying `Drestr n ∘ Q` with `Q ∘ restrictScalars`.
-/
theorem exists_rightFraction_roof
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n) (n : ℕ) :
    ∃ (Lc : CochainComplex (ModuleCat.{max u v} (A (n + 1))) ℤ)
      (σ : Lc ⟶ Kc (n + 1))
      (_ : QuasiIso σ)
      (τ : Lc ⟶ ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
              (Kc n)),
      DerivedCategory.Q.map τ
        = DerivedCategory.Q.map σ ≫ (κ (n + 1)).hom ≫ φ n
            ≫ (Drestr A f n).map (κ n).inv
            ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors).hom.app
                (Kc n) := by
  obtain ⟨Lc, σ, hσ, τ, hfac⟩ :=
    DerivedCategory.right_fac (X := Kc (n + 1))
      (Y := ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
              (Kc n))
      ((κ (n + 1)).hom ≫ φ n ≫ (Drestr A f n).map (κ n).inv
        ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors).hom.app (Kc n))
  refine ⟨Lc, σ, (DerivedCategory.isIso_Q_map_iff_quasiIso _ σ).mp hσ, τ, ?_⟩
  rw [hfac, IsIso.hom_inv_id_assoc]

/-- A complex `M` of `A_n`-modules together with a quasi-isomorphism `ψ : M ⟶ Kc n`. -/
structure TermData091I
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ) (n : ℕ) where
  /-- The complex of `A_n`-modules. -/
  M : CochainComplex (ModuleCat.{max u v} (A n)) ℤ
  /-- The chain map `M ⟶ Kc n`. -/
  ψ : M ⟶ Kc n
  /-- The map `ψ` is a quasi-isomorphism. -/
  hψ : QuasiIso ψ

/-- Given level-`e` data `prev`, level-`(e+1)` data `cur` together with a chain map
`t : cur.M ⟶ (prev.M)_{A_{e+1}}` making the square with `φ e` commute in `D(A_{e+1})`. -/
structure StepResult091I
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n)
    (e : ℕ) (prev : TermData091I A K Kc e) where
  /-- The level-`(e+1)` data. -/
  cur : TermData091I A K Kc (e + 1)
  /-- The chain map from `cur.M` to the restriction of scalars of `prev.M` along `f e`. -/
  t : cur.M ⟶ ((ModuleCat.restrictScalars.{max u v} (f e)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      prev.M
  /-- The image of `t` in `D(A_{e+1})` is compatible with `φ e` under the identifications given
  by `prev.ψ`, `cur.ψ` and `κ`. -/
  sq : DerivedCategory.Q.map t
          ≫ DerivedCategory.Q.map
              (((ModuleCat.restrictScalars.{max u v} (f e)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                  prev.ψ)
          ≫ ((ModuleCat.restrictScalars.{max u v} (f e)).mapDerivedCategoryFactors).inv.app (Kc e)
        = DerivedCategory.Q.map cur.ψ ≫ (κ (e + 1)).hom ≫ φ e
            ≫ (Drestr A f e).map (κ e).inv

/-- A choice of level-`(e+1)` data, transition map and commuting square extending the
level-`e` data `prev`. -/
noncomputable def stepData091I
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n)
    (e : ℕ) (prev : TermData091I A K Kc e) :
    StepResult091I A f K φ Kc κ e prev := by
  let ψeA := ((ModuleCat.restrictScalars.{max u v} (f e)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
      prev.ψ
  haveI : QuasiIso prev.ψ := prev.hψ
  haveI hiψeA : IsIso (DerivedCategory.Q.map ψeA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψeA).mpr inferInstance
  let R := exists_rightFraction_roof A f K φ Kc κ e
  let σ := R.choose_spec.choose
  have hσ : QuasiIso σ := R.choose_spec.choose_spec.choose
  let τ := R.choose_spec.choose_spec.choose_spec.choose
  have hroof : DerivedCategory.Q.map τ
        = DerivedCategory.Q.map σ ≫ (κ (e + 1)).hom ≫ φ e
            ≫ (Drestr A f e).map (κ e).inv
            ≫ ((ModuleCat.restrictScalars.{max u v}
                (f e)).mapDerivedCategoryFactors).hom.app (Kc e) :=
    R.choose_spec.choose_spec.choose_spec.choose_spec
  haveI hiσ : IsIso (DerivedCategory.Q.map σ) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ σ).mpr inferInstance
  let g : DerivedCategory.Q.obj (Kc (e+1)) ⟶
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{max u v} (f e)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj prev.M)
            :=
    inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map τ ≫ inv (DerivedCategory.Q.map ψeA)
  let RF := DerivedCategory.right_fac g
  let Mnext := RF.choose
  let s := RF.choose_spec.choose
  have hs : IsIso (DerivedCategory.Q.map s) := RF.choose_spec.choose_spec.choose
  let h := RF.choose_spec.choose_spec.choose_spec.choose
  have hfac : g = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map h :=
    RF.choose_spec.choose_spec.choose_spec.choose_spec
  haveI : IsIso (DerivedCategory.Q.map s) := hs
  refine ⟨⟨Mnext, s, (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs⟩, h, ?_⟩
  have hh : DerivedCategory.Q.map h
      = DerivedCategory.Q.map s ≫ inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map τ
          ≫ inv (DerivedCategory.Q.map ψeA) := by
    have := hfac
    rw [IsIso.eq_inv_comp] at this
    rw [← this]
  change DerivedCategory.Q.map h
      ≫ DerivedCategory.Q.map ψeA
      ≫ ((ModuleCat.restrictScalars.{max u v} (f e)).mapDerivedCategoryFactors).inv.app (Kc e)
    = DerivedCategory.Q.map s ≫ (κ (e + 1)).hom ≫ φ e ≫ (Drestr A f e).map (κ e).inv
  rw [hh, hroof]
  simp only [Drestr, Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, Category.comp_id]

/-- The level-`n` data defined recursively by `M 0 = Kc 0` and `ψ 0 = 𝟙`, with the successor
given by `stepData091I`. -/
noncomputable def buildData091I
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n) :
    ∀ n, TermData091I A K Kc n
  | 0 => ⟨Kc 0, 𝟙 (Kc 0), inferInstance⟩
  | (e + 1) => (stepData091I A f K φ Kc κ e (buildData091I K φ Kc κ e)).cur

/-- There are complexes `M n` of `A_n`-modules, quasi-isomorphisms `ψ n : M n ⟶ Kc n` and chain
maps `t n : M (n+1) ⟶ (M n)_{A_{n+1}}` such that, in `D(A_{n+1})`, `Q(t n)` followed by the
restriction of `Q(ψ n)` equals `Q(ψ (n+1)) ≫ κ (n+1) ≫ φ n ≫ (Drestr n).map (κ n)⁻¹`, up to the
isomorphism `mapDerivedCategoryFactors`. -/
theorem exists_termwise_resolution
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n) :
    ∃ (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
      (ψ : ∀ n, M n ⟶ Kc n)
      (_ : ∀ n, QuasiIso (ψ n))
      (t : ∀ n, M (n + 1) ⟶
            ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (M n)),
      ∀ n,
        DerivedCategory.Q.map (t n)
            ≫ DerivedCategory.Q.map
                (((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                  (ψ n))
            ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors).inv.app (Kc n)
          = DerivedCategory.Q.map (ψ (n + 1)) ≫ (κ (n + 1)).hom ≫ φ n
              ≫ (Drestr A f n).map (κ n).inv :=
  ⟨fun n => (buildData091I A f K φ Kc κ n).M,
   fun n => (buildData091I A f K φ Kc κ n).ψ,
   fun n => (buildData091I A f K φ Kc κ n).hψ,
   fun n => (stepData091I A f K φ Kc κ n (buildData091I A f K φ Kc κ n)).t,
   fun n => (stepData091I A f K φ Kc κ n (buildData091I A f K φ Kc κ n)).sq⟩

/-! ### Presheaves of modules over `ℕᵒᵖ` from inverse systems

A family of modules `N n` over `A n` with transition maps `d n : N (n+1) ⟶ (N n)_{A_{n+1}}`
defines a presheaf of modules over `Rfun A f`, whose structure map for `op (n+k) ⟶ op n` is the
composite of `k` transition maps. The coherence isomorphisms `restrictScalarsId'` and
`restrictScalarsComp'` act as the identity on underlying types. -/

/-- The composite ring hom telescope `A (n+k) →+* A n`. -/
noncomputable def Fcomp : (n k : ℕ) → (A (n + k) →+* A n)
  | _, 0 => RingHom.id _
  | n, (k+1) => (Fcomp n k).comp (f (n + k))

/-- The composite of the transition maps from `N (n+k)` to `N n`, restricted along
`Fcomp n k`. -/
noncomputable def Tel (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) :
    (n k : ℕ) → (N (n + k) ⟶ (ModuleCat.restrictScalars.{max u v} (Fcomp A f n k)).obj (N n))
  | n, 0 => (ModuleCat.restrictScalarsId' (Fcomp A f n 0) rfl).inv.app (N n)
  | n, (k+1) =>
      d (n + k)
        ≫ (ModuleCat.restrictScalars.{max u v} (f (n+k))).map (Tel N d n k)
        ≫ (ModuleCat.restrictScalarsComp' (f (n+k)) (Fcomp A f n k) (Fcomp A f n (k+1)) rfl).inv.app
            (N n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The ring homomorphism `(Rfun A f).map` of the morphism `op (n+k) ⟶ op n` is the composite
`Fcomp n k`. -/
lemma Rmap_eq_Fcomp (n k : ℕ) :
    ((Rfun A f).map (homOfLE (Nat.le_add_right n k)).op).hom = Fcomp A f n k := by
  induction k with
  | zero =>
    have hid : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [hid]
    have hmap : ((Rfun A f).map (𝟙 (op n))).hom = RingHom.id (A n) := by
      rw [CategoryTheory.Functor.map_id]; rfl
    rw [hmap, Fcomp]
    rfl
  | succ k ih =>
      rw [Fcomp, show (homOfLE (Nat.le_add_right n (k+1)) : n ⟶ n + (k+1))
            = homOfLE (Nat.le_add_right n k) ≫ homOfLE (Nat.le_add_right (n+k) 1) from
              Subsingleton.elim _ _, op_comp, Functor.map_comp, RingCat.hom_comp, ih,
          show ((Rfun A f).map (homOfLE (Nat.le_add_right (n+k) 1)).op).hom = f (n+k) from by
            simp only [Rfun, Functor.ofOpSequence_map_homOfLE_succ]; rfl]

/-- The composite `Tel` with codomain restricted along `(Rfun A f).map` of the morphism
`op (n+k) ⟶ op n`. -/
noncomputable def pomMapN (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n k : ℕ) :
    N (n+k) ⟶
      (ModuleCat.restrictScalars.{max u v} ((Rfun A f).map
          (homOfLE (Nat.le_add_right n k)).op).hom).obj
        (N n) :=
  Tel A f N d n k ≫ eqToHom (by rw [Rmap_eq_Fcomp])

/-- The general structure map `pomOfOpSeq.map` for an arbitrary `g : X ⟶ Y` in `ℕᵒᵖ`. -/
noncomputable def pomMapGen (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n))
    {X Y : ℕᵒᵖ} (g : X ⟶ Y) :
    N (unop X) ⟶ (ModuleCat.restrictScalars.{max u v} ((Rfun A f).map g).hom).obj (N (unop Y)) := by
  rcases X with ⟨m⟩
  rcases Y with ⟨n⟩
  have hnm : n ≤ m := leOfHom g.unop
  rw [show g = (homOfLE hnm).op from Subsingleton.elim _ _]
  clear g
  obtain ⟨k, hk⟩ : Σ' k, n + k = m := ⟨m - n, Nat.add_sub_cancel' hnm⟩
  subst hk
  exact pomMapN A f N d n k

/-- An `Eq.rec` over a dependent function type in `ℕ`, applied to a proof, is `HEq` to the body
applied to any proof. -/
private theorem heq_rec_pi_apply {n0 a b : ℕ} (h : a = b) {M : (x : ℕ) → (n0 ≤ x) → Sort*}
    (body : (hnm : n0 ≤ a) → M a hnm) (lp : n0 ≤ b) (vb : M b lp)
    (hv : ∀ x : n0 ≤ a, HEq (body x) vb) :
    HEq ((h ▸ body : (hnm : n0 ≤ b) → M b hnm) lp) vb := by
  subst h
  exact hv lp

/-- `pomMapGen` on the morphism `op (n+k) ⟶ op n` is `pomMapN n k`. -/
lemma pomMapGen_canonical (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n k : ℕ) :
    pomMapGen A f N d (homOfLE (Nat.le_add_right n k)).op = pomMapN A f N d n k := by
  simp only [pomMapGen, Eq.mpr]
  apply eq_of_heq
  apply heq_rec_pi_apply (n0 := n)
    (M := fun x hnm => N x ⟶ (ModuleCat.restrictScalars
      ((Rfun A f).map (homOfLE hnm).op).hom).obj (N n))
  intro x
  congr 1
  omega

/-- Carrier action of `Tel` at gap `0`: the identity. -/
lemma Tel_zero_apply (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n : ℕ)
    (x : N (n + 0)) :
    (ConcreteCategory.hom (Tel A f N d n 0)) x = x := by
  rw [Tel]
  exact ModuleCat.restrictScalarsId'App_inv_apply (Fcomp A f n 0) rfl (N n) x

/-- Carrier action of `Tel` at a successor gap: `d` followed by `Tel` at the smaller gap. -/
lemma Tel_succ_apply (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n k : ℕ)
    (x : N (n + (k + 1))) :
    (ConcreteCategory.hom (Tel A f N d n (k+1))) x
      = (ConcreteCategory.hom (Tel A f N d n k)) ((ConcreteCategory.hom (d (n+k))) x) := by
  conv_lhs => rw [Tel]
  rw [ModuleCat.restrictScalarsComp']
  simp only [ModuleCat.comp_apply, NatIso.ofComponents_inv_app]
  rfl

/-- `d` commutes with a `cast` along an equality of indices. -/
lemma d_cast (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) {i j : ℕ}
        (hij : i = j)
    (x : N (i + 1)) :
    (ConcreteCategory.hom (d j)) (cast (by rw [hij]) x)
      = cast (by rw [hij]) ((ConcreteCategory.hom (d i)) x) := by
  subst hij
  rfl

/-- Equal indices give equal carriers of `N`. -/
lemma carrierN_eq (N : ∀ n, ModuleCat.{max u v} (A n)) {i j : ℕ} (h : i = j) :
    (↑(N i) : Type (max u v)) = ↑(N j) :=
  h ▸ rfl

/-- Carrier-level telescope composition law: the fold from `n+b+a` to `n` splits at `n+b`. -/
lemma Tel_fold_comp (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n b : ℕ) :
    ∀ (a : ℕ) (x : N (n + b + a)),
      (ConcreteCategory.hom (Tel A f N d n (b + a))) (cast (by rw [Nat.add_assoc]) x)
        = (ConcreteCategory.hom (Tel A f N d n b))
            ((ConcreteCategory.hom (Tel A f N d (n + b) a)) x) := by
  intro a
  induction a with
  | zero =>
      intro x
      rw [Tel_zero_apply]
      rfl
  | succ a ih =>
      intro x
      rw [Tel_succ_apply A f N d (n + b) a x]
      rw [← ih (ConcreteCategory.hom (d (n + b + a)) x)]
      have hL : (ConcreteCategory.hom (Tel A f N d n (b + (a + 1)))) (cast (by rw [Nat.add_assoc])
          x)
          = (ConcreteCategory.hom (Tel A f N d n (b + a)))
              ((ConcreteCategory.hom (d (n + (b + a))))
                (cast (carrierN_eq A N (i := n + b + (a + 1)) (j := n + (b + a) + 1)
                  (by omega)) x)) :=
        Tel_succ_apply A f N d n (b + a)
          (cast (carrierN_eq A N (i := n + b + (a + 1)) (j := n + (b + a) + 1) (by omega)) x)
      rw [hL]
      congr 1
      exact d_cast A f N d (Nat.add_assoc n b a) x

/-- `eqToHom` between `ModuleCat` objects acts as the identity on carriers. -/
lemma eqToHom_carrier {R : Type u} [Ring R] {X Y : ModuleCat.{max u v} R} (hxy : X = Y) (z : X) :
    (ConcreteCategory.hom (eqToHom hxy)) z = cast (by rw [hxy]) z := by
  subst hxy; simp

/-- Carrier-level value of `pomMapGen` on the canonical `homOfLE`-morphism, with the source
index given via an explicit equation `m = n + k` (so we may use it at `m = n+b+a`). -/
lemma pomMapGen_homOfLE_apply (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) {n m k : ℕ}
    (hmk : m = n + k) (h : n ≤ m) (x : N m) :
    (ConcreteCategory.hom (pomMapGen A f N d (homOfLE h).op)) x
      = (ConcreteCategory.hom (Tel A f N d n k)) (cast (carrierN_eq A N hmk) x) := by
  subst hmk
  rw [show (homOfLE h).op = (homOfLE (Nat.le_add_right n k)).op from Subsingleton.elim _ _]
  rw [pomMapGen_canonical, pomMapN]
  simp only [ModuleCat.comp_apply, cast_eq]
  generalize (ConcreteCategory.hom (Tel A f N d n k)) x = z
  rw [eqToHom_carrier _ z]
  simp

/-- Carrier value of `pomMapN`: `Tel` followed by the carrier-trivial `eqToHom`. -/
lemma pomMapN_apply (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n k : ℕ)
    (z : N (n + k)) :
    (ConcreteCategory.hom (pomMapN A f N d n k)) z
      = cast (by rw [Rmap_eq_Fcomp]) ((ConcreteCategory.hom (Tel A f N d n k)) z) := by
  rw [pomMapN, ModuleCat.comp_apply, eqToHom_carrier]

/-- `pomMapGen` on any morphism `op (n+k) ⟶ op n` acts on carriers as `Tel n k`. -/
private theorem pomMapGen_apply_op (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) {n k : ℕ}
    (g : op (n + k) ⟶ op n) (x : N (n + k)) :
    (ConcreteCategory.hom (pomMapGen A f N d g)) x
      = (ConcreteCategory.hom (Tel A f N d n k)) x := by
  rw [show g = (homOfLE (Nat.le_add_right n k)).op from Subsingleton.elim _ _,
    pomMapGen_canonical, pomMapN_apply]
  rfl

/-- `pomMapGen` sends an identity morphism to the inverse of the coherence isomorphism
`restrictScalarsId'`. -/
lemma pomMapGen_id (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (X : ℕᵒᵖ) :
    pomMapGen A f N d (𝟙 X)
      = (ModuleCat.restrictScalarsId' ((Rfun A f).map (𝟙 X)).hom (by simp)).inv.app
          (N (unop X)) := by
  rcases X with ⟨n⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine (pomMapGen_apply_op A f N d (k := 0) (𝟙 _) x).trans ?_
  rw [Tel_zero_apply, ModuleCat.restrictScalarsId']
  simp only [NatIso.ofComponents_inv_app]
  exact (ModuleCat.restrictScalarsId'App_inv_apply _ _ _ _).symm

/-- `pomMapGen` sends a composite `g₁ ≫ g₂` to `pomMapGen g₁`, followed by the restriction of
`pomMapGen g₂` and the inverse of the coherence isomorphism `restrictScalarsComp'`. -/
lemma pomMapGen_comp (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n))
    {X Y Z : ℕᵒᵖ} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) :
    pomMapGen A f N d (g₁ ≫ g₂)
      = pomMapGen A f N d g₁
        ≫ (ModuleCat.restrictScalars.{max u v} ((Rfun A f).map g₁).hom).map (pomMapGen A f N d g₂)
        ≫ (ModuleCat.restrictScalarsComp' ((Rfun A f).map g₁).hom ((Rfun A f).map g₂).hom
            ((Rfun A f).map (g₁ ≫ g₂)).hom (by rw [Functor.map_comp]; rfl)).inv.app
              (N (unop Z)) := by
  rcases X with ⟨l⟩
  rcases Y with ⟨m⟩
  rcases Z with ⟨n⟩
  have hml : m ≤ l := leOfHom g₁.unop
  have hnm : n ≤ m := leOfHom g₂.unop
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hml
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [show g₁ = (homOfLE (Nat.le_add_right (n+b) a)).op from Subsingleton.elim _ _]
  rw [show g₂ = (homOfLE (Nat.le_add_right n b)).op from Subsingleton.elim _ _]
  rw [pomMapGen_canonical, pomMapGen_canonical]
  have hcomp : pomMapGen A f N d
        ((homOfLE (Nat.le_add_right (n+b) a)).op ≫ (homOfLE (Nat.le_add_right n b)).op)
      = pomMapGen A f N d
          (homOfLE (le_trans (Nat.le_add_right n b) (Nat.le_add_right (n+b) a))).op := by
    rw [← op_comp]
    rfl
  rw [hcomp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [pomMapGen_homOfLE_apply A f N d (show n + b + a = n + (b + a) from by omega)]
  rw [Tel_fold_comp A f N d n b a x]
  simp only [unop_op]
  rw [ModuleCat.comp_apply]
  change (ConcreteCategory.hom (Tel A f N d n b)) ((ConcreteCategory.hom (Tel A f N d (n + b) a)) x)
      = (ConcreteCategory.hom (pomMapN A f N d n b))
          ((ConcreteCategory.hom (pomMapN A f N d (n + b) a)) x)
  rw [pomMapN_apply, pomMapN_apply]
  simp only [cast_eq]

/-- The presheaf of modules over `ℕᵒᵖ` whose value at `op n` is `N n` and whose structure map
for `op (n+1) ⟶ op n` is `d n`. -/
noncomputable def pomOfOpSeq (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) :
    PresheafOfModules.{max u v} (Rfun A f) where
  obj X := N (unop X)
  map g := pomMapGen A f N d g
  map_id X := pomMapGen_id A f N d X
  map_comp g₁ g₂ := pomMapGen_comp A f N d g₁ g₂

/-- Evaluation of `pomOfOpSeq` at `op n` is `N n`. -/
@[simp] lemma pomOfOpSeq_obj (N : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n)) (n : ℕ) :
    (pomOfOpSeq A f N d).obj (op n) = N n := rfl

/-- A family `g n : N n ⟶ N' n` commuting with the transition maps `d` and `d'` commutes with
the structure maps of `pomOfOpSeq` for every morphism of `ℕᵒᵖ`. -/
lemma pomHomOfOpSeq_naturality (N N' : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n))
    (d' : ∀ n, N' (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N' n))
    (g : ∀ n, N n ⟶ N' n)
    (hg : ∀ n, d n ≫ (ModuleCat.restrictScalars.{max u v} (f n)).map (g n) = g (n + 1) ≫ d' n)
    {X Y : ℕᵒᵖ} (φ : X ⟶ Y) :
    (pomOfOpSeq A f N d).map φ
        ≫ (ModuleCat.restrictScalars.{max u v} ((Rfun A f).map φ).hom).map (g (unop Y))
      = g (unop X) ≫ (pomOfOpSeq A f N' d').map φ := by
  rcases X with ⟨m⟩
  rcases Y with ⟨n⟩
  have hnm : n ≤ m := leOfHom φ.unop
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hgc : ∀ (j : ℕ) (y : N (j + 1)),
      (ConcreteCategory.hom (g j)) ((ConcreteCategory.hom (d j)) y)
        = (ConcreteCategory.hom (d' j)) ((ConcreteCategory.hom (g (j + 1))) y) := by
    intro j y
    have := hg j
    apply_fun (fun m => (ConcreteCategory.hom m) y) at this
    simpa [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply] using this
  have hTel : ∀ (j : ℕ) (x : N (n + j)),
      (ConcreteCategory.hom (g n)) ((ConcreteCategory.hom (Tel A f N d n j)) x)
        = (ConcreteCategory.hom (Tel A f N' d' n j)) ((ConcreteCategory.hom (g (n + j))) x) := by
    intro j
    induction j with
    | zero =>
        intro x
        rw [Tel_zero_apply, Tel_zero_apply]
        rfl
    | succ j ih =>
        intro x
        rw [Tel_succ_apply, Tel_succ_apply]
        rw [ih ((ConcreteCategory.hom (d (n + j))) x)]
        rw [hgc (n + j) x]
        rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (ConcreteCategory.hom ((ModuleCat.restrictScalars.{max u v}
      ((Rfun A f).map φ).hom).map (g n)))
        ((ConcreteCategory.hom (pomMapGen A f N d φ)) x)
      = (ConcreteCategory.hom (pomMapGen A f N' d' φ))
          ((ConcreteCategory.hom (g (n + k))) x)
  rw [ModuleCat.restrictScalars.map_apply, pomMapGen_apply_op, pomMapGen_apply_op]
  exact hTel k x

/-- The morphism `pomOfOpSeq N d ⟶ pomOfOpSeq N' d'` whose component at `op n` is `g n`, for a
family `g` commuting with the transition maps. -/
noncomputable def pomHomOfOpSeq (N N' : ∀ n, ModuleCat.{max u v} (A n))
    (d : ∀ n, N (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N n))
    (d' : ∀ n, N' (n + 1) ⟶ (ModuleCat.restrictScalars.{max u v} (f n)).obj (N' n))
    (g : ∀ n, N n ⟶ N' n)
    (hg : ∀ n, d n ≫ (ModuleCat.restrictScalars.{max u v} (f n)).map (g n) = g (n + 1) ≫ d' n) :
    pomOfOpSeq A f N d ⟶ pomOfOpSeq A f N' d' where
  app X := g (unop X)
  naturality φ := pomHomOfOpSeq_naturality A f N N' d d' g hg φ

/-- The morphisms of presheaves of modules induced by consecutive differentials of the
complexes `M n` compose to zero. -/
lemma pomOfOpSeq_dd (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n))
    (i : ℤ) :
    pomHomOfOpSeq A f (fun n => (M n).X i) (fun n => (M n).X (i + 1))
        (fun n => (t n).f i) (fun n => (t n).f (i + 1))
        (fun n => (M n).d i (i + 1)) (fun n => by simpa using (t n).comm i (i + 1))
      ≫ pomHomOfOpSeq A f (fun n => (M n).X (i + 1)) (fun n => (M n).X (i + 1 + 1))
          (fun n => (t n).f (i + 1)) (fun n => (t n).f (i + 1 + 1))
          (fun n => (M n).d (i + 1) (i + 1 + 1))
          (fun n => by simpa using (t n).comm (i + 1) (i + 1 + 1))
      = 0 :=
  PresheafOfModules.Hom.ext <| funext fun ⟨n⟩ => (M n).d_comp_d i (i + 1) (i + 1 + 1)

/-- The complex of presheaves of modules over `ℕᵒᵖ` whose degree-`i` term is `pomOfOpSeq` of
the modules `(M n).X i` with transition maps `(t n).f i`, and whose differentials are induced by
those of the `M n`. -/
noncomputable def pomComplexOf (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n)) :
    CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ :=
  CochainComplex.of
    (fun i => pomOfOpSeq A f (fun n => (M n).X i) (fun n => (t n).f i))
    (fun i => pomHomOfOpSeq A f (fun n => (M n).X i) (fun n => (M n).X (i + 1))
        (fun n => (t n).f i) (fun n => (t n).f (i + 1))
        (fun n => (M n).d i (i + 1)) (fun n => by simpa using (t n).comm i (i + 1)))
    (fun i => pomOfOpSeq_dd A f M t i)

/-- Evaluation of `pomComplexOf M t` at `n` is isomorphic to `M n`. -/
noncomputable def pomComplexOfEvalIso (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n))
    (n : ℕ) :
    ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (pomComplexOf A f M t) ≅ M n := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => Iso.refl _) ?_
  intro i j hij
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  obtain rfl : i + 1 = j := hij
  simp only [Functor.mapHomologicalComplex_obj_d, PresheafOfModules.evaluation_map,
    pomComplexOf, CochainComplex.of_d]
  rfl

/-- Under the isomorphisms `pomComplexOfEvalIso`, the transition map of `pomComplexOf M t` from
index `n+1` to index `n` is `t n`. -/
lemma pomComplexOfEvalIso_naturality (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n))
    (n : ℕ) :
    (NatTrans.mapHomologicalComplex (evalRestrictionNT.{u, v} A f n) (ComplexShape.up ℤ)).app
          (pomComplexOf A f M t)
        ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (pomComplexOfEvalIso A f M t n).hom
      = (pomComplexOfEvalIso A f M t (n + 1)).hom ≫ t n := by
  apply HomologicalComplex.hom_ext
  intro i
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  simp only [NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
    pomComplexOfEvalIso, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hh : ((Rfun A f).map ((homOfLE (Nat.le_succ n)).op)).hom = f n := by
    unfold Rfun; rw [Functor.ofOpSequence_map_homOfLE_succ]; rfl
  have hheq : HEq (evalRestrictionNT.{u, v} A f n)
        (PresheafOfModules.restriction.{0, 0, u, max u v} (Rfun A f)
            ((homOfLE (Nat.le_succ n)).op)) := by
    unfold evalRestrictionNT
    generalize_proofs hp
    exact cast_heq _ _
  have congr_helper : ∀ {R : Type u} [Ring R]
      {MX MY₁ MY₂ : ModuleCat.{max u v} R}
      (g₁ : MX ⟶ MY₁) (g₂ : MX ⟶ MY₂) (_ : MY₁ = MY₂) (_ : HEq g₁ g₂) (y : MX),
      HEq (ModuleCat.Hom.hom g₁ y) (ModuleCat.Hom.hom g₂ y) := by
    intro R _ MX MY₁ MY₂ g₁ g₂ hY hg y
    subst hY; rw [eq_of_heq hg]
  have happ : HEq ((evalRestrictionNT.{u, v} A f n).app ((pomComplexOf A f M t).X i))
      ((PresheafOfModules.restriction.{0, 0, u, max u v} (Rfun A f)
          ((homOfLE (Nat.le_succ n)).op)).app
        ((pomComplexOf A f M t).X i)) := by
    congr 1
    rw [hh]
  rw [PresheafOfModules.restriction_app] at happ
  have hY : (ModuleCat.restrictScalars.{max u v} (f n)).obj
      (((pomComplexOf A f M t).X i).obj (op n))
      = (ModuleCat.restrictScalars.{max u v} ((Rfun A f).map
          ((homOfLE (Nat.le_succ n)).op)).hom).obj
          (((pomComplexOf A f M t).X i).obj (op n)) := by
    rw [hh]
  have hAct : (ModuleCat.Hom.hom ((evalRestrictionNT.{u, v} A f n).app
      ((pomComplexOf A f M t).X i))) x
      = (ModuleCat.Hom.hom (((pomComplexOf A f M t).X i).map ((homOfLE (Nat.le_succ n)).op))) x :=
    eq_of_heq (congr_helper _ _ hY happ x)
  change (ModuleCat.Hom.hom ((evalRestrictionNT.{u, v} A f n).app ((pomComplexOf A f M t).X i))) x
      = (ModuleCat.Hom.hom ((t n).f i)) x
  rw [hAct]
  change (ConcreteCategory.hom
        (pomMapGen A f (fun n => (M n).X i) (fun n => (t n).f i) ((homOfLE (Nat.le_succ n)).op))) x
      = (ConcreteCategory.hom ((t n).f i)) x
  rw [pomMapGen_apply_op A f _ _ (k := 1), Tel_succ_apply, Tel_zero_apply]
  rfl

/-- The `Lifting.iso` of the evaluation functor's derived lift is, definitionally, the
`mapDerivedCategoryFactors` isomorphism. -/
theorem evalLiftingIso_eq (n : ℕ) :
    Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (PresheafOfModules.{max u v} (Rfun A f)) (ComplexShape.up ℤ))
        ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapHomologicalComplex
            (ComplexShape.up ℤ)
          ⋙ DerivedCategory.Q)
        (PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op n)).mapDerivedCategory
      = (PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
          (op n)).mapDerivedCategoryFactors :=
  rfl

/-- If a complex `M0` of presheaves of modules has evaluations isomorphic to `M n` via `ev n`,
under which its transition maps are the chain maps `t n`, then in `D(A_{n+1})` the transition
morphism `transitionNT n` of `Q M0` corresponds to `Q(t n)`. -/
theorem transitionNT_app_comp_eq
    (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n))
    (M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ)
    (ev : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
        (op n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M0 ≅ M n)
    (hmod : ∀ n,
        (NatTrans.mapHomologicalComplex (evalRestrictionNT.{u, v} A f n) (ComplexShape.up ℤ)).app M0
            ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                (ev n).hom
          = (ev (n + 1)).hom ≫ t n)
    (n : ℕ) :
        (transitionNT A f n).app (DerivedCategory.Q.obj M0)
            ≫ (Drestr A f n).map
                ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
                    (op n)).mapDerivedCategoryFactors.hom.app
                    M0
                  ≫ DerivedCategory.Q.map (ev n).hom)
          = ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op (n +
              1))).mapDerivedCategoryFactors.hom.app M0
                ≫ DerivedCategory.Q.map (ev (n + 1)).hom)
              ≫ DerivedCategory.Q.map (t n)
              ≫ ((ModuleCat.restrictScalars.{max u v}
                  (f n)).mapDerivedCategoryFactors).inv.app (M n) := by
  unfold transitionNT
  simp only [id_eq, Localization.liftNatTrans_app, Localization.Lifting.compRight_iso,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app,
     Functor.map_comp, Category.assoc]
  rw [evalLiftingIso_eq, evalLiftingIso_eq]
  unfold Drestr
  rw [← Functor.map_comp_assoc ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory)
        ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
            (op n)).mapDerivedCategoryFactors.inv.app M0)
        ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
            (op n)).mapDerivedCategoryFactors.hom.app M0),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.comp_map DerivedCategory.Q
        ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory) (ev n).hom,
      ← (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors.inv.naturality
          (ev n).hom]
  have hQ := congrArg DerivedCategory.Q.map (hmod n)
  simp only [Functor.map_comp] at hQ
  simp only [Functor.comp_map]
  rw [← Category.assoc (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (evalRestrictionNT.{u, v} A f n) (ComplexShape.up ℤ)).app M0)), hQ, Category.assoc]

/-- An inverse system of complexes `(M n, t n)` is realized by a complex `M0` of presheaves of
modules over `ℕᵒᵖ` with isomorphisms `ev n` from its evaluations to `M n`, under which the
derived transition morphism `transitionNT n` of `Q M0` corresponds to `Q(t n)`. -/
theorem exists_presheafOfModules_complex_of_inverseSystem
    (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n)) :
    ∃ (M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ)
      (ev : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
          (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M0 ≅ M n),
      ∀ n,
        (transitionNT A f n).app (DerivedCategory.Q.obj M0)
            ≫ (Drestr A f n).map
                ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
                    (op n)).mapDerivedCategoryFactors.hom.app
                    M0
                  ≫ DerivedCategory.Q.map (ev n).hom)
          = ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op (n +
              1))).mapDerivedCategoryFactors.hom.app M0
                ≫ DerivedCategory.Q.map (ev (n + 1)).hom)
              ≫ DerivedCategory.Q.map (t n)
              ≫ ((ModuleCat.restrictScalars.{max u v}
                  (f n)).mapDerivedCategoryFactors).inv.app (M n) :=
  ⟨pomComplexOf A f M t, pomComplexOfEvalIso A f M t, fun n =>
    transitionNT_app_comp_eq A f M t (pomComplexOf A f M t) (pomComplexOfEvalIso A f M t)
      (pomComplexOfEvalIso_naturality A f M t) n⟩

/-- The comparison isomorphism `(Dcomp n).obj (Q M0) ≅ K n` attached to quasi-isomorphisms
`ψc n` from the evaluation of `M0` at `n` to `Kc n` and isomorphisms `κ n : Q(Kc n) ≅ K n`. -/
noncomputable def dcompIsoOfQuasiIso
    {K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n))}
    {Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ}
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n)
    {M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ}
    (ψc : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
        (op n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M0 ⟶ Kc n)
    (hψc : ∀ n, QuasiIso (ψc n)) (n : ℕ) :
    (Dcomp A f n).obj (DerivedCategory.Q.obj M0) ≅ K n :=
  haveI : IsIso (DerivedCategory.Q.map (ψc n)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (ψc n)).mpr (hψc n)
  ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
      (op n)).mapDerivedCategoryFactors.app M0)
    ≪≫ asIso (DerivedCategory.Q.map (ψc n)) ≪≫ κ n

/-- The forward map of `dcompIsoOfQuasiIso` is the `mapDerivedCategoryFactors` comparison,
followed by `Q(ψc n)` and `κ n`. -/
@[simp]
lemma dcompIsoOfQuasiIso_hom
    {K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n))}
    {Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ}
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n)
    {M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ}
    (ψc : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
        (op n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M0 ⟶ Kc n)
    (hψc : ∀ n, QuasiIso (ψc n)) (n : ℕ) :
    (dcompIsoOfQuasiIso A f κ ψc hψc n).hom
      = (PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
            (op n)).mapDerivedCategoryFactors.hom.app M0
          ≫ DerivedCategory.Q.map (ψc n) ≫ (κ n).hom :=
  rfl

/-- An isomorphism of complexes followed by a quasi-isomorphism is a quasi-isomorphism. -/
lemma quasiIso_evalIso_hom_comp
    {Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ}
    {M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ}
    (ψ : ∀ n, M n ⟶ Kc n) (hψ : ∀ n, QuasiIso (ψ n))
    {M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ}
    (ev : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
        (op n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj M0 ≅ M n) (n : ℕ) :
    QuasiIso ((ev n).hom ≫ ψ n) := by
  have : QuasiIso (ψ n) := hψ n
  have : IsIso (ev n).hom := (ev n).isIso_hom
  have : QuasiIso (ev n).hom := inferInstance
  exact quasiIso_comp (ev n).hom (ψ n)

/-- Given `M0` and `ev` as in `exists_presheafOfModules_complex_of_inverseSystem` and data `(M n, ψ
  n, t n)` as in
`exists_termwise_resolution`, the isomorphisms `Q(ψc n)` for `ψc n = (ev n).hom ≫ ψ n`, composed
  with
`κ n`, make the transition squares with `φ n` commute in `D(A_{n+1})`. -/
theorem transitionNT_app_dcompIso_comm
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n)
    (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (ψ : ∀ n, M n ⟶ Kc n)
    (hψ : ∀ n, QuasiIso (ψ n))
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n))
    (hsq : ∀ n,
        DerivedCategory.Q.map (t n)
            ≫ DerivedCategory.Q.map
                (((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                  (ψ n))
            ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors).inv.app (Kc n)
          = DerivedCategory.Q.map (ψ (n + 1)) ≫ (κ (n + 1)).hom ≫ φ n
              ≫ (Drestr A f n).map (κ n).inv)
    (M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ)
    (ev : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
        (op n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M0 ≅ M n)
    (hcompat : ∀ n,
        (transitionNT A f n).app (DerivedCategory.Q.obj M0)
            ≫ (Drestr A f n).map
                ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
                    (op n)).mapDerivedCategoryFactors.hom.app
                    M0
                  ≫ DerivedCategory.Q.map (ev n).hom)
          = ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f) (op (n +
              1))).mapDerivedCategoryFactors.hom.app M0
                ≫ DerivedCategory.Q.map (ev (n + 1)).hom)
              ≫ DerivedCategory.Q.map (t n)
              ≫ ((ModuleCat.restrictScalars.{max u v}
                  (f n)).mapDerivedCategoryFactors).inv.app (M n))
    (n : ℕ) :
    (transitionNT A f n).app (DerivedCategory.Q.obj M0)
        ≫ (Drestr A f n).map (dcompIsoOfQuasiIso A f κ (fun n => (ev n).hom ≫ ψ n)
            (quasiIso_evalIso_hom_comp A f ψ hψ ev) n).hom
      = (dcompIsoOfQuasiIso A f κ (fun n => (ev n).hom ≫ ψ n)
          (quasiIso_evalIso_hom_comp A f ψ hψ ev) (n + 1)).hom ≫ φ n := by
  simp only [dcompIsoOfQuasiIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (Drestr A f n)
        ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
            (op n)).mapDerivedCategoryFactors.hom.app M0)
        (DerivedCategory.Q.map (ev n).hom)]
  rw [reassoc_of% (hcompat n)]
  unfold Drestr
  rw [← Functor.comp_map DerivedCategory.Q
        ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategory) (ψ n),
      ← (ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors.inv.naturality_assoc
          (ψ n)]
  rw [Functor.comp_map ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
      (ComplexShape.up ℤ))
        DerivedCategory.Q (ψ n)]
  rw [reassoc_of% (hsq n)]
  show _ = _
  unfold Drestr
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Data `(M n, ψ n, t n)` as in `exists_termwise_resolution` assemble to a complex `M0` of
  presheaves
of modules over `ℕᵒᵖ` with quasi-isomorphisms `ψc n` from the evaluation of `M0` at `n` to `Kc n`
making the transition squares with `φ n` commute in `D(A_{n+1})`. -/
theorem exists_complex_presheafOfModules_quasiIso
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n)
    (M : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (ψ : ∀ n, M n ⟶ Kc n)
    (hψ : ∀ n, QuasiIso (ψ n))
    (t : ∀ n, M (n + 1) ⟶
          ((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj (M n))
    (hsq : ∀ n,
        DerivedCategory.Q.map (t n)
            ≫ DerivedCategory.Q.map
                (((ModuleCat.restrictScalars.{max u v} (f n)).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map
                  (ψ n))
            ≫ ((ModuleCat.restrictScalars.{max u v} (f n)).mapDerivedCategoryFactors).inv.app (Kc n)
          = DerivedCategory.Q.map (ψ (n + 1)) ≫ (κ (n + 1)).hom ≫ φ n
              ≫ (Drestr A f n).map (κ n).inv) :
    ∃ (M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ)
      (ψc : ∀ n, ((PresheafOfModules.evaluation.{max u v, 0, 0, u} (Rfun A f)
          (op n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M0 ⟶ Kc n)
      (hψc : ∀ n, QuasiIso (ψc n)),
      ∀ n, (transitionNT A f n).app (DerivedCategory.Q.obj M0)
          ≫ (Drestr A f n).map (dcompIsoOfQuasiIso A f κ ψc hψc n).hom
        = (dcompIsoOfQuasiIso A f κ ψc hψc (n + 1)).hom ≫ φ n := by
  obtain ⟨M0, ev, hcompat⟩ := exists_presheafOfModules_complex_of_inverseSystem A f M t
  exact ⟨M0, fun n => (ev n).hom ≫ ψ n, quasiIso_evalIso_hom_comp A f ψ hψ ev,
    fun n => transitionNT_app_dcompIso_comm A f K φ Kc κ M ψ hψ t hsq M0 ev hcompat n⟩

/-- Given complexes `Kc n` with isomorphisms `κ n : Q(Kc n) ≅ K n`, there are a complex `M0` of
presheaves of modules over `ℕᵒᵖ` and isomorphisms `ξ n : (Dcomp n).obj (Q M0) ≅ K n` with
`(transitionNT n).app (Q M0) ≫ (Drestr n).map (ξ n).hom = (ξ (n+1)).hom ≫ φ n`. -/
theorem exists_presheafOfModulesComplex_iso_dcomp
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n))
    (Kc : ∀ n, CochainComplex (ModuleCat.{max u v} (A n)) ℤ)
    (κ : ∀ n, DerivedCategory.Q.obj (Kc n) ≅ K n) :
    ∃ (M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ)
      (ξ : ∀ n, (Dcomp A f n).obj (DerivedCategory.Q.obj M0) ≅ K n),
      ∀ n, (transitionNT A f n).app (DerivedCategory.Q.obj M0)
          ≫ (Drestr A f n).map (ξ n).hom
        = (ξ (n + 1)).hom ≫ φ n := by
  obtain ⟨M, ψ, hψ, t, hsq⟩ := exists_termwise_resolution A f K φ Kc κ
  obtain ⟨M0, ψc, hψc, hsq'⟩ := exists_complex_presheafOfModules_quasiIso A f K φ Kc κ M ψ hψ t hsq
  exact ⟨M0, dcompIsoOfQuasiIso A f κ ψc hψc, hsq'⟩

/-- The object of `exists_derivedObject_of_inverseSystem` may be taken to be `Q M0` for a complex
  `M0` of presheaves of
modules over `ℕᵒᵖ`: there are isomorphisms `ξ n : (Dcomp n).obj (Q M0) ≅ K n` with
`(transitionNT n).app (Q M0) ≫ (Drestr n).map (ξ n).hom = (ξ (n+1)).hom ≫ φ n`. -/
theorem exists_presheafComplex_iso_system
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n)) :
    ∃ (M0 : CochainComplex (PresheafOfModules.{max u v} (Rfun A f)) ℤ)
      (ξ : ∀ n, (Dcomp A f n).obj (DerivedCategory.Q.obj M0) ≅ K n),
      ∀ n, (transitionNT A f n).app (DerivedCategory.Q.obj M0)
          ≫ (Drestr A f n).map (ξ n).hom
        = (ξ (n + 1)).hom ≫ φ n :=
  exists_presheafOfModulesComplex_iso_dcomp A f K φ
    (fun n => DerivedCategory.Q.objPreimage (K n))
    (fun n => DerivedCategory.Q.objObjPreimageIso (K n))

/-- **Stacks 091I**.
Let `(A_n)` be an inverse system of commutative rings with transition maps
`f n : A_{n+1} → A_n`, let `K n` be objects of `D(A_n)`, and let
`φ n : K (n+1) ⟶ (Drestr n).obj (K n)` be morphisms in `D(A_{n+1})`. Then there are an object
`M` of `D(Mod(ℕ, (A_n)))` and isomorphisms `ψ n : (Dcomp n).obj M ≅ K n` in `D(A_n)` such that
`(transitionNT n).app M ≫ (Drestr n).map (ψ n).hom = (ψ (n+1)).hom ≫ φ n`. -/
@[stacks 091I]
theorem exists_derivedObject_of_inverseSystem
    (K : ∀ n, DerivedCategory (ModuleCat.{max u v} (A n)))
    (φ : ∀ n, K (n + 1) ⟶ (Drestr A f n).obj (K n)) :
    ∃ (M : DerivedCategory (PresheafOfModules.{max u v} (Rfun A f)))
      (ψ : ∀ n, (Dcomp A f n).obj M ≅ K n),
      ∀ n, (transitionNT A f n).app M ≫ (Drestr A f n).map (ψ n).hom
        = (ψ (n + 1)).hom ≫ φ n := by
  obtain ⟨M0, ξ, hξ⟩ := exists_presheafComplex_iso_system A f K φ
  exact ⟨DerivedCategory.Q.obj M0, ξ, hξ⟩

end Stacks.InverseSystem.ModuleDerivedLift
