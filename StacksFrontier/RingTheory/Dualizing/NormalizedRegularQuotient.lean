module

public import Mathlib.RingTheory.LocalRing.Quotient
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.RingTheory.Dualizing.NormalizedFiniteMap

/-!
# Normalized dualizing complexes and a regular element

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A`, and let `f` be a
nonzerodivisor in the maximal ideal of `A`. Then `B = A ⧸ (f)` has a normalized dualizing complex
`ω_B = RHom_A(B, ω_A)`, and over `A` the three complexes sit in a distinguished triangle
`ω_B → ω_A → ω_A → ω_B[1]` whose middle map is multiplication by `f`. This is [Stacks, Tag 0A7T].

That `ω_B` is normalized dualizing is [Stacks, Tag 0AX1]
(`Dualizing.isNormalizedDualizingComplex_derivedHom`), a surjection of Noetherian local rings
being a finite local homomorphism. The triangle comes from a short exact sequence of complexes:
choosing a bounded complex of injectives `I` representing `ω_A`, the counit of the
restriction/coextension adjunction is a degreewise injection `Hom_A(B, I) → I` whose cokernel is
computed by multiplication by `f`. Surjectivity of `f • -` on each `I n` is Baer's criterion for
the injective module `I n` against the injection `f • - : A → A`, and the image of the counit in
degree `n` is exactly the `f`-torsion of `I n`, since an `A`-linear map out of `A ⧸ (f)` is
determined by its value at `1` and may be prescribed there by any element killed by `f`.

Matching the first term of that triangle with `ω_B` means identifying the total right derived
functor `RHom_A(B, -)` with the termwise coextension `Hom_A(B, I)`, which is legitimate because
`I` is K-injective.

## Main results

* `Dualizing.exists_distinguishedTriangle_nonZeroDivisor` — the triangle alone, for any complex
  of finite injective dimension over any commutative ring.
* `Dualizing.exists_distinguishedTriangle_quotient_nonZeroDivisor` — **[Stacks, Tag 0A7T]**.

## Implementation notes

The quotient complex is viewed in `D(A)` by derived restriction of scalars, and the middle map of
the triangle is written as `f • 𝟙` rather than left implicit, making explicit which map of the
short exact sequence `0 → A → A → A ⧸ (f) → 0` induces it.

Derived categories are at `HasDerivedCategory.standard`, forced by `Dualizing.derivedHom`, which
bakes that model into its own type.

## References

* [Stacks Project, Tag 0A7T](https://stacks.math.columbia.edu/tag/0A7T)
* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- For a K-injective complex `I` of `A`-modules, the termwise coextension `Hom_A(B, I)` computes
the total right derived functor `RHom_A(B, -)` on the class of `I`. -/
private noncomputable def derivedHomKInjectiveIso
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (I : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (hI : I.IsKInjective) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((ModuleCat.coextendScalars.{u, u, max v u} q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) ≅
      (derivedHom.{u, v} q).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  let F := (ModuleCat.coextendScalars.{u, u, max v u} q).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  have hA : ∀ K : CochainComplex (ModuleCat.{max v u} A) ℤ,
      ∃ (J : CochainComplex (ModuleCat.{max v u} A) ℤ) (f : K ⟶ J),
        J.IsKInjective ∧ QuasiIso f := by
    intro K
    obtain ⟨J, f, hf, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
    exact ⟨J, f, hJ, hf⟩
  let h := Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F hA
  letI : F.HasPointwiseRightDerivedFunctor W := h.1
  letI : F.HasRightDerivedFunctor W :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor F W
  let RF := F.totalRightDerived DerivedCategory.Qh W
  let α := F.totalRightDerivedUnit DerivedCategory.Qh W
  have hRF : IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    h.2 DerivedCategory.Qh RF α I hI
  let e := asIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  have hobj := Functor.mapHomotopyCategory_obj
    (ModuleCat.coextendScalars.{u, u, max v u} q) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  dsimp only [F, Functor.comp_obj] at e
  rw [hobj, HomotopyCategory.quotient_obj_as] at e
  change DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((ModuleCat.coextendScalars.{u, u, max v u} q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) ≅
    (derivedHom.{u, v} q).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
  simpa [F, RF, α, W, derivedHom] using e

/-- Restriction of scalars carries `RHom_A(B, Q I)`, for a K-injective complex `I`, to the derived
image of the termwise coextension `Hom_A(B, I)` viewed as a complex of `A`-modules. -/
private noncomputable def restrictedDerivedHomKInjectiveIso
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (I : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (hI : I.IsKInjective) :
    ((ModuleCat.restrictScalars q).mapDerivedCategory).obj
        ((derivedHom.{u, v} q).obj (DerivedCategory.Q.obj I)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars q).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.coextendScalars.{u, u, max v u} q).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)) := by
  let F := ModuleCat.restrictScalars.{max v u} q
  let C := (ModuleCat.coextendScalars.{u, u, max v u} q).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let e := (derivedHom.{u, v} q).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).symm.app I) ≪≫
    (derivedHomKInjectiveIso.{u, v} q I hI).symm ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).app (C.obj I)
  exact F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app (C.obj I)

/-- The counit `Hom_A(B, I) → I` of the restriction/coextension adjunction, applied termwise to a
complex `I` of `A`-modules. -/
private noncomputable def coextendCounitComplex
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (I : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    (((ModuleCat.restrictScalars q).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.coextendScalars.{u, u, max v u} q).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) ⟶ I :=
  (NatTrans.mapHomologicalComplex
    (ModuleCat.RestrictionCoextensionAdj.counit' q) (ComplexShape.up ℤ)).app I

/-- An `A`-linear map out of `B`, viewed as an `A`-module via `q : A → B`, sends `q a` to `a`
times its value at `1`. -/
private lemma coextend_linearMap_apply_eq_smul_apply_one
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B)
    {M : Type (max v u)} [AddCommGroup M] [Module A M]
    (k : (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) →ₗ[A] M) (a : A) :
    k (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from q a) =
      a • k (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from (1 : B)) := by
  simpa only [show a • (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from (1 : B)) =
    (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from q a) from mul_one (q a)] using
    k.map_smul a (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from (1 : B))

/-- If `f` dies in `B`, then the counit `Hom_A(B, I) → I` lands in the `f`-torsion of `I`. -/
private lemma coextendCounitComplex_smul_zero
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (f : A) (hf : q f = 0)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    coextendCounitComplex.{u, v} q I ≫ (f • 𝟙 I) = 0 := by
  ext n x
  show f • (ModuleCat.CoextendScalars.equiv q (I.X n) x)
    (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from (1 : B)) = 0
  rw [← coextend_linearMap_apply_eq_smul_apply_one.{u, v}]
  convert map_zero (ModuleCat.CoextendScalars.equiv q (I.X n) x)
  exact hf

/-- The short complex `Hom_A(B, I) → I → I` whose first map is the counit and whose second map is
multiplication by an element `f` of `A` killed by `A → B`. -/
private noncomputable def coextendShortComplex
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (f : A) (hf : q f = 0)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{max v u} A) ℤ) :=
  ShortComplex.mk (coextendCounitComplex.{u, v} q I) (f • 𝟙 I)
    (coextendCounitComplex_smul_zero.{u, v} q f hf I)

/-- Multiplication by a nonzerodivisor is surjective on an injective module. -/
private lemma smul_surjective_of_injective
    {A : Type u} [CommRing A] {M : Type (max v u)}
    [AddCommGroup M] [Module A M] [Module.Injective A M]
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    Function.Surjective (fun x : M => f • x) := by
  let l : A →ₗ[A] A := (LinearMap.lsmul A A) f
  have hl : Function.Injective l := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff.mp hf).1
    calc
      f * (x - y) = f * x - f * y := mul_sub _ _ _
      _ = 0 := sub_eq_zero.mpr hxy
  intro y
  obtain ⟨h, hh⟩ := Module.Injective.extension_property A M A A l hl
    (LinearMap.toSpanSingleton A M y)
  refine ⟨h 1, ?_⟩
  calc
    f • h 1 = h f := by simpa using (h.map_smul f (1 : A)).symm
    _ = y := by simpa [l] using congrArg (fun k : A →ₗ[A] M => k 1) hh

/-- An `A`-linear map out of a quotient ring `B` of `A`, viewed as an `A`-module, is determined by
its value at `1`. -/
private lemma coextend_linearMap_eq_of_apply_one
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    {M : Type (max v u)} [AddCommGroup M] [Module A M]
    (g h : (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) →ₗ[A] M)
    (h1 : g (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from
      (1 : B)) = h (show (ModuleCat.restrictScalars q).obj (ModuleCat.of B B) from
      (1 : B))) : g = h := by
  refine LinearMap.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hq b
  rw [coextend_linearMap_apply_eq_smul_apply_one.{u, v} q g,
    coextend_linearMap_apply_eq_smul_apply_one.{u, v} q h, h1]

/-- For a surjection `q : A → B`, the counit `Hom_A(B, I) → I` is termwise injective. -/
private lemma coextendCounitComplex_injective
    {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ) :
    Function.Injective ((coextendCounitComplex.{u, v} q I).f n) :=
  fun _ _ hxy => (ModuleCat.CoextendScalars.equiv q (I.X n)).injective
    (coextend_linearMap_eq_of_apply_one.{u, v} q hq _ _ hxy)

/-- Every element of `I` killed by `f` is in the image of the counit `Hom_A(A ⧸ (f), I) → I`. -/
private lemma coextendCounitComplex_range_of_smul_eq_zero
    {A : Type u} [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ)
    (y : I.X n) (hy : f • y = 0) :
    ∃ x : (((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.coextendScalars.{u, u, max v u}
        (Ideal.Quotient.mk (Ideal.span {f}))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)).X n,
      (coextendCounitComplex.{u, v} (Ideal.Quotient.mk (Ideal.span {f})) I).f n x = y := by
  let q : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk (Ideal.span {f})
  let g : A →ₗ[A] I.X n := LinearMap.toSpanSingleton A (I.X n) y
  have hker : (Ideal.span {f} : Submodule A A) ≤ LinearMap.ker g := by
    intro a ha
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_singleton').mp ha
    simp [g, mul_smul, hy]
  let gbar : (ModuleCat.restrictScalars q).obj
      (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})) →ₗ[A] I.X n :=
    Submodule.liftQ (Ideal.span {f}) g hker
  let x := (ModuleCat.CoextendScalars.equiv q (I.X n)).symm gbar
  refine ⟨x, ?_⟩
  show gbar (show (ModuleCat.restrictScalars q).obj
    (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})) from (1 : A ⧸ Ideal.span {f})) = y
  show (Submodule.liftQ (Ideal.span {f}) g hker)
    (Submodule.Quotient.mk (1 : A)) = y
  rw [Submodule.liftQ_apply]
  simp [g]

/-- For a nonzerodivisor `f` and a complex `I` of injective `A`-modules, the short complex
`Hom_A(A ⧸ (f), I) → I → I` is short exact. -/
private lemma coextendShortComplex_shortExact
    {A : Type u} [CommRing A] (f : A) (hf : f ∈ nonZeroDivisors A)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    (coextendShortComplex.{u, v} (Ideal.Quotient.mk (Ideal.span {f})) f
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)) I).ShortExact := by
  let q : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk (Ideal.span {f})
  have hfq : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ModuleCat.shortComplex_shortExact
  · refine fun y => ⟨coextendCounitComplex_range_of_smul_eq_zero.{u, v} f I n y, ?_⟩
    rintro ⟨x, rfl⟩
    show f • (coextendCounitComplex.{u, v} q I).f n x = 0
    exact congrArg (fun g : _ ⟶ I => g.f n x) (coextendCounitComplex_smul_zero.{u, v} q f hfq I)
  · exact coextendCounitComplex_injective.{u, v} q Ideal.Quotient.mk_surjective I n
  · show Function.Surjective (fun x : I.X n => f • x)
    have _ : Module.Injective A (I.X n) :=
      (Module.injective_iff_injective_object A (I.X n)).mpr (hI n)
    exact smul_surjective_of_injective.{u, v} f hf

/-- **The triangle of a nonzerodivisor, with no hypothesis beyond finite injective dimension.**
For a complex `K` of `A`-modules of finite injective dimension and a nonzerodivisor `f` of `A`,
derived coextension of scalars along `A → A ⧸ (f)`, viewed over `A`, is the fibre of
multiplication by `f` on `K`.

This is the part of [Stacks, Tag 0A7T] that needs neither a local ring nor a dualizing complex:
only a bounded complex of injectives representing `K`, which finite injective dimension
provides. -/
theorem exists_distinguishedTriangle_nonZeroDivisor
    {A : Type u} [CommRing A] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (f : A) (hfreg : f ∈ nonZeroDivisors A) :
    ∃ (i : ((ModuleCat.restrictScalars
            (Ideal.Quotient.mk (Ideal.span {f}))).mapDerivedCategory).obj
          ((derivedHom.{u, v} (Ideal.Quotient.mk (Ideal.span {f}))).obj K) ⟶ K)
        (δ : K ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).obj
          (((ModuleCat.restrictScalars
            (Ideal.Quotient.mk (Ideal.span {f}))).mapDerivedCategory).obj
            ((derivedHom.{u, v} (Ideal.Quotient.mk (Ideal.span {f}))).obj K))),
        Triangle.mk i (f • 𝟙 K) δ ∈ distTriang (DerivedCategory (ModuleCat.{max v u} A)) := by
  classical
  let q : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk (Ideal.span {f})
  obtain ⟨a, b, I, hGE, hLE, hInjective, ⟨e⟩⟩ := hK
  let _ : I.IsStrictlyGE a := hGE
  let _ : ∀ i, Injective (I.X i) := hInjective
  let F := ModuleCat.restrictScalars.{max v u} q
  let C := (ModuleCat.coextendScalars.{u, u, max v u} q).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hCoextend :
      F.mapDerivedCategory.obj ((derivedHom.{u, v} q).obj K) ≅
        DerivedCategory.Q.obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj I)) :=
    F.mapDerivedCategory.mapIso ((derivedHom.{u, v} q).mapIso e) ≪≫
      restrictedDerivedHomKInjectiveIso.{u, v} q I
        (CochainComplex.isKInjective_of_injective I a)
  have hfq : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  let S := coextendShortComplex.{u, v} q f hfq I
  have hS : S.ShortExact := coextendShortComplex_shortExact.{u, v} f hfreg I hInjective
  let T := DerivedCategory.triangleOfSES hS
  let a₁ : F.mapDerivedCategory.obj ((derivedHom.{u, v} q).obj K) ≅ T.obj₁ := hCoextend
  let e₂ : T.obj₂ ≅ K := e.symm
  let e₃ : T.obj₃ ≅ K := e.symm
  have hg : e₂.inv ≫ T.mor₂ ≫ e₃.hom = f • 𝟙 K := by
    show e.hom ≫ DerivedCategory.Q.map (f • 𝟙 I) ≫ e.inv = f • 𝟙 K
    rw [Functor.map_smul, DerivedCategory.Q.map_id]
    simp [CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul]
  refine ⟨a₁.hom ≫ T.mor₁ ≫ e₂.hom,
    e₃.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map a₁.inv, ?_⟩
  rw [← hg]
  refine isomorphic_distinguished T (DerivedCategory.triangleOfSES_distinguished hS) _ ?_
  refine Triangle.isoMk _ _ a₁ e₂.symm e₃.symm ?_ ?_ ?_
  · dsimp only [Triangle.mk_mor₁, Iso.symm_hom]
    simp only [Category.assoc, e₂.hom_inv_id, Category.comp_id]
  · dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
    simp only [Category.assoc, e₃.hom_inv_id, Category.comp_id]
  · dsimp only [Triangle.mk_mor₃, Iso.symm_hom]
    simp only [Category.assoc, ← Functor.map_comp, a₁.inv_hom_id]
    simp

/-- **Stacks Project, Tag 0A7T.** Dividing a Noetherian local ring by a nonzerodivisor in
its maximal ideal produces a normalized dualizing complex fitting into the distinguished
triangle induced by multiplication by that element. -/
@[stacks 0A7T]
theorem exists_distinguishedTriangle_quotient_nonZeroDivisor
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hfreg : f ∈ nonZeroDivisors A) :
    letI : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hf))
        (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).lt_top).ne
    letI : IsLocalRing (A ⧸ Ideal.span {f}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective
    ∃ (KB : DerivedCategory (ModuleCat.{max v u} (A ⧸ Ideal.span {f}))),
      IsNormalizedDualizingComplex.{u, v} KB ∧
        ∃ (i : ((ModuleCat.restrictScalars
              (Ideal.Quotient.mk (Ideal.span {f}))).mapDerivedCategory).obj KB ⟶ K)
          (δ : K ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) (1 : ℤ)).obj
            (((ModuleCat.restrictScalars
              (Ideal.Quotient.mk (Ideal.span {f}))).mapDerivedCategory).obj KB)),
          Triangle.mk i (f • 𝟙 K) δ ∈ distTriang (DerivedCategory (ModuleCat.{max v u} A)) :=
  by
    classical
    let B := A ⧸ Ideal.span {f}
    let _ : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hf))
        (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal).lt_top).ne
    let _ : IsLocalRing B :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
        Ideal.Quotient.mk_surjective
    let _ : IsNoetherianRing B := inferInstance
    let q : A →+* B := Ideal.Quotient.mk (Ideal.span {f})
    let _ : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
    exact ⟨(derivedHom.{u, v} q).obj K,
      isNormalizedDualizingComplex_derivedHom q
        (RingHom.Finite.of_surjective q Ideal.Quotient.mk_surjective) K hK,
      exists_distinguishedTriangle_nonZeroDivisor.{u, v} K hK.1.finiteInjectiveDimension f hfreg⟩

end Dualizing

end
