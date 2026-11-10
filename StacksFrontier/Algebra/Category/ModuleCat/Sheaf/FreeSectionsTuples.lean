module

public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The sections of a finite free sheaf of modules are tuples

Condition (2) of `SheafOfModules.IsCoherentOnSite`, Stacks 03DL(8), is stated sectionwise, while
Mathlib's `SheafOfModules.Presentation` asks for generating sections of a *categorical* kernel.
Comparing the two needs the sections of `SheafOfModules.free I` for a finite `I`, which are not
tuples by definition: `free I` is a coproduct of copies of the unit.  For a finite index type
that coproduct is a biproduct, hence preserved by the additive evaluation functors, and
`freeSectionsIso` is the resulting comparison with the module of tuples.

## Main results

* `Stacks.SheafOfModules.isFiniteType_of_sectionwiseEquiv`: `PresheafOfModules.IsFiniteType`
  transports along a sectionwise additive equivalence which is semilinear over a sectionwise
  ring equivalence.  Neither the ring nor the module universes need agree on the two sides.
* `Stacks.SheafOfModules.freeSectionsIso`, `Stacks.SheafOfModules.freeSectionsIso_hom_apply`:
  the sections of a free sheaf of modules on a finite index type are the tuples of sections of
  the structure sheaf, and the comparison sends a tuple to the corresponding combination of the
  tautological sections.
* `Stacks.SheafOfModules.freeSectionsCoeff` and its `apply`/naturality lemmas: the same
  comparison for the index type `ULift (Fin n)`, which is the one
  `SheafOfModules.generatingSectionsOfGenerates` produces.

## Implementation notes

`sheafEvaluation_additive` is a local instance rather than a global one: additivity of
evaluation is what makes the finite coproduct above a biproduct, and it is needed nowhere else.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w w' m m'

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Finite type is a sectionwise condition.**  If a presheaf of modules `N` over `S` is
obtained from a presheaf of modules `M` over `R` by a sectionwise additive equivalence which is
semilinear over a sectionwise ring equivalence and compatible with restriction, then `N` is of
finite type as soon as `M` is.  Neither the ring nor the module universes need agree. -/
theorem isFiniteType_of_sectionwiseEquiv
    {R : Cᵒᵖ ⥤ RingCat.{w}} {S : Cᵒᵖ ⥤ RingCat.{w'}}
    {M : PresheafOfModules.{m} R} {N : PresheafOfModules.{m'} S}
    (eR : ∀ V, R.obj V ≃+* S.obj V) (e : ∀ V, M.obj V ≃+ N.obj V)
    (he : ∀ V (a : R.obj V) (x : M.obj V), e V (a • x) = eR V a • e V x)
    (hn : ∀ {V W} (f : V ⟶ W) (x : M.obj V),
      e W (M.restrictₛₗ f x) = N.restrictₛₗ f (e V x))
    (h : PresheafOfModules.IsFiniteType J M) : PresheafOfModules.IsFiniteType J N := by
  obtain ⟨I, U, hU, hg⟩ := h.exists_generators
  refine ⟨I, U, hU, ?_⟩
  intro i
  obtain ⟨n, s, hs⟩ := hg i
  refine ⟨n, fun j ↦ e (op (U i)) (s j), ?_⟩
  intro V f t
  obtain ⟨T, hT, ht⟩ := hs V f ((e (op V)).symm t)
  refine ⟨T, hT, ?_⟩
  intro W g hgW
  obtain ⟨a, ha⟩ := ht W g hgW
  refine ⟨fun j ↦ eR (op W) (a j), ?_⟩
  have h' := congrArg (e (op W)) ha
  simpa only [map_sum, he, hn, AddEquiv.apply_symm_apply] using h'

end Transport

section FreeSections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Evaluating a sheaf of modules at an object of the site is an additive functor: it is the
forgetful functor to presheaves of modules followed by evaluation. -/
theorem sheafEvaluation_additive (R : Sheaf J RingCat.{w}) (V : Cᵒᵖ) :
    (_root_.SheafOfModules.evaluation R V).Additive :=
  inferInstanceAs ((_root_.SheafOfModules.forget R) ⋙
    PresheafOfModules.evaluation R.obj V).Additive

attribute [local instance] sheafEvaluation_additive

/-- The tautological cofan on the module of `I`-tuples of ring elements, for a finite `I`. -/
noncomputable abbrev finFreeCofan (A : Type w) [Ring A] (I : Type w) [Fintype I]
    [DecidableEq I] : Cofan (fun _ : I ↦ ModuleCat.of A A) :=
  Cofan.mk (ModuleCat.of A (I → A))
    (fun i ↦ ModuleCat.ofHom (LinearMap.single A (fun _ : I ↦ A) i))

/-- A finite tuple module is the coproduct of copies of the ring: a map out of it is determined
by the images of the standard basis vectors, and any such family extends. -/
noncomputable def isColimitFinFreeCofan (A : Type w) [Ring A] (I : Type w) [Fintype I]
    [DecidableEq I] : IsColimit (finFreeCofan A I) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ ModuleCat.ofHom
    (Fintype.linearCombination A (fun i ↦ s.inj i 1))) ?_ ?_
  · intro s i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change (∑ j, Pi.single (M := fun _ : I ↦ A) i a j • s.inj j 1) = s.inj i a
    simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    simpa only [smul_eq_mul, mul_one] using (map_smul (s.inj i).hom a (1 : A)).symm
  · intro s mm hm
    ext a
    change mm a = ∑ i, a i • s.inj i 1
    calc
      mm a = mm (∑ i, Pi.single i (a i)) := congrArg mm.hom (Finset.univ_sum_single a).symm
      _ = ∑ i, mm (Pi.single i (a i)) := map_sum mm.hom _ _
      _ = ∑ i, a i • s.inj i 1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := ConcreteCategory.congr_hom (hm i) (1 : A)
        change mm (Pi.single i 1) = s.inj i 1 at hi
        rw [← hi, ← map_smul]
        congr 1
        simpa only [smul_eq_mul, mul_one] using
          (Pi.single_smul (f := fun _ : I ↦ A) i (a i) (1 : A))

/-- The sections of a free sheaf of modules on a finite index type form a coproduct of copies of
the sections of the structure sheaf: evaluation is additive, so it preserves the finite
coproduct defining `SheafOfModules.free I`. -/
noncomputable def isColimitFreeCofanEval
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (I : Type w) [Fintype I] (V : Cᵒᵖ) :
    IsColimit (Cofan.mk ((_root_.SheafOfModules.free (R := R) I).val.obj V)
      (fun i ↦ (_root_.SheafOfModules.evaluation R V).map
        (_root_.SheafOfModules.ιFree (I := I) i))) :=
  (Cofan.isColimitMapCoconeEquiv (_root_.SheafOfModules.evaluation R V)
    (fun _ : I ↦ _root_.SheafOfModules.unit R) (_root_.SheafOfModules.freeCofan I))
      (isColimitOfPreserves (_root_.SheafOfModules.evaluation R V)
        (_root_.SheafOfModules.isColimitFreeCofan I))

/-- **The sections of a finite free sheaf of modules are tuples.** -/
noncomputable def freeSectionsIso
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (I : Type w) [Fintype I] [DecidableEq I] (V : Cᵒᵖ) :
    ModuleCat.of (R.obj.obj V) (I → R.obj.obj V) ≅
      (_root_.SheafOfModules.free (R := R) I).val.obj V :=
  (isColimitFinFreeCofan (R.obj.obj V) I).coconePointUniqueUpToIso
    (isColimitFreeCofanEval (R := R) I V)

/-- A tuple is carried to the corresponding combination of the tautological sections. -/
theorem freeSectionsIso_hom_apply
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (I : Type w) [Fintype I] [DecidableEq I] (V : Cᵒᵖ) (a : I → R.obj.obj V) :
    (freeSectionsIso (R := R) I V).hom a =
      ∑ i, SMul.smul (M := R.obj.obj V)
        (α := (_root_.SheafOfModules.free (R := R) I).val.obj V)
        (a i) ((_root_.SheafOfModules.freeSection (R := R) i).val V) := by
  have key : ∀ (i : I) (b : R.obj.obj V),
      (freeSectionsIso (R := R) I V).hom (Pi.single i b) =
        SMul.smul (M := R.obj.obj V)
          (α := (_root_.SheafOfModules.free (R := R) I).val.obj V) b
          ((_root_.SheafOfModules.freeSection (R := R) (I := I) i).val V) := by
    intro i b
    have h := ConcreteCategory.congr_hom
      ((isColimitFinFreeCofan (R.obj.obj V) I).comp_coconePointUniqueUpToIso_hom
        (isColimitFreeCofanEval (R := R) I V) ⟨i⟩) b
    change (freeSectionsIso (R := R) I V).hom (Pi.single i b) =
      (_root_.SheafOfModules.ιFree (R := R) (I := I) i).val.app V b at h
    refine h.trans ?_
    refine Eq.trans ?_ (map_smul
      ((_root_.SheafOfModules.ιFree (R := R) (I := I) i).val.app V).hom b
      (1 : R.obj.obj V))
    exact congrArg _ (by simp)
  calc (freeSectionsIso (R := R) I V).hom a
      = (freeSectionsIso (R := R) I V).hom (∑ i, Pi.single i (a i)) :=
        congrArg (fun z ↦ (freeSectionsIso (R := R) I V).hom z)
          (Finset.univ_sum_single a).symm
    _ = ∑ i, (freeSectionsIso (R := R) I V).hom (Pi.single i (a i)) :=
        map_sum ((freeSectionsIso (R := R) I V).hom).hom _ _
    _ = _ := Finset.sum_congr rfl (fun i _ ↦ key i (a i))

/-- The sections of the free sheaf of modules on `ULift (Fin n)`, as the module of `Fin n`-tuples
of sections of the structure sheaf. -/
noncomputable def freeSectionsCoeff
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (n : ℕ) (V : Cᵒᵖ) : (Fin n → R.obj.obj V) ≃ₗ[R.obj.obj V]
      (_root_.SheafOfModules.free (R := R) (ULift.{w} (Fin n))).val.obj V :=
  ({ toFun := fun a i ↦ a i.down
     invFun := fun a i ↦ a (ULift.up i)
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } :
       (Fin n → R.obj.obj V) ≃ₗ[R.obj.obj V] (ULift.{w} (Fin n) → R.obj.obj V)).trans
    (freeSectionsIso (R := R) (ULift.{w} (Fin n)) V).toLinearEquiv

/-- A tuple is carried to the corresponding combination of the tautological sections. -/
theorem freeSectionsCoeff_apply
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (n : ℕ) (V : Cᵒᵖ) (a : Fin n → R.obj.obj V) :
    freeSectionsCoeff (R := R) n V a =
      ∑ i : Fin n, SMul.smul (M := R.obj.obj V)
        (α := (_root_.SheafOfModules.free (R := R) (ULift.{w} (Fin n))).val.obj V)
        (a i) ((_root_.SheafOfModules.freeSection (R := R) (ULift.up i)).val V) := by
  change (freeSectionsIso (R := R) (ULift.{w} (Fin n)) V).hom _ = _
  refine (freeSectionsIso_hom_apply (R := R) (ULift.{w} (Fin n)) V _).trans ?_
  exact Fintype.sum_equiv Equiv.ulift _ _ (fun _ ↦ rfl)

/-- Restriction of sections of a finite free sheaf of modules is restriction of coefficients. -/
theorem freeSectionsCoeff_naturality
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (n : ℕ) {V W : Cᵒᵖ} (f : V ⟶ W) (a : Fin n → R.obj.obj V) :
    (_root_.SheafOfModules.free (R := R) (ULift.{w} (Fin n))).val.restrictₛₗ f
      (freeSectionsCoeff (R := R) n V a) =
      freeSectionsCoeff (R := R) n W (fun i ↦ R.obj.map f (a i)) := by
  refine Eq.trans (congrArg (fun z ↦ (_root_.SheafOfModules.free (R := R)
      (ULift.{w} (Fin n))).val.restrictₛₗ f z) (freeSectionsCoeff_apply (R := R) n V a)) ?_
  refine Eq.trans (map_sum ((_root_.SheafOfModules.free (R := R)
      (ULift.{w} (Fin n))).val.restrictₛₗ f) _ _) ?_
  refine Eq.trans ?_ (freeSectionsCoeff_apply (R := R) n W
    (fun i ↦ R.obj.map f (a i))).symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (((_root_.SheafOfModules.free (R := R)
      (ULift.{w} (Fin n))).val.restrictₛₗ f).map_smulₛₗ (a i) _).trans
    (congrArg (fun x ↦ R.obj.map f (a i) • x)
      (PresheafOfModules.sections_property
        (_root_.SheafOfModules.freeSection (R := R) (ULift.up i)) f))

end FreeSections

end Stacks.SheafOfModules

end
