module

public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.AugmentedComplexOfInjectives
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.FunctorialAbutment
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# The abutment of the Čech-to-cohomology spectral sequence is cohomology on the covered open

`Stacks.Cohomology.CechSpectral.cechFunctorialAbutment` builds the functorial filtered abutment of
the Čech-to-cohomology spectral sequence of [Stacks, Tag 01ES], abutting to the cohomology of the
total complex `Tot(Č^•(𝒰, I^•(F)))` of the Čech double complex of the chosen injective resolution.
What [Stacks, Tag 01ES] asserts is that it abuts to `R^nΓ_{𝒰.U}(F)`, the derived evaluation
functor on the covered open.  This file supplies the identification, *naturally in the sheaf*.

The mathematical content is [Stacks, Tag 0133]: the augmented Čech complex of an injective sheaf
is exact, so the augmentation `Γ(U, I^•(F)) ⟶ Tot(Č^•(𝒰, I^•(F)))` is a quasi-isomorphism.  Two
things make it usable here.

* **[Stacks, Tag 0133] as data.**  `quasiIso_total_of_resolution` delivers the comparison as an
  existential with a chosen witness, and a chosen witness cannot be made natural after the fact.
  `comparisonMapP` of `StacksFrontier/Algebra/Homology/TotalComplexQuasiIso.lean` is the same
  comparison *defined* by its components, with `comparisonMapP_naturality`; `abutmentIsoOfAlpha`
  is what that buys.
* **The augmentation as a natural transformation.**  `cechAugNat` is the degree-zero Čech
  augmentation as a morphism of *functors* of the sheaf --
  `Stacks.Cohomology.CechSheaf.cechAugmentationNatTrans`, the degree-zero half of
  [Stacks, Tag 01EP], with its source identified with
  `SheafOfModules.evaluation` by `sectionsTerminalFunctorIso` -- and `cechAugNatComplex` applies it
  degreewise to a complex of sheaves, so its naturality in the complex is free.

Three of the four hypotheses of [Stacks, Tag 0133] are discharged here unconditionally
(`cechHypotheses`): finiteness of the antidiagonals and vanishing in negative Čech degree hold
because both indices of the Čech double complex are extended by zero from `ℕ`, and exactness of
the columns away from degree `0` is [Stacks, Tag 01EP] for the injective terms of the resolution,
transported along the two extensions.  The fourth, `inducesIsoKernel`, is the degree-zero half of
[Stacks, Tag 01EP] and is left as an argument.

`gammaResZHomologyIso` is the other half of the identification: the cohomology of the `Γ`-applied
chosen resolution *is* the right derived functor, by
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` and the embedding-homology isomorphism of
`ComplexShape.Embedding.extendFunctorHomologyIso`.

**Nothing in this file carries the tag `01ES`.**

## Main definitions

* `Stacks.Cohomology.CechSpectral.gammaRes`, `gammaResZ`: `Γ(U, I^•(F))` and its extension by
  zero to `ℤ`.
* `Stacks.Cohomology.CechSpectral.gammaResZHomologyFunctor`: its cohomology, as a functor -- the
  total complex is functorial only up to homotopy, but homology is homotopy invariant.
* `Stacks.Cohomology.CechSpectral.cechAugNat` and `cechAugNatComplex`: the Čech augmentation as a
  natural transformation, and degreewise on complexes of sheaves.
* `Stacks.Cohomology.CechSpectral.rowZeroNatFunctor`: the complex `i ↦ Č⁰(𝒰, Y_i)`, which is the
  target of `cechAugNatComplex` on the nose.

## Main results

* `Stacks.Cohomology.CechSpectral.gammaResZHomologyIso`: `H^n(Γ(U, I^•(-))) ≅ R^nΓ_{𝒰.U}`.
* `Stacks.Cohomology.CechSpectral.cechHypotheses`: three of the four hypotheses of
  [Stacks, Tag 0133] for the Čech double complex.
* `Stacks.Cohomology.CechSpectral.abutmentIsoOfAlpha`:
  `H^n(Γ(U, I^•(-))) ≅ H^n(Tot(Č^•(𝒰, I^•(-))))`, given a natural augmentation satisfying those
  hypotheses.
* `Stacks.Cohomology.CechSpectral.isIso_kernelLift_of_mono_of_exact` and
  `isIso_kernelLift_of_iso`: a monomorphism whose short complex is exact is a kernel, and the
  kernel clause transports along an isomorphism of the three-term diagram.  This is the shape in
  which the degree-zero clause of [Stacks, Tag 01EP] supplies `inducesIsoKernel`.
* `Stacks.Cohomology.CechSpectral.cechDoubleFunctorXIso_comm`: the index convention of the Čech
  double complex is compatible with the Čech differential, so its columns carry the Čech complex
  as complexes and not only degreewise.
* `Stacks.Cohomology.CechSpectral.cechRowZeroIso_inv_f` and `cechAlpha_f`: the components of the
  identification of the zeroth row, and of the augmentation, on the range of the embedding.
* `Stacks.Cohomology.CechSpectral.inducesIsoKernel_cechAlpha`: **the fourth hypothesis of
  [Stacks, Tag 0133]**, the degree-zero clause of [Stacks, Tag 01EP] transported; hence
  `cechHypothesesFull`.
* `Stacks.Cohomology.CechSpectral.cechAbutmentIso`: **the convergence half of
  [Stacks, Tag 01ES]** -- `H^n(Tot(Č^•(𝒰, I^•(-)))) ≅ R^nΓ_{𝒰.U}`, naturally.
* `Stacks.Cohomology.CechSpectral.cechAbutment`: the `abutment` field of [Stacks, Tag 01ES].

## References

* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 01ES](https://stacks.math.columbia.edu/tag/01ES)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CochainComplex Stacks.Cohomology.Leray

namespace Stacks.Cohomology.CechSpectral

/-! ### A monomorphism with exact short complex is a kernel -/

section Helper

universe vC uC

/-- **A monomorphism whose short complex is exact is a kernel of the next map.**  The comparison
with the kernel is a monomorphism because the given map is, and an epimorphism because the short
complex is exact; an abelian category is balanced.

This is the shape in which `Stacks.Cohomology.CechSheaf.isIso_kernelLift_cechAugmentation` -- the
degree-zero clause of [Stacks, Tag 01EP] -- supplies the hypothesis `inducesIsoKernel` of
[Stacks, Tag 0133] after transport. -/
theorem isIso_kernelLift_of_mono_of_exact {C : Type uC} [Category.{vC} C] [Abelian C]
    {T A B : C} (f : T ⟶ A) (g : A ⟶ B) (hf : f ≫ g = 0) [Mono f]
    (hex : (ShortComplex.mk f g hf).Exact) :
    IsIso (kernel.lift g f hf) :=
  have : Mono (kernel.lift g f hf) := mono_of_mono_fac (kernel.lift_ι g f hf)
  have : Epi (kernel.lift g f hf) :=
    (ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.1 hex
  isIso_of_mono_of_epi _

/-- **The kernel clause transports along an isomorphism of the three-term diagram.**  Given
`f ≫ g = 0` with `f` a kernel of `g`, and an isomorphism of `T ⟶ A ⟶ B` with `T' ⟶ A' ⟶ B'`, the
primed `f'` is a kernel of `g'`.

Monomorphy transports because `f'` is `f` conjugated by isomorphisms, and exactness because the
two short complexes are isomorphic (`CategoryTheory.ShortComplex.exact_of_iso`).  This is the
shape in which the degree-zero clause of [Stacks, Tag 01EP] supplies `inducesIsoKernel` of
[Stacks, Tag 0133] for the Čech double complex, whose columns carry the Čech complex only up to
the comparison isomorphisms of the two extensions by zero. -/
theorem isIso_kernelLift_of_iso {C : Type uC} [Category.{vC} C] [Abelian C]
    {T A B T' A' B' : C} {f : T ⟶ A} {g : A ⟶ B} (hf : f ≫ g = 0)
    {f' : T' ⟶ A'} {g' : A' ⟶ B'} (hf' : f' ≫ g' = 0)
    (eT : T ≅ T') (eA : A ≅ A') (eB : B ≅ B')
    (h1 : f ≫ eA.hom = eT.hom ≫ f') (h2 : g ≫ eB.hom = eA.hom ≫ g')
    (h : IsIso (kernel.lift g f hf)) :
    IsIso (kernel.lift g' f' hf') := by
  have hmono : Mono f := by
    rw [← kernel.lift_ι g f hf]
    have := h
    infer_instance
  have : Mono f' := by
    rw [show f' = eT.inv ≫ f ≫ eA.hom by simp [h1]]
    infer_instance
  refine isIso_kernelLift_of_mono_of_exact f' g' hf' ?_
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk eT eA eB h1.symm h2.symm)
    ((ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.2 (by have := h; infer_instance))

/-- **The differential of an extension by zero, read through the comparison isomorphisms composed
with an isomorphism of the unextended complex.**

Stated in the `HomologicalComplex.extend` spelling throughout, with no project definition in
sight, which is the point: applied to a column of the Čech double complex the conclusion is
accepted across the `cechDoubleFunctor` spelling by `exact`, whereas rewriting inside that
spelling is refused -- the goal is then not type-correct at `instances` transparency. -/
theorem _root_.HomologicalComplex.extend_d_comp_extendXIso_comp
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type uC} [Category.{vC} C]
    [Preadditive C] [HasZeroObject C] (e : c.Embedding c') [e.IsRelIff]
    (Z W : HomologicalComplex C c) (θ : Z ≅ W)
    {j₁ j₂ : ι} {j₁' j₂' : ι'} (hj₁ : e.f j₁ = j₁') (hj₂ : e.f j₂ = j₂') :
    (Z.extend e).d j₁' j₂' ≫ ((Z.extendXIso e hj₂).hom ≫ θ.hom.f j₂) =
      ((Z.extendXIso e hj₁).hom ≫ θ.hom.f j₁) ≫ W.d j₁ j₂ := by
  rw [HomologicalComplex.extend_d_eq Z e hj₁ hj₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun z => (Z.extendXIso e hj₁).hom ≫ z) (θ.hom.comm j₁ j₂).symm

/-- **The extension by zero of an `ℕ`-indexed complex vanishes off the naturals.** -/
private theorem isZero_extend_X_of_not_exists {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] (K : CochainComplex C ℕ) (p : ℤ) (hp : ¬∃ i : ℕ, (i : ℤ) = p) :
    IsZero ((K.extend ComplexShape.embeddingUpNat).X p) :=
  HomologicalComplex.isZero_extend_X K _ p fun i => by simpa using fun h => hp ⟨i, h⟩

/-- **The cocycle condition transports along an isomorphism of the three-term diagram.**  The
companion of `isIso_kernelLift_of_iso`: it supplies the `hα` that the kernel clause of
[Stacks, Tag 0133] quantifies over, so that both halves of that clause come from the same two
squares. -/
theorem comp_eq_zero_of_iso {C : Type uC} [Category.{vC} C] [Abelian C]
    {T A B T' A' B' : C} {f : T ⟶ A} {g : A ⟶ B} (hf : f ≫ g = 0)
    {f' : T' ⟶ A'} {g' : A' ⟶ B'} (eT : T ≅ T') (eA : A ≅ A') (eB : B ≅ B')
    (h1 : f ≫ eA.hom = eT.hom ≫ f') (h2 : g ≫ eB.hom = eA.hom ≫ g') :
    f' ≫ g' = 0 := by
  have hf' : f' = eT.inv ≫ f ≫ eA.hom := by
    rw [h1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hf']
  simp only [Category.assoc]
  rw [← h2, ← Category.assoc f g eB.hom, hf, zero_comp, comp_zero]

/-- **The kernel of a morphism out of a zero object is zero.**  Used off the range of the
embedding, where the Čech double complex and the extended resolution both vanish, so the
comparison with the kernel is a morphism between zero objects. -/
theorem isZero_kernel_of_isZero {C : Type uC} [Category.{vC} C] [Abelian C] {A B : C}
    (g : A ⟶ B) (hA : IsZero A) : IsZero (kernel g) :=
  (IsZero.iff_id_eq_zero _).2 ((cancel_mono (kernel.ι g)).1 (hA.eq_of_tgt _ _))

end Helper

/-! ### Additivity of evaluation -/

section Additive

universe u0 r0 v0

/-- **Evaluation on an open is additive**, independently of the ring and module universes.

Stated over its own universes on purpose: with the module universe a single variable the instance
applies at `max u r v w`, which it does not if that `max` is written into the statement -- the
unifier then sticks on `max u r ?v ?w =?= max u r v w`.  The same device as the universe-command
order of `SheafOfModules.enoughInjectives_opens`. -/
instance evaluation_additive {Y : Type u0} [TopologicalSpace Y]
    (P : Sheaf (Opens.grothendieckTopology Y) RingCat.{r0}) (U : (Opens Y)ᵒᵖ) :
    (SheafOfModules.evaluation.{v0} P U).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

end Additive

universe u r v w

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{r})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, w} (TopCat.of X))

/-! ### The zeroth row of the Čech double complex -/

/-- `extend`-then-evaluate-at-`(0 : ℤ)`, the functor whose `mapHomologicalComplex` is the
zeroth row of `cechDoubleFunctor`. -/
abbrev rowZeroEvalFunctor :
    CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ ⥤
      ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)) :=
  ComplexShape.embeddingUpNat.extendFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ⋙
    HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
      (ComplexShape.up ℤ) (0 : ℤ)

/-- **The zeroth row of the Čech double complex, on the nose.** -/
theorem rowZero_cechDoubleFunctor_obj
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) :
    rowZero ((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y) =
      ((ComplexShape.embeddingUpNat.extendFunctor
              (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ⋙
            HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
              (ComplexShape.up ℤ) (0 : ℤ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y) :=
  rfl

/-- **The `ℕ`-indexed complex of degree-zero Čech terms**: `i ↦ Č⁰(𝒰, Y_i)`. -/
noncomputable def rowZeroNatFunctor :
    CochainComplex (SheafOfModules.{max u r v w} O) ℕ ⥤
      CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ :=
  cechDoubleNatFunctor.{u, r, v, w} O 𝒰 ⋙
    (HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
      (ComplexShape.up ℕ) 0).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The term of `rowZeroNatFunctor` in degree `i` is `Č⁰(𝒰, Y_i)`. -/
lemma rowZeroNatFunctor_obj_X (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) (i : ℕ) :
    ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj Y).X i =
      ((cechComplexFunctor.{u, r, v, w} O 𝒰).obj
        ((SheafOfModules.forget O).obj (Y.X i))).X 0 :=
  rfl

/-- The differential of `rowZeroNatFunctor` is the map `Č⁰(𝒰, Y_i) ⟶ Č⁰(𝒰, Y_j)` induced by
the differential `Y_i ⟶ Y_j`. -/
lemma rowZeroNatFunctor_obj_d (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ)
    (i j : ℕ) :
    ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj Y).d i j =
      ((cechComplexFunctor.{u, r, v, w} O 𝒰).map
        ((SheafOfModules.forget O).map (Y.d i j))).f 0 :=
  rfl

/-- The degree-`i` component of `rowZeroNatFunctor` applied to `φ` is the map
`Č⁰(𝒰, Y_i) ⟶ Č⁰(𝒰, Z_i)` induced by `φ_i`. -/
lemma rowZeroNatFunctor_map_f {Y Z : CochainComplex (SheafOfModules.{max u r v w} O) ℕ}
    (φ : Y ⟶ Z) (i : ℕ) :
    ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).map φ).f i =
      ((cechComplexFunctor.{u, r, v, w} O 𝒰).map
        ((SheafOfModules.forget O).map (φ.f i))).f 0 :=
  rfl

/-- The comparison `G ≅ eval (0 : ℕ)` of the two degree-zero evaluations, pushed through
`mapHomologicalComplex` in the outer direction. -/
noncomputable def rowZeroEvalNatIso :
    (rowZeroEvalFunctor.{u, r, v, w} O 𝒰).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
        (ComplexShape.up ℕ) 0).mapHomologicalComplex (ComplexShape.up ℕ) :=
  NatIso.mapHomologicalComplex
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ComplexShape.embeddingUpNat_f_zero)
    (ComplexShape.up ℕ)

/-- **The zeroth row of the Čech double complex is the `ℤ`-extension of the `ℕ`-indexed
complex of degree-zero Čech terms.** -/
noncomputable def rowZeroIsoApp (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) :
    rowZero ((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y) ≅
      (ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).obj
        ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj Y) :=
  (rowZeroEvalFunctor.{u, r, v, w} O 𝒰).mapExtendIso
      ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y) ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).mapIso
      ((rowZeroEvalNatIso.{u, r, v, w} O 𝒰).app ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y))

/-- **The same, naturally in the complex of sheaves.** -/
noncomputable def rowZeroIso :
    cechDoubleFunctor.{u, r, v, w} O 𝒰 ⋙
        rowZeroFunctor (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ≅
      rowZeroNatFunctor.{u, r, v, w} O 𝒰 ⋙
        ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) :=
  Functor.isoWhiskerLeft (cechDoubleNatFunctor.{u, r, v, w} O 𝒰)
    ((rowZeroEvalFunctor.{u, r, v, w} O 𝒰).mapExtendNatIso ComplexShape.embeddingUpNat ≪≫
      Functor.isoWhiskerRight (rowZeroEvalNatIso.{u, r, v, w} O 𝒰)
        (ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))))

/-- `rowZeroIso` is `rowZeroIsoApp` objectwise. -/
lemma rowZeroIso_app (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) :
    (rowZeroIso.{u, r, v, w} O 𝒰).app Y = rowZeroIsoApp.{u, r, v, w} O 𝒰 Y := rfl

/-- **The naturality square of `rowZeroIsoApp`.** -/
theorem rowZeroIsoApp_naturality {Y Z : CochainComplex (SheafOfModules.{max u r v w} O) ℕ}
    (φ : Y ⟶ Z) :
    rowZeroMap ((cechDoubleFunctor.{u, r, v, w} O 𝒰).map φ) ≫
        (rowZeroIsoApp.{u, r, v, w} O 𝒰 Z).hom =
      (rowZeroIsoApp.{u, r, v, w} O 𝒰 Y).hom ≫
        (ComplexShape.embeddingUpNat.extendFunctor
            (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
          ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).map φ) :=
  (rowZeroIso.{u, r, v, w} O 𝒰).hom.naturality φ

/-- The component of `rowZeroIso.hom` at `Y` is `(rowZeroIsoApp Y).hom`. -/
lemma rowZeroIso_hom_app (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) :
    (rowZeroIso.{u, r, v, w} O 𝒰).hom.app Y = (rowZeroIsoApp.{u, r, v, w} O 𝒰 Y).hom :=
  congrArg Iso.hom (rowZeroIso_app.{u, r, v, w} O 𝒰 Y)

/-- **The components of `rowZeroIsoApp`, against the index convention of
`cechDoubleFunctorXIso`.** -/
theorem rowZeroIsoApp_hom_f_comp (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ)
    (i : ℕ) (i' : ℤ) (hi : (i : ℤ) = i') :
    (rowZeroIsoApp.{u, r, v, w} O 𝒰 Y).hom.f i' ≫
        (HomologicalComplex.extendXIso ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj Y)
          ComplexShape.embeddingUpNat hi).hom =
      (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 Y i 0 i' 0 hi rfl).hom :=
  Eq.trans
    ((rowZeroEvalFunctor.{u, r, v, w} O 𝒰).mapExtendIso_hom_comp_extendFunctor_map_f
      ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y) ComplexShape.embeddingUpNat
      ((rowZeroEvalNatIso.{u, r, v, w} O 𝒰).app
        ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y)).hom hi)
    (HomologicalComplex.extendMap_f_comp_extendXIso
      (((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y).extendXIso
        ComplexShape.embeddingUpNat hi).hom
      ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero)

/-- **The index convention of `cechDoubleFunctorXIso` is compatible with the Čech differential**:
in the Čech direction it is a morphism of complexes, not merely a degreewise isomorphism.  This is
`HomologicalComplex.extend_d_comp_extendXIso_comp` for the inner extension by zero, the outer
comparison being an isomorphism of complexes already. -/
theorem cechDoubleFunctorXIso_comm
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) (i : ℕ) (i' : ℤ) (hi : (i : ℤ) = i')
    (j₁ j₂ : ℕ) (j₁' j₂' : ℤ) (hj₁ : (j₁ : ℤ) = j₁') (hj₂ : (j₂ : ℤ) = j₂') :
    (((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y).X i').d j₁' j₂' ≫
        (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 Y i j₂ i' j₂' hi hj₂).hom =
      (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 Y i j₁ i' j₁' hi hj₁).hom ≫
        ((cechComplexFunctor.{u, r, v, w} O 𝒰).obj
          ((SheafOfModules.forget O).obj (Y.X i))).d j₁ j₂ :=
  HomologicalComplex.extend_d_comp_extendXIso_comp ComplexShape.embeddingUpNat
    (((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y).X i')
    (((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y).X i)
    (HomologicalComplex.extendXIso ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y)
      ComplexShape.embeddingUpNat hi) hj₁ hj₂

/-! ### The Čech augmentation, as a natural transformation -/

/-- The Čech complex functor of a sheaf of modules is additive, being a composite of additive
functors; this is what `CategoryTheory.NatTrans.mapHomologicalComplex` asks of the target of
`cechAugNat`. -/
instance cechSheafComplexFunctor_additive :
    (cechSheafComplexFunctor.{u, r, v, w} O 𝒰).Additive := by
  dsimp [cechSheafComplexFunctor]
  infer_instance

/-- **The degree-zero Čech augmentation `Γ(𝒰.U, -) ⟹ Č⁰(𝒰, -)`, at the spelling
[Stacks, Tag 01ES] uses.**  `Stacks.Cohomology.CechSheaf.cechAugmentationNatTrans` with its source
-- sections at the terminal object of the slice, the side the Čech complex is built on -- replaced
by `SheafOfModules.evaluation` through
`Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso`; the target is the Čech complex of
[Stacks, Tag 01EJ], which `cechSheafComplexFunctor_eq` identifies with that of [Stacks, Tag 01EP]
by `rfl`. -/
noncomputable def cechAugNat :
    SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U) ⟶
      cechSheafComplexFunctor.{u, r, v, w} O 𝒰 ⋙
        HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
          (ComplexShape.up ℕ) 0 :=
  (CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).inv ≫
    CechSheaf.cechAugmentationNatTrans.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)

/-- **The Čech augmentation applied degreewise to a complex of sheaves.**  Being
`CategoryTheory.NatTrans.mapHomologicalComplex` of a natural transformation, its naturality in the
complex is free -- which is what makes the comparison of [Stacks, Tag 0133] natural in the sheaf,
through `CategoryTheory.InjectiveResolution.desc`.

Its target is `rowZeroNatFunctor` on the nose:
`(cechSheafComplexFunctor ⋙ eval 0).mapHomologicalComplex` and
`cechDoubleNatFunctor ⋙ (eval 0).mapHomologicalComplex` are the same functor by `rfl`. -/
noncomputable def cechAugNatComplex :
    (SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).mapHomologicalComplex
        (ComplexShape.up ℕ) ⟶
      rowZeroNatFunctor.{u, r, v, w} O 𝒰 :=
  NatTrans.mapHomologicalComplex (cechAugNat.{u, r, v, w} O 𝒰) (ComplexShape.up ℕ)

/-! ### The hypotheses of [Stacks, Tag 0133] for the Čech double complex -/

/-- **`diagonalFinite` for the Čech double complex.**  It vanishes unless both indices are
non-negative, so on the antidiagonal of total degree `n` only the indices in `[0, n]` survive. -/
lemma diagonalFinite_cechDoubleFunctor
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) :
    DiagonalFinite ((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  by_contra h
  exact hp (isZero_cechDoubleFunctor_X_X.{u, r, v, w} O 𝒰 Y p (n - p) (by simp at h; omega))

/-- **`zero_of_neg` for the Čech double complex**: it vanishes in negative Čech degree, the inner
index being extended by zero from `ℕ`. -/
lemma zero_of_neg_cechDoubleFunctor
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) (p q : ℤ) (hq : q < 0) :
    IsZero ((((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y).X p).X q) :=
  isZero_cechDoubleFunctor_X_X.{u, r, v, w} O 𝒰 Y p q (Or.inr hq)

/-- **The Čech complex of a complex of injective sheaves is exact in every positive degree**,
after the outer index has been extended by zero.  Off the range of the embedding the term is a
zero object and exactness is automatic; on it this is `cechSheafComplex_exactAt_of_injective`,
[Stacks, Tag 01EP], transported along `HomologicalComplex.extendXIso`. -/
lemma exactAt_cechDoubleOuter_X
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) [∀ i, Injective (Y.X i)]
    (p : ℤ) (k : ℕ) (hk : 0 < k) :
    (((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y).X p).ExactAt k := by
  by_cases hp : ∃ i : ℕ, (i : ℤ) = p
  · obtain ⟨i, hi⟩ := hp
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ k).2 ?_
    refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℕ) k).mapIso
        (HomologicalComplex.extendXIso ((cechDoubleNatFunctor.{u, r, v, w} O 𝒰).obj Y)
          ComplexShape.embeddingUpNat hi))).2 ?_
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ k).1
      (cechSheafComplex_exactAt_of_injective.{u, r, v, w} O 𝒰 (Y.X i) k hk)
  · refine (HomologicalComplex.exactAt_iff_isZero_homology _ k).2
      (Functor.map_isZero (HomologicalComplex.homologyFunctor
        (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) (ComplexShape.up ℕ) k) ?_)
    exact isZero_extend_X_of_not_exists _ p hp

/-- **`exactAt_of_ne_zero` for the Čech double complex of a complex of injective sheaves**: its
columns are exact away from Čech degree `0`.  In negative degree the column is supported away from
it, so `HomologicalComplex.extend_exactAt` applies with no input; in positive degree
`HomologicalComplex.extend_exactAt_iff` reduces to `exactAt_cechDoubleOuter_X`. -/
lemma exactAt_cechDoubleFunctor_X
    (Y : CochainComplex (SheafOfModules.{max u r v w} O) ℕ) [∀ i, Injective (Y.X i)]
    (p q : ℤ) (hq : q ≠ 0) :
    (((cechDoubleFunctor.{u, r, v, w} O 𝒰).obj Y).X p).ExactAt q := by
  rcases lt_or_gt_of_ne hq with h | h
  · exact HomologicalComplex.extend_exactAt _ ComplexShape.embeddingUpNat q
      fun j => by change ((j : ℕ) : ℤ) ≠ q; omega
  · have hk : ComplexShape.embeddingUpNat.f q.toNat = q := by
      change ((q.toNat : ℕ) : ℤ) = q; omega
    exact (HomologicalComplex.extend_exactAt_iff
      (((cechDoubleOuterFunctor.{u, r, v, w} O 𝒰).obj Y).X p)
      ComplexShape.embeddingUpNat hk).2
        (exactAt_cechDoubleOuter_X.{u, r, v, w} O 𝒰 Y p q.toNat (by omega))

section Resolution

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u r v w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u r v w}]
  [EnoughInjectives (SheafOfModules.{max u r v w} O)]

/-! #### The `Γ`-applied resolution and the right derived functor -/

/-- **Deliverable 1.** `Γ(U, I^•(F))`: the chosen injective resolution of `F`, evaluated on the
covered open `U`. -/
def gammaRes (F : SheafOfModules.{max u r v w} O) :
    CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℕ :=
  ((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex

/-- The morphism of evaluated resolutions attached to a morphism of sheaves, via the chosen
descent of that morphism to the chosen injective resolutions.  Functorial only up to homotopy. -/
def gammaResMap {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    gammaRes.{u, r, v, w} O 𝒰 F ⟶ gammaRes.{u, r, v, w} O 𝒰 G :=
  ((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- **Deliverable 2.** `gammaRes` extended by zero from `ℕ` to `ℤ`. -/
def gammaResZ (F : SheafOfModules.{max u r v w} O) :
    CochainComplex (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) ℤ :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).obj (gammaRes.{u, r, v, w} O 𝒰 F)

/-- `gammaResMap` extended by zero from `ℕ` to `ℤ`. -/
def gammaResZMap {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    gammaResZ.{u, r, v, w} O 𝒰 F ⟶ gammaResZ.{u, r, v, w} O 𝒰 G :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map (gammaResMap.{u, r, v, w} O 𝒰 f)

/-- A homotopy between two descents to the chosen injective resolutions induces a homotopy
between the induced morphisms of `ℤ`-extended evaluated complexes: evaluation is additive, and
extension by zero carries homotopies to homotopies. -/
def gammaResZHomotopy {F G : SheafOfModules.{max u r v w} O}
    {φ ψ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex}
    (H : Homotopy φ ψ) :
    Homotopy
      ((ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
        (((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ))
      ((ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
        (((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map ψ)) :=
  ((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).mapHomotopy H).extend
    ComplexShape.embeddingUpNat

/-- `gammaResZMap` sends an identity to the identity in homology. -/
lemma homologyMap_gammaResZMap_id (F : SheafOfModules.{max u r v w} O) (n : ℤ) :
    HomologicalComplex.homologyMap (gammaResZMap.{u, r, v, w} O 𝒰 (𝟙 F)) n = 𝟙 _ := by
  have h := (gammaResZHomotopy.{u, r, v, w} O 𝒰
    (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).homologyMap_eq n
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id] at h
  exact h

/-- `gammaResZMap` is multiplicative in homology. -/
lemma homologyMap_gammaResZMap_comp {F G H : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) (g : G ⟶ H) (n : ℤ) :
    HomologicalComplex.homologyMap (gammaResZMap.{u, r, v, w} O 𝒰 (f ≫ g)) n =
      HomologicalComplex.homologyMap (gammaResZMap.{u, r, v, w} O 𝒰 f) n ≫
        HomologicalComplex.homologyMap (gammaResZMap.{u, r, v, w} O 𝒰 g) n := by
  have h := (gammaResZHomotopy.{u, r, v, w} O 𝒰
    (InjectiveResolution.descCompHomotopy f g (injectiveResolution F) (injectiveResolution G)
      (injectiveResolution H))).homologyMap_eq n
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

/-- **Deliverable 3.** The `n`-th cohomology of the `Γ`-applied chosen injective resolution, as a
functor of the sheaf.  Functoriality is homotopy invariance of homology. -/
def gammaResZHomologyFunctor (n : ℕ) :
    SheafOfModules.{max u r v w} O ⥤ ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)) where
  obj F := (gammaResZ.{u, r, v, w} O 𝒰 F).homology (n : ℤ)
  map f := HomologicalComplex.homologyMap (gammaResZMap.{u, r, v, w} O 𝒰 f) (n : ℤ)
  map_id F := homologyMap_gammaResZMap_id.{u, r, v, w} O 𝒰 F (n : ℤ)
  map_comp f g := homologyMap_gammaResZMap_comp.{u, r, v, w} O 𝒰 f g (n : ℤ)

/-- Piece (a) of the comparison: in the degrees coming from `ℕ`, the cohomology of the
`ℤ`-extension is the cohomology of the original complex. -/
def gammaResExtendIso (n : ℕ) (F : SheafOfModules.{max u r v w} O) :
    (gammaResZ.{u, r, v, w} O 𝒰 F).homology (n : ℤ) ≅
      (gammaRes.{u, r, v, w} O 𝒰 F).homology n :=
  (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
    (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) n (n : ℤ) rfl).app
      (gammaRes.{u, r, v, w} O 𝒰 F)

/-- Piece (b) of the comparison: the right derived functor of evaluation computed by the chosen
injective resolution. -/
def gammaResRightDerivedIso (n : ℕ) (F : SheafOfModules.{max u r v w} O) :
    (gammaRes.{u, r, v, w} O 𝒰 F).homology n ≅
      ((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).rightDerived n).obj F :=
  ((injectiveResolution F).isoRightDerivedObj
    (SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)) n).symm

/-- The morphism in `ℕ`-indexed cohomology induced by `gammaResMap`, with its type written using
`gammaRes`.  This is the common middle term of the two naturality squares below. -/
def gammaResHomologyMap (n : ℕ) {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    (gammaRes.{u, r, v, w} O 𝒰 F).homology n ⟶ (gammaRes.{u, r, v, w} O 𝒰 G).homology n :=
  HomologicalComplex.homologyMap (gammaResMap.{u, r, v, w} O 𝒰 f) n

/-- `gammaResExtendIso` is natural: this is the naturality of
`ComplexShape.Embedding.extendFunctorHomologyIso` at `gammaResMap`. -/
lemma gammaResExtendIso_hom_naturality (n : ℕ) {F G : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) :
    HomologicalComplex.homologyMap (gammaResZMap.{u, r, v, w} O 𝒰 f) (n : ℤ) ≫
        (gammaResExtendIso.{u, r, v, w} O 𝒰 n G).hom =
      (gammaResExtendIso.{u, r, v, w} O 𝒰 n F).hom ≫
        gammaResHomologyMap.{u, r, v, w} O 𝒰 n f :=
  (ComplexShape.embeddingUpNat.extendFunctorHomologyIso
    (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U))) n (n : ℤ) rfl).hom.naturality
      (gammaResMap.{u, r, v, w} O 𝒰 f)

/-- `gammaResRightDerivedIso` is natural: this is
`CategoryTheory.InjectiveResolution.isoRightDerivedObj_inv_naturality` for the chosen descent,
whose compatibility in degree zero is `InjectiveResolution.desc_commutes_zero`. -/
lemma gammaResRightDerivedIso_hom_naturality (n : ℕ) {F G : SheafOfModules.{max u r v w} O}
    (f : F ⟶ G) :
    gammaResHomologyMap.{u, r, v, w} O 𝒰 n f ≫
        (gammaResRightDerivedIso.{u, r, v, w} O 𝒰 n G).hom =
      (gammaResRightDerivedIso.{u, r, v, w} O 𝒰 n F).hom ≫
        ((SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).rightDerived n).map f :=
  (InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution G)
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution G) (injectiveResolution F))
    (SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)) n).symm

/-- **Deliverable 4.**  The cohomology of the `Γ`-applied chosen injective resolution *is* the
right derived functor of `Γ = ` evaluation on the covered open, naturally in the sheaf. -/
def gammaResZHomologyIso (n : ℕ) :
    gammaResZHomologyFunctor.{u, r, v, w} O 𝒰 n ≅
      (SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).rightDerived n :=
  NatIso.ofComponents
    (fun F => gammaResExtendIso.{u, r, v, w} O 𝒰 n F ≪≫
      gammaResRightDerivedIso.{u, r, v, w} O 𝒰 n F)
    (fun {F G} f => by
      dsimp only [gammaResZHomologyFunctor, Iso.trans_hom]
      rw [← Category.assoc, gammaResExtendIso_hom_naturality.{u, r, v, w} O 𝒰 n f,
        Category.assoc, gammaResRightDerivedIso_hom_naturality.{u, r, v, w} O 𝒰 n f,
        Category.assoc])

/-! #### The augmentation into the zeroth row, and the comparison -/

/-- **The augmentation `Γ(U, I^•(F)) ⟶ rowZero(K^{•,•}(F))`**: the degreewise Čech augmentation of
the chosen injective resolution, extended by zero to `ℤ`, followed by the identification
`rowZeroIsoApp` of the zeroth row of the Čech double complex with that extension. -/
noncomputable def cechAlphaNat (F : SheafOfModules.{max u r v w} O) :
    gammaRes.{u, r, v, w} O 𝒰 F ⟶
      (rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex :=
  (cechAugNatComplex.{u, r, v, w} O 𝒰).app (injectiveResolution F).cocomplex

/-- **`cechAlphaNat` is natural in the sheaf**, for the chosen descent to the chosen injective
resolutions.  This is the naturality of `cechAugNatComplex`, which is free: that is a natural
transformation.  Named at the `gammaRes` spelling so that the square of `cechAlpha_naturality` is
reassociable -- `gammaRes O 𝒰 F` and the value of
`(SheafOfModules.evaluation O (op 𝒰.U)).mapHomologicalComplex` at the chosen resolution are
`rfl`-equal but not syntactically so. -/
theorem cechAlphaNat_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    cechAlphaNat.{u, r, v, w} O 𝒰 F ≫ (rowZeroNatFunctor.{u, r, v, w} O 𝒰).map
        (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F)) =
      gammaResMap.{u, r, v, w} O 𝒰 f ≫ cechAlphaNat.{u, r, v, w} O 𝒰 G :=
  ((cechAugNatComplex.{u, r, v, w} O 𝒰).naturality _).symm

/-- `rowZeroIsoApp` at the chosen injective resolution, named at the `cechDouble` spelling so
that the square of `cechAlpha_naturality` is reassociable. -/
noncomputable def cechRowZeroIso (F : SheafOfModules.{max u r v w} O) :
    rowZero (cechDouble.{u, r, v, w} O 𝒰 F) ≅
      (ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).obj
        ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex) :=
  rowZeroIsoApp.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex

/-- `cechRowZeroIso` is natural, at the `cechDoubleMap` spelling. -/
theorem cechRowZeroIso_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    rowZeroMap (cechDoubleMap.{u, r, v, w} O 𝒰 f) ≫
        (cechRowZeroIso.{u, r, v, w} O 𝒰 G).hom =
      (cechRowZeroIso.{u, r, v, w} O 𝒰 F).hom ≫
        (ComplexShape.embeddingUpNat.extendFunctor
            (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
          ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).map
            (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))) :=
  rowZeroIsoApp_naturality.{u, r, v, w} O 𝒰
    (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))

/-- **The components of `cechRowZeroIso`**, against the index convention of
`cechDoubleFunctorXIso`.

The hypothesis `(i : ℤ) = i'` is taken in *both* of its forms, and deliberately:
`cechDoubleFunctorXIso` asks for it reduced and `HomologicalComplex.extendXIso` asks for it as
`ComplexShape.embeddingUpNat.f i = i'`; the two are interchangeable only at default transparency,
while `rw` works at `instances` transparency, so a single hypothesis leaves one of the two
applications opaque to it.  They are proofs of the same proposition, so proof irrelevance makes
the resulting terms equal. -/
theorem cechRowZeroIso_inv_f (F : SheafOfModules.{max u r v w} O) (i : ℕ) (i' : ℤ)
    (hi : (i : ℤ) = i') (hi' : ComplexShape.embeddingUpNat.f i = i') :
    (cechRowZeroIso.{u, r, v, w} O 𝒰 F).inv.f i' =
      (HomologicalComplex.extendXIso
        ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex)
        ComplexShape.embeddingUpNat hi').hom ≫
      (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
        hi rfl).inv := by
  have hhom : (cechRowZeroIso.{u, r, v, w} O 𝒰 F).hom.f i' =
      (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
          hi rfl).hom ≫
        (HomologicalComplex.extendXIso
          ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex)
          ComplexShape.embeddingUpNat hi').inv :=
    (Iso.eq_comp_inv _).2
      (rowZeroIsoApp_hom_f_comp.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i i' hi)
  exact congrArg Iso.inv (Iso.ext
    (α := (HomologicalComplex.eval (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))
      (ComplexShape.up ℤ) i').mapIso (cechRowZeroIso.{u, r, v, w} O 𝒰 F))
    (β := cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
        hi rfl ≪≫
      (HomologicalComplex.extendXIso
        ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex)
        ComplexShape.embeddingUpNat hi').symm) hhom)

/-- `cechAlphaNat` extended by zero to `ℤ`.  Named at the `gammaResZ` spelling, for the same
reason `cechAlphaNat` is named at the `gammaRes` spelling. -/
noncomputable def cechAlphaZ (F : SheafOfModules.{max u r v w} O) :
    gammaResZ.{u, r, v, w} O 𝒰 F ⟶
      (ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).obj
        ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex) :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map (cechAlphaNat.{u, r, v, w} O 𝒰 F)

/-- `cechAlphaZ` is natural: `cechAlphaNat_naturality` with extension by zero applied to it. -/
theorem cechAlphaZ_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    cechAlphaZ.{u, r, v, w} O 𝒰 F ≫
        (ComplexShape.embeddingUpNat.extendFunctor
            (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
          ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).map
            (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))) =
      gammaResZMap.{u, r, v, w} O 𝒰 f ≫ cechAlphaZ.{u, r, v, w} O 𝒰 G := by
  have h := congrArg
    (ComplexShape.embeddingUpNat.extendFunctor
      (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
    (cechAlphaNat_naturality.{u, r, v, w} O 𝒰 f)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- **The augmentation `Γ(U, I^•(F)) ⟶ rowZero(K^{•,•}(F))`**: the degreewise Čech augmentation of
the chosen injective resolution, extended by zero to `ℤ`, followed by the identification
`rowZeroIsoApp` of the zeroth row of the Čech double complex with that extension. -/
noncomputable def cechAlpha (F : SheafOfModules.{max u r v w} O) :
    gammaResZ.{u, r, v, w} O 𝒰 F ⟶ rowZero (cechDouble.{u, r, v, w} O 𝒰 F) :=
  cechAlphaZ.{u, r, v, w} O 𝒰 F ≫ (cechRowZeroIso.{u, r, v, w} O 𝒰 F).inv

/-- **The augmentation is natural in the sheaf.**  `cechAugNatComplex` is a natural
transformation, so its square for the chosen descent `CategoryTheory.InjectiveResolution.desc`
holds on the nose; `rowZeroIsoApp_naturality` is the other square. -/
theorem cechAlpha_naturality {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G) :
    cechAlpha.{u, r, v, w} O 𝒰 F ≫ rowZeroMap (cechDoubleMap.{u, r, v, w} O 𝒰 f) =
      gammaResZMap.{u, r, v, w} O 𝒰 f ≫ cechAlpha.{u, r, v, w} O 𝒰 G := by
  have h1 : (cechRowZeroIso.{u, r, v, w} O 𝒰 F).inv ≫
        rowZeroMap (cechDoubleMap.{u, r, v, w} O 𝒰 f) =
      (ComplexShape.embeddingUpNat.extendFunctor
          (ModuleCat.{max u r v w} (O.obj.obj (op 𝒰.U)))).map
        ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).map
          (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F))) ≫
      (cechRowZeroIso.{u, r, v, w} O 𝒰 G).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← cechRowZeroIso_naturality.{u, r, v, w} O 𝒰 f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [cechAlpha, cechAlpha, Category.assoc, h1, ← Category.assoc,
    cechAlphaZ_naturality.{u, r, v, w} O 𝒰 f, Category.assoc]

/-- **Three of the four hypotheses of [Stacks, Tag 0133] for the Čech double complex of the chosen
injective resolution.**  Only `inducesIsoKernel` -- that the augmentation is a kernel of the first
Čech differential in each resolution degree -- is left as an argument; the other three are proved
above and depend on nothing about the augmentation. -/
theorem cechHypotheses (F : SheafOfModules.{max u r v w} O)
    (α : gammaResZ.{u, r, v, w} O 𝒰 F ⟶ rowZero (cechDouble.{u, r, v, w} O 𝒰 F))
    (hker : ∀ p : ℤ, ∃ hα : α.f p ≫ ((cechDouble.{u, r, v, w} O 𝒰 F).X p).d 0 1 = 0,
      IsIso (kernel.lift (((cechDouble.{u, r, v, w} O 𝒰 F).X p).d 0 1) (α.f p) hα)) :
    Hypotheses (gammaResZ.{u, r, v, w} O 𝒰 F) (cechDouble.{u, r, v, w} O 𝒰 F) α where
  diagonalFinite :=
    diagonalFinite_cechDoubleFunctor.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex
  zero_of_neg :=
    zero_of_neg_cechDoubleFunctor.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex
  exactAt_of_ne_zero :=
    exactAt_cechDoubleFunctor_X.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex
  inducesIsoKernel := hker

/-- **`H^n(Γ(U, I^•(F))) ≅ H^n(Tot(Č^•(𝒰, I^•(F))))`, naturally in `F`**, given an augmentation
satisfying the hypotheses of [Stacks, Tag 0133] and natural in `F`.

At each sheaf this is `comparisonHomologyIso`, the isomorphism the comparison map of
[Stacks, Tag 0133] induces on cohomology; its naturality is `comparisonMapP_naturality` with
homology applied to it.  Both are available because that comparison map is *data* and not a chosen
witness of an existential. -/
def abutmentIsoOfAlpha (n : ℕ)
    (α : ∀ F : SheafOfModules.{max u r v w} O,
      gammaResZ.{u, r, v, w} O 𝒰 F ⟶ rowZero (cechDouble.{u, r, v, w} O 𝒰 F))
    (hα : ∀ F : SheafOfModules.{max u r v w} O,
      Hypotheses (gammaResZ.{u, r, v, w} O 𝒰 F) (cechDouble.{u, r, v, w} O 𝒰 F) (α F))
    (hnat : ∀ {F G : SheafOfModules.{max u r v w} O} (f : F ⟶ G),
      α F ≫ rowZeroMap (cechDoubleMap.{u, r, v, w} O 𝒰 f) =
        gammaResZMap.{u, r, v, w} O 𝒰 f ≫ α G) :
    gammaResZHomologyFunctor.{u, r, v, w} O 𝒰 n ≅
      cechFiltrationFunctor.{u, r, v, w} O 𝒰 (n : ℤ) ⋙ CategoryTheory.FilteredObject.forget :=
  NatIso.ofComponents
    (fun F => comparisonHomologyIso (gammaResZ.{u, r, v, w} O 𝒰 F)
      (cechDouble.{u, r, v, w} O 𝒰 F) (α F) (hα F) (n : ℤ))
    (fun {F G} f => by
      have hsq := congrArg (fun u => HomologicalComplex.homologyMap u (n : ℤ))
        (comparisonMapP_naturality (gammaResZ.{u, r, v, w} O 𝒰 F)
          (cechDouble.{u, r, v, w} O 𝒰 F) (α F) (hα F) (hα G)
          (gammaResZMap.{u, r, v, w} O 𝒰 f) (cechDoubleMap.{u, r, v, w} O 𝒰 f) (hnat f))
      simp only [HomologicalComplex.homologyMap_comp] at hsq
      exact hsq.symm)

/-! #### The kernel clause of [Stacks, Tag 0133] -/

/-- **The components of `cechAlpha` on the range of the embedding**, against the index convention
of `cechDoubleFunctorXIso`.  Both forms of the hypothesis `(i : ℤ) = i'` are taken, for the reason
recorded on `cechRowZeroIso_inv_f`. -/
theorem cechAlpha_f (F : SheafOfModules.{max u r v w} O) (i : ℕ) (i' : ℤ) (hi : (i : ℤ) = i')
    (hi' : ComplexShape.embeddingUpNat.f i = i') :
    (cechAlpha.{u, r, v, w} O 𝒰 F).f i' =
      ((HomologicalComplex.extendXIso (gammaRes.{u, r, v, w} O 𝒰 F)
            ComplexShape.embeddingUpNat hi').hom ≫
          (cechAlphaNat.{u, r, v, w} O 𝒰 F).f i) ≫
        (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
          hi rfl).inv := by
  have h1 : (cechAlphaZ.{u, r, v, w} O 𝒰 F).f i' ≫
        (HomologicalComplex.extendXIso
          ((rowZeroNatFunctor.{u, r, v, w} O 𝒰).obj (injectiveResolution F).cocomplex)
          ComplexShape.embeddingUpNat hi').hom =
      (HomologicalComplex.extendXIso (gammaRes.{u, r, v, w} O 𝒰 F)
        ComplexShape.embeddingUpNat hi').hom ≫ (cechAlphaNat.{u, r, v, w} O 𝒰 F).f i :=
    HomologicalComplex.extendMap_f_comp_extendXIso (cechAlphaNat.{u, r, v, w} O 𝒰 F)
      ComplexShape.embeddingUpNat hi'
  have hz : (cechAlpha.{u, r, v, w} O 𝒰 F).f i' =
      (cechAlphaZ.{u, r, v, w} O 𝒰 F).f i' ≫ (cechRowZeroIso.{u, r, v, w} O 𝒰 F).inv.f i' := rfl
  rw [hz, cechRowZeroIso_inv_f.{u, r, v, w} O 𝒰 F i i' hi hi']
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰
      (injectiveResolution F).cocomplex i 0 i' 0 hi rfl).inv) h1)

/-- **The degree-`i` component of `cechAlphaNat` is the Čech augmentation**, once its source is
read as sections over the covered open through `sectionsTerminalFunctorIso`. -/
theorem sectionsTerminal_comp_cechAlphaNat_f (F : SheafOfModules.{max u r v w} O) (i : ℕ) :
    (CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).hom.app
          ((injectiveResolution F).cocomplex.X i) ≫ (cechAlphaNat.{u, r, v, w} O 𝒰 F).f i =
      CechSheaf.cechAugmentation.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)
        ((injectiveResolution F).cocomplex.X i) := by
  have hn : (cechAlphaNat.{u, r, v, w} O 𝒰 F).f i =
      (CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).inv.app
          ((injectiveResolution F).cocomplex.X i) ≫
        CechSheaf.cechAugmentation.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)
          ((injectiveResolution F).cocomplex.X i) := rfl
  rw [hn]
  exact Iso.hom_inv_id_app_assoc (CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U)
    ((injectiveResolution F).cocomplex.X i) _

/-- **The first square the kernel clause needs**: the Čech augmentation of `I^i(F)`, followed by
the index convention, is `cechAlpha` in degree `i` precomposed with the identification of the
source.

Hoisted into a theorem of its own and stated in a single spelling, deliberately.  Proved inside
`isIso_kernelLift_of_iso` it would be a goal mixing the `CechSheaf.sectionsPresheaf`, `gammaRes`
and `cechDouble` spellings, and `rw` builds its motive at `instances` transparency, where such a
goal is not type-correct; stated separately, each rewrite stays inside one spelling and the
composition is finished in term mode, which is checked at default transparency. -/
theorem cechAugmentation_comp_cechDoubleFunctorXIso_inv (F : SheafOfModules.{max u r v w} O)
    (i : ℕ) (i' : ℤ) (hi : (i : ℤ) = i')
    (hi' : ComplexShape.embeddingUpNat.f i = i') :
    CechSheaf.cechAugmentation.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)
          ((injectiveResolution F).cocomplex.X i) ≫
        (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
          hi rfl).inv =
      ((CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).hom.app
            ((injectiveResolution F).cocomplex.X i) ≫
          (HomologicalComplex.extendXIso (gammaRes.{u, r, v, w} O 𝒰 F)
            ComplexShape.embeddingUpNat hi').inv) ≫
        (cechAlpha.{u, r, v, w} O 𝒰 F).f i' := by
  rw [cechAlpha_f.{u, r, v, w} O 𝒰 F i i' hi hi']
  refine Eq.symm (Eq.trans (Category.assoc _ _ _).symm (Eq.trans
    (congrArg (fun z => z ≫ (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰
      (injectiveResolution F).cocomplex i 0 i' 0 hi rfl).inv) ?_) rfl))
  exact Eq.trans (Category.assoc _ _ _) (Eq.trans
    (congrArg (fun z => (CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).hom.app
        ((injectiveResolution F).cocomplex.X i) ≫ z)
      (Iso.inv_hom_id_assoc (HomologicalComplex.extendXIso (gammaRes.{u, r, v, w} O 𝒰 F)
        ComplexShape.embeddingUpNat hi') ((cechAlphaNat.{u, r, v, w} O 𝒰 F).f i)))
    (sectionsTerminal_comp_cechAlphaNat_f.{u, r, v, w} O 𝒰 F i))

/-- **The second square the kernel clause needs**: the index convention is compatible with the
first Čech differential, read with the isomorphisms inverted.  This is
`cechDoubleFunctorXIso_comm` conjugated, and like the first square it is hoisted out so that no
rewrite has to span two spellings. -/
theorem cechDoubleFunctorXIso_inv_comm (F : SheafOfModules.{max u r v w} O)
    (i : ℕ) (i' : ℤ) (hi : (i : ℤ) = i') :
    ((cechComplexFunctor.{u, r, v, w} O 𝒰).obj
            ((SheafOfModules.forget O).obj ((injectiveResolution F).cocomplex.X i))).d 0 1 ≫
        (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 1 i' 1
          hi rfl).inv =
      (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
          hi rfl).inv ≫ ((cechDouble.{u, r, v, w} O 𝒰 F).X i').d 0 1 :=
  (Iso.eq_inv_comp _).2 ((Category.assoc _ _ _).symm.trans
    ((Iso.comp_inv_eq _).2
      (cechDoubleFunctorXIso_comm.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i i' hi
        0 1 0 1 rfl rfl).symm))

/-- **The kernel clause of [Stacks, Tag 0133] for the Čech double complex, on the range of the
embedding**: the augmentation is a kernel of the first Čech differential in each resolution
degree.

This is the degree-zero clause of [Stacks, Tag 01EP],
`Stacks.Cohomology.CechSheaf.isIso_kernelLift_cechAugmentation`, transported by
`isIso_kernelLift_of_iso` along the comparison isomorphisms of the two extensions by zero. -/
theorem isIso_kernelLift_cechAlpha_f (F : SheafOfModules.{max u r v w} O) (i : ℕ) (i' : ℤ)
    (hi : (i : ℤ) = i') (hi' : ComplexShape.embeddingUpNat.f i = i')
    (hα : (cechAlpha.{u, r, v, w} O 𝒰 F).f i' ≫
      ((cechDouble.{u, r, v, w} O 𝒰 F).X i').d 0 1 = 0) :
    IsIso (kernel.lift (((cechDouble.{u, r, v, w} O 𝒰 F).X i').d 0 1)
      ((cechAlpha.{u, r, v, w} O 𝒰 F).f i') hα) := by
  refine isIso_kernelLift_of_iso
    (CechSheaf.cechAugmentation_comp_d.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)
      ((injectiveResolution F).cocomplex.X i)) hα
    ((CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).app
        ((injectiveResolution F).cocomplex.X i) ≪≫
      (HomologicalComplex.extendXIso (gammaRes.{u, r, v, w} O 𝒰 F)
        ComplexShape.embeddingUpNat hi').symm)
    (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 i' 0
      hi rfl).symm
    (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 1 i' 1
      hi rfl).symm ?_ ?_
    (CechSheaf.isIso_kernelLift_cechAugmentation.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)
      ((injectiveResolution F).cocomplex.X i))
  · exact cechAugmentation_comp_cechDoubleFunctorXIso_inv.{u, r, v, w} O 𝒰 F i i' hi hi'
  · exact cechDoubleFunctorXIso_inv_comm.{u, r, v, w} O 𝒰 F i i' hi

/-- **`inducesIsoKernel` of [Stacks, Tag 0133] for the Čech double complex of the chosen injective
resolution** -- the fourth and last of its hypotheses.

On the range of the embedding this is `isIso_kernelLift_cechAlpha_f`, the degree-zero clause of
[Stacks, Tag 01EP] transported.  Off the range both the extended resolution and the Čech double
complex vanish, so the comparison with the kernel is a morphism between zero objects. -/
theorem inducesIsoKernel_cechAlpha (F : SheafOfModules.{max u r v w} O) (p : ℤ) :
    ∃ hα : (cechAlpha.{u, r, v, w} O 𝒰 F).f p ≫
        ((cechDouble.{u, r, v, w} O 𝒰 F).X p).d 0 1 = 0,
      IsIso (kernel.lift (((cechDouble.{u, r, v, w} O 𝒰 F).X p).d 0 1)
        ((cechAlpha.{u, r, v, w} O 𝒰 F).f p) hα) := by
  by_cases hp : ∃ i : ℕ, (i : ℤ) = p
  · obtain ⟨i, hi⟩ := hp
    have hi' : ComplexShape.embeddingUpNat.f i = p := by simpa using hi
    have hα : (cechAlpha.{u, r, v, w} O 𝒰 F).f p ≫
        ((cechDouble.{u, r, v, w} O 𝒰 F).X p).d 0 1 = 0 :=
      comp_eq_zero_of_iso
        (CechSheaf.cechAugmentation_comp_d.{u, r, max u r v w, w} 𝒰.U 𝒰.obj (covers' 𝒰)
          ((injectiveResolution F).cocomplex.X i))
        ((CechSheaf.sectionsTerminalFunctorIso.{u, r, max u r v w} 𝒰.U).app
            ((injectiveResolution F).cocomplex.X i) ≪≫
          (HomologicalComplex.extendXIso (gammaRes.{u, r, v, w} O 𝒰 F)
            ComplexShape.embeddingUpNat hi').symm)
        (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 0 p 0
          hi rfl).symm
        (cechDoubleFunctorXIso.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex i 1 p 1
          hi rfl).symm
        (cechAugmentation_comp_cechDoubleFunctorXIso_inv.{u, r, v, w} O 𝒰 F i p hi hi')
        (cechDoubleFunctorXIso_inv_comm.{u, r, v, w} O 𝒰 F i p hi)
    exact ⟨hα, isIso_kernelLift_cechAlpha_f.{u, r, v, w} O 𝒰 F i p hi hi' hα⟩
  · have hsrc : IsZero ((gammaResZ.{u, r, v, w} O 𝒰 F).X p) :=
      isZero_extend_X_of_not_exists _ p hp
    have htgt : IsZero ((((cechDouble.{u, r, v, w} O 𝒰 F).X p)).X 0) :=
      isZero_cechDoubleFunctor_X_X.{u, r, v, w} O 𝒰 (injectiveResolution F).cocomplex p 0
        (Or.inl (not_le.1 fun h => hp ⟨p.toNat, by omega⟩))
    exact ⟨hsrc.eq_of_src _ _,
      StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _ hsrc (isZero_kernel_of_isZero _ htgt)⟩

/-! #### The abutment asserted by [Stacks, Tag 01ES] -/

/-- **All four hypotheses of [Stacks, Tag 0133] for the Čech double complex of the chosen injective
resolution.** -/
theorem cechHypothesesFull (F : SheafOfModules.{max u r v w} O) :
    Hypotheses (gammaResZ.{u, r, v, w} O 𝒰 F) (cechDouble.{u, r, v, w} O 𝒰 F)
      (cechAlpha.{u, r, v, w} O 𝒰 F) :=
  cechHypotheses.{u, r, v, w} O 𝒰 F (cechAlpha.{u, r, v, w} O 𝒰 F)
    (inducesIsoKernel_cechAlpha.{u, r, v, w} O 𝒰 F)

/-- **`H^n(Tot(Č^•(𝒰, I^•(F)))) ≅ R^nΓ_{𝒰.U}(F)`, naturally in `F`.**  The convergence half of
[Stacks, Tag 01ES]: the cohomology of the total complex of the Čech double complex, which is what
the functorial filtered abutment of `cechFunctorialAbutment` abuts to, is the derived evaluation
functor on the covered open, which is what the tag asserts it abuts to.

`abutmentIsoOfAlpha` identifies it with `H^n(Γ(𝒰.U, I^•(F)))` by [Stacks, Tag 0133], and
`gammaResZHomologyIso` identifies that with `R^nΓ_{𝒰.U}(F)`. -/
def cechAbutmentIso (n : ℕ) :
    cechFiltrationFunctor.{u, r, v, w} O 𝒰 (n : ℤ) ⋙ CategoryTheory.FilteredObject.forget ≅
      (SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).rightDerived n :=
  (abutmentIsoOfAlpha.{u, r, v, w} O 𝒰 n (cechAlpha.{u, r, v, w} O 𝒰)
      (cechHypothesesFull.{u, r, v, w} O 𝒰)
      (fun f => cechAlpha_naturality.{u, r, v, w} O 𝒰 f)).symm ≪≫
    gammaResZHomologyIso.{u, r, v, w} O 𝒰 n

/-- **The functorial filtered abutment of the Čech-to-cohomology spectral sequence, abutting to
cohomology on the covered open.**  This is the `abutment` field of [Stacks, Tag 01ES]:
`cechFunctorialAbutment` with its abutment transported along `cechAbutmentIso` by
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.ofIsoAbutment`. -/
def cechAbutment :
    FunctorialFirstQuadrantAbutsTo (cechSpectralSequenceFunctor.{u, r, v, w} O 𝒰)
      (fun n => (SheafOfModules.evaluation.{max u r v w} O (op 𝒰.U)).rightDerived n) :=
  (cechFunctorialAbutment.{u, r, v, w} O 𝒰).ofIsoAbutment (cechAbutmentIso.{u, r, v, w} O 𝒰)

end Resolution

end Stacks.Cohomology.CechSpectral

end
