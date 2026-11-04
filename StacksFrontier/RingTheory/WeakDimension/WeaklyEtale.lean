module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.RingTheory.Etale.Weakly
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.Module
public import StacksFrontier.Homology.TorAmplitude.Termwise
public import StacksFrontier.RingTheory.WeaklyEtale.Defs
public import StacksFrontier.RingTheory.WeaklyEtale.Flat

@[expose] public section

/-!
# Weak dimension under weakly étale ring maps

A weakly étale algebra over a commutative ring of weak dimension at most `d` again has weak
dimension at most `d`.

## Main results

* `hasWeakDimensionLE_of_weaklyEtale`: Stacks 092E — a weakly étale algebra over a commutative
  ring of weak dimension at most `d` also has weak dimension at most `d`.

## Implementation notes

**Universes.** The ring `A` lives in `Type u`, the ring `B` in `Type v`, and the two universes
are *independent*: the hypothesis is about `ModuleCat.{u} A` and the conclusion about
`ModuleCat.{v} B`, with no `ULift` anywhere in the statement. Internally the restriction of
scalars of a `B`-module is an `A`-module in `Type v`, so the auxiliary material is stated with
the ring universe and the module universe independent, and the termwise tensor product of a
complex of `A`-modules in `Type v` with an `A`-module in `Type u` lands in `Type (max u v)`.

**Source modules.** Weak dimension is `HasWeakDimensionLE` of
`StacksFrontier.RingTheory.WeaklyEtale.Defs` (Stacks 092D). The reduction of a Tor-dimension bound
to the existence of a flat resolution is `hasTorDimensionLE_iff_hasFlatRepresentative` of
`StacksFrontier.Homology.TorAmplitude.Module` (Stacks 066F); it is used in both directions, on `A`
to read off flat resolutions from the hypothesis and on `B` to establish the conclusion. Descent
of flatness along a weakly étale map is `flat_of_flat_of_mul_flat` of
`StacksFrontier.RingTheory.WeaklyEtale.Flat` (Stacks 092C). The certified derived tensor product
exhibited in the conclusion is assembled from `termwiseDerived` of
`StacksFrontier.Homology.TorAmplitude.Comparison`, whose construction rests on Stacks 06Y0,
`CochainComplex.KFlat.kFlat_tright_preserves_quasiIso` of
`StacksFrontier.Homology.KFlat.QuasiIso`, and on Stacks 064K.

**Why the flat-cokernel step is restated.** The derived form of Stacks 0653,
`cokernel_flat_of_torAmplitude` of `StacksFrontier.Homology.TorAmplitude.DerivedComparison`, is
stated for a complex in `ModuleCat.{max u v} R` with `R : Type u`, and it needs a certified
derived tensor product over that module category. The complex relevant here lives in
`ModuleCat.{v} A` with `A : Type u`, which is not of that shape, and no certified derived tensor
product over it is available. Flatness of the cokernel is therefore obtained directly from the
flatness criterion with test modules in the ring's own universe
(`Module.Flat.iff_lTensor_preserves_injective_linearMap'`) together with
`StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact` of
`StacksFrontier.Homology.TorAmplitude.Termwise`; only the categorical unfolding is restated.

**Why the vanishing is proved by dévissage.** The source argument says that the restriction of
scalars of a `B`-module has Tor dimension at most `d` over `A`, which is the hypothesis applied
to an `A`-module. That module lives in `Type v` while the hypothesis quantifies over
`ModuleCat.{u} A`, so it cannot be applied to it directly. Instead the required vanishing
`H^{-d-1}(K ⊗_A N) = 0`, for `K` a complex of flat `A`-modules exact outside degree `0` and `N`
an `A`-module in the universe of `A`, is proved by dévissage along the flat resolution of `N`
supplied by the hypothesis: the images of the differentials of that resolution give short exact
sequences of `A`-modules, tensoring with `K` keeps them short exact because `K` is termwise
flat, and the connecting map of the resulting long exact sequence moves the vanishing one degree
at a time.

## References

* [The Stacks Project, Tag 092E](https://stacks.math.columbia.edu/tag/092E)
* [Olivier, *Anneaux absolument plats universels et épimorphismes à buts réduits*][Olivier-AF]
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.WeakDimension

/-! ### A certified derived tensor product -/

variable {R : Type u} [CommRing R]

/-- Tensoring on the right, read as a functor of the module one tensors with. -/
private noncomputable def tensorByModule :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj N := StacksDraft.TorAmplitude.tensorModuleRight N
  map f :=
    { app := fun X => ModuleCat.ofHom (LinearMap.lTensor X f.hom)
      naturality := by
        intro X Y g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl }
  map_id N := by
    ext X : 2
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp f g := by
    ext X : 2
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

private instance (N : ModuleCat.{u} R) : (tensorByModule.obj N).Additive :=
  inferInstanceAs (StacksDraft.TorAmplitude.tensorModuleRight N).Additive

/-- The map of termwise tensor complexes, followed by the localization, induced by a map of
modules. -/
private noncomputable def termwiseTensorMap {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶
      (StacksDraft.TorAmplitude.tensorModuleRight N').mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (tensorByModule.map f) (ComplexShape.up ℤ))
    DerivedCategory.Q

private lemma termwiseTensorMap_id (N : ModuleCat.{u} R) :
    termwiseTensorMap (𝟙 N) = 𝟙 _ := by
  dsimp only [termwiseTensorMap]
  rw [tensorByModule.map_id, NatTrans.mapHomologicalComplex_id]
  ext K
  simp only [Functor.whiskerRight_app, NatTrans.id_app]
  exact DerivedCategory.Q.map_id _

private lemma termwiseTensorMap_comp {N N' N'' : ModuleCat.{u} R} (f : N ⟶ N') (g : N' ⟶ N'') :
    termwiseTensorMap (f ≫ g) = termwiseTensorMap f ≫ termwiseTensorMap g := by
  dsimp only [termwiseTensorMap]
  rw [tensorByModule.map_comp, NatTrans.mapHomologicalComplex_comp]
  ext K
  simp only [Functor.whiskerRight_app, NatTrans.comp_app, Functor.map_comp]
  rfl

/-- The total left derived functor of termwise tensoring, as a functor of the module. -/
private noncomputable def derivedTensorByModule :
    ModuleCat.{u} R ⥤ DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) where
  obj N := StacksDraft.TorAmplitude.termwiseDerived N
  map {N N'} f :=
    Functor.leftDerivedNatTrans (StacksDraft.TorAmplitude.termwiseDerived N)
      (StacksDraft.TorAmplitude.termwiseDerived N')
      (StacksDraft.TorAmplitude.termwiseDerivedCounit N)
      (StacksDraft.TorAmplitude.termwiseDerivedCounit N')
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (termwiseTensorMap f)
  map_id N := by
    rw [termwiseTensorMap_id]
    simp
  map_comp f g := by
    rw [termwiseTensorMap_comp]
    simp

/-- The zeroth cohomology of a module placed in degree zero is that module. -/
private noncomputable def homologySingleIso (N : ModuleCat.{u} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ≅ N :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N

/-- A derived tensor product on `D(R)`: in the variable that the certification constrains it is
the total left derived functor of termwise tensoring, and in the other variable it reads off the
zeroth cohomology, which the certification leaves free. -/
private noncomputable def certifiedTensor :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0 ⋙ derivedTensorByModule).flip

/-- Tensoring with `N` and tensoring with the zeroth cohomology of `N` placed in degree zero
agree. -/
private noncomputable def certifiedIso (N : ModuleCat.{u} R) :
    StacksDraft.TorAmplitude.termwiseDerived N ≅
      (certifiedTensor (R := R)).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) :=
  derivedTensorByModule.mapIso (homologySingleIso N).symm

/-- The comparison of `certifiedTensor` with the termwise tensor product. -/
private noncomputable def certifiedComparison (N : ModuleCat.{u} R) :
    DerivedCategory.Q ⋙
        (certifiedTensor (R := R)).flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
      (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerLeft DerivedCategory.Q (certifiedIso N).inv ≫
    StacksDraft.TorAmplitude.termwiseDerivedCounit N

/-- `certifiedTensor` is certified: tensoring with a module placed in degree zero is the total
left derived functor of the termwise tensor product, with comparison `certifiedComparison`. -/
private lemma certifiedIsLeftDerived (N : ModuleCat.{u} R) :
    ((certifiedTensor (R := R)).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
      (certifiedComparison N)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  refine (Functor.isLeftDerivedFunctor_iff_of_iso
      (LF := StacksDraft.TorAmplitude.termwiseDerived N)
      (α := StacksDraft.TorAmplitude.termwiseDerivedCounit N)
      (LF' := (certifiedTensor (R := R)).flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))
      (α' := certifiedComparison N)
      (W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (e := certifiedIso N)
      (comm := ?_)).1
    (StacksDraft.TorAmplitude.isLeftDerivedFunctor_termwiseDerivedCounit N)
  dsimp only [certifiedComparison]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id]
  simp

/-! ### Termwise tensoring with a module in the ring's own universe -/

variable {A : Type u} [CommRing A]

/-- Tensoring on the right by an `A`-module in the universe of `A`, on `A`-modules in an
independent universe. -/
private noncomputable def tensorSmall (W : ModuleCat.{u} A) :
    ModuleCat.{v} A ⥤ ModuleCat.{max u v} A where
  obj X := ModuleCat.of A (TensorProduct A X W)
  map f := ModuleCat.ofHom (LinearMap.rTensor W f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

private instance (W : ModuleCat.{u} A) : (tensorSmall.{u, v} W).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact TensorProduct.add_tmul _ _ _

/-- Termwise tensoring a complex of `A`-modules with an `A`-module in the universe of `A`,
functorially in the module. -/
private noncomputable def tensorSmallComplex (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    ModuleCat.{u} A ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ where
  obj W := ((tensorSmall.{u, v} W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  map f :=
    { f := fun i => ModuleCat.ofHom (LinearMap.lTensor (K.X i) f.hom)
      comm' := by
        intro i j _
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        rfl }
  map_id W := by
    ext i : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  map_comp f g := by
    ext i : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

private instance (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (tensorSmallComplex.{u, v} K).Additive where
  map_add := by
    intro X Y f g
    ext i : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact TensorProduct.tmul_add _ _ _

/-- Tensoring a complex termwise with a flat module preserves exactness. -/
private lemma exactAt_tensorSmallComplex_of_flat (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (W : ModuleCat.{u} A) (hW : Module.Flat A W) (i : ℤ) (h : K.ExactAt i) :
    ((tensorSmallComplex.{u, v} K).obj W).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact Module.Flat.rTensor_exact W h

/-- Tensoring a complex termwise with a zero module gives a complex that is exact in every
degree: every term of the result vanishes. -/
private lemma exactAt_tensorSmallComplex_of_subsingleton
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (W : ModuleCat.{u} A)
    (hW : Subsingleton W) (i : ℤ) :
    ((tensorSmallComplex.{u, v} K).obj W).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : Subsingleton (((tensorSmallComplex.{u, v} K).obj W).X i) := by
    refine ⟨fun s t => ?_⟩
    have hzero : ∀ x : TensorProduct A (K.X i) W, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul m w => rw [hW.elim w 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    exact (hzero s).trans (hzero t).symm
  have hIsZero : IsZero (((tensorSmallComplex.{u, v} K).obj W).X i) :=
    ModuleCat.isZero_of_subsingleton _
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hIsZero

/-- A short exact sequence of `A`-modules in the universe of `A` stays short exact after
termwise tensoring with a complex of flat `A`-modules. -/
private lemma shortExact_tensorSmallComplex (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : ∀ i : ℤ, Module.Flat A (K.X i)) (S : ShortComplex (ModuleCat.{u} A))
    (hS : S.ShortExact) : (S.map (tensorSmallComplex.{u, v} K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hK i
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact Module.Flat.lTensor_exact (K.X i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact)
  · exact Module.Flat.lTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective S.f).1 hS.mono_f)
  · exact LinearMap.lTensor_surjective _ ((ModuleCat.epi_iff_surjective S.g).1 hS.epi_g)

/-- The connecting map of the long exact sequence moves exactness one degree: if the middle
complex of a short exact sequence of complexes is exact in degree `i` and the left complex in
degree `i + 1`, then the right complex is exact in degree `i`. -/
private lemma exactAt_X₃ {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)
    (h₂ : S.X₂.ExactAt i) (h₁ : S.X₁.ExactAt (i + 1)) : S.X₃.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  have : Mono (hS.δ i (i + 1) rfl) :=
    (hS.homology_exact₃ i (i + 1) rfl).mono_g (h₂.eq_of_src _ _)
  exact IsZero.of_mono (hS.δ i (i + 1) rfl) h₁

/-! ### Dévissage along a flat resolution -/

/-- The image of a differential of a complex, as a module. -/
private noncomputable def diffImage (E : CochainComplex (ModuleCat.{u} A) ℤ) (j j' : ℤ) :
    ModuleCat.{u} A :=
  ModuleCat.of A (LinearMap.range (E.d j j').hom)

/-- The three-term sequence `Im d^j → E^{j'} → Im d^{j'}` of images of consecutive
differentials. -/
private noncomputable def imageShortComplex (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (j j' j'' : ℤ) : ShortComplex (ModuleCat.{u} A) :=
  ModuleCat.shortComplexOfCompEqZero
    (LinearMap.range (E.d j j').hom).subtype (E.d j' j'').hom.rangeRestrict (by
      apply LinearMap.ext
      rintro ⟨x, y, rfl⟩
      apply Subtype.ext
      have h := congrArg (fun φ : E.X j ⟶ E.X j'' => ModuleCat.Hom.hom φ y)
        (E.d_comp_d j j' j'')
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply] at h
      exact h)

/-- Exactness of `E` in degree `j'` makes that sequence short exact. -/
private lemma shortExact_imageShortComplex (E : CochainComplex (ModuleCat.{u} A) ℤ)
    (j j' j'' : ℤ) (h1 : j + 1 = j') (h2 : j' + 1 = j'') (hex : E.ExactAt j') :
    (imageShortComplex E j j' j'').ShortExact := by
  rw [HomologicalComplex.exactAt_iff] at hex
  replace hex := ShortComplex.exact_of_iso
    (E.isoSc' j j' j'' (by rw [CochainComplex.prev]; omega)
      (by rw [CochainComplex.next]; omega)) hex
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, LinearMap.exact_iff] at hex
  rw [imageShortComplex]
  refine ModuleCat.shortComplex_shortExact _ ?_ Subtype.val_injective
    (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.exact_iff]
  simp only [ModuleCat.hom_ofHom]
  rwa [LinearMap.ker_rangeRestrict, Submodule.range_subtype]

/-- **Dévissage.** Let `K` be a complex of flat `A`-modules exact outside degree `0`, and let
`E` be a complex of flat `A`-modules vanishing below `a` and exact outside degree `0`. Then the
termwise tensor product of `K` with the image of `d_E^{a - 1 + k}` is exact in every degree
below `1 - k`. -/
private lemma exactAt_tensorSmallComplex_diffImage
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (hKflat : ∀ i : ℤ, Module.Flat A (K.X i))
    (hKex : ∀ i : ℤ, i ≠ 0 → K.ExactAt i)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) (hEflat : ∀ i : ℤ, Module.Flat A (E.X i))
    (hEex : ∀ i : ℤ, i ≠ 0 → E.ExactAt i) (a : ℤ) (hEa : ∀ i : ℤ, i < a → IsZero (E.X i)) :
    ∀ k : ℕ, a + (k : ℤ) ≤ 0 → ∀ j j' : ℤ, j + 1 = j' → j = a - 1 + (k : ℤ) →
      ∀ i : ℤ, i < 1 - (k : ℤ) →
        ((tensorSmallComplex.{u, v} K).obj (diffImage E j j')).ExactAt i := by
  intro k
  induction k with
  | zero =>
    intro _ j j' _ hj i _
    have hsub : Subsingleton (LinearMap.range (E.d j j').hom) := by
      have hz : Subsingleton (E.X j) :=
        ModuleCat.isZero_iff_subsingleton.mp (hEa j (by push_cast at hj ⊢; omega))
      refine ⟨?_⟩
      rintro ⟨x, y, rfl⟩ ⟨x', y', rfl⟩
      exact Subtype.ext (by rw [Subsingleton.elim y y'])
    exact exactAt_tensorSmallComplex_of_subsingleton K _ hsub i
  | succ k ih =>
    intro hk j j' hjj hj i hi
    have hprev : a - 1 + (k : ℤ) + 1 = j := by push_cast at hj ⊢; omega
    have hSE : (imageShortComplex E (a - 1 + (k : ℤ)) j j').ShortExact :=
      shortExact_imageShortComplex E _ j j' hprev hjj
        (hEex j (by push_cast at hj hk ⊢; omega))
    exact exactAt_X₃ (shortExact_tensorSmallComplex.{u, v} K hKflat _ hSE) i
      (exactAt_tensorSmallComplex_of_flat K _ (hEflat j) i
        (hKex i (by push_cast at hi ⊢; omega)))
      (ih (by push_cast at hk ⊢; omega) (a - 1 + (k : ℤ)) j hprev rfl (i + 1)
        (by push_cast at hi ⊢; omega))

/-! ### Flatness of the cokernel -/

/-- If the termwise tensor product of `K` with every `A`-module in the universe of `A` is exact
in degree `a - 1`, then `Coker(d_K^{a-1})` is a flat `A`-module.

This is the flat-cokernel argument of Stacks 0653 at a module universe independent of the
ring's, where the test modules can be taken in the ring's own universe. -/
private lemma flat_cokernel_of_exactAt (K : CochainComplex (ModuleCat.{v} A) ℤ) (a : ℤ)
    (hflat : Module.Flat A (K.X a))
    (hex : ∀ N : ModuleCat.{u} A, ((tensorSmallComplex.{u, v} K).obj N).ExactAt (a - 1)) :
    Module.Flat A (cokernel (K.d (a - 1) a) : ModuleCat.{v} A) := by
  set g : (K.X (a - 1) : Type v) →ₗ[A] (K.X a : Type v) := (K.d (a - 1) a).hom with hg
  have hinj : ∀ (N : Type u) [AddCommGroup N] [Module A N],
      Function.Injective (LinearMap.rTensor N (LinearMap.range g).subtype) := by
    intro N _ _
    have he := hex (ModuleCat.of A N)
    rw [HomologicalComplex.exactAt_iff,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at he
    have key : Function.Exact
        (LinearMap.rTensor N (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom)
        (LinearMap.rTensor N (K.d (a - 1) ((ComplexShape.up ℤ).next (a - 1))).hom) := he
    rw [show (ComplexShape.up ℤ).next (a - 1) = a by rw [CochainComplex.next]; omega] at key
    refine StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact
      (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom g ?_ N key
    rw [hg, ← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]
  have hQ : Module.Flat A ((K.X a : Type v) ⧸ LinearMap.range g) := by
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{u}]
    intro N N' _ _ _ _ f hf
    exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (LinearMap.exact_subtype_mkQ (LinearMap.range g))
      (Submodule.mkQ_surjective (LinearMap.range g))
      (LinearMap.exact_map_mkQ_range f)
      (Submodule.mkQ_surjective (LinearMap.range f))
      (hinj (N' ⧸ LinearMap.range f))
      (Module.Flat.lTensor_preserves_injective_linearMap f hf)
  exact Module.Flat.of_linearEquiv
    (ModuleCat.cokernelIsoRangeQuotient (K.d (a - 1) a)).toLinearEquiv

end StacksDraft.WeakDimension

/-! ### Stacks 092E -/

open StacksDraft.WeakDimension in
/-- **Stacks Tag 092E.** A weakly étale algebra over a commutative ring of weak dimension at most
`d` also has weak dimension at most `d`. -/
@[stacks 092E]
theorem hasWeakDimensionLE_of_weaklyEtale
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (derivedTensorA :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparisonA : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensorA.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        ((tensoringRight (ModuleCat.{u} A)).obj N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedA : ∀ N : ModuleCat.{u} A,
      (derivedTensorA.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparisonA N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    (d : ℕ) (hAB : Algebra.WeaklyEtale A B)
    (hA : HasWeakDimensionLE derivedTensorA comparisonA isLeftDerivedA d) :
    ∃ (derivedTensorB :
        DerivedCategory (ModuleCat.{v} B) ⥤
          DerivedCategory (ModuleCat.{v} B) ⥤ DerivedCategory (ModuleCat.{v} B))
      (comparisonB : ∀ N : ModuleCat.{v} B,
        DerivedCategory.Q ⋙
            derivedTensorB.flip.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{v} B) 0).obj N) ⟶
          ((tensoringRight (ModuleCat.{v} B)).obj N).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (isLeftDerivedB : ∀ N : ModuleCat.{v} B,
        (derivedTensorB.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} B) 0).obj N)).IsLeftDerivedFunctor
          (comparisonB N)
          (HomologicalComplex.quasiIso (ModuleCat.{v} B) (ComplexShape.up ℤ))),
      HasWeakDimensionLE derivedTensorB comparisonB isLeftDerivedB d := by
  have : Algebra.WeaklyEtale A B := hAB
  refine ⟨certifiedTensor, certifiedComparison, certifiedIsLeftDerived, ?_⟩
  intro M
  refine (StacksDraft.TorAmplitude.hasTorDimensionLE_iff_hasFlatRepresentative
    certifiedComparison certifiedIsLeftDerived M d).1.2 ?_
  -- a projective resolution of `M` over `B`
  set P := (ProjectiveResolution.of M).cochainComplex
  have hPLE : P.IsStrictlyLE 0 := inferInstance
  have hPGE : P.IsGE 0 := inferInstance
  have hPflat : ∀ i : ℤ, Module.Flat B (P.X i) := fun i => by
    have : Projective (P.X i) := inferInstance
    infer_instance
  have hPex : ∀ i : ℤ, i ≠ 0 → P.ExactAt i := by
    intro i hi
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact (CochainComplex.isGE_iff P 0).1 hPGE i hi
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact ShortComplex.isZero_homology_of_isZero_X₂ _
        (CochainComplex.isZero_of_isStrictlyLE P 0 i hi)
  have eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{v} B) 0).obj M :=
    asIso (DerivedCategory.Q.map (ProjectiveResolution.of M).π') ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{v} B) 0).app M).symm
  -- its restriction of scalars to `A`
  set U := ModuleCat.restrictScalars.{v} (algebraMap A B)
  set K := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hKflat : ∀ i : ℤ, Module.Flat A (K.X i) := by
    intro i
    have := hPflat i
    let _ : Module A (P.X i) := Module.compHom (P.X i) (algebraMap A B)
    have : IsScalarTower A B (P.X i) := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    exact Module.Flat.trans A B (P.X i)
  have hKex : ∀ i : ℤ, i ≠ 0 → K.ExactAt i := fun i hi =>
    (HomologicalComplex.exactAt_iff _ _).2
      (((HomologicalComplex.exactAt_iff _ _).1 (hPex i hi)).map U)
  -- the cokernel in degree `-d` is flat over `A`
  have hcokA : Module.Flat A (cokernel (K.d (-(d : ℤ) - 1) (-(d : ℤ))) : ModuleCat.{v} A) := by
    refine flat_cokernel_of_exactAt K (-(d : ℤ)) (hKflat _) fun N => ?_
    obtain ⟨E, hEflat, hEGE, hELE, ⟨e⟩⟩ :=
      (StacksDraft.TorAmplitude.hasTorDimensionLE_iff_hasFlatRepresentative
        comparisonA isLeftDerivedA N d).1.1 (hA N)
    have hEa : ∀ i : ℤ, i < -(d : ℤ) → IsZero (E.X i) := by
      have := hEGE
      exact fun i hi => CochainComplex.isZero_of_isStrictlyGE E (-(d : ℤ)) i hi
    have hd0 : E.d 0 1 = 0 := by
      have := hELE
      exact (CochainComplex.isZero_of_isStrictlyLE E 0 1 (by omega)).eq_of_tgt _ _
    have hiso : ∀ i : ℤ,
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N).homology i ≅ E.homology i :=
      fun i =>
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app _).symm ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app N).symm ≪≫ e) ≪≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app E
    have hEex : ∀ i : ℤ, i ≠ 0 → E.ExactAt i := fun i hi =>
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
        ((HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N i hi).of_iso
          (hiso i).symm)
    -- `E^0` modulo the image of `d_E^{-1}` is `N`
    have hopc : ModuleCat.of A ((E.X 0 : Type u) ⧸ LinearMap.range (E.d (-1) 0).hom) ≅ N :=
      (ModuleCat.cokernelIsoRangeQuotient (E.d (-1) 0)).symm ≪≫
        (IsColimit.coconePointUniqueUpToIso
          (E.opcyclesIsCokernel (-1) 0 (by simp)) (colimit.isColimit _)).symm ≪≫
        (E.isoHomologyι 0 1 (by simp) hd0).symm ≪≫ (hiso 0).symm ≪≫
        HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 N
    have hlast : (ModuleCat.shortComplexOfCompEqZero
        (LinearMap.range (E.d (-1) 0).hom).subtype
        (LinearMap.range (E.d (-1) 0).hom).mkQ
        (LinearMap.ext fun x => (Submodule.Quotient.mk_eq_zero _).2 x.2)).ShortExact :=
      ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ _)
        Subtype.val_injective (Submodule.mkQ_surjective _)
    have hmapl := shortExact_tensorSmallComplex.{u, v} K hKflat _ hlast
    have hq : ((tensorSmallComplex.{u, v} K).obj
        (ModuleCat.of A ((E.X 0 : Type u) ⧸ LinearMap.range (E.d (-1) 0).hom))).ExactAt
          (-(d : ℤ) - 1) := by
      refine exactAt_X₃ hmapl (-(d : ℤ) - 1) ?_ ?_
      · exact exactAt_tensorSmallComplex_of_flat K _ (hEflat 0) _ (hKex _ (by omega))
      · exact exactAt_tensorSmallComplex_diffImage K hKflat hKex E hEflat hEex (-(d : ℤ)) hEa
          d (by omega) (-1) 0 (by omega) (by ring) (-(d : ℤ) - 1 + 1) (by omega)
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hq).of_iso
      (HomologicalComplex.homologyMapIso
        ((tensorSmallComplex.{u, v} K).mapIso hopc.symm) (-(d : ℤ) - 1))
  -- descend flatness to `B` and assemble the flat resolution
  have hcokAP : Module.Flat A (U.obj (cokernel (P.d (-(d : ℤ) - 1) (-(d : ℤ))))) := by
    have _ : Module.Flat A
        ((cokernel (U.map (P.d (-(d : ℤ) - 1) (-(d : ℤ)))) : ModuleCat.{v} A)) := hcokA
    exact Module.Flat.of_linearEquiv
      (PreservesCokernel.iso U (P.d (-(d : ℤ) - 1) (-(d : ℤ)))).toLinearEquiv
  have hcokB : Module.Flat B (cokernel (P.d (-(d : ℤ) - 1) (-(d : ℤ))) : ModuleCat.{v} B) := by
    let _ : Module A (cokernel (P.d (-(d : ℤ) - 1) (-(d : ℤ))) : ModuleCat.{v} B) :=
      Module.compHom _ (algebraMap A B)
    let : IsScalarTower A B (cokernel (P.d (-(d : ℤ) - 1) (-(d : ℤ))) : ModuleCat.{v} B) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    have hflatA : Module.Flat A
        (cokernel (P.d (-(d : ℤ) - 1) (-(d : ℤ))) : ModuleCat.{v} B) := hcokAP
    exact flat_of_flat_of_mul_flat A B (Algebra.WeaklyEtale.flat_lmul' A B)
      (cokernel (P.d (-(d : ℤ) - 1) (-(d : ℤ))) : ModuleCat.{v} B) hflatA
  have hopcB : Module.Flat B (P.opcycles (-(d : ℤ))) := by
    have _ : Module.Flat B
        (colimit.cocone (parallelPair (P.d (-(d : ℤ) - 1) (-(d : ℤ))) 0)).pt := hcokB
    exact Module.Flat.of_linearEquiv
      (IsColimit.coconePointUniqueUpToIso
        (P.opcyclesIsCokernel (-(d : ℤ) - 1) (-(d : ℤ)) (by simp))
        (colimit.isColimit _)).toLinearEquiv
  have hPflat' : ∀ i : ℤ, Module.Flat B (P.X i) := hPflat
  have hGE : P.IsGE (-(d : ℤ)) := P.isGE_of_ge (-(d : ℤ)) 0 (by omega)
  refine ⟨P.truncGE (-(d : ℤ)),
    StacksDraft.TorAmplitude.flat_truncGE P (-(d : ℤ)), ?_,
    StacksDraft.TorAmplitude.truncGE_isStrictlyLE P (-(d : ℤ)) 0 hPLE,
    ⟨eP.symm ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE (-(d : ℤ))))⟩⟩
  exact inferInstance

end
