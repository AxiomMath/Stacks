module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDescEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleConeHomotopy

/-!
# Morphisms out of the cone on an identity are degree `-1` families

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `K` be a right differential graded `A`-module. **A morphism of differential graded modules
`C(𝟙_K) ⟶ N` is exactly a homomorphism of graded modules `K ⟶ N[-1]`**, where `N[-1]` is
`SheafOfModules.DifferentialGradedModule.gradedShiftDown N`, the graded module whose degree-`n`
piece is `N^{n-1}`.

This is the one statement about a differential graded module which the goodness predicates of
Tag 0FSA do not see: every clause of goodness quantifies homomorphisms of *differential* graded
modules out of the module, and the datum here is a homomorphism of *graded* modules. Recognising
it as a morphism of differential graded modules into a *cofree* object is what lets the base
change of a cone be built from the base changes of its two ends -- see
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ConeDifferentialGradedModuleToposPullback.lean`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.gradedShiftDownMap` is the shift down by one on
  morphisms, so `gradedShiftDown` is a functor to graded modules.
* `SheafOfModules.DifferentialGradedModule.deltaFamily` is the degreewise family
  `d ∘ Φ + Φ ∘ d` attached to a homomorphism of graded modules `Φ : K ⟶ N[-1]`, and
  `SheafOfModules.DifferentialGradedModule.deltaHom` is the morphism of differential graded
  modules it assembles into.
* `SheafOfModules.DifferentialGradedModule.coneIdentityShiftDownEquiv`: **the bijection**
  `(C(𝟙_K) ⟶ N) ≃ (K ⟶ N[-1])`.
* `SheafOfModules.DifferentialGradedModule.cofreeCounit` is the counit `Cofree(N[-1]) ⟶ N`, and
  `SheafOfModules.DifferentialGradedModule.cofreeMap` the cofree module on a homomorphism of
  graded modules.
* `SheafOfModules.DifferentialGradedModule.coneFam` is the homomorphism of graded modules a
  morphism out of an *arbitrary* cone restricts to, and
  `SheafOfModules.DifferentialGradedModule.coneDescOf` the inverse construction; together with
  `cone_hom_ext` and `deltaHom_coneFam` they say that a morphism out of the cone of `f : K ⟶ L`
  is exactly a morphism `L ⟶ N` together with a homomorphism of graded modules `K ⟶ N[-1]` whose
  commutator with the differentials is `f` followed by the first.

## Main results

* `SheafOfModules.DifferentialGradedModule.deltaFamily_mul`: **the commutator `d ∘ Φ + Φ ∘ d` of
  a right `A`-linear degree `-1` family with the differentials is right `A`-linear.** This is the
  one computation of the file: the two Leibniz terms it produces carry the opposite signs
  `(-1)^{n-1}` and `(-1)^n` and cancel, which is
  `SheafOfModules.DifferentialGradedModule.add_negOnePow_zsmul_cancel`.
* `SheafOfModules.DifferentialGradedModule.coneIdentityShiftDownEquiv_comp`: **the bijection is
  natural in `N`.**
* `SheafOfModules.DifferentialGradedModule.deltaHom_eq`: **the commutator factors as the cofree
  lift followed by the counit.** Both factors are morphisms of differential graded modules, which
  is why the commutator transports along a base change even though the family it is built from
  does not.

## Implementation notes

Nothing here is new about cones. A morphism out of the cone of `f : K ⟶ L` is a pair, a morphism
`β : L ⟶ N` together with a right `A`-linear degreewise family `α n : K^{n+1} ⟶ N^n` which is a
null-homotopy of `f ≫ β`; that is
`SheafOfModules.DifferentialGradedModule.ConePackage.desc` and
`ConePackage.desc_homotopyOfHom` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeDescEquiv.lean`. For
`f = 𝟙_K` the null-homotopy condition **determines** `β`, namely `β = d ∘ α + α ∘ d`, so the pair
collapses to its second coordinate. The translation between a family `α` and a homomorphism into
the shift down by one is
`SheafOfModules.DifferentialGradedModule.ofShiftDownHom`/`toShiftDownHom` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleConeHomotopy.lean`,
already stated for an arbitrary differential graded module.

So the only thing to prove is that `d ∘ Φ + Φ ∘ d` really is a morphism of differential graded
modules. That it commutes with the differentials is `d ∘ d = 0` twice, at morphism level. That it
is right `A`-linear is the signed Leibniz rule used twice, once in `N` on `Φ(x) · a` and once in
`K` on `x · a`; the two mixed terms `± Φ(x) · (d a)` carry the signs `(-1)^{n-1}` and `(-1)^n` and
cancel. No closedness is available and none is needed: `Φ` is an arbitrary homomorphism of graded
modules.

The base is an arbitrary sheaf of rings on an arbitrary site, with the universes of the site, the
ring, the algebra pieces and the module pieces independent, as in the neighbouring differential
graded files. This generality is what lets the bijection be used over the two different ringed
topoi of a base change.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R} {K N N' : DifferentialGradedModule.{t, a, m} A}

/-! ### Transports along an equality of degrees -/

/-- The transport of a cochain complex along an equality of degrees, precomposed with a
differential, is the differential of the untransported degree. -/
theorem eqToHom_comp_d (X : CochainComplex (SheafOfModules.{m} R) ℤ) {i j : ℤ} (h : i = j)
    (k : ℤ) : eqToHom (congrArg X.X h) ≫ X.d j k = X.d i k := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

/-- A differential read through a transport of its source and its target. -/
theorem homSections_d_cast (X : CochainComplex (SheafOfModules.{m} R) ℤ) {p p' q q' : ℤ}
    (hp : p = p') (hq : q = q') (hpq : q = p + 1) (U : Cᵒᵖ) (z : (X.X p).val.obj U) :
    homSections (X.d p' q') U (castHom X.X hp U z) =
      castHom X.X hq U (homSections (X.d p q) U z) := by
  subst hpq hq hp
  rw [castHom_rfl, castHom_rfl]

/-- The signed Leibniz rule of a right differential graded module, with its two transports
written through `SheafOfModules.castHom` and its action through the bilinear map of the module.
This is `SheafOfModules.DifferentialGradedModule.leibniz_ofDifferentialGraded` at the spelling
the computations of this file are written in. -/
theorem leibnizMul (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U) :
    homSections (M.complex.d (n + i) (n + i + 1)) U ((M.mul n i).app U x y) =
      castHom M.complex.X (add_right_comm n 1 i) U
          ((M.mul (n + 1) i).app U (homSections (M.complex.d n (n + 1)) U x) y)
        + ((Int.negOnePow n : ℤˣ) : ℤ) •
            castHom M.complex.X (add_assoc n i 1).symm U
              ((M.mul n (i + 1)).app U x (homSections (A.complex.d i (i + 1)) U y)) := by
  simp only [castHom_apply, homSections_apply]
  exact M.leibniz n i U x y

/-! ### The shift down by one on morphisms -/

/-- **The shift down by one of a morphism of right differential graded modules**: in degree `n`
it is the degree-`n - 1` component of the morphism. -/
noncomputable def gradedShiftDownMap (g : N ⟶ N') :
    GradedModule.Hom (gradedShiftDown N) (gradedShiftDown N') where
  app n := g.toHomologicalComplex.f (n - 1)
  map_smul n i U x y := by
    refine eq_of_heq (HEq.trans ?_ (gradedShiftDown_smul_eval_heq N' n i U _ y).symm)
    refine HEq.trans (heq_dependent_apply
      (fun d : ℤ => fun z : (N.complex.X d).val.obj U =>
        (g.toHomologicalComplex.f d).val.app U z)
      (show (n + i) - 1 = (n - 1) + i by omega)
      (gradedShiftDown_smul_eval_heq N n i U x y)) ?_
    exact heq_of_eq (g.map_mul (n - 1) i U x y)

/-- The component in degree `n` of `gradedShiftDownMap g` is the component of `g` in degree
`n - 1`. -/
@[simp] theorem gradedShiftDownMap_app (g : N ⟶ N') (n : ℤ) :
    (gradedShiftDownMap g).app n = g.toHomologicalComplex.f (n - 1) := rfl

/-! ### Functoriality of the cofree differential graded module -/

section CofreeFunctor

variable {P P' : GradedModule.{t, a, m} A.toGradedAlgebra}

/-- **The first coordinate of a cofree differential graded module**, with its source spelled as
the degree-`n` piece of the cochain complex. As for
`SheafOfModules.DifferentialGradedModule.shiftDownApp`, the two spellings agree only after
unfolding a semireducible definition, so this ascription is what the statements below are
written against. -/
noncomputable def cofreeFstHom (P : GradedModule.{t, a, m} A.toGradedAlgebra) (n : ℤ) :
    (Cofree.cofree P).complex.X n ⟶ P.piece n := biprod.fst

/-- The homomorphism of graded modules attached to a morphism into a cofree module is that
morphism followed by the first coordinate. -/
theorem lowerHom_app {M : DifferentialGradedModule.{t, a, m} A} (ψ : M ⟶ Cofree.cofree P)
    (n : ℤ) :
    (Cofree.lowerHom P ψ).app n = ψ.toHomologicalComplex.f n ≫ cofreeFstHom P n := rfl

/-- **The second coordinate of a cofree differential graded module**, with its source spelled as
the degree-`n` piece of the cochain complex. -/
noncomputable def cofreeSndHom (P : GradedModule.{t, a, m} A.toGradedAlgebra) (n : ℤ) :
    (Cofree.cofree P).complex.X n ⟶ P.piece (n + 1) := biprod.snd

/-- **The differential of a cofree module followed by the first coordinate is the second
coordinate**: the differential of a cofree module sends `(x, y)` to `(y, 0)`. -/
theorem cofree_d_comp_fstHom (P : GradedModule.{t, a, m} A.toGradedAlgebra) (n : ℤ) :
    (Cofree.cofree P).complex.d n (n + 1) ≫ cofreeFstHom P (n + 1) = cofreeSndHom P n := by
  rw [show (Cofree.cofree P).complex.d n (n + 1) = Cofree.d P n from CochainComplex.of_d _ _ n]
  show (biprod.snd ≫ biprod.inl) ≫
    (biprod.fst : Cofree.piece P (n + 1) ⟶ P.piece (n + 1)) = biprod.snd
  rw [Category.assoc, biprod.inl_fst, Category.comp_id]

/-- The differential of a cofree module followed by the first coordinate and anything else. -/
theorem cofree_d_comp_fstHom_comp {Z : SheafOfModules.{m} R}
    (P : GradedModule.{t, a, m} A.toGradedAlgebra) (n : ℤ) (u : P.piece (n + 1) ⟶ Z) :
    (Cofree.cofree P).complex.d n (n + 1) ≫ cofreeFstHom P (n + 1) ≫ u =
      cofreeSndHom P n ≫ u := by
  rw [← Category.assoc, cofree_d_comp_fstHom]

/-- The degree-`n` component of a cofree lift. -/
theorem liftDgHom_f {M : DifferentialGradedModule.{t, a, m} A}
    (φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) P) (n : ℤ) :
    (Cofree.liftDgHom P φ).toHomologicalComplex.f n = Cofree.liftHom P φ n := rfl

/-- The first coordinate of a cofree lift is the graded homomorphism. -/
theorem liftHom_comp_fstHom {M : DifferentialGradedModule.{t, a, m} A}
    (φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) P) (n : ℤ) :
    Cofree.liftHom P φ n ≫ cofreeFstHom P n = φ.app n := by
  show biprod.lift (φ.app n) (M.complex.d n (n + 1) ≫ φ.app (n + 1)) ≫
    (biprod.fst : Cofree.piece P n ⟶ P.piece n) = _
  rw [biprod.lift_fst]

/-- The second coordinate of a cofree lift is the graded homomorphism after the differential. -/
theorem liftHom_comp_sndHom {M : DifferentialGradedModule.{t, a, m} A}
    (φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) P) (n : ℤ) :
    Cofree.liftHom P φ n ≫ cofreeSndHom P n = M.complex.d n (n + 1) ≫ φ.app (n + 1) := by
  show biprod.lift (φ.app n) (M.complex.d n (n + 1) ≫ φ.app (n + 1)) ≫
    (biprod.snd : Cofree.piece P n ⟶ P.piece (n + 1)) = _
  rw [biprod.lift_snd]
  rfl

/-- **The cofree differential graded module on a homomorphism of graded modules.** Morphisms into
a cofree module are homomorphisms of graded modules into its argument, so this is the cofree lift
of the first coordinate followed by the given homomorphism. -/
noncomputable def cofreeMap (k : GradedModule.Hom P P') :
    Cofree.cofree P ⟶ Cofree.cofree P' :=
  Cofree.liftDgHom P' ((Cofree.lowerHom P (𝟙 (Cofree.cofree P))).comp k)

/-- **The first coordinate of the cofree module on a homomorphism is the homomorphism.** -/
theorem cofreeMap_comp_fst (k : GradedModule.Hom P P') (n : ℤ) :
    (cofreeMap k).toHomologicalComplex.f n ≫ cofreeFstHom P' n =
      cofreeFstHom P n ≫ k.app n := by
  refine Eq.trans (lowerHom_app (cofreeMap k) n).symm (Eq.trans (congrArg
    (fun α : GradedModule.Hom (GradedModule.ofDifferentialGraded (Cofree.cofree P)) P' =>
      α.app n)
    (Cofree.lowerHom_liftDgHom P' ((Cofree.lowerHom P (𝟙 (Cofree.cofree P))).comp k))) ?_)
  show (Cofree.lowerHom P (𝟙 (Cofree.cofree P))).app n ≫ k.app n = _
  rw [lowerHom_app, id_f, Category.id_comp]
  rfl

/-- The cofree lift is injective, being inverse to taking the first coordinate. -/
theorem liftDgHom_injective (P : GradedModule.{t, a, m} A.toGradedAlgebra)
    {M : DifferentialGradedModule.{t, a, m} A} :
    Function.Injective (Cofree.liftDgHom P (M := M)) := fun a b h => by
  rw [← Cofree.lowerHom_liftDgHom P a, ← Cofree.lowerHom_liftDgHom P b, h]

/-- A morphism into a cofree module built as a biproduct lift, composed with a morphism out of
the cofree module built from its two coordinates. -/
theorem lift_comp_coords {Z W : SheafOfModules.{m} R}
    (P : GradedModule.{t, a, m} A.toGradedAlgebra) (n : ℤ) (p : Z ⟶ P.piece n)
    (q : Z ⟶ P.piece (n + 1)) (u : P.piece n ⟶ W) (v : P.piece (n + 1) ⟶ W) :
    (biprod.lift p q : Z ⟶ (Cofree.cofree P).complex.X n) ≫
        (cofreeFstHom P n ≫ u + cofreeSndHom P n ≫ v) = p ≫ u + q ≫ v := by
  show biprod.lift p q ≫ ((biprod.fst : Cofree.piece P n ⟶ P.piece n) ≫ u +
    (biprod.snd : Cofree.piece P n ⟶ P.piece (n + 1)) ≫ v) = _
  rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, biprod.lift_fst, biprod.lift_snd]

/-- The first coordinate of a morphism into a cofree module, precomposed. -/
theorem lowerHom_comp_left {M M' : DifferentialGradedModule.{t, a, m} A} (u : M ⟶ M')
    (v : M' ⟶ Cofree.cofree P) (n : ℤ) :
    (Cofree.lowerHom P (u ≫ v)).app n =
      u.toHomologicalComplex.f n ≫ (Cofree.lowerHom P v).app n := by
  rw [lowerHom_app, lowerHom_app, comp_f, Category.assoc]

/-- Taking the first coordinate is injective, being inverse to the cofree lift. -/
theorem lowerHom_injective (P : GradedModule.{t, a, m} A.toGradedAlgebra)
    {M : DifferentialGradedModule.{t, a, m} A} :
    Function.Injective (Cofree.lowerHom P (M := M)) := fun a b h => by
  rw [← Cofree.liftDgHom_lowerHom P a, ← Cofree.liftDgHom_lowerHom P b, h]

/-- **The cofree lift is natural in the graded module.** -/
theorem liftDgHom_comp {M : DifferentialGradedModule.{t, a, m} A}
    (φ : GradedModule.Hom (GradedModule.ofDifferentialGraded M) P) (k : GradedModule.Hom P P') :
    Cofree.liftDgHom P' (φ.comp k) = Cofree.liftDgHom P φ ≫ cofreeMap k := by
  refine lowerHom_injective P' (GradedModule.Hom.ext fun n => ?_)
  have hleft : (Cofree.lowerHom P' (Cofree.liftDgHom P' (φ.comp k))).app n =
      φ.app n ≫ k.app n :=
    congrArg
      (fun α : GradedModule.Hom (GradedModule.ofDifferentialGraded M) P' => α.app n)
      (Cofree.lowerHom_liftDgHom P' (φ.comp k))
  have hφ : (Cofree.liftDgHom P φ).toHomologicalComplex.f n ≫ cofreeFstHom P n = φ.app n :=
    liftHom_comp_fstHom φ n
  refine hleft.trans (Eq.trans ?_ (lowerHom_app (Cofree.liftDgHom P φ ≫ cofreeMap k) n).symm)
  show φ.app n ≫ k.app n =
    ((Cofree.liftDgHom P φ).toHomologicalComplex.f n ≫
      (cofreeMap k).toHomologicalComplex.f n) ≫ cofreeFstHom P' n
  rw [Category.assoc, cofreeMap_comp_fst, ← Category.assoc, hφ]
  rfl

end CofreeFunctor

/-! ### The commutator of a degree `-1` family with the differentials -/

section Delta

variable (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N))

/-- **The degree-`n` component of a homomorphism of graded modules into the shift down by one**,
with its source and target spelled as the pieces of the two cochain complexes. The pieces of
`SheafOfModules.GradedModule.ofDifferentialGraded` and of
`SheafOfModules.DifferentialGradedModule.gradedShiftDown` are those two objects by definition,
but only after unfolding a semireducible definition, which is not enough for the composition
below to elaborate or for `rw` to build a motive; this ascription is what every statement of the
section is written against. -/
noncomputable def shiftDownApp (n : ℤ) : K.complex.X n ⟶ N.complex.X (n - 1) := Φ.app n

/-- `shiftDownApp Φ n` acts on sections as the component `Φ.app n`. -/
theorem shiftDownApp_homSections (n : ℤ) (U : Cᵒᵖ) (z : (K.complex.X n).val.obj U) :
    homSections (shiftDownApp Φ n) U z = homSections (Φ.app n) U z := rfl

/-- A homomorphism into the shift down by one commutes with transport along an equality of
degrees. -/
theorem shiftDownApp_castHom {j j' : ℤ} (h : j = j') (U : Cᵒᵖ)
    (w : (K.complex.X j).val.obj U) :
    homSections (shiftDownApp Φ j') U (castHom K.complex.X h U w) =
      castHom N.complex.X (show j - 1 = j' - 1 by omega) U
        (homSections (shiftDownApp Φ j) U w) := by
  subst h
  rw [castHom_rfl, castHom_rfl]

/-- The family of `SheafOfModules.DifferentialGradedModule.ofShiftDownHom`, read through
`shiftDownApp`. -/
theorem ofShiftDownHom_eq (n : ℤ) :
    ofShiftDownHom Φ n =
      shiftDownApp Φ (n + 1) ≫ eqToHom (congrArg N.complex.X (degSuccSubOne n)) := rfl

/-- **The degreewise family `d ∘ Φ + Φ ∘ d`** attached to a homomorphism of graded modules from
`K` into the shift down by one of `N`. -/
noncomputable def deltaFamily (n : ℤ) : K.complex.X n ⟶ N.complex.X n :=
  shiftDownApp Φ n ≫ N.complex.d (n - 1) n + K.complex.d n (n + 1) ≫ ofShiftDownHom Φ n

/-- The commutator read on local sections. -/
theorem deltaFamily_homSections (n : ℤ) (U : Cᵒᵖ) (z : (K.complex.X n).val.obj U) :
    homSections (deltaFamily Φ n) U z =
      homSections (N.complex.d (n - 1) n) U (homSections (shiftDownApp Φ n) U z) +
        castHom N.complex.X (degSuccSubOne n) U
          (homSections (shiftDownApp Φ (n + 1)) U
            (homSections (K.complex.d n (n + 1)) U z)) := by
  rw [deltaFamily, homSections_add, homSections_comp, homSections_comp, ofShiftDownHom_eq,
    homSections_comp, homSections_eqToHom]

/-- The second summand of the commutator, read through
`SheafOfModules.DifferentialGradedModule.ofShiftDownHom`. -/
theorem ofShiftDownHom_comp_d (n : ℤ) :
    ofShiftDownHom Φ n ≫ N.complex.d n (n + 1) =
      shiftDownApp Φ (n + 1) ≫ N.complex.d ((n + 1) - 1) (n + 1) := by
  rw [ofShiftDownHom_eq, Category.assoc, eqToHom_comp_d N.complex (degSuccSubOne n)]

/-- **A homomorphism of graded modules into the shift down by one carries the action across**, in
the form the two Leibniz computations below consume: the transport identifies the degree
`(n - 1) + i` at which the shift reads a product with the degree `(n + i) - 1` at which it stores
it. -/
theorem shiftDownApp_mul (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    homSections (shiftDownApp Φ (n + i)) U ((K.mul n i).app U x y) =
      castHom N.complex.X (show (n - 1) + i = (n + i) - 1 by omega) U
        ((N.mul (n - 1) i).app U (homSections (shiftDownApp Φ n) U x) y) :=
  ((shiftDownApp_homSections Φ (n + i) U _).trans (Φ.map_smul n i U x y)).trans
    ((castHom_rfl N.complex.X U _).symm.trans
      (Cofree.castHom_eq_castHom (X := N.complex.X) rfl
        (show (n - 1) + i = (n + i) - 1 by omega) U
        (gradedShiftDown_smul_eval_heq N n i U _ y)))

/-- **The commutator `d ∘ Φ + Φ ∘ d` is right `A`-linear.** The signed Leibniz rule of `N`
applied to `Φ(x) · a` and the signed Leibniz rule of `K` applied to `x · a` each contribute a
term `Φ(x) · (d a)`, with the opposite signs `(-1)^{n-1}` and `(-1)^n`; the two cancel, and the
remaining terms are the two summands of the commutator acted on by `a`. -/
theorem deltaFamily_mul (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    homSections (deltaFamily Φ (n + i)) U ((K.mul n i).app U x y) =
      (N.mul n i).app U (homSections (deltaFamily Φ n) U x) y := by
  rw [deltaFamily_homSections, deltaFamily_homSections]
  set u := homSections (shiftDownApp Φ n) U x
  set dx := homSections (K.complex.d n (n + 1)) U x
  set v := homSections (shiftDownApp Φ (n + 1)) U dx
  set dy := homSections (A.complex.d i (i + 1)) U y
  -- the mixed term `Φ(x) · (d a)`, in the degree it lands in after every transport
  set z : (N.complex.X (n + i)).val.obj U :=
    castHom N.complex.X (show (n - 1) + (i + 1) = n + i by omega) U
      ((N.mul (n - 1) (i + 1)).app U u dy)
  -- the first summand of the commutator at `x · y`, by the Leibniz rule of `N`
  have hL1 : homSections (N.complex.d ((n + i) - 1) (n + i)) U
        (homSections (shiftDownApp Φ (n + i)) U ((K.mul n i).app U x y)) =
      (N.mul n i).app U (homSections (N.complex.d (n - 1) n) U u) y
        + ((Int.negOnePow (n - 1) : ℤˣ) : ℤ) • z := by
    rw [shiftDownApp_mul Φ n i U x y,
      homSections_d_cast N.complex (show (n - 1) + i = (n + i) - 1 by omega)
        (show (n - 1) + i + 1 = n + i by omega) (by omega) U,
      leibnizMul N (n - 1) i U u y, map_add, AddMonoidHom.map_zsmul,
      Cofree.castHom_castHom, Cofree.castHom_castHom]
    refine congrArg₂ (· + ·) ?_ (congrArg (fun w => ((Int.negOnePow (n - 1) : ℤˣ) : ℤ) • w) ?_)
    · refine Eq.trans ?_ (congrArg (fun w => (N.mul n i).app U w y)
        (castHom_homSections_d N.complex (n - 1) (show (n - 1) + 1 = n by omega) U u))
      exact (Cofree.smul_castHom_left (GradedModule.ofDifferentialGraded N)
        (show (n - 1) + 1 = n by omega) U _ y).symm
    · exact Cofree.castHom_eq_castHom (X := N.complex.X) _ _ U HEq.rfl
  -- the second summand of the commutator at `x · y`, by the Leibniz rule of `K`
  have hL2 : castHom N.complex.X (degSuccSubOne (n + i)) U
        (homSections (shiftDownApp Φ ((n + i) + 1)) U
          (homSections (K.complex.d (n + i) ((n + i) + 1)) U ((K.mul n i).app U x y))) =
      (N.mul n i).app U (castHom N.complex.X (degSuccSubOne n) U v) y
        + ((Int.negOnePow n : ℤˣ) : ℤ) • z := by
    rw [leibnizMul K n i U x y, map_add, AddMonoidHom.map_zsmul,
      shiftDownApp_castHom Φ (add_right_comm n 1 i) U,
      shiftDownApp_castHom Φ (add_assoc n i 1).symm U,
      shiftDownApp_mul Φ (n + 1) i U dx y, shiftDownApp_mul Φ n (i + 1) U x dy,
      map_add, AddMonoidHom.map_zsmul, Cofree.castHom_castHom, Cofree.castHom_castHom,
      Cofree.castHom_castHom, Cofree.castHom_castHom]
    refine congrArg₂ (· + ·) ?_ (congrArg (fun w => ((Int.negOnePow n : ℤˣ) : ℤ) • w) ?_)
    · exact (Cofree.smul_castHom_left (GradedModule.ofDifferentialGraded N)
        (degSuccSubOne n) U v y).symm
    · exact Cofree.castHom_eq_castHom (X := N.complex.X) _ _ U HEq.rfl
  rw [hL1, hL2, map_add, AddMonoidHom.add_apply]
  refine Eq.trans ?_ (add_negOnePow_zsmul_cancel n
    ((N.mul n i).app U (homSections (N.complex.d (n - 1) n) U u) y +
      (N.mul n i).app U (castHom N.complex.X (degSuccSubOne n) U v) y) z)
  abel

/-- **The morphism of right differential graded modules `d ∘ Φ + Φ ∘ d`** attached to a
homomorphism of graded modules from `K` into the shift down by one of `N`. It commutes with the
differentials because `d ∘ d = 0`, and it is right `A`-linear by
`SheafOfModules.DifferentialGradedModule.deltaFamily_mul`. -/
noncomputable def deltaHom : K ⟶ N where
  toHomologicalComplex :=
    { f := deltaFamily Φ
      comm' := by
        rintro n m (rfl : n + 1 = m)
        rw [deltaFamily, deltaFamily, Preadditive.add_comp, Preadditive.comp_add]
        simp only [Category.assoc]
        rw [N.complex.d_comp_d (n - 1) n (n + 1), comp_zero, zero_add,
          ofShiftDownHom_comp_d, ← Category.assoc (K.complex.d n (n + 1))
            (K.complex.d (n + 1) ((n + 1) + 1)),
          K.complex.d_comp_d n (n + 1) ((n + 1) + 1), zero_comp, add_zero] }
  map_mul n i U x y := deltaFamily_mul Φ n i U x y

/-- The component of `deltaHom Φ` in degree `n` is `deltaFamily Φ n`. -/
@[simp] theorem deltaHom_f (n : ℤ) :
    (deltaHom Φ).toHomologicalComplex.f n = deltaFamily Φ n := rfl

/-- **The null-homotopy condition a morphism out of the cone on the identity carries**, for the
commutator of the differentials with `Φ`: it holds by construction. -/
theorem deltaHom_delta (n : ℤ) :
    ofShiftDownHom Φ n ≫ N.complex.d n (n + 1)
        + K.complex.d (n + 1) ((n + 1) + 1) ≫ ofShiftDownHom Φ (n + 1)
      = (𝟙 K : K ⟶ K).toHomologicalComplex.f (n + 1) ≫
          (deltaHom Φ).toHomologicalComplex.f (n + 1) := by
  rw [deltaHom_f, id_f, Category.id_comp, deltaFamily, ofShiftDownHom_comp_d]

/-- **The identity's own graded homomorphism out of a cofree module on a shift down**, with its
source spelled as the graded module underlying the cofree module. This is
`SheafOfModules.Cofree.lowerHom` at the identity, ascribed; the two spellings
`(forgetToGradedModule A).obj` and `GradedModule.ofDifferentialGraded` of that graded module are
equal by definition but not syntactically, and `deltaHom` is stated at the second. -/
noncomputable def cofreeShiftDownFirst (N : DifferentialGradedModule.{t, a, m} A) :
    GradedModule.Hom (GradedModule.ofDifferentialGraded (Cofree.cofree (gradedShiftDown N)))
      (gradedShiftDown N) :=
  Cofree.lowerHom (gradedShiftDown N) (𝟙 (Cofree.cofree (gradedShiftDown N)))

/-- The component of `cofreeShiftDownFirst N` in degree `n` is the first projection
`cofreeFstHom (gradedShiftDown N) n`. -/
theorem shiftDownApp_cofreeShiftDownFirst (N : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    shiftDownApp (cofreeShiftDownFirst N) n = cofreeFstHom (gradedShiftDown N) n := by
  show (Cofree.lowerHom (gradedShiftDown N) (𝟙 (Cofree.cofree (gradedShiftDown N)))).app n = _
  rw [lowerHom_app, id_f, Category.id_comp]

/-- **The counit of the cofree construction at a shift down by one**: the morphism of right
differential graded modules `Cofree(N[-1]) ⟶ N` which carries `(x, y)` in degree `n`, with
`x ∈ N^{n-1}` and `y ∈ N^n`, to `d x + y`. It is the commutator of the differentials with the
identity's own graded homomorphism, so its right `A`-linearity is
`SheafOfModules.DifferentialGradedModule.deltaFamily_mul` and needs no second computation. -/
noncomputable def cofreeCounit (N : DifferentialGradedModule.{t, a, m} A) :
    Cofree.cofree (gradedShiftDown N) ⟶ N :=
  deltaHom (cofreeShiftDownFirst N)

/-- **The counit in coordinates**: the differential on the first, the identity on the second. -/
theorem cofreeCounit_f (N : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (cofreeCounit N).toHomologicalComplex.f n =
      cofreeFstHom (gradedShiftDown N) n ≫ N.complex.d (n - 1) n
        + cofreeSndHom (gradedShiftDown N) n ≫
          eqToHom (congrArg N.complex.X (degSuccSubOne n)) := by
  rw [cofreeCounit, deltaHom_f, deltaFamily, ofShiftDownHom_eq,
    shiftDownApp_cofreeShiftDownFirst, shiftDownApp_cofreeShiftDownFirst]
  exact congrArg₂ (· + ·) rfl (cofree_d_comp_fstHom_comp (gradedShiftDown N) n _)

/-- **The commutator `d ∘ Φ + Φ ∘ d` factors through the cofree module**: it is the cofree lift
of `Φ` followed by the counit. This is what lets the commutator be transported along a base
change: both the lift and the counit are morphisms of *differential* graded modules, which is
all a base change sees. -/
theorem deltaHom_eq
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N)) :
    deltaHom Φ = Cofree.liftDgHom (gradedShiftDown N) Φ ≫ cofreeCounit N := by
  refine Hom.ext fun n => ?_
  set ρ := Cofree.liftDgHom (gradedShiftDown N) Φ
  have hfst : ρ.toHomologicalComplex.f n ≫ cofreeFstHom (gradedShiftDown N) n =
      shiftDownApp Φ n := liftHom_comp_fstHom Φ n
  have hsnd : ρ.toHomologicalComplex.f n ≫ cofreeSndHom (gradedShiftDown N) n =
      K.complex.d n (n + 1) ≫ shiftDownApp Φ (n + 1) := liftHom_comp_sndHom Φ n
  calc (deltaHom Φ).toHomologicalComplex.f n
      = shiftDownApp Φ n ≫ N.complex.d (n - 1) n
          + K.complex.d n (n + 1) ≫ shiftDownApp Φ (n + 1) ≫
            eqToHom (congrArg N.complex.X (degSuccSubOne n)) := by
        rw [deltaHom_f, deltaFamily, ofShiftDownHom_eq]
    _ = (ρ.toHomologicalComplex.f n ≫ cofreeFstHom (gradedShiftDown N) n) ≫
            N.complex.d (n - 1) n
          + (ρ.toHomologicalComplex.f n ≫ cofreeSndHom (gradedShiftDown N) n) ≫
            eqToHom (congrArg N.complex.X (degSuccSubOne n)) :=
        congrArg₂ (· + ·) (congrArg (fun z => z ≫ N.complex.d (n - 1) n) hfst.symm)
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z => z ≫ eqToHom (congrArg N.complex.X (degSuccSubOne n)))
              hsnd.symm))
    _ = (ρ ≫ cofreeCounit N).toHomologicalComplex.f n := by
        refine Eq.trans ?_ (comp_f ρ (cofreeCounit N) n).symm
        refine Eq.trans ?_ (congrArg (fun z => ρ.toHomologicalComplex.f n ≫ z)
          (cofreeCounit_f N n)).symm
        refine Eq.trans ?_ (Eq.symm (Preadditive.comp_add _ _ _ _ _ _))
        exact congrArg₂ (· + ·) (Category.assoc _ _ _) (Category.assoc _ _ _)

end Delta

/-! ### The bijection -/

/-- The degree `-1` family a morphism out of a cone restricts to is natural in the target. -/
private theorem toShiftDownHom_homotopyOfHom_comp {L : DifferentialGradedModule.{t, a, m} A}
    {f : K ⟶ L} (h : cone f ⟶ N) (g : N ⟶ N') :
    toShiftDownHom ((conePackage f).homotopyOfHom (h ≫ g))
        ((conePackage f).homotopyOfHom_mul (h ≫ g)) =
      (toShiftDownHom ((conePackage f).homotopyOfHom h)
        ((conePackage f).homotopyOfHom_mul h)).comp (gradedShiftDownMap g) := by
  refine GradedModule.Hom.ext fun n => ?_
  change eqToHom (congrArg K.complex.X (degEqSubOneSucc n)) ≫
      (conePackage f).homotopyOfHom (h ≫ g) (n - 1) =
    (eqToHom (congrArg K.complex.X (degEqSubOneSucc n)) ≫
      (conePackage f).homotopyOfHom h (n - 1)) ≫ g.toHomologicalComplex.f (n - 1)
  rw [(conePackage f).homotopyOfHom_comp h g (n - 1), Category.assoc]

/-- **A morphism out of the cone on the identity of `K` is a homomorphism of graded modules from
`K` into the shift down by one of the target.** Forwards, a morphism out of the cone restricts to
the degree `-1` family `ConePackage.homotopyOfHom`, which is right `A`-linear; backwards, a
homomorphism `Φ` of graded modules is `ConePackage.desc` of the commutator `d ∘ Φ + Φ ∘ d`
together with `Φ` itself, the null-homotopy condition holding by construction. -/
noncomputable def coneIdentityShiftDownEquiv (K N : DifferentialGradedModule.{t, a, m} A) :
    (cone (𝟙 K) ⟶ N) ≃
      GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N) where
  toFun h := toShiftDownHom ((conePackage (𝟙 K)).homotopyOfHom h)
    ((conePackage (𝟙 K)).homotopyOfHom_mul h)
  invFun Φ := (conePackage (𝟙 K)).desc (deltaHom Φ) (ofShiftDownHom Φ)
    (ofShiftDownHom_mul Φ) (deltaHom_delta Φ)
  left_inv h := by
    refine Eq.trans ?_ ((conePackage (𝟙 K)).desc_homotopyOfHom h)
    refine ConePackage.desc_congr (conePackage (𝟙 K)) ?_
      (funext fun n => ofShiftDownHom_toShiftDownHom _
        ((conePackage (𝟙 K)).homotopyOfHom_mul h) n) _ _ _ _
    refine Hom.ext fun n => ?_
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, n = p + 1 := ⟨n - 1, by omega⟩
    refine Eq.trans ?_ ((conePackage (𝟙 K)).homotopyOfHom_delta h p)
    rw [deltaHom_f, deltaFamily, ← ofShiftDownHom_comp_d]
    simp only [ofShiftDownHom_toShiftDownHom]
  right_inv Φ := (toShiftDownHom_congr
      (funext fun n => (conePackage (𝟙 K)).homotopyOfHom_desc (deltaHom Φ) (ofShiftDownHom Φ)
        (ofShiftDownHom_mul Φ) (deltaHom_delta Φ) n) _ (ofShiftDownHom_mul Φ)).trans
    (toShiftDownHom_ofShiftDownHom Φ (ofShiftDownHom_mul Φ))

/-- **The bijection is natural in the target**: postcomposing a morphism out of the cone
postcomposes the degree `-1` family it restricts to. -/
theorem coneIdentityShiftDownEquiv_comp (h : cone (𝟙 K) ⟶ N) (g : N ⟶ N') :
    coneIdentityShiftDownEquiv K N' (h ≫ g) =
      (coneIdentityShiftDownEquiv K N h).comp (gradedShiftDownMap g) :=
  toShiftDownHom_homotopyOfHom_comp h g

/-! ### A morphism out of a cone is a morphism and a commutator -/

section ConePair

variable {L : DifferentialGradedModule.{t, a, m} A} {f : K ⟶ L}

/-- **The homomorphism of graded modules `K ⟶ N[-1]` a morphism out of the cone of `f`
restricts to.** -/
noncomputable def coneFam (h : cone f ⟶ N) :
    GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N) :=
  toShiftDownHom ((conePackage f).homotopyOfHom h) ((conePackage f).homotopyOfHom_mul h)

/-- The component of `coneFam h` in degree `n` is the homotopy `(conePackage f).homotopyOfHom h`
in degree `n`. -/
theorem ofShiftDownHom_coneFam (h : cone f ⟶ N) (n : ℤ) :
    ofShiftDownHom (coneFam h) n = (conePackage f).homotopyOfHom h n :=
  ofShiftDownHom_toShiftDownHom _ ((conePackage f).homotopyOfHom_mul h) n

/-- **A morphism out of a cone is determined by the morphism and the commutator it restricts
to.** -/
theorem cone_hom_ext {h h' : cone f ⟶ N}
    (hβ : (conePackage f).inclusion ≫ h = (conePackage f).inclusion ≫ h')
    (hα : coneFam h = coneFam h') : h = h' := by
  have hfam : (conePackage f).homotopyOfHom h = (conePackage f).homotopyOfHom h' :=
    funext fun n => ((ofShiftDownHom_coneFam h n).symm.trans
      (congrArg (fun Φ => ofShiftDownHom Φ n) hα)).trans (ofShiftDownHom_coneFam h' n)
  rw [← (conePackage f).desc_homotopyOfHom h, ← (conePackage f).desc_homotopyOfHom h']
  exact ConePackage.desc_congr (conePackage f) hβ hfam _ _ _ _

/-- **The commutator of the differentials with the family a morphism out of a cone restricts to
is `f` followed by the morphism it restricts to.** -/
theorem deltaHom_coneFam (h : cone f ⟶ N) :
    deltaHom (coneFam h) = f ≫ ((conePackage f).inclusion ≫ h) := by
  refine Hom.ext fun n => ?_
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, n = p + 1 := ⟨n - 1, by omega⟩
  refine Eq.trans ?_ ((conePackage f).homotopyOfHom_delta h p)
  rw [deltaHom_f, deltaFamily, ← ofShiftDownHom_comp_d]
  simp only [ofShiftDownHom_coneFam]

/-- The null-homotopy condition `ConePackage.desc` consumes, read off the commutator identity. -/
theorem coneDesc_delta_of_deltaHom (β : L ⟶ N)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N))
    (hcond : deltaHom Φ = f ≫ β) (n : ℤ) :
    ofShiftDownHom Φ n ≫ N.complex.d n (n + 1)
        + K.complex.d (n + 1) ((n + 1) + 1) ≫ ofShiftDownHom Φ (n + 1)
      = f.toHomologicalComplex.f (n + 1) ≫ β.toHomologicalComplex.f (n + 1) := by
  refine Eq.trans ?_ (congrArg (fun z : K ⟶ N => z.toHomologicalComplex.f (n + 1)) hcond)
  rw [deltaHom_f, deltaFamily, ofShiftDownHom_comp_d]

/-- **The morphism out of the cone of `f` given by a morphism out of the target together with a
homomorphism of graded modules into the shift down of the target whose commutator with the
differentials is `f` followed by it.** -/
noncomputable def coneDescOf (β : L ⟶ N)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N))
    (hcond : deltaHom Φ = f ≫ β) : cone f ⟶ N :=
  (conePackage f).desc β (ofShiftDownHom Φ) (ofShiftDownHom_mul Φ)
    (coneDesc_delta_of_deltaHom β Φ hcond)

/-- The morphism `coneDescOf β Φ hcond` restricts to `β` along the inclusion of `L` into the
cone. -/
theorem inclusion_coneDescOf (β : L ⟶ N)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N))
    (hcond : deltaHom Φ = f ≫ β) :
    (conePackage f).inclusion ≫ coneDescOf β Φ hcond = β :=
  ConePackage.inclusion_desc _ _ _ _ _

/-- The morphism `coneDescOf β Φ hcond` restricts to `Φ` on `K`. -/
theorem coneFam_coneDescOf (β : L ⟶ N)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded K) (gradedShiftDown N))
    (hcond : deltaHom Φ = f ≫ β) : coneFam (coneDescOf β Φ hcond) = Φ :=
  Eq.trans (toShiftDownHom_congr
    (funext fun n => (conePackage f).homotopyOfHom_desc β (ofShiftDownHom Φ)
      (ofShiftDownHom_mul Φ) (coneDesc_delta_of_deltaHom β Φ hcond) n) _
      (ofShiftDownHom_mul Φ))
    (toShiftDownHom_ofShiftDownHom Φ (ofShiftDownHom_mul Φ))

/-- **The family a morphism out of a cone restricts to is natural in the target.** -/
theorem coneFam_comp (h : cone f ⟶ N) (g : N ⟶ N') :
    coneFam (h ≫ g) = (coneFam h).comp (gradedShiftDownMap g) :=
  toShiftDownHom_homotopyOfHom_comp h g

end ConePair

end SheafOfModules.DifferentialGradedModule

end
