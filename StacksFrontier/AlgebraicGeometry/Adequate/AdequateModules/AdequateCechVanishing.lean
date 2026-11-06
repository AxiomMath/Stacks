module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateAffineSingletonSheaf
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional
public import StacksFrontier.CategoryTheory.Limits.Finite.Connected
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily

/-!
# Vanishing of the positive Čech homology of a flat surjection of affines

Let `F` be an adequate sheaf of modules on a chosen big `τ`-site over `S` and let `f : X ⟶ Y` be a
flat surjective morphism between affine objects of the site. [Stacks, Tag 06VL] asserts that the
extended Čech complex of the one-member family `{f}` is exact; this module proves the positive
degrees of that assertion, namely that the Čech complex of `{f}` with coefficients in `F` has
vanishing homology in every positive degree.

## Main results

* `Stacks.Adequate.singletonCechComplexIso` identifies the Čech complex of a one-member family
  `{f}` with the alternating coface map complex of the Čech nerve of `Over.mk f` in the slice,
  for an arbitrary additive presheaf.
* `Stacks.Adequate.isZero_cechHomology_singleton_of_isAdequate` is the vanishing itself, in the
  shape the previous isomorphism transports: the homology of the alternating coface map complex of
  the Čech nerve of `Over.mk f` is zero in every positive degree.

## Implementation notes

This module formalizes the proof of Stacks 06VL.

The argument compares the Čech cosimplicial object of the one-member family `{f}` with the
Amitsur augmentation of the corresponding ring map and then quotes [Stacks, Tag 023M], in the form
`Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat`. The comparison is a
chain of four identifications: the Čech complex of `{f}` is the alternating coface map complex of
the Čech nerve of `Over.mk f`; that nerve is carried by the slice-forgetting functor to the nerve
of the corresponding object over `Spec A`; the nerve of an affine object is the spectrum of the
Čech conerve of the ring map, because the conerve of an arrow out of an initial object is a
product; and the sections of an adequate `F` on each term of that conerve are the base change of
`F(Spec A)`, by `Stacks.Adequate.bijective_affineSectionBaseChangeMap_base` (here in the shape of
a natural isomorphism of diagrams, built from the base-change comparison map).

All of the chain except the two statements named above is `private`, and lives in the auxiliary
namespace `Stacks.Adequate.AdequateCechVanishing` so that its generic names (`conerveProductIso`,
`nerveMapIso`, …) cannot clash with a declaration of the same name in a sibling module: two
modules declaring the same private name both end up in the environment of an importer and the
import then fails.

The compiler option `backward.isDefEq.respectTransparency`, which relaxes definitional-equality
transparency, is not set here: the handful of definitions whose semireducibility the option would
hide are
made unfoldable at `implicit` transparency by the `attribute [local implicit_reducible]` block,
which is an attribute rather than an option, and the remaining places are restructured into
term-mode steps that elaborate at default transparency.

The one genuine obstruction is that the `A`-algebra structure of an object of `Alg_A` is not
definitionally the one `AdequateFunctor.moduleValuedFunctorBaseChangeMap` builds from its
structure morphism, only propositionally equal to it (`toAlgebra_algebraMap`). So
`extensionToValue` is factored through `extensionToValueOfAlgebra`, which takes that algebra
structure as an argument, and the two are compared by substituting along that equality.

The base algebra of the source's category `Alg_A` and its structure morphisms are
`Stacks.Adequate.baseAlgebra` and `Stacks.Adequate.baseAlgebraHom`, which are reducible
`abbrev`s: the module structure on `F(Spec A)` over `A` is only found by instance synthesis,
which is reducible-only, when the base algebra unfolds to `CommAlgCat.of A A`.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u m u₁ v₁ u₂ v₂

attribute [local implicit_reducible] ModuleCat.restrictScalars
  AlgebraicTopology.alternatingCofaceMapComplex
  AlgebraicTopology.AlternatingCofaceMapComplex.obj
  AlgebraicTopology.algebraMapArrow
  CategoryTheory.Arrow.cechConerve
  CategoryTheory.cechNerveTerminalFrom
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor
  CategoryTheory.PreZeroHypercover.singleton
  Stacks.CechSite.cechFormalCoproduct
  Stacks.CechSite.cechFormalCoproductMap

namespace Stacks.Adequate

namespace AdequateCechVanishing

/-! ### The flat base change identification, as an isomorphism of diagrams -/

private noncomputable def extensionToValueOfAlgebra {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion R P))
    (Y : AdequateFunctor.AlgebrasInSite R P) (i : Algebra R Y.obj)
    (halg : ∀ (b s : Y.obj) (x : F.obj (op (op Y))) (r : R),
      s = ((AdequateFunctor.siteAlgebraInclusion R P).map
        (baseAlgebraHom P hR Y)).hom.toRingHom r →
      b • (s • x) = (@algebraMap R Y.obj _ _ i) r • (b • x)) :
    letI : Algebra R Y.obj := i;
    Y.obj ⊗[R] F.obj (op (op (baseAlgebra P hR))) →ₗ[Y.obj] F.obj (op (op Y)) := by
  letI : Algebra R Y.obj := i
  letI : Module R (F.obj (op (op Y))) := Module.compHom _ (algebraMap R Y.obj)
  letI : IsScalarTower R Y.obj (F.obj (op (op Y))) :=
    IsScalarTower.of_algebraMap_smul fun _ => congrFun rfl
  refine TensorProduct.AlgebraTensorModule.lift {
    toFun := fun b => {
      toFun := fun m => b • F.map (baseAlgebraHom P hR Y).op.op m
      map_add' := by intros; simp only [map_add, smul_add]; exact rfl
      map_smul' := ?_ }
    map_add' := by intros; ext; exact add_smul _ _ _
    map_smul' := by intros; ext; exact mul_smul _ _ _ }
  rename_i b
  intro r m
  rw [F.map_smul]
  exact halg b _ _ r rfl

/-- The scalar-compatibility hypothesis of `extensionToValueOfAlgebra` for the default algebra. -/
private lemma smul_smul_of_eq_algebraMap {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion R P))
    (Y : AdequateFunctor.AlgebrasInSite R P) (b s : Y.obj) (x : F.obj (op (op Y))) (r : R)
    (hs : s = ((AdequateFunctor.siteAlgebraInclusion R P).map
      (baseAlgebraHom P hR Y)).hom.toRingHom r) :
    b • (s • x) = algebraMap R Y.obj r • (b • x) :=
  (smul_comm b s x).trans (congrArg (fun t : Y.obj => t • (b • x)) hs)

private noncomputable def extensionToValue {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion R P))
    (Y : AdequateFunctor.AlgebrasInSite R P) :
    Y.obj ⊗[R] F.obj (op (op (baseAlgebra P hR))) →ₗ[Y.obj] F.obj (op (op Y)) :=
  extensionToValueOfAlgebra P hR F Y inferInstance
    (smul_smul_of_eq_algebraMap P hR F Y)

private lemma extensionToValue_tmul {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion R P))
    (Y : AdequateFunctor.AlgebrasInSite R P) (b : Y.obj)
    (m : F.obj (op (op (baseAlgebra P hR)))) :
    extensionToValue P hR F Y (b ⊗ₜ[R] m) =
      b • F.map (baseAlgebraHom P hR Y).op.op m :=
  rfl

private lemma extensionToValue_bijective {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion R P))
    (hF : AdequateFunctor.IsAdequate (AdequateFunctor.siteAlgebraInclusion R P) F)
    (Y : AdequateFunctor.AlgebrasInSite R P) [Module.Flat R Y.obj] :
    Function.Bijective (extensionToValue P hR F Y) := by
  have hf : RingHom.Flat
      ((AdequateFunctor.siteAlgebraInclusion R P).map
        (baseAlgebraHom P hR Y)).hom.toRingHom := by
    show RingHom.Flat (algebraMap R Y.obj)
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have e := AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective
    (AdequateFunctor.siteAlgebraInclusion R P) F hF (baseAlgebraHom P hR Y) hf
  dsimp +instances only [AdequateFunctor.moduleValuedFunctorBaseChangeMap,
    baseAlgebraHom, AdequateFunctor.siteAlgebraInclusion,
    ObjectProperty.ι_map, ObjectProperty.ι_obj, ObjectProperty.homMk_hom,
    CommAlgCat.hom_ofHom, Algebra.ofId] at e
  have hi : ((algebraMap R Y.obj).toAlgebra) = (inferInstance : Algebra R Y.obj) :=
    toAlgebra_algebraMap
  have e' : ∀ h, Function.Bijective
      (extensionToValueOfAlgebra P hR F Y ((algebraMap R Y.obj).toAlgebra) h) := fun _ => e
  exact Eq.subst (motive := fun i : Algebra R Y.obj =>
    ∀ h, Function.Bijective (extensionToValueOfAlgebra P hR F Y i h)) hi e'
    (smul_smul_of_eq_algebraMap P hR F Y)

private lemma extensionToValue_naturality {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion R P))
    {Y Z : AdequateFunctor.AlgebrasInSite R P} (f : Y ⟶ Z)
    (x : Y.obj ⊗[R] F.obj (op (op (baseAlgebra P hR)))) :
    F.map f.op.op (extensionToValue P hR F Y x) =
      extensionToValue P hR F Z
        (TensorProduct.map f.hom.hom.toLinearMap LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact rfl
  | tmul b m =>
    rw [extensionToValue_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, extensionToValue_tmul]
    refine (F.map_smul f.op.op b (F.map (baseAlgebraHom P hR Y).op.op m)).trans ?_
    congr 1
    rw [← F.map_comp_apply, ← op_comp, ← op_comp, baseAlgebraHom_comp]
  | add x y hx hy => simp only [map_add, hx, hy]; exact rfl

private noncomputable def adequateFlatDiagramIso
    {R : Type u} [CommRing R]
    (P : ObjectProperty Scheme.{u}) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn.{max u m}
      (AdequateFunctor.siteAlgebraInclusion R P))
    (hF : AdequateFunctor.IsAdequate (AdequateFunctor.siteAlgebraInclusion R P) F)
    {J : Type*} [Category J] (K : J ⥤ AdequateFunctor.AlgebrasInSite R P)
    [∀ j, Module.Flat R (K.obj j).obj] :
    K ⋙ AdequateFunctor.siteAlgebraInclusion R P ⋙
        AlgebraicTopology.tensorModuleFunctor R (F.obj (op (op (baseAlgebra P hR)))) ⋙
          forget₂ (ModuleCat R) AddCommGrpCat ≅
      K ⋙ (opOpEquivalence _).inverse ⋙ F.presheaf := by
  refine NatIso.ofComponents (fun j =>
    (LinearEquiv.ofBijective (extensionToValue P hR F (K.obj j))
      (extensionToValue_bijective P hR F hF (K.obj j))).toAddEquiv.toAddCommGrpIso) ?_
  intro i j f
  ext x
  exact (extensionToValue_naturality P hR F (K.map f) x).symm

private noncomputable def affineFlatDiagramIso
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    (R : CommRingCat.{u}) (g : Spec R ⟶ S)
    (hR : schemeSizeBelow B.cutoff (Spec R))
    {J : Type*} [Category J]
    (K : J ⥤ AdequateFunctor.AlgebrasInSite R (schemeSizeBelow B.cutoff))
    [∀ j, Module.Flat R (K.obj j).obj] :
    K ⋙ AdequateFunctor.siteAlgebraInclusion R (schemeSizeBelow B.cutoff) ⋙
        AlgebraicTopology.tensorModuleFunctor R
          ((affineSectionFunctor B F R g).obj
            (op (op (baseAlgebra (schemeSizeBelow B.cutoff) hR)))) ⋙
          forget₂ (ModuleCat R) AddCommGrpCat ≅
      (K.op ⋙ affineSpecOver B R g).rightOp ⋙ F.val.presheaf :=
  adequateFlatDiagramIso.{u, m} (schemeSizeBelow B.cutoff) hR
    (affineSectionFunctor B F R g)
    (isAdequate_affineSectionFunctor.{u, m} B F hF R g hR) K

/-! ### Faithful flatness of a flat surjection of affines -/

private alias affineMap_faithfullyFlat := Stacks.Adequate.faithfullyFlat_appTop_of_bigSite_map

/-! ### Čech nerves -/

private noncomputable def nerveMapIso
    {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [HasFiniteProducts D]
    (G : C ⥤ D) [PreservesFiniteProducts G] (X : C) :
    cechNerveTerminalFrom X ⋙ G ≅ cechNerveTerminalFrom (G.obj X) := by
  refine NatIso.ofComponents
    (fun n => PreservesProduct.iso G (fun _ : Fin (n.unop.len + 1) => X)) ?_
  intro n m g
  apply Pi.hom_ext
  intro i
  simp only [PreservesProduct.iso_hom, Functor.comp_map, cechNerveTerminalFrom,
    Category.assoc, piComparison_comp_π, ← G.map_comp, Pi.lift_comp_π]

private noncomputable def algSpecNerveIso
    (R : CommRingCat.{u}) (A : CommAlgCat R) :
    cechNerveTerminalFrom (.op A) ⋙ algSpec R ≅
      cechNerveTerminalFrom ((algSpec R).obj (.op A)) :=
  nerveMapIso (algSpec R) (.op A)

private noncomputable def nerveIsoOfIso
    {C : Type*} [Category C] [HasFiniteProducts C] {X Y : C} (e : X ≅ Y) :
    cechNerveTerminalFrom X ≅ cechNerveTerminalFrom Y := by
  refine NatIso.ofComponents (fun n => Pi.mapIso (fun _ : Fin (n.unop.len + 1) => e)) ?_
  intro n m g
  apply Pi.hom_ext
  intro i
  simp only [cechNerveTerminalFrom, Category.assoc, Pi.mapIso_hom_π,
    Pi.lift_comp_π_assoc, Pi.lift_comp_π]

private noncomputable def singletonNerveIsoOfArrowIso
    {C : Type*} [Category C] {X Y X' Y' : C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (w : eX.hom ≫ f' = f ≫ eY.hom)
    [HasFiniteProducts (Over Y)] [HasFiniteProducts (Over Y')] :
    cechNerveTerminalFrom (Over.mk f) ⋙ Over.forget Y ≅
      cechNerveTerminalFrom (Over.mk f') ⋙ Over.forget Y' := by
  let H := (Over.mapIso eY).functor
  let e : H.obj (Over.mk f) ≅ Over.mk f' := Over.isoMk eX w
  exact Functor.isoWhiskerRight
    (nerveMapIso H (Over.mk f) ≪≫ nerveIsoOfIso e) (Over.forget Y')

/-! ### Alternating coface map complexes -/

private noncomputable def alternatingComplexMapIso
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (G : C ⥤ D) [G.Additive] (X : CosimplicialObject C) :
    (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex D).obj (X ⋙ G) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  rintro i _ rfl
  dsimp only [Iso.refl_hom]
  simp only [Category.id_comp, Category.comp_id]
  dsimp only [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CochainComplex.of_d, Functor.mapHomologicalComplex]
  rw [CochainComplex.of_d, CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Functor.map_sum, Functor.map_zsmul]
  rfl

/-- Isomorphic cosimplicial objects have the same vanishing of homology of the alternating coface
map complex. -/
private lemma isZero_alternatingHomology_of_iso {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [CategoryWithHomology C] {X Y : CosimplicialObject C} (e : X ≅ Y) {n : ℕ}
    (h : IsZero (((AlgebraicTopology.alternatingCofaceMapComplex C).obj Y).homology n)) :
    IsZero (((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).homology n) :=
  h.of_iso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    ((AlgebraicTopology.alternatingCofaceMapComplex C).mapIso e))

/-! ### The Čech conerve of an arrow out of an initial object -/

private noncomputable def conerveProductComponentIso
    {C : Type u₁} [Category.{v₁} C] [HasFiniteColimits C]
    (f : Arrow C) (h : IsInitial f.left) (n : SimplexCategory) :
    op (widePushout f.left (fun _ : Fin (n.len + 1) => f.right) (fun _ => f.hom)) ≅
      ∏ᶜ fun _ : Fin (n.len + 1) => op f.right := by
  let fs : Fin (n.len + 1) → (f.left ⟶ f.right) := fun _ => f.hom
  let X := ∏ᶜ fun _ : Fin (n.len + 1) => op f.right
  let q : f.left ⟶ X.unop := h.to _
  let ps : (i : Fin (n.len + 1)) → f.right ⟶ X.unop :=
    fun i => (Pi.π (fun _ : Fin (n.len + 1) => op f.right) i).unop
  have hw : ∀ i, f.hom ≫ ps i = q := fun i => h.hom_ext _ _
  refine { hom := Pi.lift (fun i => (WidePushout.ι fs i).op)
           inv := (WidePushout.desc q ps hw).op
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · apply Quiver.Hom.unop_inj
    apply WidePushout.hom_ext fs
    · intro i
      rw [unop_comp, unop_id, Category.comp_id, Quiver.Hom.unop_op, ← Category.assoc,
        WidePushout.ι_desc]
      exact congrArg Quiver.Hom.unop (Pi.lift_comp_π (fun i => (WidePushout.ι fs i).op) i)
    · rw [← WidePushout.arrow_ι fs 0]
      simp only [Category.assoc]
      congr 1
      rw [unop_comp, unop_id, Category.comp_id, Quiver.Hom.unop_op, ← Category.assoc,
        WidePushout.ι_desc]
      exact congrArg Quiver.Hom.unop (Pi.lift_comp_π (fun i => (WidePushout.ι fs i).op) 0)
  · refine Pi.hom_ext _ _ fun i => ?_
    rw [Category.assoc, Category.id_comp, Pi.lift_comp_π]
    exact congrArg Quiver.Hom.op (WidePushout.ι_desc fs q ps hw i)

private noncomputable def conerveProductIso
    {C : Type u₁} [Category.{v₁} C] [HasFiniteColimits C]
    (f : Arrow C) (h : IsInitial f.left) :
    f.cechConerve.op ≅ cechNerveTerminalFrom (op f.right) := by
  refine NatIso.ofComponents (fun n => conerveProductComponentIso f h n.unop) ?_
  intro n m g
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, conerveProductComponentIso, cechNerveTerminalFrom,
    Functor.op_map, Pi.lift_comp_π]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  exact WidePushout.ι_desc _ _ _ _ i

private noncomputable def algebraMapArrowLeftIsInitial
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    IsInitial (AlgebraicTopology.algebraMapArrow R A).left :=
  CommAlgCat.isInitialSelf

private noncomputable def conerveProductUnopIso
    {C : Type u₁} [Category.{v₁} C] [HasFiniteColimits C]
    (f : Arrow C) (h : IsInitial f.left) :
    (cechNerveTerminalFrom (op f.right)).unop ≅ f.cechConerve :=
  (NatIso.unop (conerveProductIso f h)) ≪≫ (Functor.opUnopIso f.cechConerve)

private noncomputable def amitsurNerveIso
    (R : Type u₁) (A : Type u₂) (M : Type*)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] :
    (cechNerveTerminalFrom (op (AlgebraicTopology.algebraMapArrow R A).right)).unop ⋙
      (AlgebraicTopology.tensorModuleFunctor (ULift.{u₂} R) M ⋙
        ModuleCat.restrictScalars (algebraMap R (ULift.{u₂} R))) ≅
      (AlgebraicTopology.amitsurAugmentation R A M).right :=
  Functor.isoWhiskerRight (conerveProductUnopIso
    (AlgebraicTopology.algebraMapArrow R A) (algebraMapArrowLeftIsInitial R A)) _

/-! ### The Amitsur complex is acyclic in positive degrees -/

private lemma isZero_amitsurHomology
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((AlgebraicTopology.alternatingCofaceMapComplex
      (ModuleCat R)).obj (AlgebraicTopology.amitsurAugmentation R A M).right).homology n) := by
  have h := (HomologicalComplex.acyclic_iff
    (AlgebraicTopology.amitsurExtendedCochainComplex R A M)).mp
      (Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat R A M) (n + 1)
  have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
    (ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk n (n + 1) rfl)
  have hnxt : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
    (ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (n + 1) (n + 2) (by omega))
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) hp hnxt] at h
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp
  have hprev : (ComplexShape.up ℕ).prev n = n - 1 :=
    (ComplexShape.up ℕ).prev_eq'
      (ComplexShape.up_mk (n - 1) n (Nat.sub_add_cancel hn))
  have hnext : (ComplexShape.up ℕ).next n = n + 1 :=
    (ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk n (n + 1) rfl)
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) hprev hnext]
  cases n with
  | zero => omega
  | succ n =>
    convert h using 1
    rfl

private lemma isZero_amitsurNerveHomology
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((AlgebraicTopology.alternatingCofaceMapComplex
      (ModuleCat R)).obj
        ((cechNerveTerminalFrom
          (op (AlgebraicTopology.algebraMapArrow R A).right)).unop ⋙
          (AlgebraicTopology.tensorModuleFunctor (ULift R) M ⋙
            ModuleCat.restrictScalars (algebraMap R (ULift R))))).homology n) :=
  isZero_alternatingHomology_of_iso (amitsurNerveIso R A M) (isZero_amitsurHomology R A M n hn)

private lemma isZero_homologyForget
    (R : Type*) [CommRing R] (K : CochainComplex (ModuleCat R) ℕ)
    (n : ℕ) (h : IsZero (K.homology n)) :
    IsZero ((((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).homology n) := by
  have hSC : (K.sc n).Exact := (HomologicalComplex.exactAt_iff_isZero_homology K n).mpr h
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp
    (hSC.map (forget₂ (ModuleCat R) AddCommGrpCat))

private lemma isZero_amitsurNerveAddCommGrpHomology
    (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((AlgebraicTopology.alternatingCofaceMapComplex
      AddCommGrpCat).obj
        ((cechNerveTerminalFrom
          (op (AlgebraicTopology.algebraMapArrow R A).right)).unop ⋙
          (AlgebraicTopology.tensorModuleFunctor (ULift R) M ⋙
            ModuleCat.restrictScalars (algebraMap R (ULift R))) ⋙
          forget₂ (ModuleCat R) AddCommGrpCat)).homology n) := by
  let X := (cechNerveTerminalFrom
      (op (AlgebraicTopology.algebraMapArrow R A).right)).unop ⋙
        (AlgebraicTopology.tensorModuleFunctor (ULift R) M ⋙
          ModuleCat.restrictScalars (algebraMap R (ULift R)))
  exact IsZero.of_iso (isZero_homologyForget R
    ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj X)
    n (isZero_amitsurNerveHomology R A M n hn))
    (((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (alternatingComplexMapIso (forget₂ (ModuleCat R) AddCommGrpCat) X)).symm)

/-! ### The Čech nerve of a flat algebra of the site -/

open scoped MonoidalCategory

private lemma flatBoundedProducts (R : CommRingCat.{u}) (κ : Cardinal.{u})
    (hR : (Spec R).size < κ) :
    (show ObjectProperty (CommAlgCat R)ᵒᵖ from fun A =>
      (Spec (CommRingCat.of A.unop)).size < κ ∧
        Module.Flat R A.unop).IsClosedUnderFiniteProducts := by
  let P : ObjectProperty (CommAlgCat R)ᵒᵖ := fun A =>
    (Spec (CommRingCat.of A.unop)).size < κ ∧ Module.Flat R A.unop
  let : P.IsClosedUnderIsomorphisms := ⟨by
    intro X Y e hX
    have e' := CommAlgCat.algEquivOfIso e.unop
    refine ⟨?_, ?_⟩
    · exact lt_of_eq_of_lt
        (Scheme.size_congr (Scheme.Spec.mapIso
          ((forget₂ (CommAlgCat R) CommRingCat).mapIso e.unop).op).symm) hX.1
    · let := hX.2
      exact Module.Flat.of_linearEquiv e'.toLinearEquiv⟩
  let : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨D, -⟩
    have ht : IsTerminal (limit D) :=
      (isLimitEquivIsTerminalOfIsEmpty _ (J := Discrete.{0} PEmpty) (F := D)
        (limit.cone D)) (limit.isLimit D)
    exact P.prop_of_iso (ht.uniqueUpToIso
      (terminalOpOfInitial (CommAlgCat.isInitialSelf (R := R)))).symm ⟨hR, inferInstance⟩
  let : P.IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨D, hD⟩
    let X := D.obj ⟨WalkingPair.left⟩
    let Y := D.obj ⟨WalkingPair.right⟩
    have hX := hD ⟨WalkingPair.left⟩
    have hY := hD ⟨WalkingPair.right⟩
    let := hX.2
    let := hY.2
    let e : limit D ≅ X ⊗ Y :=
      HasLimit.isoOfNatIso (diagramIsoPair D) ≪≫
        limit.isoLimitCone ⟨_, CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y⟩
    apply P.prop_of_iso e.symm
    refine ⟨?_, ?_⟩
    · exact lt_of_eq_of_lt (Scheme.size_congr (pullbackSpecIso R X.unop Y.unop)).symm
        (Scheme.size_pullback_lt _ _ hX.1 hY.1)
    · show Module.Flat R (X.unop ⊗[R] Y.unop)
      infer_instance
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

private lemma algebraNerveFlatBounded (R : CommRingCat.{u}) (κ : Cardinal.{u})
    (hR : (Spec R).size < κ) (A : CommAlgCat R)
    (hA : (Spec (CommRingCat.of A)).size < κ) [Module.Flat R A]
    (n : SimplexCategory) :
    (Spec (CommRingCat.of ((cechNerveTerminalFrom (op A)).unop.obj n))).size < κ ∧
      Module.Flat R ((cechNerveTerminalFrom (op A)).unop.obj n) := by
  let P : ObjectProperty (CommAlgCat R)ᵒᵖ := fun T =>
    (Spec (CommRingCat.of T.unop)).size < κ ∧ Module.Flat R T.unop
  let : P.IsClosedUnderFiniteProducts := flatBoundedProducts R κ hR
  exact P.prop_product (fun _ => ⟨hA, inferInstance⟩)

private noncomputable def boundedAlgebraNerve
    (R : CommRingCat.{u}) (κ : Cardinal.{u}) (hR : (Spec R).size < κ)
    (A : CommAlgCat R) (hA : (Spec (CommRingCat.of A)).size < κ) [Module.Flat R A] :
    SimplexCategory ⥤ AdequateFunctor.AlgebrasInSite R (schemeSizeBelow κ) :=
  ObjectProperty.lift _ (cechNerveTerminalFrom (op A)).unop
    (fun n => (algebraNerveFlatBounded R κ hR A hA n).1)

private noncomputable def affineSpecNerveIso
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S)
    (R : CommRingCat.{u}) (g : Spec R ⟶ S)
    (hR : (Spec R).size < B.cutoff)
    (A : AdequateFunctor.AlgebrasInSite R (schemeSizeBelow B.cutoff))
    [Module.Flat R A.obj] :
    let K := boundedAlgebraNerve R B.cutoff hR A.obj A.property
    let G := affineSpecOver B R g
    let f := G.map (baseAlgebraHom (schemeSizeBelow B.cutoff) hR A).op
    letI : HasFiniteWidePullbacks B.category :=
      CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks B.category
    K.op ⋙ G ≅ cechNerveTerminalFrom (Over.mk f) ⋙ Over.forget _ := by
  classical
  dsimp only
  letI : HasFiniteWidePullbacks B.category :=
    CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks B.category
  letI : PreservesFiniteLimits B.toOver := B.preservesFiniteLimits_toOver
  let G := affineSpecOver B R g
  let f := G.map (baseAlgebraHom (schemeSizeBelow B.cutoff) hR A).op
  let Y := G.obj (op (baseAlgebra (schemeSizeBelow B.cutoff) hR))
  let H : Over Y ⥤ Over (Spec R) :=
    Over.post B.toOver ⋙ (Over.iteratedSliceEquiv (B.toOver.obj Y)).functor
  letI : PreservesFiniteProducts H :=
    show PreservesFiniteProducts
      (Over.post B.toOver ⋙ (Over.iteratedSliceEquiv (B.toOver.obj Y)).functor) from
      inferInstance
  let e := nerveMapIso H (Over.mk f)
  let e' := algSpecNerveIso R A.obj
  let K := boundedAlgebraNerve R B.cutoff hR A.obj A.property
  have ee : (K.op ⋙ G) ⋙ B.toOver ≅
      (cechNerveTerminalFrom (Over.mk f) ⋙ Over.forget Y) ⋙ B.toOver := by
    refine (Functor.isoWhiskerRight e' (Over.map g)) ≪≫
      (Functor.isoWhiskerRight e.symm (Over.map g)) ≪≫ ?_
    refine NatIso.ofComponents (fun n => Over.isoMk (Iso.refl _) ?_) ?_
    · change 𝟙 _ ≫ (B.toOver.obj ((cechNerveTerminalFrom (Over.mk f)).obj n).left).hom =
        (B.toOver.map ((cechNerveTerminalFrom (Over.mk f)).obj n).hom).left ≫ g
      rw [Category.id_comp]
      have hw := (B.toOver.map ((cechNerveTerminalFrom (Over.mk f)).obj n).hom).w
      have hy : (B.toOver.obj Y).hom = g := by
        change Spec.map (𝟙 R) ≫ g = g
        simp
      rw [hy] at hw
      exact hw.symm
    · intro n m a
      ext
      rfl
  let hf : B.toOver.FullyFaithful := Functor.FullyFaithful.over ⟨S, B.base_mem⟩ _
    (schemeSizeBelow B.cutoff).fullyFaithfulι
  exact (hf.whiskeringRight SimplexCategoryᵒᵖ).preimageIso ee

/-! ### Vanishing for a flat surjection of affines of the site -/

private lemma isZero_affineSpecHomology
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A]
    (g : Spec (CommRingCat.of (ULift.{u} R)) ⟶ S)
    (hR : (Spec (CommRingCat.of (ULift.{u} R))).size < B.cutoff)
    (hA : (Spec (CommRingCat.of (ULift.{u} A))).size < B.cutoff) :
    let R' := CommRingCat.of (ULift.{u} R)
    let A' : AdequateFunctor.AlgebrasInSite R' (schemeSizeBelow B.cutoff) :=
      ⟨(AlgebraicTopology.algebraMapArrow R A).right, hA⟩
    let G := affineSpecOver B R' g
    let f := G.map (baseAlgebraHom (schemeSizeBelow B.cutoff) hR A').op
    letI : HasFiniteWidePullbacks B.category :=
      CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks B.category
    ∀ n : ℕ, 0 < n → IsZero (((AlgebraicTopology.alternatingCofaceMapComplex
      AddCommGrpCat.{max u m}).obj
        ((cechNerveTerminalFrom (Over.mk f)).rightOp ⋙ (Over.forget _).op ⋙
          F.val.presheaf)).homology n) := by
  dsimp only
  classical
  let : HasFiniteWidePullbacks B.category :=
    CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks B.category
  let R' := CommRingCat.of (ULift.{u} R)
  let A' : AdequateFunctor.AlgebrasInSite R' (schemeSizeBelow B.cutoff) :=
    ⟨(AlgebraicTopology.algebraMapArrow R A).right, hA⟩
  let : Algebra (ULift.{u} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  let : Module.Flat R' A'.obj := by
    dsimp [R', A', AlgebraicTopology.algebraMapArrow]
    exact (Stacks.Descent.faithfullyFlat_ulift R A).toFlat
  let K := boundedAlgebraNerve R' B.cutoff hR A'.obj hA
  let : ∀ j, Module.Flat R' (K.obj j).obj := fun j =>
    (algebraNerveFlatBounded R' B.cutoff hR A'.obj hA j).2
  let G := affineSpecOver B R' g
  let f := G.map (baseAlgebraHom (schemeSizeBelow B.cutoff) hR A').op
  let M := (affineSectionFunctor B F R' g).obj
    (op (op (baseAlgebra (schemeSizeBelow B.cutoff) hR)))
  let : Module R M := Module.compHom M (algebraMap R (ULift.{u} R))
  let e := affineSpecNerveIso B R' g hR A'
  let ec := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (opOpEquivalence SimplexCategory).inverse (NatIso.op e))
    F.val.presheaf
  let eb := affineFlatDiagramIso.{u, m} B F hF R' g hR K
  intro n hn
  exact isZero_alternatingHomology_of_iso (ec ≪≫ eb.symm)
    (isZero_amitsurNerveAddCommGrpHomology R A M n hn)

end AdequateCechVanishing

open AdequateCechVanishing

/-! ### The two statements -/

/-- The Čech complex of the one-member family `{f}` with coefficients in an additive presheaf `F`
is the alternating coface map complex of the Čech nerve of `Over.mk f` in the slice over the
target, evaluated on `F`. Each term of the Čech complex is a product over the one-element index
set of tuples, so it is the value of `F` on the iterated fibre product itself. -/
public noncomputable def singletonCechComplexIso
    {C : Type u₁} [Category.{v₁} C] {Y X : C} (f : X ⟶ Y)
    [HasFiniteProducts (Over Y)] {A : Type u₂} [Category.{v₂} A] [HasProducts.{0} A]
    [Preadditive A] (F : Cᵒᵖ ⥤ A) :
    CechSite.cechComplex (.singleton f) F ≅
      (AlgebraicTopology.alternatingCofaceMapComplex A).obj
        ((cechNerveTerminalFrom (Over.mk f)).rightOp ⋙ (Over.forget Y).op ⋙ F) :=
  (AlgebraicTopology.alternatingCofaceMapComplex A).mapIso
    (show (FormalCoproduct.cosimplicialObjectFunctor
          (CechSite.cechSimplicialObject (.singleton f))).obj ((Over.forget Y).op ⋙ F) ≅
        (cechNerveTerminalFrom (Over.mk f)).rightOp ⋙ (Over.forget Y).op ⋙ F from by
      refine NatIso.ofComponents (fun n => ?_) ?_
      · change (∏ᶜ fun _ : Fin (n.len + 1) → Unit =>
          F.obj (op ((∏ᶜ fun _ : Fin (n.len + 1) => Over.mk f).left))) ≅ _
        exact productUniqueIso _
      intro n m g
      change Pi.lift _ ≫ Pi.π _ (fun _ => PUnit.unit) = Pi.π _ (fun _ => PUnit.unit) ≫ _
      rw [Pi.lift_comp_π]
      rfl)

/-- **[Stacks, Tag 06VL], the positive degrees.** For an adequate sheaf of modules `F` on a chosen
big `τ`-site over `S` and a flat surjective morphism `f : X ⟶ Y` between affine objects of the
site, the Čech complex of the one-member family `{f}` with coefficients in `F` has vanishing
homology in every positive degree. The complex is written here as the alternating coface map
complex of the Čech nerve of `Over.mk f`, which `Stacks.Adequate.singletonCechComplexIso`
identifies with the Čech complex of `{f}`.

The proof compares that nerve with the Amitsur augmentation of the ring map underlying `f` and
quotes [Stacks, Tag 023M]. -/
public theorem isZero_cechHomology_singleton_of_isAdequate
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    {X Y : B.category} (f : X ⟶ Y)
    (hX : IsAffine ((B.toOver.obj X).left))
    (hY : IsAffine ((B.toOver.obj Y).left))
    [Flat ((B.toOver.map f).left)] [Surjective ((B.toOver.map f).left)] :
    letI : HasFiniteWidePullbacks B.category :=
      CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks B.category
    ∀ n : ℕ, 0 < n → IsZero (((AlgebraicTopology.alternatingCofaceMapComplex
      AddCommGrpCat.{max u m}).obj
        ((cechNerveTerminalFrom (Over.mk f)).rightOp ⋙ (Over.forget _).op ⋙
          F.val.presheaf)).homology n) := by
  classical
  let : HasFiniteWidePullbacks B.category :=
    CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks B.category
  let R := Γ((B.toOver.obj Y).left, ⊤)
  let A := Γ((B.toOver.obj X).left, ⊤)
  let φ := ((B.toOver.map f).left.appTop).hom
  let : Algebra R A := φ.toAlgebra
  let : Module.FaithfullyFlat R A := affineMap_faithfullyFlat B f hX hY
  let : Algebra (ULift.{u} R) (ULift.{u} A) := ULift.algebra' R (ULift.{u} A)
  let eR : CommRingCat.of (ULift.{u} R) ≅ CommRingCat.of R :=
    RingEquiv.toCommRingCatIso ULift.ringEquiv
  let eA : CommRingCat.of (ULift.{u} A) ≅ CommRingCat.of A :=
    RingEquiv.toCommRingCatIso ULift.ringEquiv
  let ey := (B.toOver.obj Y).left.isoSpec ≪≫ Scheme.Spec.mapIso eR.op
  let ex := (B.toOver.obj X).left.isoSpec ≪≫ Scheme.Spec.mapIso eA.op
  let g : Spec (CommRingCat.of (ULift.{u} R)) ⟶ S := ey.inv ≫ (B.toOver.obj Y).hom
  have hR : (Spec (CommRingCat.of (ULift.{u} R))).size < B.cutoff :=
    lt_of_eq_of_lt (Scheme.size_congr ey).symm Y.left.property
  have hA : (Spec (CommRingCat.of (ULift.{u} A))).size < B.cutoff :=
    lt_of_eq_of_lt (Scheme.size_congr ex).symm X.left.property
  let P := schemeSizeBelow B.cutoff
  let R' := CommRingCat.of (ULift.{u} R)
  let A' : AdequateFunctor.AlgebrasInSite R' P :=
    ⟨(AlgebraicTopology.algebraMapArrow R A).right, hA⟩
  let G := affineSpecOver B R' g
  let q := baseAlgebraHom P hR A'
  have hw : ex.hom ≫ (B.toOver.map (G.map q.op)).left =
      (B.toOver.map f).left ≫ ey.hom := by
    show ((B.toOver.obj X).left.isoSpec.hom ≫ Spec.map eA.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} R) (ULift.{u} A))) =
      (B.toOver.map f).left ≫ (B.toOver.obj Y).left.isoSpec.hom ≫ Spec.map eR.hom
    rw [← Scheme.isoSpec_hom_naturality_assoc, Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  let eY : Y ≅ G.obj (op (baseAlgebra P hR)) := Over.isoMk (P.isoMk ey) (by
    apply ObjectProperty.hom_ext
    show ey.hom ≫ (Spec.map (𝟙 R') ≫ g) = (B.toOver.obj Y).hom
    rw [Spec.map_id]
    show ey.hom ≫ (𝟙 _ ≫ (ey.inv ≫ _)) = _
    rw [Category.id_comp, Iso.hom_inv_id_assoc])
  let eX : X ≅ G.obj (op A') := Over.isoMk (P.isoMk ex) (by
    apply ObjectProperty.hom_ext
    show ex.hom ≫ ((B.toOver.map (G.map q.op)).left ≫ g) = (B.toOver.obj X).hom
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) hw)).trans ?_
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    exact (B.toOver.map f).w)
  have w : eX.hom ≫ G.map q.op = f ≫ eY.hom :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hw)
  let e := singletonNerveIsoOfArrowIso f (G.map q.op) eX eY w
  let ec := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (opOpEquivalence SimplexCategory).inverse (NatIso.op e))
    F.val.presheaf
  intro n hn
  exact isZero_alternatingHomology_of_iso ec.symm
    (isZero_affineSpecHomology.{u, m} B F hF R A g hR hA n hn)

end Stacks.Adequate

end
