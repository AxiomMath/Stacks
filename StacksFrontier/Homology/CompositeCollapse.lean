module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Collapse of the derived functor of a composite at an acyclic object

Let `G : C ⥤ D` be an additive, left exact functor between abelian categories which preserves
injective objects, and let `T : D ⥤ E` be additive. If an object `A : C` is `G`-acyclic, i.e.
`R ⁿ G (A) = 0` for every `n > 0`, then applying `G` degreewise to an injective resolution of
`A` produces an injective resolution of `G.obj A`. Consequently the right derived functors of
the composite collapse:
`R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G.obj A)`.

This is the Grothendieck spectral sequence edge isomorphism, obtained directly rather than
through a spectral sequence, in the only case in which it is an isomorphism for elementary
reasons. It is the mechanism behind the comparison of the cohomology of a sheaf with the
cohomology of its direct image whenever the higher direct images vanish.

The injectivity hypothesis is not needed for the derived functors to be computable: it is enough
that the terms of the resolution be **acyclic** for the functor one derives. That weaker
statement is Leray's acyclicity lemma, and the second half of this file proves it in the
indexing Mathlib's `CategoryTheory.Functor.rightDerived` uses: a resolution of an object `X` by
objects whose higher right derived functors under `T` vanish computes `R ⁿ T (X)`, with no
injectivity anywhere.

## Main definitions

* `Stacks.RightDerivedComp.mapOfAcyclic`: `G` applied degreewise to an injective resolution of
  a `G`-acyclic object, as an injective resolution of its image.
* `Stacks.RightDerivedComp.objIso`: the collapse isomorphism `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)`.
* `Stacks.RightDerivedComp.acyclic`: the `G`-acyclic objects, as an object property.
* `Stacks.RightDerivedComp.natIso`: the collapse isomorphism as a natural isomorphism on the
  full subcategory of `G`-acyclic objects.
* `Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic`: **an acyclic resolution computes the
  right derived functor** — `R ⁿ T (X) ≅ H ⁿ (T (K))` for any resolution `K` of `X` whose terms
  are `T`-acyclic.

## Main results

* `Stacks.RightDerivedComp.objIso_hom_eq`: the collapse isomorphism is computed by any
  augmentation-preserving comparison of `G` applied to the resolution with an injective
  resolution of `G.obj A`. In particular it does not depend on the chosen resolution.
* `Stacks.RightDerivedComp.toRightDerivedZero_comp_objIso_hom`: in degree zero the collapse
  isomorphism intertwines the two canonical maps to the zeroth right derived functors.
* `Stacks.RightDerivedComp.rightAcyclic_iff_acyclic`: for a left exact functor, being right
  acyclic in the sense of the derived category is the vanishing of the higher right derived
  functors in Mathlib's `ℕ`-indexing.
* `Stacks.RightDerivedComp.acyclic_shortExact`, `Stacks.RightDerivedComp.exists_mono_acyclic`:
  the `T`-acyclic objects form a class adapted to `T`, which is what makes a resolution by them
  compute `R ⁿ T`.

## Implementation notes

The statements are phrased with an explicit injective resolution `I` of `A` rather than with the
chosen one, so that `objIso_hom_eq` can be read as an independence statement. `natIso` uses the
chosen resolution at each object, which is what makes naturality available: a morphism between
`G`-acyclic objects is descended once to the chosen resolutions and the same descent computes
both sides.

The only inputs are that `G` is additive, preserves finite limits and preserves injective
objects. Left exactness is what makes `G` applied to the augmented resolution exact in degree
zero; preservation of injectives is what makes the resulting complex a resolution by injectives,
and hence usable to compute `R ⁿ T`; and acyclicity of `A` is exactness in the positive degrees.

`mapOfAcyclic` cannot be stated with a weaker hypothesis than preservation of injectives: it
*produces* a `CategoryTheory.InjectiveResolution`, one of whose fields is the injectivity of
every term. What is weakened is the use made of it, namely the computation of `R ⁿ T` on the
resulting complex, and that is what `isoRightDerivedObjOfAcyclic` provides: a resolution whose
terms are merely `T`-acyclic computes `R ⁿ T` just as well, so the collapse isomorphism needs
only that `G` carry injective objects to `T`-acyclic ones.

The acyclic half rests on three results that are already in the tree and are only joined here.
`CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso` computes `R ⁿ T` on any
resolution by objects of a class *adapted* to `T` in the sense of [Stacks, Tag 05T8];
`CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact` ([Stacks, Tag 015D]) is
the two-out-of-three property that makes the `T`-acyclic objects such a class; and
`CategoryTheory.Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus`
([Stacks, Tag 015C]) together with `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` moves
acyclicity between the derived-category spelling, in which [Stacks, Tag 015D] is proved, and the
`ℕ`-indexed vanishing statement a consumer actually holds. The derived category enters only
inside those proofs, through `HasDerivedCategory.standard`; no statement below mentions it.

Left exactness of `T` is needed for exactly one step: part (2) of [Stacks, Tag 015C], which is
what repackages a vanishing statement as acyclicity. Without it the degree-zero condition
`T ⟶ R ⁰ T` has to be carried as a separate hypothesis.

## References

* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.RightDerivedComp

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]

section Pointwise

variable (G : C ⥤ D) [G.Additive] {A : C} (I : InjectiveResolution A)

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- The complex obtained by applying `G` degreewise to an injective resolution. -/
noncomputable abbrev mapCocomplex : CochainComplex D ℕ :=
  (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

/-- The augmentation of `mapCocomplex G I` by `G.obj A`, obtained by applying `G` to the
augmentation of `I`. -/
noncomputable def mapι :
    (CochainComplex.single₀ D).obj (G.obj A) ⟶ mapCocomplex G I :=
  (CochainComplex.fromSingle₀Equiv (mapCocomplex G I) (G.obj A)).symm
    ⟨G.map (I.ι.f 0), by
      change G.map (I.ι.f 0) ≫ G.map (I.cocomplex.d 0 1) = 0
      rw [← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]⟩

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- The degree-zero component of the augmentation `mapι G I` is `G` applied to the degree-zero
component of the augmentation of `I`. -/
@[simp]
lemma mapι_f_zero : (mapι G I).f 0 = G.map (I.ι.f 0) := by
  simp [mapι, CochainComplex.fromSingle₀Equiv]

/-- `G` applied to a descent of `g` between resolutions commutes with the degree-zero
augmentations `mapι`. -/
private theorem mapι_f_zero_comp_map_desc {C' D' : Type*} [Category* C'] [Category* D']
    [Abelian C'] [Abelian D'] (F : C' ⥤ D') [F.Additive] {X Y : C'} (IX : InjectiveResolution X)
    (IY : InjectiveResolution Y) (g : X ⟶ Y) (φ : IX.cocomplex ⟶ IY.cocomplex)
    (comm : IX.ι.f 0 ≫ φ.f 0 = g ≫ IY.ι.f 0) :
    (mapι F IX).f 0 ≫ ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ).f 0 =
      F.map g ≫ (mapι F IY).f 0 := by
  rw [mapι_f_zero, mapι_f_zero, Functor.mapHomologicalComplex_map_f]
  exact (F.map_comp _ _).symm.trans ((congrArg F.map comm).trans (F.map_comp _ _))

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- The map on degree-zero cycles induced by the augmentation of `mapCocomplex G I` is the
canonical map to the zeroth right derived functor of `G`, up to the identification of the
cycles of a single complex. -/
lemma cyclesMap_mapι_zero :
    HomologicalComplex.cyclesMap (mapι G I) 0 =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (G.obj A)).hom ≫
        I.toRightDerivedZero' G := by
  apply (cancel_mono ((mapCocomplex G I).iCycles 0)).1
  simp only [HomologicalComplex.cyclesMap_i,
    HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
  show _ = _ ≫ _ ≫ I.toRightDerivedZero' G ≫ (mapCocomplex G I).iCycles 0
  rw [I.toRightDerivedZero'_comp_iCycles G]
  simp [mapι, CochainComplex.fromSingle₀Equiv, HomologicalComplex.singleObjXSelf]

variable [PreservesFiniteLimits G]
  (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))

omit [HasInjectiveResolutions D] in
include hA in
/-- For a `G`-acyclic object, the augmentation of `mapCocomplex G I` is a quasi-isomorphism:
left exactness of `G` gives exactness in degree zero and acyclicity gives it in the positive
degrees. -/
lemma quasiIso_mapι : QuasiIso (mapι G I) := by
  rw [quasiIso_iff]
  intro q
  cases q with
  | zero =>
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : IsIso (HomologicalComplex.cyclesMap (mapι G I) 0) := by
      rw [cyclesMap_mapι_zero]; infer_instance
    exact IsIso.of_isIso_fac_left (HomologicalComplex.homologyπ_naturality (mapι G I) 0)
  | succ q =>
    rw [quasiIsoAt_iff_exactAt (mapι G I) (q + 1)
      (CochainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hA (q + 1) (Nat.succ_pos q)).of_iso (I.isoRightDerivedObj G (q + 1)).symm

variable [G.PreservesInjectiveObjects]

/-- If `G` is additive, left exact and preserves injective objects, and if `A` is `G`-acyclic,
then `G` applied degreewise to an injective resolution of `A` is an injective resolution of
`G.obj A`. -/
@[simps! cocomplex]
noncomputable def mapOfAcyclic : InjectiveResolution (G.obj A) where
  cocomplex := mapCocomplex G I
  injective q := G.injective_obj (I.cocomplex.X q)
  ι := mapι G I
  quasiIso := quasiIso_mapι G I hA

omit [HasInjectiveResolutions D] in
/-- The degree-zero component of the augmentation of the resolution `mapOfAcyclic G I hA` is `G`
applied to the degree-zero component of the augmentation of `I`. -/
@[simp]
lemma mapOfAcyclic_ι_f_zero : (mapOfAcyclic G I hA).ι.f 0 = G.map (I.ι.f 0) :=
  mapι_f_zero G I

variable (T : D ⥤ E) [T.Additive] (n : ℕ)

/-- The collapse isomorphism `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G.obj A)` at a `G`-acyclic object `A`:
both sides are the `n`-th homology of `T` applied to `G` applied to an injective resolution
of `A`. -/
noncomputable def objIso :
    ((G ⋙ T).rightDerived n).obj A ≅ (T.rightDerived n).obj (G.obj A) :=
  I.isoRightDerivedObj (G ⋙ T) n ≪≫ ((mapOfAcyclic G I hA).isoRightDerivedObj T n).symm

/-- The forward map of the collapse isomorphism is the comparison isomorphism of `I` for `G ⋙ T`
followed by the inverse of the comparison isomorphism of `mapOfAcyclic G I hA` for `T`. -/
lemma objIso_hom :
    (objIso G I hA T n).hom =
      (I.isoRightDerivedObj (G ⋙ T) n).hom ≫
        ((mapOfAcyclic G I hA).isoRightDerivedObj T n).inv :=
  rfl

/-- The collapse isomorphism is computed by any comparison `φ` of `G` applied to the resolution
with an injective resolution `J` of `G.obj A` which preserves the augmentation. Together with
the naturality of `InjectiveResolution.isoRightDerivedObj` this pins the isomorphism down
independently of every choice. -/
lemma objIso_hom_eq (J : InjectiveResolution (G.obj A))
    (φ : mapCocomplex G I ⟶ J.cocomplex)
    (hφ : G.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (objIso G I hA T n).hom =
      (I.isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (J.isoRightDerivedObj T n).inv := by
  have h := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 (G.obj A)) (mapOfAcyclic G I hA) J φ
    (by rw [mapOfAcyclic_ι_f_zero]; exact hφ.trans (Category.id_comp _).symm) T n
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have e : ((mapOfAcyclic G I hA).isoRightDerivedObj T n).inv ≫
      (J.isoRightDerivedObj T n).hom =
      HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n := by
    rw [h]
    exact Iso.inv_hom_id_assoc _ _
  have key : ((mapOfAcyclic G I hA).isoRightDerivedObj T n).inv =
      HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n ≫
        (J.isoRightDerivedObj T n).inv :=
    (Iso.eq_comp_inv _).mpr e
  exact (objIso_hom G I hA T n).trans
    (congrArg ((I.isoRightDerivedObj (G ⋙ T) n).hom ≫ ·) key)

/-- In degree zero the collapse isomorphism intertwines the canonical map from `G ⋙ T` to its
zeroth right derived functor with the canonical map from `T` to its own. -/
lemma toRightDerivedZero_comp_objIso_hom :
    (G ⋙ T).toRightDerivedZero.app A ≫ (objIso G I hA T 0).hom =
      T.toRightDerivedZero.app (G.obj A) := by
  have hz : (mapOfAcyclic G I hA).toRightDerivedZero' T =
      I.toRightDerivedZero' (G ⋙ T) := by
    apply (cancel_mono
      (((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj (mapCocomplex G I)).iCycles 0)).1
    exact (((mapOfAcyclic G I hA).toRightDerivedZero'_comp_iCycles T).trans
      (congrArg T.map (mapOfAcyclic_ι_f_zero G I hA))).trans
      (I.toRightDerivedZero'_comp_iCycles (G ⋙ T)).symm
  have inner : (I.isoRightDerivedObj (G ⋙ T) 0).inv ≫ (objIso G I hA T 0).hom =
      ((mapOfAcyclic G I hA).isoRightDerivedObj T 0).inv := by
    rw [objIso_hom]
    exact Iso.inv_hom_id_assoc _ _
  have mid : (I.toRightDerivedZero' (G ⋙ T) ≫
        (CochainComplex.isoHomologyπ₀ (mapCocomplex (G ⋙ T) I)).hom ≫
          (I.isoRightDerivedObj (G ⋙ T) 0).inv) ≫ (objIso G I hA T 0).hom =
      I.toRightDerivedZero' (G ⋙ T) ≫
        (CochainComplex.isoHomologyπ₀ (mapCocomplex (G ⋙ T) I)).hom ≫
          ((mapOfAcyclic G I hA).isoRightDerivedObj T 0).inv :=
    (Category.assoc _ _ _).trans
      ((congrArg (I.toRightDerivedZero' (G ⋙ T) ≫ ·) (Category.assoc _ _ _)).trans
        (congrArg (fun x => I.toRightDerivedZero' (G ⋙ T) ≫
          (CochainComplex.isoHomologyπ₀ (mapCocomplex (G ⋙ T) I)).hom ≫ x) inner))
  exact ((congrArg (· ≫ (objIso G I hA T 0).hom) (I.toRightDerivedZero_eq (G ⋙ T))).trans
    mid).trans
      ((congrArg (· ≫ (CochainComplex.isoHomologyπ₀ (mapCocomplex (G ⋙ T) I)).hom ≫
        ((mapOfAcyclic G I hA).isoRightDerivedObj T 0).inv) hz.symm).trans
        ((mapOfAcyclic G I hA).toRightDerivedZero_eq T).symm)

end Pointwise

section Naturality

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [G.PreservesInjectiveObjects]
  (T : D ⥤ E) [T.Additive] (n : ℕ)

/-- The `G`-acyclic objects: those whose positive right derived functors under `G` vanish. -/
def acyclic : ObjectProperty C :=
  fun A => ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A)

/-- The collapse isomorphism is natural: a descent `φ` of `g` to chosen injective resolutions
computes the derived functor of the composite upstairs and, after applying `G`, the derived
functor of `T` downstairs. -/
lemma objIso_hom_naturality_of_desc {A B : C} (IA : InjectiveResolution A)
    (IB : InjectiveResolution B)
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hB : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj B)) (g : A ⟶ B)
    (φ : IA.cocomplex ⟶ IB.cocomplex) (comm : IA.ι.f 0 ≫ φ.f 0 = g ≫ IB.ι.f 0) :
    ((G ⋙ T).rightDerived n).map g ≫ (objIso G IB hB T n).hom =
      (objIso G IA hA T n).hom ≫ (T.rightDerived n).map (G.map g) := by
  have nat1 := InjectiveResolution.isoRightDerivedObj_hom_naturality g IA IB φ comm (G ⋙ T) n
  have nat2 := InjectiveResolution.isoRightDerivedObj_inv_naturality (G.map g)
    (mapOfAcyclic G IA hA) (mapOfAcyclic G IB hB)
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)
    (mapι_f_zero_comp_map_desc G IA IB g φ comm) T n
  exact ((congrArg (((G ⋙ T).rightDerived n).map g ≫ ·) (objIso_hom G IB hB T n)).trans
    (Category.assoc _ _ _).symm).trans
      ((congrArg (· ≫ ((mapOfAcyclic G IB hB).isoRightDerivedObj T n).inv) nat1).trans
        (((Category.assoc _ _ _).trans
            (congrArg ((IA.isoRightDerivedObj (G ⋙ T) n).hom ≫ ·) nat2.symm)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ (T.rightDerived n).map (G.map g))
              (objIso_hom G IA hA T n).symm))))

/-- The collapse isomorphism built from the chosen injective resolutions is natural in a
morphism `g : A ⟶ B` between `G`-acyclic objects. -/
lemma objIso_hom_naturality {A B : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hB : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj B)) (g : A ⟶ B) :
    ((G ⋙ T).rightDerived n).map g ≫
        (objIso G (injectiveResolution B) hB T n).hom =
      (objIso G (injectiveResolution A) hA T n).hom ≫
        (T.rightDerived n).map (G.map g) :=
  objIso_hom_naturality_of_desc G T n _ _ hA hB g
    (InjectiveResolution.desc g (injectiveResolution B) (injectiveResolution A))
    (InjectiveResolution.desc_commutes_zero g _ _)

/-- The collapse isomorphism, as a natural isomorphism on the full subcategory of `G`-acyclic
objects: `R ⁿ (G ⋙ T) ≅ G ⋙ R ⁿ T` there. -/
noncomputable def natIso :
    (acyclic G).ι ⋙ (G ⋙ T).rightDerived n ≅
      (acyclic G).ι ⋙ G ⋙ T.rightDerived n :=
  NatIso.ofComponents
    (fun A => objIso G (injectiveResolution A.obj) A.property T n)
    fun {A B} g => objIso_hom_naturality G T n A.property B.property g.hom

/-- The component of `natIso G T n` at a `G`-acyclic object `A` is the collapse isomorphism
`objIso` built from the chosen injective resolution of `A`. -/
@[simp]
lemma natIso_hom_app (A : (acyclic G).FullSubcategory) :
    (natIso G T n).hom.app A = (objIso G (injectiveResolution A.obj) A.property T n).hom :=
  rfl

end Naturality

/-! ### An acyclic resolution computes the right derived functor -/

section AcyclicResolution

-- `CategoryTheory.Functor.rightAcyclic` mentions `HasRightDerivedFunctor`, and instance search
-- for it would otherwise try to prove termwise injectivity of an unknown complex; the cheap
-- instance coming from `EnoughInjectives` is therefore given precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe w w'

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
  [EnoughInjectives D] (T : D ⥤ E) [T.Additive]

/-- The higher right derived functors of an additive functor vanish on an injective object.
This is `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` with the degree given as
a positive natural number rather than as a successor. -/
lemma isZero_rightDerived_obj_of_injective (Z : D) [Injective Z] (n : ℕ) (hn : 0 < n) :
    IsZero ((T.rightDerived n).obj Z) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact T.isZero_rightDerived_obj_injective_succ m Z

/-- An injective object is `T`-acyclic. -/
lemma acyclic_of_injective (Z : D) [Injective Z] : acyclic T Z :=
  isZero_rightDerived_obj_of_injective T Z

/-- Every object of `D` admits a monomorphism into a `T`-acyclic object, namely into an
injective one. This is the first of the two conditions of [Stacks, Tag 05T8]. -/
lemma exists_mono_acyclic (A : D) : ∃ (B : D) (_ : acyclic T B) (i : A ⟶ B), Mono i :=
  ⟨Injective.under A, acyclic_of_injective T _, Injective.ι A, inferInstance⟩

variable [PreservesFiniteLimits T]

/-- **Right acyclicity, in Mathlib's `ℕ`-indexing.** For a left exact functor `T`, an object is
right acyclic for `T` in the sense of [Stacks, Tag 0157] — the complex `A[0]` computes `RT` —
if and only if the higher right derived functors `R ⁿ T` of [Stacks, Tag 05TB] vanish on it.

This is part (2) of [Stacks, Tag 015C], whose statement in this repository is phrased with the
`ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`, read through the comparison of the two
indexings. It is the form a consumer holding a vanishing statement needs in order to use the
results that are stated with `CategoryTheory.Functor.rightAcyclic`. -/
lemma rightAcyclic_iff_acyclic [HasDerivedCategory.{w} D] [HasDerivedCategory.{w'} E]
    (A : D) : T.rightAcyclic A ↔ acyclic T A := by
  rw [(Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus T A).2 inferInstance]
  refine ⟨fun h n hn => ?_, fun h i hi => ?_⟩
  · exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff T n A).2
      (h n (by exact_mod_cast hn))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff T n A).1
      (h n (by exact_mod_cast hi))

/-- **Two out of three `T`-acyclic objects in a short exact sequence force the third**, and the
sequence stays short exact under `T`. This is part (2) of [Stacks, Tag 015D] in Mathlib's
`ℕ`-indexing, and it is the second of the two conditions of [Stacks, Tag 05T8]. -/
lemma acyclic_shortExact (S : ShortComplex D) (hS : S.ShortExact)
    (h₁ : acyclic T S.X₁) (h₂ : acyclic T S.X₂) :
    acyclic T S.X₃ ∧ (S.map T).ShortExact := by
  let _ := HasDerivedCategory.standard D
  let _ := HasDerivedCategory.standard E
  obtain ⟨h₃, hse⟩ := (Functor.rightAcyclic_and_shortExact_map_of_shortExact T S hS).2.1
    ((rightAcyclic_iff_acyclic T S.X₁).2 h₁) ((rightAcyclic_iff_acyclic T S.X₂).2 h₂)
  exact ⟨(rightAcyclic_iff_acyclic T S.X₃).1 h₃, hse⟩

variable {X : D} {K : CochainComplex D ℕ}

/-- The chosen comparison of a resolution of `X` with the resolving complex of an injective
resolution of `X`. It exists by `CategoryTheory.InjectiveResolution.exists_desc_of_quasiIso`,
which needs only that the source be a resolution — its terms are arbitrary — and it is unique up
to homotopy, so nothing below depends on the choice. -/
@[ega "0 11.5.2.2" "partial", ega "0 12.1.4"]
noncomputable def descOfResolution (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε]
    (J : InjectiveResolution X) : K ⟶ J.cocomplex :=
  (InjectiveResolution.exists_desc_of_quasiIso (𝟙 X) J ε).choose

omit [EnoughInjectives D] [T.Additive] [PreservesFiniteLimits T] in
/-- `descOfResolution` preserves the augmentation. -/
lemma comp_descOfResolution (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε]
    (J : InjectiveResolution X) : ε ≫ descOfResolution (D := D) ε J = J.ι := by
  have h := (InjectiveResolution.exists_desc_of_quasiIso (𝟙 X) J ε).choose_spec
  rw [descOfResolution]
  simpa using h

/-- **An acyclic resolution computes the right derived functor, along a given comparison.** Let
`T` be additive and left exact on an abelian category with enough injectives, let
`ε : X[0] ⟶ K` be a quasi-isomorphism onto a cochain complex whose terms are `T`-acyclic — a
resolution of `X` by `T`-acyclic objects, injective or not — and let `β` be any comparison of
`K` with the resolving complex of an injective resolution `J` of `X` preserving the
augmentation. Then `R ⁿ T (X)` is the degree-`n` cohomology of `T` applied to `K`.

This is the specialization to the `T`-acyclic objects of the computation of `R ⁿ T` on a
resolution by a class adapted to `T`, [Stacks, Tag 05T8]; what makes the specialization legal is
that the `T`-acyclic objects are such a class, by `exists_mono_acyclic` and
`acyclic_shortExact`. It is the content of Leray's acyclicity lemma [Stacks, Tag 015E] at a
single object, in Mathlib's `ℕ`-indexing. -/
@[ega "0 11.5.2.4", sga "4 V 0.4" "partial"]
noncomputable def isoRightDerivedObjOfAcyclicOfDesc (J : InjectiveResolution X)
    (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε] (β : K ⟶ J.cocomplex)
    (hβ : ε ≫ β = J.ι) (hK : ∀ q, acyclic T (K.X q)) (n : ℕ) :
    (T.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).obj
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  InjectiveResolution.isoRightDerivedObjOfQuasiIso T (acyclic T) (exists_mono_acyclic T)
    (fun S hS h₁ h₂ => acyclic_shortExact T S hS h₁ h₂) J ε β hβ hK
    (fun q => have := J.injective q; acyclic_of_injective T _) n

/-- **An acyclic resolution computes the right derived functor.** If `ε : X[0] ⟶ K` is a
quasi-isomorphism onto a cochain complex all of whose terms are `T`-acyclic, then
`R ⁿ T (X) ≅ H ⁿ (T (K))`.

No term of `K` is required to be injective; this is what replaces the injectivity of the
resolution in `Stacks.RightDerivedComp.mapOfAcyclic`, and hence what lets the collapse
isomorphism `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)` be had from `G` carrying injective objects to
`T`-acyclic ones instead of to injective ones. The comparison used is the chosen one; see
`isoRightDerivedObjOfAcyclicOfDesc` for the form with the comparison supplied, from which it
follows that the identification does not depend on that choice. -/
@[ega "0 11.5.2.4", sga "4 V 0.4" "partial"]
noncomputable def isoRightDerivedObjOfAcyclic (ε : (CochainComplex.single₀ D).obj X ⟶ K)
    [QuasiIso ε] (hK : ∀ q, acyclic T (K.X q)) (n : ℕ) :
    (T.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).obj
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  isoRightDerivedObjOfAcyclicOfDesc T (injectiveResolution X) ε
    (descOfResolution ε (injectiveResolution X))
    (comp_descOfResolution ε (injectiveResolution X)) hK n

/-- The higher right derived functors vanish on an object admitting a resolution by `T`-acyclic
objects which `T` carries to an exact complex in the positive degrees: the computation of
`R ⁿ T` on that resolution transports the vanishing. -/
lemma isZero_rightDerived_obj_of_exactAt (ε : (CochainComplex.single₀ D).obj X ⟶ K) [QuasiIso ε]
    (hK : ∀ q, acyclic T (K.X q)) (n : ℕ)
    (hn : ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt n) :
    IsZero ((T.rightDerived n).obj X) :=
  ((HomologicalComplex.exactAt_iff_isZero_homology _ n).1 hn).of_iso
    (isoRightDerivedObjOfAcyclic T ε hK n)

end AcyclicResolution

section CollapseOfAcyclicImage

/-- **The collapse isomorphism `R ⁿ (G ⋙ T) (A) ≅ R ⁿ T (G A)` from acyclicity of the images
of injectives.** For a `G`-acyclic object `A`, where `G` is required only to carry injective
objects to `T`-acyclic ones rather than to injective ones.

This is `Stacks.RightDerivedComp.objIso` with `[G.PreservesInjectiveObjects]` replaced by the
hypothesis `hGT`, which is what the implementation notes of this file and the docstring of
`Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic` describe as the point of the acyclic
half: an acyclic resolution computes `R ⁿ T` just as well as an injective one, so the image of
an injective resolution of `A` under `G` need only be acyclic termwise.

Both categories' universes are independent of one another throughout, as are the object and
morphism universes of each; in particular this applies to a site whose objects live in a
universe above its morphisms, which `Stacks.Cohomology.Leray` cannot reach because it is
stated for a `RingedTopos` with all three universes equal. -/
noncomputable def objIsoOfAcyclicImage {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    [EnoughInjectives D] (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E)
    [T.Additive] [PreservesFiniteLimits T] {A : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z)) (n : ℕ) :
    ((G ⋙ T).rightDerived n).obj A ≅ (T.rightDerived n).obj (G.obj A) :=
  have _ : QuasiIso (mapι G (injectiveResolution A)) :=
    quasiIso_mapι G (injectiveResolution A) hA
  (injectiveResolution A).isoRightDerivedObj (G ⋙ T) n ≪≫
    (isoRightDerivedObjOfAcyclic T (mapι G (injectiveResolution A))
      (fun q => hGT _ ((injectiveResolution A).injective q)) n).symm

/-- `mapι` is natural: the image under `G` of a descent of `e : A ⟶ A'` between injective
resolutions is compatible with the augmentations. -/
lemma mapι_naturality {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (G : C ⥤ D) [G.Additive] {A A' : C} (e : A ⟶ A') (I : InjectiveResolution A)
    (I' : InjectiveResolution A') :
    mapι G I ≫ (G.mapHomologicalComplex (ComplexShape.up ℕ)).map (I'.desc e I) =
      (CochainComplex.single₀ D).map (G.map e) ≫ mapι G I' := by
  apply HomologicalComplex.from_single_hom_ext
  simpa using mapι_f_zero_comp_map_desc G I I' e (I'.desc e I)
    (InjectiveResolution.desc_commutes_zero e I' I)

/-- The collapse isomorphism, unfolded: the identification of `R ⁿ (G ⋙ T) (A)` with the
cohomology of `T (G I)` for an injective resolution `I` of `A`, followed by the comparison with an
injective resolution of `G A`. -/
lemma objIsoOfAcyclicImage_hom {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    [EnoughInjectives D] (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E)
    [T.Additive] [PreservesFiniteLimits T] {A : C}
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z)) (n : ℕ) :
    haveI := quasiIso_mapι G (injectiveResolution A) hA
    (objIsoOfAcyclicImage G T hA hGT n).hom =
      ((injectiveResolution A).isoRightDerivedObj (G ⋙ T) n).hom ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (descOfResolution (mapι G (injectiveResolution A)) (injectiveResolution (G.obj A)))) n ≫
        ((injectiveResolution (G.obj A)).isoRightDerivedObj T n).inv :=
  rfl

/-- **The collapse isomorphism is natural** in the `G`-acyclic object. -/
lemma objIsoOfAcyclicImage_hom_naturality {C D E : Type*} [Category* C] [Category* D]
    [Category* E] [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    [EnoughInjectives D] (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] (T : D ⥤ E)
    [T.Additive] [PreservesFiniteLimits T] {A A' : C} (e : A ⟶ A')
    (hA : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A))
    (hA' : ∀ n, 0 < n → IsZero ((G.rightDerived n).obj A'))
    (hGT : ∀ Z : C, Injective Z → acyclic T (G.obj Z)) (n : ℕ) :
    ((G ⋙ T).rightDerived n).map e ≫ (objIsoOfAcyclicImage G T hA' hGT n).hom =
      (objIsoOfAcyclicImage G T hA hGT n).hom ≫ (T.rightDerived n).map (G.map e) := by
  have := quasiIso_mapι G (injectiveResolution A) hA
  have := quasiIso_mapι G (injectiveResolution A') hA'
  set I := injectiveResolution A
  set I' := injectiveResolution A'
  set J := injectiveResolution (G.obj A)
  set J' := injectiveResolution (G.obj A')
  set φ := I'.desc e I
  set ψ := J'.desc (G.map e) J
  set β := descOfResolution (mapι G I) J
  set β' := descOfResolution (mapι G I') J'
  have hβ : mapι G I ≫ β = J.ι := comp_descOfResolution (mapι G I) J
  have hβ' : mapι G I' ≫ β' = J'.ι := comp_descOfResolution (mapι G I') J'
  have hh : Nonempty (Homotopy ((G.mapHomologicalComplex _).map φ ≫ β') (β ≫ ψ)) := by
    refine InjectiveResolution.nonempty_descHomotopy_of_quasiIso J' (mapι G I) ?_
    rw [← Category.assoc, mapι_naturality, Category.assoc, hβ', ← Category.assoc, hβ,
      InjectiveResolution.desc_commutes]
  have hH := (T.mapHomotopy hh.some).homologyMap_eq n
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hH
  have h2 := InjectiveResolution.isoRightDerivedObj_inv_naturality (G.map e) J J' ψ
    (InjectiveResolution.desc_commutes_zero (G.map e) J' J) T n
  have key : HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) n ≫
        HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map β') n ≫
          (J'.isoRightDerivedObj T n).inv =
      HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map β) n ≫
        (J.isoRightDerivedObj T n).inv ≫ (T.rightDerived n).map (G.map e) := by
    have h1 := congrArg (· ≫ (J'.isoRightDerivedObj T n).inv) hH
    exact (Category.assoc _ _ _).symm.trans (h1.trans ((Category.assoc _ _ _).trans
      (congrArg (HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℕ)).map β) n ≫ ·) h2).symm))
  rw [objIsoOfAcyclicImage_hom, objIsoOfAcyclicImage_hom,
    InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc e I I' φ
      (InjectiveResolution.desc_commutes_zero e I' I) (G ⋙ T) n]
  exact (congrArg ((I.isoRightDerivedObj (G ⋙ T) n).hom ≫ ·)
    (key.trans (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm

end CollapseOfAcyclicImage

end Stacks.RightDerivedComp
