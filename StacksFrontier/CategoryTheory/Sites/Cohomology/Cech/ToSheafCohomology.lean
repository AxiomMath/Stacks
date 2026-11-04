module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RightDerivedByInjectiveResolutions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DegreeZeroAndSheafCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAsBoundedBelowFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
import StacksCore.Tactic.StacksAttribute

/-! # The map from Čech cohomology to sheaf cohomology

Let `C` be a site, let `U` be an object of `C` and let `E = {U_i → U}` be a covering family of
`U`. Stacks 03AX produces a transformation

`Č(E, -) ⟶ RΓ(U, -)`

of functors from abelian sheaves on `C` to the bounded-below derived category of abelian groups,
and hence transformations `Ȟ^p(E, F) → H^p(U, F)` from Čech cohomology to sheaf cohomology in
every degree.

The construction is the one in the source. For an abelian sheaf `F` and an injective resolution
`F → J^•`, form the double complex `Č(E, J^•)` and its total complex. There are two maps into the
total complex: the augmentation `α : Γ(U, J^•) → Tot(Č(E, J^•))`, which restricts sections of
`J^q` to the degree-zero Čech term, and the map `β : Č(E, F) → Tot(Č(E, J^•))` induced by
`F → J^0`. The map `α` is a quasi-isomorphism by the criterion of Stacks 0133
(`quasiIso_total_of_resolution`): its columns are the Čech complexes of the injective sheaves
`J^q`, which by Stacks 03AW are resolutions of `Γ(U, J^q)` — the sheaf condition for the covering
family gives degree zero and `Stacks.CechSite.injective_sheaf_cechCohomology_isZero` gives the
positive degrees. The comparison is `β` followed by the inverse of `α` in the derived category and
the canonical identification of `Γ(U, J^•)` with `RΓ(U, F)`.

## Main definitions

* `Stacks.CechSite.derivedSectionsFunctor`: the derived sections functor `RΓ(U, -)`.
* `Stacks.CechSite.cechDerivedFunctor`: the Čech complex of `E`, as a functor to `D⁺(Ab)`.
* `Stacks.CechSite.cechBicomplex`: the double complex `Č(E, J^•)`.
* `Stacks.CechSite.cechAugmentationInt`: the augmentation `Γ(U, F) → Č^0(E, F)`.
* `Stacks.CechSite.totalAugmentation`, `Stacks.CechSite.cechToTotal`: the two maps `α` and `β`
  into the total complex.
* `Stacks.CechSite.cechComparison`: the comparison morphism built from a given injective
  resolution.
* `Stacks.CechSite.cechToDerivedSections`: **Stacks 03AX**, the transformation
  `Č(E, -) ⟶ RΓ(U, -)`.
* `Stacks.CechSite.cechCohomologyToCohomology`: **Stacks 03AX**, the induced transformation on
  cohomology in a fixed degree.
* `Stacks.CechSite.CechResolutionComparison`: the data pinning the comparison down through an
  injective resolution.

## Main results

* `Stacks.CechSite.nonempty_isLimit_kernelFork_cechAugmentationPre`: the sheaf condition in Čech
  form — for a covering family the augmentation exhibits `Γ(U, F)` as the kernel of the
  degree-zero Čech differential.
* `Stacks.CechSite.exists_quasiIso_total_cechBicomplex`: the augmentation `α` is a
  quasi-isomorphism.
* `Stacks.CechSite.cechComparison_naturality`: the comparison is natural in the sheaf and
  compatible with a morphism of injective resolutions; with the identity morphism this is
  `Stacks.CechSite.cechComparison_eq`, the independence of the chosen resolution.
* `Stacks.CechSite.nonempty_cechResolutionComparison`: **Stacks 03AX**, the characterisation of
  the transformation by the two augmentations, for every injective resolution.

## Implementation notes

A site is a `CategoryTheory.GrothendieckTopology`, and a covering family is a
`PreZeroHypercover` whose generated sieve belongs to the topology. The finite fibre products
needed to form the Čech complex are supplied as product instances in the over category, as in
Stacks 03AM; this form does not require all pullbacks in the underlying category. The Čech
complex is extended by zero from natural to integer degrees before passing to the bounded-below
derived category, and sections are evaluation of the underlying presheaf at the covered object,
which is Mathlib's `CategoryTheory.sheafSections`.

Naturality of the comparison and its independence of the chosen injective resolution are one
statement, `cechComparison_naturality`: a morphism of injective resolutions above `g : F ⟶ F'`
turns the comparisons for the two resolutions into a commutative square with `RΓ(U, g)`. Taking
`g` to be the identity and the morphism of resolutions to be a descent gives independence, and
taking general `g` with resolutions chosen by `CategoryTheory.InjectiveResolution.of` gives
naturality. Its three ingredients are the naturality of the derived-functor comparison
(`CategoryTheory.InjectiveResolution.toRightDerived_naturality`) and the compatibility of `α` and
`β` with a morphism of resolutions.

The augmentation and its degree-zero properties are developed for a *presheaf*, with the sheaf
versions obtained by composing with `CategoryTheory.sheafToPresheaf`; only the identification of
`Γ(U, F)` with the kernel of the degree-zero differential uses that `F` is a sheaf and `E` a
covering.

The coefficient universe contains the object, morphism and covering-index universes. This is the
small-site convention of the source, and for the positive-degree vanishing of the Čech cohomology
of an injective sheaf it is not merely a convention: that statement is proved by presenting the
Čech complex as a `Hom` complex out of the integral Čech complex, whose terms are free abelian
presheaves on morphism sets.

## References

* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

universe a g w v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

section General

variable {C : Type u} [Category.{v} C] {U : C} (E : PreZeroHypercover.{w} U)

/-- The alternating-coface-map complex functor preserves zero morphisms. -/
instance alternatingCofaceMapComplex_preservesZeroMorphisms {A : Type u'} [Category.{v'} A]
    [Preadditive A] : (AlgebraicTopology.alternatingCofaceMapComplex A).PreservesZeroMorphisms where
  map_zero F G := by
    ext n
    simp [AlgebraicTopology.alternatingCofaceMapComplex]
    rfl

/-- Evaluation of a presheaf on formal coproducts preserves zero morphisms. -/
instance evalOp_preservesZeroMorphisms {D : Type u} [Category.{v} D] {A : Type u'}
    [Category.{v'} A] [HasProducts.{w} A] [Preadditive A] :
    (FormalCoproduct.evalOp.{w} D A).PreservesZeroMorphisms where
  map_zero F G := by
    ext X
    apply Pi.hom_ext
    intro i
    simp only [FormalCoproduct.evalOp_map_app, zero_app]
    exact (Pi.map_π (fun _ ↦ 0) i).trans (comp_zero.trans zero_comp.symm)

/-- The Čech complex functor preserves zero morphisms. -/
instance cechComplexFunctor_preservesZeroMorphisms {A : Type u'} [Category.{v'} A]
    [HasProducts.{w} A] [Preadditive A]
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))] :
    (cechComplexFunctor E (A := A)).PreservesZeroMorphisms := by
  dsimp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor,
    FormalCoproduct.cosimplicialObjectFunctor]
  infer_instance

end General

section Sections

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (U : C)
  [HasSheafify K Ab.{g}] [K.WEqualsLocallyBijective Ab.{g}]

/-- Taking sections of abelian sheaves over an object is additive. -/
instance sheafSections_additive :
    ((sheafSections K Ab.{g}).obj (op U)).Additive := by
  change (sheafToPresheaf K Ab.{g} ⋙ (evaluation Cᵒᵖ Ab.{g}).obj (op U)).Additive
  infer_instance

/-- The bounded-below derived sections functor `RΓ(U, -)` of abelian sheaves on a site. -/
def derivedSectionsFunctor [EnoughInjectives (Sheaf K Ab.{g})] :
    Sheaf K Ab.{g} ⥤ DerivedCategory.Plus Ab.{g} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    ((sheafSections K Ab.{g}).obj (op U)).rightDerivedFunctorPlus

end Sections

variable {C : Type u} [Category.{v} C]
  (K : GrothendieckTopology C) {U : C} (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]

/-- The Čech complex of a sheaf, regarded as an object of the bounded-below derived
category. -/
def cechDerivedFunctor :
    Sheaf K Ab.{max a u v w} ⥤ DerivedCategory.Plus Ab.{max a u v w} :=
  sheafToPresheaf K Ab.{max a u v w} ⋙
    cechComplexPlusFunctor E ⋙ DerivedCategory.Plus.Q

/-- The integer-graded Čech complex of an abelian presheaf. -/
@[implicit_reducible]
def cechComplexIntFunctorPre :
    (Cᵒᵖ ⥤ Ab.{max a u v w}) ⥤ CochainComplex Ab.{max a u v w} ℤ :=
  cechComplexFunctor E ⋙ ComplexShape.embeddingUpNat.extendFunctor Ab.{max a u v w}

/-- The integer-graded Čech complex of an abelian sheaf. -/
@[implicit_reducible]
def cechComplexIntFunctor :
    Sheaf K Ab.{max a u v w} ⥤ CochainComplex Ab.{max a u v w} ℤ :=
  sheafToPresheaf K Ab.{max a u v w} ⋙ cechComplexIntFunctorPre.{a} E

/-- The integer-graded Čech complex functor on presheaves preserves zero morphisms. -/
instance cechComplexIntFunctorPre_preservesZeroMorphisms :
    (cechComplexIntFunctorPre.{a} E).PreservesZeroMorphisms := by
  dsimp only [cechComplexIntFunctorPre]
  infer_instance

/-- The integer-graded Čech complex functor preserves zero morphisms. -/
instance cechComplexIntFunctor_preservesZeroMorphisms :
    (cechComplexIntFunctor.{a} K E).PreservesZeroMorphisms := by
  dsimp only [cechComplexIntFunctor]
  infer_instance

/-- The double complex with resolution degree first and Čech degree second. -/
@[implicit_reducible]
def cechBicomplex (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ) :
    HomologicalComplex₂ Ab.{max a u v w} (.up ℤ) (.up ℤ) :=
  ((cechComplexIntFunctor.{a} K E).mapHomologicalComplex (.up ℤ)).obj J

/-- The map of Čech bicomplexes induced by a morphism of complexes of abelian sheaves. -/
@[implicit_reducible]
def cechBicomplexMap {J J' : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ} (ψ : J ⟶ J') :
    cechBicomplex.{a} K E J ⟶ cechBicomplex.{a} K E J' :=
  ((cechComplexIntFunctor.{a} K E).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ

/-- The components of the induced map of Čech bicomplexes. -/
lemma cechBicomplexMap_f {J J' : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ} (ψ : J ⟶ J')
    (q : ℤ) :
    (cechBicomplexMap.{a} K E ψ).f q = (cechComplexIntFunctor.{a} K E).map (ψ.f q) :=
  Functor.mapHomologicalComplex_map_f _ _ _ _

/-- The map of total Čech complexes induced by a morphism of complexes of abelian sheaves. -/
def cechTotalMap {J J' : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ} (ψ : J ⟶ J') :
    (cechBicomplex.{a} K E J).total (ComplexShape.up ℤ) ⟶
      (cechBicomplex.{a} K E J').total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (cechBicomplexMap.{a} K E ψ) (ComplexShape.up ℤ)

/-- Restriction from sections of a presheaf over `U` to the degree-zero Čech term. -/
def cechAugmentationPre (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    F.obj (op U) ⟶ ((cechComplexFunctor E (A := Ab.{max a u v w})).obj F).X 0 :=
  Pi.lift (fun i : Fin 1 → E.I₀ ↦ F.map
    ((Over.forget U).map (Over.mkIdTerminal.from
      (∏ᶜ fun b : Fin 1 ↦ Over.mk (E.f (i b))))).op)

/-- Restriction from sections over `U` to the degree-zero Čech term. -/
def cechAugmentationNat (F : Sheaf K Ab.{max a u v w}) :
    ((sheafSections K Ab.{max a u v w}).obj (op U)).obj F ⟶
      ((cechComplexFunctor E).obj F.obj).X 0 :=
  cechAugmentationPre.{a} E F.obj

/-- The degree-`p` term of the integer-graded Čech complex of a presheaf, for `p` the image of
a natural number `m`, is the degree-`m` term of the natural-number-graded one. -/
def cechIntXIsoPre (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (m : ℕ) (p : ℤ)
    (h : ComplexShape.embeddingUpNat.f m = p) :
    ((cechComplexIntFunctorPre.{a} E).obj F).X p ≅
      ((cechComplexFunctor E (A := Ab.{max a u v w})).obj F).X m :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat h

/-- The degree-zero term of the integer-graded Čech complex of a presheaf is the degree-zero
term of the natural-number-graded one. -/
def cechIntXZeroIsoPre (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    ((cechComplexIntFunctorPre.{a} E).obj F).X 0 ≅
      ((cechComplexFunctor E (A := Ab.{max a u v w})).obj F).X 0 :=
  cechIntXIsoPre.{a} E F 0 0 rfl

/-- The augmentation in the integer-graded Čech complex of a presheaf. -/
def cechAugmentationIntPre (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    F.obj (op U) ⟶ ((cechComplexIntFunctorPre.{a} E).obj F).X 0 :=
  cechAugmentationPre.{a} E F ≫ (cechIntXZeroIsoPre.{a} E F).inv

/-- The augmentation in the integer-graded Čech complex. -/
def cechAugmentationInt (F : Sheaf K Ab.{max a u v w}) :
    ((sheafSections K Ab.{max a u v w}).obj (op U)).obj F ⟶
      ((cechComplexIntFunctor.{a} K E).obj F).X 0 :=
  cechAugmentationIntPre.{a} E F.obj

/-- The components of the augmentation. -/
@[reassoc]
lemma cechAugmentationPre_π (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (k : Fin 1 → E.I₀) :
    cechAugmentationPre.{a} E F ≫ Pi.π (cochainFactor E F 0) k =
      F.map ((Over.forget U).map (Over.mkIdTerminal.from
        (∏ᶜ fun b : Fin 1 ↦ Over.mk (E.f (k b))))).op :=
  Pi.lift_π _ k

/-- The components of the augmentation, on elements. -/
lemma cechAugmentationPre_π_apply (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (k : Fin 1 → E.I₀)
    (s : F.obj (op U)) :
    Pi.π (cochainFactor E F 0) k (cechAugmentationPre.{a} E F s) =
      F.map ((Over.forget U).map (Over.mkIdTerminal.from
        (∏ᶜ fun b : Fin 1 ↦ Over.mk (E.f (k b))))).op s :=
  ConcreteCategory.congr_hom (cechAugmentationPre_π.{a} E F k) s

/-- The augmentation is natural in the presheaf. -/
lemma cechAugmentationPre_naturality {F G : Cᵒᵖ ⥤ Ab.{max a u v w}} (φ : F ⟶ G) :
    cechAugmentationPre.{a} E F ≫
        ((cechComplexFunctor E (A := Ab.{max a u v w})).map φ).f 0 =
      φ.app (op U) ≫ cechAugmentationPre.{a} E G := by
  ext s
  apply (productAddEquiv (cochainFactor E G 0)).injective
  ext k
  change Pi.π (cochainFactor E G 0) k
      (((cechComplexFunctor E (A := Ab.{max a u v w})).map φ).f 0
        (cechAugmentationPre.{a} E F s)) =
    Pi.π (cochainFactor E G 0) k (cechAugmentationPre.{a} E G (φ.app (op U) s))
  rw [cechComplexFunctor_map_f_π_apply.{max a u v w, w, v, u},
    cechAugmentationPre_π_apply.{a, w, v, u}, cechAugmentationPre_π_apply.{a, w, v, u}]
  exact ConcreteCategory.congr_hom (φ.naturality _) s

/-- The integer-graded augmentation is natural in the presheaf. -/
lemma cechAugmentationIntPre_naturality {F G : Cᵒᵖ ⥤ Ab.{max a u v w}} (φ : F ⟶ G) :
    cechAugmentationIntPre.{a} E F ≫ ((cechComplexIntFunctorPre.{a} E).map φ).f 0 =
      φ.app (op U) ≫ cechAugmentationIntPre.{a} E G := by
  have h : ((cechComplexIntFunctorPre.{a} E).map φ).f 0 =
      (cechIntXZeroIsoPre.{a} E F).hom ≫
        ((cechComplexFunctor E (A := Ab.{max a u v w})).map φ).f 0 ≫
        (cechIntXZeroIsoPre.{a} E G).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl
  dsimp only [cechAugmentationIntPre]
  rw [h, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    cechAugmentationPre_naturality.{a, w, v, u}, Category.assoc]

/-- The integer-graded augmentation is natural in the sheaf. -/
lemma cechAugmentationInt_naturality {F G : Sheaf K Ab.{max a u v w}} (φ : F ⟶ G) :
    cechAugmentationInt.{a} K E F ≫ ((cechComplexIntFunctor.{a} K E).map φ).f 0 =
      ((sheafSections K Ab.{max a u v w}).obj (op U)).map φ ≫ cechAugmentationInt.{a} K E G :=
  cechAugmentationIntPre_naturality.{a, w, v, u} E ((sheafToPresheaf K Ab.{max a u v w}).map φ)

attribute [local instance] singletonProjection_isIso

/-- A morphism which is a kernel of `f` induces an isomorphism onto `kernel f`. -/
lemma isIso_kernelLift_of_isLimit {A : Type u'} [Category.{v'} A] [HasZeroMorphisms A]
    {X Y Z : A} (f : Y ⟶ Z) (g : X ⟶ Y) (hgf : g ≫ f = 0) [HasKernel f]
    (hl : IsLimit (KernelFork.ofι g hgf)) : IsIso (kernel.lift f g hgf) := by
  have h : kernel.lift f g hgf =
      (IsLimit.conePointUniqueUpToIso hl (kernelIsKernel f)).hom := by
    apply (cancel_mono (kernel.ι f)).mp
    simp [IsLimit.conePointUniqueUpToIso]
  rw [h]
  infer_instance

/-- The family of sections underlying the augmentation of a section over `U` is the family of
its restrictions to the members of the family `E`. -/
lemma cochainToFamily_cechAugmentationPre (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (s : F.obj (op U)) :
    cochainToFamily E F (cechAugmentationPre.{a} E F s) =
      (cechRestriction E F s : ∀ i, F.obj (op (E.X i))) := by
  funext i
  have hw : ((inv (singletonProjection E i)) ≫
      Over.mkIdTerminal.from (∏ᶜ fun _ : Fin 1 ↦ Over.mk (E.f i))).left = E.f i := by
    simp
  change F.map (inv (singletonProjection E i)).left.op
      (Pi.π (cochainFactor E F 0) (fun _ ↦ i) (cechAugmentationPre.{a} E F s)) =
    F.map (E.f i).op s
  have key : F.map ((Over.forget U).map (Over.mkIdTerminal.from
        (∏ᶜ fun _ : Fin 1 ↦ Over.mk (E.f i)))).op ≫
      F.map (inv (singletonProjection E i)).left.op = F.map (E.f i).op := by
    rw [← F.map_comp, ← op_comp, Over.forget_map, ← Over.comp_left, hw]
  rw [cechAugmentationPre_π_apply.{a, w, v, u}]
  exact ConcreteCategory.congr_hom key s

/-- The augmentation lands in the kernel of the degree-zero Čech differential. -/
lemma cechAugmentationPre_comp_d (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    cechAugmentationPre.{a} E F ≫
      ((cechComplexFunctor E (A := Ab.{max a u v w})).obj F).d 0 1 = 0 := by
  ext s
  change (cechComplex E F).d 0 1 (cechAugmentationPre.{a} E F s) = 0
  rw [← familyToCochain_cochainToFamily E F (cechAugmentationPre.{a} E F s),
    differential_eq_zero_iff, cochainToFamily_cechAugmentationPre.{a, w, v, u}]
  exact (cechRestriction E F s).property

/-- **The sheaf condition in Čech form.** For a covering family, the augmentation exhibits the
sections over the covered object as the kernel of the degree-zero Čech differential. -/
lemma nonempty_isLimit_kernelFork_cechAugmentationPre
    (hE : Sieve.generate E.presieve₀ ∈ K U) (F : Sheaf K Ab.{max a u v w}) :
    Nonempty (IsLimit (KernelFork.ofι (cechAugmentationPre.{a} E F.obj)
      (cechAugmentationPre_comp_d.{a, w, v, u} E F.obj))) := by
  have hbij : Function.Bijective (cechRestriction E F.obj) :=
    cechRestriction_bijective_of_isSheaf K F.obj F.property E hE
  have hinj : Function.Injective (cochainToFamily E F.obj) := by
    intro x y hxy
    rw [← familyToCochain_cochainToFamily E F.obj x,
      ← familyToCochain_cochainToFamily E F.obj y, hxy]
  refine (ShortComplex.exact_and_mono_f_iff_f_is_kernel
    (ShortComplex.mk (cechAugmentationPre.{a} E F.obj)
      (((cechComplexFunctor E (A := Ab.{max a u v w})).obj F.obj).d 0 1)
      (cechAugmentationPre_comp_d.{a, w, v, u} E F.obj))).1 ⟨?_, ?_⟩
  · rw [ShortComplex.ab_exact_iff]
    intro x hx
    have hmatch : PreZeroHypercover.IsMatching
        (F.obj ⋙ forget Ab.{max a u v w}) E (cochainToFamily E F.obj x) := by
      rw [← differential_eq_zero_iff, familyToCochain_cochainToFamily]
      exact hx
    obtain ⟨s, hs⟩ := hbij.2 ⟨cochainToFamily E F.obj x, hmatch⟩
    refine ⟨s, hinj ?_⟩
    rw [cochainToFamily_cechAugmentationPre.{a, w, v, u}]
    exact congrArg Subtype.val hs
  · rw [AddCommGrpCat.mono_iff_injective]
    intro s s' hss
    refine hbij.1 (Subtype.ext ?_)
    rw [← cochainToFamily_cechAugmentationPre.{a, w, v, u},
      ← cochainToFamily_cechAugmentationPre.{a, w, v, u}]
    exact congrArg (cochainToFamily E F.obj) hss


/-- The differential of the integer-graded Čech complex in nonnegative degrees. -/
lemma cechComplexIntFunctorPre_d (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (m : ℕ) (p q : ℤ)
    (hp : ComplexShape.embeddingUpNat.f m = p)
    (hq : ComplexShape.embeddingUpNat.f (m + 1) = q) :
    ((cechComplexIntFunctorPre.{a} E).obj F).d p q =
      (cechIntXIsoPre.{a} E F m p hp).hom ≫
        ((cechComplexFunctor E (A := Ab.{max a u v w})).obj F).d m (m + 1) ≫
        (cechIntXIsoPre.{a} E F (m + 1) q hq).inv :=
  HomologicalComplex.extend_d_eq _ _ hp hq

/-- The integer-graded Čech complex of a presheaf vanishes in negative degrees. -/
lemma isZero_cechComplexIntFunctorPre_X (F : Cᵒᵖ ⥤ Ab.{max a u v w}) (p : ℤ) (hp : p < 0) :
    IsZero (((cechComplexIntFunctorPre.{a} E).obj F).X p) :=
  HomologicalComplex.isZero_extend_X _ _ p (fun i hi => by
    change (i : ℤ) = p at hi
    omega)

/-- The augmentation lands in the kernel of the degree-zero differential of the integer-graded
Čech complex. -/
lemma cechAugmentationIntPre_comp_d (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    cechAugmentationIntPre.{a} E F ≫ ((cechComplexIntFunctorPre.{a} E).obj F).d 0 1 = 0 := by
  rw [cechComplexIntFunctorPre_d.{a, w, v, u} E F 0 0 1 rfl rfl]
  dsimp only [cechAugmentationIntPre, cechIntXZeroIsoPre]
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    cechAugmentationPre_comp_d.{a, w, v, u}, zero_comp]

/-- The short complex of the augmentation and the degree-zero differential, in the
natural-number grading. -/
def augmentationShortComplexNat (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    ShortComplex Ab.{max a u v w} :=
  ShortComplex.mk (cechAugmentationPre.{a} E F)
    (((cechComplexFunctor E (A := Ab.{max a u v w})).obj F).d 0 1)
    (cechAugmentationPre_comp_d.{a, w, v, u} E F)

/-- The short complex of the augmentation and the degree-zero differential, in the integer
grading. -/
def augmentationShortComplexInt (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    ShortComplex Ab.{max a u v w} :=
  ShortComplex.mk (cechAugmentationIntPre.{a} E F)
    (((cechComplexIntFunctorPre.{a} E).obj F).d 0 1)
    (cechAugmentationIntPre_comp_d.{a, w, v, u} E F)

/-- The two short complexes of the augmentation, in the two gradings, agree. -/
def augmentationShortComplexIso (F : Cᵒᵖ ⥤ Ab.{max a u v w}) :
    augmentationShortComplexNat.{a} E F ≅ augmentationShortComplexInt.{a} E F :=
  ShortComplex.isoMk (Iso.refl _) (cechIntXIsoPre.{a} E F 0 0 rfl).symm
    (cechIntXIsoPre.{a} E F 1 1 rfl).symm (by
      dsimp only [augmentationShortComplexNat, augmentationShortComplexInt,
        cechAugmentationIntPre, cechIntXZeroIsoPre, Iso.symm_hom]
      rw [Iso.refl_hom, Category.id_comp]) (by
      dsimp only [augmentationShortComplexNat, augmentationShortComplexInt, Iso.symm_hom]
      rw [cechComplexIntFunctorPre_d.{a, w, v, u} E F 0 0 1 rfl rfl,
        Iso.inv_hom_id_assoc])

/-- **The sheaf condition in Čech form**, in the integer grading: the augmentation exhibits the
sections over the covered object as the kernel of the degree-zero Čech differential. -/
lemma isIso_kernelLift_cechAugmentationIntPre
    (hE : Sieve.generate E.presieve₀ ∈ K U) (F : Sheaf K Ab.{max a u v w}) :
    IsIso (kernel.lift (((cechComplexIntFunctorPre.{a} E).obj F.obj).d 0 1)
      (cechAugmentationIntPre.{a} E F.obj)
      (cechAugmentationIntPre_comp_d.{a, w, v, u} E F.obj)) := by
  obtain ⟨hl⟩ := nonempty_isLimit_kernelFork_cechAugmentationPre.{a, w, v, u} K E hE F
  have h := (ShortComplex.exact_and_mono_f_iff_f_is_kernel
    (augmentationShortComplexNat.{a} E F.obj)).2 ⟨hl⟩
  obtain ⟨hl'⟩ := (ShortComplex.exact_and_mono_f_iff_f_is_kernel
    (augmentationShortComplexInt.{a} E F.obj)).1
      ((ShortComplex.exact_and_mono_f_iff_of_iso
        (augmentationShortComplexIso.{a} E F.obj)).1 h)
  exact isIso_kernelLift_of_isLimit _ _ _ hl'


/-- The Čech complex of an injective abelian sheaf is exact away from degree zero. -/
lemma exactAt_cechComplexIntFunctorPre_of_injective
    [HasSheafify K Ab.{max a u v w}] (I : Sheaf K Ab.{max a u v w}) [Injective I]
    (p : ℤ) (hp : p ≠ 0) :
    ((cechComplexIntFunctorPre.{a} E).obj I.obj).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.ExactAt.of_isZero
      (isZero_cechComplexIntFunctorPre_X.{a, w, v, u} E I.obj p h)
  · exact absurd h hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = p := ⟨p.toNat, by omega⟩
    refine (HomologicalComplex.extend_exactAt_iff
      ((cechComplexFunctor E (A := Ab.{max a u v w})).obj I.obj)
      ComplexShape.embeddingUpNat (j := m) (j' := (m : ℤ)) rfl).2 ?_
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact injective_sheaf_cechCohomology_isZero.{a, w, v, u} E I m (by omega)

section Resolution

variable (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ)

/-- The augmentation, as a map of complexes from the sections of a complex of abelian sheaves
to the zeroth row of the Čech bicomplex. -/
def cechRowZeroAugmentation :
    (((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex (.up ℤ)).obj J ⟶
      rowZero (cechBicomplex.{a} K E J) where
  f q := cechAugmentationInt.{a} K E (J.X q)
  comm' q q' _ := cechAugmentationInt_naturality.{a, w, v, u} K E (J.d q q')

/-- The Čech bicomplex of a bounded-below complex of sheaves has finite diagonals. -/
lemma diagonalFinite_cechBicomplex [J.IsStrictlyGE 0] :
    DiagonalFinite (cechBicomplex.{a} K E J) := by
  intro n
  refine Set.Finite.subset (Set.finite_Icc 0 n) (fun q hq ↦ ?_)
  simp only [Set.mem_ofPred_eq] at hq
  simp only [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hq ((HomologicalComplex.eval Ab.{max a u v w} (ComplexShape.up ℤ) (n - q)).map_isZero
      ((cechComplexIntFunctor.{a} K E).map_isZero
        (J.isZero_of_isStrictlyGE 0 q (by omega))))
  · by_contra h
    exact hq (isZero_cechComplexIntFunctorPre_X.{a, w, v, u} E (J.X q).obj (n - q) (by omega))

/-- **The hypotheses of Stacks 0133** for the Čech bicomplex of a bounded-below complex of
injective abelian sheaves over a covering family. -/
lemma hypotheses_cechBicomplex [HasSheafify K Ab.{max a u v w}]
    (hE : Sieve.generate E.presieve₀ ∈ K U)
    [J.IsStrictlyGE 0] [hJ : ∀ q, Injective (J.X q)] :
    Hypotheses
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J)
      (cechBicomplex.{a} K E J) (cechRowZeroAugmentation.{a} K E J) where
  diagonalFinite := diagonalFinite_cechBicomplex.{a, w, v, u} K E J
  zero_of_neg p q hq := isZero_cechComplexIntFunctorPre_X.{a, w, v, u} E (J.X p).obj q hq
  exactAt_of_ne_zero p q hq :=
    exactAt_cechComplexIntFunctorPre_of_injective.{a, w, v, u} K E (J.X p) q hq
  inducesIsoKernel p := ⟨cechAugmentationIntPre_comp_d.{a, w, v, u} E (J.X p).obj,
    isIso_kernelLift_cechAugmentationIntPre.{a, w, v, u} K E hE (J.X p)⟩

/-- **Stacks 03AX, the quasi-isomorphism.** The sections of a bounded-below complex of
injective abelian sheaves map quasi-isomorphically to the total complex of its Čech
bicomplex, by the degreewise augmentation. -/
lemma exists_quasiIso_total_cechBicomplex [HasSheafify K Ab.{max a u v w}]
    (hE : Sieve.generate E.presieve₀ ∈ K U)
    [J.IsStrictlyGE 0] [∀ q, Injective (J.X q)] :
    ∃ f : (((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J ⟶ (cechBicomplex.{a} K E J).total (ComplexShape.up ℤ),
      (∀ n : ℤ, f.f n = cechAugmentationInt.{a} K E (J.X n) ≫
        (cechBicomplex.{a} K E J).ιTotal (ComplexShape.up ℤ) n 0 n (by simp)) ∧ QuasiIso f := by
  obtain ⟨_, f, hf, hq⟩ := quasiIso_total_of_resolution _ _ _
    (hypotheses_cechBicomplex.{a, w, v, u} K E J hE)
  exact ⟨f, hf, hq⟩

end Resolution


section Comparison

variable [HasSheafify K Ab.{max a u v w}] [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})] (hE : Sieve.generate E.presieve₀ ∈ K U)

/-- The chosen augmentation of the sections of a bounded-below complex of injective abelian
sheaves into the total complex of its Čech bicomplex. -/
def totalAugmentation (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ)
    [J.IsStrictlyGE 0] [∀ q, Injective (J.X q)] :
    (((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J ⟶ (cechBicomplex.{a} K E J).total (ComplexShape.up ℤ) :=
  (exists_quasiIso_total_cechBicomplex.{a, w, v, u} K E J hE).choose

omit [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})] in
/-- The chosen augmentation restricts sections degreewise into the degree-zero column. -/
lemma totalAugmentation_f (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ)
    [J.IsStrictlyGE 0] [∀ q, Injective (J.X q)] (n : ℤ) :
    (totalAugmentation.{a} K E hE J).f n = cechAugmentationInt.{a} K E (J.X n) ≫
      (cechBicomplex.{a} K E J).ιTotal (ComplexShape.up ℤ) n 0 n (by simp) :=
  (exists_quasiIso_total_cechBicomplex.{a, w, v, u} K E J hE).choose_spec.1 n

/-- The chosen augmentation into the total Čech complex is a quasi-isomorphism. -/
instance quasiIso_totalAugmentation (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ)
    [J.IsStrictlyGE 0] [∀ q, Injective (J.X q)] :
    QuasiIso (totalAugmentation.{a} K E hE J) :=
  (exists_quasiIso_total_cechBicomplex.{a, w, v, u} K E J hE).choose_spec.2

/-- The chosen augmentation becomes invertible in the derived category. -/
instance isIso_Q_map_totalAugmentation (J : CochainComplex (Sheaf K Ab.{max a u v w}) ℤ)
    [J.IsStrictlyGE 0] [∀ q, Injective (J.X q)] :
    IsIso (DerivedCategory.Q.map (totalAugmentation.{a} K E hE J)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

variable (F : Sheaf K Ab.{max a u v w})

/-- The Čech complex of a sheaf maps to the total Čech complex of an injective resolution, by
way of the inclusion of the sheaf into the degree-zero term of the resolution. -/
def cechToTotal (J : InjectiveResolution F) :
    (cechComplexIntFunctor.{a} K E).obj F ⟶
      (cechBicomplex.{a} K E J.cochainComplex).total (ComplexShape.up ℤ) where
  f p := ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
    (cechBicomplex.{a} K E J.cochainComplex).ιTotal (ComplexShape.up ℤ) 0 p p (by simp)
  comm' p p' hpp' := by
    obtain rfl : p + 1 = p' := hpp'
    have h : (cechComplexIntFunctor.{a} K E).map J.inclusionZero ≫
        (cechComplexIntFunctor.{a} K E).map (J.cochainComplex.d 0 1) = 0 := by
      rw [← Functor.map_comp, InjectiveResolution.inclusionZero_comp_d, Functor.map_zero]
    have hz : ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
        ((cechBicomplex.{a} K E J.cochainComplex).d 0 (0 + 1)).f p = 0 := by
      rw [show (0 : ℤ) + 1 = 1 from by norm_num]
      have hd : (cechBicomplex.{a} K E J.cochainComplex).d 0 1 =
          (cechComplexIntFunctor.{a} K E).map (J.cochainComplex.d 0 1) :=
        Functor.mapHomologicalComplex_obj_d _ _ _ _ _
      rw [hd, ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ _ 0 p p (by simp),
      Preadditive.comp_add, ← Category.assoc, hz, zero_comp, zero_add,
      Int.negOnePow_zero, one_smul, ← Category.assoc, ← Category.assoc]
    congr 1
    exact ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).comm p (p + 1)

/-- **Stacks 03AX.** The comparison, in the derived category of abelian groups, from the Čech
complex of a covering family to the derived sections over the covered object, computed through
a chosen injective resolution. -/
def cechComparison (J : InjectiveResolution F) :
    DerivedCategory.Q.obj ((cechComplexIntFunctor.{a} K E).obj F) ⟶
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor (Sheaf K Ab.{max a u v w}) 0).obj F)).obj :=
  DerivedCategory.Q.map (cechToTotal.{a} K E F J) ≫
    inv (DerivedCategory.Q.map (totalAugmentation.{a} K E hE J.cochainComplex)) ≫
    J.toRightDerived ((sheafSections K Ab.{max a u v w}).obj (op U))


variable {F}

omit [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})] in
/-- The chosen total augmentations are compatible with a morphism of injective resolutions. -/
lemma totalAugmentation_naturality {F F' : Sheaf K Ab.{max a u v w}} {g : F ⟶ F'}
    {J : InjectiveResolution F} {J' : InjectiveResolution F'}
    (φ : InjectiveResolution.Hom J J' g) :
    totalAugmentation.{a} K E hE J.cochainComplex ≫
        cechTotalMap.{a} K E φ.hom' =
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ.hom') ≫
        totalAugmentation.{a} K E hE J'.cochainComplex := by
  refine HomologicalComplex.hom_ext _ _ (fun q ↦ ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    totalAugmentation_f.{a, w, v, u}, totalAugmentation_f.{a, w, v, u}, cechTotalMap,
    Category.assoc, HomologicalComplex₂.ιTotal_map, cechBicomplexMap_f.{a, w, v, u},
    Functor.mapHomologicalComplex_map_f, ← Category.assoc,
    cechAugmentationInt_naturality.{a, w, v, u}, Category.assoc]

omit [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})] in
/-- The maps into the total Čech complex are compatible with a morphism of injective
resolutions. -/
lemma cechToTotal_naturality {F F' : Sheaf K Ab.{max a u v w}} {g : F ⟶ F'}
    {J : InjectiveResolution F} {J' : InjectiveResolution F'}
    (φ : InjectiveResolution.Hom J J' g) :
    cechToTotal.{a} K E F J ≫
        cechTotalMap.{a} K E φ.hom' =
      (cechComplexIntFunctor.{a} K E).map g ≫ cechToTotal.{a} K E F' J' := by
  refine HomologicalComplex.hom_ext _ _ (fun p ↦ ?_)
  have key : ((cechComplexIntFunctor.{a} K E).map J.inclusionZero).f p ≫
      ((cechComplexIntFunctor.{a} K E).map (φ.hom'.f 0)).f p =
      ((cechComplexIntFunctor.{a} K E).map g).f p ≫
      ((cechComplexIntFunctor.{a} K E).map J'.inclusionZero).f p := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← Functor.map_comp,
      ← Functor.map_comp, InjectiveResolution.inclusionZero_comp_hom'_f_zero]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [cechToTotal]
  rw [cechTotalMap, Category.assoc, HomologicalComplex₂.ιTotal_map,
    cechBicomplexMap_f.{a, w, v, u}, ← Category.assoc, key, Category.assoc]

omit [K.WEqualsLocallyBijective Ab.{max a u v w}] in
/-- **Stacks 03AX, functoriality.** The comparison is natural in the sheaf and independent of
the chosen injective resolution: a morphism of injective resolutions above `g` makes the
comparisons into a commutative square with the derived sections of `g`. -/
lemma cechComparison_naturality {F F' : Sheaf K Ab.{max a u v w}} {g : F ⟶ F'}
    {J : InjectiveResolution F} {J' : InjectiveResolution F'}
    (φ : InjectiveResolution.Hom J J' g) :
    cechComparison.{a} K E hE F J ≫
        ((((sheafSections K Ab.{max a u v w}).obj (op U)).rightDerivedFunctorPlus).map
          ((DerivedCategory.Plus.singleFunctor (Sheaf K Ab.{max a u v w}) 0).map g)).hom =
      DerivedCategory.Q.map ((cechComplexIntFunctor.{a} K E).map g) ≫
        cechComparison.{a} K E hE F' J' := by
  have h1 := InjectiveResolution.toRightDerived_naturality
    ((sheafSections K Ab.{max a u v w}).obj (op U)) φ
  have h2 := congrArg DerivedCategory.Q.map (totalAugmentation_naturality.{a, w, v, u} K E hE φ)
  have h3 : inv (DerivedCategory.Q.map (totalAugmentation.{a} K E hE J.cochainComplex)) ≫
      DerivedCategory.Q.map
          ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ.hom') =
      DerivedCategory.Q.map (cechTotalMap.{a} K E φ.hom') ≫
        inv (DerivedCategory.Q.map (totalAugmentation.{a} K E hE J'.cochainComplex)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← Functor.map_comp, h2, Functor.map_comp,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  dsimp only [cechComparison]
  rw [Category.assoc, Category.assoc, ← h1, ← Category.assoc (inv _), h3, Category.assoc,
    ← Category.assoc (DerivedCategory.Q.map _), ← Functor.map_comp,
    cechToTotal_naturality.{a, w, v, u}, Functor.map_comp, Category.assoc]

omit [K.WEqualsLocallyBijective Ab.{max a u v w}] in
/-- The comparison does not depend on the chosen injective resolution. -/
lemma cechComparison_eq (F : Sheaf K Ab.{max a u v w}) (J : InjectiveResolution F) :
    cechComparison.{a} K E hE F (InjectiveResolution.of F) =
      cechComparison.{a} K E hE F J := by
  simpa using cechComparison_naturality.{a, w, v, u} K E hE
    (InjectiveResolution.homOfDesc (𝟙 F) (InjectiveResolution.of F) J)

/-- **Stacks Project, Tag 03AX (derived transformation).** The Čech complex of a covering
family maps naturally to derived sections over the covered object. -/
@[stacks 03AX "the derived transformation"]
def cechToDerivedSections :
    cechDerivedFunctor.{a} K E ⟶ derivedSectionsFunctor.{max a u v w} K U where
  app F := ObjectProperty.homMk
    (cechComparison.{a} K E hE F (InjectiveResolution.of F))
  naturality F F' g := ObjectProperty.hom_ext _
    (cechComparison_naturality.{a, w, v, u} K E hE
      (InjectiveResolution.homOfDesc g (InjectiveResolution.of F)
        (InjectiveResolution.of F'))).symm

/-- **Stacks Project, Tag 03AX (cohomology maps).** Taking homology of the Čech-to-derived
comparison gives maps from Čech cohomology to sheaf cohomology, natural in the sheaf. -/
@[stacks 03AX "the induced cohomology maps"]
def cechCohomologyToCohomology (p : ℤ) :
    (cechDerivedFunctor.{a} K E ⋙
        DerivedCategory.Plus.homologyFunctor Ab.{max a u v w} p) ⟶
      (derivedSectionsFunctor.{max a u v w} K U ⋙
        DerivedCategory.Plus.homologyFunctor Ab.{max a u v w} p) :=
  Functor.whiskerRight (cechToDerivedSections.{a} K E hE) _


/-- The two augmentation maps into the total Čech complex of an injective resolution, and their
identification with the canonical comparison. -/
structure CechResolutionComparison (F : Sheaf K Ab.{max a u v w})
    (J : InjectiveResolution F) where
  /-- The restriction map from sections of the resolution. -/
  α : (((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J.cochainComplex ⟶
    (cechBicomplex.{a} K E J.cochainComplex).total (ComplexShape.up ℤ)
  /-- The map induced by the resolution inclusion. -/
  β : (cechComplexIntFunctor.{a} K E).obj F ⟶
    (cechBicomplex.{a} K E J.cochainComplex).total (ComplexShape.up ℤ)
  /-- The first map restricts sections degreewise. -/
  α_f (q : ℤ) : α.f q = cechAugmentationInt.{a} K E (J.cochainComplex.X q) ≫
    (cechBicomplex.{a} K E J.cochainComplex).ιTotal (ComplexShape.up ℤ) q 0 q (by simp)
  /-- The second map is induced by `F ⟶ J⁰`. -/
  β_f (p : ℤ) : β.f p =
    ((cechComplexIntFunctor.{a} K E).map
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ J.ι'.f 0)).f p ≫
    (cechBicomplex.{a} K E J.cochainComplex).ιTotal (ComplexShape.up ℤ) 0 p p (by simp)
  /-- The augmentation is a quasi-isomorphism. -/
  αIso : DerivedCategory.Q.obj
      ((((sheafSections K Ab.{max a u v w}).obj (op U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J.cochainComplex) ≅
    DerivedCategory.Q.obj
      ((cechBicomplex.{a} K E J.cochainComplex).total (ComplexShape.up ℤ))
  /-- The isomorphism is induced by the prescribed augmentation. -/
  αIso_hom : αIso.hom = DerivedCategory.Q.map α
  /-- The comparison is `β ≫ α⁻¹`, followed by the canonical derived-sections map. -/
  comparison : ((cechToDerivedSections.{a} K E hE).app F).hom =
    DerivedCategory.Q.map β ≫ αIso.inv ≫
      J.toRightDerived ((sheafSections K Ab.{max a u v w}).obj (op U))

omit [K.WEqualsLocallyBijective Ab.{max a u v w}] in
/-- **Stacks Project, Tag 03AX (the injective-resolution specification).** For every injective
resolution, the Čech-to-derived-sections transformation is the map induced by the two canonical
augmentations into the total Čech complex. -/
@[stacks 03AX "the injective-resolution specification"]
theorem nonempty_cechResolutionComparison (F : Sheaf K Ab.{max a u v w})
    (J : InjectiveResolution F) :
    Nonempty (CechResolutionComparison.{a} K E hE F J) :=
  ⟨{ α := totalAugmentation.{a} K E hE J.cochainComplex
     β := cechToTotal.{a} K E F J
     α_f := totalAugmentation_f.{a, w, v, u} K E hE J.cochainComplex
     β_f := fun _ ↦ rfl
     αIso := asIso (DerivedCategory.Q.map (totalAugmentation.{a} K E hE J.cochainComplex))
     αIso_hom := rfl
     comparison := cechComparison_eq.{a, w, v, u} K E hE F J }⟩

end Comparison

end Stacks.CechSite

end
