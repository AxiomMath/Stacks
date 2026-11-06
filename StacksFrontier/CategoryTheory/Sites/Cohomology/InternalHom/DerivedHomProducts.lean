module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexes
import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Derived internal Hom preserves countable products in its covariant variable

Let `(𝒞, 𝒪)` be a ringed site and `K ∈ D(𝒪)`. This file proves that the functor
`R𝑆heafHom_𝒪(K, -) : D(𝒪) ⥤ D(𝒪)`
(`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` evaluated at `K`) preserves the
countable power of an arbitrary object. Together with the additivity and the `𝒪`-linearity of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomAdditive.lean` this is the
last of the three properties of that functor which carry the derived-completeness condition
`T(-, f) = 0` through derived internal Hom, which is [Stacks, Tag 099A].

## Main results

* `AlgebraicGeometry.RingedSite.isIso_homPiComparison` — at the level of complexes, the
  internal Hom complex out of a fixed complex commutes with products in its target.
* `AlgebraicGeometry.RingedSite.preservesLimit_derivedSheafHom` — `R𝑆heafHom_𝒪(K, -)`
  preserves the countable power of every object of `D(𝒪)`.

## Implementation notes

**The shape of the argument.** Everything is reduced to representatives, exactly as in
`DerivedHomAdditive.lean`: the K-injective resolution is used only to produce objects, never as
a functor, because `Stacks.Injectives.kInjectiveResolutionFunctor` is not additive. Write `K`
as the class of a K-flat complex `A` (`AlgebraicGeometry.RingedSite.kFlatModel`) and the object
`L` whose power is taken as the class of a K-injective complex `B`
(`AlgebraicGeometry.RingedSite.kInjectiveModel`). Then:

* the termwise product `∏ B` of countably many copies of `B` is K-injective, and its class is
  the countable power of `L` in `D(𝒪)` ([Stacks, Tag 0BK6], via
  `Stacks.Injectives.KInjectiveProduct.product_repr_derived`);
* `SheafHom(A, ∏ B)` is the termwise product of the complexes `SheafHom(A, B)`, which is the
  content of `AlgebraicGeometry.RingedSite.isIso_homPiComparison`;
* `SheafHom(A, B)` is K-injective by [Stacks, Tag 0A96], `A` being K-flat and `B` K-injective,
  so the class of `SheafHom(A, ∏ B)` is in turn the countable power of the class of
  `SheafHom(A, B)`;
* and on a K-injective target the derived internal Hom is the class of the internal Hom
  complex, by `AlgebraicGeometry.RingedSite.derivedSheafHomComparison` and its naturality.

So the image of a countable-power fan is a countable-power fan, which is the assertion.

**Why the internal Hom complex commutes with products in the target.** The internal Hom complex
is characterised by its sections: `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`
identifies the degree-`n` sections of `SheafHom(A, M)` over an object `U` with the degree-`n`
cochains from `A|_U` to `M|_U`, and `AlgebraicGeometry.RingedSite.homMap` acts on them by
`AlgebraicGeometry.RingedSite.cochainConj`, that is by composition. The comparison morphism is
therefore an isomorphism as soon as, over every `U` and in every degree, composition with the
projections identifies the cochains into `(∏ B)|_U` with families of cochains into `B|_U`; and
that holds because the value groups of a cochain are morphism groups into `((∏ B).X q)|_U`,
which is a product: products of complexes are formed degreewise
(`CategoryTheory.Limits.PreservesLimit` of `HomologicalComplex.eval`) and restriction to a
slice site preserves them, being a right adjoint
(`SheafOfModules.pullbackPushforwardAdjunction`). That a morphism of sheaves of modules which
is bijective on sections is an isomorphism is the reflection of isomorphisms by
`SheafOfModules.forget` followed by `PresheafOfModules.toPresheaf`, and products of sheaves of
modules are computed on sections because `SheafOfModules.evaluation` preserves limits.

**The quantified `HasMapBifunctor` hypothesis.** The K-flat resolution of [Stacks, Tag 06YS] and
Tag 0A96 are stated under a quantified hypothesis that the total complex of the tensor-product
bifunctor exists. It is not carried here:
`AlgebraicGeometry.RingedSite.hasMapBifunctor_sheafTensor` discharges it for every ringed site
at the diagonal universes, so the results below need no instance binders beyond the ringed site
itself — which is what lets them be used at a slice site without any hypothesis on the slice.

## References

* [Stacks Project, Tag 099A](https://stacks.math.columbia.edu/tag/099A)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

/-! ### Generalities on product fans -/

/-- A functor which preserves a product carries a product fan to a product fan. -/
def isLimit_fan_map {C D : Type*} [Category C] [Category D] {J : Type} {Y : J → C}
    (F : C ⥤ D) {t : Fan Y} (ht : IsLimit t) [PreservesLimit (Discrete.functor Y) F] :
    IsLimit (Fan.mk (F.obj t.pt) (fun j => F.map (t.proj j))) :=
  Fan.isLimitMapConeEquiv F Y t (isLimitOfPreserves F ht)

/-- **A product fan of modules is a product of the underlying modules.** The projections of a
product fan in `ModuleCat R` identify its apex with the dependent product of the family, so the
map they induce is bijective. -/
theorem bijective_fan_proj {R : Type u} [Ring R] {J : Type} {Y : J → ModuleCat.{u} R}
    {t : Fan Y} (ht : IsLimit t) :
    Function.Bijective (fun (x : t.pt) (j : J) => t.proj j x) := by
  have hprod : IsLimit (Fan.mk (∏ᶜ Y) (Pi.π Y)) := productIsProduct Y
  let f : t.pt ⟶ ModuleCat.of R (∀ j, Y j) :=
    (ht.conePointUniqueUpToIso hprod).hom ≫ (ModuleCat.piIsoPi Y).hom
  have hf (j : J) :
      f ≫ ModuleCat.ofHom (LinearMap.proj j : (∀ i : J, Y i) →ₗ[R] Y j) = t.proj j := by
    rw [Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype]
    exact ht.conePointUniqueUpToIso_hom_comp hprod ⟨j⟩
  convert ConcreteCategory.bijective_of_isIso f using 1
  funext x j
  exact (ConcreteCategory.congr_hom (hf j) x).symm

/-- If `g` and `g ∘ f` are bijective then so is `f`. -/
theorem bijective_of_comp_bijective {α β γ : Type*} {f : α → β} {g : β → γ}
    (hg : Function.Bijective g) (hgf : Function.Bijective (g ∘ f)) : Function.Bijective f :=
  (hg.of_comp_iff' f).mp hgf

/-- **A product fan transported along isomorphisms of its apex and of its family is again a
product fan.** -/
def isLimit_fan_of_iso {C : Type*} [Category C] {J : Type} {Y Y' : J → C}
    {t : Fan Y} (ht : IsLimit t) (P : C) (e : P ≅ t.pt) (eY : ∀ j, Y j ≅ Y' j)
    (p : ∀ j, P ⟶ Y' j) (hp : ∀ j, p j = e.hom ≫ t.proj j ≫ (eY j).hom) :
    IsLimit (Fan.mk P p) := by
  refine Fan.IsLimit.mk _
    (fun s => Fan.IsLimit.lift ht (fun j => s.proj j ≫ (eY j).inv) ≫ e.inv) ?_ ?_
  · intro s j
    rw [Category.assoc, fan_mk_proj, hp j, Iso.inv_hom_id_assoc,
      Fan.IsLimit.fac_assoc ht (fun j => s.proj j ≫ (eY j).inv) j, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · intro s m hm
    rw [Iso.eq_comp_inv]
    refine Fan.IsLimit.hom_ext ht _ _ fun j => ?_
    rw [Fan.IsLimit.fac ht (fun j => s.proj j ≫ (eY j).inv) j, Category.assoc]
    have hmj : m ≫ e.hom ≫ t.proj j ≫ (eY j).hom = s.proj j := by
      rw [← hp j]
      exact hm j
    rw [← hmj]
    simp

/-- **The localization functor of the derived category preserves products of K-injective
complexes.** This is the limit-cone form of [Stacks, Tag 0BK6]: the termwise product of a family
of K-injective complexes represents the product of the objects they define. -/
def isLimit_fan_Q_pi {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {T : Type} (K : T → CochainComplex A ℤ) [∀ n : ℤ, HasProduct fun t => (K t).X n]
    [HasProduct K] (hK : ∀ t, (K t).IsKInjective) :
    IsLimit (Fan.mk (DerivedCategory.Q.obj (∏ᶜ K))
      (fun t => DerivedCategory.Q.map (Pi.π K t))) := by
  classical
  let c : Fan (fun t => DerivedCategory.Q.obj (K t)) :=
    Fan.mk (DerivedCategory.Q.obj (∏ᶜ K)) (fun t => DerivedCategory.Q.map (Pi.π K t))
  let e (s : Fan (fun t => DerivedCategory.Q.obj (K t))) :=
    DerivedCategory.Q.objObjPreimageIso s.pt
  have hbij (s : Fan (fun t => DerivedCategory.Q.obj (K t))) :=
    Stacks.Injectives.KInjectiveProduct.product_repr_derived K hK
      (DerivedCategory.Q.objPreimage s.pt)
  let lift (s : Fan (fun t => DerivedCategory.Q.obj (K t))) :=
    ((hbij s).surjective (fun t => (e s).hom ≫ s.proj t)).choose
  have fac (s : Fan (fun t => DerivedCategory.Q.obj (K t))) (t : T) :
      lift s ≫ DerivedCategory.Q.map (Pi.π K t) = (e s).hom ≫ s.proj t :=
    congrFun ((hbij s).surjective (fun t => (e s).hom ≫ s.proj t)).choose_spec t
  refine Fan.IsLimit.mk c (fun s => (e s).inv ≫ lift s) (fun s t => ?_) (fun s m hm => ?_)
  · change ((e s).inv ≫ lift s) ≫ DerivedCategory.Q.map (Pi.π K t) = s.proj t
    rw [Category.assoc, fac, Iso.inv_hom_id_assoc]
  · apply (cancel_epi (e s).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    apply (hbij s).injective
    funext t
    change ((e s).hom ≫ m) ≫ DerivedCategory.Q.map (Pi.π K t) =
      lift s ≫ DerivedCategory.Q.map (Pi.π K t)
    rw [Category.assoc, show m ≫ DerivedCategory.Q.map (Pi.π K t) = s.proj t from hm t, fac]

variable (X : RingedSite.{u, u, u})

/-- **The total complex of the tensor product of two complexes of sheaves of modules exists.**
This discharges the quantified hypothesis under which the K-flat resolutions of [Stacks, Tag
06YS] and [Stacks, Tag 0A96] are stated. -/
theorem hasMapBifunctor_sheafTensor
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ) :
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) := by
  let : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  unfold HomologicalComplex.HasMapBifunctor
  infer_instance

attribute [local instance] hasMapBifunctor_sheafTensor

/-- Restriction of sheaves of modules to a slice site preserves products: it is a right adjoint,
extension by zero being its left adjoint. -/
instance preservesLimit_overFunctor (U : X.C) {J : Type}
    (Y : J → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesLimit (Discrete.functor Y)
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) := by
  have : (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).IsRightAdjoint :=
    ⟨_, ⟨SheafOfModules.pullbackPushforwardAdjunction
      (F := Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) : _ ⟶ _)⟩⟩
  infer_instance

/-- A product of complexes is a product in every degree. -/
def isLimit_fan_eval {J : Type}
    (B : J → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [HasProduct B] (q : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ B).X q) (fun j => (Pi.π B j).f q)) :=
  isLimit_fan_map (HomologicalComplex.eval _ _ q) (productIsProduct B)

/-- A product of complexes is a product in every degree after restriction to a slice site. -/
def isLimit_fan_eval_over {J : Type}
    (B : J → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [HasProduct B] (U : X.C) (q : ℤ) :
    IsLimit (Fan.mk (((∏ᶜ B).X q).over U) (fun j => ((Pi.π B j).f q).over U)) :=
  isLimit_fan_map (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (isLimit_fan_eval X B q)

/-- Products of sheaves of modules are computed on sections. -/
def isLimit_fan_sections {J : Type}
    (Y : J → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {t : Fan Y} (ht : IsLimit t) (U : X.C) :
    IsLimit (Fan.mk (t.pt.val.obj (op U)) (fun j => (t.proj j).val.app (op U))) :=
  letI : PreservesLimitsOfShape (Discrete J)
      (SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
    SheafOfModules.evaluationPreservesLimitsOfShape.{u}
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (D := Discrete J) (op U)
  isLimit_fan_map
    (SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) ht

/-- A composite of morphisms of sheaves of modules acts on sections by composition. -/
theorem sections_comp_apply
    {M N P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (φ : M ⟶ N) (ψ : N ⟶ P)
    (V : X.Cᵒᵖ) (y : M.val.obj V) :
    ((φ ≫ ψ).val.app V) y = ψ.val.app V (φ.val.app V y) := rfl

/-! ### The internal Hom complex commutes with products in its target -/

section Pi

variable {J : Type}
  (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (B : J → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  [HasProduct B]
  [HasProduct fun j => (sheafHomComplex X A (B j)).obj]

omit [HasProduct fun j => (sheafHomComplex X A (B j)).obj] in
/-- **Composition with the projections identifies the cochains into a product with families of
cochains.** The value groups of a cochain are morphism groups into a degree of the product
complex restricted to the slice site, and that is a product. -/
theorem bijective_cochainConj_pi (U : X.C) (n : ℤ) :
    Function.Bijective (fun (c : Cochain (restrictComplex X A U) (restrictComplex X (∏ᶜ B) U) n)
      (j : J) => cochainConj X U (𝟙 A) (Pi.π B j) c) := by
  have key (c : Cochain (restrictComplex X A U) (restrictComplex X (∏ᶜ B) U) n) (j : J)
      (p q : ℤ) (hpq : p + n = q) :
      (cochainConj X U (𝟙 A) (Pi.π B j) c).v p q hpq =
        c.v p q hpq ≫ ((Pi.π B j).f q).over U := by
    rw [cochainConj_v, HomologicalComplex.id_f,
      show SheafOfModules.Hom.over (𝟙 (A.X p)) U = 𝟙 ((A.X p).over U) from rfl, Category.id_comp]
  refine ⟨fun c c' h => ?_, fun w => ?_⟩
  · refine Cochain.ext _ _ fun p q hpq => ?_
    refine Fan.IsLimit.hom_ext (isLimit_fan_eval_over X B U q) _ _ fun j => ?_
    simpa only [key, fan_mk_proj] using
      congrArg (fun z : Cochain (restrictComplex X A U) (restrictComplex X (B j) U) n =>
        z.v p q hpq) (congrFun h j)
  · refine ⟨Cochain.mk fun p q hpq =>
      Fan.IsLimit.lift (isLimit_fan_eval_over X B U q) fun j => (w j).v p q hpq, ?_⟩
    funext j
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [key _ j p q hpq, Cochain.mk_v]
    exact Fan.IsLimit.fac (isLimit_fan_eval_over X B U q) _ j

/-- The comparison morphism from the internal Hom complex into a product to the product of the
internal Hom complexes, induced by the projections. -/
def homPiComparison :
    (sheafHomComplex X A (∏ᶜ B)).obj ⟶ ∏ᶜ fun j => (sheafHomComplex X A (B j)).obj :=
  Pi.lift fun j => homMap X (𝟙 A) (Pi.π B j)

/-- The defining property of `AlgebraicGeometry.RingedSite.homPiComparison`. -/
theorem homPiComparison_π (j : J) :
    homPiComparison X A B ≫ Pi.π (fun j => (sheafHomComplex X A (B j)).obj) j =
      homMap X (𝟙 A) (Pi.π B j) := Pi.lift_comp_π _ _

omit [HasProduct fun j => (sheafHomComplex X A (B j)).obj] in
/-- **The induced maps of internal Hom complexes identify the sections of the internal Hom
complex into a product with families of sections.** This is
`AlgebraicGeometry.RingedSite.bijective_cochainConj_pi` read through
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`. -/
theorem bijective_homMap_sections (U : X.C) (n : ℤ) :
    Function.Bijective (fun (s : ((sheafHomComplex X A (∏ᶜ B)).obj.X n).val.obj (op U))
      (j : J) => ((homMap X (𝟙 A) (Pi.π B j)).f n).val.app (op U) s) := by
  have hfac : (fun (s : ((sheafHomComplex X A (∏ᶜ B)).obj.X n).val.obj (op U)) (j : J) =>
      ((homMap X (𝟙 A) (Pi.π B j)).f n).val.app (op U) s) =
      (Equiv.piCongrRight fun j =>
          ((sheafHomComplex X A (B j)).sectionsEquiv U n).symm.toEquiv) ∘
        ((fun c (j : J) => cochainConj X U (𝟙 A) (Pi.π B j) c) ∘
          (sheafHomComplex X A (∏ᶜ B)).sectionsEquiv U n) := rfl
  rw [hfac]
  exact (Equiv.piCongrRight _).bijective.comp
    ((bijective_cochainConj_pi X A B U n).comp
      ((sheafHomComplex X A (∏ᶜ B)).sectionsEquiv U n).bijective)

/-- The comparison morphism is an isomorphism in every degree. -/
theorem isIso_f_homPiComparison (n : ℤ) : IsIso ((homPiComparison X A B).f n) := by
  have hsec : ∀ V : X.Cᵒᵖ, IsIso (((homPiComparison X A B).f n).val.app V) := by
    rintro ⟨U⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    refine bijective_of_comp_bijective
      (f := fun s => ((homPiComparison X A B).f n).val.app (op U) s)
      (g := fun (x : ((∏ᶜ fun j => (sheafHomComplex X A (B j)).obj).X n).val.obj (op U))
        (j : J) => ((Pi.π (fun j => (sheafHomComplex X A (B j)).obj) j).f n).val.app (op U) x)
      (bijective_fan_proj (isLimit_fan_sections X _
        (isLimit_fan_eval X (fun j => (sheafHomComplex X A (B j)).obj) n) U)) ?_
    convert bijective_homMap_sections X A B U n using 1
    funext s j
    simp only [Function.comp_apply]
    rw [← sections_comp_apply X ((homPiComparison X A B).f n)
      ((Pi.π (fun j => (sheafHomComplex X A (B j)).obj) j).f n) (op U) s,
      ← HomologicalComplex.comp_f, homPiComparison_π]
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ hsec

/-- **The internal Hom complex out of a fixed complex commutes with products in its target.**
The comparison morphism induced by the projections is an isomorphism of complexes. -/
theorem isIso_homPiComparison : IsIso (homPiComparison X A B) :=
  haveI := isIso_f_homPiComparison X A B
  HomologicalComplex.Hom.isIso_of_components _

end Pi

/-! ### Derived internal Hom preserves countable powers -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Derived internal Hom out of the class of a K-flat complex preserves the countable power of
the class of a K-injective complex.** -/
theorem preservesLimit_derivedSheafHom_model
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA :
      letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
      Stacks.SheafOfModules.IsKFlat.{u, u, u} X.O A) [B.IsKInjective] :
    PreservesLimit (Discrete.functor fun _ : ℕ => DerivedCategory.Q.obj B)
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))) := by
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  let Bf : ℕ → CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    fun _ => B
  have hB : ∀ j, (Bf j).IsKInjective := fun _ => inferInstance
  have hBpi : (∏ᶜ Bf).IsKInjective :=
    Stacks.Injectives.KInjectiveProduct.product_mathlib_isKInjective Bf hB
  let C : ℕ → CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    fun j => (sheafHomComplex X A (Bf j)).obj
  refine preservesLimit_of_preserves_limit_cone (isLimit_fan_Q_pi Bf hB) ?_
  refine (Fan.isLimitMapConeEquiv
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A)))
    (fun _ : ℕ => DerivedCategory.Q.obj B) _).symm ?_
  have := isIso_homPiComparison X A Bf
  refine isLimit_fan_of_iso (isLimit_fan_Q_pi C
    fun _ => isKInjective_sheafHomComplex_of_isKFlat X A B hA) _
    (derivedSheafHomComparison X A (∏ᶜ Bf) ≪≫
      DerivedCategory.Q.mapIso (asIso (homPiComparison X A Bf)))
    (fun j => (derivedSheafHomComparison X A (Bf j)).symm) _ (fun j => ?_)
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, fan_mk_proj]
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map (homPiComparison X A Bf)),
    ← DerivedCategory.Q.map_comp, homPiComparison_π, ← Category.assoc]
  exact (Iso.eq_comp_inv _).mpr (derivedSheafHomComparison_naturality_id_source X A (Pi.π Bf j))

/-- **Derived internal Hom out of a fixed object preserves countable powers.** For every
`K ∈ D(𝒪)` the functor `R𝑆heafHom_𝒪(K, -)` preserves the product of countably many copies of
any object `L ∈ D(𝒪)`. -/
theorem preservesLimit_derivedSheafHom
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    PreservesLimit (Discrete.functor fun _ : ℕ => L)
      ((derivedSheafHomBifunctor X).obj (op K)) := by
  let := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} X.O
  have hmodel : PreservesLimit
      (Discrete.functor fun _ : ℕ => DerivedCategory.Q.obj (kInjectiveModel X L))
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj (kFlatModel X K)))) := by
    have : (kInjectiveModel X L).IsKInjective := isKInjective_kInjectiveModel X L
    exact preservesLimit_derivedSheafHom_model X (kFlatModel X K) (kInjectiveModel X L)
      (isKFlat_kFlatModel X K)
  have hL : PreservesLimit (Discrete.functor fun _ : ℕ => L)
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj (kFlatModel X K)))) :=
    preservesLimit_of_iso_diagram _
      (Discrete.natIso (F := Discrete.functor fun _ : ℕ =>
        DerivedCategory.Q.obj (kInjectiveModel X L))
        (G := Discrete.functor fun _ : ℕ => L)
        (fun _ => kInjectiveModelIso X L))
  exact preservesLimit_of_natIso _
    ((derivedSheafHomBifunctor X).mapIso (kFlatModelIso X K).symm.op)

end Derived

end AlgebraicGeometry.RingedSite

end
