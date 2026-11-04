module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.KFlatStrictReplacement

/-!
# K-flatness descends to the sections at an object of the site

Let `C` be a category and `𝒪` a presheaf of commutative rings on it. A complex `𝒦` of
`𝒪`-modules has, at every object `U`, a complex of sections `𝒦(U)` over the ring `𝒪(U)`. This
file proves that **K-flatness of `𝒦` for the objectwise tensor product descends to K-flatness
of `𝒦(U)` over `𝒪(U)`**, the descent that conditions (c) and (d) of [Stacks, Tag 099D] ask
of the K-flat strict replacement `Stacks.StrictReplacement.exists_isKFlat_strictReplacement`.

## The extension by zero

Every acyclic complex `M` of `𝒪(U)`-modules is a retract of the sections at `U` of an acyclic
complex of `𝒪`-modules, its **extension by zero** `j_{U!}`, in the form available for a presheaf
of modules: `extension` sends an `𝒪(U)`-module `N` to

```
X ↦ ∏_{p : X ⟶ U} (restriction of scalars of N along 𝒪(p))
```

the product being over the morphisms `U ⟶ X` of the site. Only *restriction* of scalars
occurs, never extension, so the functor is exact. Evaluating at `U` and projecting onto the
factor indexed by `𝟙 U` exhibits `N` as a retract of the sections at `U`.

Everything here is a statement about presheaves of modules and the objectwise tensor product;
the site carries no Grothendieck topology.

## Main definitions

* `Stacks.ObjectwiseKFlat.extension`: the extension by zero of an `𝒪(U)`-module from `U`, as a
  presheaf of `𝒪`-modules.
* `Stacks.ObjectwiseKFlat.extensionFunctor`, `Stacks.ObjectwiseKFlat.extensionComplex`: the
  same as a functor, and degreewise on cochain complexes.
* `Stacks.ObjectwiseKFlat.SectionwiseTensorAcyclic`: K-flatness of `𝒦` tested *through the
  sections at `U`* — for every acyclic complex `F` of presheaves of modules the total complex
  `Tot(F(U) ⊗_{𝒪(U)} 𝒦(U))` is acyclic. This is `Stacks.SheafOfModules.IsKFlat` with the sheaf
  tensor product replaced by the objectwise one, which is what it is on a chaotic site.

## Main results

* `Stacks.ObjectwiseKFlat.extensionUnitComplex_comp_extensionProjComplex`: a complex is a
  retract of the sections at `U` of its extension by zero.
* `Stacks.ObjectwiseKFlat.acyclic_sections_extensionComplex`: the extension by zero of an
  acyclic complex is acyclic at every object — exactness of `j_{U!}`.
* `Stacks.ObjectwiseKFlat.acyclic_of_sections_acyclic`: a complex of presheaves of modules is
  acyclic as soon as its complexes of sections are.
* `Stacks.ObjectwiseKFlat.acyclic_of_retract`: a retract of an acyclic complex is acyclic,
  through an arbitrary functor into cochain complexes.
* `Stacks.ObjectwiseKFlat.kFlat_sections_of_sectionwiseTensorAcyclic`: **the descent.**
  `SectionwiseTensorAcyclic 𝒪 U 𝒦` implies `CochainComplex.KFlat (𝒦(U))`, K-flatness of the
  complex of sections over the ring of sections.
* `Stacks.ObjectwiseKFlat.kFlat_sections_of_sheafComplex`: the descent for a complex of sheaves
  of modules, read as a complex of presheaves of modules.

## Implementation notes

The conclusion is Stacks 06XZ's `CochainComplex.KFlat` over the commutative ring `𝒪(U)`, which
is the predicate `Stacks.LocalCohomology.FunctorialCechData` is stated against; its monoidal
structure is the universe-lifted one, `ModuleCat.liftedModuleMonoidal`, applied by `letI` at
`.{u, u}` exactly as `CochainComplex.KFlat` applies it, because Mathlib's same-universe
instance is a different term and is the one instance search would otherwise find.

The complex of sections is `Stacks.StrictReplacement.sectionsFunctor`, and a complex of sheaves
of modules is read as a complex of presheaves of modules by
`Stacks.StrictReplacement.toPresheafComplex`.

The site's morphism universe, the universe of the rings and the universe of the modules are
all independent in the first three sections; the descent theorem ties the first and the last to
the ring universe, because the extension by zero at `U` is indexed by `X ⟶ U` and because
`CochainComplex.KFlat` places its modules in `ModuleCat.{max u v}` over a ring in `Type u`.

## References

* [The Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [The Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [The Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u u₁ u₂ v₂ u₃ v₃

namespace Stacks.ObjectwiseKFlat

/-! ### The extension by zero of a module from one object of the site -/

section Extension

variable {C : Type u₁} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{u}) (U : Cᵒᵖ)

/-- The identity restriction map of `R` acts as the identity on elements. -/
theorem ring_map_id_apply {X : Cᵒᵖ} (r : R.obj X) : (R.map (𝟙 X)).hom r = r := by
  rw [R.map_id]; rfl

/-- The restriction map of `R` along a composite is the composite of the restriction maps, on
elements. -/
theorem ring_map_comp_apply {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (r : R.obj X) :
    (R.map (f ≫ g)).hom r = (R.map g).hom ((R.map f).hom r) := by
  rw [R.map_comp]; rfl

/-- The sections at `X` of the extension by zero of `N` from `U`: a family of elements of `N`
indexed by the morphisms `X ⟶ U` of `Cᵒᵖ`, that is by the morphisms `U ⟶ X` of the site. -/
def ExtSections (N : ModuleCat.{v} (R.obj U)) (X : Cᵒᵖ) : Type v := (X ⟶ U) → N

/-- The families of elements of `N` indexed by `X ⟶ U` form an abelian group under pointwise
addition. -/
instance (N : ModuleCat.{v} (R.obj U)) (X : Cᵒᵖ) : AddCommGroup (ExtSections R U N X) :=
  inferInstanceAs (AddCommGroup ((X ⟶ U) → (N : Type v)))

/-- `R.obj X` acts on the family `(x p)_{p : X ⟶ U}` through the restriction maps `R.map p`:
this module is the product over `p` of the restrictions of scalars of `N` along `R.map p`. -/
instance (N : ModuleCat.{v} (R.obj U)) (X : Cᵒᵖ) :
    Module (R.obj X) (ExtSections R U N X) where
  smul r x := fun p => (R.map p).hom r • x p
  one_smul x := funext fun p => by
    change (R.map p).hom 1 • x p = x p
    rw [map_one, one_smul]
  mul_smul r s x := funext fun p => by
    change (R.map p).hom (r * s) • x p = (R.map p).hom r • ((R.map p).hom s • x p)
    rw [map_mul, mul_smul]
  smul_zero r := funext fun p => by
    change (R.map p).hom r • (0 : N) = 0
    rw [smul_zero]
  smul_add r x y := funext fun p => by
    change (R.map p).hom r • (x p + y p) = (R.map p).hom r • x p + (R.map p).hom r • y p
    rw [smul_add]
  add_smul r s x := funext fun p => by
    change (R.map p).hom (r + s) • x p = (R.map p).hom r • x p + (R.map p).hom s • x p
    rw [map_add, add_smul]
  zero_smul x := funext fun p => by
    change (R.map p).hom 0 • x p = 0
    rw [map_zero, zero_smul]

/-- The component at `p` of `r • x` is `R.map p r • x p`. -/
@[simp]
theorem extSections_smul_apply {N : ModuleCat.{v} (R.obj U)} {X : Cᵒᵖ} (r : R.obj X)
    (x : ExtSections R U N X) (p : X ⟶ U) :
    (r • x) p = (R.map p).hom r • x p :=
  rfl

/-- The restriction map of the extension by zero: reindexing along precomposition with `f`. -/
def extSectionsMap (N : ModuleCat.{v} (R.obj U)) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj X) (ExtSections R U N X) ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (ExtSections R U N Y)) :=
  ModuleCat.ofHom
    (X := ExtSections R U N X)
    (Y := ((ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (ExtSections R U N Y)) : Type v))
    { toFun := fun x q => x (f ≫ q)
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => funext fun q => by
        change (r • x) (f ≫ q) = (R.map q).hom ((R.map f).hom r) • x (f ≫ q)
        rw [extSections_smul_apply, ring_map_comp_apply] }

/-- The restriction map of the extension by zero along `f` sends `x` to `q ↦ x (f ≫ q)`. -/
@[simp]
theorem extSectionsMap_apply (N : ModuleCat.{v} (R.obj U)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : ExtSections R U N X) (q : Y ⟶ U) : extSectionsMap R U N f x q = x (f ≫ q) :=
  rfl

/-- **The extension by zero of `N` from `U`.** The presheaf of `R`-modules whose sections at
`X` are the families `(x_p)_{p : X ⟶ U}` of elements of `N`, with `R.obj X` acting through the
restriction maps `R.map p`.

This is `j_{U!}` in the form in which it exists for presheaves of modules: on a site with the
chaotic topology, where a presheaf of modules is a sheaf of modules, it is the extension by
zero of Stacks 03EU. -/
def extension (N : ModuleCat.{v} (R.obj U)) : PresheafOfModules.{v} R where
  obj X := ModuleCat.of _ (ExtSections R U N X)
  map {_ _} f := extSectionsMap R U N f
  map_id X := by
    ext x
    exact funext fun q => by
      change x (𝟙 X ≫ q) = x q
      rw [Category.id_comp]
  map_comp {X Y Z} f g := by
    ext x
    exact funext fun q => by
      change x ((f ≫ g) ≫ q) = x (f ≫ g ≫ q)
      rw [Category.assoc]

/-- The extension by zero of a morphism, applied in each index. -/
def extensionHom {N N' : ModuleCat.{v} (R.obj U)} (g : N ⟶ N') (X : Cᵒᵖ) :
    (extension R U N).obj X ⟶ (extension R U N').obj X :=
  ModuleCat.ofHom
    (X := ExtSections R U N X) (Y := ExtSections R U N' X)
    { toFun := fun x p => g (x p)
      map_add' := fun _ _ => funext fun _ => map_add g.hom _ _
      map_smul' := fun r x => funext fun p => g.hom.map_smul ((R.map p).hom r) (x p) }

/-- The extension by zero of `g` applies `g` to each component. -/
@[simp]
theorem extensionHom_apply {N N' : ModuleCat.{v} (R.obj U)} (g : N ⟶ N') (X : Cᵒᵖ)
    (x : ExtSections R U N X) (p : X ⟶ U) : extensionHom R U g X x p = g (x p) :=
  rfl

/-- **Extension by zero from `U`, as a functor.** -/
def extensionFunctor : ModuleCat.{v} (R.obj U) ⥤ PresheafOfModules.{v} R where
  obj N := extension R U N
  map g := { app X := extensionHom R U g X }
  map_id N := by
    ext X x
    exact funext fun p => rfl
  map_comp g g' := by
    ext X x
    exact funext fun p => rfl

/-- The component at `X` of the extension by zero of a morphism `g` is `extensionHom R U g X`. -/
@[simp]
theorem extensionFunctor_map_app {N N' : ModuleCat.{v} (R.obj U)} (g : N ⟶ N') (X : Cᵒᵖ) :
    ((extensionFunctor R U).map g).app X = extensionHom R U g X :=
  rfl

/-- Extension by zero from `U` is an additive functor. -/
instance : (extensionFunctor R U).Additive where
  map_add := by
    intros
    ext X x
    exact funext fun p => rfl

/-! ### The extension by zero retracts onto the module it extends -/

/-- The projection of the sections at `U` of the extension by zero of `N` onto `N`: evaluation
of the family at the identity. -/
def extensionProj (N : ModuleCat.{v} (R.obj U)) : (extension R U N).obj U ⟶ N :=
  ModuleCat.ofHom
    (X := ExtSections R U N U) (Y := (N : Type v))
    { toFun := fun x => x (𝟙 U)
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (R.map (𝟙 U)).hom r • x (𝟙 U) = r • x (𝟙 U)
        rw [ring_map_id_apply] }

open Classical in
/-- The section of `extensionProj`: the family supported at the identity. -/
def extensionUnit (N : ModuleCat.{v} (R.obj U)) : N ⟶ (extension R U N).obj U :=
  ModuleCat.ofHom
    (X := (N : Type v)) (Y := ExtSections R U N U)
    { toFun := fun n p => if p = 𝟙 U then n else 0
      map_add' := fun n n' => funext fun p => by
        change (if p = 𝟙 U then n + n' else 0) =
          (if p = 𝟙 U then n else 0) + (if p = 𝟙 U then n' else 0)
        by_cases h : p = 𝟙 U
        · rw [if_pos h, if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, if_neg h, add_zero]
      map_smul' := fun r n => funext fun p => by
        change (if p = 𝟙 U then r • n else 0) =
          (R.map p).hom r • if p = 𝟙 U then n else 0
        by_cases h : p = 𝟙 U
        · rw [if_pos h, if_pos h, h, ring_map_id_apply]
        · rw [if_neg h, if_neg h, smul_zero] }

open Classical in
/-- The family `extensionUnit R U N n` is `n` at the identity and `0` elsewhere. -/
@[simp]
theorem extensionUnit_apply (N : ModuleCat.{v} (R.obj U)) (n : N) (p : U ⟶ U) :
    extensionUnit R U N n p = if p = 𝟙 U then n else 0 :=
  rfl

/-- `extensionProj R U N` evaluates a family at the identity. -/
@[simp]
theorem extensionProj_apply (N : ModuleCat.{v} (R.obj U)) (x : ExtSections R U N U) :
    extensionProj R U N x = x (𝟙 U) :=
  rfl

/-- `extensionProj R U N` is a retraction of `extensionUnit R U N`. -/
theorem extensionUnit_comp_extensionProj (N : ModuleCat.{v} (R.obj U)) :
    extensionUnit R U N ≫ extensionProj R U N = 𝟙 N := by
  classical
  ext n
  change (if (𝟙 U : U ⟶ U) = 𝟙 U then n else 0) = n
  rw [if_pos rfl]

/-- `extensionUnit` is natural in the module. -/
theorem extensionUnit_naturality {N N' : ModuleCat.{v} (R.obj U)} (g : N ⟶ N') :
    extensionUnit R U N ≫ ((extensionFunctor R U).map g).app U =
      g ≫ extensionUnit R U N' := by
  classical
  ext n
  refine funext fun p => ?_
  change g (if p = 𝟙 U then n else 0) = if p = 𝟙 U then g n else 0
  by_cases h : p = 𝟙 U
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

/-- `extensionProj` is natural in the module. -/
theorem extensionProj_naturality {N N' : ModuleCat.{v} (R.obj U)} (g : N ⟶ N') :
    ((extensionFunctor R U).map g).app U ≫ extensionProj R U N' =
      extensionProj R U N ≫ g := by
  ext x
  rfl

/-! ### The extension by zero of a complex -/

/-- Extension by zero from `U`, applied degreewise to a cochain complex. -/
abbrev extensionComplex :
    CochainComplex (ModuleCat.{v} (R.obj U)) ℤ ⥤ CochainComplex (PresheafOfModules.{v} R) ℤ :=
  (extensionFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)

variable (M : CochainComplex (ModuleCat.{v} (R.obj U)) ℤ)

/-- `M` sits inside the complex of sections at `U` of its extension by zero. -/
def extensionUnitComplex :
    M ⟶ (Stacks.StrictReplacement.sectionsFunctor R U).obj ((extensionComplex R U).obj M) where
  f n := extensionUnit R U (M.X n)
  comm' i j _ := extensionUnit_naturality R U (M.d i j)

/-- The retraction of `extensionUnitComplex`. -/
def extensionProjComplex :
    (Stacks.StrictReplacement.sectionsFunctor R U).obj ((extensionComplex R U).obj M) ⟶ M where
  f n := extensionProj R U (M.X n)
  comm' i j _ := (extensionProj_naturality R U (M.d i j)).symm

/-- **A complex is a retract of the sections at `U` of its extension by zero.** -/
theorem extensionUnitComplex_comp_extensionProjComplex :
    extensionUnitComplex R U M ≫ extensionProjComplex R U M = 𝟙 M :=
  HomologicalComplex.hom_ext _ _ fun n => extensionUnit_comp_extensionProj R U (M.X n)

/-- **Exactness of the extension by zero.** The extension by zero of an acyclic complex is
acyclic at every object of the site. -/
theorem acyclic_sections_extensionComplex (hM : M.Acyclic) (X : Cᵒᵖ) :
    ((Stacks.StrictReplacement.sectionsFunctor R X).obj
      ((extensionComplex R U).obj M)).Acyclic := by
  intro i
  have h := hM i
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at h ⊢
  intro x hx
  have hx' : ∀ p : X ⟶ U, (M.d i ((ComplexShape.up ℤ).next i)) (x p) = 0 :=
    fun p => congrFun hx p
  choose y hy using fun p => h (x p) (hx' p)
  exact ⟨y, funext fun p => hy p⟩

end Extension

/-! ### Acyclicity of a complex of presheaves of modules is objectwise -/

section Objectwise

variable {C : Type u₁} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- A presheaf of modules all of whose modules of sections are zero is zero. -/
theorem isZero_of_sections (M : PresheafOfModules.{v} R) (h : ∀ X, IsZero (M.obj X)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact PresheafOfModules.hom_ext fun X => (h X).eq_of_src _ _

/-- **Acyclicity of a complex of presheaves of modules is objectwise**: a complex whose
complexes of sections are all acyclic is acyclic. -/
theorem acyclic_of_sections_acyclic (F : CochainComplex (PresheafOfModules.{v} R) ℤ)
    (h : ∀ X, ((Stacks.StrictReplacement.sectionsFunctor R X).obj F).Acyclic) : F.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
  refine isZero_of_sections R _ fun X => ?_
  have hX := h X i
  rw [HomologicalComplex.exactAt_iff] at hX
  have heq : ((Stacks.StrictReplacement.sectionsFunctor R X).obj F).sc i
      = (F.sc i).map (PresheafOfModules.evaluation R X) := rfl
  rw [heq, ShortComplex.exact_iff_isZero_homology] at hX
  exact IsZero.of_iso hX
    ((F.sc i).mapHomologyIso (PresheafOfModules.evaluation R X)).symm

end Objectwise

/-! ### A retract of an acyclic complex is acyclic -/

/-- **A retract of an acyclic complex is acyclic**: if `M` is a retract of `F` in an arbitrary
category and `T` is a functor from that category to cochain complexes, then acyclicity of
`T.obj F` gives acyclicity of `T.obj M`. -/
theorem acyclic_of_retract {A : Type u₂} [Category.{v₂} A] {B : Type u₃} [Category.{v₃} B]
    [Preadditive B] [CategoryWithHomology B] {M F : A} (ι : M ⟶ F) (π : F ⟶ M)
    (hιπ : ι ≫ π = 𝟙 M) (T : A ⥤ CochainComplex B ℤ) (hF : (T.obj F).Acyclic) :
    (T.obj M).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have key : HomologicalComplex.homologyMap (T.map ι) i ≫
      HomologicalComplex.homologyMap (T.map π) i = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← T.map_comp, hιπ, T.map_id,
      HomologicalComplex.homologyMap_id]
  rw [← key, ((hF i).isZero_homology).eq_zero_of_tgt
    (HomologicalComplex.homologyMap (T.map ι) i), zero_comp]

/-! ### The descent of K-flatness to the sections at an object -/

section Descent

variable {C : Type u₁} [Category.{u} C] (S : Cᵒᵖ ⥤ CommRingCat.{u}) (U : Cᵒᵖ)

/-- **K-flatness tested through the sections at `U`.** For every acyclic cochain complex `F` of
presheaves of `S`-modules, the total complex `Tot(F(U) ⊗_{S(U)} K(U))` of complexes of
`S(U)`-modules is acyclic.

This is `Stacks.SheafOfModules.IsKFlat` with the sheaf tensor product replaced by the
objectwise one and read at `U`, which is what it amounts to on a site with the chaotic
topology. The monoidal structure is the universe-lifted one, applied exactly as
`CochainComplex.KFlat` applies it. -/
def SectionwiseTensorAcyclic
    (K : CochainComplex (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) ℤ) : Prop :=
  letI := ModuleCat.liftedModuleMonoidalStruct.{u, u} (R := S.obj U)
  letI := ModuleCat.liftedModuleMonoidal.{u, u} (R := S.obj U)
  ∀ F : CochainComplex (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) ℤ,
    F.Acyclic →
      (HomologicalComplex.tensorObj
        (((Stacks.StrictReplacement.sectionsFunctor _ U).obj F :
          CochainComplex (ModuleCat.{u} (S.obj U)) ℤ))
        (((Stacks.StrictReplacement.sectionsFunctor _ U).obj K :
          CochainComplex (ModuleCat.{u} (S.obj U)) ℤ))).Acyclic

/-- **K-flatness descends to the sections at an object of the site.** If tensoring with the
complex of sections `K(U)` kills the acyclic complexes that come from acyclic complexes of
presheaves of `S`-modules, then `K(U)` is a K-flat complex of `S(U)`-modules in the sense of
[Stacks, Tag 06XZ]. -/
theorem kFlat_sections_of_sectionwiseTensorAcyclic
    (K : CochainComplex (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) ℤ)
    (h : SectionwiseTensorAcyclic S U K) :
    CochainComplex.KFlat.{u, u} (R := S.obj U)
      ((Stacks.StrictReplacement.sectionsFunctor _ U).obj K) := by
  let : MonoidalCategoryStruct (ModuleCat.{u} (S.obj U)) :=
    ModuleCat.liftedModuleMonoidalStruct.{u, u}
  let : MonoidalCategory (ModuleCat.{u} (S.obj U)) := ModuleCat.liftedModuleMonoidal.{u, u}
  intro M hM
  refine acyclic_of_retract
    (extensionUnitComplex (S ⋙ forget₂ CommRingCat RingCat) U M)
    (extensionProjComplex (S ⋙ forget₂ CommRingCat RingCat) U M)
    (extensionUnitComplex_comp_extensionProjComplex
      (S ⋙ forget₂ CommRingCat RingCat) U M)
    (((curriedTensor (ModuleCat.{u} (S.obj U))).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj
      ((Stacks.StrictReplacement.sectionsFunctor _ U).obj K)) ?_
  exact h ((extensionComplex (S ⋙ forget₂ CommRingCat RingCat) U).obj M)
    (acyclic_of_sections_acyclic _ _
      (acyclic_sections_extensionComplex (S ⋙ forget₂ CommRingCat RingCat) U M hM))

/-- **K-flatness descends to the sections at an object**, for a complex of sheaves of modules
read as a complex of presheaves of modules through `Stacks.StrictReplacement.toPresheafComplex`. -/
theorem kFlat_sections_of_sheafComplex {J : GrothendieckTopology C}
    (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))
    (𝒦 : CochainComplex (SheafOfModules.{u}
      (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})) ℤ)
    (h : SectionwiseTensorAcyclic S U
      ((Stacks.StrictReplacement.toPresheafComplex
        (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})).obj 𝒦)) :
    CochainComplex.KFlat.{u, u} (R := S.obj U)
      ((Stacks.StrictReplacement.sectionsFunctor _ U).obj
        ((Stacks.StrictReplacement.toPresheafComplex
          (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u})).obj 𝒦)) :=
  kFlat_sections_of_sectionwiseTensorAcyclic S U _ h

end Descent

end Stacks.ObjectwiseKFlat

end
