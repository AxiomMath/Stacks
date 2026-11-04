module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory.GlueingDatum

/-!
# The construction of module glueing data and the adjunction `Can ⊣ H⁰`

This file packages the category of module glueing data with the canonical functor `Can` from
`R`-modules and the functor `H⁰` of compatible global sections, and proves that `H⁰` is right
adjoint to `Can`.

## Main definitions

* `FormalGlueing.ModuleGlueingConstruction`: the category and its two canonical functors.

## Main results

* `FormalGlueing.moduleGlueingConstruction`: the category of glueing data, the canonical functor
  to it, and the compatible-sections functor.
* `FormalGlueing.canonicalSectionsAdjunction`: the adjunction between canonical glueing and
  compatible global sections.

## Implementation notes

For the adjunction the category of glueing data has an independent universe parameter, and the
module category is taken in the common universe of the rings and the glueing data, so the two
functors have matching source and target categories.

## References

* [Stacks Project, Tag 05EL](https://stacks.math.columbia.edu/tag/05EL)
* [Stacks Project, Tag 0H77](https://stacks.math.columbia.edu/tag/0H77)
-/

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory Cech TensorProduct

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The category structure on glueing data together with the canonical functor and the functor of
compatible global sections. The equations on pure tensors and denominator-one fractions pin the
comparison maps of the canonical object to the canonical localization isomorphisms. -/
public structure ModuleGlueingConstruction where
  /-- The identification of iterated with simultaneous localizations. -/
  comparison : LocalizationComparisons.{u, max u v w} f
  /-- The category structure on module glueing data. -/
  category : Category.{max u v w} (ModuleGlueingDatum.{u, v, w} S f comparison)
  /-- Arrows of `category` are the compatible families of maps. -/
  homEquiv : letI := category
    ∀ X Y : ModuleGlueingDatum.{u, v, w} S f comparison, (X ⟶ Y) ≃
      ModuleGlueingMap (R := R) S f comparison X Y
  /-- The identity arrow has the identity as generic component. -/
  homEquiv_id_generic : letI := category
    ∀ X : ModuleGlueingDatum.{u, v, w} S f comparison,
      (homEquiv X X (𝟙 X)).generic = 𝟙 X.generic
  /-- The identity arrow has identities as local components. -/
  homEquiv_id_local : letI := category
    ∀ (X : ModuleGlueingDatum.{u, v, w} S f comparison) i,
      (homEquiv X X (𝟙 X)).localPiece i = 𝟙 (X.localPiece i)
  /-- Composition of arrows is composition of generic components. -/
  homEquiv_comp_generic : letI := category
    ∀ {X Y Z : ModuleGlueingDatum.{u, v, w} S f comparison} (g : X ⟶ Y) (h : Y ⟶ Z),
      (homEquiv X Z (g ≫ h)).generic = (homEquiv X Y g).generic ≫ (homEquiv Y Z h).generic
  /-- Composition of arrows is composition of local components. -/
  homEquiv_comp_local : letI := category
    ∀ {X Y Z : ModuleGlueingDatum.{u, v, w} S f comparison} (g : X ⟶ Y) (h : Y ⟶ Z) i,
      (homEquiv X Z (g ≫ h)).localPiece i =
        (homEquiv X Y g).localPiece i ≫ (homEquiv Y Z h).localPiece i
  /-- The canonical functor `Can` from `R`-modules to glueing data. -/
  canonical : letI := category
    ModuleCat.{max u v w} R ⥤ ModuleGlueingDatum.{u, v, w} S f comparison
  /-- The generic component of `Can M` is `S ⊗[R] M`. -/
  canonicalGeneric : letI := category
    ∀ M, (canonical.obj M).generic ≃ₗ[S] TensorProduct R S M
  /-- The local components of `Can M` are the localizations `M_{fᵢ}`. -/
  canonicalLocal : letI := category
    ∀ M i, (canonical.obj M).localPiece i ≃ₗ[Localization.Away (f i)]
      LocalizedModule.Away (f i) M
  /-- Under these identifications, the comparison `alpha i` of `Can M` sends `(s ⊗ m) / 1` to
  `s ⊗ (m / 1)`. -/
  canonicalAlpha : letI := category
    ∀ (M : ModuleCat.{max u v w} R) i (m : M) (s : S),
      letI : Module R ↑((canonical.obj M).localPiece i) :=
        Module.compHom _ (algebraMap R (Localization.Away (f i)))
      TensorProduct.map
          LinearMap.id (restrictAwayLinearEquiv f i (canonicalLocal M i)).toLinearMap
          ((canonical.obj M).alpha i
            (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _
              ((canonicalGeneric M).symm (s ⊗ₜ[R] m)))) =
        s ⊗ₜ[R] LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m
  /-- Under these identifications, the overlap isomorphism `alphaIJ i j` of `Can M` sends
  `m / 1 / 1` to `m / 1 / 1`. -/
  canonicalAlphaIJ : letI := category
    ∀ (M : ModuleCat.{max u v w} R) i j (m : M),
      letI : Module R ↑((canonical.obj M).localPiece j) :=
        Module.compHom _ (algebraMap R (Localization.Away (f j)))
      localizedMap f {i}
          (restrictAwayLinearEquiv f j (canonicalLocal M j)).toLinearMap
          ((canonical.obj M).alphaIJ i j
            (LocalizedModule.mkLinearMap (cechSub f {j}) _
              ((canonicalLocal M i).symm
                (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m)))) =
        LocalizedModule.mkLinearMap (cechSub f {i}) _
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) M m)
  /-- The generic component of `Can g` is `S ⊗[R] g`. -/
  canonicalMapGeneric : letI := category
    ∀ {M N : ModuleCat.{max u v w} R} (g : M ⟶ N) (m : M) (s : S),
      canonicalGeneric N
          ((homEquiv (canonical.obj M) (canonical.obj N) (canonical.map g)).generic
            ((canonicalGeneric M).symm (s ⊗ₜ[R] m))) =
        s ⊗ₜ[R] g m
  /-- The local components of `Can g` are the localizations `g_{fᵢ}`. -/
  canonicalMapLocal : letI := category
    ∀ {M N : ModuleCat.{max u v w} R} (g : M ⟶ N) i (m : M),
      canonicalLocal N i
          ((homEquiv (canonical.obj M) (canonical.obj N) (canonical.map g)).localPiece i
            ((canonicalLocal M i).symm
              (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m))) =
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N (g m)
  /-- The functor `H⁰` of compatible global sections. -/
  sections : letI := category
    ModuleGlueingDatum.{u, v, w} S f comparison ⥤ ModuleCat.{max u v w} R
  /-- The value of `H⁰` on `X` is the module of compatible tuples of `X`. -/
  sectionsObj : letI := category
    ∀ X, sections.obj X ≃ₗ[R] compatibleSections S f comparison X
  /-- On generic components, `H⁰ g` acts by the generic component of `g`. -/
  sectionsMapGeneric : letI := category
    ∀ {X Y} (g : X ⟶ Y) (x : sections.obj X),
      (sectionsObj Y (sections.map g x)).1.1 =
        (homEquiv X Y g).generic (sectionsObj X x).1.1
  /-- On local components, `H⁰ g` acts by the local components of `g`. -/
  sectionsMapLocal : letI := category
    ∀ {X Y} (g : X ⟶ Y) (x : sections.obj X) i,
      (sectionsObj Y (sections.map g x)).1.2 i =
        (homEquiv X Y g).localPiece i ((sectionsObj X x).1.2 i)
  /-- The evident map from a module to the compatible sections of its canonical glueing datum. -/
  canonicalSectionsUnit : letI := category
    𝟭 (ModuleCat.{max u v w} R) ⟶ canonical ⋙ sections
  /-- The unit sends `m` to a tuple with generic component `1 ⊗ m`. -/
  canonicalSectionsUnit_generic : letI := category
    ∀ (M : ModuleCat.{max u v w} R) (m : M),
      canonicalGeneric M
          ((sectionsObj (canonical.obj M) ((canonicalSectionsUnit.app M) m)).1.1) =
        1 ⊗ₜ[R] m
  /-- The unit sends `m` to a tuple with local components `m / 1`. -/
  canonicalSectionsUnit_local : letI := category
    ∀ (M : ModuleCat.{max u v w} R) (m : M) i,
      canonicalLocal M i
          ((sectionsObj (canonical.obj M) ((canonicalSectionsUnit.app M) m)).1.2 i) =
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m

/-- The category `Glue(R → S, f₁, …, fₜ)`, its canonical functor from `R`-modules, and its
compatible-sections functor `H⁰`. -/
@[stacks 05EL]
public noncomputable def moduleGlueingConstruction : ModuleGlueingConstruction S f where
  comparison := localizationComparisons f
  category := moduleGlueingCategory S f (localizationComparisons f)
  homEquiv _ _ := Equiv.refl _
  homEquiv_id_generic _ := rfl
  homEquiv_id_local _ _ := rfl
  homEquiv_comp_generic _ _ := rfl
  homEquiv_comp_local _ _ _ := rfl
  canonical := canonicalFunctor S f
  canonicalGeneric _ := LinearEquiv.refl _ _
  canonicalLocal _ _ := LinearEquiv.refl _ _
  canonicalAlpha M i m s := by
    change TensorProduct.map _ _ (canonicalAlpha S f M i
      (LocalizedModule.mkLinearMap _ _ (s ⊗ₜ[R] m))) = _
    rw [canonicalAlpha_mk]
    rfl
  canonicalAlphaIJ M i j m := by
    change localizedMap f {i} _ (canonicalAlphaIJ f M i j
      (LocalizedModule.mkLinearMap _ _ (canonicalLocalMk f M i m))) = _
    rw [canonicalAlphaIJ_mk]
    erw [localizedMap_mk]
    rfl
  canonicalMapGeneric _ _ _ := rfl
  canonicalMapLocal g i m := LocalizedModule.map_mk _ _ _ _
  sections := compatibleSectionsFunctor S f (localizationComparisons f)
  sectionsObj _ := LinearEquiv.refl _ _
  sectionsMapGeneric _ _ := rfl
  sectionsMapLocal _ _ _ := rfl
  canonicalSectionsUnit := FormalGlueing.canonicalSectionsUnit S f
  canonicalSectionsUnit_generic _ _ := rfl
  canonicalSectionsUnit_local _ _ _ := rfl

end FormalGlueing

end

/-! ### Compatible sections are right adjoint to canonical glueing -/

section

open CategoryTheory

public section

set_option backward.isDefEq.respectTransparency false

namespace FormalGlueing

universe u v w

open FormalGlueing Cech

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

private local instance glueCategory
    (C : ModuleGlueingConstruction.{u, v, w} S f) :
    Category (ModuleGlueingDatum.{u, v, w} S f C.comparison) := C.category

private theorem isUnitEnd {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (a : A) (ha : IsUnit (algebraMap A B a)) :
    IsUnit (algebraMap A (Module.End A M) a) := by
  obtain ⟨b, hb⟩ := ha
  let inv : M →ₗ[A] M :=
    { toFun := fun m ↦ (↑b⁻¹ : B) • m
      map_add' := by simp
      map_smul' c m := by rw [RingHom.id_apply, smul_comm] }
  refine ⟨⟨_, inv, ?_, ?_⟩, rfl⟩
  · ext m
    show a • ((↑b⁻¹ : B) • m) = m
    rw [show a • ((↑b⁻¹ : B) • m) = ((algebraMap A B a) • (↑b⁻¹ : B) • m : M)
      from (IsScalarTower.algebraMap_smul B a _).symm, ← hb, smul_smul, b.mul_inv, one_smul]
  · ext m
    show (↑b⁻¹ : B) • (a • m) = m
    rw [show a • m = ((algebraMap A B a) • m : M)
      from (IsScalarTower.algebraMap_smul B a _).symm, ← hb, smul_smul, b.inv_mul, one_smul]

/-- Powers of `fᵢ` act invertibly on the underlying `R`-module of an `R[1 / fᵢ]`-module. -/
private theorem isUnit_end_restrictFromAway (i : Fin r)
    (M : ModuleCat (Localization.Away (f i))) (a : Submonoid.powers (f i)) :
    IsUnit (algebraMap R (Module.End R (restrictFromAway f i M)) (a : R)) := by
  let : IsScalarTower R (Localization.Away (f i)) (restrictFromAway f i M) :=
    ⟨fun a b m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact isUnitEnd (M := restrictFromAway f i M) (a : R)
    (IsLocalization.map_units (Localization.Away (f i)) a)

private noncomputable def genericOfSection
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum S f C.comparison)
    (h : N ⟶ C.sections.obj X) :
    (C.canonical.obj N).generic ⟶ X.generic := by
  letI : Module R X.generic := Module.compHom X.generic (algebraMap R S)
  let g : N →ₗ[R] X.generic :=
    { toFun := fun n ↦ ((C.sectionsObj X) (h n)).1.1
      map_add' x y := by simp
      map_smul' a x := by
        rw [map_smul, map_smul]
        rfl }
  let b : S →ₛₗ[algebraMap R S] N →ₛₗ[algebraMap R S] X.generic :=
    { toFun := fun s ↦
        { toFun := fun n ↦ s • g n
          map_add' x y := by rw [map_add, smul_add]
          map_smul' := by
            intro a n
            rw [map_smul]
            change s • ((algebraMap R S a) • g n) = (algebraMap R S a) • (s • g n)
            rw [smul_comm] }
      map_add' s t := by
        ext n
        exact add_smul s t (g n)
      map_smul' := by
        intro a s
        ext n
        change (a • s) • g n = (algebraMap R S a) • (s • g n)
        rw [Algebra.smul_def, mul_smul] }
  let eR := TensorProduct.lift b
  let e : TensorProduct R S N →ₗ[S] X.generic :=
    { toFun := eR
      map_add' := eR.map_add
      map_smul' := by
        intro s z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp [hx, hy]
        | tmul a n =>
          simp only [TensorProduct.smul_tmul']
          exact mul_smul s a (g n) }
  exact ModuleCat.ofHom (e.comp (C.canonicalGeneric N).toLinearMap)

private noncomputable def localOfSection
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum S f C.comparison)
    (h : N ⟶ C.sections.obj X) (i : Fin r) :
    (C.canonical.obj N).localPiece i ⟶ X.localPiece i := by
  letI : Module R (X.localPiece i) :=
    Module.compHom (X.localPiece i) (algebraMap R (Localization.Away (f i)))
  letI : IsScalarTower R (Localization.Away (f i)) (X.localPiece i) :=
    ⟨fun a b m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let g : N →ₗ[R] X.localPiece i :=
    { toFun := fun n ↦ ((C.sectionsObj X) (h n)).1.2 i
      map_add' x y := by simp
      map_smul' a x := by
        rw [map_smul, map_smul]
        rfl }
  let e := (LocalizedModule.lift (Submonoid.powers (f i))
      g
      (isUnit_end_restrictFromAway f i (X.localPiece i)))
      |>.extendScalarsOfIsLocalization (Submonoid.powers (f i)) (Localization.Away (f i))
  exact ModuleCat.ofHom (e.comp (C.canonicalLocal N i).toLinearMap)

private theorem genericOfSection_apply
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum S f C.comparison)
    (h : N ⟶ C.sections.obj X) (n : N) :
    genericOfSection S f C N X h ((C.canonicalGeneric N).symm (1 ⊗ₜ[R] n)) =
      ((C.sectionsObj X) (h n)).1.1 := by
  simp [genericOfSection, LinearMap.comp_apply, TensorProduct.lift.tmul]

private theorem localOfSection_apply
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum S f C.comparison)
    (h : N ⟶ C.sections.obj X) (i : Fin r) (n : N) :
    localOfSection S f C N X h i
        ((C.canonicalLocal N i).symm
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N n)) =
      ((C.sectionsObj X) (h n)).1.2 i := by
  simp [localOfSection, LinearMap.comp_apply]

private theorem constructionCanonicalAlpha_mk
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (i : Fin r) (n : N) (s : S) :
    let : Module R ↑((C.canonical.obj N).localPiece i) :=
      Module.compHom _ (algebraMap R (Localization.Away (f i)))
    (C.canonical.obj N).alpha i
        (LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R S (f i))) _
          ((C.canonicalGeneric N).symm (s ⊗ₜ[R] n))) =
      s ⊗ₜ[R] ((C.canonicalLocal N i).symm
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N n)) := by
  let : Module R ↑((C.canonical.obj N).localPiece i) :=
    Module.compHom _ (algebraMap R (Localization.Away (f i)))
  let e := restrictAwayLinearEquiv f i (C.canonicalLocal N i)
  have he : e ((C.canonicalLocal N i).symm
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N n)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N n :=
    (C.canonicalLocal N i).apply_symm_apply _
  apply (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) e).injective
  show (TensorProduct.map LinearMap.id e.toLinearMap) _ =
    (TensorProduct.map LinearMap.id e.toLinearMap) _
  rw [C.canonicalAlpha N i n s]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearEquiv.coe_coe, he]

private theorem constructionCanonicalAlphaIJ_mk
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (i j : Fin r) (n : N) :
    let : Module R ↑((C.canonical.obj N).localPiece j) :=
      Module.compHom _ (algebraMap R (Localization.Away (f j)))
    (C.canonical.obj N).alphaIJ i j
        (LocalizedModule.mkLinearMap (cechSub f {j}) _
          ((C.canonicalLocal N i).symm
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N n))) =
      LocalizedModule.mkLinearMap (cechSub f {i}) _
        ((C.canonicalLocal N j).symm
          (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) N n)) := by
  let : Module R ↑((C.canonical.obj N).localPiece j) :=
    Module.compHom _ (algebraMap R (Localization.Away (f j)))
  let e := restrictAwayLinearEquiv f j (C.canonicalLocal N j)
  have he : e ((C.canonicalLocal N j).symm
      (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) N n)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (f j)) N n :=
    (C.canonicalLocal N j).apply_symm_apply _
  apply (LocalizedModule.map_injective (cechSub f {i}) e.toLinearMap e.injective)
  show (localizedMap f {i} e.toLinearMap) _ =
    (localizedMap f {i} e.toLinearMap) _
  rw [C.canonicalAlphaIJ N i j n, localizedMap_mk, LinearEquiv.coe_coe, he]

private theorem tensor_ext {A B M L P : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M]
    [AddCommGroup L] [Module B L] [AddCommGroup P] [Module B P]
    (e : L ≃ₗ[B] TensorProduct A B M) (g h : L →ₗ[B] P)
    (he : ∀ m, g (e.symm (1 ⊗ₜ[A] m)) = h (e.symm (1 ⊗ₜ[A] m))) : g = h := by
  ext l
  obtain ⟨z, rfl⟩ := e.symm.surjective l
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    have hz : b ⊗ₜ[A] m = b • (1 ⊗ₜ[A] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, map_smul, map_smul, he]

private theorem localized_ext {A M L P : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup L] [Module A L]
    [AddCommGroup P] [Module A P] (T : Submonoid A)
    (e : L ≃ₗ[A] LocalizedModule T M) (g h : L →ₗ[A] P)
    (hu : ∀ a : T, IsUnit (algebraMap A (Module.End A P) a))
    (he : ∀ m, g (e.symm (LocalizedModule.mkLinearMap T M m)) =
      h (e.symm (LocalizedModule.mkLinearMap T M m))) : g = h := by
  have hh : g.comp e.symm.toLinearMap = h.comp e.symm.toLinearMap :=
    IsLocalizedModule.ext T (LocalizedModule.mkLinearMap T M) hu (LinearMap.ext he)
  ext l
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using DFunLike.congr_fun hh (e l)

private noncomputable def glueMapOfSection
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R)
    (X : ModuleGlueingDatum S f C.comparison)
    (h : N ⟶ C.sections.obj X) : ModuleGlueingMap S f C.comparison (C.canonical.obj N) X where
  generic := genericOfSection S f C N X h
  localPiece := localOfSection S f C N X h
  alpha_compatibility i m := by
    let : Module R (X.localPiece i) :=
      Module.compHom _ (algebraMap R (Localization.Away (f i)))
    let l := ((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map (localOfSection S f C N X h i)).hom
    have hh : (X.alpha i).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _).comp
          (genericOfSection S f C N X h).hom) =
        (TensorProduct.AlgebraTensorModule.lTensor S S l).comp
          (((C.canonical.obj N).alpha i).toLinearMap.comp
            (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _)) := by
      apply tensor_ext (C.canonicalGeneric N)
      intro n
      dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [genericOfSection_apply, constructionCanonicalAlpha_mk]
      change X.alpha i _ = (1 : S) ⊗ₜ[R] (localOfSection S f C N X h i _)
      rw [localOfSection_apply]
      exact ((C.sectionsObj X) (h n)).2.1 i
    exact DFunLike.congr_fun hh m
  alphaIJ_compatibility i j m := by
    let : Module R ((C.canonical.obj N).localPiece i) :=
      Module.compHom _ (algebraMap R (Localization.Away (f i)))
    let : Module R ((C.canonical.obj N).localPiece j) :=
      Module.compHom _ (algebraMap R (Localization.Away (f j)))
    let : Module R (X.localPiece i) :=
      Module.compHom _ (algebraMap R (Localization.Away (f i)))
    let : Module R (X.localPiece j) :=
      Module.compHom _ (algebraMap R (Localization.Away (f j)))
    let li := ((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map (localOfSection S f C N X h i)).hom
    let lj := ((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f j)))).map (localOfSection S f C N X h j)).hom
    have hh : (X.alphaIJ i j).toLinearMap.comp
        ((LocalizedModule.mkLinearMap (cechSub f {j}) _).comp li) =
        (localizedMap f {i} lj).comp
          (((C.canonical.obj N).alphaIJ i j).toLinearMap.comp
            (LocalizedModule.mkLinearMap (cechSub f {j}) _)) := by
      apply localized_ext (Submonoid.powers (f i))
        (restrictAwayLinearEquiv f i (C.canonicalLocal N i))
      · intro a
        exact IsLocalizedModule.map_units (S := cechSub f {i})
          (LocalizedModule.mkLinearMap (cechSub f {i}) _)
          ⟨a, by simpa only [cechSub, Finset.prod_singleton] using a.2⟩
      · intro n
        change X.alphaIJ i j (LocalizedModule.mkLinearMap (cechSub f {j}) _
          (localOfSection S f C N X h i ((C.canonicalLocal N i).symm _))) = _
        rw [localOfSection_apply]
        change _ = localizedMap f {i} lj ((C.canonical.obj N).alphaIJ i j
          (LocalizedModule.mkLinearMap (cechSub f {j}) _ ((C.canonicalLocal N i).symm _)))
        rw [constructionCanonicalAlphaIJ_mk]
        erw [localizedMap_mk]
        change _ = LocalizedModule.mkLinearMap (cechSub f {i}) _
          (localOfSection S f C N X h j ((C.canonicalLocal N j).symm _))
        rw [localOfSection_apply]
        exact ((C.sectionsObj X) (h n)).2.2 i j
    exact DFunLike.congr_fun hh m

private noncomputable abbrev sectionsHom
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (X : ModuleGlueingDatum S f C.comparison)
    (g : C.canonical.obj N ⟶ X) : N ⟶ C.sections.obj X :=
  C.canonicalSectionsUnit.app N ≫ C.sections.map g

private theorem sectionsHom_generic
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (X : ModuleGlueingDatum S f C.comparison)
    (g : C.canonical.obj N ⟶ X) (n : N) :
    (C.sectionsObj X (sectionsHom S f C N X g n)).1.1 =
      (C.homEquiv _ _ g).generic ((C.canonicalGeneric N).symm (1 ⊗ₜ[R] n)) := by
  show (C.sectionsObj X (C.sections.map g (C.canonicalSectionsUnit.app N n))).1.1 = _
  rw [C.sectionsMapGeneric]
  congr 1
  apply (C.canonicalGeneric N).injective
  rw [C.canonicalSectionsUnit_generic, LinearEquiv.apply_symm_apply]

private theorem sectionsHom_local
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (X : ModuleGlueingDatum S f C.comparison)
    (g : C.canonical.obj N ⟶ X) (n : N) (i : Fin r) :
    (C.sectionsObj X (sectionsHom S f C N X g n)).1.2 i =
      (C.homEquiv _ _ g).localPiece i ((C.canonicalLocal N i).symm
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N n)) := by
  show (C.sectionsObj X (C.sections.map g (C.canonicalSectionsUnit.app N n))).1.2 i = _
  rw [C.sectionsMapLocal]
  congr 1
  apply (C.canonicalLocal N i).injective
  rw [C.canonicalSectionsUnit_local, LinearEquiv.apply_symm_apply]

private theorem sectionsHom_injective
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (X : ModuleGlueingDatum S f C.comparison) :
    Function.Injective (sectionsHom S f C N X) := by
  intro g h eq
  apply (C.homEquiv _ _).injective
  apply ModuleGlueingMap.ext
  · apply ModuleCat.hom_ext
    apply tensor_ext (C.canonicalGeneric N)
    intro n
    exact (sectionsHom_generic S f C N X g n).symm.trans
      ((congrArg (fun k : N ⟶ C.sections.obj X ↦ (C.sectionsObj X (k n)).1.1) eq).trans
        (sectionsHom_generic S f C N X h n))
  · funext i
    let : Module R ((C.canonical.obj N).localPiece i) :=
      Module.compHom _ (algebraMap R (Localization.Away (f i)))
    let gi := ((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map ((C.homEquiv _ _ g).localPiece i)).hom
    let hi := ((ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map ((C.homEquiv _ _ h).localPiece i)).hom
    have hh : gi = hi := by
      apply localized_ext (Submonoid.powers (f i))
        (restrictAwayLinearEquiv f i (C.canonicalLocal N i))
      · exact isUnit_end_restrictFromAway f i (X.localPiece i)
      · intro n
        exact (sectionsHom_local S f C N X g n i).symm.trans
          ((congrArg (fun k : N ⟶ C.sections.obj X ↦ (C.sectionsObj X (k n)).1.2 i) eq).trans
            (sectionsHom_local S f C N X h n i))
    apply ModuleCat.hom_ext
    ext m
    exact DFunLike.congr_fun hh m

private theorem sectionsHom_glueMapOfSection
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (X : ModuleGlueingDatum S f C.comparison)
    (h : N ⟶ C.sections.obj X) :
    sectionsHom S f C N X ((C.homEquiv _ _).symm (glueMapOfSection S f C N X h)) = h := by
  apply ModuleCat.hom_ext
  ext n
  apply (C.sectionsObj X).injective
  apply Subtype.ext
  apply Prod.ext
  · rw [sectionsHom_generic, Equiv.apply_symm_apply]
    exact genericOfSection_apply S f C N X h n
  · funext i
    rw [sectionsHom_local, Equiv.apply_symm_apply]
    exact localOfSection_apply S f C N X h i n

private noncomputable def homEquiv
    (C : ModuleGlueingConstruction.{u, v, w} S f)
    (N : ModuleCat.{max u v w} R) (X : ModuleGlueingDatum S f C.comparison) :
    (C.canonical.obj N ⟶ X) ≃ (N ⟶ C.sections.obj X) where
  toFun := sectionsHom S f C N X
  invFun h := (C.homEquiv _ _).symm (glueMapOfSection S f C N X h)
  left_inv g := sectionsHom_injective S f C N X
    (sectionsHom_glueMapOfSection S f C N X (sectionsHom S f C N X g))
  right_inv := sectionsHom_glueMapOfSection S f C N X

/-- The compatible-sections functor `H⁰` on module glueing data is right adjoint to the canonical
glueing-data functor. -/
@[stacks 0H77]
public noncomputable def canonicalSectionsAdjunction
    {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R)
    (C : FormalGlueing.ModuleGlueingConstruction.{u, v, w} S f) :
    letI := C.category
    C.canonical ⊣ C.sections := by
  letI := C.category
  exact Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv S f C
      homEquiv_naturality_left_symm := by
        intro N' N X a b
        apply (homEquiv S f C N' X).injective
        rw [Equiv.apply_symm_apply]
        change a ≫ b = C.canonicalSectionsUnit.app N' ≫
          C.sections.map (C.canonical.map a ≫ (homEquiv S f C N X).symm b)
        rw [C.sections.map_comp, ← Category.assoc]
        have hn := C.canonicalSectionsUnit.naturality a
        change a ≫ C.canonicalSectionsUnit.app N =
          C.canonicalSectionsUnit.app N' ≫ C.sections.map (C.canonical.map a) at hn
        rw [← hn]
        rw [Category.assoc]
        exact congrArg (fun k ↦ a ≫ k) ((homEquiv S f C N X).apply_symm_apply b).symm
      homEquiv_naturality_right := by
        intro N X Y a b
        change C.canonicalSectionsUnit.app N ≫ C.sections.map (a ≫ b) =
          (C.canonicalSectionsUnit.app N ≫ C.sections.map a) ≫ C.sections.map b
        rw [C.sections.map_comp, Category.assoc] }

end FormalGlueing

end

end
