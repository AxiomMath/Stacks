module

public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.BaseChangeComplexIso
public import StacksFrontier.AlgebraicGeometry.DerivedIso.LerayOpenCover
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.ModuleComplexRefinementMap
public import StacksFrontier.CategoryTheory.Sites.CechComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology and base change for the relative Čech complex ([Stacks, Tag 01XM])

For a cartesian square
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `X` and `S` of affine diagonal, a finite affine open cover `𝒰 : X = ⋃ Uᵢ` and a
quasi-coherent `𝒪_X`-module `ℱ`, with `ℱ' = (g')^*ℱ`:

* `baseChangeRelativeCechIsoDerivedPushforward`: `g^* Č ⁼(𝒰, f, ℱ) ≅ Rf'_*ℱ'` in `D⁺(S')`;
* `baseChangeRelativeCechComplexIsoOfIsAffineHom`: for affine `g`,
  `g^* Č ⁼(𝒰, f, ℱ) ≅ Č ⁼(𝒰', f', ℱ')` as complexes, where `U'ᵢ = (g')^{-1}(Uᵢ)` is affine.

Termwise, `g^*` of the coefficient `(a ≫ f)_* a^* ℱ` at a finite intersection `a : A ⟶ X` is
identified with `(a' ≫ f')_* a'^* ℱ'` at `A' = A ×_X X'` by the base change morphism of
[Stacks, Tag 02KG], which is invertible because `A ⟶ S` is affine
(`isIso_coefficientPullback_app`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.RelativeCechBaseChange

open Stacks.AlgebraicGeometry.RelativeCech

variable {X X' S S' : Scheme.{u}}

/-! ### The counit of `Over.map g' ⊣ Over.pullback g'` -/

/-- The projections `A ×_X X' ⟶ A`, as a natural transformation
`Over.pullback g' ⋙ Over.map g' ⟶ 𝟭`. -/
@[simps]
noncomputable def pullbackCounit (g' : X' ⟶ X) :
    Over.pullback g' ⋙ Over.map g' ⟶ 𝟭 (Over X) where
  app A := Over.homMk (pullback.fst A.hom g') (by simp [pullback.condition])
  naturality A B φ := by
    ext
    exact pullback.lift_fst _ _ _

/-- **The base change map of coefficient presheaves is invertible at an object `A` of `Over X`
with `A ⟶ X ⟶ S` affine**, for a cartesian square and a quasi-coherent module: it is the base
change morphism of [Stacks, Tag 02KG] for the cartesian square `A ×_X X' ⟶ A` over `S' ⟶ S`. -/
@[ega "III 7.7.2" "special case"]
theorem isIso_coefficientPullback_app {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hw : IsPullback g' f' f g) (M : X.Modules) [M.IsQuasicoherent] (A : Over X)
    [IsAffineHom (A.hom ≫ f)] :
    IsIso ((coefficientPullback hw.w (pullbackCounit g') M).app (op A)) := by
  have hsq : IsPullback ((pullbackCounit g').app A).left
      (((Over.pullback g').obj A).hom ≫ f') (A.hom ≫ f) g :=
    (IsPullback.of_hasPullback A.hom g').paste_vert hw
  have hm : (((Over.pullback g').obj A).hom ≫ g') ≫ f =
      (((Over.pullback g').obj A).hom ≫ f') ≫ g := by
    rw [Category.assoc, hw.w, Category.assoc]
  exact isIso_coefficientPullback_app_of hw.w (pullbackCounit g') M A hm hsq.w
    (AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsq
      ((Scheme.Modules.pullback A.hom).obj M))


/-! ### The Čech complexes -/

section Complex

open Stacks.AlgebraicGeometry.RelativeCechComplex

variable {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- The cover `X' = ⋃ U'ᵢ` of [Stacks, Tag 01XM], `U'ᵢ = Uᵢ ×_X X'`, as an open cover of `X'`
indexed by the same set. -/
noncomputable abbrev baseChangeCover (g' : X' ⟶ X) (T : X.AffineOpenCover.{u, u}) :
    X'.OpenCover.{u} :=
  T.openCover.pullback₂ g'

/-- The base change cover has the index set of the original cover. -/
noncomputable instance (g' : X' ⟶ X) (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀] :
    Fintype (baseChangeCover g' T).I₀ :=
  inferInstanceAs (Fintype T.I₀)

/-- The members of the base change cover are the images of the members of the original cover
under `Over.pullback g'`. -/
noncomputable def baseChangeCoverIso (g' : X' ⟶ X) (T : X.AffineOpenCover.{u, u}) (i : T.I₀) :
    (Over.pullback g').obj (Over.mk (T.f i)) ≅ Over.mk ((baseChangeCover g' T).f i) :=
  Over.isoMk (Iso.refl _) (Category.id_comp _)

/-- The finite intersections of the members of an affine open cover are affine schemes. -/
private theorem isAffine_left_pi_mk [IsAffineHom (pullback.diagonal (terminal.from X))]
    (T : X.AffineOpenCover.{u, u}) {n : ℕ} (x : Fin (n + 1) → T.I₀) :
    IsAffine (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X)).left := by
  have hoi : ∀ a, IsOpenImmersion (Over.mk (T.f (x a)) : Over X).hom :=
    fun a ↦ inferInstanceAs (IsOpenImmersion (T.f (x a)))
  have hfa : ∀ a, IsAffine (Over.mk (T.f (x a)) : Over X).left :=
    fun a ↦ inferInstanceAs (IsAffine (Spec (T.X (x a))))
  exact isAffine_left_pi _

variable (hw : IsPullback g' f' f g) (T : X.AffineOpenCover.{u, u}) [Fintype T.I₀]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))]
  (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)

omit [Fintype T.I₀] in
/-- The finite intersections of the members of an affine open cover of `X` have affine structure
morphism to `X`. -/
theorem isAffineHom_pi_hom {n : ℕ} (x : Fin (n + 1) → T.I₀) :
    IsAffineHom (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X)).hom := by
  have := isAffine_left_pi_mk T x
  exact isAffineHom_of_isAffine_source _

omit [Fintype T.I₀] in
/-- The finite intersections of the members of an affine open cover of `X` are affine over `S`. -/
theorem isAffineHom_pi_hom_comp {n : ℕ} (x : Fin (n + 1) → T.I₀) :
    IsAffineHom ((∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X)).hom ≫ f) := by
  have := isAffine_left_pi_mk T x
  exact isAffineHom_of_isAffine_source _

omit [Fintype T.I₀] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))] in
/-- The underlying module of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_qcohModule : (qcohModule F).IsQuasicoherent :=
  F.property

omit [Fintype T.I₀] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))] in
include hw in
/-- The base change map of coefficient presheaves of a quasi-coherent module is invertible at an
object `A` of `Over X` with `A ⟶ X ⟶ S` affine. -/
theorem isIso_coefficientPullback_qcohModule_app (A : Over X) [IsAffineHom (A.hom ≫ f)] :
    IsIso ((coefficientPullback hw.w (pullbackCounit g') (qcohModule F)).app (op A)) := by
  have := isQuasicoherent_qcohModule F
  exact isIso_coefficientPullback_app hw (qcohModule F) A

omit [Fintype T.I₀] in
include hw in
/-- The base change map of coefficient presheaves is invertible at the finite intersections of the
members of the cover. -/
theorem isIso_coefficientPullback_qcohModule_app_pi (n : ℕ) (x : Fin (n + 1) → T.I₀) :
    IsIso ((coefficientPullback hw.w (pullbackCounit g') (qcohModule F)).app
      (op (∏ᶜ fun a ↦ (fun i ↦ (Over.mk (T.f i) : Over X)) (x a)))) := by
  have : IsAffineHom ((∏ᶜ fun a ↦ (fun i ↦ (Over.mk (T.f i) : Over X)) (x a)).hom ≫ f) :=
    isAffineHom_pi_hom_comp (f := f) T x
  exact isIso_coefficientPullback_qcohModule_app hw F _

omit [Fintype T.I₀] in
include hw in
/-- **The map of Čech complexes induced by base change is an isomorphism.** -/
theorem isIso_cechMapPullback :
    IsIso ((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).map
      (coefficientPullback hw.w (pullbackCounit g') (qcohModule F))) :=
  isIso_cechComplexFunctor_map _ _ (isIso_coefficientPullback_qcohModule_app_pi hw T F)

/-- The quasi-coherent `𝒪_{X'}`-module `ℱ' = (g')^*ℱ`. -/
noncomputable def pullbackQcohObj (g' : X' ⟶ X)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent X'.ringCatSheaf).FullSubcategory :=
  (Stacks.Modules.pullbackQcoh g').obj F

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- The underlying module of `(g')^*ℱ` is the inverse image of the underlying module of `ℱ`. -/
theorem pullbackQcohObj_obj (g' : X' ⟶ X)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (pullbackQcohObj g' F).obj = (Scheme.Modules.pullback g').obj F.obj :=
  rfl

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- The `qcohModule` of `(g')^*ℱ` is the inverse image of the `qcohModule` of `ℱ`. -/
theorem qcohModule_pullbackQcohObj (g' : X' ⟶ X)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    qcohModule (pullbackQcohObj g' F) = (Scheme.Modules.pullback g').obj (qcohModule F) :=
  rfl

include hw in
/-- **The inverse image of the relative Čech complex is the relative Čech complex of the base
change cover**, as `ℕ`-indexed complexes. -/
noncomputable def cechBaseChangeIso :
    ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).obj
          ((relativeCechPresheaf f).obj F)) ≅
      (cechComplexFunctor fun i ↦ (Over.mk ((baseChangeCover g' T).f i) : Over X')).obj
        ((relativeCechPresheaf f').obj (pullbackQcohObj g' F)) :=
  haveI := isIso_cechMapPullback hw T F
  haveI : ∀ n : ℕ, PreservesLimit (Discrete.functor fun x : Fin (n + 1) → T.I₀ ↦
      ((relativeMonad X).flip.obj (qcohModule F) ⋙ Scheme.Modules.pushforward f).obj
        (op (Stacks.CategoryTheory.CechComplex.inter (fun i ↦ (Over.mk (T.f i) : Over X)) x)))
      (Scheme.Modules.pullback g) := fun _ ↦ inferInstance
  ((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (cechRelativeCechPresheafIso f F fun i ↦ (Over.mk (T.f i) : Over X)) ≪≫
    Stacks.CategoryTheory.CechComplex.coefficientsIso (fun i ↦ (Over.mk (T.f i) : Over X))
      ((relativeMonad X).flip.obj (qcohModule F) ⋙ Scheme.Modules.pushforward f)
      (Scheme.Modules.pullback g) ≪≫
    asIso ((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).map
      (coefficientPullback hw.w (pullbackCounit g') (qcohModule F))) ≪≫
    (cechSiteIsoObj (fun i ↦ (Over.mk (T.f i) : Over X)) (Over.pullback g')
      ((relativeMonad X').flip.obj ((Scheme.Modules.pullback g').obj (qcohModule F)) ⋙
        Scheme.Modules.pushforward f')).symm ≪≫
    (Stacks.CechSiteChange.cechComplexFunctorIsoOfFamilyIso
      (U := fun i ↦ (Over.pullback g').obj ((fun i ↦ (Over.mk (T.f i) : Over X)) i))
      (U' := fun i ↦ (Over.mk ((baseChangeCover g' T).f i) : Over X'))
      (baseChangeCoverIso g' T)).app
      ((relativeMonad X').flip.obj ((Scheme.Modules.pullback g').obj (qcohModule F)) ⋙
        Scheme.Modules.pushforward f') ≪≫
    (cechRelativeCechPresheafIsoOfEq f' (pullbackQcohObj g' F)
      (fun i ↦ (Over.mk ((baseChangeCover g' T).f i) : Over X'))
      ((Scheme.Modules.pullback g').obj (qcohModule F)) (qcohModule_pullbackQcohObj g' F)).symm

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))] in
/-- The underlying `ℤ`-indexed complex of the relative Čech complex. -/
theorem relativeCechComplex_obj_obj_extend :
    ((relativeCechComplex f T).obj F).obj =
      ((cechComplexFunctor fun i ↦ (Over.mk (T.f i) : Over X)).obj
        ((relativeCechPresheaf f).obj F)).extend ComplexShape.embeddingUpNat :=
  rfl

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))] in
/-- The underlying `ℤ`-indexed complex of the relative Čech complex of the base change cover. -/
theorem relativeCechComplex_baseChangeCover_obj_obj_extend :
    ((RelativeCechOpenCover.relativeCechComplex f' (baseChangeCover g' T)).obj
        (pullbackQcohObj g' F)).obj =
      ((cechComplexFunctor fun i ↦ (Over.mk ((baseChangeCover g' T).f i) : Over X')).obj
        ((relativeCechPresheaf f').obj (pullbackQcohObj g' F))).extend
          ComplexShape.embeddingUpNat :=
  rfl

include hw in
/-- **The inverse image of the relative Čech complex is the relative Čech complex of the base
change cover**, as bounded below complexes of `𝒪_{S'}`-modules. -/
noncomputable def baseChangeRelativeCechComplexIso :
    (Scheme.Modules.pullback g).mapCochainComplexPlus.obj ((relativeCechComplex f T).obj F) ≅
      (RelativeCechOpenCover.relativeCechComplex f' (baseChangeCover g' T)).obj
        (pullbackQcohObj g' F) :=
  (CochainComplex.Plus.fullyFaithfulι S'.Modules).preimageIso
    (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (eqToIso (relativeCechComplex_obj_obj_extend T F)) ≪≫
      Stacks.DerivedIndexing.mapExtendIsoSymm (Scheme.Modules.pullback g)
        ComplexShape.embeddingUpNat _ ≪≫
      (ComplexShape.embeddingUpNat.extendFunctor S'.Modules).mapIso (cechBaseChangeIso hw T F) ≪≫
      eqToIso (relativeCechComplex_baseChangeCover_obj_obj_extend T F).symm)

omit [Fintype T.I₀] in
include hw in
/-- The finite intersections of the members of the base change cover are affine over `X'` and
over `S'`: they are base changes of the finite intersections of the members of the original
cover. -/
theorem isAffineHom_baseChangeCover_pi (n : ℕ) (x : Fin (n + 1) → T.I₀) :
    IsAffineHom (∏ᶜ fun a ↦ (Over.mk ((baseChangeCover g' T).f (x a)) : Over X')).hom ∧
      IsAffineHom ((∏ᶜ fun a ↦ (Over.mk ((baseChangeCover g' T).f (x a)) : Over X')).hom ≫
        f') := by
  have k₁ : IsAffineHom ((Over.pullback g').obj
      (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X))).hom :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X)).hom g')
      (isAffineHom_pi_hom T x)
  have k₂ : IsAffineHom (((Over.pullback g').obj
      (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X))).hom ≫ f') :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X)).hom g').paste_vert
        hw) (isAffineHom_pi_hom_comp (f := f) T x)
  let e : (∏ᶜ fun a ↦ (Over.mk ((baseChangeCover g' T).f (x a)) : Over X')) ≅
      (Over.pullback g').obj (∏ᶜ fun a ↦ (Over.mk (T.f (x a)) : Over X)) :=
    (Limits.Pi.mapIso fun a ↦ (baseChangeCoverIso g' T (x a)).symm) ≪≫
      (PreservesProduct.iso (Over.pullback g') _).symm
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget X').map e.hom))
  rw [← Over.w e.hom, Category.assoc]
  exact ⟨inferInstance, inferInstance⟩

/-- The value of a composite of three functors. -/
theorem comp_comp_obj {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* C₄] (A : C₁ ⥤ C₂) (B : C₂ ⥤ C₃) (C : C₃ ⥤ C₄) (Z : C₁) :
    (A ⋙ B ⋙ C).obj Z = C.obj (B.obj (A.obj Z)) :=
  rfl

include hw in
/-- **[Stacks, Tag 01XM], the canonical isomorphism.**  For a cartesian square
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
with `X` and `S` of affine diagonal, a finite affine open cover `𝒰` of `X` and a quasi-coherent
`𝒪_X`-module `ℱ`, there is a canonical isomorphism

`g^* Č ⁼(𝒰, f, ℱ) ≅ Rf'_* (g')^*ℱ`

in `D⁺(S')`: the termwise inverse image of the relative Čech complex is the relative Čech complex
of the cover `X' = ⋃ Uᵢ ×_X X'` (the base change map of [Stacks, Tag 02KG] on each finite
intersection), whose finite intersections are affine over `X'` and over `S'`, so that it computes
`Rf'_*` as in [Stacks, Tag 01XL]. -/
@[stacks 01XM "the canonical isomorphism"]
noncomputable def baseChangeRelativeCechIsoDerivedPushforward :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient S'.Modules).obj
        ((Scheme.Modules.pullback g).mapCochainComplexPlus.obj
          ((relativeCechComplex f T).obj F))) ≅
      (Scheme.Modules.pushforward f').rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X'.Modules 0).obj
          ((Scheme.Modules.pullback g').obj F.obj)) :=
  DerivedCategory.Plus.Qh.mapIso ((HomotopyCategory.Plus.quotient S'.Modules).mapIso
      (baseChangeRelativeCechComplexIso hw T F)) ≪≫
    eqToIso (comp_comp_obj (RelativeCechOpenCover.relativeCechComplex f' (baseChangeCover g' T))
      (HomotopyCategory.Plus.quotient S'.Modules) DerivedCategory.Plus.Qh
      (pullbackQcohObj g' F)).symm ≪≫
    (RelativeCechOpenCover.relativeCechIsoDerivedPushforward f' (baseChangeCover g' T)
      (isAffineHom_baseChangeCover_pi hw T)).app (pullbackQcohObj g' F) ≪≫
    eqToIso ((comp_comp_obj (ObjectProperty.ι (SheafOfModules.isQuasicoherent X'.ringCatSheaf))
      (DerivedCategory.Plus.singleFunctor X'.Modules 0)
      (Scheme.Modules.pushforward f').rightDerivedFunctorPlus (pullbackQcohObj g' F)).trans
      (congrArg (fun M ↦ (Scheme.Modules.pushforward f').rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X'.Modules 0).obj M))
        ((ObjectProperty.ι_obj _).trans (pullbackQcohObj_obj g' F))))

/-- For an affine `g'`, the members of the base change cover are the members of the inverse-image
affine open cover. -/
noncomputable def baseChangeCoverAffineIso [IsAffineHom g'] (i : (baseChangeCover g' T).I₀) :
    (Over.mk ((baseChangeCover g' T).f i) : Over X') ≅
      Over.mk ((inverseImageAffineOpenCover g' T).f i) :=
  Over.isoMk (pullback (T.f i) g').isoSpec (Iso.hom_inv_id_assoc _ _)

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from S))] in
/-- The underlying `ℤ`-indexed complex of the relative Čech complex of the inverse-image affine
open cover. -/
theorem relativeCechComplex_inverseImage_obj_obj_extend [IsAffineHom g'] :
    ((relativeCechComplex f' (inverseImageAffineOpenCover g' T)).obj (pullbackQcohObj g' F)).obj =
      ((cechComplexFunctor fun i : (baseChangeCover g' T).I₀ ↦
          (Over.mk ((inverseImageAffineOpenCover g' T).f i) : Over X')).obj
        ((relativeCechPresheaf f').obj (pullbackQcohObj g' F))).extend
          ComplexShape.embeddingUpNat :=
  rfl

include hw in
/-- **[Stacks, Tag 01XM], the affine case.**  For a cartesian square as in
`baseChangeRelativeCechIsoDerivedPushforward` with `g : S' ⟶ S` affine, the members
`U'ᵢ = (g')^{-1}(Uᵢ) = Uᵢ ×_X X'` of the inverse-image cover `𝒰'` are affine, and the termwise
inverse image of the relative Čech complex is the relative Čech complex of this affine open cover:

`g^* Č ⁼(𝒰, f, ℱ) ≅ Č ⁼(𝒰', f', (g')^*ℱ)`

as bounded below complexes of `𝒪_{S'}`-modules. -/
@[stacks 01XM "the affine case"]
noncomputable def baseChangeRelativeCechComplexIsoOfIsAffineHom [IsAffineHom g] :
    letI : IsAffineHom g' := MorphismProperty.of_isPullback hw.flip inferInstance
    (Scheme.Modules.pullback g).mapCochainComplexPlus.obj ((relativeCechComplex f T).obj F) ≅
      (relativeCechComplex f' (inverseImageAffineOpenCover g' T)).obj (pullbackQcohObj g' F) :=
  letI : IsAffineHom g' := MorphismProperty.of_isPullback hw.flip inferInstance
  baseChangeRelativeCechComplexIso hw T F ≪≫
    (CochainComplex.Plus.fullyFaithfulι S'.Modules).preimageIso
      (eqToIso (relativeCechComplex_baseChangeCover_obj_obj_extend T F) ≪≫
        (ComplexShape.embeddingUpNat.extendFunctor S'.Modules).mapIso
          ((Stacks.CechSiteChange.cechComplexFunctorIsoOfFamilyIso
            (U := fun i : (baseChangeCover g' T).I₀ ↦
              (Over.mk ((baseChangeCover g' T).f i) : Over X'))
            (U' := fun i : (baseChangeCover g' T).I₀ ↦
              (Over.mk ((inverseImageAffineOpenCover g' T).f i) : Over X'))
            (baseChangeCoverAffineIso T)).app
            ((relativeCechPresheaf f').obj (pullbackQcohObj g' F))) ≪≫
        eqToIso (relativeCechComplex_inverseImage_obj_obj_extend T F).symm)

end Complex

end Stacks.AlgebraicGeometry.RelativeCechBaseChange

end
