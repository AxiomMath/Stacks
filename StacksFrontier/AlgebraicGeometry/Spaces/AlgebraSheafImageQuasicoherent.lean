module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Sheaf
public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Transport
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.UnderImages
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence

/-!
# The image of a morphism of quasi-coherent algebra sheaves on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  This file
proves that the image of a morphism of quasi-coherent sheaves of `𝒪_F`-algebras on the small
étale site is again quasi-coherent, and of finite type when the source is; and it deduces that
the finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf form a **nonempty**
category.

Nonemptiness is the first thing the directedness assertion of Stacks 082B needs, and it was the
missing one: the canonical morphism `𝒪_F ⟶ A` is of finite type and quasi-coherent at the
source, but it is **not** a monomorphism — the structure-algebra map of a quotient algebra is not
injective — so it exhibits no subobject of `A`.  Its image does, and that is what is built here.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleFunctor`: the underlying `𝒪_F`-module of
  an algebra sheaf, as a functor.  `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` was
  defined on objects only.
* `AlgebraicGeometry.Space.AlgebraSheaf.monoFactorisation` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isImage`: the image of a morphism of algebra sheaves,
  computed on the underlying sheaves of commutative rings.
* `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleImageIso`: **the underlying module of the
  image is the image of the underlying morphism of modules.**

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_image_unconditional`: the image of a morphism of
  quasi-coherent `𝒪_F`-modules is quasi-coherent, with the kernel- and cokernel-closure
  hypotheses of `AlgebraicGeometry.Space.isQuasicoherentOnSite_image` discharged.
* `AlgebraicGeometry.Space.AlgebraSheaf.isLocallySurjective_factorThruImage_right`: the
  corestriction to the image of a morphism of algebra sheaves is locally surjective on underlying
  sheaves of rings.
* `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_image`: **the image of a morphism of
  quasi-coherent algebra sheaves is quasi-coherent.**
* `AlgebraicGeometry.Space.AlgebraSheaf.isFiniteType_image`: **the image of a morphism of
  quasi-coherent algebra sheaves whose source is of finite type is of finite type.**
* `AlgebraicGeometry.Space.nonempty_finiteTypeSubalgebra_of_isQuasicoherent`: **the finite type
  quasi-coherent subalgebras of a quasi-coherent algebra sheaf are nonempty**, unconditionally.
* `AlgebraicGeometry.Space.nonempty_finiteTypeSubalgebra_integralClosureSheaf_unitAlgebra`: the
  same at a concrete algebra sheaf and with no hypothesis at all.
* `AlgebraicGeometry.Space.isFiltered_finiteTypeSubalgebra_of_exists_sup`: the directedness
  assertion of Stacks 082B reduced to the existence of upper bounds alone.

## Implementation notes

**Where the strength comes from.**  Finiteness of type of the image is
`AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType.of_surjective_app` applied to the
corestriction `𝒪_F ⟶ image φ`, and that needs the corestriction to be **surjective** on the
sections over an affine étale chart.  Only *local* surjectivity is formal: the image of a
morphism of sheaves of rings is the sheafification of the presheaf image, so the sheaf-level
corestriction is not surjective on sections.  The passage from local surjectivity to surjectivity
over an affine chart is the content of Descent, Proposition 03DW, and it is supplied here by
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`
(`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent`), which is
unconditional — faithfully flat descent along a finite affine étale refinement, with **no Čech
cohomology**.  That is the one input this file could not have had before.

**The identification of the image.**  The image of `φ` in algebra sheaves is a sheafification, so
its underlying module is not visibly an image of anything.  What makes
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleImageIso` available is that the two legs of
the factorisation have the right properties after passing to modules — the corestriction becomes
an epimorphism, the inclusion a monomorphism — and that `𝒪_F`-modules form a balanced category,
so an epi-mono factorisation there *is* the image.  The comparison is
`CategoryTheory.Limits.image.lift` of the explicit factorisation and
`CategoryTheory.isIso_of_mono_of_epi`, which is not an instance and is invoked by hand.

**Quasi-coherence of the image at the module level needs no hypothesis.**  In an abelian category
the image is the kernel of the cokernel projection, and on the small étale site quasi-coherence is
closed under cokernels unconditionally
(`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`) and under kernels
unconditionally (`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale`,
whose own `h03DX` is Descent, Proposition 03DX(2)).

**`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is removed where the abelian structure is
used.**  That instance states the abelian structure of `SheafOfModules.{max u v r w}`, whose
module universe cannot be the `u` of `AlgebraicGeometry.Space.Modules.{u, u}`; left in place it is
selected ahead of Mathlib's `SheafOfModules.instAbelian` and the elaboration dies with
`stuck at solving universe constraint u =?= max (u + 1) ?u`.  The two agree where both apply.

**No `@[stacks 082B]` attribute is claimed.**  Stacks 082B asserts that the finite type
quasi-coherent subalgebras are *directed* and that `A` is their colimit.  This file supplies
nonemptiness only.  The existence of upper bounds needs the identification of the sections of a
coproduct of algebra sheaves over an affine chart with the tensor product of the sections, which
is undischarged in this tree — including in the scheme case, where the other two inputs are
proved; see `StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebraJoin/Directedness.lean`.  A
generators argument does not avoid it: the generators live in the sections of `C` and of `D`,
and what has to be bounded is the sections of `C ⨿ D`.

## References

* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Quasi-coherence of the image of a morphism of modules -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The image of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent**, with no
hypothesis beyond quasi-coherence of the source and target.

This is `AlgebraicGeometry.Space.isQuasicoherentOnSite_image` — which asks for closure of
quasi-coherence under kernels and cokernels as hypotheses — with those two discharged on the
small étale site, and read on the `CategoryTheory.image` spelling rather than the
`imageSubobject` one.  No second proof of the image computation is given here: the closure
properties are supplied to the library lemma and its conclusion is transported along
`imageSubobjectIso`. -/
theorem isQuasicoherentOnSite_image_unconditional {M N : Modules.{u, u} B S hS F hF}
    (f : M ⟶ N) (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (image f).IsQuasicoherentOnSite :=
  ObjectProperty.prop_of_iso _ (imageSubobjectIso f)
    (isQuasicoherentOnSite_image B S hS F hF
      (isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS F hF)
      (isClosedUnderCokernels_quasicoherentSheaves B S hS F hF) f hM hN)

namespace AlgebraSheaf

variable {B S hS F hF}

/-! ### The underlying module of an algebra sheaf, as a functor -/

/-- Sectionwise naturality of the morphism of sheaves of rings underlying a morphism of algebra
sheaves. -/
theorem app_map {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    {U V : (SmallEtale B S hS F)ᵒᵖ} (i : U ⟶ V) (x : A.right.obj.obj U) :
    f.right.hom.app V (A.right.obj.map i x) = C.right.obj.map i (f.right.hom.app U x) :=
  congrArg (fun φ : A.right.obj.obj U ⟶ C.right.obj.obj V => φ.hom x)
    (f.right.hom.naturality i)

/-- Sectionwise `𝒪_F`-linearity of a morphism of algebra sheaves, written out as a statement
about the multiplication of the sheaves of rings rather than about the restricted scalar actions:
the two coincide because the module structure on the sections of the underlying module is
`Module.compHom` along the structure-algebra map. -/
theorem app_mul_algebraMap {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) (r : (structureSheaf B S hS F hF).obj.obj U)
    (x : A.right.obj.obj U) :
    f.right.hom.app U (A.algebraMap U r * x) = C.algebraMap U r * f.right.hom.app U x := by
  rw [map_mul, f.comm]

/-- The sections of a morphism of algebra sheaves over an étale chart, as an `𝒪_F(U)`-linear map
between the sections of the underlying modules. -/
noncomputable def underlyingModuleLinear {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) :
    (underlyingModule A).val.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O).obj.obj U] (underlyingModule C).val.obj U where
  toFun x := (f.right.hom.app U).hom x
  map_add' x y := map_add (f.right.hom.app U).hom x y
  map_smul' r x := app_mul_algebraMap f U r x

/-- The morphism of underlying presheaves of modules induced by a morphism of algebra sheaves:
sectionwise `underlyingModuleLinear`, natural by naturality of the underlying morphism of sheaves
of rings. -/
noncomputable def underlyingModuleValMap {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    (underlyingModule A).val ⟶ (underlyingModule C).val where
  app U := ConcreteCategory.ofHom
    (C := ModuleCat
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj.obj U))
    (underlyingModuleLinear f U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    exact app_map f i x

/-- On sections, the morphism of underlying presheaves of modules is the underlying morphism of
sheaves of rings. -/
@[simp]
theorem underlyingModuleValMap_app_apply {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x : (underlyingModule A).val.obj U) :
    (underlyingModuleValMap f).app U x = f.right.hom.app U x :=
  rfl

/-- The morphism of underlying `𝒪_F`-modules induced by a morphism of algebra sheaves. -/
noncomputable def underlyingModuleMap {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C) :
    underlyingModule A ⟶ underlyingModule C :=
  show SheafOfModules.Hom _ _ from { val := underlyingModuleValMap f }

/-- On sections, the morphism of underlying `𝒪_F`-modules is the underlying morphism of sheaves
of rings. -/
@[simp]
theorem underlyingModuleMap_app_apply {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) (x : (underlyingModule A).val.obj U) :
    (underlyingModuleMap f).val.app U x = f.right.hom.app U x :=
  rfl

/-- **The underlying `𝒪_F`-module of an algebra sheaf, as a functor.**  The module is the
algebra's own sheaf of sections with scalars restricted along the structure-algebra maps, and a
morphism of algebra sheaves is linear for those restricted actions because it is a ring map
commuting with the structure-algebra maps. -/
noncomputable def underlyingModuleFunctor :
    AlgebraSheaf.{u, m} B S hS F hF ⥤ Modules.{u, m} B S hS F hF where
  obj A := underlyingModule A
  map f := underlyingModuleMap f
  map_id _ := SheafOfModules.hom_ext <|
    PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  map_comp _ _ := SheafOfModules.hom_ext <|
    PresheafOfModules.hom_ext fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- **The underlying morphism of modules of a monomorphism of algebra sheaves is a
monomorphism.**  A monomorphism of algebra sheaves is injective on sections, and the sections of
the morphism of underlying modules are the same functions. -/
theorem mono_underlyingModuleMap_of_mono {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (hf : Mono f) : Mono (underlyingModuleMap f) :=
  have := hf
  have : (SheafOfModules.forget.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).Faithful :=
    (SheafOfModules.fullyFaithfulForget _).faithful
  have hinj : ∀ ⦃U : (SmallEtale B S hS F)ᵒᵖ⦄,
      Function.Injective ((underlyingModuleValMap f).app U) :=
    fun U => injective_app_of_mono f U
  (SheafOfModules.forget.{m} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O)).mono_of_mono_map
    (PresheafOfModules.mono_of_injective hinj)

/-- **A locally surjective morphism of algebra sheaves induces an epimorphism of underlying
`𝒪_F`-modules.**  The morphism of underlying modules has the same sections and the same functions
on sections as the underlying morphism of sheaves of rings, hence the same image sieves; for
sheaves of modules local surjectivity is the same thing as being an epimorphism. -/
theorem epi_underlyingModuleMap_of_isLocallySurjective
    {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (hf : Sheaf.IsLocallySurjective f.right) :
    Epi (underlyingModuleMap f) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun s => hf.imageSieve_mem s⟩

/-! ### Isomorphism invariance -/

/-- The underlying morphism of sheaves of rings of an isomorphism of algebra sheaves is an
isomorphism. -/
private theorem isIso_hom_right {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C) :
    IsIso e.hom.right :=
  inferInstanceAs (IsIso ((forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF)).map e.hom))

/-- The sections of an isomorphism of algebra sheaves over a chart are bijective: the forgetful
functor to sheaves of rings carries the isomorphism to one, and an isomorphism of sheaves is an
isomorphism at every object. -/
theorem bijective_iso_right_app {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C)
    (U : (SmallEtale B S hS F)ᵒᵖ) : Function.Bijective ((e.hom.right.hom.app U).hom) := by
  have h1 := isIso_hom_right e
  have h2 : IsIso e.hom.right.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf (SmallEtale.topology B S hS F)
      CommRingCat.{m}).map e.hom.right))
  have h3 : IsIso (e.hom.right.hom.app U) := NatIso.isIso_app_of_isIso _ U
  exact ConcreteCategory.bijective_of_isIso _

/-- **Finite type is invariant under isomorphism of algebra sheaves**: the sections of an
isomorphism are surjective, so
`AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType.of_surjective_app` applies. -/
theorem IsFiniteType.of_iso {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C)
    (hA : A.IsFiniteType) : C.IsFiniteType :=
  IsFiniteType.of_surjective_app e.hom (fun U _ => (bijective_iso_right_app e (op U)).2) hA

/-- **Quasi-coherence is invariant under isomorphism of algebra sheaves**: the underlying modules
are isomorphic, by `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleFunctor`. -/
theorem IsQuasicoherent.of_iso {A C : AlgebraSheaf.{u, m} B S hS F hF} (e : A ≅ C)
    (hA : A.IsQuasicoherent) : C.IsQuasicoherent :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (underlyingModuleFunctor.mapIso e) hA

/-- Quasi-coherence of algebra sheaves, as an object property closed under isomorphism.  This is
`AlgebraicGeometry.Space.AlgebraSheaf.IsQuasicoherent.of_iso` registered for instance search,
which is what cuts an equivalence of categories of algebra sheaves down to the quasi-coherent
ones. -/
instance isClosedUnderIsomorphisms_isQuasicoherent :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsQuasicoherent : ObjectProperty (AlgebraSheaf.{u, m} B S hS F hF)) where
  of_iso e hA := IsQuasicoherent.of_iso e hA

/-! ### The image of a morphism of algebra sheaves, computed on underlying rings -/

noncomputable section

/-- A mono factorisation of a morphism of algebra sheaves, read as a mono factorisation of the
underlying morphism of sheaves of commutative rings. -/
@[reducible]
def rightMonoFactorisation {A C : AlgebraSheaf.{u, u} B S hS F hF} {φ : A ⟶ C}
    (F' : MonoFactorisation φ) : MonoFactorisation φ.right where
  I := F'.I.right
  m := F'.m.right
  m_mono := by
    have := F'.m_mono
    exact mono_right_of_mono F'.m
  e := F'.e.right
  fac := congrArg Hom.right F'.fac

/-- The factorisation of a morphism of algebra sheaves through the image of its underlying
morphism of sheaves of rings, made an algebra sheaf by the composite of the structure-algebra map
with the corestriction. -/
@[reducible]
def monoFactorisation {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C) :
    MonoFactorisation φ :=
  haveI := hasImages_sheafSmallEtale B S hS F
  { I := ofHom (A.hom ≫ factorThruImage φ.right)
    m :=
      { right := image.ι φ.right
        comm := fun U r => by
          change ((factorThruImage φ.right ≫ image.ι φ.right).hom.app U)
            (A.algebraMap U r) = _
          rw [image.fac]
          exact φ.comm U r }
    m_mono := Functor.mono_of_mono_map
      (forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF))
      (show Mono (image.ι φ.right) from inferInstance)
    e :=
      { right := factorThruImage φ.right
        comm := fun _ _ => rfl }
    fac := Hom.ext (image.fac φ.right) }

/-- **The image of a morphism of algebra sheaves is the image of its underlying morphism of
sheaves of commutative rings.** -/
def isImage {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C) :
    IsImage (monoFactorisation φ) :=
  haveI := hasImages_sheafSmallEtale B S hS F
  { lift := fun F' =>
      { right := image.lift (rightMonoFactorisation F')
        comm := fun U r => by
          change ((factorThruImage φ.right ≫ image.lift (rightMonoFactorisation F')).hom.app U)
            (A.algebraMap U r) = _
          rw [image.fac_lift]
          exact F'.e.comm U r }
    lift_fac := fun F' => Hom.ext (image.lift_fac (rightMonoFactorisation F')) }

end

/-- **The corestriction to the image of a morphism of algebra sheaves on the small étale site of
an algebraic space is locally surjective** on underlying sheaves of commutative rings: the image
is computed on underlying sheaves, where it is the sheafification of the presheaf image.

Only the *local* statement is available, and that is not a defect of the proof: the sheaf-level
corestriction factors through a sheafification and is genuinely not surjective on sections. -/
theorem isLocallySurjective_factorThruImage_right
    {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C) :
    Sheaf.IsLocallySurjective (factorThruImage φ).right := by
  have := hasImages_sheafSmallEtale B S hS F
  have h : (monoFactorisation φ).e ≫ (IsImage.isoExt (isImage φ) (Image.isImage φ)).hom
      = factorThruImage φ := IsImage.e_isoExt_hom _ _
  have hr : factorThruImage φ.right
      ≫ (IsImage.isoExt (isImage φ) (Image.isImage φ)).hom.right
      = (factorThruImage φ).right := congrArg Hom.right h
  have ha := Stacks.AlgebraImageSurjective.sheaf_isLocallySurjective_of_isIso
    (SmallEtale.topology B S hS F) _
    (isIso_hom_right (IsImage.isoExt (isImage φ) (Image.isImage φ)))
  exact Stacks.AlgebraImageSurjective.sheaf_isLocallySurjective_of_fac
    (SmallEtale.topology B S hS F) hr
    (Stacks.AlgebraImageSurjective.sheaf_isLocallySurjective_factorThruImage
      (SmallEtale.topology B S hS F) φ.right
      (Stacks.AlgebraImageSurjective.presheaf_isLocallySurjective_factorThruImage
        (SmallEtale.topology B S hS F) φ.right.hom)) ha

/-! ### The underlying module of the image is the image of the underlying module map -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The underlying `𝒪_F`-module of the image of a morphism of algebra sheaves is the image of
the underlying morphism of modules.**

The corestriction to the image is locally surjective, hence an epimorphism of underlying modules;
the inclusion of the image is a monomorphism of algebra sheaves, hence a monomorphism of
underlying modules; and `𝒪_F`-modules are balanced, so this epi-mono factorisation is the
image. -/
noncomputable def underlyingModuleImageIso {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C) :
    image (underlyingModuleMap φ) ≅ underlyingModule (image φ) :=
  have hfac : underlyingModuleMap (factorThruImage φ) ≫ underlyingModuleMap (image.ι φ)
      = underlyingModuleMap φ :=
    (underlyingModuleFunctor.map_comp (factorThruImage φ) (image.ι φ)).symm.trans
      (congrArg underlyingModuleFunctor.map (image.fac φ))
  have hp : Epi (underlyingModuleMap (factorThruImage φ)) :=
    epi_underlyingModuleMap_of_isLocallySurjective (factorThruImage φ)
      (isLocallySurjective_factorThruImage_right φ)
  have hm : Mono (underlyingModuleMap (image.ι φ)) :=
    mono_underlyingModuleMap_of_mono (image.ι φ) inferInstance
  let F' : MonoFactorisation (underlyingModuleMap φ) :=
    { I := underlyingModule (image φ)
      m := underlyingModuleMap (image.ι φ)
      m_mono := hm
      e := underlyingModuleMap (factorThruImage φ)
      fac := hfac }
  have hu1 : image.lift F' ≫ underlyingModuleMap (image.ι φ)
      = image.ι (underlyingModuleMap φ) := image.lift_fac F'
  have hu2 : factorThruImage (underlyingModuleMap φ) ≫ image.lift F'
      = underlyingModuleMap (factorThruImage φ) := image.fac_lift F'
  have hmu : Mono (image.lift F') := mono_of_mono_fac hu1
  have heu : Epi (image.lift F') :=
    have := hp
    epi_of_epi_fac hu2
  have := hmu
  have := heu
  have : IsIso (image.lift F') := isIso_of_mono_of_epi _
  asIso (image.lift F')

/-! ### Quasi-coherence and finite type of the image -/

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The image of a morphism of quasi-coherent sheaves of `𝒪_F`-algebras is quasi-coherent.**

The underlying module of the image is the image of the underlying morphism of modules, and the
image of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent. -/
theorem isQuasicoherent_image {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C)
    (hA : A.IsQuasicoherent) (hC : C.IsQuasicoherent) : (image φ).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (underlyingModuleImageIso φ)
    (isQuasicoherentOnSite_image_unconditional B S hS F hF (underlyingModuleMap φ) hA hC)

/-- **The image of a morphism of quasi-coherent sheaves of `𝒪_F`-algebras whose source is of
finite type is of finite type.**

On an affine étale chart the structure-algebra map of the image is that of the source followed by
the sections of the corestriction, so it suffices that those sections be surjective.  The
corestriction is locally surjective, hence an epimorphism of underlying modules, and an
epimorphism of quasi-coherent `𝒪_F`-modules is surjective on the sections over an affine chart by
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite` — the restated form
of Descent, Proposition 03DW, reached by faithfully flat descent and no cohomology. -/
theorem isFiniteType_image {A C : AlgebraSheaf.{u, u} B S hS F hF} (φ : A ⟶ C)
    (hA : A.IsQuasicoherent) (hC : C.IsQuasicoherent) (hAft : A.IsFiniteType) :
    (image φ).IsFiniteType := by
  refine IsFiniteType.of_surjective_app (factorThruImage φ) (fun W hW => ?_) hAft
  have hepi : Epi (underlyingModuleMap (factorThruImage φ)) :=
    epi_underlyingModuleMap_of_isLocallySurjective (factorThruImage φ)
      (isLocallySurjective_factorThruImage_right φ)
  have h := surjective_val_app_of_epi_of_isQuasicoherentOnSite
    (underlyingModuleMap (factorThruImage φ)) hepi hA (isQuasicoherent_image φ hA hC) W hW
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨x, hx⟩

end AlgebraSheaf

/-! ### Nonemptiness of the finite type quasi-coherent subalgebras -/

/-- **The finite type quasi-coherent subalgebras of a quasi-coherent sheaf of `𝒪_Y`-algebras are
nonempty**, with no hypothesis beyond quasi-coherence of the algebra.

The witness is the image of the canonical morphism `𝒪_Y ⟶ A`, which is a subobject of `A` because
the inclusion of an image is a monomorphism — the canonical morphism itself is not one.  Its
quasi-coherence and its finite type are
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_image` and
`AlgebraicGeometry.Space.AlgebraSheaf.isFiniteType_image` applied to the quasi-coherence and the
finite type of `𝒪_Y` as an algebra over itself.

This is the nonemptiness half of the directedness assertion of Stacks 082B, and the half that was
missing; the other half is the existence of upper bounds, for which see
`AlgebraicGeometry.Space.isFiltered_finiteTypeSubalgebra_of_exists_sup`. -/
theorem nonempty_finiteTypeSubalgebra_of_isQuasicoherent (Y : AlgebraicSpaces B S hS)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hA : A.IsQuasicoherent) :
    Nonempty (FiniteTypeSubalgebra B S hS Y.1 Y.2 A) := by
  have hqc : (image (unitAlgebraHom B S hS Y A)).IsQuasicoherent :=
    AlgebraSheaf.isQuasicoherent_image _ (isQuasicoherent_unitAlgebra B S hS Y) hA
  have hft : (image (unitAlgebraHom B S hS Y A)).IsFiniteType :=
    AlgebraSheaf.isFiniteType_image _ (isQuasicoherent_unitAlgebra B S hS Y) hA
      (isFiniteType_unitAlgebra B S hS Y)
  exact ⟨⟨imageSubobject (unitAlgebraHom B S hS Y A),
    AlgebraSheaf.IsQuasicoherent.of_iso
      (imageSubobjectIso (unitAlgebraHom B S hS Y A)).symm hqc,
    AlgebraSheaf.IsFiniteType.of_iso
      (imageSubobjectIso (unitAlgebraHom B S hS Y A)).symm hft⟩⟩

/-- **The directedness assertion of Stacks 082B, reduced to the existence of upper bounds
alone.**  The nonemptiness hypothesis of
`AlgebraicGeometry.Space.isFiltered_finiteTypeSubalgebra_of_cocone_objs` is discharged by
`AlgebraicGeometry.Space.nonempty_finiteTypeSubalgebra_of_isQuasicoherent`.

What remains is exactly the join of two finite type quasi-coherent subalgebras: the subobject join
itself exists (`AlgebraicGeometry.Space.algebraSheaf_exists_sup`), but its quasi-coherence and its
finite type need the sections of a coproduct of algebra sheaves over an affine chart to be the
tensor product of the sections, which this tree does not carry. -/
theorem isFiltered_finiteTypeSubalgebra_of_exists_sup (Y : AlgebraicSpaces B S hS)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hA : A.IsQuasicoherent)
    (h : ∀ C D : FiniteTypeSubalgebra B S hS Y.1 Y.2 A,
      ∃ (E : FiniteTypeSubalgebra B S hS Y.1 Y.2 A) (_ : C ⟶ E) (_ : D ⟶ E), True) :
    IsFiltered (FiniteTypeSubalgebra B S hS Y.1 Y.2 A) :=
  isFiltered_finiteTypeSubalgebra_of_cocone_objs B S hS Y.1 Y.2 A
    (nonempty_finiteTypeSubalgebra_of_isQuasicoherent B S hS Y A hA) h

/-- **The finite type quasi-coherent subalgebras of the integral closure of `𝒪_Y` in itself are
nonempty**, with no hypothesis at all.

An instance of `AlgebraicGeometry.Space.nonempty_finiteTypeSubalgebra_of_isQuasicoherent` at a
concrete quasi-coherent algebra sheaf: the integral closure of the structure sheaf in a
quasi-coherent algebra is quasi-coherent by Stacks 0820,
`AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_integralClosureSheaf`, and `𝒪_Y` read as an
algebra over itself is quasi-coherent.  Having no hypotheses, this witnesses that the
quasi-coherence hypothesis above is satisfiable. -/
theorem nonempty_finiteTypeSubalgebra_integralClosureSheaf_unitAlgebra
    (Y : AlgebraicSpaces B S hS) :
    Nonempty (FiniteTypeSubalgebra B S hS Y.1 Y.2
      (AlgebraSheaf.integralClosureSheaf (unitAlgebra B S hS Y))) :=
  nonempty_finiteTypeSubalgebra_of_isQuasicoherent B S hS Y _
    (AlgebraSheaf.isQuasicoherent_integralClosureSheaf _ (isQuasicoherent_unitAlgebra B S hS Y))

end AlgebraicGeometry.Space

end
