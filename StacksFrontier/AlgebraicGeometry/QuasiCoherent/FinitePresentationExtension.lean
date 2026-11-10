module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.SliceTransport
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending a finitely presented module from a quasi-compact open

Let `X` be a quasi-compact and quasi-separated scheme, `U ⊆ X` a quasi-compact open, `F` a
quasi-coherent `𝒪_X`-module and `G` a finitely presented `𝒪_U`-module equipped with a morphism
`φ : G ⟶ F|_U`.  Then `φ` is the restriction of a morphism `G' ⟶ F` from a finitely presented
`𝒪_X`-module `G'` whose restriction to `U` is `G`.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_extension_of_hom`: the extension statement
  above.
* `AlgebraicGeometry.exists_finitePresentation_epi_isIso_restrict_of_epi`: a surjection onto a
  quasi-coherent module from a finitely presented one can be improved to a surjection which is
  moreover an isomorphism over a quasi-compact open on which the target is already of finite
  presentation.
* `AlgebraicGeometry.isFinitePresentation_of_isOpenCover`: finite presentation is local on the
  base.
* `AlgebraicGeometry.isFinitePresentation_zero`: the zero module is of finite presentation.

## Implementation notes

The proof follows the source in three stages.

On an affine scheme every quasi-coherent module has a global presentation, so a finitely
presented module on a quasi-compact open extends: generators are extended by the
quasi-coherent extension of [Stacks, Tag 01PE], and the relations are cut down by the
finite-type subobject extension of [Stacks, Tag 01PF]; this is `affineExtension`.  The key
auxiliary step `exists_finitePresentation_epi_isIso_restrict_of_epi` replaces a surjection
`A ↠ F` from a finitely presented module by a surjection from a finitely presented module which
is an isomorphism over a prescribed quasi-compact open.

On a general quasi-compact, quasi-separated `X` one enlarges the locus of finite presentation
one affine open at a time (`extendFinitePresentationLocus`, then a `Finset` induction in
`exists_finitePresentation_model`), the glueing being the fibre product of the module with the
direct image of the new affine model.  Finite presentation is local on the base, by fpqc
descent of finite presentation [Stacks, Tag 05B0], which is what turns the finished cover into
a global statement.

## References

* [Stacks Project, Tag 01PI](https://stacks.math.columbia.edu/tag/01PI)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules Opposite TopologicalSpace
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules

universe u u₁ v₁

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Hypotheses supplied explicitly rather than by instance search

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` carrying its
own `Category` instance, so `Epi f` for `f` a morphism of `𝒪_X`-modules and the same statement
read in the `SheafOfModules` spelling are definitionally but not syntactically equal, and
instance search does not cross between the two.  The three wrappers here restate the pieces of
the `SheafOfModules` generating-sections API that this file uses, with the epimorphism and
cocontinuity hypotheses as explicit arguments; crossing then happens at an ordinary
definitional unification of an explicit argument instead of inside instance search. -/

section Explicit

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- The image of a family of generating sections under an epimorphism, with the epimorphism
hypothesis supplied explicitly: `SheafOfModules.GeneratingSections.ofEpi`. -/
noncomputable def generatingSectionsOfEpi (σ : M.GeneratingSections) (p : M ⟶ N) (hp : Epi p) :
    N.GeneratingSections :=
  have := hp
  σ.ofEpi p

/-- The image of a finite family of generating sections is finite. -/
theorem isFiniteType_generatingSectionsOfEpi (σ : M.GeneratingSections) (hσ : σ.IsFiniteType)
    (p : M ⟶ N) (hp : Epi p) : (generatingSectionsOfEpi σ p hp).IsFiniteType :=
  have := hσ
  have := hp
  inferInstanceAs (σ.ofEpi p).IsFiniteType

variable {C' : Type u₁} [Category.{v₁} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The image of a family of generating sections under a cocontinuous functor, with the
cocontinuity hypothesis supplied explicitly: `SheafOfModules.GeneratingSections.map`. -/
noncomputable def generatingSectionsMap (σ : M.GeneratingSections)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    (hF : PreservesColimitsOfSize.{u, u} F) (η : unit S ≅ F.obj (unit R)) :
    (F.obj M).GeneratingSections :=
  have := hF
  σ.map F η

/-- The image of a finite family of generating sections under a cocontinuous functor is
finite. -/
theorem isFiniteType_generatingSectionsMap (σ : M.GeneratingSections) (hσ : σ.IsFiniteType)
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    (hF : PreservesColimitsOfSize.{u, u} F) (η : unit S ≅ F.obj (unit R)) :
    (generatingSectionsMap σ F hF η).IsFiniteType :=
  have := hσ
  have := hF
  inferInstanceAs (σ.map F η).IsFiniteType

end Explicit

/-- A finitely presented module on a scheme is of finite type, at the universe parameters the
subobject-extension API of [Stacks, Tag 01PF] uses. -/
private lemma isFiniteType_of_isFinitePresentation {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsFinitePresentation] : SheafOfModules.IsFiniteType.{u, u, u} M :=
  SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M

/-- Finite type transfers along an isomorphism, with the hypothesis supplied explicitly. -/
private lemma isFiniteType_of_sheafIso {Y : Scheme.{u}}
    {A B : SheafOfModules.{u} Y.ringCatSheaf} (e : A ≅ B)
    (hA : SheafOfModules.IsFiniteType.{u, u, u} A) :
    SheafOfModules.IsFiniteType.{u, u, u} B :=
  have := hA
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} e

/-- The kernel of an epimorphism from a module of finite type onto a finitely presented module
is of finite type, with the epimorphism hypothesis supplied explicitly.  This is
[Stacks, Tag 01BP] part (2). -/
private lemma isFiniteType_kernel_of_epi {Y : Scheme.{u}}
    {A B : SheafOfModules.{u} Y.ringCatSheaf} (f : A ⟶ B) (hf : Epi f)
    (hB : B.IsFinitePresentation) (hA : SheafOfModules.IsFiniteType.{u, u, u} A) :
    SheafOfModules.IsFiniteType.{u, u, u} (kernel f) :=
  have := hf
  have := hB
  have := hA
  Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType f

/-- Finite presentation transfers along an isomorphism of modules. -/
private lemma isFinitePresentation_of_modulesIso {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B)
    (hA : A.IsFinitePresentation) : B.IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso e hA

/-- The zero module on a scheme is of finite presentation. -/
theorem isFinitePresentation_zero (X : Scheme.{u}) : (0 : X.Modules).IsFinitePresentation :=
  have : (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit X
  have : SheafOfModules.IsFiniteType.{u, u, u} (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (SheafOfModules.unit X.ringCatSheaf)
  have : (cokernel (𝟙 (SheafOfModules.unit X.ringCatSheaf))).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel _
  isFinitePresentation_of_modulesIso
    (isZero_cokernel_of_epi (𝟙 (SheafOfModules.unit X.ringCatSheaf))).isoZero this

/-! ### Finite presentation is local on the base -/

/-- **Finite presentation is local on the base.** A module whose restriction to each member of
an open cover is of finite presentation is of finite presentation. -/
theorem isFinitePresentation_of_isOpenCover (F : X.Modules)
    [F.IsQuasicoherent] {I : Type*} (U : I → X.Opens) (hU : IsOpenCover U)
    (h : ∀ i, (F.restrict (U i).ι).IsFinitePresentation) : F.IsFinitePresentation := by
  let C := X.openCoverOfIsOpenCover U hU
  refine isFinitePresentation_of_pullback_fpqcCover F
    (C.weaken Scheme.zariskiPrecoverage_le_fpqcPrecoverage) fun i => ?_
  exact isFinitePresentation_of_modulesIso ((restrictFunctorIsoPullback (U i).ι).app F) (h i)

/-! ### Finite generation on an affine scheme -/

/-- A quasi-coherent module of finite type on the spectrum of a ring is generated by finitely
many global sections. -/
private lemma exists_isFiniteType_generatingSections_spec (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ σ : M.GeneratingSections, σ.IsFiniteType := by
  have hft : (tilde (moduleSpecΓFunctor.obj M)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (asIso M.fromTildeΓ).symm
  have : Module.Finite R (moduleSpecΓFunctor.obj M) := (tilde_isFiniteType_iff _).mp hft
  have hiso : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have hepi : Epi M.fromTildeΓ := inferInstance
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := moduleSpecΓFunctor.obj M)
  have hfin : Finite (s : Set (moduleSpecΓFunctor.obj M)) := inferInstance
  have hσ : ((presentationTilde (moduleSpecΓFunctor.obj M) (s : Set _) hs _
      (Submodule.span_eq _)).generators).IsFiniteType := ⟨hfin⟩
  exact ⟨generatingSectionsOfEpi _ M.fromTildeΓ hepi,
    isFiniteType_generatingSectionsOfEpi _ hσ M.fromTildeΓ hepi⟩

/-- A quasi-coherent module of finite type on an affine scheme is generated by finitely many
global sections. -/
private lemma exists_isFiniteType_generatingSections_of_isAffine (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ σ : M.GeneratingSections, σ.IsFiniteType := by
  have hft : (M.restrict X.isoSpec.inv).IsFiniteType := by
    have : ((Scheme.Modules.pullback X.isoSpec.inv).obj M).IsFiniteType :=
      SheafOfModules.pullback_isFiniteType X.isoSpec.inv.toLRSHom.toShHom M
    exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((restrictFunctorIsoPullback X.isoSpec.inv).app M).symm
  obtain ⟨σ, hσ⟩ := exists_isFiniteType_generatingSections_spec _ (M.restrict X.isoSpec.inv)
  have hpres : PreservesColimitsOfSize.{u, u} (restrictFunctor X.isoSpec.hom) :=
    (restrictAdjunction X.isoSpec.hom).leftAdjoint_preservesColimits
  have hepi : Epi (((restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm ≪≫
    restrictFunctorCongr X.isoSpec.hom_inv_id ≪≫ restrictFunctorId).app M).hom := inferInstance
  have hτ := isFiniteType_generatingSectionsMap σ hσ (restrictFunctor X.isoSpec.hom) hpres
    (restrictUnitIso X.isoSpec.hom).symm
  exact ⟨generatingSectionsOfEpi _ _ hepi, isFiniteType_generatingSectionsOfEpi _ hτ _ hepi⟩

/-! ### Restriction, isomorphy on an open, and fibre products -/

/-- A morphism whose component at every open of the form `U.ι ''ᵁ W` is an isomorphism
restricts to an isomorphism on `U`. -/
private lemma isIso_restrict_of_isIso_app {A B : X.Modules} (p : A ⟶ B) (U : X.Opens)
    (h : ∀ W : U.toScheme.Opens, IsIso (p.app (U.ι ''ᵁ W))) :
    IsIso ((restrictFunctor U.ι).map p) := by
  have : IsIso ((toPresheaf U.toScheme).map ((restrictFunctor U.ι).map p)) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun W => h W.unop
  exact isIso_of_reflects_iso _ (toPresheaf U.toScheme)

/-- A morphism which restricts to an isomorphism on `U` has an invertible component at every
open contained in `U`. -/
private lemma isIso_app_of_isIso_restrict {A B : X.Modules} (p : A ⟶ B) (U W : X.Opens)
    (hWU : W ≤ U) [IsIso ((restrictFunctor U.ι).map p)] : IsIso (p.app W) := by
  have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hWU]
  have h : IsIso (p.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) :=
    inferInstanceAs (IsIso (((toPresheaf U.toScheme).map
      ((restrictFunctor U.ι).map p)).app (op (U.ι ⁻¹ᵁ W))))
  rwa [hW] at h

/-- A morphism which restricts to an isomorphism on `V` restricts to an isomorphism on every
smaller open. -/
private lemma isIso_restrict_of_le {A B : X.Modules} (p : A ⟶ B) {U V : X.Opens} (hUV : U ≤ V)
    [IsIso ((restrictFunctor V.ι).map p)] : IsIso ((restrictFunctor U.ι).map p) :=
  isIso_restrict_of_isIso_app p U fun W => isIso_app_of_isIso_restrict p V _
    ((Scheme.Opens.ι_image_le U W).trans hUV)

/-- Finite presentation of a restriction is inherited by the restriction to the preimage of the
open along a further open immersion. -/
private lemma isFinitePresentation_restrict_preimage {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (F : X.Modules) (U : X.Opens)
    [(F.restrict U.ι).IsFinitePresentation] :
    ((F.restrict f).restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation := by
  let g := f.resLE U (f ⁻¹ᵁ U) le_rfl
  have : IsOpenImmersion g := by dsimp [g, Scheme.Hom.resLE]; infer_instance
  have h := Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict g
    (F.restrict U.ι)
  let e : (F.restrict U.ι).restrict g ≅ (F.restrict f).restrict (f ⁻¹ᵁ U).ι :=
    ((restrictFunctorComp g U.ι).symm ≪≫
      restrictFunctorCongr (f.resLE_comp_ι (U := U) (V := f ⁻¹ᵁ U) le_rfl) ≪≫
      restrictFunctorComp (f ⁻¹ᵁ U).ι f).app F
  exact isFinitePresentation_of_modulesIso e h

/-- If the restrictions of `F` to `U` and to `V` are of finite presentation, so is its
restriction to `U ⊔ V`. -/
private lemma isFinitePresentation_restrict_sup (F : X.Modules) [F.IsQuasicoherent]
    (U V : X.Opens)
    [(F.restrict U.ι).IsFinitePresentation] [(F.restrict V.ι).IsFinitePresentation] :
    (F.restrict (U ⊔ V).ι).IsFinitePresentation := by
  let W := U ⊔ V
  let T : Bool → W.toScheme.Opens := fun b => W.ι ⁻¹ᵁ (if b then U else V)
  apply isFinitePresentation_of_isOpenCover (F.restrict W.ι) T
  · change (⨆ b : Bool, W.ι ⁻¹ᵁ (if b then U else V)) = ⊤
    rw [← W.ι.preimage_iSup, iSup_bool_eq]
    exact W.ι_preimage_self
  · rintro (_ | _)
    · exact isFinitePresentation_restrict_preimage W.ι F V
    · exact isFinitePresentation_restrict_preimage W.ι F U

/-! ### Improving a presentation over a quasi-compact open -/

/-- Given a surjection `f : A ↠ F` from a finitely presented module onto a quasi-coherent
module whose restriction to a quasi-compact open `U` is already of finite presentation, there
is a surjection onto `F` from a finitely presented module which restricts to an isomorphism
over `U`.

The kernel of `f` is quasi-coherent, and over `U` it is of finite type; extending a finite-type
quasi-coherent submodule of that kernel by [Stacks, Tag 01PF] and taking the cokernel produces
the required module. -/
theorem exists_finitePresentation_epi_isIso_restrict_of_epi [CompactSpace X]
    [QuasiSeparatedSpace X]
    {A F : X.Modules} [A.IsFinitePresentation] [F.IsQuasicoherent]
    (f : A ⟶ F) (hf : Epi f) (U : X.Opens) (hU : IsCompact U.1)
    [hFU : (F.restrict U.ι).IsFinitePresentation] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (p : G ⟶ F),
      Epi p ∧ IsIso ((restrictFunctor U.ι).map p) := by
  classical
  have := hf
  have : (A.restrict U.ι).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict U.ι A
  have hA : A.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation A
  let K := kernel f
  have hK : K.IsQuasicoherent := Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel f
  let R := Scheme.Modules.restrictFunctor U.ι
  have : PreservesFiniteLimits R := Modules.preservesFiniteLimits_restrictFunctor U.ι
  have : PreservesFiniteColimits R := inferInstance
  let fU : R.obj A ⟶ R.obj F := R.map f
  have hepiU : Epi fU := Functor.map_epi R f
  have hRA : (R.obj A).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFinitePresentation_restrict U.ι A
  have : (R.obj A).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R.obj A)
  have : (R.obj F).IsFinitePresentation := hFU
  have : (R.obj A).IsQuasicoherent :=
    inferInstanceAs (((restrictFunctor U.ι).obj A).IsQuasicoherent)
  have : (R.obj F).IsQuasicoherent :=
    inferInstanceAs (((restrictFunctor U.ι).obj F).IsQuasicoherent)
  let eK : R.obj K ≅ kernel fU := PreservesKernel.iso R f
  have hfU : (kernel fU).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel fU
  let G : Subobject (K.restrict U.ι) := Subobject.mk eK.inv
  have : (G : U.toScheme.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso eK.inv).symm inferInstance
  have : SheafOfModules.IsFiniteType.{u, u, u} (G : U.toScheme.Modules) :=
    isFiniteType_of_sheafIso (Subobject.underlyingIso eK.inv).symm
      (isFiniteType_kernel_of_epi fU hepiU hFU
        (isFiniteType_of_isFinitePresentation (R.obj A)))
  obtain ⟨K', hK'qc, hK'ft, ⟨e, he⟩⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension K U hU G
  let a : (K' : X.Modules) ⟶ A := K'.arrow ≫ kernel.ι f
  let Q := cokernel a
  let q : Q ⟶ F := cokernel.desc a f (by simp [a])
  have : (K' : X.Modules).IsFiniteType := hK'ft
  have : (Q : X.Modules).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel a
  have hq_epi : Epi q := by
    apply epi_of_epi_fac (f := cokernel.π a) (h := f)
    simp [q]
  refine ⟨Q, inferInstance, q, hq_epi, ?_⟩
  let e' : R.obj (K' : X.Modules) ≅ kernel fU := e.trans (Subobject.underlyingIso eK.inv)
  have haU : R.map a = e'.hom ≫ kernel.ι fU := by
    dsimp [a]
    rw [Functor.map_comp, he]
    dsimp [e']
    change e.hom ≫ (Subobject.mk eK.inv).arrow ≫ R.map (kernel.ι f) =
      e.hom ≫ (Subobject.underlyingIso eK.inv).hom ≫ kernel.ι fU
    rw [← Subobject.underlyingIso_hom_comp_eq_mk eK.inv, Category.assoc,
      PreservesKernel.iso_inv_ι]
  have hk : kernel.ι fU = e'.inv ≫ R.map a := by rw [haU]; simp
  let b : R.obj A ⟶ R.obj Q := R.map (cokernel.π a)
  have hkb : kernel.ι fU ≫ b = 0 := by
    rw [hk]
    simp [b, ← Functor.map_comp]
  let g : R.obj F ⟶ R.obj Q := Abelian.epiDesc fU b hkb
  have hg : fU ≫ g = b := by simp [g]
  have hbq : b ≫ R.map q = fU := by
    dsimp [b, fU]
    rw [← Functor.map_comp]
    simp [q]
  have : Epi (R.map q) := Functor.map_epi R q
  have h₁ : g ≫ R.map q = 𝟙 _ := by
    apply (cancel_epi fU).1
    rw [reassoc_of% hg, hbq, Category.comp_id]
  have : Epi b := Functor.map_epi R (cokernel.π a)
  have h₂ : R.map q ≫ g = 𝟙 _ := by
    apply (cancel_epi b).1
    rw [reassoc_of% hbq, hg, Category.comp_id]
  exact ⟨⟨g, h₂, h₁⟩⟩

/-- The inclusion of a quasi-compact open subscheme is quasi-compact. -/
private lemma quasiCompact_ι_of_isCompact [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact U.1) : QuasiCompact U.ι :=
  quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp (hU.isRetrocompact U.2))

/-- **The affine case of the extension theorem.** On an affine scheme, a finitely presented
module on a quasi-compact open, together with a morphism to the restriction of a quasi-coherent
module `F`, extends to a finitely presented module with a morphism to `F`. -/
private lemma affineExtension [IsAffine X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact U.1)
    (G : U.toScheme.Modules) [G.IsFinitePresentation] (φ : G ⟶ F.restrict U.ι) :
    ∃ (G' : X.Modules) (_ : G'.IsFinitePresentation)
      (φ' : G' ⟶ F) (e : G'.restrict U.ι ≅ G),
      e.hom ≫ φ = (restrictFunctor U.ι).map φ' := by
  classical
  have := quasiCompact_ι_of_isCompact hU
  have hG : G.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation G
  obtain ⟨H, hH, ψ, ⟨e, hExtend⟩⟩ := exists_quasicoherent_extension U.ι F G φ
  have : H.IsQuasicoherent := hH
  let S : Subobject (H.restrict U.ι) := Subobject.mk (𝟙 (H.restrict U.ι))
  let iS : (S : U.toScheme.Modules) ≅ H.restrict U.ι :=
    Subobject.underlyingIso (𝟙 (H.restrict U.ι))
  have hSarrow : S.arrow = iS.hom := by
    simpa [S] using
      (Subobject.underlyingIso_hom_comp_eq_mk (f := 𝟙 (H.restrict U.ι))).symm
  have : (S : U.toScheme.Modules).IsFinitePresentation :=
    isFinitePresentation_of_modulesIso (iS ≪≫ e).symm inferInstance
  have : (S : U.toScheme.Modules).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isFinitePresentation _
  have : SheafOfModules.IsFiniteType.{u, u, u} (S : U.toScheme.Modules) :=
    isFiniteType_of_isFinitePresentation _
  obtain ⟨K, hKqc, hKft, ⟨eK, hKcomm⟩⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension H U hU S
  let eKH : (K : X.Modules).restrict U.ι ≅ H.restrict U.ι := eK ≪≫ iS
  have hKarrow : (restrictFunctor U.ι).map K.arrow = eKH.hom := by
    simpa [eKH, hSarrow] using hKcomm
  let eKG : (K : X.Modules).restrict U.ι ≅ G := eKH ≪≫ e
  have : (K : X.Modules).IsQuasicoherent := hKqc
  have : (K : X.Modules).IsFiniteType := hKft
  have : ((K : X.Modules).restrict U.ι).IsFinitePresentation :=
    isFinitePresentation_of_modulesIso eKG.symm inferInstance
  obtain ⟨σ, hσ⟩ := exists_isFiniteType_generatingSections_of_isAffine X (K : X.Modules)
  have : Finite σ.I := hσ.finite
  have : (free (R := X.ringCatSheaf) σ.I).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite X σ.I
  obtain ⟨G', hG', p, hp, hpU⟩ :=
    exists_finitePresentation_epi_isIso_restrict_of_epi σ.π σ.epi U hU
  have : IsIso ((restrictFunctor U.ι).map p) := hpU
  refine ⟨G', hG', p ≫ K.arrow ≫ ψ, asIso ((restrictFunctor U.ι).map p) ≪≫ eKG, ?_⟩
  simp only [eKG, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← hKarrow, hExtend]
  simp

/-! ### Enlarging the locus of finite presentation -/

/-- Enlarge the locus on which a quasi-coherent module is of finite presentation by one affine
open, at the cost of replacing the module by one mapping to it isomorphically over the old
locus.  The new module is the fibre product of `F` with the direct image of an affine model. -/
private lemma extendFinitePresentationLocus [QuasiSeparatedSpace X] (F : X.Modules)
    [F.IsQuasicoherent] (U V : X.Opens) (hU : IsCompact U.1) (hV : IsAffineOpen V)
    [(F.restrict U.ι).IsFinitePresentation] :
    ∃ (H : X.Modules) (_ : H.IsQuasicoherent) (p : H ⟶ F),
      IsIso ((restrictFunctor U.ι).map p) ∧ (H.restrict V.ι).IsFinitePresentation := by
  have : IsAffine V.toScheme := hV
  have := quasiCompact_ι_of_isCompact hV.isCompact
  let W := V.ι ⁻¹ᵁ U
  have : ((F.restrict V.ι).restrict W.ι).IsFinitePresentation :=
    isFinitePresentation_restrict_preimage V.ι F U
  obtain ⟨A, hA, a, e, he⟩ := affineExtension (F.restrict V.ι) W
    (V.ι.isCompact_preimage hU) ((F.restrict V.ι).restrict W.ι) (𝟙 _)
  have : A.IsFinitePresentation := hA
  have : A.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation A
  have : IsIso ((restrictFunctor W.ι).map a) := by
    rw [← he, Category.comp_id]
    infer_instance
  let R := restrictFunctor V.ι
  let P := Scheme.Modules.pushforward V.ι
  let η : F ⟶ P.obj (R.obj F) := (restrictAdjunction V.ι).unit.app F
  let b := P.map a
  let H := Limits.pullback η b
  have hPA : (P.obj A).IsQuasicoherent := AlgebraicGeometry.pushforward_isQuasicoherent V.ι A
  have hPF : (P.obj (R.obj F)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent V.ι (R.obj F)
  have : H.IsQuasicoherent := inferInstance
  let p : H ⟶ F := Limits.pullback.fst η b
  refine ⟨H, inferInstance, p, ?_, ?_⟩
  · let T := restrictFunctor U.ι
    have : PreservesFiniteLimits T := Modules.preservesFiniteLimits_restrictFunctor U.ι
    have : IsIso (T.map b) := by
      refine isIso_restrict_of_isIso_app _ _ fun Z => ?_
      change IsIso (a.app (V.ι ⁻¹ᵁ (U.ι ''ᵁ Z)))
      exact isIso_app_of_isIso_restrict a W _
        (Scheme.Hom.preimage_mono _ (Scheme.Opens.ι_image_le U Z))
    change IsIso (T.map (Limits.pullback.fst η b))
    rw [← PreservesPullback.iso_hom_fst T η b]
    infer_instance
  · have : PreservesFiniteLimits R := Modules.preservesFiniteLimits_restrictFunctor V.ι
    have : IsIso (R.map η) := by
      have hη : R.map η ≫ (restrictAdjunction V.ι).counit.app (R.obj F) = 𝟙 _ :=
        (restrictAdjunction V.ι).left_triangle_components F
      rw [(IsIso.inv_eq_of_inv_hom_id hη).symm]
      infer_instance
    have : IsIso (R.map (Limits.pullback.snd η b)) := by
      rw [← PreservesPullback.iso_hom_snd R η b]
      infer_instance
    let eH : H.restrict V.ι ≅ A := asIso (R.map (Limits.pullback.snd η b)) ≪≫
      (restrictFunctorAdjCounitIso V.ι).app A
    exact isFinitePresentation_of_modulesIso eH.symm hA

/-- On a quasi-compact, quasi-separated scheme, a quasi-coherent module whose restriction to a
quasi-compact open `U` is of finite presentation receives a morphism from a finitely presented
module which is an isomorphism over `U`.

Finitely many affine opens cover `X`, and they are added to the locus of finite presentation
one at a time by `extendFinitePresentationLocus`. -/
private lemma exists_finitePresentation_model [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsCompact U.1)
    [(F.restrict U.ι).IsFinitePresentation] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (p : G ⟶ F),
      IsIso ((restrictFunctor U.ι).map p) := by
  classical
  have build (S : Finset X.affineOpens) :
      ∃ (H : X.Modules) (_ : H.IsQuasicoherent) (p : H ⟶ F),
        IsIso ((restrictFunctor U.ι).map p) ∧
        (H.restrict (U ⊔ ⨆ V ∈ S, (V : X.Opens)).ι).IsFinitePresentation := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨F, inferInstance, 𝟙 F, by infer_instance, ?_⟩
      have hbot : (⨆ V ∈ (∅ : Finset X.affineOpens), (V : X.Opens)) = ⊥ := by
        refine le_antisymm (iSup_le fun V => iSup_le fun h => ?_) bot_le
        simp at h
      rw [hbot, sup_bot_eq]
      infer_instance
    | @insert V S hVS ih =>
      obtain ⟨H, hH, p, hp, hfp⟩ := ih
      have : H.IsQuasicoherent := hH
      let W : X.Opens := U ⊔ ⨆ V ∈ S, (V : X.Opens)
      have hW : IsCompact W.1 := by
        apply hU.union
        simp only [Opens.coe_iSup]
        exact S.isCompact_biUnion fun V _ => V.2.isCompact
      have : (H.restrict W.ι).IsFinitePresentation := hfp
      obtain ⟨K, hK, q, hq, hKV⟩ := extendFinitePresentationLocus H W V.1 hW V.2
      have : K.IsQuasicoherent := hK
      have : IsIso ((restrictFunctor W.ι).map q) := hq
      have : IsIso ((restrictFunctor U.ι).map q) :=
        isIso_restrict_of_le q (show U ≤ W from le_sup_left)
      have : IsIso ((restrictFunctor U.ι).map p) := hp
      have : (K.restrict W.ι).IsFinitePresentation :=
        isFinitePresentation_of_modulesIso (asIso ((restrictFunctor W.ι).map q)).symm hfp
      have : (K.restrict V.1.ι).IsFinitePresentation := hKV
      refine ⟨K, hK, q ≫ p, by rw [Functor.map_comp]; infer_instance, ?_⟩
      have h := isFinitePresentation_restrict_sup K W V.1
      have heq : (U ⊔ ⨆ T ∈ insert V S, (T : X.Opens)) = W ⊔ V.1 := by
        rw [Finset.iSup_insert]
        change U ⊔ ((V : X.Opens) ⊔ ⨆ T ∈ S, (T : X.Opens)) =
          (U ⊔ ⨆ T ∈ S, (T : X.Opens)) ⊔ V.1
        rw [sup_comm (V : X.Opens) (⨆ T ∈ S, (T : X.Opens)), sup_assoc]
      rwa [heq]
  obtain ⟨S, hS, hcover⟩ :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (show IsCompact (⊤ : X.Opens).1 from isCompact_univ)
  obtain ⟨H, hH, p, hp, hfp⟩ := build hS.toFinset
  have : H.IsQuasicoherent := hH
  have htop : (U ⊔ ⨆ V ∈ hS.toFinset, (V : X.Opens)) = ⊤ := by
    simpa using congrArg (fun W : X.Opens => U ⊔ W) hcover.symm
  have : (H.restrict (⊤ : X.Opens).ι).IsFinitePresentation := by rwa [htop] at hfp
  exact ⟨H, isFinitePresentation_of_isOpenCover H (fun _ : Bool => ⊤)
    (by simp [IsOpenCover]) (fun _ => inferInstance), p, hp⟩

/-- **Stacks Project, Tag 01PI.**  Extension of a finitely presented module from a
quasi-compact open.  Let `X` be a quasi-compact, quasi-separated scheme, `U` a quasi-compact
open, `F` a quasi-coherent `𝒪_X`-module and `φ : G ⟶ F|_U` a morphism from a finitely presented
`𝒪_U`-module.  Then `φ` is the restriction of a morphism `G' ⟶ F` from a finitely presented
`𝒪_X`-module `G'` restricting to `G`. -/
@[stacks 01PI, ega "I 9.4.8" "special case"]
theorem exists_finitePresentation_extension_of_hom [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsCompact U.1)
    (G : U.toScheme.Modules) [G.IsFinitePresentation] (φ : G ⟶ F.restrict U.ι) :
    ∃ (G' : X.Modules) (_ : G'.IsFinitePresentation)
      (φ' : G' ⟶ F) (e : G'.restrict U.ι ≅ G),
      e.hom ≫ φ = (restrictFunctor U.ι).map φ' := by
  have := quasiCompact_ι_of_isCompact hU
  have hG : G.IsQuasicoherent := _root_.isQuasicoherent_of_isFinitePresentation G
  obtain ⟨H, hH, ψ, ⟨e, he⟩⟩ := exists_quasicoherent_extension U.ι F G φ
  have : H.IsQuasicoherent := hH
  have : (H.restrict U.ι).IsFinitePresentation :=
    isFinitePresentation_of_modulesIso e.symm inferInstance
  obtain ⟨K, hK, p, hp⟩ := exists_finitePresentation_model H U hU
  have : IsIso ((restrictFunctor U.ι).map p) := hp
  refine ⟨K, hK, p ≫ ψ, asIso ((restrictFunctor U.ι).map p) ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Category.assoc, he, Functor.map_comp]

end AlgebraicGeometry

end
