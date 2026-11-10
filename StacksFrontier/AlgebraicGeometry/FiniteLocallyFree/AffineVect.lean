module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullback
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Proper
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vector bundles on an affine scheme

For a scheme `X`, `AlgebraicGeometry.Scheme.Vect X` is the category `Vect(X)` of finite locally
free `𝒪_X`-modules. This file records the basic lemmas on the pullback functor
`AlgebraicGeometry.Scheme.Vect.pullback : Vect(Y) ⥤ Vect(X)`, and identifies `Vect(Spec R)` with
the category of finite projective `R`-modules through `M ↦ M^~`, compatibly with base change.
This is the affine case of the correspondence between vector bundles and projective modules.

## Main definitions

* `AlgebraicGeometry.finiteProjectiveProperty` and `AlgebraicGeometry.FinProj`: the property of
  being a finite projective module, and the resulting full subcategory of `ModuleCat R`.
* `AlgebraicGeometry.FinProj.extendScalars`: extension of scalars on finite projective modules.
* `AlgebraicGeometry.tildeVect`: the comparison functor `FinProj R ⥤ Vect(Spec R)`.
* `AlgebraicGeometry.tildeVectEquivalence`: the same functor, bundled as an equivalence.
* `AlgebraicGeometry.tildeVectPullbackIso`: compatibility of the comparison with base change.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_tilde_functor_iff`: `M^~` is finite locally free if and
  only if `M` is finite projective.
* `AlgebraicGeometry.tildeVect_isEquivalence`: the comparison functor is an equivalence.

## Implementation notes

The functors on full subcategories are built with `CategoryTheory.ObjectProperty.lift`, so that
composing with `CategoryTheory.ObjectProperty.ι` returns the ambient functor definitionally.

`AlgebraicGeometry.Scheme.Modules` is not a reducible definition, so the universe arguments of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` have to be written out at every use.

## References

* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-! ### Restriction of vector bundles along a morphism of schemes -/

namespace Scheme.Vect

variable {X Y : Scheme.{u}}

/-- Pullback of finite locally free modules is pullback of modules: composing with the inclusion
of the full subcategory of finite locally free modules recovers
`AlgebraicGeometry.Scheme.Modules.pullback`. -/
lemma ι_comp_pullback (g : X ⟶ Y) :
    pullback g ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ Scheme.Modules.pullback g :=
  rfl

/-- The same identification as `AlgebraicGeometry.Scheme.Vect.ι_comp_pullback`, in the form of a
natural isomorphism. -/
noncomputable def ιCompPullbackIso (g : X ⟶ Y) :
    pullback g ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ Scheme.Modules.pullback g :=
  Iso.refl _

/-- The underlying module of a pullback of finite locally free modules. -/
@[simp]
lemma pullback_obj_obj (g : X ⟶ Y) (M : Y.Vect) :
    ((pullback g).obj M).obj = (Scheme.Modules.pullback g).obj M.obj :=
  rfl

/-- The underlying morphism of modules of the pullback of a morphism of finite locally free
modules. -/
@[simp]
lemma pullback_map_hom (g : X ⟶ Y) {M N : Y.Vect} (φ : M ⟶ N) :
    ((pullback g).map φ).hom = (Scheme.Modules.pullback g).map φ.hom :=
  rfl

end Scheme.Vect

/-! ### Finite projective modules -/

variable {R S : CommRingCat.{u}}

/-- The property of an `R`-module of being finite and projective. By
`Module.isFiniteLocallyFree_iff_finite_projective` this is the same as being finite locally
free. -/
abbrev finiteProjectiveProperty (R : CommRingCat.{u}) : ObjectProperty (ModuleCat.{u} R) :=
  fun L ↦ Module.Finite R L ∧ Module.Projective R L

/-- **The category of finite projective `R`-modules**, as a full subcategory of `ModuleCat R`. -/
@[sga "6 II 2.2.10"]
abbrev FinProj (R : CommRingCat.{u}) : Type (u + 1) :=
  (finiteProjectiveProperty R).FullSubcategory

/-- **Extension of scalars preserves finiteness and projectivity**: if `L` is a finite projective
`R`-module then `S ⊗_R L` is a finite projective `S`-module. -/
theorem finiteProjectiveProperty_extendScalars (φ : R ⟶ S) (L : FinProj R) :
    finiteProjectiveProperty S ((ModuleCat.extendScalars φ.hom).obj L.obj) := by
  let _ : Module.Finite R L.obj := L.property.1
  let _ : Module.Projective R L.obj := L.property.2
  let _ : Algebra R S := φ.hom.toAlgebra
  change Module.Finite S (TensorProduct R S L.obj) ∧ Module.Projective S (TensorProduct R S L.obj)
  exact ⟨inferInstance, inferInstance⟩

namespace FinProj

/-- **Extension of scalars on finite projective modules.** This is the restriction of
`ModuleCat.extendScalars` to the full subcategories of finite projective modules. -/
@[ega "III 6.3.8" "special case"]
noncomputable def extendScalars (φ : R ⟶ S) : FinProj R ⥤ FinProj S :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ ModuleCat.extendScalars φ.hom)
    (finiteProjectiveProperty_extendScalars φ)

/-- Extension of scalars on finite projective modules is extension of scalars: composing with the
inclusion of the full subcategory of finite projective modules recovers
`ModuleCat.extendScalars`. -/
lemma ι_comp_extendScalars (φ : R ⟶ S) :
    extendScalars φ ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ ModuleCat.extendScalars φ.hom :=
  rfl

/-- The same identification as `AlgebraicGeometry.FinProj.ι_comp_extendScalars`, in the form of a
natural isomorphism. -/
noncomputable def ιCompExtendScalarsIso (φ : R ⟶ S) :
    extendScalars φ ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ ModuleCat.extendScalars φ.hom :=
  Iso.refl _

/-- The underlying module of an extension of scalars of a finite projective module. -/
@[simp]
lemma extendScalars_obj_obj (φ : R ⟶ S) (L : FinProj R) :
    ((extendScalars φ).obj L).obj = (ModuleCat.extendScalars φ.hom).obj L.obj :=
  rfl

/-- The underlying linear map of the extension of scalars of a morphism of finite projective
modules. -/
@[simp]
lemma extendScalars_map_hom (φ : R ⟶ S) {L L' : FinProj R} (f : L ⟶ L') :
    ((extendScalars φ).map f).hom = (ModuleCat.extendScalars φ.hom).map f.hom :=
  rfl

end FinProj

/-! ### The affine comparison -/

/-- **Stacks Project, Tag 05JM, in the finite projective form.** The sheaf `M^~` on `Spec R`
associated to an `R`-module `M` is finite locally free if and only if `M` is a finite projective
`R`-module. -/
theorem isFiniteLocallyFree_tilde_functor_iff (L : ModuleCat.{u} R) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((tilde.functor R).obj L) ↔
      finiteProjectiveProperty R L :=
  Iff.trans (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module R L)
    (Module.isFiniteLocallyFree_iff_finite_projective R L)

/-- **The affine comparison functor from finite projective modules to vector bundles.** It sends
a finite projective `R`-module `M` to the finite locally free `𝒪_{Spec R}`-module `M^~`. -/
noncomputable def tildeVect (R : CommRingCat.{u}) : FinProj R ⥤ (Spec R).Vect :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ tilde.functor R)
    (fun L ↦ (isFiniteLocallyFree_tilde_functor_iff L.obj).mpr L.property)

/-- The comparison functor is `M ↦ M^~`: composing it with the inclusion of the full subcategory
of finite locally free modules recovers `AlgebraicGeometry.tilde.functor`. -/
lemma tildeVect_comp_ι (R : CommRingCat.{u}) :
    tildeVect R ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ tilde.functor R :=
  rfl

/-- The same identification as `AlgebraicGeometry.tildeVect_comp_ι`, in the form of a natural
isomorphism. -/
noncomputable def tildeVectCompιIso (R : CommRingCat.{u}) :
    ObjectProperty.ι _ ⋙ tilde.functor R ≅ tildeVect R ⋙ ObjectProperty.ι _ :=
  Iso.refl _

/-- The underlying module of the sheaf attached to a finite projective module. -/
@[simp]
lemma tildeVect_obj_obj (R : CommRingCat.{u}) (L : FinProj R) :
    ((tildeVect R).obj L).obj = (tilde.functor R).obj L.obj :=
  rfl

/-- The underlying morphism of modules attached to a morphism of finite projective modules. -/
@[simp]
lemma tildeVect_map_hom (R : CommRingCat.{u}) {L L' : FinProj R} (f : L ⟶ L') :
    ((tildeVect R).map f).hom = (tilde.functor R).map f.hom :=
  rfl

/-- The comparison functor is faithful. -/
instance tildeVect_faithful (R : CommRingCat.{u}) : (tildeVect R).Faithful :=
  Functor.Faithful.of_comp_eq (tildeVect_comp_ι R)

/-- The comparison functor is full. -/
instance tildeVect_full (R : CommRingCat.{u}) : (tildeVect R).Full :=
  Functor.Full.of_comp_faithful_iso (eqToIso (tildeVect_comp_ι R))

/-- **The comparison functor is essentially surjective**: every finite locally free
`𝒪_{Spec R}`-module is `M^~` for a finite projective `R`-module `M`, namely its module of global
sections. -/
instance tildeVect_essSurj (R : CommRingCat.{u}) : (tildeVect R).EssSurj where
  mem_essImage E := by
    let _ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E.obj := E.property
    have hiso := Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tildeΓIso E.obj
    exact ⟨⟨_, (isFiniteLocallyFree_tilde_functor_iff _).mp
      (SheafOfModules.IsFiniteLocallyFree.of_iso hiso.symm)⟩, ⟨ObjectProperty.isoMk _ hiso⟩⟩

/-- **The affine case of the correspondence between vector bundles and projective modules.** The
comparison functor `M ↦ M^~` from finite projective `R`-modules to finite locally free
`𝒪_{Spec R}`-modules is an equivalence of categories. -/
instance tildeVect_isEquivalence (R : CommRingCat.{u}) : (tildeVect R).IsEquivalence where

/-- **The equivalence between finite projective `R`-modules and vector bundles on `Spec R`**,
the bundled form of `AlgebraicGeometry.tildeVect_isEquivalence`. -/
noncomputable def tildeVectEquivalence (R : CommRingCat.{u}) : FinProj R ≌ (Spec R).Vect :=
  (tildeVect R).asEquivalence

/-- The equivalence of `AlgebraicGeometry.tildeVectEquivalence` is given by `M ↦ M^~`. -/
lemma tildeVectEquivalence_functor (R : CommRingCat.{u}) :
    (tildeVectEquivalence R).functor = tildeVect R :=
  rfl

/-! ### Base change -/

/-- **The affine comparison is compatible with base change.** Restricting `M^~` along
`Spec.map φ : Spec S ⟶ Spec R` gives `(S ⊗_R M)^~`, naturally in the finite projective
`R`-module `M`. -/
noncomputable def tildeVectPullbackIso (φ : R ⟶ S) :
    tildeVect R ⋙ Scheme.Vect.pullback (Spec.map φ) ≅ FinProj.extendScalars φ ⋙ tildeVect S :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _
      ((Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso φ).app L.obj))
    (fun f ↦ (ObjectProperty.ι _).map_injective
      ((Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso φ).hom.naturality f.hom))

/-- The base-change isomorphism of `AlgebraicGeometry.tildeVectPullbackIso` is the ambient one of
`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso` on underlying modules. -/
@[simp]
lemma tildeVectPullbackIso_hom_app_hom (φ : R ⟶ S) (L : FinProj R) :
    ((tildeVectPullbackIso φ).hom.app L).hom =
      (Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso φ).hom.app L.obj :=
  rfl

end AlgebraicGeometry

end
