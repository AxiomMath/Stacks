module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# A free sheaf of modules is the sheafification of the free presheaf of modules

Let `R : Sheaf J RingCat` be a sheaf of rings on a site and `I` a type. Mathlib defines
`SheafOfModules.free I` as the coproduct `∐ (fun _ : I ↦ SheafOfModules.unit R)` taken *in the
category of sheaves of modules*. For infinite `I` that coproduct is not computed objectwise, so
nothing about the sections of `free I` can be read off from the definition.

This file supplies the missing description. The coproduct
`freePres R I = ∐ (fun _ : I ↦ PresheafOfModules.unit R.obj)` taken in presheaves of modules
*is* computed objectwise, and sheafification is a left adjoint, so it carries that coproduct to
the coproduct in sheaves of modules. Hence `free I` is the sheafification of `freePres R I`
(`freeIso`), and the canonical morphism `toFree R I : freePres R I ⟶ (free I).val` is locally
surjective (`isLocallySurjective_toFree`): every section of `free I` is, after restriction along
the arrows of a covering sieve, a section of the objectwise coproduct.

## Main definitions

* `freePres`: the coproduct of `I` copies of `𝒪`, taken in presheaves of modules.
* `toFree`: the canonical morphism `freePres R I ⟶ (SheafOfModules.free I).val`.
* `freeCompare`: the induced morphism from the sheafification of `freePres R I` to `free I`.

## Main results

* `freeIso`: `(PresheafOfModules.sheafification (𝟙 R.obj)).obj (freePres R I) ≅
  SheafOfModules.free I`, i.e. a free sheaf of modules is the sheafification of the free
  presheaf of modules on the same index type.
* `isLocallySurjective_toFree`: `toFree R I` is locally surjective.
* `imageSieve_toFree_mem`: the section-level form, saying that a section of `free I` over `V`
  lies, locally on `V`, in the image of the objectwise coproduct.

## Implementation notes

The identification is obtained from the universal properties, not from a computation. The
cocone on `shf.obj (freePres R I)` whose legs are `shf.map (Sigma.ι _ i)` is colimiting because
`shf` is a left adjoint, and the counit of the sheafification adjunction identifies its vertices
`shf.obj (PresheafOfModules.unit R.obj)` with `SheafOfModules.unit R`; comparing the two
colimiting cocones gives `freeIso`. Local surjectivity then follows exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective`: the composite of `shf`
with `SheafOfModules.toSheaf` is definitionally the abelian-group sheafification of the
underlying presheaf, so an isomorphism after `shf` is local surjectivity before it.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u u'

namespace Stacks.SheafOfModules.FreeSheafification

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafification functor from presheaves of `R.obj`-modules to sheaves of `R`-modules.
This is `PresheafOfModules.sheafification (𝟙 R.obj)`. -/
noncomputable abbrev shf : PresheafOfModules.{u} R.obj ⥤ SheafOfModules.{u} R :=
  PresheafOfModules.sheafification (J := J) (𝟙 R.obj)

/-- The free *presheaf* of modules on a type `I`: the coproduct of `I` copies of
`PresheafOfModules.unit R.obj`, taken in presheaves of modules. Unlike the coproduct in sheaves
of modules, this one is computed objectwise. -/
noncomputable abbrev freePres (I : Type u) : PresheafOfModules.{u} R.obj :=
  ∐ (fun _ : I ↦ PresheafOfModules.unit R.obj)

/-- The canonical morphism of presheaves of modules from the free presheaf of modules on `I` to
the presheaf underlying the free sheaf of modules on `I`, given on the `i`-th summand by the
`i`-th inclusion `SheafOfModules.ιFree i`. -/
noncomputable def toFree (I : Type u) :
    freePres R I ⟶ (SheafOfModules.free (R := R) I).val :=
  Sigma.desc (fun i ↦ (SheafOfModules.ιFree (R := R) i).val)

/-- The restriction of `toFree R I` to the `i`-th summand is `SheafOfModules.ιFree i`. -/
@[reassoc (attr := simp)]
lemma ι_toFree (I : Type u) (i : I) :
    Sigma.ι (fun _ : I ↦ PresheafOfModules.unit R.obj) i ≫ toFree R I =
      (SheafOfModules.ιFree (R := R) i).val :=
  Sigma.ι_desc _ _

/-- The sheafification of `PresheafOfModules.unit R.obj` is `SheafOfModules.unit R`: a sheaf of
modules is its own sheafification, and `SheafOfModules.unit R` is by definition the sheaf of
modules whose underlying presheaf is `PresheafOfModules.unit R.obj`. -/
noncomputable abbrev unitIsoVal :
    (shf R).obj (SheafOfModules.unit R).val ≅ SheafOfModules.unit R :=
  asIso (EpiMono.counitApp (SheafOfModules.unit R))

/-- `unitIsoVal` retyped. Its source is stated as the sheafification of
`PresheafOfModules.unit R.obj`, which is the form every statement below needs; writing the
source as `(SheafOfModules.unit R).val`, as `EpiMono.counitApp` does, puts a semireducible
projection in the way of instance search and of `rw`. -/
noncomputable def unitIso :
    (shf R).obj (PresheafOfModules.unit R.obj) ≅ SheafOfModules.unit R :=
  unitIsoVal R

/-- The forward map of `unitIso R` is the counit of sheafification at `SheafOfModules.unit R`. -/
lemma unitIso_hom : (unitIso R).hom = EpiMono.counitApp (SheafOfModules.unit R) := rfl

/-- Two morphisms out of a free sheaf of modules are equal as soon as they become equal after
composition with every inclusion `SheafOfModules.ιFree i`. This is `freeHomEquiv` spelled out
as an extensionality principle; unlike `Cofan.IsColimit.hom_ext` it is stated at the type
`SheafOfModules.free I` itself rather than at the vertex of `SheafOfModules.freeCofan I`, which
matters because the latter mentions the coproduct's unexposed choice of colimit cocone. -/
lemma free_hom_ext {I : Type u} {M : SheafOfModules.{u} R}
    {f g : SheafOfModules.free (R := R) I ⟶ M}
    (h : ∀ i, SheafOfModules.ιFree (R := R) i ≫ f = SheafOfModules.ιFree i ≫ g) : f = g :=
  (SheafOfModules.freeHomEquiv M).injective (funext fun i ↦
    show M.unitHomEquiv (SheafOfModules.ιFree i ≫ f)
        = M.unitHomEquiv (SheafOfModules.ιFree i ≫ g) from congrArg _ (h i))

/-- The morphism from the sheafification of the free presheaf of modules on `I` to the free
sheaf of modules on `I`, obtained from `toFree` by the universal property of sheafification. -/
noncomputable def freeCompare (I : Type u) :
    (shf R).obj (freePres R I) ⟶ SheafOfModules.free (R := R) I :=
  (shf R).map (toFree R I) ≫ EpiMono.counitApp (SheafOfModules.free (R := R) I)

/-- The composite of the sheafified `i`-th coproduct inclusion with `freeCompare R I` is
`(unitIso R).hom ≫ SheafOfModules.ιFree i`. -/
lemma map_ι_freeCompare (I : Type u) (i : I) :
    (shf R).map (Sigma.ι (fun _ : I ↦ PresheafOfModules.unit R.obj) i) ≫ freeCompare R I =
      (unitIso R).hom ≫ SheafOfModules.ιFree (R := R) i := by
  rw [freeCompare, ← Functor.map_comp_assoc, ι_toFree]
  exact EpiMono.counitApp_naturality (SheafOfModules.ιFree (R := R) i)

/-- The inverse of `freeCompare`, built from the universal property of `free I` as a coproduct
in sheaves of modules. -/
noncomputable def freeCompareInv (I : Type u) :
    SheafOfModules.free (R := R) I ⟶ (shf R).obj (freePres R I) :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (R := R) I)
    (fun i ↦ (unitIso R).inv ≫
      (shf R).map (Sigma.ι (fun _ : I ↦ PresheafOfModules.unit R.obj) i))

/-- The composite of `SheafOfModules.ιFree i` with `freeCompareInv R I` is `(unitIso R).inv`
followed by the sheafified `i`-th coproduct inclusion. -/
@[reassoc]
lemma ιFree_freeCompareInv (I : Type u) (i : I) :
    SheafOfModules.ιFree (R := R) i ≫ freeCompareInv R I =
      (unitIso R).inv ≫
        (shf R).map (Sigma.ι (fun _ : I ↦ PresheafOfModules.unit R.obj) i) := by
  rw [freeCompareInv, ← SheafOfModules.freeCofan_inj]
  exact Cofan.IsColimit.fac _ _ i

/-- The comparison morphism `freeCompare` is an isomorphism: both its source and its target are
colimiting cocone points for the family of `I` copies of `SheafOfModules.unit R` -- the source
because `shf` is a left adjoint and hence preserves the coproduct -- and `freeCompare` is the
comparison map between them. -/
instance isIso_freeCompare (I : Type u) : IsIso (freeCompare R I) := by
  refine ⟨freeCompareInv R I, ?_, ?_⟩
  · refine Cofan.IsColimit.hom_ext
      (isColimitOfHasCoproductOfPreservesColimit (shf R)
        (fun _ : I ↦ PresheafOfModules.unit R.obj)) _ _ fun i ↦ ?_
    rw [cofan_mk_inj, ← Category.assoc, map_ι_freeCompare, Category.assoc,
      ιFree_freeCompareInv, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · refine free_hom_ext R fun i ↦ ?_
    rw [← Category.assoc, ιFree_freeCompareInv, Category.assoc, map_ι_freeCompare,
      Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

/-- **A free sheaf of modules is the sheafification of the free presheaf of modules.**  This is
the description of `(SheafOfModules.free I).val` that the definition of `free I` as a coproduct
in sheaves of modules does not provide: for infinite `I` that coproduct is not objectwise, but
the coproduct `freePres R I` in presheaves of modules is, and `free I` is its sheafification. -/
noncomputable def freeIso (I : Type u) :
    (shf R).obj (freePres R I) ≅ SheafOfModules.free (R := R) I :=
  asIso (freeCompare R I)

/-- The forward map of `freeIso R I` is `freeCompare R I`. -/
@[simp]
lemma freeIso_hom (I : Type u) : (freeIso R I).hom = freeCompare R I := rfl

/-- Sheafifying `toFree R I` gives an isomorphism of sheaves of modules. -/
instance isIso_shf_map_toFree (I : Type u) : IsIso ((shf R).map (toFree R I)) :=
  have : IsIso ((shf R).map (toFree R I) ≫
    EpiMono.counitApp (SheafOfModules.free (R := R) I)) := isIso_freeCompare R I
  IsIso.of_isIso_comp_right _ (EpiMono.counitApp (SheafOfModules.free (R := R) I))

/-- **The canonical morphism from the objectwise coproduct to a free sheaf of modules is locally
surjective.**  Every section of `SheafOfModules.free I` becomes, after restriction along the
arrows of a covering sieve, a section of the coproduct `freePres R I`, which is computed
objectwise. -/
theorem isLocallySurjective_toFree (I : Type u) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map (toFree R I)) := by
  have h2 : IsIso ((SheafOfModules.toSheaf R).map ((shf R).map (toFree R I))) := inferInstance
  have h3 : IsIso ((presheafToSheaf J AddCommGrpCat.{u}).map
      ((PresheafOfModules.toPresheaf R.obj).map (toFree R I))) := h2
  exact (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).1
    (Sheaf.isLocallySurjective_of_iso _)

/-- **Section-level form.**  For every section `s` of the free sheaf of modules on `I` over an
object `V`, the sieve of arrows `g : W ⟶ V` along which `s` restricts to a section of the
objectwise coproduct `freePres R I` is a covering sieve of `V`. -/
theorem imageSieve_toFree_mem (I : Type u) {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj
      (SheafOfModules.free (R := R) I).val).obj (op V))) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map (toFree R I)) s ∈ J V :=
  have := isLocallySurjective_toFree R I
  Presheaf.imageSieve_mem J _ s

end Stacks.SheafOfModules.FreeSheafification

end
