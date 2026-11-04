module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleToposRingedHom
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules

/-!
# `ε⁻¹` reflects the zero sheaf

Let `ε = id_{small, étale, Zar} : S_étale → S_Zar` be the morphism of ringed sites of
Stacks 070R, for a scheme `S`.  This module shows that the inverse image `ε⁻¹` of sheaves of
modules of Stacks 03D2 *reflects the zero object*: if `ε⁻¹𝓕` vanishes then so does `𝓕`.  It is
the half of the third assertion of Stacks 08H8 that is left once faithful flatness of the
structure map has discharged the extension-of-scalars half.

The argument is elementary — no stalks, no geometric points.  By
`AlgebraicGeometry.SmallEtale.toposInverseImageAuxIso`, `ε⁻¹` of a sheaf of sets `F` on the
small Zariski site of `S` is the étale sheafification of the presheaf `V ↦ F(\mathrm{im}\, V)`
on the small étale site, the image open of an object being an open of `S` because an étale
morphism is open.  Three facts then combine.

*The image open of an open is that open* (`imageOpen_opensObj`), so the presheaf
`V ↦ F(\mathrm{im}\, V)` has `F(U)` for its sections over the object `U` of the small étale
site, and its restriction maps out of that object are restrictions of `F` along inclusions of
opens of `U`.

*A sheafification unit is locally injective*, so two sections of `F(U)` with the same image in
`ε⁻¹F` agree on a covering sieve of `U` in the small étale topology.

*A covering sieve of the small étale site is jointly surjective on points*
(`exists_mem_arrows_mem_range`), and the image of a member of that sieve is an open of `U`
containing any prescribed point, so the images of the members form an *open* covering of `U`.
Being a sheaf for the Zariski topology, `F` is separated for it, and the two sections are
equal.

So `ε⁻¹F = 0` forces every `F(U)` to be a singleton, which for a sheaf of modules is the zero
object.

## Main definitions

* `AlgebraicGeometry.SmallEtale.imageOpenPresheaf`: the presheaf `V ↦ F(\mathrm{im}\, V)` of
  sets on the small étale site of `S`, for `F` a sheaf of sets on the small Zariski site.
* `AlgebraicGeometry.SmallEtale.imageOpenToInverseImage`: the comparison map identifying its
  étale sheafification with `ε⁻¹F`.

## Main results

* `AlgebraicGeometry.SmallEtale.injective_toSheafify_imageOpenPresheaf`: the sheafification
  unit of `V ↦ F(\mathrm{im}\, V)` is injective on sections over an *open* of `S`.
* `AlgebraicGeometry.SmallEtale.subsingleton_obj_of_subsingleton_toposInverseImage`: if `ε⁻¹F`
  has subsingleton sections then so does `F`.
* `AlgebraicGeometry.SmallEtale.isZero_of_isZero_inverseImageModules`: **`ε⁻¹` of sheaves of
  modules reflects the zero object.**

## Implementation notes

The whole argument is run on the underlying sheaves of *sets*, where the inverse image is the
sheafification model `AlgebraicGeometry.SmallEtale.toposInverseImageAux` up to the canonical
comparison; only the last step returns to sheaves of modules, and it does so through the
sections, which the inverse image of a sheaf of modules shares on the nose with the inverse
image of the underlying sheaf of sets (`Stacks.Sheaves.ToposPullback.pullbackModuleAb`).

`imageOpenPresheaf` has to be a separate name rather than
`(imageOpenFunctor B S hS).op ⋙ F.obj` written out, so that the local injectivity instance for
its sheafification unit is found by instance search.

## References

* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Weak equivalences of presheaves of sets on the small étale site of `S` are the locally
bijective maps, the site being essentially small.  This is
`AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective_commRing` with `Type u` in place of
`CommRingCat.{u}`, and it is what makes a sheafification unit of presheaves of sets on the
site locally injective. -/
public instance wEqualsLocallyBijective_type :
    (topology B S hS).WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- **The presheaf of sets `V ↦ F(\mathrm{im}\, V)` on the small étale site of `S`**, for `F` a
sheaf of sets on the small Zariski site of `S`: the sections of `F` over the image open of `V`.
This is `AlgebraicGeometry.SmallEtale.imageSectionsPresheaf` with a general sheaf of sets in
place of the structure sheaf. -/
public def imageOpenPresheaf (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :
    (SmallEtale B S hS)ᵒᵖ ⥤ Type u :=
  (imageOpenFunctor B S hS).op ⋙ F.obj

/-- The value of `imageOpenPresheaf` at `V` is the sections of `F` over the image open of `V`. -/
@[simp]
public theorem imageOpenPresheaf_obj (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u))
    (V : (SmallEtale B S hS)ᵒᵖ) :
    (imageOpenPresheaf B S hS F).obj V = F.obj.obj (op (imageOpen B S hS V.unop)) := rfl

/-- **The comparison map identifying the étale sheafification of `V ↦ F(\mathrm{im}\, V)` with
`ε⁻¹F`.**  This is `AlgebraicGeometry.SmallEtale.inverseImageIso` with a general sheaf of sets
in place of the structure sheaf. -/
public noncomputable def imageOpenToInverseImage
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :
    sheafify (topology B S hS) (imageOpenPresheaf B S hS F) ⟶
      ((toposInverseImage B S hS).obj F).obj :=
  ((toposInverseImageAuxIso B S hS).app F).hom.hom

/-- The comparison map `imageOpenToInverseImage` is an isomorphism. -/
public instance isIso_imageOpenToInverseImage
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) :
    IsIso (imageOpenToInverseImage B S hS F) :=
  inferInstanceAs (IsIso ((sheafToPresheaf (topology B S hS) (Type u)).mapIso
    ((toposInverseImageAuxIso B S hS).app F)).hom)

/-- **The sheafification unit of `V ↦ F(\mathrm{im}\, V)` is injective over an open of `S`.**

Two sections of `F` over the image open of `U` — that is, over `U` itself — with the same image
in the sheafification agree on a covering sieve of `U` in the small étale topology, local
injectivity of a sheafification unit.  A covering sieve of the small étale site is jointly
surjective on points, so every point of `U` lies in the image of some member, and that image is
an open of `U` over which the two sections agree.  The images of the members therefore form an
open covering of `U`, and `F` is separated for it. -/
public theorem injective_toSheafify_imageOpenPresheaf
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u)) (U : S.Opens) :
    Function.Injective
      ((toSheafify (topology B S hS) (imageOpenPresheaf B S hS F)).app
        (op (opensObj B S hS U))) := by
  intro x y hxy
  have hcov := Presheaf.equalizerSieve_mem (topology B S hS)
    (toSheafify (topology B S hS) (imageOpenPresheaf B S hS F)) x y hxy
  refine F.2.isSeparated (imageOpen B S hS (opensObj B S hS U))
    (Presheaf.equalizerSieve (F := F.obj) x y) ?_ x y (fun _ _ hf => by exact hf)
  intro p hp
  obtain ⟨q, hq⟩ : p ∈ Set.range ⇑U.ι := hp
  obtain ⟨W, g, hg, w, hw⟩ := exists_mem_arrows_mem_range B S hS hcov q
  refine ⟨imageOpen B S hS W, homOfLE (imageOpen_le_imageOpen B S hS g), hg, w, ?_⟩
  change (W.obj.hom.hom) w = p
  rw [BigEtaleOver.hom_hom_eq B S hS g.hom]
  change U.ι.base ((toScheme B S hS).map g w) = p
  rw [hw, hq]

/-- **`ε⁻¹` reflects subsingleton sections of a sheaf of sets.**  The sections of `ε⁻¹F` over an
*open* of `S`, viewed in the small étale site, receive the sections of `F` over that open
injectively, by `AlgebraicGeometry.SmallEtale.injective_toSheafify_imageOpenPresheaf` read
through `AlgebraicGeometry.SmallEtale.imageOpenToInverseImage`. -/
public theorem subsingleton_obj_of_subsingleton_toposInverseImage
    (F : Sheaf (Opens.grothendieckTopology ↥S) (Type u))
    (h : ∀ T : (SmallEtale B S hS)ᵒᵖ,
      Subsingleton (((toposInverseImage B S hS).obj F).obj.obj T))
    (U : S.Opens) : Subsingleton (F.obj.obj (op U)) := by
  have hinj : Function.Injective
      ((imageOpenToInverseImage B S hS F).app (op (opensObj B S hS U))) :=
    ((isIso_iff_bijective _).1 inferInstance).1
  have h1 : Subsingleton ((sheafify (topology B S hS) (imageOpenPresheaf B S hS F)).obj
      (op (opensObj B S hS U))) :=
    ⟨fun x y => hinj ((h _).elim _ _)⟩
  have h2 : Subsingleton (F.obj.obj (op (imageOpen B S hS (opensObj B S hS U)))) :=
    ⟨fun x y => injective_toSheafify_imageOpenPresheaf B S hS F U (h1.elim _ _)⟩
  rwa [imageOpen_opensObj] at h2

/-- **`ε⁻¹` on sheaves of modules**: the inverse image of Stacks 03D2 along the morphism of
topoi underlying `ε = id_{small, étale, Zar} : S_étale → S_Zar`.  Named with its source and
target categories spelled out, so that the universes of the two sites are solved for from the
shape of the type, exactly as for
`AlgebraicGeometry.SmallEtale.toZariskiModulePullback`. -/
public noncomputable abbrev toZariskiModuleInverseImage :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O) ⥤
      SheafOfModules.{u} (inverseImageRingSheaf (toposHom B S hS)
        (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)) :=
  inverseImageModules (toposHom B S hS)
    (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)

/-- **The inverse image `ε⁻¹` of sheaves of modules along
`ε = id_{small, étale, Zar} : S_étale → S_Zar` reflects the zero object**: if `ε⁻¹𝓕` vanishes
then so does `𝓕`.

This is the inverse-image half of the third assertion of Stacks 08H8.  It is *not* the full
assertion: the pullback `ε^*` of Stacks 03D6 (2) is the inverse image followed by extension of
scalars along the structure map, and the extension-of-scalars half is discharged, in the
namespace `Stacks.Sheaves.RingedToposModules`, by
`isZero_of_isZero_extendScalars_obj_of_locallyFaithfullyFlat_comp`. -/
public theorem isZero_of_isZero_inverseImageModules
    (𝓕 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O))
    (h : IsZero ((toZariskiModuleInverseImage B S hS).obj 𝓕)) :
    IsZero 𝓕 := by
  let F : Sheaf (Opens.grothendieckTopology ↥S) (Type u) :=
    Sheaf.moduleSheaf.{u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O) 𝓕
  exact Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections.{u, u, u} 𝓕 fun V =>
    subsingleton_obj_of_subsingleton_toposInverseImage B S hS F
      (fun T => Stacks.subsingleton_of_isZero h T) V.unop

end AlgebraicGeometry.SmallEtale

end
