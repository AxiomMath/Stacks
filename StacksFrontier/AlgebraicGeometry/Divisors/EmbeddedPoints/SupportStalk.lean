module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Support

/-!
# Supports of sheaves of modules, read off their stalks

The support of a sheaf of modules on a scheme is the set of points where the stalk is nontrivial.
This file collects the consequences of that description which are needed to compare the supports
of a sheaf, of a subsheaf of it, and of the corresponding quotient.

The stalk functor is exact on the right — it preserves colimits — so it sends the cokernel of a
morphism to the cokernel of the induced map on stalks. Hence a point outside the support of a
subsheaf is one where the quotient map is an isomorphism on stalks, and a point outside the
support of the ambient sheaf is one where the quotient has vanishing stalk. The support of a
quotient therefore lies inside the support of the sheaf and contains every point of it that is
outside the support of the subsheaf.

## Main results

* `Stacks.AlgebraicGeometry.EmbeddedPoints.supp_eq_setOf_nontrivial_stalk`: the support is the
  set of points with nontrivial stalk.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.supp_subobject_subset_supp`: the support of a
  subsheaf lies in the support of the sheaf.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.supp_cokernel_subset_supp`: the support of a quotient
  lies in the support of the sheaf.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.mem_supp_cokernel_of_mem_supp_of_notMem_supp`: a point
  of the support of the sheaf which is outside the support of the subsheaf lies in the support of
  the quotient.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.isZero_stalkFunctor_obj_sSup`: a supremum of
  subobjects all of whose stalks vanish at a point has vanishing stalk there.
* `Stacks.AlgebraicGeometry.EmbeddedPoints.isClosed_supp_of_isFiniteType`: the support of a
  module of finite type is closed.

## Implementation notes

Two notions of support coexist: `SheafOfModules.supp`, for a sheaf of modules over a sheaf of
rings on a topological space, and `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp`. They agree,
by `SheafOfModules.supp_eq_moduleSheaf_supp`, and the statements below are phrased with the
latter because that is the spelling in which the support of a module on a scheme appears.

## References

* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

variable {X : Scheme.{u}}

/-- The support of a sheaf of modules on a scheme is the set of points at which its stalk is
nontrivial. -/
lemma supp_eq_setOf_nontrivial_stalk (F : X.Modules) :
    (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp =
      {x | Nontrivial (((Scheme.Modules.toPresheaf X).obj F).stalk x)} := by
  let F' : SheafOfModules
      ((sheafCompose (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (forget₂ CommRingCat RingCat)).obj X.toRingedSpace.sheaf) := F
  change (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F').supp = _
  rw [SheafOfModules.supp_eq_moduleSheaf_supp (F := F')]
  ext x
  exact SheafOfModules.mem_supp_iff_nontrivial_stalk F' x

/-- A module over a ring whose underlying object is a zero object is a subsingleton. -/
lemma subsingleton_of_isZero {R : Type u} [Ring R] {A : ModuleCat.{u} R} (hA : IsZero A) :
    Subsingleton A := by
  have hid : (𝟙 A : A ⟶ A) = 0 := (IsZero.iff_id_eq_zero A).mp hA
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have h := congrArg (fun f : A ⟶ A => ConcreteCategory.hom f a) hid
    simpa using h
  have hb : b = 0 := by
    have h := congrArg (fun f : A ⟶ A => ConcreteCategory.hom f b) hid
    simpa using h
  exact ha.trans hb.symm

/-- A module is not nontrivial exactly when it is a zero object. -/
private lemma not_nontrivial_iff_isZero {R : Type u} [Ring R] {A : ModuleCat.{u} R} :
    ¬ Nontrivial A ↔ IsZero A := by
  rw [ModuleCat.isZero_iff_subsingleton, not_nontrivial_iff_subsingleton]

/-- A monomorphism of sheaves of modules is injective on stalks: passing to the underlying
abelian sheaf preserves monomorphisms, and so does taking stalks of abelian sheaves.

The hypothesis `Mono f` is an explicit argument rather than an instance argument: the category
structure on `X.Modules` and the one on the source of `SheafOfModules.toSheaf` are definitionally
but not reducibly equal, so instance synthesis does not transfer a monomorphism from one spelling
to the other. -/
lemma injective_stalkFunctor_map {M N : X.Modules} (f : M ⟶ N) (hf : Mono f) (x : X) :
    Function.Injective
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) := by
  have hp : (SheafOfModules.toSheaf X.ringCatSheaf).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have hm : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    @Functor.map_mono _ _ _ _ (SheafOfModules.toSheaf X.ringCatSheaf) hp _ _ f hf
  refine (AddCommGrpCat.mono_iff_injective _).mp ?_
  exact @TopCat.Presheaf.stalk_mono_of_mono AddCommGrpCat.{u} _ _ _ _ _ _ _ _ _ _ _ _ _
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) hm x

/-- Outside its support, a sheaf of modules has vanishing stalk. -/
lemma isZero_stalkFunctor_obj_of_notMem_supp (M : X.Modules) {x : X}
    (hx : x ∉ (⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M) := by
  rw [supp_eq_setOf_nontrivial_stalk] at hx
  exact not_nontrivial_iff_isZero.mp hx

/-- A colimit-preserving additive functor sends the projection to the cokernel of a morphism with
vanishing source to an isomorphism. -/
lemma isIso_map_cokernelπ_of_isZero
    {C : Type (u + 1)} [Category.{u, u + 1} C] [Preadditive C] [HasZeroObject C]
    {D : Type (u + 1)} [Category.{u, u + 1} D] [Preadditive D] [HasZeroObject D]
    (T : C ⥤ D) [T.PreservesZeroMorphisms] [PreservesColimits T]
    {A B : C} (f : A ⟶ B) [HasCokernel f] (hA : IsZero (T.obj A)) :
    IsIso (T.map (cokernel.π f)) := by
  have hf : T.map f = 0 := hA.eq_of_src _ _
  have hπ : IsIso (cokernel.π (T.map f)) := cokernel.π_of_zero hf
  have hc : T.map (cokernel.π f) ≫ (PreservesCokernel.iso T f).hom =
      cokernel.π (T.map f) := PreservesCokernel.π_iso_hom (G := T) (f := f)
  have hcomp : IsIso (T.map (cokernel.π f) ≫ (PreservesCokernel.iso T f).hom) := by
    rw [hc]; exact hπ
  exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso T f).hom

/-- A colimit-preserving additive functor sends the cokernel of a morphism with vanishing target
to a zero object. -/
lemma isZero_map_cokernel_of_isZero
    {C : Type (u + 1)} [Category.{u, u + 1} C] [Preadditive C]
    {D : Type (u + 1)} [Category.{u, u + 1} D] [Preadditive D]
    (T : C ⥤ D) [T.PreservesZeroMorphisms] [PreservesColimits T]
    {A B : C} (f : A ⟶ B) [HasCokernel f] (hB : IsZero (T.obj B)) :
    IsZero (T.obj (cokernel f)) := by
  have hf : T.map f = 0 := hB.eq_of_tgt _ _
  have hPC : PreservesColimit (parallelPair f 0) T := inferInstance
  have hπ : IsIso (cokernel.π (T.map f)) := cokernel.π_of_zero hf
  have htarget : IsZero (cokernel (T.map f)) :=
    IsZero.of_iso hB (asIso (cokernel.π (T.map f))).symm
  exact IsZero.of_iso htarget (PreservesCokernel.iso T f)

/-- A colimit of modules all of which are zero objects is a zero object. -/
lemma isZero_colimit {R : Type*} [Ring R] {J : Type*} [Category J]
    (D : J ⥤ ModuleCat R) [HasColimit D] (hD : ∀ j, IsZero (D.obj j)) :
    IsZero (colimit D) :=
  (colimit.isColimit D).isZero_pt (D.isZero hD)

/-- If every member of a set of subobjects has vanishing stalk at `x`, so does their
supremum: the supremum is the image of the coproduct of the members, and the stalk functor
preserves both the coproduct and the epimorphism onto the image. -/
lemma isZero_stalkFunctor_obj_sSup (F : X.Modules) (S : Set (Subobject F)) (x : X)
    (hS : ∀ L ∈ S, IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      X.ringCatSheaf x).obj (L : X.Modules))) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      (Subobject.sSup S : X.Modules)) := by
  classical
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  let E := equivShrink (Subobject F) '' S
  let A : E → X.Modules := fun j => (equivShrink (Subobject F)).symm j
  let D : Discrete E ⥤ X.Modules := Discrete.functor A
  have hcol : HasColimit D := inferInstance
  have hTc : PreservesColimits T := inferInstance
  have hDT : PreservesColimit D T := hTc.preservesColimitsOfShape.preservesColimit
  have hD : ∀ j, IsZero ((D ⋙ T).obj j) := by
    intro j
    exact hS _ ((Subobject.symm_apply_mem_iff_mem_image
      (equivShrink (Subobject F)) S j.as).mpr j.as.property)
  have hcop : IsZero (T.obj (@colimit _ _ _ _ D hcol)) :=
    IsZero.of_iso (@isZero_colimit _ _ _ _ (D ⋙ T) inferInstance hD)
      (@preservesColimitIso _ _ _ _ T _ _ D hDT hcol)
  let σ := Subobject.smallCoproductDesc S
  have him : HasImage σ := inferInstance
  let e := @factorThruImage _ _ _ _ σ him
  have hpe : T.PreservesEpimorphisms := preservesEpimorphisms_of_preservesColimitsOfShape _
  have hes : Epi e := by dsimp only [e, σ]; infer_instance
  have hepi : Epi (T.map e) := @Functor.map_epi _ _ _ _ T hpe _ _ e hes
  have hImage : IsZero (T.obj (@image _ _ _ _ σ him)) :=
    ModuleCat.isZero_iff_subsingleton.mpr <| @Function.Surjective.subsingleton _ _ _
      (ModuleCat.isZero_iff_subsingleton.mp hcop) ((ModuleCat.epi_iff_surjective _).mp hepi)
  exact IsZero.of_iso hImage (T.mapIso (Subobject.underlyingIso (@image.ι _ _ _ _ σ him)))

/-- The support of a subsheaf is contained in the support of the sheaf. -/
lemma supp_subobject_subset_supp (F : X.Modules) (K : Subobject F) :
    (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆
        (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp := by
  rw [supp_eq_setOf_nontrivial_stalk, supp_eq_setOf_nontrivial_stalk]
  intro x hx
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hK : Nontrivial (T.obj (K : X.Modules)) := hx
  exact (injective_stalkFunctor_map K.arrow inferInstance x).nontrivial

/-- The support of a quotient of a sheaf of modules is contained in the support of the sheaf. -/
lemma supp_cokernel_subset_supp (F : X.Modules) (K : Subobject F) :
    (⟨(cokernel K.arrow).val, (cokernel K.arrow).isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ⊆
        (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp := by
  rw [supp_eq_setOf_nontrivial_stalk, supp_eq_setOf_nontrivial_stalk]
  intro x hx
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  change Nontrivial (T.obj (cokernel K.arrow)) at hx
  by_contra hF
  exact not_nontrivial_iff_isZero.mpr
    (isZero_map_cokernel_of_isZero T K.arrow (not_nontrivial_iff_isZero.mp hF)) hx

/-- A point in the support of a sheaf of modules but outside the support of a subsheaf lies in
the support of the quotient. -/
lemma mem_supp_cokernel_of_mem_supp_of_notMem_supp (F : X.Modules) (K : Subobject F) {x : X}
    (hxF : x ∈ (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp)
    (hxK : x ∉ (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp) :
    x ∈ (⟨(cokernel K.arrow).val, (cokernel K.arrow).isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp := by
  rw [supp_eq_setOf_nontrivial_stalk] at hxF hxK ⊢
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hFnon : Nontrivial (T.obj F) := hxF
  have hπ := isIso_map_cokernelπ_of_isZero T K.arrow (not_nontrivial_iff_isZero.mp hxK)
  change Nontrivial (T.obj (cokernel K.arrow))
  by_contra hQ
  exact not_nontrivial_iff_isZero.mpr
    ((not_nontrivial_iff_isZero.mp hQ).of_iso (@asIso _ _ _ _ _ hπ)) hFnon

/-- The support of a sheaf of modules of finite type is closed.

Finite type is an explicit argument rather than an instance argument because the two
definitionally equal spellings of the category of modules on a scheme are not reducibly equal, so
instance synthesis does not see an instance stated in the other one. -/
lemma isClosed_supp_of_isFiniteType (M : X.Modules) (hM : M.IsFiniteType) :
    IsClosed ((⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) := by
  let M' : SheafOfModules
      ((sheafCompose (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.toRingedSpace.sheaf) := M
  have : M'.IsFiniteType := hM
  have h := SheafOfModules.isClosed_supp M'
  rw [← SheafOfModules.supp_eq_moduleSheaf_supp (F := M')] at h
  simpa [M', AlgebraicGeometry.SheafOfModules.moduleSheafOfModules] using h

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
