module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensor products of quasi-coherent modules on a ringed site

The tensor product of two quasi-coherent sheaves of modules on a ringed site is quasi-coherent.
The proof is local in both factors at once: each factor is globally presented on some covering
of a given object, a Grothendieck topology is closed under intersection of covering sieves, so
the two coverings have a common refinement which is still covering, and on each member of that
refinement the tensor product of the two presentations presents the tensor product.  Taking the
refinement is what makes the statement local: a tensor product has two factors, and an
intersection of two covering sieves is covering, whereas an intersection of infinitely many need
not be.

Quasi-coherence here is `SheafOfModules.IsQuasicoherentOnSite`, Stacks 03DL(6) in the
sheafification-free formulation of `SheafOfModules.HasGlobalPresentation`, and the tensor
product is `Stacks.SheafOfModules.Tensor.sheafTensor`, equivalently the monoidal
product of `Stacks.SheafOfModules.monoidalCategory`.  The conclusion is packaged as
`CategoryTheory.ObjectProperty.IsMonoidal`, so that
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory` provides the tensor product of
quasi-coherent modules as a monoidal structure on the full subcategory they cut out.

Two ingredients are proved on the way and are of independent interest.

The first is the dictionary between the two formulations of a global presentation that the
library carries: `SheafOfModules.hasGlobalPresentation_iff_nonempty_presentation` says that
`SheafOfModules.HasGlobalPresentation`, which expresses the coproducts and the cokernel by
their universal properties and wraps the module in `SheafOfModules.uliftForPresentation`, holds
exactly when the module admits a `SheafOfModules.Presentation` by generators and relations.
The second is `Stacks.SheafOfModules.tensorSheafSliceIso`, which identifies the restriction of a
tensor product to a slice site with the tensor product formed on that slice; it is the
site-level counterpart of the restriction comparison available for an open of a ringed space.

## Main definitions

* `SheafOfModules.uliftForPresentationSelfIso`: the universe lift
  `SheafOfModules.uliftForPresentation` of a module whose sections already lie in the target
  universe is isomorphic to the module itself.
* `Stacks.SheafOfModules.sliceStructurePresheaf` and
  `Stacks.SheafOfModules.sliceRestriction`: the structure presheaf of a ringed site and its
  presheaves of modules, restricted to a slice.
* `Stacks.SheafOfModules.sliceTensorUnit`: the restriction to a slice of the sheafification unit
  of an objectwise tensor product.
* `Stacks.SheafOfModules.tensorSheafSliceIso`: restriction to a slice commutes with the tensor
  product of sheaves of modules.

## Main results

* `SheafOfModules.hasGlobalPresentation_iff_nonempty_presentation`: a global presentation in the
  sense of Stacks 03DE(6) is the same thing as a presentation by generators and relations.
* `SheafOfModules.HasGlobalPresentation.overMap`: having a global presentation is stable under
  restriction along a morphism of the site, with
  `SheafOfModules.preservesColimitsOfSize_overMap` the colimit preservation it rests on.
* `Stacks.SheafOfModules.hasGlobalPresentation_tensorSheaf`: the tensor product of two globally
  presented modules is globally presented.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf`: **the tensor product of two
  quasi-coherent modules on a ringed site is quasi-coherent.**
* `Stacks.SheafOfModules.isQuasicoherentOnSite_unit`: the structure sheaf is quasi-coherent over
  itself.
* `Stacks.SheafOfModules.tensorLE_isQuasicoherentOnSite`,
  `Stacks.SheafOfModules.containsUnit_isQuasicoherentOnSite` and
  `Stacks.SheafOfModules.isMonoidal_isQuasicoherentOnSite`: quasi-coherence is a monoidal
  property of objects.

## Implementation notes

Everything is at a universe of sections and of coefficient rings of the shape `max u v w`, with
`u` the universe of the objects of the site and `v` that of its morphisms.  This is the regime
in which the coefficient universe dominates the site, and it is forced rather than chosen.
`SheafOfModules.HasGlobalPresentation` of a module with sections in `Type m` over a sheaf of
rings with sections in `Type r` quantifies over index types in `Type (max u v r m)` and over
modules with sections there, while a tensor product of sheaves of modules exists only with the
sections in the universe of the coefficient rings, because the tensor unit is the structure
sheaf viewed as a module over itself.  So a presentation of a tensor product lives in the
category where the tensor product is formed exactly when `max u v r m` is the coefficient
universe.  Writing the coefficient universe as `max u v w` makes that equation hold by universe
normalisation.  The hypothesis `UnivLE.{max u v, w}` does *not* serve instead: it is a
proposition, so it does not collapse the universe level, and `SheafOfModules.{max u v w} R`
remains a different type from `SheafOfModules.{w} R`.  In the same regime the sheafification
facts for abelian groups hold on the site and on each of its slices with no hypothesis, so none
of them appear in the statements beyond those needed to form the tensor product itself.

The restriction comparison `Stacks.SheafOfModules.tensorSheafSliceIso` computes no
sheafification.  Both sides are sheafifications of one and the same objectwise tensor product,
by `Stacks.SheafOfModules.sliceRestriction_tensorPresheaf`, and the restriction of the
sheafification unit to the slice is still locally bijective, because
`CategoryTheory.Over.forget` is cocontinuous and restriction along a cocontinuous functor
preserves local injectivity and local surjectivity.  Since sheafification of presheaves of
modules is the localization at the locally bijective morphisms, the comparison is an
isomorphism; `CategoryTheory.Localization.isoOfHom` produces it.

The three identifications of a restricted object with the corresponding object of the slice
site -- the structure sheaf (`Stacks.SheafOfModules.structureSheaf_over`), the underlying
presheaf of a sheaf of modules (`Stacks.SheafOfModules.sliceRestriction_val`) and the objectwise
tensor product (`Stacks.SheafOfModules.sliceRestriction_tensorPresheaf`) -- are definitional, and
are named as `rfl` lemmas rather than left implicit; they are deliberately not `simp` lemmas,
since rewriting an object inside a type of morphisms produces motive failures.

The refining family of a pair of coverings is indexed by the arrows of the intersection of the
two sieves they generate, so it is a family of objects of the site and never a fixed object
chosen independently of the modules.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v r m w

namespace CategoryTheory.Limits

/-- A cofan stays a colimit after precomposing every injection with a fixed isomorphism of the
constant summand. -/
noncomputable def isColimit_cofan_comp_iso {D : Type u} [Category.{v} D] {I : Type*} {A B Z : D}
    (e : A ≅ B) (f : I → (B ⟶ Z)) (h : IsColimit (Cofan.mk Z f)) :
    IsColimit (Cofan.mk Z (fun i ↦ e.hom ≫ f i)) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc h (fun i ↦ e.inv ≫ s.inj i)) (fun s i ↦ ?_) (fun s n hn ↦ ?_)
  · simpa [Category.assoc] using
      congrArg (fun g ↦ e.hom ≫ g) (Cofan.IsColimit.fac h (fun i ↦ e.inv ≫ s.inj i) i)
  · refine Cofan.IsColimit.hom_ext h _ _ fun i ↦ ?_
    have hi := hn i
    dsimp at hi
    rw [Cofan.IsColimit.fac h (fun i ↦ e.inv ≫ s.inj i) i]
    simpa [Category.assoc] using congrArg (fun g ↦ e.inv ≫ g) hi

/-- A cofan over a one-element index type whose injection is the identity is a colimit. -/
noncomputable def isColimitCofanPUnit {D : Type u} [Category.{v} D] (X : D) :
    IsColimit (Cofan.mk X (fun _ : PUnit.{m + 1} ↦ 𝟙 X)) :=
  Cofan.IsColimit.mk _ (fun s ↦ s.inj PUnit.unit) (fun _ _ ↦ Category.id_comp _)
    (fun _ n hn ↦ (Category.id_comp n).symm.trans (hn PUnit.unit))

/-- An isomorphism exhibits its target as a cokernel of the zero morphism into its source. -/
noncomputable def isColimitCokernelCoforkOfIso {D : Type u} [Category.{v} D]
    [HasZeroMorphisms D] {Q P N : D} (e : P ≅ N) :
    IsColimit (CokernelCofork.ofπ (f := (0 : Q ⟶ P)) e.hom (by simp)) :=
  Cofork.IsColimit.mk _ (fun s ↦ e.inv ≫ s.π) (fun s ↦ by simp)
    (fun s n hn ↦ by rw [← hn]; simp)

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

/-- The universe lift `SheafOfModules.uliftForPresentation` of a sheaf of modules whose sections
already lie in the target universe is isomorphic to the sheaf itself. -/
noncomputable def uliftForPresentationSelfIso (M : SheafOfModules.{m} R) :
    uliftForPresentation.{u, v, r, m, m} M ≅ M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun X ↦ (ULift.moduleEquiv (R := R.obj.obj X) (M := M.val.obj X)).toModuleIso)
      (by intro X Y f; ext x; rfl))

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{max u v w}}
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- A global presentation in the sense of Stacks 03DE(6) yields a presentation by generators and
relations. -/
theorem HasGlobalPresentation.nonempty_presentation {M : SheafOfModules.{max u v w} R}
    (hM : M.HasGlobalPresentation) : Nonempty M.Presentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hM
  set eU : SheafOfModules.unit R ≅
      uliftForPresentation.{u, v, max u v w, max u v w, max u v w} (SheafOfModules.unit R) :=
    (uliftForPresentationSelfIso _).symm with heU
  have hP' : IsColimit (Cofan.mk P (fun i ↦ eU.hom ≫ ι i)) :=
    isColimit_cofan_comp_iso eU ι hP
  have hQ' : IsColimit (Cofan.mk Q (fun k ↦ eU.hom ≫ κ k)) :=
    isColimit_cofan_comp_iso eU κ hQ
  set eP : (free I : SheafOfModules.{max u v w} R) ≅ P :=
    (isColimitFreeCofan I).coconePointUniqueUpToIso hP' with heP
  set eQ : (free K : SheafOfModules.{max u v w} R) ≅ Q :=
    (isColimitFreeCofan K).coconePointUniqueUpToIso hQ' with heQ
  set eM := uliftForPresentationSelfIso.{u, v, max u v w, max u v w} M with heM
  have hfg : (eQ.hom ≫ a ≫ eP.inv) ≫ (eP.hom ≫ b ≫ eM.hom) = 0 := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc a b, hab,
      zero_comp, comp_zero]
  set α : parallelPair a 0 ≅ parallelPair (eQ.hom ≫ a ≫ eP.inv) (0 : free K ⟶ free I) :=
    parallelPairIsoMk eQ.symm eP.symm (by simp) (by simp) with hα
  exact ⟨presentationOfIsCokernelFree _ _ hfg
    (IsColimit.equivOfNatIsoOfIso α (CokernelCofork.ofπ b hab)
      (CokernelCofork.ofπ (eP.hom ≫ b ≫ eM.hom) hfg)
      (Cocone.ext eM (by
        rintro (_ | _) <;>
          simp [hα, parallelPairIsoMk, NatIso.ofComponents_inv_app])) hb)⟩

/-- A presentation by generators and relations yields a global presentation in the sense of
Stacks 03DE(6). -/
theorem HasGlobalPresentation.of_presentation {M : SheafOfModules.{max u v w} R}
    (p : M.Presentation) : M.HasGlobalPresentation := by
  set eU := uliftForPresentationSelfIso.{u, v, max u v w, max u v w} (SheafOfModules.unit R)
    with heU
  set eM := uliftForPresentationSelfIso.{u, v, max u v w, max u v w} M with heM
  exact ⟨p.generators.I, p.relations.I, free p.generators.I, free p.relations.I,
    fun i ↦ eU.hom ≫ ιFree i, fun k ↦ eU.hom ≫ ιFree k,
    ⟨isColimit_cofan_comp_iso eU _ (isColimitFreeCofan _)⟩,
    ⟨isColimit_cofan_comp_iso eU _ (isColimitFreeCofan _)⟩,
    (freeHomEquiv _).symm p.relations.s ≫ kernel.ι _, p.generators.π ≫ eM.inv, by simp,
    ⟨p.isColimit.ofIsoColimit (Cofork.ext eM.symm rfl)⟩⟩

/-- **The two encodings of a global presentation agree.** -/
theorem hasGlobalPresentation_iff_nonempty_presentation (M : SheafOfModules.{max u v w} R) :
    M.HasGlobalPresentation ↔ Nonempty M.Presentation :=
  ⟨fun h ↦ h.nonempty_presentation, fun ⟨p⟩ ↦ .of_presentation p⟩

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Sheafification of abelian groups exists on every slice site. -/
private theorem hasSheafify_over_addCommGrpCat (J : GrothendieckTopology C) (X : C) :
    HasSheafify (J.over X) AddCommGrpCat.{max u v w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over X)

/-- Every slice site has `WEqualsLocallyBijective` for abelian groups. -/
private theorem wEqualsLocallyBijective_over_addCommGrpCat (J : GrothendieckTopology C) (X : C) :
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
    max u v, v} (J.over X)

/-- Restriction along `Over.map` preserves colimits. -/
theorem preservesColimitsOfSize_overMap (R : Sheaf J RingCat.{max u v w}) {X Y : C} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overMap.{max u v w} R f) := by
  have := hasSheafify_over_addCommGrpCat.{u, v, w} J X
  have := hasSheafify_over_addCommGrpCat.{u, v, w} J Y
  have := wEqualsLocallyBijective_over_addCommGrpCat.{u, v, w} J X
  have := wEqualsLocallyBijective_over_addCommGrpCat.{u, v, w} J Y
  let Φ := SheafOfModules.overMap.{max u v w} R f
  let G := SheafOfModules.toSheaf.{max u v w} (R.over X)
  let H := (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{max u v w}
    (J.over X) (J.over Y)
  let : H.IsLeftAdjoint :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{max u v w}
      (J.over X) (J.over Y)).isLeftAdjoint
  let : ReflectsColimitsOfSize.{max u v w, max u v w} G :=
    reflectsColimits_of_reflectsIsomorphisms
  have e : Φ ⋙ G ≅ SheafOfModules.toSheaf.{max u v w} (R.over Y) ⋙ H := Iso.refl _
  let : PreservesColimitsOfSize.{max u v w, max u v w} (Φ ⋙ G) :=
    preservesColimits_of_natIso e.symm
  exact preservesColimits_of_reflects_of_preserves Φ G

/-- Having a global presentation is stable under restriction along a morphism of the site. -/
theorem HasGlobalPresentation.overMap {R : Sheaf J RingCat.{max u v w}}
    (M : SheafOfModules.{max u v w} R) {X Y : C} (f : X ⟶ Y)
    (h : (M.over Y).HasGlobalPresentation) : (M.over X).HasGlobalPresentation := by
  have := hasSheafify_over_addCommGrpCat.{u, v, w} J X
  have := hasSheafify_over_addCommGrpCat.{u, v, w} J Y
  have := wEqualsLocallyBijective_over_addCommGrpCat.{u, v, w} J X
  have := wEqualsLocallyBijective_over_addCommGrpCat.{u, v, w} J Y
  have : PreservesColimitsOfSize.{max u v w, max u v w}
      (SheafOfModules.overMap.{max u v w} R f) := preservesColimitsOfSize_overMap.{u, v, w} R f
  obtain ⟨p⟩ := (hasGlobalPresentation_iff_nonempty_presentation.{max u v, v, w} _).mp h
  refine (hasGlobalPresentation_iff_nonempty_presentation.{max u v, v, w} _).mpr
    ⟨Presentation.ofIsIso ((SheafOfModules.overFunctorMap R f).app M).hom
      (p.map (SheafOfModules.overMap R f)
        (SheafOfModules.overMapUnitIso f).symm)⟩

end SheafOfModules

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] TensorSheafification.structureSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The structure presheaf of a ringed site restricted to a slice. -/
abbrev sliceStructurePresheaf (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (Z : C) :
    (Over Z)ᵒᵖ ⥤ CommRingCat.{max u v w} :=
  (Over.forget Z).op ⋙ 𝒪

/-- The restricted structure presheaf is a sheaf for the slice topology. -/
theorem isSheaf_sliceStructurePresheaf {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪)) (Z : C) :
    Presheaf.IsSheaf (J.over Z)
      (TensorSheafification.structureRingPresheaf (sliceStructurePresheaf 𝒪 Z)) :=
  ((TensorSheafification.structureSheaf 𝒪 h𝒪).over Z).property

/-- The structure sheaf of the slice site is the restriction of the structure sheaf. -/
theorem structureSheaf_over {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪)) (Z : C) :
    (TensorSheafification.structureSheaf 𝒪 h𝒪).over Z =
      TensorSheafification.structureSheaf (sliceStructurePresheaf 𝒪 Z)
        (isSheaf_sliceStructurePresheaf h𝒪 Z) :=
  rfl

/-- Restriction of presheaves of modules to a slice site. -/
noncomputable abbrev sliceRestriction (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (Z : C) :
    PresheafOfModules.{max u v w} (TensorSheafification.structureRingPresheaf 𝒪) ⥤
      PresheafOfModules.{max u v w}
        (TensorSheafification.structureRingPresheaf (sliceStructurePresheaf 𝒪 Z)) :=
  PresheafOfModules.pushforward₀OfCommRingCat (Over.forget Z) 𝒪

/-- Restriction to a slice commutes with the objectwise tensor product. -/
theorem sliceRestriction_tensorPresheaf (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}) (Z : C)
    (P Q : PresheafOfModules.{max u v w} (TensorSheafification.structureRingPresheaf 𝒪)) :
    (sliceRestriction 𝒪 Z).obj ((PresheafOfModules.tensorObj (O := 𝒪) (P) (Q))) =
      (PresheafOfModules.tensorObj (O := (sliceStructurePresheaf 𝒪 Z))
        (((sliceRestriction 𝒪 Z).obj P)) (((sliceRestriction 𝒪 Z).obj Q))) :=
  rfl

section Slice

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}] in
/-- Restriction to a slice of the underlying presheaf of a sheaf of modules. -/
theorem sliceRestriction_val (Z : C)
    (M : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (sliceRestriction 𝒪 Z).obj M.val = (M.over Z).val :=
  rfl

/-- The restriction to a slice of the sheafification unit of the objectwise tensor product of
two sheaves of modules. -/
noncomputable def sliceTensorUnit (Z : C)
    (F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    PresheafOfModules.tensorObj (O := sliceStructurePresheaf 𝒪 Z)
        (F.over Z).val (G.over Z).val ⟶
      (sliceRestriction 𝒪 Z).obj
        ((SheafOfModules.forget (TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
          PresheafOfModules.restrictScalars
            (𝟙 (TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj
          (((Tensor.sheafTensor.{u, v, max u v w, max u v w, max u v w}
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪
              (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G)) :=
  (sliceRestriction 𝒪 Z).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := TensorSheafification.structureSheaf 𝒪 h𝒪)
      (𝟙 (TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).unit.app
        (PresheafOfModules.tensorObj (O := 𝒪) F.val G.val))

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The restricted sheafification unit is locally injective for the slice topology:
`CategoryTheory.Over.forget` is cocontinuous, and restriction along a cocontinuous functor
preserves local injectivity. -/
theorem isLocallyInjective_sliceTensorUnit (Z : C)
    (F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    Presheaf.IsLocallyInjective (J.over Z)
      ((PresheafOfModules.toPresheaf
        (TensorSheafification.structureRingPresheaf (sliceStructurePresheaf 𝒪 Z))).map
          (sliceTensorUnit h𝒪 Z F G)) :=
  Presheaf.isLocallyInjective_whisker (J.over Z) J (Over.forget Z)
    (CategoryTheory.toSheafify J ((PresheafOfModules.tensorObj (O := 𝒪) (F.val) (G.val))).presheaf)

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The restricted sheafification unit is locally surjective for the slice topology:
`CategoryTheory.Over.forget` is cocontinuous, and restriction along a cocontinuous functor
preserves local surjectivity. -/
theorem isLocallySurjective_sliceTensorUnit (Z : C)
    (F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    Presheaf.IsLocallySurjective (J.over Z)
      ((PresheafOfModules.toPresheaf
        (TensorSheafification.structureRingPresheaf (sliceStructurePresheaf 𝒪 Z))).map
          (sliceTensorUnit h𝒪 Z F G)) :=
  Presheaf.isLocallySurjective_whisker (J.over Z) J (Over.forget Z)
    (CategoryTheory.toSheafify J ((PresheafOfModules.tensorObj (O := 𝒪) (F.val) (G.val))).presheaf)

/-- **The tensor product of sheaves of modules commutes with restriction to a slice site.**
Both sides are sheafifications of one and the same objectwise tensor product: the restriction
of the sheafification unit is still locally bijective, because restriction along the
cocontinuous functor `CategoryTheory.Over.forget` preserves local injectivity and local
surjectivity, and sheafification of presheaves of modules is the localization at the locally
bijective morphisms.  No sheafification is computed. -/
noncomputable def tensorSheafSliceIso (Z : C)
    [(J.over Z).HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
    [(J.over Z).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    [HasWeakSheafify (J.over Z) AddCommGrpCat.{max u v w}]
    (F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(sliceStructurePresheaf 𝒪 Z),
        Presheaf.isSheaf_of_isSheaf_comp _ ((sliceStructurePresheaf 𝒪 Z))
          (forget₂ CommRingCat RingCat) ((isSheaf_sliceStructurePresheaf h𝒪 Z))⟩).obj
        ((F.over Z))).obj ((G.over Z))) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
          (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (G))).over Z :=
  let target : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪) :=
    ((Tensor.sheafTensor.{u, v, max u v w, max u v w, max u v w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp J 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G
  let sheafificationFunctor :=
    sheafifyFunctor (sliceStructurePresheaf 𝒪 Z) (isSheaf_sliceStructurePresheaf h𝒪 Z)
  let pointwise :
      (sliceRestriction 𝒪 Z).obj
          ((SheafOfModules.forget (TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
            PresheafOfModules.restrictScalars
              (𝟙 (TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj target) ≅
        (target.over Z).val :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro sectionSource sectionTarget restriction
      ext sectionValue
      rfl)
  have locallyBijective :
      localIso (J := J.over Z) (sliceStructurePresheaf 𝒪 Z) (sliceTensorUnit h𝒪 Z F G) := by
    unfold localIso MorphismProperty.inverseImage
    exact (GrothendieckTopology.W_iff_isLocallyBijective (J.over Z) _).2
      ⟨isLocallyInjective_sliceTensorUnit h𝒪 Z F G,
        isLocallySurjective_sliceTensorUnit h𝒪 Z F G⟩
  Localization.isoOfHom sheafificationFunctor
      (localIso (J := J.over Z) (sliceStructurePresheaf 𝒪 Z)) (sliceTensorUnit h𝒪 Z F G)
      locallyBijective ≪≫
    sheafificationFunctor.mapIso pointwise ≪≫
    sheafifyValIso (sliceStructurePresheaf 𝒪 Z) (isSheaf_sliceStructurePresheaf h𝒪 Z)
      (target.over Z)

end Slice

section Quasicoherent

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))

/-- **The tensor product of two globally presented sheaves of modules is globally presented.**
The tensored presentation is `Stacks.SheafOfModules.TensorProduct.tensorPresentation`; the two
encodings of a global presentation are matched by
`SheafOfModules.hasGlobalPresentation_iff_nonempty_presentation`. -/
theorem hasGlobalPresentation_tensorSheaf
    {F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (hF : F.HasGlobalPresentation) (hG : G.HasGlobalPresentation) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (G))).HasGlobalPresentation := by
  obtain ⟨p⟩ := hF.nonempty_presentation
  obtain ⟨q⟩ := hG.nonempty_presentation
  exact SheafOfModules.HasGlobalPresentation.of_presentation
    (Stacks.SheafOfModules.TensorProduct.tensorPresentation 𝒪 h𝒪 p q)

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The restriction of a tensor product to a slice is globally presented as soon as the
restrictions of the two factors are. -/
theorem hasGlobalPresentation_tensorSheaf_over (Z : C)
    {F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (hF : (F.over Z).HasGlobalPresentation) (hG : (G.over Z).HasGlobalPresentation) :
    (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (G))).over Z).HasGlobalPresentation := by
  have := SheafOfModules.hasSheafify_over_addCommGrpCat.{u, v, w} J Z
  have := SheafOfModules.wEqualsLocallyBijective_over_addCommGrpCat.{u, v, w} J Z
  have hpf : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w, max u v, max u v} _
  have hcZ : (J.over Z).HasSheafCompose
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w}) := inferInstance
  exact SheafOfModules.HasGlobalPresentation.of_iso (tensorSheafSliceIso h𝒪 Z F G)
    (hasGlobalPresentation_tensorSheaf.{max u v, v, w}
      (isSheaf_sliceStructurePresheaf h𝒪 Z) hF hG)

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- **Stacks 03DL(6) is stable under tensor product.**  The tensor product of two
quasi-coherent sheaves of modules on a ringed site is quasi-coherent.  Each factor is globally
presented on some covering of a given object; the two coverings have a common refinement, still
covering, because a Grothendieck topology is closed under intersection of covering sieves, and
on each member of that refinement the tensored presentation presents the tensor product. -/
@[ega "I 9.1.1" "more general"]
theorem isQuasicoherentOnSite_tensorSheaf
    (F G : SheafOfModules.{max u v w} (TensorSheafification.structureSheaf 𝒪 h𝒪))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪)
        (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj (F)).obj (G))).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation W := by
    obtain ⟨I₁, V₁, g₁, hc₁, hp₁⟩ :=
      SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := F) W
    obtain ⟨I₂, V₂, g₂, hc₂, hp₂⟩ :=
      SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := G) W
    have hScov : Sieve.ofArrows V₁ g₁ ⊓ Sieve.ofArrows V₂ g₂ ∈ J W :=
      J.intersection_covering hc₁ hc₂
    refine ⟨{a : Over W // (Sieve.ofArrows V₁ g₁ ⊓ Sieve.ofArrows V₂ g₂).arrows a.hom},
      fun a ↦ a.1.left, fun a ↦ a.1.hom, ?_, ?_⟩
    · have hEq : Sieve.ofArrows
          (fun a : {a : Over W //
            (Sieve.ofArrows V₁ g₁ ⊓ Sieve.ofArrows V₂ g₂).arrows a.hom} ↦ a.1.left)
          (fun a ↦ a.1.hom) = Sieve.ofArrows V₁ g₁ ⊓ Sieve.ofArrows V₂ g₂ := by
        refine le_antisymm (fun Y f hf ↦ ?_) (fun Y f hf ↦ ?_)
        · rw [Sieve.mem_ofArrows_iff] at hf
          obtain ⟨a, b, rfl⟩ := hf
          exact (Sieve.ofArrows V₁ g₁ ⊓ Sieve.ofArrows V₂ g₂).downward_closed a.2 b
        · rw [Sieve.mem_ofArrows_iff]
          exact ⟨⟨Over.mk f, hf⟩, 𝟙 Y, by simp⟩
      rw [hEq]
      exact hScov
    · intro a
      obtain ⟨ha₁, ha₂⟩ := a.2
      rw [Sieve.mem_ofArrows_iff] at ha₁ ha₂
      obtain ⟨i, b₁, -⟩ := ha₁
      obtain ⟨j, b₂, -⟩ := ha₂
      exact hasGlobalPresentation_tensorSheaf_over h𝒪 _
        (SheafOfModules.HasGlobalPresentation.overMap F b₁ (hp₁ i))
        (SheafOfModules.HasGlobalPresentation.overMap G b₂ (hp₂ j))

/-- The structure sheaf, viewed as a module over itself, is quasi-coherent: it is globally
presented on the trivial covering of every object, being a coproduct of one copy of itself with
no relations. -/
instance isQuasicoherentOnSite_unit :
    (SheafOfModules.unit (TensorSheafification.structureSheaf 𝒪 h𝒪)).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    refine ⟨PUnit.{max u v + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, ?_, fun _ ↦ ?_⟩
    · have htop : Sieve.ofArrows (fun _ : PUnit.{max u v + 1} ↦ U) (fun _ ↦ 𝟙 U) = ⊤ := by
        refine le_antisymm le_top (fun Y g _ ↦ ?_)
        rw [Sieve.mem_ofArrows_iff]
        exact ⟨PUnit.unit, g, by simp⟩
      rw [htop]
      exact J.top_mem U
    · exact ⟨PUnit.{max u v w + 1}, PUnit.{max u v w + 1}, _, _, fun _ ↦ 𝟙 _,
        fun _ ↦ 𝟙 _, ⟨isColimitCofanPUnit _⟩, ⟨isColimitCofanPUnit _⟩, 0, 𝟙 _,
        Category.comp_id _,
        ⟨isColimitCokernelCoforkOfIso (Iso.refl _)⟩⟩

end Quasicoherent

section Monoidal

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (h𝒪 : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf 𝒪))

attribute [local instance] monoidalCategory

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}] in
/-- **Quasi-coherence contains the tensor unit.** -/
instance containsUnit_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite
      (TensorSheafification.structureSheaf 𝒪 h𝒪)).ContainsUnit where
  prop_unit := isQuasicoherentOnSite_unit h𝒪

/-- **Quasi-coherence is stable under the tensor product of sheaves of modules on a ringed
site.**  The monoidal structure is `Stacks.SheafOfModules.monoidalCategory`, whose tensor
product is identified with `Stacks.SheafOfModules.Tensor.sheafTensor` by
`Stacks.SheafOfModules.tensorObjIso`. -/
@[ega "I 9.1.1" "more general"]
instance tensorLE_isQuasicoherentOnSite :
    ObjectProperty.TensorLE
      (SheafOfModules.isQuasicoherentOnSite (TensorSheafification.structureSheaf 𝒪 h𝒪))
      (SheafOfModules.isQuasicoherentOnSite (TensorSheafification.structureSheaf 𝒪 h𝒪))
      (SheafOfModules.isQuasicoherentOnSite (TensorSheafification.structureSheaf 𝒪 h𝒪)) where
  prop_tensor F G hF hG := by
    have := hF
    have := hG
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso (tensorObjIso 𝒪 h𝒪 F G).symm
      (isQuasicoherentOnSite_tensorSheaf h𝒪 F G)

/-- **Quasi-coherent modules on a ringed site form a monoidal subcategory.**  Together with
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory` this provides the tensor product of
quasi-coherent modules as a monoidal structure on the full subcategory they cut out. -/
instance isMonoidal_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite
      (TensorSheafification.structureSheaf 𝒪 h𝒪)).IsMonoidal where

end Monoidal

end Stacks.SheafOfModules

end
