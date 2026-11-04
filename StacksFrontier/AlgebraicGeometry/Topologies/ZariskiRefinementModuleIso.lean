module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.LocalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiRefinementLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A Zariski-locally bijective comparison of modules on a site refining Zariski coverings

Condition (2) of Tag 03OJ says that any Zariski covering of an object `T` of a site `C` of
schemes over `S` can be refined by a covering of `C`. On such a site, a morphism of sheaves of
modules is an isomorphism as soon as its sections lift, and its equalities of sections hold, after
restriction along the arrows factoring through a member of a Zariski covering.

The file also computes global sections of pullbacks of modules to an affine scheme: the global
sections of the pullback of a free `𝒪_S`-module are the finitely supported families of regular
functions, and taking global sections of the pullback carries a right exact sequence of
quasi-coherent modules on `S` to a right exact sequence.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv`: the identification of the global
  sections of the pullback of a free `𝒪_S`-module along a morphism from an affine scheme with the
  finitely supported families of regular functions.
* `AlgebraicGeometry.Scheme.Modules.freeTautologicalSection`: the `l`-th tautological global
  section of the pullback of `⊕_L 𝒪_S`.
* `AlgebraicGeometry.Scheme.Modules.freeSectionsCombination`: finite sums of multiples of the
  tautological sections.

## Main results

* `Stacks.Sites.isIso_of_zariskiRefinement`: a morphism of sheaves of modules on a site refining
  Zariski coverings whose sections lift and whose equalities hold after restriction along the
  arrows factoring through a member of a Zariski covering is an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv_single`: the identification
  `pullbackFreeSectionsEquiv` carries `Finsupp.single l r` to `r` times the `l`-th tautological
  section.
* `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_comp` and
  `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso_comp_eq`: the identification of the pullback
  of a free module with the free module is compatible with composition of morphisms of schemes.
* `AlgebraicGeometry.Scheme.Modules.pullbackSectionsMap_freeTautologicalSection`: the pullback
  map on global sections of Tag 03DS carries the `l`-th tautological section of the pullback of
  `⊕_L 𝒪_S` to the `l`-th tautological section of its pullback further down.
* `AlgebraicGeometry.Scheme.Modules.surjective_pullback_map_appTop_of_epi`: an epimorphism of
  quasi-coherent modules on `S` stays surjective on the global sections of its pullback to an
  affine scheme.
* `AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_cokernelπ_app_eq_zero` and
  `AlgebraicGeometry.Scheme.Modules.exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero`:
  the sections over an affine open, respectively the global sections of a pullback to an affine
  scheme, are exact in the middle at a morphism of quasi-coherent modules and the projection onto
  its cokernel.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)
  (K : Precoverage C)

/-- **A Zariski-locally bijective comparison of sheaves of modules on a site refining Zariski
coverings is an isomorphism.**

Let `C` be a site of schemes over `S` satisfying condition (2) of Tag 03OJ: every Zariski
covering of the underlying scheme of an object can be refined by a covering of `C`.  Let
`α : M ⟶ N` be a morphism of sheaves of modules over a sheaf of rings on `C` such that

* every section of `N` over an object `T` admits a Zariski covering of the underlying scheme of
  `T` along whose refinement by `C` the section lifts through `α`, and
* two sections of `M` over `T` with the same image admit a Zariski covering along whose
  refinement by `C` they become equal.

Then `α` is an isomorphism.  The Zariski covering may depend on the section, respectively on the
pair of sections. -/
public theorem isIso_of_zariskiRefinement
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{u}]
    [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {O : Sheaf K.toGrothendieck RingCat.{u}} {M N : SheafOfModules.{u} O} (α : M ⟶ N)
    (hsurj : ∀ (T : C) (s : ToType (N.val.obj (op T))),
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              ∃ t : ToType (M.val.obj (op Z)),
                α.val.app (op Z) t = N.val.map f.op s)
    (hinj : ∀ (T : C) (x y : ToType (M.val.obj (op T))),
      α.val.app (op T) x = α.val.app (op T) y →
      ∃ R : Presieve ((toOver.obj T).left),
        R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) ∧
          ∀ ⦃Z : C⦄ (f : Z ⟶ T),
            (Sieve.generate R).arrows ((toOver ⋙ Over.forget S).map f) →
              M.val.map f.op x = M.val.map f.op y) :
    IsIso α := by
  have hs : Presheaf.IsLocallySurjective K.toGrothendieck
      ((PresheafOfModules.toPresheaf O.obj).map α.val) :=
    isLocallySurjective_of_zariskiRefinement S toOver K hZariski _ hsurj
  have hi : Presheaf.IsLocallyInjective K.toGrothendieck
      ((PresheafOfModules.toPresheaf O.obj).map α.val) :=
    isLocallyInjective_of_zariskiRefinement S toOver K hZariski _ hinj
  have := (Sheaf.isLocallyBijective_iff_isIso ((SheafOfModules.toSheaf O).map α)).1
    ⟨⟨hi.1⟩, ⟨hs.1⟩⟩
  exact isIso_of_reflects_iso α (SheafOfModules.toSheaf O)

end Stacks.Sites

/-! ### The sections of a free module pulled back to an affine scheme -/

namespace AlgebraicGeometry.Scheme.Modules

/-- **The global sections of the pullback of a free `𝒪_S`-module along a morphism from an affine
scheme are the finitely supported families of regular functions.** -/
public noncomputable def pullbackFreeSectionsEquiv {S X : Scheme.{u}} (g : X ⟶ S) [IsAffine X]
    (L : Type u) :
    (L →₀ Γ(X, ⊤)) ≃ₗ[Γ(X, ⊤)]
      Γ((Scheme.Modules.pullback g).obj (SheafOfModules.free (R := S.ringCatSheaf) L), ⊤) :=
  (LinearEquiv.ofBijective (Stacks.Sites.freeSectionsMap (R := X.ringCatSheaf) L (op ⊤)).hom
    (Stacks.Sites.bijective_freeSectionsMap L ⊤
      (Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact ⊤ (by
        have h : IsCompact (Set.univ : Set ↥X) := CompactSpace.isCompact_univ
        simpa using h)))) ≪≫ₗ
    sectionsLinearEquivOfIso (Scheme.Modules.pullbackFreeIso g L).symm ⊤

/-! ### Tautological sections of a pullback of a free module -/

attribute [local implicit_reducible] TopCat.Sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.unitModule

/-- On the `l`-th summand of a free module, the identification of the pullback of a free module
with the free module is the identification of the pullback of the structure sheaf with the
structure sheaf. -/
public theorem pullback_map_ιFree_comp_pullbackFreeIso_hom {S T : Scheme.{u}} (f : T ⟶ S)
    (I : Type u) (i : I) :
    (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫ (pullbackFreeIso f I).hom =
      (Scheme.Modules.pullbackUnitIso f).hom ≫ SheafOfModules.ιFree i := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom
    (φ := f.toRingCatSheafHom) (i := i)

private theorem unitIso_comp_hom {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T) :
    (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackUnitIso f).hom ≫
        (Scheme.Modules.pullbackUnitIso g).hom =
      (Scheme.Modules.pullbackComp g f).hom.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullbackUnitIso (g ≫ f)).hom := by
  rw [← Scheme.Modules.pullbackUnitIso_comp g f]
  simp

private theorem freeIso_comp_leg_left {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    (I : Type u) (i : I) :
    ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map
          (SheafOfModules.ιFree i)) ≫
        (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) I)) ≫
      (pullbackFreeIso (g ≫ f) I).hom =
    ((Scheme.Modules.pullbackComp g f).hom.app (Scheme.unitModule S) ≫
      (Scheme.Modules.pullbackUnitIso (g ≫ f)).hom) ≫ SheafOfModules.ιFree i :=
  have hNat : (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map
          (SheafOfModules.ιFree i)) ≫
        (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) I) =
      (Scheme.Modules.pullbackComp g f).hom.app (Scheme.unitModule S) ≫
        (Scheme.Modules.pullback (g ≫ f)).map (SheafOfModules.ιFree i) :=
    (Scheme.Modules.pullbackComp g f).hom.naturality (SheafOfModules.ιFree i)
  (congrArg (fun m => m ≫ (pullbackFreeIso (g ≫ f) I).hom) hNat).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => (Scheme.Modules.pullbackComp g f).hom.app
            (Scheme.unitModule S) ≫ m)
          (pullback_map_ιFree_comp_pullbackFreeIso_hom (g ≫ f) I i)).trans
        (Category.assoc _ _ _).symm))

private theorem freeIso_comp_leg_right {S T U : Scheme.{u}} (f : T ⟶ S) (g : U ⟶ T)
    (I : Type u) (i : I) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map
          (SheafOfModules.ιFree i)) ≫
        ((Scheme.Modules.pullback g).map (pullbackFreeIso f I).hom ≫
          (pullbackFreeIso g I).hom) =
    ((Scheme.Modules.pullbackComp g f).hom.app (Scheme.unitModule S) ≫
      (Scheme.Modules.pullbackUnitIso (g ≫ f)).hom) ≫ SheafOfModules.ιFree i :=
  have h1 : (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map
          (SheafOfModules.ιFree i)) ≫
        (Scheme.Modules.pullback g).map (pullbackFreeIso f I).hom =
      (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackUnitIso f).hom ≫
        (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i) :=
    ((Scheme.Modules.pullback g).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback g).map
          (pullback_map_ιFree_comp_pullbackFreeIso_hom f I i)).trans
        ((Scheme.Modules.pullback g).map_comp _ _))
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ (pullbackFreeIso g I).hom) h1).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => (Scheme.Modules.pullback g).map
              (Scheme.Modules.pullbackUnitIso f).hom ≫ m)
            (pullback_map_ιFree_comp_pullbackFreeIso_hom g I i)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun m => m ≫ SheafOfModules.ιFree i) (unitIso_comp_hom f g))))))

private theorem pullbackFreeIso_comp_hom {S T U : Scheme.{u}}
    (f : T ⟶ S) (g : U ⟶ T) (I : Type u) :
    (Scheme.Modules.pullbackComp g f).hom.app
        (SheafOfModules.free (R := S.ringCatSheaf) I) ≫
      (pullbackFreeIso (g ≫ f) I).hom =
    (Scheme.Modules.pullback g).map (pullbackFreeIso f I).hom ≫
      (pullbackFreeIso g I).hom :=
  Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback g) _ _
      (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback f) _ _
        (SheafOfModules.isColimitFreeCofan (R := S.ringCatSheaf) I))) _ _
    (fun i => (freeIso_comp_leg_left f g I i).trans (freeIso_comp_leg_right f g I i).symm)

/-- **The identification of the pullback of a free module with the free module is compatible
with composition of morphisms of schemes.** -/
public theorem pullbackFreeIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (I : Type u) :
    (Scheme.Modules.pullbackComp f g).inv.app
        (SheafOfModules.free (R := Z.ringCatSheaf) I) ≫
      (Scheme.Modules.pullback f).map (pullbackFreeIso g I).hom ≫
      (pullbackFreeIso f I).hom = (pullbackFreeIso (f ≫ g) I).hom := by
  rw [← pullbackFreeIso_comp_hom g f I, Iso.inv_hom_id_app_assoc]

/-- The composition compatibility of `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` along a
factorisation `f ≫ g = h` of morphisms of schemes. -/
public theorem pullbackFreeIso_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) (I : Type u) :
    (Scheme.Modules.pullbackCongr w).inv.app
        (SheafOfModules.free (R := Z.ringCatSheaf) I) ≫
      (Scheme.Modules.pullbackComp f g).inv.app
        (SheafOfModules.free (R := Z.ringCatSheaf) I) ≫
      (Scheme.Modules.pullback f).map (pullbackFreeIso g I).hom ≫
      (pullbackFreeIso f I).hom = (pullbackFreeIso h I).hom := by
  subst h
  simpa [Scheme.Modules.pullbackCongr, NatTrans.id_app] using pullbackFreeIso_comp f g I

/-- **The identifications of pullbacks of a free module with free modules are compatible with
the comparison of iterated pullbacks.**  For a morphism `γ` of schemes over `S`, transporting
along the comparison of `γ.left^* W.hom^* (⊕_I 𝒪_S)` with `V.hom^* (⊕_I 𝒪_S)` and then
identifying with `⊕_I 𝒪_{V.left}` is the same as identifying upstairs first. -/
public theorem pullbackFreeIso_comparison {S : Scheme.{u}} {V W : Over S} (γ : V ⟶ W)
    (I : Type u) :
    ((Scheme.Modules.pullbackComp γ.left W.hom).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) I) ≫
        (Scheme.Modules.pullbackCongr (Over.w γ)).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) I)) ≫
      (pullbackFreeIso V.hom I).hom =
      (Scheme.Modules.pullback γ.left).map (pullbackFreeIso W.hom I).hom ≫
        (pullbackFreeIso γ.left I).hom := by
  conv_lhs => rw [← pullbackFreeIso_comp_eq γ.left W.hom V.hom (Over.w γ) I]
  simp

/-- **The `l`-th tautological global section of the pullback of a free module.**  The pullback
of a free module is free (`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`), and a morphism out
of a free module on a scheme is a family of global sections of the target
(`AlgebraicGeometry.Scheme.Modules.freeHomEquivAppTop`); this is the family belonging to the
inverse of that identification. -/
public noncomputable def freeTautologicalSection {S X : Scheme.{u}} (g : X ⟶ S) (L : Type u)
    (l : L) :
    Γ((Scheme.Modules.pullback g).obj (SheafOfModules.free (R := S.ringCatSheaf) L), ⊤) :=
  Scheme.Modules.freeHomEquivAppTop X _ L (pullbackFreeIso g L).inv l

/-- The morphism out of the structure sheaf attached to a global section of a module which comes
from a morphism out of a free module is the corresponding coproduct injection followed by that
morphism. -/
public theorem unitHomEquivTop_freeHomEquivAppTop {X : Scheme.{u}} (M : X.Modules) (L : Type u)
    (φ : SheafOfModules.free (R := X.ringCatSheaf) L ⟶ M) (l : L) :
    Scheme.Modules.unitHomEquivTop M (Scheme.Modules.freeHomEquivAppTop X M L φ l) =
      SheafOfModules.ιFree l ≫ φ := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply φ l]
  exact congrArg (SheafOfModules.unitHomEquiv M).symm ((Equiv.eq_symm_apply _).1 rfl)

/-- The morphism out of the structure sheaf attached to the `l`-th tautological section is the
`l`-th coproduct injection followed by the identification of the free module with the pullback of
the free module. -/
public theorem unitHomEquivTop_freeTautologicalSection {S X : Scheme.{u}} (g : X ⟶ S)
    (L : Type u) (l : L) :
    Scheme.Modules.unitHomEquivTop _ (freeTautologicalSection g L l) =
      SheafOfModules.ιFree l ≫ (pullbackFreeIso g L).inv :=
  unitHomEquivTop_freeHomEquivAppTop _ L _ l

private theorem pullbackSectionsMap_eq_homEquiv {S : Scheme.{u}} (F : S.Modules) {V W : Over S}
    (γ : V ⟶ W) (s : Γ((Scheme.Modules.pullback W.hom).obj F, ⊤)) :
    pullbackSectionsMap F γ s =
      ((Scheme.Modules.pullback V.hom).obj F).presheaf.map
          (eqToHom (show (⊤ : V.left.Opens) = γ.left ⁻¹ᵁ ⊤ by simp)).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction γ.left).homEquiv
            ((Scheme.Modules.pullback W.hom).obj F)
            ((Scheme.Modules.pullback V.hom).obj F))
          ((Scheme.Modules.pullbackComp γ.left W.hom).hom.app F ≫
            (Scheme.Modules.pullbackCongr (Over.w γ)).hom.app F)).app ⊤ s) := by
  rw [Adjunction.homEquiv_unit]
  rfl

private theorem taut_hom_comparison {S : Scheme.{u}} {V W : Over S} (γ : V ⟶ W) (L : Type u)
    (l : L) :
    ((Scheme.Modules.pullbackUnitIso γ.left).hom ≫ SheafOfModules.ιFree l) ≫
        (pullbackFreeIso V.hom L).inv =
      (Scheme.Modules.pullback γ.left).map
          (SheafOfModules.ιFree l ≫ (pullbackFreeIso W.hom L).inv) ≫
        ((Scheme.Modules.pullbackComp γ.left W.hom).hom.app
            (SheafOfModules.free (R := S.ringCatSheaf) L) ≫
          (Scheme.Modules.pullbackCongr (Over.w γ)).hom.app
            (SheafOfModules.free (R := S.ringCatSheaf) L)) := by
  have hc := pullbackFreeIso_comparison γ L
  have hl := pullback_map_ιFree_comp_pullbackFreeIso_hom γ.left L l
  have hAinv : (Scheme.Modules.pullback γ.left).map (pullbackFreeIso W.hom L).inv ≫
      ((Scheme.Modules.pullbackComp γ.left W.hom).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) L) ≫
        (Scheme.Modules.pullbackCongr (Over.w γ)).hom.app
          (SheafOfModules.free (R := S.ringCatSheaf) L)) =
      (pullbackFreeIso γ.left L).hom ≫ (pullbackFreeIso V.hom L).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, hc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  exact (congrArg (fun m => m ≫ (pullbackFreeIso V.hom L).inv) hl.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => (Scheme.Modules.pullback γ.left).map
            (SheafOfModules.ιFree l) ≫ m) hAinv.symm).trans
        (Functor.map_comp_assoc _ _ _ _).symm))

/-- **The pullback map on global sections carries tautological sections to tautological
sections.**  For a morphism `γ : V ⟶ W` of schemes over `S`, the pullback map
`AlgebraicGeometry.pullbackSectionsMap` of Tag 03DS carries the `l`-th tautological section of
`W.hom^* (⊕_L 𝒪_S)` to the `l`-th tautological section of `V.hom^* (⊕_L 𝒪_S)`. -/
public theorem pullbackSectionsMap_freeTautologicalSection {S : Scheme.{u}} (L : Type u)
    {V W : Over S} (γ : V ⟶ W) (l : L) :
    pullbackSectionsMap (SheafOfModules.free (R := S.ringCatSheaf) L) γ
        (freeTautologicalSection W.hom L l) = freeTautologicalSection V.hom L l := by
  refine (Scheme.Modules.unitHomEquivTop _).injective ?_
  refine (cancel_epi (Scheme.Modules.pullbackUnitIso γ.left).hom).1 ?_
  have hnat := Scheme.Modules.pullbackUnitIso_sections_naturality γ.left
    ((Scheme.Modules.pullback W.hom).obj (SheafOfModules.free (R := S.ringCatSheaf) L))
    ((Scheme.Modules.pullback V.hom).obj (SheafOfModules.free (R := S.ringCatSheaf) L))
    ((Scheme.Modules.pullbackComp γ.left W.hom).hom.app
        (SheafOfModules.free (R := S.ringCatSheaf) L) ≫
      (Scheme.Modules.pullbackCongr (Over.w γ)).hom.app
        (SheafOfModules.free (R := S.ringCatSheaf) L))
    (freeTautologicalSection W.hom L l)
  rw [← pullbackSectionsMap_eq_homEquiv] at hnat
  rw [hnat, unitHomEquivTop_freeTautologicalSection, unitHomEquivTop_freeTautologicalSection]
  exact (taut_hom_comparison γ L l).symm

/-- The identification of
`AlgebraicGeometry.Scheme.Modules.pullbackFreeSectionsEquiv` carries `Finsupp.single l r` to `r`
times the `l`-th tautological section
`AlgebraicGeometry.Scheme.Modules.freeTautologicalSection`. -/
public theorem pullbackFreeSectionsEquiv_single {S X : Scheme.{u}} (g : X ⟶ S) [IsAffine X]
    (L : Type u) (l : L) (r : Γ(X, ⊤)) :
    pullbackFreeSectionsEquiv g L (Finsupp.single l r) = r • freeTautologicalSection g L l := by
  have h := Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single
    ((Scheme.Modules.pullback g).obj (SheafOfModules.free (R := S.ringCatSheaf) L))
    (SheafOfModules.freeHomEquiv _ (pullbackFreeIso g L).inv) (op ⊤) l r
  exact (congrArg (fun ψ : SheafOfModules.free (R := X.ringCatSheaf) L ⟶
          (Scheme.Modules.pullback g).obj (SheafOfModules.free (R := S.ringCatSheaf) L) =>
        (ψ.val.app (op ⊤)).hom
          ((Stacks.Sites.freeSectionsMap (R := X.ringCatSheaf) L (op ⊤)).hom
            (Finsupp.single l r)))
      (Equiv.symm_apply_apply (SheafOfModules.freeHomEquiv
        ((Scheme.Modules.pullback g).obj (SheafOfModules.free (R := S.ringCatSheaf) L)))
        (pullbackFreeIso g L).inv)).symm.trans h

/-- **A finite sum of multiples of the tautological sections** of the pullback of a free module,
as a linear map on the finitely supported families of regular functions. -/
public noncomputable abbrev freeSectionsCombination {S X : Scheme.{u}} (g : X ⟶ S)
    (L : Type u) :
    (L →₀ Γ(X, ⊤)) →ₗ[Γ(X, ⊤)]
      Γ((Scheme.Modules.pullback g).obj (SheafOfModules.free (R := S.ringCatSheaf) L), ⊤) :=
  Finsupp.linearCombination _ (freeTautologicalSection g L)

/-- **Over an affine scheme the identification of the sections of a pullback of a free module
with the finitely supported families is the finite sum of multiples of the tautological
sections.** -/
public theorem pullbackFreeSectionsEquiv_eq {S X : Scheme.{u}} (g : X ⟶ S) [IsAffine X]
    (L : Type u) (c : L →₀ Γ(X, ⊤)) :
    pullbackFreeSectionsEquiv g L c = freeSectionsCombination g L c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single l r =>
      rw [pullbackFreeSectionsEquiv_single, freeSectionsCombination,
        Finsupp.linearCombination_single]

/-- **The pullback map on global sections carries a finite sum of multiples of the tautological
sections to the finite sum of the restricted multiples.** -/
public theorem pullbackSectionsMap_freeSectionsCombination {S : Scheme.{u}} (L : Type u)
    {V W : Over S} (γ : V ⟶ W) (c : L →₀ Γ(W.left, ⊤)) :
    pullbackSectionsMap (SheafOfModules.free (R := S.ringCatSheaf) L) γ
        (freeSectionsCombination W.hom L c) =
      freeSectionsCombination V.hom L (Finsupp.mapRange γ.left.appTop (map_zero _) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← map_add,
        ← Finsupp.mapRange_add (fun a b => map_add (ConcreteCategory.hom γ.left.appTop) a b)]
  | single l r =>
      rw [Finsupp.mapRange_single, freeSectionsCombination, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, pullbackSectionsMap_smul,
        pullbackSectionsMap_freeTautologicalSection]

/-- Pullback of modules along a morphism of schemes preserves finite colimits. -/
private theorem preservesFiniteColimits_pullback {S X : Scheme.{u}} (g : X ⟶ S) :
    PreservesFiniteColimits (Scheme.Modules.pullback g) :=
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  inferInstance

/-! ### Surjectivity on sections of a pullback of an epimorphism -/

/-- **An epimorphism of quasi-coherent modules on `S` stays surjective on the global sections of
its pullback to an affine scheme.** -/
@[ega "III 1.2.5" "partial"]
public theorem surjective_pullback_map_appTop_of_epi {S X : Scheme.{u}} (g : X ⟶ S) [IsAffine X]
    {N G : S.Modules} [N.IsQuasicoherent] [G.IsQuasicoherent] (π : N ⟶ G) [Epi π] :
    Function.Surjective (((Scheme.Modules.pullback g).map π).app ⊤) := by
  have := preservesFiniteColimits_pullback g
  have := Stacks.Modules.isQuasicoherent_pullback g N inferInstance
  have := Stacks.Modules.isQuasicoherent_pullback g G inferInstance
  exact surjective_app_of_epi_of_isAffineOpen ((Scheme.Modules.pullback g).map π)
    (isAffineOpen_top X)

/-- **Over an affine open the sections of a morphism of quasi-coherent modules are exact in the
middle.**  A section of the target over an affine open which dies in the cokernel comes from a
section of the source. -/
public theorem exists_app_eq_of_cokernelπ_app_eq_zero {X : Scheme.{u}} {M N : X.Modules}
    (α : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (w : Γ(N, U)) (hw : (cokernel.π α).app U w = 0) :
    ∃ m : Γ(M, U), α.app U m = w := by
  have : (cokernel α).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel α
  have : (kernel (cokernel.π α)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _
  obtain ⟨k, hk⟩ :=
    (Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel (cokernel.π α) U w).1 hw
  obtain ⟨m, hm⟩ := surjective_app_of_epi_of_isAffineOpen (Abelian.factorThruImage α) hU k
  refine ⟨m, ?_⟩
  calc α.app U m
      = (Abelian.factorThruImage α ≫ kernel.ι (cokernel.π α)).app U m := by simp
    _ = (kernel.ι (cokernel.π α)).app U ((Abelian.factorThruImage α).app U m) := rfl
    _ = w := by rw [hm, hk]

/-- **On the global sections of the pullback to an affine scheme, a morphism of quasi-coherent
modules on `S` is exact in the middle against the projection onto its cokernel.**  Together with
`AlgebraicGeometry.Scheme.Modules.surjective_pullback_map_appTop_of_epi` this says that the
sections of the pullback to an affine scheme carry a right-exact sequence of quasi-coherent
modules to a right-exact sequence. -/
@[ega "III 1.2.5" "partial"]
public theorem exists_pullback_map_appTop_eq_of_cokernelπ_appTop_eq_zero {S X : Scheme.{u}}
    (g : X ⟶ S) [IsAffine X] {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (α : M ⟶ N) (w : Γ((Scheme.Modules.pullback g).obj N, ⊤))
    (hw : ((Scheme.Modules.pullback g).map (cokernel.π α)).app ⊤ w = 0) :
    ∃ m, ((Scheme.Modules.pullback g).map α).app ⊤ m = w := by
  have := preservesFiniteColimits_pullback g
  have := Stacks.Modules.isQuasicoherent_pullback g M inferInstance
  have := Stacks.Modules.isQuasicoherent_pullback g N inferInstance
  refine exists_app_eq_of_cokernelπ_app_eq_zero ((Scheme.Modules.pullback g).map α)
    (isAffineOpen_top X) w ?_
  calc (cokernel.π ((Scheme.Modules.pullback g).map α)).app ⊤ w
      = ((Scheme.Modules.pullback g).map (cokernel.π α) ≫
          (PreservesCokernel.iso (Scheme.Modules.pullback g) α).hom).app ⊤ w := by
        rw [PreservesCokernel.π_iso_hom]
    _ = (PreservesCokernel.iso (Scheme.Modules.pullback g) α).hom.app ⊤
          (((Scheme.Modules.pullback g).map (cokernel.π α)).app ⊤ w) := rfl
    _ = 0 := by rw [hw, map_zero]

end AlgebraicGeometry.Scheme.Modules

end
