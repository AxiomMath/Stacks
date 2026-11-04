module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback

/-!
# Base change of extension by zero along a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `U` be an open subspace of
`Y` and let `U' = f^{-1}U`.  The composite `j_{U,!}j_U^*`, which cuts a sheaf of modules down to
`U` and extends it back by zero, commutes with pullback:

`f^*(j_{U,!}j_U^*F) ≅ j_{U',!}j_{U'}^*(f^*F)`,

naturally in `F`, with no flatness hypothesis on `f`.  This is the ringed-space analogue of the
base-change isomorphism of Stacks 03S6 for the small étale site, and it is the underived input
to the comparison of Mayer--Vietoris triangles (Stacks 08BU) along `f`.

## Main results

* `Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso`: the base
  change isomorphism `(j_{U,!}j_U^*) ⋙ f^* ≅ f^* ⋙ (j_{U',!}j_{U'}^*)`.
* `Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_of_stalk_isIso` and
  `Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalk_of_isIso_jStar_map`: restriction to an
  open subspace inverts exactly the morphisms that are invertible on the stalks inside it.

## Implementation notes

No map `f^*j_{U,!}j_U^* ⟶ j_{U',!}j_{U'}^*f^*` is written down by hand.  Both functors receive a
transformation from `(j_{U,!}j_U^*) ⋙ f^* ⋙ (j_{U',!}j_{U'}^*)`: the counit of `j_{U',!} ⊣
j_{U'}^*`, and `j_{U',!}j_{U'}^*f^*` of the counit of `j_{U,!} ⊣ j_U^*`.  Each is a whiskering of
a counit, so naturality in the sheaf of modules is free, and each is invertible for a reason of
support:

* the first because `f^*(j_{U,!}j_U^*F)` has vanishing stalks off `U'` — the stalk of a pullback
  at `x` is a base change of the stalk at `f x` (Stacks 0098), and the stalk of an extension by
  zero vanishes off `U` (Stacks 00AB) — so Stacks 00AB makes the counit invertible there;
* the second because `j_U^*` of the counit of `j_{U,!} ⊣ j_U^*` is invertible by the triangle
  identity, hence so is every stalk of it inside `U`, hence every stalk inside `U'` of its
  pullback, hence `j_{U'}^*` of that pullback.

The composite of the inverse of the first with the second is therefore an honest isomorphism of
functors, and nothing in it is true by construction.

Module stalks and the stalks of the underlying sheaves of abelian groups both occur: Stacks 00AB
is stated for the latter and Stacks 0098 for the former.  They have the same carrier — the
comparison `AlgebraicGeometry.SheafOfModules.stalkFunctorCompForget₂` is `Iso.refl` — and
`Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_stalkMap_iff` crosses between them once.

## References

* [Stacks Project, Lemma 17.6.1 (Tag 00AB)](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Lemma 17.3.4 (Tag 0098)](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Lemma 59.72.1 (Tag 03S6)](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules

universe u

namespace Stacks.Cohomology.ExtensionByZeroBaseChange

/-! ### Crossing between module stalks and abelian-group stalks -/

/-- A module stalk vanishes exactly when the stalk of the underlying sheaf of abelian groups
does: the two have the same carrier. -/
lemma isZero_stalkObj_iff {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (z : Z)
    (M : SheafOfModules.{u} O) :
    IsZero (AlgebraicGeometry.SheafOfModules.stalkObj O z M) ↔
      IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z) := by
  rw [ModuleCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-- A morphism of sheaves of modules is invertible on the module stalk at `z` exactly when it is
invertible on the stalk at `z` of the underlying sheaves of abelian groups: forgetting the module
structure on stalks is `AlgebraicGeometry.SheafOfModules.stalkFunctorCompForget₂`, which is the
identity, and it reflects isomorphisms. -/
lemma isIso_stalkMap_iff {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (z : Z)
    {M N : SheafOfModules.{u} O} (φ : M ⟶ N) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap O z φ) ↔
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map ((toAb O).map φ)) := by
  let R := TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Z) O.obj z
  refine ⟨fun _ => ?_, fun h => ?_⟩
  · exact (Functor.map_isIso _ _ : IsIso ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (AlgebraicGeometry.SheafOfModules.stalkMap O z φ)))
  · have : IsIso ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (AlgebraicGeometry.SheafOfModules.stalkMap O z φ)) := h
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-! ### Restriction to an open subspace detects isomorphisms on the stalks inside it -/

/-- The stalk of `j_U^*φ` at `u ∈ U` is invertible exactly when the stalk of `φ` at `u` is. -/
private lemma isIso_stalk_jStar_map_iff {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z)
    {M N : SheafOfModules.{u} O} (φ : M ⟶ N) (z : Z) (hz : z ∈ W) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨z, hz⟩ : Usp W)).map
      ((toAb (resRing W O)).map ((jStar W O).map φ))) ↔
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map ((toAb O).map φ)) := by
  rw [toAb_jStar_map W O φ]
  exact TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff W _ _ ((toAb O).map φ) ⟨z, hz⟩

/-- **A morphism invertible on every stalk inside `U` restricts to an isomorphism.**  Restriction
is precomposition with the image functor on opens (`ExtensionByZeroModules.toAb_jStar_map`), so
its stalk at `u ∈ U` is the stalk of the morphism at `u` viewed in the ambient space. -/
lemma isIso_jStar_map_of_stalk_isIso {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z)
    {M N : SheafOfModules.{u} O} (φ : M ⟶ N)
    (h : ∀ z : Z, z ∈ W → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
      ((toAb O).map φ))) :
    IsIso ((jStar W O).map φ) :=
  isIso_of_stalk_isIso (resRing W O) ((jStar W O).map φ) fun u =>
    (isIso_stalk_jStar_map_iff O W φ (W.inclusion' u) u.2).2 (h _ u.2)

/-- **A morphism whose restriction to `U` is an isomorphism is invertible on every stalk inside
`U`.**  This is the converse half of
`Stacks.Cohomology.ExtensionByZeroBaseChange.isIso_jStar_map_of_stalk_isIso`. -/
lemma isIso_stalk_of_isIso_jStar_map {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z)
    {M N : SheafOfModules.{u} O} (φ : M ⟶ N)
    (hφ : IsIso ((jStar W O).map φ)) (z : Z) (hz : z ∈ W) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map ((toAb O).map φ)) :=
  (isIso_stalk_jStar_map_iff O W φ z hz).1 (Functor.map_isIso _ _)

/-- `j_U^*` of the counit of `j_{U,!} ⊣ j_U^*` is an isomorphism, by the right triangle
identity. -/
lemma isIso_jStar_map_counit {Z : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u}) (W : Opens Z)
    (G : SheafOfModules.{u} O) :
    IsIso ((jStar W O).map ((jShriekAdjunction W O).counit.app G)) := by
  have := isIso_jShriekAdjunction_unit W O
  exact isIso_of_hom_comp_eq_id _ ((jShriekAdjunction W O).right_triangle_components G)

/-! ### Stalks of a pullback -/

section Pullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **A pullback has vanishing stalk wherever the stalk above it vanishes.**  The stalk of `f^*N`
at `x` is the base change of the stalk of `N` at `f x` along the germ map (Stacks 0098), and base
change is additive. -/
lemma isZero_stalk_modulePullback_obj (N : SheafOfModules.{u} (structureSheafRing Y))
    (x : X.carrier)
    (h : IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf
      (f.hom.base x))) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((modulePullback f).obj N).val.presheaf x) := by
  rw [← isZero_stalkObj_iff]
  refine IsZero.of_iso ?_ (_root_.Stacks.RingedSpace.stalkModulePullbackIso f x N)
  exact Functor.map_isZero _ ((isZero_stalkObj_iff (structureSheafRing Y) (f.hom.base x) N).2 h)

/-- **A pullback is invertible on the stalk at `x` whenever the morphism is invertible on the
stalk at `f x`.**  Again the stalk of the pullback is a base change of the stalk above it
(Stacks 0098), functorially. -/
lemma isIso_stalk_modulePullback_map {M N : SheafOfModules.{u} (structureSheafRing Y)}
    (φ : M ⟶ N) (x : X.carrier)
    (h : IsIso
      (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing Y) (f.hom.base x) φ)) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing X) x
      ((modulePullback f).map φ)) := by
  have h2 : IsIso ((_root_.Stacks.RingedSpace.stalkBaseChange f x).map
      (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheafRing Y) (f.hom.base x) φ)) :=
    Functor.map_isIso _ _
  exact (NatIso.isIso_map_iff
    (_root_.Stacks.RingedSpace.stalkModulePullbackFunctorIso f x) φ).2 h2

end Pullback

/-! ### The base change isomorphism -/

section BaseChange

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens Y.carrier)

/-- The pullback of `j_{U,!}j_U^*F` has vanishing stalks outside `U' = f^{-1}U`. -/
lemma isZero_stalk_modulePullback_extensionRestriction
    (F : SheafOfModules.{u} (structureSheafRing Y))
    (x : X.carrier) (hx : x ∉ (Opens.map f.hom.base).obj U) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((modulePullback f).obj
        ((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).obj F)).val.presheaf
        x) :=
  isZero_stalk_modulePullback_obj f _ x
    (isZero_stalk_jShriek U (structureSheafRing Y) ((jStar U (structureSheafRing Y)).obj F)
      (f.hom.base x) hx)

/-- **The counit of `j_{U',!} ⊣ j_{U'}^*` at the pullback of `j_{U,!}j_U^*F` is invertible.**
That pullback has vanishing stalks off `U'`, so Stacks 00AB applies. -/
lemma isIso_counit_modulePullback_extensionRestriction
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    IsIso ((jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit.app
      ((modulePullback f).obj
        ((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).obj F))) :=
  counit_isIso_of_stalk_isZero _ _ _ fun x hx =>
    isZero_stalk_modulePullback_extensionRestriction f U F x hx

/-- **`j_{U',!}j_{U'}^*` of the pullback of the counit of `j_{U,!} ⊣ j_U^*` is invertible.**  The
counit becomes invertible after `j_U^*`, hence on every stalk inside `U`; the pullback is then
invertible on every stalk inside `U'`, hence after `j_{U'}^*`. -/
lemma isIso_extensionRestriction_map_modulePullback_counit
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    IsIso ((jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
        jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).map
      ((modulePullback f).map ((jShriekAdjunction U (structureSheafRing Y)).counit.app F))) := by
  have hstar : IsIso ((jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X)).map
      ((modulePullback f).map ((jShriekAdjunction U (structureSheafRing Y)).counit.app F))) := by
    refine isIso_jStar_map_of_stalk_isIso (structureSheafRing X) _ _ fun x hx => ?_
    refine (isIso_stalkMap_iff (structureSheafRing X) x _).1
      (isIso_stalk_modulePullback_map f _ x ?_)
    exact (isIso_stalkMap_iff (structureSheafRing Y) (f.hom.base x) _).2
      (isIso_stalk_of_isIso_jStar_map (structureSheafRing Y) U _
        (isIso_jStar_map_counit (structureSheafRing Y) U F) (f.hom.base x) hx)
  rw [Functor.comp_map]
  infer_instance

/-- The counit of `j_{U',!} ⊣ j_{U'}^*`, whiskered into the pullback of `j_{U,!}j_U^*`. -/
def extensionRestrictionPullbackCounit :
    ((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)) ⋙ modulePullback f) ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)) ⟶
      (jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)) ⋙ modulePullback f :=
  Functor.whiskerLeft _
    (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit

/-- `j_{U',!}j_{U'}^*` of the pullback of the counit of `j_{U,!} ⊣ j_U^*`. -/
def extensionRestrictionPullbackComparison :
    ((jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)) ⋙ modulePullback f) ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)) ⟶
      modulePullback f ⋙ (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
        jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)) :=
  Functor.whiskerRight
    (Functor.whiskerRight (jShriekAdjunction U (structureSheafRing Y)).counit (modulePullback f))
    (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
      jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X))

/-- The transformation `extensionRestrictionPullbackCounit f U` is a natural isomorphism. -/
instance isIso_extensionRestrictionPullbackCounit :
    IsIso (extensionRestrictionPullbackCounit f U) := by
  have h : ∀ F, IsIso ((extensionRestrictionPullbackCounit f U).app F) := fun F =>
    isIso_counit_modulePullback_extensionRestriction f U F
  exact NatIso.isIso_of_isIso_app _

/-- The transformation `extensionRestrictionPullbackComparison f U` is a natural isomorphism. -/
instance isIso_extensionRestrictionPullbackComparison :
    IsIso (extensionRestrictionPullbackComparison f U) := by
  have h : ∀ F, IsIso ((extensionRestrictionPullbackComparison f U).app F) := fun F =>
    isIso_extensionRestriction_map_modulePullback_counit f U F
  exact NatIso.isIso_of_isIso_app _

/-- **Extension by zero of a restriction commutes with pullback.**  For `f : X ⟶ Y` a morphism of
ringed spaces, `U` an open subspace of `Y` and `U' = f^{-1}U`, there is an isomorphism of functors
`(j_{U,!}j_U^*) ⋙ f^* ≅ f^* ⋙ (j_{U',!}j_{U'}^*)`, natural in the sheaf of modules and needing no
flatness of `f`. -/
def modulePullbackExtensionRestrictionIso :
    (jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)) ⋙ modulePullback f ≅
      modulePullback f ⋙ (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
        jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)) :=
  (asIso (extensionRestrictionPullbackCounit f U)).symm ≪≫
    asIso (extensionRestrictionPullbackComparison f U)

/-- **The base change isomorphism is compatible with the counits `j_!j^* ⟶ ᵀ`.**  Following it
with the counit of `j_{U',!} ⊣ j_{U'}^*` is the pullback of the counit of `j_{U,!} ⊣ j_U^*`; so
the two canonical maps to `f^*` agree.

This is not true by construction: the two transformations out of
`(j_{U,!}j_U^*) ⋙ f^* ⋙ (j_{U',!}j_{U'}^*)` that define the isomorphism become equal after the
counit only by naturality of that counit. -/
theorem modulePullbackExtensionRestrictionIso_hom_counit :
    (modulePullbackExtensionRestrictionIso f U).hom ≫
        Functor.whiskerLeft (modulePullback f)
          (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit =
      Functor.whiskerRight (jShriekAdjunction U (structureSheafRing Y)).counit
        (modulePullback f) := by
  have h : extensionRestrictionPullbackComparison f U ≫
      Functor.whiskerLeft (modulePullback f)
        (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit =
      extensionRestrictionPullbackCounit f U ≫
        Functor.whiskerRight (jShriekAdjunction U (structureSheafRing Y)).counit
          (modulePullback f) :=
    NatTrans.ext (funext fun F =>
      (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit.naturality
        ((modulePullback f).map ((jShriekAdjunction U (structureSheafRing Y)).counit.app F)))
  rw [modulePullbackExtensionRestrictionIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, h, IsIso.inv_hom_id_assoc]

end BaseChange

end Stacks.Cohomology.ExtensionByZeroBaseChange

end
