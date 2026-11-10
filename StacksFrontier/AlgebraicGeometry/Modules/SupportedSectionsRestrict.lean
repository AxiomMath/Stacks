module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SupportedSectionsFlatPullback
public import StacksFrontier.AlgebraicGeometry.SupportedQuotient.Basic

/-!
# Sections supported in a subset, under isomorphisms and under restriction to an open

Let `X` be a scheme and `Z ⊆ X` a subset. The submodule
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z F` of the sections of `F`
supported in `Z` is invariant under isomorphism of `F`, and it commutes with restriction along an
open immersion `j : Y ⟶ X` once `Z` is replaced by its inverse image. This file records both,
together with the resulting comparisons of the quotients `F / Γ_Z(F)`.

Those quotients are the strict transforms of [Stacks, Tag 080D], so the two comparisons are what
lets a strict transform be computed on an open.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_iso_iff`: membership in the
  submodule of sections supported in `Z` is detected across an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.supportedSectionsRestrictIso`: the sections supported in `Z`,
  restricted along an open immersion, are the sections of the restriction supported in the
  inverse image of `Z`.
* `AlgebraicGeometry.Scheme.Modules.pullbackSupportedQuotientIso`: the quotient by the sections
  supported in `Z` commutes with pullback along an open immersion.

## Implementation notes

The germ criterion `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_iff` is the
only input: membership is the vanishing of every germ outside `Z`, and the germs of a restricted
module are the germs of the module at the image points
(`AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app`). The pullback statement is
deduced from the restriction statement across
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which is also what makes the
restriction functor's preservation of cokernels available for the pullback.

The invariance of the quotient under an isomorphism of the ambient module is
`Stacks.SupportedQuotient.supportedSectionsCokernelIso`
(`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/SupportedSectionsFlatPullback.lean`), which
is imported rather than restated here, along with the submodule transport
`Stacks.SupportedQuotient.submoduleIso` it is built from.

## References

* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Invariance under isomorphism -/

/-- **Sections supported in a subset are detected across an isomorphism.** -/
public lemma mem_supportedSectionsSubmodule_iso_iff (Z : Set X) {F G : X.Modules} (e : F ≅ G)
    (U : X.Opens) (s : Γ(F, U)) :
    e.hom.app U s ∈ (supportedSectionsSubmodule Z G).toSubmodule.obj (op U) ↔
      s ∈ (supportedSectionsSubmodule Z F).toSubmodule.obj (op U) := by
  refine ⟨fun hs ↦ ?_, map_mem_supportedSectionsSubmodule Z e.hom U s⟩
  have ht := map_mem_supportedSectionsSubmodule Z e.inv U (e.hom.app U s) hs
  have hcancel : e.inv.app U (e.hom.app U s) = s :=
    ConcreteCategory.congr_hom
      (congrArg (fun k : F ⟶ F ↦ k.val.app (op U)) e.hom_inv_id) s
  rwa [hcancel] at ht

/-! ### Restriction to an open -/

/-- **Sections supported in a subset, seen on an open.** For an open immersion `j`, a section of
the restriction of `F` along `j` is supported in the inverse image of `Z` exactly when the
corresponding section of `F` over the image open is supported in `Z`. -/
public lemma mem_supportedSectionsSubmodule_restrict_iff {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (Z : Set X) (F : X.Modules) (U : Y.Opens) (s : Γ(F.restrict j, U)) :
    s ∈ (supportedSectionsSubmodule (j.base ⁻¹' Z) (F.restrict j)).toSubmodule.obj (op U) ↔
      (restrictAppIso j F U).hom s ∈
        (supportedSectionsSubmodule Z F).toSubmodule.obj (op (j ''ᵁ U)) := by
  rw [mem_supportedSectionsSubmodule_iff, mem_supportedSectionsSubmodule_iff]
  have key (x : Y) (hx : x ∈ U) :
      (restrictStalkNatIso j x).hom.app F ((F.restrict j).presheaf.germ U x hx s) =
        F.presheaf.germ (j ''ᵁ U) (j.base x) ⟨x, hx, rfl⟩ ((restrictAppIso j F U).hom s) :=
    ConcreteCategory.congr_hom (germ_restrictStalkNatIso_hom_app j x F hx) s
  constructor
  · intro hs y hy hyZ
    obtain ⟨x, hx, rfl⟩ := hy
    refine (key x hx).symm.trans ?_
    refine Eq.trans (congrArg (ConcreteCategory.hom
      ((restrictStalkNatIso j x).hom.app F)) (hs x hx hyZ)) ?_
    exact map_zero _
  · intro hs x hx hxZ
    refine (ConcreteCategory.bijective_of_isIso
      ((restrictStalkNatIso j x).hom.app F)).injective ?_
    exact ((key x hx).trans (hs (j.base x) ⟨x, hx, rfl⟩ hxZ)).trans (map_zero _).symm

/-- `AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_restrict_iff` with the
subset on the source given by an equation rather than as a literal inverse image. -/
public lemma mem_supportedSectionsSubmodule_restrict_iff' {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (Z : Set X) (Z' : Set Y) (hZ : Z' = j.base ⁻¹' Z) (F : X.Modules)
    (U : Y.Opens) (s : Γ(F.restrict j, U)) :
    s ∈ (supportedSectionsSubmodule Z' (F.restrict j)).toSubmodule.obj (op U) ↔
      (restrictAppIso j F U).hom s ∈
        (supportedSectionsSubmodule Z F).toSubmodule.obj (op (j ''ᵁ U)) := by
  subst hZ
  exact mem_supportedSectionsSubmodule_restrict_iff j Z F U s

/-- **The sections supported in a subset commute with restriction to an open.** -/
public def supportedSectionsRestrictIso {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (Z : Set X) (F : X.Modules) :
    (supportedSectionsObj Z F).restrict j ≅
      supportedSectionsObj (j.base ⁻¹' Z) (F.restrict j) := by
  let A : Y.Modules := (supportedSectionsObj Z F).restrict j
  let P := supportedSectionsSubmodule (j.base ⁻¹' Z) (F.restrict j)
  let φ : A ⟶ P.toSheafOfModules :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom (X := A.val.obj U)
            (Y := P.toSheafOfModules.val.obj U)
            { toFun := fun s ↦ ⟨s.1,
                (mem_supportedSectionsSubmodule_restrict_iff j Z F (unop U) s.1).mpr s.2⟩
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality := by intros; rfl } }
  let ψ : P.toSheafOfModules ⟶ A :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom (X := P.toSheafOfModules.val.obj U)
            (Y := A.val.obj U)
            { toFun := fun s ↦ ⟨s.1,
                (mem_supportedSectionsSubmodule_restrict_iff j Z F (unop U) s.1).mp s.2⟩
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          naturality := by intros; rfl } }
  exact ⟨φ, ψ, rfl, rfl⟩

/-- The comparison of the supported sections over an open is compatible with the two
inclusions. -/
@[reassoc]
public lemma supportedSectionsRestrictIso_hom_ι {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (Z : Set X) (F : X.Modules) :
    (supportedSectionsRestrictIso j Z F).hom ≫
        supportedSectionsι (j.base ⁻¹' Z) (F.restrict j) =
      (restrictFunctor j).map (supportedSectionsι Z F) :=
  rfl

/-- **The quotient by the sections supported in a subset commutes with pullback along an open
immersion.** -/
public def pullbackSupportedQuotientIso {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (Z : Set X) (F : X.Modules) :
    (Scheme.Modules.pullback j).obj (cokernel (supportedSectionsι Z F)) ≅
      cokernel (supportedSectionsι (j.base ⁻¹' Z) ((Scheme.Modules.pullback j).obj F)) :=
  ((restrictFunctorIsoPullback j).app (cokernel (supportedSectionsι Z F))).symm ≪≫
    PreservesCokernel.iso (restrictFunctor j) (supportedSectionsι Z F) ≪≫
    cokernel.mapIso ((restrictFunctor j).map (supportedSectionsι Z F))
      (supportedSectionsι (j.base ⁻¹' Z) (F.restrict j))
      (supportedSectionsRestrictIso j Z F) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, supportedSectionsRestrictIso_hom_ι]) ≪≫
    _root_.Stacks.SupportedQuotient.supportedSectionsCokernelIso (j.base ⁻¹' Z)
      ((restrictFunctorIsoPullback j).app F)

/-- **The quotient by the sections supported in a subset is computed on an open.** This is
`AlgebraicGeometry.Scheme.Modules.pullbackSupportedQuotientIso` with the subset on the source
given by an equation and the module on the source given up to isomorphism. -/
public def supportedQuotientRestrictIso {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (Z : Set X) (Z' : Set Y) (hZ : Z' = j.base ⁻¹' Z) (A : X.Modules) (A' : Y.Modules)
    (e : A' ≅ (Scheme.Modules.pullback j).obj A) :
    cokernel (supportedSectionsι Z' A') ≅
      (Scheme.Modules.pullback j).obj (cokernel (supportedSectionsι Z A)) := by
  subst hZ
  exact _root_.Stacks.SupportedQuotient.supportedSectionsCokernelIso (j.base ⁻¹' Z) e ≪≫
    (pullbackSupportedQuotientIso j Z A).symm

end AlgebraicGeometry.Scheme.Modules

end
