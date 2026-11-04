module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite

/-!
# Finite cohomology of a proper algebraic space over an affine Noetherian object of the site

`AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper` (Stacks 08AS) is stated for a
proper algebraic space over `Spec A`.  This file records the same finiteness over the ring of
functions of an arbitrary affine Noetherian object `V` of the site, for a proper morphism
`X ⟶ V`: the cohomology `H^i(X, F)` of a coherent module, read as a module over `Γ(V)` through
the pullback of functions, is finite.  It is the form consumed by Stacks 08AT, whose proof
passes to the relative spectrum of a finite type algebra, an algebraic space proper over the
spectrum of that algebra.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper_of_isAffine`: the finiteness.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u})

section AffineTarget

open CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

variable {S : Scheme.{u}} {hS : B.Contains S} (V : BigFppfOver B S hS)

/-- The functions on an object `V` of the site, read on the identity chart of `V`. -/
abbrev idChartRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V)).O)).obj.obj (op (idEtaleChart B S hS V)) :=
  (globalSectionEval _ (op (idEtaleChart B S hS V))).comp
    (pullbackToGlobalFunctions B S hS (schemeSpace V) V (𝟙 _))

/-- On the identity chart of `V` the functions are those of `V`. -/
theorem bijective_idChartRingHom : Function.Bijective (idChartRingHom B V) := by
  show Function.Bijective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (yoneda.preimage (𝟙 (yoneda.obj V) ≫ 𝟙 (yoneda.obj V)))).op).hom
  rw [Category.comp_id, Functor.preimage_id, CategoryTheory.Functor.map_id, op_id,
    CategoryTheory.Functor.map_id]
  exact Function.bijective_id

/-- Pullback of functions along `f : X ⟶ V`, into the global sections of the structure sheaf of
the small étale ringed site of `X`. -/
abbrev pullbackRingHom {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) :
    Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) →+*
      ↥(GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :=
  pullbackToGlobalFunctions B S hS X V f

/-- The global sections of an `𝒪_X`-module, read as a module over the functions on `V` along a
morphism `f : X ⟶ V`. -/
abbrev globalSectionsOverAffine {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⋙
    ModuleCat.restrictScalars (pullbackRingHom B V f)

/-- The sections over `V` of the direct image along `f : X ⟶ V`, read as a module over the
functions on `V` and lifted to the universe of global sections. -/
abbrev pushforwardSectionsOverAffine {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ ModuleCat.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  (modulePushforward B S hS f ⋙
    SheafOfModules.evaluation.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O)) (op (idEtaleChart B S hS V))) ⋙
    (ModuleCat.restrictScalars.{u} (idChartRingHom B V) ⋙
      ModuleCat.uliftFunctor.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- **The global sections of an `𝒪_X`-module are the sections of its direct image over `V`**,
linearly over the functions on `V`, for a morphism `f : X ⟶ V`. -/
def globalSectionsLinearEquivPushforwardSectionsOverAffine {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace V) (M : Modules.{u, u} B S hS X.1 X.2) :
    (globalSectionsOverAffine B V f).obj M ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      (pushforwardSectionsOverAffine B V f).obj M where
  toEquiv := globalSectionsEquivPushforwardSections (S := S) (hS := hS) V f M
  map_add' s t := by
    have h := (((globalSectionsModulePushforwardIso B S hS f).app M).inv.hom).map_add s t
    exact congrArg ULift.up (congrArg (fun z : ((modulePushforward B S hS f).obj
      M).sections => z.eval (op (idEtaleChart B S hS V))) h)
  map_smul' a s := by
    have hs : (a • s : (globalSectionsOverAffine B V f).obj M) =
        SheafOfModules.sectionsMap
          (globalSmul _ (pullbackToGlobalFunctions B S hS X V (f ≫ 𝟙 _) a) M) s :=
      Subtype.ext (funext fun _ => rfl)
    refine (congrArg (globalSectionsEquivPushforwardSections (S := S) (hS := hS) V f M) hs).trans ?_
    refine (globalSectionsEquivPushforwardSections_sectionsMap (S := S) (hS := hS) V f _ s).trans ?_
    have hpush := modulePushforward_map_globalSmul_pullbackToGlobalFunctions B S hS f (𝟙 _) M a
    refine (congrArg (fun φ : (modulePushforward B S hS f).obj M ⟶ _ =>
      (ULift.up (φ.val.app (op (idEtaleChart B S hS V))
        (globalSectionsEquivPushforwardSections (S := S) (hS := hS) V f M s).down) :
          ULift.{u + 1} (((modulePushforward B S hS f).obj M).val.obj
            (op (idEtaleChart B S hS V))))) hpush).trans ?_
    rfl

/-- `AlgebraicGeometry.Space.globalSectionsLinearEquivPushforwardSectionsOverAffine`, natural in
the module. -/
def globalSectionsOverAffineIso {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) :
    globalSectionsOverAffine B V f ≅ pushforwardSectionsOverAffine B V f :=
  NatIso.ofComponents
    (fun M => (globalSectionsLinearEquivPushforwardSectionsOverAffine B V f M).toModuleIso)
    (fun {M M'} φ => by
      ext s
      exact globalSectionsEquivPushforwardSections_sectionsMap (S := S) (hS := hS) V f φ s)

attribute [local instance] hasInjectiveResolutions_modules in
/-- **Finiteness of cohomology over an affine Noetherian target**: for a proper morphism
`f : X ⟶ V` to an affine Noetherian object of the site and a coherent `𝒪_X`-module `F`,
`Hⁱ(X, F)` is a finite module over the functions on `V`, acting through `f`.  This is
Stacks 08AS with the base `Spec A` replaced by an arbitrary affine Noetherian scheme of the
site. -/
theorem moduleFinite_cohomology_of_isProper_of_isAffine
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 F] (i : ℕ) :
    Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars (pullbackRingHom B V f)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O))).rightDerived i).obj
            F)) := by
  have := modulePushforward_additive B S hS f
  have : (SheafOfModules.evaluation.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
      (op (idEtaleChart B S hS V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have hfin := hasFiniteCohomologyOver_of_isProper B S hS V inferInstance f hf F inferInstance i
  let E := ModuleCat.restrictScalars.{u} (idChartRingHom B V) ⋙
    ModuleCat.uliftFunctor.{u + 1} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
  let Q := modulePushforward B S hS f ⋙
    SheafOfModules.evaluation.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O)) (op (idEtaleChart B S hS V))
  have : Q.Additive := ⟨fun {M N a b} => by
    show ((modulePushforward B S hS f).map (a + b)).val.app _ = _
    rw [Functor.map_add]
    rfl⟩
  let Γ' := globalSectionsFunctor.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  have e₁ := (Functor.rightDerivedCompIso Γ'
    (ModuleCat.restrictScalars.{u + 1} (pullbackRingHom B V f)) i).app F
  have e₂ := (Functor.rightDerivedIsoOfNatIso
    (F := Γ' ⋙ ModuleCat.restrictScalars.{u + 1} (pullbackRingHom B V f))
    (G := Q ⋙ E) (globalSectionsOverAffineIso B V f) i).app F
  have e₃ := (Functor.rightDerivedCompIso Q E i).app F
  have h₁ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (idChartRingHom B V)).obj ((Q.rightDerived i).obj F)) := by
    let l : ((ModuleCat.restrictScalars.{u} (idChartRingHom B V)).obj
        ((Q.rightDerived i).obj F)) →ₛₗ[idChartRingHom B V] ((Q.rightDerived i).obj F) :=
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have : RingHomSurjective (idChartRingHom B V) := ⟨(bijective_idChartRingHom B V).2⟩
    exact (l.finite_iff_of_bijective Function.bijective_id).2 hfin
  have h₂ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((Q.rightDerived i ⋙ E).obj F) :=
    Module.Finite.equiv ULift.moduleEquiv.symm
  have h₃ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (((Q ⋙ E).rightDerived i).obj F) :=
    Module.Finite.equiv e₃.symm.toLinearEquiv
  have h₄ : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (((Γ' ⋙ ModuleCat.restrictScalars.{u + 1}
        (pullbackRingHom B V f)).rightDerived i).obj F) :=
    Module.Finite.equiv e₂.symm.toLinearEquiv
  exact Module.Finite.equiv e₁.toLinearEquiv

end AffineTarget

end AlgebraicGeometry.Space

end
