module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassSurjectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# First cohomology over an object: right derived sections against `Ext` on the localized site

Let `(C, K)` be a site, `U` an object of `C` and `T = Γ(U, -)` the sections functor on abelian
sheaves. Two models of the cohomology `Hⁿ(U, G)` of an abelian sheaf `G` are in use: the right
derived functors `RⁿT(G)` of sections over `U`, and the `Ext`-groups `Extⁿ(ℤ, G|_U)` on the
localized site `(C/U, K.over U)` out of the constant sheaf `ℤ`, which is Mathlib's
`CategoryTheory.Sheaf.H (G.over U) n` and the target of the torsor classification of
Stacks 03AJ.

Restriction `G ↦ G|_U` is exact and preserves injective sheaves, so `G ↦ Extⁿ(ℤ, G|_U)` is a
universal `δ`-functor on abelian sheaves on `C`, with connecting maps the composition with the
extension class of the restricted short exact sequence. The right derived functors of `T` form a
universal `δ`-functor as well, and in degree zero both are `T`: a morphism `ℤ ⟶ G|_U` is
determined by its value on the section `1` over the terminal object `U` of `C/U`. Hence
(Stacks 010U) there is a unique isomorphism of `δ`-functors extending this identification, and
its degree-one component identifies the two models of `H¹(U, G)`.

## Main definitions

* `Stacks.Cohomology.Torsors.sliceExtDeltaFunctor`: the `δ`-functor `G ↦ Extⁿ(ℤ, G|_U)`.
* `Stacks.Cohomology.Torsors.sliceExtZeroIso`: its degree-zero part is `Γ(U, -)`.
* `Stacks.Cohomology.Torsors.sliceExtIsoRightDerived`: the isomorphism of `δ`-functors with the
  right derived functors of `Γ(U, -)` extending `sliceExtZeroIso`.
* `Stacks.Cohomology.Torsors.rightDerivedSectionsOneEquivSliceH`: the resulting identification
  `H¹(U, G) ≃+ Sheaf.H (G.over U) 1`, out of the bounded below derived model of `H¹(U, G)`.

## Main results

* `Stacks.Cohomology.Torsors.rightDerivedSectionsOneEquivSliceH_δ`: the identification carries
  the connecting map of a short exact sequence `0 → G₁ → G₂ → G₃ → 0`, applied to a section of
  `G₃` over `U`, to that section composed with the extension class of the restricted sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe a w t v u

namespace Stacks.Cohomology.Torsors

attribute [local instance] HasDerivedCategory.standard

section Exactness

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (U : C)

/-- Restriction of abelian sheaves to a localized site preserves finite limits: on underlying
presheaves it is precomposition with `Over.forget U`. -/
instance preservesFiniteLimits_overPullback_addCommGrpCat :
    PreservesFiniteLimits (K.overPullback AddCommGrpCat.{t} U) := by
  have : PreservesFiniteLimits (K.overPullback AddCommGrpCat.{t} U ⋙
      sheafToPresheaf (K.over U) AddCommGrpCat.{t}) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf K AddCommGrpCat.{t} ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{t}).obj (Over.forget U).op))
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (K.over U) AddCommGrpCat.{t})

variable [HasSheafify K AddCommGrpCat.{t}] [HasSheafify (K.over U) AddCommGrpCat.{t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- Restriction of abelian sheaves to a localized site preserves finite colimits. -/
instance preservesFiniteColimits_overPullback_addCommGrpCat :
    PreservesFiniteColimits (K.overPullback AddCommGrpCat.{t} U) :=
  Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{v, u, t} K U

end Exactness

section Restriction

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (U : C)

/-- Abelian sheaves on every localized site have sheafification at the coefficient universe
`max a u v w`. -/
theorem hasSheafify_over_addCommGrpCat (V : C) :
    HasSheafify (K.over V) AddCommGrpCat.{max a u v w} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max u v, v, max a w} (J := K.over V)

/-- Restriction of abelian sheaves to a localized site preserves injective objects, at any
coefficient universe containing the universes of the site. -/
@[sga "4 V 2.2" "special case"]
theorem preservesInjectiveObjects_overPullback_addCommGrpCat
    [HasSheafify K AddCommGrpCat.{max a u v w}] :
    (K.overPullback AddCommGrpCat.{max a u v w} U).PreservesInjectiveObjects :=
  have : ∀ V : C, HasSheafify (K.over V) AddCommGrpCat.{max a u v w} :=
    hasSheafify_over_addCommGrpCat.{a, w} K
  Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{v, u, max a u v w} K U

/-- The constant presheaf `ℤ` on `C/U`. -/
abbrev sliceUnitPresheaf : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))

/-- The constant sheaf `ℤ` on the localized site `C/U`, the source of the `Ext`-groups of
`CategoryTheory.Sheaf.H`: the sheafification of the constant presheaf `ℤ`. -/
abbrev sliceUnit [HasSheafify (K.over U) AddCommGrpCat.{t}] :
    Sheaf (K.over U) AddCommGrpCat.{t} :=
  (presheafToSheaf (K.over U) AddCommGrpCat.{t}).obj (sliceUnitPresheaf.{t} U)

variable [HasSheafify K AddCommGrpCat.{t}] [HasSheafify (K.over U) AddCommGrpCat.{t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [HasExt.{t} (Sheaf (K.over U) AddCommGrpCat.{t})]

/-- **The `δ`-functor `G ↦ Extⁿ(ℤ, G|_U)`** on abelian sheaves on `C`: the `Ext`-groups on the
localized site out of the constant sheaf `ℤ`, precomposed with the exact restriction functor. Its
degree-`n` value at `G` is `CategoryTheory.Sheaf.H (G.over U) n`. -/
def sliceExtDeltaFunctor : DeltaFunctor (Sheaf K AddCommGrpCat.{t}) AddCommGrpCat.{t} :=
  ModuleSheafCohomology.extDeltaFunctor (K.overPullback AddCommGrpCat.{t} U) (sliceUnit K U)

omit [HasSheafify K AddCommGrpCat.{t}] [HasSheafify (K.over U) AddCommGrpCat.{t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasExt.{t} (Sheaf (K.over U) AddCommGrpCat.{t})] in
/-- `G ↦ Extⁿ(ℤ, G|_U)` is a universal `δ`-functor: restriction carries injective sheaves to
injective sheaves, on which the positive `Ext`-groups vanish. -/
theorem sliceExtDeltaFunctor_isUniversal [HasSheafify K AddCommGrpCat.{max a u v w}]
    [HasSheafify (K.over U) AddCommGrpCat.{max a u v w}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
    [HasExt.{max a u v w} (Sheaf (K.over U) AddCommGrpCat.{max a u v w})]
    [EnoughInjectives (Sheaf K AddCommGrpCat.{max a u v w})] :
    (sliceExtDeltaFunctor.{max a u v w} K U).IsUniversal :=
  ModuleSheafCohomology.extDeltaFunctor_isUniversal _ _ fun I _ _ e => by
    have := preservesInjectiveObjects_overPullback_addCommGrpCat.{a, w} K U
    have : Injective ((K.overPullback AddCommGrpCat.{max a u v w} U).obj I) :=
      (K.overPullback AddCommGrpCat.{max a u v w} U).injective_obj I
    exact Ext.eq_zero_of_injective e

end Restriction

section DegreeZero

section Terminal

variable {C : Type u} [Category.{v} C] (U : C)

/-- A morphism from the constant integral presheaf on `C/U` to an abelian presheaf is the family
of restrictions of its value on `1` over the terminal object `U`. -/
theorem terminalSectionFamily_app_one {A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{t}}
    (h : (Functor.const (Over U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A) :
    terminalSectionFamily A (h.app (op (Over.mk (𝟙 U))) ⟨1⟩) = h :=
  NatTrans.ext <| funext fun W ↦ liftedInt_hom_ext _ _ <| (terminalSectionFamily_app A _ W).trans
    (sectionFamilyOfMorphism_naturality A h (Over.mkIdTerminal.from W.unop).op)

/-- The value of `terminalSectionFamily` on `1` over the terminal object is the given section. -/
theorem terminalSectionFamily_app_terminal (A : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{t})
    (y : A.obj (op (Over.mk (𝟙 U)))) :
    (terminalSectionFamily A y).app (op (Over.mk (𝟙 U))) ⟨1⟩ = y := by
  refine (terminalSectionFamily_app A y _).trans ?_
  rw [Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from (Over.mk (𝟙 U))) (𝟙 _), op_id,
    A.map_id]
  rfl

end Terminal

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (U : C)
  [HasSheafify (K.over U) AddCommGrpCat.{t}] [HasExt.{t} (Sheaf (K.over U) AddCommGrpCat.{t})]

/-- `Ext⁰(ℤ, G|_U) ≃+ Γ(U, G)`: a class is sent to the value on `1`, over the terminal object of
`C/U`, of the morphism of presheaves adjoint to the morphism of sheaves it represents. -/
def sliceExtZeroAddEquiv (G : Sheaf K AddCommGrpCat.{t}) :
    Ext (sliceUnit K U) (G.over U) 0 ≃+ G.obj.obj (op U) where
  toFun e := (((sheafificationAdjunction (K.over U) AddCommGrpCat.{t}).homAddEquiv
    (sliceUnitPresheaf.{t} U) (G.over U) (Ext.addEquiv₀ e)).app (op (Over.mk (𝟙 U))))
      (⟨1⟩ : ULift.{t} ℤ)
  invFun y := Ext.mk₀ (((sheafificationAdjunction (K.over U) AddCommGrpCat.{t}).homEquiv
    (sliceUnitPresheaf.{t} U) (G.over U)).symm (terminalSectionFamily (G.over U).obj y))
  left_inv e := by
    dsimp only
    rw [Adjunction.homAddEquiv_apply, terminalSectionFamily_app_one, Equiv.symm_apply_apply]
    exact Ext.mk₀_addEquiv₀_apply e
  right_inv y := by
    dsimp only
    rw [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply, Adjunction.homAddEquiv_apply,
      Equiv.apply_symm_apply]
    exact terminalSectionFamily_app_terminal U (G.over U).obj y
  map_add' e e' := by
    rw [map_add, map_add]
    rfl

variable [HasSheafify K AddCommGrpCat.{t}] [K.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **The degree-zero part of `G ↦ Extⁿ(ℤ, G|_U)` is the sections functor over `U`**, by
`sliceExtZeroAddEquiv`. -/
def sliceExtZeroIso : (sliceExtDeltaFunctor K U).functor 0 ≅
    (sheafSections K AddCommGrpCat.{t}).obj (op U) :=
  NatIso.ofComponents (fun G ↦ (sliceExtZeroAddEquiv K U G).toAddCommGrpIso) (by
    intro G G' g
    ext e
    change sliceExtZeroAddEquiv K U G' (e.comp (Ext.mk₀
        ((K.overPullback AddCommGrpCat.{t} U).map g)) (add_zero 0)) =
      g.hom.app (op U) (sliceExtZeroAddEquiv K U G e)
    have h : Ext.addEquiv₀ (e.comp (Ext.mk₀
        ((K.overPullback AddCommGrpCat.{t} U).map g)) (add_zero 0)) =
        Ext.addEquiv₀ e ≫ (K.overPullback AddCommGrpCat.{t} U).map g := by
      apply Ext.addEquiv₀.symm.injective
      rw [AddEquiv.symm_apply_apply, Ext.addEquiv₀_symm_apply, ← Ext.mk₀_comp_mk₀]
      exact congrArg (fun x ↦ x.comp (Ext.mk₀ ((K.overPullback AddCommGrpCat.{t} U).map g))
        (add_zero 0)) (Ext.mk₀_addEquiv₀_apply e).symm
    change (((sheafificationAdjunction (K.over U) AddCommGrpCat.{t}).homAddEquiv
        (sliceUnitPresheaf.{t} U) (G'.over U)
        (Ext.addEquiv₀ (e.comp (Ext.mk₀
          ((K.overPullback AddCommGrpCat.{t} U).map g)) (add_zero 0)))).app
          (op (Over.mk (𝟙 U)))) (⟨1⟩ : ULift.{t} ℤ) = _
    rw [h, Adjunction.homAddEquiv_apply, Adjunction.homEquiv_naturality_right]
    rfl)

/-- The inverse of `sliceExtZeroIso` sends a section over `U` to the `Ext⁰`-class of the morphism
of sheaves out of `ℤ` adjoint to the family of its restrictions. -/
theorem sliceExtZeroIso_inv_app_apply (G : Sheaf K AddCommGrpCat.{t}) (y : G.obj.obj (op U)) :
    (sliceExtZeroIso K U).inv.app G y =
      Ext.mk₀ (((sheafificationAdjunction (K.over U) AddCommGrpCat.{t}).homEquiv
        (sliceUnitPresheaf.{t} U) (G.over U)).symm (terminalSectionFamily (G.over U).obj y)) :=
  rfl

end DegreeZero

section Comparison

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (U : C)

/-- Sections over `U` of abelian sheaves preserve finite limits. -/
instance preservesFiniteLimits_sheafSections_addCommGrpCat :
    PreservesFiniteLimits ((sheafSections K AddCommGrpCat.{t}).obj (op U)) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf K AddCommGrpCat.{t} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{t}).obj (op U)))

/-- The right derived functors of sections over `U` form a universal `δ`-functor. -/
instance rightDerivedDeltaFunctor_sections_isUniversal [HasSheafify K AddCommGrpCat.{t}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{t}] [EnoughInjectives (Sheaf K AddCommGrpCat.{t})] :
    (Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor
      ((sheafSections K AddCommGrpCat.{t}).obj (op U))).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun n I _ ↦
    ((sheafSections K AddCommGrpCat.{t}).obj (op U)).isZero_rightDerived_obj_injective_succ n I

variable [HasSheafify K AddCommGrpCat.{max a u v w}]
  [HasSheafify (K.over U) AddCommGrpCat.{max a u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [HasExt.{max a u v w} (Sheaf (K.over U) AddCommGrpCat.{max a u v w})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max a u v w})]

/-- **The `Ext`-groups of the restriction to `C/U` are the right derived functors of sections over
`U`**, as the unique isomorphism of universal `δ`-functors (Stacks 010U) whose degree-zero
component is `sliceExtZeroIso` followed by the inverse of
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
def sliceExtIsoRightDerived : sliceExtDeltaFunctor.{max a u v w} K U ≅
    Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor
      ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)) :=
  haveI := sliceExtDeltaFunctor_isUniversal.{a, w} K U
  DeltaFunctor.IsUniversal.isoOfIso (sliceExtZeroIso K U ≪≫
    ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)).rightDerivedZeroIsoSelf.symm)

/-- The degree-zero component of the inverse of `sliceExtIsoRightDerived`. -/
theorem sliceExtIsoRightDerived_inv_app_zero :
    (sliceExtIsoRightDerived.{a, w} K U).inv.app 0 =
      ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)).rightDerivedZeroIsoSelf.hom ≫
        (sliceExtZeroIso K U).inv :=
  have := sliceExtDeltaFunctor_isUniversal.{a, w} K U
  DeltaFunctor.IsUniversal.isoOfIso_inv_app_zero _

/-- The degree-`n` component of `sliceExtIsoRightDerived` at a sheaf `G`, as an isomorphism of
abelian groups `Extⁿ(ℤ, G|_U) ≅ RⁿΓ(U, G)`. -/
def sliceExtIsoRightDerivedApp (n : ℕ) (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    ((sliceExtDeltaFunctor.{max a u v w} K U).functor n).obj G ≅
      (((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)).rightDerived n).obj G where
  hom := ((sliceExtIsoRightDerived.{a, w} K U).hom.app n).app G
  inv := ((sliceExtIsoRightDerived.{a, w} K U).inv.app n).app G
  hom_inv_id := congrArg (fun η : sliceExtDeltaFunctor.{max a u v w} K U ⟶ _ ↦ (η.app n).app G)
    (sliceExtIsoRightDerived.{a, w} K U).hom_inv_id
  inv_hom_id := congrArg (fun η : Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor
      ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)) ⟶ _ ↦ (η.app n).app G)
    (sliceExtIsoRightDerived.{a, w} K U).inv_hom_id

/-- **The two models of `H¹(U, G)`.** The first cohomology of `G` over `U`, read as the degree-one
homology of the right derived sections functor on the bounded below derived category, is
`CategoryTheory.Sheaf.H (G.over U) 1`, the first `Ext`-group out of `ℤ` on the localized site
`C/U`. The identification is the degree-one component of the unique isomorphism of universal
`δ`-functors normalized in degree zero by the identification of `Ext⁰(ℤ, G|_U)` with the sections
of `G` over `U` (`sliceExtIsoRightDerived`), composed with the comparison
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard` of the two indexings of the
right derived functors. -/
@[sga "4 V 2.2" "H^q(E/X, special case"]
def rightDerivedSectionsOneEquivSliceH (G : Sheaf K AddCommGrpCat.{max a u v w}) :
    (((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)).rightDerivedPlus 1).obj G ≃+
      Sheaf.H (G.over U) 1 :=
  ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
      ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)) 1).app G ≪≫
    (sliceExtIsoRightDerivedApp.{a, w} K U 1 G).symm).addCommGroupIsoToAddEquiv

/-- **The identification of the two models of `H¹(U, G)` carries connecting maps to extension
classes.** For a short exact sequence `0 → G₁ → G₂ → G₃ → 0` of abelian sheaves on `C` and a
section `y` of `G₃` over `U`, the connecting map of the right derived functors of sections, applied
to `y`, corresponds to the `Ext⁰`-class of `y` over `C/U` composed with the extension class of the
restricted short exact sequence. -/
theorem rightDerivedSectionsOneEquivSliceH_δ
    (S : ShortComplex (Sheaf K AddCommGrpCat.{max a u v w})) (hS : S.ShortExact)
    (y : S.X₃.obj.obj (op U)) :
    rightDerivedSectionsOneEquivSliceH.{a, w} K U S.X₁
        (Stacks.Cohomology.CechDelta.rightDerivedPlusδ
          ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)) hS 0
          ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard
            ((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)) 0).inv.app S.X₃
            (((sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)).toRightDerivedZero.app
              S.X₃ y))) =
      (Ext.mk₀ (((sheafificationAdjunction (K.over U) AddCommGrpCat.{max a u v w}).homEquiv
          (sliceUnitPresheaf.{max a u v w} U) (S.X₃.over U)).symm
            (terminalSectionFamily (S.X₃.over U).obj y))).comp
        (hS.map_of_exact (K.overPullback AddCommGrpCat.{max a u v w} U)).extClass
          (zero_add 1) := by
  set T := (sheafSections K AddCommGrpCat.{max a u v w}).obj (op U)
  have hcomm := (sliceExtIsoRightDerived.{a, w} K U).inv.comm hS 0
  have hδ : (Stacks.Cohomology.CechDelta.rightDerivedDeltaFunctor T).δ hS 0 =
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard T 0).inv.app S.X₃ ≫
        Stacks.Cohomology.CechDelta.rightDerivedPlusδ T hS 0 ≫
          (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard T 1).hom.app S.X₁ :=
    rfl
  rw [sliceExtIsoRightDerived_inv_app_zero, hδ] at hcomm
  have key := congrArg (fun f ↦ f (T.toRightDerivedZero.app S.X₃ y)) hcomm
  have hy : T.rightDerivedZeroIsoSelf.hom.app S.X₃ (T.toRightDerivedZero.app S.X₃ y) = y :=
    congrArg (fun f ↦ f y) (T.rightDerivedZeroIsoSelf_inv_hom_id_app S.X₃)
  exact Eq.trans (by rfl) (key.symm.trans ((congrArg (fun z ↦
    (sliceExtDeltaFunctor.{max a u v w} K U).δ hS 0 ((sliceExtZeroIso K U).inv.app S.X₃ z))
      hy).trans rfl))

end Comparison

end Stacks.Cohomology.Torsors

end
