module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.FilteredColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing

/-!
# Acyclicity of the underlying abelian sheaf of an injective sheaf of modules, on any site

Let `(𝒞, K)` be a site whose objects need not form a small type, let `R` be a sheaf of rings on it
and let `I` be an injective sheaf of `R`-modules. The underlying abelian sheaf `I_ab` of `I` is
not an injective abelian sheaf, but it is acyclic:

* `Ext^(n+1)(ℤ[U], I_ab) = 0` for every object `U` of `𝒞`, where `ℤ[U]` is the free abelian sheaf
  on the representable at `U`;
* `H^(q+1)(U, I_ab) = 0` for every object `U` of `𝒞`;
* `R^(q+1) f_* I_ab = 0` for the direct image along any continuous functor `u : 𝒟 ⥤ 𝒞`.

These are the statements of
`Stacks.Cohomology.ModuleComparison.rightAcyclic_toSheaf_obj_of_injective` and
`Stacks.Cohomology.ModuleInjectiveHigherDirectImage.isZero_higherDirectImage_toSheaf_succ`
with the smallness of the site removed: there `𝒞 : Type u` carries `[SmallCategory 𝒞]`, which the
small étale site of a scheme does not, its objects forming a type one universe above its
morphisms.

## Main results

* `Stacks.Cohomology.InjectiveModuleSheafAcyclicity.ext_eq_zero_of_injective_toSheaf`: the
  `Ext`-vanishing against the free abelian sheaf on a representable.
* `Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ`:
  `H^(q+1)(U, I_ab) = 0`.
* `Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_cohomologyPresheaf_succ`:
  the presheaf `V ↦ H^(q+1)(u(V), I_ab)` on `𝒟` is zero.
* `Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ`:
  **`R^(q+1) f_* I_ab = 0`**.

## Implementation notes

**What replaces smallness.** The hypotheses are the instances that smallness supplies: abelian
sheafification in the coefficient universe, sheafification inverting exactly the locally
bijective maps, existence of `Ext` and enough injectives. On a site whose objects live in `Type
u₁` and whose morphisms in `Type v₁` these hold for coefficients `AddCommGrpCat.{max u₁ v₁ t}`
with `t` arbitrary, by `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp` and its
companions, which transport the small-site statements along the equivalence with the small model
of the site. The coefficient universe is a `max` over the universes of the site because the
corepresentation of sections used below is, the corepresenting object being an abelian sheaf
whose sections are indexed by the morphisms of the site.

**Route.** The acyclicity is `Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`, the
torsion-free dévissage behind [Stacks, Tag 03FD], applied to the free abelian sheaf on the
representable at `U`: that sheaf is the sheafification of a sectionwise free, hence sectionwise
torsion-free, abelian presheaf. The passage from `Ext` to right-derived sections is
`Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections`, the
corepresentation of sections with the coefficient universe freed; this is shorter than the
derived-category route of [Stacks, Tag 0157] and [Stacks, Tag 015C] taken on the small site, and
needs no `HasDerivedCategory` instance. The passage from cohomology over the objects of `𝒞` to
the higher direct images is `Stacks.Cohomology.SheafifiedHigherDirectImage`, which is [Stacks,
Tag 072W] for abelian sheaves and is already stated for an arbitrary site.

**Degrees.** Everything is indexed by `Functor.rightDerived`, Mathlib's `ℕ`-indexed right derived
functors, and stated in degree `q + 1` so that positivity of the degree is automatic.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian
open Stacks.Cohomology.FreeYonedaUnivLE
open Stacks.Cohomology.SheafifiedHigherDirectImage

namespace Stacks.Cohomology.InjectiveModuleSheafAcyclicity

universe t v₁ u₁ v₂ u₂

section Sections

variable {C : Type u₁} [Category.{v₁} C] (K : GrothendieckTopology C)
  [HasSheafify K AddCommGrpCat.{max u₁ v₁ t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ t}]
  [HasExt.{max u₁ v₁ t} (Sheaf K AddCommGrpCat.{max u₁ v₁ t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max u₁ v₁ t})]
  (R : Sheaf K RingCat.{max u₁ v₁ t}) (I : SheafOfModules.{max u₁ v₁ t} R) [Injective I]

/-- **The acyclicity of [Stacks, Tag 03FD] against the free abelian sheaf on a representable.**
The underlying abelian sheaf of an injective sheaf of `R`-modules has vanishing positive-degree
`Ext` out of the free abelian sheaf on the representable at an object `V` of the site, that sheaf
being the sheafification of a sectionwise free abelian presheaf. -/
theorem ext_eq_zero_of_injective_toSheaf (V : C) (n : ℕ)
    (e : Ext.{max u₁ v₁ t} ((freeYoneda.{max u₁ t} K).obj V)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) : e = 0 :=
  Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree K R I _
    (ModuleSheafCohomology.isTorsionFree_sheafify K
      (uliftYoneda.{max u₁ t}.obj V ⋙ AddCommGrpCat.free) (fun point => by
        show Module.IsTorsionFree ℤ
          (FreeAbelianGroup (ULift.{max u₁ t} (point.unop ⟶ V)))
        exact Module.Flat.isTorsionFree)) n e

/-- **`H^(q+1)(V, I_ab) = 0`.** The higher cohomology over an object `V` of the site of the
underlying abelian sheaf of an injective sheaf of `R`-modules vanishes. Sections over `V` are
corepresented by the free abelian sheaf on the representable at `V`, so their right derived
functors are the `Ext`-groups out of it, which `ext_eq_zero_of_injective_toSheaf` kills. -/
theorem isZero_rightDerived_sections_toSheaf_succ (V : C) (q : ℕ) :
    IsZero ((((sheafSections K AddCommGrpCat.{max u₁ v₁ t}).obj (op V)).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) := by
  refine IsZero.of_iso ?_
    (((nonempty_extFunctorObj_iso_rightDerived_sections.{t} K V (q + 1)).some).app
      ((SheafOfModules.toSheaf R).obj I)).symm
  refine AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  rw [ext_eq_zero_of_injective_toSheaf.{t} K R I V q a,
    ext_eq_zero_of_injective_toSheaf.{t} K R I V q b]

end Sections

section DirectImage

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology D) (K : GrothendieckTopology C) (u : D ⥤ C) [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max u₁ v₁ t}]
  [HasSheafify K AddCommGrpCat.{max u₁ v₁ t}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ t}]
  [HasExt.{max u₁ v₁ t} (Sheaf K AddCommGrpCat.{max u₁ v₁ t})]
  [EnoughInjectives (Sheaf K AddCommGrpCat.{max u₁ v₁ t})]
  (R : Sheaf K RingCat.{max u₁ v₁ t}) (I : SheafOfModules.{max u₁ v₁ t} R) [Injective I]

/-- The vanishing of `H^(q+1)(u(V), I_ab)` read through the cohomology presheaf of the direct
image, which evaluated at `V` is the sections functor over `u(V)`. -/
theorem isZero_rightDerived_cohomologyPresheaf_obj_succ (V : D) (q : ℕ) :
    IsZero (((pushforwardCohomologyPresheaf (K := K) AddCommGrpCat.{max u₁ v₁ t} u ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{max u₁ v₁ t}).obj (op V)).rightDerived (q + 1)).obj
      ((SheafOfModules.toSheaf R).obj I)) :=
  isZero_rightDerived_sections_toSheaf_succ.{t} K R I (u.obj V) q

/-- **The cohomology presheaf of the direct image vanishes in positive degrees** on the underlying
abelian sheaf of an injective sheaf of `R`-modules: the presheaf `V ↦ H^(q+1)(u(V), I_ab)` on `𝒟`
is the zero presheaf, all of its values being zero. -/
theorem isZero_rightDerived_cohomologyPresheaf_succ (q : ℕ) :
    IsZero (((pushforwardCohomologyPresheaf (K := K) AddCommGrpCat.{max u₁ v₁ t} u).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) :=
  Functor.isZero_of_isZero_obj _ fun V ↦
    IsZero.of_iso (isZero_rightDerived_cohomologyPresheaf_obj_succ.{t} K u R I V.unop q)
      ((pushforwardCohomologyPresheafEvaluationIso AddCommGrpCat.{max u₁ v₁ t} u (q + 1)
        V.unop).app ((SheafOfModules.toSheaf R).obj I)).symm

/-- **[Stacks, Tag 03FD] for higher direct images on an arbitrary site: `R^(q+1) f_* I_ab = 0`.**
For a continuous functor `u : 𝒟 ⥤ 𝒞` and an injective sheaf of `R`-modules `I` on `𝒞`, the higher
direct images of the underlying abelian sheaf of `I` vanish in positive degrees.

The underlying abelian sheaf of `I` need not be an injective abelian sheaf, so this does not
follow from `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ`. It follows instead
from the vanishing of `H^(q+1)(V, I_ab)` for every object `V` of `𝒞` together with the
description of `R^(q+1) f_*` as the sheafification of the cohomology presheaf
`V ↦ H^(q+1)(u(V), -)` ([Stacks, Tag 072W]). -/
theorem isZero_higherDirectImage_toSheaf_succ (q : ℕ) :
    IsZero (((u.sheafPushforwardContinuous AddCommGrpCat.{max u₁ v₁ t} J K).rightDerived
      (q + 1)).obj ((SheafOfModules.toSheaf R).obj I)) :=
  IsZero.of_iso
    (Functor.map_isZero (presheafToSheaf J AddCommGrpCat.{max u₁ v₁ t})
      (isZero_rightDerived_cohomologyPresheaf_succ.{t} K u R I q))
    ((rightDerivedPushforwardIso AddCommGrpCat.{max u₁ v₁ t} u (q + 1)).app
      ((SheafOfModules.toSheaf R).obj I))

end DirectImage

end Stacks.Cohomology.InjectiveModuleSheafAcyclicity

end
