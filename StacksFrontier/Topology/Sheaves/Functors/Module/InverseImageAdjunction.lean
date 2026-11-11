module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import StacksFrontier.Topology.Sheaves.Functors.Module.InverseImage
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackPresheafAdjunction

/-!
# Adjointness of the concrete inverse image and the direct image of modules

Let `f : X ⟶ Y` be a continuous map of topological spaces and `O` a sheaf of rings on `Y`.
The inverse image `f⁻¹G` of a sheaf of `O`-modules `G` is, following the Stacks Project, the
sheafification of the presheaf-level pullback `f_p G` (Tag 008T), with the sheaf of
`f⁻¹O`-modules structure of Tag 008X (`InverseImageModules.inverseImageSheafOfModules`), where
`f⁻¹O = InverseImageModules.inverseImageRing f O` is the sheafification of `f_p O`.

For a sheaf of `f⁻¹O`-modules `F`, the direct image `f_*F` is a sheaf of `O`-modules by
restriction of scalars along the canonical map `O ⟶ f_*f⁻¹O`, the composite of the unit
`O ⟶ f_*f_p O` of Tag 008U with the pushforward of the sheafification map `f_p O ⟶ f⁻¹O`.

## Main results

* `InverseImageModules.inverseImageModules`: the concrete inverse image functor
  `G ↦ f⁻¹G`, whose value at `G` is `inverseImageSheafOfModules f O G` by definition.
* `InverseImageModules.inverseImageModulesAdjunction`: it is left adjoint to `f_*`.
* `InverseImageModules.inverseImageModulesHomEquiv`: Stacks Tag 008Y,
  `Mor_{Mod(f⁻¹O)}(f⁻¹G, F) ≃ Mor_{Mod(O)}(G, f_*F)`.

The proof follows the Stacks Project: the bijection is the composite of the sheafification
adjunction of modules (Tag 0089, `PresheafOfModules.sheafificationAdjunction`) and the
presheaf-level adjunction of Tag 008U for `f_p`
(`Stacks.PresheafOfModules.Pullback.pullbackModuleAdjunction`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Stacks.PresheafOfModules.Pullback

universe u

namespace InverseImageModules

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})

/-- The inverse image ring `f⁻¹O = inverseImageRing f O`, typed as a sheaf on the site
`Opens.grothendieckTopology X`, which is the form in which the category of sheaves of
`f⁻¹O`-modules is found by instance search. -/
noncomputable abbrev inverseImageRingSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  inverseImageRing f O

/-- The canonical morphism of sheaves of rings `O ⟶ f_*f⁻¹O`, for the concrete inverse image
ring `f⁻¹O = inverseImageRing f O`: the unit `O ⟶ f_*f_p O` followed by the pushforward of
the sheafification map `f_p O ⟶ f⁻¹O`. -/
noncomputable def toPushforwardInverseImageRing :
    O ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
        (inverseImageRingSheaf f O) :=
  ObjectProperty.homMk (pullbackRingUnitHom f O.obj ≫
    Functor.whiskerLeft (Opens.map f).op (toInverseImageRing f O))

/-- The direct image `f_*` from sheaves of `f⁻¹O`-modules on `X` to sheaves of `O`-modules on
`Y`, the `O`-module structure on `f_*F` coming by restriction of scalars along the canonical
map `O ⟶ f_*f⁻¹O` (`toPushforwardInverseImageRing`). -/
noncomputable abbrev directImageModules :
    SheafOfModules.{u} (inverseImageRingSheaf f O) ⥤ SheafOfModules.{u} O :=
  SheafOfModules.pushforward.{u} (toPushforwardInverseImageRing f O)

/-- The concrete inverse image functor `G ↦ f⁻¹G` from sheaves of `O`-modules on `Y` to sheaves
of `f⁻¹O`-modules on `X`: the sheafification of the presheaf-level pullback `f_p G` of
Tag 008T, with the module structure of Tag 008X. -/
noncomputable def inverseImageModules :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} (inverseImageRingSheaf f O) :=
  haveI := isLocallyInjective_toInverseImageRing f O
  haveI := isLocallySurjective_toInverseImageRing f O
  SheafOfModules.forget O ⋙ pullbackModuleFunctor f O.obj ⋙
    PresheafOfModules.sheafification (R := inverseImageRingSheaf f O) (toInverseImageRing f O)

/-- The concrete inverse image functor sends `G` to the sheaf of `f⁻¹O`-modules `f⁻¹G` of
Tag 008X, `inverseImageSheafOfModules f O G`. -/
theorem inverseImageModules_obj (G : SheafOfModules.{u} O) :
    (inverseImageModules f O).obj G = inverseImageSheafOfModules f O G :=
  rfl

/-- The concrete inverse image functor `f⁻¹` on sheaves of modules is left adjoint to the
direct image `f_*`: the composite of the presheaf-level adjunction of Tag 008U and the
sheafification adjunction for modules, restricted to sheaves of `O`-modules. -/
noncomputable def inverseImageModulesAdjunction :
    inverseImageModules f O ⊣ directImageModules f O :=
  haveI := isLocallyInjective_toInverseImageRing f O
  haveI := isLocallySurjective_toInverseImageRing f O
  Adjunction.restrictFullyFaithful (iC := SheafOfModules.forget O) (iD := 𝟭 _)
    ((pullbackModuleAdjunction f O.obj).comp
      (PresheafOfModules.sheafificationAdjunction (R := inverseImageRingSheaf f O)
        (toInverseImageRing f O)))
    (SheafOfModules.fullyFaithfulForget O) (Functor.FullyFaithful.id _) (Iso.refl _)
    (Iso.refl _)

/-- **Stacks Tag 008Y.**

Let `f : X ⟶ Y` be a continuous map of topological spaces, `O` a sheaf of rings on `Y`,
`G` a sheaf of `O`-modules and `F` a sheaf of `f⁻¹O`-modules. Then
`Mor_{Mod(f⁻¹O)}(f⁻¹G, F) ≃ Mor_{Mod(O)}(G, f_*F)`, where `f⁻¹G` is the inverse image with its
`f⁻¹O`-module structure of Tag 008X (`inverseImageSheafOfModules`), and `f_*F` is an
`O`-module by restriction of scalars along `O ⟶ f_*f⁻¹O`. The bijection is the hom-set
bijection of `inverseImageModulesAdjunction`, hence natural in `G` and `F`. -/
@[stacks 008Y "hom-set bijection of `inverseImageModulesAdjunction`, inverse image of 008X"]
noncomputable def inverseImageModulesHomEquiv (G : SheafOfModules.{u} O)
    (F : SheafOfModules.{u} (inverseImageRingSheaf f O)) :
    (@Quiver.Hom (SheafOfModules.{u} (inverseImageRingSheaf f O)) _
        (inverseImageSheafOfModules f O G) F) ≃
      (G ⟶ (directImageModules f O).obj F) :=
  (inverseImageModulesAdjunction f O).homEquiv G F

end InverseImageModules
