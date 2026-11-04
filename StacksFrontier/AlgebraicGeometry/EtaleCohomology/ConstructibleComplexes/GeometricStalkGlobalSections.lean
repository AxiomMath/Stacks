module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf

/-!
# The stalk of a sheaf of modules at a geometric point as global sections of the inverse image

Let `Λ` be a ring, `Ω` a separably closed field and `x : Spec Ω ⟶ X` a geometric point. For a
sheaf `F` of `Λ`-modules on the small étale site of `X`, the stalk `F_x` is the module of global
sections of the inverse image `x⁻¹F` on `Spec Ω` ([Stacks, Tag 04JN]).

The library records this for sheaves of sets
(`Stacks.EtaleCohomology.stalkIsoInverseImageGamma`); the proof works for any coefficient
category with the relevant colimits, since it rests only on the étale neighbourhoods of the
canonical point of `Spec Ω` having an initial object. Here it is given for sheaves of modules on
Mathlib's small étale site, the model `Stacks.EtaleCohomology.EtaleModules` of the trace
formula.

## Main results

* `Stacks.EtaleCohomology.etaleModuleSheafFiberIdIsoGlobalSections` — the stalk at the canonical
  point of `Spec Ω` is global sections.
* `Stacks.EtaleCohomology.etaleModuleStalkIsoInverseImageGlobalSections` — **the stalk at a
  geometric point is the global sections of the inverse image.**

## References

* [Stacks Project, Tag 04JN](https://stacks.math.columbia.edu/tag/04JN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- **The stalk of a sheaf of modules at the canonical point of the spectrum of a separably
closed field is its module of global sections.** The étale neighbourhoods of that point have an
initial object, the final object of the site with its identity lift, so the colimit computing the
fibre of a presheaf is attained there. -/
def etaleModuleSheafFiberIdIsoGlobalSections :
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) ≅
      etaleModuleGlobalSections.{u, r} Λ (Spec (.of Ω)) := by
  let ι := (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiberNatTrans
    (A := ModuleCat.{max (u + 1) r} Λ) (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    (pointSmallEtaleIdElement Ω)
  letI : ∀ P, IsIso (ι.app P) := fun P ↦
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).isColimitPresheafFiberCocone
      P).isIso_ι_app_of_isTerminal
        (op ⟨Scheme.Etale.mk (𝟙 (Spec (.of Ω))), pointSmallEtaleIdElement Ω⟩)
        (isInitialPointSmallEtaleIdElement Ω).op
  letI := NatIso.isIso_of_isIso_app ι
  exact (Functor.isoWhiskerLeft
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
      (asIso ι)).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      (isTerminalEtaleMkId (Spec (.of Ω)))).symm

/-- **The stalk at a geometric point is the module of global sections of the inverse image**
([Stacks, Tag 04JN]): the stalk of `x⁻¹F` at the canonical point of `Spec Ω` is the stalk of `F` at
`x`, and over `Spec Ω` the stalk at the canonical point is global sections. -/
def etaleModuleStalkIsoInverseImageGlobalSections {X : Scheme.{u}} (s : GeometricPoint X) :
    (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) ≅
      etaleModuleInverseImage.{u, r} Λ s.hom ⋙
        etaleModuleGlobalSections.{u, r} Λ (Spec (.of s.residueField)) := by
  let g := s.hom
  let t : Spec (.of s.residueField) ⟶ Spec (.of s.residueField) := 𝟙 _
  let A := ModuleCat.{max (u + 1) r} Λ
  let e₁ : etaleModuleInverseImage.{u, r} Λ g ⋙
        (Scheme.pointSmallEtale t).sheafFiber (A := A) ≅
      (Scheme.pointSmallEtale (t ≫ g)).sheafFiber (A := A) :=
    ((Scheme.pointSmallEtale t).sheafFiberComapIso (smallEtaleBaseChange g)
        (coverPreserving_smallEtaleBaseChange g) A).symm ≪≫
      (GrothendieckTopology.Point.sheafFiberIsoOfFiberIso (A := A)
        (Scheme.pointSmallEtale (t ≫ g))
        ((Scheme.pointSmallEtale t).comap (smallEtaleBaseChange g)
          (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g t)).symm
  let e₂ : (Scheme.pointSmallEtale (t ≫ g)).sheafFiber (A := A) ≅
      (Scheme.pointSmallEtale g).sheafFiber (A := A) :=
    eqToIso (by rw [Category.id_comp])
  exact e₂.symm ≪≫ e₁.symm ≪≫ Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, r} Λ g)
    (etaleModuleSheafFiberIdIsoGlobalSections Λ s.residueField)

end Stacks.EtaleCohomology

end
