module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.EtaleSiteStalkFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.ConstantSheafOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FiniteClosedPointsSubscheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.IntegralHomCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.SepClosedPointModuleCohomologyVanishing

/-!
# The cohomology of a constructible sheaf along a finite set of closed points

Let `X` be a scheme of a big étale site, `k` an algebraically closed field, `T` a finite set of
closed points of `X` whose residue fields are identified with `k`, and `ℱ` a constructible sheaf
of `Λ`-modules on `X_étale` for a Noetherian ring `Λ`. Write `i : Z ⟶ X` for the closed
immersion of `Stacks.EtaleCohomology.TorsionModules.pointsSchemeHom`, whose source is the
disjoint union of one copy of `Spec k` for each point of `T`. This file computes the étale
cohomology of `i_*i^{-1}ℱ`: it vanishes in positive degree, and in degree zero it is a finite
`Λ`-module.

Both come from the collapse of
`Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology_isIntegralHom_iso` along the
integral morphisms `Z ⟶ X` and `Z ⟶ Spec k`. The vanishing is then the vanishing over a
separably closed field. In degree zero the collapse leaves the module of global sections on `Z`,
which the sheaf condition for the covering of `Z` by its components turns into the product of
the sections over them; and the sections over a component are the stalk of `ℱ` at the geometric
point of `X` that the component is, finite because `ℱ` is constructible.

## Main definitions

* `Stacks.EtaleCohomology.TorsionModules.pointEtaleObj` — a component of `Z`, as an object of
  the small étale site of `Z`.
* `Stacks.EtaleCohomology.TorsionModules.pointEtaleπ` — its structure morphism to the terminal
  object of that site.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.isLimitFanPointSections` — the sections of a sheaf over
  `Z` are the product of its sections over the components.
* `Stacks.EtaleCohomology.TorsionModules.finite_sections_pointEtaleObj` — the sections of
  `i^{-1}ℱ` over a component are a finite `Λ`-module.
* `Stacks.EtaleCohomology.TorsionModules.finite_moduleEtaleCohomology_zero_pointsDirectImage` —
  `H^0_étale(X, i_*i^{-1}ℱ)` is a finite `Λ`-module.
* `Stacks.EtaleCohomology.TorsionModules.isZero_moduleEtaleCohomology_succ_pointsDirectImage` —
  `H^q_étale(X, i_*A) = 0` for every `q > 0` and every sheaf `A` of `Λ`-modules on `Z_étale`.

## Implementation notes

The identification of the sections over a component with a stalk of `ℱ` is a chain of four
comparisons already in the tree: evaluation at the terminal object of the small étale site of
`Spec k` is global sections there; global sections over a separably closed field is the fibre at
the canonical point
(`Stacks.EtaleCohomology.TorsionModules.sheafFiberIdIsoGammaModule`); the inverse image along an
étale morphism is restriction
(`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso`); and a fibre of an
inverse image is the fibre at the composed point
(`Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso`), applied once for the
component inclusion and once for `i`.

The coefficient universe is `ModuleCat.{max (u + 1) r} Λ` for `Λ : Type r`, the universe of
`Stacks.EtaleCohomology.EtaleModules` and of the module-coefficient localization sequence.

## References

Assembled for use in [Stacks Project, Tag 0GJE](https://stacks.math.columbia.edu/tag/0GJE); not
itself a cited tag.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

section Fan

variable (k : Type u) [Field k] {X : Scheme.{u}} (T : Set X)
  (e : ∀ z : T, X.residueField z.1 ≅ CommRingCat.of k)
  (Λ : Type r) [CommRing Λ]

/-- The component `Spec k` of `Z = ∐_{z ∈ T} Spec k`, as an object of the small étale site of
`Z`, in the shape in which the restriction functor along the component inclusion produces it. -/
abbrev pointEtaleObj (z : T) : (pointsScheme k T).Etale :=
  (Scheme.Etale.smallEtaleCompose
      (Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z)).obj
    (Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of k))))

/-- The structure morphism of the component, as a morphism of the small étale site of `Z` to its
terminal object. -/
def pointEtaleπ (z : T) :
    pointEtaleObj k T z ⟶ Scheme.Etale.mk (𝟙 (pointsScheme k T)) :=
  MorphismProperty.Over.homMk (Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z)
    (by
      change Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z ≫ 𝟙 (pointsScheme k T) =
        𝟙 (Spec (CommRingCat.of k)) ≫ Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z
      simp) (by trivial)

/-- **The sections of a sheaf over `Z` are the product of its sections over the components.** -/
def isLimitFanPointSections
    (A : Sheaf (pointsScheme k T).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :
    IsLimit (Fan.mk (A.obj.obj (op (Scheme.Etale.mk (𝟙 (pointsScheme k T)))))
      fun z : T ↦ A.obj.map (pointEtaleπ k T z).op) :=
  Scheme.Etale.isLimitFanSectionsOfIsoSigma A (pointEtaleπ k T) (Iso.refl _)
    (fun z ↦ by
      change Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z ≫ 𝟙 (pointsScheme k T) =
        Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z
      simp)

/-- **A module which is the vertex of a limit fan over finitely many finite modules is
finite.** -/
theorem finite_of_isLimitFan {ι : Type u} [Finite ι] {M : ModuleCat.{max (u + 1) r} Λ}
    {N : ι → ModuleCat.{max (u + 1) r} Λ} {p : ∀ i, M ⟶ N i} (h : IsLimit (Fan.mk M p))
    (hfin : ∀ i, Module.Finite Λ (N i)) : Module.Finite Λ M := by
  have : ∀ i, Module.Finite Λ (N i) := hfin
  have hiso : ModuleCat.of Λ (∀ i, N i) ≅ M :=
    (IsLimit.conePointUniqueUpToIso h
      (ModuleCat.productConeIsLimit.{r, u, max (u + 1) r} N)).symm
  exact Module.Finite.equiv hiso.toLinearEquiv

end Fan

section Constructible

variable (B : BigEtaleSite.{u}) (𝔛 : B.Scheme) (k : Type u) [Field k] [IsAlgClosed k]
  (T : Set 𝔛.obj) (e : ∀ z : T, 𝔛.obj.residueField z.1 ≅ CommRingCat.of k)
  (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  (ℱ : Sheaf 𝔛.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))

/-- **The sections over one component of `Z` of the inverse image of a constructible sheaf are a
finite `Λ`-module**: they are the stalk of the sheaf at the geometric point of `X` that the
component is. -/
theorem finite_sections_pointEtaleObj
    (hℱ : IsConstructibleEtaleSiteModuleSheaf B 𝔛 Λ ℱ) (z : T) :
    Module.Finite Λ
      (((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ
          (pointsSchemeHom k T e)).obj ℱ).obj.obj (op (pointEtaleObj k T z))) := by
  set i := pointsSchemeHom k T e with hi
  set ι := Sigma.ι (fun _ : T ↦ Spec (CommRingCat.of k)) z with hιdef
  set A := (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ i).obj ℱ
    with hA
  -- the stalk of `ℱ` at the geometric point which the component is, is finite
  have h9 : Module.Finite Λ
      (((Scheme.pointSmallEtale (pointHom k T e z)).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj ℱ) :=
    finite_sheafFiber_ulift_of_isConstructibleEtaleSiteModuleSheaf B 𝔛 Λ ℱ hℱ
      { residueField := k, hom := pointHom k T e z }
  rw [← ι_pointsSchemeHom k T e z] at h9
  -- move the stalk across the inverse image along `i`
  have h7 : Module.Finite Λ
      (((Scheme.pointSmallEtale ι).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj A) :=
    have := h9
    Module.Finite.equiv
      ((Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso.{u, r}
        Λ i ι).app ℱ).symm.toLinearEquiv
  rw [show ι = 𝟙 (Spec (CommRingCat.of k)) ≫ ι from (Category.id_comp ι).symm] at h7
  -- move the stalk across the inverse image along the component inclusion
  have h5 : Module.Finite Λ
      (((Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of k)))).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj
          ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r}
            Λ ι).obj A)) :=
    have := h7
    Module.Finite.equiv
      ((Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso.{u, r}
        Λ ι (𝟙 (Spec (CommRingCat.of k)))).app A).toLinearEquiv.symm
  -- the inverse image along an étale morphism is restriction
  have h4 : Module.Finite Λ
      (((Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of k)))).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj
          ((Stacks.EtaleCohomology.etaleModuleRestriction.{u, r} Λ ι).obj A)) :=
    have := h5
    Module.Finite.equiv
      ((((Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of k)))).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ))).mapIso
        ((Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso.{u, r}
          Λ ι).app A)).toLinearEquiv
  -- the stalk at the canonical point of `Spec k` is global sections
  have h3 : Module.Finite Λ
      ((Sheaf.Γ (Scheme.smallEtaleTopology (Spec (CommRingCat.of k)))
        (ModuleCat.{max (u + 1) r} Λ)).obj
          ((Stacks.EtaleCohomology.etaleModuleRestriction.{u, r} Λ ι).obj A)) :=
    have := h4
    Module.Finite.equiv
      (((sheafFiberIdIsoGammaModule.{u, r} Λ k).app
        ((Stacks.EtaleCohomology.etaleModuleRestriction.{u, r} Λ ι).obj A)).toLinearEquiv)
  -- and global sections is evaluation at the terminal object
  have := h3
  exact Module.Finite.equiv
    (((Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology (Spec (CommRingCat.of k)))
      (ModuleCat.{max (u + 1) r} Λ) (isTerminalEtaleMkId (Spec (CommRingCat.of k)))).app
        ((Stacks.EtaleCohomology.etaleModuleRestriction.{u, r} Λ ι).obj A)).toLinearEquiv)

variable (hT : T.Finite) (hcl : ∀ z : T, IsClosed ({z.1} : Set 𝔛.obj))

include hT hcl in
/-- **The degree-zero étale cohomology of the direct image from the closed fibre is a finite
`Λ`-module.** It is the module of global sections on `Z`, which is the product over the finitely
many points of the stalks of the constructible sheaf there. -/
theorem finite_moduleEtaleCohomology_zero_pointsDirectImage
    (hℱ : IsConstructibleEtaleSiteModuleSheaf B 𝔛 Λ ℱ) :
    Module.Finite Λ
      ((moduleEtaleCohomology.{u, r, r} Λ 𝔛.obj 0).obj
        ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ
            (pointsSchemeHom k T e)).obj
          ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ
            (pointsSchemeHom k T e)).obj ℱ))) := by
  have : Finite T := hT
  have : IsClosedImmersion (pointsSchemeHom k T e) :=
    isClosedImmersion_pointsSchemeHom k T e hT hcl
  set A := (Stacks.EtaleCohomology.etaleModuleInverseImage.{u, r} Λ
    (pointsSchemeHom k T e)).obj ℱ with hA
  have hfan : Module.Finite Λ (A.obj.obj (op (Scheme.Etale.mk (𝟙 (pointsScheme k T))))) :=
    finite_of_isLimitFan Λ (isLimitFanPointSections k T Λ A)
      (fun z ↦ finite_sections_pointEtaleObj B 𝔛 k T e Λ ℱ hℱ z)
  have hΓ : Module.Finite Λ
      ((Sheaf.Γ (pointsScheme k T).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj A) := by
    have := hfan
    have hiso : A.obj.obj (op (Scheme.Etale.mk (𝟙 (pointsScheme k T)))) ≅
        (Sheaf.Γ (pointsScheme k T).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj A :=
      ((Sheaf.ΓNatIsoSheafSections (pointsScheme k T).smallEtaleTopology
        (ModuleCat.{max (u + 1) r} Λ) (isTerminalEtaleMkId (pointsScheme k T))).app A).symm
    exact Module.Finite.equiv hiso.toLinearEquiv
  have hzero : Module.Finite Λ
      ((moduleEtaleCohomology.{u, r, r} Λ (pointsScheme k T) 0).obj A) :=
    have := hΓ
    Module.Finite.equiv
      (((Sheaf.Γ (pointsScheme k T).smallEtaleTopology
        (ModuleCat.{max (u + 1) r} Λ)).rightDerivedZeroIsoSelf.app A).symm.toLinearEquiv)
  have := hzero
  have hcollapse : (moduleEtaleCohomology.{u, r, r} Λ (pointsScheme k T) 0).obj A ≅
      (moduleEtaleCohomology.{u, r, r} Λ 𝔛.obj 0).obj
        ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ
          (pointsSchemeHom k T e)).obj A) :=
    moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ (pointsSchemeHom k T e) 0 A
  exact Module.Finite.equiv hcollapse.toLinearEquiv

omit [IsNoetherianRing Λ] in
include hT hcl in
/-- **The positive-degree étale cohomology of a direct image from the closed fibre vanishes.**
`Z` is finite over the algebraically closed field `k`, so the cohomology on `X` of a direct
image from `Z` is the cohomology on `Spec k` of a sheaf of `Λ`-modules, and that vanishes in
positive degree. -/
theorem isZero_moduleEtaleCohomology_succ_pointsDirectImage
    (A : Sheaf (pointsScheme k T).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) (n : ℕ) :
    IsZero ((moduleEtaleCohomology.{u, r, r} Λ 𝔛.obj (n + 1)).obj
      ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ
        (pointsSchemeHom k T e)).obj A)) := by
  have : Finite T := hT
  have : IsClosedImmersion (pointsSchemeHom k T e) :=
    isClosedImmersion_pointsSchemeHom k T e hT hcl
  have : IsIntegralHom (pointsSchemeToSpec k T) := isIntegralHom_pointsSchemeToSpec k T hT
  have hspec := isZero_moduleEtaleCohomology_succ_sepClosedField.{u, r} Λ k
    ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ
      (pointsSchemeToSpec k T)).obj A) n
  have hZ : IsZero
      ((moduleEtaleCohomology.{u, r, r} Λ (pointsScheme k T) (n + 1)).obj A) :=
    hspec.of_iso
      (moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ (pointsSchemeToSpec k T) (n + 1) A)
  have hcollapse : (moduleEtaleCohomology.{u, r, r} Λ (pointsScheme k T) (n + 1)).obj A ≅
      (moduleEtaleCohomology.{u, r, r} Λ 𝔛.obj (n + 1)).obj
        ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ
          (pointsSchemeHom k T e)).obj A) :=
    moduleEtaleCohomology_isIntegralHom_iso.{u, r} Λ (pointsSchemeHom k T e) (n + 1) A
  exact hZ.of_iso hcollapse.symm

end Constructible

end Stacks.EtaleCohomology.TorsionModules

end
