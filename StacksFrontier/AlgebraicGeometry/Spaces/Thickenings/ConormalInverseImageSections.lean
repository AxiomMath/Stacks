module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalModuleInverseImageKernel

/-!
# The inclusion of the conormal module on the classes of ideal sections

Let `Z ⊆ X` be a first-order thickening of algebraic spaces, with inclusion `i : Z ⟶ X`. A global
section `s` of the defining ideal `𝓘` of `Z` has a class `i^*s` in the conormal module
`𝒞_{Z/X} = i^*𝓘`. This file computes the inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X`
(`AlgebraicGeometry.Space.conormalInverseImageι`) on that class: it is the function `s` of `𝒪_X`,
read in `i^{-1}𝒪_X`. The statement is made after the direct image along `i`, which is fully
faithful (Stacks 04E5): there the class of `s`, composed with the inclusion, is `s` followed by
`𝓘 ⊆ 𝒪_X ≅ i_*i^{-1}𝒪_X`.

## Main definitions

* `Space.thickeningUnitTransportIso`: `𝒪_X ≅ i_*i^{-1}𝒪_X` for a thickening.

## Main results

* `Space.homEquiv_modulePullbackUnitIso_hom_comp_map_modulePullbackGlobalSection`:
  the class of `s`, pushed forward, is `s` followed by `𝓘 ≅ i_*𝒞_{Z/X}`.
* `Space.thickeningTransport_map_conormalInverseImageι_modulePullbackGlobalSection`:
  the inclusion on the class of `s` is `s`.

## References

* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

/-- Given `τ : R ⋙ T ≅ P`, if `H ≫ P.map κ = s ≫ φ.hom` and `T.map ι = μ.inv ≫ j ≫ u` with
`μ = φ ≪≫ (τ.app C).symm`, then `H ≫ τ.inv.app UZ ≫ T.map (R.map κ) ≫ T.map ι = s ≫ j ≫ u`.

The diagram chase is stated for abstract categories so that it is checked without unfolding the
concrete functors. -/
theorem comp_transport_map_comp_of_map_eq {𝒳 𝒵 𝒴 : Type*} [Category 𝒳] [Category 𝒵] [Category 𝒴]
    {P : 𝒵 ⥤ 𝒳} {R : 𝒵 ⥤ 𝒴} {T : 𝒴 ⥤ 𝒳} (τ : R ⋙ T ≅ P) {UX I : 𝒳} {UZ C : 𝒵} {UY : 𝒴}
    (H : UX ⟶ P.obj UZ) (κ : UZ ⟶ C) (ι : R.obj C ⟶ UY) (s : UX ⟶ I) (j : I ⟶ UX)
    (u : UX ⟶ T.obj UY) (φ : I ≅ P.obj C) (μ : I ≅ T.obj (R.obj C))
    (hμ : μ = φ ≪≫ (τ.app C).symm) (hι : T.map ι = μ.inv ≫ j ≫ u)
    (hp : H ≫ P.map κ = s ≫ φ.hom) :
    H ≫ τ.inv.app UZ ≫ T.map (R.map κ) ≫ T.map ι = s ≫ j ≫ u := by
  have hn := τ.inv.naturality κ
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  subst hμ
  rw [hι, reassoc_of% hn.symm]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hp, Iso.hom_inv_id_assoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- **The class of an ideal section, through the direct image of `i^*` and of `i^*𝓘 ⊆ 𝒪_X`**:
for a global section `s` of the defining ideal `𝓘` of a first-order thickening, the structure map
`𝒪_X ⟶ i_*𝒪_Z` followed by the direct image of the class `i^*s` is `s` followed by the unit
`𝓘 ≅ i_*𝒞_{Z/X}`. -/
theorem homEquiv_modulePullbackUnitIso_hom_comp_map_modulePullbackGlobalSection
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _
          (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom ≫
        (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
          (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s) =
      s ≫ (firstOrderConormalModuleIso B S hS Z hZ).hom := by
  have h : (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom ≫
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s) =
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).map s) :=
    ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).map_comp
      (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom
      (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s)).symm.trans
      (congrArg (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        (Iso.hom_inv_id_assoc _ _))
  have e : (firstOrderConormalModuleIso B S hS Z hZ).hom =
      (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app _ :=
    submoduleUnitIsoOfEssImage_hom B S hS (subspaceInclusion B S hS X Z) Z.2.2
      (definingIdealSheaf B S hS X Z)
      (essImage_modulePushforward_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ)
  rw [Adjunction.homEquiv_unit, e]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans ?_)
  exact ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.naturality s).symm

/-- **`𝒪_X ≅ i_*i^{-1}𝒪_X`** for a thickening `i : Z ⟶ X`, in the presentation of the direct image
by `AlgebraicGeometry.Space.thickeningTransport`: the module form of the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X`, an isomorphism of sheaves of rings for a thickening. -/
def thickeningUnitTransportIso (hZ : IsThickening B S hS X Z.1) :=
  @Stacks.SheafOfModules.IdealTransport.unitTransportIso _ _ _ _ (SmallEtale.topology B S hS X.1)
    _ _ _ (thickeningToposHom B S hS Z).pushforward _ _ _ (thickeningRingUnit B S hS Z)
    (isIso_thickeningRingUnit B S hS Z hZ)

/-- **The inclusion `𝒞_{Z/X} ⟶ i^{-1}𝒪_X` on the class of an ideal section is the section
itself.** For a global section `s` of the defining ideal `𝓘` of a first-order thickening
`i : Z ⟶ X`, the class `i^*s` of `s` in the conormal module, followed by
`AlgebraicGeometry.Space.conormalInverseImageι`, is `s` read in `i^{-1}𝒪_X`: after the (fully
faithful) direct image along `i`, precomposed with the structure map `𝒪_X ⟶ i_*𝒪_Z` (the adjunct of
`i^*𝒪_X ≅ 𝒪_Z`, `AlgebraicGeometry.Space.homEquiv_modulePullbackUnitIso_hom`), it is `s`
followed by the inclusion `𝓘 ⊆ 𝒪_X` and the identification `𝒪_X ≅ i_*i^{-1}𝒪_X`. -/
theorem thickeningTransport_map_conormalInverseImageι_modulePullbackGlobalSection
    (hZ : IsFirstOrderThickening B S hS X Z.1)
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
      (definingIdealSheaf B S hS X Z).toSheafOfModules) :
    (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _
          (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom ≫
        (thickeningTransportIso B S hS Z).inv.app _ ≫
        (thickeningTransport B S hS Z).map
          ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))).map
            (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s)) ≫
        (thickeningTransport B S hS Z).map (conormalInverseImageι B S hS Z hZ) =
      s ≫ (definingIdealSheaf B S hS X Z).ι ≫ (thickeningUnitTransportIso B S hS Z hZ.1).hom := by
  have hι : (thickeningTransport B S hS Z).map (conormalInverseImageι B S hS Z hZ) =
      (conormalDirectImageIso B S hS Z hZ).inv ≫ (definingIdealSheaf B S hS X Z).ι ≫
        (thickeningUnitTransportIso B S hS Z hZ.1).hom :=
    Stacks.SheafOfModules.IdealTransport.map_idealι
      (hηiso := isIso_thickeningRingUnit B S hS Z hZ.1)
      (SmallEtale.topology B S hS X.1) (thickeningToposHom B S hS Z).pushforward
      (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS X Z))
      (thickeningRingUnit B S hS Z) (structureSharp B S hS (subspaceInclusion B S hS X Z))
      (conormalDirectImageIso B S hS Z hZ)
  exact comp_transport_map_comp_of_map_eq (thickeningTransportIso B S hS Z)
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv _ _
      (modulePullbackUnitIso B S hS (subspaceInclusion B S hS X Z)).hom)
    (modulePullbackGlobalSection B S hS (subspaceInclusion B S hS X Z) s)
    (conormalInverseImageι B S hS Z hZ) s (definingIdealSheaf B S hS X Z).ι
    (thickeningUnitTransportIso B S hS Z hZ.1).hom
    (firstOrderConormalModuleIso B S hS Z hZ) (conormalDirectImageIso B S hS Z hZ) rfl hι
    (homEquiv_modulePullbackUnitIso_hom_comp_map_modulePullbackGlobalSection B S hS Z hZ s)

end AlgebraicGeometry.Space

end
