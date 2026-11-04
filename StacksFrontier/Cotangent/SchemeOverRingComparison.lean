module

public import StacksFrontier.Cotangent.Localization
public import StacksFrontier.Cotangent.SchemeOverRing
public import StacksFrontier.Cotangent.SheavesOfRings.StalkwiseChangeOfBase
public import StacksFrontier.Topology.Sheaves.Stalk.PullbackUnit
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent complex of a scheme over a ring is computed over the constant sheaf

Let `Λ` be a ring and let `X` be a scheme over `Λ` with structure morphism
`p : X ⟶ Spec Λ`. **Tag 08V6** asserts `L_{X/Spec Λ} = L_{𝒪_X/Λ̲}` in `D(𝒪_X)`, where `Λ̲` is the
constant sheaf with value `Λ`. This file proves it: the canonical comparison
`AlgebraicGeometry.SchemeOverRing.constantComparison` `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}` of
`StacksFrontier.Cotangent.SchemeOverRing` — the change-of-base map of the tower
`Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` — is a quasi-isomorphism, hence an isomorphism in `D(𝒪_X)`.

## The proof

The source reduces the tag to `L_q = 0` for `q : Spec Λ → (*, Λ)`, which it checks on stalks:
`(L_q)_𝔭 = L_{Λ_𝔭/Λ}` by Tag 08T0, and this vanishes by Tag 08R2. The same stalk computation is
used here, applied directly to the comparison map:
`CategoryTheory.Sheaf.quasiIso_towerCotangentChangeOfBase_of_isZero_stalk` says that the
change-of-base map `L_{𝒪_X/Λ̲} ⟶ L_{𝒪_X/p⁻¹𝒪}` is a quasi-isomorphism as soon as, at every point
`x`, the cotangent complex of the map of stalks `Λ̲_x → (p⁻¹𝒪_{Spec Λ})_x` vanishes. That map is a
localization:

* `Λ → Λ̲_x` is bijective (`AlgebraicGeometry.SchemeOverRing.bijective_constantStalkMap`): the
  stalk of the constant sheaf is the stalk of the constant presheaf;
* `Λ → (p⁻¹𝒪_{Spec Λ})_x` is the localization at the prime `p(x)`
  (`AlgebraicGeometry.SchemeOverRing.isLocalization_pullbackStalkMap`): the stalk of the inverse
  image at `x` is the stalk `𝒪_{Spec Λ, p(x)} = Λ_{p(x)}`;
* the two are compatible (`AlgebraicGeometry.SchemeOverRing.constantStalkMap_comp`), because
  `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ}` is named by the ring map `Λ → Γ(X, p⁻¹𝒪_{Spec Λ})` on global sections.

So `L_{(p⁻¹𝒪)_x/Λ̲_x} = L_{Λ_{p(x)}/Λ} = 0` by item (3) of Tag 08R2
(`CommAlgCat.isZero_cotangentComplexDerived_localization`).

## Main results

* `AlgebraicGeometry.SchemeOverRing.isZero_cotangentComplexDerived_stalk`: the cotangent complex
  of `Λ̲_x → (p⁻¹𝒪_{Spec Λ})_x` vanishes at every point.
* `AlgebraicGeometry.SchemeOverRing.quasiIso_constantComparison`: the comparison is a
  quasi-isomorphism.
* `AlgebraicGeometry.SchemeOverRing.isIso_constantComparison`: **Tag 08V6**, the comparison is
  an isomorphism `L_{𝒪_X/Λ̲} ≅ L_{X/Spec Λ}` in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 08V6](https://stacks.math.columbia.edu/tag/08V6)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u t

namespace AlgebraicGeometry.SchemeOverRing

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of Λ))

section Stalks

attribute [local instance] HasDerivedCategory.standard

/-- The ring map `Λ → Λ̲_x`: the canonical map to the global sections of the constant sheaf
followed by the germ at `x`. -/
def constantStalkMap (x : X) :
    CommRingCat.of Λ ⟶ CategoryTheory.Sheaf.stalkRing (X := X.carrier) x (constantBaseSheaf Λ X) :=
  (constantAdjunction X).unit.app (CommRingCat.of Λ) ≫
    TopCat.Presheaf.germ (X := X.carrier) (constantBaseSheaf Λ X).obj ⊤ x trivial

/-- The canonical map `Λ → Γ(X, Λ̲)` is the sheafification map of the constant presheaf on the
whole space. -/
theorem constantAdjunction_unit_app :
    (constantAdjunction X).unit.app (CommRingCat.of Λ) =
      (toSheafify (Opens.grothendieckTopology ↥X)
        ((Functor.const _).obj (CommRingCat.of Λ))).app (op ⊤) := by
  simp [constantAdjunction, constantSheafAdj, Adjunction.comp_unit_app]
  rfl

/-- The germ at `x` of the constant presheaf with value `Λ` is bijective on global sections. -/
theorem bijective_germ_const (x : X) :
    Function.Bijective (TopCat.Presheaf.germ (X := X.carrier)
      ((Functor.const (Opens ↥X)ᵒᵖ).obj (CommRingCat.of Λ)) ⊤ x trivial) := by
  let P : (Opens ↥X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const _).obj (CommRingCat.of Λ)
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · obtain ⟨W, _, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (X := X.carrier) P (U := ⊤) (V := ⊤) x
      trivial trivial a b hab
    exact e
  · obtain ⟨U, hU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (X := X.carrier) P t
    exact ⟨a, (TopCat.Presheaf.germ_res_apply (X := X.carrier) P (homOfLE le_top) x hU a).symm⟩

/-- The stalk of the constant sheaf `Λ̲` at any point is `Λ`. -/
theorem bijective_constantStalkMap (x : X) : Function.Bijective (constantStalkMap Λ x) := by
  let P : (Opens ↥X)ᵒᵖ ⥤ CommRingCat.{u} := (Functor.const _).obj (CommRingCat.of Λ)
  have hfac : constantStalkMap Λ x = TopCat.Presheaf.germ (X := X.carrier) P ⊤ x trivial ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology ↥X) P) :=
    (congrArg (fun t => t ≫ TopCat.Presheaf.germ (X := X.carrier) (constantBaseSheaf Λ X).obj
      ⊤ x trivial) (constantAdjunction_unit_app Λ)).trans
      (TopCat.Presheaf.stalkFunctor_map_germ (X := X.carrier) (⊤ : Opens ↥X) x trivial
        (toSheafify (Opens.grothendieckTopology ↥X) P)).symm
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (X := X.carrier) x
    CommRingCat.{u} P
  have hcoe : ⇑(ConcreteCategory.hom (constantStalkMap Λ x)) =
      ⇑(ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology ↥X) P))) ∘
      ⇑(ConcreteCategory.hom (TopCat.Presheaf.germ (X := X.carrier) P ⊤ x trivial)) := by
    rw [hfac]
    ext a
    exact ConcreteCategory.comp_apply _ _ a
  rw [hcoe]
  exact (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
    (toSheafify (Opens.grothendieckTopology ↥X) P))).comp (bijective_germ_const Λ x)

/-- The ring map `Λ → (p⁻¹𝒪_{Spec Λ})_x`: the canonical map to global sections followed by the
germ at `x`. -/
def pullbackStalkMap (x : X) :
    CommRingCat.of Λ ⟶
      CategoryTheory.Sheaf.stalkRing (X := X.carrier) x (pullbackStructureSheaf Λ p) :=
  pullbackUnitTop Λ p ≫ TopCat.Presheaf.germ (X := X.carrier) (pullbackStructureSheaf Λ p).obj ⊤ x
    trivial

/-- The comparison `𝒪_{Spec Λ, p(x)} ⟶ (p⁻¹𝒪_{Spec Λ})_x` of stalks, an isomorphism. -/
abbrev pullbackStalkComparison (x : X) :=
  Stacks.Sheaves.PullbackUnit.stalkComparison (structureRingedSpaceHom Λ p).hom.base
    CommRingCat.{u}
    ((Stacks.Sheaves.RingedSpaceDifferentials.sheafAdjunction
      (structureRingedSpaceHom Λ p)).unit.app (Spec (CommRingCat.of Λ)).toRingedSpace.sheaf).hom x

/-- The comparison of stalks is compatible with the maps from `Λ`. -/
theorem toStalk_comp_pullbackStalkComparison (x : X) :
    StructureSheaf.toStalk Λ ((structureRingedSpaceHom Λ p).hom.base x) ≫
      pullbackStalkComparison Λ p x = pullbackStalkMap Λ p x :=
  (Category.assoc _ _ _).trans (congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ t)
    (Stacks.Sheaves.PullbackUnit.germ_stalkComparison (structureRingedSpaceHom Λ p).hom.base
      CommRingCat.{u} _ x ⊤ trivial))

/-- The map `Λ̲_x → (p⁻¹𝒪_{Spec Λ})_x` of stalks is compatible with the maps from `Λ`. -/
theorem constantStalkMap_comp (x : X) :
    constantStalkMap Λ x ≫
        CategoryTheory.Sheaf.stalkMap (X := X.carrier) (constantToPullback Λ p) x =
      pullbackStalkMap Λ p x := by
  have h₁ : (constantAdjunction X).unit.app (CommRingCat.of Λ) ≫
      (constantToPullback Λ p).hom.app (op ⊤) = pullbackUnitTop Λ p := by
    have := (constantAdjunction X).homEquiv_unit (CommRingCat.of Λ) (pullbackStructureSheaf Λ p)
      (constantToPullback Λ p)
    rw [constantToPullback, Equiv.apply_symm_apply] at this
    exact this.symm
  exact (Category.assoc _ _ _).trans ((congrArg (fun t => (constantAdjunction X).unit.app
    (CommRingCat.of Λ) ≫ t) (TopCat.Presheaf.stalkFunctor_map_germ (X := X.carrier) (⊤ : Opens ↥X)
      x trivial (constantToPullback Λ p).hom)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ _) h₁)))

/-- The point `p(x)` of `Spec Λ`, as a prime of `Λ`. -/
abbrev imagePrime (x : X) : PrimeSpectrum Λ := (structureRingedSpaceHom Λ p).hom.base x

/-- The stalk of `p⁻¹𝒪_{Spec Λ}` at `x` is the localization `Λ_{p(x)}`. -/
theorem isLocalization_pullbackStalkMap (x : X) :
    letI := (pullbackStalkMap Λ p x).hom.toAlgebra
    IsLocalization.AtPrime (CategoryTheory.Sheaf.stalkRing (X := X.carrier) x
      (pullbackStructureSheaf Λ p)) (imagePrime Λ p x).asIdeal := by
  let := (pullbackStalkMap Λ p x).hom.toAlgebra
  let : Algebra Λ ((Spec.structureSheaf Λ).presheaf.stalk (imagePrime Λ p x)) :=
    StructureSheaf.stalkAlgebra Λ (imagePrime Λ p x)
  have : IsLocalization.AtPrime ((Spec.structureSheaf Λ).presheaf.stalk (imagePrime Λ p x))
      (imagePrime Λ p x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk Λ (imagePrime Λ p x)
  have hiso := Stacks.Sheaves.PullbackUnit.isIso_stalkComparison
    (structureRingedSpaceHom Λ p).hom.base (Spec (CommRingCat.of Λ)).toRingedSpace.sheaf x
  let e : (Spec.structureSheaf Λ).presheaf.stalk (imagePrime Λ p x) ≃+*
      CategoryTheory.Sheaf.stalkRing (X := X.carrier) x (pullbackStructureSheaf Λ p) :=
    (@asIso _ _ _ _ (pullbackStalkComparison Λ p x) hiso).commRingCatIsoToRingEquiv
  let e' : (Spec.structureSheaf Λ).presheaf.stalk (imagePrime Λ p x) ≃ₐ[Λ]
      CategoryTheory.Sheaf.stalkRing (X := X.carrier) x (pullbackStructureSheaf Λ p) :=
    AlgEquiv.ofRingEquiv (f := e) (fun r =>
      ConcreteCategory.congr_hom (toStalk_comp_pullbackStalkComparison Λ p x) r)
  exact IsLocalization.isLocalization_of_algEquiv (imagePrime Λ p x).asIdeal.primeCompl e'

/-- The cotangent complex of the map of stalks `Λ̲_x → (p⁻¹𝒪_{Spec Λ})_x` vanishes: this map is a
localization, by `bijective_constantStalkMap` and `isLocalization_pullbackStalkMap`, so
Tag 08R2 (3) applies. -/
theorem isZero_cotangentComplexDerived_stalk (x : X) :
    IsZero (CommAlgCat.cotangentComplexDerived.{u, u}
      (CategoryTheory.Sheaf.stalkRing (X := X.carrier) x (constantBaseSheaf Λ X))
      (CategoryTheory.Sheaf.stalkAlgebra (X := X.carrier) (constantToPullback Λ p) x)) := by
  let := (pullbackStalkMap Λ p x).hom.toAlgebra
  have := isLocalization_pullbackStalkMap Λ p x
  let ε := RingEquiv.ofBijective (constantStalkMap Λ x).hom (bijective_constantStalkMap Λ x)
  have hloc := IsLocalization.isLocalization_of_base_ringEquiv
    (imagePrime Λ p x).asIdeal.primeCompl
    (CategoryTheory.Sheaf.stalkRing (X := X.carrier) x (pullbackStructureSheaf Λ p)) ε
  have key : (algebraMap Λ (CategoryTheory.Sheaf.stalkRing (X := X.carrier) x
      (pullbackStructureSheaf Λ p))).comp ε.symm.toRingHom =
      (CategoryTheory.Sheaf.stalkMap (X := X.carrier) (constantToPullback Λ p) x).hom := by
    ext a
    obtain ⟨b, rfl⟩ := ε.surjective a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    exact (ConcreteCategory.congr_hom (constantStalkMap_comp Λ p x) b).symm
  rw [key] at hloc
  let := (CategoryTheory.Sheaf.stalkMap (X := X.carrier) (constantToPullback Λ p) x).hom.toAlgebra
  have := hloc
  exact CommAlgCat.isZero_cotangentComplexDerived_localization _
    ((imagePrime Λ p x).asIdeal.primeCompl.map ε) _

/-- The canonical comparison `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}` is a quasi-isomorphism of complexes of
sheaves of `𝒪_X`-modules. -/
theorem quasiIso_constantComparison : QuasiIso (constantComparison Λ p) :=
  CategoryTheory.Sheaf.quasiIso_towerCotangentChangeOfBase_of_isZero_stalk (X := X.carrier)
    (constantToPullback Λ p) (pullbackStructureMap Λ p) (isZero_cotangentComplexDerived_stalk Λ p)

end Stalks

/-- **Stacks Project, Tag 08V6.** Let `Λ` be a ring and let `X` be a scheme over `Λ`. Then
`L_{X/Spec Λ} = L_{𝒪_X/Λ̲}` in `D(𝒪_X)`, where `Λ̲` is the constant sheaf with value `Λ` on `X`:
the canonical comparison `L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ}`, the change-of-base map of the tower
`Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`, is an isomorphism in the derived category. -/
@[stacks 08V6 "L_{X/Spec Lambda} = L_{O_X/const Lambda} in D(O_X) for a scheme X over a ring \
  Lambda, const Lambda the constant sheaf with value Lambda on X: the canonical comparison \
  L_{O_X/const Lambda} ⟶ L_{X/Spec Lambda} (constantComparison) is an isomorphism in D(O_X)"]
theorem isIso_constantComparison
    [HasDerivedCategory.{t} (CategoryTheory.Sheaf.targetModules.{u, u, u}
      (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))] :
    IsIso ((DerivedCategory.Q (C := CategoryTheory.Sheaf.targetModules.{u, u, u}
      (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))).map (constantComparison Λ p)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_constantComparison Λ p)

end AlgebraicGeometry.SchemeOverRing
