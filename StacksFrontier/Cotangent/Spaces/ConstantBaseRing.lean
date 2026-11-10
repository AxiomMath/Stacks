module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingGermsOnOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingChartHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral
public import StacksFrontier.Cotangent.SheavesOfRings.HenselianStalkVanishing
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceRingedTopoi
public import StacksFrontier.Cotangent.Spaces.CotangentComplex
public import StacksFrontier.Cotangent.Spaces.RepresentableStalks
public import StacksFrontier.Cotangent.TowerVanishing

/-!
# The cotangent complex of an algebraic space over a ring

Let `Λ` be a ring and let `X` be an algebraic space over `Spec Λ`, with structure morphism
`p : X ⟶ Spec Λ`. This file proves that the cotangent complex `L_{X/Spec Λ}` of Tag 08VD is the
cotangent complex of the canonical map `Λ̲ ⟶ 𝒪_X`, where `Λ̲` is the constant sheaf with value `Λ`
on the small étale site of `X` (Tag 08VG). It is first proved for the tower
`p⁻¹Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`, with `Λ̲` the constant sheaf on `Spec(Λ)_étale`, and then
transported along the identification `Λ̲_X ≅ p⁻¹Λ̲` of constant sheaves
(`AlgebraicGeometry.Space.constantSheafInverseImageIso`). The canonical map `Λ̲_X ⟶ 𝒪_X` is the
one adjoint to the structure map `Λ → Γ(X, 𝒪_X)`, and the tower composes to it
(`AlgebraicGeometry.Space.towerConstantLower_comp_towerUpper`): both maps are adjoint to that
structure map, and `Λ̲_X ≅ p⁻¹Λ̲` is the uniqueness of left adjoints of global sections.

## The proof

The source's proof is the transitivity triangle of Tag 08V1 for `X ⟶ Spec Λ ⟶ (*, Λ)` together
with `L_q = 0` for `q : Spec(Λ)_étale ⟶ (*, Λ)`. The transitivity triangle is, by its own proof,
the fundamental triangle of Tag 08SZ for the tower `p⁻¹Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` on the site of
`X`, and that is the triangle used here
(`CategoryTheory.Sheaf.exists_distTriang_towerCotangent`). Its third vertex is `L_{X/Spec Λ}`
and its middle vertex is `L_{𝒪_X/p⁻¹Λ̲}`, so it suffices that its first vertex vanishes. That is
checked at the geometric points of `X`, which form a conservative family
(`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_uliftEtaleSitePoint`): at a geometric
point `x̄` the stalk of the lower map of the tower is the stalk of `Λ̲ ⟶ 𝒪_{Spec Λ}` at the image
point (Stacks 04K2, `AlgebraicGeometry.Space.smallEtaleInverseImageFiberRingIso`), which is the
germ map `Λ → 𝒪_{Spec Λ, p(x̄)}`. That is the source's computation of `(L_q)_{t̄}`: the étale local
ring is a strict henselization of the local ring `Λ_𝔭` of `Spec Λ` (Stacks 04KF), so its
cotangent complex over `Λ` vanishes by items (3), (7) and (8) of Stacks 08R2.

## Main definitions

* `AlgebraicGeometry.Space.etaleConstantRing` and
  `AlgebraicGeometry.Space.etaleConstantStructureMap`:
  the constant sheaf of rings `Λ̲` on the small étale site of a space over `Spec Λ` and its
  structure map `Λ̲ ⟶ 𝒪`.
* `AlgebraicGeometry.Space.structureToSpec`: the structure morphism `X ⟶ Spec Λ`.
* `AlgebraicGeometry.Space.towerLower` and `AlgebraicGeometry.Space.towerUpper`: the two maps of
  the tower `p⁻¹Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X`, with sections lifted into the universe of the site.
* `AlgebraicGeometry.Space.cotangentComplexInverseImageConstantIso`:
  `L_{𝒪_X/p⁻¹Λ̲} ≅ L_{X/Spec Λ}` in `D(𝒪_X)`.
* `AlgebraicGeometry.Space.globalStructureMap` and
  `AlgebraicGeometry.Space.constantStructureMapOfSpace`: the structure map `Λ → Γ(X, 𝒪_X)` of `X`
  over `Λ`, and its adjoint, the canonical map `Λ̲ ⟶ 𝒪_X` from the constant sheaf on `X_et`.
* `AlgebraicGeometry.Space.cotangentComplexOverConstantSheafIso`:
  `L_{𝒪_X/Λ̲} ≅ L_{X/Spec Λ}` in `D(𝒪_X)`, `Λ̲` the constant sheaf on `X_et`.

## Main results

* `CategoryTheory.GrothendieckTopology.Point.bijective_toPresheafFiber_const`: the stalk of a
  constant presheaf of rings is its value.
* `AlgebraicGeometry.Space.bijective_etaleConstantGerm`: the stalk of `Λ̲` at a geometric point is
  `Λ`.
* `AlgebraicGeometry.Space.isZero_cotangentComplexDerived_specStalkMap`: `L_q = 0` at the
  geometric points of `Spec Λ`.
* `AlgebraicGeometry.Space.isCotangentAcyclicAt_towerLower`: the lower map of the tower has
  vanishing cotangent complex at every geometric point of `X`.
* `AlgebraicGeometry.Space.constantSheafInverseImageIso_hom_comp`: under `Λ̲_X ≅ p⁻¹Λ̲`, the
  canonical map `Λ̲_X ⟶ 𝒪_X` is `p⁻¹` of that of `Spec Λ` followed by `p♯`.

## Implementation notes

The sheaves of the tower are lifted into the universe of the small étale site, as the structure
sheaf is in Tag 08VD, because the cotangent complex of a homomorphism of sheaves of rings is
stated for sections in a universe containing the site. The derived category is an arbitrary
model.

## References

* [Stacks Project, Tag 08VG](https://stacks.math.columbia.edu/tag/08VG)
* [Stacks Project, Tag 08V1](https://stacks.math.columbia.edu/tag/08V1)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u t

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} [LocallySmall.{u} C]
  (Φ : J.Point.{u})

/-- **The stalk of a constant presheaf of rings is its value.** At a point of a site, the germ at
any element of the fibre of the constant presheaf with value `M` is bijective: two germs of
constant sections agree after restriction, which does nothing, and any element of the fibre is
a germ at an element which, the category of elements being cofiltered, refines the given
one. -/
theorem bijective_toPresheafFiber_const (M : CommRingCat.{u}) (T : C) (t : Φ.fiber.obj T) :
    Function.Bijective (Φ.toPresheafFiber T t ((Functor.const Cᵒᵖ).obj M)) := by
  refine ⟨fun z₁ z₂ h => ?_, fun p => ?_⟩
  · obtain ⟨Y, f, y, -, hf⟩ := (Φ.toPresheafFiber_eq_iff' T t z₁ z₂).1 h
    exact hf
  · obtain ⟨X, x, z, rfl⟩ := Φ.toPresheafFiber_jointly_surjective p
    obtain ⟨E, f, g, -⟩ :=
      IsCofilteredOrEmpty.cone_objs (Φ.fiber.elementsMk X x) (Φ.fiber.elementsMk T t)
    have hl := Φ.toPresheafFiber_w_apply f.1 E.2 ((Functor.const Cᵒᵖ).obj M) z
    have hr := Φ.toPresheafFiber_w_apply g.1 E.2 ((Functor.const Cᵒᵖ).obj M) z
    rw [f.2] at hl
    rw [g.2] at hr
    exact ⟨z, hr.symm.trans hl⟩

end CategoryTheory.GrothendieckTopology.Point

namespace CommAlgCat

open IsLocalRing

attribute [local instance] HasDerivedCategory.standard

/-- **The cotangent complex of a henselization of a localization vanishes, across a universe
lift.** Let `A_S` be a local localization of a ring `A` in `Type u`, and let `C`, in
`Type (u + 1)`, be a henselization of `A_S`. Then `L_{C/A} = 0`, with `A` lifted to the universe
of `C` and `C` an `A`-algebra through `A → A_S → C`. -/
theorem isZero_cotangentComplexDerived_ulift_henselization_localization (A : Type u)
    [CommRing A] (S : Submonoid A) (Ap : Type u) [CommRing Ap] [Algebra A Ap]
    [IsLocalization S Ap] [IsLocalRing Ap] (L : Type u) [Field L]
    [Algebra (ResidueField Ap) L] (C : Type (u + 1)) [CommRing C] [IsLocalRing C]
    [Algebra Ap C] [IsHenselization Ap L C] :
    letI : Algebra (ULift.{u + 1} A) C :=
      ((algebraMap Ap C).comp ((algebraMap A Ap).comp ULift.ringEquiv.toRingHom)).toAlgebra
    IsZero (cotangentComplexDerived.{u + 1, u + 1} (ULift.{u + 1} A)
      (CommAlgCat.of (ULift.{u + 1} A) C)) := by
  let algC : Algebra (ULift.{u + 1} A) C :=
    ((algebraMap Ap C).comp ((algebraMap A Ap).comp ULift.ringEquiv.toRingHom)).toAlgebra
  let algP : Algebra (ULift.{u + 1} A) (ULift.{u + 1} Ap) :=
    (ULift.ringEquiv.symm.toRingHom.comp
      ((algebraMap A Ap).comp ULift.ringEquiv.toRingHom)).toAlgebra
  let algPC : Algebra (ULift.{u + 1} Ap) C :=
    ((algebraMap Ap C).comp ULift.ringEquiv.toRingHom).toAlgebra
  have : @IsScalarTower (ULift.{u + 1} A) (ULift.{u + 1} Ap) C algP.toSMul algPC.toSMul
      algC.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algP algPC algC fun _ => rfl
  have : IsLocalRing (ULift.{u + 1} Ap) :=
    IsLocalRing.of_surjective' (ULift.ringEquiv.symm : Ap ≃+* ULift.{u + 1} Ap).toRingHom
      (ULift.ringEquiv.symm : Ap ≃+* ULift.{u + 1} Ap).surjective
  have : IsLocalization (S.map (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A).toMonoidHom)
      (ULift.{u + 1} Ap) := by
    let : Algebra (ULift.{u + 1} A) Ap :=
      ((algebraMap A Ap).comp ULift.ringEquiv.toRingHom).toAlgebra
    exact (IsLocalization.isLocalization_iff_of_ringEquiv _
      (ULift.ringEquiv.symm : Ap ≃+* ULift.{u + 1} Ap)).1
      (IsLocalization.isLocalization_of_base_ringEquiv S Ap
        (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A))
  have : IsLocalHom (algebraMap (ULift.{u + 1} Ap) C) := by
    have := IsHenselization.isLocalHom (R := Ap) (L := L) (Rh := C)
    have : IsLocalHom (ULift.ringEquiv : ULift.{u + 1} Ap ≃+* Ap).toRingHom :=
      isLocalHom_toRingHom (ULift.ringEquiv : ULift.{u + 1} Ap ≃+* Ap)
    exact RingHom.isLocalHom_comp (algebraMap Ap C)
      (ULift.ringEquiv : ULift.{u + 1} Ap ≃+* Ap).toRingHom
  have : IsHenselization (ULift.{u + 1} Ap) (ResidueField C) C :=
    IsHenselization.residueField_of_ringEquiv (R := Ap) (L := L) (Rh := C)
      (ULift.ringEquiv : ULift.{u + 1} Ap ≃+* Ap) (fun _ => rfl)
  exact isZero_cotangentComplexDerived_henselization_localization (ULift.{u + 1} A)
    (S.map (ULift.ringEquiv.symm : A ≃+* ULift.{u + 1} A).toMonoidHom) (ULift.{u + 1} Ap)
    (ResidueField C) C

end CommAlgCat

namespace AlgebraicGeometry.Space

open PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))

section Presheaf

variable (F : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)

/-- The `Λ`-algebra structure of the regular functions on the étale charts of a presheaf over
`Spec Λ`: on a chart `U`, the ring map `Λ = Γ(Spec Λ) → Γ(U)` of the structure morphism
`U ⟶ Spec Λ`. -/
def etaleConstantStructurePresheafMap :
    (Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS F)ᵒᵖ).obj (CommRingCat.of Λ) ⟶
      structurePresheaf B (Spec (CommRingCat.of Λ)) hS F where
  app U := (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
    Scheme.Γ.map (openPartToBase Λ B hS F U.unop).op
  naturality := by
    intro U V f
    have hΓ : Scheme.Γ.map (openPartToBase Λ B hS F U.unop).op ≫
        Scheme.Γ.map ((smallEtaleToScheme Λ B hS F).map f.unop).op =
          Scheme.Γ.map (openPartToBase Λ B hS F V.unop).op := by
      rw [← Scheme.Γ.map_comp]
      exact congrArg Scheme.Γ.map (congrArg Quiver.Hom.op (map_comp_openPartToBase Λ B hS F f.unop))
    change (𝟙 (CommRingCat.of Λ)) ≫ ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (openPartToBase Λ B hS F V.unop).op) =
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        Scheme.Γ.map (openPartToBase Λ B hS F U.unop).op) ≫
        Scheme.Γ.map ((smallEtaleToScheme Λ B hS F).map f.unop).op
    rw [Category.id_comp]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫ t) hΓ.symm

/-- The constant sheaf of rings `Λ̲` on the small étale site of a presheaf over `Spec Λ`. -/
abbrev etaleConstantRing : Sheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS F)
    CommRingCat.{u} :=
  (presheafToSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS F) CommRingCat.{u}).obj
    ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS F)ᵒᵖ).obj (CommRingCat.of Λ))

/-- The structure map `Λ̲ ⟶ 𝒪` of an algebraic space over `Spec Λ` on its small étale site: the
map of sheaves of rings induced by `etaleConstantStructurePresheafMap`. -/
def etaleConstantStructureMap (hF : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS F) :
    etaleConstantRing Λ B hS F ⟶ structureSheaf B (Spec (CommRingCat.of Λ)) hS F hF :=
  ((sheafificationAdjunction (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS F)
    CommRingCat.{u}).homEquiv _ _).symm
    (etaleConstantStructurePresheafMap Λ B hS F)

/-- The structure map is the sheafification of `etaleConstantStructurePresheafMap`: precomposed
with the sheafification map of the constant presheaf, it is that presheaf map. -/
theorem toSheafify_comp_etaleConstantStructureMap
    (hF : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS F) :
    toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS F)
        ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS F)ᵒᵖ).obj
          (CommRingCat.of Λ)) ≫ (etaleConstantStructureMap Λ B hS F hF).hom =
      etaleConstantStructurePresheafMap Λ B hS F := by
  have h := ((sheafificationAdjunction (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS F)
    CommRingCat.{u}).homEquiv _
      (structureSheaf B (Spec (CommRingCat.of Λ)) hS F hF)).apply_symm_apply
    (etaleConstantStructurePresheafMap Λ B hS F)
  rwa [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h

end Presheaf

section Base

/-- `Spec Λ` as an algebraic space over itself: the presheaf represented by the final object of
the big fppf site of `Spec Λ`. -/
abbrev specSpace : AlgebraicSpaces B (Spec (CommRingCat.of Λ)) hS :=
  schemeSpace (BigFppfOver.terminalObj B (Spec (CommRingCat.of Λ)) hS)

variable (x : GeometricPoint B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)

/-- The identity chart of `Spec Λ`, with the geometric point itself as the lift: a small étale
neighbourhood of every geometric point of `Spec Λ`. -/
def specNeighborhood : SmallEtaleNeighborhood x where
  chart := idEtaleChart B (Spec (CommRingCat.of Λ)) hS
    (BigFppfOver.terminalObj B (Spec (CommRingCat.of Λ)) hS)
  point := x.val.value
  point_comp := rfl

/-- The point of the small étale site of `Spec Λ` attached to a geometric point. -/
abbrev specEtalePoint :
    (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1).Point.{u} :=
  etaleSitePoint B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x (specSpace Λ B hS).2

/-- The lift of the geometric point to the identity chart. -/
abbrev specLift : (specEtalePoint Λ B hS x).fiber.obj (specNeighborhood Λ B hS x).chart :=
  ⟨x.val.value, rfl⟩

/-- The germ map `Λ → Λ̲_x̄` of the constant sheaf at a geometric point, at the identity
chart. -/
def etaleConstantGerm : CommRingCat.of Λ ⟶
    ((specEtalePoint Λ B hS x).presheafFiber (A := CommRingCat.{u})).obj
      (etaleConstantRing Λ B hS (specSpace Λ B hS).1).obj :=
  (toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)
      ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)ᵒᵖ).obj
        (CommRingCat.of Λ))).app (op (specNeighborhood Λ B hS x).chart) ≫
    (specEtalePoint Λ B hS x).toPresheafFiber (specNeighborhood Λ B hS x).chart (specLift Λ B hS x)
      (etaleConstantRing Λ B hS (specSpace Λ B hS).1).obj

/-- **The stalk of the constant sheaf `Λ̲` at a geometric point is `Λ`**: the germ map is
bijective, the germ map of the constant presheaf being bijective and sheafification not changing
fibres. -/
theorem bijective_etaleConstantGerm : Function.Bijective (etaleConstantGerm Λ B hS x) := by
  have h : etaleConstantGerm Λ B hS x = (specEtalePoint Λ B hS x).toPresheafFiber
      (specNeighborhood Λ B hS x).chart (specLift Λ B hS x)
        ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)ᵒᵖ).obj
          (CommRingCat.of Λ)) ≫
      ((specEtalePoint Λ B hS x).presheafFiber (A := CommRingCat.{u})).map
        (toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)
          ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS
            (specSpace Λ B hS).1)ᵒᵖ).obj (CommRingCat.of Λ))) :=
    ((specEtalePoint Λ B hS x).toPresheafFiber_naturality _ _ _).symm
  rw [h, ConcreteCategory.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    ((specEtalePoint Λ B hS x).bijective_toPresheafFiber_const (CommRingCat.of Λ)
      (specNeighborhood Λ B hS x).chart (specLift Λ B hS x))

/-- The stalk of the constant sheaf `Λ̲` at a geometric point of `Spec Λ`, identified with `Λ`. -/
def etaleConstantFiberEquiv :
    ((specEtalePoint Λ B hS x).presheafFiber (A := CommRingCat.{u})).obj
      (etaleConstantRing Λ B hS (specSpace Λ B hS).1).obj ≃+* Λ :=
  (RingEquiv.ofBijective (etaleConstantGerm Λ B hS x).hom
    (bijective_etaleConstantGerm Λ B hS x)).symm

/-- The ring map `Λ → 𝒪_{Spec Λ, x̄}` to the étale local ring at a geometric point: the germ, at
the identity chart, of the image of `Λ` in the global regular functions. -/
def specStalkMap : Λ →+* etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x :=
  (etaleLocalRingGerm B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x
      (op (specNeighborhood Λ B hS x))).comp
    ((etaleConstantStructurePresheafMap Λ B hS (specSpace Λ B hS).1).app
      (op (specNeighborhood Λ B hS x).chart)).hom

/-- **The stalk of the structure map `Λ̲ ⟶ 𝒪` at a geometric point of `Spec Λ` is the germ map**
`Λ → 𝒪_{Spec Λ, x̄}`, through the identification of the stalk of `Λ̲` with `Λ` and of the stalk
of `𝒪` with the étale local ring. -/
theorem pointStalkRingEquiv_etaleConstantStructureMap (a : Λ) :
    pointStalkRingEquiv B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS) x
        (((specEtalePoint Λ B hS x).presheafFiber (A := CommRingCat.{u})).map
          (etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2).hom
          (etaleConstantGerm Λ B hS x a)) =
      specStalkMap Λ B hS x a := by
  have hκ := congrArg (fun φ => φ.app (op (specNeighborhood Λ B hS x).chart) a)
    (toSheafify_comp_etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2)
  simp only [NatTrans.comp_app] at hκ
  have hn := (specEtalePoint Λ B hS x).toPresheafFiber_naturality_apply
    (etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2).hom
    (specNeighborhood Λ B hS x).chart (specLift Λ B hS x)
    ((toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)
      ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1)ᵒᵖ).obj
        (CommRingCat.of Λ))).app (op (specNeighborhood Λ B hS x).chart) a)
  refine (congrArg (pointStalkRingEquiv B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS) x)
    hn).trans ?_
  rw [ConcreteCategory.comp_apply] at hκ
  rw [hκ]
  exact pointStalkRingEquiv_germ_neighborhood B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)
    x (specNeighborhood Λ B hS x) _

/-- On the identity chart of `Spec Λ`, the `Λ`-algebra structure is the inverse of the
identification `Γ(Spec Λ) = Λ`. -/
theorem etaleConstantStructurePresheafMap_app_specNeighborhood (a : Λ) :
    (etaleConstantStructurePresheafMap Λ B hS (specSpace Λ B hS).1).app
      (op (specNeighborhood Λ B hS x).chart) a = (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv a := by
  change Scheme.Γ.map (openPartToBase Λ B hS (specSpace Λ B hS).1
    (specNeighborhood Λ B hS x).chart).op ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv a) = _
  rw [show openPartToBase Λ B hS (specSpace Λ B hS).1 (specNeighborhood Λ B hS x).chart = 𝟙 _
    from B.inclusion.map_id _]
  rfl

attribute [local instance] HasDerivedCategory.standard in
/-- **`L_q = 0` at the geometric points of `Spec Λ`.** The cotangent complex of the germ map
`Λ → 𝒪_{Spec Λ, x̄}` vanishes: the étale local ring is a strict henselization of the local ring
`Λ_𝔭` of `Spec Λ` at the image point (Stacks 04KF, the identity chart), so items (3), (7) and
(8) of Stacks 08R2 apply to the tower `Λ → Λ_𝔭 → 𝒪_{Spec Λ, x̄}`. -/
theorem isZero_cotangentComplexDerived_specStalkMap :
    letI : Algebra (ULift.{u + 1} Λ)
        (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x) :=
      ((specStalkMap Λ B hS x).comp ULift.ringEquiv.toRingHom).toAlgebra
    IsZero (CommAlgCat.cotangentComplexDerived.{u + 1, u + 1} (ULift.{u + 1} Λ)
      (CommAlgCat.of (ULift.{u + 1} Λ)
        (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x))) := by
  let V := specNeighborhood Λ B hS x
  let p : PrimeSpectrum Λ := chartPoint B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V
  let : IsLocalRing (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x) :=
    isLocalRing_etaleLocalRing B _ hS _ (specSpace Λ B hS).2 x
  let algE : Algebra ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V)
      (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x) :=
    (chartLocalRingToEtaleLocalRing B _ hS _ (specSpace Λ B hS).2 V).toAlgebra
  have : IsLocalRing.IsHenselization
      ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V)
      (separableClosure (IsLocalRing.ResidueField
        ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V))
        (chartGeometricPoint V).residueField)
      (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x) :=
    IsLocalRing.IsHenselization.of_ringEquiv
      (chartStrictHenselizationEquiv B _ hS _ (specSpace Λ B hS).2 V) fun _ ↦ rfl
  have hmor : (Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
      (Spec (CommRingCat.of Λ)).presheaf.germ ⊤ p trivial =
      CommRingCat.ofHom (algebraMap (CommRingCat.of Λ) (Localization.AtPrime p.asIdeal)) ≫
        (Spec.stalkIso (CommRingCat.of Λ) p).inv :=
    (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of Λ) p).symm
  let algL : Algebra Λ
      ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V) :=
    (CommRingCat.ofHom (algebraMap (CommRingCat.of Λ) (Localization.AtPrime p.asIdeal)) ≫
      (Spec.stalkIso (CommRingCat.of Λ) p).inv).hom.toAlgebra
  have : IsLocalization p.asIdeal.primeCompl
      ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V) :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (R := Λ) p.asIdeal.primeCompl
      (S := Localization.AtPrime p.asIdeal)
      (Spec.stalkIso (CommRingCat.of Λ) p).symm.commRingCatIsoToRingEquiv).1 inferInstance
  have key := CommAlgCat.isZero_cotangentComplexDerived_ulift_henselization_localization Λ
    p.asIdeal.primeCompl
    ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V)
    (separableClosure (IsLocalRing.ResidueField
      ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V))
      (chartGeometricPoint V).residueField)
    (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x)
  have hEq : (algebraMap ↥(chartLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 V)
        (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 x)).comp
        ((algebraMap Λ _).comp ULift.ringEquiv.toRingHom) =
      (specStalkMap Λ B hS x).comp ULift.ringEquiv.toRingHom := by
    refine RingHom.ext fun a => ?_
    change chartLocalRingToEtaleLocalRing B _ hS _ (specSpace Λ B hS).2 V
        ((CommRingCat.ofHom (algebraMap (CommRingCat.of Λ) (Localization.AtPrime p.asIdeal)) ≫
          (Spec.stalkIso (CommRingCat.of Λ) p).inv) a.down) =
      etaleLocalRingGerm B _ hS _ x (op V)
        ((etaleConstantStructurePresheafMap Λ B hS (specSpace Λ B hS).1).app (op V.chart) a.down)
    rw [etaleConstantStructurePresheafMap_app_specNeighborhood, ← hmor, CommRingCat.comp_apply]
    exact chartLocalRingToEtaleLocalRing_germ B _ hS _ (specSpace Λ B hS).2 V
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv a.down)
  rwa [← hEq]

end Base

section Space

variable (X : AlgebraicSpaces B (Spec (CommRingCat.of Λ)) hS)

/-- The structure morphism `X ⟶ Spec Λ` of an algebraic space over `Spec Λ`: the unique morphism
to the presheaf represented by the final object of the big fppf site. -/
def structureToSpec : X ⟶ specSpace Λ B hS :=
  ObjectProperty.homMk
    { app := fun T => TypeCat.ofHom fun _ => (Over.mkIdTerminal (X := B.obj hS)).from T.unop
      naturality := fun _ _ _ => by
        ext
        exact (Over.mkIdTerminal (X := B.obj hS)).hom_ext _ _ }

/-- The morphism of small étale ringed topoi of the structure morphism `X ⟶ Spec Λ`. -/
abbrev structureToSpecRingedTopos :=
  smallEtaleRingedToposHom B (Spec (CommRingCat.of Λ)) hS (structureToSpec Λ B hS X)

/-- The base `p⁻¹Λ̲` of the tower `p⁻¹Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` on the small étale site of `X`,
`p : X ⟶ Spec Λ` the structure morphism, with its sections lifted into the universe of the
site. -/
abbrev towerBase : Sheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
    CommRingCat.{u + 1} :=
  (SheafOfModules.sheafULift.{u, u + 1, u}
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).obj
    ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.obj
      (etaleConstantRing Λ B hS (specSpace Λ B hS).1))

/-- The middle term `p⁻¹𝒪_{Spec Λ}` of the tower, with its sections lifted. -/
abbrev towerMiddle : Sheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
    CommRingCat.{u + 1} :=
  (SheafOfModules.sheafULift.{u, u + 1, u}
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).obj
    ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.obj
      (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)).O)

/-- The lower map `p⁻¹Λ̲ ⟶ p⁻¹𝒪_{Spec Λ}` of the tower: the inverse image of the structure map
`Λ̲ ⟶ 𝒪` of `Spec Λ`. -/
abbrev towerLower : towerBase Λ B hS X ⟶ towerMiddle Λ B hS X :=
  (SheafOfModules.sheafULift.{u, u + 1, u}
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map
    ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.map
      (etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2))

/-- The upper map `p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` of the tower: the structure map of `p`, whose cotangent
complex is `L_{X/Spec Λ}` (Tag 08VD). -/
abbrev towerUpper : towerMiddle Λ B hS X ⟶ smallEtaleStructureSheafULift B _ hS X :=
  (SheafOfModules.sheafULift.{u, u + 1, u}
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map
    (structureToSpecRingedTopos Λ B hS X).fSharpInverseImage

variable (x : GeometricPoint B (Spec (CommRingCat.of Λ)) hS X.1)

/-- The image in `Spec Λ` of a geometric point of `X`. -/
abbrev overRingImagePoint : GeometricPoint B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1 :=
  geometricPointMap (structureToSpec Λ B hS X).hom x

/-- The point of the small étale site of `X` attached to a geometric point, with its fibres
lifted into the universe of the site. -/
abbrev overRingLiftedPoint :
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J.Point.{u + 1} :=
  (etaleSitePoint B (Spec (CommRingCat.of Λ)) hS X.1 x X.2).ulift.{u + 1}

/-- The stalk of the base `p⁻¹Λ̲` of the tower at a geometric point of `X` is `Λ`: the stalk of
an inverse image is the stalk at the image point (Stacks 04K2), and the stalk of `Λ̲` is `Λ`. -/
def towerBaseFiberEquiv :
    ((overRingLiftedPoint Λ B hS X x).presheafFiber (A := CommRingCat.{u + 1})).obj
      (towerBase Λ B hS X).obj ≃+* ULift.{u + 1} Λ :=
  (Stacks.uliftRingFiberIso' (etaleSitePoint B (Spec (CommRingCat.of Λ)) hS X.1 x X.2)
      ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.obj
        (etaleConstantRing Λ B hS (specSpace Λ B hS).1)).obj).commRingCatIsoToRingEquiv.trans
    (ULift.ringEquiv.trans
      ((((smallEtaleInverseImageFiberRingIso B (Spec (CommRingCat.of Λ)) hS
          (structureToSpec Λ B hS X) x).app
          (etaleConstantRing Λ B hS (specSpace Λ B hS).1)).symm.commRingCatIsoToRingEquiv).trans
        ((etaleConstantFiberEquiv Λ B hS (overRingImagePoint Λ B hS X x)).trans
          ULift.ringEquiv.symm)))

/-- The stalk of the middle term `p⁻¹𝒪_{Spec Λ}` of the tower at a geometric point of `X` is
the étale local ring of `Spec Λ` at the image point. -/
def towerMiddleFiberEquiv :
    ((overRingLiftedPoint Λ B hS X x).presheafFiber (A := CommRingCat.{u + 1})).obj
      (towerMiddle Λ B hS X).obj ≃+*
      etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1
        (overRingImagePoint Λ B hS X x) :=
  (Stacks.uliftRingFiberIso' (etaleSitePoint B (Spec (CommRingCat.of Λ)) hS X.1 x X.2)
      ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.obj
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
          (specSpace Λ B hS)).O).obj).commRingCatIsoToRingEquiv.trans
    (ULift.ringEquiv.trans
      ((((smallEtaleInverseImageFiberRingIso B (Spec (CommRingCat.of Λ)) hS
          (structureToSpec Λ B hS X) x).app
          (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS
            (specSpace Λ B hS)).O).symm.commRingCatIsoToRingEquiv).trans
        (pointStalkRingEquiv B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)
          (overRingImagePoint Λ B hS X x))))

/-- **The stalk of the lower map of the tower at a geometric point of `X` is the germ map**
`Λ → 𝒪_{Spec Λ, p(x̄)}` at the image point. -/
theorem towerMiddleFiberEquiv_map_towerLower
    (y : ((overRingLiftedPoint Λ B hS X x).presheafFiber (A := CommRingCat.{u + 1})).obj
      (towerBase Λ B hS X).obj) :
    towerMiddleFiberEquiv Λ B hS X x
        (((overRingLiftedPoint Λ B hS X x).presheafFiber (A := CommRingCat.{u + 1})).map
          (towerLower Λ B hS X).hom y) =
      specStalkMap Λ B hS (overRingImagePoint Λ B hS X x)
        (towerBaseFiberEquiv Λ B hS X x y).down := by
  let F := (structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing
  let β := etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2
  let Φ₀ := etaleSitePoint B (Spec (CommRingCat.of Λ)) hS X.1 x X.2
  let θ := smallEtaleInverseImageFiberRingIso B (Spec (CommRingCat.of Λ)) hS
    (structureToSpec Λ B hS X) x
  have h1 := ConcreteCategory.congr_hom
    (Stacks.uliftRingFiberIso'_naturality Φ₀ (F.map β).hom) y
  have h2 := ConcreteCategory.congr_hom (θ.inv.naturality β)
    ((Stacks.uliftRingFiberIso' Φ₀ (F.obj (etaleConstantRing Λ B hS
      (specSpace Λ B hS).1)).obj).hom y).down
  set w := θ.inv.app (etaleConstantRing Λ B hS (specSpace Λ B hS).1)
    ((Stacks.uliftRingFiberIso' Φ₀ (F.obj (etaleConstantRing Λ B hS
      (specSpace Λ B hS).1)).obj).hom y).down with hw
  have h3 : w = etaleConstantGerm Λ B hS (overRingImagePoint Λ B hS X x)
      (etaleConstantFiberEquiv Λ B hS (overRingImagePoint Λ B hS X x) w) :=
    ((RingEquiv.ofBijective (etaleConstantGerm Λ B hS (overRingImagePoint Λ B hS X x)).hom
      (bijective_etaleConstantGerm Λ B hS (overRingImagePoint Λ B hS X x))).apply_symm_apply w).symm
  let G := pointStalkRingEquiv B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)
    (overRingImagePoint Λ B hS X x)
  let O := (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)).O
  calc towerMiddleFiberEquiv Λ B hS X x
        (((overRingLiftedPoint Λ B hS X x).presheafFiber (A := CommRingCat.{u + 1})).map
          (towerLower Λ B hS X).hom y)
      = G (θ.inv.app O (((Stacks.uliftRingFiberIso' Φ₀ (F.obj O).obj).hom
          (((overRingLiftedPoint Λ B hS X x).presheafFiber (A := CommRingCat.{u + 1})).map
            (towerLower Λ B hS X).hom y)).down)) := rfl
    _ = G (θ.inv.app O ((F ⋙ Φ₀.sheafFiber).map β
          ((Stacks.uliftRingFiberIso' Φ₀ (F.obj (etaleConstantRing Λ B hS
            (specSpace Λ B hS).1)).obj).hom y).down)) :=
        congrArg (fun z => G (θ.inv.app O (ULift.down z))) h1
    _ = G (((etaleSitePoint B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1
          (overRingImagePoint Λ B hS X x) (specSpace Λ B hS).2).sheafFiber
            (A := CommRingCat.{u})).map
            β w) := congrArg G h2
    _ = G (((etaleSitePoint B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1
          (overRingImagePoint Λ B hS X x) (specSpace Λ B hS).2).sheafFiber
            (A := CommRingCat.{u})).map
            β (etaleConstantGerm Λ B hS (overRingImagePoint Λ B hS X x)
              (etaleConstantFiberEquiv Λ B hS (overRingImagePoint Λ B hS X x) w))) := by rw [← h3]
  exact pointStalkRingEquiv_etaleConstantStructureMap Λ B hS (overRingImagePoint Λ B hS X x) _

/-- **The lower map of the tower has vanishing cotangent complex at every geometric point of
`X`**: its stalk is the germ map `Λ → 𝒪_{Spec Λ, p(x̄)}`, whose cotangent complex vanishes. -/
theorem isCotangentAcyclicAt_towerLower :
    CategoryTheory.Sheaf.IsCotangentAcyclicAt.{u + 1, u, u} (towerLower Λ B hS X)
      (overRingLiftedPoint Λ B hS X x) := by
  let : Algebra (ULift.{u + 1} Λ) (etaleLocalRing B (Spec (CommRingCat.of Λ)) hS
      (specSpace Λ B hS).1 (overRingImagePoint Λ B hS X x)) :=
    ((specStalkMap Λ B hS (overRingImagePoint Λ B hS X x)).comp ULift.ringEquiv.toRingHom).toAlgebra
  exact ⟨ULift.{u + 1} Λ, etaleLocalRing B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS).1
      (overRingImagePoint Λ B hS X x), inferInstance, inferInstance, inferInstance,
    towerBaseFiberEquiv Λ B hS X x, towerMiddleFiberEquiv Λ B hS X x,
    towerMiddleFiberEquiv_map_towerLower Λ B hS X x,
    fun n => CochainComplex.exactAt_of_isZero_Q _ n
      (isZero_cotangentComplexDerived_specStalkMap Λ B hS (overRingImagePoint Λ B hS X x))⟩

end Space

section Canonical

variable (X : AlgebraicSpaces B (Spec (CommRingCat.of Λ)) hS)

/-- The ring map `Λ → Γ(Spec Λ, 𝒪)` adjoint to the structure map `Λ̲ ⟶ 𝒪` of `Spec Λ`. -/
def specGlobalStructureMap : CommRingCat.of Λ ⟶ (ringGlobalSections (specSpace Λ B hS)).obj
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)).O :=
  (constantSheafGlobalSectionsAdj (specSpace Λ B hS)).homEquiv _ _
    (etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2)

/-- **The structure map of `X` over `Λ` on global sections**, `Λ → Γ(X, 𝒪_X)`: the map
`Λ → Γ(Spec Λ, 𝒪)` followed by the map on global sections induced by the structure morphism
`p : X ⟶ Spec Λ`, that is `p♯` read on global sections through
`AlgebraicGeometry.Space.globalSectionsPushforwardIso`. -/
def globalStructureMap : CommRingCat.of Λ ⟶
    (ringGlobalSections X).obj (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).O :=
  specGlobalStructureMap Λ B hS ≫
    (ringGlobalSections (specSpace Λ B hS)).map (structureToSpecRingedTopos Λ B hS X).fSharp ≫
    (globalSectionsPushforwardIso (structureToSpec Λ B hS X)).hom.app _

/-- **The structure map `Λ̲ ⟶ 𝒪_X` of an algebraic space over `Λ`** on its small étale site, `Λ̲`
the constant sheaf with value `Λ`: the map adjoint, under the adjunction between the constant
sheaf and global sections, to the structure map `Λ → Γ(X, 𝒪_X)` of `X` over `Λ`. -/
def constantStructureMapOfSpace :
    (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1) CommRingCat.{u}).obj
        (CommRingCat.of Λ) ⟶ (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).O :=
  ((constantSheafGlobalSectionsAdj X).homEquiv _ _).symm (globalStructureMap Λ B hS X)

/-- **The structure map of `X` over `Λ` factors through the inverse image of that of
`Spec Λ`**: under the identification `Λ̲_X ≅ p⁻¹Λ̲` of the constant sheaves
(`AlgebraicGeometry.Space.constantSheafInverseImageIso`), the structure map `Λ̲_X ⟶ 𝒪_X` is
`p⁻¹` of the structure map of `Spec Λ` followed by `p♯`. Both are adjoint to the structure map
`Λ → Γ(X, 𝒪_X)`, the identification being the uniqueness of left adjoints of global
sections. -/
theorem constantSheafInverseImageIso_hom_comp :
    (constantSheafInverseImageIso (structureToSpec Λ B hS X)).hom.app (CommRingCat.of Λ) ≫
        (structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.map
          (etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2) ≫
        (structureToSpecRingedTopos Λ B hS X).fSharpInverseImage =
      constantStructureMapOfSpace Λ B hS X := by
  let adj1 := constantSheafGlobalSectionsAdj X
  let adj2 := ((constantSheafGlobalSectionsAdj (specSpace Λ B hS)).comp
      (structureToSpecRingedTopos Λ B hS X).toToposHom.ringAdjunction).ofNatIsoRight
    (globalSectionsPushforwardIso (structureToSpec Λ B hS X))
  have key : ∀ {O} (h : (constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS
      (specSpace Λ B hS).1) CommRingCat.{u} ⋙
        (structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing).obj
          (CommRingCat.of Λ) ⟶ O),
      adj1.homEquiv _ _ ((adj1.leftAdjointUniq adj2).hom.app _ ≫ h) = adj2.homEquiv _ _ h := by
    intro O h
    rw [adj1.homEquiv_unit, adj2.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      Adjunction.unit_leftAdjointUniq_hom_app]
  refine (adj1.homEquiv _ _).injective (((key _).trans ?_).trans (Equiv.apply_symm_apply _ _).symm)
  let adjY := constantSheafGlobalSectionsAdj (specSpace Λ B hS)
  let ra := (structureToSpecRingedTopos Λ B hS X).toToposHom.ringAdjunction
  let st := etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2
  have hs : ra.homEquiv _ _ (structureToSpecRingedTopos Λ B hS X).fSharpInverseImage =
      (structureToSpecRingedTopos Λ B hS X).fSharp :=
    Equiv.apply_symm_apply _ _
  have h1 : ra.homEquiv _ _ ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.map
      st ≫ (structureToSpecRingedTopos Λ B hS X).fSharpInverseImage) =
        st ≫ (structureToSpecRingedTopos Λ B hS X).fSharp :=
    (ra.homEquiv_naturality_left _ _).trans (congrArg (st ≫ ·) hs)
  have h2 : (adjY.comp ra).homEquiv _ _
      ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.map st ≫
        (structureToSpecRingedTopos Λ B hS X).fSharpInverseImage) =
      specGlobalStructureMap Λ B hS ≫
        (ringGlobalSections (specSpace Λ B hS)).map (structureToSpecRingedTopos Λ B hS X).fSharp :=
    (congrArg (fun e => e _ _ ((structureToSpecRingedTopos Λ B hS X).toToposHom.inverseImageRing.map
      st ≫ (structureToSpecRingedTopos Λ B hS X).fSharpInverseImage))
        (Adjunction.comp_homEquiv adjY ra)).trans
      ((congrArg (adjY.homEquiv _ _) h1).trans (adjY.homEquiv_naturality_right _ _))
  exact (Adjunction.homEquiv_ofNatIsoRight_apply _ _ _).trans
    ((congrArg (· ≫ _) h2).trans (Category.assoc _ _ _))

end Canonical

section Main

variable (X : AlgebraicSpaces B (Spec (CommRingCat.of Λ)) hS)

/-- The abelian structure of the modules over the lifted structure sheaf of `X`, named at this
spelling: instance search otherwise tries an instance for `CategoryTheory.Sheaf.targetModules`
whose universe of sections it cannot determine. -/
instance (priority := high) abelian_smallEtaleModulesULift :
    Abelian (smallEtaleModulesULift B (Spec (CommRingCat.of Λ)) hS X) :=
  SheafOfModules.instAbelian _

open CategoryTheory.Pretriangulated in
/-- **The cotangent complex over a base whose stalks have vanishing cotangent complex.** Let
`g : R₀ ⟶ p⁻¹𝒪_{Spec Λ}` be a homomorphism of sheaves of rings on the small étale site of `X`
whose stalk map has vanishing ring-level cotangent complex at every geometric point. Then the
change-of-base map of the tower `R₀ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` is an isomorphism
`L_{𝒪_X/R₀} ≅ L_{X/Spec Λ}` in `D(𝒪_X)`: the first vertex of the tower's fundamental triangle
(Tag 08SZ) vanishes stalkwise. -/
def cotangentComplexIsoOfIsCotangentAcyclicAt
    {R₀ : Sheaf (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J CommRingCat.{u + 1}}
    (g : R₀ ⟶ towerMiddle Λ B hS X)
    (hg : ∀ x : GeometricPoint B (Spec (CommRingCat.of Λ)) hS X.1,
      CategoryTheory.Sheaf.IsCotangentAcyclicAt.{u + 1, u, u} g (overRingLiftedPoint Λ B hS X x))
    [HasDerivedCategory.{t} (smallEtaleModulesULift B (Spec (CommRingCat.of Λ)) hS X)] :
    DerivedCategory.Q.obj (CategoryTheory.Sheaf.cotangentComplex.{u + 1, u, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
        (g ≫ towerUpper Λ B hS X)) ≅
      cotangentComplexDerived B (Spec (CommRingCat.of Λ)) hS (structureToSpec Λ B hS X) :=
  have hz := CategoryTheory.Sheaf.isZero_Q_obj_baseChangedCotangentComplex_of_isCotangentAcyclicAt
    g (isConservativeFamilyOfPoints_uliftEtaleSitePoint B (Spec (CommRingCat.of Λ)) hS X.1 X.2)
    (fun Φ hΦ => by
      obtain ⟨x⟩ := hΦ
      exact hg x)
    (towerUpper Λ B hS X)
  have hT := (CategoryTheory.Sheaf.exists_distTriang_towerCotangent.{u + 1, u, u, t}
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J g
    (towerUpper Λ B hS X)).choose_spec
  @asIso _ _ _ _ (DerivedCategory.Q.map
    (CategoryTheory.Sheaf.towerCotangentChangeOfBase.{u + 1, u, u}
      (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J g
      (towerUpper Λ B hS X))) ((Triangle.isZero₁_iff_isIso₂ _ hT).1 hz)

/-- **`L_{X/Spec Λ} = L_{𝒪_X/p⁻¹Λ̲}`.** For an algebraic space `X` over `Spec Λ` with structure
morphism `p`, the change-of-base map of the tower `p⁻¹Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` is an
isomorphism `L_{𝒪_X/p⁻¹Λ̲} ≅ L_{X/Spec Λ}` in `D(𝒪_X)`. The tower's fundamental triangle
(Tag 08SZ) has first vertex `L_{p⁻¹𝒪/p⁻¹Λ̲} ⊗ 𝒪_X`, which vanishes stalkwise: at a geometric
point its stalk is the base change of the cotangent complex of the germ map
`Λ → 𝒪_{Spec Λ, p(x̄)}`, and that ring is a strict henselization of a localization of `Λ`
(Tags 04KF, 08R2). -/
def cotangentComplexInverseImageConstantIso
    [HasDerivedCategory.{t} (smallEtaleModulesULift B (Spec (CommRingCat.of Λ)) hS X)] :
    DerivedCategory.Q.obj (CategoryTheory.Sheaf.cotangentComplex.{u + 1, u, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
        (towerLower Λ B hS X ≫ towerUpper Λ B hS X)) ≅
      cotangentComplexDerived B (Spec (CommRingCat.of Λ)) hS (structureToSpec Λ B hS X) :=
  cotangentComplexIsoOfIsCotangentAcyclicAt Λ B hS X (towerLower Λ B hS X)
    (isCotangentAcyclicAt_towerLower Λ B hS X)

/-- The lower map of the tower read from the constant sheaf `Λ̲_X` of `X`: the identification
`Λ̲_X ≅ p⁻¹Λ̲` (`AlgebraicGeometry.Space.constantSheafInverseImageIso`) followed by `p⁻¹` of the
structure map of `Spec Λ`, with sections lifted. -/
abbrev towerConstantLower : (SheafOfModules.sheafULift.{u, u + 1, u}
      (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).obj
      ((constantSheaf (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1)
        CommRingCat.{u}).obj (CommRingCat.of Λ)) ⟶ towerMiddle Λ B hS X :=
  (SheafOfModules.sheafULift.{u, u + 1, u}
      (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map
      ((constantSheafInverseImageIso (structureToSpec Λ B hS X)).hom.app (CommRingCat.of Λ)) ≫
    towerLower Λ B hS X

/-- The tower `Λ̲_X ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` composes to the canonical structure map
`Λ̲_X ⟶ 𝒪_X`, with sections lifted. -/
theorem towerConstantLower_comp_towerUpper :
    towerConstantLower Λ B hS X ≫ towerUpper Λ B hS X =
      (SheafOfModules.sheafULift.{u, u + 1, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map
        (constantStructureMapOfSpace Λ B hS X) :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)).trans
    ((Functor.map_comp _ _ _).symm.trans
      (congrArg (SheafOfModules.sheafULift.{u, u + 1, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map
        (constantSheafInverseImageIso_hom_comp Λ B hS X)))

/-- Let `Λ` be a ring and `X` an algebraic space over `Λ`, with structure morphism
`p : X ⟶ Spec Λ`. Let `Λ̲` be the constant sheaf with value `Λ` on `X_et` and `Λ̲ ⟶ 𝒪_X` its
canonical map, the one adjoint to the structure map `Λ → Γ(X, 𝒪_X)`
(`AlgebraicGeometry.Space.constantStructureMapOfSpace`). Then the cotangent complex of
`Λ̲ ⟶ 𝒪_X` is isomorphic in `D(𝒪_X)` to the cotangent complex `L_{X/Spec Λ}` of Tag 08VD.

The tower `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` composes to the canonical map
(`AlgebraicGeometry.Space.towerConstantLower_comp_towerUpper`); its fundamental triangle
(Tag 08SZ) has first vertex `L_{p⁻¹𝒪/Λ̲} ⊗ 𝒪_X`, which vanishes stalkwise: at a geometric point
its stalk is the base change of the cotangent complex of the germ map
`Λ → 𝒪_{Spec Λ, p(x̄)}`, a strict henselization of a localization of `Λ` (Tags 04KF, 08R2). -/
@[stacks 08VG "an isomorphism in `D(𝒪_X)`, as the source's proof produces. `Λ̲` is Mathlib's \
`constantSheaf` with value `Λ` on `X_et`, and `Λ̲ ⟶ 𝒪_X` is the canonical map, adjoint to the \
structure map `Λ → Γ(X, 𝒪_X)`, global sections being taken at the terminal object of the \
spaces-étale site of `X` (Stacks 03G1). Both cotangent complexes are formed after lifting \
sections to universe `u + 1` (`SheafOfModules.sheafULift`), the universe in which Tag 08VD \
defines `L_{X/Spec Λ}`."]
def cotangentComplexOverConstantSheafIso
    [HasDerivedCategory.{t} (smallEtaleModulesULift B (Spec (CommRingCat.of Λ)) hS X)] :
    DerivedCategory.Q.obj (CategoryTheory.Sheaf.cotangentComplex.{u + 1, u, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J
        ((SheafOfModules.sheafULift.{u, u + 1, u}
          (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).map
          (constantStructureMapOfSpace Λ B hS X))) ≅
      cotangentComplexDerived B (Spec (CommRingCat.of Λ)) hS (structureToSpec Λ B hS X) :=
  eqToIso (congrArg (fun g => DerivedCategory.Q.obj
      (CategoryTheory.Sheaf.cotangentComplex.{u + 1, u, u}
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J g))
      (towerConstantLower_comp_towerUpper Λ B hS X)).symm ≪≫
    cotangentComplexIsoOfIsCotangentAcyclicAt Λ B hS X (towerConstantLower Λ B hS X)
      (fun x => (isCotangentAcyclicAt_towerLower Λ B hS X x).iso_hom_comp
        ((SheafOfModules.sheafULift.{u, u + 1, u}
          (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).J).mapIso
          ((constantSheafInverseImageIso (structureToSpec Λ B hS X)).app (CommRingCat.of Λ))))

end Main

end AlgebraicGeometry.Space
