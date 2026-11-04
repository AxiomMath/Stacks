module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeTarget

/-!
# Pulling back along an isomorphism an identification with a restriction

Let `e : X' ≅ X` be an isomorphism of schemes, `𝒳` a sheaf of `ℤ`-graded algebras on `X'`, `𝒞` one
on `X`, and `Φ : 𝒳 ≅ e^{-1}𝒞` an isomorphism of `𝒳` with the restriction of `𝒞` along `e`. This
file turns `Φ` into an isomorphism of sheaves of graded algebras `(e⁻¹)^*𝒳 ≅ 𝒞` and computes it on
the images of local sections of `𝒳`: it is `Φ`, read on `X`.

It is assembled from three isomorphisms of sheaves of graded algebras: the inverse image of `Φ`
along `e⁻¹`; the identification of an inverse image along an open immersion with the restriction
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackRestrictAlgebraIso`); and the
identification of the restriction along `e⁻¹` of the restriction along `e` with `𝒞`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackRestrictAlgebraIso`: **the inverse
  image of a sheaf of graded algebras along an open immersion is its restriction.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictAlgebraCompIso`: restriction along a
  composite is the iterated restriction.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictAlgebraCongrIdIso`: restriction along
  an open immersion equal to the identity is the identity.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvIso`: **the isomorphism
  `(e⁻¹)^*𝒳 ≅ 𝒞` of sheaves of graded algebras.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvIso_unit`: it sends the image of a
  section `s` of `𝒳` to the restriction of `Φ s`.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

/-! ### Inverse image along an open immersion -/

section OpenImmersion

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (G : SchemeGradedAlgebra Y)

/-- **The inverse image of a sheaf of graded algebras along an open immersion is its
restriction**, as sheaves of graded algebras: degreewise the identification
`Stacks.RingedSpace.pullbackIsoRestrict` of the inverse image with the restriction. -/
def pullbackRestrictAlgebraIso :
    pullbackGradedAlgebra f.toLRSHom.toShHom G ≅ restrictAlgebra f G :=
  SheafOfModules.GradedAlgebra.isoOfPieces
    (fun n => (pullbackIsoRestrict f).app (G.piece n))
    (fun i j U x y => by
      obtain ⟨U⟩ := U
      exact pullbackIsoRestrict_hom_mul f G i j U x y)

/-- In each degree `n`, `pullbackRestrictAlgebraIso` is the identification
`Stacks.RingedSpace.pullbackIsoRestrict` of the inverse image of the piece of degree `n` with its
restriction. -/
@[simp] theorem pullbackRestrictAlgebraIso_hom_app (n : ℤ) :
    (pullbackRestrictAlgebraIso f G).hom.app n = (pullbackIsoRestrict f).hom.app (G.piece n) :=
  rfl

end OpenImmersion

/-! ### Restriction along a composite and along the identity -/

section Restrict

variable {X Y Z : Scheme.{u}}

/-- **Restriction along a composite of open immersions is the iterated restriction**, as sheaves
of graded algebras. On sections it is the restriction map between the two (equal) opens. -/
def restrictAlgebraCompIso (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (G : SchemeGradedAlgebra Z) :
    restrictAlgebra (f ≫ g) G ≅ restrictAlgebra f (restrictAlgebra g G) :=
  SheafOfModules.GradedAlgebra.isoOfPieces
    (fun n => (Scheme.Modules.restrictFunctorComp f g).app (G.piece n))
    (fun i j _ x y => (G.mul i j).naturality _ x y)

/-- `restrictAlgebraCompIso` on sections, in the inverse direction: a restriction map. -/
theorem restrictAlgebraCompIso_inv_app_apply (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] (G : SchemeGradedAlgebra Z) (n : ℤ) (W : X.Opens)
    (z : (G.piece n).val.obj (op (g ''ᵁ (f ''ᵁ W)))) :
    ((restrictAlgebraCompIso f g G).inv.app n).val.app (op W) z =
      (G.piece n).val.map (homOfLE (Scheme.Hom.comp_image f g W).le).op z :=
  PresheafOfModules.map_eq_map (G.piece n).val _ _ z

/-- The image of an open under an open immersion equal to the identity is the open itself. -/
theorem image_eq_of_eq_id {f : X ⟶ X} [IsOpenImmersion f] (hf : f = 𝟙 X) (W : X.Opens) :
    f ''ᵁ W = W := by
  subst hf
  exact Scheme.Hom.id_image W

/-- The identification of the restriction along an open immersion equal to the identity with the
module itself. -/
def restrictCongrIdIso {f : X ⟶ X} [IsOpenImmersion f] (hf : f = 𝟙 X) (M : X.Modules) :
    Scheme.Modules.restrict M f ≅ M :=
  (Scheme.Modules.restrictFunctorCongr hf).app M ≪≫ Scheme.Modules.restrictFunctorId.app M

/-- `restrictCongrIdIso` on sections: a restriction map. -/
theorem restrictCongrIdIso_hom_app_apply {f : X ⟶ X} [IsOpenImmersion f] (hf : f = 𝟙 X)
    (M : X.Modules) (W : X.Opens) (z : M.val.obj (op (f ''ᵁ W))) :
    (restrictCongrIdIso hf M).hom.val.app (op W) z =
      M.val.map (homOfLE (image_eq_of_eq_id hf W).ge).op z := by
  show (Scheme.Modules.restrictFunctorId.hom.app M).app W
      (((Scheme.Modules.restrictFunctorCongr hf).hom.app M).app W z) = _
  rw [Scheme.Modules.restrictFunctorId_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app]
  exact PresheafOfModules.map_map_eq_map M.val _ _ _ z

/-- **Restriction along an open immersion equal to the identity is the identity**, as sheaves of
graded algebras. On sections it is the restriction map between the two (equal) opens. -/
def restrictAlgebraCongrIdIso (f : X ⟶ X) [IsOpenImmersion f] (hf : f = 𝟙 X)
    (G : SchemeGradedAlgebra X) : restrictAlgebra f G ≅ G :=
  SheafOfModules.GradedAlgebra.isoOfPieces (fun n => restrictCongrIdIso hf (G.piece n))
    (fun i j U x y => by
      obtain ⟨U⟩ := U
      refine (restrictCongrIdIso_hom_app_apply hf (G.piece (i + j)) U
        ((G.mul i j).app (op (f ''ᵁ U)) x y)).trans ?_
      refine ((G.mul i j).naturality (homOfLE (image_eq_of_eq_id hf U).ge).op x y).trans ?_
      exact congrArg₂ (fun p q => (G.mul i j).app (op U) p q)
        (restrictCongrIdIso_hom_app_apply hf (G.piece i) U x).symm
        (restrictCongrIdIso_hom_app_apply hf (G.piece j) U y).symm)

/-- In each degree `n`, `restrictAlgebraCongrIdIso` is `restrictCongrIdIso` on the piece of
degree `n`. -/
@[simp] theorem restrictAlgebraCongrIdIso_hom_app (f : X ⟶ X) [IsOpenImmersion f] (hf : f = 𝟙 X)
    (G : SchemeGradedAlgebra X) (n : ℤ) :
    (restrictAlgebraCongrIdIso f hf G).hom.app n = (restrictCongrIdIso hf (G.piece n)).hom :=
  rfl

end Restrict

/-! ### Pulling back along an isomorphism -/

section Iso

variable {X X' : Scheme.{u}} (e : X' ≅ X) {𝒳 : SchemeGradedAlgebra X'} {𝒞 : SchemeGradedAlgebra X}
  (Φ : 𝒳 ≅ restrictAlgebra e.hom 𝒞)

/-- **Pulling back along `e⁻¹` an identification `Φ : 𝒳 ≅ e^{-1}𝒞` with a restriction**: the
isomorphism `(e⁻¹)^*𝒳 ≅ 𝒞` of sheaves of graded algebras. -/
def pullbackInvIso :
    pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳 ≅ 𝒞 :=
  pullbackGradedAlgebraMapIso e.inv.toLRSHom.toShHom Φ ≪≫
    pullbackRestrictAlgebraIso e.inv (restrictAlgebra e.hom 𝒞) ≪≫
    (restrictAlgebraCompIso e.inv e.hom 𝒞).symm ≪≫
    restrictAlgebraCongrIdIso (e.inv ≫ e.hom) e.inv_hom_id 𝒞

/-- The inverse image along `e⁻¹` of an open of `X'` lies in its image under `e`. -/
theorem inv_preimage_le_image (U : X'.Opens) : e.inv ⁻¹ᵁ U ≤ e.hom ''ᵁ U := by
  intro x hx
  exact ⟨e.inv x, hx, by
    show (e.inv ≫ e.hom) x = x
    rw [e.inv_hom_id]
    rfl⟩

/-- **`pullbackInvIso` on the image of a local section `s` of `𝒳`**: the restriction of `Φ s`. -/
theorem pullbackInvIso_unit (n : ℤ) (U : X'.Opens) (s : (𝒳.piece n).val.obj (op U)) :
    ((pullbackInvIso e Φ).hom.app n).val.app (op (e.inv ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction e.inv).unit.app (𝒳.piece n)).val.app
          (op U) s) =
      (𝒞.piece n).val.map (homOfLE (inv_preimage_le_image e U)).op
        ((Φ.hom.app n).val.app (op U) s) := by
  have h1 := pullbackGradedAlgebraMap_pullbackUnit e.inv.toLRSHom.toShHom Φ.hom n U s
  have h2 := pullbackIsoRestrict_hom_pullbackUnit e.inv
    ((restrictAlgebra e.hom 𝒞).piece n) U ((Φ.hom.app n).val.app (op U) s)
  show ((restrictAlgebraCongrIdIso (e.inv ≫ e.hom) e.inv_hom_id 𝒞).hom.app n).val.app
      (op (e.inv ⁻¹ᵁ U))
      (((restrictAlgebraCompIso e.inv e.hom 𝒞).inv.app n).val.app (op (e.inv ⁻¹ᵁ U))
        (((pullbackIsoRestrict e.inv).hom.app ((restrictAlgebra e.hom 𝒞).piece n)).val.app
          (op (e.inv ⁻¹ᵁ U))
          (((pullbackGradedAlgebraMap e.inv.toLRSHom.toShHom Φ.hom).app n).val.app
            (op (e.inv ⁻¹ᵁ U))
            (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s)))) = _
  erw [h1, h2]
  refine (restrictCongrIdIso_hom_app_apply e.inv_hom_id (𝒞.piece n) _ _).trans ?_
  refine (congrArg ((𝒞.piece n).val.map _)
    (restrictAlgebraCompIso_inv_app_apply e.inv e.hom 𝒞 n _ _)).trans ?_
  have key : ∀ {P Q R T : X.Opens} (i : op P ⟶ op Q) (j : op Q ⟶ op R) (k : op R ⟶ op T)
      (l : op P ⟶ op T) (z : (𝒞.piece n).val.obj (op P)),
      (𝒞.piece n).val.map k ((𝒞.piece n).val.map j ((𝒞.piece n).val.map i z)) =
        (𝒞.piece n).val.map l z := fun i j k l z =>
    (congrArg ((𝒞.piece n).val.map k)
      (PresheafOfModules.map_map_eq_map (𝒞.piece n).val i j (i ≫ j) z)).trans
      (PresheafOfModules.map_map_eq_map (𝒞.piece n).val (i ≫ j) k l z)
  exact key _ _ _ _ _

end Iso

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
