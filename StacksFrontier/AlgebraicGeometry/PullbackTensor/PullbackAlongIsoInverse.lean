module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlongIso

/-!
# Every homomorphism out of a pullback along an isomorphism is the pullback of one

Let `e : X' ≅ X` be an isomorphism of schemes, `𝒳` a sheaf of `ℤ`-graded algebras on `X'` and `𝒞`
one on `X`. An identification `Φ : 𝒳 ≅ e^{-1}𝒞` gives an isomorphism `(e⁻¹)^*𝒳 ≅ 𝒞`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvIso`). This file does the same for
homomorphisms, `Φ : 𝒳 ⟶ e^{-1}𝒞` giving `(e⁻¹)^*𝒳 ⟶ 𝒞`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvHom`), and shows that every
homomorphism `α : (e⁻¹)^*𝒳 ⟶ 𝒞` of sheaves of graded algebras arises so, from its restriction
along `e` (`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictBack`). A homomorphism out of
`(e⁻¹)^*𝒳` is therefore determined by a homomorphism on `X'`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictAlgebraMap`: the restriction of a
  homomorphism of sheaves of graded algebras along an open immersion.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvHom`: `Φ : 𝒳 ⟶ e^{-1}𝒞` pulled
  back along `e⁻¹`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictPullbackInvIso`:
  `e^{-1}((e⁻¹)^*𝒳) ≅ 𝒳`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictBack`: a homomorphism
  `(e⁻¹)^*𝒳 ⟶ 𝒞`, restricted back along `e`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictBack_app`: `restrictBack` on sections.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvHom_restrictBack`: **every
  homomorphism out of `(e⁻¹)^*𝒳` is the pullback of its restriction back.**

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.RingedSpace RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

/-- Two restriction maps between the same opens, applied after one another, are the identity
when they start and end at the same open. -/
theorem map_map_self {X : Scheme.{u}} (M : X.Modules) {P Q : X.Opens} (i : op P ⟶ op Q)
    (j : op Q ⟶ op P) (z : M.val.obj (op P)) : M.val.map j (M.val.map i z) = z :=
  (PresheafOfModules.map_map_eq_map M.val i j (𝟙 _) z).trans
    (congr($(M.val.presheaf.map_id (op P)) z))

/-- Three restriction maps applied after one another are one restriction map. -/
theorem map_map_map_eq {X : Scheme.{u}} (M : X.Modules) {P Q R T : X.Opens} (i : op P ⟶ op Q)
    (j : op Q ⟶ op R) (k : op R ⟶ op T) (l : op P ⟶ op T) (z : M.val.obj (op P)) :
    M.val.map k (M.val.map j (M.val.map i z)) = M.val.map l z :=
  (congrArg (M.val.map k) (PresheafOfModules.map_map_eq_map M.val i j (i ≫ j) z)).trans
    (PresheafOfModules.map_map_eq_map M.val (i ≫ j) k l z)

/-- Four restriction maps from an open to itself are the identity. -/
theorem map_map_map_map_self {X : Scheme.{u}} (M : X.Modules) {P Q R T : X.Opens}
    (i : op P ⟶ op Q) (j : op Q ⟶ op R) (k : op R ⟶ op T) (l : op T ⟶ op P)
    (z : M.val.obj (op P)) :
    M.val.map l (M.val.map k (M.val.map j (M.val.map i z))) = z :=
  (congrArg (M.val.map l) (map_map_map_eq M i j k (i ≫ j ≫ k) z)).trans (map_map_self M _ _ z)

/-! ### Restriction of a homomorphism -/

section RestrictMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- **The restriction of a homomorphism of sheaves of graded algebras along an open
immersion.** -/
def restrictAlgebraMap {G H : SchemeGradedAlgebra Y} (φ : G ⟶ H) :
    restrictAlgebra f G ⟶ restrictAlgebra f H where
  app n := (Scheme.Modules.restrictFunctor f).map (φ.app n)
  map_mul i j U x y := φ.map_mul i j (op (f ''ᵁ U.unop)) x y

/-- On sections over an open `U` of `X`, the restriction of `φ` along `f` is `φ` on `f(U)`. -/
theorem restrictAlgebraMap_app_apply {G H : SchemeGradedAlgebra Y} (φ : G ⟶ H) (n : ℤ)
    (U : X.Opens) (x : (G.piece n).val.obj (op (f ''ᵁ U))) :
    ((restrictAlgebraMap f φ).app n).val.app (op U) x = (φ.app n).val.app (op (f ''ᵁ U)) x :=
  rfl

/-- **The restriction of an isomorphism of sheaves of graded algebras along an open
immersion.** -/
def restrictAlgebraMapIso {G H : SchemeGradedAlgebra Y} (φ : G ≅ H) :
    restrictAlgebra f G ≅ restrictAlgebra f H where
  hom := restrictAlgebraMap f φ.hom
  inv := restrictAlgebraMap f φ.inv
  hom_inv_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    ((Scheme.Modules.restrictFunctor f).map_comp (φ.hom.app n) (φ.inv.app n)).symm.trans
      ((congrArg (fun ψ => (Scheme.Modules.restrictFunctor f).map
        (SheafOfModules.GradedAlgebra.Hom.app ψ n)) φ.hom_inv_id).trans
        ((Scheme.Modules.restrictFunctor f).map_id _))
  inv_hom_id := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    ((Scheme.Modules.restrictFunctor f).map_comp (φ.inv.app n) (φ.hom.app n)).symm.trans
      ((congrArg (fun ψ => (Scheme.Modules.restrictFunctor f).map
        (SheafOfModules.GradedAlgebra.Hom.app ψ n)) φ.inv_hom_id).trans
        ((Scheme.Modules.restrictFunctor f).map_id _))

end RestrictMap

/-! ### Along an isomorphism -/

section Iso

variable {X X' : Scheme.{u}} (e : X' ≅ X) {𝒳 : SchemeGradedAlgebra X'} {𝒞 : SchemeGradedAlgebra X}

/-- On sections, the identification `restrictAlgebraCongrIdIso` after the inverse of
`restrictAlgebraCompIso` is a composite of two restriction maps. -/
private theorem congrIdIso_hom_compIso_inv_app_apply {A B : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ A)
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : f ≫ g = 𝟙 A) (G : SchemeGradedAlgebra A)
    (n : ℤ) (W : A.Opens) (z : (G.piece n).val.obj (op (g ''ᵁ (f ''ᵁ W)))) :
    ((restrictAlgebraCongrIdIso (f ≫ g) hfg G).hom.app n).val.app (op W)
        (((restrictAlgebraCompIso f g G).inv.app n).val.app (op W) z) =
      (G.piece n).val.map (homOfLE (image_eq_of_eq_id hfg W).ge).op
        ((G.piece n).val.map (homOfLE (Scheme.Hom.comp_image f g W).le).op z) :=
  (restrictCongrIdIso_hom_app_apply hfg (G.piece n) W _).trans
    (congrArg ((G.piece n).val.map _) (restrictAlgebraCompIso_inv_app_apply f g G n W z))

/-- The image under `e` of an open of `X'` lies in its inverse image along `e⁻¹`. -/
theorem image_le_inv_preimage (U : X'.Opens) : e.hom ''ᵁ U ≤ e.inv ⁻¹ᵁ U := by
  rintro _ ⟨x, hx, rfl⟩
  show (e.hom ≫ e.inv) x ∈ U
  rw [e.hom_inv_id]
  exact hx

/-- **`Φ : 𝒳 ⟶ e^{-1}𝒞` pulled back along `e⁻¹`**, a homomorphism `(e⁻¹)^*𝒳 ⟶ 𝒞`. -/
def pullbackInvHom (Φ : 𝒳 ⟶ restrictAlgebra e.hom 𝒞) :
    pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳 ⟶ 𝒞 :=
  pullbackGradedAlgebraMap e.inv.toLRSHom.toShHom Φ ≫
    (pullbackRestrictAlgebraIso e.inv (restrictAlgebra e.hom 𝒞)).hom ≫
    (restrictAlgebraCompIso e.inv e.hom 𝒞).inv ≫
    (restrictAlgebraCongrIdIso (e.inv ≫ e.hom) e.inv_hom_id 𝒞).hom

/-- The isomorphism `(e⁻¹)^*𝒳 ≅ 𝒞` induced by `Φ : 𝒳 ≅ e^{-1}𝒞` has underlying homomorphism
`pullbackInvHom e Φ.hom`. -/
theorem pullbackInvIso_hom (Φ : 𝒳 ≅ restrictAlgebra e.hom 𝒞) :
    (pullbackInvIso e Φ).hom = pullbackInvHom e Φ.hom :=
  rfl

/-- **`pullbackInvHom` on the image of a local section `s` of `𝒳`**: the restriction of `Φ s`. -/
theorem pullbackInvHom_unit (Φ : 𝒳 ⟶ restrictAlgebra e.hom 𝒞) (n : ℤ) (U : X'.Opens)
    (s : (𝒳.piece n).val.obj (op U)) :
    ((pullbackInvHom e Φ).app n).val.app (op (e.inv ⁻¹ᵁ U))
        (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s) =
      (𝒞.piece n).val.map (homOfLE (inv_preimage_le_image e U)).op
        ((Φ.app n).val.app (op U) s) := by
  have h1 := pullbackGradedAlgebraMap_pullbackUnit e.inv.toLRSHom.toShHom Φ n U s
  have h2 := pullbackIsoRestrict_hom_pullbackUnit e.inv
    ((restrictAlgebra e.hom 𝒞).piece n) U ((Φ.app n).val.app (op U) s)
  show ((restrictAlgebraCongrIdIso (e.inv ≫ e.hom) e.inv_hom_id 𝒞).hom.app n).val.app
      (op (e.inv ⁻¹ᵁ U))
      (((restrictAlgebraCompIso e.inv e.hom 𝒞).inv.app n).val.app (op (e.inv ⁻¹ᵁ U))
        (((pullbackIsoRestrict e.inv).hom.app ((restrictAlgebra e.hom 𝒞).piece n)).val.app
          (op (e.inv ⁻¹ᵁ U))
          (((pullbackGradedAlgebraMap e.inv.toLRSHom.toShHom Φ).app n).val.app
            (op (e.inv ⁻¹ᵁ U))
            (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s)))) = _
  refine (congrArg (fun z => ((restrictAlgebraCongrIdIso (e.inv ≫ e.hom) e.inv_hom_id 𝒞).hom.app
      n).val.app (op (e.inv ⁻¹ᵁ U))
      (((restrictAlgebraCompIso e.inv e.hom 𝒞).inv.app n).val.app (op (e.inv ⁻¹ᵁ U)) z))
    ((congrArg (((pullbackIsoRestrict e.inv).hom.app ((restrictAlgebra e.hom 𝒞).piece n)).val.app
      (op (e.inv ⁻¹ᵁ U))) h1).trans h2)).trans ?_
  refine (congrIdIso_hom_compIso_inv_app_apply e.inv e.hom e.inv_hom_id 𝒞 n _ _).trans ?_
  exact map_map_map_eq (𝒞.piece n) _ _ _ _ _

/-- **The restriction along `e` of the pullback along `e⁻¹` is the algebra itself.** -/
def restrictPullbackInvIso (𝒳 : SchemeGradedAlgebra X') :
    restrictAlgebra e.hom (pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳) ≅ 𝒳 :=
  restrictAlgebraMapIso e.hom (pullbackRestrictAlgebraIso e.inv 𝒳) ≪≫
    (restrictAlgebraCompIso e.hom e.inv 𝒳).symm ≪≫
    restrictAlgebraCongrIdIso (e.hom ≫ e.inv) e.hom_inv_id 𝒳

/-- `restrictPullbackInvIso` sends the restriction of the image of a section `s` back to `s`. -/
theorem restrictPullbackInvIso_hom_unit (𝒳 : SchemeGradedAlgebra X') (n : ℤ) (U : X'.Opens)
    (s : (𝒳.piece n).val.obj (op U)) :
    ((restrictPullbackInvIso e 𝒳).hom.app n).val.app (op U)
        (((pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳).piece n).val.map
          (homOfLE (image_le_inv_preimage e U)).op
          (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s)) = s := by
  show ((restrictAlgebraCongrIdIso (e.hom ≫ e.inv) e.hom_inv_id 𝒳).hom.app n).val.app (op U)
      (((restrictAlgebraCompIso e.hom e.inv 𝒳).inv.app n).val.app (op U)
        (((pullbackIsoRestrict e.inv).hom.app (𝒳.piece n)).val.app (op (e.hom ''ᵁ U))
          (((pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳).piece n).val.map
            (homOfLE (image_le_inv_preimage e U)).op
            (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s)))) = s
  have hnat := PresheafOfModules.naturality_apply
    ((pullbackIsoRestrict e.inv).hom.app (𝒳.piece n)).val
    (homOfLE (image_le_inv_preimage e U)).op
    (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s)
  have h2 := pullbackIsoRestrict_hom_pullbackUnit e.inv (𝒳.piece n) U s
  refine (congrArg (fun z => ((restrictAlgebraCongrIdIso (e.hom ≫ e.inv) e.hom_inv_id 𝒳).hom.app
      n).val.app (op U) (((restrictAlgebraCompIso e.hom e.inv 𝒳).inv.app n).val.app (op U) z))
    (hnat.trans (congrArg ((Scheme.Modules.restrict (𝒳.piece n) e.inv).val.map
      (homOfLE (image_le_inv_preimage e U)).op) h2))).trans ?_
  refine (congrIdIso_hom_compIso_inv_app_apply e.hom e.inv e.hom_inv_id 𝒳 n _ _).trans ?_
  exact map_map_map_map_self (𝒳.piece n) _ _ _ _ s

/-- `restrictPullbackInvIso`'s inverse: a section `s` goes to the restriction of its image. -/
theorem restrictPullbackInvIso_inv_app (𝒳 : SchemeGradedAlgebra X') (n : ℤ) (U : X'.Opens)
    (s : (𝒳.piece n).val.obj (op U)) :
    ((restrictPullbackInvIso e 𝒳).inv.app n).val.app (op U) s =
      ((pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳).piece n).val.map
        (homOfLE (image_le_inv_preimage e U)).op
        (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s) := by
  let J : (restrictAlgebra e.hom (pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳)).piece n ≅
      𝒳.piece n :=
    { hom := (restrictPullbackInvIso e 𝒳).hom.app n
      inv := (restrictPullbackInvIso e 𝒳).inv.app n
      hom_inv_id := congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
        (restrictPullbackInvIso e 𝒳).hom_inv_id
      inv_hom_id := congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
        (restrictPullbackInvIso e 𝒳).inv_hom_id }
  exact (congrArg (J.inv.val.app (op U)) (restrictPullbackInvIso_hom_unit e 𝒳 n U s)).symm.trans
    (TwistRigidity.iso_inv_app_hom_app J (op U) _)

/-- **A homomorphism `(e⁻¹)^*𝒳 ⟶ 𝒞`, restricted back along `e`**: a homomorphism
`𝒳 ⟶ e^{-1}𝒞`. -/
def restrictBack (α : pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳 ⟶ 𝒞) :
    𝒳 ⟶ restrictAlgebra e.hom 𝒞 :=
  (restrictPullbackInvIso e 𝒳).inv ≫ restrictAlgebraMap e.hom α

/-- **`restrictBack` on sections**: `α` applied to the restriction of the image of the section. -/
theorem restrictBack_app (α : pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳 ⟶ 𝒞) (n : ℤ)
    (U : X'.Opens) (s : (𝒳.piece n).val.obj (op U)) :
    ((restrictBack e α).app n).val.app (op U) s =
      (𝒞.piece n).val.map (homOfLE (image_le_inv_preimage e U)).op
        ((α.app n).val.app (op (e.inv ⁻¹ᵁ U))
          (pullbackUnit e.inv.toLRSHom.toShHom (𝒳.piece n) (op U) s)) := by
  show (α.app n).val.app (op (e.hom ''ᵁ U))
      (((restrictPullbackInvIso e 𝒳).inv.app n).val.app (op U) s) = _
  rw [restrictPullbackInvIso_inv_app]
  exact (PresheafOfModules.naturality_apply (α.app n).val _ _)

/-- **Every homomorphism out of `(e⁻¹)^*𝒳` is the pullback of its restriction back.** -/
theorem pullbackInvHom_restrictBack (α : pullbackGradedAlgebra e.inv.toLRSHom.toShHom 𝒳 ⟶ 𝒞) :
    pullbackInvHom e (restrictBack e α) = α := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    Stacks.PullbackTensorCoherence.pullback_hom_ext e.inv.toLRSHom.toShHom fun U s => ?_
  obtain ⟨U⟩ := U
  refine (pullbackInvHom_unit e (restrictBack e α) n U s).trans ?_
  refine (congrArg ((𝒞.piece n).val.map _) (restrictBack_app e α n U s)).trans ?_
  exact map_map_self (𝒞.piece n) _ _ _

end Iso

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
