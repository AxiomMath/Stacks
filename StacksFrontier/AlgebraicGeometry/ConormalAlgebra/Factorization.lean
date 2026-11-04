module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.RestrictIdealSheaf
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 01R3 (1): the conormal sheaf is the pullback of the ideal sheaf of any factorization

[Stacks, Tag 01R2] defines the conormal sheaf of an immersion `i : Z ⟶ X` using one particular
closed-immersion factorization, the canonical one
`i = i.liftCoborder ≫ i.coborderRange.ι` through `AlgebraicGeometry.Scheme.Hom.coborderRange`.
Part (1) of [Stacks, Tag 01R3] says that *every* factorization `i = i' ≫ U.ι` of `i` as a closed
immersion into an open subscheme computes the same sheaf: `𝒞_{Z/X} = (i')^* ℐ`, where
`ℐ = Ker((i')^♯)`.  That comparison is
`Stacks.Conormal.conormalSheafIsoPullbackIdealSheaf`, which this file takes from
`StacksFrontier.AlgebraicGeometry.ConormalComparison.IdealSheafComparison`; what is proved here is
the affine form `i'_* 𝒞_{Z/X} = ℐ/ℐ²` of part (1) and the surjectivity and kernel of the
canonical quotient map.

The geometric input is that `U` is then contained in `i.coborderRange` — the coborder is the
*largest* open in which the image of `i` is closed — so that the two factorizations are related
by the open immersion `X.homOfLE : U.toScheme ⟶ i.coborderRange.toScheme`.

## Main definitions

* `Stacks.Conormal.pushforwardConormalIsoCotangent`: **Tag 01R3 (1)**, on an affine open `V` of
  the subscheme `U` through which the immersion factors, the sections over `V` of the direct
  image of the conormal sheaf are `I/I²`.  This is the `i'_* 𝒞_{Z/X} = ℐ/ℐ²` half of part (1),
  read on affine opens.

## Main results

* `Stacks.Conormal.conormalQuotientMap_app_surjective`: the canonical quotient map
  `ℐ ⟶ i'_* 𝒞_{Z/X}` is surjective on the sections over an affine open.

## Implementation notes

`Stacks.Conormal.le_coborderRange_of_isClosedImmersion_morphismRestrict` already states the
geometric fact for the *restriction* `i ∣_ U`, so the only work here is to see that `i ∣_ U` is
a closed immersion: `i ⁻¹ᵁ U = ⊤` because `i` factors through `U`, hence `(i ⁻¹ᵁ U).ι` is an
isomorphism, and `i ∣_ U = (i ⁻¹ᵁ U).ι ≫ i'` by cancelling the monomorphism `U.ι`.

`Stacks.Conormal.pushforwardConormalIsoCotangent` is obtained by transporting the sections
along part (1) and then applying `Stacks.Conormal.affineIdealPullbackIsoCotangent`, the affine
computation for a closed immersion, to `i'` directly.  No second factorization is compared:
once part (1) has replaced `i.liftCoborder` by `i'`, the ambient scheme is `U.toScheme` and `i'`
is a closed immersion into it, so the affine computation applies on the nose.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction Opposite

universe u

namespace Stacks.SheafOfModules

/-- The sections over a fixed open of an isomorphism of sheaves of modules.

This is no new notion: it is `rfl`-equal to
`(CategoryTheory.SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.val W).mapIso e`.
It exists only to keep the transport proofs below readable, where the isomorphism appears four
times inside a single `change`. -/
def valObjIso {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (e : M ≅ N) (W : Cᵒᵖ) :
    M.val.obj W ≅ N.val.obj W where
  hom := e.hom.val.app W
  inv := e.inv.val.app W
  hom_inv_id := by
    change (e.hom ≫ e.inv).val.app W = _
    rw [e.hom_inv_id]; rfl
  inv_hom_id := by
    change (e.inv ≫ e.hom).val.app W = _
    rw [e.inv_hom_id]; rfl

end Stacks.SheafOfModules

namespace Stacks.Conormal

/-- An isomorphism of modules is injective on elements.  Used to read an identity between two
sections off an identity between their images under one of the affine identifications. -/
theorem injective_moduleIso_hom {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (F : M ≅ N) :
    Function.Injective F.hom.hom := fun p q h => by
  rw [← F.hom_inv_id_apply p, ← F.hom_inv_id_apply q, h]

/-! ### Tag 01R3, part (1) -/

/-- **The affine form of `i'_* 𝒞_{Z/X} = ℐ/ℐ²`**, with the ring-level data of the affine open
supplied directly instead of through an affine model.  Part (1) replaces the conormal sheaf by
`(i')^* ℐ`, after which this is `Stacks.Conormal.affineIdealPullbackIsoCotangent` for the closed
immersion `i'`. -/
noncomputable def factoredPushforwardConormalIsoCotangent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (hVpre : IsAffineOpen (i' ⁻¹ᵁ V)) (hsurj : Function.Surjective (i'.app V).hom)
    (I : Ideal Γ(U.toScheme, V)) (hker : RingHom.ker (i'.app V).hom = I) :
    ((modulePushforward i'.toLRSHom.toShHom).obj (conormalSheaf i)).val.obj (op V) ≅
      ModuleCat.of Γ(U.toScheme, V) I.Cotangent :=
  Stacks.SheafOfModules.valObjIso
      ((modulePushforward i'.toLRSHom.toShHom).mapIso
        (conormalSheafIsoPullbackIdealSheaf i U i' hfac)) (op V) ≪≫
    affineIdealPullbackIsoCotangent i' V hV hVpre hsurj ≪≫
    (Ideal.Cotangent.equivOfEq _ _ hker).toModuleIso

/-- **The affine form of `i'_* 𝒞_{Z/X} = ℐ/ℐ²` sends the canonical quotient of a section of the
ideal sheaf to its class modulo the square of the ideal.**  Since the quotient map is
surjective on these affine sections — `Ideal.toCotangent` is — this determines the
isomorphism. -/
@[sga "7 XVII 3.1" "partial"]
theorem factoredPushforwardConormalIsoCotangent_apply {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (hVpre : IsAffineOpen (i' ⁻¹ᵁ V)) (hsurj : Function.Surjective (i'.app V).hom)
    (I : Ideal Γ(U.toScheme, V)) (hker : RingHom.ker (i'.app V).hom = I)
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i'.toLRSHom.toShHom))).val.app (op V) x ∈ I) :
    (factoredPushforwardConormalIsoCotangent i U i' hfac V hV hVpre hsurj I hker).hom.hom
        ((conormalQuotientMap i U i' hfac).val.app (op V) x) =
      I.toCotangent ⟨(kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (op V) x, hx⟩ := by
  set E := Stacks.SheafOfModules.valObjIso
    ((modulePushforward i'.toLRSHom.toShHom).mapIso
      (conormalSheafIsoPullbackIdealSheaf i U i' hfac)) (op V)
  have hcancel : E.hom.hom (E.inv.hom (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
      (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)).val.app (op V) x)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
        (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)).val.app (op V) x :=
    E.inv_hom_id_apply _
  change (Ideal.Cotangent.equivOfEq _ I hker)
      ((affineIdealPullbackIsoCotangent i' V hV hVpre hsurj).hom.hom
        (E.hom.hom (E.inv.hom (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
          (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom)).val.app (op V) x)))) = _
  rw [hcancel, ← pullbackSection_self i'
      (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom) V x,
    affineIdealPullbackIsoCotangent_hom_pullbackSection i' V hV hVpre hsurj x,
    Ideal.Cotangent.equivOfEq_toCotangent]
  exact congrArg I.toCotangent (Subtype.ext (idealSheafSectionsIso_hom_coe i' V x))

/-- **[Stacks, Tag 01R3] (1), the affine form of `i'_* 𝒞_{Z/X} = ℐ/ℐ²`.**  Let `i : Z ⟶ X` be an
immersion factored as a closed immersion `i' : Z ⟶ U` into an open subscheme, let `V ⊆ U` be an
affine open, and suppose `Z ∩ V = Spec (Γ(U, V) ⧸ I)` over `V`.  Then the sections over `V` of
the direct image along `i'` of the conormal sheaf are canonically `I/I²`.

Part (1) identifies the conormal sheaf with `(i')^* ℐ`, after which this is
`Stacks.Conormal.affineIdealPullbackIsoCotangent` for the closed immersion `i'` — the
ring-theoretic content `I ⊗_R R/I = I/I²` — with the kernel of the map on sections identified
with `I` by the affine model. -/
@[stacks 01R3 "part (1): pushforward is the ideal modulo its square"]
noncomputable def pushforwardConormalIsoCotangent {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(U.toScheme, V))
    (e : CategoryTheory.Limits.pullback i' V.ι ≅ Spec (.of (Γ(U.toScheme, V) ⧸ I)))
    (he : CategoryTheory.Limits.pullback.snd i' V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ((modulePushforward i'.toLRSHom.toShHom).obj (conormalSheaf i)).val.obj (op V) ≅
      ModuleCat.of Γ(U.toScheme, V) I.Cotangent :=
  factoredPushforwardConormalIsoCotangent i U i' hfac V hV
    (isAffineOpen_preimage_of_affineModel i' V I e)
    (by rw [← Scheme.Hom.appLE_preimage_self i' V]
        exact surjective_appLE_of_affineModel i' V hV I e he) I
    (by rw [← Scheme.Hom.appLE_preimage_self i' V]
        exact ker_appLE_eq_of_affineModel i' V hV I e he)

/-- **[Stacks, Tag 01R3] (1), the normalization of the affine form of `i'_* 𝒞_{Z/X} = ℐ/ℐ²`.**
The isomorphism sends the canonical quotient of a section of the ideal sheaf to the class of
that section modulo `I²`.  Since `Ideal.toCotangent` is surjective this determines the
isomorphism, so it is the canonical one and not merely some isomorphism of the right type. -/
@[stacks 01R3 "part (1): canonical affine quotient formula"]
theorem pushforwardConormalIsoCotangent_apply {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i']
    (hfac : i' ≫ U.ι = i) (V : U.toScheme.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ(U.toScheme, V))
    (e : CategoryTheory.Limits.pullback i' V.ι ≅ Spec (.of (Γ(U.toScheme, V) ⧸ I)))
    (he : CategoryTheory.Limits.pullback.snd i' V.ι ≫ hV.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (x : (Stacks.ClosedImmersion.idealSheaf i'.toLRSHom.toShHom).val.obj (op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i'.toLRSHom.toShHom))).val.app (op V) x ∈ I) :
    (pushforwardConormalIsoCotangent i U i' hfac V hV I e he).hom.hom
        ((conormalQuotientMap i U i' hfac).val.app (op V) x) =
      I.toCotangent ⟨(kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom i'.toLRSHom.toShHom))).val.app (op V) x, hx⟩ :=
  factoredPushforwardConormalIsoCotangent_apply i U i' hfac V hV _ _ I _ x hx

/-! ### The affine data of a closed-immersion factorization -/

/-- The kernel of the map on sections over an affine open `V` of the subscheme through which the
immersion factors is `AlgebraicGeometry.Scheme.Hom.ker`'s ideal there.  This is Mathlib's
`AlgebraicGeometry.Scheme.Hom.ker_apply`, which applies because a closed immersion is
quasi-compact. -/
theorem ker_app_eq_kerIdeal {Z U : Scheme.{u}} (a : Z ⟶ U) [IsClosedImmersion a] (V : U.Opens)
    (hV : IsAffineOpen V) : RingHom.ker (a.app V).hom = a.ker.ideal ⟨V, hV⟩ :=
  (a.ker_apply ⟨V, hV⟩).symm

/-- A section of the ideal sheaf of a closed immersion lies in the ideal of
`AlgebraicGeometry.Scheme.Hom.ker` over an affine open. -/
theorem kernelι_mem_kerIdeal {Z U : Scheme.{u}} (a : Z ⟶ U) [IsClosedImmersion a] (V : U.Opens)
    (hV : IsAffineOpen V)
    (x : (Stacks.ClosedImmersion.idealSheaf a.toLRSHom.toShHom).val.obj (op V)) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom a.toLRSHom.toShHom))).val.app (op V) x ∈ a.ker.ideal ⟨V, hV⟩ := by
  rw [← ker_app_eq_kerIdeal a V hV, ← idealSheafSectionsIso_hom_coe a V x]
  exact ((idealSheafSectionsIso a V).hom.hom x).2

/-- **The canonical quotient map of [Stacks, Tag 01R3] (1) is surjective on the sections over an
affine open.**  The target is `I/I²` by
`Stacks.Conormal.factoredPushforwardConormalIsoCotangent`, `Ideal.toCotangent` is surjective,
and the quotient map hits exactly the classes of sections of the ideal sheaf. -/
theorem conormalQuotientMap_app_surjective {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i)
    (V : U.toScheme.Opens) (hV : IsAffineOpen V) :
    Function.Surjective ((conormalQuotientMap i U i' hfac).val.app (op V)) := by
  intro t
  set F := factoredPushforwardConormalIsoCotangent i U i' hfac V hV (hV.preimage i')
    (i'.app_surjective V hV) (i'.ker.ideal ⟨V, hV⟩) (ker_app_eq_kerIdeal i' V hV)
  obtain ⟨b, hb⟩ := Ideal.toCotangent_surjective (i'.ker.ideal ⟨V, hV⟩) (F.hom.hom t)
  have hbker : (b : Γ(U.toScheme, V)) ∈ RingHom.ker (i'.app V).hom := by
    rw [ker_app_eq_kerIdeal i' V hV]; exact b.2
  refine ⟨(idealSheafSectionsIso i' V).inv.hom ⟨(b : Γ(U.toScheme, V)), hbker⟩, ?_⟩
  have hcoe : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom i'.toLRSHom.toShHom))).val.app (op V)
        ((idealSheafSectionsIso i' V).inv.hom ⟨(b : Γ(U.toScheme, V)), hbker⟩) =
      (b : Γ(U.toScheme, V)) := by
    rw [← idealSheafSectionsIso_hom_coe i' V,
      (idealSheafSectionsIso i' V).inv_hom_id_apply ⟨(b : Γ(U.toScheme, V)), hbker⟩]
  refine injective_moduleIso_hom F ?_
  rw [factoredPushforwardConormalIsoCotangent_apply i U i' hfac V hV (hV.preimage i')
    (i'.app_surjective V hV) (i'.ker.ideal ⟨V, hV⟩) (ker_app_eq_kerIdeal i' V hV)
    ((idealSheafSectionsIso i' V).inv.hom ⟨(b : Γ(U.toScheme, V)), hbker⟩)
    (by rw [hcoe]; exact b.2), ← hb]
  exact congrArg (i'.ker.ideal ⟨V, hV⟩).toCotangent (Subtype.ext hcoe)

end Stacks.Conormal
