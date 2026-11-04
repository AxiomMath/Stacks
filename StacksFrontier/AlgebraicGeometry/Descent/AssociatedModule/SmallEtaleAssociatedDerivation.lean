module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentials
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType

/-!
# The derivation `d^a` of Stacks 04CS on the small étale site

Let `f : X ⟶ Y` be a morphism of schemes and let `X` lie in a big étale site `B`.  The first
half of the proof of Stacks 04CS produces a `Y`-derivation

`d^a : 𝒪_{X_étale} ⟶ (Ω_{X/Y})^a`

of the structure sheaf of the small étale site of `X` with values in the associated module of
`Ω_{X/Y}`.  Its value over an object `h : T ⟶ X` of the site is the universal derivation
`d_{T/Y}`, read through the isomorphism `((Ω_{X/Y})^a)(T) ≅ Γ(T, h^*Ω_{X/Y}) ≅ Γ(T, Ω_{T/Y})`
whose second half is Stacks 04BX.

This module assembles those objectwise values into derivation data on the site.  The values and
their three objectwise properties are
`AlgebraicGeometry.etaleAssociatedDerivation` and its companions in
`StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/EtaleSectionsComparison.lean`; what is
added here is the indexing over the objects of `AlgebraicGeometry.SmallEtale`, for which the
coefficient sheaf is taken in the sections form
`AlgebraicGeometry.SmallEtale.associatedSectionsSheaf` of Stacks 070S (2) rather than as
`(Ω_{X/Y})^a` itself.

The base over which the derivation is taken here is the constant presheaf of commutative rings
`ℤ`, i.e. only the Leibniz rule is recorded, and the vanishing on the functions pulled back from
an open of `Y` is a separate statement.  That is the division of labour the rest of the
development already uses: `AlgebraicGeometry.SmallEtale.zariskiRestrictionData` carries a
derivation of `𝒪_{X_étale}` to the small Zariski site at an arbitrary base, and
`AlgebraicGeometry.SmallEtale.zariskiRestriction` is what adds the vanishing over `f⁻¹𝒪_Y`
there, by `AlgebraicGeometry.SheafOfModules.ofComorphism`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.siteConstIntPresheaf` and
  `AlgebraicGeometry.SmallEtale.siteConstIntMap` are the constant presheaf of commutative rings
  `ℤ` on the small étale site and its unique morphism to a presheaf of commutative rings.  They
  are the counterparts on a site of `AlgebraicGeometry.SheafOfModules.constIntPresheaf` and
  `AlgebraicGeometry.SheafOfModules.constIntMap`, which are stated for the opens of a space.
* `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation` is `d^a`, as derivation data on
  the small étale site with values in the sections form of `(Ω_{X/Y})^a`, and
  `AlgebraicGeometry.SmallEtale.associatedDerivation` is the same derivation with values in
  `(Ω_{X/Y})^a` itself, carried across the isomorphism of Stacks 070S (2).

## Main results

* `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation_d`: its value over an object of the
  site is `AlgebraicGeometry.etaleAssociatedDerivation` at the structure morphism.
* `AlgebraicGeometry.SmallEtale.associatedDerivation_pullbackSection_eq_zero`: `d^a` annihilates
  every function pulled back from an open of `Y`.  This is the hypothesis under which
  `AlgebraicGeometry.SmallEtale.differentialsComparison` produces the comparison map `c''` of
  Stacks 04CS, so `d^a` is now an admissible input to it.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), the étale localization
  of relative differentials.
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), part (2).
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Sites

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- The structure morphism of an object of the small étale site is étale.  This is
`AlgebraicGeometry.SmallEtale.etale_structureMorphism` at the spelling
`AlgebraicGeometry.SmallEtale.objHom` of that morphism, which is the spelling the
pullback-sections presheaf of Stacks 03DS is indexed by. -/
public instance etale_objHom (V : SmallEtale B X hX) : Etale (objHom B X hX V) := V.property

/-- The constant presheaf of commutative rings `ℤ` on the small étale site of `X`. -/
public noncomputable def siteConstIntPresheaf : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (CommRingCat.of (ULift.{u} ℤ))

/-- The unique morphism from the constant presheaf of commutative rings `ℤ` on the small étale
site of `X` to a presheaf of commutative rings. -/
public noncomputable def siteConstIntMap (P : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}) :
    siteConstIntPresheaf B hX ⟶ P where
  app V := CommRingCat.ofHom
    ((Int.castRingHom (P.obj V)).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)
  naturality V V' i := by
    ext n
    change ((n.down : ℤ) : P.obj V') = (P.map i).hom ((n.down : ℤ) : P.obj V)
    exact (map_intCast (P.map i).hom _).symm

/-- An additive map annihilating `1` annihilates the image of every section of the constant
presheaf of commutative rings `ℤ`, since such a section is an integer multiple of `1`. -/
public theorem siteConstIntMap_app_eq_zero {P : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
    {V : (SmallEtale B X hX)ᵒᵖ} {A : Type*} [AddCommGroup A] (d : (P.obj V) →+ A)
    (hone : d 1 = 0) (a : (siteConstIntPresheaf B hX).obj V) :
    d ((siteConstIntMap B hX P).app V a) = 0 := by
  show d (((a.down : ℤ) : P.obj V)) = 0
  rw [show ((a.down : ℤ) : P.obj V) = a.down • (1 : P.obj V) by simp [zsmul_eq_mul],
    AddMonoidHom.map_zsmul, hone, smul_zero]

/-- **The derivation `d^a` of Stacks 04CS, as derivation data on the small étale site of `X`.**
Over an object `h : T ⟶ X` of the site its value is the universal `Y`-derivation `d_{T/Y}` read
through the isomorphism of Stacks 04BX, and the three conditions are the Leibniz rule and the
compatibility with restriction of those values.

The base recorded here is the constant presheaf `ℤ`; the vanishing over `f⁻¹𝒪_Y` is proved
separately, by restricting this derivation to the small Zariski site of `X`. -/
public noncomputable def associatedSectionsDerivation :
    PresheafOfModules.Derivation' (R := (commRingStructureSheaf B X hX).obj)
      (associatedSectionsSheaf B X hX (Scheme.Hom.relativeDifferentials f)).val
      (siteConstIntMap B hX _) where
  d {V} := etaleAssociatedDerivation f (objHom B X hX V.unop)
  d_mul {V} a b := etaleAssociatedDerivation_mul f (objHom B X hX V.unop) a b
  d_map {V W} g x :=
    etaleAssociatedDerivation_naturality f ((toScheme B X hX).map g.unop)
      (objHom B X hX V.unop) (objHom B X hX W.unop) (Over.w ((toOver B X hX).map g.unop)) x
  d_app {V} a :=
    siteConstIntMap_app_eq_zero (P := (commRingStructureSheaf B X hX).obj) B hX
      (etaleAssociatedDerivation f (objHom B X hX V.unop))
      (etaleAssociatedDerivation_one f (objHom B X hX V.unop)) a

/-- The value of `d^a` over an object of the small étale site of `X` is the universal
derivation `d_{T/Y}` read through the isomorphism of Stacks 04BX. -/
@[simp]
public theorem associatedSectionsDerivation_d (V : (SmallEtale B X hX)ᵒᵖ)
    (a : (commRingStructureSheaf B X hX).obj.obj V) :
    (associatedSectionsDerivation B hX f).d a =
      etaleAssociatedDerivation f (objHom B X hX V.unop) a :=
  rfl

/-- **`d^a` annihilates every function pulled back from an open of `Y`.**  Over the object
`f⁻¹W` of the small étale site the section `AlgebraicGeometry.SmallEtale.pullbackSection` is the
image of `Γ(Y, W)` under the comorphism of the structure morphism of that object, so this is
`AlgebraicGeometry.etaleAssociatedDerivation_appLE_eq_zero`.

This is the hypothesis `hD` of
`AlgebraicGeometry.SmallEtale.differentialsComparison`, discharged for `d^a`. -/
public theorem associatedSectionsDerivation_pullbackSection_eq_zero (W : Y.Opens) (b : Γ(Y, W)) :
    (associatedSectionsDerivation B hX f).d (pullbackSection B hX f W b) = 0 := by
  have hι : (⊤ : (f ⁻¹ᵁ W).toScheme.Opens) ≤ (f ⁻¹ᵁ W).ι ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    simp [Scheme.Opens.ι_preimage_self]
  refine Eq.trans ?_ (etaleAssociatedDerivation_appLE_eq_zero f (f ⁻¹ᵁ W).ι W hι b)
  refine congrArg (etaleAssociatedDerivation f (f ⁻¹ᵁ W).ι) ?_
  show ((Scheme.Opens.topIso (f ⁻¹ᵁ W)).inv).hom ((Scheme.Hom.app f W).hom b) = _
  rw [← Scheme.Opens.ι_appLE_top (f ⁻¹ᵁ W) hι, ← ConcreteCategory.comp_apply,
    ← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE]

/-- **The derivation `d^a : 𝒪_{X_étale} ⟶ (Ω_{X/Y})^a` of Stacks 04CS.**  The derivation data
of `AlgebraicGeometry.SmallEtale.associatedSectionsDerivation`, carried from the sections form
of the associated module to the associated module itself along the isomorphism of
Stacks 070S (2). -/
public noncomputable def associatedDerivation :
    PresheafOfModules.Derivation' (R := (commRingStructureSheaf B X hX).obj)
      (associatedRelativeDifferentials B hX f).val (siteConstIntMap B hX _) :=
  (associatedSectionsDerivation B hX f).postcomp
    (associatedModuleIsoSectionsSheaf B X hX (Scheme.Hom.relativeDifferentials f)).inv.val

/-- **`d^a` annihilates every function pulled back from an open of `Y`.**  This is the
hypothesis under which `AlgebraicGeometry.SmallEtale.differentialsComparison` produces the
comparison map of Stacks 04CS, discharged for `d^a`. -/
public theorem associatedDerivation_pullbackSection_eq_zero (W : Y.Opens) (b : Γ(Y, W)) :
    (associatedDerivation B hX f).d (pullbackSection B hX f W b) = 0 :=
  postcomp_pullbackSection_eq_zero B hX f (associatedSectionsDerivation B hX f)
    (associatedSectionsDerivation_pullbackSection_eq_zero B hX f) _ W b

end AlgebraicGeometry.SmallEtale

end
