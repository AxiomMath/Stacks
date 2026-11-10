module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentials
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.PullbackCompUnit

/-!
# The derivation into the associated module of differentials

Let `f : X ⟶ Y` be a morphism of schemes.  Stacks 04CS compares the small-étale sheaf
`(Ω_{X/Y})^a` associated to the quasi-coherent module `Ω_{X/Y}` with the module of differentials
of the induced morphism of small étale sites.  The proof of the source runs in two directions.
One of them, the comparison map `c''` out of `(Ω_{X/Y})^a`, is
`AlgebraicGeometry.SmallEtale.differentialsComparison`.  The other starts from the observation
that an étale morphism does not change relative differentials, Stacks 04BX, so that the sections
of `(Ω_{X/Y})^a` over an object `h : T → X` of the small étale site are the global sections of
`Ω_{T/Y}`; reading the universal derivation `d_{T/Y}` through that identification gives a
derivation of the structure sheaf of the small étale site valued in `(Ω_{X/Y})^a`.  That
derivation is what this module constructs.

Stacks 03DU (4) names the associated module by its sections, `(g : T → S) ↦ Γ(T, g^*𝓕)`.  That
this agrees with the pullback of sheaves of modules along the morphism of ringed sites is
Stacks 070S (2), and the resulting identification `𝓕^a ≅ (g : T → S) ↦ Γ(T, g^*𝓕)` is
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules'` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleLocalBijectivity.lean`.  The
sections description is therefore unconditional, and the derivation is built on it and
transported.

## Main definitions

* `AlgebraicGeometry.SmallEtale.differentialsEtaleComparison` is the canonical map
  `h^*Ω_{X/Y} ⟶ Ω_{T/Y}` of an object `h : T → X` of the small étale site, an isomorphism by
  Stacks 04BX.
* `AlgebraicGeometry.SmallEtale.sectionsDerivationHom` is the universal derivation `d_{T/Y}`
  read through that isomorphism, as an additive map on sections over `T`, and
  `AlgebraicGeometry.SmallEtale.sectionsDerivation` assembles these into a derivation of the
  structure sheaf of the small étale site.
* `AlgebraicGeometry.SmallEtale.associatedRelativeDifferentialsDerivation` is that derivation
  transported to `(Ω_{X/Y})^a`.
* `Stacks.Sites.constIntPresheaf` and `Stacks.Sites.constIntMap` are the constant presheaf of
  commutative rings `ℤ` on a category and its map to any presheaf of commutative rings, the
  relative structure against which an absolute derivation on a site is taken.

## Main results

* `AlgebraicGeometry.SmallEtale.differentialsEtaleComparison_sectionsDerivationHom`
  characterizes the derivation: the canonical map of Stacks 04BX carries it to the universal
  derivation `d_{T/Y}`.  Everything else about it is proved from this together with the
  injectivity of that map on global sections.
* `AlgebraicGeometry.SmallEtale.sectionsDerivationHom_map` is the compatibility with the
  restriction maps of the small étale site, which is what makes the family a derivation.

## Implementation notes

The derivation is taken relative to the constant presheaf of integers, as
`AlgebraicGeometry.SmallEtale.zariskiRestrictionData` is: that is the weakest relative structure,
so the resulting object is a derivation for every stronger one, and the vanishing on the
functions pulled back from `Y` is a separate statement about it rather than part of its type.

The compatibility with restriction is the only part that is not formal.  It is the composition
law for the canonical maps of Stacks 01UV along the *source*,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_top_pullbackSectionsMap`, which is
proved in `StacksFrontier/AlgebraicGeometry/Morphisms/Differentials/PullbackCompUnit.lean`.  The
composition law along the *base* that this library already had,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_comp`, does not apply, and the uniqueness
characterization of Stacks 01UV cannot be used for it either: the characterization of the
canonical map of the outer square unfolds to exactly the identity to be proved.

Every statement about the derivation is reduced to the characterization
`differentialsEtaleComparison_sectionsDerivationHom` by
`AlgebraicGeometry.SmallEtale.differentialsEtaleComparison_app_injective`, rather than by
unfolding the inverse of the canonical map.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), that an étale morphism
  of the source and of the base does not change relative differentials.
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map on
  relative differentials of a commutative square.
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS) and
  [Tag 03DT](https://stacks.math.columbia.edu/tag/03DT), the sections presheaf and that it is a
  sheaf.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module
  on the small site, and [Tag 070S](https://stacks.math.columbia.edu/tag/070S), that it is
  computed by the sections formula.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v₁ u₁

namespace Stacks.Sites

/-- The constant presheaf of commutative rings `ℤ` on a category.  An absolute derivation of a
presheaf of commutative rings is a derivation relative to this one. -/
public noncomputable def constIntPresheaf (C : Type u₁) [Category.{v₁} C] :
    Cᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (CommRingCat.of (ULift.{u} ℤ))

/-- The unique map of presheaves of commutative rings from the constant presheaf of integers. -/
public noncomputable def constIntMap {C : Type u₁} [Category.{v₁} C]
    (P : Cᵒᵖ ⥤ CommRingCat.{u}) : constIntPresheaf.{u} C ⟶ P where
  app W := CommRingCat.ofHom
    ((Int.castRingHom (P.obj W)).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)
  naturality W W' i := by
    ext n
    change ((n.down : ℤ) : P.obj W') = (P.map i).hom ((n.down : ℤ) : P.obj W)
    exact (map_intCast (P.map i).hom _).symm

/-- An additive map killing `1` kills every integer, so the vanishing condition of a derivation
relative to the constant presheaf of integers is no condition beyond the Leibniz rule. -/
public theorem constIntMap_app_eq_zero {C : Type u₁} [Category.{v₁} C]
    {P : Cᵒᵖ ⥤ CommRingCat.{u}} {W : Cᵒᵖ} {A : Type*} [AddCommGroup A] (d : (P.obj W) →+ A)
    (hone : d 1 = 0) (a : (constIntPresheaf.{u} C).obj W) :
    d ((constIntMap P).app W a) = 0 := by
  change d (((a.down : ℤ) : P.obj W)) = 0
  rw [show ((a.down : ℤ) : P.obj W) = a.down • (1 : P.obj W) by simp [zsmul_eq_mul],
    AddMonoidHom.map_zsmul, hone, smul_zero]

end Stacks.Sites

namespace AlgebraicGeometry.SmallEtale

open AlgebraicGeometry.Scheme.Hom Stacks.Sites

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small étale sheafification of the sections presheaf is the sections presheaf itself, the
sections presheaf being a sheaf.  This is the last factor of
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules'`, in the form that
exhibits it as the inverse of the unit of sheafification. -/
public noncomputable def sheafificationSectionsIso (F : S.Modules) [F.IsQuasicoherent] :
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
        (sectionsPresheafOfModules B S hS F) ≅ sectionsSheafOfModules' B S hS F :=
  (SheafOfModules.fullyFaithfulForget (structureSheaf B S hS)).preimageIso
    (@asIso _ _ _ _ _ (isIso_sheafificationAdjunction_unit_app B S hS
      (sectionsPresheafOfModules B S hS F)
      (isSheaf_sectionsPresheafOfModules B S hS F))).symm

/-! ### The comparison of differentials along an object of the small étale site -/

variable {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- The canonical map `h^*Ω_{X/Y} ⟶ Ω_{T/Y}` of Stacks 01UV attached to an object `h : T → X`
of the small étale site of `X` and the morphism `f : X ⟶ Y`. -/
public noncomputable def differentialsEtaleComparison (T : SmallEtale B X hX) :
    (Scheme.Modules.pullback ((toOver B X hX).obj T).hom).obj (relativeDifferentials f) ⟶
      relativeDifferentials (((toOver B X hX).obj T).hom ≫ f) :=
  relativeDifferentialsMap ((toOver B X hX).obj T).hom f
    (((toOver B X hX).obj T).hom ≫ f) (𝟙 Y) (Category.comp_id _).symm

/-- **Stacks 04BX on the small étale site.**  The canonical map `h^*Ω_{X/Y} ⟶ Ω_{T/Y}` of an
object of the small étale site of `X` is an isomorphism, the structure morphism of such an
object being étale. -/
public instance isIso_differentialsEtaleComparison (T : SmallEtale B X hX) :
    IsIso (differentialsEtaleComparison B hX f T) := by
  have : Etale ((toOver B X hX).obj T).hom := T.property
  exact isIso_relativeDifferentialsMap_of_comp ((toOver B X hX).obj T).hom f

/-- The canonical map of Stacks 04BX is injective on global sections, being an isomorphism. -/
public theorem differentialsEtaleComparison_app_injective (T : SmallEtale B X hX) :
    Function.Injective
      (Scheme.Modules.Hom.app (differentialsEtaleComparison B hX f T) ⊤) := by
  exact (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (differentialsEtaleComparison B hX f T) ⊤)).1

/-! ### The derivation -/

/-- The universal derivation `d_{T/Y}` of an object `h : T → X` of the small étale site of `X`,
read as a map into the global sections of `h^*Ω_{X/Y}` through the isomorphism of Stacks 04BX.
This is the value over `T` of the derivation `d^a` of the source's proof of Stacks 04CS. -/
public noncomputable def sectionsDerivationHom (T : SmallEtale B X hX) :
    (commRingStructureSheaf B X hX).obj.obj (op T) →+
      (sectionsPresheafOfModules B X hX (relativeDifferentials f)).obj (op T) :=
  (Scheme.Modules.Hom.app (inv (differentialsEtaleComparison B hX f T)) ⊤).hom.comp
    ((universalRelativeDerivation (((toOver B X hX).obj T).hom ≫ f)).d
      (X := op (⊤ : (((toOver B X hX).obj T).left).Opens)))

/-- **The characterization of `d^a` over an object of the small étale site.**  The canonical map
of Stacks 04BX carries it to the universal derivation `d_{T/Y}`. -/
public theorem differentialsEtaleComparison_sectionsDerivationHom (T : SmallEtale B X hX)
    (a : (commRingStructureSheaf B X hX).obj.obj (op T)) :
    Scheme.Modules.Hom.app (differentialsEtaleComparison B hX f T) ⊤
        (sectionsDerivationHom B hX f T a) =
      (universalRelativeDerivation (((toOver B X hX).obj T).hom ≫ f)).d
        (X := op (⊤ : (((toOver B X hX).obj T).left).Opens)) a := by
  rw [sectionsDerivationHom, Scheme.Modules.inv_app]
  exact IsIso.inv_hom_id_apply _ _

/-- **`d^a` is compatible with the restriction maps of the small étale site.**  This is the
composition law for the canonical maps of Stacks 01UV along the source, together with the
injectivity of the canonical map of the target object on global sections. -/
public theorem sectionsDerivationHom_map {T T' : SmallEtale B X hX} (g : T' ⟶ T)
    (a : (commRingStructureSheaf B X hX).obj.obj (op T)) :
    sectionsDerivationHom B hX f T' ((commRingStructureSheaf B X hX).obj.map g.op a) =
      (sectionsPresheafOfModules B X hX (relativeDifferentials f)).map g.op
        (sectionsDerivationHom B hX f T a) := by
  refine differentialsEtaleComparison_app_injective B hX f T' ?_
  rw [differentialsEtaleComparison_sectionsDerivationHom]
  exact (relativeDifferentialsMap_app_top_pullbackSectionsMap f ((toOver B X hX).map g)
    (sectionsDerivationHom B hX f T a) a
    (differentialsEtaleComparison_sectionsDerivationHom B hX f T a)).symm

/-- **The derivation `d^a` of the source's proof of Stacks 04CS**, on the sections description of
the associated module: the derivation of the structure sheaf of the small étale site of `X`
which over an object `h : T → X` is the universal derivation `d_{T/Y}`, read through the
isomorphism `h^*Ω_{X/Y} ≅ Ω_{T/Y}` of Stacks 04BX. -/
public noncomputable def sectionsDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj)
      (sectionsPresheafOfModules B X hX (relativeDifferentials f))
      (constIntMap (commRingStructureSheaf B X hX).obj) where
  d {T} := sectionsDerivationHom B hX f T.unop
  d_mul {T} a b := by
    change Scheme.Modules.Hom.app
        (inv (differentialsEtaleComparison B hX f T.unop)) ⊤
        ((universalRelativeDerivation (((toOver B X hX).obj T.unop).hom ≫ f)).d (a * b)) = _
    refine Eq.trans (congrArg
      (fun y => Scheme.Modules.Hom.app
        (inv (differentialsEtaleComparison B hX f T.unop)) ⊤ y)
      ((universalRelativeDerivation (((toOver B X hX).obj T.unop).hom ≫ f)).d_mul a b)) ?_
    refine Eq.trans ((ConcreteCategory.hom (Scheme.Modules.Hom.app
      (inv (differentialsEtaleComparison B hX f T.unop)) ⊤)).map_add _ _) ?_
    refine congrArg₂ (· + ·) ?_ ?_ <;>
      exact Scheme.Modules.Hom.app_smul (inv (differentialsEtaleComparison B hX f T.unop)) _ _
  d_map {T T'} g x := sectionsDerivationHom_map B hX f g.unop x
  d_app {T} a := by
    refine constIntMap_app_eq_zero (sectionsDerivationHom B hX f T.unop) ?_ a
    change Scheme.Modules.Hom.app
        (inv (differentialsEtaleComparison B hX f T.unop)) ⊤
        ((universalRelativeDerivation (((toOver B X hX).obj T.unop).hom ≫ f)).d 1) = 0
    exact (congrArg (fun y => Scheme.Modules.Hom.app
      (inv (differentialsEtaleComparison B hX f T.unop)) ⊤ y)
      ((universalRelativeDerivation (((toOver B X hX).obj T.unop).hom ≫ f)).d_one _)).trans
      (AddMonoidHom.map_zero _)

/-- **The derivation `d^a` of the source's proof of Stacks 04CS**, on `(Ω_{X/Y})^a` itself:
`AlgebraicGeometry.SmallEtale.sectionsDerivation` transported along the identification of the
associated module with its sections description. -/
@[stacks 04CS "the derivation `d^a` into the associated module of differentials"]
public noncomputable def associatedRelativeDifferentialsDerivation :
    PresheafOfModulesOfCommRing.Derivation' (R := (commRingStructureSheaf B X hX).obj)
      (associatedRelativeDifferentials B hX f).val
      (constIntMap (commRingStructureSheaf B X hX).obj) :=
  (sectionsDerivation B hX f).postcomp
    (associatedModuleIsoSectionsSheafOfModules' B X hX (relativeDifferentials f)).inv.val

end AlgebraicGeometry.SmallEtale

end
