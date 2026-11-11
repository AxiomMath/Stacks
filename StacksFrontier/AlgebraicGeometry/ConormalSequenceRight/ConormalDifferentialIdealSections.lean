module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalCompatibility
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion

/-!
# The first arrow of the conormal sequence on sections of the ideal sheaf

Let `i : Z ⟶ X` be an immersion of schemes over `S`, with ideal sheaf `ℐ_i ⊆ 𝒪_X`. The first arrow
`Stacks.ConormalSequenceRight.conormalDifferential i p : 𝒞_{Z/X} ⟶ i^*Ω_{X/S}` of the conormal
sequence of [Stacks, Tag 01UZ] is built through the factorization of `i` over its coborder
neighbourhood. This file reads it in the ambient scheme: preceded by the canonical quotient map
`ℐ_i ⟶ i_* 𝒞_{Z/X}` and pushed forward along `i`, it sends a section `y` of `ℐ_i` to
`1 ⊗ d y`, the image of the universal differential `d_{X/S} y` under the unit of `i^* ⊣ i_*`.

A morphism `τ₂ : i^*Ω_{X/S} ⟶ F` known only through its transpose `Ω_{X/S} ⟶ i_* F` can therefore
be evaluated on the composite `ℐ_i ⟶ i_* 𝒞_{Z/X} ⟶ i_* i^*Ω_{X/S} ⟶ i_* F`: it is the transpose
applied to `d y`.

The file also records that pushforward of modules along a preimmersion (in particular an
immersion) reflects isomorphisms, and deduces an isomorphism criterion for a morphism out of the
conormal sheaf of a first-order thickening: since `ℐ ⟶ i_* 𝒞` is then an isomorphism, a morphism
`τ : 𝒞 ⟶ F` is an isomorphism as soon as `ℐ ⟶ i_* 𝒞 ⟶ i_* F` is bijective on sections over every
open of `X`.

## Main definitions

* `Stacks.ConormalSequenceRight.idealConormalQuotientMap`: the canonical quotient map
  `ℐ_i ⟶ i_* 𝒞_{Z/X}`, with target the conormal sheaf
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i` on which the first arrow is defined.
* `Stacks.ConormalSequenceRight.idealSheafConormalDifferential`: the composite
  `ℐ_i ⟶ i_* 𝒞_{Z/X} ⟶ i_*(i^*Ω_{X/S})`.

## Main results

* `Stacks.ConormalSequenceRight.idealSheafConormalDifferential_val_app`: on a section `y` of `ℐ_i`,
  `idealSheafConormalDifferential i p` is `y ↦ 1 ⊗ d y`.
* `idealConormalQuotientMap_comp_map_conormalDifferential_comp_val_app`
  (in `Stacks.ConormalSequenceRight`): for `τ₂ : i^*Ω_{X/S} ⟶ F`, the composite with
  `i_*(conormalDifferential i p ≫ τ₂)` sends `y` to the transpose of `τ₂` applied to `d y`.
* `Stacks.ConormalSequenceRight.isIso_of_isIso_pushforward_map`: pushforward of modules along a
  preimmersion reflects isomorphisms;
  `Stacks.ConormalSequenceRight.reflectsIsomorphisms_pushforward` is the instance.
* `Stacks.ConormalSequenceRight.isIso_of_bijective_idealConormalQuotientMap_comp`: for a closed
  immersion with square-zero ideal, a morphism `τ` out of the conormal sheaf is an isomorphism when
  `ℐ ⟶ i_* 𝒞 ⟶ i_* F` is bijective on sections over every open.

## Implementation notes

The conormal sheaf has two presentations here:
`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i` (pullback of the sectionwise ideal of
the closed factor), on which the first arrow is defined, and
`Stacks.Conormal.conormalSheaf i` (pullback of the categorical kernel), which is reducibly the
target of `Stacks.Immersion.canonicalConormalQuotientMap`. They are not definitionally equal, and
`Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge` is the library isomorphism between them;
`idealConormalQuotientMap` inserts it. The section computation is
`Stacks.ConormalSequenceRight.conormalDifferential_canonicalConormalQuotientMap`.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

noncomputable section

namespace Stacks.ConormalSequenceRight

section IdealSections

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- **The canonical quotient map `ℐ_i ⟶ i_* 𝒞_{Z/X}`**, with target the conormal sheaf
`Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i` on which the first arrow of the
conormal sequence is defined: `Stacks.Immersion.canonicalConormalQuotientMap i` followed by the
pushforward of the identification `Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge` of
the two presentations of the conormal sheaf. -/
def idealConormalQuotientMap :
    Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom ⟶
      (modulePushforward i.toLRSHom.toShHom).obj
        (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i) :=
  Stacks.Immersion.canonicalConormalQuotientMap i ≫
    (modulePushforward i.toLRSHom.toShHom).map
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv

/-- **The first arrow of the conormal sequence, read on the ideal sheaf**: the composite
`ℐ_i ⟶ i_* 𝒞_{Z/X} ⟶ i_*(i^*Ω_{X/S})` of `idealConormalQuotientMap i` with the pushforward of
`conormalDifferential i p`. -/
def idealSheafConormalDifferential :
    Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom ⟶
      (modulePushforward i.toLRSHom.toShHom).obj
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) :=
  idealConormalQuotientMap i ≫
    (modulePushforward i.toLRSHom.toShHom).map (conormalDifferential i p)

/-- **The first arrow on sections of the ideal sheaf is `y ↦ 1 ⊗ d y`.** For a section `y` of the
ideal sheaf of `i` over an open `V` of `X`, `idealSheafConormalDifferential i p` sends `y` to the
image under the unit of `i^* ⊣ i_*` (in the
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` spelling) of the universal
differential of the underlying section of `𝒪_X`. -/
theorem idealSheafConormalDifferential_val_app (V : X.Opens)
    (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op V)) :
    ((idealSheafConormalDifferential i p).val.app (op V)).hom y =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Hom.relativeDifferentials p)).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d
          ((Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val.app (op V) y)) :=
  conormalDifferential_canonicalConormalQuotientMap i p V y

/-- **A morphism out of `i^*Ω_{X/S}`, composed with the first arrow, on sections of the ideal
sheaf.** For `τ₂ : i^*Ω_{X/S} ⟶ F` and a section `y` of the ideal sheaf of `i` over `V`, the
composite `ℐ_i ⟶ i_* 𝒞_{Z/X} ⟶ i_* F` of `idealConormalQuotientMap i` with the pushforward of
`conormalDifferential i p ≫ τ₂` sends `y` to the transpose `Ω_{X/S} ⟶ i_* F` of `τ₂` applied to
the universal differential of `y`. -/
theorem idealConormalQuotientMap_comp_map_conormalDifferential_comp_val_app {F : Z.Modules}
    (τ₂ : (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) ⟶ F)
    (V : X.Opens) (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op V)) :
    ((idealConormalQuotientMap i ≫ (modulePushforward i.toLRSHom.toShHom).map
        (conormalDifferential i p ≫ τ₂)).val.app (op V)).hom y =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _ τ₂).val.app
          (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d
          ((Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val.app (op V) y)) := by
  rw [Adjunction.homEquiv_unit]
  exact congrArg (fun m => (τ₂.val.app (op (i ⁻¹ᵁ V))).hom m)
    (idealSheafConormalDifferential_val_app i p V y)

end IdealSections

/-! ### Pushforward along a preimmersion reflects isomorphisms -/

section ReflectsIso

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsPreimmersion i]

/-- Every open of the source of a preimmersion is the preimage of an open of the target, since the
underlying map is an embedding. -/
theorem exists_preimage_eq_of_isPreimmersion (U : Z.Opens) : ∃ W : X.Opens, i ⁻¹ᵁ W = U := by
  obtain ⟨t, ht, hts⟩ := i.isEmbedding.isInducing.isOpen_iff.1 U.2
  exact ⟨⟨t, ht⟩, Opens.ext hts⟩

/-- **Pushforward of modules along a preimmersion reflects isomorphisms.** If `i_* τ` is an
isomorphism then so is `τ`: every open of `Z` is the preimage of an open of `X`, over which the
sections of `i_* τ` are those of `τ`. In particular this holds for every immersion. -/
theorem isIso_of_isIso_pushforward_map {M N : Z.Modules} (τ : M ⟶ N)
    (h : IsIso ((Scheme.Modules.pushforward i).map τ)) : IsIso τ := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun U => ?_
  obtain ⟨W, rfl⟩ := exists_preimage_eq_of_isPreimmersion i U
  exact (inferInstance : IsIso (((Scheme.Modules.pushforward i).map τ).app W))

/-- Pushforward of modules along a preimmersion reflects isomorphisms, as an instance. -/
instance reflectsIsomorphisms_pushforward :
    (Scheme.Modules.pushforward i).ReflectsIsomorphisms :=
  ⟨fun τ h => isIso_of_isIso_pushforward_map i τ h⟩

end ReflectsIso

/-! ### An isomorphism criterion out of the conormal sheaf of a first-order thickening -/

section Criterion

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- **A morphism out of the conormal sheaf of a first-order thickening is an isomorphism when it is
one on the ideal.** For a closed immersion `i` with `i.ker ^ 2 = ⊥` and
`τ : 𝒞_{Z/X} ⟶ F`, if the composite `ℐ ⟶ i_* 𝒞_{Z/X} ⟶ i_* F` of `idealConormalQuotientMap i`
with `i_* τ` is bijective on sections over every open of `X`, then `τ` is an isomorphism: the
composite is then an isomorphism, the quotient map is one
(`Stacks.Thickenings.isIso_canonicalConormalQuotientMap`), and pushforward along `i` reflects
isomorphisms. -/
theorem isIso_of_bijective_idealConormalQuotientMap_comp [IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) {F : Z.Modules}
    (τ : (Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf i : Z.Modules) ⟶ F)
    (h : ∀ V : X.Opens, Function.Bijective
      ((idealConormalQuotientMap i ≫ (modulePushforward i.toLRSHom.toShHom).map τ).val.app
        (op V)).hom) :
    IsIso τ := by
  have hφ : IsIso (idealConormalQuotientMap i ≫ (modulePushforward i.toLRSHom.toShHom).map τ) :=
    Stacks.SheafOfModules.isIso_of_bijective_app _ fun V => h V.unop
  have hq := Stacks.Thickenings.isIso_canonicalConormalQuotientMap i hsq
  have e : (modulePushforward i.toLRSHom.toShHom).map
        ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫ τ) =
      inv (Stacks.Immersion.canonicalConormalQuotientMap i) ≫
        (idealConormalQuotientMap i ≫ (modulePushforward i.toLRSHom.toShHom).map τ) :=
    ((modulePushforward i.toLRSHom.toShHom).map_comp _ τ).trans
      ((IsIso.inv_hom_id_assoc (Stacks.Immersion.canonicalConormalQuotientMap i) _).symm.trans
        (congrArg (fun g => inv (Stacks.Immersion.canonicalConormalQuotientMap i) ≫ g)
          (Category.assoc _ _ _).symm))
  have hpush : IsIso ((modulePushforward i.toLRSHom.toShHom).map
      ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫ τ)) :=
    Eq.mpr (congrArg IsIso e) inferInstance
  have hτ' : IsIso ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫ τ) :=
    isIso_of_isIso_pushforward_map i _ hpush
  exact (IsIso.of_isIso_comp_left
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv τ)

end Criterion

end Stacks.ConormalSequenceRight

end
