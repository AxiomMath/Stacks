module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.PowerTorsionDescent

/-!
# Power-torsion morphism groups and restriction to an open subspace

Let `X` be a topological space, `O` a sheaf of commutative rings on it and `U` an open subspace.
A global section `a` of `O` restricts to a global section `a|_U` of `𝒪_U`, and the two scalars
act on the two derived categories `D(𝒪_X)` and `D(𝒪_U)`. This file proves that restriction
`D(j^*)` is semilinear for that pair of scalars, and deduces that the property "every morphism
into `F` out of this object is killed by a power of `a`" is transported along the
adjunction `D(j_!) ⊣ D(j^*)`: a statement on `U` about `a|_U` becomes a statement on `X` about
`a`, with the extension by zero in the source. Combined with Mayer--Vietoris descent
(`Stacks.ExtensionByZero.homPowerTorsion_of_cover`), if `X = U ∪ V` and the property holds on
`U`, `V` and `U ∩ V` for the restricted morphism groups and the restricted scalar, then it holds
on `X`.

## Main definitions

* `Stacks.ExtensionByZero.restrictGlobalSection` and
  `Stacks.ExtensionByZero.restrictGlobalSectionHom`: restriction of a global section of `O` to
  the open subspace, and the ring homomorphism it defines.

## Main results

* `Stacks.ExtensionByZero.jStar_map_globalSmul`: restricting multiplication by `a` to `U` is
  multiplication by `a|_U`.
* `Stacks.ExtensionByZero.derivedRestriction_map_smul`: `D(j^*)` is semilinear over
  `Γ(X, 𝒪_X) ⟶ Γ(U, 𝒪_U)`.
* `Stacks.ExtensionByZero.homPowerTorsion_jShriek`: power torsion transfers from `U` to `X`
  across extension by zero.
* `Stacks.ExtensionByZero.homPowerTorsion_of_restrictions`: if `X = U ∪ V` and power torsion
  holds on `U`, `V` and `U ∩ V` for the restricted scalar, it holds on `X`.

## Implementation notes

The scalar is taken as an element of `Stacks.Cohomology.SiteModules.GlobalSectionRing O`, a
compatible family of sections over all the opens. For the site of opens of a space `⊤` is
terminal, so that ring is `Γ(X, 𝒪_X)`.

## References

* [Stacks Project, Tag 08EJ](https://stacks.math.columbia.edu/tag/08EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Opposite
open Stacks.Cohomology.SiteModules
open ExtensionByZeroModules
open scoped IsMulCommutative

universe u

namespace Stacks.Koszul.PowerLift

/-- Conjugating the scalar endomorphism `r • 𝟙` by an isomorphism gives the scalar endomorphism
of the other object. -/
public theorem smul_id_conj {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C]
    [Linear R C] {A B : C} (e : A ≅ B) (r : R) : e.inv ≫ (r • 𝟙 A) ≫ e.hom = r • 𝟙 B := by
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.inv_hom_id]

end Stacks.Koszul.PowerLift

namespace Stacks.ExtensionByZero

open Stacks.Koszul.PowerLift

attribute [local instance] HasDerivedCategory.standard jStar_preservesFiniteLimits
  jStar_preservesFiniteColimits

section Restrict

variable {X : TopCat.{u}} (U : Opens X) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The restriction of a global section of `O` to the open subspace `U`: a global section is a
compatible family of sections over all the opens of `X`, and its restriction is that family read
on the opens of `U`, through the image functor of the open embedding. -/
public def restrictGlobalSection (a : GlobalSectionRing O) : GlobalSectionRing (resRing U O) :=
  ⟨fun W => a.1 (op ((TopCat.Presheaf.imF U).obj W.unop)),
    fun {_ _} f => a.2 ((TopCat.Presheaf.imF U).op.map f)⟩

/-- Restriction of global sections to an open subspace, as a ring homomorphism: the ring
operations on both sides are computed open by open. -/
public def restrictGlobalSectionHom :
    GlobalSectionRing O →+* GlobalSectionRing (resRing U O) where
  toFun := restrictGlobalSection U O
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ring homomorphism `restrictGlobalSectionHom U O` sends a global section `a` to its
restriction `restrictGlobalSection U O a`. -/
@[simp]
public theorem restrictGlobalSectionHom_apply (a : GlobalSectionRing O) :
    restrictGlobalSectionHom U O a = restrictGlobalSection U O a := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for `map_pow` on the ring hom between the global section rings
/-- Restriction of global sections to `U` commutes with powers: `(a ^ k)|_U = (a|_U) ^ k`. -/
@[simp]
public theorem restrictGlobalSection_pow (a : GlobalSectionRing O) (k : ℕ) :
    restrictGlobalSection U O (a ^ k) = restrictGlobalSection U O a ^ k :=
  map_pow (restrictGlobalSectionHom U O) a k

variable [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)]

/-- The rings of sections of `𝒪_U` are rings of sections of `O`, so they are commutative with
`O`'s. -/
public instance resRing_isMulCommutative :
    ∀ W : (Opens (Usp U))ᵒᵖ, IsMulCommutative ((resRing U O).obj.obj W) :=
  fun W =>
    inferInstanceAs (IsMulCommutative (O.obj.obj (op ((TopCat.Presheaf.imF U).obj W.unop))))

/-- Restricting multiplication by a global section `a` to the open subspace `U` is
multiplication by the restricted section `a|_U`: over an open `W` of `U` both act as
multiplication by the section of `O` over the image of `W`. -/
public theorem jStar_map_globalSmul (a : GlobalSectionRing O) (M : SheafOfModules.{u} O) :
    (jStar U O).map (globalSmul O a M) =
      globalSmul (resRing U O) (restrictGlobalSection U O a) ((jStar U O).obj M) := by
  ext W x
  rfl

/-- `Stacks.ExtensionByZero.jStar_map_globalSmul` written with the scalar endomorphisms. -/
public theorem jStar_map_smul_id (a : GlobalSectionRing O) (M : SheafOfModules.{u} O) :
    (jStar U O).map (a • 𝟙 M) = restrictGlobalSection U O a • 𝟙 ((jStar U O).obj M) := by
  rw [← globalSmul_eq_smul_id, jStar_map_globalSmul, globalSmul_eq_smul_id]

/-- Restriction is semilinear degreewise on complexes. -/
public theorem mapHomologicalComplex_jStar_smul_id (a : GlobalSectionRing O)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).map (a • 𝟙 K) =
      restrictGlobalSection U O a • 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun i => by
    simpa using jStar_map_smul_id U O a (K.X i)

/-- Derived restriction takes the scalar endomorphism of an object in the image of the
localization functor to the restricted scalar endomorphism. -/
public theorem derivedRestriction_map_smul_id_Q (a : GlobalSectionRing O)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (derivedRestriction O U).map (a • 𝟙 (DerivedCategory.Q.obj K)) =
      restrictGlobalSection U O a • 𝟙 ((derivedRestriction O U).obj
        (DerivedCategory.Q.obj K)) := by
  have hnat := (jStar U O).mapDerivedCategoryFactors_hom_naturality (a • 𝟙 K)
  simp only [mapHomologicalComplex_jStar_smul_id, CategoryTheory.Functor.map_smul,
    CategoryTheory.Functor.map_id, Linear.comp_smul] at hnat
  refine (cancel_mono ((jStar U O).mapDerivedCategoryFactors.hom.app K)).1 ?_
  rw [hnat, Linear.smul_comp, Category.id_comp]
  exact congrArg _ (Category.comp_id _)

/-- Derived restriction takes the scalar endomorphism of any object to the restricted scalar
endomorphism. -/
public theorem derivedRestriction_map_smul_id (a : GlobalSectionRing O)
    (M : DerivedCategory (SheafOfModules.{u} O)) :
    (derivedRestriction O U).map (a • 𝟙 M) =
      restrictGlobalSection U O a • 𝟙 ((derivedRestriction O U).obj M) := by
  have e := DerivedCategory.Q.objObjPreimageIso M
  rw [← smul_id_conj e a, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    derivedRestriction_map_smul_id_Q]
  exact smul_id_conj ((derivedRestriction O U).mapIso e) _

/-- Derived restriction to an open subspace is semilinear over the restriction map on global
sections: `(a • φ)|_U = a|_U • φ|_U`. -/
public theorem derivedRestriction_map_smul (a : GlobalSectionRing O)
    {M N : DerivedCategory (SheafOfModules.{u} O)} (φ : M ⟶ N) :
    (derivedRestriction O U).map (a • φ) =
      restrictGlobalSection U O a • (derivedRestriction O U).map φ := by
  have h : a • φ = (a • 𝟙 M) ≫ φ := by rw [Linear.smul_comp, Category.id_comp]
  rw [h, CategoryTheory.Functor.map_comp, derivedRestriction_map_smul_id]
  simp only [Linear.smul_comp, Category.id_comp]

/-- If every morphism from `A` into the restriction of `F` to `U` is killed by a power of the
restricted global section `a|_U`, then every morphism from the extension by zero of `A` into `F`
is killed by the same power of `a`. -/
public theorem homPowerTorsion_jShriek (a : GlobalSectionRing O)
    (A : DerivedCategory (SheafOfModules.{u} (resRing U O)))
    (F : DerivedCategory (SheafOfModules.{u} O))
    (h : HomPowerTorsion (restrictGlobalSection U O a) A ((derivedRestriction O U).obj F)) :
    HomPowerTorsion a ((jShriek U O).mapDerivedCategory.obj A) F := by
  intro φ
  obtain ⟨k, hk⟩ := h ((jShriekAdjunction U O).mapDerivedCategory.homEquiv A F φ)
  refine ⟨k, (jShriekAdjunction U O).mapDerivedCategory.homEquiv A F |>.injective ?_⟩
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, CategoryTheory.Functor.map_zero,
    comp_zero, derivedRestriction_map_smul, restrictGlobalSection_pow, Linear.comp_smul]
  rwa [Adjunction.homEquiv_apply] at hk

/-- If on `U` every morphism from each shift of `E|_U` into `F|_U` is killed by a power of
`a|_U`, then on `X` every morphism from each shift of `j_{U!}(E|_U)` into `F` is killed by a
power of `a`. -/
public theorem homPowerTorsion_derivedExtensionRestriction (a : GlobalSectionRing O)
    (E F : DerivedCategory (SheafOfModules.{u} O))
    (h : ∀ n : ℤ, HomPowerTorsion (restrictGlobalSection U O a)
      (((derivedRestriction O U).obj E)⟦n⟧) ((derivedRestriction O U).obj F)) (n : ℤ) :
    HomPowerTorsion a (((derivedExtensionRestriction O U).obj E)⟦n⟧) F :=
  HomPowerTorsion.of_iso
    (((jShriek U O).mapDerivedCategory.commShiftIso n).app ((derivedRestriction O U).obj E))
    (homPowerTorsion_jShriek U O a (((derivedRestriction O U).obj E)⟦n⟧) F (h n))

end Restrict

/-- Let `X` be a topological space covered by two opens `U` and `V`, let `O` be a sheaf of
commutative rings on `X`, let `a` be a global section of `O` and let `E` and `F` be objects of
`D(𝒪_X)`. If on each of `U`, `V` and `U ∩ V` every morphism from each shift of the restriction
of `E` into the restriction of `F` is annihilated by a power of the restriction of `a`, then
every morphism `E⟦n⟧ ⟶ F` is annihilated by a power of `a`. -/
public theorem homPowerTorsion_of_restrictions {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [∀ Y : (Opens X)ᵒᵖ, IsMulCommutative (O.obj.obj Y)]
    (a : GlobalSectionRing O) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (E F : DerivedCategory (SheafOfModules.{u} O))
    (hU : ∀ n : ℤ, HomPowerTorsion (restrictGlobalSection U O a)
      (((derivedRestriction O U).obj E)⟦n⟧) ((derivedRestriction O U).obj F))
    (hV : ∀ n : ℤ, HomPowerTorsion (restrictGlobalSection V O a)
      (((derivedRestriction O V).obj E)⟦n⟧) ((derivedRestriction O V).obj F))
    (hUV' : ∀ n : ℤ, HomPowerTorsion (restrictGlobalSection (U ⊓ V) O a)
      (((derivedRestriction O (U ⊓ V)).obj E)⟦n⟧) ((derivedRestriction O (U ⊓ V)).obj F))
    (n : ℤ) : HomPowerTorsion a (E⟦n⟧) F :=
  homPowerTorsion_of_cover O a U V hUV E F
    (homPowerTorsion_derivedExtensionRestriction U O a E F hU)
    (homPowerTorsion_derivedExtensionRestriction V O a E F hV)
    (homPowerTorsion_derivedExtensionRestriction (U ⊓ V) O a E F hUV') n

end Stacks.ExtensionByZero

end
