module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedToposTwoIso
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentials
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# `Ω_{X_étale/Y_étale}` for a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes of a big étale site `B`.  The induced morphism of small
étale ringed topoi is `AlgebraicGeometry.smallEtaleRingedToposHom`, and its structure map in
inverse-image form is a homomorphism `f_small^♯ : f_small^{-1}𝒪_{Y_étale} ⟶ 𝒪_{X_étale}` of
sheaves of commutative rings on the small étale site of `X`.  This module builds the module of
differentials of that homomorphism in the sense of Stacks 04BN, together with its universal
`Y_étale`-derivation, and proves that it corepresents the functor of such derivations.

## Main definitions

* `AlgebraicGeometry.SmallEtale.etaleInverseImageStructureSheaf` is `f_small^{-1}𝒪_{Y_étale}`.
* `AlgebraicGeometry.SmallEtale.etaleStructureMap` is the inverse-image form
  `f_small^♯ : f_small^{-1}𝒪_{Y_étale} ⟶ 𝒪_{X_étale}` of the structure map.
* `AlgebraicGeometry.SmallEtale.sheafOfDifferentials` is `Ω_{X_étale/Y_étale}` and
  `AlgebraicGeometry.SmallEtale.universalDerivation` is its universal derivation.
* `AlgebraicGeometry.SmallEtale.etaleDerivationsFunctor` is the functor of `Y_étale`-derivations
  of `𝒪_{X_étale}`.

## Main results

* `AlgebraicGeometry.SmallEtale.universalDerivation_isUniversal`: every `Y_étale`-derivation with
  values in an `𝒪_{X_étale}`-module factors through the universal derivation by a unique
  morphism, so `Ω_{X_étale/Y_étale}` corepresents the functor of such derivations
  (`AlgebraicGeometry.SmallEtale.sheafOfDifferentialsCorepresentableBy`).

## Implementation notes

The small étale ringed site of a scheme is `AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its
objects live one universe above the sections of its structure sheaf. The general construction
`AlgebraicGeometry.SheafOfModules.sheafifiedObjectwiseDifferentials` lands in
`SheafOfModules.{max u u₁ v₁ v}`, which on this site is `u + 1`, whereas `(Ω_{X/Y})^a` is a
`SheafOfModules.{u}`; the same holds for the corepresentability
`AlgebraicGeometry.SheafOfModules.derivationsFunctor_isCorepresentable` of Stacks 04BL, whose
coefficient modules are constrained to that universe. The construction here is the same formula
— sheafify the presheaf of sectionwise Kähler differentials — assembled from the
universe-polymorphic `PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'` and
`PresheafOfModules.sheafification`, so it lands at `u`, as does
`AlgebraicGeometry.Space.sheafOfDifferentials` on the small étale site of an algebraic space.

`Stacks.Sheaves.Differentials.presheafDifferentialsEquiv` is stated for a small site
(`C : Type u` with `SmallCategory C`); `presheafDifferentialsEquiv` here is the same bijection
with the universes of the site left free.

Both `X` and `Y` are objects of the big étale site: `f_small` is a morphism from the small étale
site of `Y` to that of `X`, so `Y_étale` has to exist.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of
  differentials of a homomorphism of sheaves of rings on a site, and
  [Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), its universal property.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the morphism of small
  étale ringed topoi of a morphism of schemes.
-/

@[expose] public section

open CategoryTheory

universe u v₁ u₁ w

namespace AlgebraicGeometry.SmallEtale

section Presheaf

variable {C : Type u₁} [Category.{v₁} C]

/-- Morphisms out of the presheaf of sectionwise Kähler differentials of `φ' : S ⟶ R` are the
relative derivations of a presheaf of `R`-modules: the universal property of
`PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'`, packaged as a bijection. -/
private noncomputable def presheafDifferentialsEquiv
    {S R : Cᵒᵖ ⥤ CommRingCat.{w}} (φ' : S ⟶ R)
    (M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ' ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation' M φ' where
  toFun g := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ').postcomp g
  invFun := (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').desc
  left_inv _ :=
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').postcomp_injective _ _
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').fac _)
  right_inv := (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').fac

end Presheaf

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- `f_small^{-1}𝒪_{Y_étale}`, the inverse image along `f_small` of the structure sheaf of the
small étale site of `Y`, as a sheaf of commutative rings on the small étale site of `X`. -/
public noncomputable def etaleInverseImageStructureSheaf :
    Sheaf (topology B X.obj X.property) CommRingCat.{u} :=
  (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
      (smallEtaleRingedToposHom B f).toToposHom).obj
    (commRingStructureSheaf B Y.obj Y.property)

/-- The inverse-image form `f_small^♯ : f_small^{-1}𝒪_{Y_étale} ⟶ 𝒪_{X_étale}` of the structure
map of the morphism of small étale ringed topoi of `f`.  A `Y_étale`-derivation of an
`𝒪_{X_étale}`-module is by definition an `f_small^♯`-derivation. -/
public noncomputable def etaleStructureMap :
    etaleInverseImageStructureSheaf B f ⟶ commRingStructureSheaf B X.obj X.property :=
  (smallEtaleRingedToposHom B f).fSharpInverseImage

/-- A `Y_étale`-derivation of `𝒪_{X_étale}` with values in a sheaf of `𝒪_{X_étale}`-modules: a
derivation over `f_small^♯`, in the sense of Stacks 04BN. -/
public abbrev EtaleDerivation (F : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :=
  PresheafOfModulesOfCommRing.Derivation'
    (R := (commRingStructureSheaf B X.obj X.property).obj) F.val (etaleStructureMap B f).hom

/-- **`Ω_{X_étale/Y_étale}`**, the module of differentials of
`f_small^♯ : f_small^{-1}𝒪_{Y_étale} ⟶ 𝒪_{X_étale}` in the sense of Stacks 04BN: the sheaf of
modules associated to the presheaf of sectionwise Kähler differentials of `f_small^♯`. -/
public noncomputable def sheafOfDifferentials :
    SheafOfModules.{u} (structureSheaf B X.obj X.property) :=
  (PresheafOfModules.sheafification
      (𝟙 (structureSheaf B X.obj X.property).obj)).obj
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
      (etaleStructureMap B f).hom)

/-- **The universal `Y_étale`-derivation `d_{X_étale/Y_étale} : 𝒪_{X_étale} ⟶
Ω_{X_étale/Y_étale}`**: the sectionwise Kähler differential followed by the unit of
sheafification. -/
public noncomputable def universalDerivation :
    PresheafOfModulesOfCommRing.Derivation'
      (R := (commRingStructureSheaf B X.obj X.property).obj)
      (sheafOfDifferentials B f).val (etaleStructureMap B f).hom :=
  (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
      (etaleStructureMap B f).hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
        (J := topology B X.obj X.property)
        (𝟙 (structureSheaf B X.obj X.property).obj)).unit.app
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (etaleStructureMap B f).hom))

/-- **Stacks 04BN for `f_small^♯`.**  `Ω_{X_étale/Y_étale}` with its universal derivation
corepresents the functor of `Y_étale`-derivations: every such derivation with values in an
`𝒪_{X_étale}`-module factors through `d_{X_étale/Y_étale}` by a unique morphism of
`𝒪_{X_étale}`-modules. -/
public theorem universalDerivation_isUniversal
    (F : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (D : PresheafOfModulesOfCommRing.Derivation'
      (R := (commRingStructureSheaf B X.obj X.property).obj) F.val
      (etaleStructureMap B f).hom) :
    ∃! g : sheafOfDifferentials B f ⟶ F,
      (universalDerivation B f).postcomp g.val = D := by
  set e := (PresheafOfModules.sheafificationHomEquiv
      (𝟙 (structureSheaf B X.obj X.property).obj) (P :=
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (etaleStructureMap B f).hom) (F := F)).trans
    (presheafDifferentialsEquiv (etaleStructureMap B f).hom _)
  have key (g : sheafOfDifferentials B f ⟶ F) :
      e g = (universalDerivation B f).postcomp g.val := by
    ext V x
    rfl
  exact ⟨e.symm D, (key _).symm.trans (e.apply_symm_apply D),
    fun g hg ↦ (Equiv.eq_symm_apply e).mpr ((key g).trans hg)⟩

/-- **The functor of `Y_étale`-derivations of `𝒪_{X_étale}`**, with values in a sheaf of
`𝒪_{X_étale}`-modules, acting on morphisms by postcomposition.

`AlgebraicGeometry.SheafOfModules.derivationsFunctor` is the same functor on a general site, but
its coefficient sheaves of modules are constrained to the universe `max u u₁ v₁ v`, which on the
small étale site of a scheme is `u + 1`; the coefficient sheaves here are `SheafOfModules.{u}`,
the universe `(Ω_{X/Y})^a` lives in. -/
public noncomputable def etaleDerivationsFunctor :
    SheafOfModules.{u} (structureSheaf B X.obj X.property) ⥤ Type (u + 1) where
  obj F := EtaleDerivation B f F
  map {A C} g := ↾(fun D : EtaleDerivation B f A =>
    (D.postcomp g.val : EtaleDerivation B f C))
  map_id _ := by
    ext D V x
    rfl
  map_comp _ _ := by
    ext D V x
    rfl

/-- `Ω_{X_étale/Y_étale}` corepresents the functor of `Y_étale`-derivations, in the form
`CategoryTheory.Functor.CorepresentableBy`. -/
public noncomputable def sheafOfDifferentialsCorepresentableBy :
    (etaleDerivationsFunctor B f).CorepresentableBy (sheafOfDifferentials B f) := by
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro F
    refine ⟨fun g => (universalDerivation B f).postcomp g.val,
      fun D => Classical.choose (universalDerivation_isUniversal B f F D), ?_, ?_⟩
    · intro g
      exact ((Classical.choose_spec (universalDerivation_isUniversal B f F
        ((universalDerivation B f).postcomp g.val))).2 g rfl).symm
    · intro D
      exact (Classical.choose_spec (universalDerivation_isUniversal B f F D)).1
  · intro F G g h
    change (universalDerivation B f).postcomp (h.val ≫ g.val) =
      ((universalDerivation B f).postcomp h.val).postcomp g.val
    ext V x
    rfl

end AlgebraicGeometry.SmallEtale

end
