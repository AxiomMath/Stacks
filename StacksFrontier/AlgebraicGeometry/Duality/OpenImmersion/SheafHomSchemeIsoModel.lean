module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel

/-!
# The derived internal Hom is invariant under an isomorphism of schemes

Let `g : A ⟶ B` be an isomorphism of schemes. Restriction of `𝒪_B`-modules along `g` is
Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor g`, and this file identifies the
restriction of a derived internal Hom with the derived internal Hom of the restrictions:

`RSheafHom_{𝒪_B}(K, L)|_A ≅ RSheafHom_{𝒪_A}(K|_A, L|_A)`.

Together with `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`, which is the same
statement for the inclusion of an open subscheme, this lets a statement about the derived
internal Hom be moved from an affine scheme to the spectrum it is isomorphic to.

The whole file is one instantiation of the general transport along an equivalence of ringed
sites, `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso`. The equivalence of sites
is the one an isomorphism of schemes induces on lattices of opens, and the structure map is the
one `restrictFunctor` is defined by, so that `SheafOfModules.pushforward` of it is
`restrictFunctor g` on the nose — see `pushforward_schemeIsoPhi`.

## Main definitions

* `Stacks.SheafOfModules.schemeIsoOpensEquivalence`: the equivalence of the two lattices of
  opens, `Opens A ≌ Opens B`.
* `Stacks.SheafOfModules.schemeIsoPhi`: the structure map of `restrictFunctor g`, read as the
  structure map of an equivalence of ringed sites.
* `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso`: **the transport of the derived internal
  Hom.**

## Main results

* `Stacks.SheafOfModules.pushforward_schemeIsoPhi`: pushforward along `schemeIsoPhi` is
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor g`.
* `Stacks.SheafOfModules.isIso_schemeIsoPhi`: the structure map is invertible.

## Implementation notes

No `@[stacks]` attribute is attached: an isomorphism is not a localization, so none of the
restriction tags is being delivered here. The statement is used as a change of model, alongside
`derivedSheafHomSchemeRestrictionIso`, which is where [Stacks, Tag 08DL] sits.

The inverse of `g` is written `CategoryTheory.inv g` rather than `(asIso g).inv` so that the
equivalence is available from `IsIso g` alone; the two are the same term, which is what lets
Mathlib's `AlgebraicGeometry.Scheme.Hom.inv_image` be applied to `asIso g` in the proofs of the
unit and the counit. Both of those reduce to an equality of opens, since `Opens A` is a partial
order and every naturality square in it commutes.

Invertibility of the structure map is proved on the underlying presheaf of rings and then
reflected along `CategoryTheory.sheafToPresheaf`, which is fully faithful: the components are
the inverses of `AlgebraicGeometry.Scheme.Hom.appIso`, pushed along the forgetful functor to
`RingCat`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {A B : Scheme.{u}} (g : A ⟶ B) [IsIso g]

/-- **The lattices of opens of two isomorphic schemes are equivalent.** The functor is the
image functor `AlgebraicGeometry.Scheme.Hom.opensFunctor` of `g` and the inverse is that of
`g⁻¹`; the unit and the counit are equalities of opens, `Opens A` being a partial order. -/
def schemeIsoOpensEquivalence : (ringedSite A.sheaf).C ≌ (ringedSite B.sheaf).C where
  functor := Scheme.Hom.opensFunctor g
  inverse := Scheme.Hom.opensFunctor (inv g)
  unitIso := NatIso.ofComponents
    (fun U =>
      eqToIso (((Scheme.Hom.inv_image (asIso g) ((Scheme.Hom.opensFunctor g).obj U)).trans
        (Scheme.Hom.preimage_image_eq g U)).symm))
    (by intros; subsingleton)
  counitIso := NatIso.ofComponents
    (fun V => eqToIso (by
      simp only [Functor.comp_obj, Functor.id_obj]
      rw [show (Scheme.Hom.opensFunctor (inv g)).obj V = g ⁻¹ᵁ V from
        Scheme.Hom.inv_image (asIso g) V,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso]
      exact top_inf_eq V))
    (by intros; subsingleton)

/-- Taking images along `g` is continuous for the open-cover topologies, in the spelling of the
two ringed sites. -/
instance schemeIsoFunctorIsContinuous :
    (schemeIsoOpensEquivalence g).functor.IsContinuous
      (ringedSite A.sheaf).J (ringedSite B.sheaf).J :=
  inferInstanceAs ((Scheme.Hom.opensFunctor g).IsContinuous
    (Opens.grothendieckTopology ↥A) (Opens.grothendieckTopology ↥B))

/-- Taking images along `g⁻¹` is continuous for the open-cover topologies, in the spelling of
the two ringed sites. -/
instance schemeIsoInverseIsContinuous :
    (schemeIsoOpensEquivalence g).inverse.IsContinuous
      (ringedSite B.sheaf).J (ringedSite A.sheaf).J :=
  inferInstanceAs ((Scheme.Hom.opensFunctor (inv g)).IsContinuous
    (Opens.grothendieckTopology ↥B) (Opens.grothendieckTopology ↥A))

/-- **The structure map of `AlgebraicGeometry.Scheme.Modules.restrictFunctor g`**, read as the
structure map of an equivalence of ringed sites: on an open `U` of `A` it is the inverse of
`AlgebraicGeometry.Scheme.Hom.appIso`, which identifies the sections of `𝒪_B` over the image of
`U` with the sections of `𝒪_A` over `U`. This is an `abbrev` so that
`pushforward_schemeIsoPhi` stays visible. -/
abbrev schemeIsoPhi :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite A.sheaf).O) ⟶
      ((schemeIsoOpensEquivalence g).functor.sheafPushforwardContinuous RingCat.{u}
        (ringedSite A.sheaf).J (ringedSite B.sheaf).J).obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B.sheaf).O) :=
  ⟨Functor.whiskerRight
    ({ app := fun U => (Scheme.Hom.appIso g U.unop).inv } :
      A.presheaf ⟶ (Scheme.Hom.opensFunctor g).op ⋙ B.presheaf)
    (forget₂ CommRingCat RingCat)⟩

/-- Pushforward of sheaves of modules along `schemeIsoPhi` is restriction along `g`: the
structure map above is the one Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is
defined by. -/
theorem pushforward_schemeIsoPhi :
    _root_.SheafOfModules.pushforward.{u} (schemeIsoPhi g) =
      Scheme.Modules.restrictFunctor g :=
  rfl

/-- The structure map is invertible: its components are the inverses of
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
instance isIso_schemeIsoPhi : IsIso (schemeIsoPhi g) := by
  have happ : ∀ U : (Opens ↥A)ᵒᵖ,
      IsIso (((sheafToPresheaf (Opens.grothendieckTopology ↥A) RingCat.{u}).map
        (schemeIsoPhi g)).app U) := fun U =>
    inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map
      (Scheme.Hom.appIso g U.unop).inv))
  have h : IsIso ((sheafToPresheaf (Opens.grothendieckTopology ↥A)
      RingCat.{u}).map (schemeIsoPhi g)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf (Opens.grothendieckTopology ↥A) RingCat.{u})

/-- **The derived internal Hom commutes with restriction along an isomorphism of schemes.** For
objects `K`, `L` of `D(𝒪_B)` the restriction of `RSheafHom_{𝒪_B}(K, L)` along an isomorphism
`g : A ⟶ B` is the derived internal Hom `RSheafHom_{𝒪_A}(K|_A, L|_A)` on the ringed site of `A`.

This is `AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso` at the equivalence of
ringed sites `schemeIsoOpensEquivalence` and `schemeIsoPhi`, whose pushforward of modules is
restriction along `g`. -/
def derivedSheafHomSchemeIsoIso (K L : DerivedCategory (StructureSheafModules B.sheaf)) :
    (Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite B.sheaf)).obj (op K)).obj L) ≅
      ((RingedSite.derivedSheafHomBifunctor (ringedSite A.sheaf)).obj
        (op ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj K))).obj
          ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj L) :=
  RingedSite.siteEquivDerivedSheafHomIsoOfIso
    (X := ringedSite B.sheaf) (Y := ringedSite A.sheaf)
    (schemeIsoOpensEquivalence g) (schemeIsoPhi g) (hφ := isIso_schemeIsoPhi g)
    (hlim := RingedSite.pushforward_preservesFiniteLimitsOfIso
      (schemeIsoOpensEquivalence g) (schemeIsoPhi g))
    (hcolim := RingedSite.pushforward_preservesFiniteColimitsOfIso
      (schemeIsoOpensEquivalence g) (schemeIsoPhi g)) K L

end Stacks.SheafOfModules

end
