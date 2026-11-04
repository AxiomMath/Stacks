module

public import Mathlib.CategoryTheory.Sites.Canonical
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# Representable sheaves on the small étale site

The small étale topology of a scheme `S` is *subcanonical*: for every `X` étale over `S` the
presheaf `U ↦ Mor_S(U, X)` on the small étale site of `S` is a sheaf.  Equivalently, an étale
covering is an effective epimorphic family, which is descent of morphisms along an étale
covering.  Consequently the Yoneda embedding of the small étale site lands in the small étale
topos and is fully faithful there, so the étale `S`-schemes form a full subcategory of the
small étale topos.

The proof is a transport along the canonical functor to all schemes.  Morphisms of schemes
descend along an fpqc covering, i.e. the fpqc topology on the category of all schemes is
subcanonical (Mathlib's `AlgebraicGeometry.Scheme.fpqcTopology.Subcanonical`), and an étale
covering is an fpqc covering.  Transporting along a functor is exactly what
`AlgebraicGeometry.SmallEtale.compatiblePreserving_toScheme` and
`Stacks.Sites.isSheafFor_op_comp` do, and they give the sheaf condition for the presheaf
`U ↦ Mor(U, Y)` of morphisms of *schemes* into an arbitrary `Y`.  What remains is to cut out
the morphisms over `S`: a glued morphism `U ⟶ Y` lies over `S` because it does so after
restriction to a covering family, and the presheaf of morphisms into `S` is separated.

This is the half of [Stacks, Tag 03QT] that passes from étale schemes to sheaves: for
`S = Spec K` the spectrum of a field, that theorem says that taking stalks at a geometric
point is an equivalence from the small étale topos onto continuous sets over the absolute
Galois group, and its proof constructs the inverse by representing a Galois set by an étale
`K`-scheme and taking the sheaf of morphisms into it.  Nothing here carries the tag 03QT.

## Main results

* `AlgebraicGeometry.SmallEtale.isSheaf_toScheme_op_yoneda` — the presheaf of morphisms of
  schemes from the small étale site into a fixed scheme is a sheaf.
* `AlgebraicGeometry.SmallEtale.isSheaf_yoneda_obj` — every representable presheaf on the
  small étale site is a sheaf.
* `AlgebraicGeometry.SmallEtale.topology_subcanonical` — the small étale topology is
  subcanonical.

## Main definitions

* `AlgebraicGeometry.smallEtaleYoneda` — the resulting embedding of the small étale site of
  `S` into its small étale topos, fully faithful by
  `AlgebraicGeometry.smallEtaleYonedaFullyFaithful`.
* `AlgebraicGeometry.smallEtaleUliftYoneda` — its variant with values in sheaves of
  `Type (max u v)`.

## References

* [Stacks Project, Tag 03PH](https://stacks.math.columbia.edu/tag/03PH), after which the
  source remarks that the étale site is subcanonical
* [Stacks Project, Tag 03QT](https://stacks.math.columbia.edu/tag/03QT)
* [Stacks Project, Tag 04JL](https://stacks.math.columbia.edu/tag/04JL)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying morphism of schemes of a morphism of the small étale site of `S` is a
morphism over `S`. -/
theorem toScheme_map_comp_hom {U X : SmallEtale B S hS} (f : U ⟶ X) :
    (toScheme B S hS).map f ≫ B.inclusion.map X.obj.hom = B.inclusion.map U.obj.hom :=
  B.inclusion.congr_map (Over.w f.hom)

/-- The presheaf of morphisms of schemes from the small étale site of `S` into a fixed scheme
`Y` satisfies the sheaf condition for a single covering family, that family being an étale and
hence fpqc covering, for which morphisms of schemes descend. -/
theorem isSheafFor_toScheme_op_yoneda (Y : Scheme.{u}) {X : SmallEtale B S hS}
    {R : Presieve X} (hR : R ∈ precoverage B S hS X) :
    Presieve.IsSheafFor ((toScheme B S hS).op ⋙ yoneda.obj Y) R := by
  obtain ⟨E, rfl, hE⟩ := hR
  rw [Presieve.isSheafFor_iff_generate]
  refine Stacks.Sites.isSheafFor_op_comp (compatiblePreserving_toScheme B S hS)
    (Scheme.fpqcTopology.yoneda.obj Y) _ ?_
  rw [← Sieve.generate_map_eq_functorPushforward, PreZeroHypercover.presieve₀,
    Presieve.map_ofArrows]
  exact Stacks.Sites.etaleTopology_le_fpqcTopology _
    (Precoverage.generate_mem_toGrothendieck hE.1)

/-- **Descent of morphisms of schemes along an étale covering.**  The presheaf of morphisms of
schemes from the small étale site of `S` into a fixed scheme `Y` is a sheaf. -/
theorem isSheaf_toScheme_op_yoneda (Y : Scheme.{u}) :
    Presieve.IsSheaf (topology B S hS) ((toScheme B S hS).op ⋙ yoneda.obj Y) := by
  have := smallEtale_precoverage_stableUnderBaseChange B S hS
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro X R hR
  exact isSheafFor_toScheme_op_yoneda B S hS Y hR

/-- **The small étale topology is subcanonical.**  For `X` étale over `S` the presheaf
`U ↦ Mor_S(U, X)` on the small étale site of `S` is a sheaf: a compatible family of morphisms
over a covering family glues to a morphism of schemes, because morphisms of schemes descend
along an étale covering, and the glued morphism lies over `S` because it does so after
restriction to the covering family. -/
theorem isSheaf_yoneda_obj (X : SmallEtale B S hS) :
    Presieve.IsSheaf (topology B S hS) (yoneda.obj X) := by
  have := smallEtale_precoverage_stableUnderBaseChange B S hS
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro U R hR x hx
  have hsheaf := isSheafFor_toScheme_op_yoneda B S hS ((toScheme B S hS).obj X) hR
  have hsep := (isSheafFor_toScheme_op_yoneda B S hS S hR).isSeparatedFor
  -- the family of underlying morphisms of schemes
  have hx' : Presieve.FamilyOfElements.Compatible
      (P := (toScheme B S hS).op ⋙ yoneda.obj ((toScheme B S hS).obj X)) (R := R)
      (fun _ f hf ↦ (toScheme B S hS).map (x f hf)) := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    show (toScheme B S hS).map g₁ ≫ (toScheme B S hS).map (x f₁ h₁) =
      (toScheme B S hS).map g₂ ≫ (toScheme B S hS).map (x f₂ h₂)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (toScheme B S hS).congr_map (hx g₁ g₂ h₁ h₂ hcomm)
  obtain ⟨t, ht, -⟩ := hsheaf _ hx'
  have htf : ∀ ⦃V : SmallEtale B S hS⦄ (f : V ⟶ U) (hf : R f),
      (toScheme B S hS).map f ≫ t = (toScheme B S hS).map (x f hf) := fun _ f hf ↦ ht f hf
  -- every restriction of the glued morphism lies over `S`, hence so does the morphism itself
  have hover : t ≫ B.inclusion.map X.obj.hom = B.inclusion.map U.obj.hom := by
    refine hsep.ext fun V f hf ↦ ?_
    show (toScheme B S hS).map f ≫ t ≫ B.inclusion.map X.obj.hom =
      (toScheme B S hS).map f ≫ B.inclusion.map U.obj.hom
    rw [← Category.assoc, htf f hf, toScheme_map_comp_hom, toScheme_map_comp_hom]
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk t)
    (InducedCategory.hom_ext hover)), fun V f hf ↦ ?_, fun g hg ↦ ?_⟩
  · exact (toScheme B S hS).map_injective (htf f hf)
  · refine (toScheme B S hS).map_injective ?_
    refine hsheaf.isSeparatedFor.ext fun V f hf ↦ ?_
    show (toScheme B S hS).map f ≫ (toScheme B S hS).map g =
      (toScheme B S hS).map f ≫ t
    rw [← Functor.map_comp, (toScheme B S hS).congr_map (show f ≫ g = x f hf from hg f hf),
      htf f hf]

/-- **The small étale topology is subcanonical**: every representable presheaf on the small
étale site of `S` is a sheaf. -/
instance topology_subcanonical : (topology B S hS).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ (isSheaf_yoneda_obj B S hS)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The étale `S`-schemes as sheaves on the small étale site.**  An object `X` of the small
étale site of `S` is sent to the sheaf `U ↦ Mor_S(U, X)`, which is a sheaf because the small
étale topology is subcanonical. -/
noncomputable def smallEtaleYoneda : SmallEtale B S hS ⥤ smallEtaleTopos.{u, u} B S hS :=
  (SmallEtale.topology B S hS).yoneda

/-- The underlying presheaf of the sheaf represented by `X` is the representable presheaf. -/
theorem smallEtaleYoneda_obj_obj (X U : SmallEtale B S hS) :
    ((smallEtaleYoneda B S hS).obj X).obj.obj (op U) = (U ⟶ X) :=
  rfl

/-- **The étale `S`-schemes form a full subcategory of the small étale topos.**  The embedding
`AlgebraicGeometry.smallEtaleYoneda` is fully faithful, because the small étale topology is
subcanonical and the Yoneda embedding is fully faithful. -/
@[sga "3 I 1.1" "special case", sga "4 VII 2.1" "partial"]
noncomputable def smallEtaleYonedaFullyFaithful :
    (smallEtaleYoneda B S hS).FullyFaithful :=
  (SmallEtale.topology B S hS).yonedaFullyFaithful

/-- The functor `AlgebraicGeometry.smallEtaleYoneda` is full. -/
instance smallEtaleYoneda_full : (smallEtaleYoneda B S hS).Full :=
  (smallEtaleYonedaFullyFaithful B S hS).full

/-- The functor `AlgebraicGeometry.smallEtaleYoneda` is faithful. -/
instance smallEtaleYoneda_faithful : (smallEtaleYoneda B S hS).Faithful :=
  (smallEtaleYonedaFullyFaithful B S hS).faithful

/-- The variant of `AlgebraicGeometry.smallEtaleYoneda` with values in sheaves of
`Type (max u v)`, which is the universe in which the stalk functor
`AlgebraicGeometry.etaleStalkFunctor` takes its values. -/
noncomputable def smallEtaleUliftYoneda :
    SmallEtale B S hS ⥤ smallEtaleTopos.{u, max u v} B S hS :=
  (SmallEtale.topology B S hS).uliftYoneda.{v}

/-- The underlying presheaf of the sheaf represented by `X` is the representable presheaf,
with its values lifted to `Type (max u v)`. -/
theorem smallEtaleUliftYoneda_obj_obj (X U : SmallEtale B S hS) :
    ((smallEtaleUliftYoneda.{u, v} B S hS).obj X).obj.obj (op U) = ULift.{v} (U ⟶ X) :=
  rfl

/-- `AlgebraicGeometry.smallEtaleUliftYoneda` is fully faithful as well. -/
noncomputable def smallEtaleUliftYonedaFullyFaithful :
    (smallEtaleUliftYoneda.{u, v} B S hS).FullyFaithful :=
  (SmallEtale.topology B S hS).fullyFaithfulUliftYoneda

/-- The functor `AlgebraicGeometry.smallEtaleUliftYoneda` is full. -/
instance smallEtaleUliftYoneda_full : (smallEtaleUliftYoneda.{u, v} B S hS).Full :=
  (smallEtaleUliftYonedaFullyFaithful B S hS).full

/-- The functor `AlgebraicGeometry.smallEtaleUliftYoneda` is faithful. -/
instance smallEtaleUliftYoneda_faithful : (smallEtaleUliftYoneda.{u, v} B S hS).Faithful :=
  (smallEtaleUliftYonedaFullyFaithful B S hS).faithful

/-- In the morphism universe, `AlgebraicGeometry.smallEtaleUliftYoneda` is
`AlgebraicGeometry.smallEtaleYoneda`. -/
noncomputable def smallEtaleUliftYonedaIsoSmallEtaleYoneda :
    smallEtaleUliftYoneda.{u, u} B S hS ≅ smallEtaleYoneda B S hS :=
  (SmallEtale.topology B S hS).uliftYonedaIsoYoneda

end AlgebraicGeometry

end
