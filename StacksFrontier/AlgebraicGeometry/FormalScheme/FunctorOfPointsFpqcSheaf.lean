module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections

/-!
# Formal schemes are fpqc sheaves

Let `𝔛` be a formal scheme. Its functor of points `h_𝔛(S) = Mor_{Formal Schemes}(S, 𝔛)` of
Stacks 0AI1 satisfies the sheaf condition for fpqc coverings (Stacks 0AI2). This file proves the
*separatedness* half of that condition: a morphism from a scheme `T` to `𝔛` is determined by its
restrictions along an fpqc covering of `T`. Existence of amalgamations is proved in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent`.

The argument is the one the source gives for the injectivity in Stacks 0AI1, run on the covering
instead of on the affine formal charts. A morphism of locally topologically ringed spaces out of
`T` is determined by its underlying map and by what it does to sections of `𝒪_T`; the members of
an fpqc covering are jointly surjective, and they separate the sections of `𝒪_T` because a flat
morphism is injective on stalks. Neither quasi-compactness of the covering nor any bound on the
size of `𝔛` is used, so the statement is proved for every jointly surjective family of flat
morphisms.

## Main definitions

* `AlgebraicGeometry.formalSchemePoints`: the functor of points of a formal scheme on *all*
  schemes, of which `AlgebraicGeometry.formalSchemeFunctorOfPoints` is the restriction to the
  schemes of size below a cutoff cardinal.

## Main results

* `AlgebraicGeometry.formalSchemeHom_ext_of_flat_of_jointlySurjective`: a morphism from a scheme
  to a formal scheme is determined by its restrictions along a jointly surjective family of flat
  morphisms.
* `AlgebraicGeometry.isSeparated_fpqcTopology_formalSchemePoints`: the separatedness half of
  Stacks 0AI2. The functor of points of a formal scheme on the category of all schemes is
  separated for the fpqc topology.
* `AlgebraicGeometry.isSeparatedFor_formalSchemeFunctorOfPoints`: the separatedness half of
  Stacks 0AI2, for the functor of points on the schemes of size below `κ` as Stacks 0AI1
  defines it, and for an fpqc covering of such a scheme by such schemes.

## Implementation notes

*Separatedness first.* The existence of amalgamations — an fpqc descent datum of points of `𝔛`
is effective — rests on this separatedness, on the Zariski case, and on the factorisation
`AlgebraicGeometry.exists_factor_spfQuotientPointOn` of a point of `Spf A` over an affine scheme;
it is `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`.

*Two statements, two sites.* `AlgebraicGeometry.formalSchemeFunctorOfPoints` lives on the
schemes of size below `κ`, and the fpqc precoverage there is the one pulled back along the
inclusion into all schemes. That precoverage is stable under base change only once `κ` is large
enough for `Sch_κ` to be closed under fibre products, so the sieves it generates are not
described by their covering families for an arbitrary `κ`; the statement on `Sch_κ` is therefore
made for covering *families*, which is what the source's "satisfies the sheaf condition for fpqc
coverings" says, while the statement on all schemes is made for the honest Grothendieck topology
`AlgebraicGeometry.Scheme.fpqcTopology` and so covers arbitrary fpqc covering sieves.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- The *functor of points* of a formal scheme on the category of all schemes: the presheaf
`h_𝔛(S) = Mor_{Formal Schemes}(S, 𝔛)`, a scheme being viewed as a formal scheme through the
functor of Stacks 0AI0. Restricting it along the inclusion of the schemes of size below `κ`
gives `AlgebraicGeometry.formalSchemeFunctorOfPoints`. -/
noncomputable def formalSchemePoints (X : FormalScheme.{u}) : (Scheme.{u})ᵒᵖ ⥤ Type u :=
  schemeToFormalScheme.op ⋙ yoneda.obj X

/-- The points of `𝔛` on a scheme `T` are the morphisms of formal schemes from `T` to `𝔛`. -/
@[simp]
theorem formalSchemePoints_obj (X : FormalScheme.{u}) (T : Scheme.{u}) :
    (formalSchemePoints X).obj (op T) = (schemeToFormalScheme.obj T ⟶ X) := rfl

/-- A morphism of schemes acts on points by precomposition. -/
@[simp]
theorem formalSchemePoints_map (X : FormalScheme.{u}) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (f : schemeToFormalScheme.obj T ⟶ X) :
    (formalSchemePoints X).map g.op f = schemeToFormalScheme.map g ≫ f := rfl

/-- The functor of points on the schemes of size below `κ` is the restriction of the functor of
points on all schemes. -/
theorem formalSchemeFunctorOfPoints_obj_eq (κ : Cardinal.{u}) (X : FormalScheme.{u}) :
    (formalSchemeFunctorOfPoints κ).obj X = (schemeCutoff κ).ι.op ⋙ formalSchemePoints X := rfl

/-- A morphism from a scheme `T` to an object of `LTRS` is determined by its restrictions along
a jointly surjective family of flat morphisms to `T`.

The underlying maps of the family are jointly surjective by hypothesis, and the family separates
the sections of `𝒪_T` because a flat morphism of schemes is injective on stalks. Nothing is
asked of the target beyond being a locally topologically ringed space, so the statement applies
to a formal scheme à la EGA and to one in the sense of McQuillan alike. -/
theorem ltrs_hom_ext_of_flat_of_jointlySurjective {T : Scheme.{u}} {X : LTRS.{u}}
    {J : Type*} {V : J → Scheme.{u}} (π : ∀ j, V j ⟶ T) (hflat : ∀ j, Flat (π j))
    (hsurj : ∀ t : T, ∃ j, ∃ y : V j, π j y = t)
    {f g : schemeToLTRS.obj T ⟶ X}
    (h : ∀ j, schemeToLTRS.map (π j) ≫ f = schemeToLTRS.map (π j) ≫ g) :
    f = g := by
  -- Reindex the family by the points of `T`, so that it is indexed in the universe of `T`.
  choose idx pt hpt using hsurj
  have hsurj' : ∀ t : T, ∃ x : T, ∃ y : V (idx x), π (idx x) y = t := fun t => ⟨t, pt t, hpt t⟩
  refine LocallyTopologicallyRingedSpace.Hom.ext' ?_
  refine presheafedSpace_hom_ext_of_cover
    (Z := fun x : T => pseudoDiscreteSpace (V (idx x)).toPresheafedSpace)
    (fun x => schemeToLTRSHom (π (idx x))) (fun x => ⟨x, pt x, hpt x⟩) ?_ _ _ ?_
  · -- The family separates the sections of `𝒪_T` over every open set.
    intro W R a b hab
    refine Subtype.ext (RingHom.ext fun r => ?_)
    refine Scheme.section_ext_of_flat_of_jointlySurjective (fun x : T => π (idx x))
      (fun x => hflat (idx x)) hsurj' W fun x => ?_
    exact congrArg (fun k : R ⟶ _ => k.1 r) (hab x)
  · intro x
    exact congrArg (fun m : schemeToLTRS.obj (V (idx x)) ⟶ X => m.toHom) (h (idx x))

/-- The members of an fpqc covering family are jointly surjective and flat. -/
private theorem jointlySurjective_and_flat_of_mem_fpqcPrecoverage {T : Scheme.{u}} {J : Type*}
    {V : J → Scheme.{u}} {π : ∀ j, V j ⟶ T}
    (hR : Presieve.ofArrows V π ∈ Scheme.fpqcPrecoverage.{u} T) :
    (∀ t : T, ∃ j, ∃ y : V j, π j y = t) ∧ ∀ j, Flat (π j) :=
  (Scheme.presieve₀_mem_precoverage_iff (P := @Flat) (⟨J, V, π⟩ : PreZeroHypercover T)).mp
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) T hR)

/-- A morphism from a scheme `T` to an object of `LTRS` is determined by its restrictions along
the arrows of any fpqc covering sieve of `T`: such a sieve contains an fpqc covering family,
whose members are flat and jointly surjective. -/
theorem ltrs_hom_ext_of_mem_fpqcTopology {T : Scheme.{u}} {X : LTRS.{u}} {S : Sieve T}
    (hS : S ∈ Scheme.fpqcTopology.{u} T) {f g : schemeToLTRS.obj T ⟶ X}
    (h : ∀ ⦃Z : Scheme.{u}⦄ (π : Z ⟶ T), S.arrows π →
      schemeToLTRS.map π ≫ f = schemeToLTRS.map π ≫ g) :
    f = g := by
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨J, C, g', rfl⟩ := R.exists_eq_ofArrows
  have hdata := jointlySurjective_and_flat_of_mem_fpqcPrecoverage hR
  exact ltrs_hom_ext_of_flat_of_jointlySurjective g' (fun j => hdata.2 j) (fun t => hdata.1 t)
    fun j => h (g' j) (hle _ _ (Presieve.ofArrows.mk j))

/-- A morphism from a scheme `T` to a formal scheme is determined by its restrictions along a
jointly surjective family of flat morphisms to `T`. -/
theorem formalSchemeHom_ext_of_flat_of_jointlySurjective {T : Scheme.{u}} {X : FormalScheme.{u}}
    {J : Type*} {V : J → Scheme.{u}} (π : ∀ j, V j ⟶ T) (hflat : ∀ j, Flat (π j))
    (hsurj : ∀ t : T, ∃ j, ∃ y : V j, π j y = t)
    {f g : schemeToFormalScheme.obj T ⟶ X}
    (h : ∀ j, schemeToFormalScheme.map (π j) ≫ f = schemeToFormalScheme.map (π j) ≫ g) :
    f = g :=
  InducedCategory.hom_ext (ltrs_hom_ext_of_flat_of_jointlySurjective π hflat hsurj
    fun j => congrArg (fun m : schemeToFormalScheme.obj (V j) ⟶ X => m.hom) (h j))

/-- The separatedness half of Stacks 0AI2. The functor of points of a formal scheme, on the
category of all schemes, is separated for the fpqc topology: a point of `𝔛` over a scheme `T`
is determined by its restrictions along any fpqc covering sieve of `T`.

A covering sieve of the fpqc topology contains an fpqc covering family, whose members are flat
and jointly surjective, so this is
`AlgebraicGeometry.formalSchemeHom_ext_of_flat_of_jointlySurjective`. -/
theorem isSeparated_fpqcTopology_formalSchemePoints (X : FormalScheme.{u}) :
    Presieve.IsSeparated Scheme.fpqcTopology.{u} (formalSchemePoints X) := by
  intro T S hS x t₁ t₂ h₁ h₂
  refine InducedCategory.hom_ext (ltrs_hom_ext_of_mem_fpqcTopology hS fun Z π hπ => ?_)
  exact congrArg (fun m : schemeToFormalScheme.obj Z ⟶ X => m.hom)
    ((h₁ π hπ).trans (h₂ π hπ).symm)

/-- The separatedness half of Stacks 0AI2, for the functor of points of Stacks 0AI1. A point of
`𝔛` over a scheme `T` of `Sch_κ` is determined by its restrictions along a family of morphisms of
`Sch_κ` which is an fpqc covering of `T`.

The fpqc coverings of `Sch_κ` are those families whose image in the category of all schemes is
an fpqc covering, that is, the ones in the precoverage pulled back along the inclusion. -/
theorem isSeparatedFor_formalSchemeFunctorOfPoints {κ : Cardinal.{u}} (X : FormalScheme.{u})
    {T : (schemeCutoff κ).FullSubcategory} {R : Presieve T}
    (hR : R ∈ Scheme.fpqcPrecoverage.{u}.comap (schemeCutoff κ).ι T) :
    Presieve.IsSeparatedFor ((formalSchemeFunctorOfPoints κ).obj X) R := by
  obtain ⟨J, S, u, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hR
  simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map] at hR
  have hdata := jointlySurjective_and_flat_of_mem_fpqcPrecoverage hR
  intro y t₁ t₂ h₁ h₂
  refine formalSchemeHom_ext_of_flat_of_jointlySurjective (fun j => (u j).hom)
    (fun j => hdata.2 j) (fun t => hdata.1 t) fun j => ?_
  exact (h₁ _ (Presieve.ofArrows.mk j)).trans (h₂ _ (Presieve.ofArrows.mk j)).symm

end AlgebraicGeometry

end
