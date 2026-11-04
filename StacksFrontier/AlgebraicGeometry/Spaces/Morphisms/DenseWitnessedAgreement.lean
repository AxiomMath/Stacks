module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition

/-!
# Agreement witnessed at a dense set of points

Let `X` be a reduced algebraic space over a scheme `S` contained in a big fppf site and let `Y`
be an algebraic space separated over an algebraic space `T`.  Two morphisms `f, g : X ⟶ Y` over
`T` are equal as soon as there is a *dense set of points of `X` at each of which they are known
to agree along some morphism into `X`*: for every point `p` of a dense subset of `|X|` there is
a morphism `a : W ⟶ X` with `a ≫ f = a ≫ g` whose image on points contains `p`.

This is the form of Stacks 084N that an argument proving an identity at a dense family of
*rational points* consumes.  The existing form,
`AlgebraicGeometry.Space.eq_of_eq_on_dense`, asks for one subfunctor of `X` with dense point
set on which the two morphisms agree.  A family of rational points is not one subfunctor, and
forming the subfunctor it generates would require knowing that the point set of a supremum of
subfunctors is the union of their point sets.  No such statement is needed: the agreement locus
of `f` and `g` is *already* a closed subspace of `X`, every single witness `a` puts its own
image inside it, and a closed subspace whose point set is dense in a reduced algebraic space is
everything.

## Main results

* `AlgebraicGeometry.Space.eq_of_eq_on_dense_witnessed`: **two morphisms agreeing along a
  witness at each point of a dense set are equal.**
* `AlgebraicGeometry.Space.eq_of_eq_on_dense_witnessed_base`: the same with the target
  separated over the base, so that the hypothesis that the two morphisms agree after the
  structure morphism is automatic.

## Implementation notes

The witnesses are not required to be algebraic spaces, nor the morphisms `a` to be monomorphisms
or to have any local property: only the two identities `a ≫ f = a ≫ g` and
`p ∈ Set.range (pointsMap B S hS W a)` are used, the first through
`AlgebraicGeometry.Space.le_eqSubfunctor_iff` at the range of `a` and the second through the
inclusion of that range in the agreement locus.

## References

* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 084N](https://stacks.math.columbia.edu/tag/084N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {T X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The range of a morphism into `X` lies in the agreement locus of two morphisms out of `X`
which it equalizes. -/
theorem range_le_eqSubfunctor_of_comp_eq
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : Y ⟶ T) (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q)
    (a : W ⟶ X) (ha : a ≫ f = a ≫ g) :
    Subfunctor.range a ≤ eqSubfunctor B S hS q f g hfg := by
  refine (le_eqSubfunctor_iff B S hS q f g hfg _).2 ?_
  refine (cancel_epi (Subfunctor.toRange a)).1 ?_
  calc Subfunctor.toRange a ≫ (Subfunctor.range a).ι ≫ f
      = a ≫ f := by rw [← Category.assoc, Subfunctor.toRange_ι]
    _ = a ≫ g := ha
    _ = Subfunctor.toRange a ≫ (Subfunctor.range a).ι ≫ g := by
        rw [← Category.assoc, Subfunctor.toRange_ι]

/-- A point in the image of a morphism whose range lies in a subfunctor lies in the point set of
that subfunctor. -/
theorem mem_range_pointsMap_ι_of_range_le {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : W ⟶ X)
    (E : Subfunctor X) (hle : Subfunctor.range a ≤ E) {p : points B S hS X}
    (hp : p ∈ Set.range (pointsMap B S hS W a)) :
    p ∈ Set.range (pointsMap B S hS E.toFunctor E.ι) := by
  obtain ⟨w, rfl⟩ := hp
  refine ⟨pointsMap B S hS W (Subfunctor.toRange a ≫ Subfunctor.homOfLe hle) w, ?_⟩
  rw [← pointsMap_comp_apply, Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι]

/-- **Two morphisms which agree along a witness at every point of a dense set are equal.**  Let
`X` be a reduced algebraic space over `S` and `Y` an algebraic space separated over an algebraic
space `T` by `q`.  Let `f, g : X ⟶ Y` be morphisms over `q` and let `D` be a dense set of points
of `X` such that every point of `D` lies in the image on points of some morphism `a : W ⟶ X`
with `a ≫ f = a ≫ g`.  Then `f = g`.

The agreement locus of `f` and `g` is a closed subspace of `X` by Stacks 084N; each witness puts
its own image on points inside it, so its point set contains `D` and therefore all of `|X|`; and
a closed subspace of a reduced algebraic space whose point set is everything is the whole space
by Stacks 03JJ. -/
theorem eq_of_eq_on_dense_witnessed (hT : IsAlgebraicSpace B S hS T)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsReduced W))
    (q : Y ⟶ T) (hq : IsSeparated B S hS q) (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q)
    (D : Set (points B S hS X)) (hdense : Dense D)
    (hwit : ∀ p ∈ D, ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (a : W ⟶ X),
      a ≫ f = a ≫ g ∧ p ∈ Set.range (pointsMap B S hS W a)) :
    f = g := by
  set E := eqSubfunctor B S hS q f g hfg with hEdef
  have hE : IsClosedSubspace B S hS E :=
    isClosedSubspace_eqSubfunctor B S hS hT hX hY q f g hfg hq
  have hclosed : IsClosed (Set.range (pointsMap B S hS E.toFunctor E.ι)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B S hS hX E.ι hE.2
  have hDsub : D ⊆ Set.range (pointsMap B S hS E.toFunctor E.ι) := by
    intro p hp
    obtain ⟨W, a, ha, hpa⟩ := hwit p hp
    exact mem_range_pointsMap_ι_of_range_le B S hS a E
      (hEdef ▸ range_le_eqSubfunctor_of_comp_eq B S hS q f g hfg a ha) hpa
  have hfull : Set.range (pointsMap B S hS E.toFunctor E.ι) = Set.univ := by
    refine Set.eq_univ_iff_forall.2 fun x ↦ ?_
    have hx : x ∈ closure D := by rw [hdense.closure_eq]; trivial
    exact closure_minimal hDsub hclosed hx
  obtain ⟨l, hl⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX hX E hE
    hXred (𝟙 X)).2 (by rw [hfull]; exact Set.subset_univ _)
  refine (eqSubfunctor_eq_top_iff B S hS q f g hfg).1 (le_antisymm le_top ?_)
  intro V x _
  have hval : (l.app V x).1 = x := congrArg (fun j : X ⟶ X => j.app V x) hl
  exact hval ▸ (l.app V x).2

/-- **The same with the target separated over the base.**  The base is terminal among presheaves
on the site, so the hypothesis that the two morphisms agree after the structure morphism of the
target is automatic. -/
theorem eq_of_eq_on_dense_witnessed_base (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hXred : HasEtaleLocalProperty B S hS X (fun W : Scheme.{u} => IsReduced W))
    (hT : IsTerminal T) (hTalg : IsAlgebraicSpace B S hS T) (q : Y ⟶ T)
    (hq : IsSeparated B S hS q) (f g : X ⟶ Y)
    (D : Set (points B S hS X)) (hdense : Dense D)
    (hwit : ∀ p ∈ D, ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (a : W ⟶ X),
      a ≫ f = a ≫ g ∧ p ∈ Set.range (pointsMap B S hS W a)) :
    f = g :=
  eq_of_eq_on_dense_witnessed B S hS hTalg hX hY hXred q hq f g (hT.hom_ext _ _) D hdense hwit

end AlgebraicGeometry.Space

end
