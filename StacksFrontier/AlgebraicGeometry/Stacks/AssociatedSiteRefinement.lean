module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtalePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage

/-!
# Refining a covering sieve of an associated site by a chosen covering family

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of a scheme
`S` in a big fppf site `B`, and give `𝒳` the site of **Stacks 06TP** for a topology `τ` on the
underlying category of schemes of `B`, namely
`AlgebraicGeometry.Stack.associatedTopology B S hS p τ`. The generating covering families of that
topology only ask that the image of a family *generate* a `τ`-covering sieve downstairs, and the
topology is their saturation. This file sharpens both at once: every covering sieve of the
associated site contains a family whose image under `p` is one of the *chosen* covering families
of the ambient site, whenever the same holds one level down.

Two nested inherited structures have to be unwound for that, and the content is all in the
second. The chosen families of the base are stable under isomorphisms, composition and base
change, so the same holds of the families of strongly cartesian morphisms over them
(**Stacks 06NU**) and the saturation adds nothing beyond refinements
(`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`). The chosen
family downstairs produced by the hypothesis is then lifted through the factorizations its members
have, by `CategoryTheory.Functor.IsFibered.exists_isStronglyCartesian`.

Nothing here is specific to a topology or to a class of chosen families: both are parameters, the
base-level refinement being a hypothesis. The two instantiations the library needs are the fppf
one — the chosen families of `B` itself, at `τ = B.topology` — and the étale one, the chosen étale
families of **Stacks 03FF** at `τ = AlgebraicGeometry.etaleTopology B`, both of which are supplied
here at the level of the big fppf category over `S`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_etaleCovering_le_of_mem_etaleTopology`: a covering sieve
  of the big étale topology localized at `S` contains a chosen étale covering family.
* `AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`: a covering sieve
  of the site of **Stacks 06TP** contains a family whose image is a chosen covering family, for an
  arbitrary topology on the base and an arbitrary class of chosen families on the big fppf
  category over `S`.

## Implementation notes

The cartesian lift of a member of the chosen family gives an *equality* `p.obj (w i) = E₂.X i` of
objects, from `CategoryTheory.Functor.IsHomLift.domain_eq`, not an isomorphism, so the image of
the lifted family is not syntactically the family one started with. Since the chosen-family
condition is a predicate on a bundled `CategoryTheory.Covering` it cannot be transported
member-by-member, and the two pre-`0`-hypercovers have to be proved equal; that is what
`AlgebraicGeometry.Stack.preZeroHypercover_eq_of_objs_eq` below does, and the load-bearing step is
proof irrelevance — after substituting the equality of the object families the remaining
hypothesis is definitionally `rfl`, so `CategoryTheory.eqToHom_refl`, which is stated for an
arbitrary proof, fires.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve of the big étale topology localized at `S` contains a chosen étale covering
family.** This is `AlgebraicGeometry.exists_etaleCovering_le_of_mem_etaleTopology` after
localization at `S`: a covering sieve of `(AlgebraicGeometry.etaleTopology B).over (B.obj hS)` is
by definition one whose image under `CategoryTheory.Sieve.overEquiv` covers downstairs, and a
chosen étale covering family refining that image is read back upstairs by equipping each of its
members with the composite structure morphism to `S`. -/
theorem BigFppfOver.exists_etaleCovering_le_of_mem_etaleTopology
    {U : BigFppfOver B S hS} {R : Sieve U}
    (hR : R ∈ (etaleTopology B).over (B.obj hS) U) :
    ∃ E : PreZeroHypercover.{u + 1} U,
      etaleCovering B ⟨(BigFppfOver.forget B S hS).obj U,
        E.map (BigFppfOver.forget B S hS)⟩ ∧ E.presieve₀ ≤ R.arrows := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hle⟩ :=
    _root_.AlgebraicGeometry.exists_etaleCovering_le_of_mem_etaleTopology B hR
  refine ⟨⟨E.I₀, fun i => Over.mk (E.f i ≫ U.hom), fun i => Over.homMk (E.f i) rfl⟩, ?_, ?_⟩
  · change etaleCovering B ⟨U.left, _⟩
    simpa [PreZeroHypercover.map] using hE
  · rw [Presieve.ofArrows_le_iff]
    intro i
    exact (Sieve.overEquiv_iff R (E.f i)).mp (hle _ _ ⟨i⟩)

namespace Stack

/-- Two pre-`0`-hypercovers over the same index type are equal as soon as their objects agree and
their morphisms agree after the identification of those objects. -/
theorem preZeroHypercover_eq_of_objs_eq {C : Type*} [Category C] {U : C} {I : Type*}
    {Z W : I → C} {g : ∀ i, Z i ⟶ U} {f : ∀ i, W i ⟶ U} (h : ∀ i, Z i = W i)
    (hg : ∀ i, g i = eqToHom (h i) ≫ f i) :
    (⟨I, Z, g⟩ : PreZeroHypercover U) = ⟨I, W, f⟩ := by
  have hZW : Z = W := funext h
  subst hZW
  have hgf : g = f := funext fun i => by simpa using hg i
  subst hgf
  rfl

universe v v'

variable {X : Type v} [Category.{v'} X] (p : X ⥤ BigFppfOver B S hS)

/-- **A covering sieve of the site of Stacks 06TP contains a family whose image is a chosen
covering family.** The generating covering families of
`AlgebraicGeometry.Stack.associatedTopology` only ask that the image *generate* a covering sieve,
and the topology is their saturation; this sharpens both, for an arbitrary topology `τ` on the
underlying category of schemes and an arbitrary class `C` of chosen covering families on the big
fppf category over `S`, given the corresponding statement for `C` one level down.

See the module documentation for the shape of the argument. -/
theorem exists_chosenCovering_le_of_mem_associatedTopology
    (τ : GrothendieckTopology B.Schemes) (C : Covering (BigFppfOver B S hS) → Prop)
    (hbase : ∀ ⦃U : BigFppfOver B S hS⦄ {R : Sieve U}, R ∈ τ.over (B.obj hS) U →
      ∃ E : PreZeroHypercover.{u + 1} U, C ⟨U, E⟩ ∧ E.presieve₀ ≤ R.arrows)
    (hp : p.IsFiberedInGroupoids)
    ⦃y : X⦄ (T : Sieve y) (hT : T ∈ associatedTopology B S hS p τ y) :
    ∃ E : PreZeroHypercover.{u + 1} y,
      C ⟨p.obj y, E.map p⟩ ∧ E.presieve₀ ≤ T.arrows := by
  have hfib : p.IsFibered := hp.isFibered
  rw [associatedTopology, Functor.inheritedTopology_eq,
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT
  obtain ⟨R₁, ⟨-, himg⟩, hR₁le⟩ := hT
  rw [GrothendieckTopology.mem_toPrecoverage_iff] at himg
  obtain ⟨E₂, hE₂, hE₂le⟩ := hbase himg
  -- each member of the chosen family downstairs factors through the image of a member of `R₁`
  have hfac : ∀ i : E₂.I₀, ∃ (z : X) (r : z ⟶ y) (c : E₂.X i ⟶ p.obj z),
      R₁ r ∧ c ≫ p.map r = E₂.f i := by
    intro i
    obtain ⟨W, h, g, hg, hcomp⟩ := hE₂le _ _ (Presieve.ofArrows.mk i)
    obtain ⟨hr⟩ := hg
    rename_i z r
    exact ⟨z, r, h, hr, hcomp⟩
  choose z r c hrmem hcomp using hfac
  -- lift the factor cartesianly and compose
  choose w u hu using fun i =>
    Functor.IsFibered.exists_isStronglyCartesian p (Y := z i) (c i)
  have hdom : ∀ i, p.obj (w i) = E₂.X i := fun i =>
    have := hu i; IsHomLift.domain_eq p (c i) (u i)
  have hmapu : ∀ i, p.map (u i) = eqToHom (hdom i) ≫ c i := fun i =>
    have := hu i; by simpa using IsHomLift.fac' p (c i) (u i)
  have key : ∀ i, p.map (u i ≫ r i) = eqToHom (hdom i) ≫ E₂.f i := fun i => by
    rw [p.map_comp, hmapu i, Category.assoc, hcomp i]
  refine ⟨⟨E₂.I₀, w, fun i => u i ≫ r i⟩, ?_, ?_⟩
  · have hmap : PreZeroHypercover.map p ⟨E₂.I₀, w, fun i => u i ≫ r i⟩ = E₂ := by
      obtain ⟨I₀, XX, ff⟩ := E₂
      exact preZeroHypercover_eq_of_objs_eq hdom key
    rw [hmap]
    exact hE₂
  · rw [Presieve.ofArrows_le_iff]
    intro i
    exact T.downward_closed (hR₁le _ _ (hrmem i)) (u i)

/-- **A covering sieve of the étale site of a category fibred in groupoids contains a family whose
image is a chosen étale covering family.** The étale instance of
`AlgebraicGeometry.Stack.exists_chosenCovering_le_of_mem_associatedTopology`, its base-level input
being `AlgebraicGeometry.BigFppfOver.exists_etaleCovering_le_of_mem_etaleTopology`. -/
theorem exists_etaleCovering_le_of_mem_associatedTopology (hp : p.IsFiberedInGroupoids)
    ⦃y : X⦄ (T : Sieve y) (hT : T ∈ associatedTopology B S hS p (etaleTopology B) y) :
    ∃ E : PreZeroHypercover.{u + 1} y,
      etaleCovering B ⟨(BigFppfOver.forget B S hS).obj (p.obj y),
        (E.map p).map (BigFppfOver.forget B S hS)⟩ ∧ E.presieve₀ ≤ T.arrows :=
  exists_chosenCovering_le_of_mem_associatedTopology B S hS p (etaleTopology B)
    (fun E => etaleCovering B ⟨(BigFppfOver.forget B S hS).obj E.1,
      E.2.map (BigFppfOver.forget B S hS)⟩)
    (fun _ _ hR => BigFppfOver.exists_etaleCovering_le_of_mem_etaleTopology B S hS hR) hp T hT

end Stack

end AlgebraicGeometry

end
