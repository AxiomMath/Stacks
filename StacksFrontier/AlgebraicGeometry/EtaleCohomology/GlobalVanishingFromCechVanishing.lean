module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FilteredColimitsAndCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Global étale cohomology from Čech vanishing on the finite quasi-compact separated coverings

Let `X` be a quasi-compact and quasi-separated scheme. The objects of its small étale site which
are quasi-compact and separated over `X` — `Stacks.EtaleCohomology.qcSeparatedOver` — contain `X`
itself, are closed under the nonempty finite fibre products of a covering family, and the finite
coverings by them are cofinal among all coverings of such an object. Those are exactly the three
hypotheses which [Stacks, Tag 03F9] asks of a collection of objects and a collection of their
coverings, and `X` being a member is what turns the object-level conclusion of that tag into a
statement about the **global** étale cohomology of `X`.

This file draws that conclusion: an abelian sheaf on the small étale site of `X` whose
positive-degree Čech cohomology vanishes on every finite covering by objects quasi-compact and
separated over `X` has vanishing positive-degree global cohomology
`CategoryTheory.Sheaf.H`.

## Why this is the useful form

Global cohomology is `Ext` out of the constant sheaf, and the constant sheaf is the free abelian
sheaf on the *terminal sheaf*, not on an object. The direct route to a global vanishing statement
therefore resolves the terminal sheaf by free abelian sheaves on representables, which asks for a
hypercovering in every degree; a finite cover of `X` by affines and finite covers of its pairwise
intersections — a one-hypercover — control only degrees `≤ 1` and do not suffice.

Nothing of the kind is needed. A quasi-compact and quasi-separated `X` *is* an object of its own
small étale site, so the terminal sheaf is representable there, and the Čech complexes of ordinary
coverings are the only complexes involved. The price is that the coverings must be by objects
quasi-compact and separated over `X` rather than by affines: the fibre products of affine objects
over a non-separated base are not affine, and a collection of objects closed under those fibre
products is the least that Tag 03F9 can be run on.

## Main results

* `Stacks.EtaleCohomology.mem_qcSeparatedOver_of_iso`: the objects quasi-compact and separated
  over `X` form a set closed under isomorphism, which is what lets the chosen fibre products of
  a covering family be *members* of it and not merely isomorphic to members.
* `Stacks.EtaleCohomology.hasProduct_over_qcSepCovering` and
  `Stacks.EtaleCohomology.product_over_mem_qcSeparatedOver`: the iterated fibre products of a
  finite covering by such objects exist in the slice and are again such objects.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_cechCohomology_isZero_smallEtale`: **the
  conclusion.** Čech vanishing on the finite coverings by objects quasi-compact and separated
  over `X` gives vanishing of the global étale cohomology of `X` in positive degrees.

## Implementation notes

The universes of [Stacks, Tag 03F9] in the form used here,
`Stacks.CechSite.subsingleton_sheafH_of_cechCohomology_isZero`, are the object universe `u + 1`
of `AlgebraicGeometry.Scheme.Etale`, its morphism universe `u`, the index universe `u` of the
covering families of `Stacks.EtaleCohomology.qcSepCovering`, and a free universe `a` which is set
to `u`; the coefficients are then `AddCommGrpCat.{u + 1}`, the first universe in which the small
étale site of a scheme has sheafification.

No `@[stacks]` attribute is placed. Tag 03F9 is carried by
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero` and by
`Stacks.CechSite.subsingleton_ext_of_cechCohomology_isZero`, and this file only instantiates it;
tag 03Q5, whose collection of objects is the same one, is carried by
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale`.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- **The objects quasi-compact and separated over `X` are closed under isomorphism.** An
isomorphism of the small étale site is an isomorphism of the underlying schemes commuting with the
structure morphisms, and both quasi-compactness and separatedness of a morphism are unchanged by
precomposition with an isomorphism.

This is what a consumer asking for *membership* of a chosen limit needs: a chosen fibre product
is determined only up to isomorphism, so
`Stacks.Cohomology.HasIntersectionsIn.exists_mem_iso_prod_over` produces an isomorphism to a
member and not a member. -/
theorem mem_qcSeparatedOver_of_iso {V W : X.Etale} (e : V ≅ W)
    (hW : W ∈ qcSeparatedOver X) : V ∈ qcSeparatedOver X := by
  obtain ⟨hq, hs⟩ := hW
  have hiso : IsIso e.hom.left := by
    have h : IsIso ((Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X).map e.hom) :=
      inferInstance
    exact h
  have hw : V.hom = e.hom.left ≫ W.hom := (MorphismProperty.Over.w e.hom).symm
  have := hq
  refine ⟨hw ▸ (inferInstance : QuasiCompact (e.hom.left ≫ W.hom)), ?_⟩
  rw [hw]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated) _ _).2 hs

/-- The iterated fibre products of a finite covering by objects quasi-compact and separated over
`X` exist, as products in the slice over the object being covered. -/
theorem hasProduct_over_qcSepCovering {U : X.Etale} {E : PreZeroHypercover.{u} U}
    (hE : E ∈ qcSepCovering X U) (n : ℕ) (a : Fin (n + 1) → E.I₀) :
    HasProduct (fun i ↦ Over.mk (E.f (a i))) :=
  Stacks.Cohomology.HasIntersectionsIn.hasProduct_over
    (hasIntersectionsIn_qcSeparatedOver U E hE) n a

/-- Those iterated fibre products are again objects quasi-compact and separated over `X`. -/
theorem product_over_mem_qcSeparatedOver {U : X.Etale} {E : PreZeroHypercover.{u} U}
    (hE : E ∈ qcSepCovering X U) (n : ℕ) (a : Fin (n + 1) → E.I₀)
    [HasProduct (fun i ↦ Over.mk (E.f (a i)))] :
    (∏ᶜ (fun i ↦ Over.mk (E.f (a i)))).left ∈ qcSeparatedOver X := by
  obtain ⟨V, hV, ⟨e⟩⟩ := Stacks.Cohomology.HasIntersectionsIn.exists_mem_iso_prod_over
    (hasIntersectionsIn_qcSeparatedOver U E hE) n a
  exact mem_qcSeparatedOver_of_iso e hV

/-- `X` is a terminal object of its own small étale site: its structure morphism is the
identity. -/
def etaleMkIdIsTerminal (X : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  have : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))

/-- **Global étale cohomology from Čech vanishing on the finite quasi-compact separated
coverings.** Let `X` be quasi-compact and quasi-separated and let `F` be an abelian sheaf on its
small étale site. If the Čech cohomology of `F` vanishes in positive degrees on every finite
covering by objects quasi-compact and separated over `X`, then the global étale cohomology
`H^p(X, F)` vanishes for every `p > 0`.

This is [Stacks, Tag 03F9] with the collection of objects
`Stacks.EtaleCohomology.qcSeparatedOver X` and the collection of coverings
`Stacks.EtaleCohomology.qcSepCovering X`, read at the terminal object `X`, which belongs to the
collection because `X` is quasi-compact and quasi-separated. The three hypotheses of the tag are
`Stacks.EtaleCohomology.hasProduct_over_qcSepCovering`,
`Stacks.EtaleCohomology.product_over_mem_qcSeparatedOver` together with the two membership
clauses of `Stacks.EtaleCohomology.qcSepCovering`, and
`Stacks.EtaleCohomology.exists_qcSepCovering_le`. -/
theorem subsingleton_sheafH_of_cechCohomology_isZero_smallEtale (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hCech : ∀ {U : X.Etale} (E : PreZeroHypercover.{u} U) (hE : E ∈ qcSepCovering X U)
      (q : ℕ), 0 < q →
        letI : ∀ (n : ℕ) (a : Fin (n + 1) → E.I₀),
            HasProduct (fun i ↦ Over.mk (E.f (a i))) :=
          fun n a ↦ hasProduct_over_qcSepCovering hE n a
        IsZero (Stacks.CechSite.cechCohomology E F.obj q))
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H F p) :=
  Stacks.CechSite.subsingleton_sheafH_of_cechCohomology_isZero.{u + 1, u}
    X.smallEtaleTopology (qcSeparatedOver X)
    (fun U ↦ {E | E.1 ∈ qcSepCovering X U})
    (fun {_} _ hE n a ↦ hasProduct_over_qcSepCovering hE n a)
    (fun {_} _ hE ↦ ⟨hE.2.1, hE.2.2.1, fun n a ↦ product_over_mem_qcSeparatedOver hE n a⟩)
    (fun U hU R hR ↦ by
      obtain ⟨E, hE, hle⟩ := exists_qcSepCovering_le U hU R hR
      exact ⟨⟨E, hE.2.2.2⟩, hE, hle⟩)
    F (fun {_} E hE q hq ↦ hCech E.1 hE q hq)
    (etaleMkIdIsTerminal X) (etaleMkId_mem_qcSeparatedOver X) p hp

end Stacks.EtaleCohomology

end
