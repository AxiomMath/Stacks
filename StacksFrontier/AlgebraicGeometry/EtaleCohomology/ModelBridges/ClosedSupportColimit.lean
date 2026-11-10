module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.AbelianColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkFrameworkBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TorsionConstructibleSubsheaves

/-!
# Abelian sheaves on Mathlib's small étale site supported in a specialization-closed set

Let `X` be a Noetherian scheme and let `E ⊆ X` be stable under specialization. An abelian sheaf
on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology` of `X` whose stalks
vanish at every geometric point lying over a point outside `E` is a filtered colimit of abelian
sheaves, each of whose stalks vanish at the geometric points lying outside some closed subset of
`E`. This is the abelian half of [Stacks, Tag 0F0N] part (2), with the constructibility of the
terms of the colimit dropped, on Mathlib's small étale site.

## Main results

* `AlgebraicGeometry.exists_isFilteredColimit_isClosed_support_smallEtale` — the abelian form of
  [Stacks, Tag 0F0N] part (2) on Mathlib's small étale site.

## Implementation notes

The statement is `AlgebraicGeometry.exists_isFilteredColimit_isClosed_support_abelian`, proved on
the size-bounded small étale site of a big étale site containing `X`, transported along the
equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` of the sheaves on the two sites. The
geometric stalks on the size-bounded site are the stalks on Mathlib's site of the transported
sheaves (`AlgebraicGeometry.smallEtaleStalkAb_sheafEquiv_obj_iso`); so the support of a sheaf on
the size-bounded site is described by the vanishing of the stalks on Mathlib's site of its
transport, which is the form in which the hypothesis and the conclusion are stated. Pushing the
diagram back uses that an equivalence preserves colimits, the vertex being moved onto the given
sheaf by the counit. Each term is finally replaced by the image of its leg
(`Stacks.EtaleCohomology.exists_isColimit_mono_of_isColimit`), so that the terms are subsheaves
of the given sheaf (and hence torsion when it is).

This is the step of the proof of [Stacks, Tag 0F0W] (and of Interlude II in the proof of
[Stacks, Tag 0F0V]) which writes a sheaf supported in the set of points of bounded transcendence
degree as a filtered colimit of sheaves supported on closed subschemes contained in that set.

## References

* [Stacks Project, Tag 0F0N](https://stacks.math.columbia.edu/tag/0F0N)
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-- The stalk at a geometric point of an abelian sheaf on Mathlib's small étale site vanishes
exactly when the stalk of its restriction to the size-bounded small étale site does, the
restriction being the inverse of `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
private theorem isZero_etaleStalk_sheafEquiv_inverse_iff (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) (t : GeometricPoint X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsZero (etaleStalk B X hX t
        ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj G).obj) ↔
      IsZero ((smallEtaleStalkAb t.hom).obj G) := by
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  exact ((smallEtaleStalkAb_sheafEquiv_obj_iso B ⟨X, hX⟩ t (e.inverse.obj G)).symm ≪≫
    (smallEtaleStalkAb t.hom).mapIso (e.counitIso.app G)).isZero_iff

/-- **The abelian form of [Stacks, Tag 0F0N] part (2) on Mathlib's small étale site.** Let `X` be
a Noetherian scheme and let `E ⊆ X` be stable under specialization. An abelian sheaf `G` on
`X_ét` whose stalk vanishes at every geometric point not lying over `E` is a filtered colimit of
abelian subsheaves `D i` (the legs `ι i : D i ⟶ G` are monomorphisms), for each of which there is a
closed subset `W ⊆ E` such that the stalk of `D i` vanishes at every geometric point not lying over
`W`. -/
public theorem exists_isFilteredColimit_isClosed_support_smallEtale {X : Scheme.{u}}
    [IsNoetherian X] (E : Set X) (hE : StableUnderSpecialization E)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∉ E →
      IsZero ((smallEtaleStalkAb s.hom).obj G)) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj G), Nonempty (IsColimit (Cocone.mk G ι)) ∧
        (∀ i, Mono (ι.app i)) ∧
        ∀ i, ∃ W : Set X, IsClosed W ∧ W ⊆ E ∧
          ∀ s : GeometricPoint X, s.hom (IsLocalRing.closedPoint s.residueField) ∉ W →
            IsZero ((smallEtaleStalkAb s.hom).obj (D.obj i)) := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  let X' : B.Scheme := ⟨X, hX⟩
  have : IsNoetherian X'.obj := inferInstanceAs (IsNoetherian X)
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let : Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := sheafIsAbelian
  have hpt : ∀ s : GeometricPoint X,
      s.hom default = s.hom (IsLocalRing.closedPoint s.residueField) := fun s =>
    congrArg s.hom (Subsingleton.elim _ _)
  have hsupp : supportSheaf B X'.obj X'.property (e.inverse.obj G) ⊆ E := by
    rintro x ⟨p, hp, hn⟩
    rw [isZero_etaleStalk_ulift_iff, isZero_etaleStalk_sheafEquiv_inverse_iff] at hn
    rw [← hp, hpt p]
    by_contra hx
    exact hn (hG p hx)
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ :=
    exists_isFilteredColimit_isClosed_support_abelian B X' E hE (e.inverse.obj G) hsupp
  let ι₀ : D ⋙ e.functor ⟶ (Functor.const I).obj G :=
    (e.functor.mapCocone (Cocone.mk (e.inverse.obj G) ι)).ι ≫
      (Functor.const I).map (e.counitIso.app G).hom
  have hcolim₀ : IsColimit (Cocone.mk G ι₀) :=
    IsColimit.ofIsoColimit (isColimitOfPreserves e.functor hcolim)
      (Cocone.ext (e.counitIso.app G) fun _ => rfl)
  obtain ⟨D', ι', ⟨hc'⟩, hD'⟩ := exists_isColimit_mono_of_isColimit hcolim₀
  refine ⟨I, hI, hfilt, D', ι', ⟨hc'⟩, fun i => (hD' i).1, fun i => ?_⟩
  obtain ⟨W, hWclosed, hWE, hWsupp⟩ := hD i
  refine ⟨W, hWclosed, hWE, fun s hs => ?_⟩
  have hnot : s.hom default ∉ supportSheaf B X'.obj X'.property (D.obj i) :=
    fun hmem => hs (hpt s ▸ hWsupp hmem)
  have hzero : IsZero (etaleStalk B X hX s (D.obj i).obj) := by
    by_contra hn
    exact hnot ⟨s, rfl, by rwa [isZero_etaleStalk_ulift_iff]⟩
  -- the new term is a quotient of the old one, and the stalk is right exact
  obtain ⟨p, hp⟩ := (hD' i).2
  have : Epi ((smallEtaleStalkAb s.hom).map p) :=
    preserves_epi_of_preservesColimit (smallEtaleStalkAb s.hom) _
  exact (hzero.of_iso (smallEtaleStalkAb_sheafEquiv_obj_iso B X' s (D.obj i))).of_epi
    ((smallEtaleStalkAb s.hom).map p)

end AlgebraicGeometry

end
