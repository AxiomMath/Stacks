module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationFunctorIsoOfIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationIsoOfFunctorIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationMotiveTate
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilRealizationUnique

/-!
# Weil data and realizations: the bijection, from the restriction to correspondences

Data (D0)–(D3) satisfying (A), (B), (C) (`Stacks.WeilCohomology.WeilDataAxioms`) and realizations
`G : M_k ⥤ graded F-vector spaces` (`Stacks.WeilCohomology.WeilRealization`) are related when the
restriction of `G` along `X ↦ (X, 1, 0)` is monoidally isomorphic to the realization of
correspondences of degree zero of Stacks 0FHL attached to the data
(`Stacks.WeilCohomology.WeilDataAxioms.Realizes`). This file shows that this relation induces a
bijection between isomorphism classes (`Stacks.WeilCohomology.WeilDataAxioms.exists_quotientEquiv`)
as soon as every realization is related to some data: isomorphic data have isomorphic
realizations of correspondences (Stacks 0FHL), the realizations of correspondences determine the
data up to isomorphism, and a realization is determined by its restriction (Stacks 0FGH).

## References

* [Stacks Project, Tag 0FGH](https://stacks.math.columbia.edu/tag/0FGH)
* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology.WeilDataAxioms

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F]

section

attribute [local instance 10000] GradedObject.koszulBraidedCategory
  GradedObject.koszulSymmetricCategory

attribute [local instance] WeilData.corrFunctorBraided

/-- **A realization `G` realizes the data `T`**: the restriction of `G` to correspondences of
degree zero is monoidally isomorphic to the realization `c ↦ pr₂,*(γ(c) ∪ pr₁^*-)` of
Stacks 0FHL. -/
def Realizes (T : WeilDataAxioms k F) (G : WeilRealization k F) : Prop :=
  ∃ θ : TwistedKaroubi.untwistedOfObj (CorrespondenceCategory k) ⋙ G.functor ≅
      WeilData.corrFunctor T.poincareDuality T.kunneth T.cycleClassAxiom,
    NatTrans.IsMonoidal θ.hom

/-- The realization `T.toWeilRealization` attached to the data `T` realizes `T`. -/
theorem realizes_toWeilRealization (T : WeilDataAxioms k F) : T.Realizes T.toWeilRealization :=
  ⟨T.toWeilRealizationIso, inferInstance⟩

/-- If `G` realizes `T` and `T` is isomorphic to `T'`, then `G` realizes `T'`. -/
theorem Realizes.of_isIsomorphic {T T' : WeilDataAxioms k F} {G : WeilRealization k F}
    (h : (isoSetoid k F).r T T') (hT : T.Realizes G) : T'.Realizes G := by
  obtain ⟨θ, hθ⟩ := hT
  obtain ⟨ι, hι⟩ := WeilData.IsIsomorphic.nonempty_corrFunctorIso (hA := T.poincareDuality)
    (hB := T.kunneth) (hC := T.cycleClassAxiom) (hA' := T'.poincareDuality) (hB' := T'.kunneth)
    (hC' := T'.cycleClassAxiom) h
  exact ⟨θ ≪≫ ι, inferInstanceAs (NatTrans.IsMonoidal (θ.hom ≫ ι.hom))⟩

/-- If `G` realizes `T` and `G` is isomorphic to `G'`, then `G'` realizes `T`. -/
theorem Realizes.of_iso {T : WeilDataAxioms k F} {G G' : WeilRealization k F}
    (h : (WeilRealization.isoSetoid k F).r G G') (hT : T.Realizes G) : T.Realizes G' := by
  obtain ⟨θ, hθ⟩ := hT
  obtain ⟨e⟩ := h
  exact ⟨Functor.isoWhiskerLeft _ e.iso.symm ≪≫ θ,
    inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerLeft _ e.iso.inv ≫ θ.hom))⟩

/-- Two data realized by the same realization `G` are isomorphic. -/
theorem Realizes.isIsomorphic {T T' : WeilDataAxioms k F} {G : WeilRealization k F}
    (hT : T.Realizes G) (hT' : T'.Realizes G) : (isoSetoid k F).r T T' := by
  obtain ⟨θ, hθ⟩ := hT
  obtain ⟨θ', hθ'⟩ := hT'
  have : NatTrans.IsMonoidal (θ.symm ≪≫ θ').hom :=
    inferInstanceAs (NatTrans.IsMonoidal (θ.inv ≫ θ'.hom))
  exact WeilData.isIsomorphic_of_corrFunctorIso (θ.symm ≪≫ θ')

/-- If `G` realizes `T`, then `G` is isomorphic to the realization `T.toWeilRealization`. -/
theorem Realizes.rel_toWeilRealization {T : WeilDataAxioms k F} {G : WeilRealization k F}
    (hT : T.Realizes G) : (WeilRealization.isoSetoid k F).r T.toWeilRealization G := by
  obtain ⟨θ, hθ⟩ := hT
  exact WeilRealization.rel_of_untwisted _ _ _ T.toWeilRealizationIso θ

/-- **The bijection of Stacks 0FHM, from the restriction to correspondences.** If every
realization `G` realizes some data `Ψ(G)`, then `T ↦ G_T` (Stacks 0FHL) and `G ↦ Ψ(G)` are
mutually inverse bijections between isomorphism classes of data (D0)–(D3) satisfying (A), (B),
(C) and isomorphism classes of realizations. -/
theorem exists_quotientEquiv (Ψ : WeilRealization k F → WeilDataAxioms k F)
    (hΨ : ∀ G, (Ψ G).Realizes G) :
    ∃ e : Quotient (isoSetoid k F) ≃ Quotient (WeilRealization.isoSetoid k F),
      (∀ T, e ⟦T⟧ = ⟦T.toWeilRealization⟧) ∧ ∀ G, e.symm ⟦G⟧ = ⟦Ψ G⟧ :=
  exists_quotientEquiv_of_rel (sα := isoSetoid k F) (sβ := WeilRealization.isoSetoid k F)
    Realizes toWeilRealization Ψ realizes_toWeilRealization hΨ
    (fun _ _ _ h hT ↦ hT.of_isIsomorphic h) (fun _ _ _ h hT ↦ hT.of_iso h)
    (fun _ _ _ hT hT' ↦ hT.isIsomorphic hT') (fun _ _ hT ↦ hT.rel_toWeilRealization)

end

end Stacks.WeilCohomology.WeilDataAxioms

end
