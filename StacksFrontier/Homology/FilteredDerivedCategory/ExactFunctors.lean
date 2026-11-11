module

public import StacksFrontier.Homology.FilteredDerivedCategory.Triangulated

/-!
# The functors `gr^p`, `gr` and `(forget F)` on the filtered derived category

Let `𝒜` be an abelian category, `DF(𝒜) = FQis(𝒜)⁻¹K(Fil^f(𝒜))` its filtered derived category
([Stacks, Tag 05S2]) and `Gr(𝒜)` the abelian category of graded objects of `𝒜`
([Stacks, Tag 0126]). The additive functors `gr^p, (forget F) : Fil^f(𝒜) ⥤ 𝒜` and
`gr : Fil^f(𝒜) ⥤ Gr(𝒜)` induce triangulated functors on homotopy categories, and composed with
the localisation functors they invert the filtered quasi-isomorphisms; so they factor through
`Qh : K(Fil^f(𝒜)) ⥤ DF(𝒜)`, and the factorisations are exact functors
`gr^p, (forget F) : DF(𝒜) ⥤ D(𝒜)` and `gr : DF(𝒜) ⥤ D(Gr(𝒜))` commuting with the localisation
functors ([Stacks, Tag 05S3]).

## Main definitions

* `CochainComplex.FilteredDerivedCategory.grGradedDF`: the functor `gr : DF(𝒜) ⥤ D(Gr(𝒜))`;
  the functors `gr^p, (forget F) : DF(𝒜) ⥤ D(𝒜)` are `CochainComplex.FilteredDerivedCategory.grDF`
  and `CochainComplex.FilteredDerivedCategory.forgetDF`.

## Main results

* `CategoryTheory.GradedObject.quasiIso_of_forall_quasiIso_map_eval`: a morphism of complexes of
  graded objects which is a quasi-isomorphism in each degree of the grading is a
  quasi-isomorphism.
* `CochainComplex.FilteredDerivedCategory.isTriangulated_lift`: the functor `DF(𝒜) ⥤ D(B)`
  induced by an additive functor `Fil^f(𝒜) ⥤ B` is triangulated.
* `CochainComplex.FilteredDerivedCategory.isTriangulated_grDF_forgetDF_grGradedDF`:
  [Stacks, Tag 05S3].

## Implementation notes

The induced functors are `CategoryTheory.Localization.lift` along `Qh` ([Stacks, Tag 05R7]);
their commutation with the shifts is `CategoryTheory.Functor.commShiftOfLocalization`, and
exactness follows because every distinguished triangle of `DF(𝒜)` is isomorphic to the image of
a distinguished triangle of `K(Fil^f(𝒜))` (`CategoryTheory.Functor.isTriangulated_of_precomp_iso`).
`Gr(𝒜)` is `CategoryTheory.GradedObject ℤ 𝒜`, abelian by [Stacks, Tag 0126], and the derived
category `D(Gr(𝒜))` is formed under `[HasDerivedCategory (GradedObject ℤ 𝒜)]`, as `D(𝒜)` is under
`[HasDerivedCategory 𝒜]`.

## References

* [Stacks Project, Tag 05S3](https://stacks.math.columbia.edu/tag/05S3)
* [Stacks Project, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
* [Stacks Project, Tag 0126](https://stacks.math.columbia.edu/tag/0126)
-/

@[expose] public section

universe w w' v' u' v u

open CategoryTheory Limits Pretriangulated Opposite HomologicalComplex

noncomputable section

namespace CategoryTheory.GradedObject

/-- A morphism of complexes of graded objects of an abelian category is a quasi-isomorphism as
soon as it is one in each degree `b` of the grading: homology of graded objects is computed
componentwise, the evaluation functors being exact. -/
lemma quasiIso_of_forall_quasiIso_map_eval {β : Type*} {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex (GradedObject β C) c}
    (φ : K ⟶ L) (h : ∀ b, QuasiIso (((eval b).mapHomologicalComplex c).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff]
  have γ : ShortComplex.LeftHomologyMapData ((shortComplexFunctor _ c i).map φ)
      ((shortComplexFunctor _ c i).obj K).leftHomologyData
      ((shortComplexFunctor _ c i).obj L).leftHomologyData := default
  rw [γ.quasiIso_iff]
  have hb : ∀ b, IsIso (γ.φH b) := fun b => by
    have hb := (h b).quasiIsoAt i
    rw [quasiIsoAt_iff] at hb
    have h' := (γ.map (eval b)).quasiIso_iff.1 hb
    rwa [ShortComplex.LeftHomologyMapData.map_φH] at h'
  exact isIso_of_isIso_apply _

end CategoryTheory.GradedObject

namespace CochainComplex.FilteredDerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

section Lift

variable {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (G : FiniteFilteredObject 𝒜 ⥤ B) [G.Additive]
  (hG : (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
    (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh))

/-- The functor `DF(𝒜) ⥤ D(B)` induced by an additive functor `G : Fil^f(𝒜) ⥤ B` whose
extension `K(Fil^f(𝒜)) ⥤ K(B) ⥤ D(B)` inverts the filtered quasi-isomorphisms commutes with the
shifts, by the commutation of `G` and of the localisation functors with the shifts. -/
noncomputable instance commShift_lift :
    (Localization.lift _ hG Qh : FilteredDerivedCategory 𝒜 ⥤ DerivedCategory B).CommShift ℤ :=
  Functor.commShiftOfLocalization Qh (HomotopyCategory.filteredQuasiIso 𝒜) ℤ
    (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) _

/-- The isomorphism `Qh ⋙ G_DF ≅ G ⋙ Q` expressing that the induced functor commutes with the
localisation functors is compatible with the shifts. -/
instance commShift_fac_hom : NatTrans.CommShift (Localization.fac _ hG Qh).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization Qh (HomotopyCategory.filteredQuasiIso 𝒜) ℤ
    (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) (Localization.lift _ hG Qh)

/-- The functor `DF(𝒜) ⥤ D(B)` induced by `G` is exact: every distinguished triangle of `DF(𝒜)`
is the image of one of `K(Fil^f(𝒜))`, which `G` and `Q` carry to a distinguished triangle. -/
instance isTriangulated_lift :
    (Localization.lift _ hG Qh : FilteredDerivedCategory 𝒜 ⥤ DerivedCategory B).IsTriangulated :=
  have : (Qh (𝒜 := 𝒜)).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow Qh (HomotopyCategory.filteredAcyclic 𝒜).trW
  Functor.isTriangulated_of_precomp_iso (Localization.fac _ hG Qh)

end Lift

/-- `gr : K(Fil^f(𝒜)) ⥤ K(Gr(𝒜))` followed by the localisation to `D(Gr(𝒜))` inverts the
filtered quasi-isomorphisms: `gr(α)` is a quasi-isomorphism of complexes of graded objects
because each of its pieces `gr^p(α)` is a quasi-isomorphism. -/
lemma gr_inverts [HasDerivedCategory.{w'} (GradedObject ℤ 𝒜)] :
    (HomotopyCategory.filteredQuasiIso 𝒜).IsInvertedBy
      ((FiniteFilteredObject.gr (𝒜 := 𝒜)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
  rintro ⟨K⟩ ⟨L⟩ f hf
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  have hg := (filteredQuasiIso_quotient_map_iff g).1 hf
  have : QuasiIso ((FiniteFilteredObject.gr.mapHomologicalComplex _).map g) :=
    GradedObject.quasiIso_of_forall_quasiIso_map_eval _ fun p => hg p
  exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 this)

/-- `gr : DF(𝒜) ⥤ D(Gr(𝒜))`, the functor induced by `gr : K(Fil^f(𝒜)) ⥤ K(Gr(𝒜))`. -/
noncomputable abbrev grGradedDF [HasDerivedCategory.{w'} (GradedObject ℤ 𝒜)] :
    FilteredDerivedCategory 𝒜 ⥤ DerivedCategory (GradedObject ℤ 𝒜) :=
  Localization.lift _ (gr_inverts (𝒜 := 𝒜)) Qh

variable [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w'} (GradedObject ℤ 𝒜)]

/-- **Stacks 05S3.** Let `𝒜` be an abelian category, `DF(𝒜) = FQis(𝒜)⁻¹K(Fil^f(𝒜))` its filtered
derived category and `Gr(𝒜)` the abelian category of graded objects of `𝒜`. The functors
`gr^p, (forget F) : K(Fil^f(𝒜)) ⥤ K(𝒜)` and `gr : K(Fil^f(𝒜)) ⥤ K(Gr(𝒜))` induce canonical exact
functors `gr^p, (forget F) : DF(𝒜) ⥤ D(𝒜)` and `gr : DF(𝒜) ⥤ D(Gr(𝒜))` which commute with the
localisation functors. Each induced functor (`grDF p`, `forgetDF`, `grGradedDF`) is triangulated,
and it comes with an isomorphism `Qh ⋙ gr^p ≅ gr^p ⋙ Q`, `Qh ⋙ (forget F) ≅ (forget F) ⋙ Q`,
resp. `Qh ⋙ gr ≅ gr ⋙ Q`, between the two composites `K(Fil^f(𝒜)) ⥤ D(𝒜)`, resp.
`K(Fil^f(𝒜)) ⥤ D(Gr(𝒜))`, which is compatible with the shifts. The functors are the
factorisations through the localisation `Qh` given by its universal property
([Stacks, Tag 05R7]); `(forget F)` factors because a filtered quasi-isomorphism of complexes of
finitely filtered objects is a quasi-isomorphism
(`CochainComplex.isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso`). -/
@[stacks 05S3]
theorem isTriangulated_grDF_forgetDF_grGradedDF :
    (∀ p : ℤ, (grDF (𝒜 := 𝒜) p).IsTriangulated ∧
      ∃ e : Qh (𝒜 := 𝒜) ⋙ grDF p ≅
          (FiniteFilteredObject.grP p).mapHomotopyCategory _ ⋙ DerivedCategory.Qh,
        NatTrans.CommShift e.hom ℤ) ∧
    ((forgetDF (𝒜 := 𝒜)).IsTriangulated ∧
      ∃ e : Qh (𝒜 := 𝒜) ⋙ forgetDF ≅
          FiniteFilteredObject.forget.mapHomotopyCategory _ ⋙ DerivedCategory.Qh,
        NatTrans.CommShift e.hom ℤ) ∧
    ((grGradedDF (𝒜 := 𝒜)).IsTriangulated ∧
      ∃ e : Qh (𝒜 := 𝒜) ⋙ grGradedDF (𝒜 := 𝒜) ≅
          FiniteFilteredObject.gr.mapHomotopyCategory _ ⋙ DerivedCategory.Qh,
        NatTrans.CommShift e.hom ℤ) :=
  ⟨fun _ => ⟨inferInstance, Localization.fac _ _ _, inferInstance⟩,
    ⟨inferInstance, Localization.fac _ _ _, inferInstance⟩,
    ⟨inferInstance, Localization.fac _ _ _, inferInstance⟩⟩

end CochainComplex.FilteredDerivedCategory


end
