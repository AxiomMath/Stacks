module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleOverlap
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLocus

/-!
# Transport lemmas for the étale descent of Artin's contraction functor

The descent of a section `(Z, u', x̂)` of Artin's contraction functor `F` of Stacks 0GHA along
a covering family `{V_i ⟶ V}` produces the three components separately, and then has to
recognise the result as a single triple. Two kinds of bookkeeping are needed for that, and
this file supplies both.

*Transport along an equality of sets of points.* The second and third components of a triple
are morphisms out of `V ∖ Z` and out of `V_{/Z}`, so their very types depend on the first
component. The descended first component is equal to the inverse image of the given ones, but
not syntactically so, so the comparison of morphisms is a `HEq` and has to be moved across
that equality.

*Transport across the sheafification.* The glueing statements of
`StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescentCompletion` are about the
completion *subfunctor* of Stacks 0AMC, whereas the third component of a triple is a morphism
out of its fppf sheafification. The universal property of sheafification moves a morphism, and
an equality of morphisms, from the one to the other.

## Main results

* `AlgebraicGeometry.Space.heq_openSubspaceOfPointsRestrict_source` and
  `AlgebraicGeometry.Space.heq_completionSheafRestrict_source`: the restriction morphisms read
  over an equality of their source set of points.
* `AlgebraicGeometry.Space.completionSubfunctorRestrict_comp_toSheafify`: the compatibility of
  the restriction morphisms of completion subfunctors with the maps to the sheafification.
* `AlgebraicGeometry.Space.exists_hom_completionSheaf` and
  `AlgebraicGeometry.Space.hom_ext_completionSheaf`: a morphism out of the completion
  subfunctor into an fppf sheaf, compatible with a family of morphisms out of the completions
  of the members of a covering family, extends to the completion; and a morphism out of a
  completion is determined by its restrictions.
* `AlgebraicGeometry.Artin.ContractionSituation.mapTriple_u` and
  `AlgebraicGeometry.Artin.ContractionSituation.mapTriple_xhat`: the second and third components
  of the pullback of a triple, by definition.  The first is
  `AlgebraicGeometry.Artin.ContractionSituation.mapTriple_Z_eq_preimage` of
  `StacksFrontier/AlgebraicGeometry/Artin/ContractionSolutionLocus.lean`.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.heq_u`,
  `AlgebraicGeometry.Artin.ContractionSituation.Triple.heq_xhat` and
  `AlgebraicGeometry.Artin.ContractionSituation.Triple.ext_of_heq`: the components of a triple
  read over an equality of triples, and the converse.
* `AlgebraicGeometry.Artin.ContractionSituation.u_restrict_eq_of_mapTriple_eq` and
  `AlgebraicGeometry.Artin.ContractionSituation.xhat_restrict_eq_of_mapTriple_eq`: from an
  equality of two pullbacks of triples, the agreement of the restricted second and third
  components as morphisms out of one and the same open subspace, resp. completion.
* `AlgebraicGeometry.Artin.ContractionSituation`'s
  `completionSubfunctorRestrict_comp_eq_of_mapTriple_eq`: the same, read through the
  sheafification.
* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_congr` and
  `AlgebraicGeometry.Artin.ContractionSituation.adic_completionSheafRestrict_congr`: the
  compatibility condition and the adicness condition transported along an equality of sets of
  points.

## What is and is not proved

Nothing is assumed; every declaration here is proved outright, and nothing carries a Stacks
attribute. These are the bookkeeping lemmas of a descent argument, not assertions of the
source.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport along an equality of sets of points -/

section Source

variable {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The restriction morphism of open subspaces, read over an equality of its source set of
points. -/
theorem heq_openSubspaceOfPointsRestrict_source (f : F' ⟶ F)
    {A A' : Set (points B S hS F')} (hA : A = A') {W : Set (points B S hS F)}
    (h : A ⊆ pointsMap B S hS F' f ⁻¹' W) (h' : A' ⊆ pointsMap B S hS F' f ⁻¹' W)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (y : (openSubspaceOfPoints B S hS F W).toFunctor ⟶ Y) :
    HEq (openSubspaceOfPointsRestrict B S hS f A W h ≫ y)
      (openSubspaceOfPointsRestrict B S hS f A' W h' ≫ y) := by
  subst hA; rfl

/-- The restriction morphism of completions, read over an equality of its source set of
points. -/
theorem heq_completionSheafRestrict_source (f : F' ⟶ F) {A A' : Set (points B S hS F')}
    (hA : A = A') {T : Set (points B S hS F)} (h : A ⊆ pointsMap B S hS F' f ⁻¹' T)
    (h' : A' ⊆ pointsMap B S hS F' f ⁻¹' T)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (y : completionSheaf B S hS F T ⟶ Y) :
    HEq (completionSheafRestrict B S hS f A T h ≫ y)
      (completionSheafRestrict B S hS f A' T h' ≫ y) := by
  subst hA; rfl

end Source

/-! ### Transport across the sheafification -/

/-- The restriction morphism of completion subfunctors, composed with the map to a sheaf
through the sheafification, is the restriction of completions composed with that map. -/
theorem completionSubfunctorRestrict_comp_toSheafify
    {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F' ⟶ F) (T' : Set (points B S hS F'))
    (T : Set (points B S hS F)) (h : T' ⊆ pointsMap B S hS F' f ⁻¹' T)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (y : completionSheaf B S hS F T ⟶ Y) :
    completionSubfunctorRestrict B S hS f T' T h ≫
        ((BigFppfOver.topology B S hS).toSheafify
          (completionSubfunctor B S hS F T).toFunctor ≫ y.hom) =
      (BigFppfOver.topology B S hS).toSheafify
          (completionSubfunctor B S hS F' T').toFunctor ≫
        (completionSheafRestrict B S hS f T' T h ≫ y).hom :=
  GrothendieckTopology.toSheafify_naturality_assoc _
    (completionSubfunctorRestrict B S hS f T' T h) y.hom

/-- **A morphism out of a completion subfunctor extends to the completion.** Given a family of
morphisms `φ i` out of the completions of the members of a family `{V_i ⟶ V}` and a morphism
`ψ₀` out of the completion subfunctor of `V` along `Z` whose restrictions agree with them
through the sheafification, there is a morphism out of the completion `V_{/Z}` itself
restricting to the `φ i`. -/
theorem exists_hom_completionSheaf {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (Z : Set (points B S hS (yoneda.obj V)))
    (Zi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hZi : ∀ i, Zi i ⊆ pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
    {Q : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (φ : ∀ i, completionSheaf B S hS (yoneda.obj (Vi i)) (Zi i) ⟶ Q)
    (ψ₀ : (completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶ Q.obj)
    (hψ₀ : ∀ i, completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i) ≫ ψ₀ =
      (BigFppfOver.topology B S hS).toSheafify
        (completionSubfunctor B S hS (yoneda.obj (Vi i)) (Zi i)).toFunctor ≫ (φ i).hom) :
    ∃ ψ : completionSheaf B S hS (yoneda.obj V) Z ⟶ Q,
      ∀ i, completionSheafRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i) ≫ ψ = φ i := by
  refine ⟨ObjectProperty.homMk
    ((BigFppfOver.topology B S hS).sheafifyLift ψ₀ Q.property), fun i => ?_⟩
  refine ObjectProperty.hom_ext _ ?_
  show (BigFppfOver.topology B S hS).sheafifyMap
      (completionSubfunctorRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i)) ≫
    (BigFppfOver.topology B S hS).sheafifyLift ψ₀ Q.property = (φ i).hom
  rw [GrothendieckTopology.sheafifyMap_sheafifyLift, hψ₀ i]
  exact ((BigFppfOver.topology B S hS).sheafifyLift_unique _ Q.property _ rfl).symm

/-- **A morphism out of a completion is determined by its restrictions.** This is
`AlgebraicGeometry.Space.hom_ext_completionSubfunctor` for the completion of Stacks 0AMC in
place of the completion subfunctor. -/
theorem hom_ext_completionSheaf {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (Z : Set (points B S hS (yoneda.obj V)))
    (Zi : ∀ i, Set (points B S hS (yoneda.obj (Vi i))))
    (hZi : ∀ i, Zi i = pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z)
    {Q : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (ψ ψ' : completionSheaf B S hS (yoneda.obj V) Z ⟶ Q)
    (hψ : ∀ i, completionSheafRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i).subset ≫ ψ =
      completionSheafRestrict B S hS (yoneda.map (f i)) (Zi i) Z (hZi i).subset ≫ ψ') :
    ψ = ψ' := by
  refine ObjectProperty.hom_ext _
    ((BigFppfOver.topology B S hS).sheafify_hom_ext _ _ Q.property ?_)
  refine hom_ext_completionSubfunctor B S hS Vi f hf Z Zi hZi Q.property _ _ fun i => ?_
  rw [completionSubfunctorRestrict_comp_toSheafify B S hS _ _ _ (hZi i).subset ψ,
    completionSubfunctorRestrict_comp_toSheafify B S hS _ _ _ (hZi i).subset ψ', hψ i]

end Space

namespace Artin

attribute [local instance] Space.pointTopology

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-! ### The components of the pullback of a triple -/

/-- The second component of the pullback of a triple, by definition. -/
theorem mapTriple_u {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁) :
    (mapTriple c φ t).u = Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z)ᶜ t.Zᶜ
        (fun _ hz => hz) ≫ t.u := rfl

/-- The third component of the pullback of a triple, by definition. -/
theorem mapTriple_xhat {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁) :
    (mapTriple c φ t).xhat = Space.completionSheafRestrict B S hS (yoneda.map φ)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' t.Z) t.Z
        (fun _ hz => hz) ≫ t.xhat := rfl

/-! ### The components of a triple read over an equality of triples -/

/-- The second component of a triple, read over an equality of triples. -/
theorem Triple.heq_u {V : BigFppfOver B S hS} {s s' : Triple c V} (h : s = s') :
    HEq s.u s'.u := by
  subst h; rfl

/-- The third component of a triple, read over an equality of triples. -/
theorem Triple.heq_xhat {V : BigFppfOver B S hS} {s s' : Triple c V} (h : s = s') :
    HEq s.xhat s'.xhat := by
  subst h; rfl

/-- Two triples are equal as soon as their first components are equal and their second and
third components agree over that equality. This is
`AlgebraicGeometry.Artin.ContractionSituation.Triple.mk_congr` for arbitrary triples rather
than for two applications of the constructor. -/
theorem Triple.ext_of_heq {V : BigFppfOver B S hS} {s s' : Triple c V} (hZ : s.Z = s'.Z)
    (hu : HEq s.u s'.u) (hx : HEq s.xhat s'.xhat) : s = s' := by
  obtain ⟨Z, hcZ, u, x, a, w⟩ := s
  obtain ⟨Z', hcZ', u', x', a', w'⟩ := s'
  exact Triple.mk_congr hZ hu hx

/-! ### The restricted components of two triples that agree -/

/-- If two pullbacks of triples agree, so do the inverse images of their first components. -/
private theorem preimage_Z_eq_of_mapTriple_eq {Y Vi Vj : BigFppfOver B S hS} (a : Y ⟶ Vi)
    (b : Y ⟶ Vj) (ti : Triple c Vi) (tj : Triple c Vj)
    (h : mapTriple c a ti = mapTriple c b tj) :
    Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Z =
      Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map b) ⁻¹' tj.Z :=
  congrArg Triple.Z h

/-- **The restricted second components of two triples that agree.** If the pullbacks of two
triples along `a : Y ⟶ V_i` and `b : Y ⟶ V_j` are equal, then their second components, each
restricted to one and the same open subspace of `Y`, agree. -/
theorem u_restrict_eq_of_mapTriple_eq {Y Vi Vj : BigFppfOver B S hS} (a : Y ⟶ Vi)
    (b : Y ⟶ Vj) (ti : Triple c Vi) (tj : Triple c Vj)
    (h : mapTriple c a ti = mapTriple c b tj)
    (A : Set (Space.points B S hS (yoneda.obj Y)))
    (hA : A = (Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Z)ᶜ)
    (h₁ : A ⊆ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Zᶜ)
    (h₂ : A ⊆ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map b) ⁻¹' tj.Zᶜ) :
    Space.openSubspaceOfPointsRestrict B S hS (yoneda.map a) A ti.Zᶜ h₁ ≫ ti.u =
      Space.openSubspaceOfPointsRestrict B S hS (yoneda.map b) A tj.Zᶜ h₂ ≫ tj.u := by
  have hZ := preimage_Z_eq_of_mapTriple_eq c a b ti tj h
  refine eq_of_heq (HEq.trans ?_ (HEq.trans (Triple.heq_u c h) ?_))
  · exact Space.heq_openSubspaceOfPointsRestrict_source B S hS (yoneda.map a) hA h₁ _ ti.u
  · exact (Space.heq_openSubspaceOfPointsRestrict_source B S hS (yoneda.map b)
      (hA.trans (congrArg compl hZ)) h₂ _ tj.u).symm

/-- **The restricted third components of two triples that agree.** If the pullbacks of two
triples along `a : Y ⟶ V_i` and `b : Y ⟶ V_j` are equal, then their third components, each
restricted to one and the same completion of `Y`, agree. -/
theorem xhat_restrict_eq_of_mapTriple_eq {Y Vi Vj : BigFppfOver B S hS} (a : Y ⟶ Vi)
    (b : Y ⟶ Vj) (ti : Triple c Vi) (tj : Triple c Vj)
    (h : mapTriple c a ti = mapTriple c b tj)
    (A : Set (Space.points B S hS (yoneda.obj Y)))
    (hA : A = Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Z)
    (h₁ : A ⊆ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Z)
    (h₂ : A ⊆ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map b) ⁻¹' tj.Z) :
    Space.completionSheafRestrict B S hS (yoneda.map a) A ti.Z h₁ ≫ ti.xhat =
      Space.completionSheafRestrict B S hS (yoneda.map b) A tj.Z h₂ ≫ tj.xhat := by
  have hZ := preimage_Z_eq_of_mapTriple_eq c a b ti tj h
  refine eq_of_heq (HEq.trans ?_ (HEq.trans (Triple.heq_xhat c h) ?_))
  · exact Space.heq_completionSheafRestrict_source B S hS (yoneda.map a) hA h₁ _ ti.xhat
  · exact (Space.heq_completionSheafRestrict_source B S hS (yoneda.map b) (hA.trans hZ) h₂ _
      tj.xhat).symm

/-- **The restricted third components of two triples that agree, at the subfunctor level.**
The same statement as
`AlgebraicGeometry.Artin.ContractionSituation.xhat_restrict_eq_of_mapTriple_eq`, read through
the sheafification: this is the form the glueing lemma for completion subfunctors asks for. -/
theorem completionSubfunctorRestrict_comp_eq_of_mapTriple_eq {Y Vi Vj : BigFppfOver B S hS}
    (a : Y ⟶ Vi) (b : Y ⟶ Vj) (ti : Triple c Vi) (tj : Triple c Vj)
    (h : mapTriple c a ti = mapTriple c b tj)
    (A : Set (Space.points B S hS (yoneda.obj Y)))
    (hA : A = Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Z)
    (h₁ : A ⊆ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map a) ⁻¹' ti.Z)
    (h₂ : A ⊆ Space.pointsMap B S hS (yoneda.obj Y) (yoneda.map b) ⁻¹' tj.Z) :
    Space.completionSubfunctorRestrict B S hS (yoneda.map a) A ti.Z h₁ ≫
        ((BigFppfOver.topology B S hS).toSheafify
          (Space.completionSubfunctor B S hS (yoneda.obj Vi) ti.Z).toFunctor ≫ ti.xhat.hom) =
      Space.completionSubfunctorRestrict B S hS (yoneda.map b) A tj.Z h₂ ≫
        ((BigFppfOver.topology B S hS).toSheafify
          (Space.completionSubfunctor B S hS (yoneda.obj Vj) tj.Z).toFunctor ≫ tj.xhat.hom) := by
  rw [Space.completionSubfunctorRestrict_comp_toSheafify B S hS (yoneda.map a) A ti.Z h₁ ti.xhat,
    Space.completionSubfunctorRestrict_comp_toSheafify B S hS (yoneda.map b) A tj.Z h₂ tj.xhat,
    xhat_restrict_eq_of_mapTriple_eq c a b ti tj h A hA h₁ h₂]

/-! ### The two conditions on a triple, transported -/

/-- The compatibility condition transported along an equality of sets of points. -/
theorem nonempty_compatibilityWitness_congr {V : BigFppfOver B S hS}
    {Z Z' : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = Z')
    {u : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {u' : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Z'ᶜ).toFunctor ⟶ c.U'.toFunctor}
    {x : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W}
    {x' : Space.completionSheaf B S hS (yoneda.obj V) Z' ⟶ c.W}
    (hu : HEq u u') (hx : HEq x x') (h : Nonempty (CompatibilityWitness c V Z u x)) :
    Nonempty (CompatibilityWitness c V Z' u' x') := by
  subst hZ
  cases hu
  cases hx
  exact h

/-- The adicness condition of Stacks 0AQ3 on a restricted morphism, transported along an
equality of sets of points. -/
theorem adic_completionSheafRestrict_congr {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F' ⟶ F) {A A' : Set (Space.points B S hS F')} (hA : A = A')
    {T : Set (Space.points B S hS F)} (h : A ⊆ Space.pointsMap B S hS F' f ⁻¹' T)
    (h' : A' ⊆ Space.pointsMap B S hS F' f ⁻¹' T)
    {Y : FormalSpace.FppfSheaf B S hS} (y : Space.completionSheaf B S hS F T ⟶ Y) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafRestrict B S hS f A T h ≫ y).hom ↔
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafRestrict B S hS f A' T h' ≫ y).hom := by
  subst hA; exact Iff.rfl

end ContractionSituation

end Artin

end AlgebraicGeometry

end
