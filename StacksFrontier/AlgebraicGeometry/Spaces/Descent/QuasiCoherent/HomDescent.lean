module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.CanonicalFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# Descent of morphisms of modules along an étale covering of algebraic spaces

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be an étale covering
of `X`, for instance a Zariski covering.  A morphism of `𝒪_X`-modules is determined by its
inverse images along the members of the covering: along an étale morphism the inverse image of
modules of Stacks 03LU is restriction of sections by Stacks 03LW, the charts of the members
cover every chart of `X`, and a section of a sheaf is determined by its restrictions to a
covering.  Consequently the canonical descent functor of Stacks 04W5, from the quasi-coherent
`𝒪_X`-modules to the descent data relative to the covering, is faithful.

Quasi-coherence is not used: descent of morphisms along an étale covering is the sheaf
condition on the small étale site of `X`, and the statement below holds for arbitrary sheaves
of modules.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleModulePullback_map_eq_of_modulePullback`:
  two morphisms of modules with equal inverse images along an étale morphism have equal étale
  restrictions, the two descriptions of the inverse image being naturally isomorphic.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`:
  a morphism of `𝒪_X`-modules is determined by its inverse images along an étale covering.
* `faithful_canonicalDescentFunctor_of_isEtaleCovering` and its Zariski form, in the namespace
  `AlgebraicGeometry.Space.QuasiCoherentDescent`: the canonical descent functor of such a covering
  is faithful.

## Implementation notes

The reduction to the small étale site of `X` is in two steps.  Equality of the inverse images
of two morphisms is transported to equality of their étale restrictions through the natural
isomorphism `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback` of Stacks 03LW, by
cancelling an isomorphism; the étale restriction of a morphism is, on sections over a chart `V`
of `Y i`, the morphism itself on sections over the chart `V` of `X` obtained by postcomposition,
by definition of `AlgebraicGeometry.Space.etaleModulePullback`.  The charts of the members
covering a given chart of `X` are
`AlgebraicGeometry.Space.exists_refinement_of_isEtaleCovering`.

Faithfulness of the canonical descent functor is unconditional, as the functor itself is.  The
associativity coherence of the comparison of inverse images of Stacks 03LU and the
quasi-coherence of the inverse images (Stacks 03GA) are both needed to form the functor, and
neither enters this proof.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 041G](https://stacks.math.columbia.edu/tag/041G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two morphisms of modules whose inverse images along an étale morphism agree have equal
étale restrictions: the two descriptions of the inverse image are naturally isomorphic by
Stacks 03LW. -/
theorem etaleModulePullback_map_eq_of_modulePullback {A C : AlgebraicSpaces B S hS} (g : A ⟶ C)
    (hg : IsEtale B S hS g.hom) {M N : Modules.{u, u} B S hS C.1 C.2} (φ ψ : M ⟶ N)
    (h : (modulePullback B S hS g).map φ = (modulePullback B S hS g).map ψ) :
    (etaleModulePullback.{u, u} B S hS g hg).map φ =
      (etaleModulePullback.{u, u} B S hS g hg).map ψ := by
  have heq : (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M ≫
        (etaleModulePullback.{u, u} B S hS g hg).map φ =
      (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.app M ≫
        (etaleModulePullback.{u, u} B S hS g hg).map ψ := by
    rw [← (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.naturality φ,
      ← (modulePullbackIsoEtaleModulePullback B S hS g hg).hom.naturality ψ, h]
  exact
    (((modulePullbackIsoEtaleModulePullback B S hS g hg).app M).cancel_iso_hom_left _ _).1 heq

/-- On sections over a chart of the source, the étale restriction of a morphism of modules is
that morphism on sections over the chart of the target obtained by postcomposition. -/
theorem etaleModulePullback_map_val_app {A C : AlgebraicSpaces B S hS} (g : A ⟶ C)
    (hg : IsEtale B S hS g.hom) {M N : Modules.{u, u} B S hS C.1 C.2} (φ : M ⟶ N)
    (V : SmallEtale B S hS A.1) :
    ((etaleModulePullback.{u, u} B S hS g hg).map φ).val.app (.op V) =
      φ.val.app (.op ((smallEtalePostcomp B S hS g hg).obj V)) :=
  rfl

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- Along an étale covering, two morphisms of `𝒪_X`-modules with equal inverse images agree on
sections over every chart of the small étale site of `X`: the charts of the members cover that
chart, and the target is a sheaf. -/
theorem val_app_eq_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ ψ : M ⟶ N)
    (h : ∀ i, (modulePullback B S hS (f i)).map φ = (modulePullback B S hS (f i)).map ψ)
    (W : SmallEtale B S hS X.1) :
    φ.val.app (.op W) = ψ.val.app (.op W) := by
  have hsec : ∀ (i : I) (V : SmallEtale B S hS (Yi i).1),
      φ.val.app (.op ((smallEtalePostcomp B S hS (f i) (hcov.etale i)).obj V)) =
        ψ.val.app (.op ((smallEtalePostcomp B S hS (f i) (hcov.etale i)).obj V)) := by
    intro i V
    exact congrArg (fun a => a.val.app (.op V))
      (etaleModulePullback_map_eq_of_modulePullback B S hS (f i) (hcov.etale i) φ ψ (h i))
  have hN : Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf _ _ _ N.isSheaf)
  obtain ⟨V, q, hcover⟩ := exists_refinement_of_isEtaleCovering B S hS Yi f hcov W
  ext s
  have hloc : ∀ i, N.val.map (q i).op (φ.val.app (.op W) s) =
      N.val.map (q i).op (ψ.val.app (.op W) s) := fun i =>
    (PresheafOfModules.naturality_apply φ.val (q i).op s).symm.trans
      ((CategoryTheory.congr_fun (hsec i (V i)) (M.val.map (q i).op s)).trans
        (PresheafOfModules.naturality_apply ψ.val (q i).op s))
  apply (hN.isSeparated _ hcover).ext
  rintro Z r ⟨_, b, _, ⟨i⟩, rfl⟩
  exact (N.val.map_comp_apply (q i).op b.op (φ.val.app (.op W) s)).trans
    ((congrArg (fun x => N.val.map b.op x) (hloc i)).trans
      (N.val.map_comp_apply (q i).op b.op (ψ.val.app (.op W) s)).symm)

/-- **A morphism of `𝒪_X`-modules is determined by its inverse images along an étale covering**,
with the covering family taken after the equations rather than before.  No quasi-coherence is
assumed: this is the sheaf condition on the small étale site of `X`, read through the
identification of the inverse image along an étale morphism with restriction of sections. -/
theorem modulePullback_map_injective_of_isEtaleCovering'
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ ψ : M ⟶ N)
    {Vi : I → AlgebraicSpaces B S hS} {fi : ∀ i, Vi i ⟶ X}
    (h : ∀ i, (modulePullback B S hS (fi i)).map φ = (modulePullback B S hS (fi i)).map ψ)
    (hcov : IsEtaleCovering B S hS (fun i => (Vi i).1) (fun i => (fi i).hom)) :
    φ = ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    val_app_eq_of_isEtaleCovering B S hS Vi fi hcov φ ψ h U.unop)

/-- **A morphism of `𝒪_X`-modules is determined by its inverse images along an étale
covering.**  No quasi-coherence is assumed: this is the sheaf condition on the small étale site
of `X`, read through the identification of the inverse image along an étale morphism with
restriction of sections. -/
theorem modulePullback_map_injective_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ ψ : M ⟶ N)
    (h : ∀ i, (modulePullback B S hS (f i)).map φ = (modulePullback B S hS (f i)).map ψ) :
    φ = ψ :=
  modulePullback_map_injective_of_isEtaleCovering' B S hS φ ψ h hcov

/-- **The canonical descent functor of an étale covering is faithful.**  This is half of the
full faithfulness asserted by Stacks 04W6 for a Zariski covering and by Stacks 04W8 in
general. -/
theorem faithful_canonicalDescentFunctor_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (canonicalDescentFunctor B S hS Yi f).Faithful where
  map_injective {M N} φ ψ h := by
    refine ObjectProperty.hom_ext _ (modulePullback_map_injective_of_isEtaleCovering B S hS Yi f
      hcov φ.hom ψ.hom fun i => ?_)
    have hi := congrArg
      (fun a : (canonicalDescentFunctor B S hS Yi f).obj M ⟶
        (canonicalDescentFunctor B S hS Yi f).obj N => a.app i) h
    rw [canonicalDescentFunctor_map_app, canonicalDescentFunctor_map_app] at hi
    exact hi

/-- **The canonical descent functor of a Zariski covering is faithful**, a Zariski covering
being an étale covering by Stacks 0DF1. -/
theorem faithful_canonicalDescentFunctor_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom)) :
    (canonicalDescentFunctor B S hS Yi f).Faithful :=
  faithful_canonicalDescentFunctor_of_isEtaleCovering B S hS Yi f
    (isEtaleCovering_of_isZariskiCovering B S hS X.2 (fun i => (Yi i).2) hcov)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
