module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DominatingCompactification

/-!
# Independence of the compactification for `RΓ_c(X_k̄, -)` (Remark 03UI (2))

Let `k` be a field, `X` a separated scheme of finite type over `k`, `k̄` an extension field of
`k` and `Λ` a ring.  Remark 03UI (2) of the Trace Formula chapter defines

`RΓ_c(X_k̄, K) := RΓ(X̄_k̄, j_! K)`

for an open immersion `j : X ⟶ X̄` with `X̄` projective over `k` of dimension at most one, and
says that this does not depend on the choice of `X̄`.  This file proves it, for compactifications
`X̄` proper over `k` of dimension at most one (a projective `k`-scheme being proper):

* two such compactifications `X̄₁`, `X̄₂` are dominated by the closure `P` of `X` in
  `X̄₁ ×_k X̄₂`, and the projections `q_i : P ⟶ X̄_i` are finite with `X = q_i⁻¹(X)`
  (`AlgebraicGeometry.CompactificationOf.isFinite_dominatingFstMap`,
  `AlgebraicGeometry.CompactificationOf.isPullback_dominatingFstMap`);
* after base change to `k̄` they remain integral and cartesian, so the derived lower shriek
  functors `Rf_!` of `X_k̄` formed through `P_k̄`, `X̄₁_k̄`, `X̄₂_k̄` are isomorphic
  (`Stacks.EtaleCohomology.derivedLowerShriekIsoOfIntegral`), and so are the complexes
  `RΓ_c(X_k̄, -)` and the modules `H^i_c(X_k̄, -)`, naturally in the coefficient complex.

The comparison is canonical: it is built from the canonical dominating compactification, with no
choice, and the comparison of a compactification with itself is the identity
(`Stacks.EtaleCohomology.geometricCompactSupportCanonicalComparison_self`).  No proper base change
is used: the projections `q_i` are finite, and finite direct images are exact and commute with
extension by zero.

## Main definitions

* `Stacks.EtaleCohomology.compactificationFieldBaseChangeMap` — the base change to `k̄` of a
  morphism of compactifications.
* `Stacks.EtaleCohomology.geometricLowerShriekIsoOfIntegral` — the comparison of the derived
  lower shriek functors along an integral cartesian morphism of compactifications.
* `Stacks.EtaleCohomology.geometricLowerShriekCanonicalIso` — `Rf_!` of `X_k̄` is independent of
  the compactification of `X` of dimension at most one.
* `Stacks.EtaleCohomology.geometricCompactSupportCanonicalComparison` and
  `Stacks.EtaleCohomology.geometricCompactSupportGroupCanonicalComparison` — **Remark 03UI (2)**:
  `RΓ_c(X_k̄, -)` and `H^i_c(X_k̄, -)` are independent of the compactification.

## Implementation notes

The coefficient ring `Λ` lives in `Type`, the universe in which integral base change for sheaves
of modules is available
(`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isIntegralHom_of_ring`); it is otherwise
an arbitrary ring, not assumed commutative or finite.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (c c' : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (g : c.space ⟶ c'.space) (hbase : g ≫ c'.toBase = c.toBase)

/-- **The base change to `k̄` of a morphism `g : X̄ ⟶ X̄'` of compactifications**, as a morphism
`X̄_k̄ ⟶ X̄'_k̄` over `Spec k̄`. -/
def compactificationFieldBaseChangeMap :
    pullback c.toBase (Stacks.Frobenius.specAlgebraMap k kbar) ⟶
      pullback c'.toBase (Stacks.Frobenius.specAlgebraMap k kbar) :=
  pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp [hbase]) (by simp)

/-- The base change of `g` composed with the first projection `X̄'_k̄ ⟶ X̄'` is the first
projection `X̄_k̄ ⟶ X̄` followed by `g`. -/
@[reassoc (attr := simp)]
lemma compactificationFieldBaseChangeMap_fst :
    compactificationFieldBaseChangeMap c c' kbar g hbase ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ g :=
  pullback.lift_fst _ _ _

/-- The base change of `g` commutes with the second projections to `Spec k̄`. -/
@[reassoc (attr := simp)]
lemma compactificationFieldBaseChangeMap_snd :
    compactificationFieldBaseChangeMap c c' kbar g hbase ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  simp [compactificationFieldBaseChangeMap]

/-- The base change of `g` is a base change of `g`: the square formed with the two first
projections is cartesian. -/
theorem isPullback_compactificationFieldBaseChangeMap :
    IsPullback (compactificationFieldBaseChangeMap c c' kbar g hbase) (pullback.fst _ _)
      (pullback.fst _ _) g := by
  refine IsPullback.of_right ?_ (compactificationFieldBaseChangeMap_fst c c' kbar g hbase)
    (IsPullback.of_hasPullback c'.toBase (Stacks.Frobenius.specAlgebraMap k kbar)).flip
  rw [compactificationFieldBaseChangeMap_snd, hbase]
  exact (IsPullback.of_hasPullback c.toBase (Stacks.Frobenius.specAlgebraMap k kbar)).flip

/-- The base change to `k̄` of an integral morphism of compactifications is integral. -/
instance isIntegralHom_compactificationFieldBaseChangeMap [IsIntegralHom g] :
    IsIntegralHom (compactificationFieldBaseChangeMap c c' kbar g hbase) :=
  MorphismProperty.of_isPullback
    (isPullback_compactificationFieldBaseChangeMap c c' kbar g hbase).flip inferInstance

/-- The base change of `g` extends the identity of `X_k̄`. -/
@[reassoc (attr := simp)]
lemma compactificationFieldBaseChangeImmersion_comp_map (hcomp : c.immersion ≫ g = c'.immersion) :
    compactificationFieldBaseChangeImmersion f c kbar ≫
        compactificationFieldBaseChangeMap c c' kbar g hbase =
      compactificationFieldBaseChangeImmersion f c' kbar := by
  apply pullback.hom_ext
  · simp [hcomp]
  · simp

/-- **The base change of a cartesian morphism of compactifications is cartesian**: if
`X = g⁻¹(X)` then `X_k̄ = g_k̄⁻¹(X_k̄)`. -/
theorem isPullback_compactificationFieldBaseChangeMap_immersion
    (hcomp : c.immersion ≫ g = c'.immersion) (sq : IsPullback (𝟙 X) c.immersion c'.immersion g) :
    IsPullback (𝟙 _) (compactificationFieldBaseChangeImmersion f c kbar)
      (compactificationFieldBaseChangeImmersion f c' kbar)
      (compactificationFieldBaseChangeMap c c' kbar g hbase) := by
  refine IsPullback.of_bot ?_ (by simp [compactificationFieldBaseChangeImmersion_comp_map,
      hcomp]) (isPullback_compactificationFieldBaseChangeMap c c' kbar g hbase)
  rw [compactificationFieldBaseChange_immersion_comp_fst,
    compactificationFieldBaseChange_immersion_comp_fst]
  exact (IsPullback.id_horiz _).paste_vert sq

end BaseChange

section Comparison

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (Λ : Type) [Ring Λ]

/-- **The derived lower shriek functors of `X_k̄` through the base changes of two compactifications
related by an integral cartesian morphism are isomorphic.** -/
def geometricLowerShriekIsoOfIntegral (c c' : CompactificationOf (Over.mk f))
    (g : c.space ⟶ c'.space) [IsIntegralHom g] (hbase : g ≫ c'.toBase = c.toBase)
    (hcomp : c.immersion ≫ g = c'.immersion) (sq : IsPullback (𝟙 X) c.immersion c'.immersion g) :
    geometricLowerShriek.{u, 0} f c kbar Λ ≅ geometricLowerShriek.{u, 0} f c' kbar Λ :=
  have : IsIntegralHom (X := (compactificationFieldBaseChange f c kbar).space)
      (Y := (compactificationFieldBaseChange f c' kbar).space)
      (compactificationFieldBaseChangeMap c c' kbar g hbase) :=
    isIntegralHom_compactificationFieldBaseChangeMap c c' kbar g hbase
  derivedLowerShriekIsoOfIntegral Λ (compactificationFieldBaseChange f c kbar)
    (compactificationFieldBaseChange f c' kbar)
    (compactificationFieldBaseChangeMap c c' kbar g hbase)
    (compactificationFieldBaseChangeMap_snd c c' kbar g hbase)
    (isPullback_compactificationFieldBaseChangeMap_immersion c c' kbar g hbase hcomp sq)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The comparison along `g` depends only on `g`. -/
theorem geometricLowerShriekIsoOfIntegral_congr (c c' : CompactificationOf (Over.mk f))
    (g g' : c.space ⟶ c'.space) [IsIntegralHom g] [IsIntegralHom g'] (h : g = g')
    (hbase : g ≫ c'.toBase = c.toBase) (hcomp : c.immersion ≫ g = c'.immersion)
    (sq : IsPullback (𝟙 X) c.immersion c'.immersion g)
    (hbase' : g' ≫ c'.toBase = c.toBase) (hcomp' : c.immersion ≫ g' = c'.immersion)
    (sq' : IsPullback (𝟙 X) c.immersion c'.immersion g') :
    geometricLowerShriekIsoOfIntegral f kbar Λ c c' g hbase hcomp sq =
      geometricLowerShriekIsoOfIntegral f kbar Λ c c' g' hbase' hcomp' sq' := by
  subst h
  rfl

variable (c₁ c₂ : CompactificationOf (Over.mk f)) (h₁ : topologicalKrullDim c₁.space ≤ 1)
  (h₂ : topologicalKrullDim c₂.space ≤ 1)

/-- The comparison of `Rf_!` through the dominating compactification with `Rf_!` through `c₁`. -/
def geometricLowerShriekDominatingFstIso :
    geometricLowerShriek.{u, 0} f (c₁.dominating c₂) kbar Λ ≅
      geometricLowerShriek.{u, 0} f c₁ kbar Λ :=
  haveI := c₁.isFinite_dominatingFstMap c₂ h₁ h₂
  geometricLowerShriekIsoOfIntegral f kbar Λ _ c₁ (CompactificationOf.Hom.map (c₁.dominatingFst c₂))
    (c₁.dominatingFstMap_toBase c₂) (c₁.immersion_dominatingFstMap c₂)
    (c₁.isPullback_dominatingFst c₂).flip

/-- The comparison of `Rf_!` through the dominating compactification with `Rf_!` through `c₂`. -/
def geometricLowerShriekDominatingSndIso :
    geometricLowerShriek.{u, 0} f (c₁.dominating c₂) kbar Λ ≅
      geometricLowerShriek.{u, 0} f c₂ kbar Λ :=
  haveI := c₁.isFinite_dominatingSndMap c₂ h₁ h₂
  geometricLowerShriekIsoOfIntegral f kbar Λ _ c₂ (CompactificationOf.Hom.map (c₁.dominatingSnd c₂))
    (c₁.dominatingSndMap_toBase c₂) (c₁.immersion_dominatingSndMap c₂)
    (c₁.isPullback_dominatingSnd c₂).flip

/-- **`Rf_!` of `X_k̄` is independent of the compactification** of `X` over `k` of dimension at
most one: the canonical isomorphism through the dominating compactification. -/
def geometricLowerShriekCanonicalIso :
    geometricLowerShriek.{u, 0} f c₁ kbar Λ ≅ geometricLowerShriek.{u, 0} f c₂ kbar Λ :=
  (geometricLowerShriekDominatingFstIso f kbar Λ c₁ c₂ h₁ h₂).symm ≪≫
    geometricLowerShriekDominatingSndIso f kbar Λ c₁ c₂ h₁ h₂

/-- **Remark 03UI (2): `RΓ_c(X_k̄, -)` is independent of the compactification.**  Let `k` be a
field, `X` a separated scheme of finite type over `k`, `k̄` an extension field of `k` and `Λ` a
ring.  For any two compactifications `X ⟶ X̄₁` and `X ⟶ X̄₂` of `X` over `k` (open immersions
into proper `k`-schemes, which projective ones are) of dimension at most one, the complexes
`RΓ(X̄₁_k̄, j₁! K)` and `RΓ(X̄₂_k̄, j₂! K)` are canonically isomorphic, naturally in the bounded
below complex `K` of sheaves of `Λ`-modules on `X_k̄`.  The isomorphism is induced by the
canonical isomorphism `geometricLowerShriekCanonicalIso` of the derived lower shriek functors,
through the closure of `X` in `X̄₁ ×_k X̄₂`.

The coefficient ring is taken in `Type` (universe `0`), as in the companion results of
Tags 03VK and 03VL: integral base change for sheaves of modules, through which the finite
projections of the dominating compactification are handled, is available at that universe. A
finite ring, the coefficient ring of the source, is isomorphic to one in `Type`. -/
@[stacks 03UI "(2): independence of the compactification -- RΓ_c(X_k̄, -) = RΓ(X̄_k̄, j_! -) does \
not depend on the compactification X̄ of X over k of dimension at most one (proper, which a \
projective X̄ is): canonical isomorphism through the closure of X in X̄₁ ×_k X̄₂"]
def geometricCompactSupportCanonicalComparison :
    geometricCompactSupportCohomology.{u, 0} f c₁ kbar Λ ≅
      geometricCompactSupportCohomology.{u, 0} f c₂ kbar Λ :=
  geometricCompactSupportComparison.{u, 0} f c₁ c₂ kbar Λ
    (geometricLowerShriekCanonicalIso f kbar Λ c₁ c₂ h₁ h₂)

/-- **Remark 03UI (2): `H^i_c(X_k̄, -)` is independent of the compactification**, in every degree,
naturally in the coefficient complex: the isomorphism induced on cohomology by
`geometricCompactSupportCanonicalComparison`.  The coefficient ring is taken in `Type`, as in
`geometricCompactSupportCanonicalComparison`. -/
@[stacks 03UI "(2): independence of the compactification -- H^i_c(X_k̄, -) does not depend on \
the compactification X̄ of X over k of dimension at most one, in every degree"]
def geometricCompactSupportGroupCanonicalComparison (i : ℤ) :
    geometricCompactSupportCohomologyGroup.{u, 0} f c₁ kbar Λ i ≅
      geometricCompactSupportCohomologyGroup.{u, 0} f c₂ kbar Λ i :=
  geometricCompactSupportGroupComparison.{u, 0} f c₁ c₂ kbar Λ
    (geometricLowerShriekCanonicalIso f kbar Λ c₁ c₂ h₁ h₂) i

omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- The two projections of the dominating compactification of a compactification with itself
coincide: they agree on the scheme-theoretically dense image of `X`, and `X̄` is separated. -/
theorem dominatingFstMap_self_eq_dominatingSndMap :
    CompactificationOf.Hom.map (c₁.dominatingFst c₁) =
      CompactificationOf.Hom.map (c₁.dominatingSnd c₁) := by
  let P := c₁.dominating c₁
  let m := P.immersion
  have : IsSeparated (Over.mk c₁.toBase).hom := (c₁.property.2).toIsSeparated
  have hU : Scheme.Opens.IsSchemeTheoreticallyDense m.opensRange :=
    isSchemeTheoreticallyDense_toImage (c₁.dominatingLift c₁) (Or.inl inferInstance)
  exact congrArg (·.left) <| eq_of_isSchemeTheoreticallyDense (S := Spec (.of k))
    (X := Over.mk P.toBase) (Y := Over.mk c₁.toBase)
    (Over.homMk (CompactificationOf.Hom.map (c₁.dominatingFst c₁)) (c₁.dominatingFstMap_toBase c₁))
    (Over.homMk (CompactificationOf.Hom.map (c₁.dominatingSnd c₁)) (c₁.dominatingSndMap_toBase c₁))
    m.opensRange hU (by
      show m.opensRange.ι ≫ CompactificationOf.Hom.map (c₁.dominatingFst c₁) =
        m.opensRange.ι ≫ CompactificationOf.Hom.map (c₁.dominatingSnd c₁)
      rw [← cancel_epi m.isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
        m.isoOpensRange_hom_ι]
      exact (c₁.immersion_dominatingFstMap c₁).trans (c₁.immersion_dominatingSndMap c₁).symm)

omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- **The canonical comparison of a compactification with itself is the identity.** -/
theorem geometricLowerShriekCanonicalIso_self :
    geometricLowerShriekCanonicalIso f kbar Λ c₁ c₁ h₁ h₁ = Iso.refl _ := by
  have : geometricLowerShriekDominatingSndIso f kbar Λ c₁ c₁ h₁ h₁ =
      geometricLowerShriekDominatingFstIso f kbar Λ c₁ c₁ h₁ h₁ := by
    have := c₁.isFinite_dominatingFstMap c₁ h₁ h₁
    have := c₁.isFinite_dominatingSndMap c₁ h₁ h₁
    exact geometricLowerShriekIsoOfIntegral_congr f kbar Λ _ c₁ _ _
      (dominatingFstMap_self_eq_dominatingSndMap f c₁).symm _ _ _ _ _ _
  rw [geometricLowerShriekCanonicalIso, this, Iso.symm_self_id]

omit [LocallyOfFiniteType f] [IsSeparated f] in
/-- **The canonical comparison of `RΓ_c(X_k̄, -)` for a compactification with itself is the
identity.** -/
theorem geometricCompactSupportCanonicalComparison_self :
    geometricCompactSupportCanonicalComparison f kbar Λ c₁ c₁ h₁ h₁ = Iso.refl _ := by
  rw [geometricCompactSupportCanonicalComparison, geometricLowerShriekCanonicalIso_self,
    geometricCompactSupportComparison_refl]

end Comparison

end Stacks.EtaleCohomology

end
