module

public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.ModuleSheafSpectralSequence
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Basic
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Cohomology collapses when the base cohomology of the higher direct images vanishes

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F` be a sheaf of `𝒪_X`-modules. If
`H^p(Y, R^q f_* F) = 0` for every `p > 0` and every `q`, then the canonical map
```
H^q(X, F) ⟶ Γ(Y, R^q f_* F) = H^0(Y, R^q f_* F)
```
is an isomorphism for every `q`. This is part (2) of [Stacks, Tag 01F4], whose tag this file
carries; part (1) — the collapse `H^p(X, F) ≅ H^p(Y, f_* F)` when the higher direct images
themselves vanish — is `Stacks.LeraySections.cohomologyIsoOfVanishingHigherDirectImages`.

The route uses no spectral sequence. Write `Γ_X = Γ(X, -)` and `Γ_Y = Γ(Y, -)` for the
abelian-group-valued sections functors; then `Γ_X = f_* ⋙ Γ_Y` on the nose. Let `I` be an
injective resolution of `F` and let `K = f_*(I^•)`, so that `H^q(K) = R^q f_* F` and
`H^q(Γ_Y(K)) = H^q(X, F)`. Every term of `K` is `Γ_Y`-acyclic — this is [Stacks, Tag 01EX]
part (2) — and the hypothesis says that every cohomology object of `K` is `Γ_Y`-acyclic as
well. Under exactly those two hypotheses the comparison `H^q(Γ_Y(K)) ⟶ Γ_Y(H^q(K))` is an
isomorphism, which is
`Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic`; transporting its
two ends along the chosen injective resolution turns it into the statement that
`H^q(X, F) ⟶ Γ_Y(R^q f_* F) = H^0(Y, R^q f_* F)` is an isomorphism.

## Main definitions

* `Stacks.Cohomology.LerayModules.cohomologyToSectionsHigherDirectImage`: the canonical map
  `H^q(X, F) ⟶ Γ(Y, R^q f_* F)`, defined with no hypothesis on `F`.

## Main results

* `Stacks.Cohomology.LerayModules.isIso_cohomologyToSectionsHigherDirectImage_of_vanishing`:
  **part (2) of [Stacks, Tag 01F4]** stated above.
* `Stacks.Cohomology.LerayModules.nonempty_cohomology_iso_higherDirectImage_of_vanishing`: the
  same conclusion as a bare `Nonempty (· ≅ ·)`, which is the shape its consumers take.

## Implementation notes

The conclusion names *which* map is inverted. The source asserts an equality of cohomology
groups, and the map realizing it is the edge morphism of the Leray spectral sequence; asserting
only that some isomorphism exists would forget that, so
`cohomologyToSectionsHigherDirectImage` is defined unconditionally and the theorem says it is
invertible. The `Nonempty`-valued corollary is kept only because the consumers in
`StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing` are stated against it.

The canonical map is *not* `Stacks.Cohomology.RightDerivedCoEdge.secondEdge`, the co-edge
morphism of a composite of right derived functors, even though that is the same mathematics:
`secondEdge` asks the first functor to preserve injective objects, and the module pushforward
does not. The transport along the chosen injective resolution is written out here instead.

`Stacks.BoundedBelowEdge.isIso_homologyComparison_of_isStrictlyGE` is the same mathematics for
`ℤ`-indexed cochain complexes, but it asks for a complex of *injective* objects, which
`f_*(I^•)` is not, for the same reason. What is available instead, and all that the induction
behind `isIso_homologyToMapHomology_of_acyclic` needs, is right acyclicity of the terms.

Right acyclicity is read in Mathlib's `ℕ`-indexed derived functors through
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`, the hypothesis of the source being
stated with `CategoryTheory.Functor.rightDerived`.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe v v' u u'

namespace Stacks.Cohomology.LerayModules

attribute [local instance] HasDerivedCategory.standard

-- As in `StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso`: instance
-- search for `HasRightDerivedFunctor`, which `Functor.rightAcyclic` mentions, would otherwise
-- try to prove termwise injectivity of an unknown complex, so the cheap instance coming from
-- `EnoughInjectives` is given precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Reading the vanishing hypothesis as acyclicity -/

section Acyclic

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{max u v} C] [HasDerivedCategory.{max u' v'} D] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

/-- Right acyclicity, read in Mathlib's `ℕ`-indexed right derived functors: part (2) of
[Stacks, Tag 015C] followed by the comparison of the two indexings. -/
private lemma rightAcyclic_iff_isZero_rightDerived (A : C) :
    G.rightAcyclic A ↔ ∀ n : ℕ, 0 < n → IsZero ((G.rightDerived n).obj A) := by
  rw [Stacks.AcyclicQuasiIso.rightAcyclic_iff_isZero G A]
  refine ⟨fun h n hn => (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff G n A).2
    (h n (by exact_mod_cast hn)), fun h i hi => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff G n A).1 (h n (by exact_mod_cast hi))

end Acyclic

/-! ### The collapse -/

section Collapse

attribute [local instance] Stacks.Cohomology.PushforwardAcyclic.sheafOfModules_abelian
  RingedSpaceModuleAdjunction.enoughInjectives_sheafOfModules
variable {X Y : RingedSpace.{u, u}}

/-- The complex `K = f_*(I^•)` for `I` the chosen injective resolution of `F`: its `q`-th
cohomology is `R^q f_* F` and the `q`-th homology of `Γ(Y, -)` applied to it is `H^q(X, F)`,
because `Γ(X, -)` *is* `f_*` followed by `Γ(Y, -)`. -/
noncomputable abbrev pushforwardInjectiveResolution (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℕ :=
  ((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- **The canonical map `H^q(X, F) ⟶ Γ(Y, R^q f_* F)`**, which sends a cohomology class on `X`
to the global section of the `q`-th higher direct image that it induces.

Global sections on `X` *are* the direct image followed by global sections on `Y`, so for an
injective resolution `I` of `F` and `K = f_*(I^•)` the group `H^q(X, F)` is the `q`-th homology
of `Γ(Y, -)` applied to `K` and `R^q f_* F` is the `q`-th cohomology of `K`; the map is then the
comparison `H^q(Γ(Y, K)) ⟶ Γ(Y, H^q(K))` of
`Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`, read through
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` on both ends. It is the edge morphism
`H^q ⟶ E_2^{0,q}` of the Leray spectral sequence of `(f_*, Γ(Y, -))`, defined with no
hypothesis on `F`. -/
noncomputable def cohomologyToSectionsHigherDirectImage (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X)) (q : ℕ) :
    Hgroup (structureSheafRing X) ⊤ q F ⟶
      (secF (structureSheafRing Y) (⊤ : Opens Y.carrier)).obj
        (((modulePushforward f).rightDerived q).obj F) :=
  ((injectiveResolution F).isoRightDerivedObj
        (secF (structureSheafRing X) (⊤ : Opens X.carrier)) q).hom ≫
    RightDerivedCoEdge.homologyFunctorToMapHomology
        (secF (structureSheafRing Y) (⊤ : Opens Y.carrier)) (pushforwardInjectiveResolution f F) q ≫
      ((secF (structureSheafRing Y) (⊤ : Opens Y.carrier)).mapIso
        ((injectiveResolution F).isoRightDerivedObj (modulePushforward f) q).symm).hom

/-- **[Stacks, Tag 01F4] part (2).** Let `f : X ⟶ Y` be a morphism of ringed spaces and let `F`
be a sheaf of `𝒪_X`-modules. If `H^p(Y, R^q f_* F) = 0` for every `p > 0` and every `q`, then
the canonical map `H^q(X, F) ⟶ Γ(Y, R^q f_* F)` is an isomorphism for every `q`; in particular
`H^q(X, F) = H^0(Y, R^q f_* F)`, which is what the source states.

Global sections on `X` *are* the direct image followed by global sections on `Y`, so the
cohomology of `X` is the homology of `Γ(Y, -)` applied to `K = f_*(I^•)` for an injective
resolution `I` of `F`. The terms of `K` are `Γ(Y, -)`-acyclic by [Stacks, Tag 01EX] part (2)
(`Stacks.LeraySections.rightAcyclic_secF_modulePushforward_obj`) and its cohomology objects are
`Γ(Y, -)`-acyclic by hypothesis, so `Γ(Y, -)` commutes with taking homology in degree `q`:
that is `Stacks.Cohomology.RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic`, and the
two transports in `cohomologyToSectionsHigherDirectImage` are isomorphisms. -/
@[stacks 01F4 "part (2)"]
theorem isIso_cohomologyToSectionsHigherDirectImage_of_vanishing
    (f : X ⟶ Y) (F : SheafOfModules.{u} (structureSheafRing X))
    (hvan : ∀ (p q : ℕ), 0 < p →
      IsZero (Hgroup (structureSheafRing Y) ⊤ p (((modulePushforward f).rightDerived q).obj F)))
    (q : ℕ) :
    IsIso (cohomologyToSectionsHigherDirectImage f F q) := by
  have hX : ∀ n, Stacks.RightDerivedComp.acyclic
      (secF (structureSheafRing Y) (⊤ : Opens Y.carrier))
      ((pushforwardInjectiveResolution f F).X n) := fun n =>
    (rightAcyclic_iff_isZero_rightDerived _ _).1
      (Stacks.LeraySections.rightAcyclic_secF_modulePushforward_obj f ⊤
        ((injectiveResolution F).cocomplex.X n) inferInstance)
  have hH : ∀ n, Stacks.RightDerivedComp.acyclic
      (secF (structureSheafRing Y) (⊤ : Opens Y.carrier))
      ((pushforwardInjectiveResolution f F).homology n) := fun n =>
    RightDerivedCoEdge.acyclic_of_iso _
      ((injectiveResolution F).isoRightDerivedObj (modulePushforward f) n)
      fun p hp => hvan p n hp
  have hmid' : IsIso (RightDerivedCoEdge.homologyFunctorToMapHomology
      (secF (structureSheafRing Y) (⊤ : Opens Y.carrier)) (pushforwardInjectiveResolution f F)
      q) :=
    RightDerivedCoEdge.isIso_homologyToMapHomology_of_acyclic _ _ hX hH q
  -- The two transports are isomorphisms, and `IsIso.comp_isIso'` takes the middle factor as an
  -- explicit argument: the source of `hmid'` is the homology of `Γ(Y, -)` applied to `f_*(I^•)`,
  -- which is `H^q(X, F)` only because `Γ(X, -)` *is* `f_* ⋙ Γ(Y, -)`, and instance search does
  -- not unfold the two functors to see it.
  unfold cohomologyToSectionsHigherDirectImage
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' hmid' (Iso.isIso_hom _))

/-- **[Stacks, Tag 01F4] part (2), as a bare existence statement.** Under the vanishing of
`H^p(Y, R^q f_* F)` for `p > 0`, there is an isomorphism `H^q(X, F) ≅ H^0(Y, R^q f_* F)`.

This forgets which map: the canonical one is an isomorphism by
`isIso_cohomologyToSectionsHigherDirectImage_of_vanishing`, of which this is the transport along
`Γ(Y, -) ≅ R^0 Γ(Y, -)`. It is the shape the consumers in
`StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing` take. -/
theorem nonempty_cohomology_iso_higherDirectImage_of_vanishing
    (f : X ⟶ Y) (F : SheafOfModules.{u} (structureSheafRing X))
    (hvan : ∀ (p q : ℕ), 0 < p →
      IsZero (Hgroup (structureSheafRing Y) ⊤ p (((modulePushforward f).rightDerived q).obj F)))
    (q : ℕ) :
    Nonempty (Hgroup (structureSheafRing X) ⊤ q F ≅
      Hgroup (structureSheafRing Y) ⊤ 0 (((modulePushforward f).rightDerived q).obj F)) :=
  have := isIso_cohomologyToSectionsHigherDirectImage_of_vanishing f F hvan q
  ⟨asIso (cohomologyToSectionsHigherDirectImage f F q) ≪≫
    ((secF (structureSheafRing Y) (⊤ : Opens Y.carrier)).rightDerivedZeroIsoSelf.app _).symm⟩

end Collapse

end Stacks.Cohomology.LerayModules

end
