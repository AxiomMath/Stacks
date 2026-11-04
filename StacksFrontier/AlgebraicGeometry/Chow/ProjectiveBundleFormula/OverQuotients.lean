module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients

/-!
# The universal property of the projective bundle `𝐏(ℰ)` of intersection theory

Let `X` be a scheme, `ℰ` a finite locally free `𝒪_X`-module and `π : 𝐏(ℰ) = Proj_X(Sym ℰ) ⟶ X`
its projective bundle, `Stacks.Chow.bundle` with projection `Stacks.Chow.bundleProj`, twist
`Stacks.Chow.bundleTwist` and tautological surjection `Stacks.Chow.bundleTautological :
π^*ℰ ⟶ 𝒪(1)`. **For every scheme `f : T ⟶ X` over `X`, the morphisms `g : T ⟶ 𝐏(ℰ)` with
`g ≫ π = f` correspond to the invertible quotients `f^*ℰ ↠ 𝓛` up to isomorphism**, the morphism
`g` going to the quotient `f^*ℰ ≅ g^*π^*ℰ ⟶ g^*𝒪(1)` it pulls back from the tautological one;
the correspondence is natural in `T`; and the identity of `𝐏(ℰ)` corresponds to the tautological
quotient itself. This is the description of `𝐏(ℰ)` given in [Stacks, Section 27.21] as a
consequence of [Stacks, Tag 01O4].

Everything here is the specialisation to `Stacks.Chow.bundle` of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients`, which proves it for an arbitrary
quasi-coherent module on the presentation `Stacks.RelativeProj.symGradedBundle` that
`Stacks.Chow.bundle` is built on. Nothing is assumed beyond the finite local freeness that
`Stacks.Chow.bundle` itself requires.

## Main definitions

* `Stacks.Chow.bundleOverQuotient`: the invertible quotient of `f^*ℰ` that a morphism
  `g : T ⟶ 𝐏(ℰ)` over `f` pulls back from the tautological surjection.
* `Stacks.Chow.bundleTautologicalQuotient`: the tautological surjection as an invertible quotient
  of `π^*ℰ`.
* `Stacks.Chow.bundleOverEquiv`: **the bijection** between the morphisms `T ⟶ 𝐏(ℰ)` over `f`
  and the isomorphism classes of invertible quotients of `f^*ℰ`.

## Main results

* `Stacks.Chow.bundleOverEquiv_apply`: the bijection sends `g` to the class of
  `bundleOverQuotient`.
* `Stacks.Chow.bundleOverEquiv_eq_iff`: `g` goes to the class of `Q` exactly when
  `g^*𝒪(1) ≅ Q.L` compatibly with the quotient maps.
* `Stacks.Chow.bundleOverEquiv_comp`: naturality in the test scheme.
* `Stacks.Chow.bundleOverEquiv_id`: the identity of `𝐏(ℰ)` corresponds to the tautological
  quotient `π^*ℰ ⟶ 𝒪(1)`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Divisors Stacks.Modules Stacks.RelativeProj

universe u

namespace Stacks.Chow

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] {T : Scheme.{u}}

/-- **The invertible quotient of `f^*ℰ` that a morphism `g : T ⟶ 𝐏(ℰ)` over `f` pulls back from
the tautological surjection**: `g^*𝒪(1)`, with the map
`f^*ℰ ≅ (g ≫ π)^*ℰ ≅ g^*π^*ℰ ⟶ g^*𝒪(1)`. -/
def bundleOverQuotient {f : T ⟶ X} (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    InvertibleQuotient T ((Scheme.Modules.pullback f).obj E) :=
  symGradedOverQuotient _ (Iso.refl _) g hg

/-- The invertible sheaf of `Stacks.Chow.bundleOverQuotient E g hg` is `g^*𝒪_{𝐏(ℰ)}(1)`. -/
@[simp] theorem bundleOverQuotient_L {f : T ⟶ X} (g : T ⟶ bundle E)
    (hg : g ≫ bundleProj E = f) :
    (bundleOverQuotient E g hg).L = (Scheme.Modules.pullback g).obj (bundleTwist E) :=
  rfl

/-- The quotient map of `Stacks.Chow.bundleOverQuotient E g hg` is the identification
`f^*ℰ ≅ (g ≫ π)^*ℰ` followed by the pullback along `g` of the tautological surjection. -/
theorem bundleOverQuotient_q {f : T ⟶ X} (g : T ⟶ bundle E) (hg : g ≫ bundleProj E = f) :
    (bundleOverQuotient E g hg).q =
      (Scheme.Modules.pullbackCongr hg).inv.app E ≫
        quotientMapAlong (bundleProj E) (bundleTautological E) g :=
  Category.id_comp _

/-- **The tautological surjection `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`**, `Stacks.Chow.bundleTautological`, as an
invertible quotient of `π^*ℰ`. -/
def bundleTautologicalQuotient :
    InvertibleQuotient (bundle E) ((Scheme.Modules.pullback (bundleProj E)).obj E) :=
  symGradedTautologicalQuotient E

/-- The invertible sheaf of `Stacks.Chow.bundleTautologicalQuotient E` is `𝒪_{𝐏(ℰ)}(1)`, that
is, `Stacks.Chow.bundleTwist E`. -/
@[simp] theorem bundleTautologicalQuotient_L : (bundleTautologicalQuotient E).L = bundleTwist E :=
  rfl

/-- The quotient map of `Stacks.Chow.bundleTautologicalQuotient E` is the tautological surjection
`π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`. -/
@[simp] theorem bundleTautologicalQuotient_q :
    (bundleTautologicalQuotient E).q = bundleTautological E :=
  rfl

/-- **The universal property of the projective bundle**: for a scheme `f : T ⟶ X` over `X`, the
morphisms `g : T ⟶ 𝐏(ℰ)` with `g ≫ π = f` are in bijection with the isomorphism classes of
invertible quotients of `f^*ℰ`. -/
def bundleOverEquiv (f : T ⟶ X) :
    { g : T ⟶ bundle E // g ≫ bundleProj E = f } ≃
      InvertibleQuotientClass T ((Scheme.Modules.pullback f).obj E) :=
  symGradedOverEquiv _ (Iso.refl _)

/-- **The bijection is normalised by the tautological surjection**: `g` goes to the class of
the quotient `Stacks.Chow.bundleOverQuotient` that it pulls back from `π^*ℰ ⟶ 𝒪(1)`. -/
theorem bundleOverEquiv_apply {f : T ⟶ X} (g : { g : T ⟶ bundle E // g ≫ bundleProj E = f }) :
    bundleOverEquiv E f g =
      Quotient.mk (invertibleQuotientSetoid _ _) (bundleOverQuotient E g.1 g.2) :=
  symGradedOverEquiv_apply _ (Iso.refl _) g

/-- **The bijection, spelled out**: `g` goes to the class of `Q` exactly when there is an
isomorphism `g^*𝒪(1) ≅ Q.L` carrying the quotient map that `g` pulls back from the tautological
surjection to `Q.q`. -/
theorem bundleOverEquiv_eq_iff {f : T ⟶ X} (g : { g : T ⟶ bundle E // g ≫ bundleProj E = f })
    (Q : InvertibleQuotient T ((Scheme.Modules.pullback f).obj E)) :
    bundleOverEquiv E f g = Quotient.mk (invertibleQuotientSetoid _ _) Q ↔
      ∃ α : (Scheme.Modules.pullback g.1).obj (bundleTwist E) ≅ Q.L,
        (Scheme.Modules.pullbackCongr g.2).inv.app E ≫
            quotientMapAlong (bundleProj E) (bundleTautological E) g.1 ≫ α.hom = Q.q :=
  (symGradedOverEquiv_eq_iff _ (Iso.refl _) g Q).trans
    (exists_congr fun _ => Iff.of_eq (congrArg (· = Q.q) (Category.id_comp _)))

/-- **The bijection is natural in the test scheme**: for `k : T' ⟶ T`, the bijection at `k ≫ f`
sends `k ≫ g` to the base change along `k` of the class assigned to `g`, the pullback of
`f^*ℰ` along `k` being identified with `(k ≫ f)^*ℰ` by the comparison of iterated pullbacks. -/
theorem bundleOverEquiv_comp {T' : Scheme.{u}} (k : T' ⟶ T) {f : T ⟶ X}
    (g : { g : T ⟶ bundle E // g ≫ bundleProj E = f }) :
    bundleOverEquiv E (k ≫ f) ⟨k ≫ g.1, by rw [Category.assoc, g.2]⟩ =
      Stacks.ProjectiveBundleQuotients.baseChangeClass k
        ((Scheme.Modules.pullbackComp k f).app E).symm (bundleOverEquiv E f g) := by
  have h := symGradedOverEquiv_comp _ (Iso.refl _) k _
    ((Scheme.Modules.pullbackComp k f).app E).symm g
  have hiso : ((Scheme.Modules.pullbackComp k f).app E).symm ≪≫
      (Scheme.Modules.pullback k).mapIso (Iso.refl ((Scheme.Modules.pullback f).obj E)) ≪≫
        (Scheme.Modules.pullbackComp k f).app E = Iso.refl _ := by
    ext1
    simp
  rw [hiso] at h
  exact h

/-- **The universal quotient is the tautological one**: under the bijection at the projection
`π` itself, the identity of `𝐏(ℰ)` corresponds to the class of the tautological surjection
`π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)`. -/
theorem bundleOverEquiv_id :
    bundleOverEquiv E (bundleProj E) ⟨𝟙 _, Category.id_comp _⟩ =
      Quotient.mk (invertibleQuotientSetoid _ _) (bundleTautologicalQuotient E) :=
  symGradedOverEquiv_id E

end Stacks.Chow

end
