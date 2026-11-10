module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.PerfectDual
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect

/-!
# A representability theorem for homological functors on a regular proper scheme

Let `X` be a proper scheme over a field `k` which is regular, and let
`G : D_perf(𝒪_X) → Vect_k` be a `k`-linear homological functor with
`∑_{n ∈ ℤ} dim_k G(E[n]) < ∞` for every perfect `E`. Then `G ≅ Hom_X(K, -)` for a perfect `K`:
this is [Stacks, Tag 0H4A].

## Main results

* `Representability.exists_iso_linearCoyoneda_of_isHomological_of_isRegular`:
  **[Stacks, Tag 0H4A]**.
* `Representability.exists_iso_linearCoyoneda_of_representability`:
  the source's proof, from the representability theorem [Stacks, Tag 0FYH] on `D_perf(𝒪_X)`
  taken as the argument `h0FYH`; the registered statement supplies it.

## Implementation notes

The proof is the source's. The dual `E ↦ E^∨` of [Stacks, Tag 08DQ] is an exact
anti-self-equivalence of `D_perf(𝒪_X)`: it is `perfectDual`, restricted to the perfect objects by
`CategoryTheory.ObjectProperty.restrictDual`, and the biduality map is a natural isomorphism on
them. So `F(E) = G(E^∨)` is a `k`-linear cohomological functor of finite total dimension
(`CategoryTheory.Functor.isHomological_comp_of_exists_distinguished`, `perfectDualShiftIso`), and
[Stacks, Tag 0FYH] gives `F ≅ Hom_X(-, K')` with `K'` in `D^b_Coh(𝒪_X)`. On a regular scheme
`K'` is perfect ([Stacks, Tag 0FDC]), and `G(E) = Hom_X(E^∨, K') = Hom_X(K'^∨, E)`
(`CategoryTheory.exists_iso_linearCoyoneda_of_comp_iso_linearYoneda`).

## References

* [Stacks Project, Tag 0H4A](https://stacks.math.columbia.edu/tag/0H4A)
* [Stacks Project, Tag 0FYH](https://stacks.math.columbia.edu/tag/0FYH)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Cohomology.PerfectComplexes

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Representability

attribute [local instance] AlgebraicGeometry.isTriangulated_isPerfect_locallySmall

section Perfect

variable (Y : Scheme.{u})

/-- **The dual on `D_perf(𝒪_X)`**, `E ↦ E^∨`, at the locally small model. -/
abbrev perfectDerivedDual : (perfectDerived Y)ᵒᵖ ⥤ perfectDerived Y :=
  ObjectProperty.restrictDual _ (perfectDual Y) (isPerfect_perfectDual_obj Y)

/-- **The biduality isomorphism `E ≅ (E^∨)^∨` on `D_perf(𝒪_X)`** ([Stacks, Tag 08DQ]). -/
def perfectDerivedBidualIso :
    𝟭 (perfectDerived Y) ≅ (perfectDerivedDual Y).rightOp ⋙ perfectDerivedDual Y :=
  ObjectProperty.restrictBidualIso _ (perfectDual Y) (isPerfect_perfectDual_obj Y)
    (perfectBidual Y) (isIso_perfectBidual_app Y)

/-- `(E[n])^∨ ≅ (E^∨)[-n]` on `D_perf(𝒪_X)`. -/
def perfectDerivedDualShiftIso (E : perfectDerived Y) (n : ℤ) :
    (perfectDerivedDual Y).obj (op (E⟦n⟧)) ≅ ((perfectDerivedDual Y).obj (op E))⟦-n⟧ :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((perfectDual Y).mapIso (((ObjectProperty.ι _).commShiftIso n).app E).op.symm ≪≫
      perfectDualShiftIso Y E.obj n ≪≫
      (((ObjectProperty.ι _).commShiftIso (-n)).app ((perfectDerivedDual Y).obj (op E))).symm)

end Perfect

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

attribute [local instance] AlgebraicGeometry.modulesLinear

/-- The dual on `D_perf(𝒪_X)` is `k`-linear. -/
theorem perfectDerivedDual_map_smul {E E' : perfectDerived X.left} (f : E ⟶ E') (r : k) :
    (perfectDerivedDual X.left).map (r • f).op = r • (perfectDerivedDual X.left).map f.op := by
  ext
  exact perfectDual_map_smul X f.hom r

include X in
/-- **Stacks Project, Tag 0H4A, from Tag 0FYH.** Let `X` be a proper scheme over a field `k` which
is regular, and let `G : D_perf(𝒪_X) → Vect_k` be a `k`-linear homological functor with
`∑_{n ∈ ℤ} dim_k G(E[n]) < ∞` for every perfect `E`. Then `G ≅ Hom_X(K, -)` for a perfect `K`,
provided the representability theorem [Stacks, Tag 0FYH] holds, which is the hypothesis `h0FYH`,
stated exactly as `exists_iso_linearYoneda_of_converse` concludes it. -/
theorem exists_iso_linearCoyoneda_of_representability
    (h0FYH : ∀ (F : (perfectDerived X.left)ᵒᵖ ⥤ ModuleCat.{u} k) [F.IsHomological]
      (_ : ∀ {E E' : (perfectDerived X.left)ᵒᵖ} (f : E ⟶ E') (r : k),
        F.map ((r • f.unop).op) = r • F.map f)
      (_ : ∀ E : perfectDerived X.left,
        Cardinal.sum (fun n : ℤ => Module.rank k (F.obj (op (E⟦n⟧)))) < Cardinal.aleph0),
      ∃ K : DerivedCategory X.left.Modules,
        DerivedCategoryB.derivedCategoryBBounded (fun M : X.left.Modules => M.IsCoherent) K ∧
          Nonempty (F ≅ (ObjectProperty.ι _).op ⋙
            (linearYoneda k (DerivedCategory X.left.Modules)).obj K))
    (hX : IsRegular X.left)
    (G : perfectDerived X.left ⥤ ModuleCat.{u} k) [G.IsHomological]
    (hG : ∀ {E E' : perfectDerived X.left} (f : E ⟶ E') (r : k), G.map (r • f) = r • G.map f)
    (hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (G.obj (E⟦n⟧))) < Cardinal.aleph0) :
    ∃ K : perfectDerived X.left,
      Nonempty (G ≅ (linearCoyoneda k (perfectDerived X.left)).obj (op K)) := by
  let D := perfectDerivedDual X.left
  have hDtri := ObjectProperty.exists_distinguished_restrictDual
    (fun K : DerivedCategory X.left.Modules => IsPerfect.{u, u, u} (X := X.left.toRingedSpace) K)
    (perfectDual X.left)
    (isPerfect_perfectDual_obj X.left) (exists_distinguished_perfectDual X.left)
  let F : (perfectDerived X.left)ᵒᵖ ⥤ ModuleCat.{u} k := D ⋙ G
  have : F.IsHomological := Functor.isHomological_comp_of_exists_distinguished D hDtri G
  have hF : ∀ {E E' : (perfectDerived X.left)ᵒᵖ} (f : E ⟶ E') (r : k),
      F.map ((r • f.unop).op) = r • F.map f := by
    intro E E' f r
    change G.map (D.map (r • f.unop).op) = r • G.map (D.map f.unop.op)
    rw [perfectDerivedDual_map_smul, hG]
  have hFfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (F.obj (op (E⟦n⟧)))) < Cardinal.aleph0 := by
    intro E
    have hrank : ∀ n : ℤ, Module.rank k (F.obj (op (E⟦n⟧))) =
        Module.rank k (G.obj ((D.obj (op E))⟦-n⟧)) := fun n =>
      (G.mapIso (perfectDerivedDualShiftIso X.left E n)).toLinearEquiv.rank_eq
    obtain ⟨h1, h2⟩ := CoherentCharacterization.lt_aleph0_cardinalSum_iff.1 (hfin (D.obj (op E)))
    refine CoherentCharacterization.lt_aleph0_cardinalSum_iff.2 ⟨fun n => ?_, ?_⟩
    · rw [hrank]
      exact h1 (-n)
    · refine (h2.preimage (fun a _ b _ h => neg_injective h)).subset fun n hn => ?_
      simpa [hrank] using hn
  obtain ⟨K', hK', ⟨e⟩⟩ := h0FYH F hF hFfin
  have hperf : IsPerfect.{u, u, u} (X := X.left.toRingedSpace) K' :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular hX K' hK'
  let KP : perfectDerived X.left := ⟨K', hperf⟩
  let eK : (ObjectProperty.ι _).op ⋙ (linearYoneda k (DerivedCategory X.left.Modules)).obj K' ≅
      (linearYoneda k (perfectDerived X.left)).obj KP :=
    NatIso.ofComponents (fun E =>
      (show (E.unop.obj ⟶ K') ≃ₗ[k] (E.unop ⟶ KP) from
        { toFun := fun f => ObjectProperty.homMk f
          invFun := fun f => f.hom
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }).toModuleIso) (by
      intro E E' f
      ext g
      rfl)
  exact ⟨_, exists_iso_linearCoyoneda_of_comp_iso_linearYoneda k D (perfectDerivedDual_map_smul X)
    (perfectDerivedBidualIso X.left) G KP (e ≪≫ eK)⟩

/-- **Stacks Project, Tag 0H4A.** Let `X` be a proper scheme over a field `k` which is regular. Let
`G : D_perf(𝒪_X) → Vect_k` be a `k`-linear homological functor such that
`∑_{n ∈ ℤ} dim_k G(E[n]) < ∞` for all `E ∈ D_perf(𝒪_X)`. Then `G` is isomorphic to a functor of the
form `E ↦ Hom_X(K, E)` for some `K ∈ D_perf(𝒪_X)`.

Here `D_perf(𝒪_X)` is `AlgebraicGeometry.perfectDerived`, the perfect objects of the derived
category of `𝒪_X`-modules with its triangulated structure; "homological" is
`CategoryTheory.Functor.IsHomological`; `k`-linearity is for the `k`-structure induced by the
structure morphism, `AlgebraicGeometry.modulesLinear`; the sum is the cardinal sum of the
`k`-ranks over all of `ℤ`, and `< ∞` is `< ℵ₀`; regularity is `AlgebraicGeometry.IsRegular`
([Stacks, Tag 02IS]); and the isomorphism is one of `Vect_k`-valued functors with
`linearCoyoneda`, the `k`-linear `Hom_X(K, -)`.

The proof is the source's (`exists_iso_linearCoyoneda_of_representability`): `F(E) = G(E^∨)` is
cohomological of finite total dimension, so `F ≅ Hom_X(-, K')` with `K' ∈ D^b_Coh(𝒪_X)` by
[Stacks, Tag 0FYH] (`exists_iso_linearYoneda_of_isHomological_of_isProper`), `K'` is perfect by
[Stacks, Tag 0FDC], and `G ≅ Hom_X(K'^∨, -)` by [Stacks, Tag 08DQ]. -/
@[stacks 0H4A]
theorem exists_iso_linearCoyoneda_of_isHomological_of_isRegular [IsProper X.hom]
    (hX : IsRegular X.left)
    (G : perfectDerived X.left ⥤ ModuleCat.{u} k) [G.IsHomological]
    (hG : ∀ {E E' : perfectDerived X.left} (f : E ⟶ E') (r : k), G.map (r • f) = r • G.map f)
    (hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (G.obj (E⟦n⟧))) < Cardinal.aleph0) :
    ∃ K : perfectDerived X.left,
      Nonempty (G ≅ (linearCoyoneda k (perfectDerived X.left)).obj (op K)) :=
  exists_iso_linearCoyoneda_of_representability X
    (fun F _ hF hFfin => exists_iso_linearYoneda_of_isHomological_of_isProper X F hF hFfin)
    hX G hG hfin

end Stacks.AlgebraicGeometry.DerivedVarieties.Representability

end
