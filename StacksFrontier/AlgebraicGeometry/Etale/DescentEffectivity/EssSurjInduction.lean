module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.EffectivityTransport
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.EssSurjReduction

/-!
# The Noetherian induction step of Tag 0BTP, reduced to one affine chart at a generic point

`AlgebraicGeometry.isEquivalence_quasiCompactSeparatedEtaleDescentFunctor_of_exists_not_le`
derives [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) from a single step of the
Noetherian induction: over an affine Noetherian base `T`, along a finite surjective `g : Y ⟶ T`,
a quasi-compact separated étale descent datum effective over a proper open `U₀` is effective over
some open not contained in `U₀`. This file performs the two bookkeeping halves of that step and
isolates what is left.

The first half is the way the step ends. An open over which the datum is effective and which
contains one point outside `U₀` is already enough: the join of that open with `U₀` is effective,
because effectivity is stable under joins
(`AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_iSup`), and it is not contained in
`U₀`, because of that one point. So the step never needs to compare two opens; it only has to
produce an effective open through a prescribed point of the complement of `U₀`.

The second half is the way the step begins. The complement of `U₀` is a nonempty closed subset of
a Noetherian sober space, so it can be cut down by an open set to an irreducible piece with a
generic point `ξ` (`Topology.exists_isOpen_isIrreducible_genericPoint`), and that open set can be
shrunk to an affine open `W` still containing `ξ`, the affine opens being a basis. Over `W` the
complement of `U₀` is irreducible with generic point `ξ`, which is the situation the geometric
part of the argument is stated in.

What remains between the two is the geometric content of the source's proof, and it is stated
here as the hypothesis of
`AlgebraicGeometry.exists_isEtaleEffective_baseDatum_not_le_of_affineChart`: over an affine
Noetherian base on which the complement of `U₀` is irreducible with generic point `ξ`, the datum
is effective over some open containing `ξ`.

## Main results

* `AlgebraicGeometry.DescentDatum.exists_isEtaleEffective_baseDatum_not_le_of_mem`: **an
  effective open through a point outside `U₀` gives an effective open not contained in `U₀`**,
  namely its join with `U₀`.
* `AlgebraicGeometry.exists_isAffineOpen_isIrreducible_subset_closure_of_ne_top`: **a proper open
  of a Noetherian scheme has an affine open chart in which its complement is irreducible with a
  generic point.**
* `AlgebraicGeometry.exists_isEtaleEffective_baseDatum_not_le_of_affineChart`: **the Noetherian
  induction step of Tag 0BTP, reduced to the affine chart at a generic point of the
  complement.**

## Implementation notes

The join of the two opens is formed as a `Bool`-indexed supremum, that being the shape
`AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_iSup` takes; `iSup_bool_eq` turns it
back into a join.

The generic point is carried as a point of the ambient scheme together with the inclusion of the
piece in the closure of that point, rather than as `IsGenericPoint`: the piece is an open part of
the irreducible closed set it is dense in, so its closure is strictly larger than itself and
`IsGenericPoint ξ (W ∩ U₀ᶜ)` would be false. This is the form
`Topology.exists_isOpen_isIrreducible_genericPoint` produces and the form the geometric step
consumes.

## References

* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-! ### The end of the step: joining the new effective open to the old one -/

namespace DescentDatum

/-- **An open over which the datum is effective and which contains a point outside `U₀` gives an
open over which the datum is effective and which is not contained in `U₀`.** The two opens are
joined: effectivity is stable under suprema by
`AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_iSup`, and the point lies in the join
but not in `U₀`. -/
theorem exists_isEtaleEffective_baseDatum_not_le_of_mem {S X : Scheme.{u}} {f : X ⟶ S}
    [Surjective f] [IsIntegralHom f] (D : DescentDatum f) [Etale D.over.hom] {U₀ W : S.Opens}
    (h₀ : (D.baseDatum U₀).IsEtaleEffective) (hW : (D.baseDatum W).IsEtaleEffective) {ξ : S}
    (hξW : ξ ∈ W) (hξU₀ : ξ ∉ U₀) :
    ∃ U : S.Opens, (D.baseDatum U).IsEtaleEffective ∧ ¬ U ≤ U₀ := by
  refine ⟨W ⊔ U₀, ?_, fun hle ↦ hξU₀ (hle ((le_sup_left : W ≤ W ⊔ U₀) hξW))⟩
  have h := D.isEtaleEffective_baseDatum_iSup (fun b : Bool ↦ cond b W U₀)
    fun b ↦ by cases b with
      | false => exact h₀
      | true => exact hW
  rwa [iSup_bool_eq] at h

end DescentDatum

/-! ### The beginning of the step: an affine chart at a generic point of the complement -/

/-- **A proper open of a Noetherian scheme has an affine open chart in which its complement is
irreducible with a generic point.** The complement of `U₀` is a nonempty closed subset of a
Noetherian sober space, so `Topology.exists_isOpen_isIrreducible_genericPoint` cuts it down by an
open set to an irreducible piece with a generic point `ξ`; the affine opens being a basis, that
open set contains an affine open still containing `ξ`, and the piece cut out by the smaller open
is still irreducible with the same generic point. -/
theorem exists_isAffineOpen_isIrreducible_subset_closure_of_ne_top (T : Scheme.{u})
    [IsNoetherian T] {U₀ : T.Opens} (hU₀ : U₀ ≠ ⊤) :
    ∃ (W : T.Opens) (ξ : T), IsAffineOpen W ∧ ξ ∈ W ∧ ξ ∉ U₀ ∧
      IsIrreducible ((W : Set T) ∩ (U₀ : Set T)ᶜ) ∧
        (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ} := by
  have _ : NoetherianSpace (T : Type u) := IsNoetherian.noetherianSpace
  have hUne : (U₀ : Set T) ≠ Set.univ := fun h ↦ hU₀ (Opens.ext (by rw [h, Opens.coe_top]))
  have hne : (Set.univ ∩ (U₀ : Set T)ᶜ).Nonempty := by
    rw [Set.univ_inter]
    exact Set.nonempty_compl.mpr hUne
  obtain ⟨V, hVopen, -, -, ξ, hξmem, hsub⟩ :=
    Topology.exists_isOpen_isIrreducible_genericPoint (α := T) isOpen_univ _
      U₀.isOpen.isClosed_compl hne
  obtain ⟨-, ⟨W, hW, rfl⟩, hξW, hWV⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hξmem.1.1 hVopen
  have hWsub : (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ} :=
    fun y hy ↦ hsub ⟨⟨hWV hy.1, Set.mem_univ y⟩, hy.2⟩
  exact ⟨W, ξ, hW, hξW, hξmem.2, Topology.isIrreducible_of_mem_of_subset_closure_singleton
    ⟨hξW, hξmem.2⟩ hWsub, hWsub⟩

/-! ### The step reduced to the affine chart -/

/-- **The Noetherian induction step of Tag 0BTP, reduced to the affine chart at a generic point
of the complement.** The hypothesis is the geometric content of the source's proof: over an
affine Noetherian base, with a quasi-compact separated étale descent datum effective over an open
`U₀`, and given an affine open chart `W` in which the complement of `U₀` is irreducible with
generic point `ξ`, the datum is effective over some open containing `ξ`.

Given that, the step itself is bookkeeping:
`AlgebraicGeometry.exists_isAffineOpen_isIrreducible_subset_closure_of_ne_top` produces the
affine chart `W` at a generic point `ξ` of the complement, and
`AlgebraicGeometry.DescentDatum.exists_isEtaleEffective_baseDatum_not_le_of_mem` joins the open
it returns to `U₀`. -/
theorem exists_isEtaleEffective_baseDatum_not_le_of_affineChart
    (Hchart : ∀ (T Y : Scheme.{u}) (g : Y ⟶ T), IsAffine T → IsNoetherian T → IsFinite g →
      Surjective g → ∀ (D : DescentDatum g) (_ : Etale D.over.hom), QuasiCompact D.over.hom →
        IsSeparated D.over.hom → ∀ (U₀ W : T.Opens) (ξ : T),
          (D.baseDatum U₀).IsEtaleEffective → IsAffineOpen W → ξ ∈ W → ξ ∉ U₀ →
            IsIrreducible ((W : Set T) ∩ (U₀ : Set T)ᶜ) →
              (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ} →
                ∃ V : T.Opens, ξ ∈ V ∧ (D.baseDatum V).IsEtaleEffective)
    (T Y : Scheme.{u}) (g : Y ⟶ T) (hT : IsAffine T) (hTN : IsNoetherian T) (hg : IsFinite g)
    (hgs : Surjective g) (D : DescentDatum g) (hD : Etale D.over.hom)
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom) (U₀ : T.Opens)
    (heff : (D.baseDatum U₀).IsEtaleEffective) (hne : U₀ ≠ ⊤) :
    ∃ U : T.Opens, (D.baseDatum U).IsEtaleEffective ∧ ¬ U ≤ U₀ := by
  have := hD
  have := hg
  have := hgs
  have hgi : IsIntegralHom g := inferInstance
  obtain ⟨W, ξ, hWaff, hξW, hξU₀, hirr, hclos⟩ :=
    exists_isAffineOpen_isIrreducible_subset_closure_of_ne_top T hne
  obtain ⟨V, hξV, hV⟩ :=
    Hchart T Y g hT hTN hg hgs D hD hqc hsep U₀ W ξ heff hWaff hξW hξU₀ hirr hclos
  exact D.exists_isEtaleEffective_baseDatum_not_le_of_mem heff hV hξV hξU₀

end AlgebraicGeometry

end
