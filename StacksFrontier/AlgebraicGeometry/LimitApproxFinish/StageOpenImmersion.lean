module

public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.FibreProductColimit
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.FibreProductOpenImmersion

/-!
# The open immersion of a stage of the overlap into the spectrum of a fibre product

Let `R = colim_i R_i` be a filtered colimit of rings, let `s : B ⟶ R` be a ring map, and form
the fibre products `B_i = B ×_R R_i` of `Stacks.FibreProduct`.  Suppose the overlap is cut out
of `Spec B` by finitely many standard opens `D(g_l)` on which `B_{g_l} → R_{s(g_l)}` is an
isomorphism.  Then, at every stage carrying lifts of the `s(g_l)`, the union of the
corresponding standard opens of `Spec R_i` maps by an open immersion to `Spec B_i`.

This is the ring-theoretic half of step (ii) of the one-affine-open step of Tag 07RN.  In that
argument `B` is the ring of the affine open being added, `R` is the ring of global sections of
the overlap, the `R_i` are the rings of global sections of the models of the overlap at the
finite stages, and the conclusion is the open immersion `W_i ⟶ Spec R_i ⟶ Spec B_i` which makes
the glued stage of step (iii) possible.

## Main results

* `AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq` is the main statement: it is
  `AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback` — Tag 01Z9 —
  applied to the cartesian square `Stacks.FibreProduct.isPullback`.  The only work is to rewrite
  the square into the shape of plain ring maps that Tag 01Z9 states, which is what
  `CommRingCat.ofHom_hom` does.  No filteredness and no colimit hypothesis enter.

* `AlgebraicGeometry.exists_stage_isOpenImmersion_spec_fibreProduct` chooses the stage: the
  finitely many elements `s(g_l)` of `R` all come from one stage by
  `Stacks.FibreProduct.exists_app_eq_fin`, and that stage satisfies the hypothesis of the
  previous statement.

* `AlgebraicGeometry.app_eq_of_app_eq_map` records that the hypothesis is inherited by every
  later stage, by transporting the lifts along the transition map.  The one-affine-open argument
  needs the conclusion at *all* stages above the chosen one, since the new index preorder is
  built from them.

## Implementation notes

The hypothesis that `B_{g_l} → R_{s(g_l)}` is an isomorphism is phrased, as in Tag 01Z9, as
bijectivity of `Localization.awayMap`.  In the geometric application it comes from the
quasi-compact quasi-separated form of the sections-of-a-standard-open lemma, Tag 01P7, which is
Mathlib's `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`, applied once to the affine open
being added and once to the overlap.

The index universe is tied to the universe of the rings throughout, as in Tag 06AC:
`CommRingCat` in one universe does not have colimits over a larger index universe, so freeing
the index universe breaks the synthesis that the colimit hypothesis rests on.

* Tag 01Z9 is stated for bare types with `CommRing` instances, while the fibre product here
  lives in `CommRingCat`.  The bridge is that `CommRingCat.of ↥X` is the object `X` again, and
  that `CommRingCat.ofHom φ.hom` is `φ`; both are handled by `simp`, but a statement written
  with the wrong one of each pair will not unify.

* The second projection `Stacks.FibreProduct.snd` is the map Tag 01Z9 calls `r`, and the first
  projection is its `p`.  Swapping them gives a true cartesian square and the wrong conclusion:
  the open immersion goes into the spectrum of the corner *opposite* the one whose standard
  opens are being taken.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Category.{u} K] {F : K ⥤ CommRingCat.{u}} {R : CommRingCat.{u}}
  (τ : F ⟶ (Functor.const K).obj R) {B : CommRingCat.{u}} (s : B ⟶ R)

/-- **The open immersion into the spectrum of the fibre product.**  Let `D(g_l)` be finitely many
standard opens of `Spec B` on which `B_{g_l} → R_{s(g_l)}` is an isomorphism, and let `f_l` be
lifts of the `s(g_l)` to the stage `i`.  Then the union of the standard opens `D(f_l)` of
`Spec R_i` maps by an open immersion to the spectrum of `B_i = B ×_R R_i`.

This is Tag 01Z9 applied to the cartesian square `Stacks.FibreProduct.isPullback`. -/
lemma isOpenImmersion_spec_fibreProduct_of_app_eq {n : ℕ} (g : Fin n → B) (i : K)
    (f : Fin n → F.obj i) (hf : ∀ l, τ.app i (f l) = s (g l))
    (hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) :
    IsOpenImmersion ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec (F.obj i)).Opens).ι ≫
      Spec.map (Stacks.FibreProduct.snd s (τ.app i))) := by
  have hcart : IsPullback
      (CommRingCat.ofHom (Stacks.FibreProduct.fst s (τ.app i)).hom)
      (CommRingCat.ofHom (Stacks.FibreProduct.snd s (τ.app i)).hom)
      (CommRingCat.ofHom s.hom) (CommRingCat.ofHom (τ.app i).hom) := by
    simpa using Stacks.FibreProduct.isPullback s (τ.app i)
  simpa using isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback
    s.hom (Stacks.FibreProduct.fst s (τ.app i)).hom
    (Stacks.FibreProduct.snd s (τ.app i)).hom (τ.app i).hom hcart f g hf hloc

/-- The lifts of finitely many elements of the colimit transport to every later stage. -/
lemma app_eq_of_app_eq_map {n : ℕ} (g : Fin n → B) {i j : K} (u : i ⟶ j)
    (f : Fin n → F.obj i) (hf : ∀ l, τ.app i (f l) = s (g l)) :
    ∀ l, τ.app j (F.map u (f l)) = s (g l) := fun l ↦ by simpa using hf l

variable [IsFiltered K]

/-- **Some stage carries the open immersion into the spectrum of the fibre product.**  The
finitely many elements `s(g_l)` of the colimit all come from one stage, and that stage satisfies
the hypothesis of `AlgebraicGeometry.isOpenImmersion_spec_fibreProduct_of_app_eq`.  By
`AlgebraicGeometry.app_eq_of_app_eq_map` so does every later stage. -/
lemma exists_stage_isOpenImmersion_spec_fibreProduct (hτ : IsColimit (Cocone.mk R τ)) {n : ℕ}
    (g : Fin n → B) (hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) :
    ∃ (i : K) (f : Fin n → F.obj i), (∀ l, τ.app i (f l) = s (g l)) ∧
      IsOpenImmersion ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec (F.obj i)).Opens).ι ≫
        Spec.map (Stacks.FibreProduct.snd s (τ.app i))) := by
  obtain ⟨i, f, hf⟩ := Stacks.FibreProduct.exists_app_eq_fin hτ fun l ↦ s (g l)
  exact ⟨i, f, hf, isOpenImmersion_spec_fibreProduct_of_app_eq τ s g i f hf hloc⟩

end AlgebraicGeometry
