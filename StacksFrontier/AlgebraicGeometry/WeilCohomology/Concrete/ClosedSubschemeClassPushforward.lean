module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubschemeChow

/-!
# Pushing forward the class of a closed subscheme that stays closed

Let `f : P ⟶ X` be a morphism of smooth projective schemes over `k`, equidimensional of dimensions
`d` and `e`, and `h : Z ⟶ P` a closed immersion such that `h ≫ f` is again a closed immersion.
Then `f_*[Z] = [Z]` in the Chow groups graded by codimension: the class of the closed subscheme
`Z ⊆ P` pushes forward to the class of the closed subscheme `Z ⊆ X`. This is Stacks 02R6 in the
special case where `Z ⟶ f(Z)` is an isomorphism, read through `CH^c(P) = CH_{d-c}(P)`.

In cohomology this gives the step of the proof of [Stacks, Tag 0FIR] that passes from the
embedding `h : Z ⟶ X × G` to `i = h ≫ pr₁ : Z ⟶ X`: if `h_*1 = γ([Z ⊆ P])` and `γ` commutes
with pushforward along `f` on the class `[Z ⊆ P]`, then `(h ≫ f)_*1 = γ([Z ⊆ X])`, by
functoriality of the pushforward (Stacks 0FHB).

## Main results

* `Stacks.WeilCohomology.equidimensionalPushforward_closedSubschemeClass`: `f_*[Z ⊆ P] = [Z ⊆ X]`.
* `Stacks.WeilCohomology.WeilData.pushforward_unitTw_comp_eq_cycleClass`: the cohomological step.

## References

* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 0FHB](https://stacks.math.columbia.edu/tag/0FHB)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **`f_*[Z ⊆ P] = [Z ⊆ X]`.** For a morphism `f : P ⟶ X` of smooth projective schemes over
`k`, equidimensional of dimensions `d` and `e`, and a closed immersion `h : Z ⟶ P` such that
`h ≫ f` is a closed immersion, the proper pushforward `CH^p(P) ⟶ CH^q(X)`, `q = p + e - d`,
carries the class of the closed subscheme `Z` of `P` to the class of the closed subscheme `Z`
of `X`. -/
theorem equidimensionalPushforward_closedSubschemeClass
    {P X : (SmoothProjectiveScheme k).FullSubcategory}
    (f : P ⟶ X) {Z : Scheme.{u}} (h : Z ⟶ P.obj.left) [IsClosedImmersion h]
    [IsClosedImmersion (h ≫ f.hom.left)] {d e : ℕ} (hP : RelativeDimension P.obj.hom d)
    (hX : RelativeDimension X.obj.hom e) (p q : ℤ) (hq : q = p + e - d) :
    equidimensionalPushforward f d e p q hq (closedSubschemeClass P.obj.hom h p) =
      closedSubschemeClass X.obj.hom (h ≫ f.hom.left) q := by
  funext e'
  by_cases he : e' = e
  · subst he
    have : IsProper f.hom.left := by
      have : IsProper (f.hom.left ≫ X.obj.hom) := by rw [Over.w f.hom]; infer_instance
      exact IsProper.of_comp f.hom.left X.obj.hom
    have := isIso_dimPart_self_ι P.obj.hom hP
    have := (isClopenDecomposition_dimPart P.obj.hom).isProper_ι d
    have : IsClosedImmersion (h ≫ inv (dimPart P.obj.hom d).ι) := inferInstance
    have : IsClosedImmersion ((h ≫ inv (dimPart P.obj.hom d).ι) ≫
        (dimPart P.obj.hom d).ι ≫ f.hom.left) := by
      rw [Category.assoc, IsIso.inv_hom_id_assoc]; infer_instance
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, closedSubschemeClass_apply]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, closedSubschemeClass_apply]
    refine chowGroupRestrict_heq_of_eq (fieldChowSituation k) (sA := X.obj.hom) (sA' := X.obj.hom)
      (sB := partBase X.obj.hom e') (sB' := partBase X.obj.hom e') (dimPart X.obj.hom e').ι
      (dimPart X.obj.hom e').ι rfl rfl rfl rfl rfl (show (d : ℤ) - p = e' - q by omega) _ _ ?_
    have hres : chowGroupRestrict (fieldChowSituation k) P.obj.hom (partBase P.obj.hom d)
        (dimPart P.obj.hom d).ι rfl ((d : ℤ) - p)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) P.obj.hom h
          ((d : ℤ) - p))) =
        QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) (partBase P.obj.hom d)
          ((d : ℤ) - p))
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) (partBase P.obj.hom d)
            (h ≫ inv (dimPart P.obj.hom d).ι) ((d : ℤ) - p)) := by
      refine (chowGroupRestrict_mk _ _ _ _ _ _ _).trans ?_
      rw [cycleGroupRestrict_of_isIso,
        properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp]
    rw [hres, properChowPushforward_mk,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
      cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation k) X.obj.hom
        ((h ≫ inv (dimPart P.obj.hom d).ι) ≫ (dimPart P.obj.hom d).ι ≫ f.hom.left)
        (h ≫ f.hom.left) (Iso.refl Z) (by simp)]
    exact Stacks.Chow.mk_cycleAssociatedToClosedSubscheme_heq _ _ _ (by omega)
  · have := isEmpty_dimPart_of_ne X.obj.hom hX he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- **`(h ≫ f)_*1 = γ([Z ⊆ X])` from `h_*1 = γ([Z ⊆ P])`.** Let `h : Z ⟶ P` and `f : P ⟶ X` be
morphisms of nonempty equidimensional smooth projective schemes over `k`, of dimensions `e`, `d'`
and `d`, with `h` and `h ≫ f` closed immersions, of codimensions `c' = d' - e` and `c = d - e`.
If `h_*1 = γ([Z ⊆ P])` in `H^{2c'}(P)(c')` and `γ` commutes with pushforward along `f` on the class
`[Z ⊆ P]`, then `(h ≫ f)_*1 = γ([Z ⊆ X])` in `H^{2c}(X)(c)`: by functoriality of the pushforward
(Stacks 0FHB) and `f_*[Z ⊆ P] = [Z ⊆ X]`. -/
theorem pushforward_unitTw_comp_eq_cycleClass (hA : W.PerfectPairing)
    {Z P X : (SmoothProjectiveScheme k).FullSubcategory} (h : Z ⟶ P) (f : P ⟶ X)
    [IsClosedImmersion h.hom.left] [IsClosedImmersion (h ≫ f).hom.left] {e d' d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e)
    (hP : IsNonemptyEquidimensional P d') (hX : IsNonemptyEquidimensional X d) (c' c : ℤ)
    (hc' : c' = d' - e) (hc : c = d - e)
    (hh : W.pushforward hA h hZ hP 0 0 (2 * c') c' (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass P c' (closedSubschemeClass P.obj.hom h.hom.left c'))
    (hf : W.cycleClass X c (equidimensionalPushforward f d' d c' c (by omega)
        (closedSubschemeClass P.obj.hom h.hom.left c')) =
      W.pushforward hA f hP hX (2 * c') c' (2 * c) c (by omega) (by omega)
        (W.cycleClass P c' (closedSubschemeClass P.obj.hom h.hom.left c'))) :
    W.pushforward hA (h ≫ f) hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass X c (closedSubschemeClass X.obj.hom (h ≫ f).hom.left c) := by
  have : IsClosedImmersion (h.hom.left ≫ f.hom.left) := ‹IsClosedImmersion (h ≫ f).hom.left›
  rw [← W.pushforward_comp hA h f hZ hP hX 0 0 (2 * c') c' (2 * c) c (by omega) (by omega)
    (by omega) (by omega), hh, ← hf,
    equidimensionalPushforward_closedSubschemeClass f h.hom.left hP.relativeDimension
      hX.relativeDimension c' c (by omega)]
  rfl

end WeilData

end Stacks.WeilCohomology

end
