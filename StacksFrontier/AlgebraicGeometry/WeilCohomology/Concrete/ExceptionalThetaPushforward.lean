module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalProjectionPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionPushforwardOne
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.CodimensionGysinRegularImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GrassmannianProjectionPushforward

/-!
# `π_*γ(j^!θ) = 1`

Let `i : Z ⟶ X` be a closed immersion of nonempty smooth projective schemes over `k`,
equidimensional of dimensions `e < m + 1`, `b : X' ⟶ X` the blowing up in `Z`, `j : E ⟶ X'` the
exceptional divisor, `π : E ⟶ Z`, and `θ` the class of Lemma 0FIH. This file proves the input
`hπ` of the proof of Tag 0FIT, for data (D0), (D1), (D2') satisfying (A1)–(A7):

* `π_*(j^!θ) = [Z]` in `CH^0(Z)`, for the Gysin map `j^!` of Stacks 0FF3 graded by codimension
  (`codimensionGysin`): this is the second relation of Lemma 0FIH, which is stated with the Gysin
  map of the regular immersion `j` on the parts of `X'`
  (`Stacks.Chow.properChowPushforward_codimensionGysin_eq` identifies the two);
* `π_*γ(j^!θ) = γ(π_*j^!θ)` (`WeilChernData.pushforwardCompatible_exceptionalProj`, Lemma 0FIN),
  and `γ(j^!θ) = j^*γ(θ)`, so `π_*(j^*γ(θ)) = γ([Z]) = 1`.

It is used in the proof of Tag 0FIT (`WeilChernData.cycleClassPushforward_of_globalSections`).

## Main results

* `SmoothProjectiveScheme.equidimensionalPushforward_codimensionGysin_blowupTheta`:
  `π_*(j^!θ) = [Z]`.
* `Stacks.WeilCohomology.WeilChernData.pushforward_pullTw_cycleClass_blowupTheta`: `hπ`.

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 0FIN](https://stacks.math.columbia.edu/tag/0FIN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero
  Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- **The second relation of Lemma 0FIH, `π_*(j^!θ) = [Z]`, for the Gysin map of Stacks 0FF3
graded by codimension**, for `Z` and `X` nonempty and equidimensional of dimensions `e < m + 1`:
`π_*` is the proper pushforward `CH^{r-1}(E) ⟶ CH^0(Z)`, `r = m + 1 - e`. -/
theorem equidimensionalPushforward_codimensionGysin_blowupTheta {m e : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X (m + 1))
    (he : e < m + 1) (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) :
    equidimensionalPushforward (exceptionalProj i) m e ((m + 1 - e - 1 : ℕ) : ℤ) 0 (by omega)
        (codimensionGysin (exceptionalObj i).obj.hom (blowupObj i).obj.hom
          (Over.w (exceptionalHom i).hom) ((m + 1 - e - 1 : ℕ) : ℤ)
          (blowupTheta i α (m + 1 - e))) =
      fundamentalClass Z := by
  have := hZ.nonempty
  have hnd := isNowhereDense_range_of_relativeDimension i hX.relativeDimension
    hZ.relativeDimension he
  have hr := coheight_eq_of_relativeDimension i hX.relativeDimension hZ.relativeDimension
  have hr0 : 0 < m + 1 - e := by omega
  have hE := isNonemptyEquidimensional_exceptionalObj i hX.relativeDimension hnd
  have hX' := isNonemptyEquidimensional_blowupObj i hX hnd
  have hallX := (relativeDimension_iff_forall_mem_dimPart _ (m + 1)).1 hX'.relativeDimension
  have hallE := (relativeDimension_iff_forall_mem_dimPart _ m).1 hE.relativeDimension
  have hrel := properChowPushforward_regularImmersionPartGysin_blowupTheta i hr hr0 α hα m
  funext e'
  by_cases he' : e' = e
  · subst he'
    have : IsProper (exceptionalProj i).hom.left := by
      have : IsProper ((exceptionalProj i).hom.left ≫ Z.obj.hom) := by
        rw [Over.w (exceptionalProj i).hom]; infer_instance
      exact IsProper.of_comp _ Z.obj.hom
    have : Smooth ((exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom) := by
      rw [Over.w (exceptionalHom i).hom]; infer_instance
    have hbr := properChowPushforward_codimensionGysin_eq
      (isRegularImmersion_of_isClosedImmersion (exceptionalHom i))
      Z.obj.hom (exceptionalObj i).obj.hom (Over.w (exceptionalHom i).hom)
      (exceptionalProj i).hom.left (Over.w (exceptionalProj i).hom) hallX hallE
      ((m + 1 - e' - 1 : ℕ) : ℤ) (blowupTheta i α (m + 1 - e'))
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply, ↓reduceDIte,
      AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
      AddEquiv.coe_toAddMonoidHom]
    rw [hbr, hrel, chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
    have hdeg : ∀ (a b : ℤ) (_ : a = b), fundamentalChowClass (fieldChowSituation k)
        (partBase Z.obj.hom e') a ≍ fundamentalChowClass (fieldChowSituation k)
        (partBase Z.obj.hom e') b := by
      rintro _ _ rfl; rfl
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      ((hdeg _ _ (by omega)).trans (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  · have := isEmpty_dimPart_of_ne Z.obj.hom hZ.relativeDimension he'
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end Stacks.WeilCohomology.SmoothProjectiveScheme


namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- `γ([Z]) = 1` for the data of `𝔚`. -/
theorem cycleClass_fundamentalClass_eq_unitTw (Z : (SmoothProjectiveScheme k).FullSubcategory) :
    𝔚.toWeilData.cycleClass Z 0 (fundamentalClass Z) = 𝔚.toWeilData.unitTw Z 0 0 rfl := by
  apply (𝔚.toWeilData.twCoord Z (2 * 0) 0).injective
  apply Subtype.ext
  refine (𝔚.isCohomologicalChernCharacter.coe_twCoord_toWeilData_cycleClass 𝔚.coproduct
    𝔚.projectiveBundle 𝔚.kunneth 𝔚.trace Z 0 (fundamentalClass Z)).trans ?_
  rw [𝔚.isCohomologicalChernCharacter.codimensionCycleClass_fundamentalClass]
  exact (𝔚.κ_unitTw Z).trans (𝔚.toWeilData.coe_twCoord_unitTw Z _ _ rfl).symm

/-- **`π_*(j^*γ(θ)) = 1`**, the input `hπ` of the proof of Tag 0FIT ("`π_*j^!θ = [Z]` implies
`π_*γ(j^!θ) = 1` by Lemma 0FIN because `π` is a projective space bundle"), for data satisfying
(A1)–(A7): `j^*γ(θ) = γ(j^!θ)` (axiom (C)(a)), `π_*γ = γπ_*` along `π`
(`pushforwardCompatible_exceptionalProj`), `π_*(j^!θ) = [Z]` (Lemma 0FIH,
`equidimensionalPushforward_codimensionGysin_blowupTheta`) and `γ([Z]) = 1`. -/
theorem pushforward_pullTw_cycleClass_blowupTheta {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : Z ⟶ X) [IsClosedImmersion i.hom.left] {m e : ℕ} (hZ : IsNonemptyEquidimensional Z e)
    (hX : IsNonemptyEquidimensional X (m + 1)) (he : e < m + 1)
    (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) :
    haveI := hZ.nonempty
    𝔚.toWeilData.pushforward 𝔚.perfectPairing (exceptionalProj i)
      (isNonemptyEquidimensional_exceptionalObj i hX.relativeDimension
        (isNowhereDense_range_of_relativeDimension i hX.relativeDimension hZ.relativeDimension
          he)) hZ
      (2 * ((m + 1 - e - 1 : ℕ) : ℤ)) ((m + 1 - e - 1 : ℕ) : ℤ) 0 0 (by omega) (by omega)
      (𝔚.toWeilData.pullTw (exceptionalHom i) _ _
        (𝔚.toWeilData.cycleClass (blowupObj i) ((m + 1 - e - 1 : ℕ) : ℤ)
          (blowupTheta i α (m + 1 - e)))) = 𝔚.toWeilData.unitTw Z 0 0 rfl := by
  have := hZ.nonempty
  have hnd := isNowhereDense_range_of_relativeDimension i hX.relativeDimension
    hZ.relativeDimension he
  have hE := isNonemptyEquidimensional_exceptionalObj i hX.relativeDimension hnd
  rw [← 𝔚.cycleClassPullback (exceptionalHom i) ((m + 1 - e - 1 : ℕ) : ℤ)
    (blowupTheta i α (m + 1 - e))]
  have hc := 𝔚.pushforwardCompatible_exceptionalProj i hX.relativeDimension hZ.relativeDimension
    he (m + 1 - 1) e hE hZ ((m + 1 - e - 1 : ℕ) : ℤ) 0 (by omega)
    (codimensionGysin (exceptionalObj i).obj.hom (blowupObj i).obj.hom
      (Over.w (exceptionalHom i).hom) ((m + 1 - e - 1 : ℕ) : ℤ) (blowupTheta i α (m + 1 - e)))
  refine hc.symm.trans ((congrArg (𝔚.toWeilData.cycleClass Z 0)
    (equidimensionalPushforward_codimensionGysin_blowupTheta i hZ hX he α hα)).trans ?_)
  exact 𝔚.cycleClass_fundamentalClass_eq_unitTw Z

end Stacks.WeilCohomology.WeilChernData

end
