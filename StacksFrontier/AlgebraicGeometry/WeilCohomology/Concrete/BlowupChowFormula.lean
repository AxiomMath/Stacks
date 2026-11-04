module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcess
public import StacksFrontier.AlgebraicGeometry.Chow.MinusAdamsOperator
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsTotalChern
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionGysinCap

/-!
# The class `b^*α^∨ - [𝒪_{X'}(E)]` of Lemma 0FIH

For a closed immersion `i : Z ⟶ X` of smooth projective schemes over `k` with blowing up
`b : X' ⟶ X`, exceptional divisor `j : E ⟶ X'` and `π : E ⟶ Z`, let `α ∈ K_0(Vect(X))` restrict
to the class of `𝒞_{Z/X}` on `Z`. Then `b^*α^∨ - [ℐ_E^∨]` restricts on `E` to the class of
`𝓕^∨`, where `𝓕 = Ker(π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'})` and `ℐ_E^∨ = 𝒪_{X'}(E)`.

## Main results

* `AlgebraicGeometry.VectorBundleKZero.pullback_comp`: `(f ≫ g)^* = f^* ∘ g^*` on `K_0(Vect)`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.blowupKClass`: `ψ^{-1}(b^*α - [ℐ_E])
  = b^*α^∨ - [ℐ_E^∨]`, with `ψ^{-1}` the minus-one Adams operation (Tag 0FV8).
* `Stacks.WeilCohomology.SmoothProjectiveScheme.pullback_blowupKClass`: `j^*(b^*α^∨ - [ℐ_E^∨])
  = [𝓕^∨]`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.blowupTheta`:
  `θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X'] ∈ CH^{r-1}(X')`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.regularImmersionGysin_blowupTheta`:
  `j^!θ = c_{r-1}(𝓕^∨) ∩ [E]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.VectorBundleKZero

/-- **Pullback on `K_0(Vect)` is functorial**: `(f ≫ g)^* a = f^*(g^* a)`. -/
theorem pullback_comp {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (a : VectorBundleKZero W) :
    pullback (f ≫ g) a = pullback f (pullback g a) := by
  have h : pullback (f ≫ g) = (pullback f).comp (pullback g) := by
    refine addHom_ext fun M hM => ?_
    have := Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree M
    have := Stacks.Chow.isFiniteLocallyFree_pullbackObj M g
    have := Stacks.Chow.isFiniteLocallyFree_pullbackObj M (f ≫ g)
    rw [AddMonoidHom.comp_apply, pullback_classOf, pullback_classOf, pullback_classOf]
    exact classOf_eq_of_iso ((Scheme.Modules.pullbackComp f g).app M).symm
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)
  rw [h, AddMonoidHom.comp_apply]

end AlgebraicGeometry.VectorBundleKZero

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

open AlgebraicGeometry.VectorBundleKZero Stacks.ClosedImmersion
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- The minus-one Adams operation `ψ^{-1}` of `K_0(Vect(T))`, `[ℰ] ↦ [ℰ^∨]` (Tag 0FV8). -/
abbrev minusOneAdams (T : Scheme.{u}) : VectorBundleKZero T →+* VectorBundleKZero T :=
  dualRingHom (dualPreservesFiniteLocallyFree T) (dualShortExact T)

/-- The minus-one Adams operation sends the class of a finite locally free module `ℰ` to the
class of its dual: `ψ^{-1}[ℰ] = [ℰ^∨]`. -/
theorem minusOneAdams_classOf {T : Scheme.{u}} (M : T.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    minusOneAdams T (classOf T M) = classOf T (dualSheaf M) :=
  dualAddHom_classOf (dualPreservesFiniteLocallyFree T) (dualShortExact T) M
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree M)

/-- Pullback along `f : T' ⟶ T` commutes with the minus-one Adams operation:
`f^*(ψ^{-1} a) = ψ^{-1}(f^* a)`. -/
theorem pullback_minusOneAdams {T T' : Scheme.{u}} (f : T' ⟶ T) (a : VectorBundleKZero T) :
    VectorBundleKZero.pullback f (minusOneAdams T a) =
      minusOneAdams T' (VectorBundleKZero.pullback f a) := by
  rw [pullback_eq_pullbackRingHom, pullback_eq_pullbackRingHom]
  exact (dualAddHom_pullback f (dualPreservesFiniteLocallyFree T) (dualShortExact T)
    (dualPreservesFiniteLocallyFree T') (dualShortExact T') (pullbackRingHom f)
    (pullbackRingHom_classOf f) a).symm

/-- The ideal sheaf `ℐ_E` of the exceptional divisor `E ⊂ X'`. -/
abbrev exceptionalIdeal : (blowupObj i).obj.left.Modules :=
  idealSheaf (exceptionalHom i).hom.left.toLRSHom.toShHom

/-- **The class `b^*α^∨ - [𝒪_{X'}(E)]` of Lemma 0FIH**, defined as `ψ^{-1}(b^*α - [ℐ_E])`. -/
def blowupKClass (α : VectorBundleKZero X.obj.left) : VectorBundleKZero (blowupObj i).obj.left :=
  minusOneAdams _
    (VectorBundleKZero.pullback (blowupHom i).hom.left α - classOf _ (exceptionalIdeal i))


/-- An invertible module on a scheme is finite locally free. -/
private theorem isFiniteLocallyFree_of_isInvertible_scheme {T : Scheme.{u}} (L : T.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
  @Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree _ _
    (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ _ hL)

/-- **`b^*α^∨ - [𝒪_{X'}(E)]` restricts to `[𝓕^∨]` on `E`**, for `α` restricting to `[𝒞_{Z/X}]`
on `Z`. -/
theorem pullback_blowupKClass (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) :
    VectorBundleKZero.pullback (exceptionalHom i).hom.left (blowupKClass i α) =
      classOf _ (dualSheaf (excessConormal i)) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (centreConormal i) :=
    Stacks.ConormalSequenceRight.isFiniteLocallyFree_conormalSheaf_of_smooth i.hom.left X.obj.hom
  have hI := isFiniteLocallyFree_of_isInvertible_scheme _
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (isInvertible_idealSheaf_exceptionalHom i))
  have hCE := isFiniteLocallyFree_of_isInvertible_scheme _ (isInvertible_exceptionalConormal i)
  have hsq : (exceptionalHom i).hom.left ≫ (blowupHom i).hom.left =
      (exceptionalProj i).hom.left ≫ i.hom.left := (isPullback_exceptional i).w
  have hS := excessShortComplex_shortExact i
  have hF : classOf _ ((Scheme.Modules.pullback (exceptionalProj i).hom.left).obj
      (centreConormal i)) = classOf _ (excessConormal i) + classOf _ (exceptionalConormal i) :=
    @classOf_shortExact _ _ _ _ (excessShortComplex i).f (excessShortComplex i).g hS.mono_f
      hS.epi_g (excessShortComplex i).zero
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree
        (M := (Scheme.Modules.pullback (exceptionalProj i).hom.left).obj (centreConormal i))
        (hM := Stacks.Chow.isFiniteLocallyFree_pullback _ _ inferInstance))
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _) hS.exact
  rw [blowupKClass, pullback_minusOneAdams, map_sub, ← VectorBundleKZero.pullback_comp, hsq,
    VectorBundleKZero.pullback_comp, hα,
    pullback_classOf, pullback_classOf,
    ← classOf_eq_of_iso (exceptionalConormalIso i)
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _),
    hF, add_sub_cancel_right, minusOneAdams_classOf]

/-! ### `θ` and `j^!θ` -/

open Stacks.Chow in
/-- **`θ = c_{r-1}(b^*α^∨ - [𝒪_{X'}(E)]) ∩ [X'] ∈ CH^{r-1}(X')`** of the proof of Lemma 0FIH,
formed on each part of `X'` of constant dimension. -/
def blowupTheta (α : VectorBundleKZero X.obj.left) (r : ℕ) :
    codimensionChowGroup k (blowupObj i).obj.hom ((r - 1 : ℕ) : ℤ) :=
  totalChowClassCapFundamental (blowupObj i).obj.hom
    (totalChernKClass (fieldChowSituation k) (blowupObj i).obj.hom (blowupKClass i α)) (r - 1)

open Stacks.Chow in
/-- **`j^!θ = c_{r-1}(𝓕^∨) ∩ [E]`**, for `X` equidimensional of dimension `n` and `α` restricting
to `[𝒞_{Z/X}]`. The two sides live on the Chow groups of `E` for the equal structure morphisms
`j ≫ (X' ⟶ Spec k)` and `E ⟶ Spec k`, and are compared by `HEq`. -/
theorem regularImmersionGysin_blowupTheta {n : ℕ} (hX : RelativeDimension X.obj.hom n)
    (α : VectorBundleKZero X.obj.left)
    (hα : VectorBundleKZero.pullback i.hom.left α = classOf _ (centreConormal i)) (r : ℕ) :
    regularImmersionGysin (blowupObj i).obj.hom (exceptionalHom i).hom.left
        (isRegularImmersion_of_isClosedImmersion (exceptionalHom i)) (n - 1) ((r - 1 : ℕ) : ℤ)
        (blowupTheta i α r) ≍
      excessChernCap i r ((n - 1 : ℕ) : ℤ) := by
  have hw : (exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom = (exceptionalObj i).obj.hom :=
    Over.w (exceptionalHom i).hom
  have key : ∀ (q : (exceptionalObj i).obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q],
      q = (exceptionalObj i).obj.hom → RelativeDimension q (n - 1) := by
    rintro q _ rfl; exact relativeDimension_exceptionalObj i hX
  have hY : RelativeDimension ((exceptionalHom i).hom.left ≫ (blowupObj i).obj.hom) (n - 1) :=
    key _ hw
  rw [blowupTheta, regularImmersionGysin_totalChowClassCapFundamental _ _ _ _ hY,
    res_totalChernKClass, pullback_blowupKClass i α hα, totalChernKClass_classOf, excessChernCap,
    chowCohomologyCap_fundamentalChowClass]
  have key : ∀ (q : (exceptionalObj i).obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q],
      q = (exceptionalObj i).obj.hom →
      chowCohomologyCapFundamentalClass (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) q ((n - 1 : ℕ) : ℤ) ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) q
            (dualSheaf (excessConormal i)) (r - 1)) ≍
        chowCohomologyCapFundamentalClass (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) (exceptionalObj i).obj.hom
          ((n - 1 : ℕ) : ℤ) ((r - 1 : ℕ) : ℤ)
          (totalChernOfFiniteLocallyFree (fieldChowSituation k) (exceptionalObj i).obj.hom
            (dualSheaf (excessConormal i)) (r - 1)) := by
    rintro q _ rfl; rfl
  exact key _ hw

end Stacks.WeilCohomology.SmoothProjectiveScheme
