module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.CanonicalSummandIdentification

/-!
# The restriction of a global object to the total site restricts to its locally given datum

Let `(C, O_C)` be a ringed site with fibre products, `f_i : U_i ⟶ X` a family of arrows and `N`
an object of `D(O_X)`. The restrictions `N|_{U_i}`, glued by the canonical comparisons on the
overlaps, form the data of Situation 0DC9 on `C/X`. The restriction of `N` to the total site of
the Čech object of the family restricts, on every summand, to the corresponding locally given
object, compatibly with the transitions.

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.canonicalSummandIdentification`: the summandwise
  identification of the restriction of a global object to the total site with its locally given
  datum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

open CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard pretopologyRingedSite_over_hasPullbacks

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (OC : Sheaf P.toGrothendieck CommRingCat.{u}) {ι : Type u} {U : ι → C} (f : ∀ i, U i ⟶ X)

/-- The component of `cechTransitionNat'` at `N` is the image under restriction to the summand
`t` of the derived transition of the total restriction of `N`, followed by the summand comparison
`cechSummandIso` at `N`. -/
theorem cechTransitionNat'_app {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechObject P OC f).obj (op n)).I)
    (N : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X) :
    (cechTransitionNat' P OC f φ t).app N =
      (summandRestriction (overRingedSite P OC (X := X))
          (cechObject P OC f) n t).mapDerivedCategory.map
          (((situation (overRingedSite P OC (X := X)).J
              (cechObject P OC f)).derivedComponentModuleTransition
            (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) φ).app
              ((cechTotalRestriction P OC f).mapDerivedCategory.obj N)) ≫
        (cechSummandIso P OC f n t).hom.app N :=
  rfl

/-- The component of `cechPullbackNat` at `N` is the composite of the summandwise derived pullback
isomorphism of `globalLocallyGiven`, the restriction of the summand comparison `cechSummandIso` at
`N`, and the component of `globalRhoNat` at `N`. -/
theorem cechPullbackNat_app (N₀ : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    {m n : SimplexCategory} (φ : m ⟶ n) (t : ((cechObject P OC f).obj (op n)).I)
    (N : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X) :
    (cechPullbackNat P OC f N₀ φ t).app N =
      ((globalLocallyGiven P OC f N₀).summandDerivedPullbackIso
          (cechLift (X := pretopologyRingedSite P OC) f) φ t).hom.app
            (((situation (overRingedSite P OC (X := X)).J
                (cechObject P OC f)).derivedComponentModuleRestriction
              (structureSheaf (overRingedSite P OC (X := X)) (cechObject P OC f)) m).obj
                ((cechTotalRestriction P OC f).mapDerivedCategory.obj N)) ≫
        ((globalLocallyGiven P OC f N₀).restriction
          (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)).map
            ((cechSummandIso P OC f m
              (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)).hom.app N) ≫
        (globalRhoNat P OC f
          (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)).app N := by
  show 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ ((globalLocallyGiven P OC f N₀).restriction
          (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)).map (𝟙 _) ≫ _ ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  rfl

/-- **The canonical summandwise identification of the restriction of a global object to the
total site** with the locally given datum of that object. -/
def canonicalSummandIdentification (N : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X) :
    (globalLocallyGiven P OC f N).SummandIdentification
      (cechLift (X := pretopologyRingedSite P OC) f)
      ((cechTotalRestriction P OC f).mapDerivedCategory.obj N) where
  iso n t := (cechSummandIso P OC f n t).app N
  comm {m n} φ t := by
    have h := NatTrans.congr_app (cechTransitionNat'_eq_cechPullbackNat P OC f N φ t) N
    have h1 := cechTransitionNat'_app P OC f φ t N
    have h2 := cechPullbackNat_app P OC f N φ t N
    have h3 :=
      globalRhoNat_app P OC f (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t) N
    exact h1.symm.trans (h.trans (h2.trans (congrArg (fun x => _ ≫ _ ≫ x) h3)))

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
