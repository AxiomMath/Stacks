module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtFunctorBaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.HomShift.DerivedShift

/-!
# Shifting the dualizing object shifts the degree of the Ext system

`Stacks.Algebraization.dualizingExtFunctor ω i` is `X ↦ H^{-i}(RHom_A(X, ω))`. Shifting `ω`
shifts the degree:

`H^{-i}(RHom_A(X, ω⟦k⟧)) ≅ H^{-(i-k)}(RHom_A(X, ω))`     naturally in `X`.

Nothing new is proved here. The two halves both exist and are both already natural in the
source variable:

* `Dualizing.dualizingDerivedHomShiftIso` — `RHom_A(K, Ω⟦k⟧) ≅ RHom_A(K, Ω)⟦k⟧`, an
  isomorphism of functors on `D(A)ᵒᵖ`, proved for the universe-polymorphic adjunction
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`;
* `StacksDraft.PseudoCoherence.homologyFunctorShiftIso` — `Hⁱ(-⟦k⟧) ≅ H^{k+i}(-)`, the shift
  sequence on the homology functors.

The one step that is not mere composition is crossing between the two derived-Hom models:
`Stacks.Algebraization.dualizingExtFunctor` is written with the same-universe adjunction
`StacksDraft.DerivedHom.derivedHomAdjunction`, and the shift identification above with the
universe-polymorphic one. That crossing is `Dualizing.derivedHomIntoFunctorNatIso`, which is
`Dualizing.modelHomNatIsoDerivedHomAdjunctionOverRing` — an isomorphism of *bifunctors* —
whiskered into the source slot; the same step the flat base-change comparison of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.DualizingExtFunctorBaseChange` makes.

## Main definitions

* `Dualizing.derivedHomIntoFunctorShift` — the shift identification at the
  `Dualizing.derivedHomIntoFunctor` spelling.
* `Stacks.Algebraization.dualizingExtFunctorShift` — the degree shift on the functor.
* `Stacks.Algebraization.dualizingExtSystemShift` — the degree shift on the direct system,
  which is the form the route of [Stacks, Tag 0EHK] consumes.

## Implementation notes

Why the route of [Stacks, Tag 0EHK] needs this. Over a chart the base change of a normalized
dualizing complex is dualizing but *not* normalized, and at a prime `𝔮` of the chart ring the
source's normalized choice is `(ω_B^∙)_𝔮⟦-δ(𝔮)⟧` for `δ` the dimension function of the
original normalized complex. So the complex that is available there is `ω⟦δ(𝔮)⟧` for the
normalized `ω`, and this file turns the Ext system against it in degree `i` into the system
against the normalized one in degree `i - δ(𝔮)`.

That is the sign that matches the rest of the chain: the bootstrap situation
`Stacks.Algebraization.exists_bootstrapSituation_closedPoint` produces at a point `y` has
`B.s = s - δ^Y_Z(y)`, and its conclusion runs over `i ≤ B.s`, so the degrees `i ≤ s` of the
conclusion of [Stacks, Tag 0EHK] are exactly the degrees `i - δ(y) ≤ s - δ(y)` of the local
statement. The identification of that `δ(𝔮)` with `δ^Y_Z(y)` is a separate statement and is
*not* proved anywhere in the library; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.LocalCohomologyMatlisDualModel`.

`Stacks.Algebraization.dualizingExtFunctorCongr` is the companion of this file: it transports
the system along an isomorphism `ω ≅ ω'`, with no degree change. The two together move the Ext
system from any dualizing complex isomorphic to a shift of the normalized one onto the
normalized one, which is all the uniqueness statements
`Dualizing.isNormalizedDualizingComplex_shift_iff_eq` and
`Dualizing.IsNormalizedDualizingComplex.nonempty_iso` deliver.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C), derived Hom.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A]

/-- **Derived Hom into a shifted object is the shift of derived Hom**, at the spelling
`Dualizing.derivedHomIntoFunctor` uses: `RHom_A(-, ω⟦k⟧) ≅ RHom_A(-, ω)⟦k⟧` as an isomorphism
of contravariant functors on `D(A)`.

This is `Dualizing.dualizingDerivedHomShiftIso`, which is proved for the universe-polymorphic
adjunction, conjugated by `Dualizing.derivedHomIntoFunctorNatIso` to bring it to the
same-universe adjunction that `Dualizing.derivedHomIntoFunctor` is built from. -/
def derivedHomIntoFunctorShift (ω : DerivedCategory (ModuleCat.{u} A)) (k : ℤ) :
    derivedHomIntoFunctor (ω⟦k⟧) ≅
      derivedHomIntoFunctor ω ⋙
        CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k :=
  derivedHomIntoFunctorNatIso _ ≪≫ dualizingDerivedHomShiftIso.{u, u} A ω k ≪≫
    Functor.isoWhiskerRight (derivedHomIntoFunctorNatIso ω).symm _

end Dualizing

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Shifting the dualizing object shifts the degree:**
`H^{-i}(RHom_A(-, ω⟦k⟧)) ≅ H^{-(i-k)}(RHom_A(-, ω))`, as an isomorphism of functors on
`(ModuleCat A)ᵒᵖ`.

`Dualizing.derivedHomIntoFunctorShift` moves the shift out of the dualizing object, and
`StacksDraft.PseudoCoherence.homologyFunctorShiftIso` absorbs it into the degree. -/
def dualizingExtFunctorShift (ω : DerivedCategory (ModuleCat.{u} A)) (k i : ℤ) :
    dualizingExtFunctor (ω⟦k⟧) i ≅ dualizingExtFunctor ω (i - k) :=
  Functor.isoWhiskerLeft _
    (Functor.isoWhiskerRight (Dualizing.derivedHomIntoFunctorShift ω k) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Dualizing.derivedHomIntoFunctor ω)
        (StacksDraft.PseudoCoherence.homologyFunctorShiftIso.{u, u} (R := A) k (-i) ≪≫
          eqToIso (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A))
            (by omega : k + -i = -(i - k)))))

/-- **The degree shift on the direct system**, compatibly with the transition maps:
`Stacks.Algebraization.dualizingExtFunctorShift` restricted along the inverse system, exactly
as `Stacks.Algebraization.dualizingExtSystemCongr` restricts
`Stacks.Algebraization.dualizingExtFunctorCongr`. -/
def dualizingExtSystemShift (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (k i : ℤ) :
    dualizingExtSystem M (ω⟦k⟧) i ≅ dualizingExtSystem M ω (i - k) :=
  Functor.isoWhiskerLeft _ (dualizingExtFunctorShift ω k i)

/-- **The degree shift read in the direction the route of [Stacks, Tag 0EHK] uses it:** the Ext
functor against `ω` in degree `i` is the Ext functor against `ω⟦-k⟧` in degree `i - k`.

This is `Stacks.Algebraization.dualizingExtFunctorShift` at `ω⟦-k⟧` together with
`ω ≅ (ω⟦-k⟧)⟦k⟧`. It is this direction that applies at a point: there `ω` is the complex that
is *available* — the base change of the normalized complex — and `ω⟦-k⟧` is the normalized
choice, `k` being the shift that normalizes it. -/
def dualizingExtFunctorShiftNeg (ω : DerivedCategory (ModuleCat.{u} A)) (k i : ℤ) :
    dualizingExtFunctor ω i ≅ dualizingExtFunctor (ω⟦-k⟧) (i - k) :=
  dualizingExtFunctorCongr
      (((CategoryTheory.shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} A)) (-k) k
        (neg_add_cancel k)).app ω).symm) i ≪≫
    dualizingExtFunctorShift (ω⟦-k⟧) k i

/-- **`Stacks.Algebraization.dualizingExtFunctorShiftNeg` on the direct system**, compatibly
with the transition maps. -/
def dualizingExtSystemShiftNeg (M : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (ω : DerivedCategory (ModuleCat.{u} A)) (k i : ℤ) :
    dualizingExtSystem M ω i ≅ dualizingExtSystem M (ω⟦-k⟧) (i - k) :=
  Functor.isoWhiskerLeft _ (dualizingExtFunctorShiftNeg ω k i)

end Stacks.Algebraization

end
