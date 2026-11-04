module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFunctorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# The comparison functor of a square, on finite locally free modules over `colim_F 𝒪`

Let `p` be a prime and let

```
E ⟶ X'
↓     ↓
Z ⟶ X
```

be a commutative square of schemes in characteristic `p`. The transition functors of Stacks Tag
0EXE, `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback`, are strictly functorial, so the
two ways around the square agree up to the canonical composition isomorphism. This file records
that comparison and the functor it determines into the categorical fibre product

`𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}`,

which is the functor whose being an equivalence is asserted by Stacks Tags 0EXC (for the square
of Example 0EVG) and 0EXD (for the square of Example 0EVH). The construction is made for an
arbitrary commutative square, so that both tags instantiate one and the same functor; nothing
about almost blowup squares is used here.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`: **the comparison of the two
  composite transition functors around a commutative square.**
* `AlgebraicGeometry.frobeniusColimitVectorBundlesComparison`: **the functor
  `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` into the categorical fibre product** determined by it.

## Main results

* `AlgebraicGeometry.frobeniusColimitVectorBundlesComparison_fst` and
  `AlgebraicGeometry.frobeniusColimitVectorBundlesComparison_snd`: the two projections of the
  comparison functor are the two transition functors out of `𝒮_X`.

## Implementation notes

The fibre product is Mathlib's `CategoryTheory.Limits.CategoricalPullback`: its objects are a
finite locally free `colim_F 𝒪_Z`-module, a finite locally free `colim_F 𝒪_{X'}`-module and an
isomorphism of their transitions to `colim_F 𝒪_E`, which is the 2-fibre product the two tags'
displayed functors land in, taken literally. No cocycle condition over a triple overlap is
imposed, exactly as in the source.

The comparison isomorphism is the composition isomorphism of the transition functors in one
direction, the transport along the square's own commutativity, and the composition isomorphism
in the other direction. Because
`AlgebraicGeometry.frobeniusColimitStructureSheafHom_comp` is an equality of morphisms of
sheaves of rings and not merely an isomorphism, the transport is an `eqToIso` and no coherence
datum beyond the square's commutativity is needed.

## References

* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- **The comparison of the two composite transition functors around a commutative square**:
restricting from `X` to the center and then to the exceptional corner agrees with restricting
from `X` to the modification and then to the exceptional corner. -/
noncomputable def frobeniusColimitVectorBundlesSquareIso (hw : q ≫ b = e ≫ z) :
    frobeniusColimitVectorBundlesPullback p z hZ hX ⋙
        frobeniusColimitVectorBundlesPullback p e hE hZ ≅
      frobeniusColimitVectorBundlesPullback p b hX' hX ⋙
        frobeniusColimitVectorBundlesPullback p q hE hX' :=
  frobeniusColimitVectorBundlesPullbackComp p e z hE hZ hX ≪≫
    eqToIso (congrArg (fun g : E ⟶ X => frobeniusColimitVectorBundlesPullback p g hE hX)
      hw.symm) ≪≫
    (frobeniusColimitVectorBundlesPullbackComp p q b hE hX' hX).symm

/-- The square of transition functors, as a categorical commutative square over `𝒮_X`. -/
noncomputable def frobeniusColimitVectorBundlesCatCommSqOver (hw : q ≫ b = e ≫ z) :
    CategoricalPullback.CatCommSqOver
      (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')
      (frobeniusColimitVectorBundles X p hX) where
  fst := frobeniusColimitVectorBundlesPullback p z hZ hX
  snd := frobeniusColimitVectorBundlesPullback p b hX' hX
  iso := frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw

/-- **The functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` of a commutative square**, on the categories of
finite locally free modules over the Frobenius colimits of the structure sheaves. Stacks Tags
0EXC and 0EXD assert that it is an equivalence for the two shapes of almost blowup square. -/
noncomputable def frobeniusColimitVectorBundlesComparison (hw : q ≫ b = e ≫ z) :
    frobeniusColimitVectorBundles X p hX ⥤
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p e hE hZ)
        (frobeniusColimitVectorBundlesPullback p q hE hX') :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    (frobeniusColimitVectorBundlesCatCommSqOver p b z q e hX hX' hZ hE hw)

/-- The first projection of the comparison functor is restriction to the center. -/
lemma frobeniusColimitVectorBundlesComparison_fst (hw : q ≫ b = e ≫ z) :
    frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw ⋙
        CategoricalPullback.π₁ _ _ =
      frobeniusColimitVectorBundlesPullback p z hZ hX :=
  rfl

/-- The second projection of the comparison functor is restriction to the modification. -/
lemma frobeniusColimitVectorBundlesComparison_snd (hw : q ≫ b = e ≫ z) :
    frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw ⋙
        CategoricalPullback.π₂ _ _ =
      frobeniusColimitVectorBundlesPullback p b hX' hX :=
  rfl

/-! ### Restriction along an open immersion -/

section OpenImmersion

variable {Y W : Scheme.{u}} (f : W ⟶ Y) (V : Y.Opens)
  (hY : IsInCharacteristic Y p) (hW : IsInCharacteristic W p)
  (hV : IsInCharacteristic V.toScheme p)
  (hfV : IsInCharacteristic (f ⁻¹ᵁ V).toScheme p)

/-- **A transition functor commutes with restriction along an open immersion.**  For a morphism
`f : W ⟶ Y` of schemes in characteristic `p` and an open `V` of `Y`, restricting a finite locally
free `colim_F 𝒪_Y`-module along `f` and then to the open `f ⁻¹ᵁ V` of `W` agrees with restricting
it to `V` and then along the restricted morphism `f ∣_ V`.

Nothing about open subschemes is used: this is simply
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso` at the commutative square

```
f ⁻¹ᵁ V ⟶ V
   ↓       ↓
   W   ⟶   Y
```

whose commutativity is Mathlib's `AlgebraicGeometry.morphismRestrict_ι`.  No machinery beyond the
square comparison is involved: the square comparison is stated for an arbitrary commutative
square of schemes in characteristic `p`, and an open-immersion square is such a square.

Both functors here are transition functors, so this says nothing about *restriction of modules* to
an open subscheme on its own.  That the transition functor of an open immersion is indeed the
restriction functor — that is, that it agrees with
`AlgebraicGeometry.frobeniusColimitModuleRestrict`, which is slice restriction followed by the
identification `(colim_F 𝒪_Y)|_V ≅ colim_F 𝒪_V` — is a separate statement, and it is
`AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback`
(`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitOpenPullback.lean`).  It is what the
trivialising-cover step of [Stacks, Tag 0EXD] needs in order to feed a trivialised module to the
free case, and it is proved there and not here. -/
noncomputable def frobeniusColimitVectorBundlesRestrictIso :
    frobeniusColimitVectorBundlesPullback p f hW hY ⋙
        frobeniusColimitVectorBundlesPullback p (f ⁻¹ᵁ V).ι hfV hW ≅
      frobeniusColimitVectorBundlesPullback p V.ι hV hY ⋙
        frobeniusColimitVectorBundlesPullback p (f ∣_ V) hfV hV :=
  frobeniusColimitVectorBundlesSquareIso p V.ι f (f ∣_ V) (f ⁻¹ᵁ V).ι hY hV hW hfV
    (morphismRestrict_ι f V)

end OpenImmersion

end AlgebraicGeometry

end
