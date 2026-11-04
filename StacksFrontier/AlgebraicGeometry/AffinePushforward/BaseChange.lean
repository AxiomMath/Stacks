module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic

/-!
# The base-change morphism for direct images of sheaves of modules

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
this file constructs the canonical base-change morphism
`g^* f_* ⟶ f'_* (g')^*` of functors on sheaves of modules.  It is the mate, under the two
pullback--pushforward adjunctions, of the canonical identification of the two composite
direct images around the square.

## Main definitions

* `Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso` is the identification
  `g'_* ∘ f_* ≅ f'_* ∘ g_*` of the two composite direct images around a commutative square.
* `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is the base-change
  morphism `g^* f_* ⟶ f'_* (g')^*`, natural in the module.
* `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` identifies the
  restriction of an inverse image to an open with the inverse image along the restricted
  morphism.

## Implementation notes

The base-change morphism is defined as the mate of an isomorphism rather than postulated, so
it is canonical and natural in the module.  A commutative square suffices to define it; the
base-change assertion of Stacks Tag 02KG is that it is an isomorphism when the square is
cartesian and `f` is affine, on quasi-coherent modules.

`pullbackRestrictIso` is obtained by uniqueness of left adjoints: the right adjoints of the
two composites are the direct images along the two ways around the restriction square, and
those agree by `AlgebraicGeometry.morphismRestrict_ι`.

## References

* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforward

section BaseChange

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

/-- For a commutative square `g' ≫ f = f' ≫ g`, the canonical identification of the two
composite direct images `g'_* ∘ f_*` and `f'_* ∘ g_*` around the square. -/
noncomputable def pushforwardSquareIso (w : g' ≫ f = f' ≫ g) :
    Scheme.Modules.pushforward g' ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward g :=
  Scheme.Modules.pushforwardComp g' f ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
    (Scheme.Modules.pushforwardComp f' g).symm

/-- The canonical base-change morphism `g^* f_* ⟶ f'_* (g')^*` attached to a commutative
square `g' ≫ f = f' ≫ g` of schemes.  It is the mate, under the two
pullback--pushforward adjunctions, of `pushforwardSquareIso`. -/
noncomputable def baseChangeNatTrans (w : g' ≫ f = f' ≫ g) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ Scheme.Modules.pushforward f' :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g')
      (Scheme.Modules.pullbackPushforwardAdjunction g)).symm
    ((Scheme.Modules.pushforwardComp g' f).hom ≫
      (Scheme.Modules.pushforwardCongr w).hom ≫
      (Scheme.Modules.pushforwardComp f' g).inv)

/-- The base-change morphism `baseChangeNatTrans w` is the mate, under the two
pullback--pushforward adjunctions, of the identification `pushforwardSquareIso w`. -/
lemma baseChangeNatTrans_eq (w : g' ≫ f = f' ≫ g) :
    baseChangeNatTrans w =
      (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g')
        (Scheme.Modules.pullbackPushforwardAdjunction g)).symm (pushforwardSquareIso w).hom :=
  rfl

end BaseChange

/-! ### Restriction of an inverse image to an open of the source -/

section PullbackRestrict

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- The adjunction exhibiting `pullback f ⋙ restrictFunctor (f ⁻¹ᵁ V).ι` as a left adjoint of
the direct image along `(f ⁻¹ᵁ V).ι ≫ f`. -/
noncomputable def pullbackRestrictAdjunction :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⊣
      Scheme.Modules.pushforward ((f ⁻¹ᵁ V).ι ≫ f) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ V).ι)).ofNatIsoRight
    (Scheme.Modules.pushforwardComp (f ⁻¹ᵁ V).ι f)

/-- The adjunction exhibiting `restrictFunctor V.ι ⋙ pullback (f ∣_ V)` as a left adjoint of
the direct image along `(f ∣_ V) ≫ V.ι`. -/
noncomputable def restrictPullbackAdjunction :
    Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (f ∣_ V) ⊣
      Scheme.Modules.pushforward ((f ∣_ V) ≫ V.ι) :=
  ((Scheme.Modules.restrictAdjunction V.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V))).ofNatIsoRight
    (Scheme.Modules.pushforwardComp (f ∣_ V) V.ι)

/-- Restriction to the preimage of an open `V` commutes with the inverse image: the
restriction to `f ⁻¹ᵁ V` of `f^* M` is the inverse image along `f ∣_ V` of the restriction of
`M` to `V`. -/
noncomputable def pullbackRestrictIso :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ≅
      Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback (f ∣_ V) :=
  (pullbackRestrictAdjunction f V).leftAdjointUniq
    ((restrictPullbackAdjunction f V).ofNatIsoRight
      (Scheme.Modules.pushforwardCongr (morphismRestrict_ι f V)))

end PullbackRestrict

end Stacks.AlgebraicGeometry.AffinePushforward

end
