module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pasting the underived étale base change map along the direct image legs

Let

```
Y' --π'--> Y --h--> X'
|e'         |e       |f'
v           v        v
T' --π ---> T --g--> S
```

be two commutative squares of schemes sharing the edge `e : Y ⟶ T`, so that `h ≫ f' = e ≫ g`
and `π' ≫ e = e' ≫ π`. The outer rectangle commutes as well, its two horizontal composites
being `G = π ≫ g` and `H = π' ≫ h`, and this file proves that the underived base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` of the outer rectangle is the composite of the
base change maps of the two squares, read through the composition comparisons for the **direct
images** along those two composites:

`ψ_outer = H_*-to-π'_*h_* ∘ h_*(ψ_{π}) ∘ ψ_{g} ∘ (f')⁻¹(G_*-to-π_*g_*)`.

This is the direction of pasting that the integral-base steps of [Stacks, Tag 0F02] need, and
it is the direction nothing in this library had at any level. Every pasting law already present
on the étale side composes along the **inverse image** legs, the shared edge being a direct
image: `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_comp` and `..._comp'` in
`BaseChangeHigher/BasePasting.lean`, `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste` in
`BaseChangeHigher/SmallEtaleBaseChangePasting.lean`, and — derived and degreewise —
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_comp` and
`Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app`. The law proved here is the étale
abelian, underived form of [Stacks, Tag 0E46], which the library carries for ringed topoi and
sheaves of modules as
`Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_comp`; that statement lives in
the unbounded derived category of sheaves of modules on a ringed topos and so cannot be applied
to the small étale sites of schemes with abelian coefficients.

A second, independent gap is filled on the way:
`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso`, the composition isomorphism
`R(a ≫ b)_* ≅ Ra_* ⋙ Rb_*` on the bounded below derived categories. The library had **no** form
of this for direct image — only the underived
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso` and, degreewise and only for an
*integral* first leg, `Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral` — whereas the
inverse-image counterpart `Stacks.EtaleCohomology.smallEtaleDerivedPullbackComp` has been there
all along. It is the comparison that the derived form of the pasting law below will need.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso` — the composition isomorphism
  `R(a ≫ b)_* ≅ Ra_* ⋙ Rb_*` on bounded below derived categories, for arbitrary morphisms of
  schemes.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_pasteDirectImage` — the pasting law as an
  identity of 2-squares, with the two composites carried as named morphisms.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_pasteDirectImage_app` and
  `..._app'` — the same identity evaluated at an abelian sheaf, with the composites named and
  written out respectively.

## Implementation notes

The proof is the generic pasting law for mates,
`Stacks.Cohomology.DerivedBaseChangePasting.mate_twoSquare_paste`, which is stated for arbitrary
categories and adjunctions and is therefore site-agnostic. It consumes three things.

* The identification of the base change map as a mate of the comparison of the two composite
  **inverse** images around the square. That is
  `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_mateEquiv`, already proved in
  `BaseChangeHigher/BasePasting.lean`; it is the mate taken under the adjunctions of the two
  *horizontal* morphisms of the square, which is the orientation in which the direction of
  pasting is reversed. (The other mate description,
  `Stacks.EtaleCohomology.mateEquiv_smallEtaleBaseChangeAb`, is under the adjunctions of the
  two *vertical* morphisms and is what the inverse-image-direction law uses.)
* The cocycle identity for those inverse image comparison squares, in the **vertical**
  direction. This is `pullbackComparison_vComp` below, the counterpart of the horizontal
  `Stacks.EtaleCohomology.pullbackComparison_hComp` of `BaseChangeHigher/BasePasting.lean`,
  which is `private` there and composes the other way. It is three instances of the
  associativity pentagon `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'_assoc`, for the
  three chains `Y' → Y → X' → S`, `Y' → Y → T → S` and `Y' → T' → T → S`, rearranged by
  `vPasteChase`.
* The conjugates of the two comparisons of the composite legs. Those are
  `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso'_def` followed by
  `Stacks.Cohomology.BaseChange.conjugateEquiv_leftAdjointCompIso_hom` and
  `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv`; they say that the conjugate
  of the inverse image comparison of a composite is the direct image comparison, which is the
  étale instance already recorded (for written-out composites) as
  `Stacks.EtaleCohomology.conjugateEquiv_smallEtalePullbackAbCompIso_hom` and `..._inv`.

The hypotheses are the commutativity of the two squares and nothing else: neither square need be
cartesian, and no finiteness, separatedness or torsion condition enters, inverse image of abelian
sheaves being exact for every morphism of schemes.

*No derived or degreewise pasting law is proved here.* The degreewise statement that
[Stacks, Tag 0F04] and [Stacks, Tag 0F05] need is the cohomology of the derived counterpart of
this law, read through the relative Leray identifications of
`BaseChangeHigher/IntegralRelativeLeray.lean`. Of the two things that needs, one is now proved
and one is present but unconnected.

* **Proved, in `BaseChangeHigher/SmallEtaleDerivedDirectImagePasting.lean`:** a generic derived
  pasting law composing along the **non-exact** legs,
  `Stacks.Cohomology.BaseChange.derived_eq_derivedVPaste`, with the étale instance
  `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedVPaste_app`, whose only
  underived input is `smallEtaleBaseChangeAb_pasteDirectImage_app` below. What already existed,
  `Stacks.Cohomology.BaseChange.derived_paste` of `BaseChangeHigher/BasePasting.lean` and
  `Stacks.Cohomology.BaseChange.derived_eq_derivedPaste`, composes
  the comparison `pasteTrans F F' F'' G G' H H' τ₁ τ₂ : F ⋙ G ⋙ H ⟶ (G' ⋙ H') ⋙ F''` along
  `G, H` — the functors it requires to be **exact**, which on the étale side are the inverse
  images. The direct-image direction needs the composite taken in `F`, whose derived functors
  are compared not by `Stacks.Cohomology.BaseChange.exactDerivedCompIso` but by
  `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbCompIso` above.
* **Present but unconnected:** the passage between the injective-resolution convention
  `CategoryTheory.Functor.rightDerived n`, in which
  `Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral` and its input
  `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` are stated, and the
  cohomology of `rightDerivedFunctorPlus`. `Stacks.DerivedIndexing.rightDerivedIso` identifies
  the two conventions, and `Stacks.DerivedIndexing.rightDerivedPlusEdge` together with
  `Stacks.DerivedIndexing.edge_comp_rightDerivedIso` carries the composition comparison across;
  what is not recorded anywhere is that `rightDerivedPlusEdge` at
  `smallEtalePushforwardAb π` and `smallEtalePushforwardAb g` agrees with
  `smallEtaleRelativeLerayIsoOfIntegral π g`.

See the module docstring of `BaseChangeHigher/IntegralSurjectiveCover.lean`.

*No tag is placed.* [Stacks, Tag 0E46] is the derived statement, for ringed topoi and sheaves of
modules, and is already formalized as
`Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_comp`. What is proved here is
the underived étale abelian analogue, an input to the degreewise statement rather than the
statement of either tag.

## References

* [Stacks Project, Tag 0E46](https://stacks.math.columbia.edu/tag/0E46)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.BaseChange
open Stacks.Cohomology.DerivedBaseChangePasting

/-! ### The composition isomorphism for the bounded below derived direct images -/

section DerivedPushforwardComp

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The composition isomorphism `R(a ≫ b)_* ≅ Ra_* ⋙ Rb_*`** for direct image of abelian
sheaves on the small étale sites, on the bounded below derived categories.

This is the direct-image counterpart of
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackComp` of `BaseChangeHigher/BasePasting.lean`,
and the library had no form of it: the only composition comparison for direct image was the
underived `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso` and, degreewise and only for
an **integral** first leg, `Stacks.EtaleCohomology.smallEtaleRelativeLerayIsoOfIntegral`.

No hypothesis on `a` or `b` is needed. Direct image along `a` preserves injective objects
(`Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesInjectiveObjects`, it being the right
adjoint of the exact inverse image), which is exactly the hypothesis of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`; the underived comparison
`a_* ⋙ b_* ≅ (a ≫ b)_*` is carried across `rightDerivedFunctorPlus` by
`CategoryTheory.Functor.rightDerivedFunctorPlusNatIso`. -/
@[sga "4½ Th_finitude 1.3" "special case"]
public def smallEtaleDerivedPushforwardAbCompIso :
    (smallEtalePushforwardAb (a ≫ b)).rightDerivedFunctorPlus ≅
      (smallEtalePushforwardAb a).rightDerivedFunctorPlus ⋙
        (smallEtalePushforwardAb b).rightDerivedFunctorPlus :=
  letI : (smallEtalePushforwardAb a).PreservesInjectiveObjects :=
    smallEtalePushforwardAb_preservesInjectiveObjects a
  Functor.rightDerivedFunctorPlusNatIso (smallEtalePushforwardAbCompIso a b).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIso (smallEtalePushforwardAb a)
      (smallEtalePushforwardAb b)

end DerivedPushforwardComp

/-! ### The rearrangement of the three pentagons -/

/-- The cancellation that turns the three instances of the associativity pentagon of the inverse
image comparison into the vertical cocycle identity.

Stated on variables in a single category: the morphisms it is applied to are components of
comparisons of composite inverse images, and at those types the rearrangement is unreadable.
The three pentagons enter as `h₁`, `h₂`, `h₃`; the morphisms that have to be inverted are
isomorphisms, and are carried as such. -/
private theorem vPasteChase {𝒞 : Type*} [Category* 𝒞] {A B C D E F₀ G₀ H₀ : 𝒞}
    (x₁ : A ⟶ B) (x₂ : C ≅ B) (u₁ : D ≅ A) (y₁ : D ⟶ E) (y₂ : F₀ ≅ E) (v₁ : F₀ ⟶ G₀)
    (w₁ : H₀ ≅ G₀) (y₅ : H₀ ⟶ C) (z₁ : E ⟶ B) (z₂ : G₀ ⟶ B)
    (h₁ : u₁.hom ≫ x₁ = y₁ ≫ z₁) (h₂ : v₁ ≫ z₂ = y₂.hom ≫ z₁)
    (h₃ : w₁.hom ≫ z₂ = y₅ ≫ x₂.hom) :
    x₁ ≫ x₂.inv = u₁.inv ≫ y₁ ≫ y₂.inv ≫ v₁ ≫ w₁.inv ≫ y₅ := by
  have e₁ : x₁ = u₁.inv ≫ y₁ ≫ z₁ := by
    rw [← h₁, ← Category.assoc, u₁.inv_hom_id, Category.id_comp]
  have e₂ : z₁ = y₂.inv ≫ v₁ ≫ z₂ := by
    rw [h₂, ← Category.assoc, y₂.inv_hom_id, Category.id_comp]
  have e₃ : z₂ ≫ x₂.inv = w₁.inv ≫ y₅ := by
    rw [Iso.comp_inv_eq, Category.assoc, ← h₃, Iso.inv_hom_id_assoc]
  rw [e₁, e₂]
  simp only [Category.assoc, e₃]

/-! ### The vertical cocycle of the inverse image comparison squares -/

section Paste

variable {S T X' Y T' Y' : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (π : T' ⟶ T) (π' : Y' ⟶ Y) (e' : Y' ⟶ T')

/-- **The inverse image comparisons of two commutative squares sharing a vertical edge paste**,
as an identity of 2-squares. It is the associativity pentagon of the inverse image comparison,
used for the three chains `Y' → Y → X' → S`, `Y' → Y → T → S` and `Y' → T' → T → S`.

This is the vertical counterpart of `pullbackComparison_hComp` of
`BaseChangeHigher/BasePasting.lean`. -/
private theorem pullbackComparison_vComp
    (G : T' ⟶ S) (hG : G = π ≫ g) (H : Y' ⟶ X') (hH : H = π' ≫ h)
    (P₁ : Y ⟶ S) (hP₁h : P₁ = h ≫ f') (hP₁e : P₁ = e ≫ g)
    (P₂ : Y' ⟶ T) (hP₂π' : P₂ = π' ≫ e) (hP₂e' : P₂ = e' ≫ π)
    (P : Y' ⟶ S) (hPH : P = H ≫ f') (hPG : P = e' ≫ G)
    (hPπ' : P = π' ≫ P₁) (hPP₂ : P = P₂ ≫ g) :
    TwoSquare.mk (smallEtalePullbackAb f') (smallEtalePullbackAb G)
        (smallEtalePullbackAb H) (smallEtalePullbackAb e')
        ((smallEtalePullbackAbCompIso' H f' P hPH).hom ≫
          (smallEtalePullbackAbCompIso' e' G P hPG).inv) =
      TwoSquare.whiskerRight
        (TwoSquare.whiskerLeft
          (TwoSquare.vComp
            (TwoSquare.mk (smallEtalePullbackAb f') (smallEtalePullbackAb g)
              (smallEtalePullbackAb h) (smallEtalePullbackAb e)
              ((smallEtalePullbackAbCompIso' h f' P₁ hP₁h).hom ≫
                (smallEtalePullbackAbCompIso' e g P₁ hP₁e).inv))
            (TwoSquare.mk (smallEtalePullbackAb e) (smallEtalePullbackAb π)
              (smallEtalePullbackAb π') (smallEtalePullbackAb e')
              ((smallEtalePullbackAbCompIso' π' e P₂ hP₂π').hom ≫
                (smallEtalePullbackAbCompIso' e' π P₂ hP₂e').inv)))
          (smallEtalePullbackAbCompIso' π g G hG).hom)
        (smallEtalePullbackAbCompIso' π' h H hH).inv := by
  refine NatTrans.ext <| funext fun M => ?_
  have hA1 := congr_app (congrArg Iso.hom
    (smallEtalePullbackAbCompIso'_assoc f' h π' P₁ hP₁h H hH P hPH hPπ')) M
  have hA2 := congr_app (congrArg Iso.hom
    (smallEtalePullbackAbCompIso'_assoc g e π' P₁ hP₁e P₂ hP₂π' P hPP₂ hPπ')) M
  have hA3 := congr_app (congrArg Iso.hom
    (smallEtalePullbackAbCompIso'_assoc g π e' G hG P₂ hP₂e' P hPP₂ hPG)) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp] at hA1 hA2 hA3
  have hM := vPasteChase
    ((smallEtalePullbackAbCompIso' H f' P hPH).hom.app M)
    ((smallEtalePullbackAbCompIso' e' G P hPG).app M)
    ((smallEtalePullbackAbCompIso' π' h H hH).app ((smallEtalePullbackAb f').obj M))
    ((smallEtalePullbackAb π').map ((smallEtalePullbackAbCompIso' h f' P₁ hP₁h).hom.app M))
    ((smallEtalePullbackAb π').mapIso ((smallEtalePullbackAbCompIso' e g P₁ hP₁e).app M))
    ((smallEtalePullbackAbCompIso' π' e P₂ hP₂π').hom.app ((smallEtalePullbackAb g).obj M))
    ((smallEtalePullbackAbCompIso' e' π P₂ hP₂e').app ((smallEtalePullbackAb g).obj M))
    ((smallEtalePullbackAb e').map ((smallEtalePullbackAbCompIso' π g G hG).hom.app M))
    ((smallEtalePullbackAbCompIso' π' P₁ P hPπ').hom.app M)
    ((smallEtalePullbackAbCompIso' P₂ g P hPP₂).hom.app M)
    hA1 hA2 hA3
  simpa [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight, Functor.map_comp,
    Category.assoc] using hM

/-! ### The pasting law -/

/-- **The pasting law for the underived base change map of abelian small étale sheaves, along
the direct image legs.** For two commutative squares of schemes sharing a vertical edge, the
base change map of the outer rectangle is the composite of the base change maps of the two
squares, read through the comparisons of the direct images along the two composite horizontal
legs `G = π ≫ g` and `H = π' ≫ h`.

This is the étale abelian, underived form of [Stacks, Tag 0E46]. The hypotheses are the
commutativity of the two squares and nothing else. -/
public theorem smallEtaleBaseChangeAb_pasteDirectImage
    (w : h ≫ f' = e ≫ g) (w' : π' ≫ e = e' ≫ π)
    (G : T' ⟶ S) (hG : G = π ≫ g) (H : Y' ⟶ X') (hH : H = π' ≫ h)
    (wo : H ≫ f' = e' ≫ G) :
    TwoSquare.mk (smallEtalePushforwardAb G) (smallEtalePullbackAb e')
        (smallEtalePullbackAb f') (smallEtalePushforwardAb H)
        (smallEtaleBaseChangeAb f' G H e' wo) =
      TwoSquare.whiskerBottom
        (TwoSquare.whiskerTop
          (TwoSquare.hComp
            (TwoSquare.mk (smallEtalePushforwardAb π) (smallEtalePullbackAb e')
              (smallEtalePullbackAb e) (smallEtalePushforwardAb π')
              (smallEtaleBaseChangeAb e π π' e' w'))
            (TwoSquare.mk (smallEtalePushforwardAb g) (smallEtalePullbackAb e)
              (smallEtalePullbackAb f') (smallEtalePushforwardAb h)
              (smallEtaleBaseChangeAb f' g h e w)))
          (smallEtalePushforwardAbCompIso' π g G hG).inv)
        (smallEtalePushforwardAbCompIso' π' h H hH).hom := by
  have hPπ' : H ≫ f' = π' ≫ (h ≫ f') := by rw [hH, Category.assoc]
  have hPP₂ : H ≫ f' = (π' ≫ e) ≫ g := by
    rw [wo, hG, ← Category.assoc, ← w']
  have hdL : conjugateEquiv (smallEtaleAdjunctionAb G)
        ((smallEtaleAdjunctionAb g).comp (smallEtaleAdjunctionAb π))
        (smallEtalePullbackAbCompIso' π g G hG).hom =
      (smallEtalePushforwardAbCompIso' π g G hG).inv := by
    rw [smallEtalePullbackAbCompIso'_def]
    exact conjugateEquiv_leftAdjointCompIso_hom (smallEtaleAdjunctionAb g)
      (smallEtaleAdjunctionAb π) (smallEtaleAdjunctionAb G)
      (smallEtalePushforwardAbCompIso' π g G hG)
  have hdR : conjugateEquiv ((smallEtaleAdjunctionAb h).comp (smallEtaleAdjunctionAb π'))
        (smallEtaleAdjunctionAb H)
        (smallEtalePullbackAbCompIso' π' h H hH).inv =
      (smallEtalePushforwardAbCompIso' π' h H hH).hom := by
    rw [smallEtalePullbackAbCompIso'_def]
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv (smallEtaleAdjunctionAb h)
      (smallEtaleAdjunctionAb π') (smallEtaleAdjunctionAb H)
      (smallEtalePushforwardAbCompIso' π' h H hH)
  have hSo := pullbackComparison_vComp f' g h e π π' e' G hG H hH (h ≫ f') rfl w
    (π' ≫ e) rfl w' (H ≫ f') rfl wo hPπ' hPP₂
  have hmate := mate_twoSquare_paste (smallEtaleAdjunctionAb g) (smallEtaleAdjunctionAb h)
    (smallEtaleAdjunctionAb π) (smallEtaleAdjunctionAb π')
    (smallEtaleAdjunctionAb G) (smallEtaleAdjunctionAb H)
    _ _ _ _ _ _ _ hSo hdL hdR
  rw [smallEtaleBaseChangeAb_eq_mateEquiv f' G H e' wo (H ≫ f') rfl wo,
    smallEtaleBaseChangeAb_eq_mateEquiv f' g h e w (h ≫ f') rfl w,
    smallEtaleBaseChangeAb_eq_mateEquiv e π π' e' w' (π' ≫ e) rfl w']
  exact hmate

/-- **The pasting law along the direct image legs, evaluated at an abelian sheaf.** -/
public theorem smallEtaleBaseChangeAb_pasteDirectImage_app
    (w : h ≫ f' = e ≫ g) (w' : π' ≫ e = e' ≫ π)
    (G : T' ⟶ S) (hG : G = π ≫ g) (H : Y' ⟶ X') (hH : H = π' ≫ h)
    (wo : H ≫ f' = e' ≫ G) (F : Sheaf (smallEtaleTopology T') Ab.{u + 1}) :
    (smallEtaleBaseChangeAb f' G H e' wo).app F =
      (smallEtalePullbackAb f').map
          ((smallEtalePushforwardAbCompIso' π g G hG).inv.app F) ≫
        (smallEtaleBaseChangeAb f' g h e w).app ((smallEtalePushforwardAb π).obj F) ≫
          (smallEtalePushforwardAb h).map
              ((smallEtaleBaseChangeAb e π π' e' w').app F) ≫
            (smallEtalePushforwardAbCompIso' π' h H hH).hom.app
              ((smallEtalePullbackAb e').obj F) := by
  have hpaste := congr_app
    (smallEtaleBaseChangeAb_pasteDirectImage f' g h e π π' e' w w' G hG H hH wo) F
  simpa [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    Category.assoc] using hpaste

/-- **The pasting law along the direct image legs, with the two composite legs written out.**
For two commutative squares of schemes sharing a vertical edge, the base change map of the outer
rectangle at an abelian sheaf is the composite of the base change maps of the two squares, read
through `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso` at `π ≫ g` and at `π' ≫ h`. -/
public theorem smallEtaleBaseChangeAb_pasteDirectImage_app'
    (w : h ≫ f' = e ≫ g) (w' : π' ≫ e = e' ≫ π)
    (wo : (π' ≫ h) ≫ f' = e' ≫ (π ≫ g))
    (F : Sheaf (smallEtaleTopology T') Ab.{u + 1}) :
    (smallEtaleBaseChangeAb f' (π ≫ g) (π' ≫ h) e' wo).app F =
      (smallEtalePullbackAb f').map ((smallEtalePushforwardAbCompIso π g).inv.app F) ≫
        (smallEtaleBaseChangeAb f' g h e w).app ((smallEtalePushforwardAb π).obj F) ≫
          (smallEtalePushforwardAb h).map
              ((smallEtaleBaseChangeAb e π π' e' w').app F) ≫
            (smallEtalePushforwardAbCompIso π' h).hom.app
              ((smallEtalePullbackAb e').obj F) := by
  rw [← smallEtalePushforwardAbCompIso'_rfl π g, ← smallEtalePushforwardAbCompIso'_rfl π' h]
  exact smallEtaleBaseChangeAb_pasteDirectImage_app f' g h e π π' e' w w' (π ≫ g) rfl
    (π' ≫ h) rfl wo F

end Paste

end Stacks.EtaleCohomology

end
