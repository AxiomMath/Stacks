module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforward

/-!
# Compatibility of extension by zero with proper pushforward

Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let `V ⊆ Y` be an open subscheme and
let `U = f^{-1}(V)`, so that there is a commutative square with open immersions `j : U ⟶ X` and
`j' : V ⟶ Y` and the induced `g : U ⟶ V`. The extension-by-zero functors of [Stacks, Tag 0G4N]
and the proper pushforwards then satisfy

`Rj'_! ∘ Rg_* ≅ Rf_* ∘ Rj_!`

as functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_Y)`. This is [Stacks, Tag 0G4W]. Taking `g` to be
the identity gives the compatibility of `Rj_!` with a compactification, [Stacks, Tag 0G4X].

The isomorphism is the one the source's second proof constructs: a chain of identifications of
`Hom`-sets out of the two pro-objects, natural in both variables. Spelled out, with `L` an object
of `D^b_{Coh}(𝒪_Y)`,

`Hom(Rj'_! Rg_* K, L) = Hom_V(Rg_* K, L|_V) = Hom_U(K, g^!(L|_V))`
`= Hom_U(K, (f^! L)|_U) = Hom(Rj_! K, f^! L) = Hom(Rf_* Rj_! K, L)`,

using the adjointness of `Rj_!` to restriction twice, the adjointness of `Rg_*` to `g^!` and of
`Rf_*` to `f^!`, and the compatibility `g^!(L|_V) = (f^! L)|_U`, which follows from the
composition isomorphism for upper shriek, [Stacks, Tag 0ATX], and `j^! = j^*` for an open
immersion, [Stacks, Tag 0AU0]. Since both sides are pro-objects and a pro-object is its functor
of points, this chain *is* the asserted isomorphism.

## Main definitions

* `CategoryTheory.baseChangeShriekPoints`: the chain of identifications above, as an isomorphism
  of functors of points.
* `CategoryTheory.baseChangeShriek`: **Stacks 0G4W**, the resulting isomorphism
  `Rj'_! ∘ Rg_* ≅ Rf_* ∘ Rj_!`.
* `CategoryTheory.compactificationShriek`: **Stacks 0G4X**, the case `g = id`, giving
  `Rj_! ≅ Rf_* ∘ R(j')_!` for a compactification.

## Implementation notes

**What is assumed.** Everything geometric enters as data, in the shape the source uses it:

* the restriction functors `j^*` and `(j')^*` with their Deligne system assignments, which is
  `CategoryTheory.DeligneSystemAssignment`, carrying the identification of [Stacks, Tag 0G2H];
* the adjunctions `Rg_* ⊣ g^!` and `Rf_* ⊣ f^!`, which hold because `f` and `g` are proper,
  `f^!` being in that case the right adjoint of `Rf_*`;
* the compatibility `(j')^* ∘ g^! ≅ f^! ∘ j^*`, which follows from the composition isomorphism
  for upper shriek, [Stacks, Tag 0ATX], together with `j^! = j^*` for an open immersion,
  [Stacks, Tag 0AU0].

What is proved is that these determine the isomorphism of the tag, and the proof is the source's.
No triangulated structure is needed, and the statement is universe-polymorphic in all four
categories.

## References

* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 0G4X](https://stacks.math.columbia.edu/tag/0G4X)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒞' : Type u₂} [Category.{v} 𝒞']
  {𝒟 : Type u₃} [Category.{v} 𝒟] {𝒟' : Type u₄} [Category.{v} 𝒟']
  {jU : 𝒟 ⥤ 𝒞} (A : DeligneSystemAssignment jU)
  {jV : 𝒟' ⥤ 𝒞'} (A' : DeligneSystemAssignment jV)
  {gstar : 𝒞 ⥤ 𝒞'} {gshriek : 𝒞' ⥤ 𝒞} (adjg : gstar ⊣ gshriek)
  {fstar : 𝒟 ⥤ 𝒟'} {fshriek : 𝒟' ⥤ 𝒟} (adjf : fstar ⊣ fshriek)
  (κ : jV ⋙ gshriek ≅ fshriek ⋙ jU)

/-- The chain of identifications of the source's second proof, as an isomorphism of the families
of functors of points, natural in the object `K` of `D^b_{Coh}(𝒪_U)`:

`Hom_U(K, (f^! -)|_U) = Hom_U(K, g^!((-)|_V)) = Hom_V(Rg_* K, (-)|_V)`.

The left-hand side is the functor of points of `Rf_* Rj_! K` and the right-hand side is that of
`Rj'_! Rg_* K`. The first identification is the compatibility `κ`, the second is the adjunction
`Rg_* ⊣ g^!` in the form `CategoryTheory.Adjunction.compCoyonedaIso`. -/
public def baseChangeShriekPoints :
    (coyoneda ⋙ proPointsWhisker jU) ⋙ proPointsWhisker fshriek ≅
      gstar.op ⋙ coyoneda ⋙ proPointsWhisker jV :=
  Functor.isoWhiskerLeft coyoneda
      ((Functor.whiskeringLeft 𝒟' 𝒞 (Type v)).mapIso κ.symm) ≪≫
    Functor.isoWhiskerRight adjg.compCoyonedaIso.symm (proPointsWhisker jV)

/-- **Stacks Project, Tag 0G4W.** Let `f : X ⟶ Y` be a proper morphism of Noetherian schemes, let
`V ⊆ Y` be open and let `U = f^{-1}(V)`, with `j : U ⟶ X`, `j' : V ⟶ Y` the open immersions and
`g : U ⟶ V` the induced morphism. There is a canonical isomorphism

`Rj'_! ∘ Rg_* ≅ Rf_* ∘ Rj_!`

of functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_Y)`.

The isomorphism is constructed, not merely asserted: on functors of points it is the chain of
adjunctions `CategoryTheory.baseChangeShriekPoints`, which is the source's second proof. -/
@[stacks 0G4W "the Deligne system assignments, the adjunctions Rg_* ⊣ g^! and Rf_* ⊣ f^!, \
and the compatibility (j')^* ∘ g^! ≅ f^! ∘ j^* coming from Tags 0ATX and 0AU0, supplied as data"]
public def baseChangeShriek :
    gstar ⋙ extensionByZero jV A' ≅ extensionByZero jU A ⋙ ProSeq.pushforward adjf :=
  ProSeq.liftRightOpIso
    (Φ := gstar.op ⋙ coyoneda ⋙ proPointsWhisker jV)
    (Ψ := (coyoneda ⋙ proPointsWhisker jU) ⋙ proPointsWhisker fshriek)
    (fun K => ⟨A'.system (gstar.obj K.unop), ⟨A'.homIso (gstar.obj K.unop)⟩⟩)
    (fun K => isSequentialProObject_comp adjf ⟨A.system K.unop, ⟨A.homIso K.unop⟩⟩)
    (baseChangeShriekPoints adjg κ)

/-- **Stacks Project, Tag 0G4X.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes and
let `j' : U ⟶ X'` be a compactification of `U` over `X`, with structure morphism `f : X' ⟶ X`.
There is a canonical isomorphism

`Rj_! ≅ Rf_* ∘ R(j')_!`

of functors `D^b_{Coh}(𝒪_U) ⥤ Pro-D^b_{Coh}(𝒪_X)`.

This is `CategoryTheory.baseChangeShriek` for the open `j(U) ⊆ X` and the identity `U ⟶ U`: the
compatibility it needs becomes `j^* ≅ f^! ⋙ (j')^*`, which holds for a compactification because
`f^!` is local on the source and `f ∘ j' = j` is an open immersion. -/
@[stacks 0G4X "the Deligne system assignments, the adjunction Rf_* ⊣ f^!, and the compatibility \
j^* ≅ f^! ∘ (j')^* coming from Tags 0ATX and 0AU0, supplied as data"]
public def compactificationShriek {jX' : 𝒟 ⥤ 𝒞} (A₁ : DeligneSystemAssignment jX')
    {jX : 𝒟' ⥤ 𝒞} (A₂ : DeligneSystemAssignment jX)
    (κ' : jX ≅ fshriek ⋙ jX') :
    extensionByZero jX A₂ ≅ extensionByZero jX' A₁ ⋙ ProSeq.pushforward adjf :=
  (Functor.leftUnitor _).symm ≪≫
    baseChangeShriek A₁ A₂ Adjunction.id adjf ((Functor.rightUnitor _) ≪≫ κ')

end CategoryTheory

end
