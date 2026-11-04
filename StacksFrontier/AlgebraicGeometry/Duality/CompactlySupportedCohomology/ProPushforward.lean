module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroFunctor

/-!
# Pushforward along a left adjoint on pro-objects

Let `F : 𝒟 ⥤ 𝒟'` be a functor with a right adjoint `G`. Applying `F` termwise to an inverse
sequence sends pro-objects of `𝒟` to pro-objects of `𝒟'`, and the resulting functor
`Pro-𝒟 ⥤ Pro-𝒟'` is described on functors of points by precomposition with `G`:

`Mor(Pro F (M), L) = colim_n Mor(F M_n, L) = colim_n Mor(M_n, G L) = Mor(M, G L)`.

For the duality chapter `𝒟 = D^b_{Coh}(𝒪_{X'})`, `𝒟' = D^b_{Coh}(𝒪_X)`, `F = Rf_*` for a proper
morphism `f` and `G = f^!`; the functor built here is the one written `Rf_*` again when it is
applied to the pro-objects `Rj_! K` of [Stacks, Tag 0G4N].

## Main definitions

* `CategoryTheory.ProSeq.pushforward`: the functor `Pro-𝒟 ⥤ Pro-𝒟'` induced by `F`.

## Main results

* `CategoryTheory.ProSeq.points_pushforward_obj`: its functor of points is `G ⋙ (-)`.
* `CategoryTheory.ProSeq.pushforwardOfIso`: on the pro-object of an inverse sequence it is the
  pro-object of the termwise image sequence, so it is the termwise pushforward.
* `CategoryTheory.ProSeq.pushforwardHomConstEquiv`: morphisms into a constant pro-object are the
  morphisms of the source into the constant pro-object at `G L`.
* `CategoryTheory.ProSeq.liftRightOpIso`: an isomorphism of families of functors of points is an
  isomorphism of the functors into `Pro-𝒟` they define.
* `CategoryTheory.ProSeq.pushforwardIso`: the pushforward depends on the adjunction only through
  the right adjoint.
* `CategoryTheory.ProSeq.pushforward_comp`: pushing forward twice is pushing forward along the
  composite.

## Implementation notes

The functor of points of a pro-object is a colimit taken in a functor category, and precomposition
with `G` preserves those colimits, so the identification above is the image of the colimit under
`CategoryTheory.Adjunction.compCoyonedaIso`. Nothing here needs `F` or `G` to be triangulated, nor
the index category to be anything other than the lifted copy of `ℕᵒᵖ` used throughout.

## References

* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u' w₁ w₂

namespace CategoryTheory

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒟' : Type u'} [Category.{v} 𝒟']

/-- Precomposition with `G`, as a functor on the categories in which the functors of points of
pro-objects live. -/
public abbrev proPointsWhisker (G : 𝒟' ⥤ 𝒟) : (𝒟 ⥤ Type v) ⥤ (𝒟' ⥤ Type v) :=
  (Functor.whiskeringLeft 𝒟' 𝒟 (Type v)).obj G

/-- For an adjunction `F ⊣ G`, the functor of points of the termwise image `(F M_n)` of an
inverse sequence is the functor of points of `(M_n)` precomposed with `G`. This is the adjunction
`Mor(F M_n, L) = Mor(M_n, G L)` passed to the colimit over `n`. -/
public def proPointsCompIso {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G) (M : ℕᵒᵖ ⥤ 𝒟) :
    G ⋙ Pro.coyonedaColim (Pro.liftedInverseSequence M) ≅
      Pro.coyonedaColim (Pro.liftedInverseSequence (M ⋙ F)) :=
  preservesColimitIso (proPointsWhisker G)
      ((Pro.liftedInverseSequence M).op ⋙ coyoneda) ≪≫
    HasColimit.isoOfNatIso
      (Functor.isoWhiskerLeft (Pro.liftedInverseSequence M).op adj.compCoyonedaIso).symm

/-- Precomposing the functor of points of a pro-object with the right adjoint `G` again gives the
functor of points of a pro-object, namely of the termwise image sequence. -/
public lemma isSequentialProObject_comp {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G)
    {A : 𝒟 ⥤ Type v} (hA : IsSequentialProObject 𝒟 A) :
    IsSequentialProObject 𝒟' (G ⋙ A) := by
  obtain ⟨M, ⟨e⟩⟩ := hA
  exact ⟨M ⋙ F, ⟨Functor.isoWhiskerLeft G e ≪≫ proPointsCompIso adj M⟩⟩

namespace ProSeq

/-- **Pushforward of pro-objects along a left adjoint.** For `F ⊣ G` the termwise application of
`F` to an inverse sequence, as a functor `Pro-𝒟 ⥤ Pro-𝒟'`. It is defined through functors of
points, where it is precomposition with `G`; that this is the termwise image is
`CategoryTheory.ProSeq.pushforwardOfIso`. -/
public def pushforward {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G) : ProSeq 𝒟 ⥤ ProSeq 𝒟' :=
  (ObjectProperty.lift (IsSequentialProObject 𝒟')
    ((IsSequentialProObject 𝒟).ι ⋙ proPointsWhisker G)
    (fun P => isSequentialProObject_comp adj P.property)).op

/-- The functor of points of a pushed-forward pro-object is the functor of points precomposed
with the right adjoint: `Mor(Pro F P, L) = Mor(P, G L)`. -/
public lemma points_pushforward_obj {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G) (P : ProSeq 𝒟) :
    ((pushforward adj).obj P).points = G ⋙ P.points :=
  rfl

/-- The pushforward of the pro-object of an inverse sequence is the pro-object of the termwise
image sequence: the construction is the termwise pushforward of the source. -/
public def pushforwardOfIso {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G) (M : ℕᵒᵖ ⥤ 𝒟) :
    (pushforward adj).obj (of M) ≅ of (M ⋙ F) :=
  (ObjectProperty.isoMk _ (proPointsCompIso adj M).symm).op

/-- Morphisms from a pushed-forward pro-object into a constant pro-object are the morphisms of
the original pro-object into the constant pro-object at `G L`. This is the adjunction `F ⊣ G`
extended to pro-objects. -/
public def pushforwardHomConstEquiv {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟} (adj : F ⊣ G) (P : ProSeq 𝒟)
    (L : 𝒟') : ((pushforward adj).obj P ⟶ const.obj L) ≃ (P ⟶ const.obj (G.obj L)) :=
  (homConstEquiv _ L).trans (homConstEquiv P (G.obj L)).symm

/-- An isomorphism of families of functors of points gives one of the families of pro-objects
they define. -/
public def liftIso {E : Type w₁} [Category.{w₂} E] {Φ Ψ : E ⥤ (𝒟 ⥤ Type v)}
    (hΦ : ∀ X, IsSequentialProObject 𝒟 (Φ.obj X))
    (hΨ : ∀ X, IsSequentialProObject 𝒟 (Ψ.obj X)) (e : Φ ≅ Ψ) :
    ObjectProperty.lift (IsSequentialProObject 𝒟) Φ hΦ ≅
      ObjectProperty.lift (IsSequentialProObject 𝒟) Ψ hΨ :=
  NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (e.app X))
    (fun φ => ObjectProperty.hom_ext _ (e.hom.naturality φ))

/-- The pushforward functor depends on the adjunction only through the right adjoint: an
isomorphism `G ≅ G'` of right adjoints induces one of the pushforwards. -/
public def pushforwardIso {F F' : 𝒟 ⥤ 𝒟'} {G G' : 𝒟' ⥤ 𝒟} (adj : F ⊣ G) (adj' : F' ⊣ G')
    (e : G ≅ G') : pushforward adj ≅ pushforward adj' :=
  NatIso.op (liftIso _ _ (Functor.isoWhiskerLeft (IsSequentialProObject 𝒟).ι
    ((Functor.whiskeringLeft 𝒟' 𝒟 (Type v)).mapIso e.symm)))

/-- Pushing forward along `F` and then along `H` is pushing forward along `F ⋙ H`: on functors of
points both are precomposition with the composite right adjoint. -/
public lemma pushforward_comp {𝒟'' : Type w₁} [Category.{v} 𝒟''] {F : 𝒟 ⥤ 𝒟'} {G : 𝒟' ⥤ 𝒟}
    (adj : F ⊣ G) {H : 𝒟' ⥤ 𝒟''} {I : 𝒟'' ⥤ 𝒟'} (adj' : H ⊣ I) :
    pushforward adj ⋙ pushforward adj' = pushforward (adj.comp adj') :=
  rfl

/-- Two functors into `Pro-𝒟` built from families of functors of points are isomorphic as soon as
those families are: a pro-object *is* its functor of points, so an isomorphism of the latter,
natural in the parameter, is an isomorphism of the former. -/
public def liftRightOpIso {E : Type w₁} [Category.{w₂} E] {Φ Ψ : Eᵒᵖ ⥤ (𝒟 ⥤ Type v)}
    (hΦ : ∀ X, IsSequentialProObject 𝒟 (Φ.obj X))
    (hΨ : ∀ X, IsSequentialProObject 𝒟 (Ψ.obj X)) (e : Ψ ≅ Φ) :
    (ObjectProperty.lift (IsSequentialProObject 𝒟) Φ hΦ).rightOp ≅
      (ObjectProperty.lift (IsSequentialProObject 𝒟) Ψ hΨ).rightOp :=
  NatIso.ofComponents (fun X => (ObjectProperty.isoMk _ (e.app (op X))).op)
    (fun φ => by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      exact (e.hom.naturality φ.op).symm)

end ProSeq

end CategoryTheory

end
