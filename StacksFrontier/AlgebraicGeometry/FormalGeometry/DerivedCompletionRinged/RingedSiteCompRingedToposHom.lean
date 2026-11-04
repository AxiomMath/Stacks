module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafSiteTopos
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposTwoIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafToposComp
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RelocalizationDirectImage

/-!
# The passage to ringed topoi carries a composite to a composite

Let `f : (Sh(𝒞), 𝒪_X) ⟶ (Sh(𝒟), 𝒪_Y)` and `g : (Sh(𝒟), 𝒪_Y) ⟶ (Sh(ℰ), 𝒪_Z)` be morphisms of
ringed sites. [Stacks, Tag 01D3] part (2) reads each as a morphism of ringed topoi, and part (3)
composes morphisms of ringed topoi; this file compares the two ways of combining those operations.

## It is a 2-isomorphism, not an equality

The expected statement, `(f.comp g).ringedToposHom = g.ringedToposHom.comp f.ringedToposHom`, is
**not provable**, and the obstruction is in the data rather than in the proof.
`MorphismOfTopoi` stores the inverse image and the adjunction as *data*, and the inverse image of
a morphism of sites is `CategoryTheory.Functor.sheafPullback`, which is
`CategoryTheory.Functor.leftAdjoint` of the pushforward — a `Classical.choice`. So the inverse
image of the composite is *the* chosen left adjoint of the composite pushforward, while the
composite of the inverse images is the composite of two separately chosen left adjoints. Those
two functors are canonically isomorphic and are not the same term;
`CategoryTheory.Functor.sheafPullback` has no composition law in Mathlib or here, and none can be
proved.

What *is* an equality is the direct image: `CategoryTheory.Functor.sheafPushforwardContinuousComp`
is literally `CategoryTheory.Iso.refl`, so the pushforward of the composite is the composite of
the pushforwards on the nose (`AlgebraicGeometry.RingedSite.Hom.pushforward_comp_ringedToposHom`).
And a 2-isomorphism of morphisms of ringed topoi in the sense of [Stacks, Tag 04IC] is exactly an
isomorphism of the direct images compatible with the structure maps — it asks nothing of the
inverse images. So the correct statement is a
`AlgebraicGeometry.RingedToposHom.TwoIso` whose underlying isomorphism is the identity, and whose
whole content is the agreement of the two structure maps, which is
`AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom_comp`.

A square of ringed topoi *commutes*, in the sense Stacks uses, when its two composites are
2-isomorphic, and the ideal sheaf `f^{-1}ℐ · 𝒪_X` is 2-isomorphism invariant, by
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealSheaf_eq`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.pushforward_comp_ringedToposHom`: the direct images agree
  strictly.
* `AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom_comp`: the structure maps agree,
  on underlying sheaves of sets.
* `AlgebraicGeometry.RingedSite.Hom.compRingedToposTwoIso`: **the passage of [Stacks, Tag 01D3]
  part (2) carries the composition of morphisms of ringed sites to the composition of morphisms
  of ringed topoi, up to a 2-isomorphism.** Mind the argument orders:
  `AlgebraicGeometry.RingedSite.Hom.comp` is inner-first and
  `AlgebraicGeometry.RingedToposHom.comp` is outer-first.
* `AlgebraicGeometry.RingedSite.inverseImageIdealSheaf_comp`: **the composition law for
  `ℐ ↦ f^{-1}ℐ · 𝒪_X` at morphisms of ringed sites**, with no hypothesis on `ℐ` and none on
  either morphism. It is the topos-level composition law
  `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp` transported across the
  agreement of the two constructions
  (`AlgebraicGeometry.RingedSite.inverseImageIdealSheaf_ringedToposHom`) using the 2-isomorphism
  above and its invariance.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

variable {X Y Z : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)

/-- **The direct image of a composite of morphisms of ringed sites, read as a morphism of ringed
topoi, is the composite of the direct images** — strictly, not up to a comparison.

`CategoryTheory.Functor.sheafPushforwardContinuousComp` is `CategoryTheory.Iso.refl`, and
`CategoryTheory.Functor.IsContinuous` is a proposition, so the two restriction functors are the
same functor. This is the half of the passage that *is* an equality; the inverse images are only
isomorphic, which is why the comparison below is a 2-isomorphism. -/
theorem Hom.pushforward_comp_ringedToposHom :
    (f.comp g).ringedToposHom.toToposHom.pushforward =
      (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := ringedTopos Y)
        g.ringedToposHom f.ringedToposHom).toToposHom.pushforward :=
  rfl

/-- **The structure map of a composite of morphisms of ringed sites, read as a morphism of ringed
topoi, is the structure map of the composite of the morphisms of ringed topoi**, on underlying
sheaves of sets.

Both sides unwind to `g^♯` followed by the direct image under `g` of `f^♯`: on the left by
`AlgebraicGeometry.RingedSite.Hom.comp_fsharp`, whose third factor is the comparison of
successive restrictions and so the identity, and on the right by
`AlgebraicGeometry.RingedSite.forgetFSharp_comp_ringedToposHom`. -/
theorem Hom.forgetFSharp_ringedToposHom_comp :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (f.comp g).ringedToposHom =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := ringedTopos Y)
          g.ringedToposHom f.ringedToposHom) := by
  rw [Hom.forgetFSharp_ringedToposHom, forgetFSharp_comp_ringedToposHom g f, Hom.comp_fsharp]
  rfl

/-- **[Stacks, Tag 01D3] part (2) carries composition to composition, up to a 2-isomorphism.**
The morphism of ringed topoi attached to a composite of morphisms of ringed sites is
2-isomorphic, in the sense of [Stacks, Tag 04IC], to the composite of the attached morphisms of
ringed topoi.

The underlying isomorphism of direct images is the identity, by
`AlgebraicGeometry.RingedSite.Hom.pushforward_comp_ringedToposHom`, and the compatibility with
the structure maps is
`AlgebraicGeometry.RingedSite.Hom.forgetFSharp_ringedToposHom_comp`. It is not an equality of
morphisms of ringed topoi, and cannot be; see the module documentation.

Mind the argument orders: `AlgebraicGeometry.RingedSite.Hom.comp` is inner-first — `f.comp g` is
`f` followed by `g` — while `AlgebraicGeometry.RingedToposHom.comp` is outer-first. -/
def Hom.compRingedToposTwoIso :
    AlgebraicGeometry.RingedToposHom.TwoIso.{u, u, u, u, u, u}
      (A := ringedTopos X) (B := ringedTopos Z)
      (f.comp g).ringedToposHom
      (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := ringedTopos Y)
        g.ringedToposHom f.ringedToposHom) where
  e := eqToIso (Hom.pushforward_comp_ringedToposHom f g)
  commutes := (Category.comp_id _).trans (Hom.forgetFSharp_ringedToposHom_comp f g)

section Ideal

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O))))

/-- **The construction `ℐ ↦ f^{-1}ℐ · 𝒪_X` of Section 52.7 is functorial at morphisms of ringed
sites**: forming the ideal sheaf of `g` and then that of `f` gives the ideal sheaf of the
composite `g ∘ f`. No hypothesis on `ℐ`, none on `f` and none on `g`.

This is the ringed-sites form of
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp`, and it is obtained from it: the
two constructions of the ideal sheaf agree
(`AlgebraicGeometry.RingedSite.inverseImageIdealSheaf_ringedToposHom`), so the law can be read at
the level of ringed topoi, where the composite of the two attached morphisms is only
2-isomorphic to the attached morphism of the composite
(`AlgebraicGeometry.RingedSite.Hom.compRingedToposTwoIso`) — and that is enough, because the
ideal sheaf is 2-isomorphism invariant
(`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealSheaf_eq`).

It is what matches the sheaves of ideals along the square of [Stacks, Tag 03CR] in the reduction
of [Stacks, Tag 0A0G] from a morphism of ringed topoi to a morphism of ringed sites: three of the
square's arrows are presented by morphisms of ringed *sites*, and their composites have to be
recognised as the ideal sheaf of a single morphism. -/
theorem inverseImageIdealSheaf_comp :
    inverseImageIdealSheaf f (inverseImageIdealSheaf g I) =
      inverseImageIdealSheaf (f.comp g) I := by
  rw [← inverseImageIdealSheaf_ringedToposHom g I,
    ← inverseImageIdealSheaf_ringedToposHom f
      (AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf.{u} g.ringedToposHom I),
    ← inverseImageIdealSheaf_ringedToposHom (f.comp g) I,
    AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp
      g.ringedToposHom f.ringedToposHom I]
  exact (AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealSheaf_eq
    (Hom.compRingedToposTwoIso f g) I).symm

end Ideal

end AlgebraicGeometry.RingedSite

end
