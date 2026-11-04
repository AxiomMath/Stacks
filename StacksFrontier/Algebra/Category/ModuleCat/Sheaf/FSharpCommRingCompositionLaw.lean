module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.InverseImageComparison

/-!
# The composition law for the comm-ring form of the structure map

`Stacks.Sheaves.RingedToposModules.fSharpCommRing` is the inverse-image form
`f♯ : f⁻¹O_D ⟶ O_C` of the structure map of a morphism of ringed topoi, read as a morphism of
presheaves of *commutative* rings on the source site. It is the map along which scalars are
extended to form the pullback of sheaves of modules (Stacks 03D6, part (2)), so every statement
about the pullback that varies the morphism varies it only through `fSharpCommRing`. This file
supplies the composition law for that variation.

## The shape of the statement

The four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom` has no composition of its own,
so "`fSharpCommRing` of `ψ ∘ φ`" cannot be written at that level. What is written instead, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorStep2CompositionLaw.lean`, is the
two-field `AlgebraicGeometry.RingedToposHom.comp` of Stacks 01D3 (3) read through
`AlgebraicGeometry.RingedToposHom.toModulesHom`: both
`AlgebraicGeometry.RingedToposHom.comp_toToposHom` and
`AlgebraicGeometry.RingedToposHom.toModulesHom_toToposHom` hold by `rfl`, so no transport along
an equality of morphisms of topoi is needed and the inverse image along the composite is the
iterated inverse image on the nose.

The genuine transport that does remain is the one between the two ring structures carried by
that one underlying sheaf of sets, namely
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingComp`; it occurs in the law as the
comparison in front.

## Main results

* `Stacks.Sheaves.RingedToposModules.mk_fSharpCommRing_eq_fSharpInverseImage`: the comm-ring
  form of the structure map, read back as a morphism of sheaves of commutative rings, is
  `AlgebraicGeometry.RingedToposHom.fSharpInverseImage`. The two are *not* definitionally equal:
  `fSharpCommRing` of `toModulesHom` is built from the adjunct of `f♯` under the adjunction for
  sheaves of **rings**, and `fSharpInverseImage` from the adjunct of the same `f♯` under the
  adjunction for sheaves of **commutative rings**. Forgetting commutativity is fully faithful,
  and `AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage` identifies
  the two images, which is what proves this.
* `Stacks.Sheaves.RingedToposModules.fSharpCommRing_toModulesHom`: the same identification read
  on underlying presheaves of commutative rings.
* `Stacks.Sheaves.RingedToposModules.fSharpCommRing_comp`: **the composition law.** For
  `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)`, the comm-ring form of
  the structure map of `ψ ∘ φ` is the comparison of the iterated inverse image with the inverse
  image along the composite, followed by the inverse image along `φ` of the comm-ring form for
  `ψ`, followed by the comm-ring form for `φ`.

## Implementation notes

The law is obtained from `AlgebraicGeometry.RingedToposHom.compFSharpInverseImage`, the
inverse-image presentation of the structure map of a composite, by two steps that are each
recorded separately: that `compFSharpInverseImage` *is* the inverse-image form of the literal
composite — proved here from
`AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget` and
`AlgebraicGeometry.RingedToposHom.forget_map_compFSharpInverseImage` through the faithfulness of
forgetting the ring operations — and the identification of the two inverse-image forms above.
Neither step is definitional; both were checked not to be closed by `rfl`.

No `rw` is used. The only rearrangement needed is that `Sheaf.Hom.hom` of a threefold composite
is the composite of the three underlying morphisms of presheaves, and that is supplied by a
private lemma over abstract morphisms of an abstract quadruple of sheaves on an abstract site,
applied by `exact`: rewriting across the seam between a sheaf of commutative rings and its
underlying sheaf of rings reports targets that are not type-correct at the ambient
transparency.

**Universes.** The three ringed topoi share the universe of the sections of their structure
sheaves. That is inherited, not chosen: the comparison of iterated inverse images,
`Stacks.Sheaves.ToposPullback.pullbackCommRingSheafFunctorComp`, takes the sheaves of
commutative rings of its three sites in one universe, as the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposRingImageComposition.lean` record. The object
and morphism universes of the three sites stay independent. A consumer whose three ringed topoi
have independent section universes — the chain of Tag 03EL is stated that way — must therefore
instantiate it at matched section universes, or that comparison must first be generalized.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.Sheaves.RingedToposModules

universe w v u v' u' v'' u''

section HomComp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- `Sheaf.Hom.hom` of a threefold composite is the composite of the three underlying morphisms
of presheaves, with the two right-hand factors replaced along given equalities.

Stated over abstract morphisms of an abstract quadruple of sheaves on an abstract site, so that
applying it by `exact` never asks the elaborator to look inside a sheaf of commutative rings;
rewriting the same equalities in place reports a target that is not type-correct at the ambient
transparency. -/
private theorem hom_comp_comp_congr {A B D E : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) {b b' : B ⟶ D} (hb : b = b') {c c' : D ⟶ E} (hc : c = c') :
    (a ≫ b ≫ c).hom = a.hom ≫ b'.hom ≫ c'.hom := by
  subst hb; subst hc; rfl

end HomComp

section FSharpCommRingComp

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The comm-ring form of the structure map, read back as a morphism of sheaves of commutative
rings, is `AlgebraicGeometry.RingedToposHom.fSharpInverseImage`.**

Both are inverse-image forms of the same `f♯ : O_D ⟶ f_*O_C`, but they are taken through
different adjunctions — `fSharpCommRing` of `toModulesHom` through the adjunction for sheaves of
rings, `fSharpInverseImage` through the adjunction for sheaves of commutative rings — so the
identity is not definitional. It holds because forgetting commutativity is fully faithful and
carries the two to the same morphism of sheaves of rings. -/
theorem mk_fSharpCommRing_eq_fSharpInverseImage (f : AlgebraicGeometry.RingedToposHom X Y) :
    (⟨fSharpCommRing f.toModulesHom⟩ :
        (inverseImageCommRingFunctor f.toToposHom).obj Y.O ⟶ X.O) =
      f.fSharpInverseImage :=
  ((fullyFaithfulForgetCommRingSheaf X.J).map_injective
    ((AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage f).trans
      rfl)).symm

/-- The identification of the two inverse-image forms of the structure map, read on the
underlying presheaves of commutative rings. -/
theorem fSharpCommRing_toModulesHom (f : AlgebraicGeometry.RingedToposHom X Y) :
    fSharpCommRing f.toModulesHom = f.fSharpInverseImage.hom :=
  congrArg (fun m : (inverseImageCommRingFunctor f.toToposHom).obj Y.O ⟶ X.O ↦ m.hom)
    (mk_fSharpCommRing_eq_fSharpInverseImage f)

/-- **The composition law for `Stacks.Sheaves.RingedToposModules.fSharpCommRing` in the morphism
variable.** Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be
morphisms of ringed topoi in the sense of Stacks 01D3. The comm-ring form of the structure map
of `ψ ∘ φ`,

`(ψ ∘ φ)⁻¹O_E ⟶ O_C`,

is the comparison `(ψ ∘ φ)⁻¹O_E ≅ φ⁻¹(ψ⁻¹O_E)` of the inverse image along the composite with the
iterated inverse image, followed by the inverse image along `φ` of the comm-ring form for `ψ`,
followed by the comm-ring form for `φ`.

The inner occurrence has to be transported by the inverse-image functor on sheaves of
commutative rings, so it appears as the sheaf-level reading of `fSharpCommRing ψ.toModulesHom`;
`Stacks.Sheaves.RingedToposModules.mk_fSharpCommRing_eq_fSharpInverseImage` identifies that
reading with `ψ.fSharpInverseImage`. -/
theorem fSharpCommRing_comp (ψ : AlgebraicGeometry.RingedToposHom Y Z)
    (φ : AlgebraicGeometry.RingedToposHom X Y) :
    fSharpCommRing (ψ.comp φ).toModulesHom =
      ((inverseImageCommRingComp ψ.toToposHom φ.toToposHom).inv.app Z.O).hom ≫
        ((inverseImageCommRingFunctor φ.toToposHom).map
            (⟨fSharpCommRing ψ.toModulesHom⟩ :
              (inverseImageCommRingFunctor ψ.toToposHom).obj Z.O ⟶ Y.O)).hom ≫
          fSharpCommRing φ.toModulesHom := by
  have hcomp : (ψ.comp φ).fSharpInverseImage =
      AlgebraicGeometry.RingedToposHom.compFSharpInverseImage ψ φ :=
    X.forgetRing.map_injective
      ((AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget ψ φ).trans
        (AlgebraicGeometry.RingedToposHom.forget_map_compFSharpInverseImage ψ φ).symm)
  refine (fSharpCommRing_toModulesHom (ψ.comp φ)).trans ((congrArg (·.hom) hcomp).trans ?_)
  exact hom_comp_comp_congr _
    (congrArg (inverseImageCommRingFunctor φ.toToposHom).map
      (mk_fSharpCommRing_eq_fSharpInverseImage ψ).symm)
    (mk_fSharpCommRing_eq_fSharpInverseImage φ).symm

end FSharpCommRingComp

end Stacks.Sheaves.RingedToposModules

end
