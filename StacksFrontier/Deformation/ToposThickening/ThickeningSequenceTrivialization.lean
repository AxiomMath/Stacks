module

public import StacksFrontier.Deformation.ToposThickening.FirstOrderThickeningSequence
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposCompId
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexTrivialization

/-!
# A complex of first order thickenings on three sites trivializes its smallest thickening

Let `(Sh(C), O)` be a ringed topos and let

```
  (Sh(D₁), O'₁) --f₁₂--> (Sh(D₂), O'₂) --f₂₃--> (Sh(D₃), O'₃)
```

be a sequence of morphisms of first order thickenings of it in the sense of
`Deformation.ToposThickening.FirstOrderThickeningSequence`, which is a *complex*: the induced
maps `I₃ ⟶ I₂ ⟶ I₁` of defining ideals compose to zero. This file proves the consequence drawn
in the first paragraph of Stacks 08ML for that presentation: the composition
`(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` factors through `(Sh(C), O) ⟶ (Sh(D₃), O'₃)`, so that
`(Sh(D₁), O'₁)` is a trivial first order thickening of `(Sh(C), O)` and comes with a canonical
trivialization `π : (Sh(D₁), O'₁) ⟶ (Sh(C), O)`.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningSequence.splitting`: **Stacks 08ML**, the
  canonical map `O ⟶ O'₁` through which the composition `O'₃ ⟶ O'₁` factors.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.trivialization`: **Stacks 08ML**,
  the canonical trivialization `π` of the smallest thickening of a complex.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningSequence.wholeSharp_apply_eq_zero`: the
  composite `O'₃ ⟶ O'₁` kills the defining ideal `I₃` of the largest thickening.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.i₃_fSharp_comp_splitting`:
  **Stacks 08ML**, the factorization itself: the composite `O'₃ ⟶ O'₁` is `O'₃ ⟶ O ⟶ O'₁`.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.splitting_unique`: the factorizing
  map is unique, which is what makes the trivialization canonical.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.splitting_comp_fSharp`: the
  factorizing map is a section of the structure map of the smallest thickening.
* `Deformation.ToposThickening.FirstOrderThickeningSequence.isTrivial`: **Stacks 08ML**, the
  smallest thickening of a complex is trivial.

## The three steps

*The composite kills `I₃`.* This is the complex condition, transposed twice. The induced map of
defining ideals of a morphism of thickenings is characterised on the target topos: by
`Deformation.ToposThickening.MorphismOfThickenings.homEquiv_idealMap_comp_incl` the transpose of
`(f')^*J ⟶ I ⟶ O'` is `J ⟶ O_{B'} ⟶ (f')_*O'`. Applying this to the second square turns the
complex condition `f₁₂^*(f₂₃^*I₃ ⟶ I₂) ≫ (f₁₂^*I₂ ⟶ I₁) = 0` into the vanishing of
`f₂₃^*I₃ ⟶ I₂ ⟶ (f₁₂)_*O'₁`, and applying it to the first square turns *that* into the
vanishing of `I₃ ⟶ (f₂₃)_*(f₁₂)_*O'₁`. The last map is the structure map of the composite
morphism of ringed topoi, read on unit modules, by
`AlgebraicGeometry.RingedToposHom.unitStructureMap_comp`; on sections it is `(f₂₃ ∘ f₁₂)^♯`.

*The descent.* Since `O'₃ ⟶ i₃_*O` is locally surjective with kernel `I₃`, the composite
descends: `Stacks.Sites.existsUnique_commRingFactor` produces a unique map
`i₃_*O ⟶ (f₂₃)_*(f₁₂)_*O'₁` whose composite with `(i₃)^♯` is `(f₂₃ ∘ f₁₂)^♯`.

*The transport.* The descended map lives on the site of `(Sh(D₃), O'₃)`, while a trivialization
of `(Sh(D₁), O'₁)` needs a section `O ⟶ O'₁` on the site of `(Sh(D₁), O'₁)`. The two are
exchanged by the direct image: the underlying morphism of topoi of each of `f₁₂` and `f₂₃` is an
equivalence — it becomes one after composing with the equivalence a thickening induces — hence
so is the direct image of sheaves of commutative rings along it, by
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor_isEquivalence`. The descended map is
therefore the image of a unique map `i₁_*O ⟶ O'₁`, once `(f₂₃)_*(f₁₂)_*(i₁_*O)` is identified
with `i₃_*O`; that identification is `baseIso` below, built from the comparison of successive
direct images and the two commutativities of the sequence.

## Implementation notes

The composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` is used only through its structure map, never
through the square of thickenings it spans over `(Sh(C), O)`. Writing that square down would
need `(f₂₃ ∘ f₁₂) ∘ i₁ = i₃ ∘ id`, hence an associativity law for
`AlgebraicGeometry.RingedToposHom.comp`, which this development does not have; the two
commutativities of the sequence are used one at a time instead, each in the form
`AlgebraicGeometry.RingedToposHom.fSharp_comp_eqToHom` gives them. Only the identity law
`AlgebraicGeometry.RingedToposHom.comp_id` is needed, to read the commutativities as
`f₁₂ ∘ i₁ = i₂` and `f₂₃ ∘ i₂ = i₃`.

The structure map of the composite is read in two forms: as `(f₂₃ ∘ f₁₂)^♯`, which is what the
unit-module calculation produces, and as `(f₂₃)^♯ ≫ (f₂₃)_*(f₁₂)^♯` — the `wholeSharp` below —
which is the form the transport wants, the iterated direct image being where the comparison
isomorphisms are natural. The two differ by the comparison
`Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso`, which is where `whole_fSharp_eq`
puts them together.

## References

* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedToposHom (unitStructureMap pullbackUnitStructureMap
  pushforwardModules pullbackAdjPushforwardModules pushforwardModulesCompIso)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardCommRingCompIso
  pushforwardCommRingFunctor_isEquivalence)

universe v u w v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃

namespace AlgebraicGeometry.RingedToposHom

section BaseComparison

open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardCommRingCompIso)

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w₁}}
  {Y₂ : RingedTopos.{v₂, u₂, w₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- The comparison of successive direct images of the structure sheaf of the source with its
direct image along the composite, with the target spelled through the composite morphism of
ringed topoi rather than through the composite of the underlying morphisms of topoi. The two
agree definitionally; naming the comparison at this spelling is what lets a commutative triangle
of morphisms of ringed topoi be transported through it. -/
noncomputable def pushforwardCompIso (a : RingedToposHom X Y₁) (b : RingedToposHom Y₁ Y₂) :
    (pushforwardCommRingFunctor b.toToposHom).obj
        ((pushforwardCommRingFunctor a.toToposHom).obj X.O) ≅
      (pushforwardCommRingFunctor (b.comp a).toToposHom).obj X.O :=
  pushforwardCommRingCompIso a.toToposHom b.toToposHom X.O

/-- The comparison carries the structure map of `a`, pushed forward along `b` and preceded by
the structure map of `b`, to the structure map of the composite. This is the definition of
composition of morphisms of ringed topoi. -/
theorem fSharp_comp_pushforwardCompIso (a : RingedToposHom X Y₁) (b : RingedToposHom Y₁ Y₂) :
    b.fSharp ≫ (pushforwardCommRingFunctor b.toToposHom).map a.fSharp ≫
        (pushforwardCompIso a b).hom = (b.comp a).fSharp :=
  rfl

/-- For a commutative triangle `b ∘ a = c` of morphisms of ringed topoi, the comparison of the
direct image along `b` of the direct image along `a` of the structure sheaf of the source with
its direct image along `c`: the comparison of successive direct images, followed by the
transport along the triangle. -/
noncomputable def pushforwardBaseIso (a : RingedToposHom X Y₁) (b : RingedToposHom Y₁ Y₂)
    (c : RingedToposHom X Y₂) (h : b.comp a = c) :
    (pushforwardCommRingFunctor b.toToposHom).obj
        ((pushforwardCommRingFunctor a.toToposHom).obj X.O) ≅
      (pushforwardCommRingFunctor c.toToposHom).obj X.O :=
  pushforwardCompIso a b ≪≫
    eqToIso (congrArg (fun m : RingedToposHom X Y₂ ↦
      (pushforwardCommRingFunctor m.toToposHom).obj X.O) h)

/-- The comparison carries the structure map of `a`, pushed forward along `b` and preceded by
the structure map of `b`, to the structure map of `c`: once the triangle is substituted the
transport is the identity and this is `fSharp_comp_pushforwardCompIso`. -/
theorem fSharp_comp_pushforwardBaseIso (a : RingedToposHom X Y₁) (b : RingedToposHom Y₁ Y₂)
    (c : RingedToposHom X Y₂) (h : b.comp a = c) :
    b.fSharp ≫ (pushforwardCommRingFunctor b.toToposHom).map a.fSharp ≫
        (pushforwardBaseIso a b c h).hom = c.fSharp := by
  subst h
  change b.fSharp ≫ (pushforwardCommRingFunctor b.toToposHom).map a.fSharp ≫
      ((pushforwardCompIso a b).hom ≫
        eqToHom (congrArg (fun m : RingedToposHom X Y₂ ↦
          (pushforwardCommRingFunctor m.toToposHom).obj X.O) (rfl : b.comp a = b.comp a))) =
    (b.comp a).fSharp
  rw [eqToHom_refl, Category.comp_id]
  exact fSharp_comp_pushforwardCompIso a b

/-- If `b ∘ a = c` and the direct images along `a` and `c` are equivalences, so is the one
along `b`. -/
private theorem pushforward_isEquivalence_of_comp_eq (a : RingedToposHom X Y₁)
    (b : RingedToposHom Y₁ Y₂) (c : RingedToposHom X Y₂)
    (h : b.comp a = c) (ha : a.toToposHom.pushforward.IsEquivalence)
    (hc : c.toToposHom.pushforward.IsEquivalence) : b.toToposHom.pushforward.IsEquivalence := by
  have : (a.toToposHom.pushforward ⋙ b.toToposHom.pushforward).IsEquivalence := by
    rw [show a.toToposHom.pushforward ⋙ b.toToposHom.pushforward = c.toToposHom.pushforward from
      congrArg (fun m : RingedToposHom X Y₂ ↦ m.toToposHom.pushforward) h]
    exact hc
  exact Functor.isEquivalence_of_comp_left a.toToposHom.pushforward b.toToposHom.pushforward

/-- The structure map of `b`, followed by the structure map of `a` pushed forward along `b`, is
the structure map of `c` read through the inverse of the comparison. -/
private theorem fSharp_comp_map_fSharp_eq
    (a : RingedToposHom X Y₁) (b : RingedToposHom Y₁ Y₂) (c : RingedToposHom X Y₂)
    (h : b.comp a = c) :
    b.fSharp ≫ (pushforwardCommRingFunctor b.toToposHom).map a.fSharp =
      c.fSharp ≫ (pushforwardBaseIso a b c h).inv := by
  rw [← fSharp_comp_pushforwardBaseIso a b c h, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end BaseComparison

end AlgebraicGeometry.RingedToposHom

namespace Deformation.ToposThickening

namespace FirstOrderThickeningSequence

variable {X : RingedTopos.{v, u, w}} {X₁ : RingedTopos.{v₁, u₁, w₁}}
  {X₂ : RingedTopos.{v₂, u₂, w₂}} {X₃ : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₂})] [X₃.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [X₃.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  (S : FirstOrderThickeningSequence X X₁ X₂ X₃)

/-- The first morphism of the sequence lies over the identity of the base, with the identity
composed away: `f₁₂ ∘ i₁ = i₂`. -/
theorem f₁₂_comp_i₁ : S.f₁₂.comp S.i₁ = S.i₂ :=
  S.comm₁₂.trans (RingedToposHom.comp_id S.i₂)

/-- The second morphism of the sequence lies over the identity of the base, with the identity
composed away: `f₂₃ ∘ i₂ = i₃`. -/
theorem f₂₃_comp_i₂ : S.f₂₃.comp S.i₂ = S.i₃ :=
  S.comm₂₃.trans (RingedToposHom.comp_id S.i₃)

section Equivalences

/-- The underlying morphism of topoi of the first morphism of the sequence is an equivalence:
composed with the equivalence the first thickening induces it is the equivalence the second
thickening induces. -/
theorem f₁₂_pushforward_isEquivalence : S.f₁₂.toToposHom.pushforward.IsEquivalence :=
  AlgebraicGeometry.RingedToposHom.pushforward_isEquivalence_of_comp_eq S.i₁ S.f₁₂ S.i₂
    S.f₁₂_comp_i₁ S.firstOrder₁.isThickening.1 S.firstOrder₂.isThickening.1

/-- The underlying morphism of topoi of the second morphism of the sequence is an
equivalence. -/
theorem f₂₃_pushforward_isEquivalence : S.f₂₃.toToposHom.pushforward.IsEquivalence :=
  AlgebraicGeometry.RingedToposHom.pushforward_isEquivalence_of_comp_eq S.i₂ S.f₂₃ S.i₃
    S.f₂₃_comp_i₂ S.firstOrder₂.isThickening.1 S.firstOrder₃.isThickening.1

/-- The iterated direct image of sheaves of commutative rings along the sequence is fully
faithful, both factors being equivalences. -/
noncomputable def pushforwardCommRingFullyFaithful :
    (pushforwardCommRingFunctor S.f₁₂.toToposHom ⋙
      pushforwardCommRingFunctor S.f₂₃.toToposHom).FullyFaithful :=
  haveI := pushforwardCommRingFunctor_isEquivalence _ S.f₁₂_pushforward_isEquivalence
  haveI := pushforwardCommRingFunctor_isEquivalence _ S.f₂₃_pushforward_isEquivalence
  Functor.FullyFaithful.ofFullyFaithful _

end Equivalences

section BaseComparison

/-- The structure sheaf of the base, carried from the topos of the first thickening to that of
the second. -/
noncomputable def baseIso₁ :
    (pushforwardCommRingFunctor S.f₁₂.toToposHom).obj (baseRing S.i₁) ≅ baseRing S.i₂ :=
  RingedToposHom.pushforwardBaseIso S.i₁ S.f₁₂ S.i₂ S.f₁₂_comp_i₁

/-- The structure sheaf of the base, carried from the topos of the second thickening to that of
the third. -/
noncomputable def baseIso₂ :
    (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj (baseRing S.i₂) ≅ baseRing S.i₃ :=
  RingedToposHom.pushforwardBaseIso S.i₂ S.f₂₃ S.i₃ S.f₂₃_comp_i₂

/-- The structure sheaf of the base, carried from the topos of the first thickening to that of
the third along the sequence. -/
noncomputable def baseIso :
    (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj (baseRing S.i₁)) ≅ baseRing S.i₃ :=
  (pushforwardCommRingFunctor S.f₂₃.toToposHom).mapIso S.baseIso₁ ≪≫ S.baseIso₂

/-- The comparison of the first two bases carries the structure map of the first thickening,
pushed forward along `f₁₂`, to the structure map of the second thickening. -/
theorem fSharp_comp_baseIso₁ :
    S.f₁₂.fSharp ≫ (pushforwardCommRingFunctor S.f₁₂.toToposHom).map S.i₁.fSharp ≫
        S.baseIso₁.hom = S.i₂.fSharp :=
  RingedToposHom.fSharp_comp_pushforwardBaseIso S.i₁ S.f₁₂ S.i₂ S.f₁₂_comp_i₁

/-- The comparison of the last two bases carries the structure map of the second thickening,
pushed forward along `f₂₃`, to the structure map of the third thickening. -/
theorem fSharp_comp_baseIso₂ :
    S.f₂₃.fSharp ≫ (pushforwardCommRingFunctor S.f₂₃.toToposHom).map S.i₂.fSharp ≫
        S.baseIso₂.hom = S.i₃.fSharp :=
  RingedToposHom.fSharp_comp_pushforwardBaseIso S.i₂ S.f₂₃ S.i₃ S.f₂₃_comp_i₂

end BaseComparison

section WholeSharp

/-- The structure map of the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)`, read as a map into the
iterated direct image `(f₂₃)_*(f₁₂)_*O'₁`. -/
noncomputable def wholeSharp :
    X₃.O ⟶ (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj X₁.O) :=
  S.f₂₃.fSharp ≫ (pushforwardCommRingFunctor S.f₂₃.toToposHom).map S.f₁₂.fSharp

/-- Read through the comparison of successive direct images with the direct image of the
composite, `wholeSharp` is the structure map of the composite morphism of ringed topoi. -/
theorem wholeSharp_comp_compIso :
    S.wholeSharp ≫ (pushforwardCommRingCompIso S.f₁₂.toToposHom S.f₂₃.toToposHom X₁.O).hom =
      (S.f₂₃.comp S.f₁₂).fSharp :=
  Category.assoc _ _ _

/-- The composite `O'₃ ⟶ O'₁`, followed by the structure map of the smallest thickening pushed
forward along the sequence, is the structure map of the largest thickening read through the
comparison of the bases. This is the identity the section property of the canonical map comes
from. -/
theorem wholeSharp_comp_pushforward_i₁_fSharp :
    S.wholeSharp ≫ (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map S.i₁.fSharp) =
      S.i₃.fSharp ≫ S.baseIso.inv := by
  have h₁ := AlgebraicGeometry.RingedToposHom.fSharp_comp_map_fSharp_eq S.i₁ S.f₁₂ S.i₂
    S.f₁₂_comp_i₁
  have h₂ := AlgebraicGeometry.RingedToposHom.fSharp_comp_map_fSharp_eq S.i₂ S.f₂₃ S.i₃
    S.f₂₃_comp_i₂
  rw [wholeSharp, baseIso, Iso.trans_inv, Functor.mapIso_inv, Category.assoc,
    ← CategoryTheory.Functor.map_comp, h₁, CategoryTheory.Functor.map_comp, ← Category.assoc,
    h₂, Category.assoc]
  rfl

end WholeSharp

/-- Two maps out of the structure sheaf of the base into an iterated direct image agree once
composed with the locally surjective structure map of the third thickening. -/
private theorem eq_of_i₃_fSharp_comp_eq (Y : Sheaf X₁.J CommRingCat.{w₁})
    {g₁ g₂ : baseRing S.i₃ ⟶ (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj Y)}
    (h : S.i₃.fSharp ≫ g₁ = S.i₃.fSharp ≫ g₂) : g₁ = g₂ :=
  Sheaf.hom_ext (Stacks.Sites.commRingHom_ext_of_isLocallySurjective S.i₃.fSharp.hom
    S.firstOrder₃.isThickening.2.1 (Stacks.Sites.isSheaf_comp_forget_commRingCat
      ((pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj Y)).property)
    (congrArg (·.hom) h))

section Complex

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [X₃.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X₁.J AddCommGrpCat.{w₁}]
  [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify X₂.J AddCommGrpCat.{w₂}]
  [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]

/-- For a complex, the map `I₂ ⟶ (f₁₂)_*O'₁` built from the inclusion `I₂ ⊂ O'₂` and the
structure map of `f₁₂` kills the image of `f₂₃^*I₃`. This is the complex condition transposed
across the adjunction `f₁₂^* ⊣ (f₁₂)_*`. -/
theorem idealMap₂₃_comp_incl_comp_unitStructureMap (hS : S.IsComplex) :
    S.square₂₃.idealMap ≫ S.ideal₂.incl ≫ unitStructureMap S.f₁₂ = 0 := by
  have h : (pullbackModules S.f₁₂.toModulesHom).map S.square₂₃.idealMap ≫
      S.square₁₂.idealMap = 0 := hS
  have e : ((pullbackAdjPushforwardModules S.f₁₂).homEquiv _ _)
      (S.square₁₂.idealMap ≫ S.ideal₁.incl) = S.ideal₂.incl ≫ unitStructureMap S.f₁₂ :=
    S.square₁₂.homEquiv_idealMap_comp_incl
  calc S.square₂₃.idealMap ≫ S.ideal₂.incl ≫ unitStructureMap S.f₁₂
      = S.square₂₃.idealMap ≫ ((pullbackAdjPushforwardModules S.f₁₂).homEquiv _ _)
          (S.square₁₂.idealMap ≫ S.ideal₁.incl) := congrArg (_ ≫ ·) e.symm
    _ = ((pullbackAdjPushforwardModules S.f₁₂).homEquiv _ _)
          ((pullbackModules S.f₁₂.toModulesHom).map S.square₂₃.idealMap ≫
            S.square₁₂.idealMap ≫ S.ideal₁.incl) :=
        ((pullbackAdjPushforwardModules S.f₁₂).homEquiv_naturality_left _ _).symm
    _ = ((pullbackAdjPushforwardModules S.f₁₂).homEquiv _ _) 0 :=
        congrArg ((pullbackAdjPushforwardModules S.f₁₂).homEquiv _ _)
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ S.ideal₁.incl) h).trans zero_comp))
    _ = 0 := (pullbackAdjPushforwardModules S.f₁₂).homAddEquiv_zero _ _

/-- For a complex, the composite `I₃ ⟶ O'₃ ⟶ (f₂₃)_*(f₁₂)_*O'₁` vanishes: the complex condition
transposed across the second adjunction as well. -/
theorem incl₃_comp_unitStructureMap_comp_pushforward (hS : S.IsComplex) :
    S.ideal₃.incl ≫ unitStructureMap S.f₂₃ ≫
      (pushforwardModules S.f₂₃).map (unitStructureMap S.f₁₂) = 0 := by
  have e : ((pullbackAdjPushforwardModules S.f₂₃).homEquiv _ _)
      (S.square₂₃.idealMap ≫ S.ideal₂.incl) = S.ideal₃.incl ≫ unitStructureMap S.f₂₃ :=
    S.square₂₃.homEquiv_idealMap_comp_incl
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e.symm).trans
    (((pullbackAdjPushforwardModules S.f₂₃).homEquiv_naturality_right _ _).symm.trans ?_))
  exact (congrArg ((pullbackAdjPushforwardModules S.f₂₃).homEquiv _ _)
    ((Category.assoc _ _ _).trans (S.idealMap₂₃_comp_incl_comp_unitStructureMap hS))).trans
    ((pullbackAdjPushforwardModules S.f₂₃).homAddEquiv_zero _ _)

/-- For a complex, the structure map of the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)`, read on
unit modules, kills the defining ideal `I₃`. -/
theorem incl₃_comp_unitStructureMap_comp (hS : S.IsComplex) :
    S.ideal₃.incl ≫ unitStructureMap (S.f₂₃.comp S.f₁₂) = 0 :=
  (cancel_mono ((pushforwardModulesCompIso S.f₁₂ S.f₂₃).app
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O))).hom).mp <|
    ((Category.assoc _ _ _).trans <|
      (congrArg (S.ideal₃.incl ≫ ·) (RingedToposHom.unitStructureMap_comp S.f₂₃ S.f₁₂)).trans
        (S.incl₃_comp_unitStructureMap_comp_pushforward hS)).trans zero_comp.symm

/-- For a complex, a local section of `O'₃` killed by the structure map of the third thickening
is killed by the structure map of the composite `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)`. -/
theorem comp_fSharp_apply_eq_zero (hS : S.IsComplex) (U : X₃.Cᵒᵖ) (a : X₃.O.obj.obj U)
    (ha : S.i₃.fSharp.hom.app U a = 0) : (S.f₂₃.comp S.f₁₂).fSharp.hom.app U a = 0 := by
  obtain ⟨b, hb⟩ := S.ideal₃.exists_section U a ha
  rw [← hb]
  exact (RingedToposHom.unitStructureMap_val_app (S.f₂₃.comp S.f₁₂) U _).symm.trans
    (congrArg (fun m : S.ideal₃.I ⟶
        (pushforwardModules (S.f₂₃.comp S.f₁₂)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X₁.O)) ↦ m.val.app U b)
      (S.incl₃_comp_unitStructureMap_comp hS))

/-- For a complex, a local section of `O'₃` killed by the structure map of the third thickening
is killed by `wholeSharp`. -/
theorem wholeSharp_apply_eq_zero (hS : S.IsComplex) (U : X₃.Cᵒᵖ) (a : X₃.O.obj.obj U)
    (ha : S.i₃.fSharp.hom.app U a = 0) : S.wholeSharp.hom.app U a = 0 := by
  set cI := pushforwardCommRingCompIso S.f₁₂.toToposHom S.f₂₃.toToposHom X₁.O with hcI
  have e₁ : cI.hom.hom.app U (S.wholeSharp.hom.app U a) = 0 :=
    (congrArg (fun m : X₃.O ⟶ (pushforwardCommRingFunctor (S.f₂₃.comp S.f₁₂).toToposHom).obj X₁.O
      ↦ m.hom.app U a) S.wholeSharp_comp_compIso).trans
      (S.comp_fSharp_apply_eq_zero hS U a ha)
  have e₂ : cI.inv.hom.app U (cI.hom.hom.app U (S.wholeSharp.hom.app U a)) =
      S.wholeSharp.hom.app U a :=
    congrArg (fun m : (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj X₁.O) ⟶
      (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj X₁.O) ↦
      m.hom.app U (S.wholeSharp.hom.app U a)) cI.hom_inv_id
  calc S.wholeSharp.hom.app U a
      = cI.inv.hom.app U (cI.hom.hom.app U (S.wholeSharp.hom.app U a)) := e₂.symm
    _ = cI.inv.hom.app U 0 := congrArg (cI.inv.hom.app U) e₁
    _ = 0 := map_zero (cI.inv.hom.app U).hom

/-- The descent of `wholeSharp` along the structure map of the third thickening exists and is
unique: the structure map is locally surjective, its kernel is `I₃`, and `wholeSharp` kills
`I₃`. -/
theorem descent_existsUnique (hS : S.IsComplex) :
    ∃! σ : (baseRing S.i₃).obj ⟶ ((pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj X₁.O)).obj,
      S.i₃.fSharp.hom ≫ σ = S.wholeSharp.hom :=
  Stacks.Sites.existsUnique_commRingFactor S.i₃.fSharp.hom S.wholeSharp.hom
    S.firstOrder₃.isThickening.2.1
    (Stacks.Sites.isSheaf_comp_forget_commRingCat
      ((pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj X₁.O)).property)
    fun U a ha ↦ S.wholeSharp_apply_eq_zero hS U a ha

/-- The descent of the composite `O'₃ ⟶ O'₁` along the structure map of the third thickening,
read on the topos of the third thickening. -/
noncomputable def descent (hS : S.IsComplex) :
    baseRing S.i₃ ⟶ (pushforwardCommRingFunctor S.f₂₃.toToposHom).obj
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).obj X₁.O) :=
  ⟨(S.descent_existsUnique hS).choose⟩

/-- The descent factors the composite `O'₃ ⟶ O'₁` through the structure map of the third
thickening. -/
theorem i₃_fSharp_comp_descent (hS : S.IsComplex) :
    S.i₃.fSharp ≫ S.descent hS = S.wholeSharp :=
  Sheaf.hom_ext (S.descent_existsUnique hS).choose_spec.1

/-- **Stacks 08ML.** The canonical map `O ⟶ O'₁` attached to a complex of first order
thickenings: the unique map whose iterated direct image along the sequence is the descent of the
composite `O'₃ ⟶ O'₁`. -/
noncomputable def splitting (hS : S.IsComplex) : baseRing S.i₁ ⟶ X₁.O :=
  S.pushforwardCommRingFullyFaithful.preimage (S.baseIso.hom ≫ S.descent hS)

/-- The iterated direct image of the canonical map is the descent, read through the comparison
of the bases. -/
theorem map_splitting (hS : S.IsComplex) :
    (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map (S.splitting hS)) =
      S.baseIso.hom ≫ S.descent hS :=
  S.pushforwardCommRingFullyFaithful.map_preimage _

/-- **Stacks 08ML.** For a complex of first order thickenings, the composition
`(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` factors through `(Sh(C), O) ⟶ (Sh(D₃), O'₃)`: on structure
sheaves, the composite `O'₃ ⟶ O'₁` is `O'₃ ⟶ O ⟶ O'₁`, the second map being the canonical map
carried to the topos of the third thickening. -/
@[stacks 08ML "the composition D₁ ⟶ D₃ factors through the base"]
theorem i₃_fSharp_comp_splitting (hS : S.IsComplex) :
    S.i₃.fSharp ≫ S.baseIso.inv ≫ (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
        ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map (S.splitting hS)) =
      S.wholeSharp := by
  rw [S.map_splitting hS, Iso.inv_hom_id_assoc, S.i₃_fSharp_comp_descent hS]

/-- The factorization is unique: the canonical map is the only map `O ⟶ O'₁` whose iterated
direct image, read through the comparison of the bases, factors the composite `O'₃ ⟶ O'₁`
through the structure map of the third thickening. This is what makes the trivialization
canonical. -/
theorem splitting_unique (hS : S.IsComplex) (t : baseRing S.i₁ ⟶ X₁.O)
    (ht : S.i₃.fSharp ≫ S.baseIso.inv ≫ (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map t) = S.wholeSharp) :
    t = S.splitting hS := by
  refine S.pushforwardCommRingFullyFaithful.map_injective ?_
  change (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map t) =
    (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map (S.splitting hS))
  rw [S.map_splitting hS]
  exact (Iso.inv_comp_eq S.baseIso).mp
    (S.eq_of_i₃_fSharp_comp_eq _ (ht.trans (S.i₃_fSharp_comp_descent hS).symm))

/-- The canonical map is a section of the structure map of the smallest thickening: composing it
with `O'₁ ⟶ O` gives the identity, because the structure map of the third thickening is locally
surjective and the two composites with it agree. -/
theorem splitting_comp_fSharp (hS : S.IsComplex) :
    S.splitting hS ≫ S.i₁.fSharp = 𝟙 (baseRing S.i₁) := by
  have key : S.descent hS ≫ (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map S.i₁.fSharp) = S.baseIso.inv := by
    refine S.eq_of_i₃_fSharp_comp_eq _ ?_
    rw [← Category.assoc, S.i₃_fSharp_comp_descent hS, S.wholeSharp_comp_pushforward_i₁_fSharp]
  refine S.pushforwardCommRingFullyFaithful.map_injective ?_
  change (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map (S.splitting hS ≫ S.i₁.fSharp)) =
    (pushforwardCommRingFunctor S.f₂₃.toToposHom).map
      ((pushforwardCommRingFunctor S.f₁₂.toToposHom).map (𝟙 (baseRing S.i₁)))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, S.map_splitting hS,
    Category.assoc, key, Iso.hom_inv_id]

/-- **Stacks 08ML.** The canonical trivialization `π : (Sh(D₁), O'₁) ⟶ (Sh(C), O)` of the
smallest thickening of a complex of first order thickenings. -/
@[stacks 08ML "the canonical trivialization of the smallest thickening"]
noncomputable def trivialization (hS : S.IsComplex) : Trivialization S.i₁ :=
  trivializationOfBaseSplitting S.i₁ S.firstOrder₁.isThickening.1 (S.splitting hS)
    (S.splitting_comp_fSharp hS)

/-- **Stacks 08ML.** The smallest thickening of a complex of first order thickenings is a
trivial first order thickening of the base. -/
@[stacks 08ML "the smallest thickening of a complex is trivial"]
theorem isTrivial (hS : S.IsComplex) : IsTrivial S.i₁ := ⟨S.trivialization hS⟩

end Complex

end FirstOrderThickeningSequence

end Deformation.ToposThickening

end
