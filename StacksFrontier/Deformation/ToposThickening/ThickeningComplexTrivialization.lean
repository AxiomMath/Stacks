module

public import StacksFrontier.CategoryTheory.Sites.CommRingSheafFactorization
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundary
public import StacksFrontier.Deformation.ToposThickening.Trivialization.OfSplittingEquivalence

/-!
# A complex of first order thickenings trivializes its smallest thickening

Let `(Sh(C), O)` be a ringed topos and let

```
  (Sh(D₁), O'₁) ⟶ (Sh(D₂), O'₂) ⟶ (Sh(D₃), O'₃)
```

be a *complex* of first order thickenings of it in the sense of Stacks 08ML: the induced maps
`I₃ ⟶ I₂ ⟶ I₁` of defining ideals compose to zero. This file proves the consequence drawn in
the first paragraph of that remark: the composition `(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` factors
through `(Sh(C), O) ⟶ (Sh(D₃), O'₃)`, so that `(Sh(D₁), O'₁)` is a trivial first order
thickening of `(Sh(C), O)` and comes with a canonical trivialization
`π : (Sh(D₁), O'₁) ⟶ (Sh(C), O)`.

On structure sheaves the composition is the map `O'₃ ⟶ O'₁`, and the complex condition says
exactly that it kills `I₃ = Ker(O'₃ ⟶ O)`. Since `O'₃ ⟶ O` is locally surjective with kernel
`I₃`, the map descends to a map `O ⟶ O'₁` — which is the factorization — and that map is a
section of `O'₁ ⟶ O` because `O'₃ ⟶ O` is an epimorphism and the two composites with it agree.
A section of the structure map is a trivialization, by Stacks 08MG.

## Main definitions

* `Deformation.ToposThickening.trivializationOfBaseSplitting`: a section of the structure map
  of a first order thickening, read on the target topos, as a trivialization.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.splitting`: **Stacks 08ML**, the
  canonical map `O ⟶ O'₁` through which the composition `O'₃ ⟶ O'₁` factors.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.trivialization`: **Stacks 08ML**,
  the canonical trivialization `π` of the smallest thickening of a complex.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.fSharp₃_comp_splitting`:
  **Stacks 08ML**, the factorization itself: the composite `O'₃ ⟶ O'₁` is `O'₃ ⟶ O ⟶ O'₁`.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.splitting_unique`: the factorizing
  map is unique, which is what makes the trivialization canonical.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.splitting_comp_fSharp`: the
  factorizing map is a section of the structure map of the smallest thickening.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.isTrivial`: **Stacks 08ML**, the
  smallest thickening of a complex is trivial.

## Implementation notes

The complex is presented on one site, as in
`Deformation.ToposThickening.FirstOrderThickeningComplex`
(`StacksFrontier/Deformation/ToposThickening/ThickeningComplexBoundary.lean`), which is the
presentation in which the three ideals and the three structure sheaves live over one topos and
the composite `O'₃ ⟶ O'₁` is a map of sheaves on that site. The three-site presentation of the
*definitions* of the remark is
`Deformation.ToposThickening.FirstOrderThickeningSequence`
(`StacksFrontier/Deformation/ToposThickening/FirstOrderThickeningSequence.lean`); the same
consequence for that presentation is
`StacksFrontier/Deformation/ToposThickening/ThickeningSequenceTrivialization.lean`, where the
composite `O'₃ ⟶ O'₁` is a morphism of sheaves across three sites and the descended map is
carried back to the site of the smallest thickening along the equivalences of topoi the
thickenings induce. Neither file subsumes the other: there the three ideals are related only
through pullback functors, which is why the obstruction theory of Stacks 08MM is stated here.

The descent of `O'₃ ⟶ O'₁` along `O'₃ ⟶ O` is
`Stacks.Sites.existsUnique_commRingFactor`, stated for an arbitrary locally surjective morphism
of presheaves of commutative rings. It is the only genuinely sheaf-theoretic step: the section
of `O'₃ ⟶ O` over a local section of `O` exists only locally, and the glued map is a map of
rings because the target is separated.

The passage from a section `O ⟶ O'₁` of the structure map, which is what the descent produces
and which lives on the topos of the thickening, to the retraction
`π : (Sh(D₁), O'₁) ⟶ (Sh(C), O)` of ringed topoi, whose structure map lives on the base topos,
is `Deformation.ToposThickening.trivializationOfBaseSplitting`: the two are exchanged by the
adjunction `i⁻¹ ⊣ i_*`, whose counit at `O` is invertible because the direct image of a
thickening is an equivalence.

## References

* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08MG](https://stacks.math.columbia.edu/tag/08MG)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction pushforwardCommRingFunctor_isEquivalence)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

section Splitting

variable (i : RingedToposHom X Y) (hi : i.toToposHom.pushforward.IsEquivalence)
  (s : (pushforwardCommRingFunctor i.toToposHom).obj X.O ⟶ Y.O)

/-- A section of the structure map `O' ⟶ i_*O` of a first order thickening, read on the topos
of the thickening, transported to the inverse-image form `O ⟶ i⁻¹O'` across the adjunction
`i⁻¹ ⊣ i_*`. The counit of that adjunction at `O` is invertible because the direct image of a
thickening is an equivalence. -/
noncomputable def splittingInverseImage :
    X.O ⟶ (inverseImageCommRingFunctor i.toToposHom).obj Y.O :=
  haveI : (pushforwardCommRingFunctor i.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence i.toToposHom hi
  inv ((commRingImageAdjunction i.toToposHom).counit.app X.O) ≫
    (inverseImageCommRingFunctor i.toToposHom).map s

/-- The transported section is a section of the inverse-image form of the structure map. -/
theorem splittingInverseImage_comp_fSharpInverseImage (hs : s ≫ i.fSharp = 𝟙 _) :
    splittingInverseImage i hi s ≫ i.fSharpInverseImage = 𝟙 X.O := by
  have : (pushforwardCommRingFunctor i.toToposHom).IsEquivalence :=
    pushforwardCommRingFunctor_isEquivalence i.toToposHom hi
  have hfs : i.fSharpInverseImage =
      (inverseImageCommRingFunctor i.toToposHom).map i.fSharp ≫
        (commRingImageAdjunction i.toToposHom).counit.app X.O :=
    (commRingImageAdjunction i.toToposHom).homEquiv_counit Y.O X.O i.fSharp
  rw [splittingInverseImage, hfs, Category.assoc, ← Category.assoc
    ((inverseImageCommRingFunctor i.toToposHom).map s), ← CategoryTheory.Functor.map_comp, hs,
    CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]

/-- A section of the structure map of a first order thickening, read on the topos of the
thickening, is a trivialization of it. This is
`Deformation.ToposThickening.trivializationOfSplittingOfEquivalence`, the form of Stacks 08MG
with its splitting supplied in the direct-image form. -/
noncomputable def trivializationOfBaseSplitting (hs : s ≫ i.fSharp = 𝟙 _) : Trivialization i :=
  (trivializationOfSplittingOfEquivalence i hi (splittingInverseImage i hi s)
    (splittingInverseImage_comp_fSharpInverseImage i hi s hs)).1

end Splitting

namespace FirstOrderThickeningComplex

variable {i : RingedToposHom X Y} (S : FirstOrderThickeningComplex i) (hS : S.IsComplex)

include hS in
/-- For a complex of first order thickenings, the composite `O'₃ ⟶ O'₁` kills the defining ideal
`I₃` of the third thickening: a section of `I₃` has the same image in `O'₁` under it as the
section of `I₁` the induced map of defining ideals produces, and that map is zero. -/
theorem whole_hSharp_apply_eq_zero (U : Y.Cᵒᵖ) (a : S.O₃.obj.obj U)
    (ha : S.fSharp₃.hom.app U a = 0) : S.whole.hSharp.hom.app U a = 0 := by
  obtain ⟨b, hb⟩ := S.whole.second.exists_ideal_section U a ha
  have hb' : S.whole.inclTwo U b = a := hb
  have hzero : S.whole.idealMap.val.app U b = 0 := by
    rw [S.isComplex_iff_whole_idealMap_eq_zero.1 hS]
    rfl
  change S.whole.ringMapH.hom.app U a = 0
  calc S.whole.ringMapH.hom.app U a
      = S.whole.ringMapH.hom.app U (S.whole.inclTwo U b) := by rw [hb']
    _ = S.whole.inclOne U (S.whole.idealMap.val.app U b) := (S.whole.inclOne_idealMap U b).symm
    _ = S.whole.inclOne U 0 := by rw [hzero]
    _ = 0 := map_zero (S.whole.first.incl.val.app U).hom

/-- **Stacks 08ML.** The canonical map `O ⟶ O'₁` attached to a complex of first order
thickenings: the unique map through which the composite `O'₃ ⟶ O'₁` factors. -/
noncomputable def splitting : (pushforwardCommRingFunctor i.toToposHom).obj X.O ⟶ Y.O :=
  ⟨(Stacks.Sites.existsUnique_commRingFactor S.fSharp₃.hom S.whole.hSharp.hom S.third.surjective
    (Stacks.Sites.isSheaf_comp_forget_commRingCat Y.O.property)
    (S.whole_hSharp_apply_eq_zero hS)).choose⟩

/-- **Stacks 08ML.** For a complex of first order thickenings, the composition
`(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` factors through `(Sh(C), O) ⟶ (Sh(D₃), O'₃)`: on structure
sheaves, the composite `O'₃ ⟶ O'₁` is `O'₃ ⟶ O ⟶ O'₁`. -/
@[stacks 08ML "the composition D₁ ⟶ D₃ factors through the base"]
theorem fSharp₃_comp_splitting : S.fSharp₃ ≫ S.splitting hS = S.whole.hSharp :=
  Sheaf.hom_ext
    (Stacks.Sites.existsUnique_commRingFactor S.fSharp₃.hom S.whole.hSharp.hom S.third.surjective
      (Stacks.Sites.isSheaf_comp_forget_commRingCat Y.O.property)
      (S.whole_hSharp_apply_eq_zero hS)).choose_spec.1

/-- Two maps out of `O` into a sheaf of commutative rings agree when their composites with the
locally surjective map `O'₃ ⟶ O` agree. -/
private theorem hom_ext_of_fSharp₃_comp (F : Sheaf Y.J CommRingCat.{w'})
    {t t' : baseRing i ⟶ F} (h : S.fSharp₃ ≫ t = S.fSharp₃ ≫ t') : t = t' :=
  Sheaf.hom_ext (Stacks.Sites.commRingHom_ext_of_isLocallySurjective S.fSharp₃.hom
    S.third.surjective (Stacks.Sites.isSheaf_comp_forget_commRingCat F.property)
    (congrArg (fun m : S.O₃ ⟶ F => m.hom) h))

/-- The factorization is unique: the canonical map is the only map `O ⟶ O'₁` whose composite
with `O'₃ ⟶ O` is the composite `O'₃ ⟶ O'₁`. This is what makes the trivialization below
canonical. -/
theorem splitting_unique (t : baseRing i ⟶ Y.O) (ht : S.fSharp₃ ≫ t = S.whole.hSharp) :
    t = S.splitting hS :=
  hom_ext_of_fSharp₃_comp S Y.O (ht.trans (S.fSharp₃_comp_splitting hS).symm)

/-- The factorizing map is a section of the structure map of the smallest thickening: composing
it with `O'₁ ⟶ O` gives the identity, because `O'₃ ⟶ O` is locally surjective and the two
composites with it agree. -/
theorem splitting_comp_fSharp : S.splitting hS ≫ i.fSharp = 𝟙 (baseRing i) :=
  hom_ext_of_fSharp₃_comp S _ (by
    rw [← Category.assoc, S.fSharp₃_comp_splitting hS, Category.comp_id]
    exact S.whole.comm)

/-- **Stacks 08ML.** The canonical trivialization `π : (Sh(D₁), O'₁) ⟶ (Sh(C), O)` of the
smallest thickening of a complex of first order thickenings. -/
@[stacks 08ML "the canonical trivialization of the smallest thickening"]
noncomputable def trivialization : Trivialization i :=
  trivializationOfBaseSplitting i S.first.equiv (S.splitting hS) (S.splitting_comp_fSharp hS)

/-- **Stacks 08ML.** The smallest thickening of a complex of first order thickenings is a
trivial first order thickening of the base. -/
@[stacks 08ML "the smallest thickening of a complex is trivial"]
theorem isTrivial (S : FirstOrderThickeningComplex i) (hS : S.IsComplex) : IsTrivial i :=
  ⟨S.trivialization hS⟩

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
