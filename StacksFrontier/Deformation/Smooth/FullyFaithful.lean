module

public import StacksFrontier.Deformation.BaseCategory.Pi
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.Deformation.Smooth.EssentiallySurjective
public import StacksFrontier.Deformation.Smooth.Pi

/-!
# Cancelling a fully faithful factor out of a composite

The chain of **Stacks 0DZF** is proved one leg at a time and then read off the composite, so
every step needs a two-out-of-three cancellation: a conclusion established for a composite
`F ⋙ G` has to descend to its first factor `F`. This is exactly what full faithfulness of the
second factor buys. If `G` is fully faithful then a lifting problem for `F` can be pushed
forward along `G`, solved there by smoothness of the composite, and pulled back again, because
`G` has a two-sided inverse on morphisms; the same argument, run on the fibres over a fixed
base object, shows that `F` is injective on fibrewise isomorphism classes. The two statements
are the ones a leg of the chain is extracted with.

The other tools gathered here are of the same structural kind. Reindexing a product over the
base along an equivalence of index types is a fully faithful based functor, which is how the
chain's products indexed by one finite family are compared with the same products indexed by
another; a smooth morphism of predeformation categories is essentially surjective, which is
the hypothesis the dual cancellation `Deformation.isSmooth_of_essSurj_comp` asks for; and a
morphism of categories over a base is determined by its underlying functor, which is what lets
an identification of underlying functors be used as an identification of based functors.

## Main results

* `Deformation.isSmooth_of_comp_fullyFaithful`: if `BasedFunctor.comp F G` is smooth and `G` is
  fully faithful, then `F` is smooth.
* `Deformation.essSurj_of_isSmooth`: a smooth morphism of predeformation categories is
  essentially surjective.
* `Deformation.basedFunctor_ext_of_toFunctor_eq`: a morphism of categories over a base is
  determined by its underlying functor.

## Implementation notes

The companion statement that a fully faithful morphism of categories over a base is *injective*
on fibrewise isomorphism classes is not proved here: it already exists as
`Deformation.mapIsomorphismClasses_injective` in
`StacksFrontier/Deformation/Examples/Linear/ContinuousRepresentationsDenseRestriction.lean`, at the
same generality, and consumers import it from there rather than carrying a second copy.

`Deformation.basedFunctor_ext_of_toFunctor_eq` is named for its hypothesis rather than
`basedFunctor_ext` because the repository already carries two declarations of the latter name at
narrower universe shapes, neither of which applies to two based categories living in different
universes.

## References

* [Stacks Project, Tag 0DZF](https://stacks.math.columbia.edu/tag/0DZF)
* [Stacks Project, Tag 06HG](https://stacks.math.columbia.edu/tag/06HG)
* [Stacks Project, Tag 06HN](https://stacks.math.columbia.edu/tag/06HN)
* [Stacks Project, Tag 07W5](https://stacks.math.columbia.edu/tag/07W5)
-/

@[expose] public section

open CategoryTheory

universe uι u v w v₁ u₁ v₂ u₂ v₃ u₃

namespace Deformation

/-! ### Extensionality for morphisms of categories over a base -/

/-- **A morphism of categories over a base is determined by its underlying functor.** The
compatibility of a based functor with the two structure functors is a proposition, so two based
functors with the same underlying functor are equal. -/
public theorem basedFunctor_ext_of_toFunctor_eq
    {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝓕 : BasedCategory.{v₂, u₂} 𝒮} {𝓖 : BasedCategory.{v₃, u₃} 𝒮}
    {φ ψ : BasedFunctor 𝓕 𝓖} (h : φ.toFunctor = ψ.toFunctor) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-! ### Cancelling a fully faithful second factor -/

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Smoothness of a composite descends to its first factor along a fully faithful second
factor.** A lifting problem for `F` is carried to one for `BasedFunctor.comp F G` by applying
`G`, solved there, and carried back: fullness produces the required morphism in the source of
`G` and faithfulness makes it satisfy the compatibility the lifting problem asks for. -/
public theorem isSmooth_of_comp_fullyFaithful
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (F : BasedFunctor 𝓕 𝓖) (G : BasedFunctor 𝓖 𝓗)
    [G.toFunctor.Full] [G.toFunctor.Faithful]
    (h : IsSmooth (BasedFunctor.comp F G)) : IsSmooth F := by
  intro B A f hf y x g hg
  obtain ⟨x', t, a, ht, ha, he⟩ :=
    h f hf (G.obj y) x (G.map g) ((G.isHomLift_iff f g).mpr hg)
  let a' := G.toFunctor.preimage a
  have hmap : G.map a' = a := G.toFunctor.map_preimage a
  have ha' : 𝓖.p.IsHomLift (𝟙 B) a' :=
    (G.isHomLift_iff (𝟙 B) a').mp (hmap.symm ▸ ha)
  refine ⟨x', t, a', ht, ha', ?_⟩
  apply G.toFunctor.map_injective
  rwa [G.map_comp, hmap]

/-- **A smooth morphism of predeformation categories is essentially surjective.** The fibre over
the residue field is a one-object one-morphism category on both sides, so the induced functor of
special fibres is essentially surjective, and
`Deformation.essSurj_of_isSmooth_of_fiber_essSurj` promotes that to the whole functor. -/
public theorem essSurj_of_isSmooth
    {𝓕 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (h𝓖 : IsPredeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖) (hφ : IsSmooth φ) :
    φ.toFunctor.EssSurj := by
  apply essSurj_of_isSmooth_of_fiber_essSurj φ h𝓖.cofibered hφ
  obtain ⟨eF⟩ := h𝓕.specialFiber
  obtain ⟨eG⟩ := h𝓖.specialFiber
  exact ⟨fun _ => ⟨eF.inverse.obj ⟨PUnit.unit⟩,
    ⟨eG.functor.preimageIso (eqToIso (Subsingleton.elim _ _))⟩⟩⟩

end Deformation
