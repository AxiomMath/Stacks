module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAffineTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine

/-!
# Changing the base along an open immersion, and Tag 08E7 at an object of `D(R)`

Tor amplitude over the base, `AlgebraicGeometry.HasTorAmplitudeOver`, is unchanged when the base
morphism is composed with an open immersion of the target, and not merely with an isomorphism:
the predicate is read on the germs, and the germ maps of an open immersion are isomorphisms. The
affine case of Stacks 0DI7 meets Tor amplitude over the composite `V₀.ι ≫ X₀ ⟶ S₀`, which
factors as the restriction `(X₀ ⟶ S₀).resLE W₀ V₀` of the structure morphism followed by the
inclusion of the affine open `W₀` of the base; that inclusion is an open immersion, so the
statement for an isomorphism does not reach it.

Stacks 08E7 is proved for a cochain complex of modules over a ring presented as
`CommRingCat.of A`; what consumes it there is an object of `D(R)` for a variable
`R : CommRingCat`, with the sheaf side read on the derived sheafification of the object rather
than on the degreewise sheafification of a complex. The passage between the two is the canonical
complex representing the object.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_comp_iff_of_isOpenImmersion`: Tor amplitude over the
  base is unchanged by composing the base morphism with an open immersion of the target.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTilde_iff`: Tag 08E7 for an object of
  `D(R)` and its derived sheafification on `Spec R`.

## Implementation notes

`AlgebraicGeometry.hasTorAmplitudeOver_comp_iff`, the same biconditional for an isomorphism of
the target, is a special case of the first statement here, since an isomorphism is an open
immersion. The two are a supersede-and-dedup pair, not independent results.

No direction of the biconditional is lost in the generalisation. Its germ-level content is
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff`, which is a
biconditional in the ring isomorphism and not in the morphism of schemes; an open immersion
supplies that ring isomorphism through
`AlgebraicGeometry.stalkRingEquivOfIsOpenImmersion`, exactly as an isomorphism does through
`CategoryTheory.asIso`. The germ-level statement takes the three germ maps abstractly with the
factorisation as a hypothesis, because `(f ≫ d).base x` and `d.base (f.base x)` are
definitionally but not reducibly equal, so the `Preadditive` instance arguments of a goal naming
both spellings of the base ring do not match; `Stacks.ModuleSkyscraper.stalkMap_hom_comp` supplies
the factorisation at the application.

The derived sheafification in the second statement is written
`(AlgebraicGeometry.tilde.functor R).mapDerivedCategory.obj`, which is definitionally
`AlgebraicGeometry.derivedTildeObj R`, so a consumer phrased with that abbreviation can use the
statement without importing the module carrying it. Both spellings keep the ring a variable,
which is what instance search for the typeclasses of `AlgebraicGeometry.tilde.functor` needs:
those are stated for a variable `R : CommRingCat`, whose coercion has head
`CommRingCat.carrier`, while `↑(CommRingCat.of A)` reduces to `A` and the discrimination tree
then reports no instances at all.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
-/

@[expose] public noncomputable section

open CategoryTheory
open StacksDraft.TorAmplitude

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Changing the base along an open immersion -/

/-- **Tor amplitude over the base is unchanged by composing the base morphism with an open
immersion.** The representing complex is the same on both sides; only the ring over which its
germ complexes are read changes, by the germ isomorphism of the open immersion. This generalises
`AlgebraicGeometry.hasTorAmplitudeOver_comp_iff`, which is the case of an isomorphism. -/
public theorem hasTorAmplitudeOver_comp_iff_of_isOpenImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (d : Y ⟶ Z) [IsOpenImmersion d] (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver (f ≫ d) E a b ↔ HasTorAmplitudeOver f E a b := by
  have key : ∀ (K : CochainComplex X.Modules ℤ) (x : X),
      HasTorAmplitudeCanonicalLift.{u, u, u}
          (DerivedCategory.Q.obj (relativeStalkComplex (f ≫ d) K x)) a b ↔
        HasTorAmplitudeCanonicalLift.{u, u, u}
          (DerivedCategory.Q.obj (relativeStalkComplex f K x)) a b := fun K x =>
    hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff (f.stalkMap x).hom
      (d.stalkMap (f.base x)).hom ((f ≫ d).stalkMap x).hom
      (stalkRingEquivOfIsOpenImmersion d (f.base x)) rfl
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp f d x) _ a b
  exact ⟨fun ⟨K, hK, h⟩ => ⟨K, hK, fun x => (key K x).1 (h x)⟩,
    fun ⟨K, hK, h⟩ => ⟨K, hK, fun x => (key K x).2 (h x)⟩⟩

/-! ### Tag 08E7 at an object of the derived category of a ring -/

namespace RingedSpace

/-- **Tag 08E7 at an object of `D(R)`.** An object of `D(R)` is pseudo-coherent exactly when its
derived sheafification on `Spec R` is, for `R` a variable object of `CommRingCat`. The left-hand
side is definitionally `AlgebraicGeometry.derivedTildeObj R L`. -/
public theorem isPseudoCoherent_derivedTilde_iff (R : CommRingCat.{u})
    (L : DerivedCategory (ModuleCat.{u} R)) :
    IsPseudoCoherent (X := (Spec R).toRingedSpace)
        ((tilde.functor R).mapDerivedCategory.obj L) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent L := by
  obtain ⟨M, eQ⟩ : Σ' M : CochainComplex (ModuleCat.{u} R) ℤ,
      DerivedCategory.Q.obj M ≅ L :=
    ⟨DerivedCategory.Q.objPreimage L, DerivedCategory.Q.objObjPreimageIso L⟩
  have eT : (tilde.functor R).mapDerivedCategory.obj L ≅
      DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
    (tilde.functor R).mapDerivedCategory.mapIso eQ.symm ≪≫
      (tilde.functor R).mapDerivedCategoryFactors.app M
  refine Iff.trans ⟨fun h => h.of_iso eT, fun h => h.of_iso eT.symm⟩
    (Iff.trans (isPseudoCoherent_tilde_iff M) ?_)
  exact ⟨fun h => h.ofIso eQ, fun h => h.ofIso eQ.symm⟩

end RingedSpace

end AlgebraicGeometry

end
