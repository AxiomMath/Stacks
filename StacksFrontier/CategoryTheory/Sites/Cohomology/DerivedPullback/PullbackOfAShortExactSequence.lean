module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackShortExactFlat
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0G6R at the source's presentation of a morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let

`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`

be a short exact sequence of sheaves of `O_D`-modules whose final term `F₃` is **flat**.
**Stacks 0G6R** asserts that `0 ⟶ f^*F₁ ⟶ f^*F₂ ⟶ f^*F₃ ⟶ 0` is again short exact, the pullback
being the one of Stacks 03D6 part (2), `f^* = O_C ⊗_{f⁻¹O_D} f⁻¹(-)`.

## Main results

* `AlgebraicGeometry.RingedToposHom.exists_shortExact_map_pullbackModules`: **Stacks 0G6R** with
  the composite-is-zero witness carried in the statement, so that the statement does not mention
  preservation of zero morphisms by the pullback.  This is the form the source's statement takes
  and it carries the tag.

## Implementation notes

*Why the witness is existentially quantified.*  `CategoryTheory.ShortComplex.map` asks the
functor to preserve zero morphisms, so the `ShortComplex.map` form of the conclusion —
`Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules`, which is what this is one
application of — mentions a property of `pullbackModules` that is not part of that functor's
public interface.  Pairing the pullback of the two maps with a proof that they compose to zero
states the same thing without it, and the witness supplied is exactly
`(S.map (pullbackModules f)).zero`, so the two forms are the same short complex.

*Universes.*  The two ringed topoi are at the shape inherited from
`Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules`, which is in turn forced by
the inverse-image half of Stacks 05VD: writing `RingedTopos.{v₁, u₁, w₁}` for morphisms, objects
and sections, the target is `RingedTopos.{v', u', max u' v'}` and the source is
`RingedTopos.{v, max u v, max u v}`.  The source's site is therefore small in the universe of its
sections and the target's section universe is the max of its object and morphism universes, which
is what the tag string below discloses.

## References

* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u v' u'

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, max u v, max u v}} {Y : RingedTopos.{v', u', max u' v'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u' v'} RingCat.{max u' v'})]
  [X.J.HasSheafCompose (forget RingCat.{max u v})]
  [Y.J.HasSheafCompose (forget RingCat.{max u' v'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max u' v'})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  (f : RingedToposHom X Y)
  (S : ShortComplex (SheafOfModules.{max u' v'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- **Stacks Project, Tag 0G6R.**  For a morphism of ringed topoi
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and a short exact sequence of sheaves of `O_D`-modules
whose final term is flat, the pullback sequence `0 ⟶ f^*F₁ ⟶ f^*F₂ ⟶ f^*F₃ ⟶ 0` is short exact.

The pullback is the one of Stacks 03D6 part (2), `O_C ⊗_{f⁻¹O_D} f⁻¹(-)`.  The composite-is-zero
witness is carried in the statement, so that the statement does not mention preservation of zero
morphisms by the pullback, which is not part of that functor's public interface. -/
@[stacks 0G6R "morphisms of ringed topoi, with the source ringed topos's site small in the
universe of its sections and the target's section universe equal to the max of its object and
morphism universes", ega "IV 2.1.8" "(i), G' = O_{Y'}"]
theorem exists_shortExact_map_pullbackModules (hS : S.ShortExact)
    (hflat : Stacks.SheafOfModules.IsFlat (O := Y.O) S.X₃) :
    ∃ h : (f.pullbackModules).map S.f ≫ (f.pullbackModules).map S.g = 0,
      (ShortComplex.mk ((f.pullbackModules).map S.f)
        ((f.pullbackModules).map S.g) h).ShortExact :=
  ⟨(S.map (f.pullbackModules)).zero, shortExact_map_pullbackModules f S hS hflat⟩

end AlgebraicGeometry.RingedToposHom

end
