module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedToposPullbackLeftExact
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickeningsIdealMap

/-!
# The induced map of defining ideals of a strict morphism of thickenings with flat vertical arrow

Let

```
  (Sh(C), O)  --i-->  (Sh(D), O')
      |                   |
      f                   f'
      v                   v
  (Sh(B), O_B) --t--> (Sh(B'), O_{B'})
```

be a morphism of thickenings of ringed topoi (Stacks 08M7), with defining ideals
`I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`. When `f'` is flat and the square is strict in
the sense of Stacks 08M9, the induced map of defining ideals

`(f')^*J ⟶ I`

is an isomorphism. This is the remark `I = f^*J` that the Stacks project makes when setting up
Situation 08VV, and it is the statement that Stacks 08MQ, applied to `O'` itself, delivers.

## The argument

Strictness *is* surjectivity of the map, so only injectivity is at issue, and that is Stacks
04JC rather than Stacks 08MQ:

* the map `(f')^*J ⟶ O'` whose factorisation through `I` the map of ideals is
  (`Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealToStructure`) is
  `(f')^*` of the inclusion `J ⟶ O_{B'}` followed by the comparison
  `(f')^*O_{B'} ⟶ O'` of Stacks 03LU;
* the inclusion of a defining ideal is injective on sections, hence a monomorphism
  (`Deformation.ToposThickening.IdealOfThickening.mono_incl`), and `(f')^*` preserves
  monomorphisms because it is left exact for a flat `f'`, which is
  `AlgebraicGeometry.RingedToposHom.toModulesHom_pullbackModules_preservesFiniteLimits_of_isFlat`;
* the comparison of Stacks 03LU is an isomorphism
  (`AlgebraicGeometry.RingedToposHom.isIso_pullbackUnitStructureMap`);

so that composite is a monomorphism, and a map whose composite with the inclusion of `I` is a
monomorphism is one itself. Sheaves of modules over a sheaf of rings form an abelian category,
so monic and epic together give invertible.

## Main results

* `Deformation.ToposThickening.IdealOfThickening.mono_incl`: the inclusion of a defining ideal
  into the structure sheaf is a monomorphism.
* `Deformation.ToposThickening.MorphismOfThickenings.mono_idealMap`: the induced map of
  defining ideals is a monomorphism when the vertical arrow `f'` is flat.
* `Deformation.ToposThickening.MorphismOfThickenings.isIso_idealMap`: it is an isomorphism when
  moreover the square is strict.

## Implementation notes

No sheafification hypothesis is needed for the monomorphism statements beyond the ones the
pullback of sheaves of modules already carries; invertibility asks for `HasSheafify` on the
thickened upper site, which is what makes its category of sheaves of modules abelian and so lets
monic-and-epic be read as invertible.

Nothing here carries `@[stacks ...]`. The tags of the ingredients sit where they are proved:
Stacks 08M9 on `Deformation.ToposThickening.MorphismOfThickenings.IsStrict`, Stacks 04JC on
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`, Stacks 03LU on the unit
comparison.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08VV](https://stacks.math.columbia.edu/tag/08VV)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

namespace Deformation.ToposThickening

section Thickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- **The inclusion of a defining ideal into the structure sheaf is a monomorphism.** It is
injective on sections, and two morphisms into the ideal with the same composite into the
structure sheaf are therefore the same factorisation of that composite, which
`Stacks.SheafOfModules.existsUnique_factorThrough` says is unique. -/
theorem IdealOfThickening.mono_incl {i : RingedToposHom X Y} (hI : IdealOfThickening i) :
    Mono hI.incl where
  right_cancellation φ _ψ h :=
    (Stacks.SheafOfModules.existsUnique_factorThrough hI.incl hI.injective (φ ≫ hI.incl)
      fun U z ↦ ⟨φ.val.app U z, rfl⟩).unique rfl h.symm

end Thickening

namespace MorphismOfThickenings

section IdealMap

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w'}}
  {S : RingedTopos.{v'', u'', w''}} {S' : RingedTopos.{v''', u''', w'''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w'})]
  [S.J.HasSheafCompose (forget RingCat.{w''})] [S'.J.HasSheafCompose (forget RingCat.{w'''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w'''})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w'}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (D : MorphismOfThickenings X X' S S')

/-- **The induced map of defining ideals `(f')^*J ⟶ I` of a morphism of thickenings with flat
vertical arrow is a monomorphism.**

Its composite with the inclusion `I ⟶ O'` is
`Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealToStructure`, which is `(f')^*`
of the inclusion `J ⟶ O_{B'}` followed by the comparison `(f')^*O_{B'} ⟶ O'` of Stacks 03LU.
The first factor is a monomorphism because `(f')^*` is left exact for a flat `f'` and the
inclusion of a defining ideal is a monomorphism; the second is an isomorphism. -/
theorem mono_idealMap (hf' : D.f'.IsFlat) : Mono D.idealMap := by
  have hexact := D.f'.toModulesHom_pullbackModules_preservesFiniteLimits_of_isFlat hf'
  have hpres : (pullbackModules D.f'.toModulesHom).PreservesMonomorphisms := inferInstance
  have hJ : Mono ((pullbackModules D.f'.toModulesHom).map D.idealJ.incl) :=
    have := D.idealJ.mono_incl
    (pullbackModules D.f'.toModulesHom).map_mono _
  have hcomp : Mono D.pullbackIdealToStructure := mono_comp _ _
  rw [← D.idealMap_spec] at hcomp
  exact mono_of_mono D.idealMap D.idealI.incl

variable [HasSheafify X'.J AddCommGrpCat.{w'}]

/-- **The induced map of defining ideals `(f')^*J ⟶ I` of a strict morphism of thickenings with
flat vertical arrow is an isomorphism** — the remark `I = f^*J` of Situation 08VV.

Strictness is surjectivity of the map (Stacks 08M9), flatness of `f'` gives injectivity
(`Deformation.ToposThickening.MorphismOfThickenings.mono_idealMap`), and sheaves of modules form
an abelian category, where monic and epic together are invertible. -/
theorem isIso_idealMap (hf' : D.f'.IsFlat) (hstrict : D.IsStrict) : IsIso D.idealMap :=
  have := D.mono_idealMap hf'
  have : Epi D.idealMap := hstrict
  isIso_of_mono_of_epi D.idealMap

end IdealMap

end MorphismOfThickenings

end Deformation.ToposThickening

end
