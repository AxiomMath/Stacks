module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.Deformation.ToposThickening.StrictIdealProduct

/-!
# The two readings of `f⁻¹J` inside `O'` agree

Let

```
  (Sh(C), O)  --i-->  (Sh(D), O')
      |                   |
      f                   f'
      v                   v
  (Sh(B), O_B) --t--> (Sh(B'), O_{B'})
```

be a morphism of thickenings of ringed topoi (Stacks 08M7), with defining ideals
`I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`. Situation 08M7 produces a map
`f⁻¹J ⟶ I ⊂ O'` in two different ways, and the library carries both:

* through the pullback, as the canonical map `f⁻¹J ⟶ (f')^*J` of
  `Deformation.ToposThickening.MorphismOfThickenings.inverseImageIdealUnit` — the unit of the
  extension of scalars — followed by
  `Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealToStructure`, which is built
  from the comparison `(f')^*O_{B'} ⟶ O'` of Stacks 03LU;
* directly, as the inverse image of the inclusion `J ⟶ O_{B'}` followed by the inverse-image
  form `(f')^♯ : f⁻¹O_{B'} ⟶ O'` of the structure map, read on unit modules.

This file proves the two are the same map. It is the identification the source performs silently
when it writes `(f')^♯(j)` for the image in `O'` of a local section `j` of `f⁻¹J`.

## Main results

* `MorphismOfThickenings.inverseImageIdealUnit_comp_pullbackIdealToStructure`: the two readings
  of `f⁻¹J ⟶ O'` agree.

## The engine

The map through the pullback is, by the definition of the adjunction bijection, the transpose
along the adjunction of Stacks 03CZ of `(f')^*J ⟶ O'`; and `(f')^*J ⟶ O'` is the extension of
scalars of the inverse image of the inclusion of `J`, followed by the comparison of Stacks 03LU.
Naturality of that bijection in its left variable
(`CategoryTheory.Adjunction.homEquiv_naturality_left`) therefore strips the inclusion of `J` off
both sides, and what remains is a statement about the *unit module* alone: the transpose of the
comparison `(f')^*O_{B'} ⟶ O'` is the inverse-image form of the structure map. That is
`AlgebraicGeometry.RingedToposHom.fSharpAdjunction_homEquiv_pullbackUnitStructureMap`, proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackUnitValue.lean` from the
corepresentability description of Stacks 03LU: both sides send the unit section of `f⁻¹O_{B'}` to
the unit section of `O'`.

Transposing along Stacks 03D7, as
`Deformation.ToposThickening.MorphismOfThickenings.homEquiv_idealMap_comp_incl` does, is not
enough here: that bijection lands on the *lower* topos, whereas `f⁻¹J` lives on the upper one.
Only the extension-of-scalars half of the pullback may be transposed if the inverse image is to
be left standing.

## Implementation notes

The identification `f⁻¹1_{O_{B'}} = 1_{f⁻¹O_{B'}}` of
`Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` is written out rather than left to
definitional unfolding. It is `Iso.refl`, so the two objects *are* definitionally equal, but the
unifier does not find that equality cheaply at these arguments — a goal that asks it to is the
one place in this development that exhausts the heartbeat budget. Naming the isomorphism keeps
every composite on one side of the seam, and is the discipline
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposPullbackUnitValue.lean` prescribes.

The four topoi keep independent universes for their sections, and the only sheafification
hypotheses are those of the pullback of sheaves of modules on the upper right topos, where the
extension of scalars happens; the statement adds none.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedToposHom (pullbackUnitStructureMap)
open Stacks.Sheaves.ToposPullback (pullbackModuleUnitIso)
open Stacks.Sheaves.RingedToposModules (inverseImageModules fSharpAdjunction)
open Stacks.SheafOfModules.ChangeOfRings (unitToRestrictScalarsUnit)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

namespace Deformation.ToposThickening.MorphismOfThickenings

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

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{w''})] in
/-- **The two readings of the map `f⁻¹J ⟶ O'` of Situation 08M7 agree.** The canonical map
`f⁻¹J ⟶ (f')^*J` followed by `(f')^*J ⟶ O'` is the inverse image of the inclusion `J ⟶ O_{B'}`
followed by the inverse-image form `(f')^♯ : f⁻¹O_{B'} ⟶ O'` of the structure map, read on unit
modules through the identity `f⁻¹1_{O_{B'}} = 1_{f⁻¹O_{B'}}`.

Both sides are morphisms of sheaves of `f⁻¹O_{B'}`-modules out of `f⁻¹J`, the target `O'` being
read as an `f⁻¹O_{B'}`-module by restriction of scalars along `(f')^♯`; that restriction is what
makes the comparison possible at all, the left-hand side being a priori a statement about
`O'`-modules.

The sections of the common value are the family
`Deformation.ToposThickening.MorphismOfThickenings.inverseImageIdealSections`, which the source
writes `(f')^♯(j)`; this identifies them with the images of the sections of `J` under `(f')^♯`,
and so connects the submodule `(f^{-1}J)F'` of
`Deformation.ToposThickening.MorphismOfThickenings.pullbackIdealProduct` with the structure map
it is named after. -/
theorem inverseImageIdealUnit_comp_pullbackIdealToStructure :
    D.inverseImageIdealUnit ≫
        (SheafOfModules.restrictScalars D.inverseImageStructureRingMap).map
          D.pullbackIdealToStructure =
      (inverseImageModules D.f'.toModulesHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
          D.idealJ.incl ≫
        (pullbackModuleUnitIso X'.J D.f'.toToposHom.inverseImage
          (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).inv ≫
          unitToRestrictScalarsUnit D.inverseImageStructureRingMap := by
  refine ((fSharpAdjunction D.f'.toModulesHom).homEquiv_naturality_left
    ((inverseImageModules D.f'.toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
      D.idealJ.incl) (pullbackUnitStructureMap D.f')).trans ?_
  exact congrArg (fun m ↦ (inverseImageModules D.f'.toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map D.idealJ.incl ≫ m)
    (RingedToposHom.fSharpAdjunction_homEquiv_pullbackUnitStructureMap D.f')

end Deformation.ToposThickening.MorphismOfThickenings

end
