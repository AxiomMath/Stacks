module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction

/-!
# The two factors of the canonical map of Stacks 08MQ

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, let `ℱ'` be an
`O'`-module and set `ℱ = i^*ℱ'`. Stacks 08MQ states, for a strict `(f, f')` and `ℱ` flat over
`O_ℬ`, that `ℱ'` is flat over `O_{ℬ'}` if and only if the canonical map

`f^*J ⊗_O ℱ ⟶ I·ℱ'`

is an isomorphism, and that in that case both factors of its factorisation

`f^*J ⊗_O ℱ ⟶ I ⊗_O ℱ ⟶ I·ℱ'`

are isomorphisms.

This file proves the opening sentence of the source's proof and the "moreover" clause that
sentence discharges: *the map `f^*J ⟶ I` is surjective as `(f, f')` is a strict morphism of
thickenings, hence the final statement is a consequence of (2).*

## Main results

* `Deformation.ToposThickening.epi_idealTensorComparison`: **the first factor is always
  surjective for a strict square.** The first factor is
  `Deformation.ToposThickening.idealTensorComparison`, the induced map of defining ideals
  `f^*J ⟶ I` of Stacks 08M7 tensored with `ℱ`; strictness of the square is surjectivity of that
  map of ideals, and the tensor product is right exact.
* `Deformation.ToposThickening.isIso_idealTensorComparison_of_isIso_comp` and
  `Deformation.ToposThickening.isIso_of_isIso_idealTensorComparison_comp`: **granting clause (2)
  of Stacks 08MQ, both factors are isomorphisms.** Clause (2) is the invertibility of the
  composite of the first factor with the second; the second factor is left as a parameter, so
  that the statement applies to whichever presentation of the multiplication map
  `I ⊗_O ℱ ⟶ I·ℱ'` the caller has in hand.

## Implementation notes

The second factor is a parameter rather than a fixed map. The source's second factor is
multiplication `I ⊗_O ℱ ⟶ I·ℱ'`, which the library carries in two inequivalent spellings — as
`Deformation.ToposThickening.extensionActionMap` of Stacks 08MB, formed over the reduced
structure sheaf `i_*O`, and as `Stacks.SheafOfModules.FlatSquareZero.multiplicationMap` of
Stacks 08M4, formed over `O'` — and the comparison of the two tensor products
`- ⊗_{i_*O} -` and `- ⊗_{O'} -` on modules annihilated by `I` is not in the library. Taking the
second factor as a parameter makes the deduction available to both spellings without choosing
one, and it is the whole content of the source's sentence: nothing about the second factor is
used beyond its being the cofactor of an invertible composite.

The argument is the standard one. The first factor is surjective, so if the composite is
invertible the first factor is a monomorphism as well, hence invertible in an abelian category;
the second factor is then the composite of the inverse of the first with the invertible
composite.

## Scope

**This file does not prove Stacks 08MQ**; the tag is proved, and registered, in
`StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessEquivalence`, as
`Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap`. What this file leaves aside is the
equivalence of clauses (1) and (2), the part of the tag resting on Modules on Sites,
Stacks 08M4, and it does not discharge the hypotheses
`Deformation.ToposThickening.IsFlatLiftCorrespondence`,
`Deformation.ToposThickening.IsFlatLiftClassCorrespondence` or
`Deformation.ToposThickening.IsIdealProductTensorIso`: each of those needs clause (2) produced
from flatness, which is exactly the direction this file does not supply.

`Deformation.ToposThickening.IsIdealComparisonIsoOfFlat` was in that list and is no longer: it
is proved, without Stacks 08MQ, by
`Deformation.ToposThickening.isIdealComparisonIsoOfFlat`.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS'

namespace Stacks.SheafOfModules

/-- **Tensoring with a flat sheaf of modules preserves monomorphisms.** Flatness is exactness of
the tensor functor, and a functor preserving finite limits preserves monomorphisms.

`Stacks.SheafOfModules.FlatSquareZero.flat_tensor_preserves_mono` is the same statement, but it
is private to
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening`; this is the form
available to a caller. It is the first step of the route to clause (2) of Stacks 08MQ: applied
to the inclusion `f⁻¹𝒥 ⟶ f⁻¹O_{ℬ'}` and to an `f⁻¹O_{ℬ'}`-module `ℱ'` flat over `f⁻¹O_{ℬ'}`, it
gives the injectivity of multiplication `f⁻¹𝒥 ⊗ ℱ' ⟶ ℱ'`. -/
theorem mono_sheafTensorRight_map_of_isFlat {C : Type u} [CategoryTheory.Category.{v} C]
    {J : CategoryTheory.GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {O : Sheaf J CommRingCat.{w}}
    {G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat G)
    {A B : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (α : A ⟶ B)
    [Mono α] :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G).map α) := by
  let : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G) := hG.1
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  infer_instance

end Stacks.SheafOfModules

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
  (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)
  (F : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

/-- **Stacks 08MQ, the opening sentence of the proof.** For a strict morphism of first order
thickenings the first factor `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` of the canonical map is surjective: strictness
is surjectivity of the induced map of defining ideals `f^*J ⟶ I` of Stacks 08M7, and tensoring
with `ℱ` is right exact. -/
theorem epi_idealTensorComparison
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    Epi (idealTensorComparison i t f f' hi ht comm F) := by
  let : Epi (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap :=
    hstrict
  let : PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
      ((structureRestrict i).obj F)) :=
    Stacks.SheafOfModules.FlatSquareZero.tensorRight_preservesFiniteColimits X'.O _
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
      ((structureRestrict i).obj F)).PreservesEpimorphisms :=
    CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
  exact inferInstanceAs (Epi (((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
    ((structureRestrict i).obj F)).map
      (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap))

variable [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **Stacks 08MQ, the first half of the final statement.** For a strict morphism of first order
thickenings, if the canonical map of clause (2) — the composite of the first factor
`f^*J ⊗ ℱ ⟶ I ⊗ ℱ` with multiplication `I ⊗ ℱ ⟶ I·ℱ'` — is an isomorphism, then the first
factor is one.

The second factor is a parameter; see the implementation notes. -/
theorem isIso_idealTensorComparison_of_isIso_comp
    {P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    (β : ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
          ((structureRestrict i).obj F)).obj
        hi.idealOfThickening.I ⟶ P)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hiso : IsIso (idealTensorComparison i t f f' hi ht comm F ≫ β)) :
    IsIso (idealTensorComparison i t f f' hi ht comm F) := by
  let : Epi (idealTensorComparison i t f f' hi ht comm F) :=
    epi_idealTensorComparison i t f f' hi ht comm F hstrict
  let := hiso
  let : Mono (idealTensorComparison i t f f' hi ht comm F ≫ β) := inferInstance
  let : Mono (idealTensorComparison i t f f' hi ht comm F) :=
    mono_of_mono (idealTensorComparison i t f f' hi ht comm F) β
  exact isIso_of_mono_of_epi _

/-- **Stacks 08MQ, the second half of the final statement.** For a strict morphism of first order
thickenings, if the canonical map of clause (2) is an isomorphism then so is its second factor,
multiplication `I ⊗ ℱ ⟶ I·ℱ'`: the first factor is invertible by
`Deformation.ToposThickening.isIso_idealTensorComparison_of_isIso_comp`, and the second factor
is the composite of its inverse with the canonical map. -/
theorem isIso_of_isIso_idealTensorComparison_comp
    {P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    (β : ((Stacks.SheafOfModules.Tensor.sheafTensor X'.O).flip.obj
          ((structureRestrict i).obj F)).obj
        hi.idealOfThickening.I ⟶ P)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hiso : IsIso (idealTensorComparison i t f f' hi ht comm F ≫ β)) :
    IsIso β := by
  let := hiso
  let : IsIso (idealTensorComparison i t f f' hi ht comm F) :=
    isIso_idealTensorComparison_of_isIso_comp i t f f' hi ht comm F β hstrict hiso
  have h : inv (idealTensorComparison i t f f' hi ht comm F) ≫
      (idealTensorComparison i t f f' hi ht comm F ≫ β) = β := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [← h]
  infer_instance

end Deformation.ToposThickening

end
