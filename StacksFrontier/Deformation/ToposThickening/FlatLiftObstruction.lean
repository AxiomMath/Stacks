module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.IdealProduct
public import StacksFrontier.Deformation.ToposThickening.ShortExactFlatThickenings

/-!
# The obstruction to a flat lift of a module over a morphism of first order thickenings

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, and let `ℱ` be an
`O`-module flat over `O_ℬ`. A *flat lift* of `ℱ` is an `O'`-module `ℱ'` flat over `O_{ℬ'}` with
`i^*ℱ' ≅ ℱ`. For a strict `(f, f')` such a lift exists exactly when the canonical map
`f^*J ⊗_O ℱ ⟶ I ⊗_O ℱ` is an isomorphism and the obstruction class
`o(ℱ, I ⊗_O ℱ, 1) ∈ Ext²_O(ℱ, I ⊗_O ℱ)` of Stacks 08MF vanishes. When moreover `f'` is flat the
first condition is automatic, `I` being `f^*J`, and the vanishing of the class is the whole
criterion.

## Main definitions

* `Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrderThickenings`: the square of
  Stacks 08M7 determined by two first order thickenings in the sense of Stacks 08MB, so that its
  defining ideals are the square-zero ideals those thickenings name.
* `Deformation.ToposThickening.IsFlatOverBase`: `ℱ` is flat over `O_ℬ`, for `ℱ` presented on the
  thickened topos as a module over the direct image `i_*O` of the structure sheaf.
* `Deformation.ToposThickening.HasFlatLift`: `ℱ` admits a flat lift over the thickening.
* `Deformation.ToposThickening.idealTensorComparison`: the canonical map
  `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` of condition (1) of Stacks 08MV.
* `Deformation.ToposThickening.IsFlatLiftCorrespondence` and
  `Deformation.ToposThickening.IsIdealComparisonIsoOfFlat`: the two consequences of Stacks 08MQ
  that the proofs below consume. See the scope section.

## Main results

* `Deformation.ToposThickening.hasFlatLift_iff_isIso_and_obstruction_eq_zero`: **Stacks 08MV**,
  the two-condition criterion for the existence of a flat lift.
* `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero`: **Stacks 08VW, part (1)**,
  the criterion in the situation of Stacks 08VV, where `f'` is flat as well.

## Implementation notes

The square is built from two `Deformation.ToposThickening.FirstOrderThickening` structures of
Stacks 08MB rather than from the predicate
`Deformation.ToposThickening.IsFirstOrderThickening` of Stacks 08M7: the obstruction class of
Stacks 08MF is a construction on a thickening whose square-zero ideal is *named*, and only the
structure names it. The predicate is recovered from the structure by
`Deformation.ToposThickening.IsFirstOrderThickening.of_firstOrderThickening`, which is what
`Deformation.ToposThickening.MorphismOfThickenings.ofFirstOrder` asks for, and the defining
ideals of the resulting square are then the square-zero ideals of the two structures and not a
second copy of them. There is no converse bridge, so a square carrying only the predicate cannot
be used here.

Modules over `O` are presented on the thickened topos `Sh(D)` as modules over the direct image
`i_*O`, which is the presentation the extension theory of Stacks 08MB and Stacks 08MF uses: the
underlying topoi of a thickening are identified by it, and restriction of scalars along
`i^♯ : O' ⟶ i_*O` is the direct image of modules in that presentation. Three readings follow
from this.

* `i^*ℱ' ≅ ℱ` is read as `ℱ'/I·ℱ' ≅ i_*ℱ`, in the form of a short exact sequence
  `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0`. The ideal product `I·ℱ'` is
  `Deformation.ToposThickening.idealProductSubmodule`, and that `ℱ'/I·ℱ'` is `i^*ℱ'` is
  `Deformation.ToposThickening.idealProductShortComplex_shortExact` in
  `StacksFrontier/Deformation/ToposThickening/IdealProductSequence.lean`, which identifies the
  cokernel of `I·ℱ' ⟶ ℱ'` with `i_*i^*ℱ'`.
* Flatness of `ℱ` over `O_ℬ` is flatness of `ℱ` for its `i_*f⁻¹O_ℬ`-module structure, the
  structure map `f⁻¹O_ℬ ⟶ O` being carried along the direct image of sheaves of rings. The same
  condition for an `O`-module presented on `Sh(C)` is
  `Deformation.ToposThickening.FlatThickeningMorphismSituation.F_isFlat`; the two agree, the
  direct image along `i` being an equivalence on the categories of modules in question.
* The canonical map of condition (1) of Stacks 08MV is formed on `Sh(D)`, as
  `(f')^*J ⊗_{O'} i_*ℱ ⟶ I ⊗_{O'} i_*ℱ`, from the induced map of defining ideals
  `Deformation.ToposThickening.MorphismOfThickenings.idealMap` of Stacks 08M7. Both ideals are
  annihilated by `I` when the square is strict, hence are direct images of `O`-modules, and the
  direct image is monoidal on such modules, so this is the source's
  `f^*J ⊗_O ℱ ⟶ I ⊗_O ℱ`.

The two upper ringed topoi share their section universe, as they must: the ideal product is
`Deformation.ToposThickening.idealProductSubmodule`, which is stated for a first order
thickening whose source and target share theirs. The two base topoi keep independent section
universes, and all four sites keep independent universes.

## Scope

Stacks 08MQ — the characterization of the `O'`-modules flat over `O_{ℬ'}` — is not in the
library at the time of writing; it is being formalized elsewhere and is not duplicated here.
Both results below therefore carry the consequence of it that their proof consumes as an
explicit hypothesis, stated with 08MQ's own hypotheses as antecedents so that 08MQ discharges it:

* `Deformation.ToposThickening.IsFlatLiftCorrespondence`, for Stacks 08MV, is 08MQ specialized
  to the extensions with `K = I ⊗_O ℱ` and `c = 1`: granting strictness and flatness of `ℱ` over
  `O_ℬ`, a flat lift forces the canonical map of condition (1) to be an isomorphism, and once it
  is one, the flat lifts of `ℱ` are the extensions of `ℱ` by `I ⊗_O ℱ` whose canonical action of
  the square-zero ideal is the identity. This is the dictionary the source's one-line proof of
  08MV appeals to. What it carries is precisely: the equivalence of 08MQ, that `ℱ'` is flat over
  `O_{ℬ'}` exactly when `f^*J ⊗_O ℱ ⟶ I·ℱ'` is an isomorphism, and its two "moreover" clauses,
  that flatness makes each of the two factors `f^*J ⊗_O ℱ ⟶ I ⊗_O ℱ ⟶ I·ℱ'` an isomorphism;
  together with the bookkeeping of Section 08MN, which the source treats as implicit and which no
  tag states on its own: that the sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i^*ℱ' ⟶ 0` is an extension of 08MB
  whose canonical action map is the second of those two factors, so that when that factor is
  invertible, pushing the sequence out along its inverse — Stacks 08MJ,
  `Deformation.ToposThickening.extensionOne_actionMap` — normalizes the action map to the
  identity, and conversely that the middle term of an extension with action map the identity has
  `I·ℱ'` the image of `I ⊗_O ℱ`.
* `Deformation.ToposThickening.IsIdealComparisonIsoOfFlat`, for Stacks 08VW, is 08MQ applied to
  `O'` itself: granting strictness and flatness of `f'`, the induced map of defining ideals
  `f^*J ⟶ I` is an isomorphism, hence so is its tensor product with `ℱ`. This is the remark
  `I = f^*J` that the source makes when setting up Situation 08VV; it is carried in the tensored
  form, which is all the proof needs and which 08MQ's "moreover" clause gives directly.

Only part (1) of Stacks 08VW is covered. Its parts (2) and (3) — that the isomorphism classes of
flat lifts form a principal homogeneous space under `Ext¹_O(ℱ, f^*J ⊗_O ℱ)`, and that the
automorphisms of a lift restricting to the identity of `ℱ` are `Ext⁰_O(ℱ, f^*J ⊗_O ℱ)` — rest on
Stacks 08MU and Stacks 08MR. Both are now in the library, conditional on Stacks 08MQ exactly as
the results here are: `Deformation.ToposThickening.flatLiftClass_torsor` and
`Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat` in
`StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors`. Neither part (2) nor part (3) follows
from them in one step, and neither is proved anywhere:

* Part (2) needs `Ext¹` transported along `idealTensorComparison`, which is an iso of
  `O'`-modules on the thickened topos while the `Ext¹` of 08MU is over `i_*O`; the comparison must
  first be descended through `FirstOrderThickening.restrictScalarsFullyFaithful` — legitimate
  under strictness, both ideals being annihilated by `I` — and the class group then moved along it.
* Part (3) needs the same coefficient transport in degree zero, and in addition the statement that
  every lift of the identity is an isomorphism, which is the square-zero nilpotence argument and
  is in the library nowhere.

## References

* [Stacks Project, Tag 08MV](https://stacks.math.columbia.edu/tag/08MV)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]

/-- The square of Stacks 08M7 determined by a first order thickening `i` of `(Sh(C), O)`, a first
order thickening `t` of `(Sh(B), O_ℬ)`, both in the sense of Stacks 08MB, and a commutative
square `f' ∘ i = t ∘ f`. Its defining ideals are the square-zero ideals named by `hi` and `ht`,
read as submodules of the structure sheaves by
`Deformation.ToposThickening.FirstOrderThickening.idealOfThickening`. -/
noncomputable def MorphismOfThickenings.ofFirstOrderThickenings (i : RingedToposHom X X')
    (t : RingedToposHom S S') (f : RingedToposHom X S) (f' : RingedToposHom X' S')
    (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f) : MorphismOfThickenings X X' S S' :=
  MorphismOfThickenings.ofFirstOrder i t f f'
    (IsFirstOrderThickening.of_firstOrderThickening hi)
    (IsFirstOrderThickening.of_firstOrderThickening ht)
    hi.idealOfThickening ht.idealOfThickening comm

section FlatLift

variable [HasWeakSheafify X'.J AddCommGrpCat.{w}]
  [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- `ℱ` is flat over `O_ℬ`: the `O`-module `ℱ`, presented on the thickened topos as a module over
the direct image `i_*O`, is flat for its `i_*f⁻¹O_ℬ`-module structure. -/
def IsFlatOverBase (i : RingedToposHom X X') (f : RingedToposHom X S)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) : Prop :=
  AlgebraicGeometry.SheafOfModules.IsFlat
    ((SheafOfModules.restrictScalars
      ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((pushforwardCommRingFunctor i.toToposHom).map f.fSharpInverseImage))).obj F)

/-- `ℱ` admits a flat lift over the thickening `i` along `f'`: there is an `O'`-module `ℱ'`, flat
over `O_{ℬ'}`, sitting in a short exact sequence `0 ⟶ I·ℱ' ⟶ ℱ' ⟶ i_*ℱ ⟶ 0`, that is, with
`i^*ℱ' ≅ ℱ`. -/
def HasFlatLift (i : RingedToposHom X X') (f' : RingedToposHom X' S')
    (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) : Prop :=
  ∃ (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    (q : F' ⟶ (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
          Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
        (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F)
    (hq : (idealProductSubmodule hi F').ι ≫ q = 0),
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            f'.fSharpInverseImage)).obj F') ∧
      (ShortComplex.mk (idealProductSubmodule hi F').ι q hq).ShortExact

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]

/-- The canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` of condition (1) of Stacks 08MV: the induced map of
defining ideals `f^*J ⟶ I` of Stacks 08M7, tensored with `ℱ`. Both are formed on the thickened
topos, over `O'`; see the implementation notes. -/
noncomputable def idealTensorComparison (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    ((sheafTensor.{u', v', w, w, w} X'.O).flip.obj ((SheafOfModules.restrictScalars
          (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
              Stacks.SheafOfModules.Tensor.ringSheaf
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
            (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F)).obj
        (f'.toModulesHom.pullbackModules.obj ht.idealOfThickening.I) ⟶
      ((sheafTensor.{u', v', w, w, w} X'.O).flip.obj ((SheafOfModules.restrictScalars
          (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
              Stacks.SheafOfModules.Tensor.ringSheaf
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
            (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F)).obj
        hi.idealOfThickening.I :=
  ((sheafTensor.{u', v', w, w, w} X'.O).flip.obj ((SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
          Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
        (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F)).map
    (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).idealMap

variable [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MV consumes**, carried as a
hypothesis: granting that the square is strict and that `ℱ` is flat over `O_ℬ`, which are the
hypotheses of 08MQ,

* a flat lift of `ℱ` forces the canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` to be an isomorphism, which is
  the "moreover" clause of 08MQ, and
* once that map is an isomorphism, the flat lifts of `ℱ` are exactly the extensions of `ℱ` by
  `I ⊗_O ℱ` of Stacks 08MB whose canonical action of the square-zero ideal is the identity, which
  is the characterization of the `O'`-modules flat over `O_{ℬ'}` of 08MQ read through that
  identification.

This is the dictionary the source's proof of 08MV appeals to; see the scope section of the module
docstring. -/
def IsFlatLiftCorrespondence (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) : Prop :=
  (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict →
    IsFlatOverBase i f F →
      (HasFlatLift i f' hi F → IsIso (idealTensorComparison i t f f' hi ht comm F)) ∧
        (IsIso (idealTensorComparison i t f f' hi ht comm F) →
          (HasFlatLift i f' hi F ↔
            ∃ E : Abelian.YonedaExtension
                ((SheafOfModules.restrictScalars
                  (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
                      Stacks.SheafOfModules.Tensor.ringSheaf
                        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
                    (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj F)
                ((SheafOfModules.restrictScalars
                  (show Stacks.SheafOfModules.Tensor.ringSheaf X'.O ⟶
                      Stacks.SheafOfModules.Tensor.ringSheaf
                        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
                    (sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map i.fSharp)).obj
                  (((sheafTensor.{u', v', w, w, w}
                    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)) 0,
              (extensionActionMap hi E).1 =
                𝟙 (((sheafTensor.{u', v', w, w, w}
                  ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)))

/-- **The consequence of Stacks 08MQ that the proof of part (1) of Stacks 08VW consumes**,
carried as a hypothesis: granting that `f'` is flat and that the square is strict, the canonical
map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` is an isomorphism. The source obtains it by applying 08MQ to `O'` itself,
which gives `I = f^*J`, when setting up Situation 08VV. -/
def IsIdealComparisonIsoOfFlat (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) : Prop :=
  f'.IsFlat → (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict →
    IsIso (idealTensorComparison i t f f' hi ht comm F)

/-- **Stacks 08MV.** Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in
Situation 08M7, strict, and let `ℱ` be an `O`-module flat over `O_ℬ`. Then `ℱ` has a lift to an
`O'`-module flat over `O_{ℬ'}` if and only if the canonical map `f^*J ⊗ ℱ ⟶ I ⊗ ℱ` is an
isomorphism and the obstruction class `o(ℱ, I ⊗_O ℱ, 1)` of Stacks 08MF vanishes. -/
@[stacks 08MV "granting Stacks 08MQ, carried as the hypothesis `IsFlatLiftCorrespondence`"]
theorem hasFlatLift_iff_isIso_and_obstruction_eq_zero
    (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hflat : IsFlatOverBase i f F)
    (hMQ : IsFlatLiftCorrespondence i t f f' hi ht comm F) :
    HasFlatLift i f' hi F ↔
      IsIso (idealTensorComparison i t f f' hi ht comm F) ∧
        existenceObstructionClass hi F
            (((sheafTensor.{u', v', w, w, w}
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)
            (𝟙 (((sheafTensor.{u', v', w, w, w}
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)) = 0 := by
  obtain ⟨hnec, hdict⟩ := hMQ hstrict hflat
  constructor
  · intro hlift
    exact ⟨hnec hlift, (existenceObstructionClass_eq_zero_iff hi F _ _).2 ((hdict (hnec hlift)).1
      hlift)⟩
  · rintro ⟨hiso, hzero⟩
    exact (hdict hiso).2 ((existenceObstructionClass_eq_zero_iff hi F _ _).1 hzero)

/-- **Stacks 08VW, part (1).** In the situation of Stacks 08VV — a strict morphism `(f, f')` of
first order thickenings of ringed topoi with `f'` flat, and an `O`-module `ℱ` flat over `O_ℬ` —
the module `ℱ` has a lift to an `O'`-module flat over `O_{ℬ'}` if and only if the obstruction
class `o(ℱ, f^*J ⊗_O ℱ, 1)` of Stacks 08MF vanishes. The class is written here for
`I ⊗_O ℱ`, the two agreeing because `I = f^*J` under these hypotheses. -/
@[stacks 08VW "part (1) only; (2) and (3) are not proved; granting 08MQ as hypotheses"]
theorem hasFlatLift_iff_obstruction_eq_zero
    (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f)
    (F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    [HasExt.{e} (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hf' : f'.IsFlat) (hflat : IsFlatOverBase i f F)
    (hMQ : IsFlatLiftCorrespondence i t f f' hi ht comm F)
    (hMQ' : IsIdealComparisonIsoOfFlat i t f f' hi ht comm F) :
    HasFlatLift i f' hi F ↔
      existenceObstructionClass hi F
          (((sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)
          (𝟙 (((sheafTensor.{u', v', w, w, w}
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F)) = 0 :=
  (hasFlatLift_iff_isIso_and_obstruction_eq_zero i t f f' hi ht comm F hstrict hflat hMQ).trans
    (and_iff_right (hMQ' hf' hstrict))

end FlatLift

end Deformation.ToposThickening

end
