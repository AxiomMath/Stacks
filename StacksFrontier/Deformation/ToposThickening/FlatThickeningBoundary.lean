module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Deformation.ToposThickening.ExtensionRestriction
public import StacksFrontier.Deformation.ToposThickening.FlatLiftObstruction
public import StacksFrontier.Deformation.ToposThickening.IdealComparisonIsoOfFlat
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundaryPushout
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexHorizontalHom
public import StacksFrontier.Deformation.ToposThickening.TrivialExtension

/-!
# The difference of the two flat lifts over the first column of a short exact sequence

Let `f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)` be a morphism of ringed topoi and consider a commutative
diagram

```
  (Sh(C'₁), O'₁)     --h-->  (Sh(C'₂), O'₂)     ------>  (Sh(C'₃), O'₃)
      |                          |                           |
      f'₁                        f'₂                         f'₃
      v                          v                           v
  (Sh(B'₁), O_{ℬ'₁}) ------->  (Sh(B'₂), O_{ℬ'₂}) ------>  (Sh(B'₃), O_{ℬ'₃})
```

in which the upper row is a short exact sequence of first order thickenings of `(Sh(C), O)`, the
lower row is a short exact sequence of first order thickenings of `(Sh(B), O_ℬ)`, each `f'ₖ`
restricts to `f`, each pair `(f, f'ₖ)` is a strict morphism of thickenings and each `f'ₖ` is
flat; together with an `O'₂`-module `ℱ'₂` flat over `O_{ℬ'₂}`, its restriction `ℱ = ℱ'₂ ⊗ O`,
and the canonical splitting `π : (Sh(C'₁), O'₁) ⟶ (Sh(C), O)` of the upper row. This is
Situation **Stacks 08VX**.

**Stacks 08VY**, proved here, says that `π^*ℱ` and `h^*ℱ'₂` are `O'₁`-modules flat over
`O_{ℬ'₁}` restricting to `ℱ`, that their difference is a class
`θ ∈ Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)`, and that the boundary of `θ` in `Ext²_O(ℱ, f^*𝒥₃ ⊗_O ℱ)` for the
sequence `0 ⟶ f^*𝒥₃ ⊗_O ℱ ⟶ f^*𝒥₂ ⊗_O ℱ ⟶ f^*𝒥₁ ⊗_O ℱ ⟶ 0` is the obstruction of
Stacks 08VW to lifting `ℱ` to an `O'₃`-module flat over `O_{ℬ'₃}`.

## Main definitions

* `Deformation.ToposThickening.IsFlatOfFixedActionIdentity` and
  `Deformation.ToposThickening.FirstOrderThickeningComplex.IsIdealTensorShortExact`: the two
  consequences of Stacks 08MQ that the proof below consumes. See the scope section.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.idealTensor_comp_eq_zero`: the two
  maps `I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ` of a complex of first order thickenings compose to
  zero, so the coefficient sequence of the boundary is a complex.
* `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_eq_obstruction`: **Stacks 08VY**.

## Implementation notes

The whole content of Stacks 08VY is Remark **Stacks 08MM**, which the source's proof invokes:
`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_of_pushout`. Everything here is the translation of that
remark into the flat situation, and the readings below are the ones under which that remark and
Stacks 08VW are already stated in the library.

* The upper row is `Deformation.ToposThickening.FirstOrderThickeningComplex`, the one-site
  presentation of a sequence of first order thickenings of `(Sh(C), O)`: three thickened
  structure sheaves `O'₃ ⟶ O'₂ ⟶ O'₁` of `O` on the site of `Y` along one morphism of topoi.
  This is the presentation in which the obstruction class of Stacks 08MF, the class `ξ_{F'}` of
  Stacks 08MI and Remark 08MM exist, and it is what makes the three defining ideals objects of
  one category. The three-site presentation of the same situation is
  `Deformation.ToposThickening.ShortExactFlatThickeningSituation` of Stacks 08VX
  (`StacksFrontier/Deformation/ToposThickening/ShortExactFlatThickenings.lean`), which carries the
  tag for the situation; it is built over
  `Deformation.ToposThickening.FirstOrderThickeningSequence`, and transporting a sequence of
  thickenings from three sites onto one is not in the library — the same split as between
  `FirstOrderThickeningSequence.IsComplex` and `FirstOrderThickeningComplex.IsComplex`, both of
  which state the complex condition of Stacks 08ML in their own presentation. The lower row is
  a `FirstOrderThickeningComplex` as well, so that its three defining ideals `𝒥₃ ⟶ 𝒥₂ ⟶ 𝒥₁`
  likewise form one sequence and its short exactness is a single hypothesis.
* The coefficient module of the `k`-th column is written `Iₖ ⊗_O ℱ`, where the source writes
  `f^*𝒥ₖ ⊗_O ℱ`. The two agree under the hypotheses of Situation 08VX, the comparison
  `f^*𝒥ₖ ⟶ Iₖ` being an isomorphism by Stacks 08MQ; this is the reading under which
  `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero` states Stacks 08VW and
  under which `Deformation.ToposThickening.MorphismOfFirstOrderThickenings`
  `.existenceObstructionClass_first_tensorIdeal` states Stacks 0CYE, so the obstruction class
  below is exactly the class those tags are about. Identifying the two as terms would need the
  descent of `Deformation.ToposThickening.idealTensorComparison` from `O'` to `i_*O`, the gap
  recorded in the scope section of
  `StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean`.
* `ℱ'₂`, an `O'₂`-module flat over `O_{ℬ'₂}` with `i₂^*ℱ'₂ = ℱ`, enters as an extension `E₂` of
  `ℱ` by `I₂ ⊗_O ℱ` over `O'₂` as in Stacks 08MB whose canonical action of the square-zero
  ideal is the identity. That these are the same thing is Stacks 08MQ, in the form in which
  `Deformation.ToposThickening.IsFlatLiftCorrespondence` carries it. Likewise `h^*ℱ'₂` enters as
  an extension `E₁` of `ℱ` by `I₁ ⊗_O ℱ` over `O'₁` receiving a map `u` from `E₂` which is
  `I₂ ⊗ ℱ ⟶ I₁ ⊗ ℱ` on kernel modules and the identity on `ℱ`: for short exact sequences that is
  exactly the pushout square of Stacks 08MJ, so this is the extension that the functoriality of
  08MJ produces from `ℱ'₂`, which is `ℱ'₂ ⊗_{O'₂} O'₁ = h^*ℱ'₂`. Quantifying over every such
  `(E₁, u)` rather than naming
  `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.PushoutExtensionData.extensionOne`
  keeps the statement free of the narrowing of section universes that the construction of the
  `O'₁`-module structure on the pushout imposes; this is the choice Remark 08MM is already
  stated with. The instantiation at that construction — the tag's own `h^*ℱ'₂` — is
  `Deformation.ToposThickening.FirstOrderThickeningComplex`
  `.boundary_underlyingExtensionClass_eq_obstruction_pushout` in
  `StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundaryPushout.lean`, at that narrowed
  universe of sections.
* `π^*ℱ` is the trivial extension `ℱ ⊕ (I₁ ⊗_O ℱ)` of Stacks 08MI attached to the trivialization
  `π` and to the action map `1`, `Deformation.ToposThickening.trivialExtension`: the
  canonical splitting makes `O'₁ = O ⊕ I₁` as an `O`-algebra, so `π^*ℱ = O'₁ ⊗_O ℱ` is
  `ℱ ⊕ (I₁ ⊗_O ℱ)` with precisely the action that 08MI writes down. It is the trivial lift, and
  its class `ξ` vanishes (`underlyingExtensionClass_trivialExtension`).
* The *difference* of the two lifts is read through the bijection `ℱ' ↦ ξ_{ℱ'}` of Stacks 08MI,
  `Deformation.ToposThickening.bijective_underlyingExtensionClass`, which is what turns the
  principal homogeneous space of Stacks 08ME — and hence the one of part (2) of Stacks 08VW —
  into `Ext¹_O(ℱ, I₁ ⊗_O ℱ)`. The conclusion records that `θ = ξ_{h^*ℱ'₂} - ξ_{π^*ℱ}`, the
  difference of the images of the two lifts, and `ξ_{π^*ℱ} = 0`.
* "Restricting to `ℱ`" is carried by the extensions themselves: each is a short exact sequence
  `0 ⟶ I₁ ⊗_O ℱ ⟶ ℱ' ⟶ i₁_*ℱ ⟶ 0`, and the conclusion records in addition that the canonical
  action map of each is the identity, which is the source's sentence that the kernels of
  `π^*ℱ ⟶ ℱ` and `h^*ℱ'₂ ⟶ ℱ` are `f^*𝒥₁ ⊗_O ℱ`.
* That the obstruction class is *the obstruction to lifting* `ℱ` to an `O'₃`-module flat over
  `O_{ℬ'₃}` is recorded as a clause of the conclusion rather than left to the reader: it is
  Stacks 08VW, `Deformation.ToposThickening.hasFlatLift_iff_obstruction_eq_zero`, for the third
  column.

## Scope

Stacks 08MQ — the characterization of the `O'`-modules flat over `O_{ℬ'}` — is not in the
library at the time of writing; it is being formalized elsewhere and is not duplicated here. The
result below therefore carries the consequences of it that its proof consumes as explicit
hypotheses, each stated with 08MQ's own hypotheses as antecedents so that 08MQ discharges it.
This is the treatment of `Deformation.ToposThickening.IsFlatLiftCorrespondence` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftObstruction.lean`, and one of the three
hypotheses is literally that, for the third column, carried through the application of
Stacks 08VW. That one **is proved**, by
`Deformation.ToposThickening.isFlatLiftCorrespondence` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftCorrespondence.lean`, which imports this module
and so cannot discharge the binder here; the result below is restated without it in
`StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundaryCorrespondence.lean`, as
`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction'`, which is what Stacks 08VY's own statement
is now obtained from. The identification `I = f^*J` that 08VW also needs is *not* among them
either: it is proved without 08MQ, by
`Deformation.ToposThickening.isIdealComparisonIsoOfFlat`. The remaining two are:

* `Deformation.ToposThickening.IsFlatOfFixedActionIdentity`, the "if" half of 08MQ read per
  module: granting strictness of the column, flatness of `f'` and flatness of `ℱ` over `O_ℬ`,
  an extension of `ℱ` by `I ⊗_O ℱ` whose canonical action of the square-zero ideal is the
  identity has flat middle term. It is used twice, on `π^*ℱ` and on `h^*ℱ'₂`, and is the step
  the source writes as "the kernels of `π^*ℱ ⟶ ℱ` and `h^*ℱ'₂ ⟶ ℱ` are given by
  `f^*𝒥₁ ⊗_O ℱ`; hence flatness by Lemma 91.11.2", Lemma 91.11.2 being 08MQ.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.IsIdealTensorShortExact`: granting
  that the lower row is a short exact sequence of first order thickenings, that each column is
  strict with `f'ₖ` flat, and that `ℱ` is flat over `O_ℬ`, the coefficient sequence
  `0 ⟶ I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ ⟶ 0` is short exact. This is the sentence of the source's
  proof "taking the boundary makes sense as the sequence of modules ... is short exact due to
  the assumptions in Situation 91.12.4 and the fact that `ℱ` is flat over `O_ℬ`": 08MQ turns
  each `Iₖ ⊗_O ℱ` into `f^*𝒥ₖ ⊗_O ℱ`, and the sequence is then the inverse image of
  `0 ⟶ 𝒥₃ ⟶ 𝒥₂ ⟶ 𝒥₁ ⟶ 0` tensored over `f⁻¹O_ℬ` with the `f⁻¹O_ℬ`-flat module `ℱ`.

Nothing below asserts the content of 08MQ, and the result is not weaker than its source
statement once 08MQ is available.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VX](https://stacks.math.columbia.edu/tag/08VX)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08MM](https://stacks.math.columbia.edu/tag/08MM)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
* [Stacks Project, Tag 08MJ](https://stacks.math.columbia.edu/tag/08MJ)
* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u v₂ u₂ w vB uB wB vB' uB' wB' v' u' vS' uS' wS' e

namespace Deformation.ToposThickening

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08VY consumes**, carried as a
hypothesis: granting that `f'` is flat, that the square is strict and that `ℱ` is flat over
`O_ℬ`, which are the hypotheses of 08MQ, an extension `0 ⟶ I ⊗_O ℱ ⟶ ℱ' ⟶ ℱ ⟶ 0` over the
thickening whose canonical action of the square-zero ideal is the identity has `ℱ'` flat over
`O_{ℬ'}`.

This is the "if" half of the characterization of 08MQ, read per module: the ideal product
`I·ℱ'` of such an extension is the image of `I ⊗_O ℱ`, which is `f^*𝒥 ⊗_O ℱ` because `f'` is
flat, so the canonical map `f^*𝒥 ⊗_O ℱ ⟶ I·ℱ'` is an isomorphism and 08MQ applies. It is the
step the source's proof of Stacks 08VY writes as "the kernels of `π^*ℱ ⟶ ℱ` and `h^*ℱ'₂ ⟶ ℱ`
are given by `f^*𝒥₁ ⊗_O ℱ`; hence flatness by Lemma 91.11.2", Lemma 91.11.2 being 08MQ. -/
def IsFlatOfFixedActionIdentity {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
    {S : RingedTopos.{vB, uB, wB}} {S' : RingedTopos.{vS', uS', wS'}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
    [S.J.HasSheafCompose (forget RingCat.{wB})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [S.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
    [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify X'.J AddCommGrpCat.{w}] [HasWeakSheafify X'.J AddCommGrpCat.{w}]
    (j : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hj : FirstOrderThickening j) (ht : FirstOrderThickening t)
    (comm : f'.comp j = t.comp f)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing j))) : Prop :=
  f'.IsFlat → (MorphismOfThickenings.ofFirstOrderThickenings j t f f' hj ht comm).IsStrict →
    IsFlatOverBase j f F →
      ∀ E : Abelian.YonedaExtension ((structureRestrict j).obj F)
          ((structureRestrict j).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
              j)).flip.obj F).obj hj.I)) 0,
        (extensionActionMap hj E).1 = 𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
            j)).flip.obj F).obj hj.I) →
          AlgebraicGeometry.SheafOfModules.IsFlat
            ((SheafOfModules.restrictScalars
              ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
                f'.fSharpInverseImage)).obj E.Z.left)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}

namespace FirstOrderThickeningComplex

variable (S : FirstOrderThickeningComplex i)

/-- The two maps `I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ` of a complex of first order thickenings
compose to zero: the two maps of defining ideals do, and `· ⊗_O ℱ` preserves zero morphisms. -/
theorem idealTensor_comp_eq_zero (hS : S.IsComplex)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₃₂ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁ = 0 :=
          by
  let := Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesZeroMorphisms
    Y.J (baseRing i) F
  rw [← Functor.map_comp, hS, Functor.map_zero]

section Situation

variable (T : FirstOrderThickeningComplex t) (f : RingedToposHom X B)
  (f₁ : RingedToposHom Y B') (f₂ : RingedToposHom (reshape Y S.lower.O₂)
    (reshape B' T.lower.O₂)) (f₃ : RingedToposHom (reshape Y S.O₃) (reshape B' T.O₃))
  (commf₁ : f₁.comp i = t.comp f)
  (commf₂ : f₂.comp (reshapeHom i S.lower.O₂ S.lower.fSharp₂) =
    (reshapeHom t T.lower.O₂ T.lower.fSharp₂).comp f)
  (commf₃ : f₃.comp S.thirdHom = T.thirdHom.comp f)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08VY consumes**, carried as a
hypothesis: granting that the lower row is a short exact sequence of first order thickenings,
that each of the three columns is strict with its `f'ₖ` flat, that the two horizontal squares of
the diagram of Situation 08VX commute, and that `ℱ` is flat over `O_ℬ`, which are the hypotheses
of Situation 08VX, the coefficient sequence
`0 ⟶ I₃ ⊗_O ℱ ⟶ I₂ ⊗_O ℱ ⟶ I₁ ⊗_O ℱ ⟶ 0` is short exact.

This is the sentence of the source's proof "taking the boundary makes sense as the sequence of
modules `0 → f^*𝒥₃ ⊗_O ℱ → f^*𝒥₂ ⊗_O ℱ → f^*𝒥₁ ⊗_O ℱ → 0` is short exact due to the assumptions
in Situation 91.12.4 and the fact that `ℱ` is flat over `O_ℬ`": Stacks 08MQ, applied to each
column, turns `Iₖ ⊗_O ℱ` into `f^*𝒥ₖ ⊗_O ℱ`, and the resulting sequence is the inverse image of
`0 ⟶ 𝒥₃ ⟶ 𝒥₂ ⟶ 𝒥₁ ⟶ 0` tensored over `f⁻¹O_ℬ` with `ℱ`, which is flat over `f⁻¹O_ℬ`.

The two horizontal squares are the hypotheses that the diagram of Situation 08VX commutes along
its horizontal arrows:

```
  (Sh(C'₁), O'₁)     --h-->  (Sh(C'₂), O'₂)     ------>  (Sh(C'₃), O'₃)
      |                          |                           |
      f'₁                        f'₂                         f'₃
      v                          v                           v
  (Sh(B'₁), O_{ℬ'₁}) ---h_ℬ-->  (Sh(B'₂), O_{ℬ'₂}) ----->  (Sh(B'₃), O_{ℬ'₃})
```

that is, `f'₂ ∘ h = h_ℬ ∘ f'₁` and `f'₃ ∘ (O'₃ ⟶ O'₂) = (O_{ℬ'₃} ⟶ O_{ℬ'₂}) ∘ f'₂`. They are
the two squares that
`Deformation.ToposThickening.ShortExactFlatThickeningSituation.comm₁₂` and `.comm₂₃` carry in
the three-site presentation of the situation, read here in the one-site presentation: the
horizontal arrows of each row are changes of coefficient rings on a fixed site
(`AlgebraicGeometry.RingedToposHom.coefficientMorphism`), the morphism `h` of the upper row
being the one determined by `h^♯ = S.lower.hSharp` and the morphism of the lower row the one
determined by `T.lower.hSharp`.

Without them the statement is **false**, and not merely unproved: the conclusion depends on the
upper row's `h^♯` — the maps `I₂ ⟶ I₁` and `I₃ ⟶ I₂` are induced by it — while the three
strictness and three flatness hypotheses each speak about one column only.
`Deformation.ToposThickening.FirstOrderThickeningComplex`
`.not_isIdealTensorShortExact_trivializeLower` refutes the shape
without them. -/
def IsIdealTensorShortExact (hS : S.IsComplex) : Prop :=
  ∀ hT : T.IsComplex,
    (ShortComplex.mk T.idealMap₃₂ T.idealMap₂₁ hT).ShortExact →
      IsFlatOverBase i f F →
        (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁
            S.lower.first T.lower.first commf₁).IsStrict →
          (MorphismOfThickenings.ofFirstOrderThickenings
              (reshapeHom i S.lower.O₂ S.lower.fSharp₂)
              (reshapeHom t T.lower.O₂ T.lower.fSharp₂) f f₂
              S.lower.second T.lower.second commf₂).IsStrict →
            (MorphismOfThickenings.ofFirstOrderThickenings S.thirdHom T.thirdHom f f₃
                S.third T.third commf₃).IsStrict →
              f₁.IsFlat → f₂.IsFlat → f₃.IsFlat →
                f₂.comp S.lowerHorizontalHom = T.lowerHorizontalHom.comp f₁ →
                  f₃.comp S.upperHorizontalHom = T.upperHorizontalHom.comp f₂ →
                    (ShortComplex.mk (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
                        i)).flip.obj F).map S.idealMap₃₂)
                      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map
                          S.idealMap₂₁)
                      (S.idealTensor_comp_eq_zero hS F)).ShortExact

/-- **Stacks Project, Tag 08VY.** In Situation 08VX the modules `π^*ℱ` and `h^*ℱ'₂` are
`O'₁`-modules flat over `O_{ℬ'₁}` restricting to `ℱ` on `(Sh(C), O)`. Their difference
(Stacks 08VW) is an element `θ` of `Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)` whose boundary in
`Ext²_O(ℱ, f^*𝒥₃ ⊗_O ℱ)` equals the obstruction (Stacks 08VW) to lifting `ℱ` to an `O'₃`-module
flat over `O_{ℬ'₃}`.

The seven clauses of the conclusion are, in order: the canonical action map of `h^*ℱ'₂` and of
`π^*ℱ` is the identity, so the kernel of each of `h^*ℱ'₂ ⟶ ℱ` and `π^*ℱ ⟶ ℱ` is
`I₁ ⊗_O ℱ = f^*𝒥₁ ⊗_O ℱ` and each restricts to `ℱ`; each of `π^*ℱ` and `h^*ℱ'₂` is flat over
`O_{ℬ'₁}`; the class `θ = ξ_{h^*ℱ'₂}` is the difference of the two lifts under the bijection
`ℱ' ↦ ξ_{ℱ'}` of Stacks 08MI, which is what makes part (2) of Stacks 08VW a principal
homogeneous space under `Ext¹_O(ℱ, f^*𝒥₁ ⊗_O ℱ)`; the obstruction class is, by Stacks 08VW for
the third column, the obstruction to lifting `ℱ` to an `O'₃`-module flat over `O_{ℬ'₃}`; and the
boundary of `θ` for the coefficient sequence equals that obstruction class.

The last clause is Remark **Stacks 08MM** — the source's "direct translation of the result of
Remark 91.10.11 to this particular situation" — at `Kₖ = Iₖ ⊗_O ℱ` and `cₖ = 1`, for which the
compatibility square of the remark reads `1 ∘ κ = κ ∘ 1`. See the implementation notes for the
readings of `π^*ℱ`, of `h^*ℱ'₂` and of the coefficient modules, and the scope section for the
consequences of Stacks 08MQ carried as the hypotheses `hMQ`, `hMQ₁` and `hMQ₃`.

This is the general form and is untagged: it quantifies over an arbitrary Yoneda extension `E₁`,
an `E₂` and a map `u` between them, where the source speaks of `π^*ℱ` and `h^*ℱ'₂`. Stacks 08VY
itself is `Deformation.ToposThickening.FirstOrderThickeningComplex`
`.boundary_underlyingExtensionClass_eq_obstruction_pushout`
(`StacksFrontier/Deformation/ToposThickening/FlatThickeningBoundaryPushout.lean`), which
instantiates this at the tag's own two modules and assumes none of 08MQ's consequences. -/
theorem boundary_underlyingExtensionClass_eq_obstruction
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf S.O₃))]
    (hS : S.IsComplex) (hT : T.IsComplex)
    (hTSE : (ShortComplex.mk T.idealMap₃₂ T.idealMap₂₁ hT).ShortExact)
    (π : Trivialization i)
    (hπ : S.upper.ringMapH ≫ S.lower.ringMapH =
      S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first π)
    (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁
      S.lower.first T.lower.first commf₁).IsStrict)
    (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings
      (reshapeHom i S.lower.O₂ S.lower.fSharp₂) (reshapeHom t T.lower.O₂ T.lower.fSharp₂) f f₂
      S.lower.second T.lower.second commf₂).IsStrict)
    (hstrict₃ : (MorphismOfThickenings.ofFirstOrderThickenings S.thirdHom T.thirdHom f f₃
      S.third T.third commf₃).IsStrict)
    (hf₁ : f₁.IsFlat) (hf₂ : f₂.IsFlat) (hf₃ : f₃.IsFlat)
    (commh : f₂.comp S.lowerHorizontalHom = T.lowerHorizontalHom.comp f₁)
    (commh₃₂ : f₃.comp S.upperHorizontalHom = T.upperHorizontalHom.comp f₂)
    (hF : IsFlatOverBase i f F)
    (hMQ : S.IsIdealTensorShortExact T f f₁ f₂ f₃ commf₁ commf₂ commf₃ F hS)
    (E₂ : Abelian.YonedaExtension
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj F)
      ((structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.lower.second.I)) 0)
    (hE₂ : (extensionActionMap S.lower.second E₂).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.lower.second.I))
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
          F).obj S.lower.first.I)) 0)
    (u : E₂.Z.left ⟶ (S.lower.restrictedExtension E₁).Z.left)
    (hu : E₂.f ≫ u =
      (structureRestrict (reshapeHom i S.lower.O₂ S.lower.fSharp₂)).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁) ≫
        (S.lower.restrictedExtension E₁).f)
    (hug : u ≫ (S.lower.restrictedExtension E₁).g = E₂.g)
    (hMQ₁ : IsFlatOfFixedActionIdentity i t f f₁ S.lower.first T.lower.first commf₁ F)
    (hMQ₃ : IsFlatLiftCorrespondence S.thirdHom T.thirdHom f f₃ S.third T.third commf₃ F) :
    (extensionActionMap S.lower.first E₁).1 =
        𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.lower.first.I) ∧
      (extensionActionMap S.lower.first (trivialExtension S.lower.first π F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.lower.first.I)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
              S.lower.first.I)))).1 =
        𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.lower.first.I) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat
          ((SheafOfModules.restrictScalars
            ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
              f₁.fSharpInverseImage)).obj
            (trivialExtension S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I))).Z.left) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat
          ((SheafOfModules.restrictScalars
            ((sheafCompose Y.J (forget₂ CommRingCat.{w} RingCat.{w})).map
              f₁.fSharpInverseImage)).obj E₁.Z.left) ∧
      underlyingExtensionClass.{e} i S.lower.first π F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                S.lower.first.I) E₁ =
          splitRestrictionExtHom.{e} S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (extensionClass.{_, _, _, _, _, _, e} F
                (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                    S.lower.first.I) E₁) -
            splitRestrictionExtHom.{e} S.lower.first π F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.lower.first.I)
              (extensionClass.{_, _, _, _, _, _, e} F
                (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                    S.lower.first.I)
                (trivialExtension S.lower.first π F
                  (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                      S.lower.first.I)
                  (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                      S.lower.first.I)))) ∧
      (HasFlatLift S.thirdHom f₃ S.third F ↔
          existenceObstructionClass S.third F
              (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I)
              (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                  S.third.I)) = 0) ∧
      (underlyingExtensionClass.{e} i S.lower.first π F
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
                S.lower.first.I) E₁).comp
          (hMQ hT hTSE hF hstrict₁ hstrict₂ hstrict₃ hf₁ hf₂ hf₃ commh commh₃₂).extClass
          (by decide) =
        existenceObstructionClass S.third F
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj S.third.I)
          (𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
            S.third.I)) := by
  have hK := hMQ hT hTSE hF hstrict₁ hstrict₂ hstrict₃ hf₁ hf₂ hf₃ commh commh₃₂
  have hc₁ : (extensionActionMap S.lower.first E₁).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).obj
        S.lower.first.I) := by
    have hnat := (extensionActionMap_comp_of_hom S.lower.second E₂
      (S.lower.restrictedExtension E₁)
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map S.idealMap₂₁) u hu
          hug).trans
      (S.lower.restrictedExtension_actionMap E₁)
    simp only [hE₂] at hnat
    have : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map
        S.idealMap₂₁) := hK.epi_g
    refine ((cancel_epi (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj F).map
        S.idealMap₂₁)).mp ?_).symm
    rw [Category.comp_id]
    exact hnat
  refine ⟨hc₁, trivialExtension_extensionActionMap S.lower.first π F _ _,
    hMQ₁ hf₁ hstrict₁ hF _ (trivialExtension_extensionActionMap S.lower.first π F _ _),
    hMQ₁ hf₁ hstrict₁ hF E₁ hc₁, ?_, ?_, ?_⟩
  · rw [← underlyingExtensionClass_eq_splitRestrictionExtHom,
      ← underlyingExtensionClass_eq_splitRestrictionExtHom,
      underlyingExtensionClass_trivialExtension, sub_zero]
  · exact hasFlatLift_iff_obstruction_eq_zero S.thirdHom T.thirdHom f f₃ S.third T.third commf₃ F
      hstrict₃ hf₃ hF hMQ₃
      (isIdealComparisonIsoOfFlat S.thirdHom T.thirdHom f f₃ S.third T.third commf₃ F)
  · exact S.boundary_underlyingExtensionClass_of_pushout hS π hπ F _ _ _ _ _ _ _
      (S.idealTensor_comp_eq_zero hS F) hK
      ((Category.id_comp _).trans (Category.comp_id _).symm) E₂ hE₂ E₁ u hu hug

end Situation

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
