module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TwistingPullback

/-!
# The pullback of a quadruple along a morphism of test schemes

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN). Section 01NS attaches to each
`d ≥ 1` the quadruples `(d, f : T → S, L, ψ)` over a test scheme `T`, and the display 01NX
assembles their classes into `F(T) = ⋃_{d ≥ 1} F_d(T)`. Tag 01NY asserts that `F` is representable
by a scheme.

`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.TwistingPullback` pulls the map `ψ` of a
quadruple back along a morphism `g : T' ⟶ T` of test schemes and proves it multiplicative in every
pair of integer degrees and surjective in degree one, i.e. every field of a quadruple over `g ≫ f`
**except the unit normalisation** `Twisting.app_one`. That field is stated through
`Stacks.PullbackGradedAlgebra.pullbackOne`, the global unit of `f^*𝒜` for the monoidal structure
assembled from the localization, and transporting it needs the unit of that monoidal structure to
be identified with the structure-sheaf comparison of Tag 01CD — the open dedup that
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit` now closes.

This file completes the transport: **the pullback of a quadruple along a morphism of test schemes
is constructed.**

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullback`: the map `ψ` of a quadruple,
  pulled back along `g : T' ⟶ T`, as a `Twisting` over `g ≫ f` with invertible module `g^*L`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.pullback`: **the pullback of a
  quadruple along a morphism of test schemes**, with the same degree `d`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.pullbackApp_one`: **the pullback of `ψ`
  preserves the distinguished degree-zero unit**, which is the condition `Twisting.app_one` demands
  of the map of a quadruple over `g ≫ f`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison_unit`: the unit coherence of the
  comparison of an iterated pullback, at the ascribed spelling.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.oneHom_laurent`: the global unit of the Laurent
  algebra of an invertible module is the identity of the structure sheaf.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_zero`: in degree zero the
  comparison of the integral tensor powers of Tag 01CU is the structure-sheaf comparison of Tag
  01CD.

## Implementation notes

The proof of `Twisting.pullbackApp_one` is the unit triangle of the three canonical comparisons
through which `Twisting.pullbackApp` is built, and it is run after cancelling the structure-sheaf
comparison `c₃` of `g ∘ f`, which is an isomorphism. In that `inv`-free form the global unit of
`f^*𝒜` enters only as `Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne`, and the
coherence consumed is `Stacks.PullbackCompMonoidal.comparison_unit` directly, with no inverse to
transpose.

As in the sibling modules, the two spellings `ringedSpaceHom g ≫ ringedSpaceHom f` and
`ringedSpaceHom (g ≫ f)` of the underlying morphism of ringed spaces are equal by `rfl` and not
syntactically equal, so `compComparison_unit` is an ascribed restatement of
`Stacks.PullbackCompMonoidal.comparison_unit` at the second, exactly as
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.compComparison` is. Every proof below is a term
built from `Eq.trans` and `congrArg`: the goals mix
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` with
`Stacks.RingedSpace.structureRingSheaf`, which are equal by `rfl` and not syntactically equal, so
they are not type-correct at `implicit` transparency and `rw` refuses them.

## Not done here

* **Representability is not proved.** What the pullback of a quadruple does not give by itself is
  a map `F(T) → F(T')`: that needs the pullback to respect the
  two identifications of the display 01NX, i.e. to carry a strict equivalence
  (`Quadruple.StrictlyEquivalent`) and an equivalence (`Quadruple.Equivalent`) to one of the same
  kind. That is proved in
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionPullback`, which
  descends the pullback
  to the map `F.pullback : F(T) → F(T')`. It does **not** go through the functoriality of
  `Stacks.SheafOfModules.TensorPower.laurentAlgebra` in the invertible module, which is still not
  available: the witness of an identification is transported along the comparison
  `Stacks.TensorPowerPullback.pullbackIntPowIso` of the integral tensor powers with pullback
  instead, whose multiplicativity `laurentPullback_mul` is already proved here.
* The functor laws for that map *are* proved, in
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.UnionFunctor`
  (`F.pullback_id`, `F.pullback_comp`, and `Fd.pullback_id`, `Fd.pullback_comp` at a fixed
  degree), so `F` and `F_d` are the functors `F.functor` and `Fd.functor` there. The identity law
  uses the identification of the pullback along an identity morphism with the identity functor,
  `Stacks.TensorSheafSpellingIso.pullbackIdIso`.
* What is **not** stated is the functor-of-points comparison of `F` with the relative `Proj` of
  `𝒜`, nor its bijectivity.
* The **tensorator** half of the dedup between the two monoidal structures on `f^*` is still open;
  only the unit half is used here, and it is all that `Twisting.app_one` needs.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {T' T S : Scheme.{u}}

/-- **The unit coherence of the comparison of an iterated pullback**, at the ascribed spelling
`ringedSpaceHom (g ≫ f)` of the composite. Contracting the iterated pullback of the unit object
and then comparing twice with the structure sheaf agrees with comparing once along the composite;
this is `Stacks.PullbackCompMonoidal.comparison_unit`. -/
theorem compComparison_unit (g : T' ⟶ T) (f : T ⟶ S) :
    compComparison g f (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫
        (pullbackFunctor (ringedSpaceHom g)).map
            (pullbackUnitComparison (ringedSpaceHom f)) ≫
          pullbackUnitComparison (ringedSpaceHom g) =
      pullbackUnitComparison (ringedSpaceHom (g ≫ f)) :=
  Stacks.PullbackCompMonoidal.comparison_unit (ringedSpaceHom f) (ringedSpaceHom g)

/-- **The global unit of the Laurent algebra of an invertible module is the identity of the
structure sheaf.** The degree-zero piece `L^{⊗ 0}` is the structure sheaf on the nose and the
distinguished global section of `Stacks.SheafOfModules.TensorPower.laurentAlgebra` in that degree
was defined as the one the identity corresponds to. -/
theorem oneHom_laurent {T : Scheme.{u}}
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] :
    SheafOfModules.GradedAlgebra.oneHom (laurent L) =
      CategoryStruct.id (𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))) :=
  Equiv.symm_apply_apply _ _

/-- **In degree zero the comparison of the integral tensor powers of Tag 01CU is the
structure-sheaf comparison of Tag 01CD**, at the spelling the Laurent algebra of Section 01NS is
graded by. -/
theorem laurentPullback_zero (g : T' ⟶ T)
    (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L] :
    laurentPullback g L 0 = pullbackUnitComparison (ringedSpaceHom g) :=
  congrArg Iso.hom
    (Stacks.TensorPowerPullback.pullbackIntPowIso_zero (ringedSpaceHom g) L)

namespace Twisting

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The structure-sheaf comparison followed by the global unit of `f^*𝒜`, the degree-zero
identification and any `X` is the pullback of the global unit of `𝒜` followed by that
identification and `X`. -/
private theorem pullbackUnitComparison_comp_pullbackOne_eqToHom (f : T ⟶ S)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
    {Z : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (X : (pullbackFunctor (ringedSpaceHom f)).obj (A.piece (0 * d)) ⟶ Z) :
    pullbackUnitComparison (ringedSpaceHom f) ≫
        Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) A ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ X =
      (pullbackFunctor (ringedSpaceHom f)).map
          (SheafOfModules.GradedAlgebra.oneHom A ≫
            eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ X := by
  rw [Functor.map_comp, Category.assoc,
    ← Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne, Category.assoc]

/-- **The unit normalisation `Twisting.app_one` of `ψ`, with the global unit of `f^*𝒜` replaced by
its `inv`-free form**: the structure-sheaf comparison of `f` followed by the global unit of the
Laurent algebra is the pullback of the global unit of `𝒜` followed by the degree-zero component of
`ψ`. This is `Twisting.app_one` composed with
`Stacks.PullbackStrictUnit.pullbackUnitComparison_comp_pullbackOne`. -/
theorem map_oneHom_comp_app_zero (ψ : Twisting f A d L) :
    (pullbackFunctor (ringedSpaceHom f)).map
          (SheafOfModules.GradedAlgebra.oneHom A ≫
            eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ ψ.app 0 =
      pullbackUnitComparison (ringedSpaceHom f) ≫
        SheafOfModules.GradedAlgebra.oneHom (laurent L) :=
  (pullbackUnitComparison_comp_pullbackOne_eqToHom f A d _).symm.trans
    (congrArg (fun z => pullbackUnitComparison (ringedSpaceHom f) ≫ z) ψ.app_one)

/-- **The pullback of `ψ` along a morphism `g : T' ⟶ T` of test schemes preserves the
distinguished degree-zero unit**, which is exactly the condition `Twisting.app_one` demands of the
map of a quadruple over `g ≫ f` with invertible module `g^*L`.

The proof cancels the structure-sheaf comparison of `g ∘ f`, which is an isomorphism, and then
composes four facts: the `inv`-free form `map_oneHom_comp_app_zero` of `app_one` for `ψ`, the
naturality `compComparison_naturality` of the comparison of an iterated pullback, its unit
coherence `compComparison_unit`, and the degree-zero values `oneHom_laurent` and
`laurentPullback_zero` of the Laurent algebra and of the comparison of integral tensor powers. -/
theorem pullbackApp_one (ψ : Twisting f A d L) (g : T' ⟶ T) :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom (g ≫ f)) A ≫
        (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
          (eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫
        ψ.pullbackApp g 0 =
      SheafOfModules.GradedAlgebra.oneHom
        (laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)) := by
  refine (cancel_epi (pullbackUnitComparison (ringedSpaceHom (g ≫ f)))).mp ?_
  have hinner : (pullbackFunctor (ringedSpaceHom g)).map
          ((pullbackFunctor (ringedSpaceHom f)).map
            (SheafOfModules.GradedAlgebra.oneHom A ≫
              eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d)))) ≫
        ((pullbackFunctor (ringedSpaceHom g)).map (ψ.app 0) ≫ laurentPullback g L 0) =
      (pullbackFunctor (ringedSpaceHom g)).map
          (pullbackUnitComparison (ringedSpaceHom f)) ≫
        pullbackUnitComparison (ringedSpaceHom g) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ laurentPullback g L 0)
          ((CategoryTheory.Functor.map_comp (pullbackFunctor (ringedSpaceHom g)) _ _).symm.trans
            (congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map z)
              (ψ.map_oneHom_comp_app_zero)))).trans
        ((congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map
              (pullbackUnitComparison (ringedSpaceHom f) ≫ z) ≫ laurentPullback g L 0)
            (oneHom_laurent L)).trans
          ((congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map z ≫
                laurentPullback g L 0)
              (Category.comp_id (pullbackUnitComparison (ringedSpaceHom f)))).trans
            (congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map
                (pullbackUnitComparison (ringedSpaceHom f)) ≫ z)
              (laurentPullback_zero g L)))))
  refine Eq.trans ?_ (congrArg
    (fun z => pullbackUnitComparison (ringedSpaceHom (g ≫ f)) ≫ z)
    (oneHom_laurent ((pullbackFunctor (ringedSpaceHom g)).obj L)).symm)
  refine Eq.trans ?_ (Category.comp_id _).symm
  refine Eq.trans ?_ (compComparison_unit g f)
  refine (pullbackUnitComparison_comp_pullbackOne_eqToHom (g ≫ f) A d _).trans ?_
  refine Eq.trans (congrArg (fun z => (pullbackFunctor (ringedSpaceHom (g ≫ f))).map
      (SheafOfModules.GradedAlgebra.oneHom A ≫
        eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d))) ≫ z)
    (show ψ.pullbackApp g 0 = compComparison g f (A.piece (0 * d)) ≫
        ((pullbackFunctor (ringedSpaceHom g)).map (ψ.app 0) ≫ laurentPullback g L 0) from
      rfl)) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ ((pullbackFunctor (ringedSpaceHom g)).map (ψ.app 0) ≫
      laurentPullback g L 0))
    (compComparison_naturality g f (SheafOfModules.GradedAlgebra.oneHom A ≫
      eqToHom (congrArg A.piece (by ring : (0 : ℤ) = 0 * d)))).symm) ?_
  exact (Category.assoc _ _ _).trans (congrArg
    (fun z => compComparison g f
      (𝟙_ (SheafOfModules.{u} (structureRingSheaf S.toRingedSpace))) ≫ z) hinner)

/-- **The map `ψ` of a quadruple, pulled back along a morphism `g : T' ⟶ T` of test schemes.**
Its components are `Twisting.pullbackApp`, and the three conditions of a `Twisting` over `g ≫ f`
with invertible module `g^*L` are `Twisting.pullbackApp_mul` and `Twisting.pullbackApp_one`. -/
def pullback (ψ : Twisting f A d L) (g : T' ⟶ T) :
    Twisting (g ≫ f) A d ((pullbackFunctor (ringedSpaceHom g)).obj L) where
  app i := ψ.pullbackApp g i
  app_mul i j := ψ.pullbackApp_mul g i j
  app_one := ψ.pullbackApp_one g

/-- The components of the pulled-back map are `Twisting.pullbackApp`. -/
@[simp] theorem pullback_app (ψ : Twisting f A d L) (g : T' ⟶ T) (i : ℤ) :
    (ψ.pullback g).app i = ψ.pullbackApp g i := rfl

end Twisting

namespace Quadruple

variable {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}

/-- **The pullback of a quadruple `(d, f : T → S, L, ψ)` of Section 01NS along a morphism
`g : T' ⟶ T` of test schemes**: the quadruple `(d, g ∘ f, g^*L, g^*ψ)`.

The invertible module is `g^*L`, invertible by Tag 0B8L; the map is `Twisting.pullback`; and the
surjectivity of the degree-one component is `Twisting.epi_pullbackApp`, the pullback of sheaves of
modules being a left adjoint. The degree `d` is unchanged. -/
def pullback (P : Quadruple f A d) (g : T' ⟶ T) : Quadruple (g ≫ f) A d where
  L := (pullbackFunctor (ringedSpaceHom g)).obj P.L
  isInvertible := inferInstance
  twisting := P.twisting.pullback g
  epi_app_one := P.twisting.epi_pullbackApp g 1 P.epi_app_one

/-- The invertible module of the pullback of a quadruple is the pullback of its invertible
module. -/
@[simp] theorem pullback_L (P : Quadruple f A d) (g : T' ⟶ T) :
    (P.pullback g).L = (pullbackFunctor (ringedSpaceHom g)).obj P.L := rfl

/-- The components of the map of the pullback of a quadruple are `Twisting.pullbackApp`. -/
@[simp] theorem pullback_twisting_app (P : Quadruple f A d) (g : T' ⟶ T) (i : ℤ) :
    (P.pullback g).twisting.app i = P.twisting.pullbackApp g i := rfl

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
