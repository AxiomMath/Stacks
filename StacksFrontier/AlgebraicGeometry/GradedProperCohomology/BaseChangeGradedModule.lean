module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedModuleToModuleSheaf
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecGradedTildePullback
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.RelativeSpecPushforwardModule
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization

/-!
# The module `ℱ'` of the proof of Tag 0897, on the base change

[Stacks, Tag 0897] runs over the base change `X' = Spec(B) ×_{Spec A} X` of a proper
`f : X ⟶ Spec A` along `Spec B ⟶ Spec A`, with `π : X' ⟶ X` the projection, and its proof
produces a module `ℱ'` on `X'` whose direct image along `π` is the ungraded realization
`⨁ₙ ℱₙ` of the graded `𝓑`-module `ℱ`, for `𝓑 = f^* B̃`.

This file produces it. Two statements:

* over the relative spectrum of an arbitrary sheaf of graded algebras, where the module comes
  from [Stacks, Tag 01SB];
* over `X'` itself, transported along the identification `X' = Spec_X(𝓑)` of
  [Stacks, Tag 01LX].

What results is quasi-coherent, not coherent; [Stacks, Tag 0897] part (1) needs in addition the
upgrade of [Stacks, Tag 01XZ].

## Main results

* `Stacks.RelativeSpec.exists_isQuasicoherent_pushforward_relativeSpecToBase_iso_intCoprod`:
  over the relative spectrum, there is a quasi-coherent module whose direct image of
  `𝒪_X`-modules is `∐ₙ ℱₙ`.
* `Stacks.AffineGradedAlgebra.exists_isQuasicoherent_pushforward_baseChange_iso_intCoprod`: the
  same over `X' = Spec(B) ×_{Spec A} X`, along the projection `π = pullback.snd`.
* `Stacks.RelativeSpec.ι_comp_pushforwardIsoIntCoprod_inv`: **the value of the relative-spectrum
  identification on the degree-`n` summand of `∐ₙ ℱₙ`.** An equality of morphisms out of a
  coproduct is checked summand by summand, and the degreewise action of `𝓑` on `∐ₙ ℱₙ` is given
  summand by summand, so this is the form in which a comparison of the two can be stated at all.
* `Stacks.AffineGradedAlgebra.pushforwardPullbackIsoIntCoprod_inv`: the same identification over
  `X'`, with the transport along `X' ≅ Spec_X(𝓑)` peeled off the right, which is what reduces the
  summand-wise statement over `X'` to the one over the relative spectrum.

Together with the vocabulary the statements downstream of this file share:
`Stacks.AffineGradedAlgebra.baseChangeModuleOfRelativeSpec`, the `𝒪_{X'}`-module attached to a
module on `Spec_X(𝓑)`; `Stacks.AffineGradedAlgebra.qcohGradedTildePullbackModule`, the target
of the identification of [Stacks, Tag 01SB] at `𝓑 = f^* B̃`; and
`Stacks.AffineGradedAlgebra.pushforwardPullbackIsoIntCoprod`, which reads an `𝒪_X`-module
identification `π_* ℱ' ≅ ∐ₙ ℱₙ` off an identification in the quasi-coherent `𝓑`-modules. The
last is what lets a statement return the `𝓑`-linear identification and still conclude the
`𝒪_X`-module one: the second is a total function of the first.

## Implementation notes

The relative-spectrum statement is the composite of three facts: [Stacks, Tag 01SB] at the
relative spectrum produces a quasi-coherent module over `𝓑` isomorphic to
`Stacks.RelativeSpec.gradedModuleSheafOfRight`
(`exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece`); the functor of that
equivalence is the direct image of `𝒪_X`-modules once the `𝓑`-action is forgotten
(`Stacks.AffineAlgebraEquivalence`
`.restrictScalars_relativeSpecQcohEquivalence_functor_obj`); and the `𝒪_X`-module underlying
`gradedModuleSheafOfRight` is the coproduct of the homogeneous pieces over all of `ℤ`, with no
hypothesis on which degrees are occupied
(`Stacks.RelativeSpec.intCoprodIsoUnderlyingModule_gradedModuleSheaf`).

Each step is given an explicit type. Composing them as one anonymous chain of `Iso.trans` sends
`isDefEq` into the heartbeat limit: the unifier is then asked to match
`∐ fun n => (ℱ.toLeftGradedModuleOfComm _).piece n` against `∐ fun n => ℱ.piece n` underneath a
restriction of scalars and a full-subcategory projection at once. Named with their types, the
same three isomorphisms check in seconds, and the one remaining reindexing is a
`Discrete.natIso` of identities.

**The four steps are top-level declarations, not `let`s**, so that the composite can be
evaluated on a coproduct inclusion one step at a time. The `X'`-level identity
`pushforwardPullbackIsoIntCoprod_inv` is stated at the level of isomorphisms; the summand-wise
form follows from it by `CategoryTheory.Category.assoc`.

The reindexing lemma `ι_comp_intCoprodIsoToLeftGradedModule_hom` goes through the abstract
`ι_comp_isoOfNatIsoRefl_hom` rather than rewriting in place. At the concrete `∐ fun n : ℤ => ℱₙ`
the goal left by `HasColimit.isoOfNatIso_ι_hom` is not type-correct at `implicit` transparency —
`Scheme.ringCatSheaf` is seen there at its `TopCat.Sheaf` spelling, not the
`Sheaf (Opens.grothendieckTopology _)` one `SheafOfModules` expects — and both `rw` and
`simp only` refuse it. The same applies to associativity: the two component lemmas reassociate
through `CategoryTheory.Category.assoc` applied as a *term*, where `rw [Category.assoc]` fails on
the same goals.

The transport to `X'` uses the projection's own isomorphism
`Stacks.AffineGradedAlgebra.baseChangeIsoRelativeSpecGradedTildePullback` in `Over X`: its image
under `Over.forget X` is an isomorphism `α : X' ≅ Spec_X(𝓑)` with
`α.hom ≫ relativeSpecToBase 𝓑 = π`, so `α.inv ≫ π = relativeSpecToBase 𝓑` and
pseudofunctoriality of the direct image carries the relative-spectrum statement across. The
module on `X'` is written as the inverse image along `α.hom` rather than the direct image along
`α.inv`, because quasi-coherence of an inverse image is available —
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor` through
`restrictFunctorIsoPullback` — while quasi-coherence of a direct image is not; the two are
identified by `AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace Stacks.RelativeSpec

/-- **Step 1 of `pushforwardIsoIntCoprod`: the direct image of `𝒪_X`-modules of the module
underlying `ℱ'` is the restriction of scalars of the value at `ℱ'` of the equivalence of
[Stacks, Tag 01SB].** This is
`Stacks.AffineAlgebraEquivalence.restrictScalars_relativeSpecQcohEquivalence_functor_obj` read as
an isomorphism. -/
public noncomputable def pushforwardIsoRestrictScalarsFunctorObj
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (F' : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory) :
    (Scheme.Modules.pushforward (relativeSpecToBase (gradedAlgebraSheaf X A hc))).obj F'.obj ≅
      (SheafOfModules.restrictScalars.{u}
          (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).obj
        ((relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj F').obj :=
  haveI := hA
  eqToIso (restrictScalars_relativeSpecQcohEquivalence_functor_obj
    (gradedAlgebraSheaf X A hc) F').symm

/-- **Step 2 of `pushforwardIsoIntCoprod`: the given `𝒜`-linear identification, read in the
ambient category of sheaves of modules over the algebra sheaf.** The full-subcategory inclusion
applied to `iso`. -/
public noncomputable def functorObjIsoGradedModuleSheaf
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A)
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (F' : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory)
    (iso : (relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj F' ≅
      qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF) :
    ((relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj F').obj ≅
      gradedModuleSheaf X A hc (F.toLeftGradedModuleOfComm hc) :=
  (ObjectProperty.ι _).mapIso iso

/-- The coproduct of the homogeneous pieces of a right graded module is isomorphic to the
coproduct of the pieces of the left graded module it presents, via the identity on each piece
(`SheafOfModules.GradedModule.toLeftGradedModuleOfComm_piece`). -/
public noncomputable def intCoprodIsoToLeftGradedModule
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A) :
    (∐ fun n : ℤ => F.piece n) ≅ ∐ fun n : ℤ => (F.toLeftGradedModuleOfComm hc).piece n :=
  HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

/-- **In any category, the reindexing of a coproduct along a `Discrete.natIso` of identities
fixes every coproduct inclusion.**

Stated for an abstract family in an abstract category on purpose. At the concrete
`∐ fun n : ℤ => ℱₙ` below, the goal left by `HasColimit.isoOfNatIso_ι_hom` is not type-correct
at `implicit` transparency — `Scheme.ringCatSheaf` is seen there at its `TopCat.Sheaf` spelling,
not the `Sheaf (Opens.grothendieckTopology _)` one that `SheafOfModules` expects — and both `rw`
and `simp only` refuse it. Here nothing can unfold into that mismatch, and the concrete
statement follows by a single application. -/
public theorem ι_comp_isoOfNatIsoRefl_hom {C : Type*} [Category C] {β : Type*} (g : β → C)
    [HasCoproduct g] (b : β) :
    Sigma.ι g b ≫ (HasColimit.isoOfNatIso
        (Discrete.natIso fun x => Iso.refl ((Discrete.functor g).obj x))).hom = Sigma.ι g b := by
  simp

/-- The `n`-th coproduct inclusion is carried to the `n`-th coproduct inclusion by the
reindexing of `intCoprodIsoToLeftGradedModule`. -/
public theorem ι_comp_intCoprodIsoToLeftGradedModule_hom
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A) (n : ℤ) :
    Sigma.ι (fun m : ℤ => F.piece m) n ≫ (intCoprodIsoToLeftGradedModule X A hc F).hom =
      Sigma.ι (fun m : ℤ => (F.toLeftGradedModuleOfComm hc).piece m) n :=
  ι_comp_isoOfNatIsoRefl_hom (fun m : ℤ => F.piece m) n

/-- **The direct image of `𝒪_X`-modules of a module on `Spec_X(𝒜)` identified with `∐ₙ ℱₙ`**,
given an isomorphism in the quasi-coherent `𝒜`-modules between its image under the equivalence
of [Stacks, Tag 01SB] and the ungraded realization of the graded module `ℱ`.

Three facts from the library compose: the functor of that equivalence is the direct image of
`𝒪_X`-modules once the `𝒜`-action is forgotten
(`Stacks.AffineAlgebraEquivalence.restrictScalars_relativeSpecQcohEquivalence_functor_obj`); the
given isomorphism, read in the ambient category; and the `𝒪_X`-module underlying
`gradedModuleSheaf` is the coproduct of the homogeneous pieces over all of `ℤ`
(`intCoprodIsoUnderlyingModule_gradedModuleSheaf`).

Each step is given an explicit type. Composing them as one anonymous chain of `Iso.trans` sends
`isDefEq` into the heartbeat limit: the unifier is then asked to match
`∐ fun n => (ℱ.toLeftGradedModuleOfComm _).piece n` against `∐ fun n => ℱ.piece n` underneath a
restriction of scalars and a full-subcategory projection at once. Named with their types, the
same three isomorphisms check in seconds, and the one remaining reindexing is a
`Discrete.natIso` of identities.

The four steps are *named declarations* — `pushforwardIsoRestrictScalarsFunctorObj`,
`functorObjIsoGradedModuleSheaf`, `intCoprodIsoUnderlyingModule_gradedModuleSheaf` and
`intCoprodIsoToLeftGradedModule` — and not `let`s in this body. As `let`s they would not be
addressable from outside, so there would be no way to evaluate this isomorphism on a coproduct
inclusion short of reproving the whole chain; `ι_comp_pushforwardIsoIntCoprod_inv` is what the
naming buys. -/
public noncomputable def pushforwardIsoIntCoprod
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A)
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (F' : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory)
    (iso : (relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj F' ≅
      qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF) :
    (Scheme.Modules.pushforward (relativeSpecToBase (gradedAlgebraSheaf X A hc))).obj F'.obj ≅
      ∐ fun n : ℤ => F.piece n :=
  (pushforwardIsoRestrictScalarsFunctorObj X A hc hA F').trans
    (((SheafOfModules.restrictScalars.{u}
        (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).mapIso
          (functorObjIsoGradedModuleSheaf X A hc F hA hF F' iso)).trans
      ((intCoprodIsoUnderlyingModule_gradedModuleSheaf X A hc
          (F.toLeftGradedModuleOfComm hc)).symm.trans
        (intCoprodIsoToLeftGradedModule X A hc F).symm))

/-- The inverse of `pushforwardIsoIntCoprod`, as the composite of the four named steps. This is
the definitional unfolding, written out once so that no consumer has to perform it. -/
public theorem pushforwardIsoIntCoprod_inv
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A)
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (F' : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory)
    (iso : (relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj F' ≅
      qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF) :
    (pushforwardIsoIntCoprod X A hc F hA hF F' iso).inv =
      (intCoprodIsoToLeftGradedModule X A hc F).hom ≫
        (intCoprodIsoUnderlyingModule_gradedModuleSheaf X A hc
          (F.toLeftGradedModuleOfComm hc)).hom ≫
        (SheafOfModules.restrictScalars.{u}
            (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).map
          (functorObjIsoGradedModuleSheaf X A hc F hA hF F' iso).inv ≫
        (pushforwardIsoRestrictScalarsFunctorObj X A hc hA F').inv :=
  rfl

/-- **The value of `pushforwardIsoIntCoprod` on the `n`-th coproduct inclusion.** Reading
`∐ₙ ℱₙ ≅ π_* ℱ'` on the summand of degree `n` is the `n`-th inclusion into the `𝒪_X`-module
underlying `gradedModuleSheaf`, followed by the identification `iso` with the scalars forgotten
and by the identification of that restriction of scalars with the direct image.

This is the component lemma the sheaf-level comparison of the degreewise action needs: the
degreewise action is given one summand at a time, so a statement about `π_* ℱ'` can only be
checked against it summand by summand. Until the four steps above were named there was no way
to write it down. -/
public theorem ι_comp_pushforwardIsoIntCoprod_inv
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A)
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (F' : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedAlgebraSheaf X A hc)).ringCatSheaf).FullSubcategory)
    (iso : (relativeSpecQcohEquivalence (gradedAlgebraSheaf X A hc)).functor.obj F' ≅
      qcohGradedModuleSheafOfRightOfPiece X A hc F hA hF)
    (n : ℤ) :
    Sigma.ι (fun m : ℤ => F.piece m) n ≫
        (pushforwardIsoIntCoprod X A hc F hA hF F' iso).inv =
      Sigma.ι (fun m : ℤ => (F.toLeftGradedModuleOfComm hc).piece m) n ≫
        (intCoprodIsoUnderlyingModule_gradedModuleSheaf X A hc
          (F.toLeftGradedModuleOfComm hc)).hom ≫
        (SheafOfModules.restrictScalars.{u}
            (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).map
          (functorObjIsoGradedModuleSheaf X A hc F hA hF F' iso).inv ≫
        (pushforwardIsoRestrictScalarsFunctorObj X A hc hA F').inv :=
  Eq.trans
    (congrArg (fun z => Sigma.ι (fun m : ℤ => F.piece m) n ≫ z)
      (pushforwardIsoIntCoprod_inv X A hc F hA hF F' iso))
    (Eq.trans (Category.assoc _ _ _).symm
      (congrArg (fun z => z ≫
          (intCoprodIsoUnderlyingModule_gradedModuleSheaf X A hc
            (F.toLeftGradedModuleOfComm hc)).hom ≫
          (SheafOfModules.restrictScalars.{u}
              (AlgebraSheaf.structureMap (gradedAlgebraSheaf X A hc))).map
            (functorObjIsoGradedModuleSheaf X A hc F hA hF F' iso).inv ≫
          (pushforwardIsoRestrictScalarsFunctorObj X A hc hA F').inv)
        (ι_comp_intCoprodIsoToLeftGradedModule_hom X A hc F n)))

/-- **The module `ℱ'` of the proof of [Stacks, Tag 0897], over the relative spectrum.** For a
sheaf `𝒜` of graded `𝒪_X`-algebras with commutative homogeneous multiplication whose ungraded
realization is quasi-coherent, and a graded `𝒜`-module `ℱ` with quasi-coherent pieces, there is
a quasi-coherent module on `Spec_X(𝒜)` whose direct image of `𝒪_X`-modules along the structure
morphism is the coproduct `∐ₙ ℱₙ` of the homogeneous pieces.

Unlike `exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece`, whose
isomorphism lives in the quasi-coherent `𝒜`-modules, the direct image here is the direct image
of `𝒪_X`-modules, which is what a cohomology comparison along the structure morphism
consumes. -/
public theorem exists_isQuasicoherent_pushforward_relativeSpecToBase_iso_intCoprod
    (X : Scheme.{u}) (A : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf)
    (hc : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (F : SheafOfModules.GradedModule.{u, u, u} A)
    (hA : AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hc))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    ∃ G : SheafOfModules.{u} (relativeSpec (gradedAlgebraSheaf X A hc)).ringCatSheaf,
      G.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pushforward
          (relativeSpecToBase (gradedAlgebraSheaf X A hc))).obj G ≅
        ∐ fun n : ℤ => F.piece n) := by
  obtain ⟨F', ⟨iso⟩⟩ :=
    exists_iso_relativeSpecQcohPushforward_gradedModuleSheafOfRight_of_piece X A hc F hA hF
  exact ⟨F'.obj, F'.property, ⟨pushforwardIsoIntCoprod X A hc F hA hF F' iso⟩⟩

end Stacks.RelativeSpec

namespace Stacks.AffineGradedAlgebra

attribute [local instance] isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback

variable {X : Scheme.{u}} (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜] [DirectSum.Decomposition 𝒜]
  (f : X ⟶ Spec (CommRingCat.of A))

/-- **The identification `X' ≅ Spec_X(𝓑)` of [Stacks, Tag 01LX] at `𝓑 = f^* B̃`, as schemes.**
This is `baseChangeIsoRelativeSpecGradedTildePullback`, which is an isomorphism in `Over X`,
read through `Over.forget X`. -/
public noncomputable def baseChangeIsoRelativeSpec :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f ≅
      relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f) :=
  (Over.forget X).mapIso (baseChangeIsoRelativeSpecGradedTildePullback A 𝒜 f)

/-- The identification of schemes commutes with the two morphisms to `X`. -/
public theorem baseChangeIsoRelativeSpec_inv_comp_snd :
    (baseChangeIsoRelativeSpec A 𝒜 f).inv ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f =
      relativeSpecToBase (gradedTildePullbackAlgebraSheaf A 𝒜 f) :=
  (Iso.inv_comp_eq (baseChangeIsoRelativeSpec A 𝒜 f)).2
    (Over.w (baseChangeIsoRelativeSpecGradedTildePullback A 𝒜 f).hom).symm

/-- **The inverse image along `X' ≅ Spec_X(𝓑)` of a quasi-coherent module is quasi-coherent.**
The inverse image is written as a `Scheme.Modules.pullback` rather than as a direct image along
the inverse because quasi-coherence of a restriction is what the library has. -/
public theorem isQuasicoherent_pullback_baseChangeIsoRelativeSpec
    (G : (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pullback (baseChangeIsoRelativeSpec A 𝒜 f).hom).obj G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback (baseChangeIsoRelativeSpec A 𝒜 f).hom).app G)
    (Scheme.Modules.isQuasicoherent_restrictFunctor (baseChangeIsoRelativeSpec A 𝒜 f).hom G)

/-- **Transport of the direct image along `X' ≅ Spec_X(𝓑)`**: the direct image along the
projection `π = pullback.snd` of the inverse image of `𝒢` is the direct image of `𝒢` along the
structure morphism of the relative spectrum.

Pseudofunctoriality of the direct image carries it across, once the inverse image along
`α.hom` is rewritten as the direct image along `α.inv` by
`AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward`. -/
public noncomputable def pushforwardPullbackBaseChangeIso
    (G : (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).Modules) :
    (Scheme.Modules.pushforward
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj
        ((Scheme.Modules.pullback (baseChangeIsoRelativeSpec A 𝒜 f).hom).obj G) ≅
      (Scheme.Modules.pushforward
        (relativeSpecToBase (gradedTildePullbackAlgebraSheaf A 𝒜 f))).obj G :=
  ((Scheme.Modules.pushforward
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).mapIso
      ((Scheme.Modules.pullbackIsoPushforward
        (baseChangeIsoRelativeSpec A 𝒜 f).symm).app G)).trans
    (((Scheme.Modules.pushforwardComp (baseChangeIsoRelativeSpec A 𝒜 f).inv
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).app G).trans
      ((Scheme.Modules.pushforwardCongr
        (baseChangeIsoRelativeSpec_inv_comp_snd A 𝒜 f)).app G))

/-- **The `𝒪_{X'}`-module attached to a module on `Spec_X(𝓑)`**: its inverse image along the
identification `X' ≅ Spec_X(𝓑)` of [Stacks, Tag 01LX]. The module `ℱ'` of the proof of
[Stacks, Tag 0897] is this, at the module on the relative spectrum that [Stacks, Tag 01SB]
produces. -/
public abbrev baseChangeModuleOfRelativeSpec
    (G : (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).Modules) :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f).Modules :=
  (Scheme.Modules.pullback (baseChangeIsoRelativeSpec A 𝒜 f).hom).obj G

/-- **The ungraded realization of the graded `𝓑`-module `ℱ`, read as a quasi-coherent
`𝓑`-module.** This is the target of the identification [Stacks, Tag 01SB] produces at
`𝓑 = f^* B̃`: `Stacks.RelativeSpec.qcohGradedModuleSheafOfRightOfPiece` with the arguments that
`𝓑 = f^* B̃` fixes filled in. -/
public abbrev qcohGradedTildePullbackModule
    (F : SheafOfModules.GradedModule.{u, u, u}
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent
      (AlgebraSheaf.ringSheaf (gradedTildePullbackAlgebraSheaf A 𝒜 f))).FullSubcategory :=
  Stacks.RelativeSpec.qcohGradedModuleSheafOfRightOfPiece X
    (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
    (gradedTildePullback_mul_comm A 𝒜 f) F
    (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f) hF

/-- **The identification `π_* ℱ' ≅ ∐ₙ ℱₙ` of `𝒪_X`-modules read off an identification in the
quasi-coherent `𝓑`-modules.** For `ℱ'` the inverse image of `𝒢` along `X' ≅ Spec_X(𝓑)`, this is
`pushforwardPullbackBaseChangeIso` followed by `Stacks.RelativeSpec.pushforwardIsoIntCoprod`.

It is a *total function* of the `𝓑`-linear identification `isoAlg`, which is what makes it
usable where the `𝒪_X`-module identification alone is not: a consumer that builds its
`π_* ℱ' ≅ ∐ₙ ℱₙ` this way still holds `isoAlg`, and so still knows the `Γ(𝓑, U)`-action the
identification respects. An identification chosen from a bare `Nonempty` of `𝒪_X`-module
isomorphisms carries none. -/
public noncomputable def pushforwardPullbackIsoIntCoprod
    (F : SheafOfModules.GradedModule.{u, u, u}
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (G : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).ringCatSheaf).FullSubcategory)
    (isoAlg : (relativeSpecQcohEquivalence
        (gradedTildePullbackAlgebraSheaf A 𝒜 f)).functor.obj G ≅
      qcohGradedTildePullbackModule A 𝒜 f F hF) :
    (Scheme.Modules.pushforward
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj
        (baseChangeModuleOfRelativeSpec A 𝒜 f G.obj) ≅
      ∐ fun n : ℤ => F.piece n :=
  (pushforwardPullbackBaseChangeIso A 𝒜 f G.obj).trans
    (Stacks.RelativeSpec.pushforwardIsoIntCoprod X
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
      (gradedTildePullback_mul_comm A 𝒜 f) F
      (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f) hF G isoAlg)

/-- **The inverse of `pushforwardPullbackIsoIntCoprod`, with the transport along
`X' ≅ Spec_X(𝓑)` peeled off**: it is the relative-spectrum inverse followed by
`pushforwardPullbackBaseChangeIso.inv`.

This is the half of the component that the transport to `X'` hid. `Iso.trans` puts
`pushforwardPullbackBaseChangeIso.inv` *after* the relative-spectrum inverse, so a consumer
working on `X'` could not reach the relative-spectrum component at all; with this and
`CategoryTheory.Category.assoc` the value on the degree-`n` summand of `∐ₙ ℱₙ` is
`Stacks.RelativeSpec.ι_comp_pushforwardIsoIntCoprod_inv` followed by that transport.

Stated at the level of the isomorphisms rather than with a coproduct inclusion in it, because
the inclusion form costs about 11 s of elaboration warm — and some minutes cold — all
of it in the statement, because `pushforwardPullbackIsoIntCoprod`'s own arguments have to be
written out again inside a composite. This form costs a fraction of that and the consumer loses
one `Category.assoc`. -/
public theorem pushforwardPullbackIsoIntCoprod_inv
    (F : SheafOfModules.GradedModule.{u, u, u}
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent)
    (G : (SheafOfModules.isQuasicoherent
      (relativeSpec (gradedTildePullbackAlgebraSheaf A 𝒜 f)).ringCatSheaf).FullSubcategory)
    (isoAlg : (relativeSpecQcohEquivalence
        (gradedTildePullbackAlgebraSheaf A 𝒜 f)).functor.obj G ≅
      qcohGradedTildePullbackModule A 𝒜 f F hF) :
    (pushforwardPullbackIsoIntCoprod A 𝒜 f F hF G isoAlg).inv =
      (Stacks.RelativeSpec.pushforwardIsoIntCoprod X
          (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
          (gradedTildePullback_mul_comm A 𝒜 f) F
          (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f) hF G isoAlg).inv ≫
        (pushforwardPullbackBaseChangeIso A 𝒜 f G.obj).inv :=
  rfl

/-- **The module `ℱ'` of the proof of [Stacks, Tag 0897], on the base change
`X' = Spec(B) ×_{Spec A} X`.** For a graded `A`-algebra `B`, a morphism `f : X ⟶ Spec A` and a
graded `f^* B̃`-module `ℱ` with quasi-coherent pieces, there is a quasi-coherent
`𝒪_{X'}`-module whose direct image along the projection `π = pullback.snd` is the coproduct
`∐ₙ ℱₙ` of the homogeneous pieces.

Nothing is assumed of `f` beyond its target: properness enters [Stacks, Tag 0897] only through
the finiteness it feeds, not through the construction of `ℱ'`.

This is the relative-spectrum statement
`Stacks.RelativeSpec.exists_isQuasicoherent_pushforward_relativeSpecToBase_iso_intCoprod`
transported along `baseChangeIsoRelativeSpecGradedTildePullback`, which is [Stacks, Tag 01LX] at
`𝓑 = f^* B̃`. -/
public theorem exists_isQuasicoherent_pushforward_baseChange_iso_intCoprod
    (F : SheafOfModules.GradedModule.{u, u, u}
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜)))
    (hF : ∀ n : ℤ, (F.piece n).IsQuasicoherent) :
    ∃ F' : (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) f).Modules,
      F'.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pushforward
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B))) f)).obj F' ≅
          ∐ fun n : ℤ => F.piece n) := by
  obtain ⟨G, hG, ⟨isoG⟩⟩ :=
    Stacks.RelativeSpec.exists_isQuasicoherent_pushforward_relativeSpecToBase_iso_intCoprod X
      (Stacks.Conormal.gradedPullback f (gradedTildeOf A 𝒜))
      (gradedTildePullback_mul_comm A 𝒜 f) F
      (isQuasicoherent_gradedAlgebraSheaf_gradedTildePullback A 𝒜 f) hF
  have := hG
  exact ⟨(Scheme.Modules.pullback (baseChangeIsoRelativeSpec A 𝒜 f).hom).obj G,
    isQuasicoherent_pullback_baseChangeIsoRelativeSpec A 𝒜 f G,
    ⟨(pushforwardPullbackBaseChangeIso A 𝒜 f G).trans isoG⟩⟩

end Stacks.AffineGradedAlgebra

end
