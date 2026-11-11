module

public import StacksFrontier.AlgebraicGeometry.Duality.PullbackShiftedUnitTensor
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceCoheratorQCQS
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafy trace map on global derived Hom, for a quasi-compact quasi-separated morphism

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y`
quasi-compact, let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and let `L` in
`D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)`. [Stacks, Tag 0B6I] says that the sheafy trace map of
[Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

induces an isomorphism `R Hom_X(L, a(K)) ⟶ R Hom_Y(Rf_*L, K)` of global derived Homs.

`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHom.lean` proves this with the two
geometric inputs of the chain of five bijections of [Stacks, Tag 0A9Q] — the projection formula
of [Stacks, Tag 08EU] and the quasi-coherence of `Lf^*M ⊗^L_{𝒪_X} L` of [Stacks, Tag 08DX]
part (1) — and the quasi-coherence of `Rf_*` of [Stacks, Tag 08D5] part (1) as hypotheses. This
file proves them from the hypotheses the tag states.

## Main results

* `Stacks.Duality.bijective_comp_sheafyTrace_of_isIso` — the chain of five bijections of
  [Stacks, Tag 0A9Q] at a single object `M` of `D_QCoh(𝒪_Y)`, with the two geometric inputs asked
  for at that `M` only. `Stacks.Duality.bijective_comp_sheafyTrace` asks for them at every `M`;
  this form is what can be supplied at the one `M = 𝒪_Y⟦-n⟧` the proof of [Stacks, Tag 0B6I]
  uses, where the quasi-coherence of the tensor product is available without
  [Stacks, Tag 08DX].
* `Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs` — **[Stacks, Tag 0B6I]**:
  in every degree `n` the sheafy trace map induces a bijection on the morphism groups out of
  `𝒪_Y⟦-n⟧`, that is on the degree-`n` cohomology of the two global derived Homs, with no input
  of Tag 0A9Q a hypothesis.
* `Stacks.Duality.bijective_derivedPullbackHom_comp_sheafyTrace_of_qcqs` — the same bijection
  with its source transported to a morphism group on `X` by the adjunction `Lf^* ⊣ Rf_*`.

## Implementation notes

*`a` and the adjunction are the tag's data.* The statement of [Stacks, Tag 0B6I] is written with
`a(K)` in it and its map is built from the counit of `Rf_* ⊣ a`, so the functor and the
adjunction are what the tag is about: the existence assertion is the separate
[Stacks, Tag 0A9E]. They are therefore parameters, as they are of the trace map itself in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTrace.lean`, and the statements below hold for
*every* right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and every adjunction exhibiting it.
Tag 0A9E is proved, for `X` and `Y` quasi-compact and quasi-separated and at every model of the
derived categories, the standard one among them, as
`Stacks.Duality.AnyModel.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`, so such an `a`
exists; `Stacks.Duality.AnyModel.standardTwistedInverseImage` is one.

*What is derived.* From the quasi-compactness and quasi-separatedness of `f` and the
quasi-compactness of `Y`:

* that `Rf_*` preserves quasi-coherence of the cohomology sheaves — part (1) of
  [Stacks, Tag 08D5], needed to write `a` down at all — is
  `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_qcqs`;
* the projection formula of [Stacks, Tag 08EU], in the tensor slot the relative cup product
  uses, is `Stacks.Duality.isIso_pullbackProjectionFormulaMap`;
* the quasi-coherence of `Lf^*M ⊗^L_{𝒪_X} L` is supplied at the one `M` the proof uses —
  `M = 𝒪_Y⟦-n⟧` — by `Stacks.RingedSpace.pullbackShiftedUnitTensorIso`, which identifies that
  object with `L⟦-n⟧`, together with the stability of `D_QCoh(𝒪_X)` under shifts.

*Why the proofs are in term mode.* As in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceCoherator.lean`: a statement mentioning both
`DerivedCategory X.Modules` and the derived tensor product indexed by `X.sheaf` is well typed
only after unfolding `AlgebraicGeometry.Scheme.Modules`, which `rewrite` and `simp` do not do.

## References

* [Stacks Project, Tag 0B6I](https://stacks.math.columbia.edu/tag/0B6I)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  renaming derivedPullback → spaceDerivedPullback, derivedAdjunction → spaceDerivedAdjunction
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

-- Standard model only: `Stacks.Duality.sheafyTrace`, `Stacks.SheafOfModules.derivedSheafHom`.
attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The chain of five bijections at a single object -/

section Chain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-- **The chain of five bijections, at a single object.** Let `L` be an object of
`D_QCoh(𝒪_X)`, let `K` and `M` be objects of `D_QCoh(𝒪_Y)`, suppose `Lf^*M ⊗^L_{𝒪_X} L` has
quasi-coherent cohomology, and suppose the projection-formula map at `M` and `L` is an
isomorphism. Then precomposition with the sheafy trace map of [Stacks, Tag 0B6H] is a bijection

`Hom_Y(ι M, Rf_*R𝓗om_{𝒪_X}(L, a K)) ⟶ Hom_Y(ι M, R𝓗om_{𝒪_Y}(Rf_*L, K))`.

`Stacks.Duality.bijective_comp_sheafyTrace` is the same conclusion with the two hypotheses asked
at every object of `D_QCoh(𝒪_Y)`; here they are asked at the one `M` the conclusion is about,
which is all the argument uses. The proof is the same chain:
`Lf^* ⊣ Rf_*`, the tensor–internal-Hom bijection on `X`, `Rf_* ⊣ a`, the projection formula, and
the tensor–internal-Hom bijection on `Y`. -/
theorem bijective_comp_sheafyTrace_of_isIso (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) (M : quasiCoherentDerivedCategory Y)
    (hten : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((spaceDerivedPullback f.toLRSHom.toShHom).obj M.obj)).obj L.obj)).IsQuasicoherent)
    (h08EU : IsIso (pullbackProjectionFormulaMap f M.obj L.obj)) :
    Function.Bijective fun g : (ι _).obj M ⟶ (derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          (a.obj K).obj) => g ≫ sheafyTrace f DX DY hpush adj L K := by
  have hiso := h08EU
  set E : quasiCoherentDerivedCategory X :=
    ⟨((derivedTensorProductFunctor X.sheaf).obj
      ((spaceDerivedPullback f.toLRSHom.toShHom).obj M.obj)).obj L.obj, hten⟩
  set ee := ((spaceDerivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          (a.obj K).obj)).symm.trans
      ((DX.homEquiv ((spaceDerivedPullback f.toLRSHom.toShHom).obj M.obj) L.obj
            (a.obj K).obj).trans
        ((quasiCoherentCounitEquiv f hpush adj E K).trans
          (((asIso (pullbackProjectionFormulaMap f M.obj L.obj)).symm.homFromEquiv
              (Z := K.obj)).trans
            (DY.homEquiv M.obj ((derivedPushforward f).obj L.obj) K.obj).symm)))
  have key : ∀ g : (ι _).obj M ⟶ (derivedPushforward f).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj),
      g ≫ sheafyTrace f DX DY hpush adj L K =
        (DY.homEquiv M.obj ((derivedPushforward f).obj L.obj) K.obj).symm
          (pullbackProjectionFormulaMap f M.obj L.obj ≫
            quasiCoherentCounitEquiv f hpush adj E K
              (DX.homEquiv ((spaceDerivedPullback f.toLRSHom.toShHom).obj M.obj) L.obj
                (a.obj K).obj
                (((spaceDerivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
                  (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                    (a.obj K).obj)).symm g))) := by
    intro g
    refine (Equiv.eq_symm_apply _).2 ?_
    have hmap : (derivedPushforward f).map
            (((derivedTensorProductFunctor X.sheaf).map
              (((spaceDerivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
                (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                  (a.obj K).obj)).symm g)).app L.obj) ≫
          (derivedPushforward f).map (DX.evaluation L.obj (a.obj K).obj) =
        (derivedPushforward f).map
          (DX.homEquiv ((spaceDerivedPullback f.toLRSHom.toShHom).obj M.obj) L.obj (a.obj K).obj
            (((spaceDerivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
              (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                (a.obj K).obj)).symm g)) :=
      ((derivedPushforward f).map_comp _ _).symm.trans
        (congrArg (fun z => (derivedPushforward f).map z)
          ((DX.homEquiv_naturality_source _ (𝟙 _)).symm.trans
            (congrArg (DX.homEquiv _ _ _) (Category.comp_id _))))
    refine Eq.trans (homEquiv_comp_sheafyTrace f hpush adj DX DY L K M.obj g) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun t => t ≫ _) (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun t => (t ≫ _) ≫ _)
      (pullbackProjectionFormulaMap_comp_adjunct f M.obj L.obj g)) ?_
    refine Eq.trans (congrArg (fun t => t ≫ _) (Category.assoc _ _ _)) ?_
    refine Eq.trans (congrArg (fun t => (_ ≫ t) ≫ _) hmap) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun t => _ ≫ t)
      (quasiCoherentCounitEquiv_apply f hpush adj E K _).symm
  refine ⟨fun g₁ g₂ h => ee.injective ((key g₁).symm.trans (h.trans (key g₂))), fun w => ?_⟩
  exact ⟨ee.symm w, (key _).trans (ee.apply_symm_apply w)⟩

end Chain

/-! ### [Stacks, Tag 0B6I] -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f
    (isQuasicoherent_homology_derivedPushforward_qcqs f) ⊣ a)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-- **[Stacks, Tag 0B6I].** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes with `Y` quasi-compact, let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and let `L` be an object of `D_QCoh(𝒪_X)` and `K` one of
`D_QCoh(𝒪_Y)`. Then in every degree `n` the sheafy trace map of [Stacks, Tag 0B6H] induces a
bijection

`Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, Rf_*R𝓗om_{𝒪_X}(L, a K)) ⟶ Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, R𝓗om_{𝒪_Y}(Rf_*L, K))`,

that is, an isomorphism of global derived Homs `R Hom_X(L, a K) ⟶ R Hom_Y(Rf_*L, K)` read degree
by degree through `H^n(Y, E) = Ext^n_Y(𝒪_Y, E) = Hom(𝒪_Y⟦-n⟧, E)`.

No input of [Stacks, Tag 0A9Q] is a hypothesis. The projection formula of [Stacks, Tag 08EU] is
`Stacks.Duality.isIso_pullbackProjectionFormulaMap`; the quasi-coherence of
`Lf^*(𝒪_Y⟦-n⟧) ⊗^L_{𝒪_X} L` comes from
`Stacks.RingedSpace.pullbackShiftedUnitTensorIso`, which identifies that object with `L⟦-n⟧`,
and the stability of `D_QCoh(𝒪_X)` under shifts; and the quasi-coherence of `Rf_*` of part (1) of
[Stacks, Tag 08D5], which `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and hence `a` cannot be written
down without, is `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_qcqs`. All three
need only the quasi-compactness and quasi-separatedness of `f` and the quasi-compactness of `Y`,
which the tag states. `a` and `adj` are parameters because they are the tag's data: `a(K)` is
named by the statement of this tag and the trace map is built from the counit of `Rf_* ⊣ a`, so
quantifying over every right adjoint and every adjunction exhibiting it — which is what the
binders do — is stronger than fixing the one the source fixes. Their existence is the separate
[Stacks, Tag 0A9E], proved at this model as
`Stacks.Duality.AnyModel.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs`. The same holds
for `DX` and `DY`: the trace map is built from a tensor–internal-Hom adjunction of
[Stacks, Tag 08J8] on each side, the statement holds for every choice, and one exists, namely
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction`.

No coherator is needed in this form: the chain of five bijections of Tag 0A9Q is already a
statement about morphisms out of the quasi-coherent objects, and `𝒪_Y⟦-n⟧` is one of them. -/
@[stacks 0B6I "the whole lemma, for every right adjoint a of Rf_* on D_QCoh and every adjunction \
exhibiting it: a is the tag's own datum, the statement being written with a(K) in it and the map \
built from the counit, so the parameters a and adj quantify over more than the source's fixed \
choice rather than assuming anything; likewise DX and DY, every tensor-internal-hom adjunction of \
Tag 08J8 the trace map is built from, one being derivedTensorHomAdjunction. Nothing is assumed \
beyond these data: the projection formula of \
Tag 08EU, the quasi-coherence of Lf^*(O_Y[-n]) ⊗ᴸ L of Tag 08DX part (1) and the quasi-coherence \
of Rf_* of Tag 08D5 part (1) are all proved from the hypotheses the tag states, f quasi-compact \
and quasi-separated and Y quasi-compact. The two global derived homs are read degreewise as the \
morphism groups Hom(O_Y[-n], -) they corepresent by Tags 0B6A and 08DK, the left-hand one on Y \
after Rf_*, which is the source's own second expression RGamma(Y, Rf_* RHom(L, a(K))) for it"]
public theorem bijective_comp_sheafyTrace_structureSheaf_of_qcqs
    (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) (n : ℤ) :
    Function.Bijective (fun g : (ι _).obj (derivedStructureSheafInDegree Y n) ⟶
        (derivedPushforward f).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
            (a.obj K).obj) =>
      g ≫ sheafyTrace f DX DY (isQuasicoherent_homology_derivedPushforward_qcqs f) adj L K) :=
  bijective_comp_sheafyTrace_of_isIso f (isQuasicoherent_homology_derivedPushforward_qcqs f) adj
    DX DY L K (derivedStructureSheafInDegree Y n)
    (fun i => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules i).mapIso
        (Stacks.RingedSpace.pullbackShiftedUnitTensorIso f.toLRSHom.toShHom L.obj n).symm)
      (DerivedCategoryB.derivedCategoryB_shift_mem _
        (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
        (-n) L.2 i))
    (isIso_pullbackProjectionFormulaMap f (derivedStructureSheafInDegree Y n).obj L.obj
      (derivedStructureSheafInDegree Y n).2 L.2)

/-- **The bijection of [Stacks, Tag 0B6I] with its source on `X`.** Composing the bijection of
`Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs` with the adjunction
`Lf^* ⊣ Rf_*` moves the left-hand side to a morphism group on `X`: for every `n` the map

`Hom_{D(𝒪_X)}(Lf^*(𝒪_Y⟦-n⟧), R𝓗om_{𝒪_X}(L, a K)) ⟶
  Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, R𝓗om_{𝒪_Y}(Rf_*L, K))`

sending `u` to its adjunct followed by the trace map is a bijection. This is the first step of
the source's chain, [Stacks, Tag 079W]. What remains to recognise the left-hand side as
`Ext^n_X(L, a K)` is the identification of `Lf^*(𝒪_Y⟦-n⟧)` with `𝒪_X⟦-n⟧`. -/
public theorem bijective_derivedPullbackHom_comp_sheafyTrace_of_qcqs
    (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) (n : ℤ) :
    Function.Bijective (fun u : (spaceDerivedPullback f.toLRSHom.toShHom).obj
          (derivedStructureSheafInDegree Y n).obj ⟶
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj) =>
      (spaceDerivedAdjunction f.toLRSHom.toShHom).homEquiv
          (derivedStructureSheafInDegree Y n).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
            (a.obj K).obj) u ≫
        sheafyTrace f DX DY (isQuasicoherent_homology_derivedPushforward_qcqs f) adj L K) :=
  (bijective_comp_sheafyTrace_structureSheaf_of_qcqs f adj DX DY L K n).comp
    ((spaceDerivedAdjunction f.toLRSHom.toShHom).homEquiv _ _).bijective

end Stacks.Duality

end
