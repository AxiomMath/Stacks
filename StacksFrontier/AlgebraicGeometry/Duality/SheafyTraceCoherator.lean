module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTrace

/-!
# The sheafy trace map after applying the coherator

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and let `DQ : D(𝒪_Y) ⥤ D_QCoh(𝒪_Y)` be a right adjoint of
the inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` — the *coherator* of `Y`. For `L` in `D_QCoh(𝒪_X)` and `K`
in `D_QCoh(𝒪_Y)` the sheafy trace map of [Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

becomes an isomorphism after applying `DQ`. This is [Stacks, Tag 0A9Q].

Because `DQ` is right adjoint to the inclusion, a morphism of `D(𝒪_Y)` is sent by `DQ` to an
isomorphism as soon as it induces a bijection on morphisms out of `ι M` for every `M` in
`D_QCoh(𝒪_Y)`. For the trace map that bijection is the composition of five:

`Hom_Y(M, Rf_*R𝓗om_{𝒪_X}(L, a K))`
  `= Hom_X(Lf^*M, R𝓗om_{𝒪_X}(L, a K))`           by the adjunction `Lf^* ⊣ Rf_*`,
  `= Hom_X(Lf^*M ⊗^L_{𝒪_X} L, a K)`               by the tensor–internal-Hom bijection on `X`,
  `= Hom_Y(Rf_*(Lf^*M ⊗^L_{𝒪_X} L), K)`           by the adjunction `Rf_* ⊣ a`,
  `= Hom_Y(M ⊗^L_{𝒪_Y} Rf_*L, K)`                 by the projection formula,
  `= Hom_Y(M, R𝓗om_{𝒪_Y}(Rf_*L, K))`              by the tensor–internal-Hom bijection on `Y`.

That this composition is precomposition with the trace map is where the shape of the trace map
enters. The trace map is built from the relative cup product of [Stacks, Tag 0B68], and the
projection-formula map is the relative cup product preceded by the unit of `Lf^* ⊣ Rf_*`; so the
third and fourth lines above are joined by naturality of the relative cup product in its first
variable, which is `Stacks.Duality.pullbackProjectionFormulaMap_comp`.

## Main definitions

* `Stacks.Duality.quasiCoherentCounitEquiv` — the defining bijection of the right adjoint `a`,
  read in the ambient derived categories: `Hom_X(E, a K) ≃ Hom_Y(Rf_*E, K)` for `E` in
  `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)`.
* `Stacks.Duality.pullbackProjectionFormulaMap` — the projection-formula map
  `M ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*(Lf^*M ⊗^L_{𝒪_X} L)` of [Stacks, Tag 0B53], with the derived pullback
  in the first tensor factor: the unit of `Lf^* ⊣ Rf_*` in the first factor followed by the
  relative cup product.

## Main results

* `Stacks.Duality.isIso_coherator_map_of_bijective` — a morphism of `D(𝒪_Y)` inducing a
  bijection on morphisms out of every object of `D_QCoh(𝒪_Y)` is sent to an isomorphism by any
  right adjoint of the inclusion.
* `Stacks.Duality.pullbackProjectionFormulaMap_comp` and
  `Stacks.Duality.pullbackProjectionFormulaMap_comp_adjunct` — the compatibility of the relative
  cup product with the projection-formula map.
* `Stacks.Duality.homEquiv_comp_sheafyTrace` — the adjunct of precomposition with the trace map
  under the tensor–internal-Hom bijection on `Y`: the relative cup product followed by `Rf_*` of
  the evaluation morphism and the counit of `Rf_* ⊣ a`.
* `Stacks.Duality.bijective_comp_sheafyTrace` — the chain above: precomposition with the trace
  map is a bijection on morphisms out of every object of `D_QCoh(𝒪_Y)`.
* [Stacks, Tag 0A9Q] itself, for quasi-compact quasi-separated schemes, is
  `Stacks.Duality.isIso_coherator_map_sheafyTrace_of_qcqs` of
  `StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceCoheratorQCQS.lean`, deduced from the two
  results above on `isIso_coherator_map_of_bijective` and `bijective_comp_sheafyTrace`.

## Implementation notes

*The coherator is a hypothesis.* The source obtains `DQ` from [Stacks, Tag 0CR0], the existence
of a right adjoint of `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` for a quasi-compact quasi-separated scheme; that
existence statement is not available in this development. The conclusion of Tag 0A9Q cannot even
be written down without `DQ`, so `DQ` and the adjunction `ι ⊣ DQ` are carried as hypotheses.
Nothing below uses more about them than the adjunction, which is all the source's argument uses
either. For the same reason the quasi-compactness and quasi-separatedness of `Y` are absent:
they are what produce `DQ`, and they enter only through the adjunction.

*The projection formula is a hypothesis.* The invertibility of the projection-formula map for
complexes with quasi-coherent cohomology along a quasi-compact quasi-separated morphism is
[Stacks, Tag 08EU], and it is the step the source singles out as the important one. It is not
proved in this development — the map of [Stacks, Tag 0B53] is constructed here, but no
invertibility statement for it is — so it appears as the hypothesis `h08EU`. Likewise the
quasi-coherence of `Lf^*M ⊗^L_{𝒪_X} L`, which is [Stacks, Tag 08DX] part (1) and is what makes
the third line of the chain a statement about `D_QCoh`, appears as the hypothesis `hten`: the
form of that tag in the library is stated at `Stacks.SheafOfModules.derivedTensor`, whereas the
relative cup product from which the trace map is built lands in
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, and the two tensor products are
not definitionally equal; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTrace.lean`.

*The right adjoint of pushforward is a hypothesis, as it is for the trace map itself.* `a` and
the adjunction `Rf_* ⊣ a` are carried exactly as `Stacks.Duality.sheafyTrace` carries them.

*Why the proofs are in term mode.* `AlgebraicGeometry.Scheme.Modules` is a semireducible
definition, so a statement mentioning both `DerivedCategory X.Modules` and the derived tensor
product indexed by `X.sheaf` is well typed only after unfolding it. The `rewrite` and `simp`
tactics check the terms they build at a reduced transparency and fail on such goals, so the
equalities below are composed from `congrArg` and `CategoryTheory.Category.assoc` instead. The
adjunction bijection `CategoryTheory.Adjunction.homEquiv` is a plain structure projection, so
its unit and counit formulas hold definitionally and need no rewriting at all.

## References

* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0B69](https://stacks.math.columbia.edu/tag/0B69)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedAdjunction)
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Two elementary bijections -/

/-- Precomposition with an isomorphism `i : A ⟶ B` is a bijection `(B ⟶ T) ≃ (A ⟶ T)`. -/
private def precompIsoEquiv {C : Type*} [Category C] {A B : C} (i : A ⟶ B) [IsIso i] (T : C) :
    (B ⟶ T) ≃ (A ⟶ T) where
  toFun u := i ≫ u
  invFun v := inv i ≫ v
  left_inv u := by simp
  right_inv v := by simp

/-- Composing a morphism into an internal Hom with the evaluation morphism is the
tensor–internal-Hom bijection. -/
private lemma tensorHom_comp_evaluation {C : Type*} [Category C] {T : C ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ C} (D : TensorHomAdjunction T H) {A : C} (L M : C)
    (u : A ⟶ (H.obj (op L)).obj M) :
    (T.map u).app L ≫ D.evaluation L M = D.homEquiv A L M u := by
  have h := D.homEquiv_naturality_source u (𝟙 ((H.obj (op L)).obj M))
  rw [Category.comp_id] at h
  exact h.symm

/-! ### The coherator criterion -/

section Coherator

variable {Y : Scheme.{u}}
  (DQ : DerivedCategory Y.Modules ⥤ quasiCoherentDerivedCategory Y)
  (adjQ : (DerivedCategoryB.derivedCategoryB
    (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⊣ DQ)

include adjQ in
/-- **The criterion by which a statement about the coherator becomes a statement about morphisms
out of the quasi-coherent objects.** Let `DQ : D(𝒪_Y) ⥤ D_QCoh(𝒪_Y)` be a right adjoint of the
inclusion `ι : D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`. If a morphism `φ` of `D(𝒪_Y)` induces a bijection
`Hom_Y(ι M, A) ⟶ Hom_Y(ι M, B)` for every object `M` of `D_QCoh(𝒪_Y)`, then `DQ(φ)` is an
isomorphism.

Indeed the adjunction identifies `Hom(M, DQ(-))` with `Hom(ι M, -)`, so the hypothesis says
exactly that precomposition with `DQ(φ)` is a bijection on morphisms out of every object of
`D_QCoh(𝒪_Y)`, and a morphism with that property is an isomorphism. -/
theorem isIso_coherator_map_of_bijective {A B : DerivedCategory Y.Modules} (φ : A ⟶ B)
    (h : ∀ M : quasiCoherentDerivedCategory Y,
      Function.Bijective fun g : (ι _).obj M ⟶ A => g ≫ φ) :
    IsIso (DQ.map φ) := by
  refine isIso_of_yoneda_map_bijective _ fun M => ?_
  have key : (fun g : M ⟶ DQ.obj A => g ≫ DQ.map φ) =
      (adjQ.homEquiv M B) ∘ (fun g : (ι _).obj M ⟶ A => g ≫ φ) ∘ (adjQ.homEquiv M A).symm := by
    funext g
    simp only [Function.comp_apply, adjQ.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [key]
  exact (adjQ.homEquiv M B).bijective.comp ((h M).comp (adjQ.homEquiv M A).symm.bijective)

end Coherator

/-! ### The right adjoint of pushforward, read in the ambient derived categories -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

include hpush adj in
/-- **The defining bijection of the right adjoint `a`, read in the ambient derived
categories.** For `E` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` the adjunction `Rf_* ⊣ a` on the
quasi-coherent derived categories gives a bijection

`Hom_{D(𝒪_X)}(E, a(K)) ≃ Hom_{D(𝒪_Y)}(Rf_*E, K)`,

the inclusions of the quasi-coherent derived categories being fully faithful. -/
def quasiCoherentCounitEquiv (E : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    (E.obj ⟶ (a.obj K).obj) ≃ ((derivedPushforward f).obj E.obj ⟶ K.obj) :=
  ((fullyFaithfulι _).homEquiv (X := E) (Y := a.obj K)).symm.trans
    ((adj.homEquiv E K).symm.trans ((fullyFaithfulι _).homEquiv))

/-- The bijection of `Stacks.Duality.quasiCoherentCounitEquiv` is `Rf_*` followed by the counit
of `Rf_* ⊣ a`. -/
theorem quasiCoherentCounitEquiv_apply (E : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) (v : E.obj ⟶ (a.obj K).obj) :
    quasiCoherentCounitEquiv f hpush adj E K v =
      (derivedPushforward f).map v ≫ (ι _).map (adj.counit.app K) :=
  rfl

/-! ### The projection-formula map with the pullback in the first factor -/

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The projection-formula map of [Stacks, Tag 0B53] with the derived pullback in the first
tensor factor.** For `M` in `D(𝒪_Y)` and `L` in `D(𝒪_X)` the canonical map

`M ⊗^L_{𝒪_Y} Rf_*L ⟶ Rf_*(Lf^*M ⊗^L_{𝒪_X} L)`:

the unit `M ⟶ Rf_*Lf^*M` of `Lf^* ⊣ Rf_*` in the first tensor factor, followed by the relative
cup product of [Stacks, Tag 0B68] at `Lf^*M` and `L`. Its invertibility for complexes with
quasi-coherent cohomology along a quasi-compact quasi-separated morphism is
[Stacks, Tag 08EU]. -/
def pullbackProjectionFormulaMap (M : DerivedCategory Y.Modules)
    (L : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor Y.sheaf).obj M).obj ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullback f.toLRSHom.toShHom).obj M)).obj L) :=
  ((derivedTensorProductFunctor Y.sheaf).map
      ((derivedAdjunction f.toLRSHom.toShHom).unit.app M)).app
      ((derivedPushforward f).obj L) ≫
    relativeCupProduct f.toLRSHom.toShHom
      ((derivedPullback f.toLRSHom.toShHom).obj M) L

/-- **The relative cup product against the projection-formula map.** Let `u : Lf^*M ⟶ N` and let
`L` be an object of `D(𝒪_X)`. Tensoring the adjunct `M ⟶ Rf_*N` of `u` with `Rf_*L` and
following with the relative cup product at `N` and `L` is the projection-formula map at `M` and
`L` followed by `Rf_*` of `u ⊗ 1_L`.

This is naturality of the relative cup product in its first variable, applied to `u`, together
with the factorisation of the adjunct of `u` through the unit of `Lf^* ⊣ Rf_*`. -/
theorem pullbackProjectionFormulaMap_comp (M : DerivedCategory Y.Modules)
    {N : DerivedCategory X.Modules} (L : DerivedCategory X.Modules)
    (u : (derivedPullback f.toLRSHom.toShHom).obj M ⟶ N) :
    ((derivedTensorProductFunctor Y.sheaf).map
          ((derivedAdjunction f.toLRSHom.toShHom).homEquiv M N u)).app
        ((derivedPushforward f).obj L) ≫
        relativeCupProduct f.toLRSHom.toShHom N L =
      pullbackProjectionFormulaMap f M L ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.sheaf).map u).app L) := by
  have hsplit : ((derivedTensorProductFunctor Y.sheaf).map
        ((derivedAdjunction f.toLRSHom.toShHom).homEquiv M N u)).app
        ((derivedPushforward f).obj L) =
      ((derivedTensorProductFunctor Y.sheaf).map
          ((derivedAdjunction f.toLRSHom.toShHom).unit.app M)).app
          ((derivedPushforward f).obj L) ≫
        ((derivedTensorProductFunctor Y.sheaf).map
          ((derivedPushforward f).map u)).app ((derivedPushforward f).obj L) :=
    congrArg (fun t => NatTrans.app t ((derivedPushforward f).obj L))
      ((derivedTensorProductFunctor Y.sheaf).map_comp _ _)
  refine Eq.trans (congrArg (fun t => t ≫ relativeCupProduct f.toLRSHom.toShHom N L) hsplit) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => _ ≫ t)
    (relativeCupProduct_natural_left f.toLRSHom.toShHom u L)) ?_
  exact (Category.assoc _ _ _).symm

/-- `Stacks.Duality.pullbackProjectionFormulaMap_comp` written at a morphism `g : M ⟶ Rf_*N`
rather than at its adjunct. -/
theorem pullbackProjectionFormulaMap_comp_adjunct (M : DerivedCategory Y.Modules)
    {N : DerivedCategory X.Modules} (L : DerivedCategory X.Modules)
    (g : M ⟶ (derivedPushforward f).obj N) :
    ((derivedTensorProductFunctor Y.sheaf).map g).app ((derivedPushforward f).obj L) ≫
        relativeCupProduct f.toLRSHom.toShHom N L =
      pullbackProjectionFormulaMap f M L ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.sheaf).map
            (((derivedAdjunction f.toLRSHom.toShHom).homEquiv M N).symm g)).app L) := by
  refine Eq.trans (congrArg (fun t => ((derivedTensorProductFunctor Y.sheaf).map t).app
      ((derivedPushforward f).obj L) ≫ relativeCupProduct f.toLRSHom.toShHom N L)
    (((derivedAdjunction f.toLRSHom.toShHom).homEquiv M N).apply_symm_apply g).symm) ?_
  exact pullbackProjectionFormulaMap_comp f M L _

/-! ### The trace map on groups of morphisms -/

variable
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-- **The adjunct of precomposition with the sheafy trace map.** For `M` in `D(𝒪_Y)` and
`g : M ⟶ Rf_*R𝓗om_{𝒪_X}(L, a(K))`, the tensor–internal-Hom bijection on `Y` sends `g` followed
by the trace map of [Stacks, Tag 0B6H] to `g ⊗ 1_{Rf_*L}`, then the relative cup product, then
`Rf_*` of the evaluation morphism `R𝓗om_{𝒪_X}(L, a K) ⊗^L_{𝒪_X} L ⟶ a(K)`, then the counit
`Rf_*a(K) ⟶ K`.

This is naturality of the bijection in its source and in its target together with the defining
adjunction property of the map of [Stacks, Tag 0B69]. -/
theorem homEquiv_comp_sheafyTrace (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) (M : DerivedCategory Y.Modules)
    (g : M ⟶ (derivedPushforward f).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj)) :
    DY.homEquiv M ((derivedPushforward f).obj L.obj) K.obj
        (g ≫ sheafyTrace f DX DY hpush adj L K) =
      ((derivedTensorProductFunctor Y.sheaf).map g).app ((derivedPushforward f).obj L.obj) ≫
        ((relativeCupProduct f.toLRSHom.toShHom
              (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                (a.obj K).obj) L.obj ≫
            (derivedPushforward f).map (DX.evaluation L.obj (a.obj K).obj)) ≫
          (ι _).map (adj.counit.app K)) := by
  have htrace : DY.homEquiv ((derivedPushforward f).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
            (a.obj K).obj))
        ((derivedPushforward f).obj L.obj) K.obj (sheafyTrace f DX DY hpush adj L K) =
      (relativeCupProduct f.toLRSHom.toShHom
            (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
              (a.obj K).obj) L.obj ≫
          (derivedPushforward f).map (DX.evaluation L.obj (a.obj K).obj)) ≫
        (ι _).map (adj.counit.app K) :=
    (DY.homEquiv_naturality_target
        (derivedSheafHomPushforward f DX DY L.obj (a.obj K).obj)
        ((ι _).map (adj.counit.app K))).trans
      (congrArg (fun t => t ≫ (ι _).map (adj.counit.app K))
        (derivedSheafHomPushforward_homEquiv f DX DY L.obj (a.obj K).obj))
  refine Eq.trans
    (DY.homEquiv_naturality_source g (sheafyTrace f DX DY hpush adj L K)) ?_
  exact congrArg (fun t => _ ≫ t) htrace

/-! ### [Stacks, Tag 0A9Q] -/

/-- **The chain of five bijections.** Let `L` be an object of `D_QCoh(𝒪_X)` and `K` an object of
`D_QCoh(𝒪_Y)`, suppose `Lf^*M ⊗^L_{𝒪_X} L` has quasi-coherent cohomology for every `M` in
`D_QCoh(𝒪_Y)`, and suppose the projection-formula map at `M` and `L` is an isomorphism for every
such `M`. Then precomposition with the sheafy trace map of [Stacks, Tag 0B6H] is a bijection

`Hom_Y(ι M, Rf_*R𝓗om_{𝒪_X}(L, a K)) ⟶ Hom_Y(ι M, R𝓗om_{𝒪_Y}(Rf_*L, K))`

for every `M` in `D_QCoh(𝒪_Y)`. -/
theorem bijective_comp_sheafyTrace (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y)
    (hten : ∀ (M : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullback f.toLRSHom.toShHom).obj M.obj)).obj L.obj)).IsQuasicoherent)
    (h08EU : ∀ M : quasiCoherentDerivedCategory Y,
      IsIso (pullbackProjectionFormulaMap f M.obj L.obj))
    (M : quasiCoherentDerivedCategory Y) :
    Function.Bijective fun g : (ι _).obj M ⟶ (derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          (a.obj K).obj) => g ≫ sheafyTrace f DX DY hpush adj L K := by
  have hiso := h08EU M
  set E : quasiCoherentDerivedCategory X :=
    ⟨((derivedTensorProductFunctor X.sheaf).obj
      ((derivedPullback f.toLRSHom.toShHom).obj M.obj)).obj L.obj, hten M⟩
  set ee := ((derivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          (a.obj K).obj)).symm.trans
      ((DX.homEquiv ((derivedPullback f.toLRSHom.toShHom).obj M.obj) L.obj
            (a.obj K).obj).trans
        ((quasiCoherentCounitEquiv f hpush adj E K).trans
          ((precompIsoEquiv (pullbackProjectionFormulaMap f M.obj L.obj) K.obj).trans
            (DY.homEquiv M.obj ((derivedPushforward f).obj L.obj) K.obj).symm)))
  have key : ∀ g : (ι _).obj M ⟶ (derivedPushforward f).obj
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj),
      g ≫ sheafyTrace f DX DY hpush adj L K =
        (DY.homEquiv M.obj ((derivedPushforward f).obj L.obj) K.obj).symm
          (pullbackProjectionFormulaMap f M.obj L.obj ≫
            quasiCoherentCounitEquiv f hpush adj E K
              (DX.homEquiv ((derivedPullback f.toLRSHom.toShHom).obj M.obj) L.obj
                (a.obj K).obj
                (((derivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
                  (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                    (a.obj K).obj)).symm g))) := by
    intro g
    refine (Equiv.eq_symm_apply _).2 ?_
    have hmap : (derivedPushforward f).map
            (((derivedTensorProductFunctor X.sheaf).map
              (((derivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
                (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                  (a.obj K).obj)).symm g)).app L.obj) ≫
          (derivedPushforward f).map (DX.evaluation L.obj (a.obj K).obj) =
        (derivedPushforward f).map
          (DX.homEquiv ((derivedPullback f.toLRSHom.toShHom).obj M.obj) L.obj (a.obj K).obj
            (((derivedAdjunction f.toLRSHom.toShHom).homEquiv M.obj
              (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                (a.obj K).obj)).symm g)) :=
      ((derivedPushforward f).map_comp _ _).symm.trans
        (congrArg (fun z => (derivedPushforward f).map z)
          (tensorHom_comp_evaluation DX L.obj (a.obj K).obj _))
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

end Stacks.Duality

end
