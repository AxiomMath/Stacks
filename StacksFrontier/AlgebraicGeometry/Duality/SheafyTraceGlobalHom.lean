module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceCoherator

/-!
# The sheafy trace map on global derived Hom

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and let `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)`. The
sheafy trace map of [Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

induces an isomorphism `R Hom_X(L, a(K)) ⟶ R Hom_Y(Rf_*L, K)` of global derived Homs. This is
[Stacks, Tag 0B6I]; this file proves it from the two inputs of [Stacks, Tag 0A9Q] as hypotheses,
and `StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHomQcqs.lean` proves those inputs for
a quasi-compact quasi-separated `f` and states the tag there, as
`Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs`.

The source proves it exactly as follows. Global derived Hom is derived global sections of derived
internal Hom, so by Leray ([Stacks, Tag 0D5W])

`R Hom_X(L, a K) = RΓ(X, R𝓗om_{𝒪_X}(L, a K)) = RΓ(Y, Rf_*R𝓗om_{𝒪_X}(L, a K))`

and `R Hom_Y(Rf_*L, K) = RΓ(Y, R𝓗om_{𝒪_Y}(Rf_*L, K))`; and a morphism `φ` of `D(𝒪_Y)` which the
coherator `DQ_Y` sends to an isomorphism induces an isomorphism on `RΓ(Y, -)`, *because*

`H^n(Y, E) = Ext^n_Y(𝒪_Y, E) = Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, E) = Hom(𝒪_Y⟦-n⟧, DQ_Y(E))`,

the structure sheaf shifted being an object of `D_QCoh(𝒪_Y)`. Both statements below are at that
last reading: the cohomology of a global derived Hom *is* the morphism group it corepresents
([Stacks, Tag 0B6A], [Stacks, Tag 08DK]), and that is the form in which the conclusion of
[Stacks, Tag 0A9Q] is already available here, as
`Stacks.Duality.bijective_comp_sheafyTrace`.

## Main definitions

* `Stacks.Duality.derivedStructureSheafInDegree` — the structure sheaf `𝒪_Y` placed in degree
  `n`, that is `𝒪_Y⟦-n⟧`, as an object of `D_QCoh(𝒪_Y)`.

## Main results

* `Stacks.Duality.isQuasicoherent_of_isZero` — a zero sheaf of modules on a scheme is
  quasi-coherent.
* `Stacks.Duality.derivedCategoryB_singleFunctor_obj_inDegree` — a quasi-coherent module placed
  in any single degree lies in `D_QCoh(𝒪_Y)`, the degree no longer being required to be zero.
* `Stacks.Duality.bijective_comp_of_isIso_coherator_map` — the converse of
  `Stacks.Duality.isIso_coherator_map_of_bijective`: a morphism of `D(𝒪_Y)` which the coherator
  sends to an isomorphism induces a bijection on morphisms out of every object of
  `D_QCoh(𝒪_Y)`. This is the step of the source's proof which turns Tag 0A9Q into a statement
  about the cohomology of global derived Homs.
* `Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf` — the bijection of
  [Stacks, Tag 0B6I] for a morphism along which `Rf_*` preserves quasi-coherence, with the two
  inputs of Tag 0A9Q as hypotheses: in every degree `n` the sheafy trace map induces a bijection
  on the morphism groups out of `𝒪_Y⟦-n⟧`, that is on the degree-`n` cohomology of the two global
  derived Homs.
* `Stacks.Duality.bijective_derivedPullbackHom_comp_sheafyTrace` — the same bijection with its
  source transported to a morphism group on `X` by the adjunction `Lf^* ⊣ Rf_*`, which is the
  first step of the source's chain ([Stacks, Tag 079W]).

## Implementation notes

*The parameters and hypotheses.* The right adjoint `a` and the adjunction `Rf_* ⊣ a` are
parameters, exactly as they are for the trace map itself in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTrace.lean`; their existence, [Stacks, Tag 0A9E], is
`Stacks.Duality.AnyModel.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs` for a morphism
between quasi-compact quasi-separated schemes, at this model too. The projection formula of
[Stacks, Tag 08EU] and the quasi-coherence of `Lf^*M ⊗^L_{𝒪_X} L` of [Stacks, Tag 08DX] part (1)
are the hypotheses `h08EU` and `hten` of Tag 0A9Q, in the same spellings, here because `f` is
arbitrary; for a quasi-compact quasi-separated `f` the needed instances of both are proved in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceGlobalHomQcqs.lean`.

*What is not plugged in.* Two identifications the source performs silently are not formalized
here. First, the degree-`n` cohomology of a global derived Hom is read as the morphism group
`Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, -)` it corepresents rather than as the cohomology of an object of
`D(Γ(Y, 𝒪_Y))`; the identification is [Stacks, Tag 08DK], available as
`Stacks.SheafOfModules.derivedSheafHomGlobalSectionsEquiv`, but at the derived global sections
of a ringed site rather than at
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`, the functor the Leray
isomorphism of [Stacks, Tag 0D5W] is stated at, and the comparison of those two models is not
part of this development. Second, and for the same reason, the left-hand side is read on `Y`
after `Rf_*`, which is where the map of Tag 0B6H lives and is the source's own second expression
for `R Hom_X(L, a K)`; the Leray step identifying it with `RΓ(X, -)` is
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison_top`, which is unconditional, but
plugging it in needs the same model comparison.
`Stacks.Duality.bijective_derivedPullbackHom_comp_sheafyTrace` carries out the Hom-level half of
that step: it moves the source to a morphism group on `X`, out of `Lf^*(𝒪_Y⟦-n⟧)`. Identifying
`Lf^*(𝒪_Y⟦-n⟧)` with `𝒪_X⟦-n⟧` is not formalized either; the underived statement is
`Stacks.PullbackAlgebra.pullbackUnitIso`.

## References

* [Stacks Project, Tag 0B6I](https://stacks.math.columbia.edu/tag/0B6I)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0B6A](https://stacks.math.columbia.edu/tag/0B6A)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedAdjunction)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The shifted structure sheaf as an object of `D_QCoh` -/

/-- The kernel of a morphism out of a zero object is zero. -/
private theorem isZero_kernel_of_isZero {C : Type*} [Category C] [Abelian C] {A B : C}
    (f : A ⟶ B) (hA : IsZero A) : IsZero (kernel f) := by
  rw [IsZero.iff_id_eq_zero]
  exact (cancel_mono (kernel.ι f)).1 (hA.eq_of_tgt _ _)

/-- A zero sheaf of modules is generated by the empty family of sections. -/
private def generatingSectionsOfIsZero {Y : Scheme.{u}} (M : Y.Modules) (hM : IsZero M) :
    M.GeneratingSections where
  I := PEmpty.{u + 1}
  s i := PEmpty.elim i
  epi := ⟨fun g₁ g₂ _ => hM.eq_of_src g₁ g₂⟩

/-- The free sheaf of modules on the empty family is zero: a morphism out of it is the empty
family of sections, so its identity is zero. -/
private theorem isZero_free_pempty (Y : Scheme.{u}) :
    IsZero (SheafOfModules.free.{u} (R := Y.ringCatSheaf) PEmpty.{u + 1}) := by
  rw [IsZero.iff_id_eq_zero]
  refine (SheafOfModules.freeHomEquiv
    (M := SheafOfModules.free.{u} (R := Y.ringCatSheaf) PEmpty.{u + 1})).injective ?_
  funext i
  exact PEmpty.elim i

/-- A zero sheaf of modules has the empty presentation: no generators and no relations. -/
private def presentationOfIsZero {Y : Scheme.{u}} (M : Y.Modules) (hM : IsZero M) :
    M.Presentation where
  generators := generatingSectionsOfIsZero M hM
  relations := generatingSectionsOfIsZero _
    (isZero_kernel_of_isZero _ (isZero_free_pempty Y))

/-- **A zero sheaf of modules on a scheme is quasi-coherent**, being the cokernel of the identity
of the free sheaf on the empty family. -/
public theorem isQuasicoherent_of_isZero {Y : Scheme.{u}} (M : Y.Modules) (hM : IsZero M) :
    M.IsQuasicoherent :=
  (presentationOfIsZero M hM).isQuasicoherent

/-- **A quasi-coherent module placed in a single degree lies in `D_QCoh(𝒪_Y)`.** Its `n`-th
cohomology sheaf is the module itself and the others vanish, and a zero module is
quasi-coherent.

This is the statement which
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/DerivedStructureSheaf.lean` proves for
the degree zero, with the degree arbitrary. That file is not imported here: it reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose global
`CategoryTheory.HasDerivedCategory` instances are the locally small model, while the sheafy
trace map is stated at `CategoryTheory.HasDerivedCategory.standard`; the two cannot be mentioned
in one file. For the same reason the vanishing degrees are handled by
`Stacks.Duality.isQuasicoherent_of_isZero` below rather than by the weak Serre property of the
quasi-coherent modules. -/
public theorem derivedCategoryB_singleFunctor_obj_inDegree {Y : Scheme.{u}} (M : Y.Modules)
    (hM : M.IsQuasicoherent) (n : ℤ) :
    DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
      ((DerivedCategory.singleFunctor Y.Modules n).obj M) := by
  intro i
  rcases lt_trichotomy i n with h | rfl | h
  · exact isQuasicoherent_of_isZero _
      (DerivedCategory.isZero_of_isGE (C := Y.Modules)
        ((DerivedCategory.singleFunctor Y.Modules n).obj M) n i h)
  · exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules i).app M).symm hM
  · exact isQuasicoherent_of_isZero _
      (DerivedCategory.isZero_of_isLE (C := Y.Modules)
        ((DerivedCategory.singleFunctor Y.Modules n).obj M) n i h)

/-- **The structure sheaf in degree `n`, as an object of `D_QCoh(𝒪_Y)`.** This is `𝒪_Y⟦-n⟧`, the
object which corepresents the degree-`n` cohomology `H^n(Y, -) = Ext^n_Y(𝒪_Y, -)` of derived
global sections. -/
public def derivedStructureSheafInDegree (Y : Scheme.{u}) (n : ℤ) :
    quasiCoherentDerivedCategory Y :=
  ⟨(DerivedCategory.singleFunctor Y.Modules n).obj (SheafOfModules.unit Y.ringCatSheaf),
    derivedCategoryB_singleFunctor_obj_inDegree _
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y) n⟩

/-! ### The coherator criterion, in the direction Tag 0B6I uses -/

/-- Precomposition with an isomorphism is a bijection on morphisms into it. -/
private theorem bijective_comp_isIso {C : Type*} [Category C] {X Y Z : C} (f : Y ⟶ Z) [IsIso f] :
    Function.Bijective (fun g : X ⟶ Y => g ≫ f) :=
  ⟨fun g₁ g₂ h => by simpa using congrArg (fun w => w ≫ inv f) h,
    fun w => ⟨w ≫ inv f, by simp⟩⟩

section Coherator

variable {Y : Scheme.{u}}
  (DQ : DerivedCategory Y.Modules ⥤ quasiCoherentDerivedCategory Y)
  (adjQ : (DerivedCategoryB.derivedCategoryB
    (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⊣ DQ)

include adjQ in
/-- **A morphism the coherator inverts induces a bijection on morphisms out of the quasi-coherent
objects.** This is the converse of `Stacks.Duality.isIso_coherator_map_of_bijective`, and it is
the step by which [Stacks, Tag 0A9Q] becomes a statement about the cohomology of global derived
Homs: `H^n(Y, E) = Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, E)` and `𝒪_Y⟦-n⟧` lies in `D_QCoh(𝒪_Y)`, so a morphism
with invertible image under `DQ` induces isomorphisms on all the groups `H^n(Y, -)`. -/
public theorem bijective_comp_of_isIso_coherator_map {A B : DerivedCategory Y.Modules}
    (φ : A ⟶ B) (hφ : IsIso (DQ.map φ)) (M : quasiCoherentDerivedCategory Y) :
    Function.Bijective (fun g : (ι _).obj M ⟶ A => g ≫ φ) := by
  have := hφ
  have key : (fun g : (ι _).obj M ⟶ A => g ≫ φ) =
      (adjQ.homEquiv M B).symm ∘ (fun g : M ⟶ DQ.obj A => g ≫ DQ.map φ) ∘
        (adjQ.homEquiv M A) := by
    funext g
    simp only [Function.comp_apply, ← adjQ.homEquiv_naturality_right, Equiv.symm_apply_apply]
  rw [key]
  exact (adjQ.homEquiv M B).symm.bijective.comp
    ((bijective_comp_isIso (X := (M : quasiCoherentDerivedCategory Y)) (DQ.map φ)).comp
      (adjQ.homEquiv M A).bijective)

end Coherator

/-! ### [Stacks, Tag 0B6I] -/

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

/-- **The bijection of [Stacks, Tag 0B6I], from the inputs of Tag 0A9Q.** Let `f : X ⟶ Y` be a
morphism of schemes along which derived direct image preserves quasi-coherence of cohomology,
let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and let `L` be an object of
`D_QCoh(𝒪_X)` and `K` one of `D_QCoh(𝒪_Y)`. Then in every degree `n` the sheafy trace map of
[Stacks, Tag 0B6H] induces a bijection

`Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, Rf_*R𝓗om_{𝒪_X}(L, a K)) ⟶ Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, R𝓗om_{𝒪_Y}(Rf_*L, K))`,

that is, an isomorphism of global derived Homs `R Hom_X(L, a K) ⟶ R Hom_Y(Rf_*L, K)` read degree
by degree through `H^n(Y, E) = Ext^n_Y(𝒪_Y, E) = Hom(𝒪_Y⟦-n⟧, E)`.

The projection formula of [Stacks, Tag 08EU] is the hypothesis `h08EU` and the quasi-coherence of
`Lf^*M ⊗^L_{𝒪_X} L` of [Stacks, Tag 08DX] part (1) is the hypothesis `hten`, exactly as for
[Stacks, Tag 0A9Q]; the right adjoint `a` with its adjunction `adj` is a parameter, exactly as for
the trace map itself. For a quasi-compact quasi-separated `f` both hypotheses are discharged in
`Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf_of_qcqs`. No coherator is needed in
this form: the chain of five bijections of Tag 0A9Q is already a statement about morphisms out of
the quasi-coherent objects, and `𝒪_Y⟦-n⟧` is one of them. -/
public theorem bijective_comp_sheafyTrace_structureSheaf
    (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
    (hten : ∀ (M : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullback f.toLRSHom.toShHom).obj M.obj)).obj L.obj)).IsQuasicoherent)
    (h08EU : ∀ M : quasiCoherentDerivedCategory Y,
      IsIso (pullbackProjectionFormulaMap f M.obj L.obj))
    (n : ℤ) :
    Function.Bijective (fun g : (ι _).obj (derivedStructureSheafInDegree Y n) ⟶
        (derivedPushforward f).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
            (a.obj K).obj) =>
      g ≫ sheafyTrace f DX DY hpush adj L K) :=
  bijective_comp_sheafyTrace f hpush adj DX DY L K hten h08EU
    (derivedStructureSheafInDegree Y n)

/-- **The bijection of [Stacks, Tag 0B6I] with its source on `X`.** Composing the bijection of
`Stacks.Duality.bijective_comp_sheafyTrace_structureSheaf` with the adjunction `Lf^* ⊣ Rf_*`
moves the left-hand side to a morphism group on `X`: for every `n` the map

`Hom_{D(𝒪_X)}(Lf^*(𝒪_Y⟦-n⟧), R𝓗om_{𝒪_X}(L, a K)) ⟶
  Hom_{D(𝒪_Y)}(𝒪_Y⟦-n⟧, R𝓗om_{𝒪_Y}(Rf_*L, K))`

sending `u` to its adjunct followed by the trace map is a bijection. This is the first step of
the source's chain, [Stacks, Tag 079W]. What remains to recognise the left-hand side as
`Ext^n_X(L, a K)` is the identification of `Lf^*(𝒪_Y⟦-n⟧)` with `𝒪_X⟦-n⟧`. -/
public theorem bijective_derivedPullbackHom_comp_sheafyTrace
    (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
    (hten : ∀ (M : quasiCoherentDerivedCategory Y) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        (((derivedTensorProductFunctor X.sheaf).obj
          ((derivedPullback f.toLRSHom.toShHom).obj M.obj)).obj L.obj)).IsQuasicoherent)
    (h08EU : ∀ M : quasiCoherentDerivedCategory Y,
      IsIso (pullbackProjectionFormulaMap f M.obj L.obj))
    (n : ℤ) :
    Function.Bijective (fun u : (derivedPullback f.toLRSHom.toShHom).obj
          (derivedStructureSheafInDegree Y n).obj ⟶
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj (a.obj K).obj) =>
      (derivedAdjunction f.toLRSHom.toShHom).homEquiv
          (derivedStructureSheafInDegree Y n).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
            (a.obj K).obj) u ≫
        sheafyTrace f DX DY hpush adj L K) :=
  (bijective_comp_sheafyTrace_structureSheaf f hpush adj DX DY L K hten h08EU n).comp
    ((derivedAdjunction f.toLRSHom.toShHom).homEquiv _ _).bijective

end Stacks.Duality

end
