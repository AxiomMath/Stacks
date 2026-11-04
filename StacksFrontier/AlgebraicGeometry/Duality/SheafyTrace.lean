module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# The sheafy trace map of the right adjoint of pushforward

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, and let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)` there
is a canonical map

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

Equation 48.3.0.1 of [Stacks, Tag 0B6H]. It is the composition

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

whose first arrow is the projection formula for derived internal Hom of [Stacks, Tag 0B69] and
whose second is `R𝓗om_{𝒪_Y}(Rf_*L, −)` applied to the counit `Rf_*a(K) ⟶ K`. Neither side of
the map need have quasi-coherent cohomology, so both derived internal Homs and the derived
direct image on the left are taken in the unrestricted derived categories.

## Main definitions

* `Stacks.Duality.derivedSheafHomPushforward` — the canonical map
  `Rf_*R𝓗om_{𝒪_X}(L, M) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*M)` of [Stacks, Tag 0B69] for a morphism of
  schemes: the adjunct of the relative cup product of [Stacks, Tag 0B68] followed by `Rf_*` of
  the evaluation morphism.
* `Stacks.Duality.sheafyTrace` — **Equation 48.3.0.1**, that composition.

## Main results

* `Stacks.Duality.derivedSheafHomPushforward_homEquiv` — the defining adjunction property of the
  first arrow, so a consumer never unfolds it.
* `Stacks.Duality.sheafyTrace_eq` — the trace map *is* that composition.

## Implementation notes

*The right adjoint is a hypothesis.* The source obtains `a` from [Stacks, Tag 0A9E], an
existence statement available here only with its geometric inputs assumed; see
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward`. The formula for the trace map
does not depend on how `a` arises — only on an adjunction `Rf_* ⊣ a`, whose counit is the
second arrow — so `a` and the adjunction are carried as hypotheses. For the same reason the
quasi-compactness and quasi-separatedness of the source are absent: they are what produce `a`,
and they enter only through the adjunction.
The map for a morphism of quasi-compact quasi-separated schemes, built from the right adjoint of
[Stacks, Tag 0A9E] itself, is `Stacks.Duality.qcqsSheafyTrace`.

*The tensor–internal-Hom adjunctions are data.* The relative cup product of [Stacks, Tag 0B68]
lands in `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the derived tensor
product of [Stacks, Tag 06YU] indexed by the sheaf of rings, whereas the tensor–internal-Hom
bijection of [Stacks, Tag 08DI] is stated at `Stacks.SheafOfModules.derivedTensor`, the one
indexed by the ringed site. The two agree up to canonical isomorphism, both being computed by
the total tensor complex on K-flat representatives, but that isomorphism is not part of this
development and the two are not definitionally equal. The bijection is therefore carried at the
first, which is the tensor product the relative cup product lands in and so the only one at
which the adjunct can be formed; the internal Hom bifunctors are the derived internal Homs
themselves, pinned by `Stacks.SheafOfModules.derivedSheafHom`.

## References

* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0B69](https://stacks.math.columbia.edu/tag/0B69)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction (derivedTensorProductFunctor X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf))
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf))

/-- **[Stacks, Tag 0B69] for a morphism of schemes.** For `L`, `M` in `D(𝒪_X)` the canonical map
`Rf_*R𝓗om_{𝒪_X}(L, M) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*M)`: the morphism which the
tensor–internal-Hom bijection on `D(𝒪_Y)` sends to the relative cup product of
[Stacks, Tag 0B68] followed by `Rf_*` of the evaluation morphism
`R𝓗om_{𝒪_X}(L, M) ⊗^L_{𝒪_X} L ⟶ M`. -/
def derivedSheafHomPushforward (L M : DerivedCategory X.Modules) :
    (derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj M) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op ((derivedPushforward f).obj L))).obj ((derivedPushforward f).obj M) :=
  (DY.homEquiv ((derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj M))
      ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)).symm
    (relativeCupProduct f.toLRSHom.toShHom
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj M) L ≫
      (derivedPushforward f).map (DX.evaluation L M))

/-- The adjunct of `Stacks.Duality.derivedSheafHomPushforward` under the tensor–internal-Hom
bijection on `D(𝒪_Y)` is the relative cup product followed by `Rf_*` of the evaluation
morphism. -/
theorem derivedSheafHomPushforward_homEquiv (L M : DerivedCategory X.Modules) :
    DY.homEquiv ((derivedPushforward f).obj
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj M))
        ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)
        (derivedSheafHomPushforward f DX DY L M) =
      relativeCupProduct f.toLRSHom.toShHom
          (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L)).obj M) L ≫
        (derivedPushforward f).map (DX.evaluation L M) := by
  dsimp only [derivedSheafHomPushforward]
  exact (DY.homEquiv _ _ _).apply_symm_apply _

variable (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-- **Equation 48.3.0.1 of [Stacks, Tag 0B6H].** For a morphism of schemes `f : X ⟶ Y`, a right
adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and objects `L` of `D_QCoh(𝒪_X)` and `K` of
`D_QCoh(𝒪_Y)`, the canonical map `Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`: the map of
[Stacks, Tag 0B69] at `L` and `a(K)`, followed by `R𝓗om_{𝒪_Y}(Rf_*L, −)` applied to the counit
`Rf_*a(K) ⟶ K` of `Rf_* ⊣ a`. -/
@[stacks 0B6H "variant: the map for a supplied right adjoint `a`, adjunction `Rf_* ⊣ a` and \
tensor–Hom data; the tag is Stacks.Duality.qcqsSheafyTrace"]
def sheafyTrace (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    (derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          (a.obj K).obj) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op ((derivedPushforward f).obj L.obj))).obj K.obj :=
  derivedSheafHomPushforward f DX DY L.obj (a.obj K).obj ≫
    ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
      (op ((derivedPushforward f).obj L.obj))).map ((ι _).map (adj.counit.app K))

/-- **The trace map is that composition.** Equation 48.3.0.1 is the map of [Stacks, Tag 0B69]
followed by the derived internal Hom out of `Rf_*L` of the counit `Rf_*a(K) ⟶ K`. -/
theorem sheafyTrace_eq (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    sheafyTrace f DX DY hpush adj L K =
      derivedSheafHomPushforward f DX DY L.obj (a.obj K).obj ≫
        ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op ((derivedPushforward f).obj L.obj))).map ((ι _).map (adj.counit.app K)) :=
  rfl

end Stacks.Duality

end
