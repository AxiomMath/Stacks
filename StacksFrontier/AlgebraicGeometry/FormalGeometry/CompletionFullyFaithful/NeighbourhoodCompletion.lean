module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerUnitHoms
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.InternalHomLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerStability
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SectionsLeftExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SheafHomTowerBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PullbackSheafHomIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SheafHomLocallyFree

/-!
# The completion functor on the neighbourhoods of a closed subscheme

**[Stacks, Tag 0EK2].** Let `X` be a Noetherian scheme and let `Y ⊂ X` be a closed subscheme with
ideal sheaf `ℐ ⊂ 𝒪_X`. Let `Y_n ⊂ X` be the `n`-th infinitesimal neighbourhood of `Y` in `X`, and
let `𝒱` be the set of open subschemes `V ⊂ X` containing `Y`, ordered by reverse inclusion.
Consider the conditions

1. `X` is quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) ⟶ lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `ℒ` and
   `colim_𝒱 Γ(V, ℒ^{⊗ m}) ⟶ lim Γ(Y_n, ℒ^{⊗ m}|_{Y_n})` is an isomorphism for all `m ≫ 0`;
3. for every `V ∈ 𝒱` and every finite locally free `𝒪_V`-module `ℰ` the map
   `colim_{V' ≥ V} Γ(V', ℰ|_{V'}) ⟶ lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism;
4. the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, ℐ)`, `ℱ ↦ ℱ^∧`, is fully faithful on the
   full subcategory of finite locally free objects.

Then (1) ⇒ (2) ⇒ (3) ⇒ (4) and (4) ⇒ (3).

## Main definitions

* `Stacks.Algebraization.NeighbourhoodCompletion.IsQuasiAffineComplete`,
  `Stacks.Algebraization.NeighbourhoodCompletion.HasAmpleComplete`,
  `Stacks.Algebraization.NeighbourhoodCompletion.FiniteLocallyFreeComplete` and
  `Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete` — the four
  conditions.

## Main results

* `Stacks.Algebraization.NeighbourhoodCompletion.implications_among_conditions` — **the tag**:
  the four implications.
* `Stacks.Algebraization.NeighbourhoodCompletion.hasAmpleComplete_of_isQuasiAffineComplete` —
  (1) ⇒ (2): on a quasi-affine scheme the structure sheaf is an ample invertible module and all
  of its tensor powers are the structure sheaf again.
* `Stacks.Algebraization.NeighbourhoodCompletion.finiteLocallyFreeComplete_of_hasAmpleComplete` —
  (2) ⇒ (3): the universally exact sequence `0 → ℰ → (ℒ^{⊗ p})^{⊕ r}|_V → (ℒ^{⊗ q})^{⊕ s}|_V`
  obtained by dualising a presentation of `ℰ^∨` by negative twists.
* `Stacks.Algebraization.NeighbourhoodCompletion`
  `.completionFullyFaithfulComplete_of_finiteLocallyFreeComplete` — (3) ⇒ (4): condition (3) at
  the internal hom `ℋom(𝒢, ℱ)`, which is finite locally free.
* `Stacks.Algebraization.NeighbourhoodCompletion`
  `.finiteLocallyFreeComplete_of_completionFullyFaithfulComplete` — (4) ⇒ (3), the implication
  whose proof the source omits: condition (4) at the pair `(𝒪_V, ℰ)`.
* `Stacks.Algebraization.NeighbourhoodCompletion.sheafHom_sections_eq` — the sections of the
  internal hom over an open are, on the nose, the morphisms of the restrictions to that open.

## How the conditions are written

The closed subscheme is given as a closed immersion `i : Y ⟶ X`; its ideal sheaf and its
infinitesimal neighbourhoods are the ones of
`Stacks.Algebraization.nthInfinitesimalNeighbourhood`.

The isomorphism asked for in (1), (2) and (3) is spelled out by the universal properties of the
filtered colimit and of the inverse limit, as `Stacks.Algebraization.InfinitesimalTower`
`.IsSectionsComplete`: every compatible family of sections on the `Y_n` comes from a section over
some neighbourhood, and two sections over neighbourhoods inducing the same family agree over a
smaller one. The family `𝒱` is directed, so this is exactly the assertion that the canonical map
out of the colimit is bijective. In (3) the module lives on a neighbourhood `V`, and the colimit
runs over the opens of `V` containing `Y`; the `Y_n` are read over `V` through the unique
factorization of `Y_n ⟶ X` through `V ⟶ X`, which exhibits them as the infinitesimal
neighbourhoods of `Y` in `V`.

Condition (4) is `Stacks.Algebraization.InfinitesimalTower.IsHomsComplete`, written with no
internal hom at all. A morphism of the source category `colim_𝒱 Coh(𝒪_V)` from `𝒢` to `ℱ`, both
finite locally free on `V`, is an element of `colim_{W} Hom_{𝒪_W}(𝒢|_W, ℱ|_W)`, and a morphism
`𝒢^∧ ⟶ ℱ^∧` of `Coh(X, ℐ)` is a compatible family of morphisms `𝒢|_{Y_n} ⟶ ℱ|_{Y_n}`, since the
objects of `Coh(X, ℐ)` are inverse systems and `𝒢^∧` is the system `(𝒢|_{Y_n})`. Full faithfulness
on finite locally free objects is therefore the bijectivity of
`colim_W Hom(𝒢|_W, ℱ|_W) ⟶ lim_n Hom(𝒢|_{Y_n}, ℱ|_{Y_n})`, and that is what is written. Two
objects of the colimit category defined on different neighbourhoods may be compared on their
intersection, so quantifying over a common `V` is no loss.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Ample Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Algebraization.NeighbourhoodCompletion

variable {Y X : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- **Condition (1) of [Stacks, Tag 0EK2].** `X` is quasi-affine, and the colimit of the sections
of `𝒪` over the open neighbourhoods of `Y` is the inverse limit of the sections of `𝒪` on the
infinitesimal neighbourhoods of `Y`. -/
public def IsQuasiAffineComplete : Prop :=
  Scheme.IsQuasiAffine X ∧
    (infTower i).IsSectionsComplete (SheafOfModules.unit X.ringCatSheaf)

/-- **Condition (2) of [Stacks, Tag 0EK2].** `X` carries an ample invertible module `L` for which
the comparison holds for `L ^⊗ m` for all large `m`. -/
public def HasAmpleComplete : Prop :=
  ∃ (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L),
    letI := hL
    AlgebraicGeometry.Scheme.Modules.IsAmple X L ∧
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (infTower i).IsSectionsComplete
          (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (m : ℤ))

/-- **Condition (3) of [Stacks, Tag 0EK2].** For every open neighbourhood `V` of `Y` and every
finite locally free `𝒪_V`-module `ℰ`, the colimit of the sections of `ℰ` over the open
neighbourhoods of `Y` inside `V` is the inverse limit of the sections of `ℰ` on the infinitesimal
neighbourhoods of `Y`. -/
public def FiniteLocallyFreeComplete : Prop :=
  ∀ (V : X.Opens) (hV : Set.range i.base ⊆ V) (E : V.toScheme.Modules),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E →
      IsNeighbourhoodSectionsCompleteOn i V hV E

/-- **Condition (4) of [Stacks, Tag 0EK2].** The completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, ℐ)` is fully faithful on the full subcategory of finite locally free
objects: for every open neighbourhood `V` of `Y` and all finite locally free `𝒪_V`-modules `𝒢`,
`ℱ`, the colimit over the open neighbourhoods `W` of `Y` inside `V` of the morphisms
`𝒢|_W ⟶ ℱ|_W` is the inverse limit of the morphisms `𝒢|_{Y_n} ⟶ ℱ|_{Y_n}`. -/
public def CompletionFullyFaithfulComplete : Prop :=
  ∀ (V : X.Opens) (hV : Set.range i.base ⊆ V) (G F : V.toScheme.Modules),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G →
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F →
      (nbhdTower i V hV).IsHomsComplete G F

/-- **[Stacks, Tag 0EK2], (2) implies (3).** Let `ℰ` be finite locally free on an open
neighbourhood `V` of `Y`. The restriction `ℒ|_V` is again ample, so `ℰ` sits in a universally
exact sequence `0 → ℰ → (ℒ^{⊗ p})^{⊕ r}|_V → (ℒ^{⊗ q})^{⊕ s}|_V` with `p` and `q` as large as we
please — `Stacks.Algebraization.exists_dual_embedding`, the dual of a presentation of `ℰ^∨` by
negative twists. Condition (2) gives the comparison for the powers of `ℒ` on `X`; it restricts to
`V`, passes to the finite biproducts, and the universally exact sequence carries it to `ℰ`. -/
public theorem finiteLocallyFreeComplete_of_hasAmpleComplete [IsNoetherian X]
    (h : HasAmpleComplete i) : FiniteLocallyFreeComplete i := by
  obtain ⟨L, hL, hample, N, hN⟩ := h
  have := hL
  intro V hV E hE
  have : IsNoetherian V.toScheme := Stacks.AmpleRestrict.isNoetherian_opens_toScheme V
  have : IsLocallyNoetherian V.toScheme := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  have : Stacks.Ample.IsInvertibleModule V.toScheme ((Scheme.Modules.pullback V.ι).obj L) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  have hampleA : Stacks.Ample.IsAmple V.toScheme ((Scheme.Modules.pullback V.ι).obj L) :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple V.toScheme _).mp
      (Stacks.AmpleRestrict.isAmple_pullback_ι_of_isNoetherian V L hample)
  obtain ⟨p, q, ιp, ιq, hιp, hιq, hpN, hqN, bp, hbp, bq, hbq, q₀, hq₀, β, w, hrefl, hmono, hex,
    huniv⟩ := exists_dual_embedding ((Scheme.Modules.pullback V.ι).obj L) hampleA (N : ℤ) E hE
  have hSCb : ∀ (m : ℤ) {ι : Type u} [Finite ι]
      (b : Bicone fun _ : ι => tensorPowModule V.toScheme
        ((Scheme.Modules.pullback V.ι).obj L) (-m)),
      b.IsBilimit → N ≤ m → (nbhdTower i V hV).IsSectionsComplete (dualSheaf b.pt) := by
    intro m _ _ b hb hm
    lift m to ℕ using by omega
    refine InfinitesimalTower.IsSectionsComplete.bicone _ _ (dualBicone b)
      (dualBicone_isBilimit b hb) fun _ => InfinitesimalTower.IsSectionsComplete.of_iso _
        (dualTensorPowIso V.toScheme ((Scheme.Modules.pullback V.ι).obj L) m) ?_
    exact InfinitesimalTower.IsSectionsComplete.of_iso _
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso V.toScheme
        ((Scheme.Modules.pullback V.ι).obj L) (m : ℤ))
      (InfinitesimalTower.IsSectionsComplete.of_iso _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso V.ι L m)
        (Stacks.Algebraization.isSectionsComplete_restrict i V hV _ (hN m (by omega))))
  refine InfinitesimalTower.IsSectionsComplete.of_isLimit_kernelFork _ _ β w hex.fIsKernel
    (hSCb p bp hbp hpN) (hSCb q bq hbq hqN) fun n => ?_
  have := huniv _ ((nbhdTower i V hV).obj n).hom
  exact Stacks.AlgebraicGeometry.Modules.injective_app_of_mono _ ⊤

/-- **[Stacks, Tag 0EK2], (4) implies (3)**, the implication whose proof the source omits. Apply
condition (4) to the pair `(𝒪_V, ℰ)`: a morphism `𝒪_W ⟶ ℰ|_W` on an open neighbourhood `W` of `Y`
inside `V` is a section of `ℰ` over `W`, and a morphism `𝒪_{Y_n} ⟶ ℰ|_{Y_n}` is a section of `ℰ`
on `Y_n`, compatibly with shrinking `W` and with the transition maps; so the comparison of
condition (4) at that pair *is* the comparison of condition (3) at `ℰ`. The structure sheaf is
finite locally free, so condition (4) applies to the pair. -/
public theorem finiteLocallyFreeComplete_of_completionFullyFaithfulComplete
    (h : CompletionFullyFaithfulComplete i) : FiniteLocallyFreeComplete i := fun V hV E hE =>
  InfinitesimalTower.IsSectionsComplete.of_isHomsComplete_unit _ E
    (h V hV (SheafOfModules.unit V.toScheme.ringCatSheaf) E
      (AlgebraicGeometry.isFiniteLocallyFree_unit V.toScheme) hE)

/-- The sections of the internal hom over an open are, on the nose, the morphisms of the
restrictions to that open. -/
public theorem sheafHom_sections_eq {Z : Scheme.{u}} (G F : Z.Modules) (W : Z.Opens) :
    ToType Γ((Stacks.Algebraization.sheafHomFunctor Z G).obj F, W) =
      ((_root_.restrFun Z.sheaf.obj W).obj G.val ⟶
        (_root_.restrFun Z.sheaf.obj W).obj F.val) := rfl

/-- **[Stacks, Tag 0EK2], (1) implies (2).** On a quasi-affine scheme the structure sheaf is
itself an ample invertible module, and every tensor power of it is again the structure sheaf. -/
public theorem hasAmpleComplete_of_isQuasiAffineComplete [IsNoetherian X]
    (h : IsQuasiAffineComplete i) : HasAmpleComplete i := by
  obtain ⟨hX, hsec⟩ := h
  obtain ⟨L, hL, hample, N, hN⟩ :=
    quasiAffine_neighbourhoodSectionsComplete_implies_amplePower i hX
      ((infTower_isSectionsComplete_iff i _).1 hsec)
  exact ⟨L, hL, hample, N, fun m hm => (infTower_isSectionsComplete_iff i _).2 (hN m hm)⟩

/-- probe: the pullback of a tensor power is the tensor power of the pullback, with the
invertibility instance for the restriction found automatically. -/
public def probeTensorPower {Z : Scheme.{u}} (V : Z.Opens) (L : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property L] (p : ℕ) :
    (Scheme.Modules.pullback V.ι).obj
        (Stacks.SheafOfModules.Invertible.tensorPower Z.toRingedSpace.presheaf
          (structureSheafRing Z.toRingedSpace).property L (p : ℤ)) ≅
      Stacks.SheafOfModules.Invertible.tensorPower V.toScheme.toRingedSpace.presheaf
        (structureSheafRing V.toScheme.toRingedSpace).property
        ((Scheme.Modules.pullback V.ι).obj L) (p : ℤ) :=
  AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso V.ι L p

/-- **[Stacks, Tag 0EK2], (3) implies (4).** For `𝒢`, `ℱ` finite locally free on an open
neighbourhood `V` of `Y`, the internal hom `ℋ = ℋom_{𝒪_V}(𝒢, ℱ)` is again finite locally free, so
condition (3) applies to it; the sections of `ℋ` over an open `W` are the morphisms
`𝒢|_W ⟶ ℱ|_W`, and the sections of `ℋ` on `Y_n` are the morphisms `𝒢|_{Y_n} ⟶ ℱ|_{Y_n}` because
the comparison `f^* ℋom(𝒢, ℱ) ⟶ ℋom(f^* 𝒢, f^* ℱ)` of Tag 0GMX is an isomorphism for `𝒢` finite
locally free. The comparison of condition (3) at `ℋ` is therefore the comparison of condition (4)
at `(𝒢, ℱ)`. -/
public theorem completionFullyFaithfulComplete_of_finiteLocallyFreeComplete [IsNoetherian X]
    (h : FiniteLocallyFreeComplete i) : CompletionFullyFaithfulComplete i :=
  fun V hV G F hG hF =>
    InfinitesimalTower.IsHomsComplete.of_isSectionsComplete_sheafHom_of_isIso _ G F
      (fun f => isIso_pullbackSheafHomMap f G F hG)
      (h V hV _ (Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_sheafHomFunctor
        G F hG hF))

/-- **[Stacks, Tag 0EK2].** Let `X` be a Noetherian scheme and let `Y ⊂ X` be a closed subscheme
with ideal sheaf `ℐ ⊂ 𝒪_X`. Let `Y_n ⊂ X` be the `n`-th infinitesimal neighbourhood of `Y` in `X`,
and let `𝒱` be the set of open subschemes `V ⊂ X` containing `Y`, ordered by reverse inclusion.
Consider the conditions

1. `X` is quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) ⟶ lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `ℒ` and
   `colim_𝒱 Γ(V, ℒ^{⊗ m}) ⟶ lim Γ(Y_n, ℒ^{⊗ m}|_{Y_n})` is an isomorphism for all `m ≫ 0`;
3. for every `V ∈ 𝒱` and every finite locally free `𝒪_V`-module `ℰ` the map
   `colim_{V' ≥ V} Γ(V', ℰ|_{V'}) ⟶ lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism;
4. the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, ℐ)`, `ℱ ↦ ℱ^∧`, is fully faithful on the
   full subcategory of finite locally free objects.

Then `(1) ⇒ (2) ⇒ (3) ⇒ (4)` and `(4) ⇒ (3)`.

The source proves `(1) ⇒ (2)` from the ampleness of `𝒪_X` on a quasi-affine scheme, `(2) ⇒ (3)`
from a universally exact sequence `0 → ℰ → (ℒ^{⊗ p})^{⊕ r}|_V → (ℒ^{⊗ q})^{⊕ s}|_V`, and
`(3) ⇒ (4)` by applying `(3)` to the internal hom; it omits the proof of `(4) ⇒ (3)`, which is
`(4)` applied to the pair `(𝒪_V, ℰ)`, read through the identification of a section of `ℰ` with a
morphism `𝒪 ⟶ ℰ`. -/
@[stacks 0EK2]
public theorem implications_among_conditions [IsNoetherian X] :
    (IsQuasiAffineComplete i → HasAmpleComplete i) ∧
      (HasAmpleComplete i → FiniteLocallyFreeComplete i) ∧
      (FiniteLocallyFreeComplete i → CompletionFullyFaithfulComplete i) ∧
      (CompletionFullyFaithfulComplete i → FiniteLocallyFreeComplete i) :=
  ⟨hasAmpleComplete_of_isQuasiAffineComplete i,
    finiteLocallyFreeComplete_of_hasAmpleComplete i,
    completionFullyFaithfulComplete_of_finiteLocallyFreeComplete i,
    finiteLocallyFreeComplete_of_completionFullyFaithfulComplete i⟩

end Stacks.Algebraization.NeighbourhoodCompletion

end
