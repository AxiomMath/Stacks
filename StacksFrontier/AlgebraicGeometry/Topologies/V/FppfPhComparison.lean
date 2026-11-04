module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings

/-!
# Fppf coverings are ph coverings

Stacks 0DBT states that an fppf covering of schemes is a ph covering. The Stacks proof
reduces the statement to an affine base, where it follows from the fact that an fppf covering
of a quasi-compact and quasi-separated scheme is dominated, Zariski locally, by a *finite*
surjective morphism (Stacks 0CP0), together with the fact that a finite morphism is proper.

This file carries out that reduction, with the domination statement isolated as the
hypothesis `AlgebraicGeometry.FppfHasFiniteDomination`. Everything else — the base change of
the family to an affine open, the extraction of a finite subfamily, the passage from the
Zariski covering of the dominating scheme to an affine one, and the assembly of the
resulting standard ph covering and of the refinement morphism — is proved here.

## Main definitions

* `AlgebraicGeometry.FppfHasFiniteDomination` is the statement that a *finite*-index fppf
  covering of a quasi-compact and quasi-separated scheme is dominated, Zariski locally, by a
  finite surjective morphism.

## Main results

* `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage`: granted
  `AlgebraicGeometry.FppfHasFiniteDomination`, an fppf covering is a ph covering.

## Implementation notes

`AlgebraicGeometry.FppfHasFiniteDomination` is strictly weaker than Stacks 0CP0 in two
respects, both of which make it easier to discharge: the index type of the covering is
assumed finite (the reduction extracts a finite subcovering before appealing to it), and the
dominating morphism is not required to be of finite presentation (the reduction uses only
that it is finite and surjective). It is therefore an immediate consequence of 0CP0, and
together with 0CP0 `AlgebraicGeometry.isPHCovering_of_mem_fppfPrecoverage` gives Stacks 0DBT.

The predicate is universe-polymorphic in the index universe `v` as well as the scheme
universe `u`, because the finite subfamily extracted during the reduction is indexed by a
subtype of the original index type, which lives in `v`.

## References

* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0CP0](https://stacks.math.columbia.edu/tag/0CP0)
* [Stacks Project, Tag 0DBG](https://stacks.math.columbia.edu/tag/0DBG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The input to Stacks 0DBT supplied by Stacks 0CP0: an fppf covering of a quasi-compact and
quasi-separated scheme, indexed by a finite type, is dominated by a finite surjective
morphism `g : S' ⟶ S` which factors through members of the covering on a Zariski covering of
`S'`.

Stacks 0CP0 proves this without the finiteness assumption on the index type and with `g` in
addition of finite presentation, so this predicate follows from it. -/
def FppfHasFiniteDomination : Prop :=
  ∀ (I : Type v) (_ : Finite I) (S : Scheme.{u}) (_ : CompactSpace S)
    (_ : QuasiSeparatedSpace S) (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S),
      Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage S →
        ∃ (S' : Scheme.{u}) (g : S' ⟶ S), IsFinite g ∧ Surjective g ∧
          ∃ (J : Type u) (U : J → Scheme.{u}) (j : ∀ a, U a ⟶ S'),
            Presieve.ofArrows U j ∈ Scheme.zariskiPrecoverage S' ∧
              ∀ a, ∃ i, ∃ h : U a ⟶ X i, j a ≫ g = h ≫ f i

/-- **Stacks 0DBT**, granted `AlgebraicGeometry.FppfHasFiniteDomination`: an fppf covering of
schemes is a ph covering.

Over an affine open `U` of the target the family base changes to an fppf covering of `U`,
from which a finite subcovering is extracted (the members of an fppf covering are open maps,
so their ranges form an open cover of the quasi-compact space `U`). The hypothesis dominates
that finite subcovering by a finite surjection `g : S' ⟶ U`; since `g` is finite, `S'` is
affine, so the Zariski covering of `S'` provided by the hypothesis can be refined by a finite
affine open cover. The restrictions of `g` to the members of that cover form a standard ph
covering of `U`, because a finite morphism is proper, and they factor through the original
family by construction. -/
theorem isPHCovering_of_mem_fppfPrecoverage (H : FppfHasFiniteDomination.{u, v})
    {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T) :
    IsPHCovering X f := by
  classical
  have hdata := (Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hf
  rw [isPHCovering_iff]
  refine ⟨fun i ↦ have := (hdata.2 i).2; inferInstance, fun U hU ↦ ?_⟩
  have : IsAffine U.toScheme := hU
  have hmem : Presieve.ofArrows (fun i ↦ pullback (f i) U.ι)
      (fun i ↦ pullback.snd (f i) U.ι) ∈ Scheme.fppfPrecoverage U.toScheme :=
    Precoverage.mem_coverings_of_isPullback f hf U.ι (fun i ↦ pullback.snd (f i) U.ι)
      (fun i ↦ pullback.fst (f i) U.ι) fun i ↦ (IsPullback.of_hasPullback (f i) U.ι).flip
  have hdataE := (Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hmem
  have hopen : ∀ i, IsOpen (Set.range (pullback.snd (f i) U.ι)) := by
    intro i
    have := (hdataE.2 i).1
    have := (hdataE.2 i).2
    exact (pullback.snd (f i) U.ι).isOpenMap.isOpen_range
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set U.toScheme)).elim_finite_subcover
      (fun i ↦ Set.range (pullback.snd (f i) U.ι)) hopen fun x _ ↦
        Set.mem_iUnion.mpr (hdataE.1 x)
  have hmemfin : Presieve.ofArrows (fun i : {i : I // i ∈ s} ↦ pullback (f i.1) U.ι)
      (fun i : {i : I // i ∈ s} ↦ pullback.snd (f i.1) U.ι) ∈
      Scheme.fppfPrecoverage U.toScheme := by
    refine (Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr ⟨fun x ↦ ?_, fun i ↦ hdataE.2 i.1⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hx⟩
  obtain ⟨S', g, hgfin, hgsurj, J, V, j, hV, hfactor⟩ :=
    H {i : I // i ∈ s} inferInstance U.toScheme inferInstance inferInstance _ _ hmemfin
  have : IsFinite g := hgfin
  have : IsAffine S' := isAffine_of_isAffineHom g
  let Z : Scheme.OpenCover S' :=
    { toPreZeroHypercover := ⟨J, V, j⟩
      mem₀ := hV }
  let A := Z.affineRefinement.openCover
  let W := A.finiteSubcover
  let toZ : W ⟶ Z :=
    (⟨fun a ↦ A.idx a.val, fun _ ↦ 𝟙 _, fun _ ↦ rfl⟩ : W ⟶ A).comp Z.fromAffineRefinement
  refine ⟨⟨W.I₀, W.X, fun a ↦ W.f a ≫ g⟩, ?_, ?_⟩
  · exact StandardPHCovering.of_presentation _
      (hX := fun a ↦ by
        change IsAffine (Spec (Z.affineRefinement.X (A.idx a.val)))
        infer_instance)
      g W.f inferInstance hgsurj (fun _ ↦ inferInstance) W.iUnion_range fun _ ↦ rfl
  · refine ⟨⟨fun a ↦ ((hfactor (toZ.s₀ a)).choose).val,
      fun a ↦ toZ.h₀ a ≫ (hfactor (toZ.s₀ a)).choose_spec.choose, fun a ↦ ?_⟩⟩
    change (toZ.h₀ a ≫ (hfactor (toZ.s₀ a)).choose_spec.choose) ≫
      pullback.snd (f ((hfactor (toZ.s₀ a)).choose).val) U.ι = W.f a ≫ g
    rw [Category.assoc, ← (hfactor (toZ.s₀ a)).choose_spec.choose_spec, ← Category.assoc,
      toZ.w₀]

end AlgebraicGeometry

end
