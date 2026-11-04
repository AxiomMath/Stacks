module

public import Mathlib.RingTheory.SimpleModule.Isotypic
public import StacksFrontier.Deformation.Basic

/-!
# Objects of `𝒞_Λ` are small over the residue field

An Artinian local ring has finite length as a module over itself, and every simple module
over a local ring is isomorphic to its residue field. Hence an object `A` of `𝒞_Λ` admits
a finite filtration whose successive quotients are copies of `k`, so `A` is *small*
relative to any universe in which `k` is small.

This is the smallness statement needed to base change a module over an object of `𝒞_Λ`
without leaving a prescribed universe: a module of the form `B ⊗_A M` lives a priori in
the universe `max v m` of the ring and the module, and `Small` plus `Shrink` bring it back
to the universe of `M`.

## Main results

* `Deformation.small_of_small_submodule_quotient`, `Deformation.small_of_isSimpleModule`
  and `Deformation.small_of_isFiniteLength`: smallness along a finite-length filtration
  over a local ring.
* `Deformation.ArtinianLocalAlgCat.small`: an object of `𝒞_Λ` is small whenever `k` is.

## References

* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public section

namespace Deformation

universe t u v w

/-- A module with a small submodule and a small quotient is small. -/
theorem small_of_small_submodule_quotient {R : Type u} {M : Type v} [Ring R]
    [AddCommGroup M] [Module R M] (N : Submodule R M) [Small.{t} N]
    [Small.{t} (M ⧸ N)] : Small.{t} M := by
  classical
  let rep : (M ⧸ N) → M := fun q => Quotient.out q
  have hrep (q : M ⧸ N) : Submodule.Quotient.mk (rep q) = q := Submodule.Quotient.mk_out q
  let f : (M ⧸ N) × N → M := fun p => rep p.1 + p.2.1
  apply small_of_surjective (f := f)
  intro m
  have hm : m - rep (Submodule.Quotient.mk m) ∈ N := by
    have hh : rep (Submodule.Quotient.mk m) - m ∈ N :=
      (Submodule.Quotient.eq (p := N)).mp (hrep (Submodule.Quotient.mk m))
    simpa using N.neg_mem hh
  refine ⟨(Submodule.Quotient.mk m, ⟨m - rep (Submodule.Quotient.mk m), hm⟩), ?_⟩
  simp [f]

/-- A simple module over a local ring with small residue field is small. -/
theorem small_of_isSimpleModule {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Small.{t} (IsLocalRing.ResidueField R)]
    (h : IsSimpleModule R M) : Small.{t} M := by
  let : Small.{t} (R ⧸ IsLocalRing.maximalIdeal R) :=
    ‹Small.{t} (IsLocalRing.ResidueField R)›
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := M)).mp h
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact small_map e.toEquiv

/-- A module of finite length over a local ring with small residue field is small. -/
theorem small_of_isFiniteLength {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Small.{t} (IsLocalRing.ResidueField R)]
    (h : IsFiniteLength R M) : Small.{t} M := by
  refine IsFiniteLength.rec (R := R) (motive := fun M _ _ _ => Small.{t} M) ?_ ?_ h
  · intro M hAdd hMod hSub
    infer_instance
  · intro M hAdd hMod N hSimple hN ih
    let : Small.{t} N := ih
    let : Small.{t} (M ⧸ N) := small_of_isSimpleModule (R := R) (M := M ⧸ N) hSimple
    exact small_of_small_submodule_quotient N

namespace ArtinianLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An object of `𝒞_Λ` is small in any universe in which the residue field `k` is
small. -/
theorem small (A : ArtinianLocalAlgCat.{u, v, w} Λ k) [Small.{t} k] : Small.{t} A := by
  let : Small.{t} (IsLocalRing.ResidueField A) := small_map A.residueEquiv.toEquiv
  have hlen : IsFiniteLength A A := (isArtinianRing_iff_isFiniteLength A).mp inferInstance
  exact small_of_isFiniteLength hlen

end ArtinianLocalAlgCat

end Deformation

end
