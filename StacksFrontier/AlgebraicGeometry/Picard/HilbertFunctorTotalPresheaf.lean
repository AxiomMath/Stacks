module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorZariskiSheaf

/-!
# The Hilbert functor through its total presheaf on all schemes

Mathlib's form of the representability criterion of Stacks Tag 01JJ,
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`, is stated for a Zariski sheaf of
types on the category of all schemes, covered by relatively representable open immersions from
representable presheaves. The degree-`d` Hilbert functor lives on the schemes over `S`, and it is
carried to the category of all schemes by `Stacks.Sites.totalPresheaf`. This file supplies the
two passages that applying the criterion to it needs: a test for a morphism from a representable
presheaf to be an open immersion of presheaves, and the passage from a scheme representing the
total presheaf back to a scheme over `S` representing the Hilbert functor.

## Main results

* `Stacks.Morphisms.openImmersion_presheaf_of_opens` — a morphism to a presheaf from a
  representable one is an open immersion of presheaves as soon as it is injective at every test
  scheme and its image over a test scheme is cut out by an open of that scheme.
* `Stacks.Hilbert.totalSigmaMk_eq` — two elements of the total presheaf obtained by restricting
  one section along two morphisms of the slice with the same underlying morphism of schemes
  agree.
* `Stacks.Hilbert.representsHilbertFunctorOfRank_of_representableBy` — a scheme representing the
  total presheaf of the degree-`d` Hilbert functor yields a scheme over `S` representing the
  Hilbert functor itself, with the naturality of its universal family.

## Implementation notes

*Elements of the total presheaf.* The total presheaf is a dependent pair type, and its second
component is written as a value of `Stacks.Hilbert.hilbertFunctorOfRank` applied to an object
rather than as a `Stacks.Hilbert.HilbertFamily`, even though the two are the same by definition:
the pair is type-correct without unfolding the functor only in the first spelling, and the tactics
that rewrite inside such a pair work at a transparency at which the functor does not unfold.

*The passage back to the slice.* Representability of the total presheaf gives a scheme `W` and a
universal element over it whose first component makes `W` a scheme over `S`; restricting the
universal element along it produces the universal family, and the naturality field of
`Stacks.Hilbert.RepresentsHilbertFunctorOfRank` is base change of ideal sheaves.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites

universe u

namespace Stacks.Morphisms

/-! ### A criterion for an open immersion of presheaves -/

/-- **A morphism to a presheaf from a representable one is an open immersion of presheaves when
it is injective at every test scheme and its image is cut out by opens.** Here `O T x` is the
open of a test scheme `T` cutting out the locus over which the element `x` of `F` lies in the
image: a morphism `e : T' ⟶ T` factors through `W` over `x` exactly when `e` lands in `O T x`.

Pulling `η` back along the element `x` of `F` over `T` is then represented by the open subscheme
`O T x` of `T`: the hypothesis applied to the inclusion of that open produces the classifying
morphism `O T x ⟶ W`, and applied to an arbitrary `e` it produces the factorisation of `e`
through the open, which injectivity identifies with the required lift. -/
theorem openImmersion_presheaf_of_opens {F : Scheme.{u}ᵒᵖ ⥤ Type u} {W : Scheme.{u}}
    (η : yoneda.obj W ⟶ F) (hinj : ∀ T, Function.Injective (η.app T))
    (O : ∀ T : Scheme.{u}, F.obj (op T) → T.Opens)
    (hO : ∀ (T : Scheme.{u}) (x : F.obj (op T)) (T' : Scheme.{u}) (e : T' ⟶ T),
      (∃ k : T' ⟶ W, η.app _ k = F.map e.op x) ↔ ∀ t, e t ∈ O T x) :
    IsOpenImmersion.presheaf η := by
  refine MorphismProperty.relative.of_exists fun T ζ ↦ ?_
  obtain ⟨Q, hQ⟩ : ∃ Q : T.Opens, ∀ (T' : Scheme.{u}) (e : T' ⟶ T),
      (∃ k : T' ⟶ W, η.app _ k = F.map e.op (yonedaEquiv ζ)) ↔ ∀ t, e t ∈ Q :=
    ⟨_, hO T (yonedaEquiv ζ)⟩
  obtain ⟨k, hk⟩ := (hQ Q.toScheme Q.ι).2 (fun t ↦ t.property)
  have comm : yoneda.map k ≫ η = yoneda.map Q.ι ≫ ζ := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact hk.trans (map_yonedaEquiv _ _)
  refine ⟨Q.toScheme, yoneda.map k, Q.ι, ?_, inferInstance⟩
  refine IsPullback.iff_app.mpr fun T' ↦ (Types.isPullback_iff _ _ _ _).2
    ⟨congrArg (fun n ↦ n.app T') comm, fun a b hab ↦ (cancel_mono Q.ι).1 hab.2, fun a e he ↦ ?_⟩
  change T'.unop ⟶ W at a
  change T'.unop ⟶ T at e
  have heQ : ∀ t, e t ∈ Q := (hQ T'.unop e).1 ⟨a, he.trans (map_yonedaEquiv _ _).symm⟩
  let l : T'.unop ⟶ Q.toScheme := IsOpenImmersion.lift Q.ι e <| by
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨e t, heQ t⟩, rfl⟩
  have hl : l ≫ Q.ι = e := IsOpenImmersion.lift_fac _ _ _
  refine ⟨l, ?_, hl⟩
  apply hinj T'
  have hc := congrArg (fun n : yoneda.obj Q.toScheme ⟶ F ↦ n.app T' l) comm
  change η.app T' (l ≫ k) = ζ.app T' (l ≫ Q.ι) at hc
  exact hc.trans ((congrArg (ζ.app T') hl).trans he.symm)

end Stacks.Morphisms

namespace Stacks.Hilbert

/-! ### Elementary calculus in the total presheaf -/

section TotalSigma

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u} {V : Scheme.{u}}

/-- The first components of two equal elements of the total presheaf agree. -/
theorem totalSigma_fst_eq {ψ ψ' : V ⟶ S} {s : F.obj (op (Over.mk ψ))}
    {t : F.obj (op (Over.mk ψ'))}
    (h : (⟨ψ, s⟩ : Σ χ : V ⟶ S, F.obj (op (Over.mk χ))) = ⟨ψ', t⟩) : ψ = ψ' :=
  congrArg Sigma.fst h

/-- Two elements of the total presheaf with the same first component agree as soon as their
second components do. -/
theorem totalSigma_snd_eq {ψ : V ⟶ S} {s t : F.obj (op (Over.mk ψ))}
    (h : (⟨ψ, s⟩ : Σ χ : V ⟶ S, F.obj (op (Over.mk χ))) = ⟨ψ, t⟩) : s = t := by
  simpa using h

/-- Two elements of the total presheaf built by restricting one section along two morphisms of
the slice with the same underlying morphism of schemes agree. This is the one place the equation
`CategoryTheory.Over.w` has to be transported along. -/
theorem totalSigmaMk_eq {W : Over S} (s : F.obj (op W)) {ψ ψ' : V ⟶ S}
    (e : Over.mk ψ ⟶ W) (e' : Over.mk ψ' ⟶ W) (h : e.left = e'.left) :
    (⟨ψ, F.map e.op s⟩ : Σ χ : V ⟶ S, F.obj (op (Over.mk χ))) = ⟨ψ', F.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  obtain rfl : ψ = ψ' := by rw [← h1, ← h2, h]
  rw [Over.OverMorphism.ext h]

end TotalSigma

/-! ### From the total presheaf back to the slice -/

/-- **A representing scheme of the total presheaf of the degree-`d` Hilbert functor represents
the Hilbert functor.** The representing object over `S` is the representing scheme of the total
presheaf, equipped with the first component of the universal element as its structure morphism,
and the universal family is the second component. -/
theorem representsHilbertFunctorOfRank_of_representableBy {S : Scheme.{u}} (X : Over S) (d : ℕ)
    {W : Scheme.{u}} (R : (totalPresheaf (hilbertFunctorOfRank X d)).RepresentableBy W) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  classical
  obtain ⟨φ, t, hx⟩ : ∃ (φ : W ⟶ S) (t : HilbertFamily X (Over.mk φ) d),
      R.homEquiv (𝟙 W) =
        (⟨φ, t⟩ : Σ f : W ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk f))) :=
    ⟨_, (R.homEquiv (𝟙 W)).2, rfl⟩
  refine ⟨Over.mk φ, ?_⟩
  -- Restricting the universal element is restricting the universal family.
  have hmap : ∀ {A : Over S} (k : A ⟶ Over.mk φ),
      (totalPresheaf (hilbertFunctorOfRank X d)).map k.left.op (R.homEquiv (𝟙 W)) =
        (⟨A.hom, (hilbertFunctorOfRank X d).map k.op t⟩ :
          Σ f : A.left ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk f))) := by
    intro A k
    rw [hx]
    exact totalPresheafMap_mk (hilbertFunctorOfRank X d) k.left.op (Over.w k) t
  refine
    { family := fun {A} ↦ Equiv.ofBijective (fun k : A ⟶ Over.mk φ ↦ baseChange X k t) ⟨?_, ?_⟩
      naturality := ?_ }
  · intro k₁ k₂ hk
    have hk' : (hilbertFunctorOfRank X d).map k₁.op t = (hilbertFunctorOfRank X d).map k₂.op t :=
      hk
    refine Over.OverMorphism.ext (R.homEquiv.injective ?_)
    rw [R.homEquiv_eq k₁.left, R.homEquiv_eq k₂.left, hmap k₁, hmap k₂, hk']
  · intro Y
    obtain ⟨k₀, hk⟩ : ∃ k₀ : A.left ⟶ W,
        (totalPresheaf (hilbertFunctorOfRank X d)).map k₀.op (R.homEquiv (𝟙 W)) =
          (⟨A.hom, Y⟩ :
            Σ f : A.left ⟶ S, (hilbertFunctorOfRank X d).obj (op (Over.mk f))) :=
      ⟨R.homEquiv.symm _, (R.homEquiv_eq _).symm.trans (R.homEquiv.apply_symm_apply _)⟩
    have hb : k₀ ≫ φ = A.hom := totalSigma_fst_eq (F := hilbertFunctorOfRank X d)
      ((hmap (A := Over.mk (k₀ ≫ φ)) (Over.homMk k₀ rfl)).symm.trans hk)
    exact ⟨Over.homMk k₀ hb,
      totalSigma_snd_eq (F := hilbertFunctorOfRank X d) ((hmap (Over.homMk k₀ hb)).symm.trans hk)⟩
  · intro A' A m k
    show (baseChange X (m ≫ k) t).ideal =
      (baseChange X k t).ideal.comap (familyBaseChangeMap X m)
    rw [baseChange_comp, baseChange_ideal]

end Stacks.Hilbert

end
