module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMatrixDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectFullyFaithful

/-!
# Essential surjectivity of the comparison functor of Stacks Tag 0EXB

Let `p` be a prime and let `X` be a quasi-compact quasi-separated scheme in characteristic `p`.
This file proves that **every finite locally free module over the sheaf of rings `colim_F 𝒪_X` is
the extension of scalars of a finite locally free `𝒪_X`-module along a coprojection**, which is
the one hypothesis the statement of Stacks Tag 0EXB still carried, and concludes the tag.

The argument is the one Stacks gives. A finite locally free `colim_F 𝒪_X`-module `𝒢` is
trivialised over a cover of `X`, which refines to a *finite* cover by affine opens
(`AlgebraicGeometry.exists_finite_affine_subcover`); its transition matrices live over the
pairwise overlaps, which are quasi-compact because `X` is quasi-separated, so they come from
`𝒪_X` at a finite stage `n`, and raising the lifts to one common `p`-th power makes the cocycle
condition hold on the nose. Glueing the resulting matrix cocycle produces a finite locally free
`𝒪_X`-module `ℰ` with the same transition matrices
(`Stacks.SheafOfModules.MatrixCocycle.glued`), and the universal property of
`Stacks.SheafOfModules.CompatTrivialisation.compHom` identifies `𝒢` with the extension of
scalars of `ℰ` along the stage-`n` coprojection.

## Main results

* `AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`: **the stage functors of Stacks Tag
  0EXB are jointly essentially surjective.**
* `AlgebraicGeometry.isEquivalence_frobeniusColimitVectComparison`: **the comparison functor of
  Stacks Tag 0EXB is an equivalence**, with no hypotheses beyond those the tag carries.
* `AlgebraicGeometry.frobeniusColimitVectEquivalence`: **Stacks Tag 0EXB**, as an equivalence of
  categories `colim_F Vect(X) ≌ Vect(colim_F 𝒪_X)`.

## Implementation notes

The comparison with the extension of scalars is made through the universal property rather than
through the sections of `ℰ ⊗_{𝒪_X} colim_F 𝒪_X`: composing with
`Stacks.SheafOfModules.CompatTrivialisation.compHom` is a bijection
`Hom_{colim_F 𝒪_X}(𝒢, 𝒯) ≃ Hom_{𝒪_X}(ℰ, 𝒯)` for every `𝒯`, so by
`CategoryTheory.Adjunction.homEquiv_naturality_right` and
`CategoryTheory.isIso_iff_coyoneda_map_bijective` the adjunct of `compHom` under
`CategoryTheory.SheafOfModules.pullbackPushforwardAdjunction` is an isomorphism. Nothing about
the construction of the extension of scalars — a sheafified tensor product — is used.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.SheafOfModules TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- Restriction of scalars along a coprojection is the right adjoint of the stage functor, read
through `Stacks.SheafOfModules.CompatTrivialisation`'s spelling. -/
lemma pushforward_frobeniusStageStructureMap (n : ℕ) :
    _root_.SheafOfModules.pushforward.{u} (frobeniusStageStructureMap X p hX n)
      = _root_.SheafOfModules.restrictScalars (frobeniusColimitι X p hX n) := rfl

variable {X} in
/-- Combining the restrictions of a family of sections is combining the family itself, over a
smaller open. -/
private lemma combSections_comp_res
    {O : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
    (M : _root_.SheafOfModules.{u} O) {U W W' : X.Opens} {ι : Type u} [Fintype ι]
    (s : ι → ToType (M.val.obj (op U))) (g : W ≤ U) (h : W' ≤ W) :
    combSections M (fun a => res M (homOfLE g) (s a)) (homOfLE h)
      = combSections M s (homOfLE (h.trans g)) := by
  funext c
  refine Finset.sum_congr rfl fun a _ => congrArg (fun y => c a • y) ?_
  refine Eq.trans (res_res M (homOfLE g) (homOfLE h) (s a)) ?_
  exact congrArg (fun f : W' ⟶ U => res M f (s a))
    (Subsingleton.elim (homOfLE h ≫ homOfLE g) (homOfLE (h.trans g)))

/-- **A finite locally free `colim_F 𝒪_X`-module and a finite locally free `𝒪_X`-module with the
same transition matrices at a finite stage.** The cover is the finite affine refinement of a
trivialising cover; the matrices are descended by
`AlgebraicGeometry.exists_matrixCocycle_of_trivialisation` and glued by
`Stacks.SheafOfModules.MatrixCocycle.glued`. -/
theorem exists_compatTrivialisation [CompactSpace X] [QuasiSeparatedSpace X]
    (G : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    ∃ (N : ℕ) (E : _root_.SheafOfModules.{u} X.ringSheafOnOpens),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E ∧
        Nonempty (CompatTrivialisation (frobeniusColimitι X p hX N) E G) := by
  classical
  obtain ⟨I, U, m0, s0, hUtop, hbij0⟩ := exists_localTrivialisation G hG
  obtain ⟨K, hKfin, V, r, haff, hVU, hVtop⟩ :=
    exists_finite_affine_subcover U ((Opens.coversTop_iff _ U).mpr hUtop)
  let := hKfin
  have hbij : ∀ (k : K) ⦃W : X.Opens⦄ (h : W ≤ V k),
      Function.Bijective (combSections G (fun a => res G (homOfLE (hVU k)) (s0 (r k) a))
        (homOfLE h)) := by
    intro k W h
    rw [combSections_comp_res G (s0 (r k)) (hVU k) h]
    exact hbij0 (r k) (homOfLE (h.trans (hVU k)))
  obtain ⟨N, D, hD⟩ := exists_matrixCocycle_of_trivialisation X p hX G V haff
    (fun k => m0 (r k)) (fun k a => res G (homOfLE (hVU k)) (s0 (r k) a)) hbij
  refine ⟨N, D.glued, D.isFiniteLocallyFree_glued hVtop, ⟨?_⟩⟩
  refine
    { K := K
      V := V
      cover := hVtop
      m := fun k => m0 (r k)
      e := D.basis
      t := fun k a => res G (homOfLE (hVU k)) (s0 (r k) a)
      bijE := fun k W h => D.bijective_combSections_basis k h
      bijG := hbij
      compat := fun k l W hk hl a b => ?_ }
  have heq : D.entry k l hk hl a b
      = transMat D.glued V (fun k => m0 (r k)) D.basis
        (fun k W h => D.bijective_combSections_basis k h) k l hk hl a b :=
    congrFun (eq_transMat D.glued V (fun k => m0 (r k)) D.basis
      (fun k W h => D.bijective_combSections_basis k h) k l hk hl a (D.entry k l hk hl a)
      (D.res_basis k l hk hl a).symm) b
  exact Eq.trans
    (congrArg (fun z => (frobeniusColimitι X p hX N).hom.app (op W) z) heq.symm)
    (hD k l hk hl a b)

/-- **The extension of scalars of `ℰ` along the stage-`N` coprojection is `𝒢`**, when the two
carry compatible trivialisations. Composing with
`Stacks.SheafOfModules.CompatTrivialisation.compHom` is a bijection on morphisms out of `𝒢`, so
its adjunct under the extension/restriction adjunction is an isomorphism. -/
theorem nonempty_frobeniusStageExtendScalars_iso (N : ℕ)
    (E : _root_.SheafOfModules.{u} X.ringSheafOnOpens)
    (G : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    (C : CompatTrivialisation (frobeniusColimitι X p hX N) E G) :
    Nonempty ((frobeniusStageExtendScalars X p hX N).obj E ≅ G) := by
  have hadj := _root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
    (frobeniusStageStructureMap X p hX N)
  have hiso : IsIso ((hadj.homEquiv E G).symm C.compHom) := by
    rw [isIso_iff_coyoneda_map_bijective]
    intro T
    have hcomp : ∀ f : G ⟶ T,
        hadj.homEquiv E T ((hadj.homEquiv E G).symm C.compHom ≫ f)
          = C.compHom ≫ (_root_.SheafOfModules.restrictScalars
            (frobeniusColimitι X p hX N)).map f := fun f =>
      (hadj.homEquiv_naturality_right ((hadj.homEquiv E G).symm C.compHom) f).trans
        (congrArg (fun z => z ≫ (_root_.SheafOfModules.pushforward
            (frobeniusStageStructureMap X p hX N)).map f)
          ((hadj.homEquiv E G).apply_symm_apply C.compHom))
    have hb : Function.Bijective
        ((hadj.homEquiv E T) ∘ fun f : G ⟶ T => (hadj.homEquiv E G).symm C.compHom ≫ f) := by
      rw [show ((hadj.homEquiv E T) ∘ fun f : G ⟶ T =>
            (hadj.homEquiv E G).symm C.compHom ≫ f)
          = fun f : G ⟶ T => C.compHom ≫ (_root_.SheafOfModules.restrictScalars
            (frobeniusColimitι X p hX N)).map f from funext hcomp]
      exact C.bijective_comp_restrictScalars_map T
    exact ((hadj.homEquiv E T).bijective.of_comp_iff' _).mp hb
  exact ⟨@asIso _ _ _ _ ((hadj.homEquiv E G).symm C.compHom) hiso⟩

/-- **The stage functors of Stacks Tag 0EXB are jointly essentially surjective**: every finite
locally free `colim_F 𝒪_X`-module is isomorphic to the extension of scalars of a finite locally
free `𝒪_X`-module along a coprojection. -/
theorem exists_frobeniusStageFunctor_obj_iso [CompactSpace X] [QuasiSeparatedSpace X]
    (G : frobeniusColimitVectorBundles X p hX) :
    ∃ (n : ℕ) (E : X.Vect), Nonempty ((frobeniusStageFunctor X p hX n).obj E ≅ G) := by
  obtain ⟨N, E, hE, ⟨C⟩⟩ := exists_compatTrivialisation X p hX G.1 G.2
  exact ⟨N, ⟨E, hE⟩,
    ⟨ObjectProperty.isoMk _ (nonempty_frobeniusStageExtendScalars_iso X p hX N E G.1 C).some⟩⟩

/-- **The comparison functor of Stacks Tag 0EXB is an equivalence**, with no hypotheses beyond
those the tag carries: full faithfulness is
`AlgebraicGeometry.faithful_frobeniusColimitVectComparison` and
`AlgebraicGeometry.full_frobeniusColimitVectComparison`, and essential surjectivity is
`AlgebraicGeometry.exists_frobeniusStageFunctor_obj_iso`. -/
theorem isEquivalence_frobeniusColimitVectComparison [CompactSpace X] [QuasiSeparatedSpace X] :
    (frobeniusColimitVectComparison X p hX).IsEquivalence :=
  isEquivalence_frobeniusColimitVectComparison_of_essSurj X p hX
    (exists_frobeniusStageFunctor_obj_iso X p hX)

/-- **Stacks Project, Tag 0EXB.** The category `colim_F Vect(X)` of Stacks Tag 0EXA is equivalent
to the category of finite locally free modules over the sheaf of rings `colim_F 𝒪_X`, the
equivalence being the comparison functor of the tag. -/
@[stacks 0EXB "the category colim_F Vect(X) of Tag 0EXA is equivalent to the category of \
finite locally free modules over the sheaf of rings colim_F O_X"]
noncomputable def frobeniusColimitVectEquivalence [CompactSpace X] [QuasiSeparatedSpace X] :
    frobeniusColimitVectModel X p hX ≌ frobeniusColimitVectorBundles X p hX :=
  frobeniusColimitVectEquivalence_of_essSurj X p hX (exists_frobeniusStageFunctor_obj_iso X p hX)

end AlgebraicGeometry

end
