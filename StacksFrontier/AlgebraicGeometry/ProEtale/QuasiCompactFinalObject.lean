module

public import StacksFrontier.AlgebraicGeometry.ProEtale.FilteredColimitsOfProetaleCohomology

/-!
# Finite coverings of the final object of the small pro-étale site of a quasi-compact scheme

Let `X` be a quasi-compact scheme. The final object of the small pro-étale site `X_proét` is
`X` itself. Every covering sieve of it contains the arrows from a finite family of objects which
covers the final object: cover `X` by finitely many affine opens `V_k`, refine the restriction of
the sieve to each `V_k` by a finite family of affine objects
(`AlgebraicGeometry.ProEtale.exists_finite_affine_covering_le`), and compose.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.isTerminal_mk_id`: `X` is the final object of `X_proét`.
* `AlgebraicGeometry.Scheme.ProEt.exists_finite_coversTop_le`: for `X` quasi-compact, every
  covering sieve of the final object contains the arrows from a finite family covering the final
  object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-- The scheme `X`, with its identity, is the final object of the small pro-étale site. -/
noncomputable def isTerminal_mk_id : IsTerminal (ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun V => MorphismProperty.Over.homMk V.hom (Category.comp_id _) trivial)
    fun V f => by
      apply (MorphismProperty.Comma.forgetFullyFaithful
        (Functor.id Scheme.{u}) (Functor.fromPUnit X) _).map_injective
      refine CommaMorphism.ext ?_ (Subsingleton.elim _ _)
      exact (Category.comp_id f.left).symm.trans f.w

/-- An affine open of `X`, as an object of the small pro-étale site. -/
noncomputable abbrev ofAffineOpen (V : X.affineOpens) : X.ProEt := ProEt.mk V.1.ι

/-- The affine opens in a family covering `X` cover the final object of the small pro-étale
site. -/
theorem coversTop_ofAffineOpen {ι : Type*} (V : ι → X.affineOpens)
    (hV : ∀ x : X, ∃ i, x ∈ (V i : X.Opens)) :
    (ProEt.topology X).CoversTop fun i => ofAffineOpen (V i) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ isTerminal_mk_id]
  refine (ProEt.topology X).superset_covering (S := Sieve.ofArrows (fun i => ofAffineOpen (V i))
    fun i => isTerminal_mk_id.from _) ?_ (Precoverage.generate_mem_toGrothendieck ?_)
  · rintro Z f ⟨W, g, h, ⟨i⟩, rfl⟩
    exact ⟨i, ⟨g⟩⟩
  · change Presieve.map (ProEt.forget X ⋙ Over.forget X) (Presieve.ofArrows _ _) ∈
      Scheme.proetalePrecoverage _
    rw [Presieve.map_ofArrows]
    have hsurj : ∀ x : X, ∃ i, x ∈ Set.range (V i).1.ι := fun x => by
      obtain ⟨i, hi⟩ := hV x
      exact ⟨i, by rw [Scheme.Opens.range_ι]; exact hi⟩
    have hmap : ∀ i, (ProEt.forget X ⋙ Over.forget X).map (isTerminal_mk_id.from
        (ofAffineOpen (V i))) = (V i).1.ι := fun i => rfl
    simp only [hmap]
    refine ⟨Scheme.zariskiPrecoverage_le_qcPrecoverage _ ?_, ?_⟩
    · exact (Scheme.ofArrows_mem_precoverage_iff _).2
        ⟨hsurj, fun i => (inferInstance : IsOpenImmersion (V i).1.ι)⟩
    · exact (Scheme.ofArrows_mem_precoverage_iff _).2
        ⟨hsurj, fun i => (inferInstance : WeaklyEtale (V i).1.ι)⟩

/-- **Finite coverings of the final object.** If `X` is quasi-compact, every covering sieve `S`
of the final object of `X_proét` contains the arrows from a finite family of objects which
covers the final object. -/
theorem exists_finite_coversTop_le [CompactSpace X] (S : Sieve (ProEt.mk (𝟙 X)))
    (hS : S ∈ ProEt.topology X _) :
    ∃ (n : ℕ) (W : Fin n → X.ProEt), (ProEt.topology X).CoversTop W ∧
      ∀ i, S (isTerminal_mk_id.from (W i)) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => V.1.isOpen)
    (fun x _ => by
      obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  let V : t → X.affineOpens := fun k => k.1
  have hV : ∀ x : X, ∃ k, x ∈ (V k : X.Opens) := fun x => by
    obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨k, hk⟩, hx⟩
  have hE : ∀ k, ∃ E : PreZeroHypercover.{u + 1} (ofAffineOpen (V k)), Finite E.I₀ ∧
      E.presieve₀ ∈ Scheme.ProEt.precoverage X _ ∧
      E.sieve₀ ≤ S.pullback (isTerminal_mk_id.from _) ∧ ∀ i, IsAffine (E.X i).left := fun k => by
    have : IsAffine (ofAffineOpen (V k)).left := (V k).2
    exact ProEtale.exists_finite_affine_covering_le _ _
      ((ProEt.topology X).pullback_stable _ hS)
  choose E hEfin hEcov hEle _ using hE
  have : Finite (Σ k, (E k).I₀) := by
    have := fun k => hEfin k
    infer_instance
  let W' : (Σ k, (E k).I₀) → X.ProEt := fun p => (E p.1).X p.2
  have hW' : (ProEt.topology X).CoversTop W' := fun U => by
    refine (ProEt.topology X).transitive (coversTop_ofAffineOpen V hV U) _ ?_
    rintro U' f ⟨k, ⟨a⟩⟩
    refine (ProEt.topology X).superset_covering ?_
      ((ProEt.topology X).pullback_stable a (Precoverage.generate_mem_toGrothendieck
        (hEcov k)))
    rintro U'' b ⟨Y, c, d, ⟨i⟩, hcd⟩
    exact ⟨⟨k, i⟩, ⟨c⟩⟩
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Σ k, (E k).I₀)
  refine ⟨n, W' ∘ e.symm, fun U => ?_, fun j => ?_⟩
  · refine (ProEt.topology X).superset_covering ?_ (hW' U)
    rintro Z f ⟨p, ⟨g⟩⟩
    exact ⟨e p, ⟨by simpa using g⟩⟩
  · have heq : isTerminal_mk_id.from ((W' ∘ e.symm) j) =
        (E (e.symm j).1).f (e.symm j).2 ≫ isTerminal_mk_id.from _ :=
      isTerminal_mk_id.hom_ext _ _
    rw [heq]
    exact hEle _ _ (Sieve.le_generate _ _ _ (PreZeroHypercover.presieve₀_f _ _))

end AlgebraicGeometry.Scheme.ProEt

end
