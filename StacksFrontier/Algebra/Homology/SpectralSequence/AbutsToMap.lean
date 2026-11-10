module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.Transport

/-!
# Transporting an abutment along an exact functor

`CategoryTheory.SpectralSequence.map` applies an additive, homology-preserving functor `F` to
every page of a spectral sequence. This file carries the abutment statement
`CategoryTheory.SpectralSequence.AbutsTo` along that construction: if `E` abuts to `H` then
`E.map F` abuts to `F ∘ H`.

The motivating case is `F = AddCommGrpCat.uliftFunctor`, i.e.
`CategoryTheory.SpectralSequence.ulift`. A spectral sequence whose terms are `Hom` groups of an
abelian category lives in the morphism universe of that category, while the `Ext` groups it is to
abut to live in the universe of the `Hom` groups of the derived category; the two are unrelated,
and the comparison is made after lifting both to a common upper bound.

## Main results

* `CategoryTheory.SpectralSequence.hasPageInfinityAt_map`: the existence of an infinity page is
  preserved by transport along `F`.
* `CategoryTheory.SpectralSequence.AbutsTo.map`: **abutment is preserved by transport along
  `F`**, the abutment family being replaced by its image under `F`.

## Implementation notes

The witnessing filtration of `F.obj (H n)` is the image filtration `p ↦ Im(F(F^pH^n))`, i.e. the
subobject `Subobject.mk (F.map (F^pH^n).arrow)`; this needs `F` to preserve monomorphisms, which
is the only hypothesis beyond those `CategoryTheory.SpectralSequence.map` already asks for. It
reaches `⊤` and `⊥` where the original filtration does, because `F` carries an isomorphism to an
isomorphism and a zero morphism to a zero morphism, and its graded pieces are the images of the
original ones because `F` preserves cokernels.

No compatibility between the identifications at two degrees is asked for, and none is produced:
`AbutsTo` is a proposition whose witnessing isomorphisms are existentially quantified.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
-/

@[expose] public section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- **An infinity page survives transport along an exact functor.** The differentials of
`E.map F` are the images under `F` of those of `E`, so they vanish wherever the latter do. -/
theorem hasPageInfinityAt_map {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
    (E : SpectralSequence C c r₀) (pq : κ) [E.HasPageInfinityAt pq] :
    (E.map F).HasPageInfinityAt pq := by
  constructor
  · obtain ⟨r, hr⟩ := E.nonempty_hasEdgeMonoSet pq
    refine ⟨r, hr.1, fun r' hrr' => ?_⟩
    have := hr.2 r' hrr'
    refine ⟨E.le₀_of_hasEdgeMonoAt pq r', fun pq' => ?_⟩
    change F.map ((E.page r' (E.le₀_of_hasEdgeMonoAt pq r')).d pq' pq) = 0
    rw [E.d_eq_zero_of_hasEdgeMonoAt pq' pq r', F.map_zero]
  · obtain ⟨r, hr⟩ := E.nonempty_hasEdgeEpiSet pq
    refine ⟨r, hr.1, fun r' hrr' => ?_⟩
    have := hr.2 r' hrr'
    refine ⟨E.le₀_of_hasEdgeEpiAt pq r', fun pq' => ?_⟩
    change F.map ((E.page r' (E.le₀_of_hasEdgeEpiAt pq r')).d pq pq') = 0
    rw [E.d_eq_zero_of_hasEdgeEpiAt pq pq' r', F.map_zero]

/-- **Abutment is preserved by transport along an exact functor.** If the cohomological spectral
sequence `E` abuts to `H`, then `E.map F` abuts to `n ↦ F(H n)`.

The filtration of `F(H n)` is the image under `F` of the one witnessing the abutment of `E`, and
its graded pieces are the images of the graded pieces because `F` preserves cokernels; the
infinity page of `E.map F` is the image of that of `E` because both are computed on one page,
beyond the stabilisation point of either sequence. -/
theorem AbutsTo.map [F.PreservesMonomorphisms] {r₀ : ℤ}
    {E : CohomologicalSpectralSequence C r₀} {H : ℤ → C} (hE : AbutsTo E H) :
    AbutsTo (E.map F) (fun n => F.obj (H n)) := by
  obtain ⟨hinf, G, hG, hbounds, hgr⟩ := hE
  have hinf' : ∀ p q : ℤ, (E.map F).HasPageInfinityAt (p, q) := fun p q =>
    have := hinf p q; hasPageInfinityAt_map F E (p, q)
  have hle : ∀ n p p', p ≤ p' →
      Subobject.mk (F.map (G n p').arrow) ≤ Subobject.mk (F.map (G n p).arrow) := fun n p p' hp =>
    Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE _ _ (hG n hp)))
      (by rw [← F.map_comp, Subobject.ofLE_arrow])
  refine ⟨hinf', fun n p => Subobject.mk (F.map (G n p).arrow), fun n p p' hp => ?_,
    fun n => ?_, fun p q => ?_⟩
  · exact hle n p p' hp
  · obtain ⟨a, b, hab, ha, hb⟩ := hbounds n
    refine ⟨a, b, hab, ?_, ?_⟩
    · have : IsIso (G n a).arrow := (Subobject.isIso_arrow_iff_eq_top (G n a)).mpr ha
      exact (Subobject.isIso_iff_mk_eq_top _).mp (Functor.map_isIso F _)
    · rw [Subobject.mk_eq_bot_iff_zero, hb, Subobject.bot_arrow, F.map_zero]
  · obtain ⟨eInf⟩ := hgr p q
    have := hinf p q
    have := hinf' p q
    set r := max (E.rMin (p, q)) ((E.map F).rMin (p, q))
    have : E.HasEdgeMonoAtFrom (p, q) r := ⟨(E.rToMin_LE_rMin _).trans (le_max_left _ _)⟩
    have : E.HasEdgeEpiAtFrom (p, q) r := ⟨(E.rFromMin_LE_rMin _).trans (le_max_left _ _)⟩
    have : (E.map F).HasEdgeMonoAtFrom (p, q) r :=
      ⟨((E.map F).rToMin_LE_rMin _).trans (le_max_right _ _)⟩
    have : (E.map F).HasEdgeEpiAtFrom (p, q) r :=
      ⟨((E.map F).rFromMin_LE_rMin _).trans (le_max_right _ _)⟩
    have hpageInf : (E.map F).pageInfinity (p, q) ≅ F.obj (E.pageInfinity (p, q)) :=
      (E.map F).pageInfinityIso (p, q) r ≪≫ Iso.refl _ ≪≫
        F.mapIso ((E.pageInfinityIso (p, q) r).symm)
    let f := Subobject.ofLE (G (p + q) (p + 1)) (G (p + q) p) (hG (p + q) (by omega))
    have := Functor.PreservesHomology.preservesCokernel F f
    let g := Subobject.ofLE _ _ (hle (p + q) p (p + 1) (by omega))
    have hsq : (Subobject.underlyingIso (F.map (G (p + q) (p + 1)).arrow)).symm.hom ≫
        g =
          F.map f ≫ (Subobject.underlyingIso (F.map (G (p + q) p).arrow)).symm.hom := by
      apply (cancel_mono (Subobject.mk (F.map (G (p + q) p).arrow)).arrow).1
      rw [Category.assoc, Subobject.ofLE_arrow, Category.assoc, Iso.symm_hom, Iso.symm_hom,
        Subobject.underlyingIso_arrow, Subobject.underlyingIso_arrow, ← F.map_comp,
        Subobject.ofLE_arrow]
    exact ⟨hpageInf ≪≫ F.mapIso eInf ≪≫ PreservesCokernel.iso F f ≪≫
      cokernel.mapIso (F.map f) g
        (Subobject.underlyingIso (F.map (G (p + q) (p + 1)).arrow)).symm
        (Subobject.underlyingIso (F.map (G (p + q) p).arrow)).symm hsq.symm⟩

end CategoryTheory.SpectralSequence

end
