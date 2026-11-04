module

public import StacksFrontier.RingTheory.Flat.ElementaryEtaleNeighborhood

/-!
# Composing elementary étale localizations

An elementary étale localization of a ring map `R → S` at a prime `q` over a prime `p`
(`Algebra.ElementaryEtaleLocalization`, Stacks 05HW) is a commutative square with étale horizontal
maps, primes above `p` and `q`, and no extension of residue fields. Two such squares, placed side
by side, compose to a third.

## Main definitions

* `Algebra.ElementaryEtaleLocalization.comp`: an elementary étale localization of `R → S` at `q`,
  followed by one of the resulting `R' → S'` at the resulting `q'`, is an elementary étale
  localization of `R → S` at `q`.

## Main results

* `Ideal.ResidueField.map_comp`: the residue-field embedding of a composite of ring maps is the
  composite of the residue-field embeddings.

## References

* [Stacks Project, Tag 05HW](https://stacks.math.columbia.edu/tag/05HW)
* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
-/

@[expose] public section

universe u v w x w' x'

/-- The residue-field embedding of a composite is the composite of the embeddings: if
`I = f⁻¹(J)` and `J = g⁻¹(K)` then the canonical map `κ(I) → κ(K)` attached to `g ∘ f` is the
composite of the maps attached to `f` and to `g`. -/
theorem Ideal.ResidueField.map_comp {R : Type u} {S : Type v} {T : Type w} [CommRing R]
    [CommRing S] [CommRing T] (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (K : Ideal T)
    [K.IsPrime] (f : R →+* S) (g : S →+* T) (hf : I = J.comap f) (hg : J = K.comap g)
    (hfg : I = K.comap (g.comp f)) :
    (Ideal.ResidueField.map J K g hg).comp (Ideal.ResidueField.map I J f hf)
      = Ideal.ResidueField.map I K (g.comp f) hfg := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ I)) ?_
  ext x
  simp

namespace Algebra.ElementaryEtaleLocalization

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {p : Ideal R}
  {q : Ideal S} [p.IsPrime] [q.IsPrime] [q.LiesOver p]

/-- Elementary étale localizations compose: given an elementary étale localization `E` of `R → S`
at `q` and an elementary étale localization `F` of `E.R' → E.S'` at `E.q'`, the outer square is an
elementary étale localization of `R → S` at `q`, with the same upper right corner, primes and
residue fields as `F`. -/
noncomputable def comp (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') :
    ElementaryEtaleLocalization.{u, v, w', x'} R S p q where
  R' := F.R'
  S' := F.S'
  algebraRR' := ((algebraMap E.R' F.R').comp (algebraMap R E.R')).toAlgebra
  algebraSS' := ((algebraMap E.S' F.S').comp (algebraMap S E.S')).toAlgebra
  algebraR'S' := F.algebraR'S'
  commutes := by
    refine RingHom.ext fun r ↦ ?_
    have hE := RingHom.congr_fun E.commutes r
    have hF := RingHom.congr_fun F.commutes (algebraMap R E.R' r)
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra] at hE hF ⊢
    rwa [hE]
  etale_R' :=
    letI : Algebra R F.R' := ((algebraMap E.R' F.R').comp (algebraMap R E.R')).toAlgebra
    letI : IsScalarTower R E.R' F.R' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    Algebra.Etale.comp R E.R' F.R'
  etale_S' :=
    letI : Algebra S F.S' := ((algebraMap E.S' F.S').comp (algebraMap S E.S')).toAlgebra
    letI : IsScalarTower S E.S' F.S' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    Algebra.Etale.comp S E.S' F.S'
  p' := F.p'
  q' := F.q'
  p'_isPrime := F.p'_isPrime
  q'_isPrime := F.q'_isPrime
  p'_liesOver := by
    rw [RingHom.algebraMap_toAlgebra, ← Ideal.comap_comap, ← F.p'_liesOver, ← E.p'_liesOver]
  q'_liesOver_q := by
    rw [RingHom.algebraMap_toAlgebra, ← Ideal.comap_comap, ← F.q'_liesOver_q, ← E.q'_liesOver_q]
  q'_liesOver_p' := F.q'_liesOver_p'
  residueFieldMap_p_bijective := by
    have hb := F.residueFieldMap_p_bijective.comp E.residueFieldMap_p_bijective
    rwa [← RingHom.coe_comp, Ideal.ResidueField.map_comp p E.p' F.p' (algebraMap R E.R')
      (algebraMap E.R' F.R') E.p'_liesOver F.p'_liesOver
      (by rw [← Ideal.comap_comap, ← F.p'_liesOver, ← E.p'_liesOver])] at hb
  residueFieldMap_q_bijective := by
    have hb := F.residueFieldMap_q_bijective.comp E.residueFieldMap_q_bijective
    rwa [← RingHom.coe_comp, Ideal.ResidueField.map_comp q E.q' F.q' (algebraMap S E.S')
      (algebraMap E.S' F.S') E.q'_liesOver_q F.q'_liesOver_q
      (by rw [← Ideal.comap_comap, ← F.q'_liesOver_q, ← E.q'_liesOver_q])] at hb

/-- The étale `R`-algebra of `E.comp F` is `F.R'`. -/
@[simp]
theorem comp_R' (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') :
    (E.comp F).R' = F.R' := rfl

/-- The étale `S`-algebra of `E.comp F` is `F.S'`. -/
@[simp]
theorem comp_S' (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') :
    (E.comp F).S' = F.S' := rfl

/-- The prime of `E.comp F` above `p` is `F.p'`. -/
@[simp]
theorem comp_p' (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') :
    (E.comp F).p' = F.p' := rfl

/-- The prime of `E.comp F` above `q` is `F.q'`. -/
@[simp]
theorem comp_q' (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') :
    (E.comp F).q' = F.q' := rfl

/-- The structure map `R → (E.comp F).R'` is the composite of `R → E.R'` and `E.R' → F.R'`. -/
theorem algebraMap_comp_R' (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') (r : R) :
    letI := (E.comp F).algebraRR'
    algebraMap R (E.comp F).R' r = algebraMap E.R' F.R' (algebraMap R E.R' r) := rfl

/-- The structure map `S → (E.comp F).S'` is the composite of `S → E.S'` and `E.S' → F.S'`. -/
theorem algebraMap_comp_S' (E : ElementaryEtaleLocalization.{u, v, w, x} R S p q)
    (F : ElementaryEtaleLocalization.{w, x, w', x'} E.R' E.S' E.p' E.q') (s : S) :
    letI := (E.comp F).algebraSS'
    algebraMap S (E.comp F).S' s = algebraMap E.S' F.S' (algebraMap S E.S' s) := rfl

end Algebra.ElementaryEtaleLocalization

end
