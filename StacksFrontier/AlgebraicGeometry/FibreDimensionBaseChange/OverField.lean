module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecStalkHeight
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.RingTheory.KrullDimension.BaseChange

/-!
# The local ring and the residue field of a base change along a field extension

Let `k` be a field, let `π : F ⟶ Spec k` be locally of finite type, let `K / k` be a field
extension and let

```
P ---p₁---> F
|           |
p₂          π
v           v
Spec K ---> Spec k
```

be a fibre product diagram. For a point `w` of `P` with image `p₁ w` in `F` there is a single
natural number `n` which is both the excess of the dimension of the local ring of `P` at `w` over
the dimension of the local ring of `F` at `p₁ w`, and the drop of the transcendence degree of the
residue field from `κ(p₁ w) / k` to `κ(w) / K`. This is the content of Stacks 0CWE transported
from a base change of rings to a base change of schemes, and it is the case of Stacks 02FY
part (2) in which the base is the spectrum of a field.

Moreover `n` can be made `0` by a suitable choice of `w` above a given point of `F`: this is the
case of Stacks 02FY part (3) in which the base is the spectrum of a field.

## Main results

* `AlgebraicGeometry.exists_add_ringKrullDim_stalk_and_trdeg_of_isPullback_over_field` is the
  statement above.
* `AlgebraicGeometry.exists_point_eq_ringKrullDim_stalk_and_trdeg_of_isPullback_over_field` is
  the refinement with `n = 0` for a suitable point.

## Implementation notes

The argument is the one part (1) of Stacks 02FY uses in
`StacksFrontier/AlgebraicGeometry/FibreDimensionBaseChange/Basic.lean`, run for the pair
(dimension of the local ring, transcendence degree of the residue field) instead of for the
local dimension of the underlying space. There are four steps, each reducing to the next:

* an arbitrary fibre product square is replaced by the canonical pullback along
  `CategoryTheory.IsPullback.isoPullback`;
* an arbitrary source `F` is replaced by a member of its affine open cover, the point being
  lifted through `AlgebraicGeometry.Scheme.Pullback.openCoverOfLeft`;
* for an affine source `Spec A` the structure morphism is written as `Spec.map ψ` by
  `AlgebraicGeometry.Spec.map_surjective` and `ψ` is turned into an algebra structure by
  `algebraize`;
* the base change of `Spec A` along `K / k` is identified with `Spec (A ⊗[k] K)` by
  `AlgebraicGeometry.pullbackSpecIso`, where both invariants are read off the prime by
  `AlgebraicGeometry.ringKrullDim_stalk_spec` and
  `AlgebraicGeometry.trdeg_spec_residueField` and the ring-theoretic input applies.

The first three steps are all instances of one transport lemma,
`AlgebraicGeometry.stalk_and_trdeg_eq_of_isOpenImmersion`: an open immersion over `Spec k`
changes neither invariant, being étale for the dimension of the local ring (Tag 04N8) and
surjective on stalks for the residue field (Tag 0A21). Étaleness alone would *not* do for the
residue field — a finite separable field extension is étale and does not preserve the residue
field — which is why the transport is stated for open immersions and not for étale morphisms.

The statement with `n = 0` runs the same four steps in the opposite direction: a point of the
base change over the given point is produced in the affine model from the last conjunct of
0CWE (`AlgebraicGeometry.exists_liesOver_height_eq`) and then pushed forward along the three
transports, each of which carries a point of the smaller model to a point of the larger one with
the same image in `F` — through the inverse of `AlgebraicGeometry.pullbackSpecIso`, through
`CategoryTheory.Limits.pullback.map` for a chart containing the given point, and through the
inverse of `CategoryTheory.IsPullback.isoPullback`.

The ring-theoretic input `AlgebraicGeometry.exists_height_eq_add` is Stacks 0CWE
(`Algebra.IsPushout.height_fiber_add_height_eq_and_add_trdeg_eq`) with the height of the fibre
eliminated in favour of a natural number: that height is finite because `T` is of finite type
over the field `K`, hence Noetherian, so the prime `Q` has finite height, and the first of
0CWE's two equations then forces the fibre height to be finite as well. The `ℕ`-valued form is
what makes the two equations of part (2) a single statement rather than two, since the common
value appears on both.

The `k`-algebra structure on a residue field is the composite of global sections with evaluation
at the point, as in
`StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/ResidueField.lean`; it is not an instance
and is introduced in each statement. Every statement carries the image point as a separate
variable together with an equation pinning it down, so that a caller holding the point in a
different but equal form does not have to rewrite underneath the algebra structure, which is
not a type-correct rewrite.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 04N8](https://stacks.math.columbia.edu/tag/04N8)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0CWE](https://stacks.math.columbia.edu/tag/0CWE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-- An open immersion over `Spec k` changes neither the dimension of the local ring nor the
transcendence degree of the residue field over `k`. -/
private theorem stalk_and_trdeg_eq_of_isOpenImmersion {k : Type u} [Field k] {F G : Scheme.{u}}
    (π : F ⟶ Spec (.of k)) (ρ : G ⟶ Spec (.of k)) (i : G ⟶ F) [IsOpenImmersion i]
    (hi : i ≫ π = ρ) (y : G) (z : F) (hz : i y = z) :
    letI : Algebra k (F.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ F.Γevaluation z).hom.toAlgebra
    letI : Algebra k (G.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ρ.appTop ≫ G.Γevaluation y).hom.toAlgebra
    ringKrullDim (G.presheaf.stalk y) = ringKrullDim (F.presheaf.stalk z) ∧
      Algebra.trdeg k (G.residueField y) = Algebra.trdeg k (F.residueField z) := by
  subst hi
  subst hz
  have : Etale i := HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
  exact ⟨ringKrullDim_stalk_eq_of_etale i y,
    (trdeg_residueField_of_surjectiveOnStalks k π i y).symm⟩

/-- **Stacks 0CWE with the height of the fibre replaced by a natural number.** In a pushout
square `T = K ⊗[k] S` of a finite type `k`-algebra `S` along a field extension `K / k`, a prime
`Q` of `T` and the prime `q = Q ∩ S` below it satisfy `ht Q = ht q + n` and
`trdeg_k κ(q) = trdeg_K κ(Q) + n` for one and the same `n : ℕ`, namely the dimension of the
fibre ring at `Q`. -/
private theorem exists_height_eq_add (k K S T : Type u) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (Q : Ideal T) [Q.IsPrime] :
    ∃ n : ℕ, Q.height = (Q.under S).height + n ∧
      Cardinal.toENat (Algebra.trdeg k (Q.under S).ResidueField) =
        Cardinal.toENat (Algebra.trdeg K Q.ResidueField) + n := by
  have hft : Algebra.FiniteType K T :=
    Algebra.FiniteType.equiv inferInstance (Algebra.IsPushout.equiv k K S T)
  have hnoe : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  obtain ⟨h1, h2⟩ := Algebra.IsPushout.height_fiber_add_height_eq_and_add_trdeg_eq
    k K S T |>.1 (Q.under S) Q
  have hQ : Q.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hmt : (Q.map (Ideal.Quotient.mk ((Q.under S).map (algebraMap S T)))).height ≠ ⊤ :=
    fun h ↦ hQ (by rw [h, top_add] at h1; exact h1.symm)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hmt
  exact ⟨n, by rw [← h1, ← hn, add_comm], by rw [← h2, ← hn, add_comm]⟩

/-- The affine case, for an arbitrary pushout square of rings: the two invariants of `Spec T` at
a prime and of `Spec A` at the prime below it differ by the one natural number of Stacks
0CWE. -/
private theorem exists_spec_of_isPushout (k K A T : Type u) [Field k] [Field K]
    [CommRing A] [CommRing T] [Algebra k K] [Algebra k A] [Algebra k T] [Algebra K T]
    [Algebra A T] [IsScalarTower k K T] [IsScalarTower k A T] [Algebra.IsPushout k K A T]
    [Algebra.FiniteType k A] (w : Spec (.of T)) (z : Spec (.of A))
    (hz : Spec.map (CommRingCat.ofHom (algebraMap A T)) w = z) :
    letI : Algebra k ((Spec (.of A)).residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
        (Spec (.of A)).Γevaluation z).hom.toAlgebra
    letI : Algebra K ((Spec (.of T)).residueField w) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap K T))).appTop ≫
        (Spec (.of T)).Γevaluation w).hom.toAlgebra
    ∃ n : ℕ,
      ringKrullDim ((Spec (.of T)).presheaf.stalk w) =
          ringKrullDim ((Spec (.of A)).presheaf.stalk z) + n ∧
        Cardinal.toENat (Algebra.trdeg k ((Spec (.of A)).residueField z)) =
          Cardinal.toENat (Algebra.trdeg K ((Spec (.of T)).residueField w)) + n := by
  subst hz
  have hQ := w.isPrime
  obtain ⟨n, h1, h2⟩ := exists_height_eq_add k K A T w.asIdeal
  refine ⟨n, ?_, ?_⟩
  · rw [ringKrullDim_stalk_spec, ringKrullDim_stalk_spec,
      show (Spec.map (CommRingCat.ofHom (algebraMap A T)) w).asIdeal = w.asIdeal.under A from rfl,
      h1]
    push_cast
    rfl
  · rw [trdeg_spec_residueField k A, trdeg_spec_residueField K T]
    exact h2

/-- The base change of `Spec A` for a finite type `k`-algebra `A` along a field extension
`K / k`, in the canonical pullback: the invariants at a point of the pullback and at its image
differ by the natural number of Stacks 0CWE. -/
private theorem exists_canonical_of_isAffine (k K A : Type u) [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k A]
    (v : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (z : Spec (.of A))
    (hz : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) v = z) :
    letI : Algebra k ((Spec (.of A)).residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
        (Spec (.of A)).Γevaluation z).hom.toAlgebra
    letI : Algebra K ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop ≫
        (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Γevaluation v).hom.toAlgebra
    ∃ n : ℕ,
      ringKrullDim ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk v) =
          ringKrullDim ((Spec (.of A)).presheaf.stalk z) + n ∧
        Cardinal.toENat (Algebra.trdeg k ((Spec (.of A)).residueField z)) =
          Cardinal.toENat (Algebra.trdeg K
            ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v)) + n := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := K)
  obtain ⟨hdim, htr⟩ := stalk_and_trdeg_eq_of_isOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[k] K))))
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (pullbackSpecIso k A K).hom (pullbackSpecIso_hom_snd k A K) v _ rfl
  obtain ⟨n, h1, h2⟩ := exists_spec_of_isPushout k K A (A ⊗[k] K)
    ((pullbackSpecIso k A K).hom v) z
    (by rw [← hz, ← Scheme.Hom.comp_apply, pullbackSpecIso_hom_fst' k A K])
  exact ⟨n, hdim.trans h1, h2.trans (by rw [htr])⟩

/-- The affine case for an arbitrary morphism `Spec A ⟶ Spec k` locally of finite type. -/
private theorem exists_canonical_of_isAffine' {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : CommRingCat.{u}} (π : Spec A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
    (v : ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (z : Spec A)
    (hz : pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) v = z) :
    letI : Algebra k ((Spec A).residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ (Spec A).Γevaluation z).hom.toAlgebra
    letI : Algebra K
        ((pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop ≫
        (pullback π
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Γevaluation v).hom.toAlgebra
    ∃ n : ℕ,
      ringKrullDim ((pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk v) =
          ringKrullDim ((Spec A).presheaf.stalk z) + n ∧
        Cardinal.toENat (Algebra.trdeg k ((Spec A).residueField z)) =
          Cardinal.toENat (Algebra.trdeg K ((pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v)) + n := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective π
  have hft : RingHom.FiniteType ψ.hom :=
    HasRingHomProperty.Spec_iff.mp (show LocallyOfFiniteType (Spec.map ψ) from inferInstance)
  algebraize [ψ.hom]
  exact exists_canonical_of_isAffine k K ↥A v z hz

/-- The map of base changes along `g` induced by a morphism `i : G ⟶ F` over `Spec k`. -/
private noncomputable abbrev pullbackMap {k K : Type u} [Field k] [Field K] {F G : Scheme.{u}}
    (π : F ⟶ Spec (CommRingCat.of k)) (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (i : G ⟶ F) : pullback (i ≫ π) g ⟶ pullback π g :=
  pullback.map (i ≫ π) g π g i (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- For an open immersion `i : G ⟶ F` of schemes over `Spec k`, the induced open immersion of base
changes along `g : Spec K ⟶ Spec k` preserves the dimension of the local ring, the transcendence
degree of the residue field over `K`, and the image point in `F`. -/
private theorem stalk_and_trdeg_eq_pullback_map {k K : Type u} [Field k] [Field K] [Algebra k K]
    {F G : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k))
    (g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (i : G ⟶ F) [IsOpenImmersion i] (v : ↥(pullback (i ≫ π) g)) :
    letI : Algebra K ((pullback (i ≫ π) g).residueField v) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd (i ≫ π) g).appTop ≫
        (pullback (i ≫ π) g).Γevaluation v).hom.toAlgebra
    letI : Algebra K ((pullback π g).residueField (pullbackMap π g i v)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd π g).appTop ≫
        (pullback π g).Γevaluation (pullbackMap π g i v)).hom.toAlgebra
    ringKrullDim ((pullback (i ≫ π) g).presheaf.stalk v) =
        ringKrullDim ((pullback π g).presheaf.stalk (pullbackMap π g i v)) ∧
      Algebra.trdeg K ((pullback (i ≫ π) g).residueField v) =
        Algebra.trdeg K ((pullback π g).residueField (pullbackMap π g i v)) ∧
      pullback.fst π g (pullbackMap π g i v) = i (pullback.fst (i ≫ π) g v) := by
  have h := stalk_and_trdeg_eq_of_isOpenImmersion _ _ (pullbackMap π g i)
    (pullback.lift_snd _ _ _) v _ rfl
  exact ⟨h.1, h.2, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]⟩

/-- The canonical pullback of an arbitrary morphism locally of finite type to the spectrum of a
field along a field extension. -/
private theorem exists_canonical {k K : Type u} [Field k] [Field K] [Algebra k K]
    {F : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
    (v : ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
    (z : F)
    (hz : pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) v = z) :
    letI : Algebra k (F.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ F.Γevaluation z).hom.toAlgebra
    letI : Algebra K
        ((pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop ≫
        (pullback π
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Γevaluation v).hom.toAlgebra
    ∃ n : ℕ,
      ringKrullDim ((pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk v) =
          ringKrullDim (F.presheaf.stalk z) + n ∧
        Cardinal.toENat (Algebra.trdeg k (F.residueField z)) =
          Cardinal.toENat (Algebra.trdeg K ((pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v)) + n := by
  obtain ⟨j, v', rfl⟩ : ∃ (j : F.affineOpenCover.I₀)
      (v' : ↥(pullback (F.affineOpenCover.f j ≫ π)
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      pullbackMap π (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (F.affineOpenCover.f j) v' = v := by
    obtain ⟨i, v₀, hv⟩ := (Scheme.Pullback.openCoverOfLeft F.affineOpenCover.openCover π
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).exists_eq v
    exact ⟨i, v₀, hv⟩
  obtain ⟨hdimP, htrP, hfst⟩ := stalk_and_trdeg_eq_pullback_map π
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) (F.affineOpenCover.f j) v'
  obtain ⟨hdimF, htrF⟩ := stalk_and_trdeg_eq_of_isOpenImmersion π
    (F.affineOpenCover.f j ≫ π) (F.affineOpenCover.f j) rfl
    (pullback.fst (F.affineOpenCover.f j ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap k K))) v') z
    (by rw [← hz, hfst])
  obtain ⟨n, h1, h2⟩ := exists_canonical_of_isAffine' (F.affineOpenCover.f j ≫ π) v' _ rfl
  exact ⟨n, hdimP.symm.trans (h1.trans (by rw [hdimF])),
    (congrArg Cardinal.toENat htrF).symm.trans (h2.trans (by rw [htrP]))⟩

/-- **Stacks Project, Tag 02FY part (2), over a field.** Let `π : F ⟶ Spec k` be locally of
finite type, let `K / k` be a field extension and let `P` be the base change of `F` along it.
For a point `w` of `P` there is a natural number `n` which is at the same time the excess of the
dimension of the local ring of `P` at `w` over the dimension of the local ring of `F` at the
image of `w`, and the drop of the transcendence degree of the residue field from `κ(p₁ w) / k`
to `κ(w) / K`. -/
public theorem exists_add_ringKrullDim_stalk_and_trdeg_of_isPullback_over_field
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {F P : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
    {p₁ : P ⟶ F} {p₂ : P ⟶ Spec (CommRingCat.of K)}
    (hP : IsPullback p₁ p₂ π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (w : P) :
    letI : Algebra k (F.residueField (p₁ w)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ F.Γevaluation (p₁ w)).hom.toAlgebra
    letI : Algebra K (P.residueField w) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p₂.appTop ≫ P.Γevaluation w).hom.toAlgebra
    ∃ n : ℕ,
      ringKrullDim (P.presheaf.stalk w) = ringKrullDim (F.presheaf.stalk (p₁ w)) + n ∧
        Cardinal.toENat (Algebra.trdeg k (F.residueField (p₁ w))) =
          Cardinal.toENat (Algebra.trdeg K (P.residueField w)) + n := by
  obtain ⟨hdimP, htrP⟩ := stalk_and_trdeg_eq_of_isOpenImmersion
    (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) p₂
    hP.isoPullback.hom hP.isoPullback_hom_snd w _ rfl
  obtain ⟨n, h1, h2⟩ := exists_canonical π (hP.isoPullback.hom w) (p₁ w)
    (by rw [← Scheme.Hom.comp_apply, hP.isoPullback_hom_fst])
  exact ⟨n, hdimP.trans h1, h2.trans (by rw [htrP])⟩

/-- **The last conjunct of Stacks 0CWE.** In a pushout square `T = K ⊗[k] S` of a finite type
`k`-algebra `S` along a field extension `K / k`, every prime `q` of `S` has a prime `Q` of `T`
above it with `ht Q = ht q` and `trdeg_k κ(q) = trdeg_K κ(Q)`: a prime for which the dimension
of the fibre ring vanishes. -/
private theorem exists_liesOver_height_eq (k K S T : Type u) [Field k] [Field K]
    [CommRing S] [CommRing T] [Algebra k K] [Algebra k S] [Algebra k T] [Algebra K T]
    [Algebra S T] [IsScalarTower k K T] [IsScalarTower k S T] [Algebra.IsPushout k K S T]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime] :
    ∃ (Q : Ideal T) (_ : Q.IsPrime), Q.under S = q ∧ Q.height = q.height ∧
      Cardinal.toENat (Algebra.trdeg k q.ResidueField) =
        Cardinal.toENat (Algebra.trdeg K Q.ResidueField) := by
  obtain ⟨h1, h2⟩ := Algebra.IsPushout.height_fiber_add_height_eq_and_add_trdeg_eq k K S T
  obtain ⟨Q, hQp, hQo, hQ0⟩ := h2 q
  obtain ⟨e1, e2⟩ := h1 q Q
  rw [hQ0, zero_add] at e1 e2
  exact ⟨Q, hQp, (Ideal.LiesOver.over (A := S) (P := Q) (p := q)).symm, e1.symm, e2.symm⟩

/-- The affine case of the statement with `n = 0`, for an arbitrary pushout square of rings. -/
private theorem exists_point_spec_of_isPushout (k K A T : Type u) [Field k] [Field K]
    [CommRing A] [CommRing T] [Algebra k K] [Algebra k A] [Algebra k T] [Algebra K T]
    [Algebra A T] [IsScalarTower k K T] [IsScalarTower k A T] [Algebra.IsPushout k K A T]
    [Algebra.FiniteType k A] (z : Spec (.of A)) :
    letI : Algebra k ((Spec (.of A)).residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
        (Spec (.of A)).Γevaluation z).hom.toAlgebra
    ∃ w : Spec (.of T), Spec.map (CommRingCat.ofHom (algebraMap A T)) w = z ∧
      ringKrullDim ((Spec (.of T)).presheaf.stalk w) =
          ringKrullDim ((Spec (.of A)).presheaf.stalk z) ∧
      letI : Algebra K ((Spec (.of T)).residueField w) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap K T))).appTop ≫
          (Spec (.of T)).Γevaluation w).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg k ((Spec (.of A)).residueField z)) =
        Cardinal.toENat (Algebra.trdeg K ((Spec (.of T)).residueField w)) := by
  have hz := z.isPrime
  obtain ⟨Q, hQp, hunder, hh, htr⟩ := exists_liesOver_height_eq k K A T z.asIdeal
  let w : ↥(Spec (CommRingCat.of T)) := ⟨Q, hQp⟩
  refine ⟨w, PrimeSpectrum.ext hunder, ?_, ?_⟩
  · rw [ringKrullDim_stalk_spec, ringKrullDim_stalk_spec]
    exact congrArg _ hh
  · rw [trdeg_spec_residueField k A, trdeg_spec_residueField K T]
    exact htr

/-- The statement with `n = 0` for the base change of `Spec A` along `K / k`, in the canonical
pullback. -/
private theorem exists_point_canonical_of_isAffine (k K A : Type u) [Field k] [Field K]
    [CommRing A] [Algebra k K] [Algebra k A] [Algebra.FiniteType k A] (z : Spec (.of A)) :
    letI : Algebra k ((Spec (.of A)).residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
        (Spec (.of A)).Γevaluation z).hom.toAlgebra
    ∃ v : ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) v = z ∧
      ringKrullDim ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk v) =
          ringKrullDim ((Spec (.of A)).presheaf.stalk z) ∧
      letI : Algebra K ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop ≫
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Γevaluation v).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg k ((Spec (.of A)).residueField z)) =
        Cardinal.toENat (Algebra.trdeg K
          ((pullback (Spec.map (CommRingCat.ofHom (algebraMap k A)))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v)) := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := k) (A := A) (B := K)
  obtain ⟨w, hwz, hdim, htr⟩ := exists_point_spec_of_isPushout k K A (A ⊗[k] K) z
  refine ⟨(pullbackSpecIso k A K).inv w, ?_, ?_, ?_⟩
  · rw [← hwz, ← Scheme.Hom.comp_apply, pullbackSpecIso_inv_fst' k A K]
  · obtain ⟨hd, -⟩ := stalk_and_trdeg_eq_of_isOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[k] K))))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullbackSpecIso k A K).hom (pullbackSpecIso_hom_snd k A K)
      ((pullbackSpecIso k A K).inv w) w (by simp)
    exact hd.trans hdim
  · obtain ⟨-, ht⟩ := stalk_and_trdeg_eq_of_isOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[k] K))))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullbackSpecIso k A K).hom (pullbackSpecIso_hom_snd k A K)
      ((pullbackSpecIso k A K).inv w) w (by simp)
    rw [ht]
    exact htr

/-- The statement with `n = 0` for an affine source and an arbitrary structure morphism. -/
private theorem exists_point_canonical_of_isAffine' {k K : Type u} [Field k] [Field K]
    [Algebra k K] {A : CommRingCat.{u}} (π : Spec A ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType π] (z : Spec A) :
    letI : Algebra k ((Spec A).residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ (Spec A).Γevaluation z).hom.toAlgebra
    ∃ v : ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) v = z ∧
      ringKrullDim ((pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk v) =
          ringKrullDim ((Spec A).presheaf.stalk z) ∧
      letI : Algebra K
          ((pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop ≫
          (pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Γevaluation v).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg k ((Spec A).residueField z)) =
        Cardinal.toENat (Algebra.trdeg K ((pullback π
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v)) := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective π
  have hft : RingHom.FiniteType ψ.hom :=
    HasRingHomProperty.Spec_iff.mp (show LocallyOfFiniteType (Spec.map ψ) from inferInstance)
  algebraize [ψ.hom]
  exact exists_point_canonical_of_isAffine k K ↥A z

/-- The statement with `n = 0` for the canonical pullback of an arbitrary morphism locally of
finite type to the spectrum of a field. -/
private theorem exists_point_canonical {k K : Type u} [Field k] [Field K] [Algebra k K]
    {F : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π] (z : F) :
    letI : Algebra k (F.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ F.Γevaluation z).hom.toAlgebra
    ∃ v : ↥(pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      pullback.fst π (Spec.map (CommRingCat.ofHom (algebraMap k K))) v = z ∧
      ringKrullDim ((pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk v) =
          ringKrullDim (F.presheaf.stalk z) ∧
      letI : Algebra K
          ((pullback π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop ≫
          (pullback π
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Γevaluation v).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg k (F.residueField z)) =
        Cardinal.toENat (Algebra.trdeg K ((pullback π
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueField v)) := by
  obtain ⟨j, zj, hzj⟩ : ∃ (j : F.affineOpenCover.I₀) (zj : ↥(Spec (F.affineOpenCover.X j))),
      F.affineOpenCover.f j zj = z := F.affineOpenCover.openCover.exists_eq z
  obtain ⟨v', hv', hdim', htr'⟩ :=
    exists_point_canonical_of_isAffine' (K := K) (F.affineOpenCover.f j ≫ π) zj
  obtain ⟨hdimP, htrP, hfst⟩ := stalk_and_trdeg_eq_pullback_map π
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) (F.affineOpenCover.f j) v'
  obtain ⟨hdimF, htrF⟩ := stalk_and_trdeg_eq_of_isOpenImmersion π
    (F.affineOpenCover.f j ≫ π) (F.affineOpenCover.f j) rfl zj z hzj
  exact ⟨_, by rw [hfst, hv', hzj], hdimP.symm.trans (hdim'.trans hdimF),
    by rw [← htrF, ← htrP]; exact htr'⟩

/-- **Stacks Project, Tag 02FY part (3), over a field.** Let `π : F ⟶ Spec k` be locally of
finite type, let `K / k` be a field extension and let `P` be the base change of `F` along it.
Above any point `z` of `F` there is a point `w` of `P` at which the dimension of the local ring
and the transcendence degree of the residue field are unchanged, that is, at which the natural
number of part (2) is `0`. -/
public theorem exists_point_eq_ringKrullDim_stalk_and_trdeg_of_isPullback_over_field
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {F P : Scheme.{u}} (π : F ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType π]
    {p₁ : P ⟶ F} {p₂ : P ⟶ Spec (CommRingCat.of K)}
    (hP : IsPullback p₁ p₂ π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (z : F) :
    letI : Algebra k (F.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appTop ≫ F.Γevaluation z).hom.toAlgebra
    ∃ w : P, p₁ w = z ∧
      ringKrullDim (P.presheaf.stalk w) = ringKrullDim (F.presheaf.stalk z) ∧
      letI : Algebra K (P.residueField w) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ p₂.appTop ≫ P.Γevaluation w).hom.toAlgebra
      Cardinal.toENat (Algebra.trdeg k (F.residueField z)) =
        Cardinal.toENat (Algebra.trdeg K (P.residueField w)) := by
  obtain ⟨v, hv, hdim, htr⟩ := exists_point_canonical (K := K) π z
  obtain ⟨hdimP, htrP⟩ := stalk_and_trdeg_eq_of_isOpenImmersion
    (pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap k K)))) p₂
    hP.isoPullback.hom hP.isoPullback_hom_snd (hP.isoPullback.inv v) v (by simp)
  refine ⟨hP.isoPullback.inv v, ?_, hdimP.trans hdim, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]
    exact hv
  · rw [htrP]
    exact htr

end AlgebraicGeometry

end
