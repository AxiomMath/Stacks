module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVectQuotient
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVect

/-!
# Faithfulness of the comparison of Stacks Tag 0EXC

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal annihilated by `f ^ n`, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. This file proves **the
faithfulness half of Stacks Tag 0EXC**: a morphism of `colim_F Vect(Spec A)` is determined by
its restrictions to the centre `Spec (A ⧸ fA)` and the modification `Spec (A ⧸ J)`.

The input is the Milnor patching statement
`AlgebraicGeometry.vect_pullback_frobeniusPow_map_eq_zero`: a morphism of vector bundles on
`Spec A` which restricts to zero on the centre and on the modification is killed by a high
enough Frobenius twist. On the colimit categories a Frobenius twist is invisible, which is
exactly what turns that statement into faithfulness.

## Main results

* `AlgebraicGeometry.vect_pullback_frobeniusPow_map_eq`: **the Frobenius-twist faithfulness
  input, for a pair of morphisms.** Two morphisms of vector bundles on `Spec A` which agree on
  the centre and on the modification agree after a high enough Frobenius twist.
* `AlgebraicGeometry.eq_of_toCentre_map_eq_of_toModification_map_eq`: **a morphism of
  `colim_F Vect(Spec A)` between objects at a common stage is determined by its restrictions to
  the centre and the modification.**
* `AlgebraicGeometry.injective_toCentre_toModification_map`: **the same for arbitrary objects**,
  as an injectivity statement for the pair of restriction functors.
* `CategoryTheory.EndoColim.exists_map_endoRaise_eq_of_map_map_eq`: the Hom-level content of the
  two theorems above — if the functor induced by `Φ` identifies two morphisms of `colim_F C`
  presented at a common level, then `Φ` identifies the two presenting morphisms of `C` after
  raising them.

## Implementation notes

Every step is exponent bookkeeping around
`CategoryTheory.EndoColim.Hom.of_eq_of_iff`, which says that two presentations present the same
morphism of `colim_F C` exactly when raising both to a common level identifies them. The three
devices which keep the bookkeeping finite are:

* `CategoryTheory.EndoColim.exists_of_common_level`, which raises two arbitrary presentations of
  two morphisms with the same source and target to a *single* level, after which every exponent
  in sight is of the form `n + K + t`;
* `CategoryTheory.endoHomCast_injective` and `CategoryTheory.map_endoRaise_congr`, which strip
  the transports of exponents that raising produces — both are proved by substituting the
  exponent equality, which is possible only because the exponents are universally quantified
  variables, so the two lemmas cannot be replaced by a `rw` at the point of use (the transported
  morphism and its transport live in different Hom-sets, and the rewrite is dependent);
* `CategoryTheory.EndoColim.map_endoRaise_eq_of_map_eq`, which raises a conclusion about `Φ`
  rather than a hypothesis, by induction on the raise amount; the comparison
  `α : F ⋙ Φ ≅ Φ ⋙ F'` enters only through the one-step case.

For the same reason the chains of equalities below are assembled with `Eq.trans` instead of
`rw`: a raise and the transport comparing it to another raise have different types, so no
rewrite can move between them.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe v u u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/-! ### Stripping the transports of exponents -/

section Transport

variable {F : C ⥤ C}

/-- **A transport of exponents is injective.** The two exponent equalities are substituted, after
which the transports disappear. -/
lemma endoHomCast_injective {E G : C} {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    {x y : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G}
    (h : endoHomCast hm hn x = endoHomCast hm hn y) : x = y := by
  subst hm hn
  exact h

/-- **Two raises by equal amounts have the same image under a functor.** The raise amounts are
universally quantified variables, so their equality can be substituted; this is what replaces a
rewrite, which is unavailable because raising by different amounts lands in different
Hom-sets. -/
lemma map_endoRaise_congr (Φ : C ⥤ C') {E G : C} {a : ℕ}
    {x y : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G} {t t' : ℕ} (htt : t = t')
    (h : Φ.map (endoRaise x t) = Φ.map (endoRaise y t)) :
    Φ.map (endoRaise x t') = Φ.map (endoRaise y t') := by
  subst htt
  exact h

namespace EndoColim

/-- **Two morphisms of `colim_F C` with the same source and target are presented at a common
level.** Each is raised to the level `k + l`, where `k` and `l` are the levels at which they are
presented. -/
lemma exists_of_common_level {A B : EndoColim F} (u v : A ⟶ B) :
    ∃ (K : ℕ) (x y : (F.endoIter (B.stage + K)).obj A.obj ⟶
      (F.endoIter (A.stage + K)).obj B.obj), u = Hom.of K x ∧ v = Hom.of K y := by
  obtain ⟨k, x, rfl⟩ := Hom.exists_of u
  obtain ⟨l, y, rfl⟩ := Hom.exists_of v
  exact ⟨k + l, _, _, (Hom.of_raise k x l).symm,
    ((Hom.of_levelCast (endoHomCast (show B.stage + l + k = B.stage + (l + k) by omega)
        (show A.stage + l + k = A.stage + (l + k) by omega) (endoRaise y k))
      (show l + k = k + l by omega)).trans (Hom.of_raise l y k)).symm⟩

end EndoColim

end Transport

/-! ### Raising a conclusion about a functor commuting with the endofunctors -/

namespace EndoColim

section Square

variable {F : C ⥤ C} {F' : C' ⥤ C'} {Φ : C ⥤ C'}

/-- **One application of `F` preserves an identity between images under `Φ`.** Both images are
conjugated into images under `F'` by the comparison `α`. -/
lemma map_endoMap_eq_of_map_eq (α : F ⋙ Φ ≅ Φ ⋙ F') {W₁ W₂ : C} {x y : W₁ ⟶ W₂}
    (h : Φ.map x = Φ.map y) :
    Φ.map (F.map x) = Φ.map (F.map y) := by
  have hx : Φ.map (F.map x) = α.hom.app W₁ ≫ F'.map (Φ.map x) ≫ α.inv.app W₂ :=
    (NatIso.hom_app_comp_map_comp_inv_app α x).symm
  have hy : Φ.map (F.map y) = α.hom.app W₁ ≫ F'.map (Φ.map y) ≫ α.inv.app W₂ :=
    (NatIso.hom_app_comp_map_comp_inv_app α y).symm
  rw [hx, hy, h]

/-- **Raising preserves an identity between images under `Φ`.** Raising by `s` is applying `F` to
the morphism `s` times, and each application is `map_endoMap_eq_of_map_eq`. -/
lemma map_endoRaise_eq_of_map_eq (α : F ⋙ Φ ≅ Φ ⋙ F') {a : ℕ} {E G : C}
    {x y : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G} {t : ℕ}
    (h : Φ.map (endoRaise x t) = Φ.map (endoRaise y t)) (s : ℕ) :
    Φ.map (endoRaise x (t + s)) = Φ.map (endoRaise y (t + s)) := by
  induction s with
  | zero => exact h
  | succ s ih => exact map_endoMap_eq_of_map_eq α ih

/-- **The induced functor `colim_F C ⥤ colim_{F'} C'` identifies two morphisms presented at a
common level only if `Φ` identifies the two presenting morphisms of `C` after a raise.** This is
the Hom-level content of the faithfulness statements below: by
`CategoryTheory.EndoColim.map_map_of` the induced functor presents the image at the same level by
the image of the presenting morphism under `Φ`, conjugated by the iterated comparison, so
`CategoryTheory.EndoColim.Hom.of_eq_of_iff` turns the hypothesis into an identity of those
conjugates after a raise, and the conjugation cancels. -/
lemma exists_map_endoRaise_eq_of_map_map_eq (α : F ⋙ Φ ≅ Φ ⋙ F') (n K : ℕ) {E G : C}
    (x y : (F.endoIter (n + K)).obj E ⟶ (F.endoIter (n + K)).obj G)
    (h : (map F F' Φ α).map (Hom.of K x : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) =
      (map F F' Φ α).map (Hom.of K y : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩)) :
    ∃ t : ℕ, Φ.map (endoRaise x t) = Φ.map (endoRaise y t) := by
  rw [map_map_of, map_map_of] at h
  obtain ⟨j, i, hji, he⟩ := (Hom.of_eq_of_iff _ _).mp h
  have hji' : K + j = K + i := hji
  obtain rfl : j = i := by omega
  refine ⟨j, ?_⟩
  have he' : endoRaise (transportHom F F' Φ α (n + K) x) j =
      endoRaise (transportHom F F' Φ α (n + K) y) j := endoHomCast_injective _ _ he
  rw [endoRaise_transportHom, endoRaise_transportHom] at he'
  have he'' : (squareIter F F' Φ α (n + K + j) E).hom ≫ Φ.map (endoRaise x j) ≫
        (squareIter F F' Φ α (n + K + j) G).inv =
      (squareIter F F' Φ α (n + K + j) E).hom ≫ Φ.map (endoRaise y j) ≫
        (squareIter F F' Φ α (n + K + j) G).inv := he'
  exact (comp_comp_eq_comp_comp_iff _ _ _ _).mp he''

/-- Once `Φ` identifies two presenting morphisms after a raise, it identifies them after every
larger raise. -/
private theorem exists_forall_map_endoRaise_eq_of_map_map_eq (α : F ⋙ Φ ≅ Φ ⋙ F') (n K : ℕ)
    {E G : C} (x y : (F.endoIter (n + K)).obj E ⟶ (F.endoIter (n + K)).obj G)
    (h : (map F F' Φ α).map (Hom.of K x : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩) =
      (map F F' Φ α).map (Hom.of K y : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩)) :
    ∃ t : ℕ, ∀ s, t ≤ s → Φ.map (endoRaise x s) = Φ.map (endoRaise y s) := by
  obtain ⟨t, ht⟩ := exists_map_endoRaise_eq_of_map_map_eq α n K x y h
  refine ⟨t, fun s hs => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact map_endoRaise_eq_of_map_eq α ht d

end Square

end EndoColim

end CategoryTheory

namespace AlgebraicGeometry

/-! ### The Frobenius-twist faithfulness input, for a pair of morphisms -/

/-- **Two morphisms of vector bundles on `Spec A` which agree on `Spec (A ⧸ J)` and on
`Spec (A ⧸ fA)` agree after a high enough Frobenius twist.** Here `f ^ n` annihilates `J`, the
prime `p` vanishes in `A` and `n + 1 ≤ p ^ N`. This is
`AlgebraicGeometry.vect_pullback_frobeniusPow_map_eq_zero` applied to the difference of the two
morphisms, which is formed on the underlying linear maps after presenting both by finite
projective modules with `AlgebraicGeometry.exists_tildeVect_presentation`. -/
theorem vect_pullback_frobeniusPow_map_eq (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (n : ℕ) (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    (N : ℕ) (hN : n + 1 ≤ p ^ N) {M₀ N₀ : (Spec (CommRingCat.of A)).Vect} (h h' : M₀ ⟶ N₀)
    (hJ : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map h =
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map h')
    (hf : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {f}))))).map h =
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {f}))))).map h') :
    (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N)))).map h =
    (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N)))).map h' := by
  obtain ⟨L, L', e, e', hpres⟩ := exists_tildeVect_presentation (CommRingCat.of A) M₀ N₀
  obtain ⟨ψ, hψ⟩ := hpres h
  obtain ⟨ψ', hψ'⟩ := hpres h'
  let χ : L ⟶ L' := ObjectProperty.homMk (ModuleCat.ofHom (ψ.hom.hom - ψ'.hom.hom))
  have hχ : χ.hom.hom = ψ.hom.hom - ψ'.hom.hom := rfl
  have hbc : ∀ I : Ideal A,
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map h =
        (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map h' →
      LinearMap.baseChange (A ⧸ I) χ.hom.hom = 0 := by
    intro I hI
    rw [hχ, LinearMap.baseChange_sub, sub_eq_zero]
    refine (tildeVect_map_pullback_ofHom_eq_iff_baseChange (Ideal.Quotient.mk I) ψ ψ').mp ?_
    refine (Functor.map_comp_comp_eq_map_comp_comp_iff _ e.inv e'.hom _ _).mp ?_
    rwa [← hψ, ← hψ']
  have key := vect_pullback_frobeniusPow_map_eq_zero A f J n hann p hp N hN
    ((tildeVect (CommRingCat.of A)).map χ)
    ((tildeVect_map_pullback_ofHom_eq_zero_iff_baseChange (Ideal.Quotient.mk J) χ).mpr (hbc J hJ))
    ((tildeVect_map_pullback_ofHom_eq_zero_iff_baseChange
      (Ideal.Quotient.mk (Ideal.span {f})) χ).mpr (hbc _ hf))
  let _ : Algebra A A := (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N).toAlgebra
  have hfinal : LinearMap.baseChange A ψ.hom.hom = LinearMap.baseChange A ψ'.hom.hom := by
    rw [← sub_eq_zero, ← LinearMap.baseChange_sub, ← hχ]
    exact (tildeVect_map_pullback_ofHom_eq_zero_iff_baseChange
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N) χ).mp key
  rw [hψ, hψ']
  exact (Functor.map_comp_comp_eq_map_comp_comp_iff _ e.inv e'.hom _ _).mpr
    ((tildeVect_map_pullback_ofHom_eq_iff_baseChange
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N) ψ ψ').mpr hfinal)

/-- **Two morphisms of vector bundles on `Spec A` which agree after restriction along the
`p ^ N`-power map of `A` agree after being raised `N` times.** Raising `N` times is applying the
`N`-fold Frobenius pullback, which is that restriction by
`AlgebraicGeometry.frobeniusPullbackIterSpecIso`. -/
theorem endoRaise_eq_of_vect_pullback_frobeniusPow_map_eq (A : Type u) [CommRing A] (p : ℕ)
    [Fact p.Prime] (hp : (p : A) = 0) (N : ℕ) {E G : (Spec (CommRingCat.of A)).Vect} {a : ℕ}
    {x y : ((frobeniusPullback (Spec (CommRingCat.of A)) p
          (isInCharacteristic_spec A p hp)).endoIter a).obj E ⟶
      ((frobeniusPullback (Spec (CommRingCat.of A)) p
        (isInCharacteristic_spec A p hp)).endoIter a).obj G}
    (h : (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N)))).map x =
      (Scheme.Vect.pullback (Spec.map (CommRingCat.ofHom
        (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N)))).map y) :
    endoRaise x N = endoRaise y N := by
  have hiter : ((frobeniusPullback (Spec (CommRingCat.of A)) p
        (isInCharacteristic_spec A p hp)).endoIter N).map x =
      ((frobeniusPullback (Spec (CommRingCat.of A)) p
        (isInCharacteristic_spec A p hp)).endoIter N).map y :=
    (NatIso.map_eq_map_iff (frobeniusPullbackIterSpecIso A p hp N) x y).mpr h
  rw [EndoColim.endoRaise_eq_eqToHom_endoIter_map _ x N
      (EndoColim.endoIter_obj_endoIter_obj_of_eq _ rfl E).symm
      (EndoColim.endoIter_obj_endoIter_obj_of_eq _ rfl G),
    EndoColim.endoRaise_eq_eqToHom_endoIter_map _ y N
      (EndoColim.endoIter_obj_endoIter_obj_of_eq _ rfl E).symm
      (EndoColim.endoIter_obj_endoIter_obj_of_eq _ rfl G), hiter]

/-! ### Faithfulness on the colimit categories -/

/-- **A morphism of `colim_F Vect(Spec A)` is determined by its restrictions to the centre and
the modification of the almost blowup square of Stacks Example 0EVG.** -/
theorem eq_of_toCentre_map_eq_of_toModification_map_eq
    (A : Type u) [CommRing A] (f : A) (J : Ideal A) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0)
    {E G : (Spec (CommRingCat.of A)).Vect} {m : ℕ}
    (u v : (⟨E, m⟩ : OneGeneratorSquare.colimVectBase A p hp) ⟶ ⟨G, m⟩)
    (hc : (OneGeneratorSquare.toCentre A f p hp).map u =
      (OneGeneratorSquare.toCentre A f p hp).map v)
    (hm : (OneGeneratorSquare.toModification A J p hp).map u =
      (OneGeneratorSquare.toModification A J p hp).map v) :
    u = v := by
  obtain ⟨K, x, y, rfl, rfl⟩ := EndoColim.exists_of_common_level u v
  obtain ⟨tc, hc'⟩ := EndoColim.exists_forall_map_endoRaise_eq_of_map_map_eq
    (frobeniusVectPullbackIso (Spec.map (OneGeneratorSquare.toCtr A f)) p
      (OneGeneratorSquare.charCtr A f p hp) (OneGeneratorSquare.charBase A p hp))
    m K x y hc
  obtain ⟨tm, hm'⟩ := EndoColim.exists_forall_map_endoRaise_eq_of_map_map_eq
    (frobeniusVectPullbackIso (Spec.map (OneGeneratorSquare.toMod A J)) p
      (OneGeneratorSquare.charMod A J p hp) (OneGeneratorSquare.charBase A p hp))
    m K x y hm
  have hfrob := vect_pullback_frobeniusPow_map_eq A f J n hann p hp (n + 1)
    (Nat.lt_pow_self (Fact.out : Nat.Prime p).one_lt).le
    (endoRaise x (tc + tm)) (endoRaise y (tc + tm)) (hm' _ (by omega)) (hc' _ (by omega))
  have hraise : endoRaise (endoRaise x (tc + tm)) (n + 1) =
      endoRaise (endoRaise y (tc + tm)) (n + 1) :=
    endoRaise_eq_of_vect_pullback_frobeniusPow_map_eq A p hp (n + 1) hfrob
  exact (EndoColim.Hom.of_eq_of_iff x y).mpr
    (EndoColim.HomRep.agree_of_endoRaise_eq (tc + tm + (n + 1))
      (endoHomCast_injective _ _
        (((endoRaise_endoRaise x (tc + tm) (n + 1)).symm.trans hraise).trans
          (endoRaise_endoRaise y (tc + tm) (n + 1)))))

/-- **The pair of restrictions to the centre and to the modification is faithful**: on the
Hom-sets of `colim_F Vect(Spec A)` between arbitrary objects, a morphism is determined by the
pair of its images. Both objects are moved to a common stage by
`CategoryTheory.EndoColim.objShiftIso`, where
`AlgebraicGeometry.eq_of_toCentre_map_eq_of_toModification_map_eq` applies. -/
theorem injective_toCentre_toModification_map
    (R : Type u) [CommRing R] (f : R) (J : Ideal R) (n : ℕ)
    (hann : ∀ x ∈ J, f ^ n * x = 0) (p : ℕ) [Fact p.Prime] (hp : (p : R) = 0)
    (X Y : OneGeneratorSquare.colimVectBase R p hp) :
    Function.Injective (fun u : X ⟶ Y ↦
      ((OneGeneratorSquare.toCentre R f p hp).map u,
        (OneGeneratorSquare.toModification R J p hp).map u)) := by
  obtain ⟨E, a⟩ := X
  obtain ⟨G, b⟩ := Y
  intro u v huv
  simp only [Prod.mk.injEq] at huv
  obtain ⟨hc, hm⟩ := huv
  set Fr := frobeniusPullback (Spec (CommRingCat.of R)) p (OneGeneratorSquare.charBase R p hp)
  have e₁ := EndoColim.objShiftIso Fr a b E
  have e₂ := EndoColim.stageCastIso Fr ((Fr.endoIter a).obj G) (Nat.add_comm a b) ≪≫
    EndoColim.objShiftIso Fr b a G
  exact (comp_comp_eq_comp_comp_iff e₁.hom e₂.inv u v).mp
    (eq_of_toCentre_map_eq_of_toModification_map_eq R f J n hann p hp
      (e₁.hom ≫ u ≫ e₂.inv) (e₁.hom ≫ v ≫ e₂.inv)
      (by simp only [Functor.map_comp, hc]) (by simp only [Functor.map_comp, hm]))

end AlgebraicGeometry

end
