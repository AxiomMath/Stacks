module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.FiniteFieldCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed

/-!
# Vanishing bounds for étale cohomology with coefficients killed by an integer

For a scheme `X`, an integer `n` and `d ∈ WithBot ℕ∞`, `IsTorsionVanishingBound X n d` says that
`H^p_ét(X, 𝓖) = 0` for every abelian sheaf `𝓖` on `X_ét` killed by `n` and every `p > d`. For
`n` a prime power `ℓ^k` this is the bound `cd_ℓ(X) ≤ d` of Travaux de Gabber, Exposé XVIII-A, in
the form used by Stacks 0DC6. This file sets up the notion and its first properties:

* being killed by `n` is the equation `n • 𝟙 𝓖 = 0`, which every additive functor preserves;
* a sheaf killed by a positive `n` is torsion, so a bound for all torsion sheaves
  (`AlgebraicGeometry.Scheme.IsEtaleCohomologyBound`, Stacks 0F0Q) is a bound for the sheaves
  killed by `n`;
* the spectrum of a finite field has the bound `1`, that of a separably closed field the bound
  `0`.

## Main definitions

* `AlgebraicGeometry.Scheme.IsTorsionVanishingBound`: the vanishing above `d` for coefficients
  killed by `n`.

## Main results

* `AlgebraicGeometry.Scheme.forall_nsmul_eq_zero_iff_nsmul_id_eq_zero`: killed by `n` on
  sections is `n • 𝟙 𝓖 = 0`.
* `AlgebraicGeometry.Scheme.IsTorsionVanishingBound.of_isEtaleCohomologyBound`: a bound for all
  torsion sheaves is a bound for the sheaves killed by `n > 0`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_finite`: `cd_n(Spec k) ≤ 1` for a
  finite field `k`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_isSepClosed`: `cd_n(Spec k) ≤ 0` for
  a separably closed field `k`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- `d` bounds the étale cohomology of `X` with coefficients killed by `n`:
`H^p_ét(X, 𝓖) = 0` for every abelian sheaf `𝓖` on `X_ét` killed by `n` and every `p > d`. -/
def IsTorsionVanishingBound (X : Scheme.{u}) (n : ℕ) (d : WithBot ℕ∞) : Prop :=
  ∀ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
    (∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0) →
      ∀ p : ℕ, d < p → Subsingleton (Sheaf.H.{u + 1} G p)

/-- A bound for the cohomology stays a bound when it is enlarged. -/
lemma IsTorsionVanishingBound.mono {X : Scheme.{u}} {n : ℕ} {d d' : WithBot ℕ∞}
    (h : IsTorsionVanishingBound X n d) (hd : d ≤ d') : IsTorsionVanishingBound X n d' :=
  fun G hG p hp ↦ h G hG p (hd.trans_lt hp)

/-- **Killed by `n` on sections is killed by `n` as an object**: every section of an abelian
sheaf `𝓖` on `X_ét` is killed by `n` exactly when `n • 𝟙 𝓖 = 0`. -/
theorem forall_nsmul_eq_zero_iff_nsmul_id_eq_zero {X : Scheme.{u}} {n : ℕ}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0) ↔ n • 𝟙 G = 0 := by
  have h (T : X.Etaleᵒᵖ) (x : ToType (G.obj.obj T)) : ((n • 𝟙 G).hom.app T).hom x = n • x := by
    have h₁ : (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (n • 𝟙 G) =
        n • (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map (𝟙 G) :=
      Functor.map_nsmul _
    simpa using congrArg (fun φ : G.obj ⟶ G.obj => (φ.app T).hom x) h₁
  refine ⟨fun h' => ?_, fun h' T x => ?_⟩
  · ext T x
    exact (h T x).trans (h' T.unop x)
  · rw [← h, h']
    rfl

/-- **Annihilation by `n` is preserved by additive functors.** -/
theorem nsmul_id_obj_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] {n : ℕ} {A : C} (h : n • 𝟙 A = 0) :
    n • 𝟙 (Φ.obj A) = 0 := by
  have := congrArg Φ.map h
  rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at this

/-- **A sheaf killed by a positive integer is torsion.** -/
theorem torsionSheafProperty_of_forall_nsmul_eq_zero {X : Scheme.{u}} {n : ℕ} (hn : 0 < n)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : ∀ (T : X.Etale) (x : G.obj.obj (op T)), n • x = 0) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G :=
  fun T _ ↦ ⟨⊤, X.smallEtaleTopology.top_mem T, fun _ _ _ ↦ ⟨n, hn, hG _ _⟩⟩

/-- **A bound for all torsion sheaves is a bound for the sheaves killed by a positive `n`.** -/
theorem IsTorsionVanishingBound.of_isEtaleCohomologyBound {X : Scheme.{u}} {n : ℕ} (hn : 0 < n)
    {d : ℕ∞} (h : IsEtaleCohomologyBound X d) : IsTorsionVanishingBound X n d :=
  fun G hG p hp ↦ h G (torsionSheafProperty_of_forall_nsmul_eq_zero hn hG) p
    (by exact_mod_cast hp)

/-- **The cohomological dimension bounds the cohomology with coefficients killed by `n > 0`.** -/
theorem isTorsionVanishingBound_etaleCohomologicalDimension (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {n : ℕ} (hn : 0 < n) :
    IsTorsionVanishingBound X n (etaleCohomologicalDimension X) :=
  .of_isEtaleCohomologyBound hn (isEtaleCohomologyBound_etaleCohomologicalDimension X)

/-- **A finite field has `n`-cohomological dimension at most one**, for every positive `n`
(`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_one_of_finite`). -/
theorem isTorsionVanishingBound_spec_of_finite (k : Type u) [Field k] [Finite k] {n : ℕ}
    (hn : 0 < n) : IsTorsionVanishingBound (Spec (.of k)) n 1 :=
  (isTorsionVanishingBound_etaleCohomologicalDimension _ hn).mono
    (by exact_mod_cast etaleCohomologicalDimension_spec_le_one_of_finite k)

/-- **A separably closed field has `n`-cohomological dimension zero**, for every positive `n`
(`AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed`). -/
theorem isTorsionVanishingBound_spec_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    {n : ℕ} (hn : 0 < n) : IsTorsionVanishingBound (Spec (.of k)) n 0 :=
  (isTorsionVanishingBound_etaleCohomologicalDimension _ hn).mono
    (by exact_mod_cast etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k)

end AlgebraicGeometry.Scheme

end
