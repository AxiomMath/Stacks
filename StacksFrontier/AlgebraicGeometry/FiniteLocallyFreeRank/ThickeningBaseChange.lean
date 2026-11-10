module

public import Mathlib.RingTheory.LocalProperties.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget

/-!
# The rank of a finite flat morphism is read on a thickening of its target

Let `ψ' : U' ⟶ V'` be a finite flat morphism of schemes and let `i : V ⟶ V'` be a closed
immersion which is surjective, for instance the inclusion of the special fibre of a thickening.
If the base change `ψ : U ⟶ V` of `ψ'` along `i` is finite locally free of rank `d`, then so is
`ψ'`.

The statement is Zariski local on `V'`, so it reduces to `V'` affine, where it is the following
statement about modules. Let `R ⟶ A` be a surjective ring map whose kernel consists of nilpotent
elements and let `M` be a finite flat `R`-module with `A ⊗[R] M` finite locally free of rank `d`.
By Stacks 07ZD it suffices that the `(d - 1)`st Fitting ideal `J` of `M` vanishes and the `d`th
one is the unit ideal. Fitting ideals commute with base change (Stacks 07ZA). The `d`th one
becomes the unit ideal in `A`, so it is the unit ideal, the kernel being nil. The `(d - 1)`st one
becomes zero in `A`, so it consists of nilpotent elements; at a maximal ideal `m` the module
`M_m` is finite flat over a local ring, hence free, so the extension of `J` to `R_m` is either
zero or the unit ideal (Stacks 07ZB), and it cannot be the unit ideal because it consists of
nilpotent elements. So `J` vanishes at every maximal ideal, hence vanishes.

## Main results

* `Module.IsFiniteLocallyFreeOfRank.of_baseChange_of_surjective_of_ker_le_nilradical`: the module
  statement.
* `Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback_of_isClosedImmersion_of_surjective`:
  the scheme statement.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 07ZA](https://stacks.math.columbia.edu/tag/07ZA)
* [Stacks Project, Tag 07ZB](https://stacks.math.columbia.edu/tag/07ZB)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u v w

/-- An ideal contained in the nilradical whose extension to every localization at a maximal
ideal is either zero or the unit ideal is zero. -/
private theorem Ideal.eq_bot_of_le_nilradical_of_localization {R : Type u} [CommRing R]
    {J : Ideal R} (hJ : J ≤ nilradical R)
    (h : ∀ (m : Ideal R) (_ : m.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime m)) J = ⊥ ∨
        Ideal.map (algebraMap R (Localization.AtPrime m)) J = ⊤) :
    J = ⊥ := by
  refine ideal_eq_bot_of_localization' J fun m hm => ?_
  rcases h m hm with h | h
  · exact h
  · exfalso
    have hle : Ideal.map (algebraMap R (Localization.AtPrime m)) J ≤
        nilradical (Localization.AtPrime m) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact mem_nilradical.mpr
        ((mem_nilradical.mp (hJ hx)).map (algebraMap R (Localization.AtPrime m)))
    rw [h, top_le_iff] at hle
    exact not_isNilpotent_one (mem_nilradical.mp ((Ideal.eq_top_iff_one _).mp hle))

/-- **The rank of a finite flat module is read on a nil quotient of the ring.** Let `R ⟶ A` be
surjective with nil kernel and let `M` be a finite flat `R`-module. If `A ⊗[R] M` is finite
locally free of rank `d` over `A`, then `M` is finite locally free of rank `d` over `R`. -/
theorem Module.IsFiniteLocallyFreeOfRank.of_baseChange_of_surjective_of_ker_le_nilradical
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R M] (A : Type w) [CommRing A] [Algebra R A]
    (hsurj : Function.Surjective (algebraMap R A))
    (hker : RingHom.ker (algebraMap R A) ≤ nilradical R) {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank A (A ⊗[R] M) d) :
    Module.IsFiniteLocallyFreeOfRank R M d := by
  obtain ⟨hprev, htop⟩ := (finiteLocallyFreeOfRank_fittingIdeal_tfae
    (R := A) (M := A ⊗[R] M) d).out 1 2 |>.mp h
  have hbc (k : ℕ) : fittingIdeal (R := A) (M := A ⊗[R] M) (k : ℤ) =
      Ideal.map (algebraMap R A) (fittingIdeal (R := R) (M := M) (k : ℤ)) :=
    (fittingIdeal_basic_properties.{u, v, v, w} (R := R) (M := M)).2.2.1 A k
  refine ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := R) (M := M) d).out 2 1).mp
    (And.intro ?_ ?_)
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact fittingIdeal_eq_bot_of_lt_zero (by omega)
    · rw [show (d : ℤ) - 1 = ((d - 1 : ℕ) : ℤ) by omega] at hprev ⊢
      rw [hbc (d - 1), Ideal.map_eq_bot_iff_le_ker] at hprev
      refine Ideal.eq_bot_of_le_nilradical_of_localization (hprev.trans hker) fun m hm => ?_
      let Rm := Localization.AtPrime m
      have : Module.Free Rm (Rm ⊗[R] M) := Module.free_of_flat_of_isLocalRing
      rw [← (fittingIdeal_basic_properties.{u, v, v, u} (R := R) (M := M)).2.2.1 Rm (d - 1),
        fittingIdeal_eq_of_linearEquiv (Module.finBasis Rm (Rm ⊗[R] M)).equivFun,
        fittingIdeal_fin_eq_bot_or_top]
      split_ifs <;> simp
  · rw [hbc d] at htop
    have hsup : fittingIdeal (R := R) (M := M) (d : ℤ) ⊔ RingHom.ker (algebraMap R A) = ⊤ := by
      rw [← Ideal.comap_map_of_surjective' _ hsurj, htop, Ideal.comap_top]
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
    have hunit : IsUnit x := by
      rw [eq_sub_of_add_eq hxy]
      exact (mem_nilradical.mp (hker hy)).isUnit_one_sub
    exact Ideal.eq_top_of_isUnit_mem _ hx hunit

namespace Stacks.Morphisms

/-- The affine case of
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback_of_isClosedImmersion_of_surjective`. -/
private theorem isFiniteLocallyFreeOfRank_of_isPullback_of_isAffine {U U' V V' : Scheme.{u}}
    [IsAffine V'] {j : U ⟶ U'} {ψ : U ⟶ V} {ψ' : U' ⟶ V'} {i : V ⟶ V'}
    (sq : IsPullback j ψ ψ' i) [IsClosedImmersion i] [Surjective i] [IsFinite ψ'] [Flat ψ']
    {d : ℕ} (h : IsFiniteLocallyFreeOfRank ψ d) : IsFiniteLocallyFreeOfRank ψ' d := by
  have : IsAffine V := isAffine_of_isAffineHom i
  have : IsAffine U' := isAffine_of_isAffineHom ψ'
  have : IsAffineHom ψ := h.toIsAffineHom
  have : IsAffine U := isAffine_of_isAffineHom ψ
  have hpush : IsPushout i.appTop ψ'.appTop ψ.appTop j.appTop :=
    (isPushout_appTop_of_isPullback sq).flip
  have hisurj : Function.Surjective i.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hker (x : Γ(V', ⊤)) (hx : i.appTop x = 0) : IsNilpotent x := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
    have hpre : i ⁻¹ᵁ V'.basicOpen x = ⊥ := by
      rw [Scheme.preimage_basicOpen_top, hx, Scheme.basicOpen_zero]
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨z, rfl⟩ := i.surjective y
    have : z ∈ i ⁻¹ᵁ V'.basicOpen x := hy
    rw [hpre] at this
    exact this
  algebraize [i.appTop.hom, ψ'.appTop.hom, ψ.appTop.hom, j.appTop.hom,
    ψ.appTop.hom.comp i.appTop.hom]
  have : IsScalarTower ↑Γ(V', ⊤) ↑Γ(U', ⊤) ↑Γ(U, ⊤) :=
    .of_algebraMap_eq' <| congr($(hpush.1.1).hom)
  have : Algebra.IsPushout ↑Γ(V', ⊤) ↑Γ(V, ⊤) ↑Γ(U', ⊤) ↑Γ(U, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have : Module.Finite ↑Γ(V', ⊤) ↑Γ(U', ⊤) := ψ'.finite_appTop
  have : Module.Flat ↑Γ(V', ⊤) ↑Γ(U', ⊤) := ψ'.flat_appTop
  refine (isFiniteLocallyFreeOfRank_iff_module_of_isAffine ψ' d rfl).mpr ?_
  refine Module.IsFiniteLocallyFreeOfRank.of_baseChange_of_surjective_of_ker_le_nilradical
    ↑Γ(V, ⊤) hisurj (fun x hx => mem_nilradical.mpr (hker x hx)) ?_
  exact ((isFiniteLocallyFreeOfRank_iff_module_of_isAffine ψ d rfl).mp h).of_linearEquiv
    (Algebra.IsPushout.equiv ↑Γ(V', ⊤) ↑Γ(V, ⊤) ↑Γ(U', ⊤) ↑Γ(U, ⊤)).symm.toLinearEquiv

/-- **The rank of a finite flat morphism is read on a thickening of its target.** Let
`ψ' : U' ⟶ V'` be finite and flat and let `i : V ⟶ V'` be a surjective closed immersion. If the
base change `ψ : U ⟶ V` of `ψ'` along `i` is finite locally free of rank `d`, then so is `ψ'`.

The statement is Zariski local on `V'`; over an affine open of `V'` it is
`Module.IsFiniteLocallyFreeOfRank.of_baseChange_of_surjective_of_ker_le_nilradical` for the global
sections. -/
theorem IsFiniteLocallyFreeOfRank.of_isPullback_of_isClosedImmersion_of_surjective
    {U U' V V' : Scheme.{u}} {j : U ⟶ U'} {ψ : U ⟶ V} {ψ' : U' ⟶ V'} {i : V ⟶ V'}
    (sq : IsPullback j ψ ψ' i) [IsClosedImmersion i] [Surjective i] [IsFinite ψ'] [Flat ψ']
    {d : ℕ} (h : IsFiniteLocallyFreeOfRank ψ d) : IsFiniteLocallyFreeOfRank ψ' d := by
  change IsFiniteLocallyFreeOfRank.property d ψ'
  refine IsZariskiLocalAtTarget.of_openCover V'.affineCover fun k => ?_
  let ι := V'.affineCover.f k
  let jk : pullback ψ (pullback.fst i ι) ⟶ pullback ψ' ι :=
    pullback.lift (pullback.fst ψ (pullback.fst i ι) ≫ j)
      (pullback.snd ψ (pullback.fst i ι) ≫ pullback.snd i ι) (by
        rw [Category.assoc, sq.w, ← Category.assoc, pullback.condition, Category.assoc,
          pullback.condition, Category.assoc])
  have hbig : IsPullback (jk ≫ pullback.fst ψ' ι) (pullback.snd ψ (pullback.fst i ι)) ψ'
      (pullback.snd i ι ≫ ι) := by
    rw [pullback.lift_fst, ← pullback.condition]
    exact (IsPullback.of_hasPullback ψ (pullback.fst i ι)).paste_horiz sq
  have hk : IsPullback jk (pullback.snd ψ (pullback.fst i ι)) (pullback.snd ψ' ι)
      (pullback.snd i ι) :=
    hbig.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback ψ' ι)
  exact isFiniteLocallyFreeOfRank_of_isPullback_of_isAffine hk
    (IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback ψ (pullback.fst i ι)))

end Stacks.Morphisms

end
