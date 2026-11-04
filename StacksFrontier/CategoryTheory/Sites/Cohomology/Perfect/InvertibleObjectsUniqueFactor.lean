module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# On a locally ringed site only one factor of a product decomposition survives, locally

Let `(C, O)` be a ringed site and let `O = ∏_{n ∈ ℤ} O_n` be a locally finite direct product
decomposition of its structure sheaf
(`AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition`). If `(C, O)` is a
locally ringed site then every object of `C` has a covering on each member of which at most one
factor `O_n` is nonzero, and over such a member the surviving factor *is* the structure sheaf.

## Main definitions

* `ProductDecomposition.idemSection`: the idempotent section of `O` cutting out the `n`-th factor
  over an object.
* `ProductDecomposition.uniqueFactorSieve`: the sieve of arrows over whose source at most one
  factor is nonzero.

## Main results

* `ProductDecomposition.uniqueFactorSieve_mem`: that sieve is a covering sieve of every object,
  when the site is locally ringed.
* `ProductDecomposition.isIso_over_factorProjection`: over an object on which the other factors
  have no sections, the projection `O ⟶ O_{n₀}` of sheaves of `O`-modules restricts to an
  isomorphism on the slice site.

## Implementation notes

The idempotents are the sections `e_n = ι_n(1)` named by
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation.inclSection`: the section of
`O` whose `n`-th component is `1` and whose other components vanish. Over an object `V` on
which only finitely many factors are nonzero — which is what local finiteness supplies, through
`ProductDecomposition.finiteSupportSieve_mem` — those finitely many `e_n` sum to `1`, because
the two sides have the same components in every factor: in a surviving factor only one summand
contributes, and in a vanishing factor every equation holds. So they generate the unit ideal,
and the locally-ringed condition in the form of Stacks 04ES (2),
`Stacks.Sheaves.LocallyRingedSite.Condition2`, produces a covering of `V` on each member of
which some `e_{n₀}` is invertible. There no other factor has sections: applying the `n`-th
projection to `b · e_{n₀} = 1` gives `0 = 1` in `O_n`, since the `n`-th component of `e_{n₀}`
vanishes for `n ≠ n₀`.

Nothing here needs the first half of `AlgebraicGeometry.RingedSite.IsLocallyRinged`, that `0`
and `1` are nowhere equal; only `LocallyEitherUnit`, which is Stacks 04ES (1), is used.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

namespace ProductDecomposition

variable {X : RingedSite.{u, u, u}} (D : ProductDecomposition X)

/-! ### The idempotent cutting out a factor -/

/-- The section of `O` over an object `V` whose `n`-th component is `1` and whose other
components vanish: the idempotent of `O(V)` cutting out the `n`-th factor of the
decomposition. -/
def idemSection (n : ℤ) (V : X.C) : (X.O.obj.obj (op V) : Type u) :=
  D.presentation.inclSection n (op V) 1

/-- The `n`-th component of the idempotent of the `n`-th factor is `1`. -/
theorem app_idemSection_self (n : ℤ) (V : X.C) :
    (D.presentation.π n).hom.app (op V) (D.idemSection n V) = 1 :=
  D.presentation.app_inclSection_self n (op V) 1

/-- The `m`-th component of the idempotent of the `n`-th factor vanishes for `m ≠ n`. -/
theorem app_idemSection_of_ne {n m : ℤ} (h : m ≠ n) (V : X.C) :
    (D.presentation.π m).hom.app (op V) (D.idemSection n V) = 0 :=
  D.presentation.app_inclSection_of_ne h (op V) 1

/-- **The idempotents of the surviving factors sum to `1`.** Over an object outside a finite set
of indices all of whose complementary factors are trivial, the idempotents indexed by that
finite set add up to the unit section: the two sides have the same component in every factor,
only the matching summand contributing in a surviving factor and every equation holding in a
trivial one. -/
theorem sum_idemSection (V : X.C) (F : Finset ℤ)
    (hF : ∀ n : ℤ, n ∉ F → Subsingleton ((D.factor n).obj.obj (op V))) :
    ∑ n ∈ F, D.idemSection n V = 1 := by
  classical
  refine D.presentation.injective fun m => ?_
  rw [map_sum, map_one]
  by_cases hm : m ∈ F
  · refine (Finset.sum_eq_single_of_mem m hm ?_).trans (D.app_idemSection_self m V)
    exact fun b _ hbm => D.app_idemSection_of_ne (Ne.symm hbm) V
  · exact (hF m hm).elim _ _

/-! ### The sieve on which at most one factor survives -/

/-- The sieve of arrows over whose source at most one factor of the decomposition has nonzero
sections. It is a sieve because triviality of the sections of a sheaf of rings propagates along
the restriction maps. -/
def uniqueFactorSieve (U : X.C) : Sieve U where
  arrows V _ := ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V))
  downward_closed := fun {_ _ _} hf g => ⟨hf.choose, fun n hn =>
    Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le
      (T := Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)) g (hf.choose_spec n hn)⟩

/-- Triviality of the sections of a factor propagates along any arrow `W ⟶ V`. -/
private theorem subsingleton_factor_of_hom {n : ℤ} {V W : X.C} (g : W ⟶ V)
    (h : Subsingleton ((D.factor n).obj.obj (op V))) : Subsingleton ((D.factor n).obj.obj (op W)) :=
  Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le
    (T := Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)) g h

/-- **A covering of an object on each member of which at most one factor survives.** Over an
object `V` outside a finite set of indices all of whose complementary factors are trivial, the
idempotents of that finite set generate the unit ideal; the locally-ringed condition in the form
of Stacks 04ES (2) then covers `V` by objects over which one of them is invertible, and over
such an object the other factors are trivial. -/
theorem exists_mem_forall_subsingleton_of_ne (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (V : X.C) (hfin : {n : ℤ | ¬ Subsingleton ((D.factor n).obj.obj (op V))}.Finite) :
    ∃ S : Sieve V, S ∈ X.J V ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ V), S.arrows g →
      ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op W)) := by
  classical
  have hF : ∀ n : ℤ, n ∉ hfin.toFinset → Subsingleton ((D.factor n).obj.obj (op V)) := by
    intro n hn
    by_contra hcon
    exact hn (hfin.mem_toFinset.mpr hcon)
  rcases Finset.eq_empty_or_nonempty hfin.toFinset with hempty | hne
  · exact ⟨⊤, X.J.top_mem V, fun {W} g _ => ⟨0, fun n _ =>
      D.subsingleton_factor_of_hom g (hF n (by simp [hempty]))⟩⟩
  -- Enumerate the surviving indices and read the idempotents as a unit-ideal family.
  set k := hfin.toFinset.card
  have hkpos : 0 < k := Finset.card_pos.mpr hne
  set ε := hfin.toFinset.equivFin.symm
  set fs : Fin k → Stacks.Sheaves.LocallyRingedSite.sections X.O V :=
    fun i => D.idemSection ((ε i : ℤ)) V
  have hgen : Stacks.Sheaves.LocallyRingedSite.GeneratesUnitIdeal X.O fs := by
    refine ⟨fun _ => 1, ?_⟩
    have h1 : ∑ i : Fin k, (1 : Stacks.Sheaves.LocallyRingedSite.sections X.O V) * fs i
        = ∑ i : Fin k, fs i := Finset.sum_congr rfl fun i _ => one_mul _
    have h2 : ∑ i : Fin k, fs i = ∑ x : hfin.toFinset, D.idemSection (x : ℤ) V :=
      Fintype.sum_equiv ε _ _ fun i => rfl
    rw [h1, h2, Finset.sum_coe_sort hfin.toFinset fun n => D.idemSection n V]
    exact D.sum_idemSection V hfin.toFinset hF
  obtain ⟨S, hS, hprop⟩ :=
    Stacks.Sheaves.LocallyRingedSite.condition1_imp_condition2 X.O hX.2 V k hkpos fs hgen
  refine ⟨S, hS, fun {W} g hg => ?_⟩
  obtain ⟨i, hi⟩ := hprop g hg
  refine ⟨(ε i : ℤ), fun n hn => ?_⟩
  obtain ⟨b, hb⟩ := hi.exists_left_inv
  have hcomp : (D.presentation.π n).hom.app (op W)
      (b * Stacks.Sheaves.LocallyRingedSite.restrict X.O g (fs i))
      = (D.presentation.π n).hom.app (op W) 1 := by rw [hb]
  rw [map_mul, map_one] at hcomp
  have hzero : (D.presentation.π n).hom.app (op W)
      (Stacks.Sheaves.LocallyRingedSite.restrict X.O g (fs i)) = 0 := by
    rw [show Stacks.Sheaves.LocallyRingedSite.restrict X.O g (fs i)
        = X.O.obj.map g.op (D.idemSection ((ε i : ℤ)) V) from rfl,
      D.presentation.app_map n g.op, D.app_idemSection_of_ne hn V, map_zero]
  rw [hzero, mul_zero] at hcomp
  exact subsingleton_of_zero_eq_one hcomp

/-- **On a locally ringed site the sieve of objects over which at most one factor survives is a
covering sieve.** Local finiteness covers every object by objects on which only finitely many
factors survive, and `exists_mem_forall_subsingleton_of_ne` refines each of those. -/
theorem uniqueFactorSieve_mem (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) (U : X.C) :
    D.uniqueFactorSieve U ∈ X.J U := by
  refine X.J.transitive (D.finiteSupportSieve_mem U) _ fun {V} f hf => ?_
  obtain ⟨S, hS, hprop⟩ := D.exists_mem_forall_subsingleton_of_ne hX V hf
  exact X.J.superset_covering (fun W g hg => hprop g hg) hS

/-! ### The surviving factor is the structure sheaf -/

/-- **Where only one factor survives, the structure sheaf *is* that factor.** If every factor
other than the `n₀`-th has no sections over `V`, then over every object `W` of the site lying
over `V` the `n₀`-th component map `O(W) ⟶ O_{n₀}(W)` is bijective: it is injective because the
other components of a section live in trivial rings, and surjective because `inclSection` names
a preimage. -/
theorem bijective_app_of_subsingleton {n₀ : ℤ} {V : X.C}
    (hsub : ∀ n : ℤ, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)))
    {W : X.C} (g : W ⟶ V) :
    Function.Bijective fun s : (X.O.obj.obj (op W) : Type u) =>
      (D.presentation.π n₀).hom.app (op W) s := by
  refine ⟨fun s s' h => D.presentation.injective fun m => ?_, fun a =>
    ⟨D.presentation.inclSection n₀ (op W) a, D.presentation.app_inclSection_self n₀ (op W) a⟩⟩
  obtain rfl | hm := eq_or_ne m n₀
  · exact h
  · exact (D.subsingleton_factor_of_hom g (hsub m hm)).elim _ _

variable [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **On an object where only the `n₀`-th factor survives, that factor module *is* the structure
sheaf.** The morphism of sheaves of `O`-modules
`Stacks.SheafOfModules.RingSheafProductFactor.factorProjection`, whose sections map is the
`n₀`-th component map, becomes an isomorphism after restriction to the slice site over such an
object: it is bijective on the sections over every object of that slice. -/
theorem isIso_over_factorProjection {n₀ : ℤ} {V : X.C}
    (hsub : ∀ n : ℤ, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V))) :
    IsIso ((Stacks.SheafOfModules.RingSheafProductFactor.factorProjection
      D.presentation n₀).over V) := by
  refine Stacks.SheafOfModules.isIso_of_bijective_app _ fun W => ?_
  exact D.bijective_app_of_subsingleton hsub W.unop.hom

end ProductDecomposition

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
