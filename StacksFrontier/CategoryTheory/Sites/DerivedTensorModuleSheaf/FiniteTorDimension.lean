module

public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Slice
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TorAmplitude

/-!
# Finite and locally finite Tor dimension of complexes of sheaves of modules over a ring

Let `(C, J)` be a site and `Λ` a commutative ring. An object `K` of `D(C, Λ)` *has finite Tor
dimension* if it has Tor amplitude in some interval `[a, b]`, and it *locally has finite Tor
dimension* if every object `U` of `C` has a covering `{Uᵢ → U}` such that each restriction
`K|_{Uᵢ}` to the slice site `C/Uᵢ` has finite Tor dimension (Stacks 08FZ).

Tor amplitude in a fixed set of degrees is local: if a family of objects covers the final object
of the site and the restriction of `K` to each member has Tor amplitude in `S`, then so has `K`.
Indeed `Hⁱ(K ⊗_Λ^L F)` restricts to `Hⁱ(K|_V ⊗_Λ^L F|_V)` on `C/V`, and a sheaf whose restrictions
to a family covering the final object vanish is zero. Consequently, over a site whose final
object is quasi-compact, locally finite Tor dimension is finite Tor dimension.

## Main definitions

* `Stacks.ModuleSheaf.HasFiniteTorDimension`: Tor amplitude in some interval.
* `Stacks.ModuleSheaf.LocallyHasFiniteTorDimension`: finite Tor dimension locally on the site.

## Main results

* `Stacks.ModuleSheaf.isZero_obj_of_mem_of_forall_isZero` and
  `Stacks.ModuleSheaf.isZero_of_coversTop`: vanishing of a sheaf of modules is local.
* `Stacks.ModuleSheaf.hasTorAmplitude_of_coversTop`: Tor amplitude descends along a family
  covering the final object.
* `Stacks.ModuleSheaf.exists_hasTorAmplitude_of_locallyHasFiniteTorDimension`: over a
  quasi-compact final object, locally finite Tor dimension is Tor amplitude in one interval.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t t' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory derivedMonoidal
  derivedSymmetric

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Λ : Type w} [CommRing Λ] [UnivLE.{max u v, w}]
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))]

/-- **Stacks 08FZ (2).** An object `K` of `D(C, Λ)` *has finite Tor dimension* if it has Tor
amplitude in `[a, b]` for some integers `a` and `b`. -/
def HasFiniteTorDimension (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) : Prop :=
  ∃ a b : ℤ, HasTorAmplitude K (Set.Icc a b)

/-- **Stacks 08FZ (3).** An object `K` of `D(C, Λ)` *locally has finite Tor dimension* if every
object `U` of `C` carries a covering family `{Uᵢ → U}` such that the restriction `K|_{Uᵢ}` of `K`
to each slice site `C/Uᵢ` has finite Tor dimension. -/
def LocallyHasFiniteTorDimension
    [∀ V : C, HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))]
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) : Prop :=
  ∀ U : C, ∃ S : Presieve U, Sieve.generate S ∈ J U ∧
    ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
      letI := preservesFiniteLimits_overPullback J Λ V
      letI := preservesFiniteColimits_overPullback J Λ V
      HasFiniteTorDimension ((J.overPullback (ModuleCat.{w} Λ) V).mapDerivedCategory.obj K)

omit [UnivLE.{max u v, w}] [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] in
/-- A sheaf of modules whose sections vanish over the members of a covering sieve of `U` has
vanishing sections over `U`. -/
theorem isZero_obj_of_mem_of_forall_isZero (G : Sheaf J (ModuleCat.{w} Λ)) {U : C}
    {S : Sieve U} (hS : S ∈ J U)
    (h : ∀ ⦃V : C⦄ (f : V ⟶ U), S f → IsZero (G.obj.obj (Opposite.op V))) :
    IsZero (G.obj.obj (Opposite.op U)) := by
  rw [IsZero.iff_id_eq_zero]
  refine ((G.cond (G.obj.obj (Opposite.op U))) S hS).isSeparatedFor.ext fun V f hf => ?_
  exact (h f hf).eq_of_tgt _ _

omit [UnivLE.{max u v, w}] [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} Λ))] in
/-- **Vanishing of a sheaf of modules is local.** Let `W` be a family of objects covering the
final object of the site and suppose that every `W i` maps to an object `V i` over which the
restriction of `G` vanishes. Then `G` vanishes. -/
theorem isZero_of_coversTop {ι : Type*} {W V : ι → C} (hW : J.CoversTop W)
    (g : ∀ i, W i ⟶ V i) (G : Sheaf J (ModuleCat.{w} Λ))
    (h : ∀ i, IsZero ((J.overPullback (ModuleCat.{w} Λ) (V i)).obj G)) : IsZero G := by
  have hobj : ∀ U : C, IsZero (G.obj.obj (Opposite.op U)) := fun U =>
    isZero_obj_of_mem_of_forall_isZero G (hW U) fun U' f ⟨i, ⟨a⟩⟩ =>
      ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (Opposite.op (Over.mk (a ≫ g i)))).map_isZero
        (h i) :)
  rw [IsZero.iff_id_eq_zero]
  ext U : 3
  exact (hobj U.unop).eq_of_src _ _

variable [∀ V : C, HasDerivedCategory.{t'} (Sheaf (J.over V) (ModuleCat.{w} Λ))]

/-- **Tor amplitude is local.** Let `W` be a family of objects covering the final object of the
site, every member of which maps to an object `V i` over which the restriction of `K` has Tor
amplitude in `S`. Then `K` has Tor amplitude in `S`: the restriction of `Hⁱ(K ⊗_Λ^L F)` to `V i`
is `Hⁱ(K|_{V i} ⊗_Λ^L F|_{V i})`, which vanishes for `i ∉ S`. -/
theorem hasTorAmplitude_of_coversTop {ι : Type*} {W V : ι → C} (hW : J.CoversTop W)
    (g : ∀ i, W i ⟶ V i) (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (S : Set ℤ)
    (h : ∀ i,
      letI := preservesFiniteLimits_overPullback J Λ (V i)
      letI := preservesFiniteColimits_overPullback J Λ (V i)
      HasTorAmplitude ((J.overPullback (ModuleCat.{w} Λ) (V i)).mapDerivedCategory.obj K) S) :
    HasTorAmplitude K S := by
  intro F n hn
  refine isZero_of_coversTop hW g _ fun i => ?_
  let := preservesFiniteLimits_overPullback J Λ (V i)
  let := preservesFiniteColimits_overPullback J Λ (V i)
  obtain ⟨e⟩ := nonempty_homology_overPullback_tensor_iso (V i) K
    ((DerivedCategory.singleFunctor _ 0).obj F) 0 n
  refine IsZero.of_iso ?_ e
  refine IsZero.of_iso (h i ((J.overPullback (ModuleCat.{w} Λ) (V i)).obj F) n hn) ?_
  exact (DerivedCategory.homologyFunctor _ n).mapIso
    (Iso.refl _ ⊗ᵢ ((J.overPullback (ModuleCat.{w} Λ) (V i)).mapDerivedCategorySingleFunctor
      0).app F)

/-- **Over a quasi-compact final object, locally finite Tor dimension is Tor amplitude in one
interval.** Suppose that every covering sieve of the final object `U` contains the arrows from a
finite family of objects covering the final object. If `K` locally has finite Tor dimension, then
`K` has Tor amplitude in some interval `[a, b]`. -/
theorem exists_hasTorAmplitude_of_locallyHasFiniteTorDimension {U : C} (hU : IsTerminal U)
    (hfin : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (W : Fin n → C), J.CoversTop W ∧ ∀ i, S (hU.from (W i)))
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) (hK : LocallyHasFiniteTorDimension K) :
    ∃ a b : ℤ, HasTorAmplitude K (Set.Icc a b) := by
  obtain ⟨P, hP, hPK⟩ := hK U
  obtain ⟨n, W, hW, hWP⟩ := hfin _ hP
  choose V h g hg hfac using fun i => hWP i
  choose a b hab using fun i => hPK (g i) (hg i)
  have key (c : Fin n → ℤ) (i : Fin n) : -∑ j, |c j| ≤ c i ∧ c i ≤ ∑ j, |c j| :=
    abs_le.1 (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))
  refine ⟨-∑ i, |a i|, ∑ i, |b i|, hasTorAmplitude_of_coversTop hW h K _ fun i => ?_⟩
  exact (hab i).mono (Set.Icc_subset_Icc (key a i).1 (key b i).2)

end Stacks.ModuleSheaf

end
