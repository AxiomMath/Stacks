module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.NeighbourhoodIdeal

/-!
# The infinitesimal neighbourhoods of the reduction of a formal algebraic space

Let `W` be an fppf sheaf with a reduction `i : W_red ⟶ W`. The `k`-th infinitesimal neighbourhood
`W_k ⊆ W` of `W_red` is the subfunctor of sections `t` such that, over every affine object `V`
mapping to the base of `t`, the `(k+1)`st power of the ideal of `V ×_W W_red ⟶ V` vanishes. This
file shows that `W_k` is a subsheaf of `W`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.reductionNeighbourhood`: the subfunctor `W_k`.

## Main results

* `AlgebraicGeometry.FormalSpace.mem_reductionNeighbourhood_iff`: over an affine object,
  `t ∈ W_k` iff `K(t)^(k+1) = 0`.
* `AlgebraicGeometry.FormalSpace.isSheaf_reductionNeighbourhood`: `W_k` is a subsheaf.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalRing

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A sieve on `T` containing every member of a covering sieve with affine source is covering. -/
theorem mem_topology_of_affine {T : BigFppfOver B S hS} {R P : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (h : ∀ ⦃V : BigFppfOver B S hS⦄ (g : V ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) → R g → P g) :
    P ∈ BigFppfOver.topology B S hS T := by
  refine (BigFppfOver.topology B S hS).transitive hR P fun V g hg => ?_
  obtain ⟨ι, U, kk, haff, -, hmem⟩ := exists_affineOpenCover_mem V
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hmem
  rintro V' _ ⟨V'', l, _, ⟨j⟩, rfl⟩
  show P ((l ≫ kk j) ≫ g)
  rw [Category.assoc]
  exact P.downward_closed (h (kk j ≫ g) (haff j) (R.downward_closed hg (kk j))) l

/-- **An ideal of an affine object killed by the affine members of a covering sieve
vanishes.** -/
theorem eq_bot_of_forall_le_ker {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {R : Sieve V}
    (hR : R ∈ BigFppfOver.topology B S hS V)
    (h : ∀ ⦃V' : BigFppfOver B S hS⦄ (g : V' ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V') → R g →
        K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map g).appTop.hom) : K = ⊥ := by
  let Jt := BigFppfOver.topology B S hS
  have : Jt.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨T₀, h₀, hci, hker⟩ := exists_siteHom_ker_appTop_eq V K
  have : Mono h₀ := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  let P := Subfunctor.range (yoneda.map h₀)
  have hF : Presieve.IsSheaf Jt (yoneda.obj V) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hP : Presieve.IsSheaf Jt P.toFunctor :=
    (isSheaf_iff_isSheaf_of_type Jt _).1 <|
      (Presheaf.isSheaf_of_iso_iff (asIso (Subfunctor.toRange (yoneda.map h₀)))).1 <|
        (isSheaf_iff_isSheaf_of_type Jt _).2
          (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj T₀))
  have hmem : P.sieveOfSection (𝟙 V) ∈ Jt V := by
    refine mem_topology_of_affine hR fun V' g hV' hg => ?_
    obtain ⟨l, hl⟩ := (Scheme.exists_factor_iff_ker_appTop_le
      ((BigFppfOver.toScheme B S hS).map h₀) ((BigFppfOver.toScheme B S hS).map g)).2
      (hker ▸ h g hV' hg)
    obtain ⟨l₀, hl₀⟩ := exists_siteHom_of_toScheme_comp_eq h₀ g l hl
    exact ⟨l₀, hl₀.trans (Category.comp_id g).symm⟩
  obtain ⟨s, hs⟩ := (P.isSheaf_iff hF).1 hP (op V) (𝟙 V) hmem
  change s ≫ h₀ = 𝟙 V at hs
  rw [← hker, eq_bot_iff]
  intro ξ hξ
  have := congrArg (fun φ => ((BigFppfOver.toScheme B S hS).map φ).appTop ξ) hs
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    RingHom.mem_ker.1 hξ, map_zero, CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop,
    CommRingCat.hom_id, RingHom.id_apply] at this
  exact this.symm

variable {W Wred : FppfSheaf B S hS} (i : Wred ⟶ W)

/-- **The `k`-th infinitesimal neighbourhood `W_k` of `W_red` in `W`**: the sections `t` such that
over every affine object `V` mapping to the base of `t` the `(k+1)`st power of the ideal of
`V ×_W W_red ⟶ V` vanishes. -/
def reductionNeighbourhood (k : ℕ) : Subfunctor W.obj where
  obj T := {t | ∀ (V : BigFppfOver B S hS) (h : V ⟶ T.unop),
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ K, IsReductionIdeal i (W.obj.map h.op t) K → K ^ (k + 1) = ⊥}
  map {T T'} g t ht V h hV K hK := by
    refine ht V (h ≫ g.unop) hV K ?_
    rwa [op_comp, FunctorToTypes.map_comp_apply]

variable {i}

/-- **Membership in `W_k` over an affine object**: `t ∈ W_k(T)` iff `K(t)^(k+1) = 0`. -/
theorem mem_reductionNeighbourhood_iff (k : ℕ) {T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] {t : W.obj.obj (op T)}
    {K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (hK : IsReductionIdeal i t K) :
    t ∈ (reductionNeighbourhood i k).obj (op T) ↔ K ^ (k + 1) = ⊥ := by
  refine ⟨fun ht => ht T (𝟙 T) inferInstance K (by rwa [op_id, FunctorToTypes.map_id_apply]),
    fun hk V h hV K' hK' => ?_⟩
  rw [hK'.unique (hK.map h), ← Ideal.map_pow, hk, Ideal.map_bot]

/-- **`W_k` is a subsheaf of `W`.** -/
theorem isSheaf_reductionNeighbourhood (k : ℕ) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (reductionNeighbourhood i k).toFunctor := by
  let Jt := BigFppfOver.topology B S hS
  refine ((reductionNeighbourhood i k).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type Jt _).1 W.property)).2 fun T t ht V h hV K hK => ?_
  refine eq_bot_of_forall_le_ker _ (Jt.pullback_stable h ht) fun V' g hV' hg => ?_
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  refine (mem_reductionNeighbourhood_iff k (hK.map g)).1 ?_
  change W.obj.map (g ≫ h).op t ∈ _ at hg
  rwa [op_comp, FunctorToTypes.map_comp_apply] at hg

end AlgebraicGeometry.FormalSpace

end
