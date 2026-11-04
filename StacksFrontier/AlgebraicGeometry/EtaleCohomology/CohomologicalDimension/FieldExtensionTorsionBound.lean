module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtension

/-!
# Vanishing bounds with coefficients killed by `n` along limits, integral maps and fields

This file transports `AlgebraicGeometry.Scheme.IsTorsionVanishingBound` (vanishing of
`H^p_ét(X, 𝓖)` above a bound for the abelian sheaves `𝓖` killed by an integer `n`) along the
reductions used in the proof of [Stacks, Tag 0F0T] and [Stacks, Tag 0DC6]:

* to the vertex of a directed limit of quasi-compact quasi-separated schemes with affine
  transition morphisms (the `n`-killed form of Tag 0F0R);
* backwards along an integral morphism;
* from the finitely generated subalgebras `K[s]` of a `K`-algebra `L` to `L`, and from a field
  `K` to an algebraic extension `L`;
* along a field extension, from the case of transcendence degree at most one to the bound
  `c + trdeg_K(L)` (the tower argument of Tag 0F0T).

The direct image of a sheaf killed by `n` is killed by `n`: its sections are sections of the
original sheaf. So each reduction is the corresponding one for torsion sheaves with the torsion
class replaced by the class of sheaves killed by `n`.

## Main results

* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_of_isLimit_of_isDirected`: the directed
  limit.
* `AlgebraicGeometry.Scheme.IsTorsionVanishingBound.of_isIntegralHom`: integral morphisms.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_forall_adjoin`: from the `K[s]` to
  `L`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_isAlgebraic`: algebraic extensions.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_add_trdeg_of_le_one_add`: the tower
  reduction.

## Implementation notes

For an infinite transcendence degree the bound `c + trdeg_K(L)` is `⊤` unless `c = ⊥`, when it
is `⊥`. Rather than treating `c = ⊥` apart, the tower reduction writes `L` as the directed union
of its finitely generated subfields `K(s)`
(`Stacks.EtaleCohomology.finsetIntermediateFieldIsColimit`), each of finite transcendence degree
at most `trdeg_K(L)`, and passes to the limit.

## References

* [Stacks Project, Tag 0F0T](https://stacks.math.columbia.edu/tag/0F0T)
* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

section IntermediateField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The directed system of the subfields of `L` generated over `K` by the finite subsets of `L`,
as a diagram of commutative rings indexed by `Finset L`. -/
def finsetIntermediateFieldDiagram : Finset L ⥤ CommRingCat.{u} where
  obj s := CommRingCat.of (IntermediateField.adjoin K (s : Set L))
  map {s t} h := CommRingCat.ofHom
    { toFun := fun x => ⟨x.1,
        IntermediateField.adjoin.mono K _ _ (Finset.coe_subset.mpr (leOfHom h)) x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id s := by ext x; rfl
  map_comp f g := by ext x; rfl

/-- The cocone on `finsetIntermediateFieldDiagram` given by the inclusions of the subfields
into `L`. -/
def finsetIntermediateFieldCocone : Cocone (finsetIntermediateFieldDiagram K L) where
  pt := CommRingCat.of L
  ι :=
    { app := fun s => CommRingCat.ofHom (IntermediateField.adjoin K (s : Set L)).val.toRingHom
      naturality := fun s t h => by ext x; rfl }

variable {K L}

/-- Two stages of `finsetIntermediateFieldDiagram` containing the same element of `L` send it to
the same element of the vertex of any cocone. -/
lemma finsetIntermediateFieldCocone_leg_agree (T : Cocone (finsetIntermediateFieldDiagram K L))
    (s t : Finset L) (x : L) (hs : x ∈ IntermediateField.adjoin K (s : Set L))
    (ht : x ∈ IntermediateField.adjoin K (t : Set L)) :
    (T.ι.app s).hom ⟨x, hs⟩ = (T.ι.app t).hom ⟨x, ht⟩ := by
  classical
  have e₁ := congrArg (fun φ => φ.hom ⟨x, hs⟩)
    (T.ι.naturality (homOfLE (Finset.subset_union_left : s ⊆ s ∪ t)))
  have e₂ := congrArg (fun φ => φ.hom ⟨x, ht⟩)
    (T.ι.naturality (homOfLE (Finset.subset_union_right : t ⊆ s ∪ t)))
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at e₁ e₂
  rw [← e₁, ← e₂]
  rfl

/-- The map out of `L` determined by a cocone on `finsetIntermediateFieldDiagram`: an element is
sent through the stage it generates. -/
def finsetIntermediateFieldCoconeDesc (T : Cocone (finsetIntermediateFieldDiagram K L)) :
    L →+* T.pt where
  toFun b := (T.ι.app {b}).hom ⟨b, IntermediateField.subset_adjoin K _ (by simp)⟩
  map_one' := by
    rw [finsetIntermediateFieldCocone_leg_agree T _ ∅ 1 _ (one_mem _)]
    exact map_one (T.ι.app ∅).hom
  map_zero' := by
    rw [finsetIntermediateFieldCocone_leg_agree T _ ∅ 0 _ (zero_mem _)]
    exact map_zero (T.ι.app ∅).hom
  map_mul' a b := by
    classical
    have ha : a ∈ IntermediateField.adjoin K (({a, b} : Finset L) : Set L) :=
      IntermediateField.subset_adjoin K _ (by simp)
    have hb : b ∈ IntermediateField.adjoin K (({a, b} : Finset L) : Set L) :=
      IntermediateField.subset_adjoin K _ (by simp)
    rw [finsetIntermediateFieldCocone_leg_agree T _ {a, b} (a * b) _ (mul_mem ha hb),
      finsetIntermediateFieldCocone_leg_agree T _ {a, b} a _ ha,
      finsetIntermediateFieldCocone_leg_agree T _ {a, b} b _ hb]
    exact map_mul (T.ι.app {a, b}).hom ⟨a, ha⟩ ⟨b, hb⟩
  map_add' a b := by
    classical
    have ha : a ∈ IntermediateField.adjoin K (({a, b} : Finset L) : Set L) :=
      IntermediateField.subset_adjoin K _ (by simp)
    have hb : b ∈ IntermediateField.adjoin K (({a, b} : Finset L) : Set L) :=
      IntermediateField.subset_adjoin K _ (by simp)
    rw [finsetIntermediateFieldCocone_leg_agree T _ {a, b} (a + b) _ (add_mem ha hb),
      finsetIntermediateFieldCocone_leg_agree T _ {a, b} a _ ha,
      finsetIntermediateFieldCocone_leg_agree T _ {a, b} b _ hb]
    exact map_add (T.ι.app {a, b}).hom ⟨a, ha⟩ ⟨b, hb⟩

/-- The inclusions of the subfields generated by the finite subsets exhibit `L` as the colimit
of `finsetIntermediateFieldDiagram`. -/
def finsetIntermediateFieldIsColimit : IsColimit (finsetIntermediateFieldCocone K L) where
  desc T := CommRingCat.ofHom (finsetIntermediateFieldCoconeDesc T)
  fac T s := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨x, hx⟩ := x
    exact finsetIntermediateFieldCocone_leg_agree T _ s x _ hx
  uniq T m hm := by
    refine CommRingCat.hom_ext (RingHom.ext fun (b : L) => ?_)
    have hx : b ∈ IntermediateField.adjoin K (({b} : Finset L) : Set L) :=
      IntermediateField.subset_adjoin K _ (by simp)
    exact congrArg (fun φ => φ.hom ⟨b, hx⟩) (hm ({b} : Finset L))

end IntermediateField

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

section Limit

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] {c : Cone D}

/-- **A vanishing bound with coefficients killed by `n` passes to a directed limit.** Let
`X = lim X_i` be a directed limit of quasi-compact quasi-separated schemes with affine transition
morphisms. If `d` bounds the cohomology of every `X_i` with coefficients killed by `n`, it bounds
that of `X`: the direct image `f_{i,*}𝓖` of a sheaf killed by `n` along the projection
`f_i : X ⟶ X_i` is killed by `n`, and the vanishing at every level transports to `X`
(`subsingleton_sheafH_of_isLimit_of_forall_subsingleton`, Tags 0EYN and 09YQ). -/
theorem isTorsionVanishingBound_of_isLimit_of_isDirected (hc : IsLimit c) {n : ℕ}
    {d : WithBot ℕ∞} (h : ∀ i, IsTorsionVanishingBound (D.obj i) n d) :
    IsTorsionVanishingBound c.pt n d :=
  fun G hG p hp => subsingleton_sheafH_of_isLimit_of_forall_subsingleton D hc G p fun i =>
    h i _ (fun _ x => hG _ x) p hp

end Limit

/-- **A vanishing bound with coefficients killed by `n` pulls back along an integral
morphism.** For `f : X ⟶ Y` integral and `𝓖` an abelian sheaf on `X_ét` killed by `n`,
`H^p(X, 𝓖) = H^p(Y, f_*𝓖)` (`Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv`) and
`f_*𝓖` is killed by `n`. -/
theorem IsTorsionVanishingBound.of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {n : ℕ} {d : WithBot ℕ∞} (h : IsTorsionVanishingBound Y n d) :
    IsTorsionVanishingBound X n d :=
  fun G hG p hp => (sheafHSmallEtalePushforwardAddEquiv f G p).toEquiv.subsingleton_congr.2
    (h _ (fun _ x => hG _ x) p hp)

/-- A vanishing bound passes from the `Spec` of the stages of a directed diagram of commutative
rings to the `Spec` of its colimit. -/
private theorem isTorsionVanishingBound_spec_of_isColimit {J : Type u} [Preorder J]
    [IsDirected J (· ≤ ·)] [Nonempty J] {F : J ⥤ CommRingCat.{u}} {T : Cocone F}
    (hT : IsColimit T) {n : ℕ} {d : WithBot ℕ∞}
    (h : ∀ j, IsTorsionVanishingBound (Spec (F.obj j)) n d) :
    IsTorsionVanishingBound (Spec T.pt) n d := by
  have : ∀ {i j : Jᵒᵖ} (a : i ⟶ j), IsAffineHom ((F.op ⋙ Scheme.Spec).map a) :=
    fun a => inferInstanceAs (IsAffineHom (Spec.map _))
  have : ∀ i : Jᵒᵖ, CompactSpace ((F.op ⋙ Scheme.Spec).obj i) :=
    fun i => inferInstanceAs (CompactSpace (Spec _))
  have : ∀ i : Jᵒᵖ, QuasiSeparatedSpace ((F.op ⋙ Scheme.Spec).obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Spec _))
  exact isTorsionVanishingBound_of_isLimit_of_isDirected (F.op ⋙ Scheme.Spec)
    (c := Scheme.Spec.mapCone T.op) (isLimitOfPreserves Scheme.Spec hT.op) fun j => h j.unop

/-- **A bound on the finitely generated subalgebras is a bound on the algebra.** For a
`K`-algebra `L`, if `d` bounds the cohomology with coefficients killed by `n` of every
`Spec K[s]`, `s` a finite subset of `L`, then it bounds that of `Spec L`: `Spec L` is the
directed limit of the `Spec K[s]` (`Stacks.EtaleCohomology.finsetSubalgebraIsColimit`), with
affine transition morphisms. -/
theorem isTorsionVanishingBound_spec_of_forall_adjoin (K L : Type u) [CommRing K] [CommRing L]
    [Algebra K L] {n : ℕ} {d : WithBot ℕ∞}
    (h : ∀ s : Finset L, IsTorsionVanishingBound (Spec (.of (Algebra.adjoin K (s : Set L)))) n d) :
    IsTorsionVanishingBound (Spec (.of L)) n d := by
  exact isTorsionVanishingBound_spec_of_isColimit
    (finsetSubalgebraIsColimit (A := K) (B := L)) h

/-- **An algebraic extension keeps a vanishing bound with coefficients killed by `n`.** For
`L/K` algebraic, each finitely generated subalgebra `K[s]` of `L` is integral over `K`, so
`Spec K[s] ⟶ Spec K` is integral (`IsTorsionVanishingBound.of_isIntegralHom`), and `Spec L` is
the limit of the `Spec K[s]` (`isTorsionVanishingBound_spec_of_forall_adjoin`). -/
theorem isTorsionVanishingBound_spec_of_isAlgebraic (K L : Type u) [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] {n : ℕ} {d : WithBot ℕ∞}
    (hK : IsTorsionVanishingBound (Spec (.of K)) n d) :
    IsTorsionVanishingBound (Spec (.of L)) n d := by
  refine isTorsionVanishingBound_spec_of_forall_adjoin K L fun s => ?_
  let A := Algebra.adjoin K (s : Set L)
  have : Algebra.IsAlgebraic K A := Algebra.IsAlgebraic.of_injective A.val Subtype.val_injective
  have : Algebra.IsIntegral K A := Algebra.IsAlgebraic.isIntegral
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact hK.of_isIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- **The tower reduction for finite transcendence degree.** Under the hypothesis `h` of
`isTorsionVanishingBound_add_trdeg_of_le_one_add`, a field extension `L/K` with
`trdeg_K(L) ≤ m` finite takes a bound `c` on `Spec K` to the bound `c + m` on `Spec L`: by
induction on `m`, through `K ⊂ K(x) ⊂ L` with `x` transcendental over `K`. -/
theorem isTorsionVanishingBound_add_of_trdeg_le_of_le_one_add {n : ℕ}
    (h : ∀ (K L : Type u) [Field K] [Field L] [Algebra K L], IsUnit (n : K) →
      Algebra.trdeg K L ≤ 1 → ∀ c : WithBot ℕ∞,
        IsTorsionVanishingBound (Spec (.of K)) n c →
          IsTorsionVanishingBound (Spec (.of L)) n (1 + c))
    (m : ℕ) : ∀ (K L : Type u) [Field K] [Field L] [Algebra K L], IsUnit (n : K) →
      (Algebra.trdeg K L).toENat ≤ m → ∀ c : WithBot ℕ∞,
        IsTorsionVanishingBound (Spec (.of K)) n c →
          IsTorsionVanishingBound (Spec (.of L)) n (c + ((m : ℕ∞) : WithBot ℕ∞)) := by
  induction m with
  | zero =>
    intro K L _ _ _ _ hm c hK
    have h0 : Algebra.trdeg K L = 0 := by simpa using hm
    have : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.mp h0
    simpa using isTorsionVanishingBound_spec_of_isAlgebraic K L hK
  | succ m ih =>
    intro K L _ _ _ hn hm c hK
    by_cases halg : Algebra.IsAlgebraic K L
    · refine (isTorsionVanishingBound_spec_of_isAlgebraic K L hK).mono ?_
      exact le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le (m + 1))
    obtain ⟨x, hx⟩ := Algebra.transcendental_def.mp
      (Algebra.transcendental_iff_not_isAlgebraic.mpr halg)
    let M := IntermediateField.adjoin K ({x} : Set L)
    have hM1 : Algebra.trdeg K M ≤ 1 := Algebra.trdeg_adjoin_simple_le_one K L x
    have hMx : Transcendental K (IntermediateField.AdjoinSimple.gen K x) :=
      (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective M L)).mp hx
    have hM0 : 1 ≤ Algebra.trdeg K M :=
      Cardinal.one_le_iff_ne_zero.mpr
        (trdeg_ne_zero_iff.mpr (Algebra.transcendental_def.mpr ⟨_, hMx⟩))
    have htower := trdeg_add_eq K M (A := L)
    have hML : (Algebra.trdeg M L).toENat ≤ m := by
      have h' : (Algebra.trdeg K M).toENat + (Algebra.trdeg M L).toENat ≤ (m : ℕ∞) + 1 := by
        rw [← map_add, htower]; exact_mod_cast hm
      have hM1' : (Algebra.trdeg K M).toENat = 1 := by
        refine le_antisymm ?_ ?_
        · simpa using Cardinal.toENat.monotone' hM1
        · simpa using Cardinal.toENat.monotone' hM0
      rw [hM1', add_comm] at h'
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
    have hnM : IsUnit (n : M) := by
      simpa using hn.map (algebraMap K M)
    have hL := ih M L hnM hML (1 + c) (h K M hn hM1 c hK)
    refine hL.mono (le_of_eq ?_)
    push_cast
    rw [add_comm (1 : WithBot ℕ∞) c, add_assoc, add_comm (1 : WithBot ℕ∞)]

/-- **The tower reduction of Tag 0F0T for coefficients killed by `n`.** Suppose that for every
field extension `L/K` (in the universe `u`) with `n` invertible in `K` and `trdeg_K(L) ≤ 1`, a
bound `c` on the cohomology of `Spec K` with coefficients killed by `n` gives the bound `1 + c`
on `Spec L`. Then for every field extension `L/K` with `n` invertible in `K`, a bound `c` on
`Spec K` gives the bound `c + trdeg_K(L)` on `Spec L`, the transcendence degree read in `ℕ∞`.

For finite transcendence degree this is the tower argument
(`isTorsionVanishingBound_add_of_trdeg_le_of_le_one_add`). In general `L` is the directed union
of its subfields `K(s)` generated by finite subsets `s`
(`Stacks.EtaleCohomology.finsetIntermediateFieldIsColimit`), which are essentially of finite type
over `K` and so of finite transcendence degree at most `trdeg_K(L)`; `Spec L` is the directed limit
of the `Spec K(s)` (`isTorsionVanishingBound_of_isLimit_of_isDirected`). This also covers `c = ⊥`
with infinite transcendence degree, where the bound `c + trdeg_K(L)` is `⊥`. -/
theorem isTorsionVanishingBound_add_trdeg_of_le_one_add {n : ℕ}
    (h : ∀ (K L : Type u) [Field K] [Field L] [Algebra K L], IsUnit (n : K) →
      Algebra.trdeg K L ≤ 1 → ∀ c : WithBot ℕ∞,
        IsTorsionVanishingBound (Spec (.of K)) n c →
          IsTorsionVanishingBound (Spec (.of L)) n (1 + c))
    (K L : Type u) [Field K] [Field L] [Algebra K L] (hn : IsUnit (n : K)) (c : WithBot ℕ∞)
    (hK : IsTorsionVanishingBound (Spec (.of K)) n c) :
    IsTorsionVanishingBound (Spec (.of L)) n
      (c + (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞)) := by
  refine isTorsionVanishingBound_spec_of_isColimit
    (finsetIntermediateFieldIsColimit (K := K) (L := L)) fun s => ?_
  let M := IntermediateField.adjoin K ((s : Finset L) : Set L)
  have : Algebra.EssFiniteType K M :=
    IntermediateField.essFiniteType_iff.mpr ⟨s, rfl⟩
  have hfin : (Algebra.trdeg K M).toENat ≠ ⊤ := by
    rw [Ne, Cardinal.toENat_eq_top, not_le]
    exact trdeg_lt_aleph0 K M
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  have hM := isTorsionVanishingBound_add_of_trdeg_le_of_le_one_add h m K M hn hm.symm.le c hK
  refine hM.mono ?_
  have hle : Algebra.trdeg K M ≤ Algebra.trdeg K L :=
    trdeg_le_of_injective M.val M.val.toRingHom.injective
  have hle' : ((m : ℕ∞) : WithBot ℕ∞) ≤ (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) := by
    rw [hm]
    exact_mod_cast Cardinal.toENat.monotone' hle
  exact add_le_add le_rfl hle'

end AlgebraicGeometry.Scheme

end
