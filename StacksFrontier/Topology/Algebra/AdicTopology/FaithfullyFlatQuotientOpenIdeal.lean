module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Ideal
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatModWeakIdeal

/-!
# Faithful flatness of the quotients of a ring map by the closures of extended ideals

Let `φ : A → C` be a homomorphism of commutative rings with `C` a topological ring, and for an
ideal `I` of `A` write `K(I)` for the closure of `I C` in `C`, so that `φ` induces a
homomorphism `A ⧸ I → C ⧸ K(I)`. If that homomorphism is faithfully flat for one ideal `I₀`
whose `K(I₀)` is open, then it is faithfully flat for every ideal `I` containing `I₀`.

The reason is that `A ⧸ I → C ⧸ K(I)` is the base change of `A ⧸ I₀ → C ⧸ K(I₀)` along
`A ⧸ I₀ → A ⧸ I`. Writing `J` for the image of `I` in `A ⧸ I₀`, the two double quotients
`(A ⧸ I₀) ⧸ J` and `(C ⧸ K(I₀)) ⧸ J (C ⧸ K(I₀))` are `A ⧸ I` and `C ⧸ K(I)`, and faithful
flatness passes to the quotient of a faithfully flat map by an ideal of its source, which is
`RingHom.faithfullyFlat_quotientMap`.

The only topology in the argument is the identification of the second double quotient: `K(I)` is
the closure of `I C`, while the double quotient computes `I C + K(I₀)`. The closure is contained
in the sum because `K(I₀)` is open, so `I C + K(I₀)` is an ideal containing an open ideal, hence
open, hence closed. That containment is all that is used, and the purely algebraic step is
isolated as a statement about two ideals of `C` with `K ≤ I C + K₀`.

## Main results

* `RingHom.faithfullyFlat_quotientMap_of_le_sup`: the algebraic step, for ideals `K₀ ≤ K` of `C`
  with `K` inside the sum of `I C` and `K₀`.
* `RingHom.faithfullyFlat_quotientMap_closure_of_le`: faithful flatness of `A ⧸ I → C ⧸ K(I)`
  for every ideal `I` above one for which it is known and whose extended closure is open.

## Implementation notes

The quotient maps are spelled `Ideal.quotientMap (Ideal.closure (I.map φ)) φ h`, which is the
shape the consumers of this file use. The two identifications of double quotients are built by
hand out of `Ideal.Quotient.lift`, with bijectivity read off a two-sided inverse, rather than
through a double-quotient equivalence for ideals, which Mathlib does not carry.
-/

@[expose] public section

universe u

namespace RingHom

variable {A C : Type u} [CommRing A] [CommRing C]

/-- A map `f` out of a quotient `P` of `R` is bijective if it has a left inverse on the image of
`R` and `f ∘ m` is surjective. -/
private theorem bijective_of_leftInverse_comp {R P Q : Type*} (m : R → P)
    (hm : Function.Surjective m) (f : P → Q) (g : Q → P) (hgf : ∀ r, g (f (m r)) = m r)
    (hfm : Function.Surjective (f ∘ m)) : Function.Bijective f := by
  refine ⟨Function.LeftInverse.injective (g := g) fun x ↦ ?_, hfm.of_comp⟩
  obtain ⟨r, rfl⟩ := hm x
  exact hgf r

/-- **Faithful flatness of a quotient map rises with the ideal, when the target ideal is
captured by a sum.** Let `φ : A → C` be a ring homomorphism, let `I₀ ≤ I` be ideals of `A` and
let `K₀ ≤ K` be ideals of `C` with `φ(I₀) ⊆ K₀`, with `φ(I) ⊆ K`, and with `K` contained in the
sum of `I C` and `K₀`. If `A ⧸ I₀ → C ⧸ K₀` is faithfully flat then so is `A ⧸ I → C ⧸ K`.

Writing `J` for the image of `I` in `A ⧸ I₀`, the map `A ⧸ I → C ⧸ K` is, up to the two
identifications `A ⧸ I = (A ⧸ I₀) ⧸ J` and `C ⧸ K = (C ⧸ K₀) ⧸ J (C ⧸ K₀)`, the quotient of
`A ⧸ I₀ → C ⧸ K₀` by `J`; the hypothesis `K ≤ I C + K₀` is what makes the second
identification surjective. Faithful flatness of such a quotient is
`RingHom.faithfullyFlat_quotientMap`. -/
public theorem faithfullyFlat_quotientMap_of_le_sup (φ : A →+* C) {I₀ I : Ideal A}
    {K₀ K : Ideal C} (hle : I₀ ≤ I) (hK₀K : K₀ ≤ K)
    (h₀ : I₀ ≤ Ideal.comap φ K₀) (h : I ≤ Ideal.comap φ K)
    (hKsub : K ≤ I.map φ ⊔ K₀)
    (hff : (Ideal.quotientMap K₀ φ h₀).FaithfullyFlat) :
    (Ideal.quotientMap K φ h).FaithfullyFlat := by
  set ψ : A ⧸ I₀ →+* C ⧸ K₀ := Ideal.quotientMap K₀ φ h₀ with hψdef
  set J : Ideal (A ⧸ I₀) := I.map (Ideal.Quotient.mk I₀) with hJdef
  have hψmk (a : A) : ψ (Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk K₀ (φ a) := rfl
  -- the base change of `ψ` along `A ⧸ I₀ → (A ⧸ I₀) ⧸ J`
  have hbase : (Ideal.quotientMap (J.map ψ) ψ Ideal.le_comap_map).FaithfullyFlat :=
    RingHom.faithfullyFlat_quotientMap ψ hff J
  -- `A ⧸ I = (A ⧸ I₀) ⧸ J`
  have hαzero : ∀ a ∈ I, ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I₀)) a = 0 :=
    fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  set α : A ⧸ I →+* (A ⧸ I₀) ⧸ J :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I₀)) hαzero with hαdef
  have hJker : J ≤ RingHom.ker (Ideal.Quotient.factor hle) := by
    rw [hJdef]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  set α' : (A ⧸ I₀) ⧸ J →+* A ⧸ I :=
    Ideal.Quotient.lift J (Ideal.Quotient.factor hle) (fun _ hy ↦ hJker hy) with hα'def
  have hαbij : Function.Bijective α :=
    bijective_of_leftInverse_comp (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective α α'
      (fun _ ↦ rfl) (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective)
  -- `C ⧸ K = (C ⧸ K₀) ⧸ J (C ⧸ K₀)`
  have hβzero : ∀ y ∈ J.map ψ, (Ideal.Quotient.factor hK₀K) y = 0 := by
    have hsub : J.map ψ ≤ RingHom.ker (Ideal.Quotient.factor hK₀K) := by
      rw [hJdef, Ideal.map_map]
      refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
      simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
        hψmk, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h ha)
    exact fun _ hy ↦ hsub hy
  set β : (C ⧸ K₀) ⧸ (J.map ψ) →+* C ⧸ K :=
    Ideal.Quotient.lift (J.map ψ) (Ideal.Quotient.factor hK₀K) hβzero with hβdef
  have hβ'zero : ∀ c ∈ K,
      ((Ideal.Quotient.mk (J.map ψ)).comp (Ideal.Quotient.mk K₀)) c = 0 := by
    have hsub : K ≤ Ideal.comap (Ideal.Quotient.mk K₀) (J.map ψ) := by
      refine hKsub.trans (sup_le ?_ ?_)
      · refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
        simp only [Ideal.mem_comap, ← hψmk]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
      · intro c hc
        simp only [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hc]
        exact zero_mem _
    exact fun _ hc ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hsub hc)
  set β' : C ⧸ K →+* (C ⧸ K₀) ⧸ (J.map ψ) :=
    Ideal.Quotient.lift K ((Ideal.Quotient.mk (J.map ψ)).comp (Ideal.Quotient.mk K₀)) hβ'zero
    with hβ'def
  have hβbij : Function.Bijective β :=
    bijective_of_leftInverse_comp ((Ideal.Quotient.mk (J.map ψ)).comp (Ideal.Quotient.mk K₀))
      (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective) β β' (fun _ ↦ rfl)
      Ideal.Quotient.mk_surjective
  -- the three-step factorisation
  have hfact : Ideal.quotientMap K φ h =
      β.comp ((Ideal.quotientMap (J.map ψ) ψ Ideal.le_comap_map).comp α) := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [hfact]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.FaithfullyFlat.of_bijective hαbij) hbase)
    (RingHom.FaithfullyFlat.of_bijective hβbij)

variable [TopologicalSpace C] [IsTopologicalRing C]

/-- **Faithful flatness of the quotients of `φ` by the closures of extended ideals rises with
the ideal.** Let `φ : A → C` be a ring homomorphism into a topological ring and let `I₀ ≤ I` be
ideals of `A`. If the closure of `I₀ C` is open and `A ⧸ I₀ → C ⧸ (I₀ C)‾` is faithfully flat,
then so is `A ⧸ I → C ⧸ (I C)‾`.

The sum `I C + (I₀ C)‾` is an ideal containing an open ideal, hence open, hence closed, so it
contains the closure of `I C`; that is the hypothesis of
`RingHom.faithfullyFlat_quotientMap_of_le_sup`. -/
public theorem faithfullyFlat_quotientMap_closure_of_le (φ : A →+* C) {I₀ I : Ideal A}
    (hle : I₀ ≤ I) (hopen : IsOpen ((Ideal.closure (I₀.map φ) : Ideal C) : Set C))
    (hff : (Ideal.quotientMap (Ideal.closure (I₀.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp fun _ hx ↦ subset_closure hx)).FaithfullyFlat) :
    (Ideal.quotientMap (Ideal.closure (I.map φ)) φ
      (Ideal.map_le_iff_le_comap.mp fun _ hx ↦ subset_closure hx)).FaithfullyFlat := by
  have hK₀K : (Ideal.closure (I₀.map φ) : Ideal C) ≤ Ideal.closure (I.map φ) :=
    fun _ hx ↦ closure_mono (SetLike.coe_subset_coe.mpr (Ideal.map_mono hle)) hx
  have hclosed : IsClosed ((I.map φ ⊔ Ideal.closure (I₀.map φ) : Ideal C) : Set C) :=
    (I.map φ ⊔ Ideal.closure (I₀.map φ) : Ideal C).toAddSubgroup.isClosed_of_isOpen
      (Submodule.isOpen_mono le_sup_right hopen)
  exact faithfullyFlat_quotientMap_of_le_sup φ hle hK₀K _ _
    (fun _ hx ↦ closure_minimal (SetLike.coe_subset_coe.mpr le_sup_left) hclosed hx) hff

end RingHom

end
