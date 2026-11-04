module

public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Extension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticImage
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange

/-!
# Extending finite type sheaves of ideals compatibly with a flat chart

Let `X` be a quasi-compact and quasi-separated scheme, `K` a quasi-coherent sheaf of ideals on
`X`, `V₁, …, Vₙ ⊆ X` quasi-compact opens carrying finite type sheaves of ideals `Iᵢ ≤ K|_{Vᵢ}`
which agree on the overlaps, and `q : T ⟶ X` a flat morphism from a quasi-compact scheme
carrying a finite type sheaf of ideals `I_T ≤ q⁻¹K` which lies in `q⁻¹Iᵢ` over every `Vᵢ`.
Then there is a finite type sheaf of ideals `J ≤ K` on `X` restricting to `Iᵢ` on every `Vᵢ`
and with `I_T ≤ q⁻¹J`.

This is the base case — a quasi-compact quasi-separated scheme, in particular an affine one —
of the induction, along the principle of [Stacks, Tag 08GP], which extends finite type sheaves
of ideals below a given one on a quasi-compact quasi-separated algebraic space compatibly with
a flat (in practice étale) chart; that is the approximation input of [Stacks, Tag 0860].

## Main results

* `Stacks.FiniteTypeIdealSheaf.comap_inf_of_flat`,
  `Stacks.FiniteTypeIdealSheaf.comap_iInf_of_flat`: the inverse image along a flat
  morphism commutes with finite infima of sheaves of ideals.
* `Stacks.FiniteTypeIdealSheaf.map_comap_snd_le_comap_map`,
  `Stacks.FiniteTypeIdealSheaf.comap_map_of_flat`: flat base change of the direct image of a
  sheaf of ideals along a quasi-compact morphism.
* `Stacks.FiniteTypeIdealSheaf.le_comap_ker_of_mk_inf_le`: an inclusion of closed subschemes over
  a flat monomorphism, read on ideals.
* `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_comap_eq_of_flat`: **the base case.**

## Implementation notes

Both flat base change statements are consequences of [Stacks, Tag 081I], available as
`AlgebraicGeometry.ker_pullback_snd_eq_comap`, except the binary infimum, which is checked on
pairs of affine opens with the ring-theoretic statement `map_inf_of_flat`.

In the base case the sheaf of ideals `K' = K ⊓ ⨅ᵢ (Iᵢ)_*` restricts to `Iᵢ` on `Vᵢ` by the
compatibility, and by flat base change of the direct images `I_T ≤ q⁻¹K'`. The finite type `J`
is then a finite supremum of finite type sheaves of ideals below `K'`, each produced by
`Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_of_le_comap`: one along `q` for `I_T`, and
one along each open immersion `Vᵢ ⟶ X` for `Iᵢ`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 081I](https://stacks.math.columbia.edu/tag/081I)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.FiniteTypeIdealSheaf

variable {X Y T W : Scheme.{u}}

/-! ### Flat inverse image and finite infima -/

/-- **The inverse image along a flat morphism commutes with binary infima of sheaves of
ideals.** On a pair of affine opens `V ⊆ q⁻¹U` the inverse image is the extension of ideals
along the flat ring map `q.appLE U V`, which commutes with intersections. -/
theorem comap_inf_of_flat (q : T ⟶ Y) [Flat q] (I J : Y.IdealSheafData) :
    (I ⊓ J).comap q = I.comap q ⊓ J.comap q := by
  refine le_antisymm (le_inf (comap_mono q inf_le_left) (comap_mono q inf_le_right)) ?_
  refine le_of_iSup_eq_top
    (fun p : {p : Y.affineOpens × T.affineOpens // p.2.1 ≤ q ⁻¹ᵁ p.1.1} => p.1.2) ?_ ?_
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (u := (q ⁻¹ᵁ U : Set T)) hxU
        (q ⁻¹ᵁ U).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hxV⟩
  · rintro ⟨⟨U, V⟩, h⟩
    show (I.comap q).ideal V ⊓ (J.comap q).ideal V ≤ ((I ⊓ J).comap q).ideal V
    rw [Stacks.IdealSheaf.ideal_comap_appLE I q U V h,
      Stacks.IdealSheaf.ideal_comap_appLE J q U V h,
      Stacks.IdealSheaf.ideal_comap_appLE (I ⊓ J) q U V h]
    let := (q.appLE U V h).hom.toAlgebra
    have : Module.Flat Γ(Y, U.1) Γ(T, V.1) := q.flat_appLE U.2 V.2 h
    exact (map_inf_of_flat (S := Γ(T, V.1)) (I.ideal U) (J.ideal U)).ge

/-- **The inverse image along a flat morphism commutes with finite infima of sheaves of
ideals.** -/
theorem comap_iInf_of_flat (q : T ⟶ Y) [Flat q] {ι : Type*} [Finite ι]
    (M : ι → Y.IdealSheafData) : (⨅ i, M i).comap q = ⨅ i, (M i).comap q := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, (s.inf M).comap q = s.inf fun i => (M i).comap q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [comap_top]
    | insert i s _ ih => rw [Finset.inf_insert, Finset.inf_insert, comap_inf_of_flat, ih]
  rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf, key]

/-! ### Flat base change of the direct image -/

/-- The direct image of `A` along a quasi-compact `g` is the kernel of `A.subschemeι ≫ g`. -/
theorem map_eq_ker_subschemeι_comp (A : W.IdealSheafData) (g : W ⟶ Y) [QuasiCompact g] :
    A.map g = (A.subschemeι ≫ g).ker := by
  rw [← map_ker, ker_subschemeι]

/-- **Flat base change of the direct image of a sheaf of ideals, the inclusion that needs
flatness.** For a quasi-compact `g : W ⟶ Y` and a flat `q : T ⟶ Y`, the direct image along
the base change `pullback.fst q g` of the inverse image of `A` lies in the inverse image along
`q` of the direct image of `A`.

By [Stacks, Tag 081I] the right side is the kernel of the base change along `q` of
`A.subschemeι ≫ g`, and that base change factors through the closed subscheme cut out by the
left side. -/
theorem map_comap_snd_le_comap_map (A : W.IdealSheafData) (g : W ⟶ Y) (q : T ⟶ Y) [Flat q]
    [QuasiCompact g] :
    (A.comap (pullback.snd q g)).map (pullback.fst q g) ≤ (A.map g).comap q := by
  rw [map_eq_ker_subschemeι_comp A g,
    map_eq_ker_subschemeι_comp (A.comap (pullback.snd q g)) (pullback.fst q g),
    ← ker_pullback_snd_eq_comap q (A.subschemeι ≫ g)]
  let a : pullback (A.subschemeι ≫ g) q ⟶ pullback q g :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ A.subschemeι)
      (by rw [Category.assoc, ← pullback.condition])
  let b : pullback (A.subschemeι ≫ g) q ⟶ pullback (pullback.snd q g) A.subschemeι :=
    pullback.lift a (pullback.fst _ _) (pullback.lift_snd _ _ _)
  have hb : b ≫ pullback.fst _ _ = a := pullback.lift_fst _ _ _
  have ha' : a ≫ pullback.fst q g = pullback.snd _ _ := pullback.lift_fst _ _ _
  let u : pullback (A.subschemeι ≫ g) q ⟶ (A.comap (pullback.snd q g)).subscheme :=
    b ≫ (A.comapIso (pullback.snd q g)).inv
  have hu : u ≫ (A.comap (pullback.snd q g)).subschemeι ≫ pullback.fst q g =
      pullback.snd (A.subschemeι ≫ g) q := by
    rw [Category.assoc, comapIso_inv_subschemeι_assoc, reassoc_of% hb, ha']
  rw [← hu]
  exact Scheme.Hom.le_ker_comp u _

/-- **Flat base change of the direct image of a sheaf of ideals.** For a quasi-compact
`g : W ⟶ Y` and a flat `q : T ⟶ Y`, the inverse image along `q` of the direct image of `A` is
the direct image along `pullback.fst q g` of the inverse image of `A` along `pullback.snd q g`.

The inclusion `≥` is `Stacks.FiniteTypeIdealSheaf.map_comap_snd_le_comap_map`; the inclusion
`≤` is formal, from the Galois connection and the commutativity of the square. -/
theorem comap_map_of_flat (A : W.IdealSheafData) (g : W ⟶ Y) (q : T ⟶ Y) [Flat q]
    [QuasiCompact g] :
    (A.map g).comap q = (A.comap (pullback.snd q g)).map (pullback.fst q g) := by
  refine le_antisymm ((map_gc _).le_iff_le.mp ?_) (map_comap_snd_le_comap_map A g q)
  rw [← comap_comp, pullback.condition, comap_comp]
  exact comap_mono _ (comap_map_le _ _)

/-! ### Inclusions of closed subschemes over a flat monomorphism -/

/-- **An inclusion of closed subschemes over a flat monomorphism, read on ideals.** Let
`f : Z ⟶ X` be a quasi-compact monomorphism, `a : V ⟶ X` a flat monomorphism and `I` a sheaf
of ideals on `V`. If the intersection of the subobjects `f` and `a` of `X` lies in the closed
subscheme `V(I)` of `V`, then `I` lies in the inverse image along `a` of the kernel of `f`.

By [Stacks, Tag 081I] that inverse image is the kernel of `pullback.snd f a`, which factors
through `V(I)` by hypothesis. -/
theorem le_comap_ker_of_mk_inf_le {Z V : Scheme.{u}} (f : Z ⟶ X) [Mono f] [QuasiCompact f]
    (a : V ⟶ X) [Mono a] [Flat a] (I : V.IdealSheafData)
    (h : Subobject.mk f ⊓ Subobject.mk a ≤ Subobject.mk (I.subschemeι ≫ a)) :
    I ≤ f.ker.comap a := by
  rw [← ker_pullback_snd_eq_comap a f]
  have hf : (Subobject.mk (I.subschemeι ≫ a)).Factors (pullback.snd f a ≫ a) :=
    Subobject.factors_of_le _ h ((Subobject.inf_factors _).2
      ⟨(Subobject.mk_factors_iff _ _).2 ⟨pullback.fst f a, pullback.condition⟩,
        (Subobject.mk_factors_iff _ _).2 ⟨pullback.snd f a, rfl⟩⟩)
  obtain ⟨g, hg⟩ := (Subobject.mk_factors_iff _ _).1 hf
  have hg' : g ≫ I.subschemeι = pullback.snd f a :=
    (cancel_mono a).1 ((Category.assoc _ _ _).trans hg)
  rw [← hg']
  exact (ker_subschemeι I).ge.trans (Scheme.Hom.le_ker_comp g _)

/-! ### The base case -/

/-- **Extending finite type sheaves of ideals below a given one, compatibly with a flat chart:
the base case.** Let `X` be a quasi-compact quasi-separated scheme, `K` a sheaf of ideals on
`X`, `A i : V i ⟶ X` finitely many open immersions with quasi-compact sources and `I i` finite
type sheaves of ideals on the `V i` with `I i ≤ K|_{V i}` whose closed subschemes agree on the
overlaps. Let `q : T ⟶ X` be flat with `T` quasi-compact and `ID` a finite type sheaf of
ideals on `T` with `ID ≤ q⁻¹K` which, over each `V i`, lies in the inverse image of `I i`.
Then some finite type sheaf of ideals `J ≤ K` on `X` restricts to `I i` on every `V i` and
satisfies `ID ≤ q⁻¹J`.

This is the base case (an affine, indeed any quasi-compact quasi-separated, scheme) of the
extension of finite type sheaves of ideals below a given one compatibly with a flat (étale)
chart, which the induction principle [Stacks, Tag 08GP] propagates to quasi-compact
quasi-separated algebraic spaces for [Stacks, Tag 0860].

The sheaf of ideals `K' = K ⊓ ⨅ i, (I i)_*` restricts to `I i` on `V i` by the compatibility,
and `ID ≤ q⁻¹K'` by flat base change of the direct images; `J` is a finite supremum of finite
type sheaves of ideals below `K'` produced by
`Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_of_le_comap`. -/
theorem exists_isFiniteType_le_comap_eq_of_flat [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) {ι : Type*} [Finite ι] {V : ι → Scheme.{u}} (A : ∀ i, V i ⟶ X)
    [∀ i, IsOpenImmersion (A i)] [∀ i, CompactSpace (V i)]
    (I : ∀ i, (V i).IdealSheafData) (hI : ∀ i, (I i).IsFiniteType)
    (hcompat : ∀ i j, Subobject.mk ((I i).subschemeι ≫ A i) ⊓ Subobject.mk (A j) =
      Subobject.mk ((I j).subschemeι ≫ A j) ⊓ Subobject.mk (A i))
    (hIK : ∀ i, I i ≤ K.comap (A i)) [CompactSpace T] (q : T ⟶ X) [Flat q]
    (ID : T.IdealSheafData) (hID : ID.IsFiniteType) (hIDK : ID ≤ K.comap q)
    (hIDI : ∀ i, ID.comap (pullback.fst q (A i)) ≤ (I i).comap (pullback.snd q (A i))) :
    ∃ J : X.IdealSheafData, J.IsFiniteType ∧ J ≤ K ∧ (∀ i, J.comap (A i) = I i) ∧
      ID ≤ J.comap q := by
  classical
  have := Fintype.ofFinite ι
  set K' := K ⊓ ⨅ i, (I i).map (A i) with hK'
  have hK'A : ∀ j, K'.comap (A j) = I j := by
    intro j
    refine le_antisymm ((comap_mono (A j) (inf_le_right.trans (iInf_le _ j))).trans
      (comap_map_le _ _)) ?_
    rw [hK', comap_inf_of_flat, comap_iInf_of_flat]
    refine le_inf (hIK j) (le_iInf fun i => ?_)
    rw [map_eq_ker_subschemeι_comp]
    exact le_comap_ker_of_mk_inf_le _ (A j) (I j) ((hcompat i j).le.trans inf_le_left)
  have hIDK' : ID ≤ K'.comap q := by
    rw [hK', comap_inf_of_flat, comap_iInf_of_flat]
    refine le_inf hIDK (le_iInf fun i => ?_)
    exact ((map_gc _).le_iff_le.mp (hIDI i)).trans (map_comap_snd_le_comap_map (I i) (A i) q)
  obtain ⟨J₁, hJ₁, hJ₁K', hIDJ₁⟩ := exists_isFiniteType_le_of_le_comap q K' ID hID hIDK'
  choose J₂ hJ₂ hJ₂K' hIJ₂ using fun i =>
    exists_isFiniteType_le_of_le_comap (A i) K' (I i) (hI i) (hK'A i).ge
  have hJft : (J₁ ⊔ Finset.univ.sup J₂).IsFiniteType :=
    hJ₁.sup (Finset.sup_induction isFiniteType_bot (fun a ha b hb => ha.sup hb)
      fun i _ => hJ₂ i)
  have hJK' : J₁ ⊔ Finset.univ.sup J₂ ≤ K' := sup_le hJ₁K' (Finset.sup_le fun i _ => hJ₂K' i)
  refine ⟨J₁ ⊔ Finset.univ.sup J₂, hJft, hJK'.trans inf_le_left, fun i => le_antisymm
    ((comap_mono (A i) hJK').trans (hK'A i).le) ((hIJ₂ i).trans (comap_mono (A i)
      ((Finset.le_sup (f := J₂) (Finset.mem_univ i)).trans le_sup_right))),
    hIDJ₁.trans (comap_mono q le_sup_left)⟩

end Stacks.FiniteTypeIdealSheaf

end
