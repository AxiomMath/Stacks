module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CoveringResolution
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteProductIsCoproduct
public import StacksCore.Tactic.StacksAttribute

/-!
# The terms of the covering resolution of a locally finite covering are direct sums

Let `(X, R)` be a ringed space, let `X = ⋃ i, U i` be a locally finite open covering, and let
`F` be a sheaf of `R`-modules. The degree-`p` term of the covering resolution of Tag 02FU is the
product `∏ (j_{i₀ … i_p})_* F_{i₀ … i_p}` over the `(p+1)`-tuples of indices of the direct images
of the restrictions of `F` to the intersections `U i₀ ∩ ⋯ ∩ U i_p`. This file proves the third
displayed formula of Tag 02FT: that term, with the canonical injections, is also the direct sum
`⨁ (j_{i₀ … i_p})_* F_{i₀ … i_p}`.

The family of the intersections of the tuples is again locally finite
(`Stacks.locallyFinite_iInter`), and the direct image of a sheaf on an open `W` has no nonzero
sections over an open disjoint from `W`, so the family of the factors has locally finitely many
nonzero members, and
`Stacks.SheafOfModules.LocallyFiniteProduct.isColimitCofanDeltaInj` applies.

## Main results

* `Stacks.CechTotalComplex.CoveringResolution.isColimitCoveringTermCofan`: **Tag 02FT, third
  displayed formula.**

## References

* [Stacks Project, Tag 02FT](https://stacks.math.columbia.edu/tag/02FT)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits

universe u v w t

noncomputable section

namespace Stacks.CechTotalComplex.CoveringResolution

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
  {ι : Type t} (U : ι → Opens X)

/-- A sheaf of abelian groups has no nonzero sections over an empty open set. -/
theorem subsingleton_sections_of_eq_bot (G : TopCat.Sheaf AddCommGrpCat.{w} X) {O : Opens X}
    (h : O = ⊥) : Subsingleton (G.obj.obj (op O)) := by
  have hT := TopCat.Sheaf.isTerminalOfEqEmpty G h
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ c : G.obj.obj (op O), c = 0 := fun c =>
    ConcreteCategory.congr_hom (hT.hom_ext (𝟙 _) 0) c
  rw [h0 a, h0 b]

/-- The direct image of the restriction of `F` to `W` has no nonzero sections over an open set
disjoint from `W`. -/
theorem isZero_infPushforward_obj (F : SheafOfModules.{w} R) {W V : Opens X}
    (h : (V : Set X) ∩ (W : Set X) = ∅) :
    IsZero ((infPushforward.{u, v, w, t} X R F W).obj (op V)) := by
  have hb : V ⊓ W = ⊥ := Opens.ext (by simpa using h)
  have := subsingleton_sections_of_eq_bot X
    ⟨(uliftSheaf.{u, v, w, t} X R F).val.presheaf, (uliftSheaf.{u, v, w, t} X R F).isSheaf⟩ hb
  exact @ModuleCat.isZero_of_subsingleton _ _ _ this

/-- The degree-`p` term of the covering complex, as a family indexed by the `(p+1)`-tuples of
indices: the direct image of the restriction of `F` to the intersection of the tuple. -/
abbrev coveringFactor (F : SheafOfModules.{w} R) (p : ℕ) (s : Fin (p + 1) → ι) :
    SheafOfModules.{max u v w t} R :=
  (infPushforwardOpens.{u, v, w, t} X R F).obj
    (op (Stacks.CategoryTheory.CechComplex.inter U s))

/-- For a locally finite family `U`, the factors of the degree-`p` term of the covering complex
form a family with locally finitely many nonzero members. -/
theorem isLocallyFinitelyNonzero_coveringFactor (hlf : LocallyFinite fun i => (U i : Set X))
    (F : SheafOfModules.{w} R) (p : ℕ) :
    Stacks.SheafOfModules.LocallyFiniteProduct.IsLocallyFinitelyNonzero R
      (coveringFactor.{u, v, w, t} X R U F p) := by
  have hlf' : LocallyFinite fun s : Fin (p + 1) → ι =>
      ((Stacks.CategoryTheory.CechComplex.inter U s : Opens X) : Set X) := by
    convert Stacks.locallyFinite_iInter (J := Fin (p + 1)) hlf using 2 with s
    rw [Stacks.CategoryTheory.CechComplex.inter_eq_iInf, Opens.coe_iInf]
  intro V
  refine ⟨⟨fun W _ => ∃ S : Finset (Fin (p + 1) → ι), ∀ s ∉ S,
      (W : Set X) ∩ ((Stacks.CategoryTheory.CechComplex.inter U s : Opens X) : Set X) = ∅,
    fun {W W'} _ ⟨S, hS⟩ g => ⟨S, fun s hs => Set.eq_empty_of_subset_empty
      ((Set.inter_subset_inter_left _ (leOfHom g)).trans (hS s hs).subset)⟩⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨t', ht, hfin⟩ := hlf' x
    obtain ⟨W, hWt, hWo, hxW⟩ := mem_nhds_iff.mp ht
    refine ⟨V ⊓ ⟨W, hWo⟩, homOfLE inf_le_left, ⟨hfin.toFinset, fun s hs => ?_⟩, ⟨hx, hxW⟩⟩
    exact Set.eq_empty_iff_forall_notMem.mpr fun y hy =>
      hs (hfin.mem_toFinset.mpr ⟨y, hy.2, hWt hy.1.2⟩)
  · rintro W g ⟨S, hS⟩
    exact ⟨S, fun s hs => isZero_infPushforward_obj.{u, v, w, t} X R F (hS s hs)⟩

/-- The canonical injection of the factor indexed by the tuple `s` into the degree-`p` term of
the covering complex: its component at `s` is the identity and its other components are zero. -/
abbrev coveringTermInj (F : SheafOfModules.{w} R) (p : ℕ) (s : Fin (p + 1) → ι) :
    coveringFactor.{u, v, w, t} X R U F p s ⟶ ((coveringComplex.{u, v, w, t} X R U).obj F).X p :=
  Stacks.SheafOfModules.LocallyFiniteProduct.deltaInj R (coveringFactor.{u, v, w, t} X R U F p)
    (Stacks.CategoryTheory.CechComplex.π U (infPushforwardOpens.{u, v, w, t} X R F) p)
    (Stacks.CategoryTheory.CechComplex.isLimitFan U (infPushforwardOpens.{u, v, w, t} X R F) p) s

/-- **Stacks Project, Tag 02FT, third displayed formula.** Let `(X, R)` be a ringed space, let
`X = ⋃ i, U i` be a locally finite open covering and let `F` be a sheaf of `R`-modules. Then the
degree-`p` term `𝔠ᵖ(𝒰, F) = ∏ (j_{i₀ … i_p})_* F_{i₀ … i_p}` of the covering resolution of
Tag 02FU, together with the canonical injections `coveringTermInj`, is a coproduct of the
factors: `𝔠ᵖ(𝒰, F) = ⨁ (j_{i₀ … i_p})_* F_{i₀ … i_p}`.

The covering hypothesis is the source's; the proof uses only local finiteness. -/
@[stacks 02FT "(third displayed formula: the terms of the complex of Tag 02FU are
𝔠ᵖ(𝒰, F) = ⨁ (j_{i₀…i_p})_* F_{i₀…i_p})"]
def isColimitCoveringTermCofan (_hU : ⨆ i, U i = ⊤) (hlf : LocallyFinite fun i => (U i : Set X))
    (F : SheafOfModules.{w} R) (p : ℕ) :
    IsColimit (Cofan.mk (((coveringComplex.{u, v, w, t} X R U).obj F).X p)
      (coveringTermInj.{u, v, w, t} X R U F p)) :=
  let _ := wEqualsLocallyBijective_opens.{u, max v w t} X
  Stacks.SheafOfModules.LocallyFiniteProduct.isColimitCofanDeltaInj R
    (coveringFactor.{u, v, w, t} X R U F p) _
    (Stacks.CategoryTheory.CechComplex.isLimitFan U (infPushforwardOpens.{u, v, w, t} X R F) p)
    (isLocallyFinitelyNonzero_coveringFactor.{u, v, w, t} X R U hlf F p)

end Stacks.CechTotalComplex.CoveringResolution
