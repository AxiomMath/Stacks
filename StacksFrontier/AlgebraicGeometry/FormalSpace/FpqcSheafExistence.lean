module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FpqcSheafAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridgeRelation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionMiddle
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetFromCoversTop

/-!
# Descending the base change of an affine formal chart

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an fppf sheaf on the big fppf
site of `S`, and let `f : T' ⟶ T` be a morphism of the site whose underlying morphism of schemes
is surjective, flat and quasi-compact. Let `c` be a section of `X` over `T'` whose two
restrictions to `T' ×_T T'` agree. The second paragraph of the proof of **Stacks 0AQD**
produces, from one affine formal chart `u : U ⟶ X`, a section of `X` over an étale `W ⟶ T`
which induces `c` over `T' ×_T W`:

* the base change `V = U ×_{X, c} T'` is a scheme, étale and separated over `T'`, hence
  ind-quasi-affine (Stacks 0AP9 with Stacks 03WS);
* the compatibility of `c` makes `V` a descent datum relative to `T' ⟶ T` (Descent,
  Definition 023V), since both pullbacks of `V` to `T' ×_T T'` are the base change of `U`
  along the common composite `T' ×_T T' ⟶ X`;
* the datum is effective by **Stacks 0APK**, giving `W ⟶ T` with `T' ×_T W ≅ V`, and `W` is
  étale over `T` by fpqc descent of étaleness (Stacks 02VN);
* the composite `T' ×_T W ≅ V ⟶ U` is invariant under the two projections of the self-fibre
  product of `T' ×_T W` over `W`, and so descends to `W ⟶ U` because `U`, being an affine formal
  algebraic space, is an fpqc sheaf (Stacks 023Q in the form of
  `AlgebraicGeometry.FormalSpace.isSheaf_fpqc_of_isAffineFormalAlgebraicSpace`).

This module carries that out. It is the counterpart for formal algebraic spaces of
`AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_singleton_of_isEffectiveFpqcDescent` together
with `StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridge`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_gluingIso_of_isPullback_chart`: the gluing isomorphism
  of the descent datum on `V`, in the site.
* `AlgebraicGeometry.FormalSpace.exists_descended_section_of_chart`: the section of `X` over
  the descended étale `W ⟶ T`.

## Implementation notes

The chart `U` is a sheaf, not an object of the site, so the morphism `q : V ⟶ U` which the
gluing isomorphism must preserve is a morphism of sheaves out of the sheafified representable
of `V`. It can be composed only with morphisms out of objects of the site, and so cannot play
the role of the invariant morphism of schemes `b` of
`AlgebraicGeometry.exists_transition_of_pullbackIso`. It enters instead through the relation
`AlgebraicGeometry.FormalSpace.ChartRel`: two morphisms of schemes into `V` are related when
they lie over the same point of `S` and have the same composite with `q` after any morphism out
of an object of the site through which both factor. The bridge of
`StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridgeRelation` is stated for such a
relation, and asks for the extensionality of morphisms into `V` only at the triple product on
which the cocycle condition lives; that triple product is the underlying scheme of an object of
the site, by `AlgebraicGeometry.FormalSpace.exists_iso_of_isPullback_toScheme`, and there
extensionality is the pullback square defining `V`.

## References

* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


/-- A morphism of schemes from the underlying scheme of an object `Z` of the site into the
underlying scheme of an object `V` which is compatible with the structure morphisms to `S` is
the image of a morphism of the site. -/
theorem exists_hom_of_toScheme {Z V : BigFppfOver B S hS}
    (g : (BigFppfOver.toScheme B S hS).obj Z ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hg : g ≫ B.inclusion.map V.hom = B.inclusion.map Z.hom) :
    ∃ s : Z ⟶ V, (BigFppfOver.toScheme B S hS).map s = g :=
  ⟨Over.homMk (B.inclusion.preimage g)
      (B.inclusion.map_injective (by rwa [Functor.map_comp, Functor.map_preimage])),
    B.inclusion.map_preimage g⟩

/-- The structure morphism to `S` of the underlying scheme of an object of the site, read
through a morphism of the site. -/
theorem toScheme_map_comp_structure {Z V : BigFppfOver B S hS} (s : Z ⟶ V) :
    (BigFppfOver.toScheme B S hS).map s ≫ B.inclusion.map V.hom = B.inclusion.map Z.hom := by
  have h := congrArg B.inclusion.map (Over.w s)
  rwa [Functor.map_comp] at h

/-- A scheme sitting in a pullback square of schemes over a cospan of morphisms of the site is,
up to isomorphism, the underlying scheme of an object of the site, with legs the images of
morphisms of the site. This is the fact that the canonical functor to schemes preserves fibre
products. -/
theorem exists_iso_of_isPullback_toScheme {Z : Scheme.{u}} {P₁ P₂ P : BigFppfOver B S hS}
    {l₁ : Z ⟶ (BigFppfOver.toScheme B S hS).obj P₁} {l₂ : Z ⟶ (BigFppfOver.toScheme B S hS).obj P₂}
    (x : P₁ ⟶ P) (y : P₂ ⟶ P)
    (h : IsPullback l₁ l₂ ((BigFppfOver.toScheme B S hS).map x)
      ((BigFppfOver.toScheme B S hS).map y)) :
    ∃ (Z' : BigFppfOver B S hS) (e : (BigFppfOver.toScheme B S hS).obj Z' ≅ Z) (m₁ : Z' ⟶ P₁)
      (m₂ : Z' ⟶ P₂), e.hom ≫ l₁ = (BigFppfOver.toScheme B S hS).map m₁ ∧
        e.hom ≫ l₂ = (BigFppfOver.toScheme B S hS).map m₂ :=
  ⟨pullback x y,
    ((IsPullback.of_hasPullback x y).map (BigFppfOver.toScheme B S hS)).isoIsPullback _ _ h,
    pullback.fst x y, pullback.snd x y, IsPullback.isoIsPullback_hom_fst _ _ _ _,
    IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

/-- **The relation through which a chart morphism out of `V` enters the descent datum.** Two
morphisms of schemes `a₁ a₂ : Z ⟶ V`, from an arbitrary scheme into the underlying scheme of an
object `V` of the site, are related when they lie over the same point of `S` and, after every
morphism `z` into `Z` out of the underlying scheme of an object `Z'` of the site through which
both become morphisms `s₁ s₂ : Z' ⟶ V` of the site, the two composites with `q` agree. -/
def ChartRel {V : BigFppfOver B S hS} {U : FppfSheaf B S hS} (q : (fppfYoneda B S hS).obj V ⟶ U)
    {Z : Scheme.{u}}
    (a₁ a₂ : Z ⟶ (BigFppfOver.toScheme B S hS).obj V) : Prop :=
  a₁ ≫ B.inclusion.map V.hom = a₂ ≫ B.inclusion.map V.hom ∧
    ∀ (Z' : BigFppfOver B S hS) (z : (BigFppfOver.toScheme B S hS).obj Z' ⟶ Z) (s₁ s₂ : Z' ⟶ V),
      (BigFppfOver.toScheme B S hS).map s₁ = z ≫ a₁ →
      (BigFppfOver.toScheme B S hS).map s₂ = z ≫ a₂ →
        (fppfYoneda B S hS).map s₁ ≫ q = (fppfYoneda B S hS).map s₂ ≫ q

section ChartRel

variable {V : BigFppfOver B S hS} {U : FppfSheaf B S hS} (q : (fppfYoneda B S hS).obj V ⟶ U)

/-- `ChartRel q` is stable under precomposition with a morphism of schemes `k : Z₂ ⟶ Z`. -/
theorem ChartRel.comp {Z Z₂ : Scheme.{u}} (k : Z₂ ⟶ Z)
    {a₁ a₂ : Z ⟶ (BigFppfOver.toScheme B S hS).obj V}
    (h : ChartRel q a₁ a₂) : ChartRel q (k ≫ a₁) (k ≫ a₂) := by
  refine ⟨by rw [Category.assoc, Category.assoc, h.1], fun Z' z s₁ s₂ h₁ h₂ ↦ ?_⟩
  exact h.2 Z' (z ≫ k) s₁ s₂ (by rw [h₁, Category.assoc]) (by rw [h₂, Category.assoc])

/-- `ChartRel q` is symmetric. -/
theorem ChartRel.symm {Z : Scheme.{u}} {a₁ a₂ : Z ⟶ (BigFppfOver.toScheme B S hS).obj V}
    (h : ChartRel q a₁ a₂) :
    ChartRel q a₂ a₁ :=
  ⟨h.1.symm, fun Z' z s₁ s₂ h₁ h₂ ↦ (h.2 Z' z s₂ s₁ h₂ h₁).symm⟩

/-- `ChartRel q` is transitive. -/
theorem ChartRel.trans {Z : Scheme.{u}} {a₁ a₂ a₃ : Z ⟶ (BigFppfOver.toScheme B S hS).obj V}
    (h : ChartRel q a₁ a₂) (h' : ChartRel q a₂ a₃) : ChartRel q a₁ a₃ := by
  refine ⟨h.1.trans h'.1, fun Z' z s₁ s₃ h₁ h₃ ↦ ?_⟩
  obtain ⟨s₂, h₂⟩ := exists_hom_of_toScheme (z ≫ a₂) (by
    rw [Category.assoc, ← h.1, ← Category.assoc, ← h₁]
    exact toScheme_map_comp_structure s₁)
  exact (h.2 Z' z s₁ s₂ h₁ h₂).trans (h'.2 Z' z s₂ s₃ h₂ h₃)

end ChartRel

variable {T T' V : BigFppfOver B S hS} {f : T' ⟶ T} {X U : FppfSheaf B S hS} {u : U ⟶ X}
  {c : (fppfYoneda B S hS).obj T' ⟶ X} {q : (fppfYoneda B S hS).obj V ⟶ U} {p : V ⟶ T'}

/-- **The gluing isomorphism of the descent datum on the base change of a chart.** Let
`u : U ⟶ X` be a morphism of fppf sheaves, let `c` be a section of `X` over `T'` whose two
restrictions to `T' ×_T T'` agree, and let `V` represent the fibre product of `u` and `c`. Then
`V ×_{T'} (T' ×_T T')` and `(T' ×_T T') ×_{T'} V` are isomorphic over `T' ×_T T'`, compatibly
with `q`.

Both represent the fibre product of `u` with the composite `T' ×_T T' ⟶ T' ⟶ X`, the first
through the first projection and the second through the second, and those two composites agree
by `hcc`. Full faithfulness of the sheafified Yoneda embedding of the site turns the isomorphism
of sheaves into an isomorphism of the site. Nothing is assumed of `U`. -/
theorem exists_gluingIso_of_isPullback_chart (sq : IsPullback q ((fppfYoneda B S hS).map p) u c)
    (hcc : (fppfYoneda B S hS).map (pullback.fst f f) ≫ c =
      (fppfYoneda B S hS).map (pullback.snd f f) ≫ c) :
    ∃ θ : pullback p (pullback.fst f f) ≅ pullback (pullback.snd f f) p,
      θ.hom ≫ pullback.fst (pullback.snd f f) p = pullback.snd p (pullback.fst f f) ∧
      (fppfYoneda B S hS).map (θ.hom ≫ pullback.snd (pullback.snd f f) p) ≫ q =
        (fppfYoneda B S hS).map (pullback.fst p (pullback.fst f f)) ≫ q := by
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have _ := Sheaf.preservesFiniteLimits_sheafifiedYoneda (BigFppfOver.topology B S hS)
  have sqQ : IsPullback ((fppfYoneda B S hS).map (pullback.fst p (pullback.fst f f)) ≫ q)
      ((fppfYoneda B S hS).map (pullback.snd p (pullback.fst f f))) u
      ((fppfYoneda B S hS).map (pullback.fst f f) ≫ c) :=
    ((IsPullback.of_hasPullback p (pullback.fst f f)).map (fppfYoneda B S hS)).paste_horiz sq
  have sqQ' : IsPullback ((fppfYoneda B S hS).map (pullback.snd (pullback.snd f f) p) ≫ q)
      ((fppfYoneda B S hS).map (pullback.fst (pullback.snd f f) p)) u
      ((fppfYoneda B S hS).map (pullback.fst f f) ≫ c) := by
    rw [hcc]
    exact ((IsPullback.of_hasPullback (pullback.snd f f) p).flip.map
      (fppfYoneda B S hS)).paste_horiz sq
  refine ⟨(fppfYoneda B S hS).preimageIso (sqQ.isoIsPullback _ _ sqQ'), ?_, ?_⟩
  · refine (fppfYoneda B S hS).map_injective ?_
    simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage]
    exact sqQ.isoIsPullback_hom_snd _ _ sqQ'
  · simp only [Functor.map_comp, Functor.preimageIso, Functor.map_preimage, Category.assoc]
    exact sqQ.isoIsPullback_hom_fst _ _ sqQ'

/-- **The section of `X` descended from one affine formal chart: the second paragraph of the
proof of Stacks 0AQD.** Let `f : T' ⟶ T` be a morphism of the big fppf site of `S` whose
underlying morphism of schemes is surjective, flat and quasi-compact, let `u : U ⟶ X` be a
morphism of fppf sheaves out of an affine formal algebraic space, and let `c` be a section of
`X` over `T'` whose two restrictions to `T' ×_T T'` agree. Let `V` represent the fibre product of
`u` and `c`, with `V ⟶ T'` étale and separated. Then there are a morphism `w : W ⟶ T` of the
site, étale on underlying schemes, and a section `x` of `X` over `W` which restricts to the
restriction of `c` over `T' ×_T W`; the image of `W` in `T` contains the image of `V`.

`V ⟶ T'` is ind-quasi-affine (Stacks 0AP9 and Stacks 03WS), and the compatibility of `c` makes
it a descent datum relative to `T' ⟶ T`, which is effective by **Stacks 0APK**,
`AlgebraicGeometry.DescentDatum.isEffective_of_isIndQuasiAffineHom_of_quasiCompact`. The
descended scheme lies in the site because its base change along the flat surjective `f` does,
and it is étale over `T` because étaleness descends along `f` (Stacks 02VN). The composite
`T' ×_T W ≅ V ⟶ U` is invariant under the two projections of the self-fibre product of
`T' ×_T W` over `W`, so it descends to `W ⟶ U` by the fpqc sheaf property of the affine formal
algebraic space `U` (Stacks 023Q, read through
`AlgebraicGeometry.FormalSpace.isSheaf_fpqc_of_isAffineFormalAlgebraicSpace`); composing with `u`
gives `x`. -/
theorem exists_descended_section_of_chart {T T' : BigFppfOver B S hS} (f : T' ⟶ T)
    (hfs : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hff : Flat ((BigFppfOver.toScheme B S hS).map f))
    (hfq : QuasiCompact ((BigFppfOver.toScheme B S hS).map f))
    {X U : FppfSheaf B S hS} (hU : IsAffineFormalAlgebraicSpace B S hS U) (u : U ⟶ X)
    {c : (fppfYoneda B S hS).obj T' ⟶ X}
    (hcc : (fppfYoneda B S hS).map (pullback.fst f f) ≫ c =
      (fppfYoneda B S hS).map (pullback.snd f f) ≫ c)
    {V : BigFppfOver B S hS} {p : V ⟶ T'} {q : (fppfYoneda B S hS).obj V ⟶ U}
    (sq : IsPullback q ((fppfYoneda B S hS).map p) u c)
    (hpe : Etale ((BigFppfOver.toScheme B S hS).map p))
    (hps : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p)) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T) (x : (fppfYoneda B S hS).obj W ⟶ X),
      Etale ((BigFppfOver.toScheme B S hS).map w) ∧
      (fppfYoneda B S hS).map (pullback.snd f w) ≫ x =
        (fppfYoneda B S hS).map (pullback.fst f w) ≫ c ∧
      (BigFppfOver.toScheme B S hS).map f '' Set.range ((BigFppfOver.toScheme B S hS).map p) ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map w) := by
  classical
  have _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have _ := Sheaf.preservesFiniteLimits_sheafifiedYoneda (BigFppfOver.topology B S hS)
  have := hfs
  have := hff
  have := hfq
  have := hpe
  have := hps
  -- the structure morphism of `V` to `S` factors through `p` and `f`
  have hπV : B.inclusion.map V.hom = (BigFppfOver.toScheme B S hS).map p ≫
      (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map T.hom := by
    rw [toScheme_map_comp_structure f, toScheme_map_comp_structure p]
  -- the gluing isomorphism, in the site and on the literal fibre products of schemes
  obtain ⟨θ, hθfst, hθq⟩ := exists_gluingIso_of_isPullback_chart sq hcc
  have pbB : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst p (pullback.fst f f)))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd p (pullback.fst f f)) ≫
        (BigFppfOver.toScheme B S hS).map (pullback.snd f f))
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map f) :=
    ((IsPullback.of_hasPullback p (pullback.fst f f)).map
      (BigFppfOver.toScheme B S hS)).paste_vert
      ((IsPullback.of_hasPullback f f).map (BigFppfOver.toScheme B S hS))
  have pbB' : IsPullback
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (pullback.snd f f) p) ≫
        (BigFppfOver.toScheme B S hS).map (pullback.fst f f))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (pullback.snd f f) p))
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f) :=
    ((((IsPullback.of_hasPullback (pullback.snd f f) p).map
      (BigFppfOver.toScheme B S hS)).flip).paste_vert
      (((IsPullback.of_hasPullback f f).map (BigFppfOver.toScheme B S hS)).flip)).flip
  set Θ := pbB.isoPullback.symm ≪≫ (BigFppfOver.toScheme B S hS).mapIso θ ≪≫
    pbB'.isoPullback with hΘ
  have hΘfst : Θ.hom ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f) =
      pbB.isoPullback.inv ≫ (BigFppfOver.toScheme B S hS).map
        (θ.hom ≫ pullback.fst (pullback.snd f f) p ≫ pullback.fst f f) := by
    simp only [hΘ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      IsPullback.isoPullback_hom_fst, Functor.map_comp]
  have hΘsnd : Θ.hom ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f) =
      pbB.isoPullback.inv ≫ (BigFppfOver.toScheme B S hS).map
        (θ.hom ≫ pullback.snd (pullback.snd f f) p) := by
    simp only [hΘ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      IsPullback.isoPullback_hom_snd, Functor.map_comp]
  have hsite1 : θ.hom ≫ pullback.fst (pullback.snd f f) p ≫ pullback.fst f f =
      pullback.fst p (pullback.fst f f) ≫ p := by
    rw [← Category.assoc, hθfst]
    exact pullback.condition.symm
  have hsite2 : (θ.hom ≫ pullback.snd (pullback.snd f f) p) ≫ p =
      pullback.snd p (pullback.fst f f) ≫ pullback.snd f f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hθfst]
  have hΘ1 : Θ.hom ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f) =
      pullback.fst ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map f) ≫ (BigFppfOver.toScheme B S hS).map p := by
    rw [hΘfst, hsite1, Functor.map_comp, ← Category.assoc pbB.isoPullback.inv,
      pbB.isoPullback_inv_fst]
  have hΘ2 : Θ.hom ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f) ≫
        (BigFppfOver.toScheme B S hS).map p =
      pullback.snd ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map f) := by
    rw [← Category.assoc, hΘsnd, Category.assoc, ← Functor.map_comp (BigFppfOver.toScheme B S hS)
      (θ.hom ≫ pullback.snd (pullback.snd f f) p) p, hsite2, Functor.map_comp,
      pbB.isoPullback_inv_snd]
  have hΘ3 : ChartRel q (Θ.hom ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f))
      (pullback.fst ((BigFppfOver.toScheme B S hS).map p ≫ (BigFppfOver.toScheme B S hS).map f)
        ((BigFppfOver.toScheme B S hS).map f)) := by
    refine ⟨?_, fun Z' z s₁ s₂ h₁ h₂ ↦ ?_⟩
    · have h := congrArg (· ≫ (BigFppfOver.toScheme B S hS).map f ≫
        B.inclusion.map T.hom) hΘ2
      simp only [Category.assoc] at h ⊢
      rw [hπV, h, ← pullback.condition_assoc, Category.assoc]
    · obtain ⟨t, ht⟩ := exists_hom_of_toScheme (z ≫ pbB.isoPullback.inv) (by
        rw [← toScheme_map_comp_structure (pullback.fst p (pullback.fst f f)), Category.assoc,
          ← Category.assoc pbB.isoPullback.inv, pbB.isoPullback_inv_fst, ← Category.assoc, ← h₂]
        exact toScheme_map_comp_structure s₂)
      have hs₂ : s₂ = t ≫ pullback.fst p (pullback.fst f f) := by
        refine (BigFppfOver.toScheme B S hS).map_injective ?_
        rw [h₂, Functor.map_comp, ht, Category.assoc, pbB.isoPullback_inv_fst]
      have hs₁ : s₁ = t ≫ θ.hom ≫ pullback.snd (pullback.snd f f) p := by
        refine (BigFppfOver.toScheme B S hS).map_injective ?_
        rw [h₁, hΘsnd, Functor.map_comp (BigFppfOver.toScheme B S hS) t, ht, Category.assoc]
      rw [hs₁, hs₂, Functor.map_comp, Category.assoc, hθq, ← Category.assoc,
        ← Functor.map_comp]
  -- the triple product on which the cocycle condition lives is a scheme of the site
  have hP₁ : IsPullback
      (prod.fst : (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶ _).left
      (prod.snd : (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶ _).left
      ((BigFppfOver.toScheme B S hS).map (p ≫ f)) ((BigFppfOver.toScheme B S hS).map f) := by
    rw [Functor.map_comp]
    exact Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
      (prodIsProd _ _)
  obtain ⟨Z₁, e₁, m₁, m₂, -, he₂⟩ := exists_iso_of_isPullback_toScheme (p ≫ f) f hP₁
  have hP₂ : IsPullback
      ((prod.fst : ((Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map f)) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶ _).left ≫ e₁.inv)
      (prod.snd : ((Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map f)) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶ _).left
      ((BigFppfOver.toScheme B S hS).map (m₂ ≫ f)) ((BigFppfOver.toScheme B S hS).map f) := by
    refine (Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
      (prodIsProd _ _)).of_iso (Iso.refl _)
      e₁.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
    rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Functor.map_comp, ← he₂, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact (Over.w (prod.snd : (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶ _)).symm
  obtain ⟨Z₂, e₂, n₁, n₂, -, hn₂⟩ := exists_iso_of_isPullback_toScheme (m₂ ≫ f) f hP₂
  have hext : ∀ a₁ a₂ : ((Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
        (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
        Over.mk ((BigFppfOver.toScheme B S hS).map f)) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶
        (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)),
      ChartRel q a₁.left a₂.left →
        a₁.left ≫ (BigFppfOver.toScheme B S hS).map p =
          a₂.left ≫ (BigFppfOver.toScheme B S hS).map p → a₁ = a₂ := by
    intro a₁ a₂ hR hp
    have hlift : ∀ a : ((Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map f)) ⨯
            Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶
          (Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
            (Over.mk ((BigFppfOver.toScheme B S hS).map p)),
        ∃ s : Z₂ ⟶ V, (BigFppfOver.toScheme B S hS).map s = e₂.hom ≫ a.left := by
      intro a
      refine exists_hom_of_toScheme _ ?_
      have ha : a.left ≫ ((BigFppfOver.toScheme B S hS).map p ≫
          (BigFppfOver.toScheme B S hS).map f) = _ := Over.w a
      have hsn : (prod.snd : ((Over.map ((BigFppfOver.toScheme B S hS).map f)).obj
          (Over.mk ((BigFppfOver.toScheme B S hS).map p)) ⨯
          Over.mk ((BigFppfOver.toScheme B S hS).map f)) ⨯
            Over.mk ((BigFppfOver.toScheme B S hS).map f) ⟶ _).left ≫
          (BigFppfOver.toScheme B S hS).map f = _ := Over.w _
      rw [hπV, ← Category.assoc ((BigFppfOver.toScheme B S hS).map p), Category.assoc,
        ← Category.assoc a.left, ha, ← hsn]
      simp only [← Category.assoc]
      rw [hn₂]
      simp only [Category.assoc, toScheme_map_comp_structure]
    obtain ⟨s₁, hs₁⟩ := hlift a₁
    obtain ⟨s₂, hs₂⟩ := hlift a₂
    have hsp : s₁ ≫ p = s₂ ≫ p := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, Functor.map_comp, hs₁, hs₂, Category.assoc, Category.assoc, hp]
    have hs : s₁ = s₂ := (fppfYoneda B S hS).map_injective
      (sq.hom_ext (hR.2 Z₂ e₂.hom s₁ s₂ hs₁ hs₂)
        (by rw [← Functor.map_comp, ← Functor.map_comp, hsp]))
    refine Over.OverMorphism.ext ?_
    rw [← cancel_epi e₂.hom, ← hs₁, ← hs₂, hs]
  -- the descent datum and its effectivity, Stacks 0APK
  obtain ⟨φ, hco, hinv⟩ := exists_transition_of_pullbackIso_of_rel
    ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map p)
    (fun a₁ a₂ ↦ ChartRel q a₁ a₂) (fun k _ _ h ↦ h.comp q k) (fun _ _ h ↦ h.symm q)
    (fun _ _ _ h h' ↦ h.trans q h') Θ hΘ1 hΘ2 hΘ3 hext
  let D : DescentDatum ((BigFppfOver.toScheme B S hS).map f) :=
    DescentDatum.mk' (Over.mk ((BigFppfOver.toScheme B S hS).map p)) φ hco
  have hEff : DescentData.IsEffective D :=
    DescentDatum.isEffective_of_isIndQuasiAffineHom_of_quasiCompact D
      (isIndQuasiAffineHom_of_etale_of_isSeparated _ hps hpe)
  obtain ⟨W₀, w₀, α₀, hα₀, hrel⟩ := DescentData.exists_descent_of_isEffective_of_rel D
    (fun a₁ a₂ ↦ ChartRel q a₁ a₂) (fun v x ↦ hinv v x) hEff
  -- the descended scheme is an object of the site
  have hW₀ : B.Contains W₀ := BigFppfOver.contains_of_iso_pullback f hfs hff α₀
  let Wleft : B.Schemes := B.obj hW₀
  let w₀' : Wleft ⟶ T.left := B.inclusion.preimage w₀
  let W : BigFppfOver B S hS := Over.mk (w₀' ≫ T.hom)
  let w : W ⟶ T := Over.homMk w₀'
  have hwmap : (BigFppfOver.toScheme B S hS).map w = w₀ :=
    B.inclusion.map_preimage (X := Wleft) (Y := T.left) w₀
  have hPB : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst f w))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f w))
      ((BigFppfOver.toScheme B S hS).map f) w₀ := by
    rw [← hwmap]
    exact (IsPullback.of_hasPullback f w).map (BigFppfOver.toScheme B S hS)
  let e : (BigFppfOver.toScheme B S hS).obj (pullback f w) ≅
      pullback ((BigFppfOver.toScheme B S hS).map f) w₀ := hPB.isoPullback
  let β : (BigFppfOver.toScheme B S hS).obj (pullback f w) ≅
      (BigFppfOver.toScheme B S hS).obj V := e ≪≫ α₀
  have hβeq : β.hom = e.hom ≫ α₀.hom := rfl
  have hβ : β.hom ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map (pullback.fst f w) := by
    rw [hβeq, Category.assoc]
    change e.hom ≫ α₀.hom ≫ D.over.hom = _
    rw [hα₀]
    exact hPB.isoPullback_hom_fst
  let βS : (pullback f w).left ≅ V.left := B.inclusion.preimageIso β
  have hβS : B.inclusion.map βS.hom = β.hom := B.inclusion.map_preimage _
  have hleft : βS.hom ≫ p.left = (pullback.fst f w).left :=
    B.inclusion.map_injective (by rwa [Functor.map_comp, hβS])
  let α : pullback f w ≅ V := Over.isoMk βS (by
    rw [← Over.w p, ← Category.assoc, hleft, Over.w])
  have hαmap : (BigFppfOver.toScheme B S hS).map α.hom = β.hom := hβS
  have hαp : α.hom ≫ p = pullback.fst f w :=
    (BigFppfOver.toScheme B S hS).map_injective (by rwa [Functor.map_comp, hαmap])
  -- the invariance of `T' ×_T W ≅ V ⟶ U`, read in the site
  set k : pullback f w ⟶ W := pullback.snd f w with hk
  set m : pullback ((BigFppfOver.toScheme B S hS).map f) w₀ ⟶ W₀ :=
    pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀ with hm
  have hek : e.hom ≫ m = (BigFppfOver.toScheme B S hS).map k := hPB.isoPullback_hom_snd
  have hkk : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst k k))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd k k))
      ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map k) :=
    (IsPullback.of_hasPullback k k).map (BigFppfOver.toScheme B S hS)
  have hmm : IsPullback
      ((BigFppfOver.toScheme B S hS).map (pullback.fst k k) ≫ e.hom)
      ((BigFppfOver.toScheme B S hS).map (pullback.snd k k) ≫ e.hom) m m :=
    hkk.of_iso (Iso.refl _) e e (Iso.refl _) (by simp) (by simp)
      (by simpa using hek.symm) (by simpa using hek.symm)
  let d : (BigFppfOver.toScheme B S hS).obj (pullback k k) ≅ pullback m m := hmm.isoPullback
  have hd₁ : d.hom ≫ pullback.fst m m =
      (BigFppfOver.toScheme B S hS).map (pullback.fst k k) ≫ e.hom := hmm.isoPullback_hom_fst
  have hd₂ : d.hom ≫ pullback.snd m m =
      (BigFppfOver.toScheme B S hS).map (pullback.snd k k) ≫ e.hom := hmm.isoPullback_hom_snd
  have hqinv : (fppfYoneda B S hS).map (pullback.snd k k ≫ α.hom) ≫ q =
      (fppfYoneda B S hS).map (pullback.fst k k ≫ α.hom) ≫ q := by
    refine hrel.2 (pullback k k) d.hom _ _ ?_ ?_
    · rw [Functor.map_comp, hαmap, hβeq, ← Category.assoc, ← hd₂, Category.assoc]
    · rw [Functor.map_comp, hαmap, hβeq, ← Category.assoc, ← hd₁, Category.assoc]
  -- `k` is surjective, flat and quasi-compact, so `U` satisfies the sheaf condition for it
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst f w))
      ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map w) :=
    (IsPullback.of_hasPullback f w).map (BigFppfOver.toScheme B S hS)
  have hbc : ∀ {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange],
      P ((BigFppfOver.toScheme B S hS).map f) → P ((BigFppfOver.toScheme B S hS).map k) :=
    fun h ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq h
  have : Surjective ((BigFppfOver.toScheme B S hS).map k) := hbc hfs
  have : Flat ((BigFppfOver.toScheme B S hS).map k) := hbc hff
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map k) := hbc hfq
  have hR : Presieve.singleton k ∈
      Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) W := by
    rw [Precoverage.mem_comap_iff, ← Presieve.ofArrows_pUnit.{0}, Presieve.map_ofArrows,
      Presieve.ofArrows_pUnit]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage _
  have hUk : Presieve.IsSheafFor U.obj (Presieve.singleton k) :=
    (Presieve.isSheafFor_iff_generate _).2
      (((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqc_of_isAffineFormalAlgebraicSpace hU)) _
        (Precoverage.generate_mem_toGrothendieck hR))
  -- the descent of `T' ×_T W ≅ V ⟶ U` along `k`, Stacks 023Q
  set b' : (fppfYoneda B S hS).obj (pullback f w) ⟶ U :=
    (fppfYoneda B S hS).map α.hom ≫ q with hb'
  obtain ⟨t, ht, -⟩ := Presieve.isSheafFor_singleton.mp hUk
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) b') fun {Z} p₁ p₂ hp ↦ by
      rw [← Sheaf.sectionEquiv_map_comp, ← Sheaf.sectionEquiv_map_comp]
      congr 1
      obtain ⟨l, hl₁, hl₂⟩ : ∃ l : Z ⟶ pullback k k,
          l ≫ pullback.fst k k = p₁ ∧ l ≫ pullback.snd k k = p₂ :=
        ⟨pullback.lift p₁ p₂ hp, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
      have h := congrArg ((fppfYoneda B S hS).map l ≫ ·) hqinv
      rw [hb', ← hl₁, ← hl₂]
      simp only [Functor.map_comp, Category.assoc] at h ⊢
      exact h.symm
  set b : (fppfYoneda B S hS).obj W ⟶ U :=
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm t with hbdef
  have hb : (fppfYoneda B S hS).map k ≫ b = b' := by
    refine (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective ?_
    rw [Sheaf.sectionEquiv_map_comp, hbdef, Equiv.apply_symm_apply, ht]
  refine ⟨W, w, b ≫ u, ?_, ?_, ?_⟩
  · -- étaleness descends along `f`, Stacks 02VN
    have : IsZariskiLocalAtTarget (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Etale)
    have hfstet : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst f w)) := by
      rw [← hαp, Functor.map_comp]
      infer_instance
    have hQf : (@Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        ((BigFppfOver.toScheme B S hS).map f) := ⟨⟨hfs, hff⟩, hfq⟩
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
      (Q := (@Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      hsq hQf hfstet
  · rw [← Category.assoc, hb, hb', Category.assoc, sq.w, ← Category.assoc, ← Functor.map_comp,
      hαp]
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map k ((BigFppfOver.toScheme B S hS).map α.inv v), ?_⟩
    have hv : (BigFppfOver.toScheme B S hS).map (pullback.fst f w)
        ((BigFppfOver.toScheme B S hS).map α.inv v) = (BigFppfOver.toScheme B S hS).map p v := by
      rw [← hαp, ← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Category.assoc,
        Iso.inv_hom_id, Category.id_comp]
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← pullback.condition, Functor.map_comp,
      Scheme.Hom.comp_apply, hv]

end AlgebraicGeometry.FormalSpace

end
