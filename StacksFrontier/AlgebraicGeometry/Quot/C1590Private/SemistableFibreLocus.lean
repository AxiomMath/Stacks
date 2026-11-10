module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RationalTailIso

/-!
# The semistable fibre locus of a prestable family of curves

Let `f : X → S` be a prestable family of curves. Its *semistable fibre locus* is the set of points
`s ∈ S` whose fibre `X_s` has genus at least one and no rational tail. The proof of Stacks 0E70
says that the formation of this locus commutes with arbitrary base change, "because the
(non)existence of rational tails is insensitive to ground field extensions by Algebraic Curves,
Lemma 0E3L". This file proves that compatibility:

* over a field, for a prestable curve `V` over `k` and a field extension `K/k`, the curve `V` has
  genus at least one and no rational tail exactly when `V_K` has
  (`AlgebraicGeometry.C1590Private.hasPositiveGenusNoRationalTail_iff_of_isPullback`): the genus is
  invariant (Stacks 0BY9), a curve without rational tail has none after base change (the field
  extension part of Stacks 0E3L), and a rational tail `C ⊂ V` gives the nonempty disjoint union
  `C_K` of rational tails of `V_K` (Stacks 0E3I);
* for a prestable family, whether the fibre at a field-valued point of the base has genus at least
  one and no rational tail depends only on the underlying point of the base scheme
  (`AlgebraicGeometry.C1590Private.hasSemistableFibreAt_iff_of_schemePoint_eq`);
* hence the semistable fibre locus of a family mapping to a prestable family is the inverse image
  of the locus of the target (`AlgebraicGeometry.C1590Private.semistableFibreLocus_eq_preimage`),
  and a family mapping to a prestable family `G` has semistable fibres exactly when its morphism
  of bases lands in the semistable fibre locus of `G`
  (`AlgebraicGeometry.C1590Private.hasSemistableFibres_iff_range_subset`).

Consequently the input `AlgebraicGeometry.C1590Private.PrestableSemistableFibresOpen` of
`StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen` is the openness of the
semistable fibre locus of every prestable family
(`AlgebraicGeometry.C1590Private.prestableSemistableFibresOpen_of_isOpen`).

## Main definitions

* `AlgebraicGeometry.C1590Private.HasSemistableFibreAt`: the fibre at a field-valued point has
  genus at least one and no rational tail.
* `AlgebraicGeometry.C1590Private.semistableFibreLocus`: the points of the base whose fibre has
  genus at least one and no rational tail.

## References

* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3I](https://stacks.math.columbia.edu/tag/0E3I)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

/-! ### Over a field -/

/-- **Genus at least one and no rational tail is insensitive to ground field extensions.** Let `V`
be a proper scheme of dimension one over a field `k` with `H⁰(V, 𝒪_V) = k` and at-worst-nodal
singularities, and let `W` be its base change along a field extension `φ : k → K`. Then `W` has
genus at least one and no rational tail over `K` exactly when `V` has over `k`.

The genus is invariant under extension of the ground field (Stacks 0BY9). If `V` has positive
genus and no rational tail then `V_K` has none (Stacks 0E3L); conversely the base change of a
rational tail `C ⊂ V` is a finite disjoint union of rational tails of `V_K` (Stacks 0E3I), which
is nonempty since `V_K → V` is surjective. -/
theorem hasPositiveGenusNoRationalTail_iff_of_isPullback {k K : Type u} [Field k] [Field K]
    (φ : k →+* K) {V W : Scheme.{u}} (a : W ⟶ V) (w : W ⟶ Spec (.of K)) (fV : V ⟶ Spec (.of k))
    (h : IsPullback a w fV (Spec.map (CommRingCat.ofHom φ))) [IsProper fV]
    (hdim : topologicalKrullDim V = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fV.appTop)]
    (hnodal : letI : V.Over (Spec (.of k)) := ⟨fV⟩
      Stacks.Curves.HasAtWorstNodalSingularities k V) :
    HasPositiveGenusNoRationalTail K w ↔ HasPositiveGenusNoRationalTail k fV := by
  let : Algebra k K := φ.toAlgebra
  set g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have h' : IsPullback a w fV g := h
  have hgen : genus w = genus fV := genus_eq_of_isPullback k K φ a w fV h
  change (1 ≤ genus w ∧ _) ↔ (1 ≤ genus fV ∧ _)
  rw [hgen]
  refine and_congr_right fun hg => ?_
  let : V.Over (Spec (.of k)) := ⟨fV⟩
  let : W.Over (Spec (.of K)) := ⟨w⟩
  let : (pullback fV g).Over (Spec (.of K)) := ⟨pullback.snd fV g⟩
  have : IsProper (V ↘ Spec (.of k)) := inferInstanceAs (IsProper fV)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (V ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fV.appTop))
  have : IsProper (pullback fV g ↘ Spec (.of K)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback fV g)
      (inferInstanceAs (IsProper fV))
  have hiso := forall_not_isRationalTail_iff_of_isIso (k := K) h'.isoPullback.hom
    h'.isoPullback_hom_snd
  refine ⟨fun hW C hC => ?_,
    fun hV => hiso.1 (forall_not_isRationalTail_baseChange k K fV hdim hnodal hV hg)⟩
  obtain ⟨ι, _, D, hD, e, -⟩ :=
    exists_iso_sigma_isRationalTail_baseChange k K V hdim hnodal C hC
  have : IsIntegral C.subscheme := hC.isIntegral
  obtain ⟨c⟩ : Nonempty C.subscheme := inferInstance
  obtain ⟨y₀⟩ : Nonempty (Spec (.of K)) := inferInstance
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (C.subschemeι c) y₀
    (Subsingleton.elim (α := Spec (.of k)) _ _)
  have hmem : y ∈ (C.comap (pullback.fst fV g)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change pullback.fst fV g y ∈ (C.support : Set V)
    rw [hy, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨c, rfl⟩
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι] at hmem
  obtain ⟨x, -⟩ := hmem
  exact hiso.2 hW (D ((sigmaMk _).symm (e.inv x)).1) (hD _)

/-! ### Fibres of a prestable family at field-valued points -/

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Presentations of the fibres at a point and at an extension of it form a cartesian square of
schemes.** Let `r` be a field-valued point of the base of a family of curves which is the
restriction of a field-valued point `p` along a morphism `f` of field spectra, and let `V`, `W`
present the fibres at `p` and `r`. Then `W` is the base change of `V` along `f`. -/
theorem exists_isPullback_toScheme_of_dominates (X : CurveFamily B hZ)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ r.siteObject) (q' : yoneda.obj W ⟶ X.total.obj)
    (hW : IsPullback q' (yoneda.map w) X.toBase.hom (yonedaEquiv.symm r.value)) :
    ∃ l : (BigFppfOver.toScheme B integerBase hZ).obj W ⟶
        (BigFppfOver.toScheme B integerBase hZ).obj V,
      IsPullback l ((BigFppfOver.toScheme B integerBase hZ).map w)
        ((BigFppfOver.toScheme B integerBase hZ).map v)
        (Spec.map (CommRingCat.ofHom
          (Spec.preimage ((BigFppfOver.toScheme B integerBase hZ).map f)).hom)) := by
  set F := BigFppfOver.toScheme B integerBase hZ
  have hr : yonedaEquiv.symm r.value = yoneda.map f ≫ yonedaEquiv.symm p.value := by
    rw [← hf, yonedaEquiv_symm_map]
    rfl
  let l : yoneda.obj W ⟶ yoneda.obj V :=
    hV.lift q' (yoneda.map (w ≫ f)) (by rw [hW.w, hr, Functor.map_comp, Category.assoc])
  have hl₁ : l ≫ q = q' := hV.lift_fst _ _ _
  have hl₂ : l ≫ yoneda.map v = yoneda.map (w ≫ f) := hV.lift_snd _ _ _
  have hsq : IsPullback l (yoneda.map w) (yoneda.map v) (yoneda.map f) := by
    refine IsPullback.of_right (h₁₂ := q) (h₂₂ := yonedaEquiv.symm p.value)
      (v₁₃ := X.toBase.hom) ?_ (by rw [hl₂, Functor.map_comp]) hV
    rw [hl₁, ← hr]
    exact hW
  let l₀ : W ⟶ V := Yoneda.fullyFaithful.preimage l
  have hsq₀ : IsPullback l₀ w v f :=
    IsPullback.of_map_of_faithful yoneda (by rwa [Yoneda.fullyFaithful.map_preimage])
  have : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, BigFppfOver.toScheme]
    infer_instance
  have hsqS := hsq₀.map F
  have hFf : F.map f = Spec.map (CommRingCat.ofHom (Spec.preimage (F.map f)).hom) := by simp
  exact ⟨F.map l₀, hFf ▸ hsqS⟩

/-- **The semistable fibre condition is insensitive to extension of the field of the point.** For
a prestable family of curves and presentations `V`, `W` of its fibres at a field-valued point `p`
and at an extension `r` of it, `W` has genus at least one and no rational tail exactly when `V`
has. -/
theorem hasPositiveGenusNoRationalTail_iff_of_dominates {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ r.siteObject) (q' : yoneda.obj W ⟶ X.total.obj)
    (hW : IsPullback q' (yoneda.map w) X.toBase.hom (yonedaEquiv.symm r.value)) :
    HasPositiveGenusNoRationalTail r.carrier ((BigFppfOver.toScheme B integerBase hZ).map w) ↔
      HasPositiveGenusNoRationalTail p.carrier ((BigFppfOver.toScheme B integerBase hZ).map v) := by
  obtain ⟨l, hl⟩ := exists_isPullback_toScheme_of_dominates X f hf v q hV w q' hW
  obtain ⟨hprop, hdim, hΓ, hnodal⟩ := fibre_properties_of_isPrestableCurveFamily hX p v q hV
  exact hasPositiveGenusNoRationalTail_iff_of_isPullback _ l _ _ hl hdim hnodal

/-- The fibre of a family of curves at a field-valued point of its base has genus at least one and
no rational tail. -/
abbrev HasSemistableFibreAt (X : CurveFamily B hZ)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) : Prop :=
  X.HasFibreSatisfying B hZ (fun k _ _ f => HasPositiveGenusNoRationalTail k f) p

/-- The semistable fibre condition passes from a point of the base of a prestable family to every
extension of it. -/
theorem HasSemistableFibreAt.of_dominates {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    (h : HasSemistableFibreAt X p) : HasSemistableFibreAt X r := by
  obtain ⟨V, v, q, hV, hP⟩ := h
  obtain ⟨W, w, q', hW⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X r
  exact ⟨W, w, q', hW,
    (hasPositiveGenusNoRationalTail_iff_of_dominates hX f hf v q hV w q' hW).2 hP⟩

/-- The semistable fibre condition passes from an extension of a point of the base of a prestable
family to the point. -/
theorem HasSemistableFibreAt.of_dominated {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (f : r.siteObject ⟶ p.siteObject) (hf : (schemeSpace X.base).obj.map f.op p.value = r.value)
    (h : HasSemistableFibreAt X r) : HasSemistableFibreAt X p := by
  obtain ⟨W, w, q', hW, hP⟩ := h
  obtain ⟨V, v, q, hV⟩ := exists_isPullback_yoneda_fieldValuedPoint B hZ X p
  exact ⟨V, v, q, hV, (hasPositiveGenusNoRationalTail_iff_of_dominates hX f hf v q hV w q' hW).1 hP⟩

/-- **The semistable fibre condition depends only on the underlying point of the base.** For a
prestable family of curves, the fibres at two field-valued points of the base with the same
underlying point both have, or both fail to have, genus at least one and no rational tail: the
two points have a common extension. -/
theorem hasSemistableFibreAt_iff_of_schemePoint_eq {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    {p r : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    (h : Space.schemePoint B integerBase hZ X.base p =
      Space.schemePoint B integerBase hZ X.base r) :
    HasSemistableFibreAt X p ↔ HasSemistableFibreAt X r := by
  obtain ⟨s, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
    Space.hasCommonExtension_of_schemePoint_eq B integerBase hZ X.base h
  exact ⟨fun hp => (hp.of_dominates hX f₁ hf₁).of_dominated hX f₂ hf₂,
    fun hr => (hr.of_dominates hX f₂ hf₂).of_dominated hX f₁ hf₁⟩

/-! ### The semistable fibre locus -/

/-- The *semistable fibre locus* of a family of curves: the points of the base whose fibre has
genus at least one and no rational tail. -/
def semistableFibreLocus (X : CurveFamily B hZ) :
    Set ((BigFppfOver.toScheme B integerBase hZ).obj X.base) :=
  {x | HasSemistableFibreAt X (X.residueFieldPoint x)}

/-- For a prestable family, a field-valued point of the base lies over the semistable fibre locus
exactly when the fibre there has genus at least one and no rational tail. -/
theorem schemePoint_mem_semistableFibreLocus_iff {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj) :
    Space.schemePoint B integerBase hZ X.base p ∈ semistableFibreLocus X ↔
      HasSemistableFibreAt X p :=
  hasSemistableFibreAt_iff_of_schemePoint_eq hX (by simp)

/-- **The formation of the semistable fibre locus commutes with base change.** For a morphism of
families of curves `X ⟶ Y` with `Y` prestable, the semistable fibre locus of `X` is the inverse
image of that of `Y` along the morphism of bases. -/
theorem semistableFibreLocus_eq_preimage {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsPrestableCurveFamily B hZ Y) :
    semistableFibreLocus X =
      (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap ⁻¹' semistableFibreLocus Y := by
  ext x
  change HasSemistableFibreAt X _ ↔ HasSemistableFibreAt Y _
  refine (CurveFamily.hasFibreSatisfying_map_iff φ _).symm.trans
    (hasSemistableFibreAt_iff_of_schemePoint_eq hY ?_)
  rw [CurveFamily.schemePoint_residueFieldPoint]
  exact (Space.schemePoint_map_yoneda B integerBase hZ φ.baseMap _).trans
    (congrArg _ (CurveFamily.schemePoint_residueFieldPoint X x))

/-- For a prestable family, all fibres have genus at least one and no rational tail exactly when
the semistable fibre locus is the whole base. -/
theorem hasSemistableFibres_iff_semistableFibreLocus_eq_univ {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) :
    HasSemistableFibres B hZ X ↔ semistableFibreLocus X = Set.univ :=
  ⟨fun h => Set.eq_univ_of_forall fun _ => h _, fun h p =>
    (schemePoint_mem_semistableFibreLocus_iff hX p).1 (h ▸ Set.mem_univ _)⟩

/-- **A family mapping to a prestable family `Y` has semistable fibres exactly when its morphism
of bases lands in the semistable fibre locus of `Y`.** -/
theorem hasSemistableFibres_iff_range_subset {X Y : CurveFamily B hZ} (φ : X ⟶ Y)
    (hY : IsPrestableCurveFamily B hZ Y) :
    HasSemistableFibres B hZ X ↔
      Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ⊆
        semistableFibreLocus Y := by
  rw [hasSemistableFibres_iff_semistableFibreLocus_eq_univ
      (CurveFamily.isPrestableCurveFamily_of_hom φ hY),
    semistableFibreLocus_eq_preimage φ hY, Set.range_subset_iff, Set.eq_univ_iff_forall]
  rfl

variable (B hZ) in
/-- **The input `PrestableSemistableFibresOpen` is the openness of the semistable fibre locus.**
If the semistable fibre locus of every prestable family of curves is open, then
`AlgebraicGeometry.C1590Private.PrestableSemistableFibresOpen` holds, with the semistable fibre
locus as the open set. -/
theorem prestableSemistableFibresOpen_of_isOpen
    (h : ∀ G : CurveFamily B hZ, IsPrestableCurveFamily B hZ G → IsOpen (semistableFibreLocus G)) :
    PrestableSemistableFibresOpen B hZ :=
  fun G hG => ⟨semistableFibreLocus G, h G hG, fun _ a => hasSemistableFibres_iff_range_subset a hG⟩

end AlgebraicGeometry.C1590Private

end
