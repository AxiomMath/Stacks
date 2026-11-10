module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity

/-!
# The closed substack cut out by an invariant closed subspace of a chart

Let `𝒳` be an algebraic stack over `S`, let `f : (Sch/S)/W₀ ⟶ 𝒳` be a 1-morphism from the
category represented by a scheme `W₀` of the site, and let `Z` be a closed subspace of `W₀`
(**Stacks 02YU**, part (4)). Call an object `x` of `𝒳` *in the locus of `Z`* when every object
`a : T ⟶ W₀` of the chart with a morphism `f a ⟶ x` factors through `Z`. This file shows that the
locus is a **closed substack** of `𝒳` (**Stacks 04YM**, part (2)) as soon as `Z` is invariant for
the chart — two objects of the chart whose images in `𝒳` are related by a morphism lying over `g`
either both factor through `Z` after restriction along `g`, or neither does — and the chart is
locally essentially surjective. Under that invariance an object of the chart lies in the locus
exactly when it factors through `Z`.

This is the existence half of the correspondence of **Stacks 0507** between closed substacks of
`𝒳` and invariant closed subspaces of a presentation, in the form in which the proof of
**Stacks 0509** uses it.

## Main definitions

* `AlgebraicGeometry.Stack.chartLocus`: the locus of `Z` in `𝒳`.
* `AlgebraicGeometry.Stack.IsChartInvariant`: the invariance of `Z` for the chart.
* `AlgebraicGeometry.Stack.chartLocusSubfunctor`: the subfunctor of `yoneda V` of the morphisms
  along which an object over `V` restricts into the locus.

## Main results

* `AlgebraicGeometry.Stack.chartLocus_obj_iff`: an object of the chart is in the locus exactly
  when it factors through `Z`.
* `AlgebraicGeometry.Stack.isClosedSubstack_chartLocus`: the locus is a closed substack.

## Implementation notes

The base change of the inclusion of the locus along a scheme-valued point is the subfunctor
`AlgebraicGeometry.Stack.chartLocusSubfunctor` of the object of the site the point lies over,
read on the site of that object. Locally on a covering sieve supplied by the local essential
surjectivity of the chart, that subfunctor is the inverse image of `Z` along a morphism to `W₀`
(`AlgebraicGeometry.Stack.preimage_chartLocusSubfunctor`), hence is represented by a closed
immersion; effective fppf descent of closed immersions along covering sieves,
`AlgebraicGeometry.FormalSpace.presheafIsClosedImmersion_of_coveringSieve`, then represents it by
a closed immersion globally. The closed-substack criterion of
`StacksFrontier/AlgebraicGeometry/Stacks/FullSubcategoryBaseChangeClosed.lean` finishes.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {W₀ : BigFppfOver B S hS}
  (f : (schemeFibredCategory B S hS W₀).val ⥤ᵇ 𝒳.val.val)
  (Z : Subfunctor (yoneda.obj W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))

/-- **The locus of a subspace of a chart.** An object `x` of `𝒳` is in the locus of `Z` when every
object `a : T ⟶ W₀` of the chart with a morphism `f a ⟶ x` factors through `Z`. -/
def chartLocus : ObjectProperty 𝒳.val.val.obj :=
  fun x => ∀ (a : Over W₀) (_ : f.obj a ⟶ x), a.hom ∈ Z.obj (op a.left)

/-- The locus of a subspace of a chart is inherited along morphisms. -/
theorem chartLocus_of_hom {x y : 𝒳.val.val.obj} (g : x ⟶ y) (hy : chartLocus f Z y) :
    chartLocus f Z x :=
  fun a φ => hy a (φ ≫ g)

/-- **Invariance of a subspace of a chart.** If the images in `𝒳` of two objects `a` and `b` of the
chart are related by a morphism lying over `g : a ⟶ b` of the site, and `b` restricted along `g`
factors through `Z`, then `a` factors through `Z`. -/
def IsChartInvariant : Prop :=
  ∀ (a b : Over W₀) (φ : f.obj a ⟶ f.obj b) (g : a.left ⟶ b.left),
    𝒳.val.val.p.IsHomLift g φ → g ≫ b.hom ∈ Z.obj (op a.left) → a.hom ∈ Z.obj (op a.left)

/-- **Local essential surjectivity of a chart.** Every object of `𝒳` lying over `V` receives,
over the members of some covering sieve of `V`, a morphism from the image of an object of the
chart. -/
def IsChartLocallyEssSurj : Prop :=
  ∀ (V : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber V),
    ∃ R ∈ BigFppfOver.topology B S hS V,
      ∀ ⦃V' : BigFppfOver B S hS⦄ ⦃k : V' ⟶ V⦄, R.arrows k →
        ∃ (z : Over W₀) (φ : f.obj z ⟶ y.1), 𝒳.val.val.p.IsHomLift k φ

variable {f Z}

/-- The morphism of the chart from the restriction of an object along a morphism of the site lies
over that morphism. -/
theorem isHomLift_overHomMk (b : Over W₀) {T : BigFppfOver B S hS} (g : T ⟶ b.left) :
    (schemeFibredCategory B S hS W₀).val.p.IsHomLift g
      (Over.homMk g rfl : Over.mk (g ≫ b.hom) ⟶ b) :=
  IsHomLift.map (Over.forget W₀) (Over.homMk g rfl : Over.mk (g ≫ b.hom) ⟶ b)

/-- A morphism of the total category between objects over `A` and `B` lies over some `A ⟶ B`. -/
private theorem exists_isHomLift_of_obj_eq {u v : 𝒳.val.val.obj} {A B : BigFppfOver B S hS}
    (hu : 𝒳.val.val.p.obj u = A) (hv : 𝒳.val.val.p.obj v = B) (φ : u ⟶ v) :
    ∃ g : A ⟶ B, 𝒳.val.val.p.IsHomLift g φ := by
  subst hu hv
  exact ⟨_, IsHomLift.map _ φ⟩

/-- **An object of the chart is in the locus exactly when it factors through `Z`**, for an
invariant `Z`. -/
theorem chartLocus_obj_iff (hZ : IsChartInvariant f Z) (b : Over W₀) :
    chartLocus f Z (f.obj b) ↔ b.hom ∈ Z.obj (op b.left) := by
  refine ⟨fun h => h b (𝟙 _), fun hb a φ => ?_⟩
  obtain ⟨g, hg⟩ := exists_isHomLift_of_obj_eq (Functor.congr_obj f.w a) (Functor.congr_obj f.w b) φ
  exact hZ a b φ g hg (Z.map g.op hb)

variable (f Z)

/-- **The morphisms along which an object restricts into the locus.** For an object `x` of `𝒳`
lying over `V`, the subfunctor of `yoneda V` whose sections over `T` are the morphisms `g : T ⟶ V`
such that every object `a` of the chart with a morphism `f a ⟶ x` lying over `h ≫ g` for some
`h : a ⟶ T` factors through `Z`. -/
def chartLocusSubfunctor {V : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber V) :
    Subfunctor (yoneda.obj V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj T := {g | ∀ (a : Over W₀) (h : a.left ⟶ T.unop) (φ : f.obj a ⟶ x.1),
    𝒳.val.val.p.IsHomLift (h ≫ g) φ → a.hom ∈ Z.obj (op a.left)}
  map {T T'} k g hg a h φ hφ := hg a (h ≫ k.unop) φ (by simpa using hφ)

variable {f Z}

/-- **Membership in the locus, read on the subfunctor.** For a morphism `φ₀ : w ⟶ x` of `𝒳` lying
over `g : T ⟶ V`, the object `w` is in the locus exactly when `g` is a section of
`AlgebraicGeometry.Stack.chartLocusSubfunctor` at `x`. -/
theorem chartLocus_iff_mem_chartLocusSubfunctor {V T : BigFppfOver B S hS}
    (x : 𝒳.val.val.p.Fiber V) {w : 𝒳.val.val.obj} (g : T ⟶ V) (φ₀ : w ⟶ x.1)
    (hφ₀ : 𝒳.val.val.p.IsHomLift g φ₀) :
    chartLocus f Z w ↔ g ∈ (chartLocusSubfunctor f Z x).obj (op T) := by
  have hfib : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.property
  have hcart : 𝒳.val.val.p.IsStronglyCartesian g φ₀ := hfib.isStronglyCartesian_homLift g φ₀
  refine ⟨fun hw a h φ _ => hw a (Functor.IsStronglyCartesian.map 𝒳.val.val.p g φ₀ (g := h) rfl φ),
    fun hg a φ' => ?_⟩
  obtain ⟨h, hh⟩ := exists_isHomLift_of_obj_eq (A := a.left) (Functor.congr_obj f.w a)
    (IsHomLift.domain_eq _ g φ₀) φ'
  exact hg a h (φ' ≫ φ₀) inferInstance

/-- If `m ≫ e` is a section of the subfunctor at `x` and `φ : f a ⟶ x` lies over `e`, then
`m ≫ a.hom` factors through `Z`. -/
private theorem comp_hom_mem_of_comp_mem_chartLocusSubfunctor {V : BigFppfOver B S hS}
    (x : 𝒳.val.val.p.Fiber V) (a : Over W₀) (e : a.left ⟶ V) (φ : f.obj a ⟶ x.1)
    (hφ : 𝒳.val.val.p.IsHomLift e φ) {T : BigFppfOver B S hS} (m : T ⟶ a.left)
    (hm : m ≫ e ∈ (chartLocusSubfunctor f Z x).obj (op T)) : m ≫ a.hom ∈ Z.obj (op T) := by
  have := isHomLift_overHomMk a m
  have : 𝒳.val.val.p.IsHomLift m (f.map (Over.homMk m rfl : Over.mk (m ≫ a.hom) ⟶ a)) :=
    BasedFunctor.preserves_isHomLift f m _
  exact hm (Over.mk (m ≫ a.hom)) (𝟙 T) (f.map (Over.homMk m rfl) ≫ φ)
    (by simpa using (inferInstance : 𝒳.val.val.p.IsHomLift (m ≫ e)
      (f.map (Over.homMk m rfl : Over.mk (m ≫ a.hom) ⟶ a) ≫ φ)))

/-- **Locally the subfunctor is the inverse image of `Z`.** Let `ζ : f a₀ ⟶ x` lie over
`k : a₀ ⟶ V`. Then for an invariant `Z`, a morphism `g' : T ⟶ a₀` restricts `x` into the locus
along `g' ≫ k` exactly when `g' ≫ a₀` factors through `Z`. -/
theorem comp_mem_chartLocusSubfunctor_iff (hZ : IsChartInvariant f Z) {V : BigFppfOver B S hS}
    (x : 𝒳.val.val.p.Fiber V) (a₀ : Over W₀) (k : a₀.left ⟶ V) (ζ : f.obj a₀ ⟶ x.1)
    (hζ : 𝒳.val.val.p.IsHomLift k ζ) {T : BigFppfOver B S hS} (g' : T ⟶ a₀.left) :
    g' ≫ k ∈ (chartLocusSubfunctor f Z x).obj (op T) ↔ g' ≫ a₀.hom ∈ Z.obj (op T) := by
  have hfib : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.property
  constructor
  · exact fun hg => comp_hom_mem_of_comp_mem_chartLocusSubfunctor x a₀ k ζ hζ g' hg
  · intro hz a h φ hφ
    have : 𝒳.val.val.p.IsStronglyCartesian k ζ := hfib.isStronglyCartesian_homLift k ζ
    exact hZ a a₀ (Functor.IsStronglyCartesian.map 𝒳.val.val.p k ζ (f' := h ≫ g' ≫ k)
      (g := h ≫ g') (by simp) φ) (h ≫ g') inferInstance (by simpa using Z.map h.op hz)

/-- The subfunctor `AlgebraicGeometry.Stack.chartLocusSubfunctor` restricted along a morphism
`k : a₀ ⟶ V` over which `f a₀` maps to `x` is the inverse image of `Z` along `a₀`. -/
theorem preimage_chartLocusSubfunctor (hZ : IsChartInvariant f Z) {V : BigFppfOver B S hS}
    (x : 𝒳.val.val.p.Fiber V) (a₀ : Over W₀) (k : a₀.left ⟶ V) (ζ : f.obj a₀ ⟶ x.1)
    (hζ : 𝒳.val.val.p.IsHomLift k ζ) :
    (chartLocusSubfunctor f Z x).preimage (yoneda.map k) = Z.preimage (yoneda.map a₀.hom) := by
  ext T g'
  exact comp_mem_chartLocusSubfunctor_iff hZ x a₀ k ζ hζ g'

/-- **The subfunctor is a sheaf.** For a closed subspace `Z` of the chart, the subfunctor
`AlgebraicGeometry.Stack.chartLocusSubfunctor` of `yoneda V` is an fppf sheaf: membership in it is
local, because membership in `Z` is. -/
theorem isSheaf_chartLocusSubfunctor (hZc : Space.IsClosedSubspace B S hS Z)
    {V : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber V) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (chartLocusSubfunctor f Z x).toFunctor := by
  have hV := (isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS V)
  have hW := (isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS W₀)
  have hZs := (isSheaf_iff_isSheaf_of_type _ _).1 hZc.1.isSheaf
  refine (isSheaf_iff_isSheaf_of_type _ _).2 (((chartLocusSubfunctor f Z x).isSheaf_iff hV).2 ?_)
  intro T g hg a h φ hφ
  refine (Z.isSheaf_iff hW).1 hZs (op a.left) a.hom ?_
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable h hg)
  intro A' m hm
  exact comp_hom_mem_of_comp_mem_chartLocusSubfunctor x a (h ≫ g) φ hφ m (by simpa using hm)

/-- **The subfunctor is represented by a closed immersion.** For an invariant closed subspace `Z`
of a chart which is locally essentially surjective, the inclusion of
`AlgebraicGeometry.Stack.chartLocusSubfunctor` into `yoneda V` is represented by a closed
immersion of the site: over a covering sieve of `V` it is the inverse image of `Z`
(`AlgebraicGeometry.Stack.preimage_chartLocusSubfunctor`), and closed immersions descend
effectively along covering sieves. -/
theorem closedImmersionPresheafProperty_chartLocusSubfunctor (hZ : IsChartInvariant f Z)
    (hZc : Space.IsClosedSubspace B S hS Z) {V : BigFppfOver B S hS} (x : 𝒳.val.val.p.Fiber V)
    (hloc : ∃ R ∈ BigFppfOver.topology B S hS V,
      ∀ ⦃V' : BigFppfOver B S hS⦄ ⦃k : V' ⟶ V⦄, R.arrows k →
        ∃ (z : Over W₀) (φ : f.obj z ⟶ x.1), 𝒳.val.val.p.IsHomLift k φ) :
    Space.closedImmersionPresheafProperty B S hS (chartLocusSubfunctor f Z x).ι := by
  obtain ⟨R, hR, hlift⟩ := hloc
  refine FormalSpace.presheafIsClosedImmersion_of_coveringSieve B S hS
    (isSheaf_chartLocusSubfunctor hZc x) _ hR (fun V' q hq => ?_)
  obtain ⟨z, φ, hφ⟩ := hlift hq
  have hz : z.left = V' :=
    (Functor.congr_obj f.w z).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p q φ)
  subst hz
  have : (Space.closedImmersionPresheafProperty B S hS).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _ (F := yoneda)).respectsIso
  have hsq := Subfunctor.isPullback_preimage (yoneda.map q) (chartLocusSubfunctor f Z x)
  have key : Space.closedImmersionPresheafProperty B S hS
      ((chartLocusSubfunctor f Z x).preimage (yoneda.map q)).ι := by
    rw [preimage_chartLocusSubfunctor hZ x z q φ hφ]
    exact (Space.isClosedSubspace_preimage B S hS (yoneda.map z.hom) Z
      (isAlgebraicSpace_yoneda B S hS W₀) (isAlgebraicSpace_yoneda B S hS z.left) hZc).2
  have he : hsq.isoPullback.inv ≫ ((chartLocusSubfunctor f Z x).preimage (yoneda.map q)).ι =
      pullback.snd (chartLocusSubfunctor f Z x).ι (yoneda.map q) := by
    rw [Iso.inv_comp_eq, hsq.isoPullback_hom_snd]
  rw [← he]
  exact MorphismProperty.RespectsIso.precomp _ _ _ key

/-- **The base change of the inclusion of the locus along a scheme-valued point is a closed
subspace.** For an invariant closed subspace `Z` of a locally essentially surjective chart and a
scheme-valued point `z` of `𝒳` with values in `V`, the subfunctor
`AlgebraicGeometry.Stack.fullSubcategoryBaseChangeSubfunctor` of `yoneda V` cut out by the locus
of `Z` is a closed subspace of `V`.

Write `x` for the value of `z` at the terminal object of the site of `V`. Membership of `z T` in
the locus is membership of the structure morphism of `T` in
`AlgebraicGeometry.Stack.chartLocusSubfunctor` at `x`
(`AlgebraicGeometry.Stack.chartLocus_iff_mem_chartLocusSubfunctor`), and that subfunctor is the
range of a closed immersion `C ⟶ V` of the site by
`AlgebraicGeometry.Stack.closedImmersionPresheafProperty_chartLocusSubfunctor`. So the base change
subfunctor is the range of the same closed immersion read on the site of `V`. -/
theorem isClosedSubspace_fullSubcategoryBaseChangeSubfunctor_chartLocus
    (hZ : IsChartInvariant f Z) (hZc : Space.IsClosedSubspace B S hS Z)
    (hloc : IsChartLocallyEssSurj f)
    (V : BigFppfOver B S hS) (z : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj)
    (hz : z ⋙ 𝒳.val.val.p = Over.map V.hom) :
    Space.IsClosedSubspace B V.left.1 V.left.2
      (fullSubcategoryBaseChangeSubfunctor 𝒳 (fun g => chartLocus_of_hom f Z g) z) := by
  let T₀ : BigFppfOver B V.left.1 V.left.2 := Over.mk (𝟙 (B.obj V.left.2))
  let V₁ : BigFppfOver B S hS := (Over.map V.hom).obj T₀
  let x : 𝒳.val.val.p.Fiber V₁ := ⟨z.obj T₀, Functor.congr_obj hz T₀⟩
  obtain ⟨hrep, hprop⟩ := closedImmersionPresheafProperty_chartLocusSubfunctor hZ hZc x (hloc V₁ x)
  obtain ⟨C, i, s, hpb⟩ := hrep (𝟙 (yoneda.obj V₁))
  have hi : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    hprop _ _ _ hpb
  have hQ : chartLocusSubfunctor f Z x = Subfunctor.range (yoneda.map i) := by
    have h := Subfunctor.range_eq_preimage_of_isPullback hpb.flip
    rw [Subfunctor.range_ι] at h
    rw [h]
    ext T g
    simp
  -- the closed subscheme, read on the site of `V`
  let Cv : BigFppfOver B V.left.1 V.left.2 := Over.mk (i.left : C.left ⟶ T₀.left)
  let j : Cv ⟶ T₀ := Over.homMk i.left (by simp [Cv, T₀])
  have hj : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B V.left.1 V.left.2).map j) := hi
  have hiw : i.left ≫ V₁.hom = C.hom := Over.w i
  -- membership in the base change subfunctor
  have key : ∀ T : BigFppfOver B V.left.1 V.left.2,
      chartLocus f Z (z.obj T) ↔ Nonempty (T ⟶ Cv) := by
    intro T
    let e : T ⟶ T₀ := Over.homMk T.hom (by simp [T₀])
    have he : (Over.map V.hom).IsHomLift ((Over.map V.hom).map e) e := IsHomLift.map _ e
    have hφ : 𝒳.val.val.p.IsHomLift ((Over.map V.hom).map e) (z.map e) :=
      Functor.isHomLift_map_of_comp_eq hz _ e
    rw [chartLocus_iff_mem_chartLocusSubfunctor x ((Over.map V.hom).map e) (z.map e) hφ, hQ]
    constructor
    · rintro ⟨c, hc⟩
      have hc' : c ≫ i = (Over.map V.hom).map e := hc
      have hcl : c.left ≫ i.left = T.hom := by
        simpa [e] using congrArg CommaMorphism.left hc'
      exact ⟨Over.homMk c.left hcl⟩
    · rintro ⟨m⟩
      have hml : m.left ≫ i.left = T.hom := Over.w m
      refine ⟨Over.homMk m.left ?_, ?_⟩
      · change m.left ≫ C.hom = T.hom ≫ V.hom
        rw [← hiw, ← Category.assoc, hml]
        simp [V₁, T₀]
      · apply Over.OverMorphism.ext
        simpa [e] using hml
  have hF : fullSubcategoryBaseChangeSubfunctor 𝒳 (fun g => chartLocus_of_hom f Z g) z =
      Subfunctor.range (yoneda.map j) := by
    ext T e
    change chartLocus f Z (z.obj T.unop) ↔ e ∈ Set.range ((yoneda.map j).app T)
    rw [key]
    exact ⟨fun ⟨m⟩ => ⟨m, Over.mkIdTerminal.hom_ext _ _⟩, fun ⟨m, _⟩ => ⟨m⟩⟩
  rw [hF]
  exact Space.isClosedSubspace_range_yoneda_map B V.left.1 V.left.2 j hj

/-- **The locus of an invariant closed subspace of a chart is a closed substack.** Let `f` be a
locally essentially surjective 1-morphism to `𝒳` from the category represented by a scheme `W₀`,
and let `Z` be a closed subspace of `W₀` invariant for `f`. Then the locus of `Z` is a closed
substack of `𝒳` (**Stacks 04YM**, part (2)). -/
theorem isClosedSubstack_chartLocus (hZ : IsChartInvariant f Z)
    (hZc : Space.IsClosedSubspace B S hS Z)
    (hloc : IsChartLocallyEssSurj f) :
    IsClosedSubstack 𝒳 (chartLocus f Z) :=
  isClosedSubstack_of_isClosedSubspace 𝒳 (fun g => chartLocus_of_hom f Z g)
    (isClosedSubspace_fullSubcategoryBaseChangeSubfunctor_chartLocus hZ hZc hloc)

end AlgebraicGeometry.Stack

end
