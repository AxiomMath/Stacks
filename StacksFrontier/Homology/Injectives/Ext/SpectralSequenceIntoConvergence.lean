module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksFrontier.Algebra.Homology.SpectralSequence.ConvergenceNat
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.PageInfinity
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceIntoFilteredComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the Ext spectral sequence into a filtered complex

Let `A` be a Grothendieck abelian category, let `M` be an object of `D(A)` and let `K^•` be a
filtered complex of `A`. The Ext spectral sequence into `K^•` is bounded, and converges to
`Ext^{p + q}(M, K^•)`, as soon as in every degree `n` the group `Ext^n(M, F^pK^•)` vanishes for
`p ≫ 0` and maps isomorphically onto `Ext^n(M, K^•)` for `p ≪ 0`.

The filtration of the abutment is `Stacks.Injectives.extIntoFiltration`, whose `p`-th step is the
image of `Ext^n(M, F^pK^•) ⟶ Ext^n(M, K^•)`; it is *antitone* in `p`, the two hypotheses saying
that it is `⊤` for `p ≪ 0` and `⊥` for `p ≫ 0`.

Both hypotheses are read off the filtered Hom complex `Hom^•(M^•, J^•)` whose spectral sequence
the construction is: its `p`-th filtration step has cohomology `Ext^n(M, F^pK)` and its underlying
complex has cohomology `Ext^n(M, K)`, compatibly with the maps induced by the inclusions of the
filtration steps. The two hypotheses therefore say exactly that the cohomology of the filtration
steps of that filtered complex eventually vanishes on the right and eventually maps isomorphically
on the left, which is the hypothesis of
`CochainComplex.Filtered.hasPageInfinityAt_of_eventually`.

## Main definitions

* `Stacks.Injectives.extIntoComparison`: the chosen cohomology–Ext identifications for the Hom
  complex of Tag 0G1X.
* `Stacks.Injectives.extIntoHomologyExt`: the identification of the cohomology of the Hom complex
  with `Ext^n(M, K^•)`; this is what "converges to `Ext^{p + q}(M, K)`" refers to.
* `Stacks.Injectives.extIntoFiltration`: the filtration of `Ext^n(M, K^•)` by the images of the
  maps `Ext^n(M, F^pK^•) ⟶ Ext^n(M, K^•)`.

## Main results

* `Stacks.Injectives.extSpectralSequenceInto_isBounded`: the spectral sequence is bounded.
* `Stacks.Injectives.extSpectralSequenceInto_hasPageInfinityAt`: it has an infinity page at every
  bidegree.
* `Stacks.Injectives.extSpectralSequenceInto_convergesToExt`: it converges to
  `Ext^{p + q}(M, K^•)`: the filtration `Stacks.Injectives.extIntoFiltration` of each
  `Ext^n(M, K^•)` is finite, and the infinity page at `(p, q)` is its `p`-th graded piece
  `F^p/F^{p + 1}` in total degree `n = p + q`.

## Implementation notes

The vanishing hypothesis is stated as `Subsingleton` of an Ext group and the isomorphism
hypothesis as bijectivity of the map on Ext groups induced by an inclusion of filtration steps.
Both are universe-free statements about the Ext groups themselves, which lie in the
derived-category Hom universe `w`, while the Hom complex and its spectral sequence live in the
morphism universe `v` of `A`; the comparison of the two is by additive equivalences, so no
universe is identified with another.

That universe gap is also why the graded piece of the abutment is compared with the infinity page
by an *additive equivalence* rather than by an isomorphism of `AddCommGrpCat`: the infinity page
is an object of `AddCommGrpCat.{v}` and the graded piece of `Ext^n(M, K^•)` an object of
`AddCommGrpCat.{w}`, so there is no single category in which to state an isomorphism. An additive
equivalence between the two carriers is the same datum as such an isomorphism whenever the two
universes agree.

The comparison is assembled from the identification
`CochainComplex.Filtered.nonempty_pageInfinityIso_inducedFiltrationStep` of the infinity page with
a graded piece of the filtration induced on the cohomology of the Hom complex, and from the
transport of that graded piece along `Stacks.Injectives.extIntoHomologyExt`. The transport is done
through the ranges of the two maps: in `AddCommGrpCat` the quotient of the image subobject of `f`
by the image subobject of `g ≫ f` is the quotient of the range of `f` by the range of `g ≫ f`
(`Stacks.Injectives.cokernelOfLEImageSubobjectAddEquiv`), and `extIntoHomologyExt` carries the one
pair of ranges onto the other by `Stacks.Injectives.extIntoHomologyExt_naturality`.

## References

* [Stacks Project, Tag 0G1X](https://stacks.math.columbia.edu/tag/0G1X)
* [Stacks Project, Tag 012V](https://stacks.math.columbia.edu/tag/012V)
-/

@[expose] public noncomputable section

universe w' w v u t

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Injectives

/-! ### Quotients of image subobjects in `AddCommGrpCat` -/

/-- The inclusion of the image subobject of a morphism of `AddCommGrpCat` has the same range as
the morphism itself. -/
private theorem range_imageSubobject_arrow {X Y : AddCommGrpCat.{t}} (f : X ⟶ Y) :
    AddMonoidHom.range ((imageSubobject f).arrow).hom = AddMonoidHom.range f.hom := by
  have key (x : X) : (imageSubobject f).arrow (factorThruImageSubobject f x) = f x := by
    rw [← ConcreteCategory.comp_apply, imageSubobject_arrow_comp]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
      (factorThruImageSubobject f)).1 inferInstance y
    exact ⟨x, (key x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, key x⟩

/-- The underlying group of the image subobject of a morphism of `AddCommGrpCat` is the range of
that morphism, compatibly with the inclusions into the target. -/
private def imageSubobjectAddEquivRange {X Y : AddCommGrpCat.{t}} (f : X ⟶ Y) :
    (imageSubobject f : AddCommGrpCat.{t}) ≃+ AddMonoidHom.range f.hom :=
  (AddMonoidHom.ofInjective ((AddCommGrpCat.mono_iff_injective
      ((imageSubobject f).arrow)).1 inferInstance)).trans
    (AddEquiv.addSubgroupCongr (range_imageSubobject_arrow f))

/-- Under `Stacks.Injectives.imageSubobjectAddEquivRange` the inclusion of the image subobject of
`g ≫ f` in the image subobject of `f` becomes the range of `g ≫ f` inside the range of `f`. -/
private theorem map_range_ofLE {X Y Z : AddCommGrpCat.{t}} (g : X ⟶ Y) (f : Y ⟶ Z) :
    AddSubgroup.map (imageSubobjectAddEquivRange f)
        (AddMonoidHom.range (Subobject.ofLE (imageSubobject (g ≫ f)) (imageSubobject f)
          (imageSubobject_comp_le g f)).hom) =
      (AddMonoidHom.range (g ≫ f).hom).addSubgroupOf (AddMonoidHom.range f.hom) := by
  set m := Subobject.ofLE (imageSubobject (g ≫ f)) (imageSubobject f)
    (imageSubobject_comp_le g f) with hm
  have key : ∀ x : (imageSubobject (g ≫ f) : AddCommGrpCat.{t}),
      ((imageSubobjectAddEquivRange f (m x) : AddMonoidHom.range f.hom) : Z) =
        (imageSubobject (g ≫ f)).arrow x := by
    intro x
    show (imageSubobject f).arrow (m x) = _
    rw [← ConcreteCategory.comp_apply, hm, Subobject.ofLE_arrow]
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    show ((imageSubobjectAddEquivRange f (m x) : AddMonoidHom.range f.hom) : Z) ∈ _
    rw [key x, ← range_imageSubobject_arrow (g ≫ f)]
    exact ⟨x, rfl⟩
  · rintro a ha
    rw [AddSubgroup.mem_addSubgroupOf, ← range_imageSubobject_arrow (g ≫ f),
      AddMonoidHom.mem_range] at ha
    obtain ⟨x, hx⟩ := ha
    rw [AddSubgroup.mem_map]
    exact ⟨m x, ⟨x, rfl⟩, Subtype.ext ((key x).trans hx)⟩

/-- **The graded piece of a pair of image subobjects in `AddCommGrpCat`.** The quotient of the
image subobject of `f` by the image subobject of `g ≫ f` is the quotient of the range of `f` by
the range of `g ≫ f`. -/
private def cokernelOfLEImageSubobjectAddEquiv {X Y Z : AddCommGrpCat.{t}}
    (g : X ⟶ Y) (f : Y ⟶ Z) :
    ((cokernel (Subobject.ofLE (imageSubobject (g ≫ f)) (imageSubobject f)
        (imageSubobject_comp_le g f)) : AddCommGrpCat.{t}) : Type t) ≃+
      (AddMonoidHom.range f.hom ⧸
        (AddMonoidHom.range (g ≫ f).hom).addSubgroupOf (AddMonoidHom.range f.hom)) :=
  (AddCommGrpCat.cokernelIsoQuotient (Subobject.ofLE (imageSubobject (g ≫ f))
      (imageSubobject f) (imageSubobject_comp_le g f))).addCommGroupIsoToAddEquiv.trans
    (QuotientAddGroup.congr _ _ (imageSubobjectAddEquivRange f) (map_range_ofLE g f))

/-- Transport of a quotient `A/B` of subgroups along an additive equivalence carrying `A` to `A'`
and `B` to `B'`. The two ambient groups may live in different universes. -/
private def quotientAddSubgroupOfCongr {H : Type*} {G : Type*} [AddCommGroup H]
    [AddCommGroup G] (e : H ≃+ G) {A B : AddSubgroup H} {A' B' : AddSubgroup G}
    (hA : AddSubgroup.map (e : H →+ G) A = A')
    (hB : AddSubgroup.map (e : H →+ G) B = B') :
    (↥A ⧸ B.addSubgroupOf A) ≃+ (↥A' ⧸ B'.addSubgroupOf A') := by
  refine QuotientAddGroup.congr _ _ ((e.addSubgroupMap A).trans (AddEquiv.addSubgroupCongr hA)) ?_
  apply le_antisymm
  · rintro x hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [AddSubgroup.mem_addSubgroupOf] at ha ⊢
    rw [← hB]
    exact AddSubgroup.mem_map.2 ⟨(a : H), ha, rfl⟩
  · rintro x hx
    rw [AddSubgroup.mem_addSubgroupOf, ← hB, AddSubgroup.mem_map] at hx
    obtain ⟨b, hb, hbx⟩ := hx
    have hbA : b ∈ A := by
      have hmem : (e : H →+ G) b ∈ A' := hbx ▸ x.2
      rw [← hA] at hmem
      obtain ⟨a, ha, hae⟩ := AddSubgroup.mem_map.1 hmem
      exact (e.injective hae : a = b) ▸ ha
    exact AddSubgroup.mem_map.2
      ⟨⟨b, hbA⟩, AddSubgroup.mem_addSubgroupOf.2 hb, Subtype.ext hbx⟩

/-- The map induced on cohomology by the inclusion of the `p'`-th step of a filtered complex
factors through the one induced by the inclusion of the `p`-th step, for `p ≤ p'`. -/
private theorem homologyMap_filtration_ι_factor {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex.Filtered C) (n : ℤ) {p p' : ℤ} (h : p ≤ p') :
    HomologicalComplex.homologyMap (L.filtration.ι.app (op p')) n =
      HomologicalComplex.homologyMap (L.filtration.diagram.map (opHomOfLE h)) n ≫
        HomologicalComplex.homologyMap (L.filtration.ι.app (op p)) n := by
  rw [← HomologicalComplex.homologyMap_comp, L.filtration.diagram_map_comp_ι_app]

/-- The `p'`-th step of the filtration induced on cohomology, read as the image subobject of a
composite ending in the map of the `p`-th step, for `p ≤ p'`. -/
private theorem inducedFiltrationStep_eq_imageSubobject_comp {C : Type*} [Category* C] [Abelian C]
    (L : CochainComplex.Filtered C) (n : ℤ) {p p' : ℤ} (h : p ≤ p') :
    L.inducedFiltrationStep n p' =
      imageSubobject (HomologicalComplex.homologyMap
          (L.filtration.diagram.map (opHomOfLE h)) n ≫
        HomologicalComplex.homologyMap (L.filtration.ι.app (op p)) n) := by
  simp only [CochainComplex.Filtered.inducedFiltrationStep,
    homologyMap_filtration_ι_factor L n h]

/-! ### The Ext spectral sequence into a filtered complex and its abutment -/

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- A choice of compatible cohomology–Ext identifications for the Hom complex of Tag 0G1X. -/
def extIntoComparison (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    CohomologyExtComparison (extIntoSetup.{w', w} M K) :=
  (cohomologyExtComparison_nonempty (extIntoSetup.{w', w} M K)).some

/-- The cohomology of the filtered Hom complex of Tag 0G1X computes `Ext^n(M, K^•)`: this is the
group the spectral sequence converges to. -/
def extIntoHomologyExt (M : DerivedCategory A) (K : CochainComplex.Filtered A) (n : ℤ) :
    ((extIntoFilteredHomComplex.{w', w} M K).X.homology n : Type v) ≃+
      DerivedCategory.Ext M (DerivedCategory.Q.obj K.X) n :=
  let e := (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).mapIso
    (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).underlyingIso
  e.addCommGroupIsoToAddEquiv.trans ((extIntoComparison M K).homComplexIso n)

/-- The cohomology of the `p`-th filtration step of the filtered Hom complex of Tag 0G1X computes
`Ext^n(M, F^pK^•)`. -/
def extIntoFiltrationHomologyExt (M : DerivedCategory A) (K : CochainComplex.Filtered A)
    (p n : ℤ) :
    (((extIntoFilteredHomComplex.{w', w} M K).filtration.obj (op p)).homology n : Type v) ≃+
      DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n :=
  let e := (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).mapIso
    ((filteredHomComplexRealization (extIntoSetup.{w', w} M K)).stepIso p)
  e.addCommGroupIsoToAddEquiv.trans ((extIntoComparison M K).filtrationHomComplexIso p n)

/-- The two identifications turn the map induced on cohomology by the inclusion of the `p`-th
filtration step into the map induced on Ext groups by that inclusion. -/
theorem extIntoHomologyExt_naturality (M : DerivedCategory A) (K : CochainComplex.Filtered A)
    (p n : ℤ) (x : ((extIntoFilteredHomComplex.{w', w} M K).filtration.obj (op p)).homology n) :
    extIntoHomologyExt.{w', w} M K n (HomologicalComplex.homologyMap
        ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n x) =
      extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))
        (extIntoFiltrationHomologyExt.{w', w} M K p n x) := by
  have hnat := (extIntoComparison M K).filtration_naturality p n
    (HomologicalComplex.homologyMap
      ((filteredHomComplexRealization (extIntoSetup.{w', w} M K)).stepIso p).hom n x)
  have hmid :
      (HomologicalComplex.homologyMap
          (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).underlyingIso.hom n)
        ((HomologicalComplex.homologyMap
          ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n) x) =
      (HomologicalComplex.homologyMap (filtrationHomComplexι (extIntoSetup.{w', w} M K) p) n)
        ((HomologicalComplex.homologyMap
          ((filteredHomComplexRealization (extIntoSetup.{w', w} M K)).stepIso p).hom n) x) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).stepIso_hom_comp p]
  exact Eq.trans (congrArg ((extIntoComparison M K).homComplexIso n) hmid) hnat

variable (M : DerivedCategory A) (K : CochainComplex.Filtered A)

omit [IsGrothendieckAbelian.{w'} A] in
/-- The map `Ext^n(M, F^{p'}K^•) ⟶ Ext^n(M, K^•)` factors through `Ext^n(M, F^pK^•)`, for
`p ≤ p'`. -/
private theorem extIntoFiltrationMap_factor (n : ℤ) {p p' : ℤ} (h : p ≤ p') :
    AddCommGrpCat.ofHom (extPostcomp M n
        (DerivedCategory.Q.map (K.filtration.ι.app (op p')))) =
      AddCommGrpCat.ofHom (extPostcomp M n
          (DerivedCategory.Q.map (K.filtration.diagram.map (opHomOfLE h)))) ≫
        AddCommGrpCat.ofHom (extPostcomp M n
          (DerivedCategory.Q.map (K.filtration.ι.app (op p)))) := by
  ext x
  rw [← K.filtration.diagram_map_comp_ι_app (opHomOfLE h), Functor.map_comp]
  simp [extPostcomp, Functor.map_comp]

/-- **The filtration of the abutment of Tag 0G1X.** The `p`-th step of the filtration of
`Ext^n(M, K^•)` is the image of the map `Ext^n(M, F^pK^•) ⟶ Ext^n(M, K^•)` induced by the
inclusion of the `p`-th filtration step. It is antitone in `p`. -/
def extIntoFiltration (n p : ℤ) :
    Subobject (AddCommGrpCat.of (DerivedCategory.Ext M (DerivedCategory.Q.obj K.X) n)) :=
  imageSubobject (AddCommGrpCat.ofHom
    (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))))

omit [IsGrothendieckAbelian.{w'} A] in
/-- The `p'`-th step of the filtration of `Ext^n(M, K^•)`, read as the image subobject of a
composite ending in the map of the `p`-th step, for `p ≤ p'`. -/
theorem extIntoFiltration_eq_imageSubobject_comp (n : ℤ) {p p' : ℤ} (h : p ≤ p') :
    extIntoFiltration M K n p' =
      imageSubobject (AddCommGrpCat.ofHom (extPostcomp M n
          (DerivedCategory.Q.map (K.filtration.diagram.map (opHomOfLE h)))) ≫
        AddCommGrpCat.ofHom (extPostcomp M n
          (DerivedCategory.Q.map (K.filtration.ι.app (op p))))) := by
  simp only [extIntoFiltration, extIntoFiltrationMap_factor M K n h]

omit [IsGrothendieckAbelian.{w'} A] in
/-- The filtration of `Ext^n(M, K^•)` of Tag 0G1X is decreasing. -/
theorem extIntoFiltration_antitone (n : ℤ) : Antitone (extIntoFiltration M K n) := by
  intro p p' h
  rw [extIntoFiltration_eq_imageSubobject_comp M K n h]
  exact imageSubobject_comp_le _ _

omit [IsGrothendieckAbelian.{w'} A] in
/-- Where the map `Ext^n(M, F^pK^•) ⟶ Ext^n(M, K^•)` is bijective, the `p`-th step of the
filtration of `Ext^n(M, K^•)` is everything. -/
private theorem extIntoFiltration_eq_top (n p : ℤ)
    (h : Function.Bijective
      (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p))))) :
    extIntoFiltration M K n p = ⊤ := by
  have : Epi (AddCommGrpCat.ofHom
      (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p))))) :=
    (AddCommGrpCat.epi_iff_surjective _).2 h.2
  exact Subobject.imageSubobject_eq_top_of_epi _

omit [IsGrothendieckAbelian.{w'} A] in
/-- Where `Ext^n(M, F^pK^•)` vanishes, the `p`-th step of the filtration of `Ext^n(M, K^•)` is
zero. -/
private theorem extIntoFiltration_eq_bot (n p : ℤ)
    (h : Subsingleton
      (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n)) :
    extIntoFiltration M K n p = ⊥ := by
  have hz : IsZero (AddCommGrpCat.of
      (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n)) :=
    AddCommGrpCat.isZero_of_subsingleton _
  have hzero : AddCommGrpCat.ofHom
      (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))) = 0 :=
    hz.eq_of_src _ _
  simp only [extIntoFiltration, hzero]
  exact imageSubobject_zero

/-- Under `Stacks.Injectives.extIntoHomologyExt` the range of the map induced on cohomology by the
inclusion of the `p`-th filtration step of the Hom complex is the range of the map
`Ext^n(M, F^pK^•) ⟶ Ext^n(M, K^•)`. -/
private theorem map_range_homologyMap (n p : ℤ) :
    AddSubgroup.map ((extIntoHomologyExt.{w', w} M K n :
        ((extIntoFilteredHomComplex.{w', w} M K).X.homology n : Type v) →+
          DerivedCategory.Ext M (DerivedCategory.Q.obj K.X) n))
        (AddMonoidHom.range (HomologicalComplex.homologyMap
          ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n).hom) =
      AddMonoidHom.range (AddCommGrpCat.ofHom
        (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p))))).hom := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact AddMonoidHom.mem_range.2 ⟨extIntoFiltrationHomologyExt.{w', w} M K p n x,
      (extIntoHomologyExt_naturality.{w', w} M K p n x).symm⟩
  · rintro _ ⟨y, rfl⟩
    refine AddSubgroup.mem_map.2 ⟨HomologicalComplex.homologyMap
      ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n
        ((extIntoFiltrationHomologyExt.{w', w} M K p n).symm y),
      AddMonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    have hnat := extIntoHomologyExt_naturality.{w', w} M K p n
      ((extIntoFiltrationHomologyExt.{w', w} M K p n).symm y)
    rwa [AddEquiv.apply_symm_apply] at hnat

/-- The same comparison of ranges as `Stacks.Injectives.map_range_homologyMap`, with both maps
written as the composites they are for `p ≤ p'`. -/
private theorem map_range_homologyMap_factor (n : ℤ) {p p' : ℤ} (h : p ≤ p') :
    AddSubgroup.map ((extIntoHomologyExt.{w', w} M K n :
        ((extIntoFilteredHomComplex.{w', w} M K).X.homology n : Type v) →+
          DerivedCategory.Ext M (DerivedCategory.Q.obj K.X) n))
        (AddMonoidHom.range (HomologicalComplex.homologyMap
            ((extIntoFilteredHomComplex.{w', w} M K).filtration.diagram.map
              (opHomOfLE h)) n ≫
          HomologicalComplex.homologyMap
            ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n).hom) =
      AddMonoidHom.range (AddCommGrpCat.ofHom (extPostcomp M n
            (DerivedCategory.Q.map (K.filtration.diagram.map (opHomOfLE h)))) ≫
          AddCommGrpCat.ofHom (extPostcomp M n
            (DerivedCategory.Q.map (K.filtration.ι.app (op p))))).hom := by
  rw [← homologyMap_filtration_ι_factor (extIntoFilteredHomComplex.{w', w} M K) n h,
    ← extIntoFiltrationMap_factor M K n h]
  exact map_range_homologyMap.{w', w} M K n p'

/-- The vanishing hypothesis, transported to the filtered Hom complex. -/
private theorem isZero_filtrationHomology
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n))
    (n : ℤ) : ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Limits.IsZero
        (((extIntoFilteredHomComplex.{w', w} M K).filtration.obj (op p)).homology n) := by
  obtain ⟨p₀, hp₀⟩ := hzero n
  refine ⟨p₀, fun p hp ↦ ?_⟩
  have := hp₀ p hp
  have : Subsingleton
      (((extIntoFilteredHomComplex.{w', w} M K).filtration.obj (op p)).homology n : Type v) :=
    (extIntoFiltrationHomologyExt.{w', w} M K p n).toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The isomorphism hypothesis, transported to the filtered Hom complex. -/
private theorem isIso_filtrationHomologyMap
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      Function.Bijective
        (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))))
    (n : ℤ) : ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (HomologicalComplex.homologyMap
        ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n) := by
  obtain ⟨p₁, hp₁⟩ := hiso n
  refine ⟨p₁, fun p hp ↦ ?_⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  have hcomp : (extIntoHomologyExt.{w', w} M K n) ∘ (fun x ↦ HomologicalComplex.homologyMap
      ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n x) =
      (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))) ∘
        (extIntoFiltrationHomologyExt.{w', w} M K p n) :=
    funext (extIntoHomologyExt_naturality.{w', w} M K p n)
  have hb : Function.Bijective ((extIntoHomologyExt.{w', w} M K n) ∘
      (fun x ↦ HomologicalComplex.homologyMap
        ((extIntoFilteredHomComplex.{w', w} M K).filtration.ι.app (op p)) n x)) := by
    rw [hcomp]
    exact (hp₁ p hp).comp (extIntoFiltrationHomologyExt.{w', w} M K p n).bijective
  exact (Function.Bijective.of_comp_iff' (extIntoHomologyExt.{w', w} M K n).bijective _).1 hb

/-- **Stacks 0G1X, boundedness.** If in every degree `Ext^n(M, F^pK^•)` vanishes for `p ≫ 0` and
maps bijectively onto `Ext^n(M, K^•)` for `p ≪ 0`, then the Ext spectral sequence into `K^•` is
bounded: in each total degree only finitely many terms of its first page are nonzero. -/
@[stacks 0G1X "ext_spectral_sequence_convergence"]
theorem extSpectralSequenceInto_isBounded
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      Function.Bijective
        (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p))))) :
    IsBounded (extSpectralSequenceInto.{w', w} M K).1 := fun n ↦
  CochainComplex.Filtered.finite_not_isZero_page_one (extIntoFilteredHomComplex.{w', w} M K)
    (isZero_filtrationHomology.{w', w} M K hzero)
    (isIso_filtrationHomologyMap.{w', w} M K hiso) n

/-- **Stacks 0G1X, the infinity page exists.** Under the same hypotheses the Ext spectral
sequence into `K^•` stabilises at every bidegree. -/
@[stacks 0G1X "ext_spectral_sequence_convergence"]
theorem extSpectralSequenceInto_hasPageInfinityAt
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      Function.Bijective
        (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))))
    (pq : ℤ × ℤ) :
    (extSpectralSequenceInto.{w', w} M K).1.HasPageInfinityAt pq :=
  SpectralSequence.hasPageInfinityAt_of_finite_page _ 1 le_rfl
    (extSpectralSequenceInto_isBounded.{w', w} M K hzero hiso) pq

/-- The infinity page of the spectral sequence of the filtered Hom complex at `(p, q)` is the
`p`-th graded piece of the filtration induced on the cohomology of that complex. This is the
stepping stone to the convergence statement, which reads the same graded piece on
`Ext^{p + q}(M, K^•)`. -/
private theorem nonempty_extSpectralSequenceInto_pageInfinityIso
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      Function.Bijective
        (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p)))))
    (p q : ℤ) :
    Nonempty ((CochainComplex.Filtered.spectralSequenceFunctor.obj
        (extIntoFilteredHomComplex.{w', w} M K)).pageInfinity (p, q) ≅
      cokernel (Subobject.ofLE
        ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep (p + q) (p + 1))
        ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep (p + q) p)
        ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep_antitone (p + q)
          (by omega)))) :=
  CochainComplex.Filtered.nonempty_pageInfinityIso_inducedFiltrationStep
    (extIntoFilteredHomComplex.{w', w} M K)
    (isZero_filtrationHomology.{w', w} M K hzero)
    (isIso_filtrationHomologyMap.{w', w} M K hiso) p q

/-- The `p`-th graded piece of the filtration induced on the cohomology of the Hom complex is the
`p`-th graded piece of the filtration `Stacks.Injectives.extIntoFiltration` of
`Ext^{p + q}(M, K^•)`, through `Stacks.Injectives.extIntoHomologyExt`. -/
private def extIntoGradedPieceAddEquiv (p q : ℤ) :
    ((cokernel (Subobject.ofLE
          ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep (p + q) (p + 1))
          ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep (p + q) p)
          ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep_antitone (p + q)
            (by omega))) : AddCommGrpCat.{v}) : Type v) ≃+
      ((cokernel (Subobject.ofLE (extIntoFiltration M K (p + q) (p + 1))
          (extIntoFiltration M K (p + q) p)
          (extIntoFiltration_antitone M K (p + q) (by omega))) : AddCommGrpCat.{w}) : Type w) :=
  have hp : p ≤ p + 1 := by omega
  ((Subobject.cokernelOfLEIsoOfEq
      ((extIntoFilteredHomComplex.{w', w} M K).inducedFiltrationStep_antitone (p + q) hp)
      (imageSubobject_comp_le _ _)
      (inducedFiltrationStep_eq_imageSubobject_comp (extIntoFilteredHomComplex.{w', w} M K)
        (p + q) hp) rfl).addCommGroupIsoToAddEquiv).trans
    ((cokernelOfLEImageSubobjectAddEquiv _ _).trans
      ((quotientAddSubgroupOfCongr (extIntoHomologyExt.{w', w} M K (p + q))
          (map_range_homologyMap.{w', w} M K (p + q) p)
          (map_range_homologyMap_factor.{w', w} M K (p + q) hp)).trans
        ((cokernelOfLEImageSubobjectAddEquiv _ _).symm.trans
          ((Subobject.cokernelOfLEIsoOfEq (imageSubobject_comp_le _ _)
            (extIntoFiltration_antitone M K (p + q) hp)
            (extIntoFiltration_eq_imageSubobject_comp M K (p + q) hp).symm
            rfl).addCommGroupIsoToAddEquiv))))

/-- **Stacks 0G1X, convergence.** If in every degree `Ext^n(M, F^pK^•)` vanishes for `p ≫ 0` and
maps bijectively onto `Ext^n(M, K^•)` for `p ≪ 0`, then the Ext spectral sequence into `K^•`
converges to `Ext^{p + q}(M, K^•)`: the decreasing filtration
`Stacks.Injectives.extIntoFiltration` of `Ext^n(M, K^•)` is finite, being `⊤` for `p ≪ 0` and `⊥`
for `p ≫ 0`, the spectral sequence has an infinity page everywhere, and
`E_∞^{p, q} ≅ F^p/F^{p + 1}` in total degree `n = p + q`. -/
@[stacks 0G1X "ext_spectral_sequence_convergence"]
theorem extSpectralSequenceInto_convergesToExt
    (hzero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Subsingleton (DerivedCategory.Ext M (DerivedCategory.Q.obj (K.filtration.obj (op p))) n))
    (hiso : ∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      Function.Bijective
        (extPostcomp M n (DerivedCategory.Q.map (K.filtration.ι.app (op p))))) :
    let E := (extSpectralSequenceInto.{w', w} M K).1
    ∃ hF : ∀ n : ℤ, Antitone (extIntoFiltration M K n),
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ extIntoFiltration M K n a = ⊤ ∧
        extIntoFiltration M K n b = ⊥) ∧
      (∀ p q : ℤ, E.HasPageInfinityAt (p, q)) ∧
      ∀ p q : ℤ, Nonempty
        ((E.pageInfinity (p, q) : Type v) ≃+
          ((cokernel (Subobject.ofLE (extIntoFiltration M K (p + q) (p + 1))
              (extIntoFiltration M K (p + q) p)
              (hF (p + q) (by omega))) : AddCommGrpCat.{w}) : Type w)) := by
  refine ⟨extIntoFiltration_antitone M K, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨p₀, hp₀⟩ := hzero n
    obtain ⟨p₁, hp₁⟩ := hiso n
    exact ⟨min p₁ p₀, max p₁ p₀, min_le_max,
      extIntoFiltration_eq_top M K n _ (hp₁ _ (min_le_left _ _)),
      extIntoFiltration_eq_bot M K n _ (hp₀ _ (le_max_right _ _))⟩
  · exact fun p q ↦ extSpectralSequenceInto_hasPageInfinityAt.{w', w} M K hzero hiso (p, q)
  · intro p q
    have : (CochainComplex.Filtered.spectralSequenceFunctor.obj
        (extIntoFilteredHomComplex.{w', w} M K)).HasPageInfinityAt (p, q) :=
      CochainComplex.Filtered.hasPageInfinityAt_of_eventually
        (extIntoFilteredHomComplex.{w', w} M K)
        (isZero_filtrationHomology.{w', w} M K hzero)
        (isIso_filtrationHomologyMap.{w', w} M K hiso) (p, q)
    obtain ⟨i⟩ := nonempty_extSpectralSequenceInto_pageInfinityIso.{w', w} M K hzero hiso p q
    exact ⟨(((SpectralSequence.shiftStart_pageInfinityIso
        (CochainComplex.Filtered.spectralSequenceFunctor.obj
          (extIntoFilteredHomComplex.{w', w} M K)) (show (0 : ℤ) ≤ 1 by omega)
        (p, q)).trans i).addCommGroupIsoToAddEquiv).trans
      (extIntoGradedPieceAddEquiv M K p q)⟩

end Stacks.Injectives

end
