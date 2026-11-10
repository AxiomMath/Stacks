module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakAffineFormalOpen
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionKernel

/-!
# The points of a McQuillan formal scheme killing an ideal sheaf

For an ideal sheaf `ℐ` on a locally topologically ringed space `X`, a morphism `f : Y → X` *kills*
`ℐ` when `f^♯` vanishes on the sections of `ℐ`, i.e. when `ℐ` lies in the kernel ideal sheaf of
`f`. On a formal scheme `𝔛` in the sense of McQuillan the points killing `ℐ` form a subfunctor
`h_ℐ ⊆ h_𝔛` of the functor of points; this file shows that for a weak ideal of definition `ℐ` cut
out by its sections over the affine formal opens (`IdealSheaf.IsCutOutOn`) the functor `h_ℐ` is
representable by a scheme. That scheme is the scheme `(𝔛, 𝒪_𝔛/ℐ)` of Stacks 0AIV: over a weak
affine formal open `𝔘 ≅ Spfw A` it is `Spec (A/ℐ(𝔘))`, glued along the open immersions the source
leaves implicit.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.Kills`: a morphism kills an ideal
  sheaf.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.killingPoints`: the subfunctor
  `h_ℐ` of the functor of points of a McQuillan formal scheme.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.quotientScheme`: the scheme
  representing it.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isSheaf_killingPoints`: `h_ℐ` is a
  Zariski sheaf.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.quotientSchemeRepresentableBy`:
  `h_ℐ` is represented by `quotientScheme`.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}}

/-- A morphism `f : Y → X` *kills* an ideal sheaf `ℐ` on `X` when `ℐ` lies in its kernel ideal
sheaf: `f^♯` vanishes on every section of `ℐ`. -/
def Kills (I : IdealSheaf X) {Y : LTRS.{u}} (f : Y ⟶ X) : Prop :=
  ∀ V : Opens X, I.ideal V ≤ (ker f).ideal V

/-- If `f` kills `ℐ`, then so does `g ≫ f` for every morphism `g`. -/
theorem Kills.comp {I : IdealSheaf X} {Y Z : LTRS.{u}} {f : Y ⟶ X} (hf : I.Kills f) (g : Z ⟶ Y) :
    I.Kills (g ≫ f) :=
  fun V => (hf V).trans (ker_le_ker_comp g f V)

/-- A morphism kills its own kernel ideal sheaf. -/
theorem kills_ker {Y : LTRS.{u}} (f : Y ⟶ X) : (ker f).Kills f :=
  fun _ => le_rfl

/-- A morphism landing in an open `U` kills an ideal sheaf as soon as it kills its sections over
the opens contained in `U`: the preimage of `V ⊓ U` is the preimage of `V`. -/
theorem kills_of_range_subset (I : IdealSheaf X) {Y : LTRS.{u}} (f : Y ⟶ X) {U : Opens X}
    (hf : Set.range f.toHom.base ⊆ (U : Set X))
    (h : ∀ V : Opens X, V ≤ U → I.ideal V ≤ (ker f).ideal V) : I.Kills f := by
  intro V s hs
  have hres := h (V ⊓ U) inf_le_right (I.map_mem inf_le_left hs)
  rw [mem_ker_iff] at hres ⊢
  have heq : (Opens.map f.toHom.base).obj (V ⊓ U) = (Opens.map f.toHom.base).obj V :=
    Opens.ext (Set.ext fun y => ⟨fun hy => hy.1, fun hy => ⟨hy, hf (Set.mem_range_self y)⟩⟩)
  have hnat := congrArg (fun φ => φ.1 s) (f.toHom.c.naturality (homOfLE (inf_le_left :
    V ⊓ U ≤ V)).op)
  have hiso := isIso_presheaf_map_of_opens_eq Y.presheaf heq.symm
    ((Opens.map f.toHom.base).op.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op)
  have hinj : Function.Injective (Y.presheaf.map
      ((Opens.map f.toHom.base).op.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op)).1 :=
    (TopCat.homeoOfIso ((forget₂ TopCommRingCat TopCat).mapIso (asIso _))).injective
  exact hinj ((hnat.symm.trans hres).trans (map_zero _).symm)

/-- **Killing an ideal sheaf is local on the source.** A point `f : T → X` of a scheme kills an
ideal sheaf as soon as its restrictions to the members of an open cover of `T` do: a section of
`𝒪_T` vanishing on the members of a cover is zero. -/
theorem kills_of_openCover (I : IdealSheaf X) {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ X)
    {ι : Type*} (W : ι → T.Opens) (hW : iSup W = ⊤)
    (h : ∀ i, I.Kills (schemeToLTRS.map (W i).ι ≫ f)) : I.Kills f := by
  intro V s hs
  rw [mem_ker_iff]
  refine eq_zero_of_locally_zero (schemeToLTRSObj T).IsSheaf fun p hp => ?_
  obtain ⟨i, hi⟩ : ∃ i, p ∈ W i := Opens.mem_iSup.mp (hW ▸ trivial : p ∈ iSup W)
  exact ⟨(W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ (Opens.map f.toHom.base).obj V),
    fun _ ⟨q, hq, hqe⟩ => hqe ▸ hq, ⟨⟨p, hi⟩, hp, rfl⟩, mem_ker_iff.mp (h i V hs)⟩

/-! ### The points killing an ideal sheaf -/

variable (I : IdealSheaf X)

/-- The subfunctor `h_ℐ` of the functor of points of a McQuillan formal scheme `𝔛` formed by the
points `T → 𝔛` that kill an ideal sheaf `ℐ`. -/
def killingPoints {𝔛 : McQuillanFormalScheme.{u}} (I : IdealSheaf 𝔛.obj) :
    Subfunctor (mcQuillanFormalSchemePoints 𝔛) where
  obj T := {φ | I.Kills φ.hom}
  map {T T'} g φ hφ := by
    change I.Kills (schemeToLTRS.map g.unop ≫ φ.hom)
    exact hφ.comp _

/-- A point `φ : T → 𝔛` lies in `h_ℐ` exactly when it kills `ℐ`. -/
theorem mem_killingPoints {𝔛 : McQuillanFormalScheme.{u}} {I : IdealSheaf 𝔛.obj} {T : Scheme.{u}}
    (φ : (mcQuillanFormalSchemePoints 𝔛).obj (op T)) :
    φ ∈ (killingPoints I).obj (op T) ↔ I.Kills φ.hom :=
  Iff.rfl

/-- **The points killing an ideal sheaf form a Zariski sheaf**: the functor of points is one, and
killing an ideal sheaf is local on the source. -/
theorem isSheaf_killingPoints {𝔛 : McQuillanFormalScheme.{u}} (I : IdealSheaf 𝔛.obj) :
    Presieve.IsSheaf Scheme.zariskiTopology (killingPoints I).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ (isSheaf_zariskiTopology_mcQuillanFormalSchemePoints 𝔛)]
  intro T φ hφ
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hφ
  have hopen : ∀ j, IsOpenImmersion (𝒰.f j) := fun j => 𝒰.map_prop j
  let W : 𝒰.I₀ → T.unop.Opens := fun j => (𝒰.f j).opensRange
  refine kills_of_openCover I φ.hom W
    (iSup_eq_top_of_forall_exists_mem W fun x => by
      obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
      exact ⟨j, ⟨y, hy⟩⟩) fun j => ?_
  have hj : (killingPoints I).sieveOfSection φ (𝒰.f j) := h𝒰 _ _ (Presieve.ofArrows.mk j)
  have := Sieve.downward_closed _ hj
    (IsOpenImmersion.isoOfRangeEq (W j).ι (𝒰.f j) (W j).range_ι).hom
  rwa [IsOpenImmersion.isoOfRangeEq_hom_fac (W j).ι (𝒰.f j) (W j).range_ι] at this

end AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

namespace AlgebraicGeometry

/-! ### Chosen charts -/

/-- A weak affine formal chart `X|_U ≅ Spfw A` of an open `U` of an object of `LTRS`. -/
structure WeakChart (X : LTRS.{u}) (U : Opens X) where
  /-- The weakly admissible topological ring of the chart. -/
  ring : TopCommRingCat.{u}
  /-- Its topology is linear. -/
  [linear : IsLinearTopology ring.α ring.α]
  /-- It is weakly admissible. -/
  admissible : TopologicalRing.IsWeaklyAdmissible ring.α
  /-- The chart. -/
  iso : X.restrict U ≅ spfwLTRS ring.α admissible.1

attribute [instance] WeakChart.linear

/-- A chart of a weak affine formal open, chosen. -/
noncomputable def IsWeakAffineFormalOpen.chart {X : LTRS.{u}} {U : Opens X}
    (hU : IsWeakAffineFormalOpen X U) : WeakChart X U :=
  letI := hU.choose_spec.choose
  { ring := hU.choose
    admissible := hU.choose_spec.choose_spec.1
    iso := ltrsIsoOfPresheafedSpaceIso hU.choose_spec.choose_spec.2.some }

namespace LocallyTopologicallyRingedSpace.IdealSheaf

variable {X : LTRS.{u}} (I : IdealSheaf X)
  (hI : I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen X))

/-- The weak ideal of definition of the ring of a chosen chart of a weak affine formal open `U`
corresponding to `ℐ(U)`. -/
noncomputable def chartIdeal {U : Opens X} (hU : IsWeakAffineFormalOpen X U) :
    WeakIdealsOfDefinition hU.chart.ring.α :=
  weakChartIdeal _ hU.chart.admissible hU.chart.iso (I.ideal U) (hI U hU)

/-- The affine scheme `Spec (A/ℐ(U))` attached to a chosen chart `X|_U ≅ Spfw A`. -/
noncomputable abbrev chartScheme {U : Opens X} (hU : IsWeakAffineFormalOpen X U) : Scheme.{u} :=
  Spec (spfQuotientOn hU.chart.ring.α (I.chartIdeal hI hU))

/-- The quotient point `Spec (A/ℐ(U)) → X` of a chosen chart `X|_U ≅ Spfw A`. -/
noncomputable def chartPoint {U : Opens X} (hU : IsWeakAffineFormalOpen X U) :
    schemeToLTRSObj (I.chartScheme hI hU) ⟶ X :=
  weakChartPoint _ hU.chart.admissible hU.chart.iso (I.chartIdeal hI hU)

/-- The quotient point of a chosen chart of `U` lands in `U`. -/
theorem range_chartPoint_subset {U : Opens X} (hU : IsWeakAffineFormalOpen X U) :
    Set.range (I.chartPoint hI hU).toHom.base ⊆ (U : Set X) :=
  range_weakChartPoint_subset _ _ _ _

/-- Every section of `ℐ(U)` is the image of an element of the chart ideal. -/
theorem exists_chartIdeal_of_mem {U : Opens X} (hU : IsWeakAffineFormalOpen X U)
    {t : (X.presheaf.obj (op U)).α} (ht : t ∈ I.ideal U) :
    ∃ a ∈ (I.chartIdeal hI hU).1,
      (weakChartSections _ hU.chart.admissible hU.chart.iso).1 a = t := by
  set e := weakChartSectionsRingEquiv _ hU.chart.admissible hU.chart.iso
  refine ⟨e.symm t, ?_, e.apply_symm_apply t⟩
  change (weakChartSections _ hU.chart.admissible hU.chart.iso).1 (e.symm t) ∈ I.ideal U
  exact (e.apply_symm_apply t).symm ▸ ht

/-- A point landing in `U` kills `ℐ(U)` exactly when it kills the image of the chart ideal. -/
theorem forall_mem_ideal_iff_chartIdeal {U : Opens X} (hU : IsWeakAffineFormalOpen X U)
    {Y : LTRS.{u}} (f : Y ⟶ X) :
    (∀ t ∈ I.ideal U, (f.toHom.c.app (op U)).1 t = 0) ↔
      ∀ a ∈ (I.chartIdeal hI hU).1,
        (f.toHom.c.app (op U)).1 ((weakChartSections _ hU.chart.admissible hU.chart.iso).1 a) = 0 :=
  ⟨fun h a ha => h _ ha, fun h t ht => by
    obtain ⟨a, ha, rfl⟩ := I.exists_chartIdeal_of_mem hI hU ht
    exact h a ha⟩

/-- The quotient point of a chosen chart kills `ℐ(U)`. -/
theorem chartPoint_c_app_eq_zero {U : Opens X} (hU : IsWeakAffineFormalOpen X U)
    {t : (X.presheaf.obj (op U)).α} (ht : t ∈ I.ideal U) :
    ((I.chartPoint hI hU).toHom.c.app (op U)).1 t = 0 := by
  obtain ⟨a, ha, rfl⟩ := I.exists_chartIdeal_of_mem hI hU ht
  exact (weakChartPoint_c_app_weakChartSections_eq_zero_iff _ _ _ _ a).mpr ha

variable {I hI} in
/-- For an ideal sheaf cut out by its sections over the weak affine formal opens, the quotient
point of a chosen chart kills `ℐ`. -/
theorem kills_chartPoint (hC : I.IsCutOutOn (IsWeakAffineFormalOpen X)) {U : Opens X}
    (hU : IsWeakAffineFormalOpen X U) : I.Kills (I.chartPoint hI hU) :=
  kills_of_range_subset I _ (I.range_chartPoint_subset hI hU) fun V hVU s hs =>
    mem_ker_iff.mpr (((hC U hU V hVU s).mp hs) _ _ (I.range_chartPoint_subset hI hU)
      fun _ ht => I.chartPoint_c_app_eq_zero hI hU ht)

/-- **A point killing `ℐ` and landing in a weak affine formal open `U` factors uniquely through the
quotient point `Spec (A/ℐ(U)) → X` of the chosen chart.** -/
theorem existsUnique_chartPoint_factor {U : Opens X} (hU : IsWeakAffineFormalOpen X U)
    {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ X) (hf : Set.range f.toHom.base ⊆ (U : Set X))
    (hkill : ∀ t ∈ I.ideal U, (f.toHom.c.app (op U)).1 t = 0) :
    ∃! b : T ⟶ I.chartScheme hI hU, schemeToLTRS.map b ≫ I.chartPoint hI hU = f :=
  existsUnique_weakChartPoint_factor _ _ _ _ f hf
    ((I.forall_mem_ideal_iff_chartIdeal hI hU f).mp hkill)

/-! ### The open cover of `h_ℐ` by the charts -/

section Representability

variable {𝔛 : McQuillanFormalScheme.{u}} (I : IdealSheaf 𝔛.obj)
  (hI : I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj))
  (hC : I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj))

/-- The points of `h_ℐ` are determined by their underlying morphisms of `LTRS`. -/
theorem killingPoints_ext {T : Scheme.{u}} {x y : (killingPoints I).toFunctor.obj (op T)}
    (h : x.1.hom = y.1.hom) : x = y :=
  Subtype.ext (InducedCategory.hom_ext h)

/-- The action of `h_ℐ` on a morphism of schemes is precomposition. -/
theorem killingPoints_map_hom {T T' : Scheme.{u}} (f : T' ⟶ T)
    (x : (killingPoints I).toFunctor.obj (op T)) :
    ((killingPoints I).toFunctor.map f.op x).1.hom = schemeToLTRS.map f ≫ x.1.hom :=
  rfl

/-- The Zariski sheaf `h_ℐ`. -/
noncomputable def killingPointsSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨(killingPoints I).toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr (isSheaf_killingPoints I)⟩

/-- The point of `h_ℐ` given by the quotient point of a chosen chart. -/
noncomputable def chartElement {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U) :
    (killingPoints I).toFunctor.obj (op (I.chartScheme hI hU)) :=
  ⟨ObjectProperty.homMk (I.chartPoint hI hU), kills_chartPoint hC hU⟩

/-- The morphism `h_{Spec (A/ℐ(U))} → h_ℐ` of a chosen chart. -/
noncomputable def chartMap {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U) :
    yoneda.obj (I.chartScheme hI hU) ⟶ (killingPoints I).toFunctor :=
  yonedaEquiv.symm (I.chartElement hI hC hU)

/-- The chart map sends `b : T → Spec (A/ℐ(U))` to the composite of `b` with the quotient point. -/
theorem chartMap_app_hom {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U) {T : Scheme.{u}}
    (b : T ⟶ I.chartScheme hI hU) :
    ((I.chartMap hI hC hU).app (op T) b).1.hom = schemeToLTRS.map b ≫ I.chartPoint hI hU :=
  rfl

/-- A morphism `h_T → h_ℐ` acts by precomposition on its own point. -/
theorem app_hom_eq {T T' : Scheme.{u}} (g : yoneda.obj T ⟶ (killingPoints I).toFunctor)
    (k : T' ⟶ T) : (g.app (op T') k).1.hom = schemeToLTRS.map k ≫ (yonedaEquiv g).1.hom := by
  rw [show g.app (op T') k = (killingPoints I).toFunctor.map k.op (yonedaEquiv g) by
    rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]]
  rfl

/-- The preimage of `U` under a point, as an open of the source scheme. -/
noncomputable abbrev pointPreimage {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ 𝔛.obj)
    (U : Opens 𝔛.obj) : T.Opens :=
  (Opens.map f.toHom.base).obj U

/-- The restriction of a point `f` to the preimage of `U` lands in `U`. -/
theorem range_pointPreimage_subset {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ 𝔛.obj)
    (U : Opens 𝔛.obj) :
    Set.range (schemeToLTRS.map (pointPreimage f U).ι ≫ f).toHom.base ⊆ (U : Set 𝔛.obj) := by
  rintro _ ⟨y, rfl⟩
  exact y.2

/-- A point `f : T → 𝔛` killing `ℐ`, restricted to the preimage of a weak affine formal open `U`,
factors through the quotient point of the chart of `U`. -/
private theorem exists_pointPreimage_factor {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U)
    {T : Scheme.{u}} {f : schemeToLTRSObj T ⟶ 𝔛.obj} (hf : I.Kills f) :
    ∃ l : (pointPreimage f U).toScheme ⟶ I.chartScheme hI hU,
      schemeToLTRS.map l ≫ I.chartPoint hI hU = schemeToLTRS.map (pointPreimage f U).ι ≫ f :=
  (I.existsUnique_chartPoint_factor hI hU _ (range_pointPreimage_subset f U)
    fun _ ht => mem_ker_iff.mp ((hf.comp _) U ht)).exists

/-- **The chart map of `h_ℐ` is a pullback of the inclusion of the preimage of `U`.** Given a
point `φ : T → 𝔛` killing `ℐ`, the square with vertices `φ⁻¹(U)`, `Spec (A/ℐ(U))`, `T` and `h_ℐ`
is cartesian: a point of `T` together with one of `Spec (A/ℐ(U))` having the same image lands in
`φ⁻¹(U)`, and the factorisation through the quotient point is unique. -/
theorem isPullback_chartMap {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U)
    {T : Scheme.{u}} (g : yoneda.obj T ⟶ (killingPoints I).toFunctor)
    (l : (pointPreimage (yonedaEquiv g).1.hom U).toScheme ⟶ I.chartScheme hI hU)
    (hl : schemeToLTRS.map l ≫ I.chartPoint hI hU =
      schemeToLTRS.map (pointPreimage (yonedaEquiv g).1.hom U).ι ≫ (yonedaEquiv g).1.hom) :
    IsPullback (yoneda.map l) (yoneda.map (pointPreimage (yonedaEquiv g).1.hom U).ι)
      (I.chartMap hI hC hU) g := by
  have hcomp : ∀ {T' : Scheme.{u}} (k : T' ⟶ (pointPreimage (yonedaEquiv g).1.hom U).toScheme),
      schemeToLTRS.map (k ≫ l) ≫ I.chartPoint hI hU =
        schemeToLTRS.map (k ≫ (pointPreimage (yonedaEquiv g).1.hom U).ι) ≫
          (yonedaEquiv g).1.hom :=
    fun k => (congrArg (· ≫ I.chartPoint hI hU) (schemeToLTRS.map_comp k l)).trans
      ((Category.assoc _ _ _).trans ((congrArg (schemeToLTRS.map k ≫ ·) hl).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ (yonedaEquiv g).1.hom) (schemeToLTRS.map_comp k _).symm))))
  refine IsPullback.of_forall_isPullback_app fun T' => ?_
  induction T' using Opposite.rec with
  | op T' =>
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext k
    refine I.killingPoints_ext ?_
    change ((I.chartMap hI hC hU).app (op T') (k ≫ l)).1.hom =
      (g.app (op T') (k ≫ (pointPreimage (yonedaEquiv g).1.hom U).ι)).1.hom
    rw [chartMap_app_hom, app_hom_eq]
    exact hcomp k
  · rintro (k₁ : T' ⟶ _) (k₂ : T' ⟶ _) ⟨-, h₂⟩
    exact (cancel_mono (pointPreimage (yonedaEquiv g).1.hom U).ι).mp h₂
  · intro (x : T' ⟶ I.chartScheme hI hU) (y : T' ⟶ T) hxy
    have hxy' : schemeToLTRS.map x ≫ I.chartPoint hI hU =
        schemeToLTRS.map y ≫ (yonedaEquiv g).1.hom := by
      have := congrArg (fun z => z.1.hom) hxy
      simp only at this
      rwa [chartMap_app_hom, app_hom_eq] at this
    have hyU : ∀ z, (schemeToLTRS.map y ≫ (yonedaEquiv g).1.hom).toHom.base z ∈
        (U : Set 𝔛.obj) := fun z => by
      rw [← hxy']
      exact I.range_chartPoint_subset hI hU (Set.mem_range_self _)
    have hyW : Set.range y ⊆ Set.range (pointPreimage (yonedaEquiv g).1.hom U).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hyU z
    refine ⟨IsOpenImmersion.lift _ y hyW, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    have hkey : schemeToLTRS.map (IsOpenImmersion.lift _ y hyW ≫ l) ≫ I.chartPoint hI hU =
        schemeToLTRS.map y ≫ (yonedaEquiv g).1.hom := by
      rw [hcomp, IsOpenImmersion.lift_fac]
    obtain ⟨b, -, huniq⟩ := I.existsUnique_chartPoint_factor hI hU
      (schemeToLTRS.map y ≫ (yonedaEquiv g).1.hom)
      (fun _ ⟨z, hz⟩ => hz ▸ hyU z) fun t ht => mem_ker_iff.mp (((yonedaEquiv g).2.comp _) U ht)
    exact (huniq _ hkey).trans (huniq x hxy').symm

/-- **The chart maps of `h_ℐ` are relatively representable open immersions.** -/
theorem isOpenImmersion_presheaf_chartMap {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U) :
    IsOpenImmersion.presheaf (I.chartMap hI hC hU) := by
  refine MorphismProperty.relative.of_exists fun T g => ?_
  obtain ⟨l, hl⟩ := I.exists_pointPreimage_factor hI hU (yonedaEquiv g).2
  exact ⟨_, yoneda.map l, (pointPreimage (yonedaEquiv g).1.hom U).ι,
    I.isPullback_chartMap hI hC hU g l hl, inferInstance⟩

/-- The index set of the chart cover of `h_ℐ`: the weak affine formal opens. -/
abbrev ChartIndex (X : LTRS.{u}) : Type u := {U : Opens X // IsWeakAffineFormalOpen X U}

/-- The chart maps of `h_ℐ`, indexed by the weak affine formal opens. -/
noncomputable abbrev chartFamily (i : ChartIndex 𝔛.obj) :
    yoneda.obj (I.chartScheme hI i.2) ⟶ (I.killingPointsSheaf).1 :=
  I.chartMap hI hC i.2

/-- **The chart maps of `h_ℐ` are jointly surjective, Zariski locally.** A point `φ : T → 𝔛`
killing `ℐ` restricts, on the preimage of each weak affine formal open, to a point factoring
through the quotient point of the chart, and these preimages cover `T`, `𝔛` being covered by weak
affine formal opens. -/
theorem isLocallySurjective_sigmaDesc_chartFamily (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc (I.chartFamily hI hC)) := by
  refine ⟨fun {T} s => ?_⟩
  choose U hxU hU using (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen _).mp h𝔛
  let W : T → T.Opens := fun p => pointPreimage s.1.hom (U (s.1.hom.toHom.base p))
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun p => (W p).toScheme) (fun p => (W p).ι)
    (fun p => ⟨p, ⟨p, hxU _⟩, rfl⟩), ?_⟩
  rintro _ _ ⟨p⟩
  obtain ⟨l, hl⟩ := I.exists_pointPreimage_factor hI (hU (s.1.hom.toHom.base p)) s.2
  refine ⟨(Sigma.ι (fun i : ChartIndex 𝔛.obj => yoneda.obj (I.chartScheme hI i.2))
    ⟨_, hU (s.1.hom.toHom.base p)⟩).app _ l, ?_⟩
  have h := congrArg (fun η => η.app (op (W p).toScheme) l)
    (Sigma.ι_comp_desc (I.chartFamily hI hC) ⟨_, hU (s.1.hom.toHom.base p)⟩)
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h.trans (I.killingPoints_ext hl)

/-- **The scheme `(𝔛, 𝒪_𝔛/ℐ)` of Stacks 0AIV**: the scheme representing the points of a
McQuillan formal scheme `𝔛` killing a weak ideal of definition `ℐ` cut out by its sections over
the weak affine formal opens, glued from the affine schemes `Spec (A/ℐ(𝔘))` of the charts
`𝔘 ≅ Spfw A`. -/
noncomputable def quotientScheme : Scheme.{u} :=
  (Scheme.LocalRepresentability.glueData (F := I.killingPointsSheaf)
    (fun i : ChartIndex 𝔛.obj => I.isOpenImmersion_presheaf_chartMap hI hC i.2)).glued

/-- **The scheme `(𝔛, 𝒪_𝔛/ℐ)` represents the points of `𝔛` killing `ℐ`.** -/
noncomputable def quotientSchemeRepresentableBy (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    (killingPoints I).toFunctor.RepresentableBy (I.quotientScheme hI hC) :=
  haveI := I.isLocallySurjective_sigmaDesc_chartFamily hI hC h𝔛
  Scheme.LocalRepresentability.representableBy (F := I.killingPointsSheaf)
    (fun i : ChartIndex 𝔛.obj => I.isOpenImmersion_presheaf_chartMap hI hC i.2)

/-- The morphism `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` of Stacks 0AIV: the inclusion of the points killing
`ℐ`. -/
noncomputable def quotientMorphism (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    yoneda.obj (I.quotientScheme hI hC) ⟶ mcQuillanFormalSchemePoints 𝔛 :=
  (I.quotientSchemeRepresentableBy hI hC h𝔛).toIso.hom ≫ (killingPoints I).ι

/-- The obvious morphism `(𝔛, 𝒪_𝔛/ℐ) → 𝔛` of Stacks 0AIV, as a morphism of `LTRS`. -/
noncomputable def quotientPoint (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    schemeToLTRSObj (I.quotientScheme hI hC) ⟶ 𝔛.obj :=
  (yonedaEquiv (I.quotientMorphism hI hC h𝔛)).hom

/-- The morphism `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` sends `k` to the underlying point of the element of
`h_ℐ` that `k` represents. -/
theorem quotientMorphism_app (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) {T : Scheme.{u}}
    (k : T ⟶ I.quotientScheme hI hC) :
    (I.quotientMorphism hI hC h𝔛).app (op T) k =
      ((I.quotientSchemeRepresentableBy hI hC h𝔛).homEquiv k).1 :=
  rfl

/-- The obvious morphism `(𝔛, 𝒪_𝔛/ℐ) → 𝔛` kills `ℐ`. -/
theorem kills_quotientPoint (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    I.Kills (I.quotientPoint hI hC h𝔛) :=
  ((I.quotientSchemeRepresentableBy hI hC h𝔛).homEquiv (𝟙 _)).2

/-- The points of `(𝔛, 𝒪_𝔛/ℐ)` are carried to points of `𝔛` by composition with the morphism
`(𝔛, 𝒪_𝔛/ℐ) → 𝔛`. -/
theorem quotientMorphism_app_hom (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) {T : Scheme.{u}}
    (k : T ⟶ I.quotientScheme hI hC) :
    ((I.quotientMorphism hI hC h𝔛).app (op T) k).hom =
      schemeToLTRS.map k ≫ I.quotientPoint hI hC h𝔛 := by
  rw [quotientMorphism_app, (I.quotientSchemeRepresentableBy hI hC h𝔛).homEquiv_eq]
  rfl

/-- **A point of `𝔛` kills `ℐ` exactly when it factors, uniquely, through `(𝔛, 𝒪_𝔛/ℐ)`.** -/
theorem existsUnique_quotientPoint_factor (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) {T : Scheme.{u}}
    (f : schemeToLTRSObj T ⟶ 𝔛.obj) (hf : I.Kills f) :
    ∃! k : T ⟶ I.quotientScheme hI hC, schemeToLTRS.map k ≫ I.quotientPoint hI hC h𝔛 = f := by
  set e := I.quotientSchemeRepresentableBy hI hC h𝔛
  let x : (killingPoints I).toFunctor.obj (op T) := ⟨ObjectProperty.homMk f, hf⟩
  have hx : (I.quotientMorphism hI hC h𝔛).app (op T) (e.homEquiv.symm x) = x.1 :=
    congrArg Subtype.val (e.homEquiv.apply_symm_apply x)
  refine ⟨e.homEquiv.symm x,
    (I.quotientMorphism_app_hom hI hC h𝔛 (e.homEquiv.symm x)).symm.trans
      (congrArg (fun z => z.hom) hx), fun k hk => e.homEquiv.injective ?_⟩
  refine (I.killingPoints_ext ?_).trans (e.homEquiv.apply_symm_apply x).symm
  exact (I.quotientMorphism_app_hom hI hC h𝔛 k).trans hk

end Representability

end LocallyTopologicallyRingedSpace.IdealSheaf

end AlgebraicGeometry

end
