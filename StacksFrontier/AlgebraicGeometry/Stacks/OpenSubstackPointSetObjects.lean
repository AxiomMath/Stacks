module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackFiniteSubcover
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingLocus

/-!
# An open substack is cut out by its points

Let `𝒳` be an algebraic stack over `S` and let `𝒰 ⊆ 𝒳` be an open substack. An object of `𝒳`
every point seen by which lies in `|𝒰|` is an object of `𝒰`, so the objects of `𝒰` are exactly
those of `AlgebraicGeometry.Stack.pointsWithin 𝒳 |𝒰|`. This is the injectivity of the bijection
`𝒰 ↦ |𝒰|` from the open substacks of `𝒳` onto the open subsets of `|𝒳|`.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.property_of_pointsWithin`: an object every point seen by
  which lies in `|𝒰|` lies in `𝒰`.
* `AlgebraicGeometry.Stack.OpenSubstack.property_eq_pointsWithin`: the objects of `𝒰` are those
  of `AlgebraicGeometry.Stack.pointsWithin 𝒳 |𝒰|`.
* `AlgebraicGeometry.Stack.OpenSubstack.exists_isOpenImmersion_property_of_pointsWithin_iUnion`:
  an object every point seen by which lies in `⋃ᵢ |𝒰ᵢ|` lies, locally on an open cover of its
  base, in one of the `𝒰ᵢ`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

namespace OpenSubstack

/-- An object of an algebraic stack every point seen by which lies in the point set of an open
substack `𝒰` is an object of `𝒰`. -/
theorem property_of_pointsWithin (U : OpenSubstack 𝒳) {x : 𝒳.val.val.obj}
    (hx : pointsWithin 𝒳 (U.pointSet B S hS) x) : U.property x := by
  classical
  set p := 𝒳.val.val.p with hpdef
  have hfib := 𝒳.val.property
  have _ := U.strictlyFull
  have hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → U.property b → U.property a :=
    fun m h => OpenSubstack.prop_of_hom B S hS U m h
  set T := p.obj x with hTdef
  obtain ⟨y, hy, ξ, hξ⟩ := StacksRepresentableCFG.exists_pointOverMap_of_obj p hfib T x rfl
  refine U.property.prop_of_iso ξ ?_
  have hT' : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) = T := Functor.overMap_obj_mkId T
  set Sub := fullSubcategoryBaseChangeSubfunctor 𝒳 hP y with hSubdef
  obtain ⟨E⟩ := nonempty_equivalenceOver_fullSubcategoryBaseChange 𝒳 hP y hy
  obtain ⟨F, hF, ⟨eF⟩⟩ := U.isOpenImmersion.1 T y hy
  have hSub : IsAlgebraicSpace B T.left.1 T.left.2 Sub.toFunctor :=
    isAlgebraicSpace_of_iso B T.left.1 T.left.2
      (PresheafOfCategories.isoOfEquivalenceOver E eF) hF
  have hOI := U.isOpenImmersion.2 T y hy Sub.toFunctor hSub ⟨E⟩
  have _ : (Space.openImmersionProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hOI' : Space.IsOpenImmersion B S hS (OverShriek.relocalizeToYoneda T.hom Sub.toFunctor) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.openImmersionProperty B S hS) T
      Sub.toFunctor hSub).mp hOI
  set Range := Subfunctor.range (OverShriek.relocalizeToYoneda T.hom Sub.toFunctor)
  have hRange : Space.IsOpenSubspace B S hS Range :=
    Space.isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace B S hS _
      (isAlgebraicSpace_viewOver B T.left.1 S T.left.2 hS T.hom Sub.toFunctor hSub) hOI'
  have hx' : pointsWithin 𝒳 (U.pointSet B S hS) (y.obj (Over.mk (𝟙 T.left))) :=
    pointsWithin_of_hom 𝒳 _ ξ.hom hx
  have hlift : ∀ (c : BigFppfOver B T.left.1 T.left.2) (t : c ⟶ Over.mk (𝟙 T.left)),
      p.IsHomLift ((Over.map T.hom).map t ≫ eqToHom hT') (y.map t ≫ ξ.hom) := fun c t => by
    have : p.IsHomLift ((Over.map T.hom).map t) (y.map t) :=
      Functor.isHomLift_map_of_comp_eq hy ((Over.map T.hom).map t) t
    have := hξ
    infer_instance
  have hpts : ∀ v : Space.points B S hS (yoneda.obj T),
      v ∈ Set.range (Space.pointsMap B S hS Range.toFunctor Range.ι) := by
    intro v
    obtain ⟨pv, hpv⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS T
      (Space.pointsToScheme B S hS T v)
    let a : BigFppfOver B T.left.1 T.left.2 := Over.mk pv.value.left
    let ta0 : a ⟶ Over.mk (𝟙 T.left) := Over.homMk pv.value.left (Category.comp_id _)
    let r0 : FieldValuedPoint B S hS 𝒳.val.val :=
      { carrier := pv.carrier
        base := (Over.map T.hom).obj a
        isSpec := Iso.refl _
        obj := y.obj a
        «over» := Functor.congr_obj hy a }
    have hcls := hx' r0 (y.map ta0)
    obtain ⟨q', hq', hcl⟩ := (OpenSubstack.mem_pointSet_iff B S hS U _).1 hcls
    obtain ⟨r, ⟨m1⟩, ⟨m⟩⟩ :=
      (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val 𝒳.val.property q' r0).1 hcl
    have hr : U.property r.obj := hP m1 hq'
    let m' : r.obj ⟶ x := m ≫ y.map ta0 ≫ ξ.hom
    let tt : p.obj r.obj ⟶ T := p.map m'
    let a' : BigFppfOver B T.left.1 T.left.2 := Over.mk tt.left
    let ta : a' ⟶ Over.mk (𝟙 T.left) := Over.homMk tt.left (Category.comp_id _)
    let e : (Over.map T.hom).obj a' ⟶ p.obj r.obj := Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ _ = tt.left ≫ T.hom
      rw [Category.id_comp, Over.w tt])
    have he : (Over.map T.hom).map ta ≫ eqToHom hT' = e ≫ tt := by
      ext
      simp [e, ta, a']
    have _ : p.IsHomLift tt m' := IsHomLift.map p m'
    have _ : p.IsStronglyCartesian tt m' := hfib.isStronglyCartesian_homLift tt m'
    have := hlift _ ta
    let k : y.obj a' ⟶ r.obj := Functor.IsStronglyCartesian.map p tt m' he (y.map ta ≫ ξ.hom)
    have hza : U.property (y.obj a') := hP k hr
    let W'' : BigFppfOver B S hS := (Over.map T.hom).obj a'
    let elt : ((OverShriek.relocalizePresheafFunctor T.hom).obj Sub.toFunctor).obj (op W'') :=
      ⟨⟨tt.left, ⟨ta, hza⟩⟩, rfl⟩
    let g : W'' ⟶ T := Over.homMk tt.left rfl
    let σ : yoneda.obj W'' ⟶ Range.toFunctor := yonedaEquiv.symm ⟨g, elt, rfl⟩
    have hσ : σ ≫ Range.ι = yoneda.map g := by
      ext Z f
      rfl
    have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj W'') := by
      show Nonempty ((BigFppfOver.toScheme B S hS).obj (p.obj r.obj))
      rw [r.over]
      exact ⟨r.isSpec.inv (Classical.arbitrary _)⟩
    obtain ⟨w0⟩ := hne
    obtain ⟨q'', hq''⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS W'' w0
    refine ⟨Space.pointsMap B S hS (yoneda.obj W'') σ (q''.class B S hS _), ?_⟩
    apply Space.injective_pointsToScheme B S hS T
    rw [← Space.pointsMap_comp_apply, hσ, Space.pointsToScheme_pointsMap_yoneda,
      Space.pointsToScheme_class, hq'', ← hpv]
    have hm0 : p.IsHomLift (p.map m ≫ eqToHom (Functor.congr_obj hy a)) m := by
      infer_instance
    have hm' : p.IsHomLift ((p.map m ≫ eqToHom (Functor.congr_obj hy a)) ≫
        ((Over.map T.hom).map ta0 ≫ eqToHom hT')) m' := by
      have := hm0
      have := hlift _ ta0
      exact IsHomLift.comp p _ _ m (y.map ta0 ≫ ξ.hom)
    have htt : tt = (p.map m ≫ eqToHom (Functor.congr_obj hy a)) ≫
        ((Over.map T.hom).map ta0 ≫ eqToHom hT') := by
      have := IsHomLift.fac' p ((p.map m ≫ eqToHom (Functor.congr_obj hy a)) ≫
        ((Over.map T.hom).map ta0 ≫ eqToHom hT')) m'
      simpa using this
    show B.inclusion.map tt.left w0 = B.inclusion.map pv.value.left _
    rw [htt]
    simp only [Over.comp_left, Functor.map_comp, Scheme.Hom.comp_apply]
    have hsub : Subsingleton (B.inclusion.obj a.left) := by
      show Subsingleton (Spec (.of pv.carrier))
      infer_instance
    exact congrArg (fun z => (B.inclusion.map pv.value.left) z) (@Subsingleton.elim _ hsub _ _)
  have hle : (⊤ : Subfunctor (yoneda.obj T)) ≤ Range :=
    Space.le_of_range_pointsMap_ι_subset B S hS hRange (by
      rintro _ ⟨v, rfl⟩
      exact hpts _)
  obtain ⟨e, he⟩ := hle (op T) (Set.mem_univ (𝟙 T))
  obtain ⟨⟨ψ, s⟩, hψ⟩ := e
  have hψ1 : ψ = 𝟙 T.left := congrArg CommaMorphism.left he
  subst hψ1
  exact s.2

/-- The objects of an open substack are exactly the objects every point seen by which lies in its
point set. -/
theorem property_eq_pointsWithin (U : OpenSubstack 𝒳) :
    U.property = pointsWithin 𝒳 (U.pointSet B S hS) :=
  funext fun _ => propext ⟨fun hx => U.pointsWithin_pointSet B S hS hx,
    fun hx => U.property_of_pointsWithin hx⟩

end OpenSubstack

/-! ### Local membership in a union of open substacks -/

/-- For an open set `Ω` of points of `𝒳` and a scheme-valued point `y` of `𝒳` with values in
`U`, there is an open `V` of the scheme `U` containing exactly the points of `U` whose image in
`|𝒳|` lies in `Ω`, and an object `T` of the big fppf site of `U` maps into `V` exactly when every
point of `|𝒳|` seen by `y T` lies in `Ω`. -/
theorem exists_isOpen_mem_iff_and_pointsWithin_iff (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property))
    (hΩ : @IsOpen _ (pointTopology B S hS 𝒳.val) Ω) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen V ∧
      (∀ z, pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
          𝒳.val.property ⟨y, hy⟩ z ∈ Ω ↔ schemeSlicePoint U z ∈ V) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        pointsWithin 𝒳 Ω (y.obj T) ↔ Set.range (B.inclusion.map T.hom) ⊆ V := by
  let F : (schemeSlice B S hS U).val ⥤ᵇ 𝒳.val.val := ⟨y, hy⟩
  let := pointTopology B S hS (schemeSlice B S hS U)
  let := pointTopology B S hS 𝒳.val
  have hΩ' := (continuous_pointsMap B S hS (schemeSlice B S hS U) 𝒳.val F).isOpen_preimage Ω hΩ
  obtain ⟨V, hV, hΩV⟩ := exists_isOpen_mem_iff_schemeSlicePoint_mem U _ hΩ'
  refine ⟨V, hV, hΩV, fun T => ?_⟩
  rw [← forall_mem_of_hom_iff_range_subset hΩV T]
  exact pointsWithin_obj_iff 𝒳 F Ω T

namespace OpenSubstack

/-- Let `y` be a scheme-valued point of `𝒳` with values in `T` such that every point of `|𝒳|`
seen by `y T` lies in `⋃ᵢ |𝒰ᵢ|`. Then every point of `T` lies in an open subscheme `V ⊆ T` such
that `y V` is an object of one of the `𝒰ᵢ`. -/
theorem exists_isOpenImmersion_property_of_pointsWithin_iUnion {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map T.hom)
    (hW : pointsWithin 𝒳 (⋃ i, (𝒰 i).pointSet B S hS) (y.obj (Over.mk (𝟙 T.left))))
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (V : BigFppfOver B T.left.1 T.left.2) (j : V ⟶ Over.mk (𝟙 T.left)),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B T.left.1 T.left.2).map j) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B T.left.1 T.left.2).map j) ∧
      ∃ i, (𝒰 i).property (y.obj V) := by
  let F : (schemeSlice B S hS T).val ⥤ᵇ 𝒳.val.val := ⟨y, hy⟩
  obtain ⟨z, hz⟩ : ∃ z, schemeSlicePoint T z = t := by
    obtain ⟨p, hp⟩ := Space.exists_fieldValuedPoint_schemePoint_eq B S hS T t
    exact ⟨_, (schemeSlicePoint_spacePointMap T p).trans hp⟩
  have hFz : pointsMap B S hS (schemeSlice B S hS T).val (schemeSlice B S hS T).property
      𝒳.val.property F z ∈ ⋃ i, (𝒰 i).pointSet B S hS := by
    induction z using Quotient.inductionOn with
    | h r => exact (pointsWithin_obj_iff 𝒳 F _ _).1 hW r (Over.mkIdTerminal.from r.obj)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hFz
  obtain ⟨Vi, hVi, hΩVi, hVT⟩ := exists_isOpen_mem_iff_and_pointsWithin_iff 𝒳 _
    ((𝒰 i).isOpen_pointSet B S hS) T y hy
  have htV : t ∈ Vi := hz ▸ (hΩVi z).1 hi
  obtain ⟨V, j, hj, hjrange, -⟩ := exists_restrict_bigFppfOver
    (Over.mk (𝟙 (B.obj T.left.2)) : BigFppfOver B T.left.1 T.left.2) ⟨Vi, hVi⟩
  refine ⟨V, j, hj, hjrange ▸ htV, i, ?_⟩
  refine (𝒰 i).property_of_pointsWithin ((hVT V).2 ?_)
  have hVhom : V.hom = j.left := by simpa using (Over.w j).symm
  rw [hVhom]
  exact hjrange.subset

end OpenSubstack

end AlgebraicGeometry.Stack

end
