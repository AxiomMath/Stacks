module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace.ZeroPointNeighbourhoods

/-!
# Finiteness over a dense open subspace: the quasi-compact and the separated cases

Points of codimension zero which all have open neighbourhoods lie in a single dense open
subspace. An open subspace containing every point of codimension zero whose range on points is
closed is the whole space (Stacks 0BAR), and a morphism whose composite with a separated
morphism is finite has closed range on points. With this, a quasi-separated morphism of finite
type whose fibres over the points of codimension zero are finite is finite over a dense open
subspace of the target (Stacks 0ACZ), and so is a separated morphism locally of finite type,
via quasi-separated open neighbourhoods of the points of codimension zero (Stacks 0AD0).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology
attribute [local instance] CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_QuasiCompactAndSeparatedCases :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_QuasiCompactAndSeparatedCases
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Small products of presheaves on the big fppf site (needed by `simp` side goals; instance
search times out without this shortcut). -/
local instance (priority := high) hasProducts_presheaf_QuasiCompactAndSeparatedCases :
    HasProducts.{0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

open FiniteOverDense

private lemma exists_dense_open_subspace_containing_zero_points
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hnear : ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        ∃ V : Subfunctor Y,
          IsOpenSubspace B S hS V ∧
          y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)) :
    letI := pointTopology B S hS Y
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
      Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
      (∀ y : points B S hS Y,
        localRingDimension B S hS y = 0 →
          y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
  let : TopologicalSpace (points B S hS Y) :=
    pointTopology B S hS Y
  let e := openSubspacesOrderIso B S hS Y hY
  let I := {y : points B S hS Y |
    localRingDimension B S hS y = 0}
  let V₀ : I → {W : Subfunctor Y // IsOpenSubspace B S hS W} :=
    fun y => ⟨(hnear y.1 y.2).choose, (hnear y.1 y.2).choose_spec.1⟩
  let O : TopologicalSpace.Opens (points B S hS Y) :=
    ⨆ y : I, e (V₀ y)
  let Vdata := e.symm O
  let V : Subfunctor Y := Vdata.1
  have hV : IsOpenSubspace B S hS V := Vdata.2
  have hEv : e Vdata = O := by
    show e (e.symm O) = O
    exact e.apply_symm_apply O
  have hImage : Set.range (pointsMap B S hS V.toFunctor V.ι) =
      (O : Set (points B S hS Y)) := by
    rw [← hEv]
    exact (openSubspacesOrderIso_apply
      B S hS Y hY Vdata).symm
  have hzero : {y : points B S hS Y |
      localRingDimension B S hS y = 0} ⊆
      (O : Set (points B S hS Y)) := by
    intro y hy
    let i : I := ⟨y, hy⟩
    have hyi : y ∈ (e (V₀ i) : Set (points B S hS Y)) := by
      show y ∈ (e (V₀ i)).1
      rw [openSubspacesOrderIso_apply
        B S hS Y hY (V₀ i)]
      exact (hnear y hy).choose_spec.2
    exact (le_iSup (fun i : I => e (V₀ i)) i) hyi
  have hdense : Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
    rw [hImage]
    exact (codimensionZeroPoints_dense B S hS hY).mono hzero
  refine ⟨V, hV, hdense, ?_⟩
  intro y hy
  rw [hImage]
  exact hzero hy

private noncomputable def topSubfunctorIso'
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    (⊤ : Subfunctor X).toFunctor ≅ X :=
  { hom := (⊤ : Subfunctor X).ι
    inv := Subfunctor.lift (𝟙 X) (by intro T x hx; simp)
    hom_inv_id := by ext T x; rfl
    inv_hom_id := by ext T x; rfl }

private theorem top_isOpenSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    IsOpenSubspace B S hS (⊤ : Subfunctor X) := by
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))
  let : Q.RespectsIso := inferInstance
  exact ⟨algebraicSpace_of_iso B S hS (topSubfunctorIso' (X := X)).symm hX,
    MorphismProperty.RespectsIso.postcomp Q (⊤ : Subfunctor X).ι
      (𝟙 ((⊤ : Subfunctor X).toFunctor)) (Q.id_mem _)⟩

private theorem openSubspace_eq_top_of_closed_range_points
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U)
    (hclosed : @IsClosed _ (pointTopology B S hS F)
      (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hzero : {x : points B S hS F |
        localRingDimension B S hS x = 0} ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    U = ⊤ := by
  let : TopologicalSpace (points B S hS F) :=
    pointTopology B S hS F
  have hdense : Dense
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    (codimensionZeroPoints_dense B S hS hF).mono hzero
  have hrange : Set.range (pointsMap B S hS U.toFunctor U.ι) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ closure
        (Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
      rw [(dense_iff_closure_eq.mp hdense)]
      simp
    rwa [hclosed.closure_eq] at hx
  let e := openSubspacesOrderIso B S hS F hF
  let Udata : {W : Subfunctor F // IsOpenSubspace B S hS W} := ⟨U, hU⟩
  let topData : {W : Subfunctor F // IsOpenSubspace B S hS W} :=
    ⟨⊤, top_isOpenSubspace B S hS hF⟩
  have htoprange : Set.range
      (pointsMap B S hS topData.1.toFunctor topData.1.ι) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let eTop := topSubfunctorIso' (X := F)
    refine ⟨pointsMap B S hS F eTop.inv x, ?_⟩
    have hcomp := congrFun (pointsMap_comp B S hS _ eTop.inv eTop.hom) x
    rw [eTop.inv_hom_id] at hcomp
    rw [pointsMap_id'] at hcomp
    simpa [topData, eTop, topSubfunctorIso'] using hcomp.symm
  have htop : e Udata = e topData := by
    ext x
    show x ∈ (e Udata).1 ↔ x ∈ (e topData).1
    rw [openSubspacesOrderIso_apply
      B S hS F hF Udata,
      openSubspacesOrderIso_apply
      B S hS F hF topData]
    rw [hrange, htoprange]
  exact congrArg Subtype.val (e.injective htop)

private theorem isClosed_range_of_finite_factor_through_separated
    {A P V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A)
    (hP : IsAlgebraicSpace B S hS P)
    (hV : IsAlgebraicSpace B S hS V)
    (j : A ⟶ P) (q : P ⟶ V) (g : A ⟶ V)
    (hcomm : j ≫ q = g)
    (hg : IsFinite B S hS g)
    (hq : IsSeparated B S hS q) :
    @IsClosed _ (pointTopology B S hS P)
      (Set.range (pointsMap B S hS A j)) := by
  have hclosed : UniversallyClosed B S hS g :=
    ((isFinite_iff_isAffineHom_and_isProper B S hS hA hV g).mp hg).2.2.2
  have hclosed' : UniversallyClosed B S hS (j ≫ q) :=
    hcomm.symm ▸ hclosed
  exact isClosed_range_of_comp_of_isSeparated B S hS
    hA hP hV j q hclosed' hq

private theorem isFinite_of_openSubspace_finite_closed_range_contains_zero
    {F V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAlgebraicSpace B S hS V)
    (U : Subfunctor F) (hU : IsOpenSubspace B S hS U)
    (j : U.toFunctor ⟶ F) (q : F ⟶ V) (g : U.toFunctor ⟶ V)
    (hj : j = U.ι) (hcomm : j ≫ q = g)
    (hfinite : IsFinite B S hS g)
    (hq : IsSeparated B S hS q)
    (hzero : {x : points B S hS F |
        localRingDimension B S hS x = 0} ⊆
      Set.range (pointsMap B S hS U.toFunctor j)) :
    IsFinite B S hS q := by
  have hclosed := isClosed_range_of_finite_factor_through_separated
    B S hS hU.1 hF hV j q g hcomm hfinite hq
  have htop : U = ⊤ := openSubspace_eq_top_of_closed_range_points
    B S hS hF U hU (by simpa only [hj] using hclosed)
      (by simpa only [hj] using hzero)
  let e₁ : U.toFunctor ≅ (⊤ : Subfunctor F).toFunctor :=
    eqToIso (congrArg Subfunctor.toFunctor htop)
  let e₂ := e₁ ≪≫ topSubfunctorIso' (X := F)
  have he : e₂.hom = j := by
    cases htop
    simp [e₂, e₁, topSubfunctorIso', hj]
  apply isFinite_of_arrowIso B S hS g q e₂ (Iso.refl V) ?_ hfinite
  simpa [he] using hcomm

private theorem finite_pullback_of_finite_open_subspace_covering_zero_points
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (f : X ⟶ Y) (g : U.toFunctor ⟶ V.toFunctor)
    (hcomm : g ≫ V.ι = U.ι ≫ f)
    (hfinite : IsFinite B S hS g)
    (hq : IsSeparated B S hS (pullback.snd f V.ι))
    (hzero : {x : points B S hS (pullback f V.ι) |
        localRingDimension B S hS x = 0} ⊆
      Set.range (pointsMap B S hS
        (U.preimage (pullback.fst f V.ι)).toFunctor
        (U.preimage (pullback.fst f V.ι)).ι)) :
    IsFinite B S hS (pullback.snd f V.ι) := by
  let : Mono V.ι := mono_of_isOpenImmersion B S hS V.ι hV.2
  let A := U.preimage (pullback.fst f V.ι)
  have hA : IsOpenSubspace B S hS A :=
    isOpenSubspace_preimage B S hS (pullback.fst f V.ι) U hX
      (isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY) hU
  let e := openPreimageFactorIso f V.ι U g hcomm
  let g' : A.toFunctor ⟶ V.toFunctor := e.hom ≫ g
  have hfinite' : IsFinite B S hS g' := by
    apply isFinite_of_arrowIso B S hS g g' e.symm (Iso.refl V.toFunctor) ?_ hfinite
    simp [g', e]
  have hcomm' : A.ι ≫ pullback.snd f V.ι = g' := by
    apply (cancel_mono V.ι).mp
    dsimp [g', e, openPreimageFactorIso]
    calc
      A.ι ≫ pullback.snd f V.ι ≫ V.ι = A.ι ≫ pullback.fst f V.ι ≫ f :=
        (congrArg (fun t => A.ι ≫ t) pullback.condition).symm
      _ = U.fromPreimage (pullback.fst f V.ι) ≫ U.ι ≫ f := by
        simpa only [Category.assoc] using
          congrArg (fun t => t ≫ f)
            (Subfunctor.fromPreimage_ι U (pullback.fst f V.ι)).symm
      _ = U.fromPreimage (pullback.fst f V.ι) ≫ g ≫ V.ι :=
        congrArg (fun t => U.fromPreimage (pullback.fst f V.ι) ≫ t) hcomm.symm
  exact isFinite_of_openSubspace_finite_closed_range_contains_zero
    B S hS (isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY)
    hV.1 A hA A.ι (pullback.snd f V.ι) g' rfl hcomm' hfinite' hq hzero


theorem finite_codimensionZeroPoints_of_openImmersion
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (j : X ⟶ Y) (hj : IsOpenImmersion B S hS j)
    (hfinite : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0}) :
    Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0} := by
  have : Mono j := mono_of_isOpenImmersion B S hS j hj
  exact (hfinite.preimage (pointsMap_injective_of_mono B S hS j).injOn).subset fun x hx =>
    localRingDimension_zero_map_of_openSubspace B S hS hX hY j hj x hx

private theorem pointsMap_preimage_range
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) :
    Set.range (pointsMap B S hS (U.preimage f).toFunctor
      (U.preimage f).ι) =
      (pointsMap B S hS Y f) ⁻¹'
        Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  let hP := (isOpenSubspace_preimage B S hS f U hX hY hU).1
  let P' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨(U.preimage f).toFunctor, hP⟩
  let U' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
  let X' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
  have sq : IsPullback
      (ObjectProperty.homMk (U.fromPreimage f) : P' ⟶ U')
      (ObjectProperty.homMk (U.preimage f).ι : P' ⟶ Y')
      (ObjectProperty.homMk U.ι : U' ⟶ X')
      (ObjectProperty.homMk f : Y' ⟶ X') :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
      (CategoryTheory.Subfunctor.isPullback_preimage f U)
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨pointsMap B S hS _ (U.fromPreimage f) z, ?_⟩
    have hc := congrArg (fun k => pointsMap B S hS _ k z)
      (Subfunctor.fromPreimage_ι U f)
    simpa only [pointsMap_comp, Function.comp_apply] using hc
  · rintro ⟨x, hx⟩
    obtain ⟨z, _, hz⟩ := exists_point_of_isPullback B S hS sq x y hx
    exact ⟨z, hz⟩

theorem exists_dense_open_isFinite_of_quasiSeparated_finiteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hfib : ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        Set.Finite {x : points B S hS X |
          pointsMap B S hS X f x = y}) :
    letI := pointTopology B S hS Y
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
      Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  apply exists_dense_open_isFinite_of_finite_open_neighborhoods B S hS hX hY f hYzero
  intro y hy
  obtain ⟨p, hp⟩ := Quot.exists_rep y
  apply (exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber
    B S hS hX hY f hqs hft y p hp hy)
  exact (finite_fieldFiber_iff_finite_setFiber_of_decent
    B S hS hX hY f hqs hft hYdecent y p hp).mpr (hfib y hy)

/-- The projection of an open subspace of `Y` is an open immersion. -/
private theorem isOpenImmersion_pullback_fst_of_isOpenSubspace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V) :
    IsOpenImmersion B S hS (pullback.fst f V.ι) := by
  let X' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let V' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨V.toFunctor, hV.1⟩
  have sq := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk f : X' ⟶ Y')
    (ObjectProperty.homMk V.ι : V' ⟶ Y')
  exact isOpenImmersion_of_isPullback B S hS sq.flip hV.2

private theorem isFinite_of_finite_restriction_containing_zero_points
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hzero : {x : points B S hS X |
      localRingDimension B S hS x = 0} ⊆
      Set.range (pointsMap B S hS U.toFunctor U.ι))
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hfinite : IsFinite B S hS
      (pullback.snd (U.ι ≫ f) V.ι)) :
    IsFinite B S hS (pullback.snd f V.ι) := by
  let P := pullback f V.ι
  let p : P ⟶ X := pullback.fst f V.ι
  let q : P ⟶ V.toFunctor := pullback.snd f V.ι
  let hP := isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY
  let A := U.preimage p
  have hA := isOpenSubspace_preimage B S hS p U hX hP hU
  have sq : IsPullback (U.fromPreimage p) (A.ι ≫ q) (U.ι ≫ f) V.ι :=
    (CategoryTheory.Subfunctor.isPullback_preimage p U).paste_vert (IsPullback.of_hasPullback f V.ι)
  have hAfin : IsFinite B S hS (A.ι ≫ q) := by
    apply isFinite_of_arrowIso B S hS _ _ sq.isoPullback.symm (Iso.refl _) ?_ hfinite
    simp
  have hqsep : IsSeparated B S hS q :=
    isSeparated_pullback B S hS f V.ι hsep
  have hpopen := isOpenImmersion_pullback_fst_of_isOpenSubspace B S hS hX hY f V hV
  apply isFinite_of_openSubspace_finite_closed_range_contains_zero
    B S hS hP hV.1 A hA A.ι q (A.ι ≫ q) rfl rfl hAfin hqsep
  intro x hx
  rw [pointsMap_preimage_range B S hS hX hP p U hU]
  exact hzero (localRingDimension_zero_map_of_openSubspace
    B S hS hP hX p hpopen x hx)

private theorem exists_dense_open_isFinite_of_separated_quasiSeparated_target
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hsep : IsSeparated B S hS f)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hfib : ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        Set.Finite {x : points B S hS X |
          pointsMap B S hS X f x = y}) :
    letI := pointTopology B S hS Y
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
      Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  obtain ⟨U, hU, hUqc, hcover⟩ := exists_quasiCompact_openSubspace_covering_finite
    B S hS hX _ hXzero
  have hUqs := isQuasiSeparated_of_mono B S hS U.ι inferInstance
  have hgqs := isQuasiSeparated_comp
    B S hS hU.1 hX U.ι f hUqs
      (isQuasiSeparated_of_isSeparated B S hS hsep)
  have hglft := isLocallyOfFiniteType_comp B S hS hU.1 hX hY U.ι f
    (locallyOfFiniteType_of_openImmersion B S hS hU.1 hX U.ι hU.2) hlft
  have hgqc := isQuasiCompact_of_isQuasiCompactSpace
    B S hS hZ hY hYqs hUqc (U.ι ≫ f)
  have hgfib (y) (hy : localRingDimension B S hS y = 0) :
      Set.Finite {x : points B S hS U.toFunctor |
        pointsMap B S hS U.toFunctor (U.ι ≫ f) x = y} := by
    simpa only [pointsMap_comp, Function.comp_apply, Set.preimage_ofPred_eq] using
      (hfib y hy).preimage
        (pointsMap_injective_of_mono B S hS U.ι).injOn
  obtain ⟨V, hV, hdense, hfin⟩ :=
    exists_dense_open_isFinite_of_quasiSeparated_finiteType B S hS hU.1 hY
      (U.ι ≫ f) hgqs ⟨hglft, hgqc⟩ hYdecent hYzero hgfib
  exact ⟨V, hV, hdense, isFinite_of_finite_restriction_containing_zero_points
    B S hS hX hY f hsep U hU hcover V hV hfin⟩

/-- Finiteness of a base change to `W` restricts to the image of `V ⊆ W` in `Y`. -/
private theorem isFinite_pullback_snd_range_comp
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (W : Subfunctor Y) (V : Subfunctor W.toFunctor)
    (hfin : IsFinite B S hS (pullback.snd (pullback.snd f W.ι) V.ι)) :
    IsFinite B S hS (pullback.snd f (Subfunctor.range (V.ι ≫ W.ι)).ι) := by
  let j := V.ι ≫ W.ι
  let U := Subfunctor.range j
  let : Mono j := inferInstance
  let e : V.toFunctor ≅ U.toFunctor := asIso (Subfunctor.toRange j)
  have hcomp : e.hom ≫ U.ι = V.ι ≫ W.ι := Subfunctor.toRange_ι j
  have hfin' : IsFinite B S hS
      (pullback.snd f j) := by
    apply isFinite_of_arrowIso B S hS _ _
      (pullbackLeftPullbackSndIso f W.ι V.ι) (Iso.refl _) ?_ hfin
    simp [j]
  let ep := pullback.map f j f U.ι (𝟙 X) e.hom (𝟙 Y)
    (by simp) (by simpa using hcomp.symm)
  apply isFinite_of_arrowIso B S hS _ _ (asIso ep) e ?_ hfin'
  dsimp only [ep, pullback.map]
  simpa only [asIso_hom] using pullback.lift_snd _ _ _

/-- Points of `V` map to the same point of `Y` through `V ⊆ W ⊆ Y` and through the range. -/
private theorem pointsMap_range_comp_toRange
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Subfunctor Y) (V : Subfunctor W.toFunctor) (v : points B S hS V.toFunctor) :
    pointsMap B S hS (Subfunctor.range (V.ι ≫ W.ι)).toFunctor
        (Subfunctor.range (V.ι ≫ W.ι)).ι
        (pointsMap B S hS V.toFunctor (Subfunctor.toRange (V.ι ≫ W.ι)) v) =
      pointsMap B S hS W.toFunctor W.ι (pointsMap B S hS V.toFunctor V.ι v) :=
  calc
    _ = pointsMap B S hS V.toFunctor
        (Subfunctor.toRange (V.ι ≫ W.ι) ≫ (Subfunctor.range (V.ι ≫ W.ι)).ι) v :=
      (congrFun (pointsMap_comp B S hS _ _ _) v).symm
    _ = _ := by rw [Subfunctor.toRange_ι, pointsMap_comp, Function.comp_apply]

private theorem exists_dense_open_isFinite_of_dense_open_restriction
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (W : Subfunctor Y)
    (hW : IsDenseOpenSubspace B S hS hY W)
    (V : Subfunctor W.toFunctor)
    (hV : IsDenseOpenSubspace B S hS hW.1.1 V)
    (hfin : IsFinite B S hS
      (pullback.snd (pullback.snd f W.ι) V.ι)) :
    ∃ U : Subfunctor Y,
      IsDenseOpenSubspace B S hS hY U ∧
      IsFinite B S hS (pullback.snd f U.ι) := by
  let j := V.ι ≫ W.ι
  let U := Subfunctor.range j
  let : Mono j := inferInstance
  have hU := isOpenSubspace_range_of_isAlgebraicSpace B S hS hV.1.1 j
    (isOpenImmersion_comp B S hS V.ι W.ι hV.1.2 hW.1.2)
  have hdense : @Dense _ (pointTopology B S hS Y)
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) := by
    let := pointTopology B S hS Y
    let := pointTopology B S hS W.toFunctor
    have hc := (pointTopologyFamily B S hS).continuous hW.1.1 hY W.ι
    have hd : DenseRange (pointsMap B S hS W.toFunctor W.ι ∘
        pointsMap B S hS V.toFunctor V.ι) :=
      DenseRange.comp hW.2 hV.2 hc
    apply hd.mono
    rintro _ ⟨v, rfl⟩
    exact ⟨_, pointsMap_range_comp_toRange B S hS W V v⟩
  exact ⟨U, ⟨hU, hdense⟩, isFinite_pullback_snd_range_comp B S hS f W V hfin⟩

private theorem exists_affine_open_neighborhood_of_representable
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hrep : Y.IsRepresentable) (y : points B S hS Y) :
    ∃ (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsOpenImmersion B S hS j ∧
      y ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) := by
  classical
  obtain ⟨T, ⟨r⟩⟩ := hrep.has_representation
  let e : yoneda.obj T ≅ Y := Functor.representableByEquiv r
  let Q := BigFppfOver.toScheme B S hS
  obtain ⟨p, hp⟩ := Quot.exists_rep
    (pointsMap B S hS Y e.inv y)
  change p.class B S hS (yoneda.obj T) = pointsMap B S hS Y e.inv y at hp
  let m : p.siteObject B S hS (yoneda.obj T) ⟶ T := p.value
  let z := Q.map m (IsLocalRing.closedPoint p.carrier)
  obtain ⟨A, hA, hzA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Q.obj T) (U := ⊤) (x := z) trivial
  have hAcontains : B.Contains A.toScheme :=
    (Scheme.size_coe_opens_le (Q.obj T) A).trans_lt T.left.2
  let kScheme : B.inclusion.obj (B.obj hAcontains) ⟶ B.inclusion.obj T.left := A.ι
  let k₀ : B.obj hAcontains ⟶ T.left := B.inclusion.preimage kScheme
  let U : BigFppfOver B S hS := Over.mk (k₀ ≫ T.hom)
  let k : U ⟶ T := Over.homMk k₀ (by simp [U])
  have hk : Q.map k = A.ι := by
    show B.inclusion.map (B.inclusion.preimage kScheme) = kScheme
    exact B.inclusion.map_preimage kScheme
  have hmap : Set.range (Q.map m).base ⊆ Set.range A.ι.base := by
    rintro _ ⟨t, rfl⟩
    have heq : t = IsLocalRing.closedPoint p.carrier := by
      let : Subsingleton (Q.obj (p.siteObject B S hS (yoneda.obj T))) := by
        show Subsingleton (PrimeSpectrum p.carrier)
        infer_instance
      exact Subsingleton.elim _ _
    subst t
    exact ⟨⟨z, hzA⟩, rfl⟩
  let l₀ : Q.obj (p.siteObject B S hS (yoneda.obj T)) ⟶ A.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.lift A.ι (Q.map m) hmap
  have hl₀ : l₀ ≫ A.ι = Q.map m :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac A.ι (Q.map m) hmap
  let lScheme : B.inclusion.obj (p.siteObject B S hS (yoneda.obj T)).left ⟶
      B.inclusion.obj U.left := l₀
  let l : p.siteObject B S hS (yoneda.obj T) ⟶ U :=
    Over.homMk (B.inclusion.preimage lScheme) (by
      apply B.inclusion.map_injective
      show B.inclusion.map (B.inclusion.preimage lScheme ≫ (k₀ ≫ T.hom)) = _
      simp only [Functor.map_comp, Functor.map_preimage, k₀]
      show l₀ ≫ A.ι ≫ B.inclusion.map T.hom = _
      rw [← Category.assoc, hl₀]
      exact congrArg B.inclusion.map m.w)
  have hl : l ≫ k = m := by
    apply Q.map_injective
    rw [Functor.map_comp, hk]
    show B.inclusion.map (B.inclusion.preimage lScheme) ≫ A.ι = Q.map m
    rw [Functor.map_preimage, hl₀]
  let q : FieldValuedPoint B S hS (yoneda.obj U) :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := l }
  have hq : pointsMap B S hS (yoneda.obj U) (yoneda.map k)
      (q.class B S hS (yoneda.obj U)) = p.class B S hS (yoneda.obj T) := by
    show Quot.mk _ (FieldValuedPoint.map B S hS (yoneda.obj U)
      (yoneda.map k) q) = Quot.mk _ p
    congr 1
    show ({
      carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := l ≫ k } : FieldValuedPoint B S hS (yoneda.obj T)) = p
    rw [hl]
  refine ⟨U, yoneda.map k ≫ e.hom, hA, ?_, ?_⟩
  · let P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) Q
    have hkopen : P k := by
      show AlgebraicGeometry.IsOpenImmersion (Q.map k)
      rw [hk]
      infer_instance
    let : ObjectProperty.IsClosedUnderIsomorphisms
        (AlgebraicGeometry.schemeSizeBelow B.cutoff) := ⟨by
      intro X Y e h
      show Y.size < B.cutoff
      rwa [← Scheme.size_congr e]⟩
    let : ObjectProperty.IsClosedUnderLimitsOfShape
        (AlgebraicGeometry.schemeSizeBelow B.cutoff) WalkingCospan := .mk' (by
      rintro _ ⟨G, hG⟩
      show (limit G).size < B.cutoff
      rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan G))]
      exact Scheme.size_pullback_lt _ _ (hG .left) (hG .right))
    let : HasPullbacks B.Schemes := hasLimitsOfShape_of_closedUnderLimits
      (J := WalkingCospan) (P := AlgebraicGeometry.schemeSizeBelow B.cutoff)
    let : HasPullbacks (BigFppfOver B S hS) := Over.instHasPullbacks
    let : CreatesLimitsOfShape WalkingCospan B.inclusion :=
      createsLimitsOfShapeFullSubcategoryInclusion
        (J := WalkingCospan) (P := AlgebraicGeometry.schemeSizeBelow B.cutoff)
    let : PreservesLimitsOfShape WalkingCospan Q := by
      dsimp [Q, BigFppfOver.toScheme]
      infer_instance
    let : P.IsStableUnderBaseChange := by
      constructor
      intro A C D E g h i j hsquare hg
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.IsOpenImmersion.{u}) (hsquare.map Q) hg
    exact MorphismProperty.RespectsIso.postcomp P.presheaf e.hom (yoneda.map k)
      (MorphismProperty.relative_map hkopen)
  · refine ⟨q.class B S hS (yoneda.obj U), ?_⟩
    rw [pointsMap_comp, Function.comp_apply, hq, hp]
    have heq := congrFun (pointsMap_comp B S hS _ e.inv e.hom) y
    simpa only [e.inv_hom_id, pointsMap_id', Function.comp_apply, id_eq] using heq.symm

theorem exists_quasiSeparated_open_neighborhood_of_zero
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ (W : Subfunctor Y), IsOpenSubspace B S hS W ∧
      IsQuasiCompactSpace B S hS W.toFunctor ∧
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.toFunctor ∧
      (∃ T : BigFppfOver B S hS,
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
          Nonempty (yoneda.obj T ≅ W.toFunctor)) ∧
      y ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) := by
  obtain ⟨⟨V, hV, hrep, hdense, hcomp, _⟩, hYcomp⟩ :=
    exists_dense_open_scheme_of_decent_of_zero_finite B S hS hY hYdecent hYzero
  have hygen : y ∈ @genericPoints _ (pointTopology B S hS Y) :=
    ((mem_genericPoints_tfae B S hS hY hYdecent y).out
      1 4).mpr hy
  rw [← image_genericPoints_eq_genericPoints_of_denseRange B S hS hV hdense hYcomp] at hygen
  obtain ⟨v, _, hv⟩ := hygen
  obtain ⟨U, j, hU, hj, u, hu⟩ :=
    exists_affine_open_neighborhood_of_representable B S hS hrep v
  let k := j ≫ V.ι
  let W := Subfunctor.range k
  have hk := isOpenImmersion_comp B S hS j V.ι hj hV.2
  have hAlgU := isAlgebraicSpace_yoneda B S hS U
  have hW := isOpenSubspace_range_of_isAlgebraicSpace B S hS hAlgU k hk
  let : Mono k := mono_of_isOpenImmersion B S hS k hk
  let e : yoneda.obj U ≅ W.toFunctor := asIso (Subfunctor.toRange k)
  have hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.toFunctor := by
    apply isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme
      B S hS B.contains_terminal (X := W.toFunctor)
    refine ⟨U, ?_, ⟨?_⟩⟩
    · let := hU
      infer_instance
    · exact Functor.representableByEquiv.symm e
  refine ⟨W, hW, isQuasiCompactSpace_of_iso B S hS e
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU), hWqs,
    ⟨U, hU, ⟨e⟩⟩,
    pointsMap B S hS _ e.hom u, ?_⟩
  have he : e.hom ≫ W.ι = j ≫ V.ι := Subfunctor.toRange_ι k
  calc
    pointsMap B S hS W.toFunctor W.ι
        (pointsMap B S hS (yoneda.obj U) e.hom u) =
        pointsMap B S hS (yoneda.obj U) (e.hom ≫ W.ι) u :=
      (congrFun (pointsMap_comp B S hS _ e.hom W.ι) u).symm
    _ = y := by rw [he, pointsMap_comp, Function.comp_apply, hu, hv]

theorem genericPoint_mem_dense_open_of_finite
    {P : Type*} [TopologicalSpace P] [T0Space P] [QuasiSober P]
    (hfinite : (genericPoints P).Finite) {D : Set P}
    (hD : Dense D) (hDopen : IsOpen D) {y : P} (hy : y ∈ genericPoints P) :
    y ∈ D := by
  obtain ⟨O, hyO, huniq⟩ := exists_open_nhds_unique_generic hfinite ⟨y, hy⟩
  obtain ⟨z, hzO, hzD⟩ := hD.inter_open_nonempty O O.isOpen ⟨y, hyO⟩
  have hgen : Dense (genericPoints P) := dense_iff_closure_eq.mpr genericPoints.closure
  obtain ⟨x, hx, hxgen⟩ := hgen.inter_open_nonempty (O ∩ D)
    (O.isOpen.inter hDopen) ⟨z, hzO, hzD⟩
  have hxy : x = y := congrArg Subtype.val (huniq ⟨x, hxgen⟩ hx.1)
  exact hxy ▸ hx.2

theorem zeroPoint_mem_dense_open
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYdecent : IsDecentSpace B S hS Y)
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (V : Subfunctor Y) (hV : IsDenseOpenSubspace B S hS hY V)
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := by
  let := pointTopology B S hS Y
  let := t0Space_points_of_isDecentSpace B S hS hY hYdecent
  let : QuasiSober (points B S hS Y) :=
    (stacksSober_iff_t0_and_quasiSober.mp
      (stacksSober_points_of_isDecentSpace B S hS hY hYdecent)).2
  apply genericPoint_mem_dense_open_of_finite
    (genericPoints_finite_of_zero_finite B S hS hY hYdecent hYzero) hV.2
  · rw [← openSubspacesOrderIso_apply B S hS Y hY ⟨V, hV.1⟩]
    exact (openSubspacesOrderIso B S hS Y hY ⟨V, hV.1⟩).isOpen
  · exact ((mem_genericPoints_tfae
      B S hS hY hYdecent y).out 1 4).mpr hy

private theorem exists_finite_open_neighborhood_of_separated
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hsep : IsSeparated B S hS f)
    (hYdecent : IsDecentSpace B S hS Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hfib : ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        Set.Finite {x : points B S hS X |
          pointsMap B S hS X f x = y})
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  obtain ⟨W, hW, _hWqc, hWqs, _hWrep, w, hw⟩ :=
    exists_quasiSeparated_open_neighborhood_of_zero B S hS hY hYdecent hYzero y hy
  let P := pullback f W.ι
  let p : P ⟶ X := pullback.fst f W.ι
  let q : P ⟶ W.toFunctor := pullback.snd f W.ι
  have hP := isAlgebraicSpace_pullback B S hS f W.ι hX hW.1 hY
  have hp := isOpenImmersion_pullback_fst_of_isOpenSubspace B S hS hX hY f W hW
  let : Mono p := mono_of_isOpenImmersion B S hS p hp
  have hqsep : IsSeparated B S hS q :=
    isSeparated_pullback B S hS f W.ι hsep
  have hWdecent := isDecentSpace_of_isEtale B S hS W.ι
    hW.1 hY (isEtale_of_openImmersion B S hS W.ι hW.2) hYdecent
  have hWzero := finite_codimensionZeroPoints_of_openImmersion B S hS
    hW.1 hY W.ι hW.2 hYzero
  have hPzero := finite_codimensionZeroPoints_of_openImmersion B S hS hP hX p hp hXzero
  have hqfib (v : points B S hS W.toFunctor)
      (hv : localRingDimension B S hS v = 0) :
      Set.Finite {x : points B S hS P |
        pointsMap B S hS P q x = v} := by
    apply ((hfib (pointsMap B S hS W.toFunctor W.ι v)
      (localRingDimension_zero_map_of_openSubspace B S hS hW.1 hY W.ι hW.2 v hv)).preimage
        (pointsMap_injective_of_mono B S hS p).injOn).subset
    intro x hx
    show pointsMap B S hS X f (pointsMap B S hS P p x) = _
    calc
      pointsMap B S hS X f (pointsMap B S hS P p x) =
          pointsMap B S hS P (p ≫ f) x :=
        (congrFun (pointsMap_comp B S hS _ p f) x).symm
      _ = pointsMap B S hS W.toFunctor W.ι v := by
        show pointsMap B S hS P (pullback.fst f W.ι ≫ f) x = _
        rw [pullback.condition, pointsMap_comp, Function.comp_apply, hx]
  obtain ⟨V, hV, hdense, hfin⟩ :=
    exists_dense_open_isFinite_of_separated_quasiSeparated_target
      B S hS B.contains_terminal hP hW.1 q
      (locallyOfFiniteType_pullback_snd B S hS hX hY hW.1 f W.ι hlft)
      hqsep hWqs hWdecent hPzero hWzero hqfib
  have hwzero : localRingDimension B S hS w = 0 :=
    (localRingDimension_zero_iff_of_openImmersion B S hS hW.1 hY W.ι hW.2 w).2
      (hw.symm ▸ hy)
  obtain ⟨v, hv⟩ := zeroPoint_mem_dense_open B S hS hW.1 hWdecent hWzero
    V ⟨hV, hdense⟩ w hwzero
  let U := Subfunctor.range (V.ι ≫ W.ι)
  have hU := isOpenSubspace_range_of_isAlgebraicSpace B S hS hV.1 (V.ι ≫ W.ι)
    (isOpenImmersion_comp B S hS V.ι W.ι hV.2 hW.2)
  refine ⟨U, hU, ⟨pointsMap B S hS V.toFunctor (Subfunctor.toRange (V.ι ≫ W.ι)) v, ?_⟩,
    isFinite_pullback_snd_range_comp B S hS f W V hfin⟩
  rw [pointsMap_range_comp_toRange, hv, hw]

theorem exists_dense_open_isFinite_of_separated
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (hsep : IsSeparated B S hS f)
    (hYdecent : IsDecentSpace B S hS Y)
    (hXzero : Set.Finite {x : points B S hS X |
      localRingDimension B S hS x = 0})
    (hYzero : Set.Finite {y : points B S hS Y |
      localRingDimension B S hS y = 0})
    (hfib : ∀ y : points B S hS Y,
      localRingDimension B S hS y = 0 →
        Set.Finite {x : points B S hS X |
          pointsMap B S hS X f x = y}) :
    letI := pointTopology B S hS Y
    ∃ V : Subfunctor Y, IsOpenSubspace B S hS V ∧
      Dense (Set.range (pointsMap B S hS V.toFunctor V.ι)) ∧
      IsFinite B S hS (pullback.snd f V.ι) :=
  exists_dense_open_isFinite_of_finite_open_neighborhoods B S hS hX hY f hYzero
    (exists_finite_open_neighborhood_of_separated B S hS hX hY f hlft hsep
      hYdecent hXzero hYzero hfib)

end AlgebraicGeometry.Space

end
