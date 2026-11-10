module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliMap
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.UniversalHomeomorphismFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeDecent
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.RelativePropertyFamilyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.CartesianCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# Separatedness, quasi-compactness and universal homeomorphism of the moduli map (Stacks 0DUT)

For a small Keel–Mori cover the moduli map `f : 𝒳 ⟶ M` has, after base change along each
`u i : M i ⟶ M`, the moduli map `f i` of the `i`-th member (the squares (0DUU) are cartesian). The
`u i` are étale and jointly cover `M`, so the properties of the `f i` descend to `f`. The descent
lemmas of the library are stated along a single cover; here they are run along the family.

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.exists_cover_lift_point`: points of `M` lift locally to
  the `M i`.
* `AlgebraicGeometry.Stack.liftsLocally_diagonalMapDiag`: objects of `𝒳 ×_M 𝒳` lift locally to the
  self-products of the base changes along such a family.
* `AlgebraicGeometry.Stack.KeelMoriCover.isSeparated_moduliMap`: the moduli map is separated.
* `AlgebraicGeometry.Stack.KeelMoriCover.universalHomeomorphism_moduliMap`: the moduli map is a
  universal homeomorphism.
* `AlgebraicGeometry.Stack.KeelMoriCover.isQuasiCompactMorphism_moduliMap`: the moduli map is
  quasi-compact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.KeelMoriCover

universe u w

/-! ### Lifting objects of `𝒳 ×_M 𝒳` along a family of étale pieces of `M` -/

section DiagonalLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two morphisms of the category attached to a presheaf of sets lying over the same arrow are
equal. -/
theorem fibredCategory_hom_eq_of_isHomLift {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X Y : (fibredCategory B S hS E).val.obj} {R R' : BigFppfOver B S hS} (k : R ⟶ R')
    (φ ψ : X ⟶ Y) (hφ : (fibredCategory B S hS E).val.p.IsHomLift k φ)
    (hψ : (fibredCategory B S hS E).val.p.IsHomLift k ψ) : φ = ψ := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
    ((IsHomLift.fac' (fibredCategory B S hS E).val.p k φ).trans
      (IsHomLift.fac' (fibredCategory B S hS E).val.p k ψ).symm) ?_
  apply Discrete.hom_eq

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hE : IsAlgebraicSpace B S hS E) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS E hE)
  {J : Type*} {Mj : J → BigFppfOver B S hS} (v : ∀ j, yoneda.obj (Mj j) ⟶ E)

/-- The 1-morphism of algebraic stacks attached to the `j`-th piece `Mⱼ ⟶ M`. -/
noncomputable abbrev pieceMap (j : J) :
    algebraicSpaceStack.{u, w} B S hS (yoneda.obj (Mj j)) (isAlgebraicSpace_yoneda B S hS (Mj j)) ⟶
      algebraicSpaceStack.{u, w} B S hS E hE :=
  algebraicSpaceStackMap.{u, w} B S hS (isAlgebraicSpace_yoneda B S hS (Mj j)) hE (v j)

/-- **Objects of `𝒳 ×_M 𝒳` lift locally along the self-products of the pieces.** If every point of
`M` lifts, along the arrows of a covering sieve, to one of the pieces `vⱼ : Mⱼ ⟶ M`, then every
object `(x₁, x₂, f x₁ = f x₂)` of `𝒳 ×_M 𝒳` lifts, along the arrows of a covering sieve, to an
object of `(𝒳 ×_M Mⱼ) ×_{Mⱼ} (𝒳 ×_M Mⱼ)` for some `j`. -/
theorem liftsLocally_diagonalMapDiag
    (hv : ∀ (T : BigFppfOver B S hS) (m : E.obj (op T)),
      ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ T⦄, R.arrows k →
        ∃ (j : J) (n : V ⟶ Mj j), (v j).app (op V) n = E.map k.op m) :
    ∀ (U : BigFppfOver B S hS)
      (y : (twoFibreProduct B S hS (algebraicSpaceStack.{u, w} B S hS E hE).val 𝒳.val 𝒳.val
        f.hom.hom f.hom.hom).val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ (j : J) (z : (twoFibreProduct B S hS
              (algebraicSpaceStack.{u, w} B S hS (yoneda.obj (Mj j))
                (isAlgebraicSpace_yoneda B S hS (Mj j))).val
              (twoFibreProductAlgebraicStack B S hS f (pieceMap hE v j)).val
              (twoFibreProductAlgebraicStack B S hS f (pieceMap hE v j)).val
              (twoFibreProductSquareAlgebraicStacks B S hS f (pieceMap hE v j)).snd.hom.hom
              (twoFibreProductSquareAlgebraicStacks B S hS f
                (pieceMap hE v j)).snd.hom.hom).val.obj)
            (φ : (CatFiberedInGroupoids.homFunctor
              (diagonalMapDiag B S hS f (pieceMap hE v j))).obj z ⟶ y.1),
            (twoFibreProduct B S hS (algebraicSpaceStack.{u, w} B S hS E hE).val 𝒳.val 𝒳.val
              f.hom.hom f.hom.hom).val.p.IsHomLift k φ := by
  rintro U ⟨y, rfl⟩
  let F := f.hom.hom
  let p𝒳 := 𝒳.val.val.p
  let pE := (fibredCategory B S hS E).val.p
  have hb₁ : (F.obj y.x).base = y.base := (Functor.congr_obj F.w y.x).trans y.hx
  have hb₂ : (F.obj y.y).base = y.base := (Functor.congr_obj F.w y.y).trans y.hy
  have h₁₂ : F.obj y.x = F.obj y.y :=
    fibredCategory_obj_eq_of_isHomLift_id B S hS hb₁ hb₂ y.iso.hom y.vertical
  obtain ⟨R, hR, hRl⟩ := hv y.base (PresheafOfCategories.elementOf E hb₁)
  refine ⟨R, hR, fun V k hk => ?_⟩
  obtain ⟨j, n, hn⟩ := hRl hk
  let nV : (fibredCategory B S hS (yoneda.obj (Mj j))).val.obj := ⟨V, Discrete.mk n⟩
  have hvn : (pieceMap.{u, w} hE v j).hom.hom.obj nV = ⟨V, Discrete.mk ((v j).app (op V) n)⟩ :=
    associatedMap_obj B S hS _ _
  -- restrict a component naming the same element of `E` as `y.x` along `k`
  have restrict : ∀ (x₀ : 𝒳.val.val.obj) (hx₀ : p𝒳.obj x₀ = y.base)
      (hb : (F.obj x₀).base = y.base),
      PresheafOfCategories.elementOf E hb = PresheafOfCategories.elementOf E hb₁ →
      ∃ (x : 𝒳.val.val.obj) (a : x ⟶ x₀), p𝒳.IsHomLift k a ∧ ∃ hx : p𝒳.obj x = V,
        F.obj x = (pieceMap.{u, w} hE v j).hom.hom.obj nV := by
    intro x₀ hx₀ hb hel
    obtain ⟨x, a, ha⟩ := exists_lift_obj (𝒜 := 𝒳.val) x₀ (k ≫ eqToHom hx₀.symm)
    have ha' : p𝒳.IsHomLift k a := (IsHomLift.lift_comp_eqToHom_iff _ k a hx₀.symm).mp ha
    have hx : p𝒳.obj x = V := IsHomLift.domain_eq p𝒳 k a
    have hFx : (F.obj x).base = V := (Functor.congr_obj F.w x).trans hx
    refine ⟨x, a, ha', hx, ?_⟩
    rw [hvn]
    refine PresheafOfCategories.obj_eq_of_elementOf_eq (P := E) hFx rfl ?_
    rw [ChartBaseChange.fibredCategory_elementOf_eq_map hFx hb k (F.map a)
      (Functor.isHomLift_map_of_comp_eq F.w k a), hel, hn]
    rfl
  obtain ⟨x₁, a₁, ha₁', hx₁, e₁⟩ := restrict y.x y.hx hb₁ rfl
  obtain ⟨x₂, a₂, ha₂', hx₂, e₂⟩ := restrict y.y y.hy hb₂ (elementOf_congr h₁₂ hb₁ hb₂).symm
  let mkw (x : 𝒳.val.val.obj) (hx : p𝒳.obj x = V) (e : F.obj x = _) :
      (twoFibreProductAlgebraicStack B S hS f (pieceMap hE v j)).val.val.obj :=
    { base := V, x := x, y := nV, hx := hx, hy := rfl, iso := eqToIso e
      vertical := IsHomLift.eqToHom_domain_lift_id e ((Functor.congr_obj F.w x).trans hx) }
  let z : (twoFibreProduct B S hS
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj (Mj j))
        (isAlgebraicSpace_yoneda B S hS (Mj j))).val
      (twoFibreProductAlgebraicStack B S hS f (pieceMap hE v j)).val
      (twoFibreProductAlgebraicStack B S hS f (pieceMap hE v j)).val
      (twoFibreProductSquareAlgebraicStacks B S hS f (pieceMap hE v j)).snd.hom.hom
      (twoFibreProductSquareAlgebraicStacks B S hS f (pieceMap hE v j)).snd.hom.hom).val.obj :=
    { base := V, x := mkw x₁ hx₁ e₁, y := mkw x₂ hx₂ e₂, hx := rfl, hy := rfl, iso := Iso.refl nV
      vertical := IsHomLift.id rfl }
  refine ⟨j, z, ⟨k, a₁, a₂, ha₁', ha₂', ?_⟩, ?_⟩
  · have hv₁ : pE.IsHomLift (𝟙 y.base) y.iso.hom := y.vertical
    have hv₂ : pE.IsHomLift (𝟙 V)
        ((CatFiberedInGroupoids.homFunctor
          (diagonalMapDiag B S hS f (pieceMap hE v j))).obj z).iso.hom :=
      ((CatFiberedInGroupoids.homFunctor
          (diagonalMapDiag B S hS f (pieceMap hE v j))).obj z).vertical
    exact fibredCategory_hom_eq_of_isHomLift k _ _
      (@IsHomLift.comp_lift_id_right _ _ _ _ pE _ _ _ _ _ k _
        (Functor.isHomLift_map_of_comp_eq F.w k a₁) _ hv₁)
      (@IsHomLift.comp_lift_id_left _ _ _ _ pE _ _ _ _ _ k _
        (Functor.isHomLift_map_of_comp_eq F.w k a₂) _ hv₂)
  · exact TwoFibreProductOver.structureFunctor_isHomLift _ k ha₁'

/-- **Separatedness of the second leg does not depend on the chosen 2-fibre product square.** -/
theorem _root_.AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_snd_of_isTwoFibreProduct
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    {R R' : Bicategory.TwoCommSq f g} (hR : Bicategory.IsTwoFibreProduct R)
    (hR' : Bicategory.IsTwoFibreProduct R')
    (h : AlgebraicStacks.IsSeparated B S hS R.snd) : AlgebraicStacks.IsSeparated B S hS R'.snd := by
  let d : Bicategory.TwoCommSq.PreHom R' R := _root_.Quotient.out (hR.from R')
  exact AlgebraicStacks.isSeparated_of_equivalence B S hS R.snd R'.snd d.hom.hom.hom
    (algStackHomHomIso B S hS d.isoSnd.symm)
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hR' hR d) h

end DiagonalLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {C : KeelMoriCover B S hS 𝒳} (hC : C.IsSmall)

attribute [local instance] hasSheafify_bigFppfOver

/-- **Points of `M` lift locally to the `M i`**: the étale atlas `U ⟶ M` pulled back along a point
`T ⟶ M` is an étale scheme over `T` covering it, and it splits along the pieces `M i` of `U`. -/
theorem exists_cover_lift_point {T : BigFppfOver B S hS} (m : (Mq hC).obj (op T)) :
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ T⦄, R.arrows k →
      ∃ (i : C.ι) (n : V ⟶ C.M i), (u hC i).app (op V) n = (Mq hC).map k.op m := by
  classical
  set m' : yoneda.obj T ⟶ Mq hC := yonedaEquiv.symm m
  have hbce : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
      Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hbcs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  set hp := MorphismProperty.relative.rep (π_etale hC)
  set r : hp.pullback m' ⟶ U hC := yoneda.preimage (hp.fst m') with hrdef
  set p : hp.pullback m' ⟶ T := hp.snd m'
  have hs : IsPullback (yoneda.map r) (yoneda.map p) (π hC) m' := by
    rw [hrdef, yoneda.map_preimage]
    exact hp.isPullback m'
  have hpe : Etale ((BigFppfOver.toScheme B S hS).map p) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).1
      (hbce.of_isPullback hs (π_etale hC))
  have hps : Surjective ((BigFppfOver.toScheme B S hS).map p) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ p).1
      (hbcs.of_isPullback hs (π_surjective hC))
  let W : C.ι → BigFppfOver B S hS := fun i => pullback r (ιU hC i)
  let w : ∀ i, W i ⟶ T := fun i => pullback.fst r (ιU hC i) ≫ p
  have hwe : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (w i)) := fun i => by
    have := isOpenImmersion_toScheme_pullback_fst r (ιU hC i)
    simp only [w, Functor.map_comp]
    infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows W w),
    Space.generate_ofArrows_mem_topology_of_etale W w hwe ?_, ?_⟩
  · intro t
    obtain ⟨z, hz⟩ := hps.surj t
    obtain ⟨i, y, hy⟩ := cover_ιU hC ((BigFppfOver.toScheme B S hS).map r z)
    obtain ⟨z', hz', -⟩ := exists_preimage_pullback_site r (ιU hC i) z y hy.symm
    exact ⟨i, z', by
      simp only [w, Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app]
      rw [hz', hz]⟩
  · rintro V k ⟨Y, l, g', ⟨i⟩, rfl⟩
    refine ⟨i, l ≫ pullback.snd r (ιU hC i), ?_⟩
    have key : yoneda.map (l ≫ pullback.snd r (ιU hC i)) ≫ u hC i =
        yoneda.map (l ≫ w i) ≫ m' := by
      simp only [u, w, Functor.map_comp, Category.assoc]
      rw [← hs.w, ← reassoc_of% (yoneda.map_comp (pullback.snd r (ιU hC i)) (ιU hC i)),
        ← pullback.condition, Functor.map_comp, Category.assoc]
    have h₁ := congrArg yonedaEquiv key
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map] at h₁
    refine h₁.trans ?_
    change m'.app (op V) (l ≫ w i) = (Mq hC).map (l ≫ w i).op m
    exact yonedaEquiv_symm_app_apply m (op V) (l ≫ w i)

/-- The 1-morphism of algebraic stacks `M i ⟶ M`. -/
noncomputable abbrev uStack (i : C.ι) :
    algebraicSpaceStack.{u, w} B S hS (yoneda.obj (C.M i))
        (isAlgebraicSpace_yoneda B S hS (C.M i)) ⟶
      algebraicSpaceStack.{u, w} B S hS (Mq hC) (isAlgebraicSpace_Mq hC) :=
  pieceMap (isAlgebraicSpace_Mq hC) (u hC) i

/-- The square (0DUU) `𝒳 i ⟶ 𝒳` over `M i ⟶ M`, in the 2-category of algebraic stacks. -/
noncomputable abbrev pieceSq (i : C.ι) : Bicategory.TwoCommSq (uStack hC i) (moduliMap hC) :=
  ⟨C.obj i, C.f i, C.map i, eqToIso (Bicategory.InducedBicategory.hom_ext
    (map_comp_moduliMap hC i).symm)⟩

/-- **The square (0DUU) is a 2-fibre product in the 2-category of algebraic stacks.** -/
theorem nonempty_isTwoFibreProduct_pieceSq (i : C.ι) :
    Nonempty (Bicategory.IsTwoFibreProduct (pieceSq hC i)) := by
  obtain ⟨h⟩ := nonempty_isTwoFibreProduct_square hC i
  exact ⟨Bicategory.isTwoFibreProduct_of_underlying
    (isTwoFibreProduct_of_eq_of_discrete B S hS _ h _)⟩

/-- **The moduli map is separated** (Stacks 0DUT): its base change along each `M i ⟶ M` is the
separated moduli map of the `i`-th member, and separatedness descends along the jointly covering
family of étale morphisms `M i ⟶ M`, through the relative diagonal (Stacks 04YR, 045D). -/
theorem isSeparated_moduliMap : AlgebraicStacks.IsSeparated B S hS (moduliMap hC) := by
  have hprBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have hprLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsProper B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  have hsep : ∀ i, AlgebraicStacks.IsSeparated B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS (moduliMap hC) (uStack hC i)).snd := fun i =>
    AlgebraicStacks.isSeparated_snd_of_isTwoFibreProduct (R := (pieceSq hC i).swap)
      (Bicategory.isTwoFibreProduct_swap (nonempty_isTwoFibreProduct_pieceSq hC i).some)
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _)
      ((C.chart i).isSeparated_moduliMap (C.wellNighAffine i))
  exact hasRelativeProperty_of_baseChange_family.{u, u, u, u} B S hS 𝒳.val
    (twoFibreProduct B S hS
      (algebraicSpaceStack.{u, w} B S hS (Mq hC) (isAlgebraicSpace_Mq hC)).val 𝒳.val 𝒳.val
      (moduliMap hC).hom.hom (moduliMap hC).hom.hom) _
    (fun _ _ k => Space.IsProper B S hS k.hom)
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val _ (moduliMap hC).hom)
    (fun i => diagonalMapDiag B S hS (moduliMap hC) (uStack hC i))
    (fun i => diagonalBaseChangeSquare B S hS (moduliMap hC) (uStack hC i))
    (fun i => isTwoFibreProduct_diagonalBaseChangeSquare B S hS (moduliMap hC) (uStack hC i))
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS (moduliMap hC))
    (liftsLocally_diagonalMapDiag (isAlgebraicSpace_Mq hC) (moduliMap hC) (u hC)
      (fun _ m => exists_cover_lift_point hC m)) hsep

/-! ### Universal homeomorphism -/

/-- **The pieces `M i ⟶ M` are jointly surjective on points**: the atlas `U ⟶ M` is surjective and
`U` is the disjoint union of the `M i`. -/
theorem iUnion_range_pointsMap_u :
    ⋃ i, Set.range (Space.pointsMap B S hS (yoneda.obj (C.M i)) (u hC i)) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := Space.isSurjective_of_presheafSurjective B S hS (π hC) (π_surjective hC) y
  obtain ⟨i, z, hz⟩ := cover_ιU hC (Space.pointsEquivScheme B S hS (U hC) x)
  refine Set.mem_iUnion.2 ⟨i, (Space.pointsEquivScheme B S hS (C.M i)).symm z, ?_⟩
  have h : (Space.pointsEquivScheme B S hS (U hC)).symm
      (((BigFppfOver.toScheme B S hS).map (ιU hC i)).base z) = x :=
    (Equiv.symm_apply_eq _).2 hz
  rw [u, Space.pointsMap_comp, Function.comp_apply,
    ← Space.pointsEquivScheme_symm_map B S hS (ιU hC i) z, h]

/-- **The pieces `M i ⟶ M` are jointly surjective on the points of the algebraic stack `M`.** -/
theorem exists_pointsMap_uStack_eq
    (y : AlgebraicStacks.points B S hS
      (algebraicSpaceStack.{u, w} B S hS (Mq hC) (isAlgebraicSpace_Mq hC))) :
    ∃ i, ∃ w : AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS
        (yoneda.obj (C.M i)) (isAlgebraicSpace_yoneda B S hS (C.M i))),
      AlgebraicStacks.pointsMap B S hS (uStack hC i) w = y := by
  obtain ⟨y', rfl⟩ := (spacePointMap_id_bijective B S hS (Mq hC)).2 y
  have hy' : y' ∈ ⋃ i, Set.range (Space.pointsMap B S hS (yoneda.obj (C.M i)) (u hC i)) := by
    rw [iUnion_range_pointsMap_u hC]
    trivial
  obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hy'
  exact ⟨i, _, (spacePointMap_pointsMap_associatedMap B S hS (u hC i) x).symm⟩

/-- The 1-morphism `M i ⟶ M` of algebraic stacks attached to the `i`-th piece is flat. -/
theorem isFlat_uStack (i : C.ι) : AlgebraicStacks.IsFlat B S hS (uStack hC i) :=
  (isFlat_algebraicSpaceStackMap_iff B S hS _ _ _).2
    (Space.isFlat_of_isEtale B S hS (isEtale_u hC i))

/-- The 1-morphism `M i ⟶ M` of algebraic stacks attached to the `i`-th piece is locally of finite
presentation. -/
theorem isLocallyOfFinitePresentation_uStack (i : C.ι) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (uStack hC i) :=
  (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff B S hS _ _ _).2
    (Space.isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_u hC i))

/-- **The moduli map is a universal homeomorphism** (Stacks 0DUT): its base change along each
`M i ⟶ M` is the moduli map of the `i`-th member, a universal homeomorphism (Stacks 0DUP), and the
`M i ⟶ M` are étale and jointly surjective (the family form of Stacks 0DTQ). -/
theorem universalHomeomorphism_moduliMap : UniversalHomeomorphism B S hS (moduliMap hC) :=
  universalHomeomorphism_of_flatFamily B S hS (moduliMap hC) _ (uStack hC)
    (exists_pointsMap_uStack_eq hC) (isFlat_uStack hC) (isLocallyOfFinitePresentation_uStack hC)
    (pieceSq hC) (fun i => (nonempty_isTwoFibreProduct_pieceSq hC i).some)
    (fun i => (C.chart i).universalHomeomorphism_moduliMap)

/-- The moduli map is a universal homeomorphism in the sense of the canonical base changes. -/
theorem algebraicStacks_universalHomeomorphism_moduliMap :
    AlgebraicStacks.UniversalHomeomorphism B S hS (moduliMap hC) := fun 𝒵 g =>
  universalHomeomorphism_moduliMap hC 𝒵 g _
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g _)

/-- **The moduli map is quasi-compact** (Stacks 0DUT): a universal homeomorphism is. -/
theorem isQuasiCompactMorphism_moduliMap :
    IsQuasiCompactMorphism.{u, w} B S hS (moduliMap hC) :=
  isQuasiCompactMorphism_of_universalHomeomorphism B S hS _
    (algebraicStacks_universalHomeomorphism_moduliMap hC)

end AlgebraicGeometry.Stack.KeelMoriCover

end
