module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.UnitIsoFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LocallyFreeChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSplittingDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom

/-!
# Modules descending along a morphism with invertible structure map

Let `p : X ⟶ Y` be a morphism of algebraic spaces and `M` an `𝒪_X`-module. Say that `M`
*descends along `p`* when `M ≅ p^*N` for a finite locally free `𝒪_Y`-module `N`. The descent
condition `AlgebraicGeometry.Space.HasDescentAt` of Stacks 0D23 at `g : Y' ⟶ Y` is this condition
for the base change `f' : X ×_Y Y' ⟶ Y'` and the pullback of `E`.

When the structure map `𝒪_Y ⟶ p_*𝒪_X` is an isomorphism, the descended module is necessarily
`p_*M` (the projection formula for a finite locally free module, Stacks 0D23): `M` descends along
`p` exactly when `p_*M` is finite locally free and the counit `p^*p_*M ⟶ M` is an isomorphism.
That characterization is étale local on `Y`, because the base change map `h^*p_* ⟶ p'_*h'^*` is
an isomorphism along an étale `h`.

## Main definitions

* `AlgebraicGeometry.Space.DescentStratum.DescendsAlong`: `M ≅ p^*N` for a finite locally free
  `𝒪_Y`-module `N`.

## Main results

* `AlgebraicGeometry.Space.DescentStratum.descendsAlong_iff`: the characterization by `p_*M` and
  the counit.
* `AlgebraicGeometry.Space.DescentStratum.DescendsAlong.pullback`: stability under base change.
* `AlgebraicGeometry.Space.DescentStratum.descendsAlong_comp_iff`: invariance under an
  isomorphism of the source.
* `AlgebraicGeometry.Space.DescentStratum.descendsAlong_of_forall_chart`: étale locality on `Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.DescentStratum

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Two local criteria -/

/-- **Isomorphisms of modules are detected along a jointly surjective family of étale
morphisms.** -/
theorem isIso_of_isIso_modulePullback_of_forall_mem_range {V : AlgebraicSpaces B S hS}
    {ι : Type*} {W : ι → AlgebraicSpaces B S hS} (a : ∀ i, W i ⟶ V)
    (ha : ∀ i, IsEtale B S hS (a i).hom)
    (hcov : ∀ v : points B S hS V.1, ∃ i, v ∈ Set.range (pointsMap B S hS (W i).1 (a i).hom))
    {M N : Modules.{u, u} B S hS V.1 V.2} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((modulePullback B S hS (a i)).map φ)) : IsIso φ := by
  have key : ∀ {X : AlgebraicSpaces B S hS} (g : X ⟶ V) (c : SmallEtale B S hS V.1)
      (b : chartSpace B S hS V c ⟶ X) (_ : b ≫ g = chartToSpace B S hS V c),
      IsIso ((modulePullback B S hS g).map φ) →
      IsIso ((modulePullback B S hS (chartToSpace B S hS V c)).map φ) := by
    intro X g c b hb hg
    have := hg
    rw [← hb]
    exact (NatIso.isIso_map_iff (modulePullbackCompIso B S hS b g) φ).1
      (inferInstanceAs (IsIso ((modulePullback B S hS b).map ((modulePullback B S hS g).map φ))))
  choose T t hts hte using fun i => (W i).2.exists_atlas
  have ht : ∀ i, IsEtale B S hS (t i) := fun i =>
    (isEtale_iff_presheaf_of_yoneda B S hS (t i)).2 (hte i)
  have hA : ∀ i, _ := fun i =>
    (isEtale_iff_presheaf_of_yoneda B S hS (t i ≫ (a i).hom)).1
      (isEtale_comp B S hS (ht i) (ha i))
  let c : ι → SmallEtale B S hS V.1 := fun i => ⟨CostructuredArrow.mk (t i ≫ (a i).hom), hA i⟩
  refine isIso_of_isIso_modulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_of_iUnion_range_eq_univ B S hS V c ?_) φ fun i => ?_
  · refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨i, w, rfl⟩ := hcov v
    obtain ⟨s, rfl⟩ := surjective_pointsMap_of_presheaf_surjective B S hS (t i) (hts i) w
    exact Set.mem_iUnion.2 ⟨i, s, pointsMap_comp_apply B S hS (t i) (a i).hom s⟩
  · exact key (a i) (c i) (chartToSpace B S hS (W i)
      (⟨CostructuredArrow.mk (t i), hte i⟩ : SmallEtale B S hS (W i).1))
      (ObjectProperty.hom_ext _ rfl) (h i)

/-- The generating sections given by an isomorphism with a free module have invertible
projection. -/
theorem isIso_ofIsoFree_π {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{u} R} {I : Type u}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (e : _root_.SheafOfModules.free I ≅ M) :
    IsIso (_root_.SheafOfModules.GeneratingSections.ofIsoFree e).π := by
  rw [_root_.SheafOfModules.GeneratingSections.ofIsoFree_π]
  exact Iso.isIso_hom e

/-- **The chart criterion for finite local freeness.** A module on an algebraic space is finite
locally free exactly when every point lies in the image of an étale chart on which the module is
free on a finite basis. -/
theorem isFiniteLocallyFree_iff_forall_chart {Y : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    SheafOfModules.IsFiniteLocallyFree M ↔
      ∀ y : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1,
        y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
          ∃ n : ℕ, Nonempty ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M ≅
            SheafOfModules.free (R := structureRingSheaf B S hS (chartSpace B S hS Y V))
              (ULift.{u} (Fin n))) := by
  constructor
  · rintro ⟨q, hq, hfin⟩ y
    obtain ⟨k, hk⟩ := SmallEtale.exists_mem_range_of_coversTop B S hS Y.2 q.coversTop y
    have : Finite (q.generators k).I := (hfin.isFiniteType k).finite
    let σ := Finite.equivFin (q.generators k).I
    refine ⟨q.X k, hk, _, ⟨modulePullbackFreeIsoOfOverIso B S hS (q.X k) M _
      ((SheafOfModules.freeFunctor (R := (structureRingSheaf B S hS Y).over (q.X k))).mapIso
          (σ.trans Equiv.ulift.symm).toIso.symm ≪≫
        @asIso _ _ _ _ (q.generators k).π (hq.isIso k))⟩⟩
  · intro h
    choose V hV n e using h
    have hcov := SmallEtale.coversTop_of_forall_mem_range B S hS fun y => ⟨y, hV y⟩
    have key : ∀ k, ∃ σ : (M.over (V k)).GeneratingSections, IsIso σ.π ∧ Finite σ.I := fun k =>
      ⟨SheafOfModules.GeneratingSections.ofIsoFree
        (overFreeIsoOfModulePullback B S hS Y (V k) M _ (e k).some), isIso_ofIsoFree_π _,
          inferInstanceAs (Finite (ULift.{u} (Fin (n k))))⟩
    choose σ hσ hfin using key
    exact ⟨⟨⟨_, V, hcov, σ⟩, ⟨hσ⟩, ⟨fun k => ⟨hfin k⟩⟩⟩⟩

/-- **Finite local freeness on charts covering the space gives finite local freeness.** -/
theorem isFiniteLocallyFree_of_forall_chart {Y : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (h : ∀ y : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
        SheafOfModules.IsFiniteLocallyFree
          ((modulePullback B S hS (chartToSpace B S hS Y V)).obj M)) :
    SheafOfModules.IsFiniteLocallyFree M := by
  refine (isFiniteLocallyFree_iff_forall_chart M).2 fun y => ?_
  obtain ⟨V, ⟨v, rfl⟩, hV⟩ := h y
  obtain ⟨A, ⟨a, rfl⟩, n, ⟨e⟩⟩ := (isFiniteLocallyFree_iff_forall_chart _).1 hV v
  refine ⟨(smallEtalePostcomp B S hS (chartToSpace B S hS Y V)
    (isEtale_chartToSpace B S hS Y V)).obj A, ⟨a, ?_⟩, n,
    ⟨modulePullbackChartChartIso B S hS V A M ≪≫ e⟩⟩
  exact pointsMap_comp_apply B S hS A.1.hom V.1.hom a

/-- **The pullback of a finite locally free module is finite locally free**, along any morphism
of algebraic spaces. -/
theorem isFiniteLocallyFree_modulePullback {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    {N : Modules.{u, u} B S hS Y.1 Y.2} (hN : SheafOfModules.IsFiniteLocallyFree N) :
    SheafOfModules.IsFiniteLocallyFree ((modulePullback B S hS a).obj N) :=
  SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite _
    (isFiniteLocallyFreeOnSite_modulePullback B S hS a N
      (isQuasicoherentOnSite_of_isFiniteLocallyFree N hN)
      (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree N hN))

/-! ### Descent along a morphism -/

/-- **A module descends along `p : X ⟶ Y`** when it is the pullback `p^*N` of a finite locally
free `𝒪_Y`-module `N`. -/
def DescendsAlong {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ N : Modules.{u, u} B S hS Y.1 Y.2, SheafOfModules.IsFiniteLocallyFree N ∧
    Nonempty ((modulePullback B S hS p).obj N ≅ M)

/-- The descent condition of Stacks 0D23 at `g` is descent of the pullback of `E` along the base
change of `f`. -/
theorem hasDescentAt_iff_descendsAlong {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (E : Modules.{u, u} B S hS X.1 X.2) (g : Y' ⟶ Y) :
    HasDescentAt f E g ↔
      DescendsAlong (pullback.snd f g) ((modulePullback B S hS (pullback.fst f g)).obj E) :=
  Iff.rfl

/-- Descent only depends on the module up to isomorphism. -/
theorem DescendsAlong.of_iso {X Y : AlgebraicSpaces B S hS} {p : X ⟶ Y}
    {M M' : Modules.{u, u} B S hS X.1 X.2} (h : DescendsAlong p M) (e : M ≅ M') :
    DescendsAlong p M' :=
  h.imp fun _ ⟨hN, ⟨e'⟩⟩ => ⟨hN, ⟨e' ≪≫ e⟩⟩

/-- **The characterization of descent along a morphism with invertible structure map.** If
`𝒪_Y ⟶ p_*𝒪_X` is an isomorphism, then `M` descends along `p` exactly when `p_*M` is finite
locally free and the counit `p^*p_*M ⟶ M` is an isomorphism. -/
theorem descendsAlong_iff {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (hp : IsIso (structureSharp B S hS p)) (M : Modules.{u, u} B S hS X.1 X.2) :
    DescendsAlong p M ↔
      SheafOfModules.IsFiniteLocallyFree ((modulePushforward B S hS p).obj M) ∧
        IsIso ((modulePullbackAdjunction B S hS p).counit.app M) := by
  constructor
  · rintro ⟨N, hN, ⟨e⟩⟩
    obtain ⟨h1, -⟩ := isFiniteLocallyFree_modulePushforward_of_iso_modulePullback p hp N hN M
      e.symm
    refine ⟨h1, ?_⟩
    have := isIso_modulePullbackAdjunction_unit_app_of_isFiniteLocallyFree p hp N hN
    have h2 : IsIso ((modulePullbackAdjunction B S hS p).counit.app
        ((modulePullback B S hS p).obj N)) :=
      IsIso.of_isIso_fac_left ((modulePullbackAdjunction B S hS p).left_triangle_components N)
    have w := (modulePullbackAdjunction B S hS p).counit.naturality e.hom
    simp only [Functor.comp_map, Functor.id_map] at w
    exact IsIso.of_isIso_fac_left w
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, ⟨asIso ((modulePullbackAdjunction B S hS p).counit.app M)⟩⟩

/-- **Descent is stable under base change.** If `M ≅ p^*N`, then the pullback of `M` to
`X ×_Y Y'` is the pullback of `t^*N` along the base change of `p`. -/
theorem DescendsAlong.pullback {X Y Y' : AlgebraicSpaces B S hS} {p : X ⟶ Y}
    {M : Modules.{u, u} B S hS X.1 X.2} (h : DescendsAlong p M) (t : Y' ⟶ Y) :
    DescendsAlong (pullback.snd p t) ((modulePullback B S hS (pullback.fst p t)).obj M) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  exact ⟨(modulePullback B S hS t).obj N, isFiniteLocallyFree_modulePullback t hN,
    ⟨(modulePullbackSquareComparison p t (pullback.snd p t) (pullback.fst p t)
      pullback.condition).symm.app N ≪≫ (modulePullback B S hS (pullback.fst p t)).mapIso e⟩⟩

/-- **Descent is invariant under an isomorphism of the source.** -/
theorem descendsAlong_comp_iff {X X' Y : AlgebraicSpaces B S hS} (e : X' ≅ X) (p : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    DescendsAlong (e.hom ≫ p) ((modulePullback B S hS e.hom).obj M) ↔ DescendsAlong p M := by
  constructor
  · rintro ⟨N, hN, ⟨e'⟩⟩
    refine ⟨N, hN, ⟨?_⟩⟩
    exact eqToIso (congrArg (fun k => (modulePullback B S hS k).obj N)
        (e.inv_hom_id_assoc p).symm) ≪≫
      ((modulePullbackCompIso B S hS e.inv (e.hom ≫ p)).app N).symm ≪≫
      (modulePullback B S hS e.inv).mapIso e' ≪≫
      (modulePullbackCompIso B S hS e.inv e.hom).app M ≪≫
      eqToIso (congrArg (fun k => (modulePullback B S hS k).obj M) e.inv_hom_id) ≪≫
      (modulePullbackIdIso B S hS X).app M
  · rintro ⟨N, hN, ⟨e'⟩⟩
    exact ⟨N, hN, ⟨((modulePullbackCompIso B S hS e.hom p).app N).symm ≪≫
      (modulePullback B S hS e.hom).mapIso e'⟩⟩

/-- **Descent is étale local on the target.** Let `p : X ⟶ Y` have invertible structure map,
and suppose every point of `Y` lies in the image of an étale chart `c : V ⟶ Y` along whose base
change `p'` the structure map is invertible and the pullback of `M` descends. Then `M` descends
along `p`. -/
theorem descendsAlong_of_forall_chart {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (hp : IsIso (structureSharp B S hS p)) (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ y : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1,
      y ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
        IsIso (structureSharp B S hS (pullback.snd p (chartToSpace B S hS Y V))) ∧
        DescendsAlong (pullback.snd p (chartToSpace B S hS Y V))
          ((modulePullback B S hS (pullback.fst p (chartToSpace B S hS Y V))).obj M)) :
    DescendsAlong p M := by
  choose V hV hV' hd using h
  let β := fun y => moduleBaseChangeMap p (chartToSpace B S hS Y (V y))
    (pullback.snd p (chartToSpace B S hS Y (V y))) (pullback.fst p (chartToSpace B S hS Y (V y)))
    pullback.condition
  have hβ : ∀ y, IsIso (β y) := fun y =>
    isIso_moduleBaseChangeMap_of_isEtale B S hS _ _ _ _ (IsPullback.of_hasPullback _ _)
      (isEtale_chartToSpace B S hS Y (V y))
  have hd' := fun y => (descendsAlong_iff _ (hV' y) _).1 (hd y)
  rw [descendsAlong_iff p hp]
  refine ⟨isFiniteLocallyFree_of_forall_chart _ fun y => ⟨V y, hV y, ?_⟩, ?_⟩
  · have := hβ y
    exact isFiniteLocallyFree_of_iso (asIso ((β y).app M)).symm (hd' y).1
  · refine isIso_of_isIso_modulePullback_of_forall_mem_range
      (fun y => pullback.fst p (chartToSpace B S hS Y (V y)))
      (fun y => isEtale_of_isPullback B S hS _ _ _ _ (IsPullback.of_hasPullback p _).flip
        (isEtale_chartToSpace B S hS Y (V y))) (fun x => ?_) _ fun y => ?_
    · obtain ⟨v, hv⟩ := hV (pointsMap B S hS X.1 p.hom x)
      obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS
        (IsPullback.of_hasPullback p
          (chartToSpace B S hS Y (V (pointsMap B S hS X.1 p.hom x)))).flip
        v x hv
      exact ⟨_, w, hw⟩
    · have hs := moduleBaseChangeMap_adjoint_split p (chartToSpace B S hS Y (V y))
        (pullback.snd p (chartToSpace B S hS Y (V y)))
        (pullback.fst p (chartToSpace B S hS Y (V y))) pullback.condition M
      rw [Adjunction.homEquiv_counit] at hs
      have := (hd' y).2
      have := hβ y
      have h1 : IsIso ((modulePullback B S hS (pullback.snd p (chartToSpace B S hS Y (V y)))).map
          ((β y).app M) ≫
          (modulePullbackAdjunction B S hS
            (pullback.snd p (chartToSpace B S hS Y (V y)))).counit.app _) := inferInstance
      rw [hs] at h1
      exact IsIso.of_isIso_comp_left
        ((modulePullbackSquareComparison p (chartToSpace B S hS Y (V y))
          (pullback.snd p (chartToSpace B S hS Y (V y)))
          (pullback.fst p (chartToSpace B S hS Y (V y))) pullback.condition).inv.app
            ((modulePushforward B S hS p).obj M)) _

end AlgebraicGeometry.Space.DescentStratum

end
