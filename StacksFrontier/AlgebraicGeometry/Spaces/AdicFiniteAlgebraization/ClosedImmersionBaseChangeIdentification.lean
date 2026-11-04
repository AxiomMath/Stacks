module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafPushforwardDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSheafCartesianSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian

/-!
# A closed subspace is identified with a base change by its direct image

Let `j : Z ⟶ X` be a closed immersion of algebraic spaces, `ι : Y ⟶ X` a morphism and
`z : Z' ⟶ Y` a closed immersion. Suppose that the pullback `ι^*(j_*𝒪_Z)` is isomorphic to
`z_*𝒪_{Z'}` compatibly with the two maps out of `𝒪_Y = ι^*𝒪_X`. Then `Z'` is the base change
`Z ×_X Y`, as a space over `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_comp_eq_of_kernelIdealSheaf_le`: a morphism factors through a
  closed immersion `i` when it kills the kernel ideal sheaf of `i`.
* `AlgebraicGeometry.Space.comp_pushforwardStructureProjection_eq_zero_iff`: a map into `𝒪_X` is
  killed by `(f ≫ g)♯` exactly when its pullback along `g` is killed by `f♯`.
* `AlgebraicGeometry.Space.exists_iso_fiberProduct_of_modulePullback_iso`: a closed subspace
  of `Y` whose direct image is `ι^*(j_*𝒪_Z)` under `𝒪_Y` is the base change of `j` along `ι`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the modules of the universe used here; `AlgebraicGeometry.Space.Modules`
carries its own abelian structure. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism factors through a closed immersion as soon as it kills the kernel ideal sheaf of
the immersion.** -/
theorem exists_comp_eq_of_kernelIdealSheaf_le {T Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (h : T ⟶ X)
    (hle : kernelIdealSheaf B S hS i ≤ kernelIdealSheaf B S hS h) :
    ∃ g : T ⟶ Z, g ≫ i = h := by
  have : Mono i.hom := mono_of_isClosedImmersion B S hS i.hom hi
  let W : ClosedSubspaces B S hS X.1 :=
    ⟨Subfunctor.range i.hom, isClosedSubspace_range_of_isClosedImmersion B S hS i.hom Z.2 hi⟩
  let e : Z ≅ (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (asIso (Subfunctor.toRange i.hom))
  have he : e.hom ≫ (ObjectProperty.homMk W.1.ι :
      (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) = i :=
    ObjectProperty.hom_ext _ (Subfunctor.toRange_ι i.hom)
  have hk : kernelIdealSheaf B S hS i = definingIdealSheaf B S hS X W := by
    rw [← he, kernelIdealSheaf_comp_of_isIso]
    rfl
  obtain ⟨g, hg⟩ :=
    (exists_comp_eq_iff_definingIdealSheaf_le_kernelIdealSheaf B S hS X W h).2 (hk ▸ hle)
  exact ⟨g ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact hg⟩

/-- **A map into `𝒪_X` is killed by `(f ≫ g)♯` exactly when its pullback along `g`, read into
`𝒪_Y`, is killed by `f♯`.** For `f : T ⟶ Y`, `g : Y ⟶ X` and `φ : 𝓜 ⟶ 𝒪_X`, the composite
`g^*𝓜 ⟶ g^*𝒪_X ≅ 𝒪_Y ⟶ f_*𝒪_T` vanishes exactly when `𝓜 ⟶ 𝒪_X ⟶ (f ≫ g)_*𝒪_T` does. -/
theorem comp_pushforwardStructureProjection_eq_zero_iff {T Y X : AlgebraicSpaces B S hS}
    (f : T ⟶ Y) (g : Y ⟶ X) {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) :
    ((modulePullback B S hS g).map φ ≫ (modulePullbackUnitIso B S hS g).hom) ≫
        pushforwardStructureProjection B S hS f = 0 ↔
      φ ≫ pushforwardStructureProjection B S hS (f ≫ g) = 0 := by
  have hc := modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom B S hS f g
  have hn := (modulePullbackCompIso B S hS f g).hom.naturality φ
  have key : (modulePullback B S hS f).map
        ((modulePullback B S hS g).map φ ≫ (modulePullbackUnitIso B S hS g).hom) ≫
        (modulePullbackUnitIso B S hS f).hom =
      (modulePullbackCompIso B S hS f g).hom.app M ≫
        ((modulePullback B S hS (f ≫ g)).map φ ≫ (modulePullbackUnitIso B S hS (f ≫ g)).hom) := by
    calc _ = ((modulePullback B S hS f).map ((modulePullback B S hS g).map φ) ≫
            (modulePullback B S hS f).map (modulePullbackUnitIso B S hS g).hom) ≫
            (modulePullbackUnitIso B S hS f).hom :=
          congrArg (· ≫ (modulePullbackUnitIso B S hS f).hom) (Functor.map_comp _ _ _)
      _ = (modulePullback B S hS f).map ((modulePullback B S hS g).map φ) ≫
            ((modulePullback B S hS f).map (modulePullbackUnitIso B S hS g).hom ≫
            (modulePullbackUnitIso B S hS f).hom) := Category.assoc _ _ _
      _ = (modulePullback B S hS f).map ((modulePullback B S hS g).map φ) ≫
            ((modulePullbackCompIso B S hS f g).hom.app
              (SheafOfModules.unit (structureRingSheaf B S hS X)) ≫
            (modulePullbackUnitIso B S hS (f ≫ g)).hom) :=
          congrArg ((modulePullback B S hS f).map ((modulePullback B S hS g).map φ) ≫ ·) hc.symm
      _ = ((modulePullback B S hS g ⋙ modulePullback B S hS f).map φ ≫
            (modulePullbackCompIso B S hS f g).hom.app
              (SheafOfModules.unit (structureRingSheaf B S hS X))) ≫
            (modulePullbackUnitIso B S hS (f ≫ g)).hom := (Category.assoc _ _ _).symm
      _ = ((modulePullbackCompIso B S hS f g).hom.app M ≫
            (modulePullback B S hS (f ≫ g)).map φ) ≫
            (modulePullbackUnitIso B S hS (f ≫ g)).hom :=
          congrArg (· ≫ (modulePullbackUnitIso B S hS (f ≫ g)).hom) hn
      _ = _ := Category.assoc _ _ _
  refine (modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff B S hS f
    ((modulePullback B S hS g).map φ ≫ (modulePullbackUnitIso B S hS g).hom)).symm.trans
    (Iff.trans ?_ (modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff B S hS (f ≫ g) φ))
  exact (Iff.of_eq (congrArg (· = 0) key)).trans (Preadditive.IsIso.comp_left_eq_zero _ _)

/-- The vanishing criterion of `comp_pushforwardStructureProjection_eq_zero_iff`, read on sections
over every étale chart. -/
private theorem comp_pushforwardStructureProjection_eq_zero_iff_forall
    {T Y X : AlgebraicSpaces B S hS} (f : T ⟶ Y) (g : Y ⟶ X) {M : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) :
    ((modulePullback B S hS g).map φ ≫ (modulePullbackUnitIso B S hS g).hom) ≫
        pushforwardStructureProjection B S hS f = 0 ↔
      ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj U),
        (structureSharp B S hS (f ≫ g)).hom.app U (φ.val.app U x) = 0 :=
  (comp_pushforwardStructureProjection_eq_zero_iff B S hS f g φ).trans
    ((modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff B S hS (f ≫ g) φ).symm.trans
      (modulePullback_map_comp_modulePullbackUnitIso_hom_eq_zero_iff_forall B S hS (f ≫ g) φ))

variable {B S hS}

/-- **A closed subspace of `Y` whose direct image is `ι^*(j_*𝒪_Z)` under `𝒪_Y` is the base
change of `j` along `ι`.** Let `j : Z ⟶ X` and `z : Z' ⟶ Y` be closed immersions and
`ι : Y ⟶ X` a morphism of algebraic spaces. An isomorphism `ι^*(j_*𝒪_Z) ≅ z_*𝒪_{Z'}` of
`𝒪_Y`-modules carrying the pullback of `𝒪_X ⟶ j_*𝒪_Z`, read out of `𝒪_Y = ι^*𝒪_X`, to
`𝒪_Y ⟶ z_*𝒪_{Z'}` identifies `Z'` over `Y` with the fibre product `Z ×_X Y`. -/
theorem exists_iso_fiberProduct_of_modulePullback_iso {X Y Zs Zn : AlgebraicSpaces B S hS}
    (j : Zs ⟶ X) (hj : IsClosedImmersion B S hS j.hom) (ι : Y ⟶ X)
    (z : Zn ⟶ Y) (hz : IsClosedImmersion B S hS z.hom)
    (e : (modulePullback B S hS ι).obj (structureSheafPushforward B S hS j) ≅
      structureSheafPushforward B S hS z)
    (he : (modulePullbackUnitIso B S hS ι).inv ≫
        (modulePullback B S hS ι).map (pushforwardStructureProjection B S hS j) ≫ e.hom =
      pushforwardStructureProjection B S hS z) :
    ∃ e' : Zn ≅ AlgebraicSpaces.fiberProduct B S hS j ι,
      e'.hom ≫ (ObjectProperty.homMk (pullback.snd j.hom ι.hom) :
        AlgebraicSpaces.fiberProduct B S hS j ι ⟶ Y) = z := by
  obtain ⟨q, p, sq, hp⟩ : ∃ (q : AlgebraicSpaces.fiberProduct B S hS j ι ⟶ Zs)
      (p : AlgebraicSpaces.fiberProduct B S hS j ι ⟶ Y), IsPullback q p j ι ∧
        p = ObjectProperty.homMk (pullback.snd j.hom ι.hom) :=
    ⟨_, _, AlgebraicSpaces.isPullback_fiberProduct B S hS j ι, rfl⟩
  have hpmono : Mono p.hom := by
    subst hp
    have : Mono j.hom := mono_of_isClosedImmersion B S hS j.hom hj
    exact inferInstanceAs (Mono (pullback.snd j.hom ι.hom))
  rw [← hp]
  obtain ⟨M, φ, hφ, hmem, hsurj, hdesc⟩ : ∃ (M : Modules.{u, u} B S hS X.1 X.2)
      (φ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)),
      φ ≫ pushforwardStructureProjection B S hS j = 0 ∧
      (∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj U),
        (show (structureRingSheaf B S hS X).obj.obj U from φ.val.app U x) ∈
          (kernelIdealSheaf B S hS j).obj U) ∧
      (∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (s : (structureRingSheaf B S hS X).obj.obj U),
        s ∈ (kernelIdealSheaf B S hS j).obj U →
          ∃ x : M.val.obj U,
            (show (structureRingSheaf B S hS X).obj.obj U from φ.val.app U x) = s) ∧
      ∀ {N : Modules.{u, u} B S hS X.1 X.2}
        (t : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ N), φ ≫ t = 0 →
        ∃ w : structureSheafPushforward B S hS j ⟶ N,
          pushforwardStructureProjection B S hS j ≫ w = t := by
    have hSE := pushforwardStructureShortComplex_shortExact B S hS j hj
    have := hSE.epi_g
    exact ⟨_, (pushforwardStructureShortComplex B S hS j).f,
      (pushforwardStructureShortComplex B S hS j).zero, fun U x => x.2,
      fun U s hs => ⟨⟨s, hs⟩, rfl⟩,
      fun t ht => ⟨hSE.exact.desc t ht, hSE.exact.g_desc t ht⟩⟩
  have he' : (modulePullbackUnitIso B S hS ι).inv ≫
      (modulePullback B S hS ι).map (pushforwardStructureProjection B S hS j) =
      pushforwardStructureProjection B S hS z ≫ e.inv :=
    (Iso.eq_comp_inv e).2 ((Category.assoc _ _ _).trans he)
  have ha : ((modulePullback B S hS ι).map φ ≫ (modulePullbackUnitIso B S hS ι).hom) ≫
      pushforwardStructureProjection B S hS z = 0 := by
    calc _ = ((modulePullback B S hS ι).map φ ≫ (modulePullbackUnitIso B S hS ι).hom) ≫
          ((modulePullbackUnitIso B S hS ι).inv ≫
            (modulePullback B S hS ι).map (pushforwardStructureProjection B S hS j) ≫ e.hom) :=
          congrArg (_ ≫ ·) he.symm
      _ = (modulePullback B S hS ι).map φ ≫
            (modulePullback B S hS ι).map (pushforwardStructureProjection B S hS j) ≫ e.hom :=
          (Category.assoc _ _ _).trans
            (congrArg ((modulePullback B S hS ι).map φ ≫ ·) (Iso.hom_inv_id_assoc _ _))
      _ = (modulePullback B S hS ι).map (φ ≫ pushforwardStructureProjection B S hS j) ≫ e.hom :=
          (Functor.map_comp_assoc _ _ _ _).symm
      _ = (modulePullback B S hS ι).map 0 ≫ e.hom :=
          congrArg (fun k => (modulePullback B S hS ι).map k ≫ e.hom) hφ
      _ = 0 := by
          have : (modulePullback B S hS ι).IsLeftAdjoint :=
            (modulePullbackAdjunction B S hS ι).isLeftAdjoint
          rw [Functor.map_zero, zero_comp]
  have ha' := (comp_pushforwardStructureProjection_eq_zero_iff_forall B S hS z ι φ).1 ha
  have hlea : kernelIdealSheaf B S hS j ≤ kernelIdealSheaf B S hS (z ≫ ι) := by
    intro U s hs
    obtain ⟨x, rfl⟩ := hsurj U s hs
    exact (RingHom.mem_ker (f := ((structureSharp B S hS (z ≫ ι)).hom.app U).hom)).2 (ha' U x)
  obtain ⟨g, hg⟩ := exists_comp_eq_of_kernelIdealSheaf_le B S hS j hj (z ≫ ι) hlea
  have hb := (comp_pushforwardStructureProjection_eq_zero_iff_forall B S hS p ι φ).2
    fun U x => RingHom.mem_ker.1 (kernelIdealSheaf_le_comp B S hS p j q ι sq.w.symm U (hmem U x))
  have ht : φ ≫ (modulePullbackAdjunction B S hS ι).homEquiv _ _
      ((modulePullbackUnitIso B S hS ι).hom ≫ pushforwardStructureProjection B S hS p) = 0 := by
    refine ((modulePullbackAdjunction B S hS ι).homEquiv_naturality_left φ _).symm.trans ?_
    refine (congrArg ((modulePullbackAdjunction B S hS ι).homEquiv _ _)
      ((Category.assoc _ _ _).symm.trans hb)).trans ?_
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  obtain ⟨w', hw'⟩ := hdesc _ ht
  have hw : (modulePullback B S hS ι).map (pushforwardStructureProjection B S hS j) ≫
      ((modulePullbackAdjunction B S hS ι).homEquiv _ _).symm w' =
      (modulePullbackUnitIso B S hS ι).hom ≫ pushforwardStructureProjection B S hS p :=
    ((modulePullbackAdjunction B S hS ι).homEquiv_naturality_left_symm _ _).symm.trans
      ((congrArg ((modulePullbackAdjunction B S hS ι).homEquiv _ _).symm hw').trans
        (((modulePullbackAdjunction B S hS ι).homEquiv _ _).symm_apply_apply _))
  have hpz : pushforwardStructureProjection B S hS p = pushforwardStructureProjection B S hS z ≫
      e.inv ≫ ((modulePullbackAdjunction B S hS ι).homEquiv _ _).symm w' :=
    (Iso.inv_hom_id_assoc _ _).symm.trans
      ((congrArg ((modulePullbackUnitIso B S hS ι).inv ≫ ·) hw.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ ((modulePullbackAdjunction B S hS ι).homEquiv _ _).symm w') he').trans
            (Category.assoc _ _ _))))
  have hleb : kernelIdealSheaf B S hS z ≤ kernelIdealSheaf B S hS p := by
    intro U x hx
    have h0 : (pushforwardStructureProjection B S hS z).val.app U x = 0 :=
      (RingHom.mem_ker (f := ((structureSharp B S hS z).hom.app U).hom)).1 hx
    refine (RingHom.mem_ker (f := ((structureSharp B S hS p).hom.app U).hom)).2
      ((congrArg (fun k => k.val.app U
      (show (SheafOfModules.unit (structureRingSheaf B S hS Y)).val.obj U from x)) hpz).trans ?_)
    show (e.inv ≫ ((modulePullbackAdjunction B S hS ι).homEquiv _ _).symm w').val.app U
      ((pushforwardStructureProjection B S hS z).val.app U x) = 0
    rw [h0, map_zero]
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_kernelIdealSheaf_le B S hS z hz p hleb
  have : Mono z :=
    (ObjectProperty.ι _).mono_of_mono_map (mono_of_isClosedImmersion B S hS z.hom hz)
  have : Mono p := (ObjectProperty.ι _).mono_of_mono_map hpmono
  refine ⟨⟨sq.lift g z hg, g', ?_, ?_⟩, sq.lift_snd g z hg⟩
  · exact (cancel_mono z).1 (by rw [Category.assoc, hg', sq.lift_snd, Category.id_comp])
  · exact (cancel_mono p).1 (by rw [Category.assoc, sq.lift_snd, hg', Category.id_comp])

end AlgebraicGeometry.Space

end
