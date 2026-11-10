module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteLocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel

/-!
# Limit preservation of the Hilbert functor of points

Let `X` be a scheme of finite presentation over `S` and let `d` be a natural number. The
degree-`d` Hilbert functor of points of `X` turns a cofiltered inverse limit of affine
`S`-schemes into a filtered colimit of sets: a degree-`d` family over the limit comes from a
degree-`d` family over some stage, and two families over stages which agree over the limit
already agree at a later stage.

## Main results

* `Stacks.Hilbert.exists_hilbertFamily_model`: a degree-`d` family over a cofiltered limit of
  affine `S`-schemes is the base change of a degree-`d` family over some stage.
* `Stacks.Hilbert.isLimitPreserving_hilbertFunctorOfRank`: **Stacks Tag 0B96**, the degree-`d`
  Hilbert functor of a scheme of finite presentation over `S` is limit preserving.

## Implementation notes

A degree-`d` family over `T` is an ideal sheaf on the ambient scheme `X ×_S T`, so the inverse
system that the descent arguments run over is not the given system `{T_i}` but the system
`{X ×_S T_i}` of ambient schemes, with limit `X ×_S T`. That system is `D` composed with
`Stacks.Hilbert.ambientSchemeFunctor`, and its limit cone is obtained from the limit cone of `D`
by the fact that `CategoryTheory.Over.pullback` is a right adjoint and that the forgetful functor
of an over category preserves connected limits. The ambient functor is written with the fibre
product in the order `X ×_S T` rather than `T ×_S X`, matching
`Stacks.Hilbert.familyBaseChangeMap`, and the comparison with `CategoryTheory.Over.pullback` is
`Stacks.Hilbert.ambientFunctorIso`.

Surjectivity of the comparison map is the source's argument: the closed subscheme cut out by the
family is of finite presentation over `T`, so it is the base change of a scheme over some stage
by Stacks Tag 01ZM part (1); its morphism to the ambient scheme is a closed immersion already at
a later stage by Stacks Tag 01ZP; and it is finite locally free of degree `d` at a later stage
still by the fixed-degree refinement of Stacks Tag 06AC. Injectivity is Stacks Tag 01ZM part (2)
applied twice, to the two closed immersions comparing the two families, which turns an inclusion
of ideal sheaves over the limit into an inclusion at a finite stage.

## References

* [Stacks Project, Tag 0B96](https://stacks.math.columbia.edu/tag/0B96)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 06AC](https://stacks.math.columbia.edu/tag/06AC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Hilbert

attribute [local instance] IsCofiltered.isConnected

private instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance quasiCompact_respectsIso :
    MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance quasiSeparated_respectsIso :
    MorphismProperty.RespectsIso (@QuasiSeparated : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-! ### The system of ambient schemes -/

/-- The ambient scheme `X ×_S T` of the degree-`d` families in `X` over `T`, as a functor of `T`
with values in the schemes over `X`. -/
def ambientFunctor {S : Scheme.{u}} (X : Over S) : Over S ⥤ Over X.left where
  obj T := Over.mk (pullback.fst X.hom T.hom)
  map g := Over.homMk (familyBaseChangeMap X g) (by
    simp [familyBaseChangeMap, pullback.map])
  map_id T := by
    ext
    apply pullback.hom_ext <;> simp [familyBaseChangeMap, pullback.map]
  map_comp f g := by
    ext
    apply pullback.hom_ext <;>
      simp [familyBaseChangeMap, pullback.map, Category.assoc]

/-- Comparison of the ambient scheme functor with `CategoryTheory.Over.pullback`: the two differ
by the order of the factors of the fibre product. -/
def ambientFunctorIso {S : Scheme.{u}} (X : Over S) :
    Over.pullback X.hom ≅ ambientFunctor X :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (pullbackSymmetry T.hom X.hom) (by simp [ambientFunctor]))
    (by
      intro T T' g
      ext
      apply pullback.hom_ext <;>
        dsimp [Over.isoMk, CostructuredArrow.isoMk, Comma.isoMk, Over.homMk,
          Over.Hom.left, Over.pullback, ambientFunctor] <;>
        simp only [familyBaseChangeMap, pullback.map, Category.assoc,
          pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
          pullback.lift_fst, pullback.lift_snd, Category.comp_id]
      simp only [← Category.assoc, pullbackSymmetry_hom_comp_snd])

/-- The ambient scheme `X ×_S T` as a functor of `T` with values in schemes. -/
abbrev ambientSchemeFunctor {S : Scheme.{u}} (X : Over S) : Over S ⥤ Scheme.{u} :=
  ambientFunctor X ⋙ Over.forget X.left

/-- The base change of a scheme of finite presentation is of finite presentation. -/
private theorem finitePresentation_ambient {S : Scheme.{u}} {X : Over S}
    (hX : FinitePresentation X.hom) (T : Over S) :
    FinitePresentation ((Over.pullback T.hom).obj X).hom :=
  finitePresentation_overPullbackObj T.hom X hX

/-! ### Ideal sheaves of closed subschemes descend -/

/-- The kernel of a base change of a closed immersion is the pullback of its kernel. -/
private theorem ker_pullback_snd {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsClosedImmersion f] : (pullback.snd f g).ker = f.ker.comap g := by
  rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry g f).hom,
    pullbackSymmetry_hom_comp_snd, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The closed subscheme cut out by the kernel of a closed immersion of finite presentation is
of finite presentation. -/
private theorem finitePresentation_ker_subschemeι {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [IsClosedImmersion f] (hf : FinitePresentation f) :
    FinitePresentation f.ker.subschemeι := by
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  change FinitePresentation f.imageι
  refine ⟨?_, ?_, ?_⟩
  · rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @LocallyOfFinitePresentation) f.toImage, f.toImage_imageι]
    infer_instance
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @QuasiCompact) f.toImage,
      f.toImage_imageι]
    infer_instance
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @QuasiSeparated) f.toImage,
      f.toImage_imageι]
    infer_instance

/-- If the closed subscheme cut out by `K` is isomorphic over `T` to the base change of a closed
immersion `Z ⟶ Y` along `q`, then `K` is the pullback along `q` of the kernel of `Z ⟶ Y`. -/
private theorem comap_ker_eq_of_iso {Y T : Scheme.{u}} (Z : Over Y) [IsClosedImmersion Z.hom]
    (q : T ⟶ Y) {K : T.IdealSheafData} (a : Over.mk K.subschemeι ≅ (Over.pullback q).obj Z) :
    Z.hom.ker.comap q = K := by
  have : IsIso a.hom.left := (Over.forget _).map_isIso a.hom
  rw [← ker_pullback_snd, ← Scheme.Hom.ker_comp_of_isIso a.hom.left]
  change (a.hom.left ≫ ((Over.pullback q).obj Z).hom).ker = K
  rw [Over.w a.hom]
  exact K.ker_subschemeι

/-- If the closed subscheme cut out by `K` is isomorphic over `T` to the base change of `Z` along
`q`, then that base change is a closed immersion. -/
private theorem isClosedImmersion_pullback_hom_of_iso {Y T : Scheme.{u}} (Z : Over Y)
    (q : T ⟶ Y) {K : T.IdealSheafData} (a : Over.mk K.subschemeι ≅ (Over.pullback q).obj Z) :
    IsClosedImmersion ((Over.pullback q).obj Z).hom := by
  have : IsIso a.hom.left := (Over.forget _).map_isIso a.hom
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) a.hom.left,
    Over.w a.hom]
  exact inferInstanceAs (IsClosedImmersion K.subschemeι)

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- An inclusion of the pullbacks of two ideal sheaves of finite presentation to the limit holds
already at a finite stage. -/
private theorem eventually_comap_le (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (J K : (D.obj i).IdealSheafData)
    (hJ : FinitePresentation J.subschemeι) (hK : FinitePresentation K.subschemeι)
    (h : J.comap (c.π.app i) ≤ K.comap (c.π.app i)) :
    ∃ (j : I) (e : j ⟶ i), J.comap (D.map e) ≤ K.comap (D.map e) := by
  let X := Over.mk K.subschemeι
  let Y := Over.mk J.subschemeι
  let X' := (Over.pullback (c.π.app i)).obj X
  let Y' := (Over.pullback (c.π.app i)).obj Y
  have hk : Y'.hom.ker ≤ X'.hom.ker := by
    simpa only [X', Y', X, Y, Over.pullback_obj_hom, Over.mk_hom, ker_pullback_snd,
      Scheme.IdealSheafData.ker_subschemeι] using h
  have : IsClosedImmersion Y'.hom := by
    change IsClosedImmersion (pullback.snd J.subschemeι (c.π.app i))
    infer_instance
  let f : X' ⟶ Y' := Over.homMk (IsClosedImmersion.lift Y'.hom X'.hom hk)
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ :=
    AlgebraicGeometry.exists_morphism_after_baseChange D c hc i X Y hK hJ f
  refine ⟨j, e, ?_⟩
  have hh := g.left.le_ker_comp ((Over.pullback (D.map e)).obj Y).hom
  rw [Over.w g] at hh
  simpa only [X, Y, Over.pullback_obj_hom, Over.mk_hom, ker_pullback_snd,
    Scheme.IdealSheafData.ker_subschemeι] using hh

/-- Two ideal sheaves of finite presentation with the same pullback to the limit have the same
pullback at a finite stage. -/
private theorem eventually_comap_eq (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (J K : (D.obj i).IdealSheafData)
    (hJ : FinitePresentation J.subschemeι) (hK : FinitePresentation K.subschemeι)
    (h : J.comap (c.π.app i) = K.comap (c.π.app i)) :
    ∃ (j : I) (e : j ⟶ i), J.comap (D.map e) = K.comap (D.map e) := by
  obtain ⟨j, e, hj⟩ := eventually_comap_le D c hc i J K hJ hK h.le
  obtain ⟨k, f, hk⟩ := eventually_comap_le D c hc i K J hK hJ h.ge
  obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan e f
  have step {m n : I} (J K : (D.obj i).IdealSheafData) (p : m ⟶ i) (q : n ⟶ m)
      (h : J.comap (D.map p) ≤ K.comap (D.map p)) :
      J.comap (D.map (q ≫ p)) ≤ K.comap (D.map (q ≫ p)) := by
    simpa only [D.map_comp, Scheme.IdealSheafData.comap_comp] using
      Scheme.IdealSheafData.comap_mono (f := D.map q) h
  exact ⟨l, a ≫ e, le_antisymm (step J K e a hj) (hab ▸ step K J f b hk)⟩

/-- An ideal sheaf of finite presentation on the limit is the pullback of an ideal sheaf of
finite presentation at a finite stage. -/
theorem exists_closed_model (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [EssentiallySmall.{u} I]
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (K : c.pt.IdealSheafData) (hK : FinitePresentation K.subschemeι) :
    ∃ (i : I) (J : (D.obj i).IdealSheafData),
      FinitePresentation J.subschemeι ∧ J.comap (c.π.app i) = K := by
  obtain ⟨i, Z, hZ, ⟨a⟩⟩ :=
    AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation D c hc
      (Over.mk K.subschemeι) hK
  have : LocallyOfFinitePresentation Z.hom := hZ.1
  have : QuasiCompact Z.hom := hZ.2.1
  have : QuasiSeparated Z.hom := hZ.2.2
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have hiso {Y : Scheme.{u}} (q : Y ⟶ D.obj i) :
      IsIso ((Over.pullback q).obj (Over.mk (𝟙 (D.obj i)))).hom := by
    change IsIso (pullback.snd (𝟙 _) q)
    infer_instance
  have : LocallyOfFiniteType
      (Over.homMk Z.hom (Category.comp_id Z.hom) :
        Z ⟶ Over.mk (𝟙 (D.obj i))).left := by
    change LocallyOfFiniteType Z.hom
    infer_instance
  have := isClosedImmersion_pullback_hom_of_iso Z (c.π.app i) a
  have : IsClosedImmersion
      ((Over.pullback (c.π.app i)).map
        (Over.homMk Z.hom (Category.comp_id Z.hom) :
          Z ⟶ Over.mk (𝟙 (D.obj i)))).left := by
    have := hiso (c.π.app i)
    rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _
      ((Over.pullback (c.π.app i)).obj (Over.mk (𝟙 (D.obj i)))).hom, Over.w]
    infer_instance
  obtain ⟨j, e, he⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_baseChange_of_isLimit D c hc i Z
      (Over.mk (𝟙 (D.obj i))) (Over.homMk Z.hom (Category.comp_id Z.hom))
  have := hiso (D.map e)
  have hci : IsClosedImmersion ((Over.pullback (D.map e)).obj Z).hom := by
    rw [← Over.w ((Over.pullback (D.map e)).map
      (Over.homMk Z.hom (Category.comp_id Z.hom) : Z ⟶ Over.mk (𝟙 (D.obj i))))]
    infer_instance
  have hZ' : FinitePresentation ((Over.pullback (D.map e)).obj Z).hom :=
    finitePresentation_overPullbackObj (D.map e) Z hZ
  exact ⟨j, ((Over.pullback (D.map e)).obj Z).hom.ker, finitePresentation_ker_subschemeι _ hZ',
    comap_ker_eq_of_iso ((Over.pullback (D.map e)).obj Z) (c.π.app j)
      (a ≪≫ AlgebraicGeometry.overPullbackObj_shiftIso D c e Z)⟩

/-! ### Comparing the degree of a closed subscheme with its base change -/

/-- Around a cartesian square, the restriction of the base change of a closed subscheme is
finite locally free of degree `d` exactly when the base change of the restriction is. -/
private theorem rank_comap_iff {A T A' T' : Scheme.{u}}
    {p : A ⟶ T} {p' : A' ⟶ T'} {a : A' ⟶ A} {g : T' ⟶ T}
    (sq : IsPullback a p' p g) (J : A.IdealSheafData) (d : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((J.comap a).subschemeι ≫ p') d ↔
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank
        (pullback.snd (J.subschemeι ≫ p) g) d := by
  have hs : IsPullback (J.comap a).subschemeι
      ((J.comapIso a).hom ≫ pullback.snd a J.subschemeι) a J.subschemeι := by
    apply isPullback_of_isClosedImmersion
    · rw [← J.comapIso_hom_fst a, Category.assoc, pullback.condition, Category.assoc]
    · simp
  exact AlgebraicGeometry.prop_iff_of_isPullback
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} d)
    (hs.flip.paste_vert sq) (IsPullback.of_hasPullback (J.subschemeι ≫ p) g)

/-- The closed subscheme cut out by a degree-`d` family is of finite presentation over the
ambient scheme. -/
private theorem finitePresentation_family_subschemeι {S : Scheme.{u}} {X T : Over S} {dd : ℕ}
    [LocallyOfFiniteType X.hom] (F : HilbertFamily X T dd) :
    FinitePresentation F.ideal.subschemeι := by
  have hcomp : LocallyOfFinitePresentation
      (F.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (F.ideal.subschemeι ≫ ((Over.pullback T.hom).obj X).hom)).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ dd
        (h := F.isFiniteLocallyFreeOfRank))).2.2
  have : LocallyOfFiniteType ((Over.pullback T.hom).obj X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom T.hom)
    infer_instance
  exact ⟨AlgebraicGeometry.locallyOfFinitePresentation_of_comp F.ideal.subschemeι
    ((Over.pullback T.hom).obj X).hom, inferInstance, inferInstance⟩

/-! ### Degree-`d` families descend -/

variable {S : Scheme.{u}}

private instance isAffineHom_map_ambientSchemeFunctor (X : Over S) (D : I ⥤ Over S)
    [∀ i, IsAffine (D.obj i).left] {i j : I} (e : i ⟶ j) :
    IsAffineHom ((D ⋙ ambientSchemeFunctor X).map e) := by
  change IsAffineHom (familyBaseChangeMap X (D.map e))
  have : IsAffineHom (D.map e).left := inferInstance
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_familyBaseChangeMap X (D.map e)).flip inferInstance

private instance compactSpace_obj_ambientSchemeFunctor (X : Over S) [QuasiCompact X.hom]
    (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left] (i : I) :
    CompactSpace ((D ⋙ ambientSchemeFunctor X).obj i) := by
  change CompactSpace ↑(Limits.pullback X.hom (D.obj i).hom)
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd X.hom (D.obj i).hom)

private instance quasiSeparatedSpace_obj_ambientSchemeFunctor (X : Over S)
    [QuasiSeparated X.hom] (D : I ⥤ Over S) [∀ i, QuasiSeparatedSpace (D.obj i).left] (i : I) :
    QuasiSeparatedSpace ((D ⋙ ambientSchemeFunctor X).obj i) := by
  change QuasiSeparatedSpace ↑(Limits.pullback X.hom (D.obj i).hom)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd X.hom (D.obj i).hom)

/-- The ambient-scheme functor `T ↦ X ×_S T` preserves limit cones. -/
private def isLimitAmbientMapCone (X : Over S) {J : Type u} [Category.{u} J] [IsCofiltered J]
    {D : J ⥤ Over S} {c : Cone D} (hc : IsLimit c) : IsLimit ((ambientSchemeFunctor X).mapCone c) :=
  have : PreservesLimit D (ambientFunctor X) := preservesLimit_of_natIso D (ambientFunctorIso X)
  isLimitOfPreserves (ambientSchemeFunctor X) hc

/-- If an ideal sheaf on `X ×_S T` pulls back along `g : T' ⟶ T` to a degree-`d` family, then
the base change along `g` of the closed subscheme it cuts out is finite locally free of
degree `d`. -/
private theorem isFiniteLocallyFreeOfRank_of_comap_eq {X T T' : Over S} {d : ℕ} (g : T' ⟶ T)
    (J : ((Over.pullback T.hom).obj X).left.IdealSheafData) (F : HilbertFamily X T' d)
    (hJF : J.comap (familyBaseChangeMap X g) = F.ideal) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd (J.subschemeι ≫ ((Over.pullback T.hom).obj X).hom) g.left) d := by
  refine (rank_comap_iff (isPullback_familyBaseChangeMap X g) J d).mp ?_
  rw [hJF]
  exact F.isFiniteLocallyFreeOfRank

/-- **A degree-`d` family over a cofiltered limit comes from a stage.** Let `X` be of finite
presentation over `S` and let `D` be a cofiltered inverse system of affine schemes over `S` with
limit cone `c`. Every degree-`d` family in `X` over the limit is the base change of a degree-`d`
family in `X` over some stage. -/
theorem exists_hilbertFamily_model (X : Over S) (d : ℕ) (hX : FinitePresentation X.hom)
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i).left]
    (F : HilbertFamily X c.pt d) :
    ∃ (i : I) (G : HilbertFamily X (D.obj i) d),
      G.ideal.comap (familyBaseChangeMap X (c.π.app i)) = F.ideal := by
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  -- The system of ambient schemes and its limit cone.
  -- Tag 01ZM part (1) together with Tag 01ZP: the family descends as a closed subscheme.
  obtain ⟨i, J, hJ, hJF⟩ := exists_closed_model (D ⋙ ambientSchemeFunctor X)
    ((ambientSchemeFunctor X).mapCone c) (isLimitAmbientMapCone X hc) F.ideal
      (finitePresentation_family_subschemeι F)
  -- The degree-`d` condition descends by the fixed-degree refinement of Tag 06AC.
  have hp := finitePresentation_ambient hX (D.obj i)
  let Zi : Over (D.obj i).left :=
    Over.mk (J.subschemeι ≫ ((Over.pullback (D.obj i).hom).obj X).hom)
  have hZi : FinitePresentation Zi.hom :=
    ⟨@locallyOfFinitePresentation_comp _ _ _ _ _ hJ.1 hp.1,
      @quasiCompact_comp _ _ _ _ _ hJ.2.1 hp.2.1,
      @quasiSeparated_comp _ _ _ _ _ hJ.2.2 hp.2.2⟩
  have {i j : I} (e : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget S).map e) := by
    change IsAffineHom (D.map e).left
    infer_instance
  have (i : I) : CompactSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace ((D ⋙ Over.forget S).obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Over.pullback (((Over.forget S).mapCone c).π.app i)).obj Zi).hom d :=
    isFiniteLocallyFreeOfRank_of_comap_eq (c.π.app i) J F hJF
  obtain ⟨j, e, he⟩ :=
    AlgebraicGeometry.exists_isFiniteLocallyFreeOfRank_overPullbackObj_of_isLimit
      (D ⋙ Over.forget S) ((Over.forget S).mapCone c)
      (isLimitOfPreserves (Over.forget S) hc) i Zi hZi d
  have he' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((J.comap (familyBaseChangeMap X (D.map e))).subschemeι ≫
        ((Over.pullback (D.obj j).hom).obj X).hom) d :=
    (rank_comap_iff (isPullback_familyBaseChangeMap X (D.map e)) J d).mpr he
  refine ⟨j, ⟨J.comap (familyBaseChangeMap X (D.map e)), he'⟩, ?_⟩
  change (J.comap ((D ⋙ ambientSchemeFunctor X).map e)).comap
    (((ambientSchemeFunctor X).mapCone c).π.app j) = F.ideal
  rw [← Scheme.IdealSheafData.comap_comp, ((ambientSchemeFunctor X).mapCone c).w e, hJF]

/-- **Stacks Project, Tag 0B96.** If `X ⟶ S` is of finite presentation, then the degree-`d`
Hilbert functor of points of `X` over `S` is limit preserving: it turns every cofiltered inverse
limit of affine `S`-schemes into a filtered colimit of sets. -/
@[stacks 0B96]
theorem isLimitPreserving_hilbertFunctorOfRank (X : Over S) (d : ℕ)
    (hX : FinitePresentation X.hom) :
    Scheme.IsLimitPreserving S (hilbertFunctorOfRank X d) := by
  intro I _ _ D hD
  classical
  have : LocallyOfFinitePresentation X.hom := hX.1
  have : QuasiCompact X.hom := hX.2.1
  have : QuasiSeparated X.hom := hX.2.2
  have (i : I) : IsAffine (D.obj i).left := hD i
  refine ⟨fun {cc} hcc ↦ ⟨?_⟩⟩
  set H := hilbertFunctorOfRank X d
  refine Types.FilteredColimit.isColimitOf (D.op ⋙ H) (H.mapCocone cc) ?_ ?_
  · intro z
    obtain ⟨i, G, hG⟩ := exists_hilbertFamily_model X d hX D cc.unop hcc.unop z
    exact ⟨Opposite.op i, G, HilbertFamily.ext hG.symm⟩
  · intro i j x y hxy
    obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i.unop j.unop
    have hxk : (H.map (cc.unop.π.app k).op) (H.map (D.map a).op x) =
        (H.map (cc.unop.π.app i.unop).op) x := by
      rw [← Functor.map_comp_apply, ← op_comp, cc.unop.w a]
    have hyk : (H.map (cc.unop.π.app k).op) (H.map (D.map b).op y) =
        (H.map (cc.unop.π.app j.unop).op) y := by
      rw [← Functor.map_comp_apply, ← op_comp, cc.unop.w b]
    have hbase : (baseChange X (cc.unop.π.app k) (baseChange X (D.map a) x)).ideal =
        (baseChange X (cc.unop.π.app k) (baseChange X (D.map b) y)).ideal :=
      congrArg HilbertFamily.ideal (hxk.trans (hxy.trans hyk.symm))
    obtain ⟨l, e, he⟩ := eventually_comap_eq (D ⋙ ambientSchemeFunctor X)
      ((ambientSchemeFunctor X).mapCone cc.unop) (isLimitAmbientMapCone X hcc.unop) k
      (baseChange X (D.map a) x).ideal (baseChange X (D.map b) y).ideal
      (finitePresentation_family_subschemeι (baseChange X (D.map a) x))
      (finitePresentation_family_subschemeι (baseChange X (D.map b) y))
      hbase
    refine ⟨Opposite.op l, (e ≫ a).op, (e ≫ b).op, ?_⟩
    change baseChange X (D.map (e ≫ a)) x = baseChange X (D.map (e ≫ b)) y
    rw [D.map_comp, D.map_comp]
    exact (baseChange_comp X (D.map e) (D.map a) x).trans
      ((HilbertFamily.ext he).trans (baseChange_comp X (D.map e) (D.map b) y).symm)

end Stacks.Hilbert

end
