module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Quot.PicardSequenceSplitting
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackGerbe
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackSchemeProperty
public import StacksFrontier.CategoryTheory.Sites.CostructuredArrowRestrictedTopology

/-!
# The diagonal of the relative Picard functor

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S`, and let `Pic_{X/B}` be its
relative Picard functor (Stacks 0D25), a sheaf on the schemes over `B`. Stacks 0D2D asserts that
under the hypotheses of Stacks 0D2C the diagonal `Pic_{X/B} ⟶ Pic_{X/B} ×_B Pic_{X/B}` is
representable by immersions. Its proof has two steps: a reduction to the case where the two
points of `Pic_{X/B}` come from invertible modules, by fppf descent of immersions, and the case
of invertible modules, which is Stacks 0D23.

The first step, the reduction, holds unconditionally, in three parts. The second step is
Stacks 0D23: the locally closed subscheme of the base over which an invertible module on `X_T`
becomes the pullback of an invertible module on the base.

* **The diagonal of a morphism of presheaves is read on equalizers.** For a morphism
  `q : F ⟶ G` of presheaves on the big fppf site of `S` and a point `h : h_a ⟶ F ×_G F`, the
  base change of the relative diagonal of `q` along `h` is the inclusion of the subfunctor of
  `h_a` of the morphisms `g : U ⟶ a` along which the two components of `h` agree
  (`AlgebraicGeometry.Space.diagonalEqualizer`). So the diagonal is an immersion exactly when
  every such subfunctor is represented by immersions.
* **The equalizers of the Picard functor.** For a test scheme `T` over the base and two points
  `x, y` of `Pic_{X/B}(T)`, the morphisms `g : U ⟶ T` with `g^*x = g^*y` form a subfunctor
  `AlgebraicGeometry.Space.PicardSituation.picardEqualizer` of `h_T`. It is an fppf sheaf because
  `Pic_{X/B}` is, and its inverse image along a morphism `g : U ⟶ T` is the equalizer of
  `g^*x` and `g^*y`.
* **The reduction of Stacks 0D2D.** Every point of `Pic_{X/B}(T)` comes, fppf locally on `T`,
  from `Pic(X_T)`, and immersions descend effectively along the covering sieves of the site
  (Stacks 02W8 and 02YM), so the equalizer of `x` and `y` is represented by immersions as soon as
  the equalizers of the classes of any two invertible modules are, over every test scheme.

## Main definitions

* `AlgebraicGeometry.Space.diagonalEqualizer`: the subfunctor of `h_a` on which the two
  components of a point `h_a ⟶ F ×_G F` agree.
* `AlgebraicGeometry.Space.PicardSituation.picardEqualizer`: the subfunctor of `h_T` on which two
  points of `Pic_{X/B}(T)` agree.

## Main results

* `AlgebraicGeometry.Space.isImmersion_diagonal_iff`: the relative diagonal of `q` is an immersion
  exactly when every `diagonalEqualizer` is represented by immersions.
* `AlgebraicGeometry.Space.PicardSituation.isSheaf_picardEqualizer`: the equalizer of two points
  of `Pic_{X/B}(T)` is an fppf sheaf.
* `AlgebraicGeometry.Space.PicardSituation.picardEqualizer_preimage`: its inverse image along a
  morphism `g : U ⟶ T` is the equalizer of the pulled back points.
* `AlgebraicGeometry.Space.PicardSituation.mem_picardEqualizer_picardClassMap_iff`: for points
  coming from classes `v, w ∈ Pic(X_T)`, a morphism `g : U ⟶ T` lies in the equalizer exactly when
  `g^*v` and `g^*w` agree in `Pic(X_U)` fppf locally on `U`.
* `AlgebraicGeometry.Space.PicardSituation.picardEqualizer_picardClassMap_sub`: the equalizer of
  the images of `v, w ∈ Pic(X_T)` is the equalizer of the images of `v - w` and `0`.
* `AlgebraicGeometry.Space.PicardSituation.isImmersion_picardEqualizer_of_picardClassMap`: the
  reduction of Stacks 0D2D to points coming from invertible modules.
* `AlgebraicGeometry.Space.PicardSituation.isLocallySeparated_iff_of_represents`: for a morphism
  of presheaves `q : F ⟶ B` whose fibres are identified with `Pic_{X/B}` naturally in the test
  scheme, `q` is locally separated exactly when every equalizer of two points of `Pic_{X/B}` is
  represented by immersions.

## References

* [Stacks Project, Tag 0D2D](https://stacks.math.columbia.edu/tag/0D2D)
* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02YM](https://stacks.math.columbia.edu/tag/02YM)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The relative diagonal read on equalizers -/

section Diagonal

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F ⟶ G)

/-- The subfunctor of `h_a` on which the two components of a point `h : h_a ⟶ F ×_G F` agree:
the morphisms `g : U ⟶ a` with `g^*(h ≫ pr₁) = g^*(h ≫ pr₂)` in `F(U)`. -/
def diagonalEqualizer {a : BigFppfOver B S hS} (h : yoneda.obj a ⟶ pullback q q) :
    Subfunctor (yoneda.obj a) where
  obj U := {g | F.map g.op (yonedaEquiv (h ≫ pullback.fst q q)) =
    F.map g.op (yonedaEquiv (h ≫ pullback.snd q q))}
  map {U V} k g hg := by
    change F.map (k.unop ≫ g).op _ = F.map (k.unop ≫ g).op _
    simp only [op_comp, F.map_comp, types_comp_apply]
    exact congrArg (F.map k) hg

/-- A morphism `g : U ⟶ a` lies in the equalizer of the two components of `h : h_a ⟶ F ×_G F`
exactly when the two components of `h` agree after precomposition with `g`. -/
theorem mem_diagonalEqualizer_iff {a U : BigFppfOver B S hS} (h : yoneda.obj a ⟶ pullback q q)
    (g : U ⟶ a) :
    g ∈ (diagonalEqualizer q h).obj (Opposite.op U) ↔
      yoneda.map g ≫ h ≫ pullback.fst q q = yoneda.map g ≫ h ≫ pullback.snd q q := by
  change F.map g.op _ = F.map g.op _ ↔ _
  rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
  exact yonedaEquiv.injective.eq_iff

/-- The inverse image of the image of the relative diagonal along a point `h_a ⟶ F ×_G F` is
the equalizer of the two components of the point. -/
theorem preimage_range_diagonal {a : BigFppfOver B S hS} (h : yoneda.obj a ⟶ pullback q q) :
    (Subfunctor.range (pullback.diagonal q)).preimage h = diagonalEqualizer q h := by
  ext ⟨U⟩ g
  change h.app _ g ∈ (Subfunctor.range (pullback.diagonal q)).obj _ ↔ _
  rw [mem_diagonalEqualizer_iff]
  have hg : h.app (Opposite.op U) g = yonedaEquiv (yoneda.map g ≫ h) := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [hg]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : yonedaEquiv.symm z ≫ pullback.diagonal q = yoneda.map g ≫ h := by
      apply yonedaEquiv.injective
      rwa [yonedaEquiv_comp, Equiv.apply_symm_apply]
    rw [← Category.assoc, ← Category.assoc, ← hz', Category.assoc, Category.assoc,
      pullback.diagonal_fst, pullback.diagonal_snd]
  · intro hfs
    refine ⟨yonedaEquiv (yoneda.map g ≫ h ≫ pullback.fst q q), ?_⟩
    rw [← yonedaEquiv_comp]
    congr 1
    apply pullback.hom_ext
    · simp
    · simp [hfs]

/-- Being an immersion of the underlying schemes, for morphisms of presheaves on the big fppf
site, is stable under base change. -/
private theorem isStableUnderBaseChange_presheaf_inverseImage_isImmersion :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _

/-- **The relative diagonal of `q` is an immersion exactly when every equalizer of two points of
`F` with the same image in `G` is represented by immersions.** -/
theorem isImmersion_diagonal_iff :
    IsImmersion B S hS (pullback.diagonal q) ↔
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ pullback q q),
        IsImmersion B S hS (diagonalEqualizer q h).ι := by
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : Mono (pullback.diagonal q) := IsSplitMono.mono _
  have _ : IsIso (Subfunctor.toRange (pullback.diagonal q)) := inferInstance
  have hiso : Arrow.mk (pullback.diagonal q) ≅
      Arrow.mk (Subfunctor.range (pullback.diagonal q)).ι :=
    Arrow.isoMk (asIso (Subfunctor.toRange (pullback.diagonal q))) (Iso.refl _) (by simp)
  have hdiag : IsImmersion B S hS (pullback.diagonal q) ↔
      IsImmersion B S hS (Subfunctor.range (pullback.diagonal q)).ι :=
    MorphismProperty.arrow_mk_iso_iff _ hiso
  rw [hdiag]
  constructor
  · intro hd a h
    rw [← preimage_range_diagonal]
    exact isStableUnderBaseChange_presheaf_inverseImage_isImmersion.of_isPullback
      (Subfunctor.isPullback_preimage h (Subfunctor.range (pullback.diagonal q))) hd
  · intro hall
    refine presheaf_ι_of_forall_preimage _ fun a h => ?_
    rw [preimage_range_diagonal]
    exact hall h

end Diagonal

/-! ### The equalizers of the relative Picard functor -/

namespace PicardSituation

variable (s : PicardSituation B S hS)

/-- **The equalizer of two points of `Pic_{X/B}(T)`**: the subfunctor of `h_T` of the morphisms
`g : U ⟶ T` of the site along which the two points agree, `g^*x = g^*y`. A morphism `g` of the
site into the underlying scheme of the test scheme `T` is read as a morphism of test schemes
through the projection, which is a discrete fibration; this is the image of the equalizer sieve
of `x` and `y` under it. -/
def picardEqualizer (T : s.SchemesOver) (x y : s.picardFunctor.obj (Opposite.op T)) :
    Subfunctor (yoneda.obj T.left) where
  obj U := {g | (Sieve.functorPushforward
    (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)
    (Presheaf.equalizerSieve (F := s.picardFunctor) (X := Opposite.op T) x y)).arrows g}
  map {_ _} k g hg := by
    change (Sieve.functorPushforward (CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)
      (Presheaf.equalizerSieve (F := s.picardFunctor) (X := Opposite.op T) x y)).arrows
        (k.unop ≫ g)
    exact Sieve.downward_closed _ hg k.unop

/-- A morphism of test schemes `m : W ⟶ T` lies in the equalizer of `x` and `y` exactly when
`m^*x = m^*y`. -/
theorem mem_picardEqualizer_iff {T W : s.SchemesOver} (x y : s.picardFunctor.obj (Opposite.op T))
    (m : W ⟶ T) :
    m.left ∈ (s.picardEqualizer T x y).obj (Opposite.op W.left) ↔
      s.picardFunctor.map m.op x = s.picardFunctor.map m.op y :=
  CostructuredArrow.mem_functorPushforward_proj_iff _ _
    (Presheaf.equalizerSieve (F := s.picardFunctor) (X := Opposite.op T) x y) m

/-- **The equalizer of two points of `Pic_{X/B}(T)` is an fppf sheaf.** -/
theorem isSheaf_picardEqualizer (T : s.SchemesOver) (x y : s.picardFunctor.obj (Opposite.op T)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (s.picardEqualizer T x y).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS T.left))).2 ?_
  rintro ⟨U⟩ (g : U ⟶ T.left) hg
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  refine (s.mem_picardEqualizer_iff x y m).2 ?_
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 s.isSheaf_picardFunctor).isSeparated
  let R := Sieve.pullback m (Presheaf.equalizerSieve (F := s.picardFunctor)
    (X := Opposite.op T) x y)
  have hR : R ∈ s.fppfTopology _ := by
    rw [CostructuredArrow.mem_restrictedTopology_proj_iff]
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hg
    intro V k hk
    let n := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base
      (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom)) k
    exact (CostructuredArrow.mem_functorPushforward_proj_iff _ _ R n).2
      ((s.mem_picardEqualizer_iff x y (n ≫ m)).1 hk)
  refine (hsep R hR).ext fun V n hn => ?_
  change s.picardFunctor.map (n ≫ m).op x = s.picardFunctor.map (n ≫ m).op y at hn
  simpa only [op_comp, Functor.map_comp_apply] using hn

/-- **The inverse image of the equalizer of `x` and `y` along `g : U ⟶ T` is the equalizer of
`g^*x` and `g^*y`.** -/
theorem picardEqualizer_preimage (T : s.SchemesOver) (x y : s.picardFunctor.obj (Opposite.op T))
    {U : BigFppfOver B S hS} (g : U ⟶ T.left) :
    (s.picardEqualizer T x y).preimage (yoneda.map g) =
      s.picardEqualizer (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom))
        (s.picardFunctor.map (CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g).op
          x)
        (s.picardFunctor.map (CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g).op
          y) := by
  ext ⟨V⟩ k
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  let n := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base
    (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom)) k
  refine (s.mem_picardEqualizer_iff x y (n ≫ m)).trans (Iff.trans ?_
    (s.mem_picardEqualizer_iff _ _ n).symm)
  simp only [op_comp, Functor.map_comp_apply]
  exact Iff.rfl

/-- **Two classes of `Pic(X_T)` agree in `Pic_{X/B}` after pulling back along `g : U ⟶ T`
exactly when their pullbacks to `Pic(X_U)` agree fppf locally on `U`.** -/
theorem mem_picardEqualizer_picardClassMap_iff (T : s.SchemesOver) (v w : s.picardAt T)
    {U : BigFppfOver B S hS} (g : U ⟶ T.left) :
    g ∈ (s.picardEqualizer T (s.picardClassMap T v) (s.picardClassMap T w)).obj
        (Opposite.op U) ↔
      Presheaf.equalizerSieve (F := s.picardPresheaf)
          (X := Opposite.op (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom)))
          (s.picardMap (CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g) v)
          (s.picardMap (CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g) w) ∈
        s.fppfTopology _ := by
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  refine (s.mem_picardEqualizer_iff _ _ m).trans ?_
  rw [← s.picardClassMap_picardMap, ← s.picardClassMap_picardMap]
  refine ⟨fun h => s.isLocallyInjective_toPicardFunctor.equalizerSieve_mem
    (X := Opposite.op (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ T.hom)))
    (s.picardMap m v) (s.picardMap m w) h, fun h => ?_⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 s.isSheaf_picardFunctor).isSeparated
  refine (hsep _ h).ext fun V n hn => ?_
  change s.picardMap n (s.picardMap m v) = s.picardMap n (s.picardMap m w) at hn
  rw [← s.picardClassMap_picardMap, ← s.picardClassMap_picardMap, hn]

/-- **The equalizer of the images of `v, w ∈ Pic(X_T)` is the equalizer of the images of `v - w`
and `0`.** This is the step "set `L = V ⊗ W^{⊗ -1}`" of the proof of Stacks 0D2D. -/
theorem picardEqualizer_picardClassMap_sub (T : s.SchemesOver) (v w : s.picardAt T) :
    s.picardEqualizer T (s.picardClassMap T v) (s.picardClassMap T w) =
      s.picardEqualizer T (s.picardClassMap T (v - w)) (s.picardClassMap T 0) := by
  ext ⟨U⟩ g
  rw [mem_picardEqualizer_picardClassMap_iff, mem_picardEqualizer_picardClassMap_iff]
  have key : ∀ {W : s.SchemesOver} (k : W ⟶ T),
      s.picardMap k v = s.picardMap k w ↔ s.picardMap k (v - w) = s.picardMap k 0 := by
    intro W k
    simp only [picardMap_eq, ← picardPullbackHom_apply, map_sub, map_zero, sub_eq_zero]
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  refine Iff.of_eq (congrArg (fun R => R ∈ s.fppfTopology _) (Sieve.ext fun W n => ?_))
  change s.picardMap n (s.picardMap m v) = s.picardMap n (s.picardMap m w) ↔
    s.picardMap n (s.picardMap m (v - w)) = s.picardMap n (s.picardMap m (0 : s.picardAt T))
  rw [← s.picardMap_comp, ← s.picardMap_comp, ← s.picardMap_comp, ← s.picardMap_comp]
  exact key _

/-- **The reduction of Stacks 0D2D to points coming from invertible modules.** If, over every
test scheme `T`, the equalizer of the images in `Pic_{X/B}(T)` of any two classes of `Pic(X_T)`
is represented by immersions, then so is the equalizer of any two points of `Pic_{X/B}(T)`. -/
theorem isImmersion_picardEqualizer_of_picardClassMap
    (H : ∀ (T : s.SchemesOver) (v w : s.picardAt T),
      IsImmersion B S hS (s.picardEqualizer T (s.picardClassMap T v) (s.picardClassMap T w)).ι)
    (T : s.SchemesOver) (x y : s.picardFunctor.obj (Opposite.op T)) :
    IsImmersion B S hS (s.picardEqualizer T x y).ι := by
  have _ := (isStableUnderBaseChange_presheaf_inverseImage_isImmersion (B := B) (S := S)
    (hS := hS)).respectsIso
  let R : Sieve T := Presheaf.imageSieve s.toPicardFunctor x ⊓
    Presheaf.imageSieve s.toPicardFunctor y
  have hR : R ∈ s.fppfTopology T := s.fppfTopology.intersection_covering
    (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor x)
    (Presheaf.imageSieve_mem s.fppfTopology s.toPicardFunctor y)
  rw [CostructuredArrow.mem_restrictedTopology_proj_iff] at hR
  refine presheaf_of_coveringSieve (isEffectiveDescentAlongCoveringSieve_isImmersion B S hS)
    (s.isSheaf_picardEqualizer T x y) _ hR fun V g hg => ?_
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ :=
    (CostructuredArrow.mem_functorPushforward_proj_iff _ _ R m).1 hg
  have hpb := Subfunctor.isPullback_preimage (yoneda.map g) (s.picardEqualizer T x y)
  refine (MorphismProperty.cancel_left_of_respectsIso _ hpb.isoPullback.hom _).1 ?_
  rw [hpb.isoPullback_hom_snd, s.picardEqualizer_preimage]
  have h := H _ v w
  change IsImmersion B S hS (s.picardEqualizer _ (s.toPicardFunctor.app _ v)
    (s.toPicardFunctor.app _ w)).ι at h
  rwa [hv, hw] at h

/-! ### Models of the relative Picard functor -/

section Represents

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : F ⟶ s.base.1)
  (e : ∀ T : s.SchemesOver, s.picardFunctor.obj (Opposite.op T) ≃
    {x : F.obj (Opposite.op T.left) //
      q.app (Opposite.op T.left) x =
        yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom)})
  (he : ∀ (T U : s.SchemesOver) (g : T ⟶ U) (x : s.picardFunctor.obj (Opposite.op U)),
    (e T (s.picardFunctor.map g.op x)).val = F.map g.left.op (e U x).val)

include he in
/-- For a model `q : F ⟶ B` of the relative Picard functor, two points of `Pic_{X/B}(T)` agree
after pulling back along `g : U ⟶ T` exactly when the corresponding points of `F` do. -/
theorem map_val_eq_iff_mem_picardEqualizer (T : s.SchemesOver)
    (x y : s.picardFunctor.obj (Opposite.op T)) {U : BigFppfOver B S hS} (g : U ⟶ T.left) :
    F.map g.op (e T x).val = F.map g.op (e T y).val ↔
      g ∈ (s.picardEqualizer T x y).obj (Opposite.op U) := by
  let m := CostructuredArrow.liftHom (schemeSpaceFunctor B S hS) s.base T g
  refine Iff.trans ?_ (s.mem_picardEqualizer_iff x y m).symm
  change F.map m.left.op _ = F.map m.left.op _ ↔ _
  rw [← he, ← he]
  exact ⟨fun h' => (e _).injective (Subtype.ext h'), fun h' => by rw [h']⟩

include he in
/-- For a model `q : F ⟶ B` of the relative Picard functor, the equalizer of two points of `F`
over a test scheme `T` with the same image in `B` is the equalizer of the corresponding points
of `Pic_{X/B}(T)`. -/
theorem diagonalEqualizer_eq_picardEqualizer (T : s.SchemesOver)
    (h : yoneda.obj T.left ⟶ pullback q q) (x y : s.picardFunctor.obj (Opposite.op T))
    (hx : yonedaEquiv (h ≫ pullback.fst q q) = (e T x).val)
    (hy : yonedaEquiv (h ≫ pullback.snd q q) = (e T y).val) :
    diagonalEqualizer q h = s.picardEqualizer T x y := by
  ext ⟨U⟩ g
  change F.map g.op _ = F.map g.op _ ↔ _
  rw [hx, hy]
  exact s.map_val_eq_iff_mem_picardEqualizer F q e he T x y g

include he in
/-- **A model `q : F ⟶ B` of the relative Picard functor is locally separated exactly when the
equalizer of any two points of `Pic_{X/B}(T)`, over any test scheme `T`, is represented by
immersions.** This is the translation of Stacks 0D2D, that the diagonal of `Pic_{X/B} ⟶ B` is
representable by immersions, into a statement about `Pic_{X/B}` alone. -/
theorem isLocallySeparated_iff_of_represents :
    IsLocallySeparated B S hS q ↔
      ∀ (T : s.SchemesOver) (x y : s.picardFunctor.obj (Opposite.op T)),
        IsImmersion B S hS (s.picardEqualizer T x y).ι := by
  rw [IsLocallySeparated, isImmersion_diagonal_iff]
  constructor
  · intro hq T x y
    have hxy : q.app _ (e T x).val = q.app _ (e T y).val := (e T x).property.trans
      (e T y).property.symm
    let h : yoneda.obj T.left ⟶ pullback q q :=
      pullback.lift (yonedaEquiv.symm (e T x).val) (yonedaEquiv.symm (e T y).val) (by
        apply yonedaEquiv.injective
        simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
        exact hxy)
    rw [← s.diagonalEqualizer_eq_picardEqualizer F q e he T h x y
      (by rw [pullback.lift_fst, Equiv.apply_symm_apply])
      (by rw [pullback.lift_snd, Equiv.apply_symm_apply])]
    exact hq h
  · intro hP a h
    let x₀ : F.obj (Opposite.op a) := yonedaEquiv (h ≫ pullback.fst q q)
    let y₀ : F.obj (Opposite.op a) := yonedaEquiv (h ≫ pullback.snd q q)
    have hq : q.app _ x₀ = q.app _ y₀ := by
      simp only [x₀, y₀, ← yonedaEquiv_comp, Category.assoc, pullback.condition]
    let hb : (schemeSpaceFunctor B S hS).obj a ⟶ s.base :=
      ObjectProperty.homMk (yonedaEquiv.symm (q.app _ x₀))
    let T : s.SchemesOver := CostructuredArrow.mk hb
    have hT : yonedaEquiv (show yoneda.obj T.left ⟶ s.base.1 from T.hom.hom) = q.app _ x₀ :=
      yonedaEquiv.apply_symm_apply _
    let x := (e T).symm ⟨x₀, hT.symm⟩
    let y := (e T).symm ⟨y₀, hq.symm.trans hT.symm⟩
    rw [s.diagonalEqualizer_eq_picardEqualizer F q e he T h x y (by simp [x, x₀])
      (by simp [y, y₀])]
    exact hP T x y

end Represents

end PicardSituation

end AlgebraicGeometry.Space

end
