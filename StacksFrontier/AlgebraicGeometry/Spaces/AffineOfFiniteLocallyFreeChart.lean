module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatChartCoequalizer

/-!
# Affineness of an algebraic space with an affine finite locally free chart

An algebraic space over a scheme `S` which receives a surjective finite locally free morphism
from an object of the big fppf site with affine underlying scheme is affine.

The relation `R = U ×_F U` of the chart is affine over the affine `U`, hence affine, and its
two projections are finite locally free because the chart is; the relation is an equivalence
relation, so Stacks 03BM makes the spectrum of its ring of invariant functions a quotient of
`U` by a surjective finite locally free morphism with the same kernel pair. A chart which is
surjective, flat and locally of finite presentation exhibits its algebraic space as the
coequalizer of its kernel pair, and the two coequalizers of the one pair agree, so that
spectrum represents `F`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback_of_isFiniteLocallyFree`: an
  algebraic space with a surjective finite locally free chart is represented by any object of
  the site receiving from the chart a faithfully flat morphism of finite presentation with the
  same kernel pair.
* `AlgebraicGeometry.Space.isAffineSpace_of_isFiniteLocallyFree_affineChart`: an algebraic
  space with a surjective finite locally free chart whose source has affine underlying scheme
  is affine.

## Implementation notes

The representability step is the argument of
`AlgebraicGeometry.Space.exists_iso_yoneda_of_isPullback` with the étale hypothesis on the
chart replaced by finite local freeness: the only use of étaleness there is to make the chart a
surjection of fppf sheaves, and
`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveFiniteLocallyFree` supplies the same
conclusion for a surjective finite locally free chart. Representability is read off the
universal property of a locally surjective morphism of sheaves whose kernel pair is realised
pointwise (`CategoryTheory.Sheaf.nonempty_isColimitCoforkOfKernelPair`), so no quotient sheaf
is formed.

Finite local freeness of the chart is read in the representable sense, condition (1) of
Stacks 03ZW, and surjectivity likewise as the relative property of Stacks 02YN; for a morphism
from a representable presheaf to an algebraic space the latter is surjectivity on points by
Stacks 03H5.

The equivalence relation is transported along `CategoryTheory.Over.post` of the inclusion of
the cutoff category, which is the shape Stacks 03BM is stated in.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Two morphisms `x y : V ⟶ U` of the big fppf site whose images under `Over.post` agree after
composing with `π` factor through any kernel pair `t, s : R ⟶ U` of `π`. -/
theorem exists_comp_eq_of_isPullback_post_map
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U R U' V : BigFppfOver B S hS} {t s : R ⟶ U}
    {π : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj U'}
    (hπ : IsPullback ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) π π)
    (x y : V ⟶ U)
    (hxy : (Over.post B.inclusion).map x ≫ π = (Over.post B.inclusion).map y ≫ π) :
    ∃ r : V ⟶ R, r ≫ t = x ∧ r ≫ s = y := by
  refine ⟨(Over.post B.inclusion).preimage (hπ.lift _ _ hxy), ?_, ?_⟩ <;>
    refine (Over.post B.inclusion).map_injective ?_ <;>
    rw [Functor.map_comp, Functor.map_preimage]
  exacts [hπ.lift_fst _ _ hxy, hπ.lift_snd _ _ hxy]

/-- An algebraic space over `S` with a surjective finite locally free chart `f` whose kernel
pair is represented by `t, s : R ⟶ U` is represented by any object `U'` of the site receiving
from `U` a faithfully flat morphism of finite presentation whose kernel pair is again `t, s`. -/
theorem exists_iso_yoneda_of_isPullback_of_isFiniteLocallyFree
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U R U' : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (π : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj U')
    (hflat : Flat π.left) (hlfp : LocallyOfFinitePresentation π.left)
    (hsurjπ : Surjective π.left)
    (hπ : IsPullback ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) π π) :
    ∃ (m : U ⟶ U') (e : F ≅ yoneda.obj U'),
      (Over.post B.inclusion).map m = π ∧ f ≫ e.hom = yoneda.map m := by
  classical
  obtain ⟨hRsh, hUsh, hcolimF⟩ :=
    isCoequalizer_of_surjectiveFiniteLocallyFree B S hS f t s hR hF hsurj hflf
  set J := BigFppfOver.topology B S hS
  set RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  set UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  set FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  set MF : Sheaf J (Type u) :=
    ⟨Stacks.Groupoids.points (Over.post B.inclusion) ((Over.post B.inclusion).obj U'),
      Stacks.Groupoids.isSheaf_points B S hS ((Over.post B.inclusion).obj U')⟩
  set tf : RF ⟶ UF := ⟨yoneda.map t⟩
  set sf : RF ⟶ UF := ⟨yoneda.map s⟩
  set ff : UF ⟶ FF := ⟨f⟩
  set p : yoneda.obj U ⟶
      Stacks.Groupoids.points (Over.post B.inclusion) ((Over.post B.inclusion).obj U') :=
    (pointsYonedaIso (Over.post B.inclusion) U).inv ≫
      (Over.post B.inclusion).op.whiskerLeft (yoneda.map π) with hp
  have hpapp : ∀ (V : BigFppfOver B S hS) (g : V ⟶ U),
      p.app (op V) g = (Over.post B.inclusion).map g ≫ π := by
    intro V g
    simp [hp, pointsYonedaIso, Stacks.Groupoids.points,
      Functor.FullyFaithful.homEquiv, Functor.FullyFaithful.ofFullyFaithful]
  set pf : UF ⟶ MF := ⟨p⟩
  have hwp : tf ≫ pf = sf ≫ pf := by
    apply Sheaf.hom_ext
    ext V g
    show p.app V ((yoneda.map t).app V g) = p.app V ((yoneda.map s).app V g)
    obtain ⟨V⟩ := V
    rw [show ((yoneda.map t).app (op V) g) = g ≫ t from rfl,
      show ((yoneda.map s).app (op V) g) = g ≫ s from rfl]
    simp only [hpapp, Functor.map_comp, Category.assoc, hπ.w]
  have hker : ∀ ⦃V : BigFppfOver B S hS⦄ (x y : UF.obj.obj (op V)),
      pf.hom.app (op V) x = pf.hom.app (op V) y →
      ∃ r : RF.obj.obj (op V), tf.hom.app (op V) r = x ∧ sf.hom.app (op V) r = y := by
    intro V x y hxy
    exact exists_comp_eq_of_isPullback_post_map B S hS hπ x y
      ((hpapp V x).symm.trans (hxy.trans (hpapp V y)))
  have h1 : Presheaf.IsLocallySurjective J
      ((Over.post B.inclusion).op.whiskerLeft (yoneda.map π)) :=
    isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS π
  have hlocsurj : Presheaf.IsLocallySurjective J pf.hom := by
    show Presheaf.IsLocallySurjective J p
    rw [hp]
    infer_instance
  obtain ⟨hcolimM⟩ := Sheaf.nonempty_isColimitCoforkOfKernelPair tf sf pf hwp hker hlocsurj
  obtain ⟨hcolimF⟩ := hcolimF
  have hpres : f ≫ ((sheafToPresheaf J (Type u)).mapIso
      (IsColimit.coconePointUniqueUpToIso hcolimF hcolimM)).hom = p :=
    congrArg (fun h => h.hom)
      (IsColimit.comp_coconePointUniqueUpToIso_hom hcolimF hcolimM WalkingParallelPair.one)
  refine ⟨(Over.post B.inclusion).preimage π,
    (sheafToPresheaf J (Type u)).mapIso
      (IsColimit.coconePointUniqueUpToIso hcolimF hcolimM) ≪≫
        pointsYonedaIso (Over.post B.inclusion) U', Functor.map_preimage _ _, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hpres, hp, Category.assoc, pointsYonedaIso_inv_comp]

/-- **An algebraic space over `S` receiving a surjective finite locally free morphism from an
object of the big fppf site with affine underlying scheme is affine.**

The relation of the chart is affine, its projections are finite locally free, and it is an
equivalence relation, so Stacks 03BM produces an affine scheme of the site receiving a
surjective finite locally free morphism from the chart with the same kernel pair; the chart and
that morphism then have the same coequalizer, which is the space. -/
theorem isAffineSpace_of_isFiniteLocallyFree_affineChart
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (q : yoneda.obj U ⟶ F)
    (hqsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hqflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q) :
    IsAffineSpace B S hS F := by
  classical
  set R : BigFppfOver B S hS := hqflf.1.pullback q
  set s : R ⟶ U := hqflf.1.snd q
  set t : R ⟶ U := yoneda.preimage (hqflf.1.fst q)
  have hyt : yoneda.map t = hqflf.1.fst q := Functor.map_preimage yoneda _
  have hR : IsPullback (yoneda.map t) (yoneda.map s) q q := by
    rw [hyt]
    exact hqflf.1.isPullback q
  have hflfs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) :=
    hqflf.property_snd q
  have hflft : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t) :=
    hqflf.property q (yoneda.map s) t hR.flip
  have hRaff : IsAffine ((BigFppfOver.toScheme B S hS).obj R) :=
    isAffine_of_isFinite ((BigFppfOver.toScheme B S hS).map s)
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
        ((BigFppfOver.toScheme B S hS).map s)).mp hflfs).1 hU
  have _ : IsAffine ((Over.post B.inclusion).obj U).left := hU
  have _ : IsAffine ((Over.post B.inclusion).obj R).left := hRaff
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map s).left := hflfs
  have _ : Stacks.Morphisms.IsFiniteLocallyFree ((Over.post B.inclusion).map t).left := hflft
  have _ : IsEquivalenceRelation ((Over.post B.inclusion).map t)
      ((Over.post B.inclusion).map s) := isEquivalenceRelation_of_isPullback B S hS q t s hR
  obtain ⟨A, _, g, π, hsize, hflf, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S
      ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s)
  have hAcontains : B.Contains (Spec (CommRingCat.of A)) := lt_of_le_of_lt hsize U.left.2
  have _ := hflf
  obtain ⟨m, e, -, -⟩ :=
    exists_iso_yoneda_of_isPullback_of_isFiniteLocallyFree B S hS hF q t s hR hqsurj hqflf
      (U' := Over.mk (⟨g⟩ : B.obj hAcontains ⟶ B.obj hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hpb
  exact ⟨Over.mk (⟨g⟩ : B.obj hAcontains ⟶ B.obj hS), inferInstanceAs
    (IsAffine (Spec (CommRingCat.of A))), ⟨e⟩⟩

end AlgebraicGeometry.Space

end
