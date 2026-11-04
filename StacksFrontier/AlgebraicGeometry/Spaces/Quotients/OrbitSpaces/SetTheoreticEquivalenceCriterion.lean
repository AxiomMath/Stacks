module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Radicial
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.SetTheoreticEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.PreEquivalenceGeometricCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Criteria for a set-theoretic equivalence relation

Let `j : R ⟶ U ×_B U` be a pre-relation of algebraic spaces over an algebraic space `B`. By
**Stacks 0490** it is a *set-theoretic equivalence relation* when it is universally injective
and the relation it induces on the points of `U` over every algebraically closed field is an
equivalence relation, arrows being allowed to appear after a field extension. Two further
descriptions of that condition are available. Pointwise, it says that `j` is universally
injective and that its image on topological points contains the images of the three natural
maps to `U ×_B U` attached to a relation; this is **Stacks 0491** with universal injectivity
added on both sides. Over fields, it says that for every algebraically closed field `k` over
`B` of sufficiently large cardinality the map `R(k) ⟶ U(k) × U(k)` is injective with image an
equivalence relation. When `j` is decent, locally separated or quasi-separated the cardinality
restriction can be dropped: the criterion over fields then holds for *every* algebraically
closed field over `B`.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation.HasGeometricEquivalence` is the condition over a
  single algebraically closed field: injectivity of the map on arrows over that field together
  with the equivalence-relation property of the relation its arrows cut out.

## Main results

* `AlgebraicGeometry.Space.isSetTheoreticEquivalenceRelation_iff_containsRelationImages`:
  **Stacks 049X**, conditions (1) and (2), the pointwise criterion.
* `AlgebraicGeometry.Space.isSetTheoreticEquivalenceRelation_iff_exists_hasGeometricEquivalence`:
  **Stacks 049X**, conditions (1) and (3), the criterion over all sufficiently large
  algebraically closed fields.
* `AlgebraicGeometry.Space.isSetTheoreticEquivalenceRelation_iff_hasGeometricEquivalence`:
  **Stacks 049X**, condition (4), the criterion over all algebraically closed fields, for a
  pre-relation which is decent, locally separated or quasi-separated.

## Implementation notes

The condition of **Stacks 0490** is stated for a pre-relation of presheaves, so throughout the
pre-relation of algebraic spaces is read in the slice of presheaves over the underlying
presheaf of the base by `AlgebraicGeometry.Space.presheafPreRelation`, exactly as in
**Stacks 0491**; "the morphism `j`" is its underlying natural transformation
`(presheafPreRelation j).left`, which is the morphism whose universal injectivity the
condition of **Stacks 0490** asks for, and whose components at the objects of the site are the
maps `R(k) ⟶ U(k) × U(k)` of the criterion over fields. The three image containments are
`AlgebraicGeometry.Space.PreRelation.ContainsRelationImages`, which is phrased through the
endpoint maps of the original pre-relation, as **Stacks 0491** states it. The two readings of
`j` differ only by the comparison morphism from the image of `U ×_B U` to the product of the
images of `U`, which is an isomorphism because by **Stacks 02X2** the presheaf fibre product of
two algebraic spaces is their product among algebraic spaces as well; the endpoint maps, which
are what the image containments use, are literally the same on both sides by
`AlgebraicGeometry.Space.presheafPreRelation_source_left` and
`AlgebraicGeometry.Space.presheafPreRelation_target_left`.

"Sufficiently large cardinality" is one cardinal strictly below the size cutoff of the site,
uniformly in the geometric point of the base, as in **Stacks 0491**: the bound has to be
strictly below the cutoff, since every field whose spectrum is an object of the site has
cardinality below the cutoff and a bound at the cutoff would be met by no field at all. The
bound produced here is the maximum of the one **Stacks 0491** produces for the three image
containments and the invariant `sup {ℵ₀, |κ(v)|}` of a scheme atlas of `R`, which is the
hypothesis under which `AlgebraicGeometry.Space.exists_lift_of_large_field` descends a point
of the source to a section over the field itself. That descent, applied to the relative
diagonal of `j`, is what turns universal injectivity into injectivity on the arrows over the
field; in the other direction injectivity over all large fields makes the relative diagonal
surjective on points, which is universal injectivity by **Stacks 040X**, and the passage from
the sections over large fields to the points is **Stacks 0491** applied to the trivial
pre-relation attached to the morphism.

The separation hypothesis of the last criterion enters through **Stacks 0484**: a universally
injective morphism which is decent, locally separated or quasi-separated is radicial, and the
reduction of a fibre of a radicial morphism over an algebraically closed field is the spectrum
of a purely inseparable extension of that field, hence of the field itself. Such a fibre
therefore has exactly one section over the field as soon as it has a point at all, which gives
both the injectivity on arrows and the descent of an arrow available only after a field
extension.

Products in the slice of presheaves over the base are fibre products over it, by
`CategoryTheory.Over.isPullback_of_binaryFan_isLimit`; this is how the target of `j` is seen to
be an algebraic space and how two morphisms into it are compared.

## References

* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 0484](https://stacks.math.columbia.edu/tag/0484)
* [Stacks Project, Tag 0488](https://stacks.math.columbia.edu/tag/0488)
* [Stacks Project, Tag 0490](https://stacks.math.columbia.edu/tag/0490)
* [Stacks Project, Tag 0491](https://stacks.math.columbia.edu/tag/0491)
* [Stacks Project, Tag 049X](https://stacks.math.columbia.edu/tag/049X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-! ### Products in the slice of presheaves over the base -/

/-- A binary product in the slice of presheaves over the underlying presheaf of an algebraic
space is the presheaf fibre product of the two structure morphisms. -/
private theorem isPullback_prod_left (A C : Over B.obj) :
    IsPullback (prod.fst : A ⨯ C ⟶ A).left (prod.snd : A ⨯ C ⟶ C).left A.hom C.hom := by
  have h := Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst : A ⨯ C ⟶ A) (prod.snd : A ⨯ C ⟶ C)) (prodIsProd A C)
  simpa only [BinaryFan.mk_fst, BinaryFan.mk_snd] using h

/-- Two morphisms into a binary product in the slice of presheaves over the base agree as soon
as their two components do. -/
private theorem prod_left_hom_ext {A C : Over B.obj}
    {V : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {a c : V ⟶ (A ⨯ C : Over B.obj).left}
    (hfst : a ≫ (prod.fst : A ⨯ C ⟶ A).left = c ≫ (prod.fst : A ⨯ C ⟶ A).left)
    (hsnd : a ≫ (prod.snd : A ⨯ C ⟶ C).left = c ≫ (prod.snd : A ⨯ C ⟶ C).left) : a = c :=
  (isPullback_prod_left A C).hom_ext hfst hsnd

/-- A binary product of algebraic spaces in the slice of presheaves over the base is an
algebraic space: it is their fibre product over the base. -/
private theorem isAlgebraicSpace_prod_left {A C : Over B.obj}
    (hA : IsAlgebraicSpace site S hS A.left) (hC : IsAlgebraicSpace site S hS C.left) :
    IsAlgebraicSpace site S hS (A ⨯ C : Over B.obj).left :=
  isAlgebraicSpace_of_iso site S hS (isPullback_prod_left A C).isoPullback.symm
    (isAlgebraicSpace_pullback site S hS _ _ hA hC B.property)

/-! ### Sections of a fibre product of presheaves -/

/-- A section of a fibre product of presheaves on the big fppf site of `S` over an object of the
site is determined by its two components. -/
private theorem pullback_app_ext {X Y Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z)
    (g : Y ⟶ Z) (T : BigFppfOver site S hS)
    {x y : (pullback f g).obj (Opposite.op T)}
    (hfst : (pullback.fst f g).app (Opposite.op T) x =
      (pullback.fst f g).app (Opposite.op T) y)
    (hsnd : (pullback.snd f g).app (Opposite.op T) x =
      (pullback.snd f g).app (Opposite.op T) y) : x = y := by
  refine yonedaEquiv.symm.injective (pullback.hom_ext ?_ ?_)
  · simpa only [yonedaEquiv_symm_naturality_right] using congrArg yonedaEquiv.symm hfst
  · simpa only [yonedaEquiv_symm_naturality_right] using congrArg yonedaEquiv.symm hsnd

/-! ### Sections of a radicial morphism over an algebraically closed field -/

/-- A purely inseparable extension of an algebraically closed field is an isomorphism. -/
private theorem isIso_ofHom_algebraMap (k L : Type u) [Field k] [IsAlgClosed k] [Field L]
    [Algebra k L] [IsPurelyInseparable k L] :
    IsIso (CommRingCat.ofHom (algebraMap k L)) := by
  have hbij : Function.Bijective (algebraMap k L) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃+* L := RingEquiv.ofBijective (algebraMap k L) hbij
  show IsIso (CommRingCat.ofHom e.toRingHom)
  exact e.toCommRingCatIso.isIso_hom

/-- **A fibre of a radicial morphism over an algebraically closed field in the site has exactly
one section over that field as soon as it has a point.**

The reduction of the fibre is the spectrum of a purely inseparable extension of the field, which
is the field itself because the field is algebraically closed; so the first projection
identifies the reduction with the represented presheaf of the test object. A section of the
fibre factors through the reduction, the test object being reduced, and there it is the inverse
of that identification. -/
private theorem existsUnique_lift_of_isRadicial
    {X Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace site S hS X) (hY : IsAlgebraicSpace site S hS Y)
    (f : X ⟶ Y) (hf : IsRadicial site S hS hX hY f)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (g : yoneda.obj (fieldObject (hS := hS) k hk b) ⟶ Y)
    (hne : Nonempty (points site S hS (pullback g f))) :
    ∃! a : yoneda.obj (fieldObject (hS := hS) k hk b) ⟶ X, a ≫ f = g := by
  classical
  let T : BigFppfOver site S hS := fieldObject (hS := hS) k hk b
  let P := pullback g f
  let hP : IsAlgebraicSpace site S hS P :=
    isAlgebraicSpace_pullback site S hS g f (isAlgebraicSpace_yoneda site S hS T) hX hY
  let _ : TopologicalSpace (points site S hS P) := pointTopology site S hS P
  let Z := reducedClosedSubspace site S hS P hP Set.univ isClosed_univ
  have eT : (BigFppfOver.toScheme site S hS).obj T ≅ Spec (.of k) := Iso.refl _
  have hzne : Nonempty (points site S hS Z.toFunctor) := by
    obtain ⟨p⟩ := hne
    have hp : p ∈ Set.range (pointsMap site S hS Z.toFunctor Z.ι) := by
      rw [range_pointsMap_ι_reducedClosedSubspace site S hS P hP Set.univ isClosed_univ]
      trivial
    exact ⟨hp.choose⟩
  have hredField : HasEtaleLocalProperty site S hS (yoneda.obj T)
      (fun V : Scheme.{u} => IsReduced V) :=
    (exists_atlas_iff_of_representable site S hS (yoneda.obj T)
      (fun V : Scheme.{u} => IsReduced V) T (Iso.refl _)).2
        (by change IsReduced (Spec (.of k)); infer_instance)
  have liftZ : ∀ p : yoneda.obj T ⟶ P, ∃ r : yoneda.obj T ⟶ Z.toFunctor, r ≫ Z.ι = p :=
    fun p ↦ (exists_lift_closedSubspace_iff_pointsMap_range_subset site S hS hP
      (isAlgebraicSpace_yoneda site S hS T) Z
      (isClosedSubspace_reducedClosedSubspace site S hS P hP Set.univ isClosed_univ)
      hredField p).2 fun z _ ↦ by
        rw [range_pointsMap_ι_reducedClosedSubspace site S hS P hP Set.univ isClosed_univ]
        exact Set.mem_univ _
  rcases hf k T eT g with hempty | ⟨L, hL, hAlg, hPI, M, m, eU, e, hproj, hm⟩
  · exact (hempty.false hzne.some).elim
  · let _ : Field L := hL
    let _ : Algebra k L := hAlg
    have _ : IsPurelyInseparable k L := hPI
    have _ : IsIso (CommRingCat.ofHom (algebraMap k L)) := isIso_ofHom_algebraMap k L
    have _ : IsIso ((BigFppfOver.toScheme site S hS).map m) := by
      rw [hm]; infer_instance
    have _ : IsIso m := isIso_of_reflects_iso m (BigFppfOver.toScheme site S hS)
    have _ : IsIso (e.inv ≫ Z.ι ≫ pullback.fst g f) := by
      rw [hproj]; infer_instance
    have hw : IsIso (Z.ι ≫ pullback.fst g f) := IsIso.of_isIso_comp_left e.inv _
    refine ⟨inv (Z.ι ≫ pullback.fst g f) ≫ Z.ι ≫ pullback.snd g f, ?_, ?_⟩
    · beta_reduce
      rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc Z.ι,
        IsIso.inv_hom_id_assoc]
    · intro a ha
      have hcond : 𝟙 (yoneda.obj T) ≫ g = a ≫ f := by simpa using ha.symm
      obtain ⟨r, hr⟩ := liftZ (pullback.lift (𝟙 _) a hcond)
      have hrw : r ≫ Z.ι ≫ pullback.fst g f = 𝟙 (yoneda.obj T) := by
        rw [← Category.assoc, hr, pullback.lift_fst]
      rw [← IsIso.eq_inv_of_inv_hom_id hrw, ← Category.assoc, hr, pullback.lift_snd]

/-- **A radicial morphism is injective on the sections over an algebraically closed field in the
site.** Two such sections with the same image are two sections of one fibre, and a fibre of a
radicial morphism over an algebraically closed field has at most one section. -/
private theorem injective_app_of_isRadicial
    {X Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace site S hS X) (hY : IsAlgebraicSpace site S hS Y)
    (f : X ⟶ Y) (hf : IsRadicial site S hS hX hY f)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S) :
    Function.Injective (f.app (Opposite.op (fieldObject (hS := hS) k hk b))) := by
  intro x y hxy
  let T : BigFppfOver site S hS := fieldObject (hS := hS) k hk b
  let g : yoneda.obj T ⟶ Y := yonedaEquiv.symm (f.app (Opposite.op T) x)
  have hx : yonedaEquiv.symm x ≫ f = g := yonedaEquiv_symm_naturality_right T f x
  have hy : yonedaEquiv.symm y ≫ f = g := by
    rw [yonedaEquiv_symm_naturality_right]
    exact congrArg yonedaEquiv.symm hxy.symm
  have hcond : 𝟙 (yoneda.obj T) ≫ g = yonedaEquiv.symm x ≫ f := by simpa using hx.symm
  have hne : Nonempty (points site S hS (pullback g f)) :=
    ⟨FieldValuedPoint.class site S hS _
      { carrier := k
        contained := hk
        toBase := b
        value := yonedaEquiv (pullback.lift (𝟙 _) (yonedaEquiv.symm x) hcond) }⟩
  exact yonedaEquiv.symm.injective
    ((existsUnique_lift_of_isRadicial hX hY f hf k hk b g hne).unique hx hy)

/-! ### Injectivity on arrows over a large algebraically closed field -/

/-- The first projection of the pullback of a morphism with itself sends the image of a section
under the relative diagonal back to that section. -/
private theorem app_pullback_fst_diagonal {X Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (T : BigFppfOver site S hS) (r : X.obj (Opposite.op T)) :
    (pullback.fst f f).app (Opposite.op T) ((pullback.diagonal f).app (Opposite.op T) r) = r :=
  congrArg (fun α : X ⟶ X ↦ α.app (Opposite.op T) r) (pullback.diagonal_fst f)

/-- The second projection of the pullback of a morphism with itself sends the image of a section
under the relative diagonal back to that section. -/
private theorem app_pullback_snd_diagonal {X Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (T : BigFppfOver site S hS) (r : X.obj (Opposite.op T)) :
    (pullback.snd f f).app (Opposite.op T) ((pullback.diagonal f).app (Opposite.op T) r) = r :=
  congrArg (fun α : X ⟶ X ↦ α.app (Opposite.op T) r) (pullback.diagonal_snd f)

/-- **A universally injective morphism is injective on the sections over a sufficiently large
algebraically closed field in the site.**

The two sections with the same image assemble into a section of the fibre product of the
morphism with itself. Universal injectivity makes the relative diagonal surjective on points by
**Stacks 040X**, so a point of the source is carried to the class of that section; over a field
larger than every residue field of a scheme atlas of the source that point is represented by a
section over the field itself, by **Stacks 0488**, whose image under the diagonal is the given
section. Its two components are the two sections, and they are equal. -/
private theorem injective_app_of_universallyInjective_of_large
    {X Y : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace site S hS X) (hY : IsAlgebraicSpace site S hS Y)
    (f : X ⟶ Y) (hf : UniversallyInjective site S hS f)
    (V : BigFppfOver site S hS) (pV : yoneda.obj V ⟶ X)
    (hpVsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS))) pV)
    (hpVetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS))) pV)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (hlarge : Cardinal.aleph0 ⊔
      (⨆ v : (BigFppfOver.toScheme site S hS).obj V,
        Cardinal.mk (((BigFppfOver.toScheme site S hS).obj V).residueField v)) <
          Cardinal.mk k) :
    Function.Injective (f.app (Opposite.op (fieldObject (hS := hS) k hk b))) := by
  intro x y hxy
  let T : BigFppfOver site S hS := fieldObject (hS := hS) k hk b
  have hP : IsAlgebraicSpace site S hS (pullback f f) :=
    isAlgebraicSpace_pullback site S hS f f hX hX hY
  have hcomp : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm y ≫ f := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hxy]
  obtain ⟨z, hzfst, hzsnd⟩ : ∃ z : (pullback f f).obj (Opposite.op T),
      (pullback.fst f f).app (Opposite.op T) z = x ∧
        (pullback.snd f f).app (Opposite.op T) z = y := by
    refine ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) hcomp), ?_, ?_⟩ <;>
      simp only [← yonedaEquiv_comp, pullback.lift_fst, pullback.lift_snd, Equiv.apply_symm_apply]
  obtain ⟨ξ, hξ⟩ := isSurjective_diagonal_of_universallyInjective site S hS hX f hf
    (FieldValuedPoint.class site S hS (pullback f f)
      { carrier := k, contained := hk, toBase := b, value := z })
  obtain ⟨r, hr, -⟩ := exists_lift_of_large_field site S hS hX hP (pullback.diagonal f)
    V pV hpVsurj hpVetale k hk b hlarge ξ z hξ
  rw [← hzfst, ← hzsnd, ← hr, app_pullback_fst_diagonal, app_pullback_snd_diagonal]

/-! ### Surjectivity on points from the sections over large algebraically closed fields -/

/-- **A morphism of algebraic spaces over `B` which is surjective on the sections over every
sufficiently large algebraically closed field in the site is surjective on points.**

The morphism `f : X ⟶ Y` is the structure morphism of an object of the slice over `Y`, and
together with itself it is a pre-relation on the terminal object of that slice. A point of `Y`
lies in a fibre of that terminal object consisting of a single section, so the hypothesis says
exactly that the relation cut out on such a fibre by the arrows over the field is total, hence
an equivalence relation; by **Stacks 0491** the image of the pre-relation on points therefore
contains the image of the diagonal, which is all of the points of `Y`. -/
private theorem isSurjective_of_surjective_app_of_large {X Y : AlgebraicSpaces site S hS}
    (f : X ⟶ Y) (κ : Cardinal.{u}) (hκ : κ < site.cutoff)
    (hf : ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
      (b : Spec (.of k) ⟶ S), κ < Cardinal.mk k →
      Function.Surjective (f.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)))) :
    IsSurjective site S hS f.hom := by
  let V : Over Y := Over.mk (𝟙 Y)
  let W : Over Y := Over.mk f
  let a : W ⟶ V := Over.homMk f (by simp [V, W])
  let q : PreRelation W V := prod.lift a a
  have hπ : ∀ {Z : Over Y} (m : Z ⟶ V ⨯ V) (π : V ⨯ V ⟶ V) (n : Z ⟶ V), m ≫ π = n →
      m.left.hom ≫ π.left.hom = n.left.hom := fun m π n h ↦ by rw [← h]; rfl
  have h1 : q.left.hom ≫ (prod.snd : V ⨯ V ⟶ V).left.hom = f.hom := hπ q _ a (prod.lift_snd a a)
  have hsrc : (presheafPreRelation q).source.left = f.hom :=
    (presheafPreRelation_source_left q).trans h1
  have htgt : (presheafPreRelation q).target.left = f.hom :=
    (presheafPreRelation_target_left q).trans (hπ q _ a (prod.lift_fst a a))
  have hq : q.ContainsRelationImages := by
    refine (containsRelationImages_iff_exists_geometricRel_equivalence q).mpr ⟨κ, hκ, ?_⟩
    intro k _ _ hk b β hmk
    have hrel : ∀ x y, (presheafPreRelation q).GeometricRel k hk b β x y := by
      intro x y
      obtain ⟨r, hr⟩ := hf k hk b hmk β
      exact ⟨r, by rw [hsrc]; exact hr.trans x.property.symm,
        by rw [htgt]; exact hr.trans y.property.symm⟩
    exact ⟨fun x ↦ hrel x x, fun _ ↦ hrel _ _, fun _ _ ↦ hrel _ _⟩
  intro y
  obtain ⟨x, hx⟩ := hq.1 ⟨y, rfl⟩
  refine ⟨x, ?_⟩
  have he := congrArg
    (pointsMap site S hS (V ⨯ V : Over Y).left.obj (prod.snd : V ⨯ V ⟶ V).left.hom) hx
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply] at he
  have h2 : (diag V).left.hom ≫ (prod.snd : V ⨯ V ⟶ V).left.hom = 𝟙 V.left.obj :=
    hπ (diag V) _ (𝟙 V) (by simp)
  rwa [h1, h2, pointsMap_id, id_eq] at he

/-! ### The criteria -/

variable {R U : Over B}

/-- The criterion over a single algebraically closed field `k` over the base: the map
`R(k) ⟶ U(k) × U(k)` on the arrows over `k` is injective, and the relation the arrows present
over `k` cut out on one fibre of `U(k)` is an equivalence relation. -/
noncomputable abbrev PreRelation.HasGeometricEquivalence (j : PreRelation R U)
    (k : Type u) [Field k] (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))) : Prop :=
  Function.Injective ((presheafPreRelation j).left.app
      (Opposite.op (fieldObject (hS := hS) k hk b))) ∧
    Equivalence ((presheafPreRelation j).GeometricRel k hk b β)

/-- **Stacks 049X, conditions (1) and (2).** A pre-relation of algebraic spaces is a
set-theoretic equivalence relation exactly when it is universally injective and its image on
topological points contains the images of the diagonal of `U`, of its flip, and of the endpoint
map on composable pairs of its arrows.

Universal injectivity is one of the two conditions on either side, and the other two are
equivalent by **Stacks 0491**. -/
@[stacks 049X "conditions (1) and (2)"]
theorem isSetTheoreticEquivalenceRelation_iff_containsRelationImages (j : PreRelation R U) :
    IsSetTheoreticEquivalenceRelation (presheafPreRelation j) ↔
      UniversallyInjective site S hS (presheafPreRelation j).left ∧
        j.ContainsRelationImages :=
  and_congr_right' (isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages j)

/-- **Stacks 049X, conditions (1) and (3).** A pre-relation of algebraic spaces is a
set-theoretic equivalence relation exactly when, over every algebraically closed field in the
site above one cardinal strictly below the size cutoff of the site, its map on arrows is
injective and the relation its arrows cut out is an equivalence relation.

The equivalence-relation half is **Stacks 0491**. Universal injectivity gives the injectivity
over every sufficiently large field through the descent of a point of `R` along the relative
diagonal of `j`, and conversely injectivity over all sufficiently large fields makes that
diagonal surjective on points, which is universal injectivity by **Stacks 040X**. -/
@[stacks 049X "conditions (1) and (3)"]
theorem isSetTheoreticEquivalenceRelation_iff_exists_hasGeometricEquivalence
    (j : PreRelation R U) :
    IsSetTheoreticEquivalenceRelation (presheafPreRelation j) ↔
      ∃ κ : Cardinal.{u}, κ < site.cutoff ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
        (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))),
        κ < Cardinal.mk k → j.HasGeometricEquivalence k hk b β := by
  have hTgt : IsAlgebraicSpace site S hS
      ((overForgetSpace B).obj U ⨯ (overForgetSpace B).obj U : Over B.obj).left :=
    isAlgebraicSpace_prod_left U.left.property U.left.property
  constructor
  · rintro ⟨hinj, hpre⟩
    obtain ⟨κ, hκ, hrel⟩ := (containsRelationImages_iff_exists_geometricRel_equivalence j).mp
      ((isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages j).mp hpre)
    obtain ⟨V, pV, hpVsurj, hpVetale⟩ := R.left.property.exists_atlas
    refine ⟨κ ⊔ (Cardinal.aleph0 ⊔ ⨆ v : (BigFppfOver.toScheme site S hS).obj V,
        Cardinal.mk (((BigFppfOver.toScheme site S hS).obj V).residueField v)),
      max_lt hκ ((aleph0_sup_iSup_residueField_le_size
        ((BigFppfOver.toScheme site S hS).obj V)).trans_lt V.left.property), ?_⟩
    intro k _ _ hk b β hmk
    exact ⟨injective_app_of_universallyInjective_of_large R.left.property hTgt
        (presheafPreRelation j).left hinj V pV hpVsurj hpVetale k hk b
        (lt_of_le_of_lt le_sup_right hmk),
      hrel k hk b β (lt_of_le_of_lt le_sup_left hmk)⟩
  · rintro ⟨κ, hκ, hgeom⟩
    refine ⟨?_, (isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages j).mpr
      ((containsRelationImages_iff_exists_geometricRel_equivalence j).mpr
        ⟨κ, hκ, fun k _ _ hk b β hmk ↦ (hgeom k hk b β hmk).2⟩)⟩
    refine universallyInjective_of_isSurjective_diagonal site S hS
      (presheafPreRelation j).left ?_
    let Y' : AlgebraicSpaces site S hS := ⟨_, hTgt⟩
    let f' : R.left ⟶ Y' := ObjectProperty.homMk (presheafPreRelation j).left
    let d : R.left ⟶ AlgebraicSpaces.fiberProduct site S hS f' f' :=
      ObjectProperty.homMk (pullback.diagonal (presheafPreRelation j).left)
    refine isSurjective_of_surjective_app_of_large d κ hκ ?_
    intro k _ _ hk b hmk p
    let T : BigFppfOver site S hS := fieldObject (hS := hS) k hk b
    refine ⟨(pullback.fst (presheafPreRelation j).left
      (presheafPreRelation j).left).app (Opposite.op T) p, ?_⟩
    have hxy : (pullback.fst (presheafPreRelation j).left
          (presheafPreRelation j).left).app (Opposite.op T) p =
        (pullback.snd (presheafPreRelation j).left
          (presheafPreRelation j).left).app (Opposite.op T) p :=
      (hgeom k hk b (R.hom.hom.app (Opposite.op T)
        ((pullback.fst (presheafPreRelation j).left
          (presheafPreRelation j).left).app (Opposite.op T) p)) hmk).1 <|
        congrArg (fun α ↦ α.app (Opposite.op T) p)
          (pullback.condition (f := (presheafPreRelation j).left)
            (g := (presheafPreRelation j).left))
    exact pullback_app_ext _ _ T (app_pullback_fst_diagonal _ T _)
      ((app_pullback_snd_diagonal _ T _).trans hxy)

/-- **An arrow of a radicial pre-relation available after an extension of an algebraically closed
field is already available over the field.**

The pair of the two points of `U` is a morphism over the base out of the presheaf represented by
the test object of the field, and the arrow over the extension field is a point of the fibre of
the pre-relation above that pair; a nonempty fibre of a radicial morphism over an algebraically
closed field has a section, which is the required arrow. -/
private theorem geometricRel_of_setTheoreticRel_of_isRadicial {R' U' : Over B.obj}
    (j : PreRelation R' U') (hR : IsAlgebraicSpace site S hS R'.left)
    (hU : IsAlgebraicSpace site S hS U'.left)
    (hrad : IsRadicial site S hS hR (isAlgebraicSpace_prod_left hU hU) j.left)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U'.left.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U'.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (hxy : j.SetTheoreticRel k hk b β x y) :
    j.GeometricRel k hk b β x y := by
  classical
  let T : BigFppfOver site S hS := fieldObject (hS := hS) k hk b
  let A : Over B.obj := Over.mk (yonedaEquiv.symm β)
  have hsec : ∀ v : {v : U'.left.obj (Opposite.op T) // U'.hom.app (Opposite.op T) v = β},
      yonedaEquiv.symm v.1 ≫ U'.hom = A.hom := by
    intro v
    show yonedaEquiv.symm v.1 ≫ U'.hom = yonedaEquiv.symm β
    rw [yonedaEquiv_symm_naturality_right, v.property]
  let mx : A ⟶ U' := Over.homMk (yonedaEquiv.symm x.1) (hsec x)
  let my : A ⟶ U' := Over.homMk (yonedaEquiv.symm y.1) (hsec y)
  let g : yoneda.obj T ⟶ (U' ⨯ U' : Over B.obj).left := (prod.lift my mx).left
  have gfst : g ≫ (prod.fst : U' ⨯ U' ⟶ U').left = yonedaEquiv.symm y.1 :=
    congrArg (fun e : A ⟶ U' ↦ e.left) (prod.lift_fst my mx)
  have gsnd : g ≫ (prod.snd : U' ⨯ U' ⟶ U').left = yonedaEquiv.symm x.1 :=
    congrArg (fun e : A ⟶ U' ↦ e.left) (prod.lift_snd my mx)
  have hfst : j.left ≫ (prod.fst : U' ⨯ U' ⟶ U').left = j.target.left := rfl
  have hsnd : j.left ≫ (prod.snd : U' ⨯ U' ⟶ U').left = j.source.left := rfl
  obtain ⟨p, t, hps, hpt⟩ := hxy
  have hc : ∀ (π : (U' ⨯ U' : Over B.obj).left ⟶ U'.left) (m : R'.left ⟶ U'.left)
      (v : U'.left.obj (Opposite.op T)), j.left ≫ π = m → g ≫ π = yonedaEquiv.symm v →
      m.app _ p.value = U'.left.map t.op v →
      (yoneda.map t ≫ g) ≫ π = (yonedaEquiv.symm p.value ≫ j.left) ≫ π :=
    fun π m v hm hg hp ↦ by
      rw [Category.assoc, Category.assoc, hg, hm, yonedaEquiv_symm_naturality_left,
        yonedaEquiv_symm_naturality_right]
      exact congrArg yonedaEquiv.symm hp.symm
  have hcompat : yoneda.map t ≫ g = yonedaEquiv.symm p.value ≫ j.left :=
    prod_left_hom_ext (hc _ _ _ hfst gfst hpt) (hc _ _ _ hsnd gsnd hps)
  have hne : Nonempty (points site S hS (pullback g j.left)) :=
    ⟨FieldValuedPoint.class site S hS _
      { carrier := p.carrier
        contained := p.contained
        toBase := p.toBase
        value := yonedaEquiv
          (pullback.lift (yoneda.map t) (yonedaEquiv.symm p.value) hcompat) }⟩
  obtain ⟨a, ha, -⟩ := existsUnique_lift_of_isRadicial hR (isAlgebraicSpace_prod_left hU hU)
    j.left hrad k hk b g hne
  have hf : ∀ (π : (U' ⨯ U' : Over B.obj).left ⟶ U'.left) (m : R'.left ⟶ U'.left)
      (v : U'.left.obj (Opposite.op T)), j.left ≫ π = m → g ≫ π = yonedaEquiv.symm v →
      m.app (Opposite.op T) (yonedaEquiv a) = v := fun π m v hm hg ↦ by
    have h : a ≫ m = yonedaEquiv.symm v := by rw [← hm, ← Category.assoc, ha, hg]
    simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using congrArg yonedaEquiv h
  exact ⟨yonedaEquiv a, hf _ _ _ hsnd gsnd, hf _ _ _ hfst gfst⟩

/-- **Stacks 049X, condition (4).** For a pre-relation of algebraic spaces which is decent,
locally separated or quasi-separated the cardinality restriction can be dropped: it is a
set-theoretic equivalence relation exactly when over *every* algebraically closed field in the
site its map on arrows is injective and the relation its arrows cut out is an equivalence
relation.

Under any of the three hypotheses a universally injective pre-relation is radicial by
**Stacks 0484**, and over an algebraically closed field a fibre of a radicial morphism has
exactly one section as soon as it has a point: this gives the injectivity on arrows, and makes
the relation cut out by the arrows present over the field agree with the one of
**Stacks 0490**, where arrows are allowed to appear after a field extension. -/
@[stacks 049X "condition (4)"]
theorem isSetTheoreticEquivalenceRelation_iff_hasGeometricEquivalence
    (j : PreRelation R U)
    (hsep : IsDecent site S hS (presheafPreRelation j).left ∨
      IsLocallySeparated site S hS (presheafPreRelation j).left ∨
      IsQuasiSeparated site S hS (presheafPreRelation j).left) :
    IsSetTheoreticEquivalenceRelation (presheafPreRelation j) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
        (b : Spec (.of k) ⟶ S)
        (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))),
        j.HasGeometricEquivalence k hk b β := by
  constructor
  · intro h
    have hrad : IsRadicial site S hS R.left.property
        (isAlgebraicSpace_prod_left (A := (overForgetSpace B).obj U)
          (C := (overForgetSpace B).obj U) U.left.property U.left.property)
        (presheafPreRelation j).left := by
      rcases hsep with hd | hl | hq
      · exact isRadicial_of_universallyInjective_of_isDecent site S hS _ _ _ h.1 hd
      · exact isRadicial_of_universallyInjective_of_isLocallySeparated site S hS _ _ _ h.1 hl
      · exact isRadicial_of_universallyInjective_of_isQuasiSeparated site S hS _ _ _ h.1 hq
    intro k _ _ hk b β
    refine ⟨injective_app_of_isRadicial R.left.property _
      (presheafPreRelation j).left hrad k hk b, ?_⟩
    have he : (presheafPreRelation j).GeometricRel k hk b β =
        (presheafPreRelation j).SetTheoreticRel k hk b β := by
      funext x y
      refine propext ⟨?_, geometricRel_of_setTheoreticRel_of_isRadicial (presheafPreRelation j)
        R.left.property U.left.property hrad k hk b β x y⟩
      rintro ⟨r, hrs, hrt⟩
      refine ⟨{ carrier := k, contained := hk, toBase := b, value := r }, 𝟙 _, ?_, ?_⟩
      · simpa [FieldValuedPoint.siteObject, fieldObject] using hrs
      · simpa [FieldValuedPoint.siteObject, fieldObject] using hrt
    rw [he]
    exact h.2 k hk b β
  · exact fun h ↦ (isSetTheoreticEquivalenceRelation_iff_exists_hasGeometricEquivalence j).mpr
      ⟨0, Cardinal.aleph0_pos.trans site.aleph0_lt_cutoff, fun k _ _ hk b β _ ↦ h k hk b β⟩

end AlgebraicGeometry.Space

end
