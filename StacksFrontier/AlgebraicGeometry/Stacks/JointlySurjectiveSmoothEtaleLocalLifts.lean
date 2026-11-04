module

public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts

/-!
# Étale-local sections of a jointly surjective smooth family of 1-morphisms

Let `f j : 𝒳 j ⟶ 𝒴`, `j ∈ J`, be a family of 1-morphisms of algebraic stacks over `S` which are
each smooth (**Stacks 075U**) and *jointly surjective*, that is `|𝒴| = ⋃ j, |f j|(|𝒳 j|)` for the
points of **Stacks 04XG**. This file proves the smooth analogue of **Stacks 07AN**: for every
object `U` of the big fppf site of `S` and every object `y` of the fibre of `𝒴` over `U` there is
an *étale* covering `{W i → U}` of `U`, a map `a` from its index set to `J`, and for every `i` an
object of `𝒳 (a i)` over `W i` whose image is isomorphic to the restriction of `y` to `W i`.

The proof is the proof of **Stacks 07AN** with "flat and locally of finite presentation" replaced
throughout by "smooth", followed by the refinement step of **Stacks 06XH** part (2). In detail:
for a point `x` of `U`, read as a point `z` of the algebraic stack of `U` through
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, joint surjectivity supplies an index `j` and a
point of `|𝒳 j|` with the same image in `|𝒴|` as `z` has under the 1-morphism
`AlgebraicGeometry.Stack.fibreObjectStackMap` attached to `y` by the 2-Yoneda lemma
(**Stacks 004B**); by **Stacks 04XH** the two lift to a point of the 2-fibre product
`𝒳 j ×_𝒴 U` (**Stacks 04T2**), and a smooth surjective scheme presentation of that 2-fibre
product therefore contains a point above `x`. That presentation composed with the first projection
is smooth by **Stacks 075V** and **Stacks 075W**, and — both its source and its target being
represented — it is 2-isomorphic to the 1-morphism attached to a smooth morphism of the site, by
**Stacks 04SW**. Finally **Stacks 055U** shrinks a smooth morphism of the site hitting `x` to an
étale one hitting `x` and factoring through it, and the lift of `y` restricts along that
factorisation. The resulting family, indexed by the points of `U`, is étale and jointly
surjective, hence an étale covering of `U`, and each member carries a lift of `y`.

## Main results

* `AlgebraicGeometry.Stack.exists_schemeMap_of_isSmooth`: a smooth 1-morphism between represented
  algebraic stacks is 2-isomorphic to the one attached to a smooth morphism of the site.
* `AlgebraicGeometry.Stack.exists_scheme_lift_of_isSmooth_at_point`: a smooth 1-morphism admits,
  above any point of `U` whose image in `|𝒴|` lies in the image of the 1-morphism, a single
  smooth morphism of the site hitting that point and carrying a lift of `y`.
* `AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift`: the smooth analogue of
  **Stacks 07AN**, with the étale covering produced as a family of morphisms of the site together
  with the index map to `J`.

## Implementation notes

The covering is indexed by the points of the underlying scheme of `U`, lifted to the index
universe `Type (u + 1)`; this is where the index map `a` of the statement acquires content, since
the index set `J` of the family is left in an arbitrary universe. Choosing one member of the
covering per point of `U` is what replaces the coproduct `∐ j, 𝒳 j` of the source's argument, and
it is also what frees `J` from any smallness assumption.

`AlgebraicGeometry.Stack.exists_schemeMap_of_isSmooth` repeats the smoothness and 2-isomorphism
parts of `AlgebraicGeometry.Stack.exists_schemeMap_of_isSurjective_isSmooth`, whose statement also
concludes surjectivity of the morphism of the site and therefore assumes surjectivity of the
1-morphism; no member of the covering here is surjective on its own.

The isomorphism `f (a i) (x i) ≅ y|_{W i}` is rendered, as in
`AlgebraicGeometry.Stack.exists_fppfCovering_family_fibre_lift`, as a morphism
`f (a i) (x i) ⟶ y` lying over the member `W i → U` of the covering: in a category fibred in
groupoids that is exactly an isomorphism in the fibre over `W i`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 055U](https://stacks.math.columbia.edu/tag/055U)
* [Stacks Project, Tag 055V](https://stacks.math.columbia.edu/tag/055V)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.BasedFunctor.overMap

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The shrinking step of Stacks 055V inside a size-bounded big fppf site.** A point in the
image of a smooth morphism `m` of objects of a big fppf site is hit by an étale morphism from an
object of the site factoring through `m`. -/
private alias exists_etale_lift_of_mem_range_of_smooth :=
  AlgebraicGeometry.exists_contains_etale_lift_of_smooth

/-- **A smooth 1-morphism of represented algebraic stacks comes from a smooth morphism of the
site.** By the uniqueness half of **Stacks 04SW** a 1-morphism `schemeStack V ⟶ schemeStack U` is
2-isomorphic to the one attached to a morphism `q : V ⟶ U` of the big fppf category of `S`, namely
the morphism whose `yoneda.map` is the induced morphism of representing presheaves; and `q` is
then smooth as a morphism of schemes. -/
theorem exists_schemeMap_of_isSmooth {V U : BigFppfOver B S hS}
    (h : schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U)
    (hsm : AlgebraicStacks.IsSmooth B S hS h) :
    ∃ q : V ⟶ U, Smooth ((BigFppfOver.toScheme B S hS).map q) ∧
      Nonempty (h.hom ≅ schemeFibredCategoryMap B S hS q) := by
  obtain ⟨q, hq⟩ : ∃ q : V ⟶ U, yoneda.map q =
      representingMap B S hS (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
        (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
        h.hom :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  refine ⟨q, ?_, ?_⟩
  · refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Smooth.isEtaleLocalOnSourceAndTarget q).1 ?_
    rw [hq]
    exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
      (fun _ _ k => Space.IsSmooth B S hS k) (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (schemeStack.{u, w} B S hS V).property (schemeStack.{u, w} B S hS U).property
      (yoneda.obj V) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
      (representedChart B S hS V) (representedChart B S hS U) h.hom).1 hsm
  · obtain ⟨hu⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS
      (schemeFibredCategory B S hS V) (schemeFibredCategory B S hS U)
      (yoneda.obj V) (yoneda.obj U) (representedChart B S hS V) (representedChart B S hS U)
      (f := h.hom) (g := schemeFibredCategoryMap B S hS q)
      (by rw [representingMap_schemeFibredCategoryMap]; exact hq.symm)
    exact ⟨hu.default⟩

/-- **A smooth morphism of the site through a prescribed point, along which an object lifts.**
Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks over `S`, let `y` be an object of the
fibre of `𝒴` over an object `U` of the site, and let `z` be a point of the algebraic stack of `U`
whose image in `|𝒴|` under the 1-morphism named by `y` lies in the image of `|f|`. Then there is a
smooth morphism `m : T ⟶ U.left` of the underlying category of the site whose image contains the
point of `U` corresponding to `z`, together with an object of `𝒳` over its source whose image is
isomorphic to the restriction of `y` along `m`.

This is the argument of **Stacks 06XH** part (2) with surjectivity of `f` replaced by the
hypothesis at the single point `z`: that hypothesis is what **Stacks 04XH** turns into a point of
the 2-fibre product `𝒳 ×_𝒴 U` above `z`, which the smooth surjective scheme presentation of that
2-fibre product then lifts. -/
theorem exists_scheme_lift_of_isSmooth_at_point
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hsm : AlgebraicStacks.IsSmooth B S hS f)
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U)
    (z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U))
    (hz : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
      Set.range (AlgebraicStacks.pointsMap B S hS f)) :
    ∃ (T : B.Schemes) (m : T ⟶ U.left), Smooth (B.inclusion.map m) ∧
      pointsHomeomorphScheme B S hS U z ∈ Set.range (B.inclusion.map m) ∧
      ∃ (x : 𝒳.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶ y.1),
        𝒴.val.val.p.IsHomLift
          (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  let b : schemeStack.{u, w} B S hS U ⟶ 𝒴 := fibreObjectStackMap B S hS 𝒴 U y
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  obtain ⟨V, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  obtain ⟨q, hqsm, ⟨e⟩⟩ := exists_schemeMap_of_isSmooth B S hS (c ≫ P.fst)
    (AlgebraicStacks.isSmooth_comp B S hS c P.fst hcsm
      (AlgebraicStacks.isSmooth_baseChange B S hS f b P hP hsm))
  obtain ⟨ξ, hξ⟩ := hz
  obtain ⟨p, hp, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP z ξ hξ.symm
  obtain ⟨t, ht⟩ := hcsurj p
  have htz : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) t = z := by
    rwa [AlgebraicStacks.pointsMap_comp, Function.comp_apply, ht]
  have hpts : AlgebraicStacks.pointsMap B S hS (c ≫ P.fst) =
      pointsMap B S hS (schemeFibredCategory B S hS V).val
        (Classical.choose (schemeStack.{u, w} B S hS V).property)
        (Classical.choose (schemeStack.{u, w} B S hS U).property)
        (schemeFibredCategoryMap B S hS q).hom :=
    pointsMap_eq_of_basedNatTrans B S hS (schemeFibredCategory B S hS V).val _ _ e.hom.hom
  refine ⟨V.left, q.left, hqsm, ⟨pointsHomeomorphScheme B S hS V t, ?_⟩, ?_⟩
  · exact (pointsHomeomorphScheme_naturality B S hS q t).symm.trans
      (congrArg (pointsHomeomorphScheme B S hS U) ((congrFun hpts t).symm.trans htz))
  · obtain ⟨x, α, hα⟩ := exists_fibre_lift_of_twoCell 𝒳.val.val.p 𝒴.val.val.p
      y q f.hom.hom (c ≫ P.snd).hom.hom
      (Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y)
      (Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
        (Over.mk (𝟙 U))).φ
      ((Functor.TwoYoneda.chosenLift 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids U y
        (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift)
      ((Bicategory.whiskerLeft c P.iso.inv).hom.hom ≫
        (Bicategory.whiskerRight e.hom b.hom).hom)
    exact ⟨x.1, α, isHomLift_homMk_left B S hS 𝒴.val.val.p q α hα⟩

/-- **The smooth analogue of Stacks 07AN.** Let `f j : 𝒳 j ⟶ 𝒴`, `j ∈ J`, be a family of
1-morphisms of algebraic stacks over `S` which are each smooth and which are jointly surjective,
that is `|𝒴| = ⋃ j, |f j|(|𝒳 j|)`. Then for every object `U` of the big fppf site of `S` and every
object `y` of the fibre of `𝒴` over `U` there are an étale covering `{W i → U}_{i ∈ I}` of `U`, a
map `a : I → J` and, for every `i`, an object of `𝒳 (a i)` over `W i` whose image is isomorphic to
the restriction of `y` to `W i`.

The covering is given as a family of morphisms `e i : W i ⟶ U.left` of the underlying category of
the site which are étale and jointly surjective on the underlying schemes — which is what an
étale covering of `U` is. The isomorphism over a member is rendered as a morphism from the image
of the object to `y` lying over that member, which in a category fibred in groupoids is exactly an
isomorphism in the fibre. -/
theorem exists_etaleCovering_family_fibre_lift {J : Type v}
    {𝒳 : J → AlgebraicStacks.{u, w} B S hS} {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒳 j ⟶ 𝒴)
    (hsmooth : ∀ j, AlgebraicStacks.IsSmooth B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒴)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (U : BigFppfOver B S hS) (y : 𝒴.val.val.p.Fiber U) :
    ∃ (I : Type (u + 1)) (W : I → B.Schemes) (e : ∀ i, W i ⟶ U.left) (a : I → J),
      (∀ i, Etale (B.inclusion.map (e i))) ∧
        (∀ x : (B.inclusion.obj U.left), ∃ i, x ∈ Set.range (B.inclusion.map (e i))) ∧
          ∀ i, ∃ (x : (𝒳 (a i)).val.val.obj)
            (α : (CatFiberedInGroupoids.homFunctor (f (a i)).hom).obj x ⟶ y.1),
            𝒴.val.val.p.IsHomLift
              (Over.homMk (e i) rfl :
                (Over.mk (e i ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
  classical
  have key : ∀ x : (B.inclusion.obj U.left), ∃ (j : J) (W : B.Schemes) (e : W ⟶ U.left),
      Etale (B.inclusion.map e) ∧ x ∈ Set.range (B.inclusion.map e) ∧
        ∃ (x' : (𝒳 j).val.val.obj)
          (α : (CatFiberedInGroupoids.homFunctor (f j).hom).obj x' ⟶ y.1),
          𝒴.val.val.p.IsHomLift
            (Over.homMk e rfl : (Over.mk (e ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α := by
    intro x
    let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
    let z : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS U) :=
      (pointsHomeomorphScheme B S hS U).symm x
    have hmem : AlgebraicStacks.pointsMap B S hS (fibreObjectStackMap B S hS 𝒴 U y) z ∈
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)) := by
      rw [← hjs]
      exact Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨T, m, hmsm, hmpt, x₀, α, hα⟩ :=
      exists_scheme_lift_of_isSmooth_at_point B S hS (f j) (hsmooth j) U y z hj
    rw [show pointsHomeomorphScheme B S hS U z = x from
      (pointsHomeomorphScheme B S hS U).apply_symm_apply x] at hmpt
    obtain ⟨X, hX, e, hetale, hxe, c, hc⟩ :=
      exists_etale_lift_of_mem_range_of_smooth B m hmsm x hmpt
    refine ⟨j, B.obj hX, ObjectProperty.homMk e, hetale, hxe, ?_⟩
    have hfac : (ObjectProperty.homMk c : B.obj hX ⟶ T) ≫ m
        = (ObjectProperty.homMk e : B.obj hX ⟶ U.left) := ObjectProperty.hom_ext _ hc
    set b : (Over.mk ((ObjectProperty.homMk e : B.obj hX ⟶ U.left) ≫ U.hom) :
        BigFppfOver B S hS) ⟶ Over.mk (m ≫ U.hom) :=
      Over.homMk (ObjectProperty.homMk c) (by simp [← hfac]) with hbdef
    have hb : b ≫ (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
        = Over.homMk (ObjectProperty.homMk e) rfl := by
      rw [hbdef]
      exact Over.OverMorphism.ext (by simpa using hfac)
    have hw : CatFiberedInGroupoids.homFunctor (f j).hom ⋙ 𝒴.val.val.p = (𝒳 j).val.val.p :=
      (f j).hom.hom.w
    have hxbase : (𝒳 j).val.val.p.obj x₀ = Over.mk (m ≫ U.hom) := by
      rw [← hw]
      exact IsHomLift.domain_eq 𝒴.val.val.p
        (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U) α
    obtain ⟨x₁, ρ, hρ⟩ := (𝒳 j).val.isFiberedInGroupoids.exists_lift b x₀ hxbase
    refine ⟨x₁, (CatFiberedInGroupoids.homFunctor (f j).hom).map ρ ≫ α, ?_⟩
    rw [← hb]
    have h₁ : 𝒴.val.val.p.IsHomLift b ((CatFiberedInGroupoids.homFunctor (f j).hom).map ρ) :=
      PresheafOfCategories.isHomLift_map_of_comp hw b ρ hρ
    exact IsHomLift.comp 𝒴.val.val.p b
      (Over.homMk m rfl : (Over.mk (m ≫ U.hom) : BigFppfOver B S hS) ⟶ U)
      ((CatFiberedInGroupoids.homFunctor (f j).hom).map ρ) α
  choose jj WW ee hee using key
  exact ⟨ULift.{u + 1} (B.inclusion.obj U.left), fun i => WW i.down, fun i => ee i.down,
    fun i => jj i.down, fun i => (hee i.down).1, fun x => ⟨ULift.up x, (hee x).2.1⟩,
    fun i => (hee i.down).2.2⟩

end AlgebraicGeometry.Stack

end
