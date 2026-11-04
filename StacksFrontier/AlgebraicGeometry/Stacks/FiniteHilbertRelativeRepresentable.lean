module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FibreSectionSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePointIso
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.CategoryTheory.TwoYoneda.TautologicalValue

/-!
# The induced morphism of relative finite Hilbert stacks is representable (Stacks 05YJ)

Let `G : 𝒳' ⟶ 𝒳` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`,
let `F : 𝒳 ⟶ 𝒴` and `F' : 𝒳' ⟶ 𝒴` be 1-morphisms to a third stack and let
`γ : F' ⟶ F ∘ G` be a 2-isomorphism, so that Stacks 05XN produces the canonical 1-morphism
`ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` relative finite Hilbert stacks. Stacks 05YJ asserts that
this 1-morphism is representable by algebraic spaces as soon as `G` is — with no étaleness
hypothesis, which is what distinguishes it from Stacks 05YG.

The source's proof unwinds the fibre over an object `ξ = (U, Z, y, x, α)` of `ℋ_d(𝒳/𝒴)`: an
object of that fibre over `a : U' ⟶ U` is an object of `𝒳'` over `U' ×_{a, U} Z` together with an
identification of its image under `G` with the restriction of `x`, that is a section over `U'` of
`W ⟶ Z`, where `W` is an algebraic space representing the fibre of `G` over the scheme-valued
point of `𝒳` determined by `x`. So the fibre is the restriction of scalars `Res_{Z/U}(W)`, which
is an algebraic space by Stacks 05YF because `Z ⟶ U` is finite locally free.

This file performs that deduction. The identification of the fibre over the universal family of
an object with the space of sections is
`AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace`, which is
already available; what this file adds is the production of `W` from the representability
hypothesis on `G`, the appeal to Stacks 05YF, and the passage from the universal families to an
arbitrary scheme-valued point.

That last step is the 2-Yoneda normalisation: a scheme-valued point `y` of `ℋ_d(𝒳/𝒴)` over `U`
is 2-isomorphic over the site to the universal family of the object `ξ = y(id_U)`, because the
two points agree at the tautological object — the value of the universal family there is `ξ` by
`CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso` — so Stacks 02Y4 in the form
`StacksRepresentableCFG.exists_natIso_of_iso_at_id` produces a vertical 2-isomorphism between
them, and `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_reindex` carries a
representation of the 2-fibre product across it.

## Main definitions

* `AlgebraicGeometry.Stack.FibresOverUniversalFamiliesAlgebraic`: the assertion that the 2-fibre
  product of a 1-morphism into `ℋ_d(𝒳/𝒴)` with the universal family of every *object* of
  `ℋ_d(𝒳/𝒴)` is representable by an algebraic space.
* `AlgebraicGeometry.Stack.universalFamilyTautIso`: the vertical isomorphism from the value of
  the universal family of an object at the tautological object to that object.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_universalFamilies`: the 2-Yoneda
  normalisation — a 1-morphism into `ℋ_d(𝒳/𝒴)` whose 2-fibre product with the universal family
  of every object is representable by an algebraic space is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.FiniteHilbert.Object.exists_isAlgebraicSpace_sectionSpace`: the
  2-fibre product of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` with the universal family of an object of
  `ℋ_d(𝒳/𝒴)` is representable by an algebraic space, given that `G` is representable by
  algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_mapRelative_of_representable`:
  **Stacks 05YJ**, the 1-morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` is representable by algebraic spaces.

The hypothesis that `G` is representable by algebraic spaces is used exactly where the source uses
it — to produce the algebraic space `W` over `Z` representing the fibre of `G` over the point of
`𝒳` carried by `ξ`. The source's Proposition Stacks 05YF, that a restriction of scalars along a
finite locally free cover is an algebraic space, enters as
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree`, the case of a base
which is a scheme, applied to the cover `Z ⟶ U` of `ξ`.

Nothing of Stacks 05YH is proved here; it is
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.ProductFibreEquivalence`.

## Implementation notes

The presentation `w` of the relocalized presheaf over the cover, which
`AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace` takes as an
argument, is the structural morphism `CategoryTheory.OverShriek.relocalizeToYoneda`, whose
defining property is exactly the hypothesis `hw` of that theorem and holds by `rfl`.

The normalisation is proved by `subst` on the equality `ξ.U = U` of the base of the object with
the given one, which is what moves the representation from the site of `ξ.U` to the site of `U`
without a transport of categories; this is why
`AlgebraicGeometry.Stack.exists_equivalenceOver_of_obj` takes the object, the
base and that equality as three separate arguments rather than instantiating the base.

The hypotheses of Stacks 05YJ are weaker than those of Stacks 05YG, so this statement is not
subsumed by `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_mapRelative`: the latter
carries the identification of every fibre with the space of sections of a *separated étale*
morphism, which is both more than this file proves and more than the hypotheses of Stacks 05YJ
supply.

## References

* [Stacks Project, Tag 02Y4](https://stacks.math.columbia.edu/tag/02Y4)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 05XN](https://stacks.math.columbia.edu/tag/05XN)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YG](https://stacks.math.columbia.edu/tag/05YG)
* [Stacks Project, Tag 05YJ](https://stacks.math.columbia.edu/tag/05YJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w v₁ u₁ a₁ b₁

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] BasedCategory.ofFunctor finiteHilbertCategory
  FiniteHilbert.Object.universalFamily

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-! ### The 2-Yoneda normalisation of a scheme-valued point -/

/-- **The value of the universal family of an object at the tautological object is that
object.** This is `CategoryTheory.Functor.TwoYoneda.liftFunctorTautIso` for the forgetful functor
of the relative finite Hilbert category. -/
noncomputable def universalFamilyTautIso (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    ξ.universalFamily.obj (Over.mk (𝟙 ξ.U.left)) ≅ ξ :=
  Functor.TwoYoneda.liftFunctorTautIso (finiteHilbertProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) isFiberedInGroupoids_finiteHilbertProjection ξ.U
    (Functor.Fiber.mk rfl)

/-- `AlgebraicGeometry.Stack.universalFamilyTautIso` is vertical. -/
theorem isHomLift_universalFamilyTautIso (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsHomLift (𝟙 ((Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left))))
      (universalFamilyTautIso ξ).hom :=
  Functor.TwoYoneda.isHomLift_liftFunctorTautIso_hom _ _ _ _

/-- The assertion that the 2-fibre product of a 1-morphism `f` into `ℋ_d(𝒳/𝒴)` with the universal
family of an object `ξ` of `ℋ_d(𝒳/𝒴)` is representable by an algebraic space over the base of
`ξ`, for every object `ξ`.

This is the condition of Stacks 02ZW restricted to those scheme-valued points of `ℋ_d(𝒳/𝒴)` which
the 2-Yoneda lemma attaches to an object. -/
abbrev FibresOverUniversalFamiliesAlgebraic {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)}
    (f : 𝒵 ⥤ᵇ finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)) : Prop :=
  ∀ ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d,
    ∃ A : (BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property A ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map ξ.U.hom) 𝒵.p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p ξ.universalFamily f.toFunctor)
          (presheafOfCategories (A ⋙ typeToCat)).p)

/-- **A scheme-valued point whose value at the tautological object is a given object `ξ` has the
same 2-fibre product as the universal family of `ξ`.** The two points agree, vertically, at the
tautological object — the value of the universal family there is `ξ` by
`AlgebraicGeometry.Stack.universalFamilyTautIso` — so they are 2-isomorphic over the site by
Stacks 02Y4, and reindexing the 2-fibre product along that 2-isomorphism is an equivalence over
the site of the base. Any property `P` of a presheaf representing the 2-fibre product over the
universal families is therefore inherited by one representing it over an arbitrary point. -/
theorem exists_equivalenceOver_of_obj
    (P : ∀ (V : Scheme.{u}) (hV : B.Contains V), ((BigFppfOver B V hV)ᵒᵖ ⥤ Type u) → Prop)
    {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)}
    (f : 𝒵 ⥤ᵇ finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (hfam : ∀ ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d,
      ∃ A : (BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)ᵒᵖ ⥤ Type u,
        P (B.inclusion.obj ξ.U.left) ξ.U.left.property A ∧
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map ξ.U.hom) 𝒵.p
              (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
                (d := d)).p ξ.universalFamily f.toFunctor)
            (presheafOfCategories (A ⋙ typeToCat)).p))
    (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) (U : BigFppfOver B S hS) (hξU : ξ.U = U)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).obj)
    (hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p = Over.map U.hom)
    (hpt : y.obj (Over.mk (𝟙 U.left)) = ξ) :
    ∃ A : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      P U.left.1 U.left.2 A ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒵.p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p y f.toFunctor)
          (presheafOfCategories (A ⋙ typeToCat)).p) := by
  subst hξU
  obtain ⟨A, hA, ⟨e⟩⟩ := hfam ξ
  refine ⟨A, hA, ?_⟩
  -- the two points agree at the tautological object, vertically
  have hid : finiteHilbertProjection.obj (y.obj (Over.mk (𝟙 ξ.U.left))) =
      (Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left)) :=
    congrArg (fun K => K.obj (Over.mk (𝟙 ξ.U.left))) hy
  have hptv : finiteHilbertProjection.IsHomLift
      (𝟙 ((Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left)))) (eqToHom hpt) := by
    refine IsHomLift.of_fac' _ _ _ hid (hid.symm.trans (congrArg _ hpt)).symm ?_
    simp [eqToHom_map]
  have hvert := isHomLift_universalFamilyTautIso ξ
  have hinv := IsHomLift.lift_id_inv finiteHilbertProjection
    ((Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left))) (universalFamilyTautIso ξ)
  have hθ : finiteHilbertProjection.IsHomLift
      (𝟙 ((Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left))))
      (eqToHom hpt ≫ (universalFamilyTautIso ξ).inv) := by
    have := hptv
    have := hinv
    have hc := IsHomLift.comp finiteHilbertProjection
      (𝟙 ((Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left))))
      (𝟙 ((Over.map ξ.U.hom).obj (Over.mk (𝟙 ξ.U.left)))) (eqToHom hpt)
      (universalFamilyTautIso ξ).inv
    rwa [Category.comp_id] at hc
  -- Stacks 02Y4: the two points are 2-isomorphic over the site
  obtain ⟨α, hα⟩ := StacksRepresentableCFG.exists_natIso_of_iso_at_id ξ.U.hom y
    ξ.universalFamily hy ξ.universalFamily_comp isFiberedInGroupoids_finiteHilbertProjection
    (Iso.trans (eqToIso hpt) (universalFamilyTautIso ξ).symm) hθ
  -- both 2-fibre products are fibred in groupoids over the site of the base
  have hfibre : ∀ z, z ⋙ finiteHilbertProjection = Over.map ξ.U.hom →
      (TwoFibreProductOver.fst (Over.map ξ.U.hom) 𝒵.p
        finiteHilbertProjection z f.toFunctor).IsFiberedInGroupoids := fun z hz =>
    (Functor.isFiberedInGroupoids_comp_overMap_iff ξ.U.hom _).1 (by
      rw [TwoFibreProductOver.fst_comp_eq]
      exact TwoFibreProductOver.isFiberedInGroupoids (Over.map ξ.U.hom) 𝒵.p
        finiteHilbertProjection z f.toFunctor
        (Functor.IsFiberedInGroupoids.over_map ξ.U.hom) h𝒵
        isFiberedInGroupoids_finiteHilbertProjection hz f.w)
  obtain ⟨k⟩ := TwoFibreProductOver.nonempty_equivalenceOver_reindex α hα (hfibre y hy)
    (hfibre _ ξ.universalFamily_comp)
  exact ⟨k.trans e⟩

/-- **The 2-Yoneda normalisation of a scheme-valued point of a relative finite Hilbert
category.** A 1-morphism into `ℋ_d(𝒳/𝒴)` whose 2-fibre product with the universal family of every
object of `ℋ_d(𝒳/𝒴)` is representable by an algebraic space is representable by algebraic spaces
in the sense of Stacks 02ZW.

Given a scheme-valued point `y` over `U`, the object `ξ = y(id_U)` has base `U`, because `y` is a
1-morphism over the site, and `y` takes the tautological object to `ξ` by construction;
`AlgebraicGeometry.Stack.exists_equivalenceOver_of_obj` then identifies the
2-fibre product over `y` with the one over the universal family of `ξ`. -/
theorem isRepresentableByAlgebraicSpaces_of_universalFamilies
    {𝒵 : BasedCategory.{a₁, b₁} (BigFppfOver B S hS)}
    (f : 𝒵 ⥤ᵇ finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (hfam : FibresOverUniversalFamiliesAlgebraic f) :
    IsRepresentableByAlgebraicSpaces B S hS f := by
  intro U 𝒰 p𝒰 y hy
  have hξU : (y.obj (Over.mk (𝟙 U.left))).U = U :=
    (congrArg (fun K => K.obj (Over.mk (𝟙 U.left))) hy).trans
      (Over.iteratedSliceBackward_obj_mk_id_left U)
  exact exists_equivalenceOver_of_obj (fun V hV A => IsAlgebraicSpace B V hV A) f h𝒵 hfam
    (y.obj (Over.mk (𝟙 U.left))) U hξU y hy rfl

/-! ### Stacks 05YJ -/

variable {𝒳' : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory}

/-- **The 2-fibre product of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` with the universal family of an object `ξ`
of `ℋ_d(𝒳/𝒴)` is representable by an algebraic space.** The fibre of `G` over the scheme-valued
point of `𝒳` carried by `ξ` is represented by an algebraic space `W` over the cover `Z` of `ξ`,
since `G` is representable by algebraic spaces; the 2-fibre product is then the space of sections
over the base of `ξ` of the relocalization of `W`, by
`AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace`; and that
space of sections is an algebraic space by Stacks 05YF, since `Z` is finite locally free of
degree `d` over the base. -/
theorem FiniteHilbert.Object.exists_isAlgebraicSpace_sectionSpace
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hG : IsRepresentableByAlgebraicSpaces B S hS G)
    (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    ∃ A : (BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property A ∧
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map ξ.U.hom)
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
              (d := d)).p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p ξ.universalFamily
            (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor)
          (presheafOfCategories (A ⋙ typeToCat)).p) := by
  obtain ⟨W, hW, hfibre⟩ := hG ξ.Z ξ.sourcePoint ξ.sourcePoint_comp
  have : Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map (Over.mk ξ.q.left).hom) :=
    @Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d ξ.finiteLocallyFree
  exact ⟨Space.sectionSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property (Over.mk ξ.q.left)
      ((OverShriek.relocalizePresheafFunctor ξ.q.left).obj W)
      (OverShriek.relocalizeToYoneda ξ.q.left W),
    Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree (Over.mk ξ.q.left)
      (isAlgebraicSpace_viewOver B ξ.Z.left.1 ξ.U.left.1 ξ.Z.left.2 ξ.U.left.2 ξ.q.left W hW) _,
    ξ.nonempty_equivalenceOver_sectionSpace W (OverShriek.relocalizeToYoneda ξ.q.left W)
      (fun _ _ => rfl) γ hfibre⟩

/-- **Stacks 05YJ.** Let `G : 𝒳' ⟶ 𝒳` be a 1-morphism of stacks in groupoids over the big fppf
site of `S` which is representable by algebraic spaces, and let `γ` present `𝒳' ⟶ 𝒴` as the
composite of `G` with `F : 𝒳 ⟶ 𝒴`. Then the canonical 1-morphism
`ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` relative finite Hilbert stacks is representable by
algebraic spaces.

The fibre over the universal family of an object `ξ = (U, Z, y, x, α)` is the restriction of
scalars along `Z ⟶ U` of an algebraic space representing the fibre of `G` over `x`, which is an
algebraic space by Stacks 05YF; that is
`AlgebraicGeometry.Stack.FiniteHilbert.Object.exists_isAlgebraicSpace_sectionSpace`. An arbitrary
scheme-valued point reduces to those by the 2-Yoneda normalisation
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_universalFamilies`. -/
@[stacks 05YJ]
theorem isRepresentableByAlgebraicSpaces_mapRelative_of_representable
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hG : IsRepresentableByAlgebraicSpaces B S hS G) :
    IsRepresentableByAlgebraicSpaces B S hS
      (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ) :=
  isRepresentableByAlgebraicSpaces_of_universalFamilies _
    isFiberedInGroupoids_finiteHilbertProjection
    fun ξ ↦ ξ.exists_isAlgebraicSpace_sectionSpace γ hG

end AlgebraicGeometry.Stack

end
