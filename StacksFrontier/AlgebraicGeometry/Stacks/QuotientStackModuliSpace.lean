module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CategoricalQuotient
public import StacksFrontier.AlgebraicGeometry.Stacks.CategoricalModuliSpace

/-!
# Quotient stacks as categorical moduli spaces

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a terminal base algebraic space
`B`, let `𝒳 = [U/R]` be its quotient stack and let `f : 𝒳 ⟶ Y` be a 1-morphism to an algebraic
space. Stacks 0DUH attaches to `f` the `R`-invariant morphism `φ : U ⟶ Y`, the restriction of `f`
along the projection `π : U ⟶ [U/R]`, and that attachment is a bijection. Then `f` is a
categorical moduli space (Stacks 0DUG) exactly when `φ` is a categorical quotient (Stacks 048J),
and the same holds in a full subcategory of the algebraic spaces (Stacks 0DUI, non-uniform case).

## Main definitions

* `AlgebraicGeometry.Stack.isTerminal_terminalAlgebraicSpace`: the presheaf represented by the
  terminal object of the big fppf site is a terminal algebraic space.
* `AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpace` and
  `AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpaceIn`: the conditions of parts (1) and (3)
  of Stacks 0DUG, for a 1-morphism of based categories at any hom universe.

## Main results

* `AlgebraicGeometry.Stack.restrictedMorphism_comp_associatedMap`: restriction along the
  projection turns a factorization of `f` through a morphism `h` of algebraic spaces into a
  factorization of `φ`, namely `(f ∘ h)|_U = φ ∘ h`.
* `AlgebraicGeometry.Stack.isCategoricalModuliSpace_iff_forall_basedFunctor`:
  `AlgebraicGeometry.Stack.IsCategoricalModuliSpace` is equivalent to
  `AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpace`.
* `AlgebraicGeometry.Stack.quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient` and
  `quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient_prodLift`:
  `f` is a categorical moduli space if and only if `φ` is a categorical quotient of the
  pre-relation `(t, s)`.
* `AlgebraicGeometry.Stack.quotientStack_isCategoricalModuliSpaceIn_iff_isCategoricalQuotientIn`:
  the same in a full subcategory.

## References

* [Stacks Project, Tag 048J](https://stacks.math.columbia.edu/tag/048J)
* [Stacks Project, Tag 048L](https://stacks.math.columbia.edu/tag/048L)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
* [Stacks Project, Tag 0DUI](https://stacks.math.columbia.edu/tag/0DUI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe v w v' w' u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The terminal algebraic space -/

/-- The presheaf represented by the terminal object of the big fppf site is a terminal algebraic
space. -/
def isTerminal_terminalAlgebraicSpace :
    IsTerminal (⟨yoneda.obj (⊤_ (BigFppfOver C S hS)),
      isAlgebraicSpace_yoneda C S hS _⟩ : AlgebraicSpaces C S hS) :=
  IsTerminal.ofUniqueHom
    (fun W => ObjectProperty.homMk ((Space.isTerminal_yoneda_obj_terminal C S hS).from W.obj))
    fun _ _ => ObjectProperty.hom_ext _
      ((Space.isTerminal_yoneda_obj_terminal C S hS).hom_ext _ _)

/-! ### Factorizations through the category attached to a presheaf -/

/-- Two 1-morphisms from a category over the site, with morphisms in any universe, into the
category attached to a presheaf of sets which are joined by a 2-morphism are equal. -/
theorem basedFunctor_eq_of_basedNatTrans {𝒳 : BasedCategory.{v, w} (BigFppfOver C S hS)}
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {a b : 𝒳 ⥤ᵇ (fibredCategory C S hS F).val} (η : BasedNatTrans a b) : a = b := by
  have : (fibredCategory C S hS F).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection F).IsFiberedInSets
  refine BasedCategory.BasedFunctor.ext' (Functor.IsFiberedInSets.eq_of_obj_eq
    𝒳.p (fibredCategory C S hS F).val.p _ _ a.w b.w fun x => ?_)
  have := η.isHomLift' x
  have : (fibredCategory C S hS F).val.p.IsHomLift (𝟙 (𝒳.p.obj x)) (𝟙 (b.obj x)) :=
    IsHomLift.id (BasedFunctor.w_obj b x)
  exact (Functor.IsFiberedInSets.eq_of_isHomLift (fibredCategory C S hS F).val.p
    (𝟙 (𝒳.p.obj x)) (η.toNatTrans.app x) (𝟙 (b.obj x))).choose

/-- If two 1-morphisms `a b : 𝒳 ⟶ 𝒴` are joined by a 2-morphism, then their composites with a
1-morphism `D` into the category attached to a presheaf of sets are equal. -/
theorem comp_eq_of_basedNatTrans {𝒳 : BasedCategory.{v, w} (BigFppfOver C S hS)}
    {𝒴 : BasedCategory.{v', w'} (BigFppfOver C S hS)}
    {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {a b : 𝒳 ⥤ᵇ 𝒴} (η : BasedNatTrans a b)
    (D : 𝒴 ⥤ᵇ (fibredCategory C S hS F).val) :
    BasedFunctor.comp a D = BasedFunctor.comp b D :=
  basedFunctor_eq_of_basedNatTrans (BasedCategory.whiskerRight η D)

/-! ### The universal property of a categorical moduli space -/

/-- A 1-morphism `F : 𝒵 ⟶ Y` from a category over the big fppf site to the category attached to
an algebraic space `Y` is a *categorical moduli space* when for every algebraic space `W` and
every 1-morphism `g` from `𝒵` to the category attached to `W` there is a unique morphism
`h : Y ⟶ W` of algebraic spaces with `F ∘ h = g`. -/
abbrev IsBasedCategoricalModuliSpace {𝒵 : BasedCategory.{v, w} (BigFppfOver C S hS)}
    (Y : AlgebraicSpaces C S hS) (F : 𝒵 ⥤ᵇ (fibredCategory C S hS Y.obj).val) : Prop :=
  ∀ (W : AlgebraicSpaces C S hS) (g : 𝒵 ⥤ᵇ (fibredCategory C S hS W.obj).val),
    ∃! h : Y ⟶ W, BasedFunctor.comp F (associatedMap C S hS h.hom).1.hom = g

/-- The universal property of `AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpace` with the
target algebraic spaces restricted to the full subcategory selected by the object predicate `P`,
which `Y` is required to meet. -/
abbrev IsBasedCategoricalModuliSpaceIn {𝒵 : BasedCategory.{v, w} (BigFppfOver C S hS)}
    (P : AlgebraicSpaces C S hS → Prop) (Y : AlgebraicSpaces C S hS)
    (F : 𝒵 ⥤ᵇ (fibredCategory C S hS Y.obj).val) : Prop :=
  P Y ∧ ∀ (W : AlgebraicSpaces C S hS), P W →
    ∀ g : 𝒵 ⥤ᵇ (fibredCategory C S hS W.obj).val,
      ∃! h : Y ⟶ W, BasedFunctor.comp F (associatedMap C S hS h.hom).1.hom = g

/-- For 1-morphisms `f` and `g` into the categories attached to algebraic spaces `Y` and `W`,
there is a unique `h : Y ⟶ W` with `f ∘ h ≅ g` if and only if there is a unique `h : Y ⟶ W` with
`f ∘ h = g` as 1-morphisms of based categories. -/
theorem existsUnique_factorization_iff
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    {Y W : AlgebraicSpaces C S hS} (f : 𝒳 ⟶ fibredCategory C S hS Y.obj)
    (g : 𝒳 ⟶ fibredCategory C S hS W.obj) :
    (∃! h : Y ⟶ W, Nonempty (f ≫ (associatedMap C S hS h.hom).1 ≅ g)) ↔
      ∃! h : Y ⟶ W, BasedFunctor.comp f.hom (associatedMap C S hS h.hom).1.hom = g.hom :=
  existsUnique_congr fun _ =>
    ⟨fun ⟨e⟩ => congrArg Bicategory.InducedBicategory.Hom.hom (hom_eq_of_hom₂ C S hS e.hom),
      fun he => ⟨eqToIso (Bicategory.InducedBicategory.hom_ext he)⟩⟩

/-- `AlgebraicGeometry.Stack.IsCategoricalModuliSpace` is equivalent to
`AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpace` of the underlying 1-morphism of based
categories. -/
theorem isCategoricalModuliSpace_iff_forall_basedFunctor
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (Y : AlgebraicSpaces C S hS) (f : 𝒳 ⟶ fibredCategory C S hS Y.obj) :
    IsCategoricalModuliSpace C S hS Y f ↔ IsBasedCategoricalModuliSpace Y f.hom :=
  ⟨fun hf W g =>
      (existsUnique_factorization_iff f (Bicategory.InducedBicategory.mkHom g)).1 (hf W _),
    fun hf W g => (existsUnique_factorization_iff f g).2 (hf W g.hom)⟩

/-- `AlgebraicGeometry.Stack.IsCategoricalModuliSpaceIn` is equivalent to
`AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpaceIn` of the underlying 1-morphism of based
categories. -/
theorem isCategoricalModuliSpaceIn_iff_forall_basedFunctor
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver C S hS)}
    (P : AlgebraicSpaces C S hS → Prop) (Y : AlgebraicSpaces C S hS)
    (f : 𝒳 ⟶ fibredCategory C S hS Y.obj) :
    IsCategoricalModuliSpaceIn C S hS P Y f ↔ IsBasedCategoricalModuliSpaceIn P Y f.hom :=
  and_congr_right' ⟨fun hf W hW g =>
      (existsUnique_factorization_iff f (Bicategory.InducedBicategory.mkHom g)).1 (hf W hW _),
    fun hf W hW g => (existsUnique_factorization_iff f g).2 (hf W hW g.hom)⟩

/-! ### Restriction of a factorization along the projection -/

/-- If `f : [U/R] ⟶ Y` restricts to `φ : U ⟶ Y` along the projection and `h : Y ⟶ W` is a
morphism of algebraic spaces, then `f` followed by `h` restricts to `φ` followed by `h`. -/
theorem restrictedMorphism_comp_associatedMap (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y W : AlgebraicSpaces C S hS}
    (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) (h : Y ⟶ W) :
    restrictedMorphism G (BasedFunctor.comp f (associatedMap C S hS h.hom).1.hom) =
      restrictedMorphism G f ≫ h := by
  refine ObjectProperty.hom_ext _ ?_
  have e : (associatedMap C S hS
        (restrictedMorphism G (BasedFunctor.comp f (associatedMap C S hS h.hom).1.hom)).hom).1.hom =
      (associatedMap C S hS ((restrictedMorphism G f).hom ≫ h.hom)).1.hom := by
    rw [← restrictedMorphism_spec]
    change BasedFunctor.comp (BasedFunctor.comp (quotientStackProjection G) f)
      (associatedMap C S hS h.hom).1.hom = _
    rw [restrictedMorphism_spec, associatedMap_comp]
    rfl
  have he := congrArg
    (fun θ : (fibredCategory C S hS G.objects.obj).val ⥤ᵇ (fibredCategory C S hS W.obj).val =>
      PresheafOfCategories.natTransOfBasedFunctor θ.toFunctor θ.w) e
  rwa [natTransOfBasedFunctor_associatedMap, natTransOfBasedFunctor_associatedMap] at he

/-! ### Categorical moduli spaces and categorical quotients -/

section Comparison

variable {G : GroupoidInAlgebraicSpaces C S hS B}
  {j : Space.PreRelation (Over.mk G.arrowsToBase) (Over.mk G.objectsToBase)}

/-- Invariance under the pre-relation `(t, s)` of a groupoid in algebraic spaces, read in the
slice of algebraic spaces over the base, is invariance under the pre-relation of presheaves
`AlgebraicGeometry.Space.groupoidPreRelation` of the groupoid. -/
theorem isInvariant_iff_isInvariant_groupoidPreRelation
    (hjt : (Space.PreRelation.target j).left = G.target)
    (hjs : (Space.PreRelation.source j).left = G.source)
    {W : AlgebraicSpaces C S hS} (ψ : G.objects ⟶ W) :
    Space.IsInvariant j ψ ↔ Space.IsInvariant (Space.groupoidPreRelation G) ψ.hom := by
  rw [isInvariant_iff]
  change (Space.PreRelation.target j).left ≫ ψ = (Space.PreRelation.source j).left ≫ ψ ↔ _
  rw [hjt, hjs]

/-- A 1-morphism out of a quotient stack is determined by its restriction along the
projection. -/
theorem restrictedMorphism_injective (G : GroupoidInAlgebraicSpaces C S hS B)
    {W : AlgebraicSpaces C S hS}
    (g₁ g₂ : quotientStack G ⥤ᵇ (fibredCategory C S hS W.obj).val)
    (hg : restrictedMorphism G g₁ = restrictedMorphism G g₂) : g₁ = g₂ :=
  restriction_injective G g₁ g₂ (by rw [restrictedMorphism_spec, restrictedMorphism_spec, hg])

/-- Every `R`-invariant morphism out of the object space is the restriction of a 1-morphism out
of the quotient stack. -/
theorem exists_restrictedMorphism_eq (G : GroupoidInAlgebraicSpaces C S hS B)
    {W : AlgebraicSpaces C S hS} (ψ : G.objects ⟶ W)
    (hψ : Space.IsInvariant (Space.groupoidPreRelation G) ψ.hom) :
    ∃ g : quotientStack G ⥤ᵇ (fibredCategory C S hS W.obj).val, restrictedMorphism G g = ψ :=
  ⟨(quotientStackHomEquivInvariant G W).symm ⟨ψ, hψ⟩,
    congrArg Subtype.val ((quotientStackHomEquivInvariant G W).apply_symm_apply ⟨ψ, hψ⟩)⟩

/-- A factorization of `g` through `f` by a morphism `h` of algebraic spaces is the same as one of
the restrictions along the projection. -/
private theorem comp_associatedMap_eq_iff (G : GroupoidInAlgebraicSpaces C S hS B)
    {Y W : AlgebraicSpaces C S hS} (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    (g : quotientStack G ⥤ᵇ (fibredCategory C S hS W.obj).val) (h : Y ⟶ W) :
    BasedFunctor.comp f (associatedMap C S hS h.hom).1.hom = g ↔
      restrictedMorphism G f ≫ h = restrictedMorphism G g :=
  ⟨fun e => by rw [← restrictedMorphism_comp_associatedMap, e],
    fun e => restrictedMorphism_injective G _ _
      (by rw [restrictedMorphism_comp_associatedMap, e])⟩

/-- For an algebraic space `Z` over a terminal base, every 1-morphism `[U/R] ⟶ Z` factors uniquely
through `f` if and only if every `R`-invariant morphism `U ⟶ Z` factors uniquely through the
restriction `φ` of `f`. -/
private theorem factorization_iff (hB : IsTerminal B)
    (hjt : (Space.PreRelation.target j).left = G.target)
    (hjs : (Space.PreRelation.source j).left = G.source)
    (Y : AlgebraicSpaces C S hS)
    (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) (Z : Over B) :
    (∀ g : quotientStack G ⥤ᵇ (fibredCategory C S hS Z.left.obj).val,
        ∃! h : Y ⟶ Z.left, BasedFunctor.comp f (associatedMap C S hS h.hom).1.hom = g) ↔
      ∀ ψ : (Over.mk G.objectsToBase : Over B) ⟶ Z, Space.IsInvariant j ψ.left →
        ∃! χ : (Over.mk (hB.from Y) : Over B) ⟶ Z,
          (Over.homMk (restrictedMorphism G f) (hB.hom_ext _ _) :
            (Over.mk G.objectsToBase : Over B) ⟶ Over.mk (hB.from Y)) ≫ χ = ψ := by
  constructor
  · intro H ψ hψ
    obtain ⟨g, hg⟩ := exists_restrictedMorphism_eq G ψ.left
      ((isInvariant_iff_isInvariant_groupoidPreRelation hjt hjs ψ.left).1 hψ)
    obtain ⟨h₀, hh₀, huniq⟩ := H g
    refine ⟨Over.homMk h₀ (hB.hom_ext _ _), Over.OverMorphism.ext ?_, fun χ hχ =>
      Over.OverMorphism.ext (huniq χ.left ((comp_associatedMap_eq_iff G f g _).2 ?_))⟩
    · exact ((comp_associatedMap_eq_iff G f g h₀).1 hh₀).trans hg
    · exact (congrArg Over.Hom.left hχ).trans hg.symm
  · intro H g
    obtain ⟨χ, hχ, huniq⟩ := H (Over.homMk (restrictedMorphism G g) (hB.hom_ext _ _))
      ((isInvariant_iff_isInvariant_groupoidPreRelation hjt hjs _).2
        (restrictedMorphism_isInvariant G g))
    refine ⟨χ.left, (comp_associatedMap_eq_iff G f g _).2 (congrArg Over.Hom.left hχ),
      fun h' hh' => congrArg Over.Hom.left
        (huniq (Over.homMk h' (hB.hom_ext _ _))
          (Over.OverMorphism.ext ((comp_associatedMap_eq_iff G f g h').1 hh')))⟩

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a terminal base, let
`j = (t, s)` be its pre-relation and let `f : [U/R] ⟶ Y` be a 1-morphism to the category attached
to an algebraic space `Y`. Then `f` is a categorical moduli space exactly when its restriction
`φ : U ⟶ Y` along the projection is a categorical quotient of `j`. -/
@[stacks 0DUI "the non-uniform case, for a groupoid over the terminal base as in the source"]
theorem quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient (hB : IsTerminal B)
    (hjt : (Space.PreRelation.target j).left = G.target)
    (hjs : (Space.PreRelation.source j).left = G.source)
    (Y : AlgebraicSpaces C S hS)
    (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) :
    IsBasedCategoricalModuliSpace Y f ↔
      Space.IsCategoricalQuotient j
        (Over.homMk (restrictedMorphism G f) (hB.hom_ext _ _) :
          (Over.mk G.objectsToBase : Over B) ⟶ Over.mk (hB.from Y)) := by
  refine ⟨fun H => ⟨?_, fun Z ψ hψ => (factorization_iff hB hjt hjs Y f Z).1 (H Z.left) ψ hψ⟩,
    fun H W => (factorization_iff hB hjt hjs Y f (Over.mk (hB.from W))).2 fun ψ hψ => H.2 _ ψ hψ⟩
  exact (isInvariant_iff_isInvariant_groupoidPreRelation hjt hjs _).2
    (restrictedMorphism_isInvariant G f)

/-- Let `G` be a groupoid in algebraic spaces over a terminal base and let `f : [U/R] ⟶ Y` be a
1-morphism to the category attached to an algebraic space `Y`. Then `f` is a categorical moduli
space exactly when its restriction `φ : U ⟶ Y` along the projection is a categorical quotient of
the pre-relation `prod.lift t s` of `G`. -/
@[stacks 0DUI "the non-uniform case at the pre-relation (t, s) the groupoid cuts out"]
theorem quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient_prodLift
    (hB : IsTerminal B) (G : GroupoidInAlgebraicSpaces C S hS B)
    (Y : AlgebraicSpaces C S hS)
    (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) :
    IsBasedCategoricalModuliSpace Y f ↔
      Space.IsCategoricalQuotient
        (prod.lift (Over.homMk G.target G.target_over) (Over.homMk G.source G.source_over) :
          Space.PreRelation (Over.mk G.arrowsToBase) (Over.mk G.objectsToBase))
        (Over.homMk (restrictedMorphism G f) (hB.hom_ext _ _) :
          (Over.mk G.objectsToBase : Over B) ⟶ Over.mk (hB.from Y)) :=
  quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient hB
    (congrArg Over.Hom.left (prod.lift_fst _ _)) (congrArg Over.Hom.left (prod.lift_snd _ _)) Y f

/-- With the same data as
`AlgebraicGeometry.Stack.quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient` and a
full subcategory of the algebraic spaces, selected by a predicate `P` on objects and containing
the object and arrow spaces of the groupoid, `f` is a categorical moduli space in that
subcategory exactly when `φ` is a categorical quotient in it. -/
@[stacks 0DUI "the non-uniform case in a full subcategory, for a groupoid over the terminal base"]
theorem quotientStack_isCategoricalModuliSpaceIn_iff_isCategoricalQuotientIn (hB : IsTerminal B)
    (hjt : (Space.PreRelation.target j).left = G.target)
    (hjs : (Space.PreRelation.source j).left = G.source)
    (P : AlgebraicSpaces C S hS → Prop) (hR : P G.arrows) (hU : P G.objects)
    (Y : AlgebraicSpaces C S hS)
    (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val) :
    IsBasedCategoricalModuliSpaceIn P Y f ↔
      Space.IsCategoricalQuotientIn (fun Z : Over B => P Z.left) j
        (Over.homMk (restrictedMorphism G f) (hB.hom_ext _ _) :
          (Over.mk G.objectsToBase : Over B) ⟶ Over.mk (hB.from Y)) := by
  refine ⟨fun H => ⟨hR, hU, H.1, ?_, fun Z hZ ψ hψ =>
      (factorization_iff hB hjt hjs Y f Z).1 (H.2 Z.left hZ) ψ hψ⟩,
    fun H => ⟨H.2.2.1, fun W hW =>
      (factorization_iff hB hjt hjs Y f (Over.mk (hB.from W))).2
        fun ψ hψ => H.2.2.2.2 _ hW ψ hψ⟩⟩
  exact (isInvariant_iff_isInvariant_groupoidPreRelation hjt hjs _).2
    (restrictedMorphism_isInvariant G f)

end Comparison

end AlgebraicGeometry.Stack

end
