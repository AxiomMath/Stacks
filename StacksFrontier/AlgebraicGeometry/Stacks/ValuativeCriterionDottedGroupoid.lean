module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondRelativeDiagonalInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniqueness
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Dotted arrows for a 1-morphism with separated relative diagonal (Stacks 0CLC)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` of a big fppf site `B`.
Stacks 0CLC asserts that the category of dotted arrows of a 2-commutative square for `f` is a
groupoid, and that it is a setoid as soon as the relative diagonal `Δ_f` is separated.

An automorphism of a dotted arrow `(a, α, β)` is a 2-morphism `θ : a ⟶ a` with
`β = (id_f ⋆ θ) ∘ β` and `α = α ∘ (θ ⋆ id_j)`. The first condition says that `θ` defines a
1-morphism into the relative inertia `I_{𝒳/𝒴}` over `a`, the second that its restriction along
the generic point is the identity. Pulling the neutral section `e : 𝒳 ⟶ I_{𝒳/𝒴}` back along that
1-morphism gives a closed immersion into the spectrum of the valuation ring whose image contains
the generic point; since that spectrum is reduced and the generic point is dominant, the closed
immersion is an isomorphism, so `θ` is the identity.

## Main results

* `AlgebraicGeometry.Stack.isClosedImmersion_relativeInertiaNeutralSection_of_isSeparated`:
  **Stacks 0CL0, part (1), (b) ⇒ (c)** — a separated relative diagonal makes the neutral section
  `e : 𝒳 ⟶ I_{𝒳/𝒴}` a closed immersion.
* `AlgebraicGeometry.Stack.isSetoidCategory_dottedArrow_of_isSeparated_relativeDiagonal`:
  **Stacks 0CLC**, the setoid assertion.

## References

* [Stacks Project, Tag 0CLC](https://stacks.math.columbia.edu/tag/0CLC)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
* [Stacks Project, Tag 04YS](https://stacks.math.columbia.edu/tag/04YS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Products of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_ValuativeCriterionDottedGroupoid
    (J : Type) : Limits.HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ValuativeCriterionDottedGroupoid :
    Limits.HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-! ### Closed immersions through which a dominant morphism factors -/

/-- A closed immersion with reduced target through which a dominant morphism factors is an
isomorphism: the factorisation makes it dominant, hence scheme-theoretically dominant since the
target is reduced, so its kernel ideal sheaf vanishes. -/
@[sga "3 VIII 7.1" "partial"]
theorem isIso_of_isClosedImmersion_of_isDominant_factor
    {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Z ⟶ Y)
    [IsReduced Y] [IsDominant j] [AlgebraicGeometry.IsClosedImmersion i]
    (l : X ⟶ Z) (hl : l ≫ i = j) : IsIso i := by
  have : IsDominant (l ≫ i) := hl ▸ ‹IsDominant j›
  have : IsDominant i := IsDominant.of_comp l i
  have : IsSchemeTheoreticallyDominant i := IsSchemeTheoreticallyDominant.of_isDominant i
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (IsSchemeTheoreticallyDominant.ker_eq_bot i)

/-- **A closed immersion of algebraic spaces into a reduced object of the site through which a
dominant morphism factors has a section.** The morphism `p` is representable, so the base change
of `p` along the identity of `U` is a morphism `i` of the site whose underlying morphism of
schemes is a closed immersion; the section `s` of `p` over `V` factors `j` through `i`, so `i` is
an isomorphism and its inverse composed with the projection is the wanted section. -/
theorem exists_section_of_isClosedImmersion_of_isDominant
    {U V : BigFppfOver B S hS} (j : V ⟶ U)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj U)]
    [IsDominant ((BigFppfOver.toScheme B S hS).map j)]
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : F ⟶ yoneda.obj U) (hp : Space.IsClosedImmersion B S hS p)
    (s : F.obj (.op V)) (hs : p.app (.op V) s = j) :
    ∃ t : F.obj (.op U), p.app (.op U) t = 𝟙 U := by
  let T := BigFppfOver.toScheme B S hS
  let i := hp.rep.snd (𝟙 (yoneda.obj U))
  let q := hp.rep.fst (𝟙 (yoneda.obj U))
  have : AlgebraicGeometry.IsClosedImmersion (T.map i) :=
    hp.property_snd (𝟙 (yoneda.obj U))
  have hs' : yonedaEquiv.symm s ≫ p = yoneda.map j ≫ 𝟙 _ := by
    apply yonedaEquiv.injective
    show p.app (.op V) (F.map (𝟙 V).op s) = (𝟙 V) ≫ j
    simpa using hs
  let l := hp.rep.lift (yonedaEquiv.symm s) j hs'
  have hl : l ≫ i = j := hp.rep.lift_snd _ _ _
  have : IsIso (T.map i) := isIso_of_isClosedImmersion_of_isDominant_factor
    (T.map j) (T.map i) (T.map l) (by rw [← T.map_comp, hl])
  have : IsIso i := isIso_of_reflects_iso i T
  refine ⟨(yoneda.map (inv i) ≫ q).app (.op U) (𝟙 U), ?_⟩
  have hq : q ≫ p = yoneda.map i := by
    simpa [q, i] using hp.rep.w (𝟙 (yoneda.obj U))
  have hh : (yoneda.map (inv i) ≫ q) ≫ p = 𝟙 _ := by
    rw [Category.assoc, hq, ← yoneda.map_comp, IsIso.inv_hom_id]
    exact yoneda.map_id _
  exact congrArg (fun k => k.app (.op U) (𝟙 U)) hh

/-- **The relocalised form of `exists_section_of_isClosedImmersion_of_isDominant`.** If the
algebraic space `F` over the slice at `U` represents a closed immersion over `U`, and `F` has a
section over the object `Over.mk j.left` of that slice, then it has a section over the unit
object, provided `U` is reduced and `j` is dominant. -/
theorem nonempty_section_of_isClosedImmersion_of_isDominant
    {U V : BigFppfOver B S hS} (j : V ⟶ U)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj U)]
    [IsDominant ((BigFppfOver.toScheme B S hS).map j)]
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hp : Space.IsClosedImmersion B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (s : F.obj (.op (Over.mk j.left))) :
    Nonempty (F.obj (.op (Over.mk (𝟙 U.left)))) := by
  let G := spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom
  let A : AlgebraicSpaces B U.left.1 U.left.2 := ⟨F, hF⟩
  let i := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app A
  let z : ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (.op V) := ⟨⟨j.left, s⟩, j.w⟩
  have hz : ((G.obj A).1.hom.app (.op V)) (i.inv.app (.op V) z) = j :=
    spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom A
      (.op V) z
  obtain ⟨t, ht⟩ := exists_section_of_isClosedImmersion_of_isDominant B S hS j _ hp
    (i.inv.app (.op V) z) hz
  let z' := i.hom.app (.op U) t
  have hφ : z'.1.1 = 𝟙 U.left := congrArg (fun g => g.left) ht
  exact ⟨hφ ▸ z'.1.2⟩

/-! ### Sections of the relative inertia -/

/-- An object of the relative inertia isomorphic to a value of the neutral section has trivial
automorphism. -/
theorem relativeInertia_auto_eq_id_of_iso_neutralSection
    {X Y : Type*} [Category X] [Category Y] {f : X ⥤ Y}
    {A : RelativeInertia f} {x : X}
    (e : A ≅ (RelativeInertia.neutralSection f).obj x) :
    A.auto.asIso.hom = 𝟙 A.obj := by
  have hiso : IsIso ((RelativeInertia.π f).map e.hom) := inferInstance
  have : IsIso e.hom.hom := hiso
  apply (cancel_mono e.hom.hom).1
  simpa [RelativeInertia.neutralSection] using e.hom.comm.symm

/-- **A section of the base change of the neutral section is the triviality of an automorphism.**
Let `y` be a 1-morphism into the relative inertia of `f` over `p`, and let `F` represent the
2-fibre product of `y` with the neutral section. Then `F` has a section over an object `V`
exactly when the automorphism `y` attaches to `V` is the identity. -/
theorem nonempty_relativeInertia_section_iff
    {C T X Y : Type*} [Category C] [Category T] [Category X] [Category Y]
    (p : C ⥤ T) (q : X ⥤ T) (f : X ⥤ Y)
    (y : C ⥤ RelativeInertia f) (hy : y ⋙ RelativeInertia.π f ⋙ q = p)
    (F : Cᵒᵖ ⥤ Type*)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst p q (RelativeInertia.π f ⋙ q) y
        (RelativeInertia.neutralSection f))
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (V : C) :
    Nonempty (F.obj (.op V)) ↔ (y.obj V).auto.asIso.hom = 𝟙 (y.obj V).obj := by
  constructor
  · rintro ⟨s⟩
    let t : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨V, Discrete.mk s⟩
    let A := e.inv.functor.obj t
    have hA : A.x = V := congrArg (fun G => G.obj t) e.inv.w
    have h := relativeInertia_auto_eq_id_of_iso_neutralSection A.iso
    change (y.obj A.x).auto.asIso.hom = 𝟙 (y.obj A.x).obj at h
    rwa [hA] at h
  · intro h
    let i : y.obj V ≅ (RelativeInertia.neutralSection f).obj (y.obj V).obj :=
      { hom := ⟨𝟙 _, by simpa [RelativeInertia.neutralSection] using h.symm⟩
        inv := ⟨𝟙 _, by simpa [RelativeInertia.neutralSection] using h⟩
        hom_inv_id := RelativeInertiaHom.ext (by simp [RelativeInertia.neutralSection])
        inv_hom_id := RelativeInertiaHom.ext (by simp [RelativeInertia.neutralSection]) }
    have hbase : (RelativeInertia.π f ⋙ q).obj (y.obj V) = p.obj V :=
      congrArg (fun G => G.obj V) hy
    let A : TwoFibreProductOver p q (RelativeInertia.π f ⋙ q) y
        (RelativeInertia.neutralSection f) :=
      { base := p.obj V
        x := V
        y := (y.obj V).obj
        hx := rfl
        hy := hbase
        iso := i
        vertical := IsHomLift.of_fac' _ _ _ hbase hbase (by
          rw [Category.id_comp, eqToHom_trans]
          exact q.map_id _) }
    let t := e.hom.functor.obj A
    have ht : t.base = V := congrArg (fun G => G.obj A) e.hom.w
    have s : F.obj (.op t.base) := t.fiber.as
    exact ⟨ht ▸ s⟩

/-! ### Automorphisms of dotted arrows -/

/-- A 2-morphism of 1-morphisms out of a slice which is the identity at the unit object is the
identity: this is the faithfulness half of the 2-Yoneda lemma. -/
theorem basedNatTrans_eq_id_of_app_unit
    {C : Type*} [Category C] {X : BasedCategory C}
    (hX : X.p.IsFiberedInGroupoids) (U : C)
    (a : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X) (θ : a ⟶ a)
    (hθ : θ.app (Over.mk (𝟙 U)) = 𝟙 (a.obj (Over.mk (𝟙 U)))) :
    θ = 𝟙 a := by
  have := CategoryTheory.Functor.twoYonedaEvaluation_faithful X.p hX U
  exact (CategoryTheory.Functor.twoYonedaEvaluation X.p U).map_injective
    (CategoryTheory.Functor.Fiber.hom_ext hθ)

/-- A natural endomorphism which is the identity at an object is the identity at every object
isomorphic to it. -/
private theorem natTrans_app_eq_id_of_iso {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (θ : F ⟶ F) {X Y : C} (k : X ≅ Y) (h : θ.app X = 𝟙 _) : θ.app Y = 𝟙 _ := by
  have hk := θ.naturality k.hom
  rw [h, Category.id_comp] at hk
  rw [← cancel_epi (F.map k.hom), hk, Category.comp_id]

section FibredInGroupoids

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **An automorphism of a 1-morphism out of a slice which lies in the relative inertia and is
trivial along a dominant morphism is trivial.** Let `e : 𝒳 ⟶ I_{𝒳/𝒴}` be a closed immersion, let
`U` be a reduced object of the site and `j : V ⟶ U` dominant, and let `θ` be a 2-morphism of a
1-morphism `a : U ⟶ 𝒳` which `f` sends to an identity and whose value at `j` is an identity. Then
`θ` is the identity.

The data of `θ` is a 1-morphism `y : U ⟶ I_{𝒳/𝒴}` lifting `a`; the base change of `e` along `y`
is a closed immersion with a section over `V`, hence by
`AlgebraicGeometry.Stack.nonempty_section_of_isClosedImmersion_of_isDominant` has a section over
`U`, which says that `θ` is an identity at the unit object. The 2-Yoneda lemma then makes `θ` the
identity. -/
theorem eq_id_of_isClosedImmersion_relativeInertiaNeutralSection (f : 𝒳 ⟶ 𝒴)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS
      (relativeInertiaNeutralSection B S hS f).hom)
    (hci : IsClosedImmersion B S hS (relativeInertiaNeutralSection B S hS f))
    {U V : BigFppfOver B S hS} (j : V ⟶ U)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj U)]
    [IsDominant ((BigFppfOver.toScheme B S hS).map j)]
    (a : schemeFibredCategory B S hS U ⟶ 𝒳) (θ : a ⟶ a)
    (hθ : ∀ t, f.hom.toFunctor.map (θ.hom.app t) = 𝟙 (f.hom.toFunctor.obj (a.hom.obj t)))
    (hj : θ.hom.app (Over.mk j) = 𝟙 (a.hom.obj (Over.mk j))) : θ = 𝟙 a := by
  let J := Over.iteratedSliceBackward U
  have hθapp (t) : IsIso (θ.hom.app t) :=
    𝒳.property.isIso_of_isHomLift_id (θ.hom.app t) (θ.hom.app_isHomLift t)
  let y : BigFppfOver B U.left.1 U.left.2 ⥤ RelativeInertia f.hom.toFunctor :=
    { obj := fun t => ⟨a.hom.obj (J.obj t),
        .of (@asIso _ _ _ _ (θ.hom.app (J.obj t)) (hθapp (J.obj t))), hθ _⟩
      map := fun g => ⟨a.hom.map (J.map g), θ.hom.toNatTrans.naturality (J.map g)⟩
      map_id := fun t => RelativeInertiaHom.ext (by
        rw [J.map_id]
        exact a.hom.toFunctor.map_id (J.obj t))
      map_comp := fun g k => RelativeInertiaHom.ext (by
        rw [J.map_comp]
        exact a.hom.toFunctor.map_comp (J.map g) (J.map k)) }
  have hw : J ⋙ a.hom.toFunctor ⋙ 𝒳.val.p = Over.map U.hom :=
    (congrArg (fun G => J ⋙ G) a.hom.w).trans (Over.iteratedSliceBackward_forget U)
  have hy : y ⋙ RelativeInertia.π f.hom.toFunctor ⋙ 𝒳.val.p = Over.map U.hom := hw
  obtain ⟨F, hF, ⟨e⟩⟩ := hrep U y hy
  have hp := hci U y hy F hF ⟨e⟩
  have key := nonempty_relativeInertia_section_iff (Over.map U.hom) 𝒳.val.p
    f.hom.toFunctor y hy F e
  have hs : Nonempty (F.obj (.op (Over.mk j.left))) := by
    apply (key _).2
    show θ.hom.app (J.obj (Over.mk j.left)) = 𝟙 _
    exact natTrans_app_eq_id_of_iso θ.hom.toNatTrans
      ((Over.iteratedSliceEquiv U).unitIso.app (Over.mk j)) hj
  obtain ⟨s⟩ := hs
  have ht := nonempty_section_of_isClosedImmersion_of_isDominant B S hS j F hF hp s
  have ht' : θ.hom.app (J.obj (Over.mk (𝟙 U.left))) = 𝟙 _ :=
    (key _).1 ht
  apply Bicategory.InducedBicategory.hom₂_ext
  apply basedNatTrans_eq_id_of_app_unit 𝒳.property U a.hom θ.hom
  exact natTrans_app_eq_id_of_iso θ.hom.toNatTrans
    ((Over.iteratedSliceEquiv U).unitIso.app (Over.mk (𝟙 U))).symm ht'

end FibredInGroupoids

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-! ### Stacks 0CL0, part (1), and Stacks 0CLC -/

/-- **Stacks 0CL0, part (1), (b) ⇒ (c).** If the relative diagonal `Δ_f` of a 1-morphism of
algebraic stacks is separated in the sense of Stacks 04XB, then the neutral section
`e : 𝒳 ⟶ I_{𝒳/𝒴}` of the relative inertia is a closed immersion in that sense.

This is Stacks 04YS, conditions (1) and (2), read at `Δ_f` — whose representability hypothesis is
automatic — followed by the identification of the second relative diagonal `Δ_{f, 2}` with the
neutral section. -/
theorem isClosedImmersion_relativeInertiaNeutralSection_of_isSeparated (f : 𝒳 ⟶ 𝒴)
    (hf : IsSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)) :
    IsClosedImmersion B S hS (relativeInertiaNeutralSection B S hS f.hom) :=
  (isClosedImmersion_secondRelativeDiagonal_iff_neutralSection B S hS f.hom).mp
    ((isSeparated_iff_isClosedImmersion_relativeDiagonal B S hS
      (relativeDiagonalAlgebraicStacks B S hS f)
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).mp hf)

/-- **Stacks 0CLC, the setoid assertion.** If the relative diagonal `Δ_f` of a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is separated in the sense of Stacks 04XB, then the
category of dotted arrows of every valuative diagram for `f` is a setoid.

The category is a groupoid because the 2-category of categories fibred in groupoids is locally
groupoidal, so only the triviality of automorphisms is at issue. The two compatibility conditions
on an automorphism `θ` of a dotted arrow say that `θ` lies in the relative inertia of `f` and is
trivial at the generic point; separatedness of `Δ_f` makes the neutral section of the relative
inertia a closed immersion, and
`AlgebraicGeometry.Stack.eq_id_of_isClosedImmersion_relativeInertiaNeutralSection` concludes,
the spectrum of a valuation ring being reduced and its generic point dominant. -/
@[stacks 0CLC "setoid"]
theorem isSetoidCategory_dottedArrow_of_isSeparated_relativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hf : IsSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom))
    (D : ValuativeDiagram B S hS 𝒳 𝒴 f) :
    IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) := by
  let := D.ring
  let := D.domain
  have hred : IsReduced ((BigFppfOver.toScheme B S hS).obj D.whole) :=
    isReduced_of_isOpenImmersion D.whole_iso.hom
  have hgen : IsDominant
      (Spec.map (CommRingCat.ofHom (algebraMap D.R (FractionRing D.R)))) := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (algebraMap D.R (FractionRing D.R)))
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).mp
        (IsFractionRing.injective D.R (FractionRing D.R))).le.trans bot_le)
  have hj : IsDominant ((BigFppfOver.toScheme B S hS).map D.inclusion) := by
    rw [D.inclusion_spec]
    infer_instance
  have hci := isClosedImmersion_relativeInertiaNeutralSection_of_isSeparated B S hS f hf
  have hrep := (isRepresentableByAlgebraicSpaces_secondRelativeDiagonal_iff_neutralSection
    B S hS f.hom).mp
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
        (relativeDiagonalAlgebraicStacks B S hS f))
  refine ⟨fun _ => inferInstance, fun a θ => ?_⟩
  apply CategoryTheory.DottedArrow.Hom.ext
  show θ.θ = 𝟙 a.a
  have hβiso : IsIso a.β := (CatFiberedInGroupoids.homGroupoid _ _).all_isIso a.β
  have hαiso : IsIso a.α := (CatFiberedInGroupoids.homGroupoid _ _).all_isIso a.α
  have hβ : θ.θ ▷ f.hom = 𝟙 (a.a ≫ f.hom) := by
    apply (cancel_epi a.β).1
    simpa using θ.cond_β.symm
  have hα : D.j ◁ θ.θ = 𝟙 (D.j ≫ a.a) := by
    apply (cancel_mono a.α).1
    simpa using θ.cond_α.symm
  refine eq_id_of_isClosedImmersion_relativeInertiaNeutralSection B S hS f.hom hrep hci
    D.inclusion a.a θ.θ (fun t => congrArg (fun η => η.hom.app t) hβ) ?_
  have h := congrArg (fun η => η.hom.app (Over.mk (𝟙 D.generic))) hα
  change θ.θ.hom.app (D.j.hom.toFunctor.obj (Over.mk (𝟙 D.generic))) = 𝟙 _ at h
  rw [D.j_canonical] at h
  change θ.θ.hom.app (Over.mk ((𝟙 D.generic) ≫ D.inclusion)) = 𝟙 _ at h
  rwa [Category.id_comp] at h

end AlgebraicGeometry.Stack

end
