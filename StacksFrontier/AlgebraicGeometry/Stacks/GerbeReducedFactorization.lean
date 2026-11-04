module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedToResidualSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbeExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFactorizationDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedClosedSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackFactorization
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStackFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace

/-!
# A reduced stack over one point of a gerbe factors through a one-point substack

This is the last step of the proof of **Stacks 0H25**. Let `π : 𝒰 ⟶ 𝒱` make `𝒰` a gerbe over an
algebraic stack `𝒱` represented by an algebraic space `F` which is decent or locally Noetherian,
let `u` be a point of `𝒰` and let `g : 𝒴 ⟶ 𝒰` be a 1-morphism from a reduced algebraic stack all
of whose points map to `u`. Then `g` factors, up to a 2-isomorphism, through a 1-morphism
`𝒲 ⟶ 𝒰` hitting `u` whose source satisfies condition (2) of **Stacks 06MP**: it admits a
surjective flat 1-morphism, locally of finite presentation, from the spectrum of a field.

The source's argument, with its omitted details: the image `x̄` of `u` in `|F|` has a residual
space `Z ⟶ F` through which every morphism from a reduced algebraic space with image `{x̄}`
factors (**Stacks 0H1T** for decent `F`, **Stacks 0H1S** for locally Noetherian `F`). A reduced
smooth scheme atlas of `𝒴` maps to `F` with image `{x̄}`, so it factors through `Z`; that
factorization descends to `𝒴`
(`AlgebraicGeometry.Stack.exists_factorization_of_isMonomorphism_of_cover`), so `g` lifts to the
2-fibre product `𝒲₀ = 𝒰 ×_𝒱 Z`. That 2-fibre product is a gerbe over `Z` (**Stacks 06QE**), hence
has a single point lying over `u` and is locally Noetherian (**Stacks 06R6**, a gerbe being locally
of finite presentation). Its reduction `𝒲` (**Stacks 0509**) is reduced, locally Noetherian and has
one point, so it satisfies condition (2) of Stacks 06MP (**Stacks 06MP**), and `𝒴`, being reduced,
maps into it (**Stacks 050B**).

## Main results

* `AlgebraicGeometry.Space.exists_isResidualSpaceAt_forall_factorization`: a residual space
  through which every reduced algebraic space with singleton image factors, at a point of a decent
  or locally Noetherian algebraic space.
* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_algebraicSpaceStack`: the algebraic stack of
  a locally Noetherian algebraic space is locally Noetherian.
* `AlgebraicGeometry.Stack.exists_cover_factorization_of_isGerbeOver`: the factorization above.
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A residual space at a point of a decent or locally Noetherian algebraic space through which
every reduced algebraic space over the point factors (Stacks 0H1T, Stacks 0H1S).** Let `F` be an
algebraic space over `S` which is decent or locally Noetherian and let `x` be a point of `|F|`.
There is a residual space `i : Z ⟶ F` at `x` (**Stacks 06R0**) such that every morphism from a
reduced algebraic space whose image on points is contained in `{x}` factors through `i`.

For decent `F` the residual space is the monomorphic field-valued representative of `x` that
decency supplies, and the factorization is **Stacks 0H1T**; for locally Noetherian `F` it is any
residual space (**Stacks 06QZ**), and the factorization is **Stacks 0H1S**. -/
theorem exists_isResidualSpaceAt_forall_factorization
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (hcase : IsDecentSpace B S hS F ∨
      HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    ∃ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : Z ⟶ F), IsResidualSpaceAt B S hS F x i ∧
      ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ F),
        Set.range (pointsMap B S hS Y f) ⊆ {x} →
        HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T) →
        ∃ g : Y ⟶ Z, g ≫ i = f := by
  rcases hcase with hdec | hN
  · obtain ⟨p, hpx, hmono, hqc⟩ := hdec x
    exact ⟨_, fieldMorphism B S hS F p,
      isResidualSpaceAt_fieldMorphism_of_mono B S hS x p hpx hmono,
      fun Y hY f hf hred => exists_comp_fieldMorphism_eq_of_range_pointsMap_subset_singleton
        B S hS hF hY f x hf hred p hpx hmono hqc⟩
  · obtain ⟨Z, i, hi⟩ := exists_isResidualSpaceAt B S hS hF x
    exact ⟨Z, i, hi, fun Y hY f hf hred =>
      (existsUnique_comp_eq_of_isResidualSpaceAt B S hS hF hY f x i hi hf hred hN).exists⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The algebraic stack of a locally Noetherian algebraic space is locally Noetherian.** Its
identity 1-morphism is a smooth surjective algebraic-space atlas whose source has the étale-local
property, which is the algebraic-space form of the criterion of **Stacks 04YF**. -/
theorem isLocallyNoetherianStack_algebraicSpaceStack
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (h : Space.HasEtaleLocalProperty B S hS Z (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsLocallyNoetherianStack B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ) := by
  have : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  exact (exists_scheme_atlas_iff_exists_space_atlas B S hS _ _).2
    ⟨Z, hZ, 𝟙 _, isSurjective_id B S hS _, AlgebraicStacks.isSmooth_id B S hS _, h⟩

/-- **A 1-morphism into a strictly full substack, lifted.** A 1-morphism all of whose objects are
carried into the objects with a property `P` lifts strictly through the inclusion of the full
subcategory cut out by `P`. -/
def liftFullSubcategory {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒴.val.val.obj}
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hmem : ∀ ξ : 𝒳.val.val.obj, P (f.hom.hom.toFunctor.obj ξ)) :
    𝒳 ⟶ fullSubcategoryAlgebraicStack 𝒴 P hP :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := P.lift f.hom.hom.toFunctor hmem
      w := f.hom.hom.w })

/-- The lift composed with the inclusion is the given 1-morphism. -/
theorem liftFullSubcategory_comp {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒴.val.val.obj}
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hmem : ∀ ξ : 𝒳.val.val.obj, P (f.hom.hom.toFunctor.obj ξ)) :
    liftFullSubcategory B S hS f hP hmem ≫ fullSubcategoryInclusion 𝒴 P hP = f :=
  rfl

/-- The algebraic stack of an algebraic space with at most one point has at most one point. -/
theorem subsingleton_points_algebraicSpaceStack
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
    (hZsub : Subsingleton (Space.points B S hS Z)) :
    Subsingleton (AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ)) := by
  have hZbij := bijective_spacePointMap_representing B S hS Z
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val (StacksRepresentableCFG.EquivalenceOver.refl _)
  refine ⟨fun k k' => ?_⟩
  obtain ⟨v, rfl⟩ := hZbij.2 k
  obtain ⟨v', rfl⟩ := hZbij.2 k'
  exact congrArg _ (hZsub.elim v v')

/-- A scheme chart of a 1-morphism all of whose points map to the image of `x` has image `{x}`
on points of the representing algebraic space. -/
theorem range_pointsMap_representingMap_subset_singleton {𝒴 𝒱 : AlgebraicStacks.{u, w} B S hS}
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : BigFppfOver B S hS) (b : schemeStack.{u, w} B S hS U ⟶ 𝒴) (f : 𝒴 ⟶ 𝒱)
    (x : Space.points B S hS F) (v : AlgebraicStacks.points B S hS 𝒱)
    (hx : spacePointMap B S hS F 𝒱.val (representingEquivalence B S hS F 𝒱.val eF).functor x = v)
    (hf : ∀ y, AlgebraicStacks.pointsMap B S hS f y = v) :
    Set.range (Space.pointsMap B S hS (yoneda.obj U)
      (representingMap B S hS (schemeStack.{u, w} B S hS U).val 𝒱.val (yoneda.obj U) F
        (representedChart B S hS U) eF (b ≫ f).hom)) ⊆ {x} := by
  rintro _ ⟨τ, rfl⟩
  refine (bijective_spacePointMap_representing B S hS F 𝒱.val eF).1
    ((spacePointMap_representing_naturality B S hS (yoneda.obj U) F
      (schemeStack.{u, w} B S hS U).val 𝒱.val (representedChart B S hS U) eF
      (b ≫ f).hom τ).trans ?_)
  rw [hx]
  show AlgebraicStacks.pointsMap B S hS (b ≫ f) _ = _
  rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hf]

/-- The source of a gerbe over an algebraic stack with at most one point has at most one point. -/
theorem subsingleton_points_of_isGerbeOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsGerbeOver B S hS f)
    (h : Subsingleton (AlgebraicStacks.points B S hS 𝒴)) :
    Subsingleton (AlgebraicStacks.points B S hS 𝒳) :=
  ⟨fun _ _ => injective_pointsMap_of_isGerbeOver B S hS f hf (h.elim _ _)⟩

/-- The source of a gerbe over a locally Noetherian algebraic stack is locally Noetherian. -/
theorem isLocallyNoetherianStack_of_isGerbeOver {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsGerbeOver B S hS f)
    (h : IsLocallyNoetherianStack B S hS 𝒴) : IsLocallyNoetherianStack B S hS 𝒳 :=
  AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f
    (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver B S hS f hf).2) h

/-- **A reduced stack mapping to a locally Noetherian stack with one point factors through its
reduction.** The reduction `j : 𝒲 ⟶ 𝒳` of a locally Noetherian algebraic stack `𝒳` with at most
one point is reduced, locally Noetherian with a unique point over any given point of `𝒳`, and
every 1-morphism from a reduced algebraic stack lifts strictly through `j`. -/
theorem exists_reducedLocallyNoetherianWithUniquePoint_lift
    {𝒴 𝒳 : AlgebraicStacks.{u, w} B S hS} (hsub : Subsingleton (AlgebraicStacks.points B S hS 𝒳))
    (hnoeth : IsLocallyNoetherianStack B S hS 𝒳) (p₀ : AlgebraicStacks.points B S hS 𝒳)
    (L : 𝒴 ⟶ 𝒳) (hred : IsReducedStack B S hS 𝒴) :
    ∃ (𝒲 : AlgebraicStacks.{u, w} B S hS) (j : 𝒲 ⟶ 𝒳),
      IsReducedLocallyNoetherianWithUniquePoint B S hS 𝒲 ∧
        (∃ w, AlgebraicStacks.pointsMap B S hS j w = p₀) ∧ ∃ l : 𝒴 ⟶ 𝒲, l ≫ j = L := by
  obtain ⟨R, hRclosed, hRspec⟩ := exists_reduction.{u, w} B S hS 𝒳
  obtain ⟨-, hRalg, -⟩ := id hRclosed
  obtain ⟨hRred, hRsurj⟩ := hRspec hRalg
  have hjinj := pointsMap_injective_of_fullyFaithful B S hS
    (fullSubcategoryInclusion 𝒳 R hRalg)
  obtain ⟨w₀, hw₀⟩ := hRsurj p₀
  have : R.IsClosedUnderIsomorphisms := hRclosed.1
  exact ⟨_, fullSubcategoryInclusion 𝒳 R hRalg,
    ⟨⟨hRred, ⟨w₀⟩, ⟨fun _ _ => hjinj (hsub.elim _ _)⟩⟩,
      isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 R hRclosed hRalg hnoeth⟩,
    ⟨w₀, hw₀⟩, liftFullSubcategory B S hS L hRalg ((factorsThroughSubstack_iff_forall L).1
      ((factorsThroughSubstack_iff_range_pointsMap_subset B S hS L hRclosed hRalg hred).2
        fun q _ => hRsurj q)), liftFullSubcategory_comp B S hS L hRalg _⟩

/-- **A reduced stack over one point lifts through a monomorphism onto a residual space.** Let
`a : 𝒦 ⟶ 𝒱` be a monomorphism of algebraic stacks represented by `i : Z ⟶ F`, through which every
reduced algebraic space over `x ∈ |F|` factors. Then every 1-morphism `f : 𝒴 ⟶ 𝒱` from a reduced
algebraic stack all of whose points map to the image of `x` lifts through `a` up to a
2-isomorphism: a reduced scheme atlas of `𝒴` factors through `Z`, and that factorization
descends. -/
theorem exists_lift_of_isMonomorphism_of_forall_factorization
    {𝒴 𝒦 𝒱 : AlgebraicStacks.{u, w} B S hS} (Z F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eZ : StacksRepresentableCFG.EquivalenceOver 𝒦.val.val.p
      (presheafOfCategories (Z ⋙ typeToCat)).p)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (i : Z ⟶ F) (a : 𝒦 ⟶ 𝒱) (ha : AlgebraicStacks.IsMonomorphism B S hS a)
    (ha' : representingMap B S hS 𝒦.val 𝒱.val Z F eZ eF a.hom = i) (x : Space.points B S hS F)
    (hfac : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hY : IsAlgebraicSpace B S hS Y)
      (f : Y ⟶ F), Set.range (Space.pointsMap B S hS Y f) ⊆ {x} →
        Space.HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T) →
        ∃ g : Y ⟶ Z, g ≫ i = f)
    (v : AlgebraicStacks.points B S hS 𝒱)
    (hx : spacePointMap B S hS F 𝒱.val (representingEquivalence B S hS F 𝒱.val eF).functor x = v)
    (f : 𝒴 ⟶ 𝒱) (hf : ∀ y, AlgebraicStacks.pointsMap B S hS f y = v)
    (hred : IsReducedStack B S hS 𝒴) :
    ∃ g : 𝒴 ⟶ 𝒦, Nonempty (g ≫ a ≅ f) := by
  obtain ⟨U, b, hbsurj, hbsm, hUred⟩ := hred
  obtain ⟨g', hg'⟩ := hfac (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) _
    (range_pointsMap_representingMap_subset_singleton B S hS F eF U b f x v hx hf)
    ((Space.exists_atlas_iff_of_representable B S hS (yoneda.obj U)
      (fun T : Scheme.{u} => IsReduced T) U (Iso.refl _)).mpr hUred)
  obtain ⟨c', hc'⟩ := exists_oneMorphism_representingMap_eq' B S hS
    (schemeStack.{u, w} B S hS U).val 𝒦.val (yoneda.obj U) Z (representedChart B S hS U) eZ g'
  let c : schemeStack.{u, w} B S hS U ⟶ 𝒦 := Bicategory.InducedBicategory.mkHom c'
  have hca : representingMap B S hS (schemeStack.{u, w} B S hS U).val 𝒱.val (yoneda.obj U) F
      (representedChart B S hS U) eF (c ≫ a).hom = representingMap B S hS
        (schemeStack.{u, w} B S hS U).val 𝒱.val (yoneda.obj U) F (representedChart B S hS U) eF
        (b ≫ f).hom := by
    show representingMap B S hS _ _ (yoneda.obj U) F (representedChart B S hS U) eF
      (c' ≫ a.hom) = _
    rw [representingMap_comp B S hS (yoneda.obj U) Z F (representedChart B S hS U) eZ eF, hc',
      ha', hg']
  obtain ⟨⟨η₀⟩⟩ := nonempty_unique_twoIso_of_representingMap_eq B S hS _ _ (yoneda.obj U) F
    (representedChart B S hS U) eF hca
  exact exists_factorization_of_isMonomorphism_of_cover B S hS f a ha U b
    (AlgebraicStacks.isFlat_of_isSmooth B S hS b hbsm)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS b hbsm) hbsurj c
    (Bicategory.InducedBicategory.isoMk η₀.default)

/-- **A reduced stack over one point of a gerbe over an algebraic space factors through a stack
covered by the spectrum of a field.** Let `π : 𝒰 ⟶ 𝒱` make `𝒰` a gerbe over an algebraic stack
`𝒱` represented by an algebraic space `F` which is decent or locally Noetherian, let `u` be a point
of `𝒰` and let `g : 𝒴 ⟶ 𝒰` be a 1-morphism from a reduced algebraic stack all of whose points map
to `u`. Then there are an algebraic stack `𝒲` satisfying condition (2) of **Stacks 06MP**, a
1-morphism `h : 𝒲 ⟶ 𝒰` some point of which maps to `u`, and a 1-morphism `a : 𝒴 ⟶ 𝒲` with
`a ≫ h ≅ g`.

This is the gerbe case of the proof of **Stacks 0H25**: the factorization of a reduced scheme
atlas of `𝒴` through a residual space of `F` (**Stacks 0H1T**, **Stacks 0H1S**) descends to `𝒴`,
lifting `g` to the base change of the residual space along `π`, which is a gerbe over it
(**Stacks 06QE**); `𝒲` is the reduction (**Stacks 0509**) of that base change. -/
theorem exists_cover_factorization_of_isGerbeOver
    {𝒴 𝒰 𝒱 : AlgebraicStacks.{u, w} B S hS} (π : 𝒰 ⟶ 𝒱)
    (hπ : AlgebraicStacks.IsGerbeOver B S hS π)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒱.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (hcase : Space.IsDecentSpace B S hS F ∨
      Space.HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (u : AlgebraicStacks.points B S hS 𝒰) (g : 𝒴 ⟶ 𝒰)
    (hg : ∀ y, AlgebraicStacks.pointsMap B S hS g y = u) (hred : IsReducedStack B S hS 𝒴) :
    ∃ (𝒲 : AlgebraicStacks.{u, w} B S hS) (h : 𝒲 ⟶ 𝒰),
      HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒲 ∧
        (∃ w, AlgebraicStacks.pointsMap B S hS h w = u) ∧
          ∃ a : 𝒴 ⟶ 𝒲, Nonempty (a ≫ h ≅ g) := by
  classical
  -- The point of `F` below `u`, and a residual space there.
  obtain ⟨xbar, hxbar⟩ := (bijective_spacePointMap_representing B S hS F 𝒱.val eF).2
    (AlgebraicStacks.pointsMap B S hS π u)
  obtain ⟨Z, i, hi, hfac⟩ := Space.exists_isResidualSpaceAt_forall_factorization B S hS hF xbar
    hcase
  obtain ⟨hZ, hmono, -, hZnoeth, ⟨z₀⟩, hZsub, hZover⟩ := hi
  -- The algebraic stack of `Z` and the monomorphism `a` inducing `i`.
  set 𝒦 : AlgebraicStacks.{u, w} B S hS := algebraicSpaceStack.{u, w} B S hS Z hZ
  let eZ : StacksRepresentableCFG.EquivalenceOver 𝒦.val.val.p
    (presheafOfCategories (Z ⋙ typeToCat)).p := StacksRepresentableCFG.EquivalenceOver.refl _
  obtain ⟨a', ha'⟩ := exists_oneMorphism_representingMap_eq' B S hS 𝒦.val 𝒱.val Z F eZ eF i
  let a : 𝒦 ⟶ 𝒱 := Bicategory.InducedBicategory.mkHom a'
  have ha : AlgebraicStacks.IsMonomorphism B S hS a :=
    AlgebraicStacks.isMonomorphism_of_mono_representingMap B S hS a Z F hZ hF eZ eF
      (by rwa [ha'])
  let k₀ : AlgebraicStacks.points B S hS 𝒦 :=
    spacePointMap B S hS Z 𝒦.val (representingEquivalence B S hS Z 𝒦.val eZ).functor z₀
  have hk₀ : AlgebraicStacks.pointsMap B S hS a k₀ = AlgebraicStacks.pointsMap B S hS π u := by
    have hnat := spacePointMap_representing_naturality B S hS Z F 𝒦.val 𝒱.val eZ eF a' z₀
    rw [ha', hZover z₀, hxbar] at hnat
    exact hnat.symm
  -- The factorization of `g ≫ π` through `a`, from a reduced smooth scheme atlas of `𝒴`.
  obtain ⟨g₁, ⟨η₁⟩⟩ := exists_lift_of_isMonomorphism_of_forall_factorization B S hS Z F eZ eF i
    a ha ha' xbar hfac _ hxbar (g ≫ π)
    (fun y => by rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hg]) hred
  -- The lift of `g` to the base change `𝒰 ×_𝒱 𝒦`.
  set P := twoFibreProductSquareAlgebraicStacks B S hS π a with hPdef
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS π a
  let L := Bicategory.twoFibreProductPreHom hP
    { pt := 𝒴, fst := g, snd := g₁, iso := η₁.symm }
  -- The base change is a gerbe over `𝒦`: one point, over `u`, and locally Noetherian.
  have hsnd : AlgebraicStacks.IsGerbeOver B S hS P.snd :=
    AlgebraicStacks.isGerbeOver_of_isTwoFibreProduct B S hS P hP hπ
  obtain ⟨p₀, hp₀, -⟩ :=
    exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP u k₀ hk₀.symm
  -- Its reduction, into which `𝒴` maps.
  obtain ⟨𝒲, j, h𝒲, ⟨w₀, hw₀⟩, l, hl⟩ := exists_reducedLocallyNoetherianWithUniquePoint_lift B S hS
    (subsingleton_points_of_isGerbeOver B S hS P.snd hsnd
      (subsingleton_points_algebraicSpaceStack.{u, w} B S hS Z hZ hZsub))
    (isLocallyNoetherianStack_of_isGerbeOver B S hS P.snd hsnd
      (isLocallyNoetherianStack_algebraicSpaceStack B S hS Z hZ hZnoeth))
    p₀ L.hom hred
  refine ⟨𝒲, j ≫ P.fst, hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian
    B S hS 𝒲 h𝒲, ⟨w₀, ?_⟩, l, ⟨?_⟩⟩
  · rwa [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hw₀]
  · exact (Bicategory.associator l j P.fst).symm ≪≫ eqToIso (by rw [hl]) ≪≫ L.isoFst.symm

end AlgebraicGeometry.Stack
