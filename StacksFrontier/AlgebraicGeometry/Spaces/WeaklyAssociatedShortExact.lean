module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated

/-!
# Weakly associated points in a short exact sequence on an algebraic space

Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of `𝒪_X`-modules on an algebraic space
`X`. Every weakly associated point of `F₁` is weakly associated to `F₂`, and every weakly
associated point of `F₂` is weakly associated to `F₁` or to `F₃`.

## Main results

* `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_of_shortExact`:
  `WeakAss(F₁) ⊆ WeakAss(F₂)`.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_subset_union_of_shortExact`:
  `WeakAss(F₂) ⊆ WeakAss(F₁) ∪ WeakAss(F₃)`.

## Implementation notes

Both inclusions are read at a geometric point `x̄` above the given point, where they become the
module-theoretic inclusions `Module.weaklyAssociatedPrimes_subset_of_injective` and
`Module.weaklyAssociatedPrimes_subset_union_of_exact` of Stacks 0548 for the geometric stalks.
The source states the lemma for quasi-coherent modules; quasi-coherence is used nowhere in that
argument, so neither statement below carries it.

`AlgebraicGeometry.Space.geometricModuleStalk` is the stalk at the point of the small étale site
determined by `x̄`, with its scalars extended along
`AlgebraicGeometry.Space.pointStalkRingEquiv`. `Stacks.moduleStalkLargeMap` is the functoriality
of `Stacks.moduleStalkLarge` in the module, which the definition of the geometric stalk does not
provide; injectivity and exactness reach it from the corresponding statements on sections
because the stalk is a filtered colimit of the sections. Extension of scalars along a ring
isomorphism is tensoring with a flat module, so it preserves both.

The middle-term inclusion assumes `CategoryTheory.Balanced` on the `𝒪_X`-modules. Its input is
`SheafOfModules.exact_val_app_of_shortExact`, left exactness of the sections, which identifies
the first term with a kernel of the second map and so needs the ambient category to be balanced;
that holds for the module universe `m := u` and for `m := u + 1` but not at a free `m`, as
`AlgebraicGeometry.Spaces.ShortExactQuasicoherent` records. The subsheaf inclusion uses only
monomorphy of the first map and is unconditional.

## References

* [Stacks Project, Tag 0CTZ](https://stacks.math.columbia.edu/tag/0CTZ)
* [Stacks Project, Tag 0548](https://stacks.math.columbia.edu/tag/0548)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

/-- The map of filtered colimits of modules induced by a morphism of the diagrams of sections
which is linear over the diagram of rings. -/
private noncomputable def colimitModuleMap {D : Type w} [SmallCategory D] [IsFiltered D]
    (R : D ⥤ RingCat.{w}) (M N : D ⥤ AddCommGrpCat.{max w m})
    [∀ i, Module (R.obj i) (M.obj i)] [∀ i, Module (R.obj i) (N.obj i)]
    (hM : ∀ {i j} (f : i ⟶ j) (r : R.obj i) (x : M.obj i),
      M.map f (r • x) = R.map f r • M.map f x)
    (hN : ∀ {i j} (f : i ⟶ j) (r : R.obj i) (x : N.obj i),
      N.map f (r • x) = R.map f r • N.map f x)
    (τ : M ⟶ N)
    (hτ : ∀ i (r : R.obj i) (x : M.obj i), τ.app i (r • x) = r • τ.app i x) :
    letI : Module ↑(colimit R) ↑(colimit M) :=
      IsColimit.module R M hM (colimit.isColimit R) (colimit.isColimit M)
    letI : Module ↑(colimit R) ↑(colimit N) :=
      IsColimit.module R N hN (colimit.isColimit R) (colimit.isColimit N)
    ModuleCat.of ↑(colimit R) ↑(colimit M) ⟶ ModuleCat.of ↑(colimit R) ↑(colimit N) := by
  letI : Module ↑(colimit R) ↑(colimit M) :=
    IsColimit.module R M hM (colimit.isColimit R) (colimit.isColimit M)
  letI : Module ↑(colimit R) ↑(colimit N) :=
    IsColimit.module R N hN (colimit.isColimit R) (colimit.isColimit N)
  letI : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max w m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max w m})
  exact ModuleCat.ofHom
    { toFun := (colim.map τ : colimit M ⟶ colimit N)
      map_add' := map_add _
      map_smul' := by
        intro r z
        change (colim.map τ : colimit M ⟶ colimit N) (r • z) =
          HSMul.hSMul (α := ↑(colimit R)) (β := ↑(colimit N))
            r ((colim.map τ : colimit M ⟶ colimit N) z)
        obtain ⟨i, scalar, hscalar⟩ := Concrete.colimit_exists_rep R r
        obtain ⟨j, value, hvalue⟩ := Concrete.colimit_exists_rep M z
        rw [← hscalar, ← hvalue]
        obtain ⟨k, left, right, -⟩ := IsFilteredOrEmpty.cocone_objs i j
        have hr := ConcreteCategory.congr_hom (colimit.w R left) scalar
        have hz := ConcreteCategory.congr_hom (colimit.w M right) value
        simp only [ConcreteCategory.comp_apply] at hr hz
        rw [← hr, ← hz]
        have hsmul := IsColimit.ι_smul R M hM (colimit.isColimit R)
          (colimit.isColimit M) k (R.map left scalar) (M.map right value)
        change colimit.ι M k (R.map left scalar • M.map right value) =
          colimit.ι R k (R.map left scalar) •
            colimit.ι M k (M.map right value) at hsmul
        rw [← hsmul]
        have hmap (y : M.obj k) :
            (colim.map τ : colimit M ⟶ colimit N) (colimit.ι M k y) =
              colimit.ι N k (τ.app k y) :=
          ConcreteCategory.congr_hom (colimit.ι_map τ k) y
        rw [hmap, hmap, hτ]
        exact IsColimit.ι_smul R N hN (colimit.isColimit R) (colimit.isColimit N) k _ _ }

/-- The map of stalks at a point of a site induced by a morphism of sheaves of modules. -/
private noncomputable def moduleStalkLargeMap (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)} (α : F₁ ⟶ F₂) :
    moduleStalkLarge.{m} p O F₁ ⟶ moduleStalkLarge.{m} p O F₂ := by
  let D := FinallySmall.FilteredFinalModel.{w} (p.fiber.Elementsᵒᵖ)
  let G : D ⥤ p.fiber.Elementsᵒᵖ := FinallySmall.fromFilteredFinalModel _
  let R := G ⋙ (CategoryOfElements.π p.fiber).op ⋙ (commRingSheafToRingSheaf O).obj
  let M := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₁.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let N := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₂.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  letI (i : D) : Module (R.obj i) (M.obj i) := by
    change Module _ (ULift (F₁.val.obj _))
    letI : Module ((commRingSheafToRingSheaf O).obj.obj
        ((CategoryOfElements.π p.fiber).op.obj (G.obj i)))
        (F₁.val.obj ((CategoryOfElements.π p.fiber).op.obj (G.obj i))) :=
      (F₁.val.obj _).isModule
    infer_instance
  letI (i : D) : Module (R.obj i) (N.obj i) := by
    change Module _ (ULift (F₂.val.obj _))
    letI : Module ((commRingSheafToRingSheaf O).obj.obj
        ((CategoryOfElements.π p.fiber).op.obj (G.obj i)))
        (F₂.val.obj ((CategoryOfElements.π p.fiber).op.obj (G.obj i))) :=
      (F₂.val.obj _).isModule
    infer_instance
  have hM : ∀ {i j} (f : i ⟶ j) (r : R.obj i) (x : M.obj i),
      M.map f (r • x) = R.map f r • M.map f x := by
    intro i j f r x
    let : Module (R.obj i)
        (F₁.val.presheaf.obj ((CategoryOfElements.π p.fiber).op.obj (G.obj i))) :=
      (F₁.val.obj _).isModule
    change ULift.up (F₁.val.map _ (r • x.down)) = ULift.up (_ • F₁.val.map _ x.down)
    congr 1
    exact F₁.val.map_smul _ _ _
  have hN : ∀ {i j} (f : i ⟶ j) (r : R.obj i) (x : N.obj i),
      N.map f (r • x) = R.map f r • N.map f x := by
    intro i j f r x
    let : Module (R.obj i)
        (F₂.val.presheaf.obj ((CategoryOfElements.π p.fiber).op.obj (G.obj i))) :=
      (F₂.val.obj _).isModule
    change ULift.up (F₂.val.map _ (r • x.down)) = ULift.up (_ • F₂.val.map _ x.down)
    congr 1
    exact F₂.val.map_smul _ _ _
  let τ : M ⟶ N := Functor.whiskerLeft (G ⋙ (CategoryOfElements.π p.fiber).op)
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map α.val)
      AddCommGrpCat.uliftFunctor.{w})
  have hτ : ∀ i (r : R.obj i) (x : M.obj i), τ.app i (r • x) = r • τ.app i x := by
    intro i r x
    let : Module (R.obj i)
        (F₁.val.presheaf.obj ((CategoryOfElements.π p.fiber).op.obj (G.obj i))) :=
      (F₁.val.obj _).isModule
    change ULift.up ((α.val.app ((CategoryOfElements.π p.fiber).op.obj (G.obj i))).hom
        (r • x.down)) =
      ULift.up (r • (α.val.app ((CategoryOfElements.π p.fiber).op.obj (G.obj i))).hom x.down)
    congr 1
    exact (α.val.app _).hom.map_smul r x.down
  letI : PreservesColimitsOfShape (p.fiber.Elementsᵒᵖ) (forget₂ CommRingCat.{w} RingCat.{w}) :=
    FinallySmall.preservesColimitsOfShape_of_isFiltered _ _
  let e : (colimit.cocone R).pt ≅ (forget₂ CommRingCat RingCat).obj
      ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
    Functor.Final.colimitIso G _ ≪≫
      (preservesColimitIso (forget₂ CommRingCat RingCat)
        ((CategoryOfElements.π p.fiber).op ⋙ O.obj)).symm
  exact (ModuleCat.restrictScalars e.inv.hom).map
    (colimitModuleMap R M N hM hN τ hτ)

/-- The stalk at a point of a site of an injective morphism of sheaves of modules — one which
is injective on sections — is injective. -/
private theorem injective_moduleStalkLargeMap (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    {F₁ F₂ : SheafOfModules.{m} (commRingSheafToRingSheaf O)} (α : F₁ ⟶ F₂)
    (hα : ∀ U, Function.Injective (α.val.app U).hom) :
    Function.Injective (moduleStalkLargeMap p O α) := by
  let D := FinallySmall.FilteredFinalModel.{w} (p.fiber.Elementsᵒᵖ)
  let G : D ⥤ p.fiber.Elementsᵒᵖ := FinallySmall.fromFilteredFinalModel _
  let M := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₁.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let N := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₂.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let τ : M ⟶ N := Functor.whiskerLeft (G ⋙ (CategoryOfElements.π p.fiber).op)
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map α.val)
      AddCommGrpCat.uliftFunctor.{w})
  have happ : ∀ i, Function.Injective (τ.app i) := by
    intro i a b hab
    apply ULift.ext
    exact hα _ (ULift.ext_iff.mp hab)
  have happ' : ∀ i, Mono (τ.app i) := fun i => ConcreteCategory.mono_of_injective _ (happ i)
  have hmono : Mono τ := NatTrans.mono_of_mono_app τ
  let : AB5OfSize.{w, w} AddCommGrpCat.{max w m} :=
    AB5OfSize_of_univLE AddCommGrpCat.{max w m}
  let : PreservesFiniteLimits (colim (J := D) (C := AddCommGrpCat.{max w m})) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  have : Mono ((colim (J := D) (C := AddCommGrpCat.{max w m})).map τ) :=
    (colim (J := D) (C := AddCommGrpCat.{max w m})).map_mono τ
  exact (ConcreteCategory.injective_of_mono_of_preservesPullback _ :
    Function.Injective ((colim (J := D) (C := AddCommGrpCat.{max w m})).map τ))

/-- The stalk at a point of a site of a pair of morphisms of sheaves of modules which is exact
on sections is exact: the stalk is a filtered colimit of the sections. -/
private theorem exact_moduleStalkLargeMap (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    {F₁ F₂ F₃ : SheafOfModules.{m} (commRingSheafToRingSheaf O)} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (h : ∀ U, Function.Exact (α.val.app U).hom (β.val.app U).hom) :
    Function.Exact (moduleStalkLargeMap p O α) (moduleStalkLargeMap p O β) := by
  let D := FinallySmall.FilteredFinalModel.{w} (p.fiber.Elementsᵒᵖ)
  let G : D ⥤ p.fiber.Elementsᵒᵖ := FinallySmall.fromFilteredFinalModel _
  let M₁ := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₁.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let M₂ := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₂.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let M₃ := G ⋙ (CategoryOfElements.π p.fiber).op ⋙
    F₃.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}
  let τ : M₁ ⟶ M₂ := Functor.whiskerLeft (G ⋙ (CategoryOfElements.π p.fiber).op)
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map α.val)
      AddCommGrpCat.uliftFunctor.{w})
  let σ : M₂ ⟶ M₃ := Functor.whiskerLeft (G ⋙ (CategoryOfElements.π p.fiber).op)
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map β.val)
      AddCommGrpCat.uliftFunctor.{w})
  let : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max w m}) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat.{max w m})
  have hlocal : ∀ k, Function.Exact (τ.app k) (σ.app k) := by
    intro k z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨a, ha⟩ := (h ((CategoryOfElements.π p.fiber).op.obj (G.obj k)) z.down).mp
        (ULift.ext_iff.mp hz)
      exact ⟨ULift.up a, ULift.ext_iff.mpr ha⟩
    · rintro ⟨x, rfl⟩
      exact ULift.ext_iff.mpr ((h ((CategoryOfElements.π p.fiber).op.obj (G.obj k)) _).mpr
        ⟨x.down, rfl⟩)
  have hcomp : τ ≫ σ = 0 := by
    ext k z
    exact (hlocal k (τ.app k z)).mpr ⟨z, rfl⟩
  have hιτ : ∀ (j : D) (x : M₁.obj j),
      (colim (J := D) (C := AddCommGrpCat.{max w m})).map τ (colimit.ι M₁ j x) =
        colimit.ι M₂ j (τ.app j x) := fun j x => by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (colimit.ι_map τ j) x
  have hισ : ∀ (j : D) (y : M₂.obj j),
      (colim (J := D) (C := AddCommGrpCat.{max w m})).map σ (colimit.ι M₂ j y) =
        colimit.ι M₃ j (σ.app j y) := fun j y => by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (colimit.ι_map σ j) y
  have hnat : ∀ {i j : D} (f : i ⟶ j) (y : M₂.obj i),
      σ.app j (M₂.map f y) = M₃.map f (σ.app i y) := fun f y => by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (σ.naturality f) y
  have hw : ∀ {i j : D} (f : i ⟶ j) (y : M₂.obj i),
      colimit.ι M₂ j (M₂.map f y) = colimit.ι M₂ i y := fun f y => by
    simpa only [ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (colimit.w M₂ f) y
  have key : Function.Exact ((colim (J := D) (C := AddCommGrpCat.{max w m})).map τ)
      ((colim (J := D) (C := AddCommGrpCat.{max w m})).map σ) := by
    intro z
    refine ⟨fun hz => ?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := Concrete.colimit_exists_rep M₂ z
      rw [hισ] at hz
      have h1 : colimit.ι M₃ i (σ.app i y) = colimit.ι M₃ i 0 := by
        rwa [map_zero]
      obtain ⟨k, f, g, hfg⟩ := (Concrete.colimit_rep_eq_iff_exists M₃ _ _).mp h1
      rw [map_zero] at hfg
      obtain ⟨x, hx⟩ := (hlocal k (M₂.map f y)).mp (by rw [hnat, hfg])
      exact ⟨colimit.ι M₁ k x, by rw [hιτ, hx, hw]⟩
    · rintro ⟨x, rfl⟩
      have h3 : (colim (J := D) (C := AddCommGrpCat.{max w m})).map τ ≫ colim.map σ = 0 := by
        rw [← Functor.map_comp, hcomp, Functor.map_zero]
      simpa using ConcreteCategory.congr_hom h3 x
  exact key

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- Extending the scalars of the geometric stalk map of a morphism that is injective on sections
along the ring isomorphism `pointStalkRingEquiv` gives an injective map. -/
private theorem injective_extendScalars_moduleStalkLargeMap (xbar : GeometricPoint B S hS X.1)
    {F₁ F₂ : Modules.{u, m} B S hS X.1 X.2} (f : F₁ ⟶ F₂)
    (hf : ∀ U, Function.Injective (f.val.app U).hom) :
    Function.Injective (((ModuleCat.extendScalars
      (pointStalkRingEquiv B S hS X xbar).toRingHom).map
        (Stacks.moduleStalkLargeMap (etaleSitePoint B S hS X.1 xbar X.2)
          (smallEtaleRingedTopos B S hS X).O f)).hom) := by
  let p := etaleSitePoint B S hS X.1 xbar X.2
  let O := (smallEtaleRingedTopos B S hS X).O
  let e := pointStalkRingEquiv B S hS X xbar
  let : Algebra ↑(p.presheafFiber.obj O.obj) ↑(etaleLocalRing B S hS X.1 xbar) :=
    e.toRingHom.toAlgebra
  have : Module.Flat ↑(p.presheafFiber.obj O.obj) ↑(etaleLocalRing B S hS X.1 xbar) :=
    RingHom.Flat.of_bijective e.bijective
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (Stacks.injective_moduleStalkLargeMap p O f hf)

/-- **Stacks 0CTZ, first inclusion.** In a short exact sequence of `𝒪_X`-modules on an
algebraic space, every weakly associated point of the first module is weakly associated to the
middle module. -/
@[stacks 0CTZ "subsheaf"]
theorem weaklyAssociatedPoints_subset_of_shortExact
    (σ : ShortComplex (Modules.{u, m} B S hS X.1 X.2)) (hσ : σ.ShortExact) :
    weaklyAssociatedPoints B S hS X σ.X₁ ⊆ weaklyAssociatedPoints B S hS X σ.X₂ := by
  rintro x ⟨xbar, hxbar, hweak⟩
  refine ⟨xbar, hxbar, ?_⟩
  have : Mono σ.f := hσ.mono_f
  have : Mono σ.f.val := (SheafOfModules.forget _).map_mono σ.f
  exact Module.weaklyAssociatedPrimes_subset_of_injective
    (injective_extendScalars_moduleStalkLargeMap B S hS X xbar σ.f
      (fun U => PresheafOfModules.injective_of_mono σ.f.val U)) hweak

/-- **Stacks 0CTZ, second inclusion.** In a short exact sequence of `𝒪_X`-modules on an
algebraic space, every weakly associated point of the middle module is weakly associated to one
of the outer modules. -/
@[stacks 0CTZ "middle_term"]
theorem weaklyAssociatedPoints_subset_union_of_shortExact
    [Balanced (Modules.{u, m} B S hS X.1 X.2)]
    (σ : ShortComplex (Modules.{u, m} B S hS X.1 X.2)) (hσ : σ.ShortExact) :
    weaklyAssociatedPoints B S hS X σ.X₂ ⊆
      weaklyAssociatedPoints B S hS X σ.X₁ ∪ weaklyAssociatedPoints B S hS X σ.X₃ := by
  rintro x ⟨xbar, hxbar, hweak⟩
  let p := etaleSitePoint B S hS X.1 xbar X.2
  let O := (smallEtaleRingedTopos B S hS X).O
  let e := pointStalkRingEquiv B S hS X xbar
  let φ := Stacks.moduleStalkLargeMap p O σ.f
  let ψ := Stacks.moduleStalkLargeMap p O σ.g
  have hexact := Stacks.exact_moduleStalkLargeMap p O σ.f σ.g
    (SheafOfModules.exact_val_app_of_shortExact hσ :
      ∀ U, Function.Exact (σ.f.val.app U).hom (σ.g.val.app U).hom)
  let : Algebra ↑(p.presheafFiber.obj O.obj) ↑(etaleLocalRing B S hS X.1 xbar) :=
    e.toRingHom.toAlgebra
  have : Module.Flat ↑(p.presheafFiber.obj O.obj) ↑(etaleLocalRing B S hS X.1 xbar) :=
    RingHom.Flat.of_bijective e.bijective
  have hgexact : Function.Exact (((ModuleCat.extendScalars e.toRingHom).map φ).hom)
      (((ModuleCat.extendScalars e.toRingHom).map ψ).hom) :=
    Module.Flat.lTensor_exact ↑(etaleLocalRing B S hS X.1 xbar) hexact
  have hginj := injective_extendScalars_moduleStalkLargeMap B S hS X xbar σ.f
    (SheafOfModules.injective_f_val_app_of_shortExact hσ)
  rcases Module.weaklyAssociatedPrimes_subset_union_of_exact hginj hgexact hweak with h₁ | h₃
  · exact Or.inl ⟨xbar, hxbar, h₁⟩
  · exact Or.inr ⟨xbar, hxbar, h₃⟩

end AlgebraicGeometry.Space

end
