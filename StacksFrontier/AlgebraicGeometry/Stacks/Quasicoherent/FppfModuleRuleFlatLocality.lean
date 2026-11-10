module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RelativeLeraySpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedSmoothLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfDescentModuleRule
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFppfWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModulePullbackNatIso

/-!
# Locality of a module rule along a flat, locally finitely presented family (Stacks 07AQ (2))

Let `M` assign to every algebraic stack `𝒳` over `S` a class of modules on its fppf site, with
sections in the universe `u` of the schemes. **Stacks 07AQ** part (2) is the statement, for
`M = LQCoh^fbc`, that membership in `M` descends along a jointly surjective family
`f j : 𝒵 j ⟶ 𝒳` of flat, locally finitely presented 1-morphisms: if every `f j^* F` is in `M`,
so is `F`. The source proves it ("analogous to the proof of Stacks 07AP") from four closure
properties of `LQCoh^fbc` and from part (1); this file carries out that proof for an arbitrary
`M` with those properties, so that the tagged statement is its instance.

The properties used are: closure under isomorphisms; under inverse images along every
1-morphism (**Stacks 0771** (3)); under direct images along 1-morphisms between algebraic stacks
representable by affine schemes (the case of **Stacks 0771** (4)(b), degree `0`, which the proof
uses); under equalizers (**Stacks 0771** (2)); and locality along jointly surjective families of
smooth 1-morphisms (**Stacks 07AQ** (1)).

## The proof

* *Over an affine object* (`AlgebraicGeometry.Stack.mem_fppfModulesPullback_of_isAffine`). Let
  `β : (Sch/A) ⟶ 𝒳` with `A` affine. **Stacks 07AN** gives an fppf covering `{W i ⟶ A}` over
  whose members the object named by `β` lifts through some `f j`; so the inverse image of `F` to
  each `W i` is, up to the 2-isomorphism of **Stacks 004B**, an inverse image of some `f j^* F`
  (`AlgebraicGeometry.Stack.mem_fppfModulesPullback_comp_of_isHomLift`). The covering is refined
  to finitely many affines `V k`, whose disjoint union `D` is affine with a flat, locally finitely
  presented, surjective `d : D ⟶ A`. Locality along the open immersions `V k ⟶ D` puts the
  inverse image to `D` in `M`, and the descent step
  `AlgebraicGeometry.Stack.mem_of_mem_fppfModulesPullback` along `d` (whose hypotheses are the
  closure properties, `d` being a morphism of affines) concludes.
* *In general*
  (`AlgebraicGeometry.Stack.mem_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective`).
  The smooth 1-morphisms out of algebraic stacks of affine objects are jointly surjective, since
  a smooth surjective scheme chart is covered by affine opens; locality along them reduces to the
  affine case.

## Main results

* `AlgebraicGeometry.Stack.isoOfTautologicalHom`: two 1-morphisms out of `(Sch/W)` whose values
  at the tautological object are joined by an arrow over the identity are 2-isomorphic.
* `AlgebraicGeometry.Stack.exists_affine_sigma_of_finite_family`: the disjoint union of a finite
  family of affine objects covering an object of the site; the finite refinement itself is
  `AlgebraicGeometry.Stack.exists_finite_affine_flat_family_of_mem_topology`.
* `AlgebraicGeometry.Stack.mem_fppfModulesPullback_of_isAffine` and
  `AlgebraicGeometry.Stack.mem_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective`.

## Implementation notes

The source applies part (1) to a single smooth surjective `x : U ⟶ 𝒳` and then "Zariski locally
on `U`"; here locality is applied once, to the family of all smooth 1-morphisms out of algebraic
stacks of affine objects, which is the same reduction in one step. Locality is asked for families
indexed by a type of universe `u + 1`, which covers both uses.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06XE](https://stacks.math.columbia.edu/tag/06XE)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 07AP](https://stacks.math.columbia.edu/tag/07AP)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (M : ∀ 𝒳 : AlgebraicStacks.{u, w} B S hS, ObjectProperty (fppfModules B S hS 𝒳))

/-- **Stacks 004B for 1-morphisms out of the algebraic stack of an object of the site.** Two
1-morphisms `G₁ G₂ : (Sch/W) ⟶ 𝒳` whose values at the tautological object are joined by an
arrow lying over the identity of `W` are 2-isomorphic: evaluation at the tautological object is an
equivalence, and the fibre of `𝒳` over `W` is a groupoid. -/
noncomputable def isoOfTautologicalHom {W : BigFppfOver B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (G₁ G₂ : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (φ : (CatFiberedInGroupoids.homFunctor G₁.hom).obj (Over.mk (𝟙 W)) ⟶
      (CatFiberedInGroupoids.homFunctor G₂.hom).obj (Over.mk (𝟙 W)))
    (hφ : 𝒳.val.val.p.IsHomLift (𝟙 W) φ) : G₁ ≅ G₂ :=
  have := Functor.twoYonedaEvaluation_isEquivalence 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids W
  have := 𝒳.val.isFiberedInGroupoids.fiber_isGroupoid W
  let ev := Functor.twoYonedaEvaluation 𝒳.val.val.p W
  let φ' : ev.obj G₁.hom.hom ⟶ ev.obj G₂.hom.hom := Functor.Fiber.homMk _ _ φ
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (ev.preimageIso (asIso φ')))

/-- One member of the covering of **Stacks 07AN**. Let `β : (Sch/A) ⟶ 𝒳` be a 1-morphism, and
let `m : W ⟶ A` be a morphism along which the value of `β` at the tautological object lifts to an
object `x` of `𝒵` through `f : 𝒵 ⟶ 𝒳`. If `M` is closed under isomorphisms and inverse images and
contains `f^* F`, then it contains the inverse image of `F` along `(Sch/W) ⟶ (Sch/A) ⟶ 𝒳`: that
1-morphism is 2-isomorphic to `(Sch/W) ⟶ 𝒵 ⟶ 𝒳` (**Stacks 004B**). -/
theorem mem_fppfModulesPullback_comp_of_isHomLift [∀ 𝒳, (M 𝒳).IsClosedUnderIsomorphisms]
    (hpull : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (G : fppfModules B S hS 𝒴),
      M 𝒴 G → M 𝒳 ((fppfModulesPullback B S hS f).obj G))
    {𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} {A : BigFppfOver B S hS}
    (β : schemeStack.{u, w} B S hS A ⟶ 𝒳) (f : 𝒵 ⟶ 𝒳) {W : B.Schemes} (m : W ⟶ A.left)
    (x : 𝒵.val.val.obj)
    (α : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶
      (CatFiberedInGroupoids.homFunctor β.hom).obj (Over.mk (𝟙 A)))
    (hα : 𝒳.val.val.p.IsHomLift
      (Over.homMk m rfl : (Over.mk (m ≫ A.hom) : BigFppfOver B S hS) ⟶ A) α)
    (F : fppfModules B S hS 𝒳) (hF : M 𝒵 ((fppfModulesPullback B S hS f).obj F)) :
    M (schemeStack.{u, w} B S hS (Over.mk (m ≫ A.hom)))
      ((fppfModulesPullback B S hS
        (schemeStackMap.{u, w} B S hS (Over.homMk m rfl) ≫ β)).obj F) := by
  let W' : BigFppfOver B S hS := Over.mk (m ≫ A.hom)
  let g : W' ⟶ A := Over.homMk m rfl
  have hX := 𝒳.val.isFiberedInGroupoids
  have hZ := 𝒵.val.isFiberedInGroupoids
  have : 𝒳.val.val.p.IsFibered := hX.isFibered
  have : 𝒵.val.val.p.IsFibered := hZ.isFibered
  have hx : 𝒵.val.val.p.obj x = W' :=
    (congrArg (fun F => F.obj x) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).symm.trans
      (IsHomLift.domain_eq 𝒳.val.val.p g α)
  let G₁ : schemeStack.{u, w} B S hS W' ⟶ 𝒳 := fibreObjectStackMap B S hS 𝒵 W' ⟨x, hx⟩ ≫ f
  let G₂ : schemeStack.{u, w} B S hS W' ⟶ 𝒳 := schemeStackMap.{u, w} B S hS g ≫ β
  -- the value of `G₂` at the tautological object maps to that of `β` over `g`
  let ψ₂ : (CatFiberedInGroupoids.homFunctor G₂.hom).obj (Over.mk (𝟙 W')) ⟶
      (CatFiberedInGroupoids.homFunctor β.hom).obj (Over.mk (𝟙 A)) :=
    (CatFiberedInGroupoids.homFunctor β.hom).map
      (Over.homMk g (by simp) : (Over.mk (𝟙 W' ≫ g) : Over A) ⟶ Over.mk (𝟙 A))
  have hψ₂ : 𝒳.val.val.p.IsHomLift g ψ₂ := by
    have h : (schemeStack.{u, w} B S hS A).val.val.p.IsHomLift g
        (Over.homMk g (by simp) : (Over.mk (𝟙 W' ≫ g) : Over A) ⟶ Over.mk (𝟙 A)) :=
      IsHomLift.map (Over.forget A)
        (Over.homMk g (by simp) : (Over.mk (𝟙 W' ≫ g) : Over A) ⟶ Over.mk (𝟙 A))
    exact @BasedFunctor.preserves_isHomLift _ _ _ _ β.hom.hom _ _ _ _ g _ h
  have : 𝒳.val.val.p.IsStronglyCartesian g ψ₂ :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hX _ ψ₂
  -- the value of `G₁` at the tautological object maps to that of `β` over `g`
  let c := Functor.TwoYoneda.chosenLift 𝒵.val.val.p hZ W' ⟨x, hx⟩ (Over.mk (𝟙 W'))
  let ψ₁ : (CatFiberedInGroupoids.homFunctor G₁.hom).obj (Over.mk (𝟙 W')) ⟶
      (CatFiberedInGroupoids.homFunctor β.hom).obj (Over.mk (𝟙 A)) :=
    (CatFiberedInGroupoids.homFunctor f.hom).map c.φ ≫ α
  have hψ₁ : 𝒳.val.val.p.IsHomLift g ψ₁ := by
    have h : 𝒵.val.val.p.IsHomLift (𝟙 W') c.φ := c.isStronglyCartesian.toIsHomLift
    have h' : 𝒳.val.val.p.IsHomLift (𝟙 W') ((CatFiberedInGroupoids.homFunctor f.hom).map c.φ) :=
      @BasedFunctor.preserves_isHomLift _ _ _ _ f.hom.hom _ _ _ _ (𝟙 W') c.φ h
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒳.val.val.p _ _ _ W' _ h' _ _ g α hα
  let φ := Functor.IsStronglyCartesian.map 𝒳.val.val.p g ψ₂ (g := 𝟙 W')
    (Category.id_comp g).symm ψ₁
  let e : G₁ ≅ G₂ := isoOfTautologicalHom G₁ G₂ φ inferInstance
  have h₁ : M (schemeStack.{u, w} B S hS W')
      ((fppfModulesPullback B S hS (fibreObjectStackMap B S hS 𝒵 W' ⟨x, hx⟩)).obj
        ((fppfModulesPullback B S hS f).obj F)) := hpull _ _ hF
  have i₁ : (fppfModulesPullback B S hS G₁).obj F ≅
      (fppfModulesPullback B S hS (fibreObjectStackMap B S hS 𝒵 W' ⟨x, hx⟩)).obj
        ((fppfModulesPullback B S hS f).obj F) :=
    (fppfModulesPullbackCompIso B S hS (fibreObjectStackMap B S hS 𝒵 W' ⟨x, hx⟩) f).app F
  have h₂ : M (schemeStack.{u, w} B S hS W') ((fppfModulesPullback B S hS G₁).obj F) :=
    (M _).prop_of_iso i₁.symm h₁
  have i₂ : (fppfModulesPullback B S hS G₁).obj F ≅ (fppfModulesPullback B S hS G₂).obj F :=
    (fppfModulesPullbackIsoOfIso B S hS e).app F
  exact (M _).prop_of_iso i₂ h₂

variable (B S hS) in
/-- The algebraic stack `(Sch/A)` of an affine object `A` of the big fppf site is representable
by an affine scheme. -/
theorem isAffineRepresentable_schemeStack {A : BigFppfOver B S hS}
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A)) :
    AlgebraicStacks.IsAffineRepresentable B S hS (schemeStack.{u, w} B S hS A) :=
  ⟨A, hA, ⟨StacksRepresentableCFG.EquivalenceOver.refl _⟩⟩

variable (B S hS) in
/-- **The disjoint union of a finite family of affine objects of the big fppf site of `S` over
an object `A`.** For finitely many affine `V i` with flat, locally finitely presented arrows
`v i : V i ⟶ A` whose images cover `A`, the coproduct `D = ∐ V i` is an affine object of the
site with an arrow `d : D ⟶ A` which is flat, locally of finite presentation and surjective,
through which every `v i` factors by a coprojection; the coprojections are open immersions and
their images cover `D`. -/
theorem exists_affine_sigma_of_finite_family {A : BigFppfOver B S hS} {I : Type u} [Finite I]
    (V : I → BigFppfOver B S hS) (v : ∀ i, V i ⟶ A)
    (hV : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i)))
    (hflat : ∀ i, Flat ((BigFppfOver.toScheme B S hS).map (v i)))
    (hlfp : ∀ i, LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (v i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj A,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base) :
    ∃ (D : BigFppfOver B S hS) (d : D ⟶ A) (ι : ∀ i, V i ⟶ D),
      IsAffine ((BigFppfOver.toScheme B S hS).obj D) ∧
        Flat ((BigFppfOver.toScheme B S hS).map d) ∧
        LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map d) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map d) ∧ (∀ i, ι i ≫ d = v i) ∧
        (∀ i, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (ι i))) ∧
        ∀ x : (BigFppfOver.toScheme B S hS).obj D,
          ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι i)).base := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let Y (i : I) : Scheme.{u} := T.obj (V i)
  let d₀ : (∐ Y) ⟶ T.obj A := Sigma.desc (fun i => T.map (v i))
  have hY : B.Contains (∐ Y) := Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Y (fun i => (V i).left.property)
  let D : BigFppfOver B S hS := Over.mk (⟨d₀ ≫ B.inclusion.map A.hom⟩ : B.obj hY ⟶ B.obj hS)
  let d : D ⟶ A := Over.homMk ⟨d₀⟩ rfl
  let ι (i : I) : V i ⟶ D := Over.homMk ⟨Sigma.ι Y i⟩ (by
    apply B.inclusion.map_injective
    change Sigma.ι Y i ≫ d₀ ≫ B.inclusion.map A.hom = B.inclusion.map (V i).hom
    rw [Sigma.ι_comp_desc_assoc]
    change B.inclusion.map (v i).left ≫ B.inclusion.map A.hom = _
    rw [← Functor.map_comp, Over.w])
  have hιd : ∀ i, ι i ≫ d = v i := fun i => by
    refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    change Sigma.ι Y i ≫ d₀ = B.inclusion.map (v i).left
    exact Sigma.ι_comp_desc _ _
  refine ⟨D, d, ι, ?_, ?_, ?_, ?_, hιd, fun i => ?_, fun x => ?_⟩
  · change IsAffine (∐ Y)
    let instAff (i : I) : IsAffine (Y i) := hV i
    infer_instance
  · have : ∀ i, Flat (T.map (v i)) := hflat
    exact inferInstanceAs (Flat (Sigma.desc fun i => T.map (v i)))
  · have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    exact IsZariskiLocalAtSource.sigmaDesc hlfp
  · exact Surjective.sigmaDesc_of_union_range_eq_univ
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcov x))
  · change AlgebraicGeometry.IsOpenImmersion (Sigma.ι Y i)
    infer_instance
  · obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk Y).surjective x
    exact ⟨i, y, (sigmaMk_mk Y i y).symm⟩

include M in
/-- **The reduction of Stacks 07AQ (2) over an affine object.** Let `M` assign to every algebraic
stack a class of modules on its fppf site at module universe `u`, closed under isomorphisms,
inverse images, direct images along 1-morphisms of algebraic stacks representable by affine
schemes, equalizers, and local for jointly surjective families of smooth 1-morphisms. Let
`f j : 𝒵 j ⟶ 𝒳` be a jointly surjective family of flat, locally finitely presented 1-morphisms
and `F` a module on `𝒳` with every `f j^* F` in `M`. Then for every affine object `A` of the
site and every 1-morphism `β : (Sch/A) ⟶ 𝒳`, the module `β^* F` is in `M`.

The proof is the second paragraph of the source's proof: **Stacks 07AN** gives an fppf covering
of `A` over whose members `β` lifts through some `f j`; it is refined to finitely many affines,
whose disjoint union `D` maps to `A` by a flat, locally finitely presented, surjective morphism
`d`; `d^* β^* F` is in `M` by locality along the open immersions of the summands, and the descent
step `AlgebraicGeometry.Stack.mem_of_mem_fppfModulesPullback` along `d` concludes. -/
theorem mem_fppfModulesPullback_of_isAffine [∀ 𝒳, (M 𝒳).IsClosedUnderIsomorphisms]
    (hpull : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (G : fppfModules B S hS 𝒴),
      M 𝒴 G → M 𝒳 ((fppfModulesPullback B S hS f).obj G))
    (hpush : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴),
      AlgebraicStacks.IsAffineRepresentable B S hS 𝒳 →
      AlgebraicStacks.IsAffineRepresentable B S hS 𝒴 →
      ∀ G, M 𝒳 G → M 𝒴 ((fppfModulesPushforward B S hS f).obj G))
    (heq : ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) {G₁ G₂ K : fppfModules B S hS 𝒳}
      (g h : G₁ ⟶ G₂) (ι : K ⟶ G₁) (w : ι ≫ g = ι ≫ h), IsLimit (Fork.ofι ι w) →
      M 𝒳 G₁ → M 𝒳 G₂ → M 𝒳 K)
    (hlocal : ∀ {J : Type (u + 1)} {𝒵 : J → AlgebraicStacks.{u, w} B S hS}
      {𝒳 : AlgebraicStacks.{u, w} B S hS} (g : ∀ j, 𝒵 j ⟶ 𝒳),
      (∀ j, AlgebraicStacks.IsSmooth B S hS (g j)) →
      (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (g j)) →
      ∀ G, (∀ j, M (𝒵 j) ((fppfModulesPullback B S hS (g j)).obj G)) → M 𝒳 G)
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : fppfModules B S hS 𝒳) (hF : ∀ j, M (𝒵 j) ((fppfModulesPullback B S hS (f j)).obj F))
    {A : BigFppfOver B S hS} (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (β : schemeStack.{u, w} B S hS A ⟶ 𝒳) :
    M (schemeStack.{u, w} B S hS A) ((fppfModulesPullback B S hS β).obj F) := by
  classical
  let y : 𝒳.val.val.p.Fiber A := (Functor.twoYonedaEvaluation 𝒳.val.val.p A).obj β.hom.hom
  obtain ⟨I, W, m, a, hmflat, hmlfp, hmsurj, hlift⟩ :=
    exists_fppfCovering_family_fibre_lift B S hS f hflat hlfp hjs A y
  choose x α hα using hlift
  obtain ⟨K, hK, V, v, hVaff, hvR, hvflat, hvlfp, hvcov⟩ :=
    exists_finite_affine_flat_family_of_mem_topology B S hS hA
      (mem_topology_of_family B S hS W m hmflat hmlfp hmsurj)
  obtain ⟨D, d, ι, hDaff, hdflat, hdlfp, hdsurj, hιd, hιopen, hιcov⟩ :=
    exists_affine_sigma_of_finite_family B S hS V v hVaff hvflat hvlfp hvcov
  -- the inverse image of `F` along every `V k ⟶ A ⟶ 𝒳` is in `M`
  have hmem : ∀ k, M (schemeStack.{u, w} B S hS (V k))
      ((fppfModulesPullback B S hS (schemeStackMap.{u, w} B S hS (v k) ≫ β)).obj F) := by
    intro k
    obtain ⟨T, g, h, ⟨i⟩, hgh⟩ := hvR k
    have hg := hpull (schemeStackMap.{u, w} B S hS g) _
      (mem_fppfModulesPullback_comp_of_isHomLift M hpull β (f (a i)) (m i) (x i)
        (α i) (hα i) F (hF (a i)))
    rw [← hgh, ← schemeStackMap_comp]
    exact (M _).prop_of_iso ((fppfModulesPullbackCompIso B S hS (schemeStackMap.{u, w} B S hS g)
      (schemeStackMap.{u, w} B S hS (Over.homMk (m i) rfl) ≫ β)).app F).symm hg
  -- the inverse image of `F` along `D ⟶ A ⟶ 𝒳` is in `M`, by locality along the summands
  have hD : M (schemeStack.{u, w} B S hS D)
      ((fppfModulesPullback B S hS (schemeStackMap.{u, w} B S hS d ≫ β)).obj F) := by
    refine hlocal (J := ULift.{u + 1} K) (𝒵 := fun k => schemeStack.{u, w} B S hS (V k.down))
      (fun k => schemeStackMap.{u, w} B S hS (ι k.down)) (fun k => ?_) ?_ _ (fun k => ?_)
    · have := hιopen k.down
      exact isSmooth_schemeStackMap B S hS _ inferInstance
    · refine (Set.eq_univ_of_forall fun z => ?_).symm
      obtain ⟨k, hk⟩ := exists_mem_range_pointsMap_schemeStackMap.{u, w} B S hS
        (fun k : ULift.{u + 1} K => V k.down) (fun k => ι k.down)
        (fun x => (hιcov x).elim fun k hk => ⟨ULift.up k, hk⟩) z
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    · refine (M _).prop_of_iso ((fppfModulesPullbackCompIso B S hS
        (schemeStackMap.{u, w} B S hS (ι k.down)) (schemeStackMap.{u, w} B S hS d ≫ β)).app F) ?_
      rw [← Category.assoc, schemeStackMap_comp, hιd]
      exact hmem k.down
  -- the descent step along `d`
  have hcover := exists_presieve_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    (schemeStackMap.{u, w} B S hS d) (isSurjective_schemeFibredCategoryMap.{u, w} B S hS d hdsurj)
    (isFlat_schemeFibredCategoryMap.{u, w} B S hS d hdflat)
    (AlgebraicStacks.isLocallyOfFinitePresentation_schemeStackMap.{u, w} B S hS d hdlfp)
  exact mem_of_mem_fppfModulesPullback M (schemeStackMap.{u, w} B S hS d) hcover
    (hpull _)
    (hpush _ (isAffineRepresentable_schemeStack B S hS hDaff)
      (isAffineRepresentable_schemeStack B S hS hA)) (heq _) _
    ((M _).prop_of_iso ((fppfModulesPullbackCompIso B S hS _ β).app F) hD)

include M in
/-- **The reduction of Stacks 07AQ (2) for a module rule.** Let `M` assign to every algebraic
stack a class of modules on its fppf site at module universe `u`, closed under isomorphisms,
inverse images, direct images along 1-morphisms of algebraic stacks representable by affine
schemes and equalizers, and local for jointly surjective families of smooth 1-morphisms (the
analogue of **Stacks 07AQ** part (1)). Let `f j : 𝒵 j ⟶ 𝒳` be a jointly surjective family of
flat, locally finitely presented 1-morphisms of algebraic stacks and `F` a module on `𝒳` with
every `f j^* F` in `M`. Then `F` is in `M`.

By locality along the smooth 1-morphisms out of affine schemes, which are jointly surjective
since a smooth scheme chart is covered by affine opens, this is
`AlgebraicGeometry.Stack.mem_fppfModulesPullback_of_isAffine`. -/
theorem mem_of_isFlat_isLocallyOfFinitePresentation_jointlySurjective
    [∀ 𝒳, (M 𝒳).IsClosedUnderIsomorphisms]
    (hpull : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (G : fppfModules B S hS 𝒴),
      M 𝒴 G → M 𝒳 ((fppfModulesPullback B S hS f).obj G))
    (hpush : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴),
      AlgebraicStacks.IsAffineRepresentable B S hS 𝒳 →
      AlgebraicStacks.IsAffineRepresentable B S hS 𝒴 →
      ∀ G, M 𝒳 G → M 𝒴 ((fppfModulesPushforward B S hS f).obj G))
    (heq : ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) {G₁ G₂ K : fppfModules B S hS 𝒳}
      (g h : G₁ ⟶ G₂) (ι : K ⟶ G₁) (w : ι ≫ g = ι ≫ h), IsLimit (Fork.ofι ι w) →
      M 𝒳 G₁ → M 𝒳 G₂ → M 𝒳 K)
    (hlocal : ∀ {J : Type (u + 1)} {𝒵 : J → AlgebraicStacks.{u, w} B S hS}
      {𝒳 : AlgebraicStacks.{u, w} B S hS} (g : ∀ j, 𝒵 j ⟶ 𝒳),
      (∀ j, AlgebraicStacks.IsSmooth B S hS (g j)) →
      (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
        ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (g j)) →
      ∀ G, (∀ j, M (𝒵 j) ((fppfModulesPullback B S hS (g j)).obj G)) → M 𝒳 G)
    {J : Type v} {𝒵 : J → AlgebraicStacks.{u, w} B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : ∀ j, 𝒵 j ⟶ 𝒳)
    (hflat : ∀ j, AlgebraicStacks.IsFlat B S hS (f j))
    (hlfp : ∀ j, AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (f j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (f j)))
    (F : fppfModules B S hS 𝒳) (hF : ∀ j, M (𝒵 j) ((fppfModulesPullback B S hS (f j)).obj F)) :
    M 𝒳 F := by
  classical
  let C := {c : Σ A : BigFppfOver B S hS, schemeStack.{u, w} B S hS A ⟶ 𝒳 //
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.1) ∧ AlgebraicStacks.IsSmooth B S hS c.2}
  refine hlocal (J := C) (𝒵 := fun c => schemeStack.{u, w} B S hS c.1.1) (fun c => c.1.2)
    (fun c => c.2.2) ?_ F (fun c => mem_fppfModulesPullback_of_isAffine M hpull hpush heq hlocal
      f hflat hlfp hjs F hF c.2.1 c.1.2)
  refine (Set.eq_univ_of_forall fun ξ => ?_).symm
  obtain ⟨U, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  obtain ⟨t, rfl⟩ := hcsurj ξ
  choose V v hvopen hvrange hVaff using
    fun Uo : ((BigFppfOver.toScheme B S hS).obj U).affineOpens =>
      BigFppfOver.exists_affineOpen_restrict B S hS U Uo
  have hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (v i)).base := by
    intro x
    obtain ⟨-, ⟨Uo, hUo, rfl⟩, hxUo, -⟩ :=
      ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
    exact ⟨⟨Uo, hUo⟩, by rwa [hvrange]⟩
  obtain ⟨i, s, hs⟩ := exists_mem_range_pointsMap_schemeStackMap.{u, w} B S hS V v hcov t
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (v i)) := hvopen i
  refine Set.mem_iUnion.2 ⟨⟨⟨V i, schemeStackMap.{u, w} B S hS (v i) ≫ c⟩, hVaff i,
    AlgebraicStacks.isSmooth_comp B S hS _ c
      (isSmooth_schemeStackMap B S hS _ inferInstance) hcsm⟩, s, ?_⟩
  rw [AlgebraicStacks.pointsMap_comp, Function.comp_apply, hs]

end AlgebraicGeometry.Stack
