module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.ExtensionFullyFaithful
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The self-product condition of Stacks 0DTI makes the residual gerbe fully faithful

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `x` be a point of `|𝒳|` and let
`𝒵_x ⊂ 𝒳` be a residual gerbe at `x`. Assume that some `q : Spec k ⟶ 𝒳` in the equivalence class
of `x` has `Spec k ×_𝒳 Spec k ⟶ Spec k ×_𝒴 Spec k` an isomorphism. The first two paragraphs of the
source's proof of **Stacks 0DTI** conclude that the composite `𝒵_x ⟶ 𝒳 ⟶ 𝒴` is fully faithful.
This file proves the descent steps of that argument; they are assembled, with no input beyond
the statement's, as `AlgebraicGeometry.Stack.full_and_faithful_comp_of_hasSelfProductEquivalenceAt`
in `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeIsomorphism`.

## The route

The source first shows that the self-product condition does not depend on the representative of
`x`, by faithfully flat descent along `Spec(k' ⊗ k') ⟶ Spec(k ⊗ k)` for a field extension `k'/k`,
then takes the representative to be a surjective, flat, locally finitely presented
`Spec k ⟶ 𝒵_x`, presents `𝒵_x` as `[Spec k/R]` with `R = Spec k ×_𝒳 Spec k`, as in the proof of
**Stacks 06MR**, and applies **Stacks 04T4 (6)** to `R = Spec k ×_𝒴 Spec k`.

Here the same three steps are taken on the sheaves of morphisms rather than on the groupoid. Call
an object `ξ` of `𝒳` *good* when `f` is bijective on the morphisms of every fibre between any two
objects that map to `ξ`, that is, between any two base changes of `ξ`.

1. The self-product condition says that the image `ξ` under `q` of the tautological object of
   `Spec k` is good: an object of `Spec k ×_𝒳 Spec k` over `T` is a pair of `T`-points of `Spec k`
   with an isomorphism of their images, and the comparison being an equivalence of categories is
   bijectivity of `f` on those isomorphisms
   (`AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_isEquivalence_mapBase`).
2. Let `c : Spec k₀ ⟶ 𝒵_x` be surjective, flat and locally of finite presentation (the implication
   (1) ⟹ (2) of **Stacks 06MP**) and `ξ₀` the image of its tautological object. The two points
   `q` and `c` of `𝒳` both lie over `x`, so they have a common refinement `Spec Ω` (**Stacks
   04XF**), and the refinement is good, being a base change of `ξ`. Being bijective is local on the
   base for the fpqc topology, since the sheaves of morphisms of an algebraic stack are fpqc
   sheaves (**Stacks 0APL** through **Stacks 045G**), and `Spec Ω ⟶ Spec k₀` is surjective, flat
   and quasi-compact; so `ξ₀` is good
   (`AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_isHomLift_descent₂`). This is the
   independence of the representative.
3. Every object of `𝒵_x` is fppf locally a base change of `ξ₀`, by **Stacks 07AN**, and the
   sheaves of morphisms of `𝒵_x` and `𝒴` are fppf sheaves, so bijectivity on base changes of `ξ₀`
   is bijectivity everywhere (the local-to-global step of **Stacks 04WQ**, in the form
   `CategoryTheory.Functor.Stackification.isLocallyInjective_morPresheafMap_of_essImage`). That
   is full faithfulness of `𝒵_x ⟶ 𝒴` by **Stacks 003Z**.

Step 3 is the source's appeal to Stacks 04T4 (6) for the presentation `[Spec k₀/R₀]`, carried out
on the fibres directly, so no groupoid presentation of the residual gerbe (and no Stacks 06FI) is
needed.

## Main results

* `AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_fpqc`: a 1-morphism of algebraic stacks
  is bijective on the morphisms of the fibre over `U` between two objects as soon as it is so after
  every base change factoring through a surjective, flat, quasi-compact `d ⟶ U`.
* `AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_isHomLift_descent₂`: goodness descends
  along a morphism of `𝒳` lying over a surjective, flat, quasi-compact morphism.
* `AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_isEquivalence_mapBase`: an equivalence
  `𝒰 ×_𝒵 𝒰 ⟶ 𝒰 ×_𝒲 𝒰` makes `𝒵 ⟶ 𝒲` bijective on fibre morphisms between images of `𝒰`.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 0DTI](https://stacks.math.columbia.edu/tag/0DTI)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Descent

variable (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (F : 𝒳.val ⥤ᵇ 𝒴.val)

/-- **The map of morphism presheaves over `g` is bijective exactly when `F` is bijective on the
morphisms between the chosen base changes along `g`.** The map of Stacks 042V is the action of `F`
on the fibre over the source of `g`, conjugated by the comparison isomorphisms. -/
theorem bijective_morPresheafMap_app_iff {U : BigFppfOver B S hS} (a b : 𝒳.val.p.Fiber U)
    (g : Over U) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
    Function.Bijective
        (((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap a b).app (op g)) ↔
      Function.Bijective (fun m : Functor.pullbackFiber 𝒳.val.p a g.hom ⟶
          Functor.pullbackFiber 𝒳.val.p b g.hom =>
        (fibreFunctor B S hS 𝒳 𝒴 F g.left).map m) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  set hF := isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F
  have key : (fun m => ((hF.morPresheafMap a b).app (op g)) m) =
      (Iso.homCongr (hF.mapPullbackFiberIso a g.hom).symm
          (hF.mapPullbackFiberIso b g.hom).symm) ∘
        (fun m => (fibreFunctor B S hS 𝒳 𝒴 F g.left).map m) := by
    funext m
    simp [Iso.homCongr]
  show Function.Bijective (fun m => ((hF.morPresheafMap a b).app (op g)) m) ↔ _
  rw [key]
  exact Equiv.comp_bijective _ _

/-- **The map of Isom sheaves at `T` is bijective exactly when the map of morphism presheaves is
bijective at the corresponding object of `𝒞/U`.** Every morphism of a fibre of a category fibred
in groupoids is invertible, so `Isom(a, b)` is the whole of `Mor(a, b)`. -/
theorem bijective_isomSpaceMap_app_iff {U : BigFppfOver B S hS} (a b : 𝒳.val.p.Fiber U)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
    Function.Bijective ((isomSpaceMap B S hS 𝒳 𝒴 F U a b).app T) ↔
      Function.Bijective
        (((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap a b).app
          (op (sliceObj B S hS U T))) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  set g := sliceObj B S hS U T
  have h𝒳 := 𝒳.isFiberedInGroupoids.fiber_isGroupoid g.left
  have h𝒴 := 𝒴.isFiberedInGroupoids.fiber_isGroupoid g.left
  set ι₁ : ((isomSpace B S hS 𝒳 U a b).obj T) → ((𝒳.val.p.morPresheaf a b).obj (op g)) :=
    fun m => m.1
  set ι₂ : ((isomSpace B S hS 𝒴 U (imageFiberObj B S hS 𝒳 𝒴 F U a)
      (imageFiberObj B S hS 𝒳 𝒴 F U b)).obj T) →
      ((𝒴.val.p.morPresheaf (imageFiberObj B S hS 𝒳 𝒴 F U a)
        (imageFiberObj B S hS 𝒳 𝒴 F U b)).obj (op g)) := fun m => m.1
  have hι₁ : Function.Bijective ι₁ := ⟨Subtype.val_injective, fun m =>
    ⟨⟨m, (Functor.mem_isomSubpresheaf_obj (p := 𝒳.val.p) a b m).mpr inferInstance⟩, rfl⟩⟩
  have hι₂ : Function.Bijective ι₂ := ⟨Subtype.val_injective, fun m =>
    ⟨⟨m, (Functor.mem_isomSubpresheaf_obj (p := 𝒴.val.p) _ _ m).mpr inferInstance⟩, rfl⟩⟩
  have hsq : ι₂ ∘ (fun m => (isomSpaceMap B S hS 𝒳 𝒴 F U a b).app T m) =
      (fun m => ((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap a b).app
        (op g) m) ∘ ι₁ := rfl
  show Function.Bijective (fun m => (isomSpaceMap B S hS 𝒳 𝒴 F U a b).app T m) ↔
    Function.Bijective (fun m => ((isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F).morPresheafMap
      a b).app (op g) m)
  rw [← Function.Bijective.of_comp_iff' hι₂, hsq, Function.Bijective.of_comp_iff _ hι₁]

/-- **Bijectivity on the morphisms of a fibre is fpqc local on the base.** Let `F : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`, let `a` and `b` be objects of the fibre of `𝒳` over `U`,
and let `d` be an object of the big fppf site of `U` whose structure morphism is surjective, flat
and quasi-compact. If `F` is bijective on the morphisms between the base changes of `a` and `b`
along every `T ⟶ U` which factors through `d`, then it is bijective on the morphisms `a ⟶ b`.

The sheaves `Isom(a, b)` and `Isom(F a, F b)` are fpqc sheaves on the big fppf site of `U`
(`AlgebraicGeometry.Stack.isSheaf_fpqc_isomSpace_of_isAlgebraicStack`, Stacks 0APL through
Stacks 045G), so the map between them is an isomorphism by
`AlgebraicGeometry.Space.isIso_of_bijective_app_over_of_isSheaf_fpqc`; its value at `U` itself is
the action of `F` on `a ⟶ b`. -/
theorem bijective_fibreFunctor_map_of_fpqc
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    {U : BigFppfOver B S hS} (a b : 𝒳.val.p.Fiber U) (d : BigFppfOver B U.left.1 U.left.2)
    (hds : Surjective (B.inclusion.map d.hom)) (hdf : Flat (B.inclusion.map d.hom))
    (hdc : QuasiCompact (B.inclusion.map d.hom))
    (h : letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
      ∀ (T : BigFppfOver B U.left.1 U.left.2) (_ : T ⟶ d),
      Function.Bijective (fun m : Functor.pullbackFiber 𝒳.val.p a (sliceObj B S hS U (op T)).hom ⟶
          Functor.pullbackFiber 𝒳.val.p b (sliceObj B S hS U (op T)).hom =>
        (fibreFunctor B S hS 𝒳 𝒴 F (sliceObj B S hS U (op T)).left).map m)) :
    Function.Bijective (fun m : a ⟶ b => (fibreFunctor B S hS 𝒳 𝒴 F U).map m) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  set hF := isFibredOneMorphism_basedFunctor B S hS 𝒳 𝒴 F
  have hiso : IsIso (isomSpaceMap B S hS 𝒳 𝒴 F U a b) :=
    Space.isIso_of_bijective_app_over_of_isSheaf_fpqc B U.left.1 U.left.2
      (isSheaf_fpqc_isomSpace_of_isAlgebraicStack B S hS 𝒳 h𝒳 U a b)
      (isSheaf_fpqc_isomSpace_of_isAlgebraicStack B S hS 𝒴 h𝒴 U _ _) _ d hds hdf hdc
      fun T u => (bijective_isomSpaceMap_app_iff B S hS 𝒳 𝒴 F a b (op T)).2
        ((bijective_morPresheafMap_app_iff B S hS 𝒳 𝒴 F a b _).2 (h T u))
  set T₀ : BigFppfOver B U.left.1 U.left.2 :=
    (Over.iteratedSliceEquiv U).functor.obj (Over.mk (𝟙 U))
  have h₀ : Function.Bijective ((hF.morPresheafMap a b).app (op (sliceObj B S hS U (op T₀)))) :=
    (bijective_isomSpaceMap_app_iff B S hS 𝒳 𝒴 F a b (op T₀)).1
      ((ConcreteCategory.isIso_iff_bijective _).1
        (inferInstanceAs (IsIso ((isomSpaceMap B S hS 𝒳 𝒴 F U a b).app (op T₀)))))
  exact Comma.bijective_fiberFunctor_map_of_bijective_app hF a b
    (Presheaf.bijective_app_of_iso (hF.morPresheafMap a b)
      ((Over.iteratedSliceEquiv U).unitIso.app (Over.mk (𝟙 U))) h₀)

/-- A morphism whose source and target lie over `R` and `k` lies over some morphism `R ⟶ k`. -/
private theorem exists_isHomLift_of_obj_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (p : 𝒟 ⥤ 𝒞)
    {R k : 𝒞} {x y : 𝒟} (φ : x ⟶ y) (hx : p.obj x = R) (hk : p.obj y = k) :
    ∃ h : R ⟶ k, p.IsHomLift h φ :=
  ⟨eqToHom hx.symm ≫ p.map φ ≫ eqToHom hk, IsHomLift.of_fac' _ _ _ hx hk (by simp)⟩

omit 𝒳 𝒴 F in
/-- **The base change of a surjective, flat, quasi-compact morphism, as an object over `V`.** For
morphisms `s : V ⟶ k` and `c : Ω ⟶ k` of the big fppf site of `S`, with `c` surjective, flat and
quasi-compact, the projection `V ×_k Ω ⟶ V` is again surjective, flat and quasi-compact, and every
object over `V` mapping to it has its composite with `s` factored through `c`. -/
theorem exists_fpqc_cover_factor (V : BigFppfOver B S hS) {k Ω : BigFppfOver B S hS}
    (s : V ⟶ k) (c : Ω ⟶ k) (hcs : Surjective (B.inclusion.map c.left))
    (hcf : Flat (B.inclusion.map c.left)) (hcc : QuasiCompact (B.inclusion.map c.left)) :
    ∃ d : BigFppfOver B V.left.1 V.left.2, Surjective (B.inclusion.map d.hom) ∧
      Flat (B.inclusion.map d.hom) ∧ QuasiCompact (B.inclusion.map d.hom) ∧
      ∀ (T : BigFppfOver B V.left.1 V.left.2) (_ : T ⟶ d),
        ∃ m : (sliceObj B S hS V (op T)).left ⟶ Ω, m ≫ c = (sliceObj B S hS V (op T)).hom ≫ s := by
  have hsq : IsPullback (B.inclusion.map (Limits.pullback.fst s.left c.left))
      (B.inclusion.map (Limits.pullback.snd s.left c.left))
      (B.inclusion.map s.left) (B.inclusion.map c.left) :=
    (IsPullback.of_hasPullback s.left c.left).map B.inclusion
  refine ⟨Over.mk (Limits.pullback.fst s.left c.left),
    MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hcs,
    MorphismProperty.of_isPullback (P := @Flat) hsq.flip hcf,
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hcc, fun T u => ?_⟩
  have hu : u.left ≫ Limits.pullback.fst s.left c.left = T.hom := Over.w u
  have hcond : Limits.pullback.fst s.left c.left ≫ s.left =
      Limits.pullback.snd s.left c.left ≫ c.left := Limits.pullback.condition
  refine ⟨Over.homMk (u.left ≫ Limits.pullback.snd s.left c.left) ?_, ?_⟩
  · show (u.left ≫ Limits.pullback.snd s.left c.left) ≫ Ω.hom = T.hom ≫ V.hom
    rw [← Over.w c, Category.assoc, ← Category.assoc (Limits.pullback.snd s.left c.left),
      ← hcond, Category.assoc, Over.w s, ← Category.assoc, hu]
  · apply Over.OverMorphism.ext
    show (u.left ≫ Limits.pullback.snd s.left c.left) ≫ c.left = T.hom ≫ s.left
    rw [Category.assoc, ← hcond, ← Category.assoc, hu]

/-- **Descent of goodness in the first variable.** Let `c : ζ ⟶ ζ₀` be a morphism of `𝒳` lying over
a surjective, flat, quasi-compact morphism `σ`. If `F` is bijective on the fibre morphisms
`a' ⟶ b'` whenever `a'` maps to `ζ` and `b'` maps to `ζ₁`, then it is bijective on the fibre
morphisms `a ⟶ b` whenever `a` maps to `ζ₀` and `b` maps to `ζ₁`.

The base change of `σ` along the base morphism `V ⟶ k` of `a ⟶ ζ₀` is an fpqc cover of `V`, and
over it the base change of `a` factors through `c`, `c` being strongly cartesian; so
`AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_fpqc` applies. -/
theorem bijective_fibreFunctor_map_of_isHomLift_descent
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    {Ω k : BigFppfOver B S hS} {ζ ζ₀ ζ₁ : 𝒳.val.obj} (σ : Ω ⟶ k) (c : ζ ⟶ ζ₀)
    (hc : 𝒳.val.p.IsHomLift σ c)
    (hσs : Surjective (B.inclusion.map σ.left)) (hσf : Flat (B.inclusion.map σ.left))
    (hσc : QuasiCompact (B.inclusion.map σ.left))
    (h : ∀ (W : BigFppfOver B S hS) (a' b' : 𝒳.val.p.Fiber W), Nonempty (a'.1 ⟶ ζ) →
      Nonempty (b'.1 ⟶ ζ₁) →
      Function.Bijective (fun m : a' ⟶ b' => (fibreFunctor B S hS 𝒳 𝒴 F W).map m))
    {V : BigFppfOver B S hS} (a b : 𝒳.val.p.Fiber V) (ha : Nonempty (a.1 ⟶ ζ₀))
    (hb : Nonempty (b.1 ⟶ ζ₁)) :
    Function.Bijective (fun m : a ⟶ b => (fibreFunctor B S hS 𝒳 𝒴 F V).map m) := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨φa⟩ := ha
  obtain ⟨φb⟩ := hb
  have hk : 𝒳.val.p.obj ζ₀ = k := IsHomLift.codomain_eq 𝒳.val.p σ c
  obtain ⟨s, hsl⟩ := exists_isHomLift_of_obj_eq 𝒳.val.p φa a.2 hk
  have hcart : 𝒳.val.p.IsStronglyCartesian σ c :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift σ c
  obtain ⟨d, hds, hdf, hdc, hfac⟩ := exists_fpqc_cover_factor B S hS V s σ hσs hσf hσc
  refine bijective_fibreFunctor_map_of_fpqc B S hS 𝒳 𝒴 F h𝒳 h𝒴 a b d hds hdf hdc
    fun T u => h _ _ _ ?_ ⟨Functor.IsPreFibered.pullbackMap b.2 _ ≫ φb⟩
  obtain ⟨m, hm⟩ := hfac T u
  exact ⟨Functor.IsStronglyCartesian.map 𝒳.val.p σ c (g := m) hm.symm
    (Functor.IsPreFibered.pullbackMap a.2 (sliceObj B S hS V (op T)).hom ≫ φa)⟩

/-- Bijectivity of a 1-morphism of categories fibred in groupoids on the fibre morphisms `a ⟶ b`
gives it on `b ⟶ a`: inversion is a bijection commuting with the functor. -/
theorem bijective_fibreFunctor_map_swap {V : BigFppfOver B S hS} (a b : 𝒳.val.p.Fiber V)
    (h : Function.Bijective (fun m : a ⟶ b => (fibreFunctor B S hS 𝒳 𝒴 F V).map m)) :
    Function.Bijective (fun m : b ⟶ a => (fibreFunctor B S hS 𝒳 𝒴 F V).map m) := by
  have := 𝒳.isFiberedInGroupoids.fiber_isGroupoid V
  have := 𝒴.isFiberedInGroupoids.fiber_isGroupoid V
  set e₁ : (a ⟶ b) ≃ (b ⟶ a) := ⟨fun m => inv m, fun m => inv m, fun m => by simp,
    fun m => by simp⟩
  set e₂ : ((fibreFunctor B S hS 𝒳 𝒴 F V).obj a ⟶ (fibreFunctor B S hS 𝒳 𝒴 F V).obj b) ≃
      ((fibreFunctor B S hS 𝒳 𝒴 F V).obj b ⟶ (fibreFunctor B S hS 𝒳 𝒴 F V).obj a) :=
    ⟨fun m => inv m, fun m => inv m, fun m => by simp, fun m => by simp⟩
  have hsq : (fun m : b ⟶ a => (fibreFunctor B S hS 𝒳 𝒴 F V).map m) ∘ e₁ =
      e₂ ∘ (fun m : a ⟶ b => (fibreFunctor B S hS 𝒳 𝒴 F V).map m) := by
    funext m
    simp [e₁, e₂, Functor.map_inv]
  rw [← Function.Bijective.of_comp_iff _ e₁.bijective, hsq]
  exact e₂.bijective.comp h

/-- **Descent of goodness.** Let `c : ζ ⟶ ζ₀` be a morphism of `𝒳` lying over a surjective, flat,
quasi-compact morphism. If `F` is bijective on the fibre morphisms between any two objects mapping
to `ζ`, it is bijective on the fibre morphisms between any two objects mapping to `ζ₀`: this is
`AlgebraicGeometry.Stack.bijective_fibreFunctor_map_of_isHomLift_descent` applied once in each
variable. -/
theorem bijective_fibreFunctor_map_of_isHomLift_descent₂
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val)
    {Ω k : BigFppfOver B S hS} {ζ ζ₀ : 𝒳.val.obj} (σ : Ω ⟶ k) (c : ζ ⟶ ζ₀)
    (hc : 𝒳.val.p.IsHomLift σ c)
    (hσs : Surjective (B.inclusion.map σ.left)) (hσf : Flat (B.inclusion.map σ.left))
    (hσc : QuasiCompact (B.inclusion.map σ.left))
    (h : ∀ (W : BigFppfOver B S hS) (a' b' : 𝒳.val.p.Fiber W), Nonempty (a'.1 ⟶ ζ) →
      Nonempty (b'.1 ⟶ ζ) →
      Function.Bijective (fun m : a' ⟶ b' => (fibreFunctor B S hS 𝒳 𝒴 F W).map m))
    {V : BigFppfOver B S hS} (a b : 𝒳.val.p.Fiber V) (ha : Nonempty (a.1 ⟶ ζ₀))
    (hb : Nonempty (b.1 ⟶ ζ₀)) :
    Function.Bijective (fun m : a ⟶ b => (fibreFunctor B S hS 𝒳 𝒴 F V).map m) :=
  bijective_fibreFunctor_map_of_isHomLift_descent B S hS 𝒳 𝒴 F h𝒳 h𝒴 σ c hc hσs hσf hσc
    (fun _ a' b' ha' hb' => bijective_fibreFunctor_map_swap B S hS 𝒳 𝒴 F b' a'
      (bijective_fibreFunctor_map_of_isHomLift_descent B S hS 𝒳 𝒴 F h𝒳 h𝒴 σ c hc hσs hσf hσc h
        b' a' hb' ha'))
    a b ha hb

/-- **An object of a fibre with a morphism to the image of `a` is in the essential image of the
induced functor on that fibre.** In a category fibred in groupoids the morphism is cartesian, and
so is the image of the chosen base change of `a` along its base morphism. -/
theorem essImage_fiberFunctor_of_hom
    {𝒜 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (G : 𝒜.val ⥤ᵇ 𝒳.val)
    {V : BigFppfOver B S hS} (z : 𝒳.val.p.Fiber V) (a : 𝒜.val.obj)
    (β : z.1 ⟶ G.obj a) :
    (Functor.fiberFunctorOfCompEq
      (isFibredOneMorphism_basedFunctor B S hS 𝒜 𝒳 G).comp_eq V).essImage z := by
  let : 𝒜.val.p.IsFibered := 𝒜.isFiberedInGroupoids.isFibered
  have ha : 𝒳.val.p.obj (G.obj a) = 𝒜.val.p.obj a := Functor.congr_obj G.w a
  obtain ⟨h, hβ⟩ := exists_isHomLift_of_obj_eq 𝒳.val.p β z.2 ha
  set ψ := Functor.IsPreFibered.pullbackMap (p := 𝒜.val.p) (rfl : 𝒜.val.p.obj a = _) h
  have hGψ : 𝒳.val.p.IsHomLift h (G.map ψ) := Functor.isHomLift_map_of_comp_eq G.w h ψ
  exact ⟨⟨_, Functor.IsPreFibered.pullbackObj_proj (rfl : 𝒜.val.p.obj a = _) h⟩,
    ⟨Functor.fiberIsoOfCartesian h (G.map ψ) β
      (𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift h
        (G.map ψ)).isCartesian_of_isStronglyCartesian
      (𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift h β).isCartesian_of_isStronglyCartesian⟩⟩

/-- **The self-product comparison being an equivalence is bijectivity on fibre morphisms.** Let
`Q : 𝒰 ⟶ 𝒵` and `H : 𝒵 ⟶ 𝒲` be 1-morphisms of categories fibred in groupoids. If postcomposition
with `H`, `𝒰 ×_𝒵 𝒰 ⥤ 𝒰 ×_𝒲 𝒰`, is an equivalence of categories, then for objects `a`, `b` of the
fibre of `𝒰` over `V`, `H` is bijective on the fibre morphisms `Q a ⟶ Q b`.

An object of `𝒰 ×_𝒵 𝒰` over `V` with legs `a` and `b` is exactly such a fibre morphism, and the
comparison does not change the legs. Faithfulness and fullness give injectivity; essential
surjectivity gives an object whose legs are isomorphic to `a` and `b`, and transporting its
comparison isomorphism along those gives the preimage. -/
theorem bijective_fibreFunctor_map_of_isEquivalence_mapBase
    {𝒰 𝒵 𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Q : 𝒰.val ⥤ᵇ 𝒵.val) (H : 𝒵.val ⥤ᵇ 𝒲.val)
    (hC : (TwoFibreProductOver.mapBase (pT := 𝒰.val.p) (p𝒜 := 𝒰.val.p) Q.toFunctor Q.toFunctor
      H.toFunctor H.w).IsEquivalence)
    {V : BigFppfOver B S hS} (a b : 𝒰.val.p.Fiber V) :
    Function.Bijective (fun m : (fibreFunctor B S hS 𝒰 𝒵 Q V).obj a ⟶
        (fibreFunctor B S hS 𝒰 𝒵 Q V).obj b => (fibreFunctor B S hS 𝒵 𝒲 H V).map m) := by
  set C := TwoFibreProductOver.mapBase (pT := 𝒰.val.p) (p𝒜 := 𝒰.val.p) Q.toFunctor Q.toFunctor
    H.toFunctor H.w with hCdef
  have h𝒵 := 𝒵.isFiberedInGroupoids.fiber_isGroupoid V
  have h𝒲 := 𝒲.isFiberedInGroupoids.fiber_isGroupoid V
  constructor
  · intro m₁ m₂ hm
    have hm' : H.toFunctor.map m₁.1 = H.toFunctor.map m₂.1 := congrArg Subtype.val hm
    have i₁ : IsIso m₁.1 := Functor.map_isIso Functor.Fiber.fiberInclusion m₁
    have i₂ : IsIso m₂.1 := Functor.map_isIso Functor.Fiber.fiberInclusion m₂
    let P₁ : TwoFibreProductOver 𝒰.val.p 𝒰.val.p 𝒵.val.p Q.toFunctor Q.toFunctor :=
      ⟨V, a.1, b.1, a.2, b.2, asIso m₁.1, m₁.2⟩
    let P₂ : TwoFibreProductOver 𝒰.val.p 𝒰.val.p 𝒵.val.p Q.toFunctor Q.toFunctor :=
      ⟨V, a.1, b.1, a.2, b.2, asIso m₂.1, m₂.2⟩
    let k : C.obj P₁ ⟶ C.obj P₂ :=
      { hbase := 𝟙 V
        a := 𝟙 a.1
        b := 𝟙 b.1
        ha := IsHomLift.id a.2
        hb := IsHomLift.id b.2
        w := by
          show (Q.toFunctor ⋙ H.toFunctor).map (𝟙 a.1) ≫ H.toFunctor.map m₂.1 =
            H.toFunctor.map m₁.1 ≫ (Q.toFunctor ⋙ H.toFunctor).map (𝟙 b.1)
          simp [hm'] }
    have hl : C.map (C.preimage k) = k := C.map_preimage k
    have ha : (C.preimage k).a = 𝟙 a.1 := congrArg TwoFibreProductOver.Hom.a hl
    have hb : (C.preimage k).b = 𝟙 b.1 := congrArg TwoFibreProductOver.Hom.b hl
    have hw := (C.preimage k).w
    rw [ha, hb] at hw
    exact Functor.Fiber.hom_ext (by simpa [P₁, P₂] using hw.symm : m₁.1 = m₂.1)
  · intro θ
    have iθ : IsIso θ.1 := Functor.map_isIso Functor.Fiber.fiberInclusion θ
    let Pθ : TwoFibreProductOver 𝒰.val.p 𝒰.val.p 𝒲.val.p (Q.toFunctor ⋙ H.toFunctor)
        (Q.toFunctor ⋙ H.toFunctor) :=
      ⟨V, a.1, b.1, a.2, b.2, asIso θ.1, θ.2⟩
    set P := C.objPreimage Pθ
    set e := C.objObjPreimageIso Pθ
    have hea : IsIso e.hom.a := ⟨e.inv.a, by
      rw [← TwoFibreProductOver.comp_a, e.hom_inv_id]; rfl, by
      rw [← TwoFibreProductOver.comp_a, e.inv_hom_id]; rfl⟩
    have heb : IsIso e.hom.b := ⟨e.inv.b, by
      rw [← TwoFibreProductOver.comp_b, e.hom_inv_id]; rfl, by
      rw [← TwoFibreProductOver.comp_b, e.inv_hom_id]; rfl⟩
    have hφ : H.toFunctor.map (Q.toFunctor.map (inv e.hom.a) ≫ P.iso.hom ≫
        Q.toFunctor.map e.hom.b) = θ.1 := by
      have hw : H.toFunctor.map (Q.toFunctor.map e.hom.a) ≫ θ.1 =
          H.toFunctor.map P.iso.hom ≫ H.toFunctor.map (Q.toFunctor.map e.hom.b) := e.hom.w
      simp only [Functor.map_comp, Functor.map_inv]
      rw [IsIso.inv_comp_eq, hw]
      exact H.toFunctor.map_comp _ _
    have hθ : 𝒲.val.p.IsHomLift (𝟙 V) θ.1 := θ.2
    rw [← hφ] at hθ
    exact ⟨⟨Q.toFunctor.map (inv e.hom.a) ≫ P.iso.hom ≫ Q.toFunctor.map e.hom.b,
      Functor.isHomLift_of_isHomLift_map_of_comp_eq H.w _ _ hθ⟩, Functor.Fiber.hom_ext hφ⟩

end Descent

end AlgebraicGeometry.Stack

end
