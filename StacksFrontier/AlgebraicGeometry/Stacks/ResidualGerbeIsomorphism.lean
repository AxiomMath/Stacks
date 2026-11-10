module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSelfProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# A self-product isomorphism makes the map of residual gerbes an isomorphism (Stacks 0DTI)

**Stacks 0DTI.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `x` be a point
of `|𝒳|` with image `y` in `|𝒴|`, and assume the residual gerbes `𝒵_x ⊂ 𝒳` and `𝒵_y ⊂ 𝒴` of `x`
and `y` exist. If there is a 1-morphism `Spec k ⟶ 𝒳` in the equivalence class of `x` for which the
comparison
```
  Spec k ×_𝒳 Spec k ⟶ Spec k ×_𝒴 Spec k
```
is an isomorphism, then the 1-morphism `𝒵_x ⟶ 𝒵_y` induced by `f` is an isomorphism.

## How the statement is rendered

Residual gerbes are not constructed in this library; what it has is the specification they are
asserted to satisfy uniquely, `AlgebraicGeometry.Stack.IsResidualGerbeAt` (the final assertion of
**Stacks 06MT**). So "`𝒵_x ⊂ 𝒳` exists" is read, as in
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFunctoriality`, as "the object property `P` of
`𝒳` satisfies that specification", `𝒵_x` is
`AlgebraicGeometry.Stack.fullSubcategoryAlgebraicStack 𝒳 P _` and the inclusion `𝒵_x ⟶ 𝒳` is
`AlgebraicGeometry.Stack.fullSubcategoryInclusion`. The induced 1-morphism `𝒵_x ⟶ 𝒵_y` is
`AlgebraicGeometry.Stack.residualGerbeMap`, the **Stacks 0DTH** map, at the membership statement
`AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`.

The comparison `Spec k ×_𝒳 Spec k ⟶ Spec k ×_𝒴 Spec k` is
`AlgebraicGeometry.Stack.selfProductTargetComparison` below: the 2-fibre products are the ones of
**Stacks 0040** over the big fppf site of `S`, and the comparison is
`CategoryTheory.TwoFibreProductOver.mapBase` at the functor underlying `f`, which postcomposes
both legs with it and leaves the two projections to `Spec k` untouched. That is exactly the
morphism the source names. "In the equivalence class of `x`" is spelled as in
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFieldPointFactorization` (**Stacks 06MW**):
the
source of the 1-morphism is the algebraic stack of an `AlgebraicGeometry.Stack.FieldSpectrum` and
some point of it maps to `x`. "Is an isomorphism", for the comparison and for the conclusion, is
rendered the way this library renders an isomorphism of algebraic stacks throughout: the
underlying functor is an equivalence of categories for the comparison, and for the conclusion the
stronger `CategoryTheory.Functor.IsEquivalenceOver` --- an equivalence in the 2-category of
fibred categories over the site, with a quasi-inverse strictly over the site and vertical unit and
counit --- which is what **Stacks 06MQ** produces.

## The proof

The source's proof has three steps. Its first two paragraphs show that the self-product condition
is independent of the chosen representative of `x` and then, presenting `𝒵_x` as `[Spec k/R]` with
`R = Spec k ×_𝒳 Spec k = Spec k ×_𝒴 Spec k`, that the composite `𝒵_x ⟶ 𝒳 ⟶ 𝒴` is fully faithful.
That is `AlgebraicGeometry.Stack.full_and_faithful_comp_of_hasSelfProductEquivalenceAt` of
`StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSelfProduct`, proved with no further input:
the
independence of the representative is fpqc descent on the sheaves of morphisms of `𝒳` and `𝒴`, and
the role of the presentation and of **Stacks 04T4 (6)** is played by the local-to-global step of
**Stacks 04WQ** along a surjective, flat, locally finitely presented cover of `𝒵_x`.

Its last sentence concludes, here by the route through **Stacks 06MQ** rather than through
Stacks 06MX: full faithfulness of `𝒵_x ⟶ 𝒵_y` is deduced from that of `𝒵_x ⟶ 𝒳 ⟶ 𝒴` by
cancelling the fully faithful inclusion `𝒵_y ⟶ 𝒴` against the Stacks 0DTH square, which commutes
on the nose; that makes `𝒵_x ⟶ 𝒵_y` a monomorphism by **Stacks 04ZZ** once it is known
to be representable by algebraic spaces; `𝒵_y` is reduced, locally Noetherian and one-point by its
residual-gerbe specification, hence covered by the spectrum of a field by the implication
(1) ⟹ (2) of **Stacks 06MP**; and `|𝒵_x|` is nonempty, again by its specification, which excludes
the empty alternative of **Stacks 06MQ**.

The source takes the representability of `𝒵_x ⟶ 𝒵_y`, and that of the inclusion `𝒵_y ⟶ 𝒴` behind
the Stacks 0DTH map (`AlgebraicGeometry.Stack.map_mem_of_isResidualGerbeAt`), from
**Stacks 04Y5**. The library has the implication (2) ⟹ (3) of Stacks 04Y5 as
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`,
fed with the bootstrap theorem Stacks 04S6 part (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.

## Main results

* `AlgebraicGeometry.Stack.full_and_faithful_of_comp_fullSubcategoryInclusion`: a 1-morphism into
  an algebraic full subcategory whose composite with the inclusion is fully faithful is itself
  fully faithful.
* `AlgebraicGeometry.Stack.isEquivalenceOver_residualGerbeMap_of_hasSelfProductEquivalenceAt`:
  **Stacks 0DTI**.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WQ](https://stacks.math.columbia.edu/tag/04WQ)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MW](https://stacks.math.columbia.edu/tag/06MW)
* [Stacks Project, Tag 06MX](https://stacks.math.columbia.edu/tag/06MX)
* [Stacks Project, Tag 0DTH](https://stacks.math.columbia.edu/tag/0DTH)
* [Stacks Project, Tag 0DTI](https://stacks.math.columbia.edu/tag/0DTI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ResidualGerbe

open Opposite

/-- **The comparison of self 2-fibre products induced by a 1-morphism of the target.** For
1-morphisms `q : 𝒰 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒲` of algebraic stacks over `S`, postcomposing both legs of
the 2-fibre product `𝒰 ×_𝒵 𝒰` of **Stacks 0040** with the functor underlying `h` gives a functor
`𝒰 ×_𝒵 𝒰 ⥤ 𝒰 ×_𝒲 𝒰`, strictly over both projections to `𝒰`.

With `𝒰` the algebraic stack of the spectrum of a field this is the morphism
`Spec k ×_𝒵 Spec k ⟶ Spec k ×_𝒲 Spec k` of **Stacks 0DTI**.

The name is *not* `selfProductComparison`: that name is already taken, in namespace
`AlgebraicGeometry.Stack`, by a different object ---
`AlgebraicGeometry.Stack.selfProductComparison` of
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonal`, a
`CategoryTheory.Bicategory.TwoCommSq.PreHom` comparing the canonical 2-fibre product of
`(f ≫ j, f ≫ j)` with a reindexed twice-pasted model of it. -/
def selfProductTargetComparison {𝒰 𝒵 𝒲 : AlgebraicStacks.{u, w} B S hS} (q : 𝒰 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒲) :
    TwoFibreProductOver 𝒰.val.val.p 𝒰.val.val.p 𝒵.val.val.p
        (CatFiberedInGroupoids.homFunctor q.hom) (CatFiberedInGroupoids.homFunctor q.hom) ⥤
      TwoFibreProductOver 𝒰.val.val.p 𝒰.val.val.p 𝒲.val.val.p
        (CatFiberedInGroupoids.homFunctor q.hom ⋙ CatFiberedInGroupoids.homFunctor h.hom)
        (CatFiberedInGroupoids.homFunctor q.hom ⋙ CatFiberedInGroupoids.homFunctor h.hom) :=
  TwoFibreProductOver.mapBase (CatFiberedInGroupoids.homFunctor q.hom)
    (CatFiberedInGroupoids.homFunctor q.hom) (CatFiberedInGroupoids.homFunctor h.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p h.hom)

/-- **The hypothesis of Stacks 0DTI.** There is a 1-morphism `q : Spec k ⟶ 𝒳` out of the algebraic
stack of the spectrum of a field, some point of which maps to `x` --- that is, `q` is in the
equivalence class of `x` --- such that the comparison
`Spec k ×_𝒳 Spec k ⟶ Spec k ×_𝒴 Spec k` of
`AlgebraicGeometry.Stack.selfProductTargetComparison` is an isomorphism, i.e. an equivalence of
the underlying categories. -/
abbrev HasSelfProductEquivalenceAt {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : AlgebraicStacks.points B S hS 𝒳) : Prop :=
  ∃ (F : FieldSpectrum B S hS) (q : schemeStack.{u, w} B S hS F.base ⟶ 𝒳)
    (t : AlgebraicStacks.points B S hS (schemeStack.{u, w} B S hS F.base)),
    AlgebraicStacks.pointsMap B S hS q t = x ∧
      (selfProductTargetComparison B S hS q f).IsEquivalence

/-- **A residual gerbe satisfies condition (1) of Stacks 06MP.** The specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT** asks of the full subcategory it
selects that it be a reduced, locally Noetherian algebraic stack with exactly one point, lying
over the given point; forgetting which point that is leaves condition (1) of **Stacks 06MP**. -/
theorem isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : AlgebraicStacks.points B S hS 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P) :
    IsReducedLocallyNoetherianWithUniquePoint B S hS
      (fullSubcategoryAlgebraicStack 𝒳 P hP.2.choose) := by
  obtain ⟨z, huniq, -⟩ := hP.2.choose_spec.2.2
  exact ⟨⟨hP.2.choose_spec.1, ⟨z⟩, ⟨fun a b => (huniq a).trans (huniq b).symm⟩⟩,
    hP.2.choose_spec.2.1⟩

/-- **The first two paragraphs of the proof of Stacks 0DTI.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, let `x` be a point of `|𝒳|` and let `P` be a residual gerbe of `𝒳` at
`x`. If some 1-morphism from the spectrum of a field to `𝒳` in the equivalence class of `x` has
its self-product comparison over `𝒳` and over `𝒴` an equivalence, then the composite
`𝒵_x ⟶ 𝒳 ⟶ 𝒴` is fully faithful.

See the module documentation for the three steps: the self-product condition at the given
representative, its transport to a surjective, flat, locally finitely presented cover of `𝒵_x`
by fpqc descent along a common refinement, and the local-to-global step along that cover. -/
theorem full_and_faithful_comp_of_hasSelfProductEquivalenceAt
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (x : AlgebraicStacks.points B S hS 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hx : IsResidualGerbeAt B S hS 𝒳 x P) (hself : HasSelfProductEquivalenceAt B S hS f x) :
    (CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒳 P hP ≫ f).hom).Full ∧
      (CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒳 P hP ≫ f).hom).Faithful := by
  classical
  set 𝒵 := fullSubcategoryAlgebraicStack 𝒳 P hP with h𝒵
  set ι := fullSubcategoryInclusion 𝒳 P hP with hι
  let : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  let : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  let : 𝒵.val.val.p.IsFibered := 𝒵.val.isFiberedInGroupoids.isFibered
  -- the good objects of `𝒳`: `f` is bijective on the fibre morphisms between any two objects
  -- mapping to them
  let Good : 𝒳.val.val.obj → Prop := fun ξ => ∀ (W : BigFppfOver B S hS)
    (a b : 𝒳.val.val.p.Fiber W), Nonempty (a.1 ⟶ ξ) → Nonempty (b.1 ⟶ ξ) →
      Function.Bijective (fun m : a ⟶ b => (fibreFunctor B S hS 𝒳.val 𝒴.val f.hom.hom W).map m)
  have good_of_hom : ∀ {ξ ξ' : 𝒳.val.val.obj}, (ξ' ⟶ ξ) → Good ξ → Good ξ' :=
    fun e hξ W a b ⟨φa⟩ ⟨φb⟩ => hξ W a b ⟨φa ≫ e⟩ ⟨φb ≫ e⟩
  -- the self-product condition makes the image of the tautological object good
  obtain ⟨F, q, t, hqt, hC⟩ := hself
  set a₀ : (schemeStack.{u, w} B S hS F.base).val.val.obj := Over.mk (𝟙 F.base)
  have good₀ : Good (q.hom.hom.obj a₀) := by
    intro W a b ⟨φa⟩ ⟨φb⟩
    obtain ⟨a', ⟨ia⟩⟩ := essImage_fiberFunctor_of_hom B S hS 𝒳.val q.hom.hom a a₀ φa
    obtain ⟨b', ⟨ib⟩⟩ := essImage_fiberFunctor_of_hom B S hS 𝒳.val q.hom.hom b a₀ φb
    exact Functor.bijective_map_of_isos _ ia ib
      (bijective_fibreFunctor_map_of_isEquivalence_mapBase B S hS q.hom.hom f.hom.hom hC a' b')
  -- a representative of `x` through `q`
  obtain ⟨t₀, rfl⟩ := Quotient.exists_rep t
  set pq := fieldValuedPointMap B S hS _ q.hom.hom t₀ with hpq
  have hpqx : pointClass B S hS 𝒳.val.val (Classical.choose 𝒳.property) pq = x := hqt
  have hpq₀ : pq.obj ⟶ q.hom.hom.obj a₀ :=
    q.hom.hom.map (Over.homMk t₀.obj.hom (Category.comp_id _) : t₀.obj ⟶ a₀)
  -- a surjective flat cover of the residual gerbe, locally of finite presentation
  obtain ⟨Fk, c, hclfp, hcsurj, hcflat⟩ :=
    hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian B S hS 𝒵
      (isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt B S hS 𝒳 x P hx)
  set c₀ : (schemeStack.{u, w} B S hS Fk.base).val.val.obj := Over.mk (𝟙 Fk.base)
  set ξk : 𝒳.val.val.obj := (c ≫ ι).hom.hom.obj c₀ with hξk
  have hξkover : 𝒳.val.val.p.obj ξk = Fk.base := Functor.congr_obj (c ≫ ι).hom.hom.w c₀
  let pk𝒵 : FieldValuedPoint B S hS 𝒵.val.val :=
    ⟨Fk.carrier, Fk.base, Fk.isSpec, c.hom.hom.obj c₀, Functor.congr_obj c.hom.hom.w c₀⟩
  set pk := fieldValuedPointMap B S hS _ ι.hom.hom pk𝒵 with hpk
  have hpkx : pointClass B S hS 𝒳.val.val (Classical.choose 𝒳.property) pk = x :=
    pointsMap_eq_of_isResidualGerbeAt B S hS hx hP
      (pointClass B S hS 𝒵.val.val (Classical.choose 𝒵.property) pk𝒵)
  obtain ⟨r, ⟨ρq⟩, ⟨ρk⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val
    (Classical.choose 𝒳.property) pq pk).mp (hpqx.trans hpkx.symm)
  have goodr : Good r.obj := good_of_hom (ρq ≫ hpq₀) good₀
  -- descent along the extension of fields underlying `ρk`
  obtain ⟨hσs, hσf, hσc⟩ := surjective_flat_quasiCompact_fieldValuedPointBaseMap B S hS
    (𝒳 := 𝒳) (p := pk) (t := r) ρk
  have hlift : 𝒳.val.val.p.IsHomLift (fieldValuedPointBaseMap B S hS ρk) ρk :=
    IsHomLift.of_fac' 𝒳.val.val.p (fieldValuedPointBaseMap B S hS ρk) ρk r.over pk.over
      (by simp [fieldValuedPointBaseMap])
  have goodk : Good pk.obj := fun W a b ha hb =>
    bijective_fibreFunctor_map_of_isHomLift_descent₂ B S hS 𝒳.val 𝒴.val f.hom.hom 𝒳.property
      𝒴.property _ ρk hlift hσs hσf hσc goodr a b ha hb
  -- every object of the residual gerbe is fppf locally a base change of the cover
  set hG := isFibredOneMorphism_basedFunctor B S hS
    (schemeStack.{u, w} B S hS Fk.base).val 𝒵.val c.hom.hom
  set hH := isFibredOneMorphism_basedFunctor B S hS 𝒵.val 𝒴.val (ι ≫ f).hom.hom
  have hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒵)) =
      ⋃ _ : Unit, Set.range (AlgebraicStacks.pointsMap B S hS c) := by
    rw [Set.iUnion_const, hcsurj.range_eq]
  have hGobj : ∀ (U : BigFppfOver B S hS) (y : 𝒵.val.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U, ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄,
        R.arrows k → (Functor.fiberFunctorOfCompEq hG.comp_eq V).essImage
          (Functor.pullbackFiber 𝒵.val.val.p y k) := by
    intro U y
    obtain ⟨R, hR, hRlift⟩ := exists_fppfCovering_fibre_lift_of_family B S hS
      (𝒳 := fun _ : Unit => schemeStack.{u, w} B S hS Fk.base) (𝒴 := 𝒵)
      (fun _ => c) (fun _ => hcflat) (fun _ => hclfp) hjs U y
    refine ⟨R, hR, fun V k hk => ?_⟩
    obtain ⟨-, x₀, α, hα⟩ := hRlift hk
    have hcart : 𝒵.val.val.p.IsStronglyCartesian k α :=
      𝒵.val.isFiberedInGroupoids.isStronglyCartesian_homLift k α
    exact essImage_fiberFunctor_of_hom B S hS 𝒵.val c.hom.hom _ x₀
      (Functor.IsStronglyCartesian.map 𝒵.val.val.p k α (g := 𝟙 V) (f' := k)
        (Category.id_comp k).symm
        (Functor.IsPreFibered.pullbackMap y.2 k))
  -- on base changes of the cover, `ι ≫ f` is bijective on fibre morphisms
  have hbij : ∀ {V : BigFppfOver B S hS} {z y : 𝒵.val.val.p.Fiber V},
      (Functor.fiberFunctorOfCompEq hG.comp_eq V).essImage z →
      (Functor.fiberFunctorOfCompEq hG.comp_eq V).essImage y →
      Function.Bijective (fun m : z ⟶ y => (Functor.fiberFunctorOfCompEq hH.comp_eq V).map m) := by
    intro V z y hz hy
    have hto : ∀ {w : 𝒵.val.val.p.Fiber V},
        (Functor.fiberFunctorOfCompEq hG.comp_eq V).essImage w →
          Nonempty (((fibreFunctor B S hS 𝒵.val 𝒳.val ι.hom.hom V).obj w).1 ⟶ pk.obj) := by
      rintro w ⟨a, ⟨i⟩⟩
      exact ⟨ι.hom.hom.map (i.inv.1 ≫ c.hom.hom.map
        (Over.homMk a.1.hom (Category.comp_id _) : a.1 ⟶ c₀))⟩
    have hι : Function.Bijective (fun m : z ⟶ y =>
        (fibreFunctor B S hS 𝒵.val 𝒳.val ι.hom.hom V).map m) := by
      refine ⟨fun m₁ m₂ hm => Functor.Fiber.hom_ext
        (ι.hom.hom.toFunctor.map_injective (congrArg Subtype.val hm)), fun n => ?_⟩
      have hn : 𝒳.val.val.p.IsHomLift (𝟙 V) (ι.hom.hom.toFunctor.map
          (ι.hom.hom.toFunctor.preimage n.1)) := by
        rw [Functor.map_preimage]
        exact n.2
      exact ⟨⟨ι.hom.hom.toFunctor.preimage n.1,
        Functor.isHomLift_of_isHomLift_map_of_comp_eq ι.hom.hom.w _ _ hn⟩,
        Functor.Fiber.hom_ext (ι.hom.hom.toFunctor.map_preimage n.1)⟩
    exact (goodk V _ _ (hto hz) (hto hy)).comp hι
  have hfib : ∀ (U : BigFppfOver B S hS) (z z' : 𝒵.val.val.p.Fiber U),
      Function.Bijective (fun m : z ⟶ z' => (Functor.fiberFunctorOfCompEq hH.comp_eq U).map m) := by
    intro U z z'
    have h1 := Functor.Stackification.isLocallyInjective_morPresheafMap_of_essImage hG hH
      (BigFppfOver.topology B S hS) hbij hGobj U z z'
    have h2 := Functor.Stackification.isLocallySurjective_morPresheafMap_of_essImage hG hH
      (BigFppfOver.topology B S hS) hbij hGobj U z z'
    have hiso := Presheaf.isIso_of_isLocallyBijective ((BigFppfOver.topology B S hS).over U)
      (hH.morPresheafMap z z')
      ((isStack_of_isAlgebraicStack.{u, w} B S hS 𝒵.property).isMorSheaf U z z')
      ((isStack_of_isAlgebraicStack.{u, w} B S hS 𝒴.property).isMorSheaf U _ _)
    refine Comma.bijective_fiberFunctor_map_of_bijective_app hH _ _ ?_
    rw [← isIso_iff_bijective]
    infer_instance
  exact ⟨Comma.full_of_fiber_full hH fun U => ⟨fun {z z'} ψ => (hfib U z z').2 ψ⟩,
    Comma.faithful_of_fiber_faithful hH fun U => ⟨fun {z z'} m n hmn => (hfib U z z').1 hmn⟩⟩

end ResidualGerbe

/-- **Cancelling an algebraic full subcategory inclusion off full faithfulness.** If the composite
of a 1-morphism `g` of algebraic stacks over `S` with the inclusion of an algebraic full
subcategory of its target is fully faithful, then `g` is fully faithful.

The inclusion of a full subcategory is faithful, which is what lets fullness be cancelled. -/
theorem full_and_faithful_of_comp_fullSubcategoryInclusion
    {𝒵 𝒴 : AlgebraicStacks.{u, w} B S hS} (Q : ObjectProperty 𝒴.val.val.obj)
    (hQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 Q))
    (g : 𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒴 Q hQ) (j : 𝒵 ⟶ 𝒴)
    (hj : g ≫ fullSubcategoryInclusion 𝒴 Q hQ = j)
    (hfull : (CatFiberedInGroupoids.homFunctor j.hom).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor j.hom).Faithful) :
    (CatFiberedInGroupoids.homFunctor g.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor g.hom).Faithful := by
  subst hj
  have : (CatFiberedInGroupoids.homFunctor g.hom ⋙
    CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒴 Q hQ).hom).Full := hfull
  have : (CatFiberedInGroupoids.homFunctor g.hom ⋙
    CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒴 Q hQ).hom).Faithful := hfaithful
  have : (CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒴 Q hQ).hom).Faithful :=
    faithful_fullSubcategoryInclusion 𝒴 Q hQ
  exact ⟨Functor.Full.of_comp_faithful (CatFiberedInGroupoids.homFunctor g.hom)
      (CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒴 Q hQ).hom),
    Functor.Faithful.of_comp (CatFiberedInGroupoids.homFunctor g.hom)
      (CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒴 Q hQ).hom)⟩

/-- **Stacks 0DTI.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `x` be a
point of `|𝒳|` and let the object properties `P` of `𝒳` and `Q` of `𝒴` be residual gerbes of `𝒳`
at `x` and of `𝒴` at the image of `x`, in the sense of the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of **Stacks 06MT**. If there is a 1-morphism from the
algebraic stack of the spectrum of a field to `𝒳` in the equivalence class of `x` whose
self-product comparison over `𝒳` and over `𝒴` is an equivalence, then the 1-morphism
`𝒵_x ⟶ 𝒵_y` induced by `f` --- the **Stacks 0DTH** map
`AlgebraicGeometry.Stack.residualGerbeMap` --- is an isomorphism: an equivalence over the big
fppf site of `S`.

The proof is the source's. Full faithfulness of `𝒵_x ⟶ 𝒳 ⟶ 𝒴`, the source's first two
paragraphs, is `AlgebraicGeometry.Stack.full_and_faithful_comp_of_hasSelfProductEquivalenceAt`.
The concluding sentence is taken through **Stacks 06MQ**: the **Stacks 0DTH** square commutes on
the nose, so cancelling the faithful inclusion `𝒵_y ⟶ 𝒴` makes `𝒵_x ⟶ 𝒵_y` fully faithful, hence
a monomorphism by the implication (2) ⟹ (1) of **Stacks 04ZZ** once it is known representable by
algebraic spaces. The residual gerbe `𝒵_y` is reduced, locally Noetherian and one-point by its
specification, so it is covered by the spectrum of a field by the implication (1) ⟹ (2) of
**Stacks 06MP**, and `|𝒵_x|` is nonempty by its own specification, which rules out the empty
alternative of Stacks 06MQ.

The representability of `𝒵_x ⟶ 𝒵_y`, and of the inclusion `𝒵_y ⟶ 𝒴` behind the Stacks 0DTH map,
is what the source takes from Stacks 04Y5; the library has the implication (2) ⟹ (3) of
Stacks 04Y5 from the bootstrap theorem Stacks 04S6 part (3). -/
@[stacks 0DTI]
theorem isEquivalenceOver_residualGerbeMap_of_hasSelfProductEquivalenceAt
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (x : AlgebraicStacks.points B S hS 𝒳)
    (P : ObjectProperty 𝒳.val.val.obj) (Q : ObjectProperty 𝒴.val.val.obj)
    (hx : IsResidualGerbeAt B S hS 𝒳 x P)
    (hy : IsResidualGerbeAt B S hS 𝒴 (AlgebraicStacks.pointsMap B S hS f x) Q)
    (hself : HasSelfProductEquivalenceAt B S hS f x) :
    Nonempty (Functor.IsEquivalenceOver
      (fullSubcategoryAlgebraicStack 𝒳 P hx.2.choose).val.val.p
      (fullSubcategoryAlgebraicStack 𝒴 Q hy.2.choose).val.val.p
      (CatFiberedInGroupoids.homFunctor
        (residualGerbeMap B S hS f hx.2.choose hy.2.choose
          (map_mem_of_isResidualGerbeAt B S hS f x _ rfl hx hy)).hom)) := by
  classical
  set hmem := map_mem_of_isResidualGerbeAt B S hS f x _ rfl hx hy
  obtain ⟨hcfull, hcfaithful⟩ :=
    full_and_faithful_comp_of_hasSelfProductEquivalenceAt B S hS f x P hx.2.choose hx hself
  obtain ⟨hgfull, hgfaithful⟩ := full_and_faithful_of_comp_fullSubcategoryInclusion B S hS Q
    hy.2.choose (residualGerbeMap B S hS f hx.2.choose hy.2.choose hmem)
    (fullSubcategoryInclusion 𝒳 P hx.2.choose ≫ f)
    (residualGerbeMap_comp_inclusion B S hS f hx.2.choose hy.2.choose hmem) hcfull hcfaithful
  obtain ⟨z, -, -⟩ := hx.2.choose_spec.2.2
  exact (isEmpty_points_or_isEquivalenceOver_of_isMonomorphism B S hS
    (fullSubcategoryAlgebraicStack 𝒳 P hx.2.choose)
    (fullSubcategoryAlgebraicStack 𝒴 Q hy.2.choose)
    (residualGerbeMap B S hS f hx.2.choose hy.2.choose hmem)
    (AlgebraicStacks.isMonomorphism_of_full_and_faithful B S hS _ hgfull hgfaithful)
    (hasLocallyOfFinitePresentationFlatFieldCover_of_isReducedLocallyNoetherian B S hS
      (fullSubcategoryAlgebraicStack 𝒴 Q hy.2.choose)
      (isReducedLocallyNoetherianWithUniquePoint_of_isResidualGerbeAt B S hS 𝒴
        (AlgebraicStacks.pointsMap B S hS f x) Q hy))).resolve_left fun h => h.elim z

end AlgebraicGeometry.Stack

end
