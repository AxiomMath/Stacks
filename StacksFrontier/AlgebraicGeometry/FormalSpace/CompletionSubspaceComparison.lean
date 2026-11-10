module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceBaseChange
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.NilpotentUnits
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Equivalence
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# Comparing the two completions of an algebraic space along a closed subspace

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊆ X` be a closed subspace with point set `T = |Z|`. There are two formal algebraic
spaces attached to this datum:

* the completion `X^∧_Z = colim Z_n` of `X` along the closed subspace `Z`, the colimit of the
  infinitesimal neighbourhoods of `Z` in `X`, which is
  `AlgebraicGeometry.Space.completionSubspace` of Stacks 0GXU; and
* the completion `X_{/T}` of `X` along the closed *subset* `T`, which is
  `AlgebraicGeometry.Space.completionSheaf` of Stacks 0AIX.

Both are sheafifications of subfunctors of the universe lift of `X`, and the first subfunctor
is contained in the second: a section of `X` whose inverse image of `Z` is a thickening has
all of its field-valued points factoring through `Z`. This file constructs the resulting
canonical morphism `c : X^∧_Z ⟶ X_{/T}`.

## Main definitions

* `AlgebraicGeometry.Space.completionSubspaceComparison` is the canonical morphism
  `c : X^∧_Z ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.Space.isIso_completionSubspaceComparison`: **Stacks 0H8N**, the positive
  half: `c` is an isomorphism when `Z ⟶ X` is of finite presentation.
* `AlgebraicGeometry.Space.hasImageIn_of_mem_completionSubspaceSubfunctor` and
  `AlgebraicGeometry.Space.completionSubspaceSubfunctor_le_completionSubfunctor`: a section of
  `X` lying in the union of the infinitesimal neighbourhoods of `Z` has point-set image in
  `T = |Z|`, so the subfunctor defining `X^∧_Z` is contained in the one defining `X_{/T}`.
* `AlgebraicGeometry.Space.completionSubspaceComparison_comp_completionSheafInclusion`: the
  comparison is a morphism over `X`.

## What is not proved

Stacks 0H8N also asserts that `c` is **not** an isomorphism in general. That assertion is not
formalized here. It is only formalizable with the source's counterexample —
`A = ℤ[x₁, x₂, …]`, `Z` cut out by `I = (x₁, x₂, …)`, and the section
`Spec(A/(xₙⁿ, n ≥ 1)) ⟶ Spec A`, which is supported on `|Z|` but factors through no
infinitesimal neighbourhood of `Z`, not even after an fppf covering — and this library has no
such example. Nothing weaker is stated in its place.

## Implementation notes

The containment of subfunctors is checked on a field-valued point `p` of the object `U`
carrying the section `g`. The completion subfunctor of `Z` asks the inverse image `g⁻¹(Z)` to
be an `n`th-order thickening *universally*, so in particular after base change along
`p : Spec(k) ⟶ U`; that base change is the inverse image of `Z` along the composite
`Spec(k) ⟶ U ⟶ X`, by `CategoryTheory.Subfunctor.preimage_comp` and
`CategoryTheory.yonedaEquiv_symm_map`. Being a thickening it is surjective on points, and
`Spec(k)` has exactly one point
(`AlgebraicGeometry.Space.subsingleton_points_yoneda_siteObject`), so that point comes from
the inverse image and its image in `|X|` — which is the point represented by `p` composed
with `g`, by `AlgebraicGeometry.Space.FieldValuedPoint.pointsMap_eq_class` — lies in `|Z|`.

Only the topological clause of a thickening is used, so the containment needs no hypothesis on
`Z` at all: it holds for an arbitrary subfunctor of `X`, exactly as the two completions are
constructed for an arbitrary subfunctor and an arbitrary set of points.

Invertibility of `c` is local bijectivity of that inclusion of subfunctors, by
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`: the inclusion is injective on sections, and
it is locally surjective because the affine objects of the site are a dense subsite (Stacks
021V) and over an affine object the two subfunctors agree. That last point is the mathematical
content, and it is where finite presentation of `Z ⟶ X` enters: the inverse image of `Z` along a
section over an affine object is a closed subspace cut out by a finitely generated ideal (Stacks
084Q read on the identity chart, which is a surjective étale chart of a representable space),
the section being supported on `|Z|` makes that closed immersion surjective, hence its ideal
lies in the nilradical (the topological criterion of Stacks 09NY), and a finitely generated
ideal inside the nilradical is nilpotent. The resulting order bounds every base change at once,
because a base change of an `n`th-order thickening of schemes is one (Stacks 09ZU) and
`CategoryTheory.MorphismProperty.relative` records exactly that uniformity.

Passing from the vanishing power of the kernel ideal *sheaf* to the vanishing power of the
kernel on *global sections*, which is what
`AlgebraicGeometry.Space.definingIdealAt` is, is
`AlgebraicGeometry.Scheme.ker_appTop_pow_eq_bot`; the target of a chart is not assumed affine,
so `AlgebraicGeometry.Scheme.ker_pow_eq_bot_iff_of_isAffine` does not apply there.

## References

* [Stacks Project, Tag 0GXT](https://stacks.math.columbia.edu/tag/0GXT)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
* [Stacks Project, Tag 0H8N](https://stacks.math.columbia.edu/tag/0H8N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point set of a subspace -/

/-- The point set `|Z|` of a subfunctor `Z` of a presheaf `X` on the big fppf site of `S`:
the image of the point set of `Z` in that of `X`. -/
abbrev subspacePoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Z : Subfunctor X) :
    Set (points B S hS X) :=
  Set.range (pointsMap B S hS Z.toFunctor Z.ι)

/-! ### The infinitesimal neighbourhoods are supported on the point set -/

/-- A section of `X` lying in the union of the infinitesimal neighbourhoods of a subfunctor
`Z` of `X` has point-set image in `|Z|`.

Indeed its inverse image of `Z` is universally a finite-order thickening, so after base change
along a field-valued point `p` of the carrying object it is a thickening of the spectrum of a
field; being surjective on points it accounts for the unique point there, whose image in `|X|`
is the point represented by `p` composed with the section. -/
theorem hasImageIn_of_mem_completionSubspaceSubfunctor
    (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) (U : BigFppfOver B S hS)
    (g : X.1.obj (op U))
    (hg : (ULift.up g : (X.1 ⋙ uliftFunctor.{u + 1}).obj (op U)) ∈
      (completionSubspaceSubfunctor B S hS X Z).obj (op U)) :
    HasImageIn B S hS X.1 (subspacePoints B S hS Z) U g := by
  obtain ⟨n, hn⟩ := hg
  intro p
  -- The base change of the inverse image of `Z` along `p` is the inverse image of `Z`
  -- along the composite `Spec(k) ⟶ U ⟶ X`.
  set h : yoneda.obj p.siteObject ⟶ X.1 :=
    yonedaEquiv.symm (X.1.map p.value.op g) with hh
  have hsub : ((Z.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)).preimage
      (yoneda.map p.value) : Subfunctor (yoneda.obj p.siteObject)) = Z.preimage h := by
    rw [← Subfunctor.preimage_comp, hh, yonedaEquiv_symm_map p.value.op g]
    rfl
  have hsurj₀ : Function.Surjective (pointsMap B S hS
      ((Z.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)).preimage
          (yoneda.map p.value) : Subfunctor (yoneda.obj p.siteObject)).toFunctor
      ((Z.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)).preimage
          (yoneda.map p.value) : Subfunctor (yoneda.obj p.siteObject)).ι) :=
    (hn p.siteObject (yoneda.map p.value)).1.2
  rw [hsub] at hsurj₀
  -- The spectrum of a field has one point, which therefore comes from the inverse image.
  set q : FieldValuedPoint B S hS X.1 :=
    ⟨p.carrier, p.contained, p.toBase, X.1.map p.value.op g⟩ with hq
  obtain ⟨y, hy⟩ := hsurj₀
    ((FieldValuedPoint.tautological B S hS q).class B S hS (yoneda.obj p.siteObject))
  refine ⟨pointsMap B S hS (Z.preimage h).toFunctor (Z.fromPreimage h) y, ?_⟩
  have e₁ := congrFun
    (pointsMap_comp B S hS (Z.preimage h).toFunctor (Z.fromPreimage h) Z.ι) y
  have e₂ := congrFun
    (pointsMap_comp B S hS (Z.preimage h).toFunctor (Z.preimage h).ι h) y
  simp only [Function.comp_apply] at e₁ e₂
  rw [← e₁, Subfunctor.fromPreimage_ι, e₂, hy]
  exact FieldValuedPoint.pointsMap_eq_class B S hS q _

/-- The subfunctor of sections of `X` lying in the union of the infinitesimal neighbourhoods
of `Z` is contained in the subfunctor of sections with point-set image in `|Z|`. -/
theorem completionSubspaceSubfunctor_le_completionSubfunctor
    (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    completionSubspaceSubfunctor B S hS X Z ≤
      completionSubfunctor B S hS X.1 (subspacePoints B S hS Z) :=
  fun U g hg ↦ hasImageIn_of_mem_completionSubspaceSubfunctor B S hS X Z U.unop g.down hg

/-! ### The canonical comparison morphism -/

/-- **The canonical morphism `c : X^∧_Z ⟶ X_{/T}`** comparing the completion of an algebraic
space `X` over `S` along a closed subspace `Z` with its completion along the point set
`T = |Z|`: the sheafification of the inclusion of the union of the infinitesimal
neighbourhoods of `Z` into the subfunctor of sections supported on `T`. -/
def completionSubspaceComparison (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    completionSubspace B S hS X Z ⟶
      completionSheaf B S hS X.1 (subspacePoints B S hS Z) :=
  ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (Subfunctor.homOfLe
      (completionSubspaceSubfunctor_le_completionSubfunctor B S hS X Z)))

/-- The comparison morphism is a morphism over `X`: composing it with the inclusion of
`X_{/T}` into `X` gives the inclusion of `X^∧_Z` into `X`. -/
theorem completionSubspaceComparison_comp_completionSheafInclusion
    (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    completionSubspaceComparison B S hS X Z ≫
        completionSheafInclusion B S hS X.1 (subspacePoints B S hS Z) =
      completionSubspaceToAmbient B S hS X Z := by
  apply Sheaf.hom_ext
  change (BigFppfOver.topology B S hS).sheafifyMap _ ≫
      (BigFppfOver.topology B S hS).sheafifyMap _ =
    (BigFppfOver.topology B S hS).sheafifyMap _
  rw [← GrothendieckTopology.sheafifyMap_comp]
  exact congrArg (BigFppfOver.topology B S hS).sheafifyMap
    (Subfunctor.homOfLe_ι
      (completionSubspaceSubfunctor_le_completionSubfunctor B S hS X Z))

/-! ### The order of a thickening as a property of morphisms of schemes -/

/-- A closed subspace of a representable algebraic space is *represented by `n`th-order
thickenings* when every represented base change of its inclusion is an `n`th-order thickening
of schemes. -/
abbrev IsRepresentedAtOrder (n : ℕ) {V : BigFppfOver B S hS}
    (G : Subfunctor (yoneda.obj V)) : Prop :=
  (MorphismProperty.inverseImage (thickOrder.{u} n)
    (BigFppfOver.toScheme B S hS)).presheaf G.ι

/-- A closed subspace of a representable algebraic space is *represented by `n`th-order
thickenings* when every represented base change of its inclusion is an `n`th-order thickening
of schemes.

The file-private form of `IsRepresentedAtOrder`. -/
private abbrev IsRepresentedNthOrder (n : ℕ) {V : BigFppfOver B S hS}
    (G : Subfunctor (yoneda.obj V)) : Prop :=
  IsRepresentedAtOrder (hS := hS) (S := S) (B := B) (n := n) (V := V) (G := G)

/-- A closed subspace of a representable algebraic space all of whose represented base changes
are `n`th-order thickenings of schemes is an `n`th-order thickening of algebraic spaces.

The topological clause is the surjectivity of the base change along the identity chart, read on
points through `AlgebraicGeometry.Space.surjective_pointsMap_yoneda_iff`; the ideal clause is
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`, which presents the defining ideal on an étale
chart as the kernel on global sections of the base-changed closed immersion, together with
`AlgebraicGeometry.Scheme.ker_appTop_pow_eq_bot`, which passes from the vanishing of the power
of the kernel ideal sheaf to the vanishing of the power of that kernel. -/
theorem isNthOrderThickening_of_isRepresentedAtOrder (n : ℕ)
    {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) (hQ : IsRepresentedAtOrder B S hS n G) :
    IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj V) G := by
  have hsurj : Function.Surjective (pointsMap B S hS G.toFunctor G.ι) := by
    have hsq := hG.2.rep.isPullback (𝟙 (yoneda.obj V))
    have hn : Stacks.Thickenings.IsNthOrderThickening n
        ((BigFppfOver.toScheme B S hS).map (hG.2.rep.snd (𝟙 (yoneda.obj V)))) :=
      hQ.property_snd (𝟙 (yoneda.obj V))
    have hs0 := (surjective_pointsMap_yoneda_iff B S hS
      (hG.2.rep.snd (𝟙 (yoneda.obj V)))).2 hn.isThickening.2
    have hw : hG.2.rep.fst (𝟙 (yoneda.obj V)) ≫ G.ι =
        yoneda.map (hG.2.rep.snd (𝟙 (yoneda.obj V))) := by
      exact hsq.w.trans (Category.comp_id _)
    rw [← hw, pointsMap_comp] at hs0
    exact hs0.of_comp
  refine ⟨⟨hG, hsurj⟩, fun W ↦ ?_⟩
  -- The chart morphism, read with the target spelled as the representable presheaf.
  have hn : Stacks.Thickenings.IsNthOrderThickening n
      ((BigFppfOver.toScheme B S hS).map
        (hG.2.rep.snd (W.1.hom : yoneda.obj W.1.left ⟶ yoneda.obj V))) :=
    hQ.property_snd _
  have hkey : RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (hG.2.rep.snd (W.1.hom : yoneda.obj W.1.left ⟶ yoneda.obj V))).appTop.hom ^ (n + 1) =
      ⊥ :=
    Scheme.ker_appTop_pow_eq_bot _ (by have := hn.1; infer_instance) hn.2
  rw [definingIdealAt_eq_ker B S hS ((schemeSpaceFunctor B S hS).obj V) ⟨G, hG⟩ W, Scheme.Γ_map_op]
  exact hkey

/-- A closed subspace of a representable algebraic space all of whose represented base changes
are `n`th-order thickenings of schemes is an `n`th-order thickening of algebraic spaces.

The topological clause is the surjectivity of the base change along the identity chart, read on
points through `AlgebraicGeometry.Space.surjective_pointsMap_yoneda_iff`; the ideal clause is
`AlgebraicGeometry.Space.definingIdealAt_eq_ker`, which presents the defining ideal on an étale
chart as the kernel on global sections of the base-changed closed immersion, together with
`AlgebraicGeometry.Scheme.ker_appTop_pow_eq_bot`, which passes from the vanishing of the power
of the kernel ideal sheaf to the vanishing of the power of that kernel.

The file-private form of `isNthOrderThickening_of_isRepresentedAtOrder`. -/
private theorem isNthOrderThickening_of_isRepresentedNthOrder (n : ℕ)
    {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) (hQ : IsRepresentedNthOrder B S hS n G) :
    IsNthOrderThickening B S hS n ((schemeSpaceFunctor B S hS).obj V) G :=
  isNthOrderThickening_of_isRepresentedAtOrder (hS := hS) (S := S) (B := B) (n := n) (V := V)
    (G := G) (hG := hG) (hQ := hQ)

/-- Being represented by `n`th-order thickenings passes to the inverse image along any
morphism of representable presheaves: the inverse image is a base change of the subspace by
Stacks 083Q, and the property is stable under base change. -/
theorem isRepresentedAtOrder_preimage (n : ℕ) {U V : BigFppfOver B S hS}
    (G : Subfunctor (yoneda.obj U)) (k : yoneda.obj V ⟶ yoneda.obj U)
    (hQ : IsRepresentedAtOrder B S hS n G) :
    IsRepresentedAtOrder B S hS n (G.preimage k) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (Subfunctor.isPullback_preimage k G) hQ

/-- Being represented by `n`th-order thickenings passes to the inverse image along any
morphism of representable presheaves: the inverse image is a base change of the subspace by
Stacks 083Q, and the property is stable under base change.

The file-private form of `isRepresentedAtOrder_preimage`. -/
private theorem isRepresentedNthOrder_preimage (n : ℕ) {U V : BigFppfOver B S hS}
    (G : Subfunctor (yoneda.obj U)) (k : yoneda.obj V ⟶ yoneda.obj U)
    (hQ : IsRepresentedNthOrder B S hS n G) :
    IsRepresentedNthOrder B S hS n (G.preimage k) :=
  isRepresentedAtOrder_preimage (hS := hS) (S := S) (B := B) (n := n) (U := U) (V := V) (G := G)
    (k := k) (hQ := hQ)

/-- A closed subspace represented by `n`th-order thickenings is a *universal* `n`th-order
thickening: each of its base changes is again represented by `n`th-order thickenings, hence is
an `n`th-order thickening of algebraic spaces. -/
theorem isUniversalNthOrderThickening_of_isRepresentedAtOrder (n : ℕ)
    {U : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj U))
    (hG : IsClosedSubspace B S hS G) (hQ : IsRepresentedAtOrder B S hS n G) :
    IsUniversalNthOrderThickening B S hS n U G := fun V k ↦
  isNthOrderThickening_of_isRepresentedAtOrder B S hS n (G.preimage k)
    (isClosedSubspace_preimage B S hS k G (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) hG)
    (isRepresentedAtOrder_preimage B S hS n G k hQ)

/-- A closed subspace represented by `n`th-order thickenings is a *universal* `n`th-order
thickening: each of its base changes is again represented by `n`th-order thickenings, hence is
an `n`th-order thickening of algebraic spaces.

The file-private form of `isUniversalNthOrderThickening_of_isRepresentedAtOrder`. -/
private theorem isUniversalNthOrderThickening_of_isRepresentedNthOrder (n : ℕ)
    {U : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj U))
    (hG : IsClosedSubspace B S hS G) (hQ : IsRepresentedNthOrder B S hS n G) :
    IsUniversalNthOrderThickening B S hS n U G :=
  isUniversalNthOrderThickening_of_isRepresentedAtOrder (hS := hS) (S := S) (B := B) (n := n)
    (U := U) (G := G) (hG := hG) (hQ := hQ)

/-! ### The affine case -/

/-- **A surjective closed immersion of finite presentation into an affine scheme is a
finite-order thickening, uniformly in its base changes.** Let `G` be a closed subspace of an
affine object `V` of the site whose inclusion is of finite presentation and surjective on
points. Then some `n` makes every represented base change of `G.ι` an `n`th-order thickening of
schemes.

Finite presentation gives a finitely generated defining ideal over the whole of `V`, by Stacks
084Q read on the identity chart, which is a surjective étale chart because `V` is
representable. Surjectivity gives that ideal inside the nilradical, by Stacks 09NY's
topological criterion. A finitely generated ideal inside the nilradical is nilpotent, and over
an affine scheme the kernel ideal sheaf is determined by its global ideal, so a power of the
kernel ideal sheaf vanishes. -/
private theorem exists_isRepresentedNthOrder_of_isAffine {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (G : Subfunctor (yoneda.obj V)) (hG : IsClosedSubspace B S hS G)
    (hfp : IsFinitePresentation B S hS G.ι)
    (hsurj : Function.Surjective (pointsMap B S hS G.toFunctor G.ι)) :
    ∃ n : ℕ, IsRepresentedNthOrder B S hS n G := by
  have hid : (𝟙 (yoneda.obj V) : yoneda.obj V ⟶ yoneda.obj V) = yoneda.map (𝟙 V) := by
    rw [yoneda.map_id]
  have hEt : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj V)) := by
    rw [hid]
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (𝟙 V)).2 ?_
    rw [CategoryTheory.Functor.map_id]
    exact inferInstance
  have hSurjChart : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj V)) := by
    rw [hid]
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (𝟙 V)).2 ?_
    rw [CategoryTheory.Functor.map_id]
    exact inferInstance
  set i₀ := hG.2.rep.snd (𝟙 (yoneda.obj V)) with hi₀
  set f₀ := (BigFppfOver.toScheme B S hS).map i₀ with hf₀
  have hsq := hG.2.rep.isPullback (𝟙 (yoneda.obj V))
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion f₀ :=
    hG.2.property_snd (𝟙 (yoneda.obj V))
  have := hci
  -- the ideal is finitely generated over the whole of `V`
  have hfg : (f₀.ker.ideal
      ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V)⟩).FG :=
    (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (ObjectProperty.homMk G.ι :
        (⟨G.toFunctor, hG.1⟩ : AlgebraicSpaces B S hS) ⟶ (schemeSpaceFunctor B S hS).obj V)
      hG.2 hEt hSurjChart).1 hfp _
  rw [Scheme.Hom.ker_apply] at hfg
  -- and it lies in the nilradical, because the closed immersion is surjective
  have hsurj₀ : Function.Surjective ⇑f₀ :=
    (surjective_pointsMap_yoneda_iff B S hS i₀).1
      (surjective_pointsMap_of_isPullback B S hS hsq hsurj)
  have hnil : RingHom.ker f₀.appTop.hom ≤
      nilradical Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    Stacks.LiftInvertible.ker_app_le_nilradical f₀
      (Stacks.LiftInvertible.ker_le_nilradical_of_surjective f₀ hsurj₀)
      ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V)⟩
  obtain ⟨m, hm⟩ := hfg.isNilpotent_iff_le_nilradical.mpr hnil
  refine ⟨m, ?_⟩
  have hpow : f₀.ker ^ (m + 1) = ⊥ := by
    refine (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine f₀ (m + 1)).2 ?_
    exact le_antisymm ((Ideal.pow_le_pow_right (Nat.le_succ m)).trans (le_of_eq hm)) bot_le
  have hP : (MorphismProperty.inverseImage (thickOrder.{u} m)
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ i₀).2 ⟨hci, hpow⟩
  have hw : hG.2.rep.fst (𝟙 (yoneda.obj V)) ≫ G.ι = yoneda.map i₀ :=
    hsq.w.trans (Category.comp_id _)
  have hiso : IsIso (hG.2.rep.fst (𝟙 (yoneda.obj V))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.isomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      hsq.flip (inferInstanceAs (IsIso (𝟙 (yoneda.obj V))))
  rw [← hw] at hP
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hP

/-! ### Supported sections over an affine object -/

/-- A section of `X` whose point-set image lies in `|Z|` has inverse image of `Z` surjective on
points: the point set of the inverse image is the inverse image of the point set, by Stacks
083Q and Stacks 03MH. -/
private theorem surjective_pointsMap_preimage_of_hasImageIn
    (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) {U : BigFppfOver B S hS}
    (g : X.1.obj (op U)) (hg : HasImageIn B S hS X.1 (subspacePoints B S hS Z) U g) :
    Function.Surjective (pointsMap B S hS
      (Z.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)).toFunctor
      (Z.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)).ι) := by
  intro x
  have hmem : x ∈ subspacePointSet B S hS (yoneda.obj U)
      (Z.preimage (yonedaEquiv.symm g : yoneda.obj U ⟶ X.1)) := by
    rw [subspacePointSet_preimage]
    induction x using Quot.ind with | _ p => ?_
    rw [Set.mem_preimage, pointsMap_class]
    exact hg p
  exact hmem

/-- **The affine case of Stacks 0H8N.** Over an affine object of the site, a section of `X`
whose point-set image lies in `|Z|` already lies in the union of the infinitesimal
neighbourhoods of `Z`, provided `Z ⟶ X` is of finite presentation.

The inverse image of `Z` along the section is a closed subspace of the affine object, is of
finite presentation as a base change of `Z ⟶ X`, and is surjective on points because the
section is supported on `|Z|`; so some power of its defining ideal vanishes, uniformly in all
base changes, which is exactly the required finite order. -/
private theorem mem_completionSubspaceSubfunctor_of_hasImageIn_of_isAffine
    (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z)
    (hfp : IsFinitePresentation B S hS Z.ι) {U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (g : X.1.obj (op U))
    (hg : HasImageIn B S hS X.1 (subspacePoints B S hS Z) U g) :
    (ULift.up g : (X.1 ⋙ uliftFunctor.{u + 1}).obj (op U)) ∈
      (completionSubspaceSubfunctor B S hS X Z).obj (op U) := by
  set h : yoneda.obj U ⟶ X.1 := yonedaEquiv.symm g with hh
  have hcs : IsClosedSubspace B S hS (Z.preimage h) :=
    isClosedSubspace_preimage B S hS h Z X.2 (isAlgebraicSpace_yoneda B S hS U) hZ
  have hsqA : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage h) :
        (⟨(Z.preimage h).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (Z.preimage h).ι :
        (⟨(Z.preimage h).toFunctor, hcs.1⟩ : AlgebraicSpaces B S hS) ⟶
          (schemeSpaceFunctor B S hS).obj U)
      (ObjectProperty.homMk Z.ι : (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (ObjectProperty.homMk h : (schemeSpaceFunctor B S hS).obj U ⟶ X) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS T)) (Subfunctor.isPullback_preimage h Z)
  have hfp' : IsFinitePresentation B S hS (Z.preimage h).ι :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) ↦
        IsFinitePresentation B S hS f.hom) hsqA hfp
  obtain ⟨n, hn⟩ := exists_isRepresentedNthOrder_of_isAffine B S hS (Z.preimage h) hcs hfp'
    (surjective_pointsMap_preimage_of_hasImageIn B S hS X Z g hg)
  exact ⟨n, isUniversalNthOrderThickening_of_isRepresentedNthOrder B S hS n
    (Z.preimage h) hcs hn⟩

/-! ### Invertibility of the comparison -/

/-- **Stacks 0H8N, the positive half.** Let `X` be an algebraic space over `S` and let `Z ⊆ X`
be a closed subspace with point set `T = |Z|`. If `Z ⟶ X` is of finite presentation, the
canonical morphism `c : X^∧_Z ⟶ X_{/T}` is an isomorphism.

Both sides are sheafifications of subfunctors of `X`, and `c` is the sheafification of the
inclusion of the first into the second. That inclusion is injective on sections, hence locally
injective; and it is locally surjective because the affine objects of the site generate the
fppf topology (Stacks 021V) and over an affine object the two subfunctors agree, by
`AlgebraicGeometry.Space.mem_completionSubspaceSubfunctor_of_hasImageIn_of_isAffine`. A locally
bijective morphism of sheaves of types is an isomorphism.

The negative half of the source's statement — that `c` is *not* an isomorphism in general — is
not formalized here; see the module documentation. -/
@[stacks 0H8N "the comparison is an isomorphism for a closed subspace of finite presentation"]
theorem isIso_completionSubspaceComparison (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1)
    (hZ : IsClosedSubspace B S hS Z) (hfp : IsFinitePresentation B S hS Z.ι) :
    IsIso (completionSubspaceComparison B S hS X Z) := by
  have hle := completionSubspaceSubfunctor_le_completionSubfunctor B S hS X Z
  have hcd : (BigAffineFppf.inclusion B S hS).IsCoverDense
      (BigFppfOver.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (BigAffineFppf.inclusion B S hS)
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Subfunctor.homOfLe hle) := by
    constructor
    intro U s
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (Functor.is_cover_of_isCoverDense (BigAffineFppf.inclusion B S hS) _ U)
    rintro V k ⟨⟨W₀, lift, map₀, hfac⟩⟩
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj W₀)) :=
      BigAffineFppf.isAffine_toScheme_obj B S hS W₀
    set t₀ := (completionSubfunctor B S hS X.1 (subspacePoints B S hS Z)).toFunctor.map
      map₀.op s
    have hmemA : t₀.1 ∈ (completionSubspaceSubfunctor B S hS X Z).obj
        (op ((BigAffineFppf.inclusion B S hS).obj W₀)) :=
      mem_completionSubspaceSubfunctor_of_hasImageIn_of_isAffine B S hS X Z hZ hfp
        t₀.1.down t₀.2
    refine ⟨⟨_, (completionSubspaceSubfunctor B S hS X Z).map lift.op hmemA⟩, ?_⟩
    apply Subtype.ext
    change (X.1 ⋙ uliftFunctor.{u + 1}).map lift.op
      ((X.1 ⋙ uliftFunctor.{u + 1}).map map₀.op s.1) = _
    rw [← Functor.map_comp_apply, ← op_comp, hfac]
    rfl
  have hinj : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (Subfunctor.homOfLe hle) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac (BigFppfOver.topology B S hS)
      (Subfunctor.homOfLe_ι hle)
  have hfac := (BigFppfOver.topology B S hS).toSheafify_naturality (Subfunctor.homOfLe hle)
  have hsurj' : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).sheafifyMap (Subfunctor.homOfLe hle)) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (BigFppfOver.topology B S hS) hfac.symm
  have hinj' : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).sheafifyMap (Subfunctor.homOfLe hle)) :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      (BigFppfOver.topology B S hS) _ hfac.symm
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj', hsurj'⟩

end AlgebraicGeometry.Space

end
