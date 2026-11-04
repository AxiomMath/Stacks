module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.SectionValue
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist

/-!
# The comparison maps on twists for the morphism induced by a graded ring homomorphism

This is the map `θ` of Tag 01MY: for a homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded
rings with domain of definition `U(ψ) ⊆ Proj ℬ` and induced morphism
`mapHom : U(ψ) ⟶ Proj 𝒜`, a morphism of sheaves of modules

`θ n : mapHom* 𝒪_{Proj 𝒜}(n) ⟶ ι* 𝒪_{Proj ℬ}(n)`

for every `n : ℤ`, where `ι : U(ψ) ⟶ Proj ℬ` is the inclusion.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistFibreMap`: the comparison on the fibres of the
  twisting sheaves at a point of `U(ψ)`, sending `a / s` to `ψ a / ψ s`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection`: the comparison on sections over an
  open, fibre by fibre.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`: the adjoint form of `θ`, a
  morphism `𝒪_{Proj 𝒜}(n) ⟶ mapHom_* (𝒪_{Proj ℬ}(n)|_{U(ψ)})`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`: `θ n` itself.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.ProjMapData` and
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`: Tag 01MY's bundle of the morphism with
  its maps on all twists, and its canonical construction.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistFibreMap_mk`: the fibre comparison on a
  fraction. This is what makes the construction non-degenerate and is worth reading first.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection_val` and
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_app_val`: the defining pointwise
  formula, and the same formula read off the adjoint morphism.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.twistFibreMap_val_app`: the semilinearity, which is
  `val_app` of the companion file transported to the twisting sheaves.

## Implementation notes

The route is the pullback–pushforward adjunction. A morphism out of `mapHom* 𝒪_{Proj 𝒜}(n)` is
not directly constructible — the pullback is a sheafification of a tensor product and has no
usable description of its sections — but by
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` it is the same thing as a
morphism `𝒪_{Proj 𝒜}(n) ⟶ mapHom_* (ι* 𝒪_{Proj ℬ}(n))`, and there both sides are concrete:
sections of the twisting sheaf are dependent families of homogeneous fractions, and the
pushforward of a restriction along an open immersion has, over `U`, exactly the sections of
`𝒪_{Proj ℬ}(n)` over the image of `mapHom ⁻¹ᵁ U`. The target is formed with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` rather than the pullback for that reason, and
is traded for the pullback at the very end by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

Everything then happens fibre by fibre. The map sends the family `(a_x)` to
`(ψ a / ψ s)_y`; the local-fraction condition on the image family comes from
`map_mem_twistGrading` (the numerator stays homogeneous of the same degree) and
`notMem_of_notMem` (the denominator stays invertible), and the open witnessing it is the image
of the inverse image of the open witnessing it for `a`.

The one step that is not formal is the linearity. The scalar action of `Γ(Proj 𝒜, U)` on the
pushed-forward sections is restricted along `mapHom.app U`, so semilinearity of the fibrewise
map is precisely the assertion that the value of `mapHom.app U r` at a point is the fibre
comparison of the value of `r` — which is `val_app` of the companion file. That is the one
non-formal input of the construction, and it enters in exactly one place, as
`twistFibreMap_val_app`.

Four technical points, all of them places where the obvious approach fails.

* The morphism is assembled with `PresheafOfModules.homMk`, which takes a morphism of the
  underlying presheaves of abelian groups together with the linearity condition. Writing the
  `app` directly as a `ModuleCat.ofHom` of a structure literal does not work: elaborating the
  literal forces instance search for the module structure on the pushforward target before
  unification has fixed it, and that search fails.
* `AlgebraicGeometry.Scheme.Opens.ι_appIso` is a propositional equality, not a definitional one,
  because `AlgebraicGeometry.Scheme.Hom.appIso` is not exposed. The scalar restriction hidden
  inside `restrictFunctor` therefore cannot be unfolded away, and is discharged by rewriting
  with `ι_appIso_inv_apply`; this is why `val_app_val` exists beside
  `twistFibreMap_val_app`, carrying the comparison isomorphism explicitly.
* `twistFamily` is a named definition rather than an inline lambda. Inlining it makes the
  local-fraction proof unify two very large terms and the elaborator reaches a deterministic
  `whnf` timeout — which is a size problem, not a universe problem: the universes here are
  pinned, both rings living in the single universe `u`.
* `TopCat.Sheaf`, `sheafCompose` and `AlgebraicGeometry.Proj` are made `implicit_reducible`
  locally. The first two because a twisting sheaf is an object of
  `AlgebraicGeometry.Scheme.Modules` only up to them, as in the sibling twist files; the third
  because the index category of the twisting sheaf is `Opens ↑(ProjectiveSpectrum.top 𝒜)` while
  that of `Scheme.Modules` is `Opens ↑(Proj 𝒜)`, and without it every rewrite across the two
  spellings fails its motive check.

## What is not done

Compatibility of `θ` with the multiplication maps `𝒪(n) ⊗ 𝒪(m) → 𝒪(n+m)` between twists is not
proved here.  It *is* stateable: the
comparison between the pullback of a tensor product of module sheaves and the tensor product of
the pullbacks is `Stacks.PullbackTensorIso.pullbackTensorIso`, unconditional, and the clause
now elaborates verbatim — see
`StacksFrontier/AlgebraicGeometry/ProjTwistTheta/Multiplication.lean`, which writes it in
library vocabulary and bounds the five transport steps that remain. The unit law is not
proved either, but **only one of its two inputs is missing.** Tag 01MY's `twistUnitMap` is in this library and in this very
namespace — `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap`, the morphism `𝒪_X ⟶ 𝒪(0)`
of `StacksFrontier/AlgebraicGeometry/ProjTwistCompare/Unit.lean` — and it is an *isomorphism*, by
`Stacks.AlgebraicGeometry.ProjEulerSequence.isIso_twistUnitMap`, for an arbitrary nonnegatively
graded ring and with no generation hypothesis. What is genuinely absent is `pullbackTwistUnit`,
the comparison `ψ^* 𝒪(0) ⟶ 𝒪(0)`; its input is Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`, which this library already uses and already knows to be
invertible (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackInvertible/Basic.lean`).
Functoriality in `ψ` — the composite
case of Tag 01MZ — and the statement that `θ` is an isomorphism when `ψ` is a restriction of a
graded algebra of sections, Tag 01NO, are not proved either.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### Reading a point of an image back into the domain of definition -/

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- A point of the image of an open of `U(ψ)` lies in `U(ψ)`. -/
public theorem mem_mapDomain_of_mem_image (ψ : 𝒜 →+*ᵍ ℬ)
    {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens} {z : AlgebraicGeometry.Proj ℬ}
    (hz : z ∈ (mapDomain 𝒜 ℬ ψ).ι ''ᵁ V) : z ∈ mapDomain 𝒜 ℬ ψ := by
  obtain ⟨y, -, rfl⟩ := hz
  exact y.2

/-- A point of the image of an open `V ⊆ U(ψ)`, read back as a point of `U(ψ)`. -/
public def liftPt (ψ : 𝒜 →+*ᵍ ℬ) {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens}
    (z : ↥((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V)) : (mapDomain 𝒜 ℬ ψ).toScheme :=
  ⟨z.1, mem_mapDomain_of_mem_image 𝒜 ℬ ψ z.2⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `liftPt` does not move the underlying point of `Proj ℬ`. -/
public theorem liftPt_val (ψ : 𝒜 →+*ᵍ ℬ) {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens}
    (z : ↥((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V)) :
    ((liftPt 𝒜 ℬ ψ z).1 : AlgebraicGeometry.Proj ℬ) = z.1 := rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `liftPt` lands in the open whose image was taken. -/
public theorem liftPt_mem (ψ : 𝒜 →+*ᵍ ℬ) {V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens}
    (z : ↥((mapDomain 𝒜 ℬ ψ).ι ''ᵁ V)) : liftPt 𝒜 ℬ ψ z ∈ V := by
  have hz := z.2
  obtain ⟨y, hy, hzy⟩ := hz
  have he : liftPt 𝒜 ℬ ψ z = y := Subtype.ext hzy.symm
  rw [he]
  exact hy

/-! ### The comparison on the fibres of the twisting sheaves -/

/-- The comparison map on the fibres of the associated-module sheaves at a point of `U(ψ)`:
the fibre of `𝒜` at the image point maps to the fibre of `ℬ` at the point. Both fibres are
ordinary localizations, because the underlying module of every twist is the ring itself. -/
public def twistFibreMap (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ModuleFiber (M := A) 𝒜 (basePoint 𝒜 ℬ ψ y) →+*
      ModuleFiber (M := B) ℬ (ambientPoint 𝒜 ℬ ψ y) :=
  fibreMap 𝒜 ℬ ψ _ _ (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ y)

/-- The fibre comparison sends `a / s` to `ψ a / ψ s`. -/
public theorem twistFibreMap_mk (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) (a s : A)
    (hs : s ∉ (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal)
    (hψs : ψ s ∉ (ambientPoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal) :
    twistFibreMap 𝒜 ℬ ψ y (LocalizedModule.mk a ⟨s, hs⟩) =
      LocalizedModule.mk (ψ a) ⟨ψ s, hψs⟩ :=
  fibreMap_mk 𝒜 ℬ ψ _ _ _ a s hs hψs

/-- The fibre comparison agrees with the one on the structure sheaves, after `val`. -/
public theorem val_fibreHom (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (c : AtPrime 𝒜 (basePoint 𝒜 ℬ ψ y).asHomogeneousIdeal.toIdeal) :
    (fibreHom 𝒜 ℬ ψ y c).val = twistFibreMap 𝒜 ℬ ψ y c.val :=
  val_homogeneousFibreMap 𝒜 ℬ ψ _ _ _ c

/-! ### The comparison on sections -/

/-- The image family: the comparison on sections, before the local-fraction condition. -/
public def twistFamily (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (.op U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    ModuleFiber (M := B) ℬ (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)) :=
  twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
    (a.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)

/-- **The comparison map on sections of the `n`-th twist.** The family of homogeneous fractions
`(a_x)` over an open `U` of `Proj 𝒜` goes to the family `(ψ a / ψ s)` over the image of
`mapHom ⁻¹ᵁ U`. -/
public def twistSection (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (.op U)) :
    (twistingSheaf ℬ n).val.obj
      (.op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) := by
  refine ⟨twistFamily 𝒜 ℬ ψ n U a, ?_⟩
  intro z
  obtain ⟨V₀, hxV₀, i, k, m, s, hm, hs, hns, heq⟩ :=
    a.2 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩
  have hVU : mapHom 𝒜 ℬ ψ ⁻¹ᵁ V₀ ≤ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U := fun p hp => leOfHom i hp
  refine ⟨(mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ V₀),
    mem_image_of_mem 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) hxV₀,
    homOfLE (Scheme.Hom.image_mono _ hVU), k, ψ m, ψ s,
    map_mem_twistGrading 𝒜 ℬ ψ n (k : ℤ) hm, ψ.map_mem hs, ?_, ?_⟩
  · exact fun q => notMem_of_notMem 𝒜 ℬ ψ hs (liftPt 𝒜 ℬ ψ q)
      (hns ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ q), liftPt_mem 𝒜 ℬ ψ q⟩)
  · intro q
    refine Eq.trans ?_ (twistFibreMap_mk 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ q) m s
      (hns ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ q), liftPt_mem 𝒜 ℬ ψ q⟩) _)
    exact congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ q))
      (heq ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ q), liftPt_mem 𝒜 ℬ ψ q⟩)

/-- The defining pointwise formula for the comparison on sections. -/
public theorem twistSection_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 n).val.obj (.op U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    (twistSection 𝒜 ℬ ψ n U a).1 z =
      twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (a.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) := rfl

/-! ### Linearity -/

/-- The bridge supplied by `val_app`: the value of `mapHom.app U r` at a point of the image is
the fibre comparison of the value of `r` at the image point. This is the semilinearity of the
comparison on sections, and the only step of the construction that is not formal. -/
public theorem twistFibreMap_val_app (ψ : 𝒜 →+*ᵍ ℬ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (r : Γ(AlgebraicGeometry.Proj 𝒜, U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (HomogeneousLocalization.val
          (r.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) =
      HomogeneousLocalization.val ((((mapHom 𝒜 ℬ ψ).app U).hom' r).1 z) := by
  rw [← val_fibreHom]
  exact (congrArg HomogeneousLocalization.val
    (val_app 𝒜 ℬ ψ U r (liftPt 𝒜 ℬ ψ z) (liftPt_mem 𝒜 ℬ ψ z))).symm

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- On sections over the image of an open, the comparison isomorphism of the inclusion of an
open subscheme is the identity. This is `AlgebraicGeometry.Scheme.Opens.ι_appIso`, which is a
propositional equality and not a definitional one, because `AlgebraicGeometry.Scheme.Hom.appIso`
is not exposed; so the scalar restriction hidden in
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` has to be discharged by rewriting. -/
public theorem ι_appIso_inv_apply (ψ : 𝒜 →+*ᵍ ℬ)
    (V : (mapDomain 𝒜 ℬ ψ).toScheme.Opens) (t : Γ((mapDomain 𝒜 ℬ ψ).toScheme, V)) :
    ((mapDomain 𝒜 ℬ ψ).ι.appIso V).inv.hom' t = t := by
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- `twistFibreMap_val_app` in the spelling the scalar action on the pushed-forward sections
actually takes, with the scalar restriction of `restrictFunctor` written out. -/
public theorem val_app_val (ψ : 𝒜 →+*ᵍ ℬ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (r : Γ(AlgebraicGeometry.Proj 𝒜, U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (HomogeneousLocalization.val
          (r.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) =
      HomogeneousLocalization.val
        ((((mapDomain 𝒜 ℬ ψ).ι.appIso (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)).inv.hom'
          (((mapHom 𝒜 ℬ ψ).app U).hom' r)).1 z) := by
  rw [ι_appIso_inv_apply]
  exact twistFibreMap_val_app 𝒜 ℬ ψ U r z

/-- The comparison on sections is additive, pointwise. -/
public theorem twistSection_add_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (a b : (twistingSheaf 𝒜 n).val.obj (.op U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    (twistSection 𝒜 ℬ ψ n U (a + b)).1 z =
      (twistSection 𝒜 ℬ ψ n U a).1 z + (twistSection 𝒜 ℬ ψ n U b).1 z := by
  rw [twistSection_val, twistSection_val, twistSection_val]
  exact map_add _ _ _

/-! ### The adjoint morphism and the comparison on twists -/

/-- The comparison on sections, as a morphism of the underlying presheaves of abelian groups. -/
public def twistPresheafMap (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    (twistingSheaf 𝒜 n).val.presheaf ⟶
      ((Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
        ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj
          (twistingSheaf ℬ n))).val.presheaf where
  app U := AddCommGrpCat.ofHom
    { toFun := twistSection 𝒜 ℬ ψ n U.unop
      map_zero' := Subtype.ext (funext fun z =>
        map_zero (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)))
      map_add' := fun a b => Subtype.ext (funext fun z =>
        twistSection_add_val 𝒜 ℬ ψ n U.unop a b z) }
  naturality := by
    intro U V f
    ext a
    exact Subtype.ext (funext fun _ => rfl)

/-- **The adjoint form of `θ`**: the comparison
`𝒪_{Proj 𝒜}(n) ⟶ mapHom_* (𝒪_{Proj ℬ}(n)|_{U(ψ)})`. The linearity condition is `val_app`. -/
public def twistPushforwardMap (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    twistingSheaf 𝒜 n ⟶ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).obj
      ((Scheme.Modules.restrictFunctor (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)) :=
  ⟨PresheafOfModules.homMk (twistPresheafMap 𝒜 ℬ ψ n) (fun U r m => by
    refine Subtype.ext (funext fun z => ?_)
    have hL : ((ConcreteCategory.hom ((twistPresheafMap 𝒜 ℬ ψ n).app U)) (r • m)).1 z =
        twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
          ((r • m).1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) := rfl
    refine Eq.trans hL ?_
    refine Eq.trans (map_mul (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
      (HomogeneousLocalization.val
        (r.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩))
      (m.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) ?_
    exact congrArg (fun c => c * twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (m.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩))
      (val_app_val 𝒜 ℬ ψ U.unop r z))⟩

/-- The pointwise formula, read off the adjoint morphism. -/
public theorem twistPushforwardMap_app_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (Opens ↑(AlgebraicGeometry.Proj 𝒜))ᵒᵖ)
    (a : (twistingSheaf 𝒜 n).val.obj U)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U.unop))) :
    (((twistPushforwardMap 𝒜 ℬ ψ n).val.app U).hom' a).1 z =
      twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)
        (a.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩) := rfl

/-- **The comparison map on the `n`-th twist**, Tag 01MY's `θ n`:
`mapHom* 𝒪_{Proj 𝒜}(n) ⟶ ι* 𝒪_{Proj ℬ}(n)`. -/
public def twistMap (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    (Scheme.Modules.pullback (mapHom 𝒜 ℬ ψ)).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _).symm
      (twistPushforwardMap 𝒜 ℬ ψ n) ≫
    (Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ n)

/-! ### The bundle -/

/-- Tag 01MY's bundle: the morphism induced by a graded ring homomorphism on its domain of
definition, together with its comparison maps on every integer twist. The statements of Tags 01MZ and
01NO quantify over this record rather than over the two pieces separately. -/
public structure ProjMapData (ψ : 𝒜 →+*ᵍ ℬ) where
  /-- The morphism of schemes `U(ψ) ⟶ Proj 𝒜`. -/
  hom : (mapDomain 𝒜 ℬ ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜
  /-- The comparison map on the `n`-th twist. -/
  twistMap : ∀ n : ℤ,
    (Scheme.Modules.pullback hom).obj (twistingSheaf 𝒜 n) ⟶
      (Scheme.Modules.pullback (mapDomain 𝒜 ℬ ψ).ι).obj (twistingSheaf ℬ n)

/-- **The canonical bundle of Tag 01MY**: the glued morphism `mapHom` together with the
comparison maps `θ` on all twists. -/
@[stacks 01MY "the morphism and the maps on all twists"]
public def projMapData (ψ : 𝒜 →+*ᵍ ℬ) : ProjMapData 𝒜 ℬ ψ where
  hom := mapHom 𝒜 ℬ ψ
  twistMap := twistMap 𝒜 ℬ ψ

/-- The underlying morphism of the canonical bundle is `mapHom`. -/
public theorem projMapData_hom (ψ : 𝒜 →+*ᵍ ℬ) :
    (projMapData 𝒜 ℬ ψ).hom = mapHom 𝒜 ℬ ψ := rfl

/-- The twist maps of the canonical bundle are `twistMap`. -/
public theorem projMapData_twistMap (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    (projMapData 𝒜 ℬ ψ).twistMap n = twistMap 𝒜 ℬ ψ n := rfl

end Stacks.AlgebraicGeometry.ProjTwistCompare

end
