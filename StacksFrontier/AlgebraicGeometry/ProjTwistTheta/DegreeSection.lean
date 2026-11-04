module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The comparison maps on twists on homogeneous global sections, Tag 01MY part (1)

Let `psi : A -> B` be a homomorphism of nonnegatively graded rings, `U(psi) subset Proj B` its
domain of definition, `mapHom : U(psi) -> Proj A` the induced morphism and `theta n` the
comparison map on the `n`-th twist. This file proves the first clause of Tag 01MY: for a
homogeneous element `a` of degree `n`, the comparison carries the global section of `O(n)`
attached to `a` to the one attached to `psi a`.

Both sections are read through the unit of the pullback-pushforward adjunction, which is the
form in which a global section of a twist can be compared with a global section of the
pullback of that twist.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_degreeSection_val`: the
  pointwise computation. The adjoint form of `theta` sends the section whose value is
  everywhere `a / 1` to the one whose value is everywhere `psi a / 1`.
* `Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_degreeSection`: the same
  identity with the right-hand side named, as the restriction of the degree-`n` section of
  `O(n)` on `Proj B` along the unit of the restriction adjunction.
* `Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection`: **Tag 01MY, part (1),
  homogeneous global sections.** The identity for `theta` itself, on the bundle
  `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`.

## The route

Three steps, two of them pure adjunction coherence and one a computation.

The computation is the pointwise one. The value of the adjoint form of `theta` at a point is
the fibre comparison of the value of the argument at the image point
(`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_app_val`), the value of the
degree-`n` section is `a / 1`
(`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply`), and the fibre comparison
sends `a / s` to `psi a / psi s`
(`Stacks.AlgebraicGeometry.ProjTwistCompare.twistFibreMap_mk`). With `s = 1` the denominator
has to be moved across `psi 1 = 1`, which is the only step that is not a rewrite.

The right-hand side of the statement is the unit of the *pullback* adjunction for the open
immersion `ι`, while `theta` is built from the *restriction* functor, which has concrete
sections. The two are related by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`,
which is by definition `CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` says exactly that composing the
restriction unit with it gives the pullback unit. On the source side the same mechanism in the
other direction: `theta` is the inverse adjoint transpose of
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, so composing the unit with its
pushforward returns that morphism, which is `CategoryTheory.Adjunction.homEquiv_unit`.

## Implementation notes

* `AlgebraicGeometry.Scheme.Modules` is a `def`, so the two equalities of morphisms are
  transported onto elements by `congrArg` of a function that evaluates a morphism, never by
  `rw`, and the pointwise computation is a chain of `Eq.trans` rather than a sequence of
  rewrites: the coercion of a section of a twisting sheaf to a dependent family appears at two
  spellings of the ambient space one unfolding apart, so a rewrite fails its motive check even
  when the two sides print identically.
* The opens `mapHom ⁻¹ᵁ ⊤`, `ι ⁻¹ᵁ ⊤` and `⊤` are definitionally equal, so the sections of a
  pushforward over `⊤` need no transport; nothing is said at a general open.

## What is not done

Only the first clause of Tag 01MY is here. Compatibility of the comparison maps with the
multiplication maps of the twisting algebra, the unit law in the source's spelling, and
uniqueness of the family of comparison maps are not proved, and neither is the statement that
the comparison is an isomorphism when `psi` is a restriction of a graded algebra of sections
(Tag 01NO). Nothing is proved about the comparison on sections over an open other than `⊤`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.AlgebraicGeometry.ProjTwistCompare

namespace Stacks.AlgebraicGeometry.ProjTwistTheta

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The pointwise computation -/

/-- The adjoint form of the comparison map on the `n`-th twist sends the global section
attached to a homogeneous element `a` of degree `n` to the section whose value at every point
is the fraction `psi a / 1`. -/
public theorem twistPushforwardMap_degreeSection_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℕ) (a : 𝒜 n)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)))) :
    (((twistPushforwardMap 𝒜 ℬ ψ (n : ℤ)).val.app (.op ⊤)).hom'
        (degreeSection 𝒜 n a)).1 z =
      LocalizedModule.mk ((ψ a : B)) 1 := by
  have hone : (ψ (1 : A)) = 1 := map_one ψ
  have hs : (1 : A) ∉ (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal :=
    (basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).isPrime.one_notMem
  have hψs : (ψ (1 : A)) ∉
      (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal := by
    rw [hone]
    exact (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).isPrime.one_notMem
  refine Eq.trans
    (twistPushforwardMap_app_val 𝒜 ℬ ψ (n : ℤ) (.op ⊤) (degreeSection 𝒜 n a) z) ?_
  refine Eq.trans (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
    (degreeSection_apply 𝒜 n a
      ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) ?_
  refine Eq.trans
    (twistFibreMap_mk 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z) (a : A) 1 hs hψs) ?_
  exact congrArg (fun s => LocalizedModule.mk (M := B) (ψ (a : A)) s)
    (Subtype.ext hone :
      (⟨ψ (1 : A), hψs⟩ :
          (ambientPoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)).asHomogeneousIdeal.toIdeal.primeCompl) = 1)

/-- The unit of the restriction adjunction, over `⊤`, carries the global section of `O(n)`
attached to a homogeneous element `b` of degree `n` to the family whose value at every point of
the domain of definition is the fraction `b / 1`. Over `⊤` that unit is the restriction map of
the twisting sheaf, and restriction of a section of a twisting sheaf is restriction of the
underlying dependent family. -/
public theorem restrictUnit_degreeSection_val (ψ : 𝒜 →+*ᵍ ℬ) (n : ℕ) (b : ℬ n)
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ
      (mapHom 𝒜 ℬ ψ ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)))) :
    ((((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)).hom'
        (degreeSection ℬ n b)).1 z =
      LocalizedModule.mk ((b : B)) 1 :=
  degreeSection_apply ℬ n b ⟨z.1, trivial⟩

/-- The adjoint form of the comparison map on the `n`-th twist carries the global section of
`O(n)` on `Proj A` attached to a homogeneous element `a` of degree `n` to the restriction, to
the domain of definition, of the global section of `O(n)` on `Proj B` attached to `psi a`.

The right-hand side is written through the unit of the restriction adjunction, which over `⊤`
is the restriction map of the twisting sheaf. -/
public theorem twistPushforwardMap_degreeSection (ψ : 𝒜 →+*ᵍ ℬ) (n : ℕ) (a : 𝒜 n) :
    ((twistPushforwardMap 𝒜 ℬ ψ (n : ℤ)).val.app (.op ⊤)).hom' (degreeSection 𝒜 n a) =
      (((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
          (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)).hom'
        (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩) :=
  Subtype.ext (funext fun z =>
    (twistPushforwardMap_degreeSection_val 𝒜 ℬ ψ n a z).trans
      (restrictUnit_degreeSection_val 𝒜 ℬ ψ n ⟨ψ a, ψ.map_mem a.2⟩ z).symm)

/-! ### The two adjunction coherences -/

/-- The unit of the pullback--pushforward adjunction followed by the pushforward of the
comparison map on the `n`-th twist is the adjoint form of that comparison map, followed by the
pushforward of the identification of restriction with pullback.

This is `CategoryTheory.Adjunction.homEquiv_unit` for the transpose that defines
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`. -/
public theorem unit_comp_map_twistMap (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
        (twistingSheaf 𝒜 n) ≫
      (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map (twistMap 𝒜 ℬ ψ n) =
    twistPushforwardMap 𝒜 ℬ ψ n ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
        (twistingSheaf ℬ n)) := by
  have hmap : (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map (twistMap 𝒜 ℬ ψ n) =
      (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
          (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv
            (twistingSheaf 𝒜 n) _).symm (twistPushforwardMap 𝒜 ℬ ψ n)) ≫
        (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
          ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
            (twistingSheaf ℬ n)) :=
    Functor.map_comp _ _ _
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
        (twistingSheaf 𝒜 n) ≫
      (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv
          (twistingSheaf 𝒜 n) _).symm (twistPushforwardMap 𝒜 ℬ ψ n)) =
      twistPushforwardMap 𝒜 ℬ ψ n :=
    (Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ))
      _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  refine Eq.trans (congrArg (fun k =>
    (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
      (twistingSheaf 𝒜 n) ≫ k) hmap) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫ (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
    ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ n))) hu

/-- The unit of the restriction adjunction followed by the pushforward of the identification of
restriction with pullback is the unit of the pullback--pushforward adjunction.

This is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, which applies because
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is by definition
`CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions. -/
public theorem restrictUnit_comp_map_restrictFunctorIsoPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (M : Y.Modules) :
    (Scheme.Modules.restrictAdjunction g).unit.app M ≫
        (Scheme.Modules.pushforward g).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction g) M

/-- Equal morphisms of modules agree on global sections. -/
private theorem hom_app_top_congr {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N} (h : f = g)
    (s : M.val.obj (.op ⊤)) : (f.val.app (.op ⊤)).hom' s = (g.val.app (.op ⊤)).hom' s := by
  subst h
  rfl

/-! ### Tag 01MY, part (1) -/

/-- **Tag 01MY, part (1), homogeneous global sections.** The comparison map on the `n`-th twist
carries the global section of `O(n)` attached to a homogeneous element `a` of degree `n` to the
global section attached to `psi a`, both read through the unit of the pullback--pushforward
adjunction. -/
@[stacks 01MY "part (1), homogeneous global sections"]
public theorem twistMap_degreeSection (ψ : 𝒜 →+*ᵍ ℬ) (n : ℕ) (a : 𝒜 n) :
    ((projMapData 𝒜 ℬ ψ).twistMap (n : ℤ)).val.app (.op ⊤)
      (((Scheme.Modules.pullbackPushforwardAdjunction (projMapData 𝒜 ℬ ψ).hom).unit.app
        (twistingSheaf 𝒜 (n : ℤ))).val.app (.op ⊤)
          (degreeSection 𝒜 n a)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
      (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)
        (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩) := by
  refine Eq.trans (hom_app_top_congr (unit_comp_map_twistMap 𝒜 ℬ ψ (n : ℤ)) _) ?_
  refine Eq.trans (congrArg
    (((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ (n : ℤ))).val.app (.op ⊤)).hom'
    (twistPushforwardMap_degreeSection 𝒜 ℬ ψ n a)) ?_
  exact hom_app_top_congr (restrictUnit_comp_map_restrictFunctorIsoPullback
    (mapDomain 𝒜 ℬ ψ).ι (twistingSheaf ℬ (n : ℤ))) _

end Stacks.AlgebraicGeometry.ProjTwistTheta

end
