module

public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0
public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Assembly
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Local
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective

/-!
# Tag 01N1 part (3)'s twist comparison on homogeneous global sections, for a graded surjection

`Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap` identifies the pullback of `𝒪_{Proj 𝒮}(n)`
along `Proj ψ`, for a graded ring homomorphism `ψ : 𝒮 →+*ᵍ ℬ` everywhere defined
(`mapDomain 𝒮 ℬ ψ = ⊤`) and invertible on twists, with `𝒪_{Proj ℬ}(n)` — but only as a
`Nonempty`, so no fact proved about the *specific* comparison its proof builds can be transported
to whatever witness `Nonempty.some` returns. This file supplies a named replacement,
`pullbackTwistCompositeIso`, built from the same five structural factors and the same comparison
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, and computes its action on a homogeneous
global section attached to a homogeneous element.

The route mirrors `StacksFrontier/AlgebraicGeometry/ProjInclusionDegreeSection/Basic.lean`, which
performs the analogous computation for Tag 01NO's comparison in the chart-inclusion case: every
factor other than the one built from `twistMap` is a structural isomorphism of the inverse image,
and `Stacks.AlgebraicGeometry.PullbackUnit` (the companion file
`ProjInclusionDegreeSection/Unit.lean`) says what each of those does to a pulled-back global
section, generically, with no reference to `Proj` at all. The present file's factors differ from
that precedent's only in using `AlgebraicGeometry.Scheme.Modules.pullbackCongr` for both
congruences, in place of one `pullbackCongr` and one raw `CategoryTheory.eqToIso`; the two are
the same isomorphism (`Stacks.AlgebraicGeometry.PullbackUnit`'s module docstring: `pullbackCongr`
*is* `eqToIso` of the induced equality of objects, after `subst`), so writing the comparison with
`pullbackCongr` throughout lets the existing pointwise lemmas apply with no new machinery.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.baseChange`: the section
  `Proj ℬ ⟶ U(ψ)` of the inclusion, present once `U(ψ) = ⊤`.
* `Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistCompositeIso`: the
  degree-`n` comparison `(Proj ψ)^*𝒪_{Proj 𝒮}(n) ≅ 𝒪_{Proj ℬ}(n)`, as a named isomorphism rather
  than a `Nonempty` witness.
* `Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso`: the same comparison from
  `nonempty_pullbackTwist_projMap`'s own hypotheses (eventual surjectivity, generation in degree
  one), a direct drop-in replacement for `nonempty_pullbackTwist_projMap (...).some`.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistCompositeIso_degreeSection`
  and its restatement `pullbackTwistIso_degreeSection`:
  **the comparison carries the pulled-back global section of `𝒪(n)` attached to a homogeneous
  element `a` to the global section attached to `ψ a`.** This is exactly the compatibility with
  `Stacks.AlgebraicGeometry.ProjTwistedSections.smul_homogeneous` that a family of these
  comparisons, one per degree, would need in order to be assembled into a morphism of graded
  modules: on the generators `a` of degree one, which generate the whole graded ring, the
  comparison is forced to agree with multiplication by `ψ a`.

## What this does not give

Only the action on one homogeneous global section at a time is computed, not abstract
multiplicativity of the comparison as an endomorphism family in the sense of
`Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative` — which is not needed here, because
`smul_homogeneous`-compatibility is a statement about one section at a time, not about a product
of two. Nothing is said about invertibility of `pullbackTwistCompositeIso`'s underlying morphism:
that is exactly `Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap`, supplied here
as the hypothesis `htw` rather than re-derived.

A consumer that needs more than one section at a time (for instance, the degreewise-finiteness
transport in `StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardGradedSections.lean`) runs
into exactly this limit. `pullbackTwistCompositeIso_degreeSection`/`pullbackTwistIso_degreeSection`
give the comparison's action *elementwise*: one degree-one generator `a`, one section built from
it by `degreeSection d a`. Additivity of `degreeSection`
extends this across *sums of ring elements acting* — `degreeSection d a + degreeSection d a' =
degreeSection d (a + a')` — but not across arbitrary sections of the target sheaf, which need not
be a `degreeSection` image of any single ring element; closing that remaining gap by reduction to
this elementwise fact would need `degreeSection` to be surjective at the relevant degree, which is
not available for every sheaf this comparison is applied to. Bridging it in general would need the
composite-multiplicativity that `StacksFrontier/AlgebraicGeometry/ThetaMultiplicative/Basic.lean`'s
module docstring records as unavailable for a composite of [Stacks, Tag 01NO] comparisons wrapped
in the same five structural factors this file's `pullbackTwistCompositeIso` is built from; that
claim was checked against the present composite and found accurate.

## References

* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Filter TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.PullbackUnit
open Stacks.AlgebraicGeometry.ProjInclusionDegreeSection (comp_app_of)

namespace Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection

universe u

variable {S B σ τ : Type u}
  [CommRing S] [CommRing B] [SetLike σ S] [AddSubgroupClass σ S]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒮 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒮] [GradedRing ℬ]

/-- **The section of the inclusion.** For a graded ring homomorphism everywhere defined
(`mapDomain 𝒮 ℬ ψ = ⊤`), the induced identification of `Proj ℬ` with `U(ψ)`, composed with the
inclusion of `U(ψ)` into `(mapDomain 𝒮 ℬ ψ).toScheme`. This is the morphism named `e` in the
proof of `Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap`. -/
@[irreducible] public def baseChange (ψ : 𝒮 →+*ᵍ ℬ) (hdom : mapDomain 𝒮 ℬ ψ = ⊤) :
    AlgebraicGeometry.Proj ℬ ⟶ (mapDomain 𝒮 ℬ ψ).toScheme :=
  (Scheme.topIso _).inv ≫ ((AlgebraicGeometry.Proj ℬ).isoOfEq hdom.symm).hom

/-- **`baseChange` followed by the induced morphism is `Proj ψ`.** -/
public theorem baseChange_comp_mapHom (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hdom : mapDomain 𝒮 ℬ ψ = ⊤) :
    baseChange 𝒮 ℬ ψ hdom ≫ mapHom 𝒮 ℬ ψ = AlgebraicGeometry.Proj.map ψ hψ := by
  rw [← Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map 𝒮 ℬ ψ hψ hdom,
    Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop, baseChange, Category.assoc]

omit [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **`baseChange` is a section of the inclusion of `U(ψ)`.** -/
public theorem baseChange_comp_ι (ψ : 𝒮 →+*ᵍ ℬ) (hdom : mapDomain 𝒮 ℬ ψ = ⊤) :
    baseChange 𝒮 ℬ ψ hdom ≫ (mapDomain 𝒮 ℬ ψ).ι = 𝟙 (AlgebraicGeometry.Proj ℬ) := by
  rw [baseChange, Category.assoc]
  exact Stacks.AlgebraicGeometry.RelativeProj.topIso_inv_isoOfEq_hom_ι 𝒮 ℬ ψ hdom

variable {𝒮 ℬ}

/-- **The degree-`n` comparison, as a named isomorphism.** The same five structural factors as
`Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap`, with both congruence factors written
through `AlgebraicGeometry.Scheme.Modules.pullbackCongr` rather than raw `CategoryTheory.eqToIso`
— the same isomorphism, by `Stacks.AlgebraicGeometry.PullbackUnit`'s own account of what
`pullbackCongr` is. -/
public def pullbackTwistCompositeIso (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hdom : mapDomain 𝒮 ℬ ψ = ⊤) (n : ℤ) (htw : IsIso (twistMap 𝒮 ℬ ψ n)) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒮 n) ≅
      twistingSheaf ℬ n :=
  have := htw
  ((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒮 ℬ ψ hψ hdom)).symm.app
        (twistingSheaf 𝒮 n) ≪≫
      ((Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ ψ hdom) (mapHom 𝒮 ℬ ψ)).app
          (twistingSheaf 𝒮 n)).symm ≪≫
      (Scheme.Modules.pullback (baseChange 𝒮 ℬ ψ hdom)).mapIso (asIso (twistMap 𝒮 ℬ ψ n))) ≪≫
    ((Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ ψ hdom) (mapDomain 𝒮 ℬ ψ).ι).app
          (twistingSheaf ℬ n) ≪≫
      (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒮 ℬ ψ hdom)).app (twistingSheaf ℬ n) ≪≫
      (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).app (twistingSheaf ℬ n))

/-- A composite of three module morphisms, evaluated on a global section, is computed stepwise. -/
private theorem comp_comp_app_of {W : Scheme.{u}} {M₀ M₁ M₂ M₃ : W.Modules} (a : M₀ ⟶ M₁)
    (b : M₁ ⟶ M₂) (c : M₂ ⟶ M₃) (V : W.Opens) {x : M₀.val.obj (op V)} {y : M₁.val.obj (op V)}
    {z : M₂.val.obj (op V)} {w : M₃.val.obj (op V)} (ha : a.val.app (op V) x = y)
    (hb : b.val.app (op V) y = z) (hc : c.val.app (op V) z = w) :
    (a ≫ b ≫ c).val.app (op V) x = w :=
  (comp_app_of _ _ V ha).trans ((comp_app_of _ _ V hb).trans hc)

/-- **The first three factors on a homogeneous global section.** The congruence undoing
`baseChange_comp_mapHom`, the pseudofunctoriality isomorphism for the factorisation of the
induced morphism through `baseChange`, and the functor image of `twistMap`. -/
public theorem head_degreeSection (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hdom : mapDomain 𝒮 ℬ ψ = ⊤) (n : ℕ) (a : 𝒮 n) :
    (((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒮 ℬ ψ hψ hdom)).inv.app
          (twistingSheaf 𝒮 (n : ℤ)) ≫
        (Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ ψ hdom) (mapHom 𝒮 ℬ ψ)).inv.app
          (twistingSheaf 𝒮 (n : ℤ)) ≫
        (Scheme.Modules.pullback (baseChange 𝒮 ℬ ψ hdom)).map
          (twistMap 𝒮 ℬ ψ (n : ℤ))).val.app (op ⊤))
        (pullbackSection (AlgebraicGeometry.Proj.map ψ hψ)
          (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a)) =
      pullbackSection (baseChange 𝒮 ℬ ψ hdom)
        ((Scheme.Modules.pullback (mapDomain 𝒮 ℬ ψ).ι).obj (twistingSheaf ℬ (n : ℤ)))
        (pullbackSection (mapDomain 𝒮 ℬ ψ).ι (twistingSheaf ℬ (n : ℤ))
          (degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩)) :=
  comp_comp_app_of _ _ _ ⊤
    (pullbackCongr_inv_pullbackSection (baseChange_comp_mapHom 𝒮 ℬ ψ hψ hdom)
      (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a))
    (pullbackComp_inv_pullbackSection (baseChange 𝒮 ℬ ψ hdom) (mapHom 𝒮 ℬ ψ)
      (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a))
    ((pullback_map_pullbackSection (baseChange 𝒮 ℬ ψ hdom) (twistMap 𝒮 ℬ ψ (n : ℤ)) _).trans
      (congrArg (pullbackSection (baseChange 𝒮 ℬ ψ hdom) _)
        (twistMap_degreeSection 𝒮 ℬ ψ n a)))

omit [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **The last two factors on a homogeneous global section.** The pseudofunctoriality
isomorphism undoing the factorisation of `baseChange_comp_ι`, the congruence collapsing the
composite to the identity, and the pullback along the identity. -/
public theorem tail_degreeSection (ψ : 𝒮 →+*ᵍ ℬ) (hdom : mapDomain 𝒮 ℬ ψ = ⊤) (n : ℕ) (b : ℬ n) :
    (((Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ ψ hdom) (mapDomain 𝒮 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ (n : ℤ)) ≫
        (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒮 ℬ ψ hdom)).hom.app
          (twistingSheaf ℬ (n : ℤ)) ≫
        (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
          (twistingSheaf ℬ (n : ℤ))).val.app (op ⊤))
        (pullbackSection (baseChange 𝒮 ℬ ψ hdom)
          ((Scheme.Modules.pullback (mapDomain 𝒮 ℬ ψ).ι).obj (twistingSheaf ℬ (n : ℤ)))
          (pullbackSection (mapDomain 𝒮 ℬ ψ).ι (twistingSheaf ℬ (n : ℤ)) (degreeSection ℬ n b))) =
      degreeSection ℬ n b :=
  comp_comp_app_of _ _ _ ⊤
    (pullbackComp_hom_pullbackSection (baseChange 𝒮 ℬ ψ hdom) (mapDomain 𝒮 ℬ ψ).ι
      (twistingSheaf ℬ (n : ℤ)) (degreeSection ℬ n b))
    (pullbackCongr_hom_pullbackSection (baseChange_comp_ι 𝒮 ℬ ψ hdom)
      (twistingSheaf ℬ (n : ℤ)) (degreeSection ℬ n b))
    (pullbackId_hom_pullbackSection (AlgebraicGeometry.Proj ℬ) (twistingSheaf ℬ (n : ℤ))
      (degreeSection ℬ n b))

/-- **The whole six-factor composite on a homogeneous global section.** -/
public theorem composite_degreeSection (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hdom : mapDomain 𝒮 ℬ ψ = ⊤) (n : ℕ) (a : 𝒮 n) :
    ((((Scheme.Modules.pullbackCongr (baseChange_comp_mapHom 𝒮 ℬ ψ hψ hdom)).inv.app
            (twistingSheaf 𝒮 (n : ℤ)) ≫
          (Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ ψ hdom) (mapHom 𝒮 ℬ ψ)).inv.app
            (twistingSheaf 𝒮 (n : ℤ)) ≫
          (Scheme.Modules.pullback (baseChange 𝒮 ℬ ψ hdom)).map
            (twistMap 𝒮 ℬ ψ (n : ℤ))) ≫
        ((Scheme.Modules.pullbackComp (baseChange 𝒮 ℬ ψ hdom) (mapDomain 𝒮 ℬ ψ).ι).hom.app
              (twistingSheaf ℬ (n : ℤ)) ≫
          (Scheme.Modules.pullbackCongr (baseChange_comp_ι 𝒮 ℬ ψ hdom)).hom.app
            (twistingSheaf ℬ (n : ℤ)) ≫
          (Scheme.Modules.pullbackId (AlgebraicGeometry.Proj ℬ)).hom.app
            (twistingSheaf ℬ (n : ℤ)))).val.app (op ⊤))
        (pullbackSection (AlgebraicGeometry.Proj.map ψ hψ)
          (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a)) =
      degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩ :=
  (comp_app_of _ _ ⊤ (head_degreeSection ψ hψ hdom n a)).trans
    (tail_degreeSection ψ hdom n ⟨ψ a, ψ.map_mem a.2⟩)

/-- **The named comparison carries the pulled-back global section of `𝒪(n)` attached to a
homogeneous element `a` to the global section attached to `ψ a`.**

This is the compatibility `Stacks.AlgebraicGeometry.ProjTwistedSections.smul_homogeneous`
(Tag 03GK) needs of a family of these comparisons, one per degree, in order to be assembled into
a morphism of graded modules: on a generator, the comparison agrees with multiplication by its
image. -/
public theorem pullbackTwistCompositeIso_degreeSection (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hdom : mapDomain 𝒮 ℬ ψ = ⊤) (n : ℕ) (htw : IsIso (twistMap 𝒮 ℬ ψ (n : ℤ))) (a : 𝒮 n) :
    (pullbackTwistCompositeIso ψ hψ hdom (n : ℤ) htw).hom.val.app (op ⊤)
        (pullbackSection (AlgebraicGeometry.Proj.map ψ hψ)
          (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a)) =
      degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩ :=
  composite_degreeSection ψ hψ hdom n a

/-- **The named comparison, from the same hypotheses as
`Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap`.** A drop-in replacement for that
theorem's `Nonempty` witness: everywhere-surjective on the graded pieces eventually
(`hsurj`) and generated in degree one (`hgen`) derive `mapDomain 𝒮 ℬ ψ = ⊤` and invertibility of
`twistMap 𝒮 ℬ ψ n`, the same way `nonempty_pullbackTwist_projMap`'s proof does, and
`pullbackTwistCompositeIso` is applied to the result — so anything proved about
`pullbackTwistCompositeIso` (in particular `pullbackTwistCompositeIso_degreeSection`) is proved
about this comparison too, unlike `nonempty_pullbackTwist_projMap.some`. -/
public def pullbackTwistIso (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hsurj : Function.Surjective (ψ : S → B))
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) (n : ℤ) :
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map ψ hψ)).obj (twistingSheaf 𝒮 n) ≅
      twistingSheaf ℬ n :=
  have hev : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d) :=
    Eventually.of_forall fun d => Proj.gradedAddHom_surjective_of_surjective ψ hsurj d
  have hdom : mapDomain 𝒮 ℬ ψ = ⊤ :=
    Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective 𝒮 ℬ ψ hev
  have htw : IsIso (twistMap 𝒮 ℬ ψ n) :=
    Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap 𝒮 ℬ ψ hev hgen n
  pullbackTwistCompositeIso ψ hψ hdom n htw

/-- **`pullbackTwistIso`'s action on a homogeneous global section**, restated from
`pullbackTwistCompositeIso_degreeSection` under `nonempty_pullbackTwist_projMap`'s own
hypotheses. -/
public theorem pullbackTwistIso_degreeSection (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hsurj : Function.Surjective (ψ : S → B))
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤) (n : ℕ) (a : 𝒮 n) :
    (pullbackTwistIso ψ hψ hsurj hgen (n : ℤ)).hom.val.app (op ⊤)
        (pullbackSection (AlgebraicGeometry.Proj.map ψ hψ)
          (twistingSheaf 𝒮 (n : ℤ)) (degreeSection 𝒮 n a)) =
      degreeSection ℬ n ⟨ψ a, ψ.map_mem a.2⟩ :=
  pullbackTwistCompositeIso_degreeSection ψ hψ _ n _ a

end Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection

end
