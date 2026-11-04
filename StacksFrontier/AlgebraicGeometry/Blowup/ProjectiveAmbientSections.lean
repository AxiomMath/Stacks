module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveIdealSheafTwistSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.AmbientSectionsInjective
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaAffine.Sections
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistGlobalSectionsPolynomial

/-!
# Serre's computation of the twisted sections on the blowup, surjective half

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec A` in
`I`. [Stacks, Tag 0AG6] part (3) says that the canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` is bijective
for every large `q`. Its injective half is proved, as
`Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections`. This file
supplies the **surjective** half and therefore the bijectivity.

The surjection `Γ(𝐏, 𝒪_𝐏(q)) ⟶ Γ(X, 𝒪_X(q))` is also proved, in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveIdealSheafTwistSections.lean`, and so is the
computation `Γ(𝐏, 𝒪_𝐏(q)) = (A[T₀, …, T_m])_q` on projective space
(`Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection`). What was missing, and is proved
here, is that the two are maps out of *the same* group: the surjection onto `Γ(X, 𝒪_X(q))` is
built from the **projection formula** at the closed immersion `i : X ⟶ 𝐏`, while the computation
on `𝐏` is about the **canonical section** of a homogeneous polynomial, which travels along the
*adjunction unit*. The content of this file is that the two agree.

## The identity, and why it is formal

Write `f : X ⟶ Y` for a closed immersion, `η` for the unit of `f^* ⊣ f_*` and `φ : 𝒪_Y ⟶ f_*𝒪_X`
for the canonical restriction. The projection formula
`Stacks.AffineProjectionFormula.projectionFormulaMap` carries, over any open, the image of a
pure tensor `a ⊗ b` to the image of `a ⊗ η b`
(`Stacks.ProjectionFormula.projectionFormulaMap_app_top`). Feeding it the global section
`1 ⊗ s` — which is what the inverse left unitor of `s` is, by
`Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply` — therefore returns `1 ⊗ η s`, and the left
unitor on the other side turns that back into `η s`. So *the projection formula read on
`⊤`-sections is the adjunction unit on `⊤`-sections*, with no hypothesis beyond the one needed to
form the projection-formula isomorphism. Nothing about the geometry enters: the three steps are a
section formula for the projection formula, a section formula for the unitor, and `one_smul`.

Sections of a direct image over the whole target are the sections of the source
(`Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, which is the identity), and `f ⁻¹ᵁ ⊤` and
`⊤` are definitionally equal, so no further comparison intervenes anywhere.

## Main results

The elided prefix is `Stacks.Blowup`.

* `pushforwardTensorSheafIso_app_top`: the projection formula at a closed immersion, on a pure
  tensor of global sections.
* `pushforwardUnitTensorIso_app_top_one_tmul`: **the identity above** — the projection formula
  followed by the left unitor carries `1 ⊗ s` to the image of
  `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection`.
* `leftUnitor_twistedSectionsUnitMap`: the same at `Proj ψ` for a graded surjection `ψ`, in the
  vocabulary of `Stacks.Blowup.twistedSectionsUnitMap` and
  `Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.twistedSectionsAddHom`: the composite that
  `StacksFrontier/AlgebraicGeometry/Blowup/ProjectiveIdealSheafTwistSections.lean` proves surjective
  *is* the adjunction unit followed by the comparison that
  `Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso_degreeSection` describes.
* `surjective_degreeSection_of_surjective_comp`: consequently surjectivity of the canonical
  section map transports along `Proj ψ`.
* `exists_forall_surjective_degreeSection_reesGrading` and
  `exists_forall_surjective_ambientSections`: **the surjective half of [Stacks, Tag 0AG6] part
  (3) on the blowup**, for a chosen finite generating family and then for an arbitrary ideal of a
  Noetherian ring.
* `exists_forall_bijective_ambientSections`: **the bijectivity**, which was the field
  `amb_serre_sections` of `Stacks.LocalCohomology.UniformityIII.GeometricInput` and is now
  called by clause (4) of [Stacks, Tag 0GA7] rather than assumed. It is also what
  `StacksFrontier/AlgebraicGeometry/Blowup/TwistedSectionsIdealPow.lean` promotes to an isomorphism
  of `A`-modules, which is the last hypothesis of [Stacks, Tag 0G9Z].

## What is still owed, and why no attribute is attached

`exists_forall_bijective_ambientSections` is [Stacks, Tag 0AG6] part (3) at the Rees grading
only, not for a general graded ring generated in degree one, so it is not a full clause of that
tag; and it is an *input* to the four clauses of [Stacks, Tag 0GA7], not a clause of it. With it
shed, the one field of `Stacks.LocalCohomology.UniformityIII.GeometricInput` that is a theorem of
the source rather than part of the Situation of [Stacks, Tag 0GA6] is `base_vanishing_gt`, and
[Stacks, Tag 02V7] is registered in this repository only at fibre dimension zero; the Situation's
own fields — the two short exact sequences and the three properties defining `q(S)` — also still
stand, so [Stacks, Tag 0GA7] remains conditional. Nothing below carries an attribute for either
tag.

## Implementation notes

All the carriers are taken in one universe `Type u`, as in
`StacksFrontier/AlgebraicGeometry/ProjMapTwistDegreeSection/Basic.lean`.

`Stacks.Blowup.surjective_degreeSection_of_surjective_comp` is stated for a variable graded
surjection `ψ` and consumes the surjectivity of the composite as a hypothesis, rather than being
inlined into the blowup theorem: instantiating the unitor bookkeeping at
`Stacks.Blowup.reesPresentation` directly exhausts the kernel's deterministic reduction budget,
`AlgebraicGeometry.Proj.map` being declared with the transparency-respecting defeq check
disabled. With the bookkeeping done on variables, the blowup theorem only applies it.

Every equality of morphisms is transported onto a section by `congrArg` of a function that
evaluates a morphism, never by `rw`: the goals here mix the two spellings of the category of
modules and `rw` reports them as not type-correct at `implicit` transparency.

The projection-formula map has two spellings as well, one for a morphism of ringed spaces and
one for a morphism of schemes, and `pushforwardTensorSheafIso_app_top` is stated in the first
and proved from a lemma about the second. They are not interchangeable by unfolding: the
ringed-space map tensors the counit with an identity through
`CategoryTheory.Functor.uncurry` of the tensor bifunctor, the scheme map through the flip of
that bifunctor, and the two agree only by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`, which is what
`Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq` supplies. That lemma and
`Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso_hom` are therefore composed
explicitly instead of being left to the elaborator, which does not find the composite.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GA7](https://stacks.math.columbia.edu/tag/0GA7)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules)
open Stacks.SheafOfModules.TensorStalkRingedSpace
  (toTensorSheafSection tensorSheafMap_app_toTensorSheafSection)
open Stacks.SheafOfModules.OnSpace (tensorObjTmul unitSection)
open Stacks.AlgebraicGeometry.PullbackUnit (pullbackSection)
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep (twistedSectionsAddHom)
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection (pullbackTwistIso)
open scoped TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.Blowup

attribute [local instance] modulesMonoidal modulesMonoidal'

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- **The projection formula at a closed immersion, on a pure tensor of global sections.** -/
public theorem pushforwardTensorSheafIso_app_top (G : X.Modules) (E : Y.Modules)
    (a : ((Scheme.Modules.pushforward f).obj G).val.obj (op ⊤))
    (b : E.val.obj (op ⊤)) :
    ((Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso f G E).hom.val.app
        (op ⊤)).hom
        (toTensorSheafSection Y.toRingedSpace
          ((Scheme.Modules.pushforward f).obj G) E (op ⊤)
          (a ⊗ₜ[Y.toRingedSpace.presheaf.obj (op ⊤)] b))
      = toTensorSheafSection X.toRingedSpace G ((Scheme.Modules.pullback f).obj E) (op ⊤)
          (a ⊗ₜ[X.toRingedSpace.presheaf.obj (op ⊤)] pullbackSection f E b) :=
  Eq.trans (congrArg (fun φ => (φ.val.app (op ⊤)).hom
      (toTensorSheafSection Y.toRingedSpace ((Scheme.Modules.pushforward f).obj G) E (op ⊤)
        (a ⊗ₜ[Y.toRingedSpace.presheaf.obj (op ⊤)] b)))
    ((Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso_hom f G E).trans
      (Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap_eq f G E).symm))
    (Stacks.ProjectionFormula.projectionFormulaMap_app_top f G E a b)

/-- **The projection formula followed by the left unitor, on the global section `1 ⊗ s`.** -/
public theorem pushforwardUnitTensorIso_app_top_one_tmul (E : Y.Modules) (G : X.Modules)
    (e : (Scheme.Modules.pullback f).obj E ≅ G) (s : E.val.obj (op ⊤)) :
    ((pushforwardUnitTensorIso f E G e).hom.val.app (op ⊤)).hom
        (tensorObjTmul Y.toRingedSpace
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) E (op ⊤)
          (1 : X.toRingedSpace.presheaf.obj (op ⊤)) s)
      = (e.hom.val.app (op ⊤)).hom (pullbackSection f E s) := by
  refine Eq.trans (congrArg
    (fun t => (((Scheme.Modules.pushforward f).map
        ((𝟙_ X.Modules ◁ e.hom) ≫ (λ_ G).hom)).val.app (op ⊤)).hom t)
    (pushforwardTensorSheafIso_app_top f (SheafOfModules.unit X.ringCatSheaf) E
      (1 : X.toRingedSpace.presheaf.obj (op ⊤)) s)) ?_
  refine Eq.trans (congrArg ((λ_ G).hom.val.app (op ⊤)).hom
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul X.toRingedSpace
      (𝟙_ X.Modules) e.hom (op ⊤) (1 : X.toRingedSpace.presheaf.obj (op ⊤))
      (pullbackSection f E s))) ?_
  exact (Stacks.SheafOfModules.OnSpace.leftUnitor_tmul X.toRingedSpace G (op ⊤)
    (1 : X.toRingedSpace.presheaf.obj (op ⊤))
    ((e.hom.val.app (op ⊤)).hom (pullbackSection f E s))).trans (one_smul _ _)

/-- An isomorphism of modules followed by its inverse is the identity on global sections. -/
private theorem iso_hom_app_top_inv_app_top {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (x : N.val.obj (op ⊤)) :
    (e.hom.val.app (op ⊤)).hom ((e.inv.val.app (op ⊤)).hom x) = x :=
  congrArg (fun α : N ⟶ N => (α.val.app (op ⊤)).hom x) e.inv_hom_id

end General

section ProjMap

variable {S B' σ τ : Type u} [CommRing S] [CommRing B'] [SetLike σ S] [AddSubgroupClass σ S]
  [SetLike τ B'] [AddSubgroupClass τ B'] (𝒮 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒮] [GradedRing ℬ]
  (ψ : 𝒮 →+*ᵍ ℬ)
  (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
  (hsurj : Function.Surjective (ψ : S → B'))
  (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
  [IsClosedImmersion (AlgebraicGeometry.Proj.map ψ hψ)]

/-- **The projection-formula composite on global sections is the adjunction unit followed by the
pullback comparison.** -/
public theorem leftUnitor_twistedSectionsUnitMap (d : ℤ)
    (s : (twistingSheaf 𝒮 d).val.obj (op ⊤)) :
    ((λ_ (twistObj ℬ d)).hom.val.app (op ⊤)).hom
        (twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d
          (twistedSectionsAddHom 𝒮
            (SheafOfModules.unitToPushforwardObjUnit
              (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom) d
            (((λ_ (twistObj 𝒮 d)).inv.val.app (op ⊤)).hom s)))
      = ((pullbackTwistIso ψ hψ hsurj hgen d).hom.val.app (op ⊤)).hom
          (pullbackSection (AlgebraicGeometry.Proj.map ψ hψ) (twistingSheaf 𝒮 d) s) := by
  have h1 : ((λ_ (twistObj 𝒮 d)).inv.val.app (op ⊤)).hom s
      = tensorObjTmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules) (twistObj 𝒮 d) (op ⊤)
          (1 : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤)) s :=
    Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twistObj 𝒮 d) (op ⊤) s
  have h2 : twistedSectionsAddHom 𝒮
        (SheafOfModules.unitToPushforwardObjUnit
          (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom) d
        (tensorObjTmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules) (twistObj 𝒮 d) (op ⊤)
          (1 : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤)) s)
      = tensorObjTmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
            (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf))
          (twistObj 𝒮 d) (op ⊤)
          (((SheafOfModules.unitToPushforwardObjUnit
              (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom).val.app (op ⊤)).hom
            (1 : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤))) s := by
    have mappedSection := tensorSheafMap_app_toTensorSheafSection
      (AlgebraicGeometry.Proj 𝒮).toRingedSpace
      (𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules) (twistObj 𝒮 d)
      ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf))
      (twistObj 𝒮 d)
      (SheafOfModules.unitToPushforwardObjUnit
        (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom)
      (𝟙 (twistObj 𝒮 d)) ⊤
      (1 : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤)) s
    exact (congrArg (fun tensorMap => ((tensorMap.val.app (op ⊤)).hom
      (tensorObjTmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace
        (𝟙_ (AlgebraicGeometry.Proj 𝒮).Modules) (twistObj 𝒮 d) (op ⊤)
        (1 : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤)) s)))
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
        (AlgebraicGeometry.Proj 𝒮).sheaf
        (SheafOfModules.unitToPushforwardObjUnit
          (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom)
        (𝟙 (twistObj 𝒮 d)))).symm.trans mappedSection
  have h3 : (((SheafOfModules.unitToPushforwardObjUnit
          (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom).val.app (op ⊤)).hom
        (1 : (AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf.obj (op ⊤)))
      = (1 : (AlgebraicGeometry.Proj ℬ).toRingedSpace.presheaf.obj (op ⊤)) :=
    map_one ((AlgebraicGeometry.Proj.map ψ hψ).app ⊤).hom
  have h4 := pushforwardUnitTensorIso_app_top_one_tmul
    (AlgebraicGeometry.Proj.map ψ hψ) (twistingSheaf 𝒮 d)
    (𝟙_ (AlgebraicGeometry.Proj ℬ).Modules ⊗ twistObj ℬ d)
    (pullbackTwistUnitIso 𝒮 ℬ ψ hψ hsurj hgen d) s
  have hstep : twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d
        (twistedSectionsAddHom 𝒮
          (SheafOfModules.unitToPushforwardObjUnit
            (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom) d
          (((λ_ (twistObj 𝒮 d)).inv.val.app (op ⊤)).hom s))
      = ((λ_ (twistObj ℬ d)).inv.val.app (op ⊤)).hom
          (((pullbackTwistIso ψ hψ hsurj hgen d).hom.val.app (op ⊤)).hom
            (pullbackSection (AlgebraicGeometry.Proj.map ψ hψ) (twistingSheaf 𝒮 d) s)) := by
    refine Eq.trans (congrArg (twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen d)
      (Eq.trans (congrArg (twistedSectionsAddHom 𝒮
        (SheafOfModules.unitToPushforwardObjUnit
          (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom) d) h1)
        (Eq.trans h2 (congrArg (fun z => tensorObjTmul
          (AlgebraicGeometry.Proj 𝒮).toRingedSpace
          ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
            (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf))
          (twistObj 𝒮 d) (op ⊤) z s) h3)))) ?_
    exact h4
  refine Eq.trans (congrArg ((λ_ (twistObj ℬ d)).hom.val.app (op ⊤)).hom hstep) ?_
  exact iso_hom_app_top_inv_app_top (λ_ (twistObj ℬ d)) _

/-- **Transport of surjectivity of the section map along the closed immersion `Proj ψ`.** If
every global section of `𝒪_{Proj ℬ}(d)` lifts through the projection-formula composite, and
every global section of `𝒪_{Proj 𝒮}(d)` is the canonical section of a homogeneous element of
degree `d`, then every global section of `𝒪_{Proj ℬ}(d)` is the canonical section of a
homogeneous element of degree `d` — namely of the image under `ψ` of the one upstairs.

The two `Stacks.Blowup.twistObj` unitors convert between the group
`Γ(Proj ℬ, 𝒪 ⊗ 𝒪(d))` that the projection-formula composite lands in and the group
`Γ(Proj ℬ, 𝒪(d))` that the canonical section lands in; the identification of the composite
itself is `Stacks.Blowup.leftUnitor_twistedSectionsUnitMap`, and the action of the pullback
comparison on a canonical section is
`Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso_degreeSection`. -/
public theorem surjective_degreeSection_of_surjective_comp (d : ℕ)
    (hcomp : Function.Surjective (fun t =>
      twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen (d : ℤ)
        (twistedSectionsAddHom 𝒮
          (SheafOfModules.unitToPushforwardObjUnit
            (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom) (d : ℤ) t)))
    (hsec : Function.Surjective
      (degreeSection 𝒮 d)) :
    Function.Surjective
      (degreeSection ℬ d) := by
  intro u
  obtain ⟨t, ht⟩ := hcomp (((λ_ (twistObj ℬ (d : ℤ))).inv.val.app (op ⊤)).hom u)
  obtain ⟨a, ha⟩ := hsec (((λ_ (twistObj 𝒮 (d : ℤ))).hom.val.app (op ⊤)).hom t)
  have h1 : ((λ_ (twistObj 𝒮 (d : ℤ))).inv.val.app (op ⊤)).hom
        (degreeSection 𝒮 d a) = t := by
    refine Eq.trans (congrArg ((λ_ (twistObj 𝒮 (d : ℤ))).inv.val.app (op ⊤)).hom ha) ?_
    exact iso_hom_app_top_inv_app_top (λ_ (twistObj 𝒮 (d : ℤ))).symm t
  refine ⟨⟨ψ a, ψ.map_mem a.2⟩, ?_⟩
  refine Eq.trans
    (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso_degreeSection
      ψ hψ hsurj hgen d a).symm ?_
  refine Eq.trans (leftUnitor_twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen (d : ℤ)
    (degreeSection 𝒮 d a)).symm ?_
  refine Eq.trans (congrArg (fun z => ((λ_ (twistObj ℬ (d : ℤ))).hom.val.app (op ⊤)).hom
      (twistedSectionsUnitMap 𝒮 ℬ ψ hψ hsurj hgen (d : ℤ)
        (twistedSectionsAddHom 𝒮
          (SheafOfModules.unitToPushforwardObjUnit
            (AlgebraicGeometry.Proj.map ψ hψ).toRingCatSheafHom) (d : ℤ) z))) h1) ?_
  refine Eq.trans (congrArg ((λ_ (twistObj ℬ (d : ℤ))).hom.val.app (op ⊤)).hom ht) ?_
  exact iso_hom_app_top_inv_app_top (λ_ (twistObj ℬ (d : ℤ))) u

end ProjMap

section Blowup

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.ProjectiveCohomology (polyGrading)

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` is surjective as soon as the degree-`q` section map
of [Stacks, Tag 0AG2] for the Rees grading is: the two differ by
`Stacks.Blowup.reesGradingEquivPow`, the identification of `Iᑫ` with the degree-`q` piece of the
Rees algebra. -/
public theorem surjective_ambientSections_of_surjective_degreeSection {I : Ideal A} (q : ℕ)
    (h : Function.Surjective
      (degreeSection (reesGrading I) q)) :
    Function.Surjective (Stacks.LocalCohomology.UniformityIII.ambientSections I q) := by
  intro u
  obtain ⟨b, hb⟩ := h u
  exact ⟨(reesGradingEquivPow I q).symm b,
    Eq.trans (congrArg (degreeSection
      (reesGrading I) q) ((reesGradingEquivPow I q).apply_symm_apply b)) hb⟩

/-- **Serre's computation of the twisted global sections on the blowup, surjective half**, for an
ideal with a chosen finite generating family: for every large `q` each global section of
`𝒪_X(q)` is the canonical section of a homogeneous element of degree `q` of the Rees algebra.

This is the sibling surjection `Γ(𝐏, 𝒪_𝐏(q)) ⟶ Γ(X, 𝒪_X(q))`
(`Stacks.Blowup.exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace` followed by
`Stacks.Blowup.twistedSectionsUnitMap`) composed with the computation of the sections on
projective space (`Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection`), the two being
glued by `Stacks.Blowup.surjective_degreeSection_of_surjective_comp`. -/
public theorem exists_forall_surjective_degreeSection_reesGrading {I : Ideal A} {m : ℕ}
    (x : Fin (m + 1) → A) (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x)) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      Function.Surjective
        (degreeSection (reesGrading I) q) := by
  have : IsClosedImmersion (AlgebraicGeometry.Proj.map (reesPresentation I x hx)
      (AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _
        (surjective_reesPresentation I x hx hspan))) :=
    isClosedImmersion_blowUpSpecToProjSpace I x hx hspan
  obtain ⟨q₀, hq₀⟩ :=
    exists_forall_surjective_twistedSectionsAddHom_blowUpSpecToProjSpace x hx hspan
  refine ⟨q₀.toNat, fun q hq => ?_⟩
  exact surjective_degreeSection_of_surjective_comp (polyGrading A m) (reesGrading I)
    (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) q
    (Function.Surjective.comp
      (twistedSectionsUnitMap_surjective (polyGrading A m) (reesGrading I)
        (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
        (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A m) (q : ℤ))
      (hq₀ (q : ℤ) (by omega)))
    (Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection A m q)

/-- **Serre's computation of the twisted global sections on the blowup, surjective half**, for an
arbitrary ideal of a Noetherian ring: for every large `q` the canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))`
of `Stacks.LocalCohomology.UniformityIII.ambientSections` is surjective.

A Noetherian ring has every ideal finitely generated, so a generating family is available for
`Stacks.Blowup.exists_forall_surjective_degreeSection_reesGrading`; it is padded with a zero so
as to be indexed by a nonempty `Fin`, which is the shape the projective-space results are stated
in. -/
public theorem exists_forall_surjective_ambientSections (I : Ideal A) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      Function.Surjective (Stacks.LocalCohomology.UniformityIII.ambientSections I q) := by
  classical
  obtain ⟨m, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hspan : Ideal.span (Set.range (Fin.snoc y (0 : A))) = I := by
    refine le_antisymm (Ideal.span_le.2 ?_) (hy ▸ Ideal.span_mono ?_)
    · rintro b ⟨j, rfl⟩
      refine Fin.lastCases ?_ ?_ j
      · simpa using Submodule.zero_mem I
      · intro j
        simpa using hy ▸ Ideal.subset_span (Set.mem_range_self (f := y) j)
    · rintro b ⟨j, rfl⟩
      exact ⟨j.castSucc, by simp⟩
  obtain ⟨q₀, hq₀⟩ := exists_forall_surjective_degreeSection_reesGrading (I := I)
    (Fin.snoc y 0)
    (fun j => hspan ▸ Ideal.subset_span (Set.mem_range_self (f := Fin.snoc y (0 : A)) j))
    hspan.symm
  exact ⟨q₀, fun q hq => surjective_ambientSections_of_surjective_degreeSection q (hq₀ q hq)⟩

/-- **The canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` on the blowup is bijective for every large `q`.**

This is [Stacks, Tag 0AG6] part (3) at the Rees grading, which was the field
`amb_serre_sections` of `Stacks.LocalCohomology.UniformityIII.GeometricInput` — an input of the
four clauses of [Stacks, Tag 0GA7] that is a theorem of the source rather than part of the
Situation of [Stacks, Tag 0GA6], and which
`Stacks.LocalCohomology.UniformityIII.bijective_ambientSections` now calls here instead. The
injective half is
`Stacks.LocalCohomology.UniformityIII.exists_forall_injective_ambientSections`; what is supplied
here is the surjective half. -/
public theorem exists_forall_bijective_ambientSections (I : Ideal A) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      Function.Bijective (Stacks.LocalCohomology.UniformityIII.ambientSections I q) :=
  Stacks.LocalCohomology.UniformityIII.exists_bijective_ambientSections_of_exists_surjective I
    (exists_forall_surjective_ambientSections I)

end Blowup

end Stacks.Blowup

end
