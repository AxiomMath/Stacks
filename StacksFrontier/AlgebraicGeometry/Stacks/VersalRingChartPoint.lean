module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction
public import StacksFrontier.Deformation.Artin.Versality.SliceSmoothness
public import StacksFrontier.Deformation.Artin.Versality.AffineChartVersality
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation

/-!
# Versality of a scheme chart at a finite type point (Stacks 0DQZ)

In the versal situation of **Stacks 0DQU** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S` — let `x : U ⟶ 𝒳` be a morphism from a scheme `U` locally of finite
type over `S` and let `u₀ ∈ U` be a finite type point with residue field `k = κ(u₀)`. **Stacks
0DQZ** lists four equivalent conditions on `(x, u₀)` and then concludes that, when they hold, the
completion `𝒪^∧_{U, u₀}` is a versal ring to `𝒳` at the induced point `x₀ : Spec k ⟶ 𝒳`.

This file supplies the second and third of those conditions and the final conclusion. The third
condition is versality of the formal object attached to the restriction of `x` to
`Spec 𝒪^∧_{U, u₀}`, and its equivalence with versality of `x` at `u₀` is Artin's Axioms, **Stacks
0CXK**; what is added here is the step from that equivalence to the definition of a versal ring
(**Stacks 0DQV**), which is the content of the sentence "The final statement follows from the
definitions as `𝒪^∧_{U, u₀}` prorepresents `𝓕_{U, k, u₀}`".

## Main results

* `AlgebraicGeometry.Stack.isVersalAt_iff_isSmooth_hatX`: **Stacks 0DQZ**, the equivalence of
  conditions (1) and (2).
* `AlgebraicGeometry.Stack.isVersalAt_iff_isVersal_completion`: **Stacks 0DQZ**, the equivalence
  of conditions (1) and (3).
* `AlgebraicGeometry.Stack.locallyOfFiniteType_and_quasiCompact_residueField_formalBase`: the
  sentence "Since `U → S` is locally of finite type, `Spec(k) → S` is of finite type (again as a
  composition). Thus the statement makes sense" — read at the complete local base, whose residue
  point is the structure morphism of the zeroth infinitesimal level.
* `AlgebraicGeometry.Stack.schemeMap_closedFibre_eq_residuePoint`: the closed fibre of the formal
  object is the restriction of `x` along the residue point of `u₀`, that is, the point `x₀` of the
  lemma's preamble.
* `AlgebraicGeometry.Stack.isVersalRingAt_completeLocalBase`: **Stacks 0DQZ**, the final
  statement — the completion `𝒪^∧_{U, u₀}` is a versal ring to `𝒳` at `x₀`.
* `AlgebraicGeometry.Stack.exists_algebra_of_formalBase_mem_range`: a complete local base whose
  closed point lies in an affine open `Spec Λ ⊆ S` is canonically a `Λ`-algebra over `S`.
* `AlgebraicGeometry.Stack.exists_isVersalRingAt_completion_of_isVersalAt`: the final statement
  with the presentation of the completion produced rather than supplied, for a `U` of finite type
  over `S`.

## What this file does not contain

Condition (4) of **Stacks 0DQZ** — smoothness of `x` after shrinking `U` — and its equivalence
with (1) are `AlgebraicGeometry.Stack.isVersalAt_iff_exists_isRelativelySmooth_restrict` in
`StacksFrontier/AlgebraicGeometry/Stacks/VersalChartSmoothBaseChange.lean`, which also carries the
`0DQZ` tag; the two directions are proved in that file and in
`StacksFrontier/AlgebraicGeometry/Stacks/VersalChartSmoothNeighbourhood.lean`.

Condition (2) is `Deformation.IsSmooth` of the map of predeformation categories
`Deformation.Artin.mapPredeformationCategory` (Stacks 07WJ) induced by the 2-Yoneda morphism
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor` of `x`, at the residue point of `u₀`.
The construction `Deformation.Artin.hatX` of Stacks 07XE is not used, because it asks for the
category to be fibred in groupoids over all schemes over `S`, which a stack over a bounded big
fppf site is not.

## Implementation notes

The completion `𝒪^∧_{U, u₀}` enters through a presentation, as everywhere in this part of the
tree: a complete local object `xR` restricting `x`, the formal object `ξ` the approximation
functor of **Stacks 07X6** attaches to it, and a ring isomorphism `e` of the completed local ring
onto `ξ.base.R` together with the morphism `g : Spec ξ.base.R ⟶ U` it presents. That is the data
`Deformation.Artin.isVersalAt_iff_isVersal_affineChart` consumes, and
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint` produces it from a finite type
point whose completion lies in the chosen big fppf site.

The deformation base is the ring `Λ` of an affine open `Spec Λ ⊆ S` through which the image of
`u₀` factors, which is what `AlgebraicGeometry.Stack.IsVersalRingAt` is stated over; Artin's
Axioms states **Stacks 0CXK** over the local ring `𝒪_{S,s}` instead, and
`Deformation.Artin.isVersalAt_iff_isVersal_affineChart` is the form of that comparison with the
base moved onto an affine open.

The point `x₀` of the conclusion is the closed fibre `ξ.level 0` of the formal object, and the
versal ring is `ξ.completeLocalBase Λ`, which is `ξ.base.R` — hence `𝒪^∧_{U, u₀}` through `e` —
with its canonical residue-field identification. That the residue point of that base is of finite
type over `S`, which `AlgebraicGeometry.Stack.IsVersalRingAt` records, is not an extra hypothesis:
a `Deformation.Artin.FormalBase` carries exactly those two conditions on
`Spec(R / 𝔪) ⟶ Spec R ⟶ S`, and the zeroth level of `ξ` lies over that morphism.

## References

* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 0DQU](https://stacks.math.columbia.edu/tag/0DQU)
* [Stacks Project, Tag 0DQV](https://stacks.math.columbia.edu/tag/0DQV)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

section ChartPoint

variable (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
  (U : Over D.S) [LocallyOfFiniteType U.hom]
  (x : D.𝒳.val.val.obj)
  (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
  (u₀ : U.left)
  (xR : Deformation.Artin.CompleteLocalObjects D.B D.S D.hS D.𝒳.val.val.p)
  (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
  (hξ : ξ = (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
    D.𝒳.val.property).obj xR)
  (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R)
  (g : Spec (.of ξ.base.R) ⟶ U.left)
  (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
    U.left.fromSpecStalk u₀)
  (hbase : ξ.base.toS = g ≫ U.hom)
  (r : xR.obj.1 ⟶ x)
  (hr : D.𝒳.val.val.p.IsCartesian (D.𝒳.val.val.p.map r) r)
  (hrbase : HEq ((eqToHom (Deformation.Artin.chosenBase_eq D.B D.S D.hS
      D.𝒳.val.val.p xR.obj).symm ≫ D.𝒳.val.val.p.map r).left.hom ≫
      eqToHom (congrArg Over.left hx)) g)
  (Λ : Type u) [CommRing Λ] [Algebra Λ ξ.base.R]
  (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
  (hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS)

include hΛ in
/-- **The residue point of the complete local base of a formal object is of finite type over
`S`.** This is the sentence of **Stacks 0DQZ** that makes the statement of the lemma meaningful:
the composition `Spec(k) → U → S` is of finite type because `U → S` is. Here it is read off the
complete local base itself, a `Deformation.Artin.FormalBase` carrying the two conditions on
`Spec(R / 𝔪) ⟶ Spec R ⟶ S` by definition; the zeroth infinitesimal level of `ξ` lies over that
morphism, which is what identifies it with `Spec k ⟶ Spec Λ ⟶ S`. -/
theorem locallyOfFiniteType_and_quasiCompact_residueField_formalBase :
    LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) ∧
      QuasiCompact
        (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) := by
  have h : (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) : Over D.S) =
      (Over.post D.B.inclusion).obj
        (Deformation.Artin.truncationOver D.B D.S D.hS ξ.base ξ.contains 0) :=
    (ξ.basePoint Λ iΛ hΛ).symm.trans (ξ.truncBase 0)
  have key : ∀ V : Over D.S,
      (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) : Over D.S) = V →
      LocallyOfFiniteType V.hom → QuasiCompact V.hom →
      LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) ∧
        QuasiCompact
          (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ξ.base.R))) ≫ iΛ) := by
    intro V hV hLFT hQC
    subst hV
    exact ⟨hLFT, hQC⟩
  exact key _ h ξ.base.residueLocallyFiniteType ξ.base.residueQuasiCompact

include hξ e g hg hbase r hr hrbase hiΛ in
/-- **Stacks 0DQZ, the equivalence of (1) and (3).** In the versal situation, let `x` be an
object of `𝒳` over a scheme `U` locally of finite type over `S`, let `u₀` be a point of `U`
whose image in `S` lies in the affine open `Spec Λ`, and let `ξ` be the formal object the
approximation functor attaches to a Cartesian restriction of `x` over a presentation of
`𝒪^∧_{U, u₀}`. Then `x` is versal at `u₀` exactly when `ξ` is versal.

This is Artin's Axioms, **Stacks 0CXK**, read in the versal situation of **Stacks 0DQU**, with
the deformation base on the ring of an affine open of `S` rather than on a local ring of `S`. -/
@[stacks 0DQZ "the equivalence of (1) and (3): x is versal at u₀ exactly when the formal object \
associated to the restriction of x to Spec 𝒪^∧_{U,u₀} is versal"]
theorem isVersalAt_iff_isVersal_completion
    (t : Spec (.of Λ)) (ht : iΛ t = Deformation.Artin.basePoint U u₀)
    [Algebra Λ (U.left.residueField u₀)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u₀))) ≫ iΛ =
      U.left.fromSpecResidueField u₀ ≫ U.hom) :
    Deformation.Artin.IsVersalAt U (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x hx ↔
      Deformation.Artin.FormalObject.IsVersal D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property
        ξ Λ iΛ hΛ := by
  have := hiΛ
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  exact Deformation.Artin.isVersalAt_iff_isVersal_affineChart D.B D.S D.hS
    D.𝒳.val.val.p D.𝒳.val.property U x hx u₀ xR ξ hξ e g hg hbase r hr hrbase Λ iΛ hΛ t ht
    hcompat

omit [LocallyOfFiniteType U.hom] in
include hξ hrbase in
/-- **The closed fibre of `ξ` is the point `x₀` induced by `u₀`.** The restriction of `x` along
the residue point `Spec κ(u₀) ⟶ Spec 𝒪^∧_{U, u₀} ⟶ U` is the zeroth infinitesimal level of the
formal object: the morphism of schemes underlying the canonical arrow `ξ.level 0 ⟶ x` is that
residue point. This is what makes the final statement of **Stacks 0DQZ** a statement about the
point `x₀ : Spec k ⟶ 𝒳` of the lemma's preamble. -/
theorem schemeMap_closedFibre_eq_residuePoint :
    Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion)
        (ξ.basePoint Λ iΛ hΛ) hx
        (Deformation.Artin.approximationLevelToOriginal D.B D.S D.hS D.𝒳.val.val.p
          D.𝒳.val.property xR ξ hξ r 0) =
      Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g := by
  set q := D.𝒳.val.val.p ⋙ Over.post D.B.inclusion
  set hx₀ := ξ.basePoint Λ iΛ hΛ
  set r₀ := Deformation.Artin.approximationLevelToOriginal D.B D.S D.hS D.𝒳.val.val.p
    D.𝒳.val.property xR ξ hξ r 0
  have restriction_base := Deformation.Artin.approximationLevelToOriginal_schemeMap
    D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property xR ξ hξ r U hx g hrbase 0
  have restriction_base_normalized :
      Deformation.Artin.schemeMap q
          (congrArg (Over.post D.B.inclusion).obj (ξ.level_eq 0)) hx r₀ =
        AlgebraicGeometry.adicThickeningι ξ.base.R (maximalIdeal ξ.base.R) 0 ≫ g := by
    simpa [Deformation.Artin.schemeMap, q, AlgebraicGeometry.BigFppfOver.toScheme,
      AlgebraicGeometry.BigFppfOver.forget, Over.post, Category.assoc] using restriction_base
  have hξ₀ := congrArg (Over.post D.B.inclusion).obj (ξ.level_eq 0)
  have ht : Spec (.of (ResidueField ξ.base.R)) = ξ.base.truncation 0 :=
    (congrArg Over.left hx₀).symm.trans (congrArg Over.left hξ₀)
  have he := Deformation.Artin.schemeMap_eqToHom_comp q hx₀ hξ₀ hx rfl ht r₀
  have hι := Deformation.Artin.quotientSpecMap_eqToHom ξ.base.R
    (pow_one (maximalIdeal ξ.base.R)) ht
  have hchain := he.trans
    ((congrArg (fun a => eqToHom ht ≫ a) restriction_base_normalized).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ g) hι)))
  simp only [eqToHom_refl, Category.id_comp] at hchain
  exact hchain

include hξ e g hg hbase r hr hrbase in
/-- **Stacks 0DQZ, the final statement.** In the versal situation, if `x` is versal at the
finite type point `u₀`, then the completion `𝒪^∧_{U, u₀}` — presented by the complete local base
of the formal object `ξ` attached to the restriction of `x` over it — is a versal ring to `𝒳` at
the closed fibre `x₀` of `ξ`.

The first conjunct identifies the point: the closed fibre `ξ.level 0`, over which the versal
ring is exhibited, is the restriction of `x` along the residue point of `u₀`, hence the point
`x₀` of the lemma's preamble. The second is the conclusion, and its proof is the one of the
source: the equivalence of (1) and (3) turns versality of `x` at `u₀` into versality of `ξ`,
and versality of a formal object is by definition versality of the formal object of the
predeformation category of its closed fibre that it determines, which is exactly what
**Stacks 0DQV** asks of a versal ring. -/
@[stacks 0DQZ "the final statement: the completion 𝒪^∧_{U,u₀} is a versal ring to 𝒳 at the \
point x₀ induced by u₀"]
theorem isVersalRingAt_completeLocalBase
    (t : Spec (.of Λ)) (ht : iΛ t = Deformation.Artin.basePoint U u₀)
    [Algebra Λ (U.left.residueField u₀)]
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ (U.left.residueField u₀))) ≫ iΛ =
      U.left.fromSpecResidueField u₀ ≫ U.hom)
    (hversal : Deformation.Artin.IsVersalAt U
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x hx) :
    Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion)
          (ξ.basePoint Λ iΛ hΛ) hx
          (Deformation.Artin.approximationLevelToOriginal D.B D.S D.hS D.𝒳.val.val.p
            D.𝒳.val.property xR ξ hξ r 0) =
        Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫ g ∧
      IsVersalRingAt D iΛ hiΛ (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
        (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
        (ξ.completeLocalBase Λ) :=
  ⟨schemeMap_closedFibre_eq_residuePoint D U x hx xR ξ hξ g r hrbase Λ iΛ hΛ,
    Deformation.Artin.FormalObject.exists_versalPredeformationFormalObject
      D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property ξ Λ iΛ hΛ
      ((isVersalAt_iff_isVersal_completion D U x hx u₀ xR ξ hξ e g hg hbase r hr hrbase
        Λ iΛ hiΛ hΛ t ht hcompat).mp hversal)⟩

end ChartPoint

/-! ### Condition (2): smoothness of `x̂` -/

section HatX

variable (D : AlgebraicGeometry.Stack.VersalSituation.{u, w}) (x : D.𝒳.val.val.obj)
  (c : D.𝒳.val.val.p.ChoiceOfPullbacks)
  (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
  {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S) [IsOpenImmersion iΛ]
  [Algebra Λ (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀)]
  (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ
      (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀))) ≫ iΛ =
    ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀ ≫
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom)

/-- The residue point `u₀ : Spec κ(u₀) ⟶ U` as an object of `(Sch/U)_{fppf}`, the slice of the
site at the scheme `U` underlying `x`. -/
abbrev chartResiduePoint : Over (D.𝒳.val.val.p.obj x) :=
  Deformation.Artin.residueFieldSlicePoint D.B D.S D.hS D.𝒳.val.val.p x u₀
    (Deformation.Artin.residueFieldPoint_site_contains D.B D.S D.hS D.𝒳.val.val.p x u₀)

omit [IsOpenImmersion iΛ] in
include hcompat in
/-- The residue point of `u₀` lies over `Spec κ(u₀) ⟶ Spec Λ ⟶ S`. -/
theorem chartResiduePoint_base :
    (Over.forget (D.𝒳.val.val.p.obj x) ⋙ Over.post D.B.inclusion).obj
        (chartResiduePoint D x u₀) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ
        (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀))) ≫ iΛ) :=
  Deformation.Artin.residueFieldSlicePoint_base D.B D.S D.hS D.𝒳.val.val.p x iΛ u₀ _ hcompat

/-- **Stacks 0DQZ, the equivalence of (1) and (2).** In the versal situation, let `x` be an
object of `𝒳` over a scheme `U`, let `u₀ ∈ U` with residue field `k = κ(u₀)`, and let
`Spec Λ ⊆ S` be an affine open through which `Spec k ⟶ S` factors. Then `x` is versal at `u₀`
exactly when the map of predeformation categories over `𝒞_Λ`
`x̂ : 𝓕_{U, k, u₀} ⟶ 𝓕_{𝒳, k, x₀}` induced by the 2-Yoneda morphism `x : (Sch/U)_{fppf} ⟶ 𝒳`
(for any choice `c` of pullbacks) at the residue point of `u₀` is smooth.

The source records this as "the definition of `x` being versal at `u₀`"; in this library
`Deformation.Artin.IsVersalAt` is the lifting property spelled out over the local ring of `S`,
so the equivalence is `Deformation.Artin.isVersalAt_iff_isSmooth_mapPredeformationCategory`.
Neither local finite type of `U` nor the finite type of `u₀` is needed. -/
@[stacks 0DQZ "the equivalence of (1) and (2): x is versal at u₀ exactly when \
x̂ : 𝓕_{U,k,u₀} ⟶ 𝓕_{𝒳,k,x₀} is smooth"]
theorem isVersalAt_iff_isSmooth_hatX (t : Spec (.of Λ))
    (ht : iΛ t = Deformation.Artin.basePoint
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x) u₀) :
    Deformation.Artin.IsVersalAt ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x)
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x rfl ↔
      Deformation.IsSmooth
        (Deformation.Artin.mapPredeformationCategory iΛ
          (Over.forget (D.𝒳.val.val.p.obj x) ⋙ Over.post D.B.inclusion)
          (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion)
          (c.sliceFunctor (⟨x, rfl⟩ : D.𝒳.val.val.p.Fiber (D.𝒳.val.val.p.obj x)))
          (Deformation.Artin.sliceFunctor_comp_post D.B D.S D.hS D.𝒳.val.val.p c x)
          (chartResiduePoint D x u₀) (chartResiduePoint_base D x u₀ iΛ hcompat)).toBasedFunctor :=
  Deformation.Artin.isVersalAt_iff_isSmooth_mapPredeformationCategory D.B D.S D.hS
    D.𝒳.val.val.p x iΛ D.𝒳.val.property c u₀ t ht hcompat _ _
    (Deformation.Artin.residueFieldSlicePoint_fieldPointMap D.B D.S D.hS D.𝒳.val.val.p x iΛ
      u₀ _ _)

end HatX

/-! ### Producing the presentation from an affine chart of the base -/

/-- **A complete local base whose closed point lies in an affine open of `S` is an algebra over
that open.** Every point of the spectrum of a local ring has the closed point in its closure, so
the structure morphism of a `Deformation.Artin.FormalBase` carries all of `Spec R` into any open
subset of `S` containing the image of the closed point; over an affine open it therefore factors
through `Spec Λ ⟶ S`, and the factorization is the spectrum of a ring map `Λ ⟶ R`. -/
theorem exists_algebra_of_formalBase_mem_range {S : Scheme.{u}}
    (A : Deformation.Artin.FormalBase S)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ S) (hiΛ : IsOpenImmersion iΛ)
    (hmem : A.toS (closedPoint A.R) ∈ Set.range iΛ.base) :
    ∃ _alg : Algebra Λ A.R,
      Spec.map (CommRingCat.ofHom (algebraMap Λ A.R)) ≫ iΛ = A.toS := by
  have := hiΛ
  have hpoint : A.toS (closedPoint A.R) ∈ iΛ.opensRange := hmem
  have hrange : Set.range A.toS.base ⊆ Set.range iΛ.base := by
    have h := Scheme.preimage_eq_top_of_closedPoint_mem A.toS hpoint
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ A.toS ⁻¹ᵁ iΛ.opensRange := by rw [h]; trivial
    exact ha
  refine ⟨((Spec.homEquiv (IsOpenImmersion.lift iΛ A.toS hrange)).hom).toAlgebra, ?_⟩
  have hg : Spec.map (CommRingCat.ofHom
      ((Spec.homEquiv (IsOpenImmersion.lift iΛ A.toS hrange)).hom)) =
      IsOpenImmersion.lift iΛ A.toS hrange :=
    Spec.homEquiv.symm_apply_apply _
  change Spec.map (CommRingCat.ofHom
      ((Spec.homEquiv (IsOpenImmersion.lift iΛ A.toS hrange)).hom)) ≫ iΛ = A.toS
  rw [hg]
  exact IsOpenImmersion.lift_fac iΛ A.toS hrange

/-- **Stacks 0DQZ, the final statement with the presentation produced.** In the versal situation,
let `x` be an object of `𝒳` over a scheme `U` of finite type over `S`, let `u₀` be a finite type
point of `U` whose completed local ring lies in the chosen big fppf site, and let `Spec Λ ⊆ S` be
an affine open containing the image of `u₀`. If `x` is versal at `u₀` then there are a formal
object `ξ` of `𝒳`, a presentation `e` of `𝒪^∧_{U, u₀}` by its complete local base and a
`Λ`-algebra structure on that base over `S` for which the closed fibre of `ξ` is the restriction
of `x` along the residue point of `u₀` — that is, the point `x₀` of the lemma's preamble — and
`𝒪^∧_{U, u₀}` is a versal ring to `𝒳` at `x₀`.

Quasi-compactness of `U ⟶ S` is assumed because it is what
`Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint` needs in order to restrict
`x` over the completion at all; the source assumes only local finite type, so this declaration is
the finite-type case of the final statement and carries no tag. The general statement, with the
presentation supplied rather than produced, is
`AlgebraicGeometry.Stack.isVersalRingAt_completeLocalBase`. -/
theorem exists_isVersalRingAt_completion_of_isVersalAt
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    (U : Over D.S) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : D.𝒳.val.val.obj)
    (hx : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x = U)
    (u₀ : U.left) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hC : D.B.Contains
      (Spec (.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : IsOpenImmersion iΛ)
    (H : Set.range (U.left.fromSpecResidueField u₀ ≫ U.hom).base ⊆ Set.range iΛ.base)
    (hversal : Deformation.Artin.IsVersalAt U
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) u₀ x hx) :
    ∃ (ξ : Deformation.Artin.FormalObject D.B D.S D.hS D.𝒳.val.val.p)
      (e : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R)
      (alg : Algebra Λ ξ.base.R),
      letI := alg
      ∃ hΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ ξ.base.R)) ≫ iΛ = ξ.base.toS,
        (∃ r₀ : ξ.level 0 ⟶ x,
          Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion)
              (ξ.basePoint Λ iΛ hΛ) hx r₀ =
            Spec.map (CommRingCat.ofHom (residue ξ.base.R)) ≫
              Spec.map (CommRingCat.ofHom e.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
                (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
              U.left.fromSpecStalk u₀) ∧
        IsVersalRingAt D iΛ hiΛ (ξ.level 0) (ξ.basePoint Λ iΛ hΛ)
          (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ξ Λ iΛ hΛ)
          (ξ.completeLocalBase Λ) := by
  have := hiΛ
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  obtain ⟨xR, r, e₀, hr, hrbase₀, hbase₀⟩ :=
    Deformation.Artin.exists_completeLocalObject_of_isFiniteTypePoint D.B D.S D.hS
      D.𝒳.val.val.p D.𝒳.val.property U x hx u₀ hu₀ hC
  set ξ := (Deformation.Artin.approximationFunctor D.B D.S D.hS D.𝒳.val.val.p
    D.𝒳.val.property).obj xR
  obtain ⟨e, hrbase, hbase, hs⟩ := Deformation.Artin.exists_approximationBase_presentation
    D.B D.S D.hS D.𝒳.val.val.p D.𝒳.val.property U x hx u₀ xR ξ rfl r e₀ hrbase₀ hbase₀
  have hmem : Deformation.Artin.basePoint U u₀ ∈ Set.range iΛ.base :=
    H ⟨IsLocalRing.closedPoint (U.left.residueField u₀), rfl⟩
  obtain ⟨alg, hΛ⟩ := exists_algebra_of_formalBase_mem_range ξ.base iΛ hiΛ (hs ▸ hmem)
  obtain ⟨t, ht⟩ := hmem
  let _ := alg
  let _ := Deformation.Artin.chartResidueAlgebra iΛ U u₀ H
  refine ⟨ξ, e, alg, hΛ, ?_⟩
  obtain ⟨hpoint, hring⟩ := isVersalRingAt_completeLocalBase D U x hx u₀ xR ξ rfl e
    (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
      U.left.fromSpecStalk u₀) rfl hbase r hr hrbase Λ iΛ hiΛ hΛ t ht
    (Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U u₀ H) hversal
  exact ⟨⟨_, hpoint⟩, hring⟩

end AlgebraicGeometry.Stack

end
