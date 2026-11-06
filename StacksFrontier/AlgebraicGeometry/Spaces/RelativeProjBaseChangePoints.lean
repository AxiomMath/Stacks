module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPointTwists

/-!
# Base change of the relative Proj of an algebraic space

Let `S` be a scheme, let `g : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `𝒜` be
a quasi-coherent graded `𝒪_X`-algebra.  Stacks 085C asserts two things:

1. there is a canonical isomorphism `r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)`;
2. there is a corresponding isomorphism
   `θ : r^* pr₂^*(⨁_{d ∈ ℤ} 𝒪_{Proj_X(𝒜)}(d)) ⟶ ⨁_{d ∈ ℤ} 𝒪_{Proj_{X'}(g^*𝒜)}(d)` of `ℤ`-graded
   `𝒪_{Proj_{X'}(g^*𝒜)}`-algebras.

**How the relative Proj enters.**  `Proj_X(𝒜)` for an algebraic space `X` is *not* constructed
from `𝒜` in this library, because Stacks 084B — the representability of the functor of
quadruples of Stacks 084A, with the identifications `Proj_Z(h^*𝒜) = Z ×_X Proj_X(𝒜)` compatible
with further base change — is not proved.  As for Stacks 084D, 085D and 085F, the relative Proj
is therefore presented through its base changes to the scheme points of the base, by
`AlgebraicGeometry.Space.RelativeProjPoints`: at every object `T` of the site and every
`T`-point `f` of `X` a quasi-coherent graded algebra `f^*𝒜` on the scheme of `T` and a cartesian
square identifying `T ×_X Proj_X(𝒜)` with the scheme-level relative Proj `Proj_T(f^*𝒜)` of
Stacks 01NQ.  `AlgebraicGeometry.Space.RelativeProjBaseChangePoints d d' g` says that the
presentation `d'` of `π' : P' ⟶ X'` is the base change along `g` of the presentation `d` of
`π : P ⟶ X`: its algebra at `f` is the algebra of `d` at `f ∘ g`, and the comparison of the two
presentations is compatible with restriction in the test object (the analogue, for this
statement, of the two compatibility fields of `AlgebraicGeometry.Space.RelativeProjHomPoints`
used for Stacks 085F).  `AlgebraicGeometry.Space.RelativeProjBaseChangePoints.comap` shows the
restricted presentation of `X' ×_X P` satisfies it, so nothing here is vacuous.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjBaseChangePoints.baseChangeIso` is **Stacks 085C's `r`, as
  an isomorphism of algebraic spaces** `P' ≅ X' ×_X P`: an isomorphism of presheaves on the big
  fppf site of `S`, that is, natural in the test object.
* `AlgebraicGeometry.Space.RelativeProjPoints.fibreBaseChangeTheta` is **Stacks 085C's `θ` over a
  scheme point `f : T ⟶ X'`**: an isomorphism of `ℤ`-graded algebras from the inverse image, along
  the base change `r_T` of `r`, of the twists `⨁_d 𝒪(d)` of Stacks 084D on `T ×_X Proj_X(𝒜)`, to
  the twists on `T ×_{X'} Proj_{X'}(g^*𝒜)`.
* `AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv` is the comparison of the two
  presentations over one point of `X'`, from which `r` is assembled
  (`…basePointEquiv`, `…basePointEquivPullback`), and `…fibreBaseChangeIso` is the isomorphism of
  schemes it induces between the two base changes.
* `AlgebraicGeometry.Space.RelativeProjPoints.comap` restricts a presentation of `Proj_X(𝒜)`
  along `g` to a presentation of `Proj_{X'}(g^*𝒜)` on the fibre product `X' ×_X Proj_X(𝒜)`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjBaseChangePoints.baseChangeIso_hom_fst`: `r` is an
  isomorphism over `X'`.
* `AlgebraicGeometry.Space.RelativeProjBaseChangePoints.baseChangeIso_hom_snd`: over every scheme
  point of `X'` the base change of `r` is the identification of the two scheme-level relative
  Projs of one graded algebra given by Stacks 084B, and `…baseChangeIso_hom_unique`: that
  description determines `r`.
* `AlgebraicGeometry.Space.RelativeProjBaseChangePoints.toScheme_map_pointEquivOver_baseChangeIso`:
  the morphism `T ×_{X'} P' ⟶ T ×_X P` that `r` induces is `…fibreBaseChangeIso`, so `θ` above is
  taken across `r`.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointPsiHom_heq`: `θ` is compatible with the
  canonical homomorphism `ψ` of Stacks 084D at every scheme point; `…pointTwistAlgebra_heq` and
  `…pointTwistTheta_heq` say the same of the twist algebras and of the identifications `θ` of
  Stacks 01O3 with every further base change.
* `AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv_natural`: the comparison over
  a fixed point of `X'` is natural in the test object.

## Implementation notes

**Where the comparison comes from.**  `AlgebraicGeometry.Space.RelativeProjPoints` presents the
points of `P` over a point of the base as sections of a scheme-level relative Proj
(`AlgebraicGeometry.Space.RelativeProjPoints.pointEquivProjOver`), naturally in the test object
(`…pointEquivProjOver_natural`).  The two presentations send the two sides to sections of one
and the same scheme-level relative Proj, so the comparison is the composite of one such
bijection with the inverse of the other, and its naturality is the naturality of each.  The
equality of graded algebras enters only as `projOverCongr`, the transport of the sections along
it.  Assembling the comparisons over the several points of `X'` into one morphism of presheaves
is where the compatibility field of `AlgebraicGeometry.Space.RelativeProjBaseChangePoints` is
used: it identifies the comparison computed at a point along `k : T₁ ⟶ T` with the one computed
at the restricted point, which `AlgebraicGeometry.Space.RelativeProjPoints` alone does not relate,
its data over distinct points of the base being independent.

**Why `θ` costs so little here.**  Stacks 084D's twists at a scheme point are
`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistAlgebra`, which is Stacks 01NR's
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of the restricted algebra
and so a function of that algebra alone.  Equal restricted algebras therefore have the same
twists and the same `ψ`, and all that is left is to move them along the isomorphism of the
presented schemes the equality produces; that is `thetaOfAlgebraEq`, two applications of the
pseudofunctoriality of the inverse image of graded algebras.

## Not done here

* **`θ` as a map of sheaves on the algebraic space `Proj_{X'}(g^*𝒜)`.**  The two sides of the
  source's `θ` are sheaves of graded algebras on the algebraic spaces `Proj_X(𝒜)` and
  `Proj_{X'}(g^*𝒜)`, the twists of Stacks 084D.  In this library those twists exist at every
  scheme point of the base and not on the space: on the present substrate the space-level twists
  cannot be constructed at all (a real conic presented over `Spec ℝ` and `Spec ℂ` with unrelated
  algebras admits no module restricting to both; see the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjPointTwists.lean`), and what pins
  `Proj_X(𝒜)` to `𝒜` is Stacks 084B.  So `θ` is delivered over every scheme point of `X'`, across
  the base change of `r` there, compatibly with `ψ` and with further base change.
* **`r` for the functor of quadruples itself.**  The functor `F` of Stacks 084A is formalized as
  its values `AlgebraicGeometry.Space.GradedAlgebraPoints.F` on test objects, not as a functor
  (the restriction of `𝒜` along a point and along its composite with a morphism of test objects
  are not compared there), so the bijections
  `AlgebraicGeometry.Space.GradedAlgebraPoints.F.baseChangeEquiv` of the source's proof are not
  assembled into a natural transformation; `r` is assembled on the presentations instead, which is
  what an isomorphism of the representing algebraic spaces is.

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.GluedTwistAlgebra
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (pbAlgS)
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

namespace AlgebraicGeometry.Space

universe u

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_RelativeProjBaseChangePoints
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The pullback of a cospan of presheaves on the big fppf site, found at once. -/
local instance (priority := high) hasPullback_presheaf_RelativeProjBaseChangePoints
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Transport along an equality of the graded algebra -/

/-- The sections of the scheme-level relative Proj of Stacks 01NQ over a fixed morphism of the
base, transported along an equality of the graded algebra. -/
def projOverCongr {Z : Scheme.{u}} :
    ∀ {A A' : SheafGradedAlgebra Z}, A = A' → ∀ {W : Scheme.{u}} (m : W ⟶ Z),
      ({x : W ⟶ (relativeProj A).scheme // x ≫ (relativeProj A).toBase = m} ≃
        {x : W ⟶ (relativeProj A').scheme // x ≫ (relativeProj A').toBase = m})
  | _, _, rfl, _, _ => Equiv.refl _

/-- The transport commutes with precomposition by a morphism of the source. -/
theorem projOverCongr_comp {Z W V : Scheme.{u}} {A A' : SheafGradedAlgebra Z}
    (h : A = A') (k : V ⟶ W) {m : W ⟶ Z} {m' : V ⟶ Z}
    (y : {x : W ⟶ (relativeProj A).scheme // x ≫ (relativeProj A).toBase = m})
    (hy : (k ≫ y.1) ≫ (relativeProj A).toBase = m') :
    (projOverCongr h m' ⟨k ≫ y.1, hy⟩).1 = k ≫ (projOverCongr h m y).1 := by
  subst h
  rfl

/-- Under an equality of the graded algebras, the transport of the schemes carries the structure
morphism of one relative Proj to that of the other. -/
theorem eqToHom_comp_relativeProj_toBase {Z : Scheme.{u}} {A A' : SheafGradedAlgebra Z}
    (h : A = A') :
    eqToHom (congrArg (fun a : SheafGradedAlgebra Z => (relativeProj a).scheme) h) ≫
        (relativeProj A').toBase = (relativeProj A).toBase := by
  subst h
  simp

/-- **The comparison of two graded algebras of the relative Proj across an equality of the
graded algebra on the base.**

For any assignment `W` of a sheaf of `ℤ`-graded algebras to the relative Proj of a graded
algebra on `Z`, and for two schemes presented as the relative Projs of equal graded algebras,
the inverse image of `W` along the resulting isomorphism of the presented schemes is `W`.

This is the shape in which the `θ` of Stacks 085C is obtained below: the two sides are the twists
of the two relative Projs, and `W` is the twist algebra of Stacks 01NR. -/
def thetaOfAlgebraEq {Z Y Y' : Scheme.{u}} {A A' : SheafGradedAlgebra Z} (h : A = A')
    (W : ∀ a : SheafGradedAlgebra Z, SchemeGradedAlgebra (relativeProj a).scheme)
    (iso' : Y ≅ (relativeProj A).scheme) (iso : Y' ≅ (relativeProj A').scheme) :
    pbAlgS (iso'.hom ≫ eqToHom (congrArg (fun a : SheafGradedAlgebra Z =>
          (relativeProj a).scheme) h) ≫ iso.inv) (pbAlgS iso.hom (W A')) ≅
      pbAlgS iso'.hom (W A) := by
  subst h
  exact (pullbackGradedAlgebraCompIso (W A) _ iso.hom).trans
    (pullbackGradedAlgebraCongrIso (W A) (by simp))

/-! ### The comparison over a point of the base -/

variable {X X' P P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X} {π' : P' ⟶ X'}
    (d : RelativeProjPoints B S hS π) (d' : RelativeProjPoints B S hS π') (g : X' ⟶ X)
    (halg : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'),
      d'.algebra T f = d.algebra T (f ≫ g))

/-- **The comparison underlying Stacks 085C's `r`, over a point of `X'`.**

Let `g : X' ⟶ X` be a morphism of algebraic spaces over `S`, let `π : P ⟶ X` be presented as
`Proj_X(𝒜)` and `π' : P' ⟶ X'` as `Proj_{X'}(g^*𝒜)` — that is, by a presentation whose graded
algebra at a `T`-point `f` of `X'` is the graded algebra of the first at `f ∘ g`.  Then for
every `T`-point `f` of `X'` and every `r : T' ⟶ T` the `T'`-points of `P` over `f ∘ r` are the
`T'`-points of `P'` over `g ∘ f ∘ r`.

Both sides are sections of one and the same scheme-level relative Proj of Stacks 01NQ, by
`AlgebraicGeometry.Space.RelativeProjPoints.pointEquivProjOver` for the two presentations. -/
def baseChangePointEquiv (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) :
    {u : yoneda.obj T' ⟶ P' // u ≫ π' = yoneda.map r ≫ f} ≃
      {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ (f ≫ g)} :=
  (d'.pointEquivProjOver T f r).trans
    ((projOverCongr (halg T f) _).trans (d.pointEquivProjOver T (f ≫ g) r).symm)

/-- The point of `P` attached to a point of `P'`, read through the two presentations. -/
theorem pointEquivProjOver_baseChangePointEquiv (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X') {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (u : {u : yoneda.obj T' ⟶ P' // u ≫ π' = yoneda.map r ≫ f}) :
    d.pointEquivProjOver T (f ≫ g) r (baseChangePointEquiv d d' g halg T f r u) =
      projOverCongr (halg T f) _ (d'.pointEquivProjOver T f r u) :=
  (d.pointEquivProjOver T (f ≫ g) r).apply_symm_apply _

/-- **The comparison over a point of `X'` is natural in the test object.**

Restricting a `T'`-point of `P'` along `r' : T'' ⟶ T'` restricts the `T'`-point of `P` it
corresponds to.  Both sides are computed by the two presentations at the one point `f` of `X'`,
so this is `AlgebraicGeometry.Space.RelativeProjPoints.pointEquivProjOver_natural` for each of
them, together with the commutation `projOverCongr_comp` of the transport with precomposition. -/
theorem baseChangePointEquiv_natural (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T')
    (u : {u : yoneda.obj T' ⟶ P' // u ≫ π' = yoneda.map r ≫ f}) :
    (baseChangePointEquiv d d' g halg T f (r' ≫ r) ⟨yoneda.map r' ≫ u.1, by
        rw [Category.assoc, u.2, ← Category.assoc, ← CategoryTheory.Functor.map_comp]⟩).1
      = yoneda.map r' ≫ (baseChangePointEquiv d d' g halg T f r u).1 := by
  set v := baseChangePointEquiv d d' g halg T f r u with hv
  have hgoal : (baseChangePointEquiv d d' g halg T f (r' ≫ r) ⟨yoneda.map r' ≫ u.1, by
        rw [Category.assoc, u.2, ← Category.assoc, ← CategoryTheory.Functor.map_comp]⟩)
      = (⟨yoneda.map r' ≫ v.1, by
        rw [Category.assoc, v.2, ← Category.assoc, ← CategoryTheory.Functor.map_comp]⟩ :
          {u : yoneda.obj T'' ⟶ P // u ≫ π = yoneda.map (r' ≫ r) ≫ (f ≫ g)}) := by
    refine (d.pointEquivProjOver T (f ≫ g) (r' ≫ r)).injective (Subtype.ext ?_)
    rw [pointEquivProjOver_baseChangePointEquiv]
    rw [d.pointEquivProjOver_natural T (f ≫ g) r r' v]
    rw [show d'.pointEquivProjOver T f (r' ≫ r) ⟨yoneda.map r' ≫ u.1, by
            rw [Category.assoc, u.2, ← Category.assoc, ← CategoryTheory.Functor.map_comp]⟩ =
          ⟨(BigFppfOver.toScheme B S hS).map r' ≫ (d'.pointEquivProjOver T f r u).1, by
            rw [Category.assoc, (d'.pointEquivProjOver T f r u).2,
              ← CategoryTheory.Functor.map_comp]⟩ from
        Subtype.ext (d'.pointEquivProjOver_natural T f r r' u)]
    rw [projOverCongr_comp, hv, pointEquivProjOver_baseChangePointEquiv]
  exact congrArg Subtype.val hgoal

/-! ### The comparison on all points of a test object -/

/-- **The comparison on the points of a test object.**  The `T`-points of
`P' = Proj_{X'}(g^*𝒜)` are the `T`-points of `X' ×_X P`: a `T`-point `f` of `X'` together with a
`T`-point of `P = Proj_X(𝒜)` lying over `f ∘ g`.

The decomposition of a point of `P'` by its image in `X'` matches the decomposition of a pair by
its first component, and over each point of `X'` the two fibres agree by
`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv`. -/
def basePointEquiv (T : BigFppfOver B S hS) :
    (yoneda.obj T ⟶ P') ≃
      Σ f : yoneda.obj T ⟶ X', {u : yoneda.obj T ⟶ P // u ≫ π = f ≫ g} :=
  (Equiv.sigmaFiberEquiv (fun u : yoneda.obj T ⟶ P' => u ≫ π')).symm.trans
    (Equiv.sigmaCongrRight fun f =>
      ((Equiv.subtypeEquivRight (fun u => by
          rw [CategoryTheory.Functor.map_id, Category.id_comp])).trans
        (baseChangePointEquiv d d' g halg T f (𝟙 T))).trans
        (Equiv.subtypeEquivRight (fun u => by
          rw [CategoryTheory.Functor.map_id, Category.id_comp])))

/-- **The points of the fibre product over a point of `X'`.** A `T`-point of `X' ×_X P` lying
over a `T`-point `f` of `X'` is a `T`-point of `P` lying over the image `f ∘ g` of `f` in `X`;
this is the universal property of the fibre product. -/
def pullbackFibrePointEquiv (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    {u : yoneda.obj T ⟶ pullback g π // u ≫ pullback.fst g π = f} ≃
      {v : yoneda.obj T ⟶ P // v ≫ π = f ≫ g} where
  toFun u := ⟨u.1 ≫ pullback.snd g π, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, u.2]⟩
  invFun v := ⟨pullback.lift f v.1 v.2.symm, pullback.lift_fst _ _ _⟩
  left_inv u := Subtype.ext (pullback.hom_ext
    (by rw [pullback.lift_fst, u.2]) (by rw [pullback.lift_snd]))
  right_inv v := Subtype.ext (pullback.lift_snd _ _ _)

/-- **The points of the fibre product at a test object.** A `T`-point of `X' ×_X P` is a
`T`-point of `X'` together with a `T`-point of `P` lying over its image in `X`. -/
def pullbackPointEquiv (T : BigFppfOver B S hS) :
    (yoneda.obj T ⟶ pullback g π) ≃
      Σ f : yoneda.obj T ⟶ X', {u : yoneda.obj T ⟶ P // u ≫ π = f ≫ g} :=
  (Equiv.sigmaFiberEquiv
      (fun u : yoneda.obj T ⟶ pullback g π => u ≫ pullback.fst g π)).symm.trans
    (Equiv.sigmaCongrRight fun f => pullbackFibrePointEquiv g T f)

/-- **The comparison on all points of a test object.** At every object `T` of the site the
`T`-points of `P' = Proj_{X'}(g^*𝒜)` are the `T`-points of `X' ×_X Proj_X(𝒜)`.

This is `AlgebraicGeometry.Space.RelativeProjPoints.basePointEquiv` read through the universal
property of the fibre product.  Under the compatibility of
`AlgebraicGeometry.Space.RelativeProjBaseChangePoints` these bijections are the components of
the isomorphism of algebraic spaces
`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.baseChangeIso`. -/
def basePointEquivPullback (T : BigFppfOver B S hS) :
    (yoneda.obj T ⟶ P') ≃ (yoneda.obj T ⟶ pullback g π) :=
  (basePointEquiv d d' g halg T).trans (pullbackPointEquiv g T).symm

/-! ### `r` and `θ` after base change to a scheme point of `X'` -/

/-- **The isomorphism `r`, after base change to a scheme point of `X'`.**

Over a `T`-point `f` of `X'` the base change `T ×_{X'} Proj_{X'}(g^*𝒜)` and the base change
`T ×_X Proj_X(𝒜)` along the image point `f ∘ g` are both presented as the scheme-level relative
Proj of Stacks 01NQ of one and the same graded algebra on the scheme of `T`, so they are
isomorphic as schemes.  This is `r` base changed to the scheme point `f`
(`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.toScheme_map_pointEquivOver_baseChangeIso`).
-/
def fibreBaseChangeIso (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (BigFppfOver.toScheme B S hS).obj (d'.fibre T f) ≅
      (BigFppfOver.toScheme B S hS).obj (d.fibre T (f ≫ g)) :=
  d'.fibreIso T f ≪≫ eqToIso (congrArg (fun a : SheafGradedAlgebra
      ((BigFppfOver.toScheme B S hS).obj T) => (relativeProj a).scheme) (halg T f)) ≪≫
    (d.fibreIso T (f ≫ g)).symm

/-- The base change of `r` to a scheme point, as a composite of the two presentations with the
transport along the equality of the restricted algebras. -/
theorem fibreBaseChangeIso_hom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (fibreBaseChangeIso d d' g halg T f).hom =
      (d'.fibreIso T f).hom ≫ eqToHom (congrArg (fun a : SheafGradedAlgebra
          ((BigFppfOver.toScheme B S hS).obj T) => (relativeProj a).scheme) (halg T f)) ≫
        (d.fibreIso T (f ≫ g)).inv :=
  rfl

/-- **`r` after base change to a scheme point lies over the test object.** -/
theorem fibreBaseChangeIso_hom_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (fibreBaseChangeIso d d' g halg T f).hom ≫
        (BigFppfOver.toScheme B S hS).map (d.fibreHom T (f ≫ g)) =
      (BigFppfOver.toScheme B S hS).map (d'.fibreHom T f) := by
  rw [fibreBaseChangeIso_hom, d'.fibreHom_comp T f, d.fibreHom_comp T (f ≫ g),
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    eqToHom_comp_relativeProj_toBase (halg T f)]

/-- **Stacks 085C, the isomorphism `θ`, over a scheme point of `X'`.**

The inverse image, along the base change `r_T` of
`AlgebraicGeometry.Space.RelativeProjPoints.fibreBaseChangeIso`, of the sheaf of `ℤ`-graded
algebras `⨁_{d ∈ ℤ} 𝒪(d)` on `T ×_X Proj_X(𝒜)` is the sheaf of `ℤ`-graded algebras
`⨁_{d ∈ ℤ} 𝒪(d)` on `T ×_{X'} Proj_{X'}(g^*𝒜)`.

The two twist algebras are Stacks 084D's, in the form
`AlgebraicGeometry.Space.RelativeProjPoints.fibreTwistAlgebra`, so they are the twists of
Stacks 01NR of the two restricted algebras; those restricted algebras are equal, and `r` is the
isomorphism of the presented schemes that equality produces, so `θ` is
`AlgebraicGeometry.Space.RelativeProjPoints.thetaOfAlgebraEq`.  That `fibreBaseChangeIso` is the
base change of the isomorphism of algebraic spaces `r` is
`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.toScheme_map_pointEquivOver_baseChangeIso`;
the compatibility of `θ` with `ψ` is `AlgebraicGeometry.Space.RelativeProjPoints.pointPsiHom_heq`.
The source's `θ` on the algebraic space `Proj_{X'}(g^*𝒜)` itself needs the twists of Stacks 084D
as sheaves on the space, which need Stacks 084B; see the module docstring. -/
@[stacks 085C "the isomorphism theta over a scheme point f : T -> X' of X': an isomorphism of \
Z-graded algebras from the inverse image, along the base change of r to T \
(toScheme_map_pointEquivOver_baseChangeIso), of (+)_{d in Z} O(d) on T x_X Proj_X(A) to \
(+)_{d in Z} O(d) on T x_{X'} Proj_{X'}(g^*A), both being Tag 084D's twists of Tag 01NR; theta as \
a map of sheaves on the algebraic space Proj_{X'}(g^*A) needs those twists on the space, i.e. 084B"]
def fibreBaseChangeTheta (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    pbAlgS (fibreBaseChangeIso d d' g halg T f).hom (d.fibreTwistAlgebra T (f ≫ g)) ≅
      d'.fibreTwistAlgebra T f :=
  thetaOfAlgebraEq (halg T f) (fun a => (twistDataOfGradedAlgebra a).algebra)
    (d'.fibreIso T f) (d.fibreIso T (f ≫ g))

/-! ### The restricted presentation -/

/-- **The restriction of a presentation of `Proj_X(𝒜)` along `g : X' ⟶ X`.**

For every presentation of `π : P ⟶ X` as `Proj_X(𝒜)`, the first projection
`X' ×_X P ⟶ X'` carries a presentation of `Proj_{X'}(g^*𝒜)`: its graded algebra at a `T`-point
`f` of `X'` is the graded algebra of the given presentation at `f ∘ g`, its fibre over that
point is the same object of the site, and the cartesian square is the given one pasted with the
fibre product square.

This inhabits the hypotheses of
`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv`, so nothing stated with them
is vacuous. -/
def comap : RelativeProjPoints B S hS (pullback.fst g π) where
  algebra T f := d.algebra T (f ≫ g)
  fibre T f := d.fibre T (f ≫ g)
  fibreIso T f := d.fibreIso T (f ≫ g)
  fibreHom T f := d.fibreHom T (f ≫ g)
  fibreHom_comp T f := d.fibreHom_comp T (f ≫ g)
  fibreToSpace T f := (IsPullback.of_hasPullback g π).flip.lift
    (d.fibreToSpace T (f ≫ g)) (yoneda.map (d.fibreHom T (f ≫ g)) ≫ f)
    (by rw [Category.assoc]; exact (d.isPullback T (f ≫ g)).w)
  isPullback T f :=
    IsPullback.of_right' (d.isPullback T (f ≫ g)) (IsPullback.of_hasPullback g π).flip

/-- The restricted presentation has the restricted graded algebra at every point of `X'`. -/
@[simp] theorem comap_algebra (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (d.comap g).algebra T f = d.algebra T (f ≫ g) :=
  rfl

/-- The restricted presentation has the same fibre over a point of `X'` as the given one has
over its image in `X`. -/
@[simp] theorem comap_fibre (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (d.comap g).fibre T f = d.fibre T (f ≫ g) :=
  rfl

/-- **The hypotheses of the comparison are inhabited.** The restricted presentation of
`AlgebraicGeometry.Space.RelativeProjPoints.comap` satisfies the equality of graded algebras
that `AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv` asks for, by
`AlgebraicGeometry.Space.RelativeProjPoints.comap_algebra`, so the comparison is available for
it; this declaration exhibits it.

The presentation it is available for is of course the fibre product itself, so this witness does
not make the comparison interesting — it makes it non-vacuous. -/
def comapBaseChangePointEquiv (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) :
    {u : yoneda.obj T' ⟶ pullback g π // u ≫ pullback.fst g π = yoneda.map r ≫ f} ≃
      {u : yoneda.obj T' ⟶ P // u ≫ π = yoneda.map r ≫ (f ≫ g)} :=
  baseChangePointEquiv d (d.comap g) g (fun _ _ => rfl) T f r

/-! ### Auxiliary identities for the comparison -/

/-- The transport of a section along an equality of the graded algebra is composition with the
resulting identification of the two relative Projs. -/
theorem projOverCongr_val {Z W : Scheme.{u}} {A A' : SheafGradedAlgebra Z} (h : A = A')
    (m : W ⟶ Z)
    (y : {x : W ⟶ (relativeProj A).scheme // x ≫ (relativeProj A).toBase = m}) :
    (projOverCongr h m y).1 =
      y.1 ≫ eqToHom (congrArg (fun a : SheafGradedAlgebra Z => (relativeProj a).scheme) h) := by
  subst h
  simp [projOverCongr]

/-- For the restricted presentation, the section over `f ∘ g` attached to a point `u` of
`X' ×_X P` over `f` is the one attached to its second component `u ∘ pr₂`. -/
theorem comap_pointEquivOver (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (u : {u : yoneda.obj T' ⟶ pullback g π // u ≫ pullback.fst g π = yoneda.map r ≫ f}) :
    ((d.comap g).pointEquivOver T f r u).1 =
      (d.pointEquivOver T (f ≫ g) r ⟨u.1 ≫ pullback.snd g π, by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, u.2, Category.assoc]⟩).1 := by
  refine congrArg Subtype.val ((Equiv.symm_apply_eq (d.pointEquivOver T (f ≫ g) r)).1 ?_)
  apply Subtype.ext
  show yoneda.map ((d.comap g).pointEquivOver T f r u).1 ≫ d.fibreToSpace T (f ≫ g) =
    u.1 ≫ pullback.snd g π
  rw [← (d.comap g).map_pointEquivOver T f r u, Category.assoc]
  exact congrArg (yoneda.map ((d.comap g).pointEquivOver T f r u).1 ≫ ·)
    ((IsPullback.of_hasPullback g π).flip.lift_fst _ _ _).symm

/-- **For the restricted presentation the comparison is the second projection.** The point of
`P` that `AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv` attaches to a point `u`
of `X' ×_X P`, for the presentation `AlgebraicGeometry.Space.RelativeProjPoints.comap`, is
`u ∘ pr₂`, over every point of `X'` and along every morphism of test objects. -/
theorem comap_baseChangePointEquiv (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (u : {u : yoneda.obj T' ⟶ pullback g π // u ≫ pullback.fst g π = yoneda.map r ≫ f}) :
    (baseChangePointEquiv d (d.comap g) g (fun _ _ => rfl) T f r u).1 =
      u.1 ≫ pullback.snd g π := by
  have key : (d.comap g).pointEquivProjOver T f r u =
      d.pointEquivProjOver T (f ≫ g) r ⟨u.1 ≫ pullback.snd g π, by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, u.2, Category.assoc]⟩ := by
    apply Subtype.ext
    rw [pointEquivProjOver_apply, pointEquivProjOver_apply]
    exact congrArg (fun s => (BigFppfOver.toScheme B S hS).map s ≫ (d.fibreIso T (f ≫ g)).hom)
      (comap_pointEquivOver d g T f r u)
  show ((d.pointEquivProjOver T (f ≫ g) r).symm
    (projOverCongr rfl _ ((d.comap g).pointEquivProjOver T f r u))).1 = _
  rw [key]
  exact congrArg Subtype.val ((d.pointEquivProjOver T (f ≫ g) r).symm_apply_apply _)

/-- The comparison over a point of `X'` depends on that point and on the morphism of test objects
only through their values. -/
theorem baseChangePointEquiv_congr (T : BigFppfOver B S hS) {f f₁ : yoneda.obj T ⟶ X'}
    (hf : f = f₁) {T' : BigFppfOver B S hS} {r r₁ : T' ⟶ T} (hr : r = r₁)
    (u : {u : yoneda.obj T' ⟶ P' // u ≫ π' = yoneda.map r ≫ f})
    (hu₁ : u.1 ≫ π' = yoneda.map r₁ ≫ f₁) :
    (baseChangePointEquiv d d' g halg T f r u).1 =
      (baseChangePointEquiv d d' g halg T f₁ r₁ ⟨u.1, hu₁⟩).1 := by
  subst hf hr
  rfl

/-- The point of `X' ×_X P` that `basePointEquivPullback` attaches to a point `u` of `P'` lies over
the image `u ∘ π'` of `u` in `X'`. -/
theorem basePointEquivPullback_fst (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ P') :
    basePointEquivPullback d d' g halg T u ≫ pullback.fst g π = u ≫ π' :=
  pullback.lift_fst _ _ _

/-- The second component of the point of `X' ×_X P` attached to a point `u` of `P'` is the point
of `P` that the comparison over `u ∘ π'` attaches to `u`. -/
theorem basePointEquivPullback_snd (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ P') :
    basePointEquivPullback d d' g halg T u ≫ pullback.snd g π =
      (baseChangePointEquiv d d' g halg T (u ≫ π') (𝟙 T)
        ⟨u, by rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩).1 :=
  pullback.lift_snd _ _ _

/-! ### `θ` across `r`, and its compatibility with `ψ` -/

/-- **Stacks 085C: the base change of `r` to a scheme point of `X'` is `fibreBaseChangeIso`.**
Over a `T`-point `f` of `X'`, the comparison `r` of
`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv` carries the tautological point
of `T ×_{X'} Proj_{X'}(g^*𝒜)` — the morphism `d'.fibreToSpace T f` to `P'` — to a point of
`P = Proj_X(𝒜)` over `f ∘ g`, that is, by the cartesian square of Stacks 084B, to a morphism of
schemes `T ×_{X'} Proj_{X'}(g^*𝒜) ⟶ T ×_X Proj_X(𝒜)` over `T`.  That morphism is
`AlgebraicGeometry.Space.RelativeProjPoints.fibreBaseChangeIso`, the morphism along which
`AlgebraicGeometry.Space.RelativeProjPoints.fibreBaseChangeTheta` pulls back the twists; so that
isomorphism is the base change to `T` of the source's `θ : r^* pr₂^*(⨁_d 𝒪(d)) ⟶ ⨁_d 𝒪(d)`. -/
theorem toScheme_map_pointEquivOver_baseChangePointEquiv (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X') :
    (BigFppfOver.toScheme B S hS).map
        (d.pointEquivOver T (f ≫ g) (d'.fibreHom T f)
          (baseChangePointEquiv d d' g halg T f (d'.fibreHom T f)
            ⟨d'.fibreToSpace T f, (d'.isPullback T f).w⟩)).1 =
      (fibreBaseChangeIso d d' g halg T f).hom := by
  have hself : d'.pointEquivOver T f (d'.fibreHom T f)
      ⟨d'.fibreToSpace T f, (d'.isPullback T f).w⟩ = ⟨𝟙 _, Category.id_comp _⟩ :=
    ((d'.pointEquivOver T f (d'.fibreHom T f)).eq_symm_apply).1
      (Subtype.ext (by
        show d'.fibreToSpace T f = yoneda.map (𝟙 (d'.fibre T f)) ≫ d'.fibreToSpace T f
        rw [CategoryTheory.Functor.map_id, Category.id_comp]))
  have key := congrArg Subtype.val (pointEquivProjOver_baseChangePointEquiv d d' g halg
    T f (d'.fibreHom T f) ⟨d'.fibreToSpace T f, (d'.isPullback T f).w⟩)
  rw [pointEquivProjOver_apply, projOverCongr_val, pointEquivProjOver_apply, hself] at key
  change (BigFppfOver.toScheme B S hS).map _ ≫ _ =
    ((BigFppfOver.toScheme B S hS).map (𝟙 _) ≫ _) ≫ _ at key
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at key
  rw [fibreBaseChangeIso_hom]
  exact ((Iso.eq_comp_inv _).2 key).trans (Category.assoc _ _ _)

include halg in
/-- **Stacks 085C: `θ` is compatible with `ψ`, over the scheme points of `X'`.**  Over a
`T`-point `f` of `X'`, the canonical homomorphism of graded algebras
`ψ : π_T^*(f^*g^*𝒜) ⟶ ⨁_{n ∈ ℤ} 𝒪(n)` of Stacks 084D for `Proj_{X'}(g^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjPoints.pointPsiHom`) is the one for `Proj_X(𝒜)` at the
image point `f ∘ g`, transported along the identification of the two restricted algebras: the
source's `θ` carries `ψ` to `ψ`.  The graded algebras of twists themselves correspond in the same
way (`…pointTwistAlgebra_heq`), and so do the identifications `θ` of Stacks 01O3 with every
further base change (`…pointTwistTheta_heq`) and the `ψ` of Stacks 01NR after it
(`AlgebraicGeometry.Space.RelativeProjPoints.basePsi_pointTwistTheta`). -/
@[stacks 085C "theta is compatible with psi: over a scheme point f : T -> X' the canonical \
homomorphism psi : pi_T^*(f^*g^*A) -> (+)_n O(n) of Tag 084D for Proj_{X'}(g^*A) is the one for \
Proj_X(A) at f g, across the identification of the two restricted algebras"]
theorem pointPsiHom_heq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    HEq (d'.pointPsiHom T f) (d.pointPsiHom T (f ≫ g)) := by
  exact congr_arg_heq (fun A => (twistDataOfGradedAlgebra A).psiTransposeHom) (halg T f)

include halg in
/-- The graded algebras of twists of Stacks 084D for `Proj_{X'}(g^*𝒜)` at a point `f` of `X'`
and for `Proj_X(𝒜)` at `f ∘ g` correspond across the identification of the two restricted
algebras. -/
theorem pointTwistAlgebra_heq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    HEq (d'.pointTwistAlgebra T f) (d.pointTwistAlgebra T (f ≫ g)) := by
  exact congr_arg_heq (fun A => (twistDataOfGradedAlgebra A).algebra) (halg T f)

include halg in
/-- **`θ` is compatible with further base change.**  For a further morphism of schemes
`k : Z ⟶ T`, the isomorphism of Stacks 01O3 identifying the inverse image of the twists along
`Proj_Z(k^*f^*g^*𝒜) ⟶ Proj_T(f^*g^*𝒜)` with the twists of `Proj_Z(k^*f^*g^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjPoints.pointTwistTheta`) is, for `Proj_{X'}(g^*𝒜)` at `f`,
the one for `Proj_X(𝒜)` at `f ∘ g`. -/
theorem pointTwistTheta_heq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') {Z : Scheme.{u}}
    (k : Z ⟶ (BigFppfOver.toScheme B S hS).obj T) :
    HEq (d'.pointTwistTheta T f k) (d.pointTwistTheta T (f ≫ g) k) := by
  exact congr_arg_heq (fun A =>
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A k) (halg T f)


end RelativeProjPoints

/-! ### `r` as an isomorphism of algebraic spaces -/

section Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' P P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X} {π' : P' ⟶ X'}

open RelativeProjPoints

/-- **`π' : P' ⟶ X'` is presented as the base change `Proj_{X'}(g^*𝒜)` of the presentation of
`π : P ⟶ X` as `Proj_X(𝒜)`, along `g : X' ⟶ X`.**

The first field says the graded algebra of the presentation `d'` at a `T`-point `f` of `X'` is the
graded algebra of `d` at `f ∘ g`, which is how `g^*𝒜` is read on the scheme points of `X'` (the
same reading as `AlgebraicGeometry.Space.GradedAlgebraPoints.comap`).  The second says that the
comparison `AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv` of the two
presentations is compatible with restriction in the test object: the point of `P` that it
attaches to a `T'`-point of `P'` lying over `f ∘ r`, computed through the identifications
`Proj_T(f^*g^*𝒜) = T ×_{X'} P'` and `Proj_T((f g)^*𝒜) = T ×_X P` of Stacks 084B at the point `f`,
is the one computed through those identifications at the restricted point `f ∘ r`.

That is the canonicity of Stacks 084B's identifications — the identification
`Proj_{T'}((f r)^*𝒜) = T' ×_X P` at a restricted point is the base change of the one at `f` —
read on the two presentations.  It says that the comparison commutes with changing the point of
the base; together with its naturality at a fixed point, which is proved
(`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv_natural`), it is what makes the
comparisons the components of a morphism of presheaves.  It cannot be derived from
`AlgebraicGeometry.Space.RelativeProjPoints` alone: that structure gives the identification at
each point of the base as independent data, with no comparison between a point and its
restriction, and in the source this compatibility is part of the canonicity of Stacks 084B, which
is not proved in this library.  `AlgebraicGeometry.Space.RelativeProjHomPoints` carries the same
compatibility, in the same shape, for Stacks 085F.  Both fields hold for the restricted
presentation `AlgebraicGeometry.Space.RelativeProjPoints.comap`
(`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.comap`), so nothing stated with this
structure is vacuous. -/
structure RelativeProjBaseChangePoints (d : RelativeProjPoints B S hS π)
    (d' : RelativeProjPoints B S hS π') (g : X' ⟶ X) : Prop where
  /-- The graded algebra of `P'` at a point of `X'` is that of `P` at its image in `X`. -/
  algebra_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    d'.algebra T f = d.algebra T (f ≫ g)
  /-- The comparison of the two presentations is compatible with restriction in the test
  object. -/
  baseChangePointEquiv_eq (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
      {T' : BigFppfOver B S hS} (r : T' ⟶ T)
      (u : {u : yoneda.obj T' ⟶ P' // u ≫ π' = yoneda.map r ≫ f}) :
    (baseChangePointEquiv d d' g algebra_eq T f r u).1 =
      (baseChangePointEquiv d d' g algebra_eq T' (yoneda.map r ≫ f) (𝟙 T')
        ⟨u.1, by rw [u.2, CategoryTheory.Functor.map_id, Category.id_comp]⟩).1

namespace RelativeProjBaseChangePoints

/-- **The hypotheses are satisfiable.**  The restricted presentation
`AlgebraicGeometry.Space.RelativeProjPoints.comap` of `X' ×_X P ⟶ X'` is a base change of the
presentation of `P` in the sense of `AlgebraicGeometry.Space.RelativeProjBaseChangePoints`: over
every point and along every morphism of test objects the comparison is the second projection
(`AlgebraicGeometry.Space.RelativeProjPoints.comap_baseChangePointEquiv`). -/
theorem comap (d₀ : RelativeProjPoints B S hS π) (g₀ : X' ⟶ X) :
    RelativeProjBaseChangePoints d₀ (d₀.comap g₀) g₀ where
  algebra_eq _ _ := rfl
  baseChangePointEquiv_eq T f T' r u :=
    (comap_baseChangePointEquiv d₀ g₀ T f r u).trans
      (comap_baseChangePointEquiv d₀ g₀ T' (yoneda.map r ≫ f) (𝟙 T') _).symm

variable {d : RelativeProjPoints B S hS π} {d' : RelativeProjPoints B S hS π'} {g : X' ⟶ X}
  (h : RelativeProjBaseChangePoints d d' g)

/-- **The isomorphism `r` on `T`-points is compatible with restriction of the test object.**
Restricting a `T`-point of `P'` along `k : T₁ ⟶ T` restricts the `T`-point of `X' ×_X P` it
corresponds to.  The first components agree trivially; for the second, the comparison computed at
the restricted point is the one computed at the original point along `k`
(`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.baseChangePointEquiv_eq`), and that one is
natural in the test object at the fixed point
(`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv_natural`). -/
theorem basePointEquivPullback_restrict (T T₁ : BigFppfOver B S hS) (k : T₁ ⟶ T)
    (u : yoneda.obj T ⟶ P') :
    basePointEquivPullback d d' g h.algebra_eq T₁ (yoneda.map k ≫ u) =
      yoneda.map k ≫ basePointEquivPullback d d' g h.algebra_eq T u := by
  apply pullback.hom_ext
  · simp only [Category.assoc, basePointEquivPullback_fst]
  · refine (basePointEquivPullback_snd d d' g h.algebra_eq T₁ _).trans
      (Eq.trans ?_ (Category.assoc _ _ _).symm)
    rw [basePointEquivPullback_snd d d' g h.algebra_eq T u]
    refine Eq.trans ?_ (baseChangePointEquiv_natural d d' g h.algebra_eq T (u ≫ π') (𝟙 T) k
      ⟨u, by rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩)
    refine Eq.trans ?_ (h.baseChangePointEquiv_eq T (u ≫ π') (k ≫ 𝟙 T) _).symm
    exact baseChangePointEquiv_congr d d' g h.algebra_eq T₁
      (by rw [Category.comp_id, Category.assoc]) rfl _ _

/-- **Stacks 085C, the canonical isomorphism `r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)`, as an
isomorphism of algebraic spaces.**

Let `g : X' ⟶ X` be a morphism of algebraic spaces over `S`, let `π : P ⟶ X` be presented as
`Proj_X(𝒜)` and `π' : P' ⟶ X'` as its base change `Proj_{X'}(g^*𝒜)` in the sense of
`AlgebraicGeometry.Space.RelativeProjBaseChangePoints`.  Then `P'` is isomorphic to the fibre
product `X' ×_X P` as a presheaf on the big fppf site of `S`, that is, as an algebraic space.  At
a test object `T` the isomorphism is the bijection
`AlgebraicGeometry.Space.RelativeProjPoints.basePointEquivPullback`, which over a `T`-point `f` of
`X'` sends a point of `P'` to the point of `P` over `f ∘ g` that the two identifications of
Stacks 084B at `f` attach to it — the source's proof builds `r` on the values of the functors in
the same way — and its naturality in the test object is
`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.basePointEquivPullback_restrict`.

The relative Proj of an algebraic space is presented here, as for Stacks 084D, 085D and 085F,
through its base changes to the scheme points of the base: the space `Proj_X(𝒜)` itself is not
constructed from `𝒜` in this library, because Stacks 084B is not proved. -/
@[stacks 085C "the canonical isomorphism r : Proj_{X'}(g^*A) -> X' x_X Proj_X(A), as an \
isomorphism of presheaves on the big fppf site (that is, of algebraic spaces), natural in the \
test object; Proj_X(A) and Proj_{X'}(g^*A) are given by Stacks 084B's presentations over the \
scheme points of the base, Proj_X(A) not being constructed from A in this library (084B)"]
def baseChangeIso : P' ≅ pullback g π :=
  NatIso.ofComponents
    (fun Y => (yonedaEquiv.symm.trans
      ((basePointEquivPullback d d' g h.algebra_eq Y.unop).trans yonedaEquiv)).toIso)
    (fun {Y Z} i => TypeCat.homEquiv.injective (funext fun x => by
      change yonedaEquiv (basePointEquivPullback d d' g h.algebra_eq Z.unop
          (yonedaEquiv.symm (P'.map i x))) =
        (pullback g π).map i (yonedaEquiv (basePointEquivPullback d d' g h.algebra_eq Y.unop
          (yonedaEquiv.symm x)))
      rw [yonedaEquiv_symm_map, yonedaEquiv_naturality',
        h.basePointEquivPullback_restrict Y.unop Z.unop i.unop]))

/-- The isomorphism `r` read on a `T`-point of `P'`. -/
theorem comp_baseChangeIso_hom (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ P') :
    u ≫ h.baseChangeIso.hom = basePointEquivPullback d d' g h.algebra_eq T u := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  show yonedaEquiv (basePointEquivPullback d d' g h.algebra_eq T
    (yonedaEquiv.symm (yonedaEquiv u))) = _
  rw [Equiv.symm_apply_apply]

/-- **Stacks 085C: `r` is a morphism over `X'`.**  The isomorphism
`r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)` followed by the first projection is the structure
morphism of `Proj_{X'}(g^*𝒜)`. -/
@[stacks 085C "r is an isomorphism over X': followed by the first projection X' x_X Proj_X(A) -> \
X' it is the structure morphism of Proj_{X'}(g^*A)"]
theorem baseChangeIso_hom_fst : h.baseChangeIso.hom ≫ pullback.fst g π = π' :=
  hom_ext_yoneda fun T u => by
    rw [← Category.assoc, h.comp_baseChangeIso_hom, basePointEquivPullback_fst]

/-- **Stacks 085C: the description of `r` over the scheme points of `X'`.**  For a `T`-point `f`
of `X'`, a morphism `r : T' ⟶ T` and a `T'`-point `u` of `P' = Proj_{X'}(g^*𝒜)` over `f ∘ r`, the
second component of `r(u)` is the point of `P = Proj_X(𝒜)` over `f ∘ g ∘ r` that the
identifications `Proj_T(f^*g^*𝒜) = T ×_{X'} P'` and `Proj_T((f g)^*𝒜) = T ×_X P` of Stacks 084B
attach to `u` (`AlgebraicGeometry.Space.RelativeProjPoints.baseChangePointEquiv`).  So over every
scheme `T` over `X'` the base change of `r` is the identification of the two scheme-level
relative Projs of one graded algebra, which is how the source describes `r` étale locally; with
`AlgebraicGeometry.Space.RelativeProjBaseChangePoints.baseChangeIso_hom_unique` it determines
`r`. -/
@[stacks 085C "the description of r over the scheme points of X': over a point f : T -> X' the \
base change of r is the identification of Proj_T(f^*g^*A) = T x_{X'} Proj_{X'}(g^*A) with \
Proj_T((g f)^*A) = T x_X Proj_X(A) given by Stacks 084B"]
theorem baseChangeIso_hom_snd (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X')
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (u : {u : yoneda.obj T' ⟶ P' // u ≫ π' = yoneda.map r ≫ f}) :
    u.1 ≫ h.baseChangeIso.hom ≫ pullback.snd g π =
      (baseChangePointEquiv d d' g h.algebra_eq T f r u).1 := by
  rw [← Category.assoc, h.comp_baseChangeIso_hom, basePointEquivPullback_snd,
    h.baseChangePointEquiv_eq T f r u]
  exact baseChangePointEquiv_congr d d' g h.algebra_eq T' u.2 rfl _ _

/-- **`r` is the only morphism over `X'` with that description.**  A morphism
`P' ⟶ X' ×_X P` over `X'` whose second component, on every `T`-point of `P'`, is the point of
`P` that the identifications of Stacks 084B attach to it, is `r`. -/
theorem baseChangeIso_hom_unique (φ : P' ⟶ pullback g π)
    (hfst : φ ≫ pullback.fst g π = π')
    (hsnd : ∀ (T : BigFppfOver B S hS) (u : yoneda.obj T ⟶ P'),
      u ≫ φ ≫ pullback.snd g π =
        (baseChangePointEquiv d d' g h.algebra_eq T (u ≫ π') (𝟙 T)
          ⟨u, by rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩).1) :
    φ = h.baseChangeIso.hom :=
  hom_ext_yoneda fun T u => by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst, Category.assoc, h.baseChangeIso_hom_fst]
    · rw [Category.assoc, Category.assoc]
      exact (hsnd T u).trans (h.baseChangeIso_hom_snd T (u ≫ π') (𝟙 T)
        ⟨u, by rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩).symm

/-- The point of `P` attached by `r` to the tautological point of `T ×_{X'} P'` lies over the
image of that point in `X`. -/
theorem fibreToSpace_baseChangeIso_snd_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X') :
    (d'.fibreToSpace T f ≫ h.baseChangeIso.hom ≫ pullback.snd g π) ≫ π =
      yoneda.map (d'.fibreHom T f) ≫ (f ≫ g) := by
  rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% h.baseChangeIso_hom_fst,
    ← Category.assoc, (d'.isPullback T f).w, Category.assoc]

/-- **Stacks 085C: the isomorphism `θ` is taken across `r`.**  Over a `T`-point `f` of `X'`, the
morphism of schemes `T ×_{X'} Proj_{X'}(g^*𝒜) ⟶ T ×_X Proj_X(𝒜)` over `T` that `r` induces
through the two cartesian squares of Stacks 084B is
`AlgebraicGeometry.Space.RelativeProjPoints.fibreBaseChangeIso`.  So the isomorphism
`AlgebraicGeometry.Space.RelativeProjPoints.fibreBaseChangeTheta`, which is stated as an
isomorphism from the inverse image along `fibreBaseChangeIso` of the twists on `T ×_X Proj_X(𝒜)`,
is the base change to `T` of the source's `θ : r^* pr₂^*(⨁_d 𝒪(d)) ⟶ ⨁_d 𝒪(d)`. -/
@[stacks 085C "theta is taken across r: over a scheme point f : T -> X' the morphism of schemes \
T x_{X'} Proj_{X'}(g^*A) -> T x_X Proj_X(A) over T that r induces through the cartesian squares \
of Stacks 084B is fibreBaseChangeIso, the morphism along which fibreBaseChangeTheta pulls back \
the twists"]
theorem toScheme_map_pointEquivOver_baseChangeIso (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X') :
    (BigFppfOver.toScheme B S hS).map
        (d.pointEquivOver T (f ≫ g) (d'.fibreHom T f)
          ⟨d'.fibreToSpace T f ≫ h.baseChangeIso.hom ≫ pullback.snd g π,
            h.fibreToSpace_baseChangeIso_snd_comp T f⟩).1 =
      (fibreBaseChangeIso d d' g h.algebra_eq T f).hom := by
  have hv : (⟨d'.fibreToSpace T f ≫ h.baseChangeIso.hom ≫ pullback.snd g π,
        h.fibreToSpace_baseChangeIso_snd_comp T f⟩ :
        {u : yoneda.obj (d'.fibre T f) ⟶ P //
          u ≫ π = yoneda.map (d'.fibreHom T f) ≫ (f ≫ g)}) =
      baseChangePointEquiv d d' g h.algebra_eq T f (d'.fibreHom T f)
        ⟨d'.fibreToSpace T f, (d'.isPullback T f).w⟩ :=
    Subtype.ext (h.baseChangeIso_hom_snd T f (d'.fibreHom T f)
      ⟨d'.fibreToSpace T f, (d'.isPullback T f).w⟩)
  rw [hv]
  exact toScheme_map_pointEquivOver_baseChangePointEquiv d d' g h.algebra_eq T f

end RelativeProjBaseChangePoints

end Space

end AlgebraicGeometry.Space

end
