module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardGradedSections
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.PullbackScalarSquare

/-!
# The blowup's degreewise twist comparison intertwines the graded scalar action

Let `A` be a Noetherian ring, `I ⊆ A` an ideal with a chosen finite generating family, and
`i : X ⟶ 𝐏` the closed immersion of the blowup `X = Proj(⨁ₙ Iⁿ)` into projective space coming
from the polynomial presentation `ψ` of the Rees algebra.
`Stacks.Blowup.twistSheafOfModules_pushforward_unit_iso` is the degree-`d` comparison
`Φ_d : (i_*𝒪_X)(d) ≅ i_*(𝒪_X(d))`. This file proves that the family `{Φ_d}` is compatible with
the graded scalar action: for a homogeneous `a` of degree `j`,

`(a ·) ≫ Φ_{j + d} = Φ_d ≫ i_*((ψ a) ·)`.

## Why this is the missing compatibility, and why it is not expensive

`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardGradedSections.lean`'s "What that
route still owes" records two needs, both of which are this one statement: the finiteness of
`Stacks.Blowup.moduleFinite_truncation_pushforward_of_span` is about the graded
`A[T₀, …, T_m]`-module `⨁_{d ≥ k} Γ(𝐏, (i_*𝒪_X)(d))`, whose module structure moves a section of
degree `d` to one of degree `d + e`, and transporting it along `{Φ_d}` needs exactly that the
family intertwine that action.

The record there says the route to it is to prove that `Φ_d` "has the formula `u ⊗ s ↦ u · ρ_d s`
on a pure tensor". That formula is true, but it is not what the compatibility needs, and the
compatibility is cheaper than it. `Φ_d` is a composite of two factors, the projection formula at
`i` and the left unitor after whiskering with the degree-`d` comparison, and **both factors are
natural**: the projection formula in the module on the target
(`Stacks.AffineProjectionFormula.projectionFormulaMap_natural`) and the unitor by the monoidal
axiom. So the square for `Φ` reduces, with no computation on sections at all, to the square for
the degree-`d` comparison alone — which is
`Stacks.AlgebraicGeometry.ThetaMultiplicative.pullbackTwistIso_twistScalarSheafMap`.

The obstruction recorded against the pullback spelling of `θ` — that its five structural
inverse-image factors defeat the transport — is a statement about transporting a *product*
formula, and remains accurate as such. The scalar action is multiplication by a **fixed**
homogeneous element, i.e. a *morphism* of twisting sheaves, and a natural transformation
commutes with an arbitrary morphism by definition; so each structural factor costs one
naturality square and nothing more. See
`StacksFrontier/AlgebraicGeometry/ThetaMultiplicative/PullbackScalarSquare.lean`.

## Main results

The elided prefix is `Stacks.Blowup`.

* `whiskerLeft_eq_tensorSheafMap`: whiskering on the left in
  `Stacks.SheafOfModules.OnSpace.monoidal` is `tensorSheafMap` of an identity. The monoidal
  structure is transported along an equivalence, so this needs the pure-tensor extensionality of
  `Stacks.SheafOfModules.OnSpace.tensor_hom_ext`; it is the only place in this file where a
  section appears.
* `projectionFormulaMap_tensorSheafMap_id` and `pushforwardTensorSheafIso_naturality`:
  naturality of the projection formula at a closed immersion in the module on the target, in the
  `tensorSheafMap` spelling the twists are written with.
* `pushforwardUnitTensorIso_hom` and `whisker_square`: the two factors of
  `Stacks.Blowup.pushforwardUnitTensorIso` separated, and the square for the second.
* `pushforwardUnitTensorIso_hom_naturality`: **the general statement** — the projection formula's
  unit case is natural in the pair of comparisons it is built from.
* `pushforwardUnitTensorIso_pullbackTwistIso_square`: **the square for the comparison the
  blowup uses**, `(a ·) ≫ Φ_{j + d} = Φ_d ≫ (Proj ψ)_*((ψ a) ·)`, for an arbitrary graded
  surjection `ψ` whose `AlgebraicGeometry.Proj.map` is a closed immersion.
* `twistSheafScalarMap_eq_tensorSheafMap` and `twistSheafOfModules_pushforward_unit_iso_eq`: the
  two `rfl` equations bridging that square's spelling to
  `Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap` and
  `Stacks.Blowup.twistSheafOfModules_pushforward_unit_iso`.

## What is still owed, and one thing that is a machine limit rather than mathematics

The square is proved for an arbitrary graded surjection `ψ` with
`AlgebraicGeometry.Proj.map ψ hψ` a closed immersion, i.e. in exactly the generality the blowup
needs; `Stacks.Blowup.blowUpSpecToProjSpace I x hx hspan` **is**
`AlgebraicGeometry.Proj.map (reesPresentation I x hx) _` by definition, so the blowup's square is
that statement instantiated.

Writing that instantiation down as a theorem of its own does not currently typecheck. The
statement elaborates, and so does the one-line proof, but the **kernel** then exceeds its
deterministic reduction budget checking the instantiated type: at concrete arguments the type
mentions `AlgebraicGeometry.Proj (polyGrading R m)` and
`AlgebraicGeometry.Proj.map (reesPresentation I x hx) _`, and Mathlib's `Proj.map` is itself
declared with the transparency-respecting `isDefEq` check disabled, precisely because it does
not reduce affordably. This was tried five ways — the general lemma applied directly, via
`rw` with the two bridging `rfl` equations below, with the morphism spelled as `Proj.map` rather
than `blowUpSpecToProjSpace`, and with the `IsNoetherianRing` hypothesis dropped — and every one
of them ends in `(kernel) deterministic timeout`. Since that escape hatch is unavailable in this
library, the
instantiation is left to the consumer, which performs it inside a larger proof where the
surrounding context fixes the elaboration order. The two `rfl` equations that bridge the
spellings, `twistSheafScalarMap_eq_tensorSheafMap` and
`twistSheafOfModules_pushforward_unit_iso_eq`, are proved here individually; it is their
*combination* in one statement that overflows.

Beyond that: reading the square on global sections and assembling the family `{Φ_d}` into a
morphism of graded modules — so that
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation`'s two
hypotheses can be transported from `𝐏` to `X` — is not done here. It is done in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardStep.lean`, for the *second* of those
two hypotheses, and by a route that needs no assembly into a morphism of graded modules at all:
both finiteness statements are in the `ℱ`-twist spelling, so the comparison is taken with the
unit tensor left in place on both sides (`Stacks.Blowup.pushforwardTwistUnitIso`), and degree-one
generation transports one degree at a time.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules)
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap)

universe u

namespace Stacks.Blowup

attribute [local instance] modulesMonoidal modulesMonoidal'

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- **Whiskering on the left by `A` is the canonical induced morphism `𝟙_A ⊗ g`.** The monoidal
structure of `Stacks.SheafOfModules.OnSpace.monoidal` is transported along an equivalence, so
`A ◁ g` is not syntactically `tensorSheafMap`; the two agree because both act on a local pure
tensor by applying `g` to the right factor, which is
`Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul` on one side and
`tensorSheafMap_app_toTensorSheafSection` on the other, and a morphism out of a sheafified
tensor product is determined by its effect on local pure tensors. -/
public theorem whiskerLeft_eq_tensorSheafMap (Z : RingedSpace.{u, u})
    (A : SheafOfModules.{u} (_root_.structureSheafRing Z))
    {B B' : SheafOfModules.{u} (_root_.structureSheafRing Z)} (g : B ⟶ B') :
    letI := Stacks.SheafOfModules.OnSpace.monoidal Z
    (A ◁ g) = ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
        (((𝟙 A), g) : (_, _) ⟶ (_, _))) :=
  let := Stacks.SheafOfModules.OnSpace.monoidal Z
  Stacks.SheafOfModules.OnSpace.tensor_hom_ext Z fun U a b =>
    (Stacks.SheafOfModules.OnSpace.whiskerLeft_tmul Z A g U a b).trans
      (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
        Z A B A B' (𝟙 A) g U.unop a b).symm

/-- **The projection formula at a closed immersion followed by the left unitor, written out.**
`Stacks.Blowup.pushforwardUnitTensorIso` is this composite by definition; naming it lets the two
factors be treated separately, which is what the naturality below does. -/
public theorem pushforwardUnitTensorIso_hom (E : Y.Modules) (G : X.Modules)
    (e : (Scheme.Modules.pullback f).obj E ≅ G) :
    (pushforwardUnitTensorIso f E G e).hom =
      (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso f
          (SheafOfModules.unit X.ringCatSheaf) E).hom ≫
        (Scheme.Modules.pushforward f).map
          ((𝟙_ X.Modules ◁ e.hom) ≫ (λ_ G).hom) := rfl

/-- **Naturality of the projection-formula map in the module on the target, in the
`tensorSheafMap` spelling.** This is
`Stacks.AffineProjectionFormula.projectionFormulaMap_natural` at `g = 𝟙`. It is stated at the
level of ringed spaces, on bare variables, because at the `AlgebraicGeometry.Scheme.Modules`
spelling `rw` cannot see through the two spellings of the identity morphism. -/
public theorem projectionFormulaMap_tensorSheafMap_id {Z W : RingedSpace.{u, u}} (h : Z ⟶ W)
    (G : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Z))
    {H H' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf W)} (k : H ⟶ H') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)).map
        (((𝟙 ((Stacks.RingedSpace.pushforwardFunctor h).obj G)), k) : (_, _) ⟶ (_, _))) ≫
        Stacks.AffineProjectionFormula.projectionFormulaMap h G H' =
      Stacks.AffineProjectionFormula.projectionFormulaMap h G H ≫
        (Stacks.RingedSpace.pushforwardFunctor h).map
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)).map
              (((𝟙 G), ((Stacks.RingedSpace.pullbackFunctor h).map k)) :
                (_, _) ⟶ (_, _)))) := by
  have hnat := Stacks.AffineProjectionFormula.projectionFormulaMap_natural h (𝟙 G) k
  rw [CategoryTheory.Functor.map_id] at hnat
  exact hnat

/-- **The projection formula at a closed immersion is natural in the module on the target**, at
the `AlgebraicGeometry.Scheme.Modules` spelling. -/
public theorem pushforwardTensorSheafIso_naturality (E E' : Y.Modules) (k : E ⟶ E') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
        (((𝟙 ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))), k) :
          (_, _) ⟶ (_, _))) ≫
        (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso f
          (SheafOfModules.unit X.ringCatSheaf) E').hom =
      (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso f
          (SheafOfModules.unit X.ringCatSheaf) E).hom ≫
        (Scheme.Modules.pushforward f).map
          (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
              (((𝟙 (SheafOfModules.unit X.ringCatSheaf)), ((Scheme.Modules.pullback f).map k)) :
                (_, _) ⟶ (_, _)))) :=
  projectionFormulaMap_tensorSheafMap_id f.toLRSHom.toShHom
    (SheafOfModules.unit X.ringCatSheaf) k

omit [IsClosedImmersion f] in
/-- **The second factor of `pushforwardUnitTensorIso` intertwines `k` with `g`**, provided the
comparisons `e`, `e'` do: `(𝟙_ ⊗ f^*k) ≫ (𝟙_ ⊗ e'.hom) ≫ λ = ((𝟙_ ⊗ e.hom) ≫ λ) ≫ g`.

Only two monoidal facts are used, `MonoidalCategory.whiskerLeft_comp` to merge the two
whiskerings and `MonoidalCategory.leftUnitor_naturality` to move `g` past the unitor. Nothing
here is a statement about products, which is why the obstruction recorded for the pullback
spelling of `θ` in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardGradedSections.lean` does not
apply. -/
public theorem whisker_square {E E' : Y.Modules} {G G' : X.Modules}
    (e : (Scheme.Modules.pullback f).obj E ≅ G)
    (e' : (Scheme.Modules.pullback f).obj E' ≅ G') (k : E ⟶ E') (g : G ⟶ G')
    (hk : (Scheme.Modules.pullback f).map k ≫ e'.hom = e.hom ≫ g) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
        (((𝟙 (𝟙_ X.Modules)), ((Scheme.Modules.pullback f).map k)) : (_, _) ⟶ (_, _))) ≫
        ((𝟙_ X.Modules ◁ e'.hom) ≫ (λ_ G').hom) =
      ((𝟙_ X.Modules ◁ e.hom) ≫ (λ_ G).hom) ≫ g := by
  refine Eq.trans (congrArg (fun t => t ≫ ((𝟙_ X.Modules ◁ e'.hom) ≫ (λ_ G').hom))
    (whiskerLeft_eq_tensorSheafMap X.toRingedSpace (𝟙_ X.Modules)
      ((Scheme.Modules.pullback f).map k)).symm) ?_
  calc (𝟙_ X.Modules ◁ (Scheme.Modules.pullback f).map k) ≫
          ((𝟙_ X.Modules ◁ e'.hom) ≫ (λ_ G').hom)
      = ((𝟙_ X.Modules ◁ (Scheme.Modules.pullback f).map k) ≫
          (𝟙_ X.Modules ◁ e'.hom)) ≫ (λ_ G').hom := (Category.assoc _ _ _).symm
    _ = (𝟙_ X.Modules ◁ ((Scheme.Modules.pullback f).map k ≫ e'.hom)) ≫ (λ_ G').hom := by
        rw [MonoidalCategory.whiskerLeft_comp]
    _ = (𝟙_ X.Modules ◁ (e.hom ≫ g)) ≫ (λ_ G').hom := by rw [hk]
    _ = ((𝟙_ X.Modules ◁ e.hom) ≫ (𝟙_ X.Modules ◁ g)) ≫ (λ_ G').hom := by
        rw [MonoidalCategory.whiskerLeft_comp]
    _ = (𝟙_ X.Modules ◁ e.hom) ≫ ((𝟙_ X.Modules ◁ g) ≫ (λ_ G').hom) := Category.assoc _ _ _
    _ = (𝟙_ X.Modules ◁ e.hom) ≫ ((λ_ G).hom ≫ g) := by
        rw [MonoidalCategory.leftUnitor_naturality]
    _ = ((𝟙_ X.Modules ◁ e.hom) ≫ (λ_ G).hom) ≫ g := (Category.assoc _ _ _).symm

/-- **`pushforwardUnitTensorIso` is natural in the pair of comparisons.** Given
`k : E ⟶ E'` on the target, `g : G ⟶ G'` on the source and a commuting square
`f^*k ≫ e'.hom = e.hom ≫ g`, the two isomorphisms `f_*𝒪_X ⊗ E ≅ f_*G` and `f_*𝒪_X ⊗ E' ≅ f_*G'`
intertwine `𝟙 ⊗ k` with `f_*g`.

This is the whole of route (b): the square for the already-invertible comparison is the square
for `e` transported through naturality of the projection formula and of the left unitor, with no
elementwise computation and no re-derivation of [Stacks, Tag 01NO]. -/
public theorem pushforwardUnitTensorIso_hom_naturality {E E' : Y.Modules} {G G' : X.Modules}
    (e : (Scheme.Modules.pullback f).obj E ≅ G)
    (e' : (Scheme.Modules.pullback f).obj E' ≅ G') (k : E ⟶ E') (g : G ⟶ G')
    (hk : (Scheme.Modules.pullback f).map k ≫ e'.hom = e.hom ≫ g) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)).map
        (((𝟙 ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))), k) :
          (_, _) ⟶ (_, _))) ≫
        (pushforwardUnitTensorIso f E' G' e').hom =
      (pushforwardUnitTensorIso f E G e).hom ≫ (Scheme.Modules.pushforward f).map g := by
  have hP : (Scheme.Modules.pushforward f).map
        (((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)).map
            (((𝟙 (SheafOfModules.unit X.ringCatSheaf)), ((Scheme.Modules.pullback f).map k)) :
              (_, _) ⟶ (_, _)))) ≫
        (Scheme.Modules.pushforward f).map ((𝟙_ X.Modules ◁ e'.hom) ≫ (λ_ G').hom) =
      (Scheme.Modules.pushforward f).map ((𝟙_ X.Modules ◁ e.hom) ≫ (λ_ G).hom) ≫
        (Scheme.Modules.pushforward f).map g :=
    ((Scheme.Modules.pushforward f).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pushforward f).map
        (whisker_square f e e' k g hk)).trans
        ((Scheme.Modules.pushforward f).map_comp _ _))
  rw [pushforwardUnitTensorIso_hom f E' G' e', pushforwardUnitTensorIso_hom f E G e]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ (Scheme.Modules.pushforward f).map
      ((𝟙_ X.Modules ◁ e'.hom) ≫ (λ_ G').hom))
    (pushforwardTensorSheafIso_naturality f E E' k)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t =>
    (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso f
      (SheafOfModules.unit X.ringCatSheaf) E).hom ≫ t) hP) ?_
  exact (Category.assoc _ _ _).symm

/-- **The graded scalar action on a twist of `ℱ` is `tensorSheafMap` of an identity.** This is
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistSheafScalarMap` by definition; naming the
equation isolates the definitional unfolding, which is between the
`Stacks.SheafOfModules.TensorSheafification` and `Stacks.SheafOfModules.TensorStalkRingedSpace`
spellings of the sheafified tensor product and is expensive to re-check inside a larger
unification problem. -/
public theorem twistSheafScalarMap_eq_tensorSheafMap {S σ : Type u} [CommRing S] [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    (F : SheafOfModules.{u}
      ((CategoryTheory.sheafCompose
        (_root_.Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
        (CategoryTheory.forget₂ CommRingCat.{u} RingCat.{u})).obj
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
    (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k) (a : 𝒮 i) :
    twistSheafScalarMap 𝒮 F i n k hk a =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (AlgebraicGeometry.Proj 𝒮).sheaf)).map
          (((𝟙 F), (twistScalarSheafMap 𝒮 i n k hk a)) : (_, _) ⟶ (_, _))) := rfl

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The blowup's degreewise comparison, with its two ingredients named.** This is the
definition of `Stacks.Blowup.twistSheafOfModules_pushforward_unit_iso` with the `have` in its
body unfolded, so that the general naturality above can be applied to it without unfolding the
definition inside a unification problem. -/
public theorem twistSheafOfModules_pushforward_unit_iso_eq {R : Type u}
    [CommRing R] [IsNoetherianRing R] {I : Ideal R} {m : ℕ} (x : Fin (m + 1) → R)
    (hx : ∀ j, x j ∈ I) (hspan : I = Ideal.span (Set.range x)) (d : ℤ) :
    twistSheafOfModules_pushforward_unit_iso x hx hspan d =
      pushforwardUnitTensorIso (blowUpSpecToProjSpace I x hx hspan)
        (twistingSheaf (polyGrading R m) d) (twistingSheaf (reesGrading I) d)
        (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso
          (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
          (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading R m) d) := rfl

/-- **The degreewise comparison built from [Stacks, Tag 01N1] part (3) intertwines the graded
scalar action.** For a graded surjection `ψ : 𝒮 →+*ᵍ ℬ` generated in degree one whose induced
morphism `π = Proj ψ` is a closed immersion, write
`Φ_d : (π_*𝒪_{Proj ℬ})(d) ≅ π_*(𝒪_{Proj ℬ}(d))` for the projection formula at `π` followed by
the degree-`d` comparison. Then for every homogeneous `a` of degree `i` and every integer `d`

`(a ·) ≫ Φ_{i + d} = Φ_d ≫ π_*((ψ a) ·)`.

This is the compatibility across degrees that
`Stacks.Blowup.moduleFinite_truncation_pushforward_of_span`'s finiteness needs in order to be
transported from `⨁_{d ≥ k} Γ(𝐏, (i_*𝒪_X)(d))` to `⨁_{d ≥ k} Γ(X, 𝒪_X(d))`, and the first of
the two things
`StacksFrontier/AlgebraicGeometry/Blowup/ProjectivePushforwardGradedSections.lean`'s "What that
route still owes" records as outstanding. It is an identity of morphisms of sheaves, so it holds
on **every** section of `(π_*𝒪)(d)` — not only on sections of the form `degreeSection d a`,
which is the limitation that made
`Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso_degreeSection`
insufficient. -/
public theorem pushforwardUnitTensorIso_pullbackTwistIso_square {S B' σ τ : Type u}
    [CommRing S] [CommRing B'] [SetLike σ S] [AddSubgroupClass σ S] [SetLike τ B']
    [AddSubgroupClass τ B'] (𝒮 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒮] [GradedRing ℬ]
    (ψ : 𝒮 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒮).map ψ)
    (hsurj : Function.Surjective (ψ : S → B'))
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    [IsClosedImmersion (AlgebraicGeometry.Proj.map ψ hψ)] (i : ℕ) (d : ℤ) (a : 𝒮 i) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (AlgebraicGeometry.Proj 𝒮).sheaf)).map
        (((𝟙 ((Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).obj
            (SheafOfModules.unit (AlgebraicGeometry.Proj ℬ).ringCatSheaf))),
          (twistScalarSheafMap 𝒮 i d ((i : ℤ) + d) rfl a)) : (_, _) ⟶ (_, _))) ≫
        (pushforwardUnitTensorIso (AlgebraicGeometry.Proj.map ψ hψ)
          (twistingSheaf 𝒮 ((i : ℤ) + d)) (twistingSheaf ℬ ((i : ℤ) + d))
          (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso
            ψ hψ hsurj hgen ((i : ℤ) + d))).hom =
      (pushforwardUnitTensorIso (AlgebraicGeometry.Proj.map ψ hψ)
          (twistingSheaf 𝒮 d) (twistingSheaf ℬ d)
          (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso
            ψ hψ hsurj hgen d)).hom ≫
        (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map
          (twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩) :=
  pushforwardUnitTensorIso_hom_naturality (AlgebraicGeometry.Proj.map ψ hψ)
    (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso ψ hψ hsurj hgen d)
    (Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso ψ hψ hsurj hgen
      ((i : ℤ) + d))
    (twistScalarSheafMap 𝒮 i d ((i : ℤ) + d) rfl a)
    (twistScalarSheafMap ℬ i d ((i : ℤ) + d) rfl ⟨ψ a, ψ.map_mem a.2⟩)
    (Stacks.AlgebraicGeometry.ThetaMultiplicative.pullbackTwistIso_twistScalarSheafMap
      𝒮 ℬ ψ hψ hsurj hgen i d a)

end Stacks.Blowup

end
