module

public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0AYU] at a morphism: the degree is unchanged by pulling back

[Stacks, Tag 0AYU] has two statements. The first is for `g : X' ⟶ X` a **birational** morphism of
proper schemes of dimension at most one over a field `k`:

`deg(g^*ℰ) = deg(ℰ)` for every finite locally free `ℰ` of constant rank.

The second — "more generally it suffices if `g` induces a bijection between irreducible components
of dimension `1` and isomorphisms of local rings at the corresponding generic points" — implies
the first and is the one the companion file
`StacksFrontier/AlgebraicGeometry/BirationalCurveFinite/Basic.lean` and this file are organised
around.

`StacksFrontier/AlgebraicGeometry/CurveDegreeInvariance/Basic.lean` proves the *computation* of the
tag, in a form that does not mention `g`: from a four-term exact sequence
`0 ⟶ 𝒦 ⟶ 𝒪_X ⟶ 𝒫 ⟶ 𝒬 ⟶ 0` whose ends satisfy clause (5) of [Stacks, Tag 0AYT] it concludes
`χ(X, 𝒫 ⊗ ℰ) − n·χ(X, 𝒫) = deg(ℰ)`. This file instantiates that at `𝒫 = g_*𝒪_{X'}` and reads the
left-hand side on `X'`, which is what turns the computation into a statement about `g`.

## What is discharged here, from the tag's own hypotheses

* `g` is **finite**: this is the first sentence of the source's proof, and it is
  `Stacks.AlgebraicGeometry.BirationalCurveFinite.isFinite_of_bijOn_genericPointsOne`, which
  needs exactly the bijection on the generic points of the one-dimensional components.
* the **four-term sequence** `0 ⟶ ker φ ⟶ 𝒪_X ⟶ g_*𝒪_{X'} ⟶ coker φ ⟶ 0` for
  `φ = 𝒪_X ⟶ g_*𝒪_{X'}`, broken at its coimage into two short exact sequences, together with the
  coherence of all four terms — the kernel and cokernel of a map of coherent modules on a
  locally Noetherian scheme are coherent ([Stacks, Tag 01Y0]), and `g_*𝒪_{X'}` is coherent
  because `g` is finite ([Stacks, Tag 01Y6]);
* the step the source spends its hypothesis on local rings on: **the kernel and the cokernel of
  `𝒪_X ⟶ g_*𝒪_{X'}` have supports of dimension `≤ 0`.** Over a generic point `y` of a
  one-dimensional component the fibre of `g` is the single point `z` that the bijection assigns
  to it, so the preimages of the open neighbourhoods of `y` are a neighbourhood basis of `z`
  (`Stacks.Topology.exists_mem_preimage_le_of_isClosedMap`, which is where properness of `g`
  enters as closedness); the assumed isomorphism `𝒪_{X,y} ≅ 𝒪_{X',z}` of local rings then makes
  the stalk of `φ` at `y` bijective, hence the stalks of its kernel and cokernel zero and `y`
  outside both supports. A closed subset of a scheme of dimension at most one containing no
  generic point of a one-dimensional component is a sober `T1` space, hence of dimension at most
  zero, so the supports satisfy the hypothesis of clause (5) of [Stacks, Tag 0AYT];
* the two **cohomology comparisons** along the finite — hence affine — morphism `g`, which are
  [Stacks, Tag 089W] in the form
  `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isAffineHom`:
  `χ(X, g_*𝒪_{X'}) = χ(X', 𝒪_{X'})` and `χ(X, g_*g^*ℰ) = χ(X', g^*ℰ)`.

## The projection formula at `g`

`AlgebraicGeometry.projectionFormula_iso_of_isFiniteLocallyFreeOfRank`, stated just above the
theorem below, proves the source's displayed equation `g_*g^*ℰ ≅ ℰ ⊗_{𝒪_X} g_*𝒪_{X'}`, the
projection formula ([Stacks, Tag 01E8], and at an affine morphism [Stacks, Tag 0FZE]) at `g`, for
`ℰ` finite locally free of rank `n`. It composes
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`
(`StacksFrontier/AlgebraicGeometry/ProjectionFormula/FiniteLocallyFree.lean`), which proves the
canonical map invertible for an arbitrary morphism of schemes as soon as the module on the
target is free of finite rank on each member of an open covering, with the pointwise
trivialisation that `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff`
(`StacksFrontier/AlgebraicGeometry/FiniteLocallyFreeRank/Sheaf.lean`) extracts from `ℰ`'s
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` hypothesis, and with the left unit
constraint of the sheaf tensor product (`Stacks.AffineProjectionFormula.structureUnitor`) to
remove the unit module `𝒪_{X'}` from the target.

## The attribute

`AlgebraicGeometry.curveDegree_pullback_eq_of_bijOn_genericPointsOne` carries the Tag 0AYU
attribute unconditionally. It states the "more generally" half of the tag with exactly the tag's
own hypotheses — the bijection on the generic points of the one-dimensional components, and the
isomorphisms of local rings at the corresponding points — and the projection formula, which the
source's proof uses, is proved rather than assumed.

**The `"birational"` half is not separately derived.** It is implied by the "more generally"
half, but deriving it in this repository's vocabulary needs
`Set.BijOn g (genericPointsOne X') (genericPointsOne X)` from
`AlgebraicGeometry.IsBirational g`, which is bijectivity on *all* generic points
(`StacksFrontier/AlgebraicGeometry/Morphisms/Birational/Basic.lean`, line 67), and the two differ by
the claim that `g` preserves the dimension of a component. Over a field that is the
transcendence-degree formula [Stacks, Tag 0A21], available as
`AlgebraicGeometry.topologicalKrullDim_eq_trdeg_residueField`
(`StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/Trdeg.lean`, line 96) only for an
irreducible *scheme*, so it would have to be read on
`Stacks.AlgebraicGeometry.ComponentDegrees.reducedComponent` and matched with the residue field of
`X` at the generic point; none of that is done.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.unitModule` and
  `AlgebraicGeometry.Scheme.Modules.pushforwardUnit`: `𝒪_X` and `g_*𝒪_{X'}`, read in
  `AlgebraicGeometry.Scheme.Modules`.
* `AlgebraicGeometry.Scheme.Modules.pushforwardUnitHom`: the canonical map
  `𝒪_X ⟶ g_*𝒪_{X'}` attached to a morphism of schemes.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `Stacks.Topology.exists_mem_preimage_le_of_isClosedMap`: at a one-point fibre of a closed map,
  the preimages of the open neighbourhoods of the image are a neighbourhood basis.
* `Scheme.Modules.shortExact_kernel_coimage` and `Scheme.Modules.shortExact_coimage_cokernel`: a
  morphism of modules on a scheme breaks into two short exact sequences at its coimage. This is
  the four-term sequence of the source in the shape `CurveDegreeInvariance/Basic.lean` consumes
  it.
* `Scheme.Modules.injective_stalkLinearMap_pushforwardUnitHom` and
  `Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom`: the stalk map of
  `𝒪_X ⟶ g_*𝒪_{X'}` at the image of a point where `g` induces an isomorphism of local rings is
  injective, and surjective as soon as that point has a one-point fibre and `g` is closed.
* `Scheme.Modules.notMem_supp_kernel_pushforwardUnitHom` and
  `Scheme.Modules.notMem_supp_cokernel_pushforwardUnitHom`: consequently that image point lies
  outside the supports of the kernel and of the cokernel.
* `topologicalKrullDim_le_zero_of_isClosed_of_forall_notMem_genericPointsOne` and
  `topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne`: a closed subset — in
  particular the support of a coherent module — of a scheme of dimension at most one which
  contains no generic point of a one-dimensional component has dimension at most zero.
* `projectionFormula_iso_of_isFiniteLocallyFreeOfRank`: **the projection formula
  [Stacks, Tag 01E8] at `g`**, for `ℰ` finite locally free of rank `n`.
* `curveDegree_pullback_eq_of_bijOn_genericPointsOne`: **[Stacks, Tag 0AYU]**, the "more
  generally" statement, `deg(g^*ℰ) = deg(ℰ)`, under the tag's own hypotheses `hbij` and `hstalk`.

## Implementation notes

The four-term sequence is broken at the **coimage** `coker(ker φ ⟶ 𝒪_X)` rather than at the
abelian image `ker(g_*𝒪_{X'} ⟶ coker φ)`. The two are isomorphic, but with the coimage both
sequences are cokernel presentations, so both exactness statements are instances of
`CategoryTheory.ShortComplex.exact_of_g_is_cokernel`; at the image the first sequence would need
the kernel of `𝒪_X ⟶ im φ` to be identified with `ker φ`.

Coherence of the three terms built from `φ` is obtained from [Stacks, Tag 01Y0] and not from the
subobject and quotient clauses of [Stacks, Tag 01Y1]: the latter ask for quasi-coherence of the
subobject or quotient as a separate hypothesis, which for an arbitrary submodule of `𝒪_X` is not
available.

**The stalk argument never compares a stalk of rings with a stalk of abelian groups.** The
support of a module is computed from the stalk of its presheaf of abelian groups, while the
hypothesis on local rings is about `AlgebraicGeometry.Scheme.Hom.stalkMap`, a morphism of
`CommRingCat`; the stalks of a presheaf in the two categories are colimits in different
categories and the repository has no comparison between them. Both halves of the stalk argument
therefore pass through **equalities of sections**: the local-ring map is used only to produce an
open on which two sections of `𝒪_{X'}` agree, or on which one vanishes, and the germ of abelian
groups is taken afterwards. `TopCat.Presheaf.germ_eq` is what turns an equality of germs into an
equality of sections over a smaller open, and the one-point-fibre lemma is what makes that
smaller open the preimage of an open of `X`.

Several applications below are written with `@` and explicit coherence or monomorphism arguments.
That is the style of `CurveDegreeInvariance/Basic.lean`, and it is forced: `Scheme.Modules` is a
`def` for a category of sheaves of modules, so instance search does not reliably cross between
the two spellings of `SheafOfModules.IsCoherent` or of `Mono` even when a proof is in context.
For the same reason `AlgebraicGeometry.Scheme.Modules.unitModule` and `pushforwardUnit` exist:
`(SheafOfModules.unit X.ringCatSheaf : X.Modules).presheaf` does not elaborate, because the
ascription does not change the head of the term's type.

## References

* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.BirationalCurveFinite
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Topology

/-- **At a one-point fibre of a closed map, the preimages of the open neighbourhoods of the image
are a neighbourhood basis.** For `f` closed with `f ⁻¹' {f x} ⊆ {x}`, every open neighbourhood `W`
of `x` contains the preimage of an open neighbourhood of `f x`, namely the complement of the
closed set `f '' Wᶜ`. -/
theorem exists_mem_preimage_le_of_isClosedMap {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (hcl : IsClosedMap f) (hfib : f ⁻¹' {f x} ⊆ {x}) (W : Opens X) (hx : x ∈ W) :
    ∃ U : Opens Y, f x ∈ U ∧ (Opens.map f).obj U ≤ W := by
  refine ⟨⟨(f '' (W : Set X)ᶜ)ᶜ, (hcl _ W.2.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨z, hz, hfz⟩
    exact hz ((hfib (Set.mem_preimage.mpr hfz)) ▸ hx)
  · intro z hz
    by_contra hzW
    exact hz ⟨z, hzW, rfl⟩

end Stacks.Topology

namespace AlgebraicGeometry

/-! ### The canonical map to the direct image of the structure sheaf -/

/-- The structure sheaf `𝒪_X`, read in `AlgebraicGeometry.Scheme.Modules`. The ascription is
what makes the projections of that category — its presheaf, and the stalk functor on it —
available on the term. -/
abbrev Scheme.Modules.unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The direct image `g_*𝒪_{X'}`, read in `AlgebraicGeometry.Scheme.Modules`. -/
abbrev Scheme.Modules.pushforwardUnit {X' X : Scheme.{u}} (g : X' ⟶ X) : X.Modules :=
  (Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule X')

/-- The canonical map `𝒪_X ⟶ g_*𝒪_{X'}` attached to a morphism of schemes `g : X' ⟶ X`: on
sections over an open `U` it is the comorphism `Γ(X, U) ⟶ Γ(X', g⁻¹U)` of `g`. -/
def Scheme.Modules.pushforwardUnitHom {X' X : Scheme.{u}} (g : X' ⟶ X) :
    Scheme.Modules.unitModule X ⟶ Scheme.Modules.pushforwardUnit g :=
  SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom

/-! ### Breaking a morphism of modules into two short exact sequences -/

section Sequences

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)

/-- The map from the coimage of `φ` to its target is annihilated by the projection to the
cokernel of `φ`: both become `φ ≫ coker.π φ = 0` after precomposing with the epimorphism
`M ⟶ coim φ`. -/
theorem Scheme.Modules.factorThruCoimage_comp_cokernel_π :
    Abelian.factorThruCoimage φ ≫ cokernel.π φ = 0 := by
  rw [← cancel_epi (Abelian.coimage.π φ), comp_zero, ← Category.assoc, Abelian.coimage.fac,
    cokernel.condition]

/-- **The left half of the four-term sequence of `φ`**: `0 ⟶ ker φ ⟶ M ⟶ coim φ ⟶ 0` is short
exact, the coimage being by definition the cokernel of `ker φ ⟶ M`. -/
theorem Scheme.Modules.shortExact_kernel_coimage :
    (ShortComplex.mk (kernel.ι φ) (Abelian.coimage.π φ) (by simp)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (kernel.ι φ))
  mono_f := inferInstance
  epi_g := inferInstance

/-- **The right half of the four-term sequence of `φ`**: `0 ⟶ coim φ ⟶ N ⟶ coker φ ⟶ 0` is short
exact. The projection `N ⟶ coker φ` is a cokernel of `coim φ ⟶ N` because it is a cokernel of
`φ`, which factors through it by the epimorphism `M ⟶ coim φ`. -/
theorem Scheme.Modules.shortExact_coimage_cokernel :
    (ShortComplex.mk (Abelian.factorThruCoimage φ) (cokernel.π φ)
      (Scheme.Modules.factorThruCoimage_comp_cokernel_π φ)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _
    (CokernelCofork.IsColimit.ofπ' _ (Scheme.Modules.factorThruCoimage_comp_cokernel_π φ)
      fun k hk =>
        ⟨cokernel.desc φ k (by rw [← Abelian.coimage.fac φ, Category.assoc, hk, comp_zero]),
          cokernel.π_desc _ _ _⟩)
  mono_f := inferInstance
  epi_g := inferInstance

end Sequences

/-! ### The stalk of the canonical map at a one-point fibre -/

section Stalk

open TopCat.Presheaf

variable {X' X : Scheme.{u}} (g : X' ⟶ X)

/-- The stalk map of `𝒪_X ⟶ g_*𝒪_{X'}` on the germ of a section `a` over `U` is the germ of the
comorphism `g.app U a`. -/
theorem Scheme.Modules.stalkLinearMap_pushforwardUnitHom_germ (x : X') (U : X.Opens)
    (hx : g.base x ∈ U) (a : Γ(X, U)) :
    stalkLinearMap (Scheme.Modules.unitModule X)
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))
        (Scheme.Modules.pushforwardUnitHom g) (g.base x)
        ((Scheme.Modules.unitModule X).presheaf.germ U (g.base x) hx a) =
      (Scheme.Modules.pushforwardUnit g).presheaf.germ U (g.base x) hx (g.app U a) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := Ab.{u}) U (g.base x) hx
    (Scheme.Modules.Hom.mapPresheaf (Scheme.Modules.pushforwardUnitHom g)) a

/-- **Injectivity of the stalk map of `𝒪_X ⟶ g_*𝒪_{X'}` at a point of the image.** A germ killed
by the map has a representative whose comorphism dies on a smaller open, which makes the
corresponding germ of `𝒪_{X'}` at `x` zero; injectivity of the local-ring map returns a smaller
open on which the representative itself vanishes. No hypothesis on the fibre is needed. -/
theorem Scheme.Modules.injective_stalkLinearMap_pushforwardUnitHom (x : X')
    (hinj : Function.Injective (g.stalkMap x)) :
    Function.Injective (stalkLinearMap (Scheme.Modules.unitModule X)
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))
      (Scheme.Modules.pushforwardUnitHom g) (g.base x)) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨U, hU, a, rfl⟩ :=
    (Scheme.Modules.unitModule X).presheaf.exists_germ_eq m
  have hm' : (Scheme.Modules.pushforwardUnit g).presheaf.germ U (g.base x) hU (g.app U a) = 0 :=
    (Scheme.Modules.stalkLinearMap_pushforwardUnitHom_germ g x U hU a).symm.trans hm
  obtain ⟨W, hW, iW1, iW2, heq⟩ :=
    (Scheme.Modules.pushforwardUnit g).presheaf.germ_eq (g.base x) hU hU (g.app U a) 0
      (hm'.trans (map_zero _).symm)
  have hres : g.app W (X.presheaf.map iW1.op a) = 0 :=
    (ConcreteCategory.congr_hom (g.naturality iW1.op) a).trans (heq.trans (map_zero _))
  have hz : X.presheaf.germ W (g.base x) hW (X.presheaf.map iW1.op a) = 0 :=
    hinj (((Scheme.Hom.germ_stalkMap_apply g W x hW _).trans
      (by rw [hres, map_zero])).trans (map_zero _).symm)
  obtain ⟨V, hV, iV1, iV2, heq2⟩ := X.presheaf.germ_eq (g.base x) hW hW
    (X.presheaf.map iW1.op a) 0 (hz.trans (map_zero _).symm)
  have key : (Scheme.Modules.unitModule X).presheaf.germ V (g.base x) hV
      ((Scheme.Modules.unitModule X).presheaf.map iV1.op
        ((Scheme.Modules.unitModule X).presheaf.map iW1.op a)) = 0 :=
    (congrArg (ConcreteCategory.hom
      ((Scheme.Modules.unitModule X).presheaf.germ V (g.base x) hV))
      (show (Scheme.Modules.unitModule X).presheaf.map iV1.op
          ((Scheme.Modules.unitModule X).presheaf.map iW1.op a) = 0 from
        heq2.trans (map_zero _))).trans (map_zero _)
  exact (((TopCat.Presheaf.germ_res_apply
    (Scheme.Modules.unitModule X).presheaf iV1 (g.base x) hV
      ((Scheme.Modules.unitModule X).presheaf.map iW1.op a)).trans
        (TopCat.Presheaf.germ_res_apply
          (Scheme.Modules.unitModule X).presheaf iW1 (g.base x)
            (iV1.le hV) a)).symm).trans key

/-- **Surjectivity of the stalk map of `𝒪_X ⟶ g_*𝒪_{X'}` at a one-point fibre of a closed map.**
A germ of `g_*𝒪_{X'}` at `g x` is represented by a section over `g⁻¹V`; surjectivity of the
local-ring map produces a section of `𝒪_X` over some `W` whose comorphism has the same germ at
`x`, hence agrees with it on an open `T ∋ x`, and
`Stacks.Topology.exists_mem_preimage_le_of_isClosedMap` shrinks `T` to the preimage of an open
neighbourhood of `g x`, where the two sections agree outright. -/
theorem Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom (x : X')
    (hcl : IsClosedMap g.base) (hfib : g.base ⁻¹' {g.base x} ⊆ {x})
    (hsurj : Function.Surjective (g.stalkMap x)) :
    Function.Surjective (stalkLinearMap (Scheme.Modules.unitModule X)
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf))
      (Scheme.Modules.pushforwardUnitHom g) (g.base x)) := by
  intro t
  obtain ⟨V, hV, a, rfl⟩ :=
    (Scheme.Modules.pushforwardUnit g).presheaf.exists_germ_eq t
  obtain ⟨s, hs⟩ := hsurj (X'.presheaf.germ (g ⁻¹ᵁ V) x hV a)
  obtain ⟨W, hW, r, rfl⟩ := X.presheaf.exists_germ_eq s
  rw [Scheme.Hom.germ_stalkMap_apply] at hs
  obtain ⟨T, hT, iT1, iT2, heq⟩ := X'.presheaf.germ_eq x hW hV (g.app W r) a hs
  obtain ⟨U0, hU0, hU0T⟩ :=
    Stacks.Topology.exists_mem_preimage_le_of_isClosedMap g.base x hcl hfib T hT
  have hUmem : g.base x ∈ U0 ⊓ W ⊓ V := ⟨⟨hU0, hW⟩, hV⟩
  have hUW : U0 ⊓ W ⊓ V ≤ W := le_trans inf_le_left inf_le_right
  have hUV : U0 ⊓ W ⊓ V ≤ V := inf_le_right
  have hAT : (g ⁻¹ᵁ (U0 ⊓ W ⊓ V)) ≤ T :=
    le_trans ((Opens.map g.base).map
      (homOfLE (le_trans inf_le_left inf_le_left : U0 ⊓ W ⊓ V ≤ U0))).le hU0T
  have heq' : restrictOpen (g.app W r) T iT1.le =
      restrictOpen (show Γ(X', g ⁻¹ᵁ V) from a) T iT2.le := heq
  have hsec : restrictOpen (g.app W r) (g ⁻¹ᵁ (U0 ⊓ W ⊓ V)) (hAT.trans iT1.le) =
      restrictOpen (show Γ(X', g ⁻¹ᵁ V) from a) (g ⁻¹ᵁ (U0 ⊓ W ⊓ V)) (hAT.trans iT2.le) := by
    rw [← restrict_restrict hAT iT1.le (g.app W r),
      ← restrict_restrict hAT iT2.le (show Γ(X', g ⁻¹ᵁ V) from a), heq']
  refine ⟨(Scheme.Modules.unitModule X).presheaf.germ (U0 ⊓ W ⊓ V)
    (g.base x) hUmem (restrictOpen r (U0 ⊓ W ⊓ V) hUW), ?_⟩
  refine (Scheme.Modules.stalkLinearMap_pushforwardUnitHom_germ g x (U0 ⊓ W ⊓ V) hUmem
    (restrictOpen r (U0 ⊓ W ⊓ V) hUW)).trans ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
    ((Scheme.Modules.pushforwardUnit g).presheaf.germ (U0 ⊓ W ⊓ V) (g.base x) hUmem))
      ((map_restrict g.c hUW r).trans hsec)) ?_
  exact germ_res_apply (Scheme.Modules.pushforwardUnit g).presheaf (homOfLE hUV)
    (g.base x) hUmem a

/-- A point where the stalk map of a morphism of modules is injective misses the support of its
kernel: the stalk functor preserves monomorphisms, so the stalk of the inclusion of the kernel is
a monomorphism, and it vanishes. -/
theorem Scheme.Modules.notMem_supp_kernel_of_injective_stalkLinearMap {Z : Scheme.{u}}
    {A B : Z.Modules} (f : A ⟶ B) (z : Z)
    (h : Function.Injective (stalkLinearMap A B f z)) :
    z ∉ _root_.SheafOfModules.supp (kernel f) := by
  have hmono : Mono ((Scheme.Modules.stalkFunctor Z z).map f) :=
    (ModuleCat.mono_iff_injective _).2 h
  have hmono2 : Mono ((Scheme.Modules.stalkFunctor Z z).map (kernel.ι f)) :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.mono_stalkFunctor_map _ z
  exact (Scheme.Modules.notMem_supp_iff_isZero_stalk _ z).2
    (@IsZero.of_mono_eq_zero _ _ _ _ _ _ hmono2
      (Scheme.Modules.stalkFunctor_map_kernel_ι_eq_zero f z hmono))

/-- **The kernel of `𝒪_X ⟶ g_*𝒪_{X'}` is not supported at the image of a point where `g` induces
an isomorphism of local rings.** -/
theorem Scheme.Modules.notMem_supp_kernel_pushforwardUnitHom (x : X')
    (hiso : IsIso (g.stalkMap x)) :
    g.base x ∉ _root_.SheafOfModules.supp (kernel (Scheme.Modules.pushforwardUnitHom g)) :=
  have _ := hiso
  Scheme.Modules.notMem_supp_kernel_of_injective_stalkLinearMap _ _
    (Scheme.Modules.injective_stalkLinearMap_pushforwardUnitHom g x
      (ConcreteCategory.bijective_of_isIso (g.stalkMap x)).1)

/-- **The cokernel of `𝒪_X ⟶ g_*𝒪_{X'}` is not supported at the image of a one-point fibre where
`g` induces an isomorphism of local rings**, for `g` a closed map. -/
theorem Scheme.Modules.notMem_supp_cokernel_pushforwardUnitHom (x : X')
    (hcl : IsClosedMap g.base) (hfib : g.base ⁻¹' {g.base x} ⊆ {x})
    (hiso : IsIso (g.stalkMap x)) :
    g.base x ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom g)) :=
  have _ := hiso
  (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel _ _).1
    (Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom g x hcl hfib
      (ConcreteCategory.bijective_of_isIso (g.stalkMap x)).2)

end Stalk

/-! ### Closed subsets avoiding the one-dimensional generic points -/

/-- **A closed subset of a scheme of dimension at most one which contains no generic point of a
one-dimensional irreducible component has dimension at most zero.** Every one of its points is
closed in the scheme, hence in the subset, so the subset is a sober `T1` space and its
irreducible closed subsets are its singletons. -/
@[ega "IV 5.2.4" "special case"]
theorem topologicalKrullDim_le_zero_of_isClosed_of_forall_notMem_genericPointsOne
    {X : Scheme.{u}} (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    {s : Set X} (hs : IsClosed s) (hsgen : ∀ x ∈ s, x ∉ genericPointsOne X) :
    topologicalKrullDim s ≤ 0 := by
  have : T1Space ↥s := ⟨fun x => by
    have hx : ({x} : Set ↥s) = Subtype.val ⁻¹' ({(x : X)} : Set X) := by
      ext y; simp [Subtype.ext_iff]
    rw [hx]
    exact (isClosed_singleton_of_notMem_genericPointsOne hdim (hsgen x.1 x.2)).preimage
      continuous_subtype_val⟩
  have : QuasiSober ↥s := hs.isClosedEmbedding_subtypeVal.quasiSober
  exact Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space

/-- **The support of a coherent module on a scheme of dimension at most one has dimension at most
zero as soon as it avoids the generic points of the one-dimensional components.** The support of a
module of finite type is closed, by [Stacks, Tag 056J]. -/
theorem topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne
    {X : Scheme.{u}} (hdim : topologicalKrullDim (X : Type u) ≤ 1) (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F)
    (hFgen : ∀ x ∈ genericPointsOne X, x ∉ _root_.SheafOfModules.supp F) :
    topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0 :=
  have : F.IsFiniteType := hF.isFiniteType
  topologicalKrullDim_le_zero_of_isClosed_of_forall_notMem_genericPointsOne hdim
    (_root_.SheafOfModules.isClosed_supp F) fun x hx hgen => hFgen x hgen hx

/-! ### Tag 0AYU at a morphism -/

/-- **The projection formula [Stacks, Tag 01E8] at `g`, for `ℰ` finite locally free of rank
`n`.** The source's displayed equation `g_*g^*ℰ ≅ ℰ ⊗_{𝒪_X} g_*𝒪_{X'}`.

`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff` turns the hypothesis on `E` into
a pointwise trivialisation `E|_V ≅ 𝒪_V^{⊕ n}` on a neighbourhood of every point of `X`, which
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`
(`ProjectionFormula/FiniteLocallyFree.lean`) turns into invertibility of the canonical map
`g_*𝒪_{X'} ⊗_{𝒪_X} ℰ ⟶ g_*(𝒪_{X'} ⊗_{𝒪_{X'}} g^*ℰ)`; composing with the left unit constraint
`Stacks.AffineProjectionFormula.structureUnitor` of the sheaf tensor product removes the unit
factor `𝒪_{X'}` on the right, landing on `g_*g^*ℰ ≅ g_*𝒪_{X'} ⊗_{𝒪_X} ℰ`, which is `hproj`'s
statement with the two tensor factors as the source displays them. -/
@[ega "0 5.4.10" "special case"]
def projectionFormula_iso_of_isFiniteLocallyFreeOfRank {X' X : Scheme.{u}} (g : X' ⟶ X)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)))).obj (E)) :
          X.Modules) ≅
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj E) := by
  have hpt : Scheme.Modules.IsFiniteLocallyFreeOfRank E n :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E n).mpr inferInstance
  have hH : ∀ x : X.carrier, ∃ (V : X.Opens) (_ : x ∈ V) (I : Type u) (_ : Finite I),
      Nonempty (Stacks.AffineProjectionFormula.openRestrictModule V E ≅
        SheafOfModules.free.{u} I) := by
    intro x
    obtain ⟨V, hV, ⟨ε⟩⟩ := hpt x
    exact ⟨V, hV, ULift.{u, 0} (Fin n), inferInstance, ⟨ε⟩⟩
  have hiso := Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree g
    (SheafOfModules.unit X'.ringCatSheaf) E hH
  exact (@asIso _ _ _ _ (Stacks.AffineProjectionFormula.projectionFormulaMap g.toLRSHom.toShHom
      (SheafOfModules.unit X'.ringCatSheaf) E) hiso) ≪≫
    (Scheme.Modules.pushforward g).mapIso
      (Stacks.AffineProjectionFormula.structureUnitor ((Scheme.Modules.pullback g).obj E))

/-- **[Stacks, Tag 0AYU], the "more generally" statement.** Let `k` be a field and let
`g : X' ⟶ X` be a morphism over `k` between schemes proper over `k` and of dimension at most one
which induces a bijection between the generic points of the one-dimensional irreducible
components of `X'` and those of `X`, and isomorphisms of local rings at the points of `X'`
involved. Let `ℰ` be finite locally free of constant rank `n` on `X`. Then

`deg(g^*ℰ) = deg(ℰ)`.

`hbij` and `hstalk` are the tag's own hypotheses — the bijection on the generic points of the
one-dimensional components and the isomorphisms of local rings at the corresponding points — and
the source's "more generally" clause implies its first, birational, sentence, which is not
separately derived here. The finiteness input [Stacks, Tag 02O6] over a field is not assumed: it
is `AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper`. The projection formula
[Stacks, Tag 01E8] at `g`, the source's displayed equation `g_*g^*ℰ ≅ ℰ ⊗_{𝒪_X} g_*𝒪_{X'}`, is
proved rather than assumed, by `projectionFormula_iso_of_isFiniteLocallyFreeOfRank` above.

The proof is the source's. The bijection on generic points makes `g` finite, so the cohomology of
`X'` is read on `X` through `g_*`; the isomorphisms of local rings make the kernel and the
cokernel of `𝒪_X ⟶ g_*𝒪_{X'}` vanish at the generic points of the one-dimensional components,
hence give them zero-dimensional support, so clause (5) of [Stacks, Tag 0AYT] applies at both;
and the computation of `CurveDegreeInvariance/Basic.lean` collapses the difference of the two
degrees to zero. -/
@[stacks 0AYU, sga "6 X 4.4" "special case"]
theorem curveDegree_pullback_eq_of_bijOn_genericPointsOne (k : Type u) [Field k]
    {X' X : Scheme.{u}} (p' : X' ⟶ Spec (.of k)) (p : X ⟶ Spec (.of k))
    [IsProper p'] [IsProper p]
    (hdimX' : topologicalKrullDim (X' : Type u) ≤ 1)
    (hdimX : topologicalKrullDim (X : Type u) ≤ 1)
    (g : X' ⟶ X) (hgOver : g ≫ p = p')
    (hbij : Set.BijOn g (genericPointsOne X') (genericPointsOne X))
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    (hstalk : ∀ z ∈ genericPointsOne X', IsIso (g.stalkMap z)) :
    @curveDegree k _ X' p' _ hdimX' ((Scheme.Modules.pullback g).obj E) n
        (isFiniteLocallyFreeOfRank_pullback g E n) =
      curveDegree k p hdimX E n := by
  subst hgOver
  have hFin : IsFinite g :=
    isFinite_of_bijOn_genericPointsOne k (g ≫ p) p hdimX' hdimX g rfl hbij
  have hProperG : IsProper g := isProper_of_comp_eq (f := g) (p := p) rfl
  have hcl : IsClosedMap g.base := g.isClosedMap
  have hnot : ∀ y ∈ genericPointsOne X,
      y ∉ _root_.SheafOfModules.supp (kernel (Scheme.Modules.pushforwardUnitHom g)) ∧
        y ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom g)) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hy
    exact ⟨Scheme.Modules.notMem_supp_kernel_pushforwardUnitHom g z (hstalk z hz),
      Scheme.Modules.notMem_supp_cokernel_pushforwardUnitHom g z hcl (fun w hw =>
        hbij.injOn (preimage_singleton_subset_genericPointsOne k (g ≫ p) p hdimX' g rfl hy hw) hz
          hw) (hstalk z hz)⟩
  have hNoe : IsNoetherian X := isNoetherian_of_isProper_over_field k p
  have hOX' : (SheafOfModules.unit X'.ringCatSheaf).IsCoherent := isCoherent_unit k (g ≫ p)
  have hOX : (SheafOfModules.unit X.ringCatSheaf).IsCoherent := isCoherent_unit k p
  have hE : SheafOfModules.IsCoherent E := isCoherent_of_isFiniteLocallyFreeOfRank k p E n
  have hgE : SheafOfModules.IsCoherent ((Scheme.Modules.pullback g).obj E) :=
    @isCoherent_of_isFiniteLocallyFreeOfRank k _ X' (g ≫ p) _ _ n
      (isFiniteLocallyFreeOfRank_pullback g E n)
  have hP : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite g _
  have hPE : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj E)) :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite g _
  have hKc : SheafOfModules.IsCoherent (kernel (Scheme.Modules.pushforwardUnitHom g)) :=
    @isCoherent_kernel X _ _ _ hOX hP (Scheme.Modules.pushforwardUnitHom g)
  have hQc : SheafOfModules.IsCoherent (cokernel (Scheme.Modules.pushforwardUnitHom g)) :=
    @isCoherent_cokernel X _ _ _ hOX hP (Scheme.Modules.pushforwardUnitHom g)
  have hJc :
      SheafOfModules.IsCoherent (Abelian.coimage (Scheme.Modules.pushforwardUnitHom g)) :=
    @isCoherent_cokernel X _ _ _ hKc hOX (kernel.ι (Scheme.Modules.pushforwardUnitHom g))
  obtain ⟨hTK, hKeq⟩ := @exists_eulerCharacteristic_tensorSheaf_eq_rank_mul X k _ p _
    (kernel (Scheme.Modules.pushforwardUnitHom g)) hKc
    (topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdimX _ hKc
      fun y hy => (hnot y hy).1) E n _
  obtain ⟨hTQ, hQeq⟩ := @exists_eulerCharacteristic_tensorSheaf_eq_rank_mul X k _ p _
    (cokernel (Scheme.Modules.pushforwardUnitHom g)) hQc
    (topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdimX _ hQc
      fun y hy => (hnot y hy).2) E n _
  have hmain := eulerCharacteristic_tensorSheaf_sub_eq_curveDegree_of_shortExact_pair k p hdimX
    E n _ _ _ _ hKc hJc hQc hP hE hOX _ _ _
    (Scheme.Modules.shortExact_kernel_coimage (Scheme.Modules.pushforwardUnitHom g)) _ _ _
    (Scheme.Modules.shortExact_coimage_cokernel (Scheme.Modules.pushforwardUnitHom g))
    (fun G hG m => cohomologyFiniteDimensionalOverField_of_isProper k X p inferInstance G hG m)
    hKeq hQeq
  have hPEcoh : SheafOfModules.IsCoherent ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
      (((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)))).obj (E))) :=
    @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ E hP hE
  have hbase : @eulerCharacteristic k _ X p _
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)) hP =
      @eulerCharacteristic k _ X' (g ≫ p) _ (SheafOfModules.unit X'.ringCatSheaf) hOX' :=
    eulerCharacteristic_pushforward_of_isAffineHom k g p _ hOX' hP
  have htens : @eulerCharacteristic k _ X p _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
        (((Scheme.Modules.pushforward g).obj (SheafOfModules.unit X'.ringCatSheaf)))).obj (E)))
        hPEcoh =
      @eulerCharacteristic k _ X' (g ≫ p) _ ((Scheme.Modules.pullback g).obj E) hgE := by
    have hgEq :=
      @_root_.isQuasicoherent_of_isCoherent _ _ _ ((Scheme.Modules.pullback g).obj E) hgE
    rw [@eulerCharacteristic_eq_of_iso k _ X p _ _ _ hPEcoh hPE
      (projectionFormula_iso_of_isFiniteLocallyFreeOfRank g E n)]
    exact @eulerCharacteristic_pushforward_of_isAffineHom k _ X' X g _ p _ _
      ((Scheme.Modules.pullback g).obj E) hgEq hgE hPE
  have hdeg' := @curveDegree_eq_eulerCharacteristic_sub k _ X' (g ≫ p) _ hdimX'
    ((Scheme.Modules.pullback g).obj E) n (isFiniteLocallyFreeOfRank_pullback g E n) hgE hOX'
  rw [hdeg', ← htens, ← hbase]
  exact hmain

end AlgebraicGeometry

end
