module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Descent
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Functorial
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjDirected

/-!
# Transition data for the twisting sheaves of a relative projective spectrum

Let `s` be a relative `Proj` situation. Its relative projective spectrum is glued from the
absolute projective spectra `Proj 𝒜(W)` of the graded section rings over the affine opens `W` of
the base, and each chart carries the absolute twisting sheaf `𝒪(n)`. Glueing those into
`𝒪_{Proj(s)}(n)` needs comparison data for the chart twists, and this file constructs it.

For an inclusion `W ≤ W'` of affine opens of the base the comparison morphism of charts
`r : Proj 𝒜(W) ⟶ Proj 𝒜(W')` carries the canonical twist comparison
`θ : r^* 𝒪_{Proj 𝒜(W')}(n) ⟶ 𝒪_{Proj 𝒜(W)}(n)`, which is an isomorphism. Pushing its adjoint
transpose forward along the chart over `W'` and composing with the identification of iterated
pushforwards gives a morphism of sheaves of modules on the relative `Proj` from the pushforward
of the chart twist over `W'` to the pushforward of the chart twist over `W`. On sections over an
open lying inside the chart over `W` it is bijective, so it inverts to the required linear
equivalence, and it is functorial in the inclusion because the twist comparison is. That is
exactly a directed transition datum, and hence — by descent along the locally directed cover by
charts — a pairwise one and the sheaf `𝒪_{Proj(s)}(n)` itself.

## Main definitions

* `Stacks.RelativeProj.Situation.twistPushforwardMap`: the comparison of the pushed-forward chart
  twists attached to an inclusion of affine opens of the base.
* `Stacks.RelativeProj.Situation.twistTransEquiv`: that comparison inverted on sections over an
  open lying in the smaller chart.
* `Stacks.RelativeProj.Situation.directedTwistTransition`: **directed transition data for the
  chart twists of an arbitrary relative projective spectrum.**
* `Stacks.RelativeProj.Situation.twistTransition`: the pairwise transition datum it descends to.
* `Stacks.RelativeProj.Situation.twistSheaf`: `𝒪_{Proj(s)}(n)`, with no carried hypothesis.

## Main results

* `Stacks.RelativeProj.Situation.bijective_twistPushforwardMap_app`: the comparison is bijective
  on sections over an open of the relative `Proj` lying in the chart over the smaller affine
  open.
* `Stacks.RelativeProj.Situation.twistPushforwardMap_comp_apply` and
  `Stacks.RelativeProj.Situation.twistPushforwardMap_naturality`: the comparisons are functorial
  in the inclusion and commute with restriction.
* `Stacks.RelativeProj.Situation.twistSheafChartIso`: `𝒪_{Proj(s)}(n)` restricts on the chart
  over `W` to the absolute twisting sheaf `𝒪(n)` of `Proj 𝒜(W)`.

## Implementation notes

The comparison is assembled from `Stacks.ProjTwistComparison.pushforwardTwistMap`, the adjoint
transpose of `θ`, rather than from `θ` itself: an equation between `θ` for a composite of graded
ring homomorphisms and the composite of the two `θ`s cannot be stated without transporting along
`AlgebraicGeometry.Proj.map_comp`, whereas on sections the comparison of a composite *is* the
composite of the comparisons. The only transport that survives is a restriction along the
equality of opens `chart W ⁻¹ᵁ V = r ⁻¹ᵁ (chart W' ⁻¹ᵁ V)`, supplied by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, and it is an isomorphism on sections.

Functoriality is proved pointwise in the module fibres. The two points of `Proj 𝒜(W'')` at which
the two sides read a section — the one below a point of `Proj 𝒜(W)` for the restriction map of
`W ≤ W''`, and the one reached in two steps — agree only propositionally, so
`Stacks.ProjTwistComparison.fibreMap_comp_of_eq` takes the factorization of the graded
restriction map as a hypothesis and substitutes it away, after which the two points agree
definitionally and the membership proofs are identified by proof irrelevance.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjTwistComparison Stacks.SheafOfModules

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.ProjTwistComparison

variable {A B C : Type u} {σ τ ρ : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

/-- **The fibre comparison of a graded ring homomorphism that factors is the composite of the
fibre comparisons of its factors**, read on a dependent family of module fibres indexed by the
points of `Proj 𝒜` lying below the points of `Proj 𝒞`. -/
theorem fibreMap_comp_of_eq (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ) (ψ : ℬ →+*ᵍ 𝒞)
    (hψ : 𝒞₊ ≤ ℬ₊.map ψ) (χ : 𝒜 →+*ᵍ 𝒞) (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (hc : χ = ψ.comp φ)
    (x : ProjectiveSpectrum 𝒞) {P : ProjectiveSpectrum 𝒜 → Prop}
    (f : ∀ q : Subtype P, ModuleFiber (M := A) 𝒜 q.1)
    (h₁ : P (ProjectiveSpectrum.comapFun χ hχ x))
    (h₂ : P (ProjectiveSpectrum.comapFun φ hφ (ProjectiveSpectrum.comapFun ψ hψ x))) :
    fibreMap χ hχ x (f ⟨_, h₁⟩)
      = fibreMap ψ hψ x (fibreMap φ hφ (ProjectiveSpectrum.comapFun ψ hψ x) (f ⟨_, h₂⟩)) := by
  subst hc
  exact fibreMap_comp φ hφ ψ hψ hχ x (f ⟨_, h₁⟩)

end Stacks.ProjTwistComparison

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (n : ℤ)

/-- Restriction of sections along an equality of opens is bijective. -/
private theorem bijective_presheaf_map_eqToHom {Y : Scheme.{u}} (M : Y.Modules)
    {P Q : Y.Opens} (e : P = Q) :
    Function.Bijective (M.presheaf.map (eqToHom e).op) := by
  subst e
  simpa using Function.bijective_id

/-- The part of the chart over `W` lying over an open `V` of the relative projective spectrum is
the preimage, under the comparison morphism of charts, of the part of the chart over `W'` lying
over `V`. -/
theorem preimage_relativeProjChart_eq {W W' : s.base.affineOpens} (h : W ≤ W')
    (V : (relativeProj s).Opens) :
    relativeProjChart s W ⁻¹ᵁ V =
      projInclusionMap s W.1 W'.1 h W.2 W'.2 ⁻¹ᵁ (relativeProjChart s W' ⁻¹ᵁ V) :=
  congrArg (fun f => f ⁻¹ᵁ V) (relativeProjChart_transition s h).symm

/-- The comparison morphism of charts commutes with the two charts on points. -/
private theorem relativeProjChart_projInclusionMap_apply {W W' : s.base.affineOpens} (h : W ≤ W')
    (z : AlgebraicGeometry.Proj (s.sectionRingGrading W.1)) :
    relativeProjChart s W' (projInclusionMap s W.1 W'.1 h W.2 W'.2 z)
      = relativeProjChart s W z := by
  rw [← Scheme.Hom.comp_apply, relativeProjChart_transition s h]

/-- The comparison morphism of charts carries a point of the chart over `W` lying over an open
`V` of the relative projective spectrum to a point of the chart over `W'` lying over `V`. -/
theorem comapFun_gradedSectionRestriction_mem {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (x : relativeProjChart s W ⁻¹ᵁ V) :
    ProjectiveSpectrum.comapFun (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) x.1
      ∈ relativeProjChart s W' ⁻¹ᵁ V := by
  show relativeProjChart s W' (projInclusionMap s W.1 W'.1 h W.2 W'.2 x.1) ∈ V
  rw [relativeProjChart_projInclusionMap_apply]
  exact x.2

/-- **The comparison of the pushed-forward chart twists attached to an inclusion `W ≤ W'` of
affine opens of the base**: the adjoint transpose of the canonical twist comparison across the
comparison morphism of charts, pushed forward along the chart over `W'`. -/
def twistPushforwardMap {W W' : s.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.pushforward (relativeProjChart s W')).obj (twistChart s n W') ⟶
      (Scheme.Modules.pushforward (relativeProjChart s W)).obj (twistChart s n W) :=
  (Scheme.Modules.pushforward (relativeProjChart s W')).map
      (pushforwardTwistMap (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) n) ≫
    (Scheme.Modules.pushforwardComp
        (projInclusionMap s W.1 W'.1 h W.2 W'.2) (relativeProjChart s W')).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (relativeProjChart_transition s h)).hom.app _

/-- On sections over an open `V` of the relative projective spectrum, the comparison is the twist
comparison on sections over the part of the chart over `W'` lying over `V`, followed by the
restriction along the identification of opens of the chart over `W`. -/
theorem twistPushforwardMap_apply {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W') (twistChart s n W') V)) :
    ((twistPushforwardMap s n h).val.app (op V)).hom y =
      (twistChart s n W).presheaf.map (eqToHom (preimage_relativeProjChart_eq s h V)).op
        (sectionsMap (gradedSectionRestriction s W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) n
          (relativeProjChart s W' ⁻¹ᵁ V) y) := rfl

/-- The value of the comparison at a point of the chart over `W`: the fibre comparison of the
graded restriction map, applied to the value of the section at the point below. -/
theorem twistPushforwardMap_val {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W') (twistChart s n W') V))
    (x : relativeProjChart s W ⁻¹ᵁ V) :
    (((twistPushforwardMap s n h).val.app (op V)).hom y).1 x
      = fibreMap (gradedSectionRestriction s W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) x.1
          (y.1 ⟨_, comapFun_gradedSectionRestriction_mem s h x⟩) := rfl

/-- **The comparison is bijective on sections over an open of the relative projective spectrum
lying in the chart over `W`**, because over such an open the twist comparison attached to the
inclusion is bijective on sections. -/
theorem bijective_twistPushforwardMap_app {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange) :
    Function.Bijective ((twistPushforwardMap s n h).val.app (op V)).hom := by
  have hfun : ⇑((twistPushforwardMap s n h).val.app (op V)).hom =
      (fun z => (twistChart s n W).presheaf.map
          (eqToHom (preimage_relativeProjChart_eq s h V)).op z) ∘
        sectionsMap (gradedSectionRestriction s W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2) n
          (relativeProjChart s W' ⁻¹ᵁ V) :=
    funext (twistPushforwardMap_apply s n h)
  rw [hfun]
  refine Function.Bijective.comp (bijective_presheaf_map_eqToHom _ _) ?_
  refine bijective_sectionsMap_gradedSectionRestriction s h W.2 W'.2 n _ fun x => ?_
  obtain ⟨z, hz⟩ := hV x.2
  refine ⟨z, (relativeProjChart s W').isOpenEmbedding.injective ?_⟩
  exact (relativeProjChart_projInclusionMap_apply s h z).trans hz

/-- **The comparisons are functorial in the inclusion**: the comparison attached to `W ≤ W''` is
the comparison attached to `W' ≤ W''` followed by the one attached to `W ≤ W'`. -/
theorem twistPushforwardMap_comp_apply {W W' W'' : s.base.affineOpens} (h : W ≤ W')
    (h' : W' ≤ W'') {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W'') (twistChart s n W'') V)) :
    ((twistPushforwardMap s n (h.trans h')).val.app (op V)).hom y
      = ((twistPushforwardMap s n h).val.app (op V)).hom
          (((twistPushforwardMap s n h').val.app (op V)).hom y) := by
  refine Subtype.ext (funext fun x => ?_)
  exact fibreMap_comp_of_eq (gradedSectionRestriction s W'.1 W''.1 h')
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W''.1 h' W'.2 W''.2)
    (gradedSectionRestriction s W.1 W'.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
    (gradedSectionRestriction s W.1 W''.1 (h.trans h'))
    (irrelevant_le_map_gradedSectionRestriction s W.1 W''.1 (h.trans h') W.2 W''.2)
    (gradedSectionRestriction_comp s W.1 W'.1 W''.1 h h') x.1 y.1
    (comapFun_gradedSectionRestriction_mem s (h.trans h') x)
    (comapFun_gradedSectionRestriction_mem s h' ⟨_, comapFun_gradedSectionRestriction_mem s h x⟩)

/-- **The comparisons commute with the restriction maps** of the pushed-forward chart twists. -/
theorem twistPushforwardMap_naturality {W W' : s.base.affineOpens} (h : W ≤ W')
    {V U : (relativeProj s).Opens} (hUV : U ≤ V)
    (y : ToType (openSections (relativeProjChart s W') (twistChart s n W') V)) :
    ((twistPushforwardMap s n h).val.app (op U)).hom
        (((Scheme.Modules.pushforward (relativeProjChart s W')).obj
          (twistChart s n W')).val.map (homOfLE hUV).op y)
      = ((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (twistChart s n W)).val.map (homOfLE hUV).op
          (((twistPushforwardMap s n h).val.app (op V)).hom y) :=
  PresheafOfModules.naturality_apply (twistPushforwardMap s n h).val (homOfLE hUV).op y

/-- The comparison of the sections of the chart twists over `W` and over `W'` on an open `V` of
the relative projective spectrum lying in the chart over `W`, linear over the functions on `V`:
the inverse of `Stacks.RelativeProj.Situation.twistPushforwardMap` there. -/
def twistTransEquiv {W W' : s.base.affineOpens} (h : W ≤ W') {V : (relativeProj s).Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange) :
    openSections (relativeProjChart s W) (twistChart s n W) V
      ≃ₗ[ToType ((relativeProj s).ringCatSheaf.obj.obj (op V))]
      openSections (relativeProjChart s W') (twistChart s n W') V :=
  (LinearEquiv.ofBijective ((twistPushforwardMap s n h).val.app (op V)).hom
    (bijective_twistPushforwardMap_app s n h hV)).symm

/-- The comparison undoes the linear equivalence it was inverted from. -/
theorem twistPushforwardMap_twistTransEquiv {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (t : ToType (openSections (relativeProjChart s W) (twistChart s n W) V)) :
    ((twistPushforwardMap s n h).val.app (op V)).hom (twistTransEquiv s n h hV t) = t :=
  (LinearEquiv.ofBijective _ (bijective_twistPushforwardMap_app s n h hV)).apply_symm_apply t

/-- **Directed transition data for the chart twists of a relative projective spectrum.** For each
inclusion `W ≤ W'` of affine opens of the base it is the canonical twist comparison across the
comparison morphism of charts, inverted on sections over the opens lying in the chart over
`W`. -/
def directedTwistTransition : DirectedTwistTransition s n where
  trans := fun {_ _} h {_} hV => twistTransEquiv s n h hV
  trans_map := by
    intro W W' h V U hV hUV t
    refine (bijective_twistPushforwardMap_app s n h (hUV.trans hV)).1 ?_
    refine (twistPushforwardMap_twistTransEquiv s n h (hUV.trans hV) _).trans
      ((twistPushforwardMap_naturality s n h hUV _).trans (congrArg
        (fun z => ((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (twistChart s n W)).val.map (homOfLE hUV).op z)
        (twistPushforwardMap_twistTransEquiv s n h hV t))).symm
  trans_trans := by
    intro W W' W'' h h' V hV t
    refine (bijective_twistPushforwardMap_app s n (h.trans h') hV).1 ?_
    rw [twistPushforwardMap_twistTransEquiv s n (h.trans h') hV,
      twistPushforwardMap_comp_apply s n h h',
      twistPushforwardMap_twistTransEquiv s n h'
        (hV.trans (opensRange_relativeProjChart_mono s h)),
      twistPushforwardMap_twistTransEquiv s n h hV]

/-- **Transition data for the chart twists of a relative projective spectrum**, obtained from the
directed datum by descent along the locally directed cover by charts. -/
def twistTransition : TwistTransition s n :=
  (directedTwistTransition s n).toTwistTransition

/-- **The `n`-th twisting sheaf `𝒪_{Proj(s)}(n)` of a relative projective spectrum**, glued from
the absolute twisting sheaves of its charts. -/
def twistSheaf : (relativeProj s).Modules := Situation.twist (twistTransition s n)

/-- `𝒪_{Proj(s)}(n)` restricts on the chart over `W` to the absolute twisting sheaf `𝒪(n)` of
`Proj 𝒜(W)`. -/
def twistSheafChartIso (W : s.base.affineOpens) :
    (twistSheaf s n).restrict (relativeProjChart s W) ≅ twistChart s n W :=
  Situation.twistChartIso (twistTransition s n) W

/-- The inverse of the comparison on sections is the comparison of pushed-forward chart twists
itself: `twistTransEquiv` is defined by inverting it. -/
theorem twistTransEquiv_symm_apply {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (y : ToType (openSections (relativeProjChart s W') (twistChart s n W') V)) :
    (twistTransEquiv s n h hV).symm y = ((twistPushforwardMap s n h).val.app (op V)).hom y :=
  rfl

/-- **Reading a section of `𝒪_{Proj(s)}(n)` on the chart over a smaller affine open of the base
is the comparison of the pushed-forward chart twists.** For `W ≤ W'` and an open `V` lying in the
chart over `W`, the sections of `𝒪_{Proj(s)}(n)` over `V` read on the chart over `W'` and then
transported along `Stacks.RelativeProj.Situation.twistPushforwardMap` are the same sections read
on the chart over `W` directly.

This is the glued transition datum evaluated at an inclusion of charts, which
`Stacks.RelativeProj.Situation.DirectedTwistTransition.toTwistTransition_trans_eq_trans_symm`
identifies with the directed datum it was descended from. -/
theorem twistPushforwardMap_twistSectionsIso {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (x : ToType ((twistSheaf s n).val.obj (op V))) :
    ((twistPushforwardMap s n h).val.app (op V)).hom
        ((twistSectionsIso (twistTransition s n) W'
          (hV.trans (opensRange_relativeProjChart_mono s h))).hom x)
      = (twistSectionsIso (twistTransition s n) W hV).hom x :=
  (((directedTwistTransition s n).toTwistTransition_trans_eq_trans_symm h hV _).symm).trans
    ((twistGlueData (twistTransition s n)).trans_chartSectionsIso W' W
      (hV.trans (opensRange_relativeProjChart_mono s h)) hV x)

end Stacks.RelativeProj.Situation

end
