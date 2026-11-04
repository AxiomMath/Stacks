module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableChartSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicInvertible
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# The system `(𝓛ₙ)` of the non-algebraizable example is an invertible object of `Coh(U, I𝒪_U)`

For `A = k[x,y][[t]]`, `I = (t)` and `U` the punctured spectrum of `A`, the family `(𝓛ₙ)` of
[Stacks, Tag 0EHE] is the diagram
`Stacks.Algebraization.NonAlgebraizableExample.levelSystem : ℕᵒᵖ ⥤ U.Modules`. Three of the four
inputs of `Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker` are supplied by the module
`NonAlgebraizableLevelSystem` of this directory; this file supplies the fourth, which is the
computation of the kernel of each transition map over the affine opens `D(hg)` of `U`, and
assembles the object of `Coh(U, I𝒪_U)` together with its invertibility.

The kernel computation has two halves. The inclusion `I(V)^{n+1} 𝓛ₙ₊₂(V) ⊆ ker` holds because the
transition map is `Γ(U, V)`-linear and its target is annihilated by `(I𝒪_U)^{n+1}`. The reverse
inclusion is the chartwise computation
`Stacks.Algebraization.NonAlgebraizableExample.ker_chartReduction` — the kernel of
`A_r/t^{n+2}A_r → A_r/t^{n+1}A_r` is `t^{n+1}A_r/t^{n+2}A_r` — carried along two trivializations:
`Stacks.Algebraization.NonAlgebraizableExample.chartLinearEquiv_levelTransition` turns the
transition map into the map of functions induced by the closed immersion of punctured spectra,
and `Stacks.Algebraization.NonAlgebraizableExample.chartOpenEquiv` turns that map of functions
into the reduction of chart rings.

The one identity that joins the two halves is
`Stacks.Algebraization.NonAlgebraizableExample.appLE_levelStructureMap_chartOpenEquiv`: the two
routes by which an element of `A` reaches the sections of `𝒪` over a chart of the punctured
spectrum of `A/tᵐA` — restrict it to `V ⊆ U` and pull it back along the structure map, or reduce
it modulo `tᵐ` and restrict it to the chart — agree. The first route is the one the ideal
`(I𝒪_U)(V)` is described by, the second is the one the chart rings are described by, so this is
what turns `t^{n+1}` in the chart ring into `t^{n+1}` in `I(V)^{n+1}`.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.levelCoherentAdicSystem` — the family `(𝓛ₙ)` as
  an object of `Coh(U, I𝒪_U)`.

## Main results

* `Stacks.Algebraization.ker_app_eq_idealPower_smul_top` — the shape in which a sectionwise
  kernel is identified with `I(V)ⁿ M(V)`: the easy inclusion is annihilation of the target, so
  only the other one has to be supplied.
* `Stacks.Algebraization.NonAlgebraizableExample.appLE_levelStructureMap_chartOpenEquiv` — the
  two routes from `A` into the sections over a chart agree.
* `Stacks.Algebraization.NonAlgebraizableExample.app_levelOpenMap_appLE_ι_chartOpenEquiv` — on
  the sections over an open whose image is the basic open `D(r̄)`, the closed immersion of
  punctured spectra induces the reduction `A_r/t^{m+1}A_r → A_r/tᵐA_r`.
* `Stacks.Algebraization.NonAlgebraizableExample.ker_app_levelSystem_map_succ` — the kernel of
  each transition map of the system over an affine open `D(hg)` is `I(V)^{n+1} 𝓛ₙ₊₂(V)`. This is
  the hypothesis `hker` of `Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker`.
* `Stacks.Algebraization.NonAlgebraizableExample.isCoherentAdicSystem_levelSystem` — the system
  `(𝓛ₙ)` lies in `Coh(U, I𝒪_U)`.
* `Stacks.Algebraization.NonAlgebraizableExample.isInvertibleAdic_levelCoherentAdicSystem` — that
  object is invertible.

## Implementation notes

Two general lemmas are proved first because the `appLE` calculus needs them.
`AlgebraicGeometry.Scheme.Hom.appLE_congr_hom` transports `AlgebraicGeometry.Scheme.Hom.appLE`
across an equality of morphisms; that is why
`StacksFrontier/AlgebraicGeometry/Pushout/FlatSectionsDescent.lean` is imported here, far from its
subject. It is proved there by `subst`, and a `rw` cannot replace it, because the proof argument
of an `appLE` written with `le_top` has type `W ≤ ⊤` where the declaration asks for
`W ≤ f ⁻¹ᵁ ⊤`, and the two differ by an unfolding `rw`'s own type-correctness check does not
perform. For the same reason
`Stacks.Algebraization.NonAlgebraizableExample.tSection_mem_idealOnOpen` takes that proof as a
hypothesis rather than writing `le_top` in its statement: the hypothesis then carries the type
`AlgebraicGeometry.Scheme.Opens.ι_appLE` has to match.
`AlgebraicGeometry.Scheme.Opens.bijective_appLE_ι` says that restriction along the inclusion of
an open into the image of a smaller one is bijective when the two images agree, which is how the
sections over an open of the punctured spectrum are identified with a chart ring: for a general
open `P` with `ι ''ᵁ P = D(r̄)` there is no named ring equivalence — the ones that exist,
`levelChartRingEquiv` and `levelOverlapRingEquiv`, are for the charts and their overlap — so the
identification is used in the composite form `appLE ∘ chartOpenEquiv` and its bijectivity is this
lemma.

The kernel statements are proved through `Stacks.Algebraization.ker_app_eq_idealPower_smul_top`,
over a *variable* scheme, rather than inline on `U`. Over `U = (situation k).U.toScheme` the two
spellings of the ring of sections — `Γ(U, V)` as `AlgebraicGeometry.Scheme.presheaf` and the ring
a `ModuleCat` morphism of `U.Modules` is stated over, `AlgebraicGeometry.Scheme.ringCatSheaf` —
are equal by `rfl` but not type-correct against each other at `implicit` transparency, so
`LinearMap.mem_ker` and `map_smul` fail to elaborate there. Over a variable scheme they do not,
and the statement is then instantiated at `U`.

Invertibility of the object is `isInvertibleModule_levelModule` carried along the isomorphism of
`Stacks.Algebraization.NonAlgebraizableExample.exists_subschemeIso_levelOpen` by
`AlgebraicGeometry.Scheme.isInvertibleModule_pushforward_of_isIso`, which is the direct image
along an isomorphism read as an inverse image
(`AlgebraicGeometry.Scheme.Modules.pushforwardInvIsoPullback`) followed by [Stacks, Tag 0B8L]
(`Stacks.Modules.isInvertible_pullback`). The direct-image identification
`i_* (e_* 𝓛ₙ) ≅ 𝓛ₙ` on `U` is the same composite of
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` as
`Stacks.Algebraization.NonAlgebraizableExample.levelPushforwardIso`.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace AlgebraicGeometry.Scheme

/-- **Restriction between two opens each contained in the other is bijective.** The two
restriction maps compose to the identity in both orders, any two morphisms of opens with the same
source and target being equal. -/
public theorem bijective_presheaf_map_homOfLE {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V)
    (h' : V ≤ W) : Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  have : IsIso (homOfLE h).op := ⟨(homOfLE h').op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact ConcreteCategory.bijective_of_isIso (X.presheaf.map (homOfLE h).op)

/-- **The sections of an open subscheme over an open with a given image.** For an open `W` of the
open subscheme `U` whose image in `X` is the open `V`, the map from the sections over `V` to the
sections over `W` induced by the inclusion `U ⟶ X` is bijective: it is the restriction from `V` to
the image of `W`, and the two agree. -/
public theorem Opens.bijective_appLE_ι {X : Scheme.{u}} (U V : X.Opens) (W : U.toScheme.Opens)
    (e : W ≤ U.ι ⁻¹ᵁ V) (h : V ≤ U.ι ''ᵁ W) :
    Function.Bijective (U.ι.appLE V W e).hom := by
  rw [Scheme.Opens.ι_appLE U V W e]
  exact bijective_presheaf_map_homOfLE _ h

/-- **The direct image of an invertible module along an isomorphism of schemes is invertible.**
The direct image along the inverse of an isomorphism is its inverse image
(`AlgebraicGeometry.Scheme.Modules.pushforwardInvIsoPullback`), and the inverse image of an
invertible module is invertible (`Stacks.Modules.isInvertible_pullback`). -/
@[stacks 0B8L "the direct image of an invertible module along an isomorphism"]
public theorem isInvertibleModule_pushforward_of_isIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (L : Y.Modules) (hL : Stacks.Ample.IsInvertibleModule Y L) :
    Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pushforward e.inv).obj L) := by
  have := hL
  have := Stacks.Modules.isInvertible_pullback e.hom L
  exact Stacks.SheafOfModules.isInvertible_of_iso X.presheaf _
    (Scheme.Modules.pushforwardInvIsoPullback e L).symm

end AlgebraicGeometry.Scheme

namespace Stacks.Algebraization

/-- **A sectionwise kernel is `Iⁿ M` once the hard inclusion is known.** For a morphism
`p : M ⟶ N` whose target is annihilated by `Iⁿ`, the kernel of `p` on the sections over an affine
open `V` contains `I(V)ⁿ M(V)` automatically, `p` being `Γ(X, V)`-linear, so the identification of
the two reduces to the inclusion asked for as the hypothesis `hle`. -/
public theorem ker_app_eq_idealPower_smul_top {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} (p : M ⟶ N) (V : X.affineOpens)
    (hann : idealPowerMultiple I n N = ⊥)
    (hle : ∀ s : Γ(M, V), (p.val.app (op (V : X.Opens))).hom s = 0 →
      s ∈ I.ideal V ^ n • (⊤ : Submodule Γ(X, V) Γ(M, V))) :
    LinearMap.ker (p.val.app (op (V : X.Opens))).hom =
      I.ideal V ^ n • (⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  refine le_antisymm (fun s hs => hle s hs) (Submodule.smul_le.mpr fun r hr x _ => ?_)
  change ((p.val.app (op (V : X.Opens))).hom) (r • x) = 0
  refine (LinearMap.map_smul ((p.val.app (op (V : X.Opens))).hom) r x).trans ?_
  exact (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated I n N).mp hann V r hr _

/-- **A sectionwise kernel over an open where the source vanishes.** Both the kernel and
`I(V)ⁿ M(V)` are submodules of a module with one element, hence equal. -/
public theorem ker_app_eq_idealPower_smul_top_of_subsingleton {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules} (p : M ⟶ N) (V : X.affineOpens)
    (hM : Subsingleton Γ(M, V)) :
    LinearMap.ker (p.val.app (op (V : X.Opens))).hom =
      I.ideal V ^ n • (⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  refine le_antisymm (fun x _ => ?_) (fun x _ => ?_) <;>
    rw [hM.elim x 0] <;> exact Submodule.zero_mem _

end Stacks.Algebraization

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-! ### The two routes from `A` into the sections over a chart -/

/-- The structure map `Spec(A/tᵐA) ∩ U ⟶ U` followed by the inclusion of `U` is the inclusion of
the punctured spectrum of `A/tᵐA` followed by the structure map `Spec(A/tᵐA) ⟶ Spec(A)`. -/
public theorem levelStructureMap_comp_ι (m : ℕ) :
    levelStructureMap k m ≫ (situation k).U.ι = (levelOpen k m).ι ≫ levelToAmbient k m :=
  Scheme.Hom.resLE_comp_ι (levelToAmbient k m) (preimage_U_levelToAmbient k m).ge

/-- The two routes from the global functions of `Spec(A)` to the sections over an open `P` of the
punctured spectrum of `A/tᵐA` lying over an open `V` of `U` agree: restrict to `V` and pull back
along the structure map `Spec(A/tᵐA) ∩ U ⟶ U`, or reduce modulo `tᵐ` and restrict to `P`. -/
public theorem appLE_levelStructureMap_comp (m : ℕ) {V : (situation k).U.toScheme.Opens}
    {P : (levelOpen k m).toScheme.Opens} (e : P ≤ levelStructureMap k m ⁻¹ᵁ V) :
    (situation k).U.ι.appLE ⊤ V le_top ≫ (levelStructureMap k m).appLE V P e =
      (levelToAmbient k m).appTop ≫ (levelOpen k m).ι.appLE ⊤ P le_top := by
  refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
  refine (Scheme.Hom.appLE_congr_hom (levelStructureMap_comp_ι k m) ⊤ P _ le_top).trans ?_
  refine (Scheme.Hom.appLE_comp_appLE (levelOpen k m).ι (levelToAmbient k m) ⊤ ⊤ P
    le_top le_top).symm.trans ?_
  exact congrArg (fun φ => φ ≫ (levelOpen k m).ι.appLE ⊤ P le_top)
    (Scheme.Hom.appLE_eq_app (levelToAmbient k m))

/-- **The two routes from `A` into a chart's sections agree.** An element `z` of `A`, restricted
to an open `V` of `U` and pulled back along the structure map `Spec(A/tᵐA) ∩ U ⟶ U` to an open `P`
inside the chart `D(r̄)`, is the image of `z` in the chart ring `A_r/tᵐA_r` read as a section of
`𝒪` and restricted to `P`.

This is what joins the description of the ideal `(I𝒪_U)(V)` — the image of `I` under
`A → Γ(X, X) → Γ(U, V)` — to the description of the chart rings, and so the identity the kernel
computation of the transition maps rests on. -/
@[stacks 0EHE "the two routes from A into the sections of O over a chart agree"]
public theorem appLE_levelStructureMap_chartOpenEquiv (q : AmbientRing k) (m : ℕ)
    {V : (situation k).U.toScheme.Opens} {P : (levelOpen k m).toScheme.Opens}
    (e : P ≤ levelStructureMap k m ⁻¹ᵁ V)
    (e' : P ≤ (levelOpen k m).ι ⁻¹ᵁ chartOpen k q m) (z : AmbientRing k) :
    ((levelStructureMap k m).appLE V P e).hom
        (((situation k).U.ι.appLE ⊤ V le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom z)) =
      ((levelOpen k m).ι.appLE (chartOpen k q m) P e').hom
        (chartOpenEquiv k q m (levelToChart k q m (levelElt k z m))) := by
  have hnat : (levelToAmbient k m).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom z) =
      (Scheme.ΓSpecIso (CommRingCat.of (levelRing k m))).inv.hom (levelElt k z m) :=
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Ideal.Quotient.mk ((idealT k) ^ m))))) z).symm
  have hcom : chartOpenEquiv k q m (levelToChart k q m (levelElt k z m)) =
      algebraMap (levelRing k m) Γ(levelScheme k m, chartOpen k q m) (levelElt k z m) :=
    (chartOpenEquiv k q m).commutes _
  have htoOpen : algebraMap (levelRing k m) Γ(levelScheme k m, chartOpen k q m)
        (levelElt k z m) =
      ((levelScheme k m).presheaf.map (homOfLE (le_top : chartOpen k q m ≤ ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (levelRing k m))).inv.hom (levelElt k z m)) :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.toOpen_eq (CommRingCat.of (levelRing k m)) (chartOpen k q m))) (levelElt k z m)
  have hmap : (levelScheme k m).presheaf.map (homOfLE (le_top : chartOpen k q m ≤ ⊤)).op ≫
      (levelOpen k m).ι.appLE (chartOpen k q m) P e' =
      (levelOpen k m).ι.appLE ⊤ P le_top :=
    Scheme.Hom.map_appLE (levelOpen k m).ι e' (homOfLE (le_top : chartOpen k q m ≤ ⊤)).op
  refine Eq.trans (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (appLE_levelStructureMap_comp k m e))
    ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom z)) ?_
  change ((levelOpen k m).ι.appLE ⊤ P le_top).hom
      ((levelToAmbient k m).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom z)) = _
  rw [hnat, hcom, htoOpen]
  exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmap)
    ((Scheme.ΓSpecIso (CommRingCat.of (levelRing k m))).inv.hom (levelElt k z m))).symm

/-! ### The closed immersion of punctured spectra on the sections over a chart -/

/-- The closed immersion of the punctured spectrum of `A/tᵐA` in that of `A/t^{m+1}A` followed by
the inclusion of the latter is the inclusion of the former followed by
`Spec(A/tᵐA) ⟶ Spec(A/t^{m+1}A)`. -/
public theorem levelOpenMap_comp_ι (m : ℕ) :
    levelOpenMap k m ≫ (levelOpen k (m + 1)).ι = (levelOpen k m).ι ≫ levelSchemeMap k m :=
  Scheme.Hom.resLE_comp_ι (levelSchemeMap k m) (preimage_levelOpen k m).ge

/-- On the sections over the basic open `D(r̄)` of `Spec(A/t^{m+1}A)` and an open `P` of the
punctured spectrum inside the corresponding chart, the closed immersion of punctured spectra and
the closed immersion `Spec(A/tᵐA) ⟶ Spec(A/t^{m+1}A)` induce the same map. -/
public theorem appLE_ι_comp_app_levelOpenMap (q : AmbientRing k) (m : ℕ)
    {P : (levelOpen k (m + 1)).toScheme.Opens}
    (e' : P ≤ (levelOpen k (m + 1)).ι ⁻¹ᵁ chartOpen k q (m + 1))
    (f' : levelOpenMap k m ⁻¹ᵁ P ≤ (levelOpen k m).ι ⁻¹ᵁ chartOpen k q m) :
    (levelOpen k (m + 1)).ι.appLE (chartOpen k q (m + 1)) P e' ≫ (levelOpenMap k m).app P =
      (levelSchemeMap k m).app (chartOpen k q (m + 1)) ≫
        (levelOpen k m).ι.appLE (chartOpen k q m) (levelOpenMap k m ⁻¹ᵁ P) f' := by
  have h1 : (levelOpenMap k m).app P =
      (levelOpenMap k m).appLE P (levelOpenMap k m ⁻¹ᵁ P) le_rfl :=
    (Scheme.Hom.appLE_eq_app (levelOpenMap k m)).symm
  have h2 : (levelSchemeMap k m).app (chartOpen k q (m + 1)) =
      (levelSchemeMap k m).appLE (chartOpen k q (m + 1)) (chartOpen k q m) le_rfl :=
    (Scheme.Hom.appLE_eq_app (levelSchemeMap k m)).symm
  have hRHS : (levelSchemeMap k m).app (chartOpen k q (m + 1)) ≫
      (levelOpen k m).ι.appLE (chartOpen k q m) (levelOpenMap k m ⁻¹ᵁ P) f' =
      ((levelOpen k m).ι ≫ levelSchemeMap k m).appLE (chartOpen k q (m + 1))
        (levelOpenMap k m ⁻¹ᵁ P) f' :=
    (congrArg (fun φ => φ ≫ (levelOpen k m).ι.appLE (chartOpen k q m)
        (levelOpenMap k m ⁻¹ᵁ P) f') h2).trans
      (Scheme.Hom.appLE_comp_appLE (levelOpen k m).ι (levelSchemeMap k m)
        (chartOpen k q (m + 1)) (chartOpen k q m) (levelOpenMap k m ⁻¹ᵁ P) le_rfl f')
  have hLHS : (levelOpen k (m + 1)).ι.appLE (chartOpen k q (m + 1)) P e' ≫
      (levelOpenMap k m).app P =
      (levelOpenMap k m ≫ (levelOpen k (m + 1)).ι).appLE (chartOpen k q (m + 1))
        (levelOpenMap k m ⁻¹ᵁ P) ((levelOpenMap k m).preimage_mono e') :=
    (congrArg (fun φ => (levelOpen k (m + 1)).ι.appLE (chartOpen k q (m + 1)) P e' ≫ φ)
        h1).trans
      (Scheme.Hom.appLE_comp_appLE (levelOpenMap k m) (levelOpen k (m + 1)).ι
        (chartOpen k q (m + 1)) P (levelOpenMap k m ⁻¹ᵁ P) e' le_rfl)
  exact (hLHS.trans (Scheme.Hom.appLE_congr_hom (levelOpenMap_comp_ι k m)
    (chartOpen k q (m + 1)) (levelOpenMap k m ⁻¹ᵁ P) _ f')).trans hRHS.symm

/-- **The closed immersion of punctured spectra on a chart's sections.** Over an open `P` of the
punctured spectrum of `A/t^{m+1}A` whose image is the basic open `D(r̄)`, the closed immersion of
punctured spectra induces the reduction of chart rings `A_r/t^{m+1}A_r → A_r/tᵐA_r`.

This is the general-open analogue of
`Stacks.Algebraization.NonAlgebraizableExample.app_levelOverlapRingEquiv`, which is the case of
the overlap of the two charts. -/
@[stacks 0EHE "on an open over D(r) the closed immersion induces A_r/t^(m+1) -> A_r/t^m"]
public theorem app_levelOpenMap_appLE_ι_chartOpenEquiv (q : AmbientRing k) (m : ℕ)
    {P : (levelOpen k (m + 1)).toScheme.Opens}
    (e' : P ≤ (levelOpen k (m + 1)).ι ⁻¹ᵁ chartOpen k q (m + 1))
    (f' : levelOpenMap k m ⁻¹ᵁ P ≤ (levelOpen k m).ι ⁻¹ᵁ chartOpen k q m)
    (v : chartRing k q (m + 1)) :
    ((levelOpenMap k m).app P).hom
        (((levelOpen k (m + 1)).ι.appLE (chartOpen k q (m + 1)) P e').hom
          (chartOpenEquiv k q (m + 1) v)) =
      ((levelOpen k m).ι.appLE (chartOpen k q m) (levelOpenMap k m ⁻¹ᵁ P) f').hom
        (chartOpenEquiv k q m (chartReduction k q m v)) := by
  refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (appLE_ι_comp_app_levelOpenMap k q m e' f')) (chartOpenEquiv k q (m + 1) v)).trans ?_
  change ((levelOpen k m).ι.appLE (chartOpen k q m) (levelOpenMap k m ⁻¹ᵁ P) f').hom
      (((levelSchemeMap k m).app (chartOpen k q (m + 1))).hom
        (chartOpenEquiv k q (m + 1) v)) = _
  rw [app_levelSchemeMap_chartOpenEquiv]

/-! ### The kernel of the chart reduction, as a principal multiple -/

/-- A chart function killed by the reduction `A_r/t^{n+1}A_r → A_r/tⁿA_r` is a multiple of the
`n`-th power of the image of `t`. This is
`Stacks.Algebraization.NonAlgebraizableExample.ker_chartReduction` read elementwise, the ideal
`(tⁿ)` being principal. -/
public theorem exists_mul_of_chartReduction_eq_zero (q : AmbientRing k) (n : ℕ)
    (v : chartRing k q (n + 1)) (hv : chartReduction k q n v = 0) :
    ∃ w, v = levelToChart k q (n + 1) (levelElt k (tVar k) (n + 1)) ^ n * w := by
  have hmem : v ∈ LinearMap.ker (chartReduction k q n).toLinearMap := hv
  rw [ker_chartReduction, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨w, -, rfl⟩ := hmem
  exact ⟨w, by rw [Algebra.smul_def, map_pow, levelToChart_mk, Ideal.Quotient.algebraMap_eq]⟩

/-! ### The kernel of a transition map of the system over a basic open -/

/-- The chart trivialization of `𝓛ₘ` on `U` is semilinear over the comorphism of the structure
map: it carries the action of a function on `U` to multiplication by its pullback. -/
public theorem chartLinearEquiv_smul (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (m : ℕ)
    (i : ULift.{u} Bool) {W : (situation k).U.toScheme.Opens}
    (hW : levelStructureMap k m ⁻¹ᵁ W ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) m) (levelChart k (yVar k) m) i)
    (c : Γ((situation k).U.toScheme, W)) (x : Γ(levelModuleOnOpen k a φ m, W)) :
    (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ m)).chartLinearEquiv i hW
        (c • x) =
      ((levelStructureMap k m).app W).hom c *
        (Stacks.SheafOfModules.twoChartCocycle
          (levelOverlapUnit k a φ m)).chartLinearEquiv i hW x :=
  (((Stacks.SheafOfModules.twoChartCocycle
    (levelOverlapUnit k a φ m)).chartLinearEquiv i hW).map_smul
    (((levelStructureMap k m).app W).hom c) x).trans (smul_eq_mul _ _)

/-- The restriction from a chart `D(r̄)` of `Spec(A/tⁿA)` to an open `P` equal to the chart of the
punctured spectrum is bijective. -/
private theorem bijective_appLE_ι_levelChart (q : AmbientRing k) (n : ℕ)
    (hle : chartOpen k q n ≤ levelOpen k n) (P : (levelOpen k n).toScheme.Opens)
    (hP : P = levelChart k q n) :
    Function.Bijective ((levelOpen k n).ι.appLE (chartOpen k q n) P hP.le).hom :=
  Scheme.Opens.bijective_appLE_ι _ _ _ _ (by rw [hP, image_levelChart k q n hle])

/-- **The hard half of the kernel computation.** A section of `𝓛ₘ₊₁`
over an open `V` of `U` whose preimage is a chart `D(r̄)` of the punctured spectrum of
`A/t^{m+1}A`, killed by the transition map `𝓛ₘ₊₁ ⟶ 𝓛ₘ`, is `tᵐ` times a section.

Both modules are trivialized over the chart by
`Stacks.Algebraization.NonAlgebraizableExample.chartLinearEquiv_levelTransition`, the sections
over the chart are the chart ring by
`Stacks.Algebraization.NonAlgebraizableExample.chartOpenEquiv`, and there the statement is
`Stacks.Algebraization.NonAlgebraizableExample.ker_chartReduction`. The factor `tᵐ` produced
upstairs is the pullback of the restriction of `t` to `V` by
`Stacks.Algebraization.NonAlgebraizableExample.appLE_levelStructureMap_chartOpenEquiv`. -/
@[stacks 0EHE "a section of L_(m+1) killed by the transition map is t^m times a section"]
public theorem exists_smul_of_app_levelTransitionOnOpen_eq_zero (a : ℕ → PlaneRing k)
    (φ : ℕ → ℕ) (m : ℕ) (q : AmbientRing k) (i : ULift.{u} Bool)
    (hq : PrimeSpectrum.basicOpen q ≤ (situation k).U)
    {V : (situation k).U.toScheme.Opens}
    (hPeq : levelStructureMap k (m + 1) ⁻¹ᵁ V = levelChart k q (m + 1))
    (hchart : levelChart k q (m + 1) ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (m + 1)) (levelChart k (yVar k) (m + 1)) i)
    (s : Γ(levelModuleOnOpen k a φ (m + 1), V))
    (hs : ((levelTransitionOnOpen k a φ m).val.app (op V)).hom s = 0) :
    ∃ y : Γ(levelModuleOnOpen k a φ (m + 1), V),
      s = ((situation k).U.ι.appLE ⊤ V le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom (tVar k)) ^ m • y := by
  have hle : chartOpen k q (m + 1) ≤ levelOpen k (m + 1) :=
    chartOpen_le_levelOpen k q (m + 1) hq
  have hPch : levelOpenMap k m ⁻¹ᵁ (levelStructureMap k (m + 1) ⁻¹ᵁ V) =
      levelChart k q m := by
    rw [hPeq]
    exact preimage_levelChart k q m hle
  have hP : levelStructureMap k (m + 1) ⁻¹ᵁ V ≤
      Stacks.SheafOfModules.twoChartFamily (levelChart k (xVar k) (m + 1))
        (levelChart k (yVar k) (m + 1)) i := hPeq.le.trans hchart
  have hP' : levelOpenMap k m ⁻¹ᵁ (levelStructureMap k (m + 1) ⁻¹ᵁ V) ≤
      Stacks.SheafOfModules.twoChartFamily (levelChart k (xVar k) m)
        (levelChart k (yVar k) m) i :=
    ((levelOpenMap k m).preimage_mono hP).trans (preimage_twoChartFamily k m i).le
  have hbij1 := bijective_appLE_ι_levelChart k q (m + 1) hle _ hPeq
  have hbij0 := bijective_appLE_ι_levelChart k q m (chartOpen_le_levelOpen k q m hq) _ hPch
  have hzero : (levelTransition k a φ m).val.app
      (op (levelStructureMap k (m + 1) ⁻¹ᵁ V)) s = 0 :=
    (ConcreteCategory.bijective_of_isIso
      (((levelPushforwardIso k m).hom.app (levelModule k a φ m)).app
        V)).1 (hs.trans (map_zero _).symm)
  have hkey0 : ((levelOpenMap k m).app
        (levelStructureMap k (m + 1) ⁻¹ᵁ V)).hom
        ((Stacks.SheafOfModules.twoChartCocycle
          (levelOverlapUnit k a φ (m + 1))).chartLinearEquiv i hP s) = 0 :=
    (chartLinearEquiv_levelTransition k a φ m i hP hP' s).symm.trans
      ((congrArg (fun z => (Stacks.SheafOfModules.twoChartCocycle
        (levelOverlapUnit k a φ m)).chartLinearEquiv i hP' z) hzero).trans (map_zero _))
  obtain ⟨y₁, hy₁⟩ := hbij1.2 ((Stacks.SheafOfModules.twoChartCocycle
    (levelOverlapUnit k a φ (m + 1))).chartLinearEquiv i hP s)
  obtain ⟨v, rfl⟩ := (chartOpenEquiv k q (m + 1)).surjective y₁
  have hred : chartReduction k q m v = 0 := by
    have h1 : ((levelOpen k m).ι.appLE (chartOpen k q m)
        (levelOpenMap k m ⁻¹ᵁ (levelStructureMap k (m + 1) ⁻¹ᵁ V))
        hPch.le).hom (chartOpenEquiv k q m (chartReduction k q m v)) = 0 := by
      rw [← app_levelOpenMap_appLE_ι_chartOpenEquiv k q m hPeq.le hPch.le v, hy₁]
      exact hkey0
    have h2 : chartOpenEquiv k q m (chartReduction k q m v) = 0 :=
      hbij0.1 (h1.trans (map_zero _).symm)
    exact (chartOpenEquiv k q m).injective (h2.trans (map_zero _).symm)
  obtain ⟨w, hw⟩ := exists_mul_of_chartReduction_eq_zero k q m v hred
  have happ : (levelStructureMap k (m + 1)).app V =
      (levelStructureMap k (m + 1)).appLE V
        (levelStructureMap k (m + 1) ⁻¹ᵁ V) le_rfl :=
    (Scheme.Hom.appLE_eq_app (levelStructureMap k (m + 1))).symm
  have hLHS : (Stacks.SheafOfModules.twoChartCocycle
        (levelOverlapUnit k a φ (m + 1))).chartLinearEquiv i hP s =
      ((levelStructureMap k (m + 1)).app V).hom
          (((situation k).U.ι.appLE ⊤ V le_top).hom
            ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom (tVar k))) ^ m *
        ((levelOpen k (m + 1)).ι.appLE (chartOpen k q (m + 1))
          (levelStructureMap k (m + 1) ⁻¹ᵁ V) hPeq.le).hom
            (chartOpenEquiv k q (m + 1) w) := by
    rw [happ, appLE_levelStructureMap_chartOpenEquiv k q (m + 1) le_rfl hPeq.le (tVar k),
      ← hy₁, hw, map_mul, map_pow, map_mul, map_pow]
  refine ⟨((Stacks.SheafOfModules.twoChartCocycle
    (levelOverlapUnit k a φ (m + 1))).chartLinearEquiv i hP).symm
      (((levelOpen k (m + 1)).ι.appLE (chartOpen k q (m + 1))
        (levelStructureMap k (m + 1) ⁻¹ᵁ V) hPeq.le).hom
          (chartOpenEquiv k q (m + 1) w)), ?_⟩
  refine ((Stacks.SheafOfModules.twoChartCocycle
    (levelOverlapUnit k a φ (m + 1))).chartLinearEquiv i hP).injective (hLHS.trans ?_)
  refine Eq.symm ((chartLinearEquiv_smul k a φ (m + 1) i hP _ _).trans ?_)
  rw [LinearEquiv.apply_symm_apply, map_pow]

/-- The restriction of `t` to an affine open `V` of `U` lies in the ideal of `I𝒪_U` on `V`, that
ideal being the image of `I = (t)` under `A → Γ(X, X) → Γ(U, V)`.

The proof argument of the `AlgebraicGeometry.Scheme.Hom.appLE` is a hypothesis rather than
`le_top` so that it carries the type `AlgebraicGeometry.Scheme.Opens.ι_appLE` asks for; see this
module's implementation notes. -/
public theorem tSection_mem_idealOnOpen (V : (situation k).U.toScheme.affineOpens)
    (e₁ : (V : (situation k).U.toScheme.Opens) ≤
      (situation k).U.ι ⁻¹ᵁ (⊤ : (situation k).X.Opens)) :
    ((situation k).U.ι.appLE ⊤ (V : (situation k).U.toScheme.Opens) e₁).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (AmbientRing k))).inv.hom (tVar k)) ∈
      (idealOnOpen (situation k)).ideal V := by
  have hin : (Scheme.ΓSpecIso (CommRingCat.of (situation k).A)).inv.hom (tVar k) ∈
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (situation k).A)).inv.hom (situation k).I :=
    Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self (tVar k))
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.mem_comap,
    Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.Opens.ι_appIso, Scheme.Opens.ι_appLE,
    Iso.refl_inv]
  exact Ideal.mem_map_of_mem _ hin

/-- The sections of `𝓛ₘ`, read on `U`, over an open whose preimage upstairs is empty vanish: the
functions on the empty open form the zero ring. -/
public theorem subsingleton_sections_levelModuleOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (m : ℕ) (W : (situation k).U.toScheme.Opens) (hW : levelStructureMap k m ⁻¹ᵁ W = ⊥) :
    Subsingleton Γ(levelModuleOnOpen k a φ m, W) := by
  change Subsingleton Γ(levelModule k a φ m, levelStructureMap k m ⁻¹ᵁ W)
  rw [hW]
  exact Module.subsingleton Γ((levelOpen k m).toScheme,
    (⊥ : (levelOpen k m).toScheme.Opens)) _

/-- **The kernel over a basic open inside a chart.** Over an affine
open `V` of `U` whose preimage upstairs is a chart of the punctured spectrum of `A/t^{m+1}A`, the
kernel of the transition map `𝓛ₘ₊₁ ⟶ 𝓛ₘ` is `I(V)ᵐ 𝓛ₘ₊₁(V)`. -/
@[stacks 0EHE "over a basic open inside a chart ker(L_(m+1) -> L_m) = I(V)^m L_(m+1)(V)"]
public theorem ker_app_levelTransitionOnOpen_chart (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (m : ℕ)
    (q : AmbientRing k) (i : ULift.{u} Bool)
    (hq : PrimeSpectrum.basicOpen q ≤ (situation k).U)
    (V : (situation k).U.toScheme.affineOpens)
    (hPeq : levelStructureMap k (m + 1) ⁻¹ᵁ (V : (situation k).U.toScheme.Opens) =
      levelChart k q (m + 1))
    (hchart : levelChart k q (m + 1) ≤ Stacks.SheafOfModules.twoChartFamily
      (levelChart k (xVar k) (m + 1)) (levelChart k (yVar k) (m + 1)) i) :
    LinearMap.ker ((levelTransitionOnOpen k a φ m).val.app
        (op (V : (situation k).U.toScheme.Opens))).hom =
      (idealOnOpen (situation k)).ideal V ^ m •
        (⊤ : Submodule Γ((situation k).U.toScheme, (V : (situation k).U.toScheme.Opens))
          Γ(levelModuleOnOpen k a φ (m + 1), (V : (situation k).U.toScheme.Opens))) :=
  ker_app_eq_idealPower_smul_top (idealOnOpen (situation k)) m (levelTransitionOnOpen k a φ m) V
    (idealPowerMultiple_levelModuleOnOpen_eq_bot k a φ m) fun s hs => by
      obtain ⟨y, rfl⟩ := exists_smul_of_app_levelTransitionOnOpen_eq_zero k a φ m q i hq hPeq
        hchart s hs
      exact Submodule.smul_mem_smul
        (Ideal.pow_mem_pow (tSection_mem_idealOnOpen k V le_top) m) Submodule.mem_top

/-- **The kernel over a basic open meeting no chart.** Over an affine
open `V` of `U` whose preimage upstairs is empty — a `D(ht)`, the image of `t` being nilpotent in
`A/t^{m+1}A` — the kernel of the transition map `𝓛ₘ₊₁ ⟶ 𝓛ₘ` is `I(V)ᵐ 𝓛ₘ₊₁(V)`, both sides
being submodules of a module with one element. -/
@[stacks 0EHE "over a basic open with empty preimage both sides of the kernel identity vanish"]
public theorem ker_app_levelTransitionOnOpen_of_preimage_eq_bot (a : ℕ → PlaneRing k)
    (φ : ℕ → ℕ) (m : ℕ) (V : (situation k).U.toScheme.affineOpens)
    (hbot : levelStructureMap k (m + 1) ⁻¹ᵁ (V : (situation k).U.toScheme.Opens) = ⊥) :
    LinearMap.ker ((levelTransitionOnOpen k a φ m).val.app
        (op (V : (situation k).U.toScheme.Opens))).hom =
      (idealOnOpen (situation k)).ideal V ^ m •
        (⊤ : Submodule Γ((situation k).U.toScheme, (V : (situation k).U.toScheme.Opens))
          Γ(levelModuleOnOpen k a φ (m + 1), (V : (situation k).U.toScheme.Opens))) :=
  ker_app_eq_idealPower_smul_top_of_subsingleton (idealOnOpen (situation k)) m
    (levelTransitionOnOpen k a φ m) V
    (subsingleton_sections_levelModuleOnOpen k a φ (m + 1)
      (V : (situation k).U.toScheme.Opens) hbot)

/-! ### The system as an invertible object of `Coh(U, I𝒪_U)` -/

/-- **The kernel computation of the system.** The kernel of the map of
the system `(𝓛ₙ)` from its `(n + 1)`-st term to its `n`-th one, over a member `D(hg)` of the basis
of affine opens, is `I(V)^{n+1}` times the sections of the `(n + 1)`-st term. This is the
hypothesis `hker` of `Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker`.

For `g` one of the two variables the preimage of `D(hg)` upstairs is a chart, where the chartwise
computation applies; for `g = t` it is empty and both sides vanish. -/
@[stacks 0EHE "the kernel of the maps of the system over the basis of affine opens D(hg)"]
public theorem ker_app_levelSystem_map_succ (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ)
    (V : (situation k).U.toScheme.affineOpens) (hV : V ∈ ambientBasicAffineOpens k) :
    LinearMap.ker (((levelSystem k a φ).map (homOfLE (Nat.le_succ n)).op).val.app
        (op (V : (situation k).U.toScheme.Opens))).hom =
      (idealOnOpen (situation k)).ideal V ^ (n + 1) •
        (⊤ : Submodule Γ((situation k).U.toScheme, (V : (situation k).U.toScheme.Opens))
          Γ((levelSystem k a φ).obj (op (n + 1)),
            (V : (situation k).U.toScheme.Opens))) := by
  obtain ⟨h, g, hg, hVeq⟩ := hV
  rw [levelSystem_map_succ]
  have hpre : levelStructureMap k (n + 2) ⁻¹ᵁ (V : (situation k).U.toScheme.Opens) =
      levelChart k (h * g) (n + 2) :=
    (congrArg (fun W => levelStructureMap k (n + 2) ⁻¹ᵁ W) hVeq).trans
      (preimage_levelStructureMap_ambientBasicOpen k (h * g) (n + 2))
  rcases hg with rfl | rfl | rfl
  · exact ker_app_levelTransitionOnOpen_chart k a φ (n + 1) (h * xVar k) ⟨false⟩
      ((PrimeSpectrum.basicOpen_mul_le_right h (xVar k)).trans
        (basicOpen_le_U k (Set.mem_insert _ _))) V hpre
      (levelChart_mul_le k h (xVar k) (n + 2))
  · exact ker_app_levelTransitionOnOpen_chart k a φ (n + 1) (h * yVar k) ⟨true⟩
      ((PrimeSpectrum.basicOpen_mul_le_right h (yVar k)).trans
        (basicOpen_le_U k (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) V hpre
      (levelChart_mul_le k h (yVar k) (n + 2))
  · exact ker_app_levelTransitionOnOpen_of_preimage_eq_bot k a φ (n + 1) V
      (hpre.trans (levelChart_mul_tVar_eq_bot k h (n + 2)))

/-- **The system lies in `Coh(U, I𝒪_U)`.** The family `(𝓛ₙ)`, as a diagram over `ℕᵒᵖ` of modules
on the punctured spectrum `U` of `A`, is a coherent `I𝒪_U`-adic system: its terms are coherent and
annihilated by the successive powers of `I𝒪_U`, its transition maps are epimorphisms, and their
kernels over the basis of affine opens `D(hg)` are the expected ideal multiples. -/
@[stacks 0EHE "the system (L_n) is a coherent I O_U-adic system"]
public theorem isCoherentAdicSystem_levelSystem (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    Stacks.Coherent.IsCoherentAdicSystem (idealOnOpen (situation k)) (levelSystem k a φ) :=
  isCoherentAdicSystem_of_basis_ker _ _ (ambientBasicAffineOpens k)
    (exists_mem_ambientBasicAffineOpens k) (isCoherent_levelSystem_obj k a φ)
    (idealPowerMultiple_levelSystem_obj_eq_bot k a φ) (epi_levelSystem_map_succ k a φ)
    (ker_app_levelSystem_map_succ k a φ)

/-- **The object of `Coh(U, I𝒪_U)`.** The family `(𝓛ₙ)` as an object
of the category `Coh(U, I𝒪_U)` of coherent `I𝒪_U`-adic systems on the punctured spectrum `U` of
`A`. -/
@[stacks 0EHE "the family (L_n) as an object of Coh(U, I O_U)"]
public def levelCoherentAdicSystem (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    Stacks.Coherent.CoherentAdicSystems (idealOnOpen (situation k)) :=
  ⟨levelSystem k a φ, isCoherentAdicSystem_levelSystem k a φ⟩

/-- **The object is invertible.** The object `(𝓛ₙ)` of
`Coh(U, I𝒪_U)` is invertible: its `n`-th term is the direct image of an invertible module on the
closed subscheme `V((I𝒪_U)^{n+1})` of `U`.

That subscheme is the punctured spectrum of `A/t^{n+1}A` by
`Stacks.Algebraization.NonAlgebraizableExample.exists_subschemeIso_levelOpen`, compatibly with
the two morphisms to `U`, and `𝓛ₙ₊₁` is invertible there by
`Stacks.Algebraization.NonAlgebraizableExample.isInvertibleModule_levelModule`. -/
@[stacks 0EHE "the object (L_n) of Coh(U, I O_U) is invertible"]
public theorem isInvertibleAdic_levelCoherentAdicSystem (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) :
    Stacks.Coherent.IsInvertibleAdic (idealOnOpen (situation k))
      (levelCoherentAdicSystem k a φ) := by
  intro n
  obtain ⟨e, he⟩ := exists_subschemeIso_levelOpen k (n + 1)
  have hcomp : e.inv ≫ (idealOnOpen (situation k) ^ (n + 1)).subschemeι =
      levelStructureMap k (n + 1) := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact ⟨(Scheme.Modules.pushforward e.inv).obj (levelModule k a φ (n + 1)),
    Scheme.isInvertibleModule_pushforward_of_isIso e (levelModule k a φ (n + 1))
      (isInvertibleModule_levelModule k a φ (n + 1)),
    ⟨(Scheme.Modules.pushforwardComp e.inv
        (idealOnOpen (situation k) ^ (n + 1)).subschemeι).app (levelModule k a φ (n + 1)) ≪≫
      (Scheme.Modules.pushforwardCongr hcomp).app (levelModule k a φ (n + 1))⟩⟩

end Stacks.Algebraization.NonAlgebraizableExample

end
