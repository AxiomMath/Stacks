module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic

/-!
# Glueing morphisms of sheaves of modules given on the members of a cover by open subschemes

`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/Basic.lean` glues local morphism data recorded on
the opens of `Y` inside the members of a cover. A construction, however, produces its local
morphisms on the *covering schemes*: as morphisms
`AlgebraicGeometry.Scheme.Modules.restrict M f ⟶ AlgebraicGeometry.Scheme.Modules.restrict N f`
for open immersions `f`. This file converts between the two and states the gluing in that shape.

That is the shape of the separation half,
`Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.hom_ext_of_chartImage`: a morphism of sheaves of
modules on an open of a scheme is *determined* by its restrictions along the inclusions of the
pieces of a cover. The statement here is the matching existence half.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleHomGlue.appImage`: the action of a morphism of the restrictions
  on the sections over the *image* of an open of the covering scheme.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp`: the action on the sections over an open `V` of
  `Y` presented as the image of an open `W` of the covering scheme. This is `appImage` transported
  along `f ''ᵁ W = V`, and it is the local datum fed to `localModuleHomOfApp`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_congr`: `localApp` does not depend on the chosen
  presentation of `V` as an image, because `f ''ᵁ ·` is injective for an open immersion. This is
  what makes the transport harmless.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`: **a family of
  morphisms of the restrictions of `M` and `N` to the members of a cover of `Y` by open
  subschemes, agreeing wherever two members see the same open of `Y`, comes from exactly one
  morphism `M ⟶ N` restricting to each of them.**
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_restrictFunctor_map_eq`: the restrictions of one
  global morphism satisfy that compatibility hypothesis, so it is satisfiable and the statement is
  not vacuous.

Unconditional: `Y` is an arbitrary scheme, the covering morphisms are arbitrary open immersions
whose images cover `Y`, and `M` and `N` are arbitrary sheaves of `𝒪_Y`-modules. No quasi-coherence,
affineness or finiteness hypothesis appears anywhere.

## The other consumer

`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean` records under "What this does not
do" that comparing its glued object with one given in advance needs the morphism half of the sheaf
axiom, and names `TopCat.Sheaf.existsUnique_hom_of_localModuleHom` for it.
`existsUnique_hom_of_restrict_cover` is that statement at the level its `chartIso` lives on, so it
serves that comparison — with one hypothesis to watch. A
`Stacks.AlgebraicGeometry.SchemeModuleGlue.ChartGlueData` carries only the *containment*
`G.hom i ''ᵁ ⊤ ≤ U i` of a chart's image in its open, so `⨆ i, U i = ⊤` alone does not give
`⨆ i, G.hom i ''ᵁ ⊤ = ⊤`: the charts must be known to exhaust their opens. When they do — as they
do for the projective-spectrum charts of a relative Proj, whose images are the inverse images of
the affine opens — the hypothesis here is met.

## Implementation notes

The sections of a restriction over `W` **are** the sections over the image `f ''ᵁ W`:
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl`. So `appImage` is definitionally
the action of the morphism itself, and its only job is to put the open at the spelling the
consumer's statement uses — the one on which the scalar ring is `Γ(Y, f ''ᵁ W)`. Written without
that definition the statement of `appImage_smul` does not elaborate: the scalar action is
registered at `Γ(N.restrict f, W)`, and the error names a missing `HSMul` rather than the spelling
mismatch it is. `appImage_eq_app` is therefore `rfl`. The two `Iso.refl`s have to be written out:
with `appImage` defined as the bare `ψ.app W` at the ascribed type, `appImage_eq_app` is still
`rfl` but `appImage_smul` is no longer reachable by `simp`, because the simp lemmas that transport
the scalar across the restriction — `AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom` and
its elementwise form — are stated with `restrictAppIso` present.

Linearity over the base is not an extra hypothesis but a consequence. The scalars of the
restriction are those of `Y` pulled back along the ring *isomorphism*
`AlgebraicGeometry.Scheme.Hom.appIso`, so a map linear for the restricted action is linear for the
original one; `appImage_smul` is `AlgebraicGeometry.Scheme.Modules.Hom.app_smul` applied to the
transported scalar.

The transport along an equality of opens is the only delicate point, and it is handled by
*parametrising* rather than by rewriting: `localApp` takes the equality `f ''ᵁ W = V` as an
argument, so every lemma about it is proved by substituting that equality away, after which the
goal is the corresponding statement about `appImage`. Rewriting an open inside the type of
`appImage` in place, by contrast, fails its motive check. `localApp_congr` then says the result
does not depend on `W`: the two sources are equal by
`AlgebraicGeometry.Scheme.Hom.image_injective`, and proof irrelevance closes the goal by `rfl`.

## No tag is claimed

No `stacks` attribute is attached, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/Basic.lean`.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
  (ψ : M.restrict f ⟶ N.restrict f)

/-- An open of `Y` contained in the image of an open immersion is the image of an open of the
source. This restates `Stacks.AlgebraicGeometry.TwistUnique.image_preimage_eq_self`, which is not
imported here because its module pulls in the whole relative-Proj chain. -/
public theorem image_preimage_eq_self {V : Y.Opens} (hV : V ≤ f ''ᵁ ⊤) : f ''ᵁ (f ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange]
  exact inf_eq_right.mpr hV

/-- **The action of a morphism of the restrictions on the sections over an image open.** The
sections of `M.restrict f` over `W` are the sections of `M` over `f ''ᵁ W`, by `Iso.refl`, so this
is `ψ.app W` with the open written on the target side — where the scalars are `Γ(Y, f ''ᵁ W)`. -/
public def appImage (W : X.Opens) : Γ(M, f ''ᵁ W) ⟶ Γ(N, f ''ᵁ W) :=
  (M.restrictAppIso f W).inv ≫ ψ.app W ≫ (N.restrictAppIso f W).hom

/-- `appImage` is the action of `ψ` itself; only the spelling of the open differs. The two
identifications are `Iso.refl`, so this is `rfl` — the definition exists only to carry the
spelling. -/
public theorem appImage_eq_app (W : X.Opens) : appImage f ψ W = ψ.app W := rfl

/-- `appImage` is linear over the sections of `𝒪_Y` on the image open. The restriction of a sheaf
of modules along an open immersion has the scalars of `Y` pulled back along the ring isomorphism
`AlgebraicGeometry.Scheme.Hom.appIso`, so linearity for the restricted action gives linearity for
the original one. -/
public theorem appImage_smul (W : X.Opens) (r : Γ(Y, f ''ᵁ W)) (s : Γ(M, f ''ᵁ W)) :
    appImage f ψ W (r • s) = r • appImage f ψ W s := by
  simp [appImage]

/-- `appImage` commutes with the restriction maps between image opens. This is the naturality of
`ψ`, read through the identification of the sections of a restriction with the sections over the
image. -/
public theorem appImage_map {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (s : Γ(M, f ''ᵁ W₁)) :
    appImage f ψ W₂ (M.presheaf.map (homOfLE (Scheme.Hom.image_mono f h)).op s) =
      N.presheaf.map (homOfLE (Scheme.Hom.image_mono f h)).op (appImage f ψ W₁ s) :=
  congr($(ψ.mapPresheaf.naturality (homOfLE h).op) s)

/-- The restriction of a morphism `φ : M ⟶ N` along `f` acts on the sections over an image open as
`φ` itself. -/
public theorem appImage_restrictFunctor_map (φ : M ⟶ N) (W : X.Opens) :
    appImage f ((Scheme.Modules.restrictFunctor f).map φ) W = φ.app (f ''ᵁ W) :=
  appImage_eq_app f _ W

/-- **The action of a morphism of the restrictions on the sections over an open of `Y` presented as
an image.** `appImage` transported along the equality `f ''ᵁ W = V`. -/
public def localApp {W : X.Opens} {V : Y.Opens} (hWV : f ''ᵁ W = V) : Γ(M, V) ⟶ Γ(N, V) :=
  hWV ▸ appImage f ψ W

/-- At the tautological presentation of an image open, `localApp` is `appImage`. -/
public theorem localApp_image (W : X.Opens) :
    localApp f ψ (rfl : f ''ᵁ W = f ''ᵁ W) = appImage f ψ W := rfl

/-- **`localApp` does not depend on the chosen presentation of `V` as an image.** For an open
immersion the map `f ''ᵁ ·` is injective, so the two sources of the presentation are equal, and
proof irrelevance does the rest. -/
public theorem localApp_congr {W₁ W₂ : X.Opens} {V : Y.Opens}
    (h₁ : f ''ᵁ W₁ = V) (h₂ : f ''ᵁ W₂ = V) : localApp f ψ h₁ = localApp f ψ h₂ := by
  obtain rfl : W₁ = W₂ := f.image_injective (h₁.trans h₂.symm)
  rfl

/-- `localApp` is linear over the sections of `𝒪_Y`. -/
public theorem localApp_smul {W : X.Opens} {V : Y.Opens} (hWV : f ''ᵁ W = V)
    (r : Γ(Y, V)) (s : Γ(M, V)) : localApp f ψ hWV (r • s) = r • localApp f ψ hWV s := by
  subst hWV
  exact appImage_smul f ψ W r s

/-- `localApp` commutes with the restriction maps of `M` and `N`. -/
public theorem localApp_map {W₁ W₂ : X.Opens} {V₁ V₂ : Y.Opens}
    (h₁ : f ''ᵁ W₁ = V₁) (h₂ : f ''ᵁ W₂ = V₂) (hV : V₂ ≤ V₁) (s : Γ(M, V₁)) :
    localApp f ψ h₂ (M.presheaf.map (homOfLE hV).op s) =
      N.presheaf.map (homOfLE hV).op (localApp f ψ h₁ s) := by
  subst h₁
  subst h₂
  exact appImage_map f ψ ((Scheme.Hom.image_le_image_iff f W₂ W₁).mp hV) s

/-- The restriction of a morphism `φ : M ⟶ N` along `f` has `localApp` equal to the action of `φ`
on the sections over the image open. -/
public theorem localApp_restrictFunctor_map (φ : M ⟶ N) {W : X.Opens} {V : Y.Opens}
    (hWV : f ''ᵁ W = V) :
    localApp f ((Scheme.Modules.restrictFunctor f).map φ) hWV = φ.app V := by
  subst hWV
  exact appImage_restrictFunctor_map f φ W

/-- The restrictions of a single morphism `φ : M ⟶ N` to two open subschemes satisfy the
compatibility hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`: both local maps are
the action of `φ` on the sections over the common image open. So that hypothesis is satisfiable
and the theorem is not vacuous. -/
public theorem localApp_restrictFunctor_map_eq {X' : Scheme.{u}} (f' : X' ⟶ Y)
    [IsOpenImmersion f'] (φ : M ⟶ N) {W : X.Opens} {W' : X'.Opens} {V : Y.Opens}
    (hWV : f ''ᵁ W = V) (hWV' : f' ''ᵁ W' = V) :
    localApp f ((Scheme.Modules.restrictFunctor f).map φ) hWV =
      localApp f' ((Scheme.Modules.restrictFunctor f').map φ) hWV' :=
  (localApp_restrictFunctor_map f φ hWV).trans
    (localApp_restrictFunctor_map f' φ hWV').symm

/-- **Morphisms of sheaves of modules glue over a cover by open subschemes.** Let `g i : Z i ⟶ Y`
be open immersions whose images cover `Y`, and let `M`, `N` be sheaves of `𝒪_Y`-modules. A family
of morphisms `M|_{Z i} ⟶ N|_{Z i}` which agree wherever two members of the cover see the same open
of `Y` comes from exactly one morphism `M ⟶ N` restricting to each of them.

This is the existence half matching the separation half
`Stacks.AlgebraicGeometry.Tag07ZGTwistLocality.hom_ext_of_chartImage`. Nothing is assumed of `Y`,
of the cover or of `M` and `N`. -/
public theorem existsUnique_hom_of_restrict_cover {ι : Type u} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ⨆ i, g i ''ᵁ (⊤ : (Z i).Opens) = ⊤) {M N : Y.Modules}
    (ψ : ∀ i, M.restrict (g i) ⟶ N.restrict (g i))
    (hψ : ∀ (i j : ι) (W₁ : (Z i).Opens) (W₂ : (Z j).Opens) (V : Y.Opens)
      (h₁ : g i ''ᵁ W₁ = V) (h₂ : g j ''ᵁ W₂ = V),
        localApp (g i) (ψ i) h₁ = localApp (g j) (ψ j) h₂) :
    ∃! φ : M ⟶ N, ∀ i, (Scheme.Modules.restrictFunctor (g i)).map φ = ψ i := by
  have key (i : ι) := @image_preimage_eq_self _ _ (g i) _
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_hom_of_cover_app hg
    (fun i V hV => localApp (g i) (ψ i) (key i hV))
    (fun i _ hV => localApp_smul (g i) (ψ i) (key i hV))
    (fun i _ _ hV hWV => localApp_map (g i) (ψ i) (key i hV)
      (key i (hWV.trans hV)) hWV)
    (fun i j V hVi hVj => hψ i j _ _ V (key i hVi)
      (key j hVj))
  refine ⟨φ, fun i => Scheme.Modules.hom_ext _ _ fun W => ?_, fun φ' hφ' => huniq φ' fun i V hV =>
    ?_⟩
  · exact (hφ i (g i ''ᵁ W) (Scheme.Hom.image_mono (g i) le_top)).trans
      (localApp_congr (g i) (ψ i) _ rfl)
  · rw [← hφ' i]
    exact (localApp_restrictFunctor_map (g i) φ' (key i hV)).symm

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
