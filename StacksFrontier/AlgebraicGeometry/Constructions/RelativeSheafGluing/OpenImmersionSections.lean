module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalRestriction
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Modules.QcqsLocalization
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections

/-!
# Relative gluing of quasi-coherent sheaves

Let `S` be a scheme and let `𝒰` be a locally directed open cover of `S`, so that the members of
`𝒰` are ordered and every point of an overlap of two members lies in a member mapping to both.
Let schemes `X i` over the members `U i` be given, with transition morphisms making every square
```
X i  ⟶  X j
 |        |
 v        v
U i  ⟶  U j
```
cartesian; these glue to a scheme `X` over `S` whose part over `U i` is `X i`.

This file glues **quasi-coherent modules** along such a datum. Given a quasi-coherent module
`F i` on each `X i` and isomorphisms `(ρ i j)^* (F j) ≅ F i` along the transition morphisms which
satisfy the cocycle condition on composable pairs, there is a quasi-coherent module `F` on the
glued scheme `X` together with isomorphisms `F i ≅ (ι i)^* F` identifying each prescribed module
with the inverse image of `F` on the `i`-th chart, compatibly with the given transition
isomorphisms; and the pair consisting of `F` and its local identifications is unique up to a
unique isomorphism compatible with them.

## Main definitions

* `RelativeSheafGluingData`: compatible quasi-coherent modules on a relative gluing datum.
* `RelativeSheafGluingData.Realization`: a module on the glued scheme together with the
  prescribed local identifications.

## Main results

* `RelativeSheafGluingData.exists_realization`: relative sheaf gluing — a realization exists.
* `RelativeSheafGluingData.exists_isPullback_localIso`: the same existence assertion with the
  charts of the glued scheme and their properties spelled out, which is the conclusion of Tag
  01LI as the source states it.
* `RelativeSheafGluingData.existsUnique_iso_realization`: uniqueness of the glued sheaf with its
  local identifications, up to a unique isomorphism.
* `RelativeSheafGluingData.exists_hom_of_chartHom`: the gluing step the uniqueness rests on, for
  an arbitrary pair of modules on the glued scheme — a family of morphisms of their inverse
  images, one over each chart, compatible along the transition maps
  (`RelativeSheafGluingData.IsChartCompatible`), is the inverse image of a single morphism.

## Implementation notes

The scheme and its map to the base are the canonical colimit and structure map supplied by
relative scheme gluing (Tag 01LH).  Thus the result is stated on a `RelativeGluingData`; its
transition maps already include the scheme cocycle and cartesian-square hypotheses.  The first
result gives the sheaf and all local comparison isomorphisms, including their compatibility with
the given transition isomorphisms.  The second result is the unique-isomorphism assertion.

The glued module is built as the limit, over the opposite of the chart category, of the
pushforwards of the local modules to the glued scheme; so it is an honest construction and not a
choice.  Its sections over an open `W` are the families of local sections matched by the
transition maps, and the comparison with the module on a chart is proved by showing that the
projection to the chart's factor is bijective on the opens contained in that chart's image.
Quasi-coherence of the limit is then local on the cover by the chart images.

The uniqueness assertion is proved by glueing morphisms of `𝒪`-modules over the covering of the
glued scheme by the images of the charts, with
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app`.  Local directedness
enters twice: once through the cocycle condition, which makes the comparison morphisms of two
charts agree along an arrow between them, and once to see that the arrows into two charts cover
their overlap, so that separatedness of the target upgrades agreement along arrows to agreement
on overlaps.

Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` compares the restriction
of a module along an open immersion with its inverse image; `ofPullbackHom` transports a morphism
of inverse images to a morphism of restrictions, where it acts on sections, and
`ofPullbackHom_comp` and `ofPullbackHom_congr` are the two coherences of that transport which the
chart bookkeeping needs.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 01LI](https://stacks.math.columbia.edu/tag/01LI)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.ModuleLimits

namespace Stacks.AlgebraicGeometry.RelativeSheafGluing

section Sections

open AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- An open contained in the range of an open immersion is the image of its preimage. -/
lemma image_preimage_eq_self (f : X ⟶ Y) [IsOpenImmersion f] {V : Y.Opens}
    (hV : V ≤ f.opensRange) : f ''ᵁ (f ⁻¹ᵁ V) = V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]

/-- Two restriction maps of the structure sheaf which return to their starting open cancel. -/
private lemma presheaf_map_map (Y : Scheme.{u}) {V₁ V₂ : Y.Opens} (a : op V₁ ⟶ op V₂)
    (b : op V₂ ⟶ op V₁) (r : Γ(Y, V₁)) : Y.presheaf.map b (Y.presheaf.map a r) = r := by
  rw [← ConcreteCategory.comp_apply, ← Y.presheaf.map_comp,
    Subsingleton.elim (a ≫ b) (𝟙 _), Y.presheaf.map_id, ConcreteCategory.id_apply]

/-- A restriction map of an `𝒪`-module which returns to its starting open is the identity. -/
lemma module_presheaf_map_self (M : X.Modules) {V : X.Opens} (a : op V ⟶ op V)
    (s : Γ(M, V)) : M.presheaf.map a s = s := by
  rw [Subsingleton.elim a (𝟙 _), M.presheaf.map_id, ConcreteCategory.id_apply]

/-- Two successive restriction maps of an `𝒪`-module compose to the restriction map between the
outer pair of opens: a morphism of the lattice of opens between a fixed pair is unique. -/
lemma presheaf_map_presheaf_map (M : X.Modules) {A B C : X.Opensᵒᵖ}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (s : M.presheaf.obj A) :
    M.presheaf.map b (M.presheaf.map a s) = M.presheaf.map c s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp,
    presheaf_map_eq_presheaf_map M (a ≫ b) c]

/-- A morphism of `𝒪`-modules commutes with the restriction maps along a containment of opens. -/
lemma app_presheaf_map_le {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (h : W ≤ V)
    (s : Γ(M, V)) :
    φ.app W (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (φ.app V s) :=
  Hom.app_presheaf_map φ (homOfLE h) s

/-- Separatedness of an `𝒪`-module, in terms of `Γ`. -/
lemma eq_of_locally_eq_module (M : X.Modules) {κ : Type*} (U : κ → X.Opens)
    (V : X.Opens) (iUV : ∀ a, U a ≤ V) (hcover : V ≤ iSup U) (x y : Γ(M, V))
    (h : ∀ a, M.presheaf.map (homOfLE (iUV a)).op x = M.presheaf.map (homOfLE (iUV a)).op y) :
    x = y :=
  (Stacks.AlgebraicGeometry.QcqsLocalization.abSheaf M).eq_of_locally_eq' U V
    (fun a => homOfLE (iUV a)) hcover x y h

/-! ### Transporting a morphism of inverse images to a morphism of restrictions -/

/-- A morphism between the inverse images of two `𝒪`-modules along an open immersion, read as a
morphism between their restrictions, where it acts on sections. -/
noncomputable def ofPullbackHom (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    M.restrict f ⟶ N.restrict f :=
  (restrictFunctorIsoPullback f).hom.app M ≫ φ ≫ (restrictFunctorIsoPullback f).inv.app N

/-- The action on sections of a morphism of restrictions along an open immersion, read as a map
between sections over the *image* open.  Pinning this type is what lets the calculus below be
carried out entirely in terms of `Γ(M, ·)`. -/
noncomputable def restrictApp (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (W : X.Opens) : Γ(M, f ''ᵁ W) ⟶ Γ(N, f ''ᵁ W) :=
  θ.app W

/-- A morphism of restrictions along an open immersion is linear for the sections of the
structure sheaf of the target. -/
private lemma restrictApp_smul (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (W : X.Opens) (r : Γ(Y, f ''ᵁ W)) (x : Γ(M, f ''ᵁ W)) :
    restrictApp f θ W (r • x) = r • restrictApp f θ W x := by
  have h1 : @HSMul.hSMul Γ(X, W) Γ(M.restrict f, W) _ _ ((f.appIso W).hom r) x
      = @HSMul.hSMul Γ(Y, f ''ᵁ W) Γ(M, f ''ᵁ W) _ _ r x :=
    (smul_restrictAppIso_inv_apply f M W r x).symm
  have h2 : @HSMul.hSMul Γ(X, W) Γ(N.restrict f, W) _ _ ((f.appIso W).hom r) (θ.app W x)
      = @HSMul.hSMul Γ(Y, f ''ᵁ W) Γ(N, f ''ᵁ W) _ _ r (θ.app W x) :=
    (smul_restrictAppIso_inv_apply f N W r (θ.app W x)).symm
  have h3 : θ.app W (@HSMul.hSMul Γ(X, W) Γ(M.restrict f, W) _ _ ((f.appIso W).hom r) x)
      = @HSMul.hSMul Γ(X, W) Γ(N.restrict f, W) _ _ ((f.appIso W).hom r) (θ.app W x) :=
    Hom.app_smul θ _ _
  show θ.app W (@HSMul.hSMul Γ(Y, f ''ᵁ W) Γ(M, f ''ᵁ W) _ _ r x)
    = @HSMul.hSMul Γ(Y, f ''ᵁ W) Γ(N, f ''ᵁ W) _ _ r (θ.app W x)
  rw [← h1, ← h2, h3]

/-- A morphism of restrictions along an open immersion commutes with the restriction maps of the
target, read on the images of the opens. -/
private lemma restrictApp_presheaf_map (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) {W W' : X.Opens} (h : W' ≤ W)
    (hi : f ''ᵁ W' ≤ f ''ᵁ W) (s : Γ(M, f ''ᵁ W)) :
    restrictApp f θ W' (M.presheaf.map (homOfLE hi).op s) =
      N.presheaf.map (homOfLE hi).op (restrictApp f θ W s) :=
  app_presheaf_map_le θ h s

/-- The map on sections over `V` induced by a morphism of restrictions along `f`, computed through
an open `W` of the source whose image is `V`. -/
noncomputable def secHom (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (W : X.Opens) (V : Y.Opens) (h : f ''ᵁ W = V) :
    Γ(M, V) ⟶ Γ(N, V) :=
  M.presheaf.map (homOfLE h.le).op ≫ restrictApp f θ W ≫ N.presheaf.map (homOfLE h.ge).op

private lemma secHom_apply (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (W : X.Opens) (V : Y.Opens) (h : f ''ᵁ W = V)
    (s : Γ(M, V)) :
    secHom f θ W V h s =
      N.presheaf.map (homOfLE h.ge).op
        (restrictApp f θ W (M.presheaf.map (homOfLE h.le).op s)) := by
  simp only [secHom, ConcreteCategory.comp_apply]

lemma secHom_self (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (W : X.Opens) :
    secHom f θ W (f ''ᵁ W) rfl = restrictApp f θ W := by
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  rw [secHom_apply, module_presheaf_map_self M, module_presheaf_map_self N]

private lemma secHom_congr (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (W W' : X.Opens) (V : Y.Opens) (h : f ''ᵁ W = V)
    (h' : f ''ᵁ W' = V) : secHom f θ W V h = secHom f θ W' V h' := by
  have hWW' : W = W' := by
    rw [← f.preimage_image_eq W, ← f.preimage_image_eq W', h, h']
  subst hWW'
  rfl

lemma secHom_comp_congr (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    {f' : X ⟶ Z} (hf' : f ≫ g = f') [IsOpenImmersion f'] {M N : Z.Modules}
    (θ : M.restrict g ⟶ N.restrict g) (θ' : M.restrict f' ⟶ N.restrict f')
    (hθ : (restrictFunctorCongr hf').hom.app M ≫ θ' =
      ((restrictFunctorComp f g).hom.app M ≫ (restrictFunctor f).map θ ≫
        (restrictFunctorComp f g).inv.app N) ≫ (restrictFunctorCongr hf').hom.app N)
    (W : X.Opens) (V : Z.Opens) (h : f' ''ᵁ W = V) (h' : g ''ᵁ (f ''ᵁ W) = V) :
    secHom f' θ' W V h = secHom g θ (f ''ᵁ W) V h' := by
  have hc : (f ≫ g) ''ᵁ W = g ''ᵁ (f ''ᵁ W) := Scheme.Hom.comp_image f g W
  have hV0 : (f ≫ g) ''ᵁ W = V := hc.trans h'
  have e1 : f' ''ᵁ W ≤ (f ≫ g) ''ᵁ W := (h.trans hV0.symm).le
  have e2 : g ''ᵁ (f ''ᵁ W) ≤ (f ≫ g) ''ᵁ W := hc.ge
  have e3 : (f ≫ g) ''ᵁ W ≤ g ''ᵁ (f ''ᵁ W) := hc.le
  have e5 : f' ''ᵁ W ≤ g ''ᵁ (f ''ᵁ W) := (h.trans h'.symm).le
  have hL : ∀ t : Γ(M, (f ≫ g) ''ᵁ W),
      ((restrictFunctorCongr hf').hom.app M ≫ θ').app W t =
        restrictApp f' θ' W (M.presheaf.map (homOfLE e1).op t) := fun _ => rfl
  have hR : ∀ t : Γ(M, (f ≫ g) ''ᵁ W),
      (((restrictFunctorComp f g).hom.app M ≫ (restrictFunctor f).map θ ≫
          (restrictFunctorComp f g).inv.app N) ≫ (restrictFunctorCongr hf').hom.app N).app W t =
        N.presheaf.map (homOfLE e1).op (N.presheaf.map (homOfLE e3).op
          (restrictApp g θ (f ''ᵁ W) (M.presheaf.map (homOfLE e2).op t))) := fun _ => rfl
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  have hap : restrictApp f' θ' W
        (M.presheaf.map (homOfLE e1).op (M.presheaf.map (homOfLE hV0.le).op s)) =
      N.presheaf.map (homOfLE e1).op (N.presheaf.map (homOfLE e3).op
        (restrictApp g θ (f ''ᵁ W)
          (M.presheaf.map (homOfLE e2).op (M.presheaf.map (homOfLE hV0.le).op s)))) := by
    rw [← hL, ← hR, hθ]
  rw [presheaf_map_presheaf_map M _ _ (homOfLE h.le).op,
    presheaf_map_presheaf_map M _ _ (homOfLE h'.le).op] at hap
  rw [secHom_apply, secHom_apply, hap,
    presheaf_map_presheaf_map N (homOfLE e3).op (homOfLE e1).op (homOfLE e5).op,
    presheaf_map_presheaf_map N (homOfLE e5).op (homOfLE h.ge).op (homOfLE h'.ge).op]

/-- The action on sections over an open contained in the range of an open immersion `f` of a
morphism of restrictions along `f`. -/
noncomputable def chartApp (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (V : Y.Opens) (hV : V ≤ f.opensRange) :
    Γ(M, V) ⟶ Γ(N, V) :=
  secHom f θ (f ⁻¹ᵁ V) V (image_preimage_eq_self f hV)

lemma chartApp_eq (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) {V : Y.Opens} (hV : V ≤ f.opensRange) (W : X.Opens)
    (hW : f ''ᵁ W = V) : chartApp f θ V hV = secHom f θ W V hW :=
  secHom_congr f θ (f ⁻¹ᵁ V) W V (image_preimage_eq_self f hV) hW

/-- The action on sections of a morphism of restrictions commutes with the restriction maps. -/
lemma chartApp_map (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (V W : Y.Opens) (hV : V ≤ f.opensRange) (hWV : W ≤ V)
    (s : Γ(M, V)) :
    chartApp f θ W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op s) =
      N.presheaf.map (homOfLE hWV).op (chartApp f θ V hV s) := by
  have hpre : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V := f.preimage_mono hWV
  have him : f ''ᵁ (f ⁻¹ᵁ W) ≤ f ''ᵁ (f ⁻¹ᵁ V) := Scheme.Hom.image_mono f hpre
  have hWtoV : f ''ᵁ (f ⁻¹ᵁ W) ≤ V := (f.image_preimage_le W).trans hWV
  have hVtoW : W ≤ f ''ᵁ (f ⁻¹ᵁ V) := hWV.trans (image_preimage_eq_self f hV).ge
  rw [chartApp, chartApp, secHom_apply, secHom_apply,
    presheaf_map_presheaf_map M _ _ (homOfLE hWtoV).op,
    ← presheaf_map_presheaf_map M (homOfLE (f.image_preimage_le V)).op (homOfLE him).op
      (homOfLE hWtoV).op,
    restrictApp_presheaf_map f θ hpre him,
    presheaf_map_presheaf_map N _ _ (homOfLE hVtoW).op,
    presheaf_map_presheaf_map N _ _ (homOfLE hVtoW).op]

/-- The action on sections of a morphism of restrictions is linear over the structure sheaf. -/
lemma chartApp_smul (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M.restrict f ⟶ N.restrict f) (V : Y.Opens) (hV : V ≤ f.opensRange) (r : Γ(Y, V))
    (x : Γ(M, V)) : chartApp f θ V hV (r • x) = r • chartApp f θ V hV x := by
  rw [chartApp, secHom_apply, secHom_apply,
    Scheme.Modules.map_smul M (homOfLE (f.image_preimage_le V)) r x, restrictApp_smul,
    Scheme.Modules.map_smul N (homOfLE (image_preimage_eq_self f hV).ge),
    presheaf_map_map Y _ _ r]

/-- The restriction functor acts on a morphism by its action on sections over the image open. -/
private lemma restrictFunctor_map_app (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (θ : M ⟶ N) (V : X.Opens) :
    ((restrictFunctor f).map θ).app V = θ.app (f ''ᵁ V) := rfl

/-- The action on sections of the morphism `M ⟶ f_* N` adjoint to a morphism `M|_f ⟶ N`.  Pinning
this type is what makes the formula of `pushMap_app` usable. -/
noncomputable def pushSecApp (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {N : X.Modules} (θ : M.restrict f ⟶ N) (U : Y.Opens) : Γ(M, U) ⟶ Γ(N, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.restrictAdjunction f).unit.app M ≫
    (Scheme.Modules.pushforward f).map θ).app U

private lemma pushSecApp_eq (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules} {N : X.Modules}
    (θ : M.restrict f ⟶ N) (U : Y.Opens) :
    pushSecApp f θ U =
      M.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫ θ.app (f ⁻¹ᵁ U) := rfl

/-- The morphism of `𝒪`-modules on the base induced, by pushforward along a factorisation
`f ≫ g = h` of open immersions, by a morphism `M|_f ⟶ N`. -/
noncomputable def pushMap (f : X ⟶ Y) {g : Y ⟶ Z} {h : X ⟶ Z} (hg : f ≫ g = h)
    [IsOpenImmersion f] {M : Y.Modules} {N : X.Modules} (θ : M.restrict f ⟶ N) :
    (Scheme.Modules.pushforward g).obj M ⟶ (Scheme.Modules.pushforward h).obj N :=
  (Scheme.Modules.pushforward g).map
      ((Scheme.Modules.restrictAdjunction f).homEquiv _ _ θ) ≫
    (Scheme.Modules.pushforwardComp f g).hom.app N ≫
      (Scheme.Modules.pushforwardCongr hg).hom.app N

/-- `pushMap` on sections: it is the adjoint morphism on sections, followed by the
restriction to the preimage along the composite. -/
lemma pushMap_app (f : X ⟶ Y) {g : Y ⟶ Z} {h : X ⟶ Z} (hg : f ≫ g = h)
    [IsOpenImmersion f] {M : Y.Modules} {N : X.Modules} (θ : M.restrict f ⟶ N) (W : Z.Opens)
    (hpi : h ⁻¹ᵁ W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ W)) :
    (pushMap f hg θ).app W = pushSecApp f θ (g ⁻¹ᵁ W) ≫ N.presheaf.map (homOfLE hpi).op := by
  show pushSecApp f θ (g ⁻¹ᵁ W) ≫ 𝟙 _ ≫ N.presheaf.map (eqToHom (by simp [← hg])).op = _
  rw [Category.id_comp, presheaf_map_eq_presheaf_map N _ (homOfLE hpi).op]

/-- **The transport of a morphism of inverse images commutes with reindexing along an equality of
open immersions.**  If two morphisms of inverse images correspond under the comparison of the
inverse images along equal open immersions, then so do their transports to the restrictions. -/
lemma ofPullbackHom_congr {f f' : X ⟶ Y} (hff' : f = f') [i : IsOpenImmersion f]
    [i' : IsOpenImmersion f'] {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (φ' : (Scheme.Modules.pullback f').obj M ⟶ (Scheme.Modules.pullback f').obj N)
    (h : (Scheme.Modules.pullbackCongr hff').hom.app M ≫ φ' =
      φ ≫ (Scheme.Modules.pullbackCongr hff').hom.app N) :
    (restrictFunctorCongr hff').hom.app M ≫ ofPullbackHom f' φ' =
      ofPullbackHom f φ ≫ (restrictFunctorCongr hff').hom.app N := by
  subst hff'
  obtain rfl : i = i' := rfl
  have hpM : (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ := rfl
  have hpN : (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app N = 𝟙 _ := rfl
  rw [hpM, hpN, Category.id_comp, Category.comp_id] at h
  have hc : ∀ M : Y.Modules, (restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := fun M => by
    simpa using NatTrans.congr_app (restrictFunctorCongr_rfl f) M
  rw [hc, hc, Category.id_comp, Category.comp_id, h]

/-- **The transport of a morphism of inverse images is compatible with composition.**  A morphism
of inverse images along a composite of two open immersions which corresponds, under the comparison
of the iterated inverse image with the inverse image along the composite, to the inverse image of a
morphism, transports to the iterated restriction of that morphism's transport. -/
lemma ofPullbackHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] {M N : Z.Modules}
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)
    (ψ : (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ (Scheme.Modules.pullback (f ≫ g)).obj N)
    (h : (Scheme.Modules.pullbackComp f g).hom.app M ≫ ψ =
      (Scheme.Modules.pullback f).map φ ≫ (Scheme.Modules.pullbackComp f g).hom.app N) :
    (restrictFunctorComp f g).hom.app M ≫ (restrictFunctor f).map (ofPullbackHom g φ) ≫
        (restrictFunctorComp f g).inv.app N = ofPullbackHom (f ≫ g) ψ := by
  have hpb : (Scheme.Modules.pullbackComp f g).hom.app M ≫ ψ ≫
      (Scheme.Modules.pullbackComp f g).inv.app N = (Scheme.Modules.pullback f).map φ := by
    rw [reassoc_of% h, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hr : (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.pullback f).map φ ≫
        (restrictFunctorIsoPullback f).inv.app ((Scheme.Modules.pullback g).obj N) =
      (restrictFunctor f).map φ := by
    rw [← reassoc_of% ((restrictFunctorIsoPullback f).hom.naturality φ), Iso.hom_inv_id_app,
      Category.comp_id]
  conv_rhs => rw [ofPullbackHom, restrictFunctorIsoPullback_hom_app_comp f g M,
    restrictFunctorIsoPullback_inv_app_comp f g N]
  rw [ofPullbackHom, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← hr, ← hpb]
  simp only [Category.assoc]

/-- **The cocycle condition, transported to the restriction functor.**  A cocycle for a
composable pair of open immersions, phrased with `Scheme.Modules.pullbackComp` and
`Scheme.Modules.pullbackCongr`, becomes the corresponding statement for
`Scheme.Modules.restrictFunctor`, where every comparison is a restriction map of the underlying
presheaf and therefore acts on sections. -/
lemma cocycle_restrict {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hh : h = f ≫ g)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    {Mi : X.Modules} {Mj : Y.Modules} {Mk : Z.Modules}
    (tij : (Scheme.Modules.pullback f).obj Mj ⟶ Mi)
    (tjk : (Scheme.Modules.pullback g).obj Mk ⟶ Mj)
    (tik : (Scheme.Modules.pullback h).obj Mk ⟶ Mi)
    (hcoc : (Scheme.Modules.pullbackCongr hh).hom.app Mk ≫
      (Scheme.Modules.pullbackComp f g).inv.app Mk ≫
        (Scheme.Modules.pullback f).map tjk ≫ tij = tik) :
    (restrictFunctorIsoPullback h).hom.app Mk ≫ tik =
      (restrictFunctorCongr hh).hom.app Mk ≫ (restrictFunctorComp f g).hom.app Mk ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app Mk ≫ tjk) ≫
          ((restrictFunctorIsoPullback f).hom.app Mj ≫ tij) := by
  have h2 : (restrictFunctorIsoPullback (f ≫ g)).hom.app Mk ≫
      (Scheme.Modules.pullbackComp f g).inv.app Mk =
      (restrictFunctorComp f g).hom.app Mk ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app Mk) ≫
          (restrictFunctorIsoPullback f).hom.app
            ((Scheme.Modules.pullback g).obj Mk) := by
    rw [restrictFunctorIsoPullback_hom_app_comp f g Mk]
    simp
  have h3 := (restrictFunctorIsoPullback f).hom.naturality tjk
  have h4 : (restrictFunctorIsoPullback (f ≫ g)).hom.app Mk ≫
        (Scheme.Modules.pullbackComp f g).inv.app Mk ≫
          (Scheme.Modules.pullback f).map tjk ≫ tij =
      (restrictFunctorComp f g).hom.app Mk ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app Mk ≫ tjk) ≫
          ((restrictFunctorIsoPullback f).hom.app Mj ≫ tij) := by
    rw [← Category.assoc ((restrictFunctorIsoPullback (f ≫ g)).hom.app Mk), h2,
      Category.assoc, Category.assoc, ← reassoc_of% h3, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
  have hcg := (NatTrans.congr_app
    (restrictFunctorCongr_hom_restrictFunctorIsoPullback_hom hh) Mk).symm
  simp only [NatTrans.comp_app] at hcg
  rw [← hcoc, ← Category.assoc, hcg, Category.assoc, h4]

/-! ### Quasi-coherence of a module which is quasi-coherent on the members of an open covering

Quasi-coherence of a module on a scheme is an assertion about the Grothendieck slices `M.over U`,
while the modules produced below are compared with the geometric restrictions `M.restrict U.ι`.
The two are identified by `Scheme.Modules.overFunctorEquiv`, and the comparison transports
quasi-coherence because the inverse of `Scheme.Modules.overEquiv` is a pushforward along an
equivalence of sites with an invertible comparison of structure sheaves. -/

/-- Continuity of `Over.post` along the equivalence of sites attached to an open of a scheme.
This is the hypothesis `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint` needs in order
to see the inverse of `Scheme.Modules.overEquiv` as a pushforward. -/
private lemma overPost_isContinuous (U : X.Opens) :
    ∀ V : Over U,
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology (X : TopCat)).over U).over V)
        ((Opens.grothendieckTopology (↥U)).over (U.overEquivalence.functor.obj V)) := by
  let G := U.overEquivalence.functor
  have : G.IsDenseSubsite ((Opens.grothendieckTopology (X : TopCat)).over U)
      (Opens.grothendieckTopology (↥U)) := inferInstance
  intro V
  let e := Over.postEquiv (X := V) U.overEquivalence
  let _ := e.isEquivalence_functor
  have hF : ∀ {c : Over V} {t : Over (G.obj V)} (_ : t ⟶ (Over.post G).obj c),
      Σ c', (Over.post G).obj c' ≅ t := fun _ => ⟨e.inverse.obj _, e.counitIso.app _⟩
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed
      (K := (Opens.grothendieckTopology (↥U)).over (G.obj V)) (Over.post G) hF)
    (CoverPreserving.overPost V
      (CoverPreserving.of_isContinuous G
        ((Opens.grothendieckTopology (X : TopCat)).over U)
        (Opens.grothendieckTopology (↥U))))

/-- **Quasi-coherence passes from the geometric restriction to the Grothendieck slice.**  If the
restriction of `M` to the open subscheme `U` is quasi-coherent, then so is the slice `M.over U`. -/
private lemma isQuasicoherent_over_of_restrict (U : X.Opens) (M : X.Modules)
    [((restrictFunctor U.ι).obj M).IsQuasicoherent] : (M.over U).IsQuasicoherent := by
  let e := U.sheafOfModulesEquivOver X.ringCatSheaf
  let φ := (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
  have hsource : ((restrictFunctor U.ι).obj M).IsQuasicoherent := inferInstance
  have hφ : IsIso φ := by
    dsimp [φ]
    infer_instance
  have : ∀ V : Over U,
      (Over.post U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology (X : TopCat)).over U).over V)
        ((Opens.grothendieckTopology (↥U)).over
          (U.overEquivalence.functor.obj V)) := overPost_isContinuous U
  have hlocal : (e.inverse.obj ((restrictFunctor U.ι).obj M)).IsQuasicoherent := by
    show SheafOfModules.IsQuasicoherent ((SheafOfModules.pushforward φ).obj
      ((restrictFunctor U.ι).obj M))
    exact @SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u}
      (C := TopologicalSpace.Opens (↥U)) inferInstance
      (J := Opens.grothendieckTopology (↥U))
      (R := U.sheafRestrict.obj X.ringCatSheaf) inferInstance inferInstance
      (D := Over U) inferInstance
      (K := (Opens.grothendieckTopology (X : TopCat)).over U)
      (S := X.ringCatSheaf.over U) inferInstance inferInstance inferInstance
      (G := U.overEquivalence.functor) inferInstance inferInstance (φ := φ)
      (η := U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf) inferInstance hφ
      inferInstance inferInstance inferInstance
      (M := (restrictFunctor U.ι).obj M) hsource
  have hIso : e.inverse.obj ((restrictFunctor U.ι).obj M) ≅ M.over U :=
    e.inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫ (e.unitIso.app (M.over U)).symm
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso hIso hlocal

/-- The restriction of `M` to the range of an open immersion `f` is quasi-coherent as soon as the
restriction of `M` along `f` is identified with a quasi-coherent module. The identification of
the source of `f` with the open subscheme `f.opensRange` is
`AlgebraicGeometry.IsOpenImmersion.lift`. -/
lemma isQuasicoherent_restrict_opensRange (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (N : Y.Modules) [N.IsQuasicoherent] (e : M.restrict f ≅ N) :
    ((restrictFunctor f.opensRange.ι).obj M).IsQuasicoherent := by
  have hr : Set.range f.opensRange.ι.base ⊆ Set.range f.base := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
  let g := IsOpenImmersion.lift f f.opensRange.ι hr
  have hfac : g ≫ f = f.opensRange.ι := IsOpenImmersion.lift_fac _ _ hr
  let iso : (restrictFunctor g).obj N ≅ (restrictFunctor f.opensRange.ι).obj M :=
    ((restrictFunctor g).mapIso e).symm ≪≫ ((restrictFunctorComp g f).app M).symm ≪≫
      (restrictFunctorCongr hfac).app M
  exact (SheafOfModules.isQuasicoherent
    (f.opensRange : Scheme.{u}).ringCatSheaf).prop_of_iso iso inferInstance

/-- **Quasi-coherence is local on the base.**  A module whose restriction to each member of an open
covering is quasi-coherent is quasi-coherent. -/
lemma isQuasicoherent_of_cover (M : X.Modules) {I : Type u} (V : I → X.Opens)
    (hcov : TopologicalSpace.IsOpenCover V)
    (h : ∀ i, ((restrictFunctor (V i).ι).obj M).IsQuasicoherent) : M.IsQuasicoherent := by
  have h2 : ∀ i, (M.over (V i)).IsQuasicoherent := fun i =>
    have := h i
    isQuasicoherent_over_of_restrict (V i) M
  exact SheafOfModules.IsQuasicoherent.of_coversTop M V ((Opens.coversTop_iff _ V).mpr hcov)

/-- **The compatibility of a family of local comparisons, transported to the inverse image.**  The
identity between restrictions of `T` which says that the comparisons `ei`, `ej` of two charts are
exchanged by `tij` becomes, for the inverse image, exactly the compatibility required of a
realization of relative sheaf gluing. -/
lemma pullback_compat_of_restrict (m : X ⟶ Y) (nj : Y ⟶ Z) {ni : X ⟶ Z}
    [IsOpenImmersion m] [IsOpenImmersion nj] [IsOpenImmersion ni] (w : m ≫ nj = ni)
    (T : Z.Modules) {Mi : X.Modules} {Mj : Y.Modules}
    (ei : T.restrict ni ≅ Mi) (ej : T.restrict nj ≅ Mj)
    (tij : (Scheme.Modules.pullback m).obj Mj ⟶ Mi)
    (hc : (restrictFunctorCongr w).inv.app T ≫ (restrictFunctorComp m nj).hom.app T ≫
      (restrictFunctor m).map ej.hom ≫
        (restrictFunctorIsoPullback m).hom.app Mj ≫ tij = ei.hom) :
    tij ≫ ei.inv ≫ (restrictFunctorIsoPullback ni).hom.app T =
      (Scheme.Modules.pullback m).map (ej.inv ≫ (restrictFunctorIsoPullback nj).hom.app T) ≫
        (Scheme.Modules.pullbackComp m nj).hom.app T ≫
          (Scheme.Modules.pullbackCongr w).hom.app T := by
  have key : (restrictFunctorComp m nj).inv.app T ≫ (restrictFunctorCongr w).hom.app T ≫
        (restrictFunctorIsoPullback ni).hom.app T =
      (restrictFunctor m).map ((restrictFunctorIsoPullback nj).hom.app T) ≫
        (restrictFunctorIsoPullback m).hom.app ((Scheme.Modules.pullback nj).obj T) ≫
          (Scheme.Modules.pullbackComp m nj).hom.app T ≫
            (Scheme.Modules.pullbackCongr w).hom.app T := by
    simpa using NatTrans.congr_app (restrictFunctorIsoPullback_hom_comp_of_eq m nj w) T
  have h1 : (restrictFunctor m).map ej.hom ≫ (restrictFunctorIsoPullback m).hom.app Mj ≫ tij =
      (restrictFunctorComp m nj).inv.app T ≫ (restrictFunctorCongr w).hom.app T ≫ ei.hom := by
    rw [← hc]; simp
  have htr : (restrictFunctorIsoPullback m).hom.app Mj ≫ tij ≫ ei.inv =
      (restrictFunctor m).map ej.inv ≫ (restrictFunctorComp m nj).inv.app T ≫
        (restrictFunctorCongr w).hom.app T := by
    rw [← cancel_epi ((restrictFunctor m).map ej.hom), reassoc_of% h1]
    simp
  rw [← cancel_epi ((restrictFunctorIsoPullback m).hom.app Mj),
    ← reassoc_of% ((restrictFunctorIsoPullback m).hom.naturality
      (ej.inv ≫ (restrictFunctorIsoPullback nj).hom.app T)),
    reassoc_of% htr, CategoryTheory.Functor.map_comp, key, Category.assoc]

end Sections

end Stacks.AlgebraicGeometry.RelativeSheafGluing
