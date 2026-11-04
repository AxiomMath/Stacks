module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.FiniteOrder
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.QuasiAffineLimit
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.SectionRatioNoAmple.Pullback

/-!
# Ampleness ascends along an arbitrary thickening

Let `i : Z ⟶ X` be a closed immersion inducing a homeomorphism of underlying spaces and let `𝓛`
be an invertible `𝒪_X`-module with `i^* 𝓛` ample. Then `𝓛` is ample. This is the hard
implication of [Stacks, Tag 09MW], with no Noetherian hypothesis, proved by the limit argument
of the source.

## The argument

`X` is quasi-compact and quasi-separated, being homeomorphic to `Z`, so absolute Noetherian
approximation ([Stacks, Tag 01ZA]) writes `X = lim Xⱼ` over a directed set, with affine transition
morphisms and every `Xⱼ` Noetherian. By [Stacks, Tag 0B8W] (2) `𝓛` is the pullback of an
invertible module `𝓛₀` on some stage `X₀`.

Let `Zⱼ ⊆ Xⱼ` be the scheme-theoretic image of `Z`; then `Z = lim Zⱼ`
(`Stacks.Thickenings.imageSubschemeConeIsLimit`), and `i^* 𝓛` is the pullback of `𝓛₀|_{Z₀}`, so
by [Stacks, Tag 09MT] the restriction of `𝓛₀` to `Zⱼ` is ample for some stage `j`. The image of `X`
in `Xⱼ` lies in the closed — hence, `Xⱼ` being Noetherian, constructible — subset `Zⱼ`, so by
[Stacks, Tag 05F4] some later stage `X_l ⟶ Xⱼ` lands in `Zⱼ` set-theoretically. The scheme
theoretic inverse image `T = X_l ×_{Xⱼ} Zⱼ` is a thickening of the Noetherian scheme `X_l`, and
the pullback of `𝓛₀` to it is ample because `T ⟶ Zⱼ` is affine ([Stacks, Tag 0892]). So the
pullback of `𝓛₀` to `X_l` is ample by the Noetherian case
`Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isLocallyNoetherian`, and its
pullback to `X`, which is `𝓛`, is ample by [Stacks, Tag 0892] again, `X ⟶ X_l` being affine.

## Main results

* `Stacks.AmpleThickeningAscent.isAmple_of_isThickening_of_descentSituation`: the ascent along a
  thickening of the limit of a directed system of Noetherian schemes with affine transition
  morphisms.
* `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isThickening`: **the ascent along
  an arbitrary thickening.**

## References

* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample
open Stacks.Thickenings
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleThickeningAscent

/-- Ampleness of a pullback along a composite is ampleness of the iterated pullback. -/
theorem isAmple_pullback_comp_iff {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (N : C.Modules)
    [IsInvertibleModule C N] :
    IsAmple A (pullbackModule (a ≫ b) N) ↔ IsAmple A (pullbackModule a (pullbackModule b N)) :=
  Stacks.RelativeVeryAmple.isAmple_congr _ _
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso a b N)

/-- Ampleness of a pullback depends only on the morphism, transported along an equality. -/
theorem isAmple_pullback_congr {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) (N : B.Modules)
    [IsInvertibleModule B N] :
    IsAmple A (pullbackModule a N) ↔ IsAmple A (pullbackModule b N) := by
  subst h; rfl

/-- **Ampleness ascends along a thickening of the limit of a directed system of Noetherian schemes
with affine transition morphisms.** See the module docstring. -/
theorem isAmple_of_isThickening_of_descentSituation
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (d : AlgebraicGeometry.DescentSituation.{u, u} J)
    (hN : ∀ j : Jᵒᵖ, IsNoetherian (d.system.obj j))
    {Z : Scheme.{u}} (i : Z ⟶ d.limitCone.pt) (hi : IsThickening i)
    (L : d.limitCone.pt.Modules) [IsInvertibleModule d.limitCone.pt L]
    (h : IsAmple Z (pullbackModule i L)) : IsAmple d.limitCone.pt L := by
  classical
  have := hN
  have : IsClosedImmersion i := hi.1
  have : Surjective i := ⟨hi.2⟩
  have : Nonempty J := ⟨d.base⟩
  have : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), IsAffineHom (d.system.map f) := d.transition_affine
  have : ∀ j : Jᵒᵖ, CompactSpace (d.system.obj j) := fun j => d.quasiCompact j.unop
  have : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (d.system.obj j) := fun j => d.quasiSeparated j.unop
  -- descend `L` to a stage
  obtain ⟨j₀, L₀, hL₀, ⟨eL⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      d.system d.limitCone d.isLimit L ‹IsInvertibleModule _ L›
  have : IsInvertibleModule (d.system.obj j₀) L₀ := hL₀
  have hL : ∀ {k : Jᵒᵖ} (g : k ⟶ j₀),
      IsAmple d.limitCone.pt (pullbackModule (d.limitCone.π.app k)
        (pullbackModule (d.system.map g) L₀)) → IsAmple d.limitCone.pt L := by
    intro k g hk
    rw [← isAmple_pullback_comp_iff, d.limitCone.w g] at hk
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _ eL).mpr hk
  -- the scheme-theoretic images of `Z`
  let E := imageSubschemeDiagram d.system d.limitCone i.ker
  let a := imageSubschemeInclusion d.system d.limitCone i.ker
  let c := imageSubschemeCone d.system d.limitCone i
  have hacl : ∀ j : Jᵒᵖ, IsClosedImmersion (a.app j) := by
    intro j
    show IsClosedImmersion (i.ker.map (d.limitCone.π.app j)).subschemeι
    infer_instance
  have : ∀ {j k : Jᵒᵖ} (g : j ⟶ k), IsAffineHom (E.map g) := by
    intro j k g
    have : IsAffineHom (E.map g ≫ a.app k) := by
      rw [a.naturality g]
      infer_instance
    exact IsAffineHom.of_comp _ (a.app k)
  have : ∀ j : Jᵒᵖ, CompactSpace (E.obj j) := fun j =>
    QuasiCompact.compactSpace_of_compactSpace (a.app j)
  have : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (E.obj j) := fun j =>
    quasiSeparatedSpace_of_quasiSeparated (a.app j)
  -- [Stacks, Tag 09MT] on the images
  let M₀ := pullbackModule (a.app j₀) L₀
  have hM₀ : IsAmple c.pt (pullbackModule (c.π.app j₀) M₀) := by
    have h1 : IsAmple Z (pullbackModule i (pullbackModule (d.limitCone.π.app j₀) L₀)) :=
      (Stacks.RelativeVeryAmple.isAmple_congr _ _
        ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).mapIso eL)).mp h
    have h2 := (isAmple_pullback_comp_iff i (d.limitCone.π.app j₀) L₀).mpr h1
    have h3 := (isAmple_pullback_congr (imageSubschemeCone_fac d.system d.limitCone i j₀)
      L₀).mpr h2
    exact (isAmple_pullback_comp_iff (c.π.app j₀) (a.app j₀) L₀).mp h3
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (E.obj j₀).toRingedSpace.presheaf
      (structureSheafRing (E.obj j₀).toRingedSpace).property M₀ :=
    (inferInstance : IsInvertibleModule (E.obj j₀) M₀)
  obtain ⟨j₁, g, hE⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs
      E c (imageSubschemeConeIsLimit d.system d.limitCone d.isLimit i) j₀ M₀
      ((Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp hM₀)
  have hE' : IsAmple (E.obj j₁) (pullbackModule (E.map g) M₀) :=
    (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr hE
  set L₁ := pullbackModule (d.system.map g) L₀
  have hE'' : IsAmple (E.obj j₁) (pullbackModule (a.app j₁) L₁) := by
    have h1 := (isAmple_pullback_comp_iff (E.map g) (a.app j₀) L₀).mpr hE'
    have h2 := (isAmple_pullback_congr (a.naturality g) L₀).mp h1
    exact (isAmple_pullback_comp_iff (a.app j₁) (d.system.map g) L₀).mp h2
  -- a later stage lands in the image set-theoretically ([Stacks, Tag 05F4])
  rcases j₁ with ⟨j₁⟩
  let dj : AlgebraicGeometry.DescentSituation.{u, u} J := { d with base := j₁ }
  let S : Set (d.system.obj (op j₁)) := (i.ker.map (d.limitCone.π.app (op j₁))).support
  have hS : Topology.IsLocallyConstructible S := by
    refine Topology.IsConstructible.isLocallyConstructible (Topology.IsConstructible.of_compl ?_)
    exact (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible
      (i.ker.map (d.limitCone.π.app (op j₁))).support.isClosed.isOpen_compl
  have hlim : Set.range (dj.limitCone.π.app (op dj.base)).base ⊆ S := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (show Function.Surjective i from Surjective.surj (f := i)) x
    have h := Scheme.Hom.range_subset_ker_support (i ≫ d.limitCone.π.app (op j₁))
    exact (show Set.range (i ≫ d.limitCone.π.app (op j₁)) ⊆ S by
      simpa [S, Scheme.Hom.ker_comp] using h) ⟨z, rfl⟩
  obtain ⟨l, hl, hlS⟩ :=
    (AlgebraicGeometry.eventually_range_transition_subset_of_isLocallyConstructible dj S hS
      hlim).exists
  let g' := d.system.map (homOfLE hl).op
  have : IsAffineHom g' := d.transition_affine _
  have : IsAffineHom (pullback.snd g' (a.app (op j₁))) :=
    AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g' (a.app (op j₁))) inferInstance
  have : IsClosedImmersion (pullback.fst g' (a.app (op j₁))) :=
    AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g' (a.app (op j₁))).flip (hacl _)
  have : Surjective (pullback.fst g' (a.app (op j₁))) := by
    rw [surjective_iff]
    intro x
    have hx' : g' x ∈ Set.range (a.app (op j₁)).base := by
      show g' x ∈ Set.range (i.ker.map (d.limitCone.π.app (op j₁))).subschemeι.base
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hlS ⟨x, rfl⟩
    have hmem : x ∈ Set.range (pullback.fst g' (a.app (op j₁))).base := by
      rw [Scheme.Pullback.range_fst]
      exact hx'
    exact hmem
  -- the thickening `T ⟶ X_l` of the Noetherian stage
  have hT : IsAmple (pullback g' (a.app (op j₁)))
      (pullbackModule (pullback.fst g' (a.app (op j₁))) (pullbackModule g' L₁)) := by
    have h1 := Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom
      (pullback.snd g' (a.app (op j₁))) _ hE''
    have h2 := (isAmple_pullback_comp_iff _ _ L₁).mpr h1
    have h3 := (isAmple_pullback_congr (pullback.condition (f := g') (g := a.app (op j₁)))
      L₁).mpr h2
    exact (isAmple_pullback_comp_iff _ _ L₁).mp h3
  have hl' : IsAmple (d.system.obj (op l)) (pullbackModule g' L₁) :=
    isAmple_of_isAmple_pullback_of_isLocallyNoetherian
      (show IsThickening (pullback.fst g' (a.app (op j₁))) from
        ⟨inferInstance, Surjective.surj⟩) _ hT
  -- pulled back to the limit
  have : IsAffineHom (d.limitCone.π.app (op l)) :=
    AlgebraicGeometry.isAffineHom_π_app d.system d.limitCone d.isLimit (op l)
  have hX := Stacks.SectionRatioNoAmple.isAmple_modulePullback_of_isQuasiAffineHom
    (d.limitCone.π.app (op l)) _ hl'
  have h1 := (isAmple_pullback_comp_iff _ _ L₁).mpr hX
  have h2 := (isAmple_pullback_congr (d.limitCone.w (homOfLE hl).op) L₁).mp h1
  exact hL g h2

/-- **Ampleness ascends along an arbitrary thickening.** For a closed immersion `k : Y ⟶ Y'`
surjective on points and an invertible `𝒪_{Y'}`-module `𝓛'`, ampleness of `k^* 𝓛'` gives
ampleness of `𝓛'`. No Noetherian hypothesis and no hypothesis on the ideal sheaf of `k`.

`Y'` is quasi-compact and quasi-separated, being homeomorphic to `Y`, which is quasi-compact by
ampleness and separated by [Stacks, Tag 09MP]; absolute Noetherian approximation
([Stacks, Tag 01ZA]) presents it as the limit of a directed system of Noetherian schemes with
affine transition morphisms, and
`Stacks.AmpleThickeningAscent.isAmple_of_isThickening_of_descentSituation` applies. -/
theorem isAmple_of_isAmple_pullback_of_isThickening {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}
    (hk : IsThickening k) (L' : Y'.Modules) [IsInvertibleModule Y' L']
    (h : IsAmple Y (pullbackModule k L')) : IsAmple Y' L' := by
  classical
  have : IsClosedImmersion k := hk.1
  have : CompactSpace Y := h.1
  have : Y.IsSeparated := ((Stacks.AmpleBridge.isAmple_iff_isAmple Y _).mp h).isSeparated
  have : CompactSpace Y' := hk.homeomorph.compactSpace
  have : QuasiSeparatedSpace Y' := (quasiSeparatedSpace_congr hk.homeomorph).mp inferInstance
  obtain ⟨I, hpre, hne, hdir, F, cc, hAff, hFT, hQC, ⟨hcc⟩⟩ :=
    Scheme.exists_isLimit_affine_locallyOfFiniteType Y'
  let e : Iᵒᵖ ≌ Iᵒᵈ := (orderDualEquivalence I).symm
  have (j : Iᵒᵖ) : IsNoetherian (F.obj (e.functor.obj j)) :=
    have := hFT (e.functor.obj j)
    have := hQC (e.functor.obj j)
    AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType_terminal_from _
  let d : AlgebraicGeometry.DescentSituation.{u, u} I :=
    { system := e.functor ⋙ F
      transition_affine := fun f => hAff (e.functor.map f)
      quasiCompact := fun j => inferInstanceAs (CompactSpace (F.obj (e.functor.obj (op j))))
      quasiSeparated := fun j =>
        inferInstanceAs (QuasiSeparatedSpace (F.obj (e.functor.obj (op j))))
      limitCone := Cone.whisker e.functor (Cone.mk Y' cc)
      isLimit := hcc.whiskerEquivalence e
      base := Classical.arbitrary I }
  exact isAmple_of_isThickening_of_descentSituation d
    (fun j => inferInstanceAs (IsNoetherian (F.obj (e.functor.obj j)))) k hk L' h

end Stacks.AmpleThickeningAscent

end
