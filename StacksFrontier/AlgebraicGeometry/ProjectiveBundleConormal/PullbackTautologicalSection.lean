module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SectionPreimage
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.UnitSection

/-!
# The section of `σ^*𝒪(1)` that the classifying hypothesis computes

Clause 3 of [Stacks, Tag 0B3V] is handed a section `σ` of `π : 𝐏(ℰ) ⟶ X` *classifying* the
invertible quotient `q : ℰ ⟶ 𝓛`, and that hypothesis is the equation

  `(collapse) ≫ σ^*u ≫ e = q`

named `hqe` throughout this development, where `collapse : ℰ ≅ σ^*π^*ℰ` is the composite of the
three structural comparisons `AlgebraicGeometry.Scheme.Modules.pullbackId`,
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp` supplied by `σ ≫ π = 𝟙 X`
(`Stacks.ProjectiveBundleConormal.pullbackSectionNatIso`). **This file reads that equation on
sections.** Over an open `W` of the base and at a section `s` of `ℰ` there, the left-hand side
becomes the pullback along `σ` of the degree-one section `u(s)` of `𝒪(1)` over `π⁻¹W`, so `hqe`
says

  `e(σ^*(u(s))) = q(s)`.

This is what the factorization criterion
`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top_pullbackSection` needs: the
pulled-back degree-one section attached to `s` is, up to the isomorphism `e`, the image of `s`
under `q`, so on an open where `q(s)` generates `𝓛` it vanishes nowhere and `σ` factors through
the standard open cut out by `s`.

## Main results

* `Stacks.ProjectiveBundleConormal.pullbackSection_collapse`: **the collapse read on sections**,
  at an arbitrary module. The composite of the three structural comparisons, at a section `s` of
  `F` over `W`, is the pullback along `σ` of the pullback along `π` of `s`.
* `Stacks.ProjectiveBundleConormal.hom_pullbackSection_tautologicalMap`: **the classifying
  hypothesis on sections**, the displayed equation `e(σ^*(u(s))) = q(s)`.

## Implementation notes

**Why `AlgebraicGeometry.Scheme.Modules.pullbackSection` and not the bare adjunction unit.** The
unit at `W` lands in the sections over `σ ⁻¹ᵁ (π ⁻¹ᵁ W)`, which is `W` by
`Stacks.ProjectiveBundleConormal.preimage_toBase_preimage` but is not that open on the nose, so
an equation between it and a section over `W` does not even typecheck without a transport.
`AlgebraicGeometry.Scheme.Modules.pullbackSection`, which carries the target open as an argument
bounded by the preimage, has exactly the slack needed, and its structural lemmas
`pullbackSection_comp`, `pullbackSection_congr` and `pullbackSection_naturality` are stated in
the same slack form. So the whole computation is carried out over `W` and no cast appears.

**The two preimage reductions are `rfl`.** `AlgebraicGeometry.Scheme.Hom.id_preimage` and
`AlgebraicGeometry.Scheme.Hom.comp_preimage` are both proved by `rfl` in Mathlib, so `(𝟙 X) ⁻¹ᵁ W`
is `W` and `(σ ≫ π) ⁻¹ᵁ W` is `σ ⁻¹ᵁ (π ⁻¹ᵁ W)` definitionally; the inequalities the structural
lemmas ask for are therefore `le_rfl` and the single inequality
`Stacks.ProjectiveBundleConormal.preimage_toBase_preimage` supplies.

**Each comparison is cancelled forwards.** The structural lemmas are stated with the `hom` of the
comparison applied to the pulled-back section, whereas `hqe` composes the `inv`s. Rather than
invert them by injectivity, each is turned around by
`Stacks.AlgebraicGeometry.PullbackUnit.natIso_inv_hom_app` below, so every step is an `Eq.trans`
of `congrArg`s and no `rw` occurs on these legs — the motive abstraction of `rw` is what times
out here.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection)
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.PullbackUnit

/-- **A natural isomorphism of functors into modules is cancelled on sections, the other way
round.** `Stacks.AlgebraicGeometry.PullbackUnit.natIso_hom_inv_app` cancels `hom` against `inv`;
this cancels `inv` against `hom`, the direction in which a structural comparison stated with its
`hom` is turned around. -/
theorem natIso_inv_hom_app {C : Type*} [Category C] {W : Scheme.{u}}
    {F G : C ⥤ W.Modules} (ε : F ≅ G) (c : C) (V : W.Opens) (x : (F.obj c).val.obj (op V)) :
    (ε.inv.app c).val.app (op V) ((ε.hom.app c).val.app (op V) x) = x :=
  congrArg (fun ρ : F ⟶ F => (ρ.app c).val.app (op V) x) ε.hom_inv_id

end Stacks.AlgebraicGeometry.PullbackUnit

namespace Stacks.ProjectiveBundleConormal

/-- **Pulling a section back to the whole preimage of the open it lives on is the adjunction
unit.** The restriction that `AlgebraicGeometry.Scheme.Modules.pullbackSection` interposes is
along the identity of `f ⁻¹ᵁ U`. This is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_top` with `⊤` replaced by an arbitrary open,
and has the same proof. -/
theorem pullbackSection_preimage_self {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (h : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U) (a : M.val.obj (op U)) :
    Scheme.Modules.pullbackSection f M U (f ⁻¹ᵁ U) h a = unitSection f M U a := by
  unfold Scheme.Modules.pullbackSection unitSection
  rw [show (homOfLE h).op = 𝟙 (op (f ⁻¹ᵁ U)) from Subsingleton.elim _ _]
  simp
  rfl

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)

/-! ### The collapse `ℰ ≅ σ^*π^*ℰ`, read on sections -/

/-- A natural isomorphism turns `hom x = y` around: `x = inv y`. -/
private theorem eq_inv_of_hom_eq {C : Type*} [Category C] {W : Scheme.{u}}
    {F G : C ⥤ W.Modules} (ε : F ≅ G) (c : C) (V : W.Opens) (x : (F.obj c).val.obj (op V))
    (y : (G.obj c).val.obj (op V)) (h : (ε.hom.app c).val.app (op V) x = y) :
    x = (ε.inv.app c).val.app (op V) y :=
  (Stacks.AlgebraicGeometry.PullbackUnit.natIso_inv_hom_app ε c V x).symm.trans
    (congrArg ((ε.inv.app c).val.app (op V)) h)

include hσ in
/-- **The structural collapse supplied by `σ ≫ π = 𝟙 X`, read on a section.** At a section `s`
of a module `F` over an open `W` of the base, the composite
`pullbackId`-`pullbackCongr`-`pullbackComp` carries `s` to the pullback along `σ` of its
pullback along `π`, over `W` itself.

The module is a variable and not `ℰ`: the conormal map of [Stacks, Tag 0B3V] clause 3 crosses
this collapse at `ker q` — that is what
`Stacks.ProjectiveBundleConormal.pullbackSourceIso` is built from — while the classifying
hypothesis crosses it at `ℰ`, and the proof knows nothing about either.

This is the pseudofunctoriality of the inverse image at one section:
`AlgebraicGeometry.Scheme.Modules.pullbackSection_comp`,
`AlgebraicGeometry.Scheme.Modules.pullbackSection_congr` and
`Stacks.Chow.GenuineChern.pullbackId_hom_unitSection` are the three factors. -/
theorem pullbackSection_collapse (F : X.Modules) (W : X.Opens) (s : F.val.obj (op W)) :
    Scheme.Modules.pullbackSection σ
        ((Scheme.Modules.pullback (bundle E).toBase).obj F)
        ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
        (unitSection (bundle E).toBase F W s) =
      ((Scheme.Modules.pullbackId X).inv.app F ≫
        (Scheme.Modules.pullbackCongr hσ).inv.app F ≫
          (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app F).val.app (op W) s := by
  have hσπ : W ≤ σ ⁻¹ᵁ ((bundle E).toBase ⁻¹ᵁ W) := (preimage_toBase_preimage E hσ W).ge
  have hid : W ≤ (𝟙 X) ⁻¹ᵁ W := le_rfl
  have h₁ : Scheme.Modules.pullbackSection (𝟙 X) F W W hid s =
      ((Scheme.Modules.pullbackId X).inv.app F).val.app (op W) s :=
    (pullbackSection_preimage_self (𝟙 X) F W hid s).trans
      (eq_inv_of_hom_eq (Scheme.Modules.pullbackId X) F W _ _
        (Stacks.Chow.GenuineChern.pullbackId_hom_unitSection X F W s))
  have h₂ : Scheme.Modules.pullbackSection (σ ≫ (bundle E).toBase) F W W hσπ s =
      ((Scheme.Modules.pullbackCongr hσ).inv.app F).val.app (op W)
        (((Scheme.Modules.pullbackId X).inv.app F).val.app (op W) s) :=
    eq_inv_of_hom_eq (Scheme.Modules.pullbackCongr hσ) F W _ _
      ((Scheme.Modules.pullbackSection_congr hσ F W W hσπ hid s).trans h₁)
  have h₃ : ((Scheme.Modules.pullbackComp σ (bundle E).toBase).hom.app F).val.app (op W)
        (Scheme.Modules.pullbackSection σ
          ((Scheme.Modules.pullback (bundle E).toBase).obj F)
          ((bundle E).toBase ⁻¹ᵁ W) W hσπ (unitSection (bundle E).toBase F W s)) =
      Scheme.Modules.pullbackSection (σ ≫ (bundle E).toBase) F W W hσπ s :=
    (congrArg
        (fun y => ((Scheme.Modules.pullbackComp σ (bundle E).toBase).hom.app F).val.app (op W)
          (Scheme.Modules.pullbackSection σ
            ((Scheme.Modules.pullback (bundle E).toBase).obj F)
            ((bundle E).toBase ⁻¹ᵁ W) W hσπ y))
        (pullbackSection_preimage_self (bundle E).toBase F W le_rfl s).symm).trans
      (Scheme.Modules.pullbackSection_comp σ (bundle E).toBase F W
        ((bundle E).toBase ⁻¹ᵁ W) W le_rfl hσπ hσπ s)
  exact (eq_inv_of_hom_eq (Scheme.Modules.pullbackComp σ (bundle E).toBase) F W _ _ h₃).trans
    (congrArg
      (((Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app F).val.app (op W)) h₂)

/-! ### The classifying hypothesis, read on sections -/

variable (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)

include hσ e hqe in
/-- **The classifying hypothesis `hqe`, read on sections.** The degree-one section of `𝒪(1)`
attached to `s : Γ(ℰ, W)` by the tautological map, pulled back along `σ` and carried across the
comparison `e : σ^*𝒪(1) ≅ 𝓛`, is `q(s)`.

So on an open where `q(s)` generates `𝓛` the pulled-back section generates `σ^*𝒪(1)`, which is
the hypothesis of
`Stacks.ProjectiveBundleConormal.preimage_basicOpen_eq_top_pullbackSection`. -/
theorem hom_pullbackSection_tautologicalMap (W : X.Opens) (s : E.val.obj (op W)) :
    e.hom.val.app (op W)
        (Scheme.Modules.pullbackSection σ (tautologicalTwist E (symPieces E))
          ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
          ((tautologicalMap E (symPieces E)).val.app (op ((bundle E).toBase ⁻¹ᵁ W))
            (unitSection (bundle E).toBase E W s))) =
      Q.q.val.app (op W) s :=
  (congrArg (e.hom.val.app (op W))
      ((Scheme.Modules.pullbackSection_naturality σ (tautologicalMap E (symPieces E))
          ((bundle E).toBase ⁻¹ᵁ W) W (preimage_toBase_preimage E hσ W).ge
          (unitSection (bundle E).toBase E W s)).symm.trans
        (congrArg
          (((Scheme.Modules.pullback σ).map
            (tautologicalMap E (symPieces E))).val.app (op W))
          (pullbackSection_collapse E hσ E W s)))).trans
    (congrArg (fun φ : E ⟶ Q.L => φ.val.app (op W) s) hqe)

end Stacks.ProjectiveBundleConormal

end
