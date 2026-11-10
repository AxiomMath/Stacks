module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyAgreement
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.PicardGroup.OpenUFD
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Rationally equivalent invertible modules on a normal variety

Let `k` be a field, let `X` be a normal variety over `k` — an integral scheme all of whose local
rings are normal domains, with separated structure morphism of finite type — and let
`U ⊆ 𝔸^n_k` be an open subscheme carrying two `k`-rational points `p, q ∈ U(k)`. This file proves
[Stacks, Tag 0BEH](https://stacks.math.columbia.edu/tag/0BEH): for every invertible module `ℒ` on
`X ×_{Spec k} U` the restrictions `ℒ|_{X × p}` and `ℒ|_{X × q}` are isomorphic.

Both halves of the source's proof are carried out here. The fibre of the projection
`X ×_{Spec k} U → X` over a point `x` is the base change of `U` along `Spec κ(x) → Spec k`, hence
an open subscheme of affine `n`-space over the field `κ(x)`; it therefore has trivial Picard
group by [Stacks, Tag 0BDA], and it is integral, being nonempty because `p` gives it a rational
point. The second half is the appeal to [Stacks, Tag 0BD7], which turns triviality of `ℒ` on the
generic fibre into an isomorphism `ℒ ≅ pr_X^* 𝒩` with `𝒩` invertible on `X`; both restrictions
are then isomorphic to `𝒩`, because `X × p → X` and `X × q → X` are isomorphisms.

## Main results

* `Stacks.PicardGroup.subsingleton_picardGroup_pullback_openAffineSpace`: the base change of an
  open subscheme of affine `n`-space along a morphism from the spectrum of a field has trivial
  Picard group.
* `Stacks.PicardGroup.subsingleton_picardGroup_fiber_fst`: every fibre of the projection
  `X ×_{Spec k} U → X` has trivial Picard group.
* `Stacks.PicardGroup.isIntegral_fiber_fst`: every fibre of that projection is integral, once
  `U` carries a `k`-rational point.
* `Stacks.PicardGroup.nonempty_iso_pullback_of_sections`: a module pulled back from the target of
  a morphism has isomorphic pullbacks along any two sections of that morphism.
* `Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint`: the argument from [Stacks, Tag 0BDA]
  alone, with the appeal to [Stacks, Tag 0BD7] carried as the hypothesis `h0BD7`.
* `Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint_of_finite`: **[Stacks, Tag 0BEH]**,
  with `h0BD7` discharged and no hypothesis the source does not have.

## Implementation notes

A `k`-rational point of `U` is a section `p : Spec k ⟶ U` of the structure morphism, and the
closed subscheme `X × p ⊆ X ×_{Spec k} U` is the image of the section `sectionOfPoint f p hp` of
the projection to `X`. That section is an isomorphism onto `X × p` inverse to the projection, so
restriction to `X × p`, read on `X`, is pullback along `sectionOfPoint f p hp`.

The index type of affine space is an arbitrary type in the auxiliary results, as it is in Tag
0BDA, rather than a natural number. The tag itself asks for `𝔸^n_k` with `n` a natural number,
so `Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint_of_finite` assumes the index type
finite — a genuine need, not a convenience: hypotheses (1) and (2) of Tag 0BD7 ask for locally
Noetherian schemes, and `X ×_{Spec k} 𝔸^n_k` is locally Noetherian because the projection is
locally of finite type, which a polynomial algebra on infinitely many variables is not.

The hypothesis `h0BD7` of `Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint` is Tag 0BD7
at the projection `X ×_{Spec k} U → X`: its antecedent is hypothesis (5) of that tag, triviality
of the module on the generic fibre, and it is discharged there from
`subsingleton_picardGroup_fiber_fst`. Hypotheses (1)–(4) of that tag, which constrain the
projection and not the module, are carried inside the implication; they are supplied in
`Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint_of_finite`, where the implication is
closed by
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat`.

## References

* [Stacks Project, Tag 0BEH](https://stacks.math.columbia.edu/tag/0BEH)
* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.PicardGroup

/-- The structure morphism to `Spec k` of an open subscheme of affine `n`-space over a field
`k`. -/
def openAffineSpaceOver (k : Type u) [Field k] {n : Type u}
    (U : (𝔸(n; Spec (.of k))).Opens) : U.toScheme ⟶ Spec (.of k) :=
  U.ι ≫ 𝔸(n; Spec (.of k)) ↘ Spec (.of k)

/-- The section `X ⟶ X ×_S V` of the first projection attached to a point `p : S ⟶ V` of `V`
over `S`; its image is the subscheme `X × p`. -/
def sectionOfPoint {X V S : Scheme.{u}} (f : X ⟶ S) {g : V ⟶ S} (p : S ⟶ V)
    (hp : p ≫ g = 𝟙 S) : X ⟶ Limits.pullback f g :=
  Limits.pullback.lift (𝟙 X) (f ≫ p)
    (by rw [Category.id_comp, Category.assoc, hp, Category.comp_id])

/-- The morphism attached to a point of `V` over `S` is a section of the first projection of
`X ×_S V`. -/
theorem sectionOfPoint_fst {X V S : Scheme.{u}} (f : X ⟶ S) {g : V ⟶ S} (p : S ⟶ V)
    (hp : p ≫ g = 𝟙 S) : sectionOfPoint f p hp ≫ Limits.pullback.fst f g = 𝟙 X :=
  Limits.pullback.lift_fst _ _ _

/-- The second component of the morphism attached to a point of `V` over `S` is the constant
morphism at that point; together with `sectionOfPoint_fst` this says it is the graph of `p`. -/
theorem sectionOfPoint_snd {X V S : Scheme.{u}} (f : X ⟶ S) {g : V ⟶ S} (p : S ⟶ V)
    (hp : p ≫ g = 𝟙 S) : sectionOfPoint f p hp ≫ Limits.pullback.snd f g = f ≫ p :=
  Limits.pullback.lift_snd _ _ _

/-- A module pulled back from the target of `pr` along a section `s` of `pr` is the module on the
target itself. -/
private def pullbackSectionIso {W Z : Scheme.{u}} {pr : W ⟶ Z} {L : W.Modules} {N : Z.Modules}
    (e : (Scheme.Modules.pullback pr).obj N ≅ L) {s : Z ⟶ W} (hs : s ≫ pr = 𝟙 Z) :
    (Scheme.Modules.pullback s).obj L ≅ N :=
  (Scheme.Modules.pullback s).mapIso e.symm ≪≫ (Scheme.Modules.pullbackComp s pr).app N ≪≫
    (Scheme.Modules.pullbackCongr hs).app N ≪≫ (Scheme.Modules.pullbackId Z).app N

/-- A module pulled back from the target of a morphism has isomorphic pullbacks along any two
sections of that morphism. -/
theorem nonempty_iso_pullback_of_sections {W Z : Scheme.{u}} {pr : W ⟶ Z} {L : W.Modules}
    {N : Z.Modules} (e : (Scheme.Modules.pullback pr).obj N ≅ L) {s t : Z ⟶ W}
    (hs : s ≫ pr = 𝟙 Z) (ht : t ≫ pr = 𝟙 Z) :
    Nonempty ((Scheme.Modules.pullback s).obj L ≅ (Scheme.Modules.pullback t).obj L) :=
  ⟨pullbackSectionIso e hs ≪≫ (pullbackSectionIso e ht).symm⟩

/-- The base change along `h : T ⟶ S` of an open subscheme of affine `n`-space over `S`, as an
open immersion into affine `n`-space over `T`. -/
private abbrev baseChangeToAffineSpace {n : Type u} {S T : Scheme.{u}} (U : (𝔸(n; S)).Opens)
    (h : T ⟶ S) : Limits.pullback (U.ι ≫ 𝔸(n; S) ↘ S) h ⟶ 𝔸(n; T) :=
  (Limits.pullbackRightPullbackFstIso (𝔸(n; S) ↘ S) h U.ι).inv ≫
    Limits.pullback.snd U.ι (Limits.pullback.fst (𝔸(n; S) ↘ S) h) ≫
      (AffineSpace.isPullback_map (n := n) h).isoPullback.inv

/-- The base change of an open subscheme of affine `n`-space along a morphism from the spectrum
of a field `K` is an open subscheme of affine `n`-space over `K`, so its Picard group is trivial
by Tag 0BDA. -/
@[sga "6 X 7.18.5" "special case"]
theorem subsingleton_picardGroup_pullback_openAffineSpace (K : Type u) [Field K] {n : Type u}
    {S : Scheme.{u}} (U : (𝔸(n; S)).Opens) (h : Spec (.of K) ⟶ S) :
    Subsingleton (PicardGroup (Limits.pullback (U.ι ≫ 𝔸(n; S) ↘ S) h).presheaf
      (Limits.pullback (U.ι ≫ 𝔸(n; S) ↘ S) h).ringCatSheaf.2) :=
  subsingleton_of_iso (Scheme.Hom.isoOpensRange (baseChangeToAffineSpace U h)).symm
    (Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace K n _)

/-- The fibre over `x` of the projection `X ×_S V → X` is the base change of `V → S` along the
morphism `Spec κ(x) → X → S`. -/
private def fiberFstIso {X V S : Scheme.{u}} (f : X ⟶ S) (g : V ⟶ S) (x : X) :
    (Limits.pullback.fst f g).fiber x ≅ Limits.pullback g (X.fromSpecResidueField x ≫ f) :=
  Limits.pullbackSymmetry _ _ ≪≫
    Limits.pullbackRightPullbackFstIso f g (X.fromSpecResidueField x) ≪≫
      Limits.pullbackSymmetry _ _

/-- **Every fibre of the projection `X ×_{Spec k} U → X` has trivial Picard group.** The fibre
over `x` is the base change of `U` along `Spec κ(x) → Spec k`, an open subscheme of affine
`n`-space over the field `κ(x)`, so Tag 0BDA applies. -/
theorem subsingleton_picardGroup_fiber_fst (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {n : Type u} (U : (𝔸(n; Spec (.of k))).Opens) (x : X) :
    Subsingleton (PicardGroup
      ((Limits.pullback.fst f (openAffineSpaceOver k U)).fiber x).presheaf
      ((Limits.pullback.fst f (openAffineSpaceOver k U)).fiber x).ringCatSheaf.2) :=
  subsingleton_of_iso (fiberFstIso f (openAffineSpaceOver k U) x).symm
    (subsingleton_picardGroup_pullback_openAffineSpace ↥(X.residueField x) U
      (X.fromSpecResidueField x ≫ f))

/-- Affine `n`-space over a field `K` is integral: it is the spectrum of a polynomial algebra
over `K`, which is a domain. -/
private theorem isIntegral_affineSpace (K : Type u) [Field K] (n : Type u) :
    AlgebraicGeometry.IsIntegral 𝔸(n; Spec (.of K)) :=
  IsIntegral.of_isIso (AffineSpace.SpecIso n (CommRingCat.of K)).inv

/-- The base change along a morphism from the spectrum of a field `K` of an open subscheme of
affine `n`-space is an open subscheme of affine `n`-space over `K`, hence integral as soon as it
is nonempty. -/
private theorem isIntegral_pullback_openAffineSpace (K : Type u) [Field K] {n : Type u}
    {S : Scheme.{u}} (U : (𝔸(n; S)).Opens) (h : Spec (.of K) ⟶ S)
    (hne : Nonempty ↥(Limits.pullback (U.ι ≫ 𝔸(n; S) ↘ S) h)) :
    AlgebraicGeometry.IsIntegral (Limits.pullback (U.ι ≫ 𝔸(n; S) ↘ S) h) :=
  haveI := isIntegral_affineSpace K n
  haveI := hne
  isIntegral_of_isOpenImmersion (baseChangeToAffineSpace U h)

/-- **Every fibre of the projection `X ×_{Spec k} U → X` is integral.** The fibre over `x` is the
base change of `U` along `Spec κ(x) → Spec k`, an open subscheme of affine `n`-space over the
field `κ(x)`, and a `k`-rational point `p` of `U` makes it nonempty: the section
`sectionOfPoint f p hp` of the projection meets every fibre. -/
theorem isIntegral_fiber_fst (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {n : Type u} (U : (𝔸(n; Spec (.of k))).Opens)
    (p : Spec (.of k) ⟶ U.toScheme)
    (hp : p ≫ openAffineSpaceOver k U = 𝟙 (Spec (.of k))) (x : X) :
    AlgebraicGeometry.IsIntegral
      ((Limits.pullback.fst f (openAffineSpaceOver k U)).fiber x) := by
  have hx : (Limits.pullback.fst f (openAffineSpaceOver k U)).base
      ((sectionOfPoint f p hp).base x) = x := congr($(sectionOfPoint_fst f p hp).base x)
  have hne : Nonempty ((Limits.pullback.fst f (openAffineSpaceOver k U)).fiber x) :=
    hx ▸ ⟨(Limits.pullback.fst f (openAffineSpaceOver k U)).asFiber _⟩
  have : AlgebraicGeometry.IsIntegral (Limits.pullback (openAffineSpaceOver k U)
      (X.fromSpecResidueField x ≫ f)) :=
    isIntegral_pullback_openAffineSpace ↥(X.residueField x) U
      (X.fromSpecResidueField x ≫ f)
      ⟨(fiberFstIso f (openAffineSpaceOver k U) x).hom.base hne.some⟩
  exact IsIntegral.of_isIso (fiberFstIso f (openAffineSpaceOver k U) x).inv

/-- **Stacks Project, Tag 0BEH, granting Tag 0BD7 at the projection.** Let `k` be a field, `X` a
normal variety over `k`, and `U ⊆ 𝔸^n_k` an open subscheme with `k`-rational points
`p, q ∈ U(k)`. For every invertible module `ℒ` on `X ×_{Spec k} U` the restrictions
`ℒ|_{X × p}` and `ℒ|_{X × q}` are isomorphic.

Tag 0BD7 at the projection `X ×_{Spec k} U → X` is carried as the hypothesis `h0BD7`; its
antecedent, triviality of `ℒ` on the generic fibre, is discharged from
`subsingleton_picardGroup_fiber_fst`, which is the appeal to Tag 0BDA of the source's proof.

For the tag with `h0BD7` discharged, and with the index type of affine space a natural number as
the tag asks, see `Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint_of_finite`; this form
keeps its own registration, the index type here being arbitrary. -/
-- The `@[stacks 0BEH]` registration is deliberately absent here: this statement assumes its
-- own input, and nonempty_iso_pullback_sectionOfPoint_of_finite (:256) discharges h0BD7.
theorem nonempty_iso_pullback_sectionOfPoint (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] [IsNormal X] {n : Type u}
    (U : (𝔸(n; Spec (.of k))).Opens) (p q : Spec (.of k) ⟶ U.toScheme)
    (hp : p ≫ openAffineSpaceOver k U = 𝟙 (Spec (.of k)))
    (hq : q ≫ openAffineSpaceOver k U = 𝟙 (Spec (.of k)))
    (L : (Limits.pullback f (openAffineSpaceOver k U)).Modules)
    [IsInvertible (Limits.pullback f (openAffineSpaceOver k U)).presheaf
      (structureSheafRing
        (Limits.pullback f (openAffineSpaceOver k U)).toRingedSpace).property L]
    (h0BD7 : IsTrivial
        ((Limits.pullback.fst f (openAffineSpaceOver k U)).fiber (genericPoint X)).presheaf
        ((Limits.pullback.fst f (openAffineSpaceOver k U)).fiber
          (genericPoint X)).ringCatSheaf.2
        ((Scheme.Modules.pullback ((Limits.pullback.fst f
          (openAffineSpaceOver k U)).fiberι (genericPoint X))).obj L) →
      ∃ N : X.Modules,
        IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property N ∧
          Nonempty ((Scheme.Modules.pullback
            (Limits.pullback.fst f (openAffineSpaceOver k U))).obj N ≅ L)) :
    Nonempty ((Scheme.Modules.pullback (sectionOfPoint f p hp)).obj L ≅
      (Scheme.Modules.pullback (sectionOfPoint f q hq)).obj L) := by
  obtain ⟨N, -, ⟨e⟩⟩ := h0BD7 (isTrivial_of_subsingleton
    (subsingleton_picardGroup_fiber_fst k f U (genericPoint X)) _
    (Stacks.Modules.isInvertible_pullback _ L))
  exact nonempty_iso_pullback_of_sections e (sectionOfPoint_fst f p hp)
    (sectionOfPoint_fst f q hq)

/-- **Stacks Project, Tag 0BEH.** Let `k` be a field, `X` a normal variety over `k`, and
`U ⊆ 𝔸^n_k` an open subscheme with `k`-rational points `p, q ∈ U(k)`. For every invertible module
`ℒ` on `X ×_{Spec k} U` the restrictions `ℒ|_{X × p}` and `ℒ|_{X × q}` are isomorphic.

Nothing is assumed beyond the source's hypotheses. The appeal to [Stacks, Tag 0BD7] at the
projection `pr : X ×_{Spec k} U → X` is made through
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat`,
whose hypotheses hold here: `pr` is the base change of `U → Spec k`, which is flat (an open
immersion followed by the structure morphism of affine space) and, `n` being finite, locally of
finite type; `X` is integral, normal and — being of finite type over a field — locally
Noetherian, and so is `X ×_{Spec k} U`; and every fibre of `pr` is integral by
`Stacks.PicardGroup.isIntegral_fiber_fst`. Its remaining hypothesis, triviality of `ℒ` on the
generic fibre, is the one `Stacks.PicardGroup.nonempty_iso_pullback_sectionOfPoint` discharges
from [Stacks, Tag 0BDA]. -/
@[stacks 0BEH "k a field, X a normal variety over k, U an open of affine n-space over k with \
two k-rational points: an invertible module on X ×_{Spec k} U has isomorphic restrictions to \
X × p and X × q"]
theorem nonempty_iso_pullback_sectionOfPoint_of_finite (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] [IsNormal X] {n : Type u} [Finite n]
    (U : (𝔸(n; Spec (.of k))).Opens) (p q : Spec (.of k) ⟶ U.toScheme)
    (hp : p ≫ openAffineSpaceOver k U = 𝟙 (Spec (.of k)))
    (hq : q ≫ openAffineSpaceOver k U = 𝟙 (Spec (.of k)))
    (L : (Limits.pullback f (openAffineSpaceOver k U)).Modules)
    [hL : IsInvertible (Limits.pullback f (openAffineSpaceOver k U)).presheaf
      (structureSheafRing
        (Limits.pullback f (openAffineSpaceOver k U)).toRingedSpace).property L] :
    Nonempty ((Scheme.Modules.pullback (sectionOfPoint f p hp)).obj L ≅
      (Scheme.Modules.pullback (sectionOfPoint f q hq)).obj L) := by
  refine nonempty_iso_pullback_sectionOfPoint k f U p q hp hq L fun hgen => ?_
  have : LocallyOfFiniteType (openAffineSpaceOver k U) := by
    unfold openAffineSpaceOver; infer_instance
  have : Flat (openAffineSpaceOver k U) := by
    unfold openAffineSpaceOver
    have := AlgebraicGeometry.flat_affineSpace n (Spec (.of k))
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat
    (Limits.pullback.fst f (openAffineSpaceOver k U)) L hL
    (isIntegral_fiber_fst k f U p hp) (Or.inr inferInstance) hgen

end Stacks.PicardGroup

end
