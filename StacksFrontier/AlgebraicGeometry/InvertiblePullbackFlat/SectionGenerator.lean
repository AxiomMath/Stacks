module

public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# From a generator of a stalk to a generator of the sections on a neighbourhood

The penultimate paragraph of [Stacks, Tag 0BD7] produces, at a point `x`, a meromorphic
function `g/r` on the base with the property that `φ^*(g/r) s` generates the stalk `ℒ_x`, and
then asserts that `φ^*(g/r) s` therefore "generates `ℒ` in a neighbourhood `U` of `x`". This
file supplies that passage, for an invertible sheaf of modules on a ringed space whose stalks
are local rings: a section whose germ at `x` generates the stalk generates the sections over
every open inside a suitable neighbourhood of `x`.

"Generates" is spelled as in
`StacksFrontier/AlgebraicGeometry/InvertibleTrivialization/Basic.lean`, where the converse half
of [Stacks, Tag 0B8M] is recorded: `c ↦ c • t|_V` is a bijection `𝒪_X(V) → ℒ(V)`. The
hypothesis at the stalk is the non-membership `germ_x t ∉ 𝔪_x ℒ_x`, which for a *global* section
is membership of the nonvanishing locus
`Stacks.SheafOfModules.nonvanishingLocus`; that locus is open by
`Stacks.SheafOfModules.isOpen_nonvanishingLocus` (Tag 01CY) and is compatible with pullback by
`Stacks.SheafOfModules.preimage_nonvanishingLocus` (Tag 0H78), so the topology of the paragraph
is already available and what is added here is only the passage from the stalk to the sections.

## Main results

* `Stacks.SheafOfModules.bijective_smul_of_forall_exists_bijective_smul`: **generating the
  sections is a local property of an open.** For an arbitrary sheaf of modules and an arbitrary
  section `u` over `V`, if `c ↦ c • u|_K` is bijective for every `K` small enough around each
  point of `V`, then `c ↦ c • u` is bijective over `V` itself. Neither invertibility nor
  locality of the stalks enters; this is the sheaf condition alone.
* `Stacks.SheafOfModules.exists_le_tensorPairing_eq_unitSection`: a section whose germ at `x`
  generates the stalk pairs to the unit section, against a trivialization `ψ : ℒ ⊗ 𝒩 ≅ 𝒪_X`, on
  some neighbourhood of `x` inside its own domain.
* `Stacks.SheafOfModules.exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top`: **the
  passage asked for**. A section `t` of an invertible `ℒ` over `U`, whose germ at `x ∈ U`
  does not lie in `𝔪_x ℒ_x`, generates `ℒ(V)` for every open `V` inside some neighbourhood
  `W ⊆ U` of `x`.
* `Stacks.SheafOfModules.exists_bijective_smul_of_mem_nonvanishingLocus`: the same statement for
  a global section, with the hypothesis read off the nonvanishing locus.
* `Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`: a section
  over `U` generates over *every* open `V ≤ U` at all of whose points its germ generates, not
  only near each such point — the form in which the last paragraph of Tag 0BD7 uses the
  generator, where `φ^*(g_y) s` is regular only on a neighbourhood of the fibre and what is
  wanted is a generator on an open neighbourhood of the whole fibre.
* `Stacks.SheafOfModules.bijective_smul_of_subset_nonvanishingLocus`: its `U = ⊤` case, with the
  hypothesis in the form of the nonvanishing locus of a global section.

## Implementation notes

The proof of `exists_le_tensorPairing_eq_unitSection` is the proof of
`Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection` with the generator of the stalk
*given* rather than produced from freeness: there the section of `ℒ` is built from a chosen
isomorphism `ℒ_x ≃ₗ 𝒪_{X,x}`, here it is the restriction of the section supplied, and the
conclusion therefore records that the neighbourhood lies inside the section's own domain. Once
the pairing with the unit section is available,
`Stacks.SheafOfModules.bijective_smul_of_tensorPairing_eq_unitSection` gives bijectivity over
every smaller open with no further work, which is why the statement quantifies over all
`V ≤ W` rather than only over `W`.

Restrictions are composed by `PresheafOfModules.map_comp_apply` together with uniqueness of
morphisms in the category of opens, so the generator produced is literally a restriction of `t`
and not merely a section with the same germ.

The local-to-global statement is phrased with `PresheafOfModules.restrictₛₗ`, not with
`PresheafOfModules.map`, and that is forced rather than cosmetic. `L.val.map i` lands in
`(ModuleCat.restrictScalars _).obj (L.val.obj (op K))`, so in `d • L.val.map i u` the scalar
action is found at that type and the result cannot then be fed to another restriction: the
composite is rejected as not type-correct at `implicit` transparency even though it is
well-typed at `default`. `restrictₛₗ` is the same function with `L.val.obj (op K)` as its
*declared* codomain, which is what instance search and the rewrite motives see. The two
spellings are interchangeable by `exact` — `PresheafOfModules.restrictₛₗ_apply` is `rfl` — so
the corollaries below are stated at the `map` spelling of their siblings and cross by defeq.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

section LocalToGlobal

variable {X : RingedSpace.{u, u}} {L : SheafOfModules.{u} (structureSheafRing X)}

/-- Restricting a scalar multiple of a section restricts the scalar and the section. -/
theorem restrictₛₗ_smul_presheafMap {K K' : Opens X.carrier} (i : K ⟶ K')
    (d : X.presheaf.obj (op K')) (w : L.val.obj (op K')) :
    L.val.restrictₛₗ i.op (d • w) = (X.presheaf.map i.op d) • L.val.restrictₛₗ i.op w := by
  rw [PresheafOfModules.restrictₛₗ_apply, L.val.map_smul]
  rfl

/-- Restricting a restriction of a section is restricting along the composite. -/
private theorem restrictₛₗ_restrictₛₗ_eq {K K' K'' : Opens X.carrier} (i : K ⟶ K') (j : K' ⟶ K'')
    (k : K ⟶ K'') (w : L.val.obj (op K'')) :
    L.val.restrictₛₗ i.op (L.val.restrictₛₗ j.op w) = L.val.restrictₛₗ k.op w := by
  change L.val.map i.op (L.val.map j.op w) = L.val.map k.op w
  rw [← L.val.map_comp_apply]
  congr 1

/-- If every point of `V` has a neighbourhood `W ⊆ V` on which `c ↦ c • u|_W` is injective, then
`c ↦ c • u` is injective on `V`. -/
theorem injective_smul_of_forall_exists_injective_smul
    {V : Opens X.carrier} (u : L.val.obj (op V))
    (h : ∀ y ∈ V, ∃ (W : Opens X.carrier) (_ : y ∈ W) (hWV : W ≤ V),
      Function.Injective fun c : X.presheaf.obj (op W) =>
        c • L.val.restrictₛₗ (homOfLE hWV).op u) :
    Function.Injective fun c : X.presheaf.obj (op V) => c • u := by
  intro c c' hcc
  refine TopCat.Presheaf.section_ext (C := CommRingCat.{u}) ⟨X.presheaf, X.IsSheaf⟩ V c c'
    fun z hz => ?_
  obtain ⟨W, hzW, hWV, hinj⟩ := h z hz
  have key : (X.presheaf.map (homOfLE hWV).op c) • L.val.restrictₛₗ (homOfLE hWV).op u
      = (X.presheaf.map (homOfLE hWV).op c') • L.val.restrictₛₗ (homOfLE hWV).op u := by
    rw [← restrictₛₗ_smul_presheafMap (homOfLE hWV) c u,
      ← restrictₛₗ_smul_presheafMap (homOfLE hWV) c' u]
    exact congrArg (L.val.restrictₛₗ (homOfLE hWV).op) hcc
  rw [← X.presheaf.germ_res_apply (homOfLE hWV) z hzW c,
    ← X.presheaf.germ_res_apply (homOfLE hWV) z hzW c', hinj key]

/-- **Generating the sections is a local property of an open.** Let `u` be a section of a sheaf
of modules `ℒ` over an open `V`. If every point of `V` has a neighbourhood `W ⊆ V` such that
`c ↦ c • u|_K` is a bijection `𝒪_X(K) → ℒ(K)` for every open `K ≤ W`, then `c ↦ c • u` is already
a bijection `𝒪_X(V) → ℒ(V)`.

Both halves are the sheaf condition: injectivity because a section of `𝒪_X` is determined by its
germs, surjectivity because the local preimages are unique, hence agree on overlaps, hence glue.
Neither invertibility of `ℒ` nor locality of the stalks is used — this is the local-to-global step
on its own, with the hypotheses that produce the local bijections left to the caller. -/
theorem bijective_smul_of_forall_exists_bijective_smul
    {V : Opens X.carrier} (u : L.val.obj (op V))
    (h : ∀ y ∈ V, ∃ (W : Opens X.carrier) (_ : y ∈ W) (hWV : W ≤ V),
      ∀ (K : Opens X.carrier) (hKW : K ≤ W),
        Function.Bijective fun c : X.presheaf.obj (op K) =>
          c • L.val.restrictₛₗ (homOfLE (hKW.trans hWV)).op u) :
    Function.Bijective fun c : X.presheaf.obj (op V) => c • u := by
  classical
  refine ⟨injective_smul_of_forall_exists_injective_smul u fun y hy => ?_, fun m => ?_⟩
  · obtain ⟨W, hyW, hWV, hb⟩ := h y hy
    exact ⟨W, hyW, hWV, (hb W le_rfl).1⟩
  choose W hmemW hWV hb using fun y : V => h y.1 y.2
  choose c hc using fun y : V => (hb y (W y) le_rfl).2
    (L.val.restrictₛₗ (homOfLE (hWV y)).op m)
  have hc' : ∀ y : V, (c y) • L.val.restrictₛₗ (homOfLE (hWV y)).op u
      = L.val.restrictₛₗ (homOfLE (hWV y)).op m := hc
  have step : ∀ (y₀ : V) {K : Opens X.carrier} (i : K ⟶ W y₀) (k : K ⟶ V),
      (X.presheaf.map i.op (c y₀)) • L.val.restrictₛₗ k.op u
        = L.val.restrictₛₗ k.op m := by
    intro y₀ K i k
    rw [← restrictₛₗ_restrictₛₗ_eq i (homOfLE (hWV y₀)) k u,
      ← restrictₛₗ_smul_presheafMap i (c y₀) (L.val.restrictₛₗ (homOfLE (hWV y₀)).op u),
      hc' y₀, restrictₛₗ_restrictₛₗ_eq i (homOfLE (hWV y₀)) k m]
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf (fun y : V => W y) c := by
    intro y y'
    refine (hb y (W y ⊓ W y') inf_le_left).1 ?_
    dsimp only
    exact (step y _ _).trans (step y' _ _).symm
  obtain ⟨d, hd, -⟩ := X.sheaf.existsUnique_gluing' (fun y : V => W y) V
    (fun y => homOfLE (hWV y))
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hmemW ⟨z, hz⟩⟩) c hcompat
  have hd' : ∀ y : V, X.presheaf.map (homOfLE (hWV y)).op
      (show X.presheaf.obj (op V) from d) = c y := hd
  refine ⟨show X.presheaf.obj (op V) from d, ?_⟩
  refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) ⟨L.val.presheaf, L.isSheaf⟩ V _ m
    fun z hz => ?_
  have hkey : L.val.restrictₛₗ (homOfLE (hWV ⟨z, hz⟩)).op
        ((show X.presheaf.obj (op V) from d) • u)
      = L.val.restrictₛₗ (homOfLE (hWV ⟨z, hz⟩)).op m := by
    rw [restrictₛₗ_smul_presheafMap (homOfLE (hWV ⟨z, hz⟩)) (show X.presheaf.obj (op V) from d) u,
      hd' ⟨z, hz⟩, hc' ⟨z, hz⟩]
  rw [← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE (hWV ⟨z, hz⟩)) z (hmemW ⟨z, hz⟩)
      ((show X.presheaf.obj (op V) from d) • u),
    ← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE (hWV ⟨z, hz⟩)) z (hmemW ⟨z, hz⟩) m]
  exact congrArg _ hkey

end LocalToGlobal

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  {L N : SheafOfModules.{u} (structureSheafRing X)}

/-- **A section generating a stalk pairs to the unit section near that point.** Given a
trivialization `ψ : ℒ ⊗_{𝒪_X} 𝒩 ≅ 𝒪_X` and a section `t` of `ℒ` over `U` whose germ at `x ∈ U`
does not lie in `𝔪_x ℒ_x`, there is an open `W` with `x ∈ W ⊆ U` and a section of `𝒩` over `W`
pairing with `t|_W` to the unit section.

The germ of `t` pairs to `1` with some element of the stalk of `𝒩`, because an element outside
`𝔪_x ℒ_x` has unit image under the stalk pairing; that element is the germ of a section on a
neighbourhood, and two sections with equal germs agree on a smaller neighbourhood. -/
theorem exists_le_tensorPairing_eq_unitSection
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X))
    {U : Opens X.carrier} (t : L.val.obj (op U)) (x : X.carrier) (hxU : x ∈ U)
    (ht : grpGerm X L.val x U hxU t ∉
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x))) :
    ∃ (W : Opens X.carrier) (_ : x ∈ W) (hWU : W ≤ U) (b : N.val.obj (op W)),
      tensorPairing ψ W (L.val.map (homOfLE hWU).op t) b = unitSection X W := by
  obtain ⟨n, hn⟩ := exists_tmul_eq_one (stalkPairing ψ x) _ ht
  obtain ⟨U₂, hx₂, b₂, hb₂⟩ := exists_grpGerm_eq X N.val x n
  set U' : Opens X.carrier := U ⊓ U₂ with hU'
  have hxU' : x ∈ U' := ⟨hxU, hx₂⟩
  set t' : L.val.obj (op U') := L.val.map (homOfLE (inf_le_left : U' ≤ U)).op t with ht'
  obtain ⟨b, hgb⟩ : ∃ b : N.val.obj (op U'), grpGerm X N.val x U' hxU' b = n :=
    ⟨N.val.map (homOfLE (inf_le_right : U' ≤ U₂)).op b₂,
      Eq.trans (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) N.val.presheaf
        (homOfLE (inf_le_right : U' ≤ U₂)) x hxU' b₂) hb₂⟩
  have hgt : grpGerm X L.val x U' hxU' t' = grpGerm X L.val x U hxU t :=
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf
      (homOfLE (inf_le_left : U' ≤ U)) x hxU' t
  have hring : ringGerm X x U' hxU' (tensorPairing ψ U' t' b) = 1 := by
    rw [← stalkPairing_germ ψ x U' hxU' t' b, hgt, hgb, hn]
  have hgrp : grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x U' hxU'
      (tensorPairing ψ U' t' b)
      = grpGerm X (SheafOfModules.unit (structureSheafRing X)).val x ⊤ (Opens.mem_top x)
        (unitSection X ⊤) := by
    rw [← ringGerm_smul_unitGerm X x U' hxU' (tensorPairing ψ U' t' b), hring, one_smul, unitGerm]
  obtain ⟨W, hxW, iW, jW, hW⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    (SheafOfModules.unit (structureSheafRing X)).val.presheaf x hxU' (Opens.mem_top x)
    (tensorPairing ψ U' t' b) (unitSection X ⊤) hgrp
  have hWU : W ≤ U := iW.le.trans inf_le_left
  have hres : L.val.map iW.op t' = L.val.map (homOfLE hWU).op t := by
    exact restrictₛₗ_restrictₛₗ_eq iW (homOfLE inf_le_left) _ t
  refine ⟨W, hxW, hWU, N.val.map iW.op b, ?_⟩
  rw [← hres, ← tensorPairing_res]
  exact hW.trans (map_one ((structureSheafRing X).obj.map jW.op).hom)

variable (L) in
/-- **A generator of a stalk generates the sections on a neighbourhood.** Let `ℒ` be an
invertible sheaf of modules on a ringed space whose stalks are local rings, and let `t` be a
section of `ℒ` over `U` whose germ at `x ∈ U` does not lie in `𝔪_x ℒ_x`. Then there is an open
`W` with `x ∈ W ⊆ U` such that `c ↦ c • t|_V` is a bijection `𝒪_X(V) → ℒ(V)` for *every* open
`V ≤ W`.

This is the step "`φ^*(g) s` generates `ℒ_x`, hence `φ^*(g) s` generates `ℒ` in a neighbourhood
`U` of `x`" of the penultimate paragraph of Stacks Tag 0BD7. -/
theorem exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) (x : X.carrier) (hxU : x ∈ U)
    (ht : grpGerm X L.val x U hxU t ∉
      maximalIdeal (ringStalk X x) • (⊤ : Submodule (ringStalk X x) (grpStalk X L.val x))) :
    ∃ (W : Opens X.carrier) (_ : x ∈ W) (hWU : W ≤ U),
      ∀ (V : Opens X.carrier) (hVW : V ≤ W),
        Function.Bijective fun c : X.presheaf.obj (op V) =>
          c • (L.val.map (homOfLE (hVW.trans hWU)).op t) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  obtain ⟨W, hxW, hWU, b, hab⟩ := exists_le_tensorPairing_eq_unitSection ψ t x hxU ht
  refine ⟨W, hxW, hWU, fun V hVW => ?_⟩
  have h := bijective_smul_of_tensorPairing_eq_unitSection ψ W
    (L.val.map (homOfLE hWU).op t) b hab V hVW
  have hres : L.val.map (homOfLE hVW).op (L.val.map (homOfLE hWU).op t)
      = L.val.map (homOfLE (hVW.trans hWU)).op t :=
    restrictₛₗ_restrictₛₗ_eq _ _ _ t
  rwa [hres] at h

variable (L) in
/-- **The nonvanishing locus is where a global section generates.** For an invertible sheaf of
modules on a ringed space whose stalks are local rings and a global section `s`, every point of
the nonvanishing locus of `s` has an open neighbourhood `W` such that `c ↦ c • s|_V` is a
bijection `𝒪_X(V) → ℒ(V)` for every open `V ≤ W`.

Together with `Stacks.SheafOfModules.isOpen_nonvanishingLocus` this says that a global section
generates `ℒ` on a neighbourhood of each point where it does not vanish. -/
@[ega "0 5.5.2" "partial"]
theorem exists_bijective_smul_of_mem_nonvanishingLocus
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections)
    (x : X.carrier) (hx : x ∈ nonvanishingLocus L s) :
    ∃ (W : Opens X.carrier) (_ : x ∈ W),
      ∀ (V : Opens X.carrier) (_ : V ≤ W),
        Function.Bijective fun c : X.presheaf.obj (op V) => c • s.eval (op V) := by
  obtain ⟨W, hxW, hWU, hbij⟩ := exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top L
    (U := ⊤) (s.eval (op ⊤)) x (Opens.mem_top x) hx
  refine ⟨W, hxW, fun V hVW => ?_⟩
  have h := hbij V hVW
  rwa [show L.val.map (homOfLE (hVW.trans hWU)).op (s.eval (op ⊤)) = s.eval (op V) from
    PresheafOfModules.sections_property s (homOfLE (hVW.trans hWU)).op] at h

variable (L) in
/-- **A section over `U` generates on the whole of the part of `U` where its germ generates.**
Let `t` be a section of an invertible `ℒ` over an open `U` and let `V ≤ U` be an open at every
point of which the germ of `t` does not lie in `𝔪_y ℒ_y`. Then `c ↦ c • t|_V` is a bijection
`𝒪_X(V) → ℒ(V)` — on the whole of `V`, not merely on a neighbourhood of each of its points.

This is the form the last paragraph of Stacks Tag 0BD7 uses. There the generator is `φ^*(g_y) s`,
which is regular only on a neighbourhood `U` of the fibre and is *never* a global section, and
what is wanted is that it generates on an open neighbourhood `V` of the whole fibre. -/
theorem bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) (V : Opens X.carrier) (hVU : V ≤ U)
    (ht : ∀ (y : X.carrier) (hy : y ∈ V), grpGerm X L.val y U (hVU hy) t ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y))) :
    Function.Bijective fun c : X.presheaf.obj (op V) =>
      c • L.val.map (homOfLE hVU).op t := by
  have main : Function.Bijective fun c : X.presheaf.obj (op V) =>
      c • L.val.restrictₛₗ (homOfLE hVU).op t := by
    refine bijective_smul_of_forall_exists_bijective_smul
      (L.val.restrictₛₗ (homOfLE hVU).op t) fun y hy => ?_
    obtain ⟨W, hyW, hWU, hbij⟩ :=
      exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top L t y (hVU hy) (ht y hy)
    refine ⟨W ⊓ V, ⟨hyW, hy⟩, inf_le_right, fun K hKW => ?_⟩
    have e : L.val.restrictₛₗ (homOfLE (hKW.trans (inf_le_right : W ⊓ V ≤ V))).op
          (L.val.restrictₛₗ (homOfLE hVU).op t)
        = L.val.restrictₛₗ (homOfLE ((hKW.trans (inf_le_left : W ⊓ V ≤ W)).trans hWU)).op t :=
      restrictₛₗ_restrictₛₗ_eq _ _ _ t
    exact e ▸ hbij K (hKW.trans (inf_le_left : W ⊓ V ≤ W))
  exact main

variable (L) in
/-- **A global section generates on the whole of its nonvanishing locus.** If every point of an
open `V` lies in the nonvanishing locus of a global section `s` of an invertible `ℒ`, then
`c ↦ c • s|_V` is a bijection `𝒪_X(V) → ℒ(V)` — not merely on a neighbourhood of each point of
`V`.

The special case `U = ⊤` of
`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`, kept because
the hypothesis in the form of the nonvanishing locus is what `Stacks.SheafOfModules.sections`
consumers have to hand. -/
theorem bijective_smul_of_subset_nonvanishingLocus
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections)
    (V : Opens X.carrier) (hV : (V : Set X.carrier) ⊆ nonvanishingLocus L s) :
    Function.Bijective fun c : X.presheaf.obj (op V) => c • s.eval (op V) := by
  have h := bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top L (s.eval (op ⊤)) V le_top
    fun y hy => hV hy
  rwa [show L.val.map (homOfLE (le_top : V ≤ ⊤)).op (s.eval (op ⊤)) = s.eval (op V) from
    PresheafOfModules.sections_property s (homOfLE (le_top : V ≤ ⊤)).op] at h

end Stacks.SheafOfModules

end
