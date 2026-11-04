module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealResidueFibre
public import StacksFrontier.RingTheory.Flat.HenselianEssFiniteTypeColimit
public import StacksFrontier.RingTheory.Flat.MittagLefflerLocal

/-!
# A map out of a colimit of free modules into a flat module

Let `(A, 𝔪)` be a local ring, let `(F i, u_{i i'})` be a directed system of free `A`-modules
whose transition maps induce injective maps `F i / 𝔪 F i → F i' / 𝔪 F i'`, let `N` be the
colimit of the system, let `M` be a flat `A`-module and let `u : N → M` be a map whose reduction
`N/𝔪N → M/𝔪M` is injective.  Then `u` is `A`-universally injective.

This is the first paragraph of the proof of Stacks 0AT3: in Situation 0AT0 over a henselian base
one first disposes of the case where `N` is in addition flat over `A`, and in that case Stacks
05U7 presents `N` as such a colimit, each composite `F i → M` is `A`-universally injective by
Stacks 05FQ, and `u` is the colimit of those composites.  The colimit argument itself uses
neither the flatness of `N` nor the henselian hypothesis: both enter only through the colimit
presentation, which is why the general statement takes the presentation as its input, and the
henselian flat case then obtains that presentation from Stacks 05U7.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.ColimitFreeInjectivity.injective_mapQ_leg`: each leg `F i → N` of the colimit is
  itself injective modulo `𝔪`.  This is the step the source leaves implicit when it says that
  injectivity of `ū` makes each `ū_i` injective.
* `Stacks.ColimitFreeInjectivity.rTensor_injective_of_colimit_free`: the universal injectivity
  of `u`.
* `AlgebraicGeometry.universallyInjective_of_colimit_free`: the same conclusion in the bundle of
  Situation 0AT0, for a source module presented as such a colimit.
* `AlgebraicGeometry.universallyInjective_of_henselian_of_flat`: the first paragraph of the
  proof of Stacks 0AT3. In Situation 0AT0 over a henselian base with `N` flat over `A`, the map
  `u` is `A`-universally injective; the colimit presentation is the one constructed in the proof
  of Stacks 05U7.

The second paragraph of the proof of Stacks 0AT3, which removes the flatness of `N` by the
flattening ideal of Stacks 05PG, is the square-zero step in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianSquareZeroStep`.

## Implementation notes

The reduction of a map modulo the maximal ideal is the canonical `Submodule.mapQ` between the
quotients by `𝔪 • ⊤`, as in Stacks 05FQ
(`Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal`), in Stacks 0AS5,
and in the bundle of Stacks 0AT0; so the hypothesis on the transition maps is literally the one
Stacks 05U7 produces and the hypothesis on `u` is literally the one Stacks 0AT0 carries.
Universal injectivity is spelled out as injectivity of `u ⊗ id_Q` for every test module `Q`,
`Mathlib` having no name for it, again as in Stacks 05FQ.

The index category is a nonempty directed preorder, which is what the source means by a filtered
colimit of modules and what the geometric proof of Stacks 05U7 supplies.  A directed preorder is
filtered (`CategoryTheory.isFiltered_of_directed_le_nonempty`), which is what makes the
element-level description of the colimit available: an element of a stage killed by its leg is
killed by a transition map.

The modules of the system, the target and the test modules live in one universe `v`, with
`Small.{v} A`.  This is inherited from Stacks 05FQ, through Stacks 0AS5, and is no restriction
when `v = max u v`, in particular when the ring and the modules share a universe.  The index type
is taken in `v` as well, which is what lets the forgetful functor of `ModuleCat.{v} A` be used to
read the colimit on elements.

That the legs of the colimit are injective modulo `𝔪` is proved by comparing two descriptions of
`𝔪 • N`: it is the supremum over the stages of the images of `𝔪 • F i`, because the images of the
legs cover `N` and `𝔪 • -` commutes with suprema.  An element of `F i` landing in `𝔪 • N` is
therefore congruent, after a transition map, to an element of `𝔪 • F j`; a common upper bound and
the element-level description of the colimit move the congruence to a single stage, where the
hypothesis on the transition maps applies.

## References

* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 05FQ](https://stacks.math.columbia.edu/tag/05FQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.MittagLeffler.DirectedColimit
open scoped TensorProduct

universe u v

namespace Stacks.ColimitFreeInjectivity

variable {A : Type u} [CommRing A] {J : Type v} [Preorder J] [IsDirectedOrder J]
  {F : J ⥤ ModuleCat.{v} A} {c : Cocone F}

/-- An element of a stage killed by its leg is killed by a transition map. -/
private lemma exists_map_eq_zero [Nonempty J] (hc : IsColimit c) {i : J} (y : F.obj i)
    (hy : legHom c i y = 0) : ∃ (j : J) (f : i ⟶ j), (F.map f).hom y = 0 := by
  have : IsFiltered J := isFiltered_of_directed_le_nonempty J
  have : PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{v} A)) := by
    have : PreservesColimitsOfSize.{v, v} (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{v, u, v, v} A
    exact comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}) (CategoryTheory.forget AddCommGrpCat.{v})
  have : PreservesColimitsOfShape J (CategoryTheory.forget (ModuleCat.{v} A)) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
  have h0 : legHom c i y = legHom c i 0 := by rw [hy, map_zero]
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq F hc y (0 : F.obj i) h0
  exact ⟨k, f, by simpa using hfg⟩

/-- The images under the legs of the submodules `I • F i` form a directed family. -/
private lemma directed_map_smul_top_leg (I : Ideal A) :
    Directed (· ≤ ·) fun i : J ↦ (I • (⊤ : Submodule A (F.obj i))).map (legHom c i) := by
  have h (i : J) : (I • (⊤ : Submodule A (F.obj i))).map (legHom c i) =
      I • LinearMap.range (legHom c i) := by rw [Submodule.map_smul'', Submodule.map_top]
  simp only [h]
  exact directed_range_legHom.mono_comp (· ≤ ·) (g := (I • ·))
    fun _ _ hxy ↦ Submodule.smul_mono le_rfl hxy

omit [IsDirectedOrder J] in
/-- `I` times the colimit is the supremum over the stages of the images of `I` times the stage. -/
private lemma iSup_map_smul_top_leg_eq (hc : IsColimit c) (I : Ideal A) :
    (⨆ i : J, (I • (⊤ : Submodule A (F.obj i))).map (legHom c i)) =
      I • (⊤ : Submodule A (c.pt : Type v)) := by
  calc (⨆ i : J, (I • (⊤ : Submodule A (F.obj i))).map (legHom c i))
      = ⨆ i : J, I • LinearMap.range (legHom c i) := by
        refine iSup_congr fun i ↦ ?_
        rw [Submodule.map_smul'', Submodule.map_top]
    _ = I • ⨆ i : J, LinearMap.range (legHom c i) := (Submodule.smul_iSup).symm
    _ = I • (⊤ : Submodule A (c.pt : Type v)) := by rw [iSup_range_legHom_eq_top hc]

/-- **The legs of the colimit are injective modulo the maximal ideal.** Let `(A, 𝔪)` be a local
ring and let `(F i, u_{i i'})` be a directed system of `A`-modules, indexed by a nonempty directed
preorder, whose transition maps induce injective maps `F i / 𝔪 F i → F i' / 𝔪 F i'`.  Then for
every `i` the leg `F i → N` into the colimit induces an injective map `F i / 𝔪 F i → N / 𝔪 N`.

This is the step the proof of Stacks 0AT3 passes over silently when it concludes from injectivity
of `ū : N/𝔪N → M/𝔪M` that every `ū_i : F i/𝔪 F i → M/𝔪M` is injective. -/
theorem injective_mapQ_leg [IsLocalRing A] [Nonempty J]
    (hinj : ∀ {i j : J} (f : i ⟶ j), Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j))) (F.map f).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map f).hom)))
    (hc : IsColimit c) (i : J) :
    Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (c.pt : Type v))) (legHom c i)
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (legHom c i))) := by
  rw [Submodule.injective_mapQ_smul_top_iff]
  intro y hy
  rw [← iSup_map_smul_top_leg_eq hc] at hy
  obtain ⟨j, hj⟩ :=
    (Submodule.mem_iSup_of_directed _ (directed_map_smul_top_leg (maximalIdeal A))).1 hy
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hj
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hkey : legHom c k
      ((F.map (homOfLE hik)).hom y - (F.map (homOfLE hjk)).hom z) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply, legHom_comp_map, legHom_comp_map,
      hzy, sub_self]
  obtain ⟨l, g, hg⟩ := exists_map_eq_zero hc _ hkey
  have hstage : (F.map g).hom ((F.map (homOfLE hik)).hom y) =
      (F.map g).hom ((F.map (homOfLE hjk)).hom z) := by
    rw [map_sub, sub_eq_zero] at hg
    exact hg
  have hmem : (F.map (homOfLE hik ≫ g)).hom y ∈
      maximalIdeal A • (⊤ : Submodule A (F.obj l)) := by
    have hfac : (F.map (homOfLE hik ≫ g)).hom y =
        (F.map g).hom ((F.map (homOfLE hik)).hom y) := by
      rw [F.map_comp]; rfl
    rw [hfac, hstage]
    exact Submodule.smul_top_le_comap_smul_top _ (F.map g).hom
      (Submodule.smul_top_le_comap_smul_top _ (F.map (homOfLE hjk)).hom hz)
  exact (Submodule.injective_mapQ_smul_top_iff _ _).1 (hinj (homOfLE hik ≫ g)) y hmem

/-- **The first paragraph of the proof of Stacks 0AT3.** Let `(A, 𝔪)` be a local ring, let
`(F i, u_{i i'})` be a directed system of free `A`-modules indexed by a nonempty directed preorder
whose transition maps induce injective maps `F i / 𝔪 F i → F i' / 𝔪 F i'`, let `N` be the colimit
of the system, let `M` be a flat `A`-module, and let `u : N → M` be an `A`-linear map whose
reduction `N/𝔪N → M/𝔪M` is injective.  Then `u` is `A`-universally injective, that is `u ⊗ id_Q`
is injective for every `A`-module `Q`.

Each composite `F i → N → M` has injective reduction modulo `𝔪`, because the leg does
(`injective_mapQ_leg`) and `u` does by hypothesis, and is therefore `A`-universally injective by
Stacks 05FQ, `F i` being free hence projective and `M` being flat.  Since every element of
`N ⊗ Q` comes from some `F i ⊗ Q`, this forces `u ⊗ id_Q` to be injective. -/
theorem rTensor_injective_of_colimit_free [IsLocalRing A] [Small.{v} A] [Nonempty J]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
    (hfree : ∀ i, Module.Free A (F.obj i))
    (hinj : ∀ {i j : J} (f : i ⟶ j), Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A (F.obj i)))
        (maximalIdeal A • (⊤ : Submodule A (F.obj j))) (F.map f).hom
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (F.map f).hom)))
    (hc : IsColimit c) (u : (c.pt : Type v) →ₗ[A] M)
    (hu : Function.Injective
      (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A (c.pt : Type v)))
        (maximalIdeal A • (⊤ : Submodule A M)) u
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) u))) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module A Q], Function.Injective (u.rTensor Q) := by
  intro Q _ _
  have hcomp : ∀ i : J, Function.Injective ((u ∘ₗ legHom c i).rTensor Q) := by
    intro i
    have := hfree i
    refine Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal
      (u ∘ₗ legHom c i) ?_ Q
    rw [Submodule.injective_mapQ_smul_top_iff]
    intro y hy
    exact (Submodule.injective_mapQ_smul_top_iff _ _).1 (injective_mapQ_leg hinj hc i) y
      ((Submodule.injective_mapQ_smul_top_iff u (maximalIdeal A)).1 hu _ hy)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, y, hy⟩ := exists_legHom_rTensor_eq hc Q x
  have hfac : ((u ∘ₗ legHom c i).rTensor Q) y = u.rTensor Q ((legHom c i).rTensor Q y) := by
    rw [LinearMap.rTensor_comp]; rfl
  have hy0 : y = 0 := by
    refine hcomp i ?_
    rw [map_zero, hfac, hy]
    exact hx
  rw [← hy, hy0, map_zero]

end Stacks.ColimitFreeInjectivity

namespace AlgebraicGeometry

universe u₁ u₂ u₃ u₄ u₅

open Stacks.ColimitFreeInjectivity

/-- Membership in `I • ⊤` transports along a linear equivalence. -/
lemma mem_smul_top_equiv_iff {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (I : Ideal A) (x : M) :
    e x ∈ I • (⊤ : Submodule A N) ↔ x ∈ I • (⊤ : Submodule A M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.smul_top_le_comap_smul_top I e.toLinearMap h⟩
  simpa using Submodule.smul_top_le_comap_smul_top I e.symm.toLinearMap h

/-- Universal injectivity of a single base change is invariant under linear equivalences of the
source and of the target. -/
private lemma injective_rTensor_of_comp_equiv {A : Type*} [CommRing A]
    {M N M' N' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup M'] [Module A M'] [AddCommGroup N'] [Module A N']
    (f : M →ₗ[A] N) (eM : M' ≃ₗ[A] M) (eN : N ≃ₗ[A] N')
    (Q : Type*) [AddCommGroup Q] [Module A Q]
    (h : Function.Injective ((eN.toLinearMap ∘ₗ f ∘ₗ eM.toLinearMap).rTensor Q)) :
    Function.Injective (f.rTensor Q) := by
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.coe_comp] at h
  exact (Function.Injective.of_comp_iff' _ (eM.rTensor Q).bijective).mp h.of_comp

/-- **A map out of a filtered colimit of free modules, in Situation 0AT0.** In Situation 0AT0,
if `N` is a filtered colimit of free `A`-modules whose transition maps induce injective maps
modulo `𝔪_A`, then `u` is `A`-universally injective.

The presentation `hcolim` has the shape of the first conclusion of Stacks 05U7, with the index
category a nonempty directed preorder. -/
theorem universallyInjective_of_colimit_free
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hcolim : ∃ (I : Type (max u₁ u₃ u₄ u₅)) (_ : Preorder I) (_ : IsDirectedOrder I)
        (_ : Nonempty I) (F : I ⥤ ModuleCat.{max u₁ u₃ u₄ u₅} S.A) (c : Limits.Cocone F),
      (∀ i, Module.Free S.A (F.obj i)) ∧
      (∀ {i j : I} (f : i ⟶ j), Function.Injective
        (Submodule.mapQ
          (IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A (F.obj i)))
          (IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A (F.obj j)))
          (F.map f).hom
          (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal S.A)
            (F.map f).hom))) ∧
      Nonempty (Limits.IsColimit c) ∧
      Nonempty (c.pt ≅ ModuleCat.of S.A (ULift.{max u₁ u₃ u₄ u₅} S.N))) :
    UniversallyInjectivePoly.{u₁, u₅} S.u := by
  obtain ⟨I, _, _, _, F, c, hfree, hinj, ⟨hc⟩, ⟨eiso⟩⟩ := hcolim
  let eN : (c.pt : Type (max u₁ u₃ u₄ u₅)) ≃ₗ[S.A] S.N :=
    eiso.toLinearEquiv ≪≫ₗ ULift.moduleEquiv
  let eM : (ULift.{max u₁ u₃ u₄ u₅} S.M) ≃ₗ[S.A] S.M := ULift.moduleEquiv
  have hflat : Module.Flat S.A (ULift.{max u₁ u₃ u₄ u₅} S.M) := Module.Flat.of_linearEquiv eM
  have hu' : Function.Injective
      (Submodule.mapQ
        (IsLocalRing.maximalIdeal S.A •
          (⊤ : Submodule S.A (c.pt : Type (max u₁ u₃ u₄ u₅))))
        (IsLocalRing.maximalIdeal S.A •
          (⊤ : Submodule S.A (ULift.{max u₁ u₃ u₄ u₅} S.M)))
        (eM.symm.toLinearMap ∘ₗ S.u ∘ₗ eN.toLinearMap)
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal S.A)
          (eM.symm.toLinearMap ∘ₗ S.u ∘ₗ eN.toLinearMap))) := by
    rw [Submodule.injective_mapQ_smul_top_iff]
    intro x hx
    have h1 : S.u (eN x) ∈ IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A S.M) :=
      (mem_smul_top_equiv_iff eM.symm (IsLocalRing.maximalIdeal S.A) (S.u (eN x))).1 hx
    have h2 : eN x ∈ IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A S.N) :=
      (Submodule.injective_mapQ_smul_top_iff S.u
        (IsLocalRing.maximalIdeal S.A)).1 S.injective_mod_maximalIdeal _ h1
    exact (mem_smul_top_equiv_iff eN (IsLocalRing.maximalIdeal S.A) x).1 h2
  have key := rTensor_injective_of_colimit_free (M := ULift.{max u₁ u₃ u₄ u₅} S.M)
    hfree hinj hc (eM.symm.toLinearMap ∘ₗ S.u ∘ₗ eN.toLinearMap) hu'
  intro Q _ _
  refine (injective_rTensor_iff_of_equiv S.u
    (ULift.moduleEquiv : ULift.{max u₁ u₃ u₄ u₅} Q ≃ₗ[S.A] Q)).mp ?_
  exact injective_rTensor_of_comp_equiv S.u eN eM.symm _
    (key (ULift.{max u₁ u₃ u₄ u₅} Q))

/-- **The flat case of Stacks 0AT3.** In Situation 0AT0, if `A` is henselian and `N` is flat
over `A`, then `u` is `A`-universally injective.

This is the first paragraph of the proof of Stacks 0AT3. By the proof of Stacks 05U7, `N` is a
filtered colimit of free `A`-modules whose transition maps are injective modulo `𝔪_A`: `N` is the
localization at a prime over `𝔪_A` of a finite module over a polynomial ring over `A`
(`Module.exists_polynomial_localizedModule_linearEquiv`), and such a flat localization has that
presentation (`exists_colimit_free_of_flat_localizedModule`). The colimit is taken of a universe
lift of `N`, so that it lives in the universe `universallyInjective_of_colimit_free` asks for. -/
theorem universallyInjective_of_henselian_of_flat
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [HenselianLocalRing S.A]
    [Module.Flat S.A S.N] : UniversallyInjectivePoly.{u₁, u₅} S.u := by
  let N' : Type (max u₁ u₃ u₄ u₅) := ULift.{max u₁ u₃ u₅} S.N
  let eN' : N' ≃ₗ[S.A] S.N := ULift.moduleEquiv
  let eN'B : N' ≃ₗ[S.B] S.N := ULift.moduleEquiv
  have : Module.Finite S.B N' := Module.Finite.equiv eN'B.symm
  have : Module.Flat S.A N' := Module.Flat.of_linearEquiv eN'
  obtain ⟨n, q, _, M, _, _, _, _, _, hq, ⟨eN⟩⟩ :=
    Module.exists_polynomial_localizedModule_linearEquiv (N := N') S.essentiallyFiniteType
  have hflat : Module.Flat S.A (LocalizedModule q.primeCompl M) := Module.Flat.of_linearEquiv eN
  obtain ⟨I, _, _, _, F, c, hfree, hinj, hc, ⟨e⟩⟩ :=
    exists_colimit_free_of_flat_localizedModule q hq M hflat eN
  let eU : ULift.{u₁} N' ≃ₗ[S.A] ULift.{max u₁ u₃ u₄ u₅} S.N :=
    ULift.moduleEquiv.trans (eN'.trans ULift.moduleEquiv.symm)
  exact universallyInjective_of_colimit_free S
    ⟨I, inferInstance, inferInstance, inferInstance, F, c, hfree, hinj, hc,
      ⟨e ≪≫ eU.toModuleIso⟩⟩

end AlgebraicGeometry

end
