module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicPro
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
import StacksFrontier.AlgebraicGeometry.ReflexiveExtensionGate.Basic
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Basic
import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmbeddedPointStep
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianPushforwardExact

/-!
# The higher-rank devissage criterion over one irreducible closed subset

[Stacks, Tag 01YL] refines the criterion of [Stacks, Tag 01YG] to modules supported inside one
irreducible closed subset `Z₀` of a Noetherian scheme `X`, with generic point `ξ`. Its
hypotheses on a property `P` of coherent modules are

1. `P` is stable under extensions: in a short exact sequence of coherent modules, if the two
   outer terms have `P` then so does the middle one;
2. `P` descends from a nonempty finite direct sum: if `P` holds for a sum of `r` copies of `F`
   with `r ≥ 1`, then `P` holds for `F`;
3. `P` holds for the direct image of every quasi-coherent sheaf of ideals on every integral
   closed subscheme strictly inside `Z₀`;
4. there is one coherent `G` with support exactly `Z₀`, with `G_ξ` annihilated by the maximal
   ideal of the local ring at `ξ`, and such that for every quasi-coherent sheaf of ideals `J`
   with `J_ξ` the whole local ring there is a quasi-coherent `G' ⊆ J·G` with `G'_ξ = G_ξ` for
   which `P` holds.

The conclusion is that `P` holds for every coherent module on `X` whose support is contained in
`Z₀`. The proof is the source's: condition (1) propagates `P` along a finite filtration, which
with (3) and the filtration of [Stacks, Tag 01YF] — consumed through the criterion of
[Stacks, Tag 01YG] applied to "`P`, or the support is not inside `Z₀`" — settles every module
supported strictly inside `Z₀`; [Stacks, Tag 01YE] embeds a direct image `i_*(ℐ^{⊕r})` of an
ideal on the integral subscheme carried by `Z₀` into `G` isomorphically near `ξ`; shrinking `ℐ`
to `ℐ'`, the quotient is killed by a power of the ideal cutting out its support by
[Stacks, Tag 01Y9], so (4)(c) produces `G'` inside that power multiple of `G` and inside
`i_*((ℐ')^{⊕r})`, whence `P` for `i_*((ℐ')^{⊕r})` by (1) and for `i_*ℐ'` by (2); intersecting an
arbitrary ideal with `ℐ` transfers `P` to every `i_*ℐ''`; and [Stacks, Tag 01YG] finishes.

## Main results

* `Stacks.AlgebraicGeometry.HigherRankIrreducibleDevissage.property_irreducible_higher_rank`:
  **[Stacks, Tag 01YL]**, in the corrected form described below.
* `Stacks.AlgebraicGeometry.HigherRankIrreducibleDevissage.hasIrreducibleHigherRankCriterion`:
  the same statement in the form the library already consumes it,
  `Stacks.AlgebraicGeometry.Tag01YMHigherRank.HasIrreducibleHigherRankCriterion`, which until now
  was carried as an open hypothesis by every downstream use of this tag.

## Implementation notes

**The correction: `P` is also assumed for the zero module, and the source statement is false
without it.** The theorem below carries `hzero : P (⊤_ X.Modules)`, which the source's list of
four conditions does not contain and does not imply. The conclusion is asserted for every
coherent module whose support is contained in `Z₀`, and the zero module is one; the source's own
proof covers it by the filtration of [Stacks, Tag 01YF], which for the zero module has no steps
at all, so `P` on the zero module has to come from the hypotheses. Condition (1) only ever
concludes about the middle term of a sequence whose outer terms already have `P`, so it cannot
produce it; condition (2) applied to the zero module is circular; and condition (3) is vacuous
exactly when `Z₀` has no integral closed subscheme strictly inside it, that is when `Z₀` is a
single closed point. For such a `Z₀` — take `X` the spectrum of a field and `Z₀` its one point —
the property `fun F => ¬ IsZero F` satisfies (1), (2), (3) vacuously and (4) with `G` the
structure sheaf, and fails for the zero module, whose support is contained in `Z₀`. The same
correction is already carried by the statements of the companion tags [Stacks, Tag 01YG] and
[Stacks, Tag 01YI], for the same reason, and by the library's own restatement of this tag in
`StacksFrontier/AlgebraicGeometry/HigherRank/Basic.lean`. The `stacks` attribute records it.

**Even where `Z₀` is not a point the hypothesis cannot be dropped here.** Condition (3) applied
to the zero ideal on a proper integral closed subscheme gives `P` for a direct image that is a
zero object, but `P` is an arbitrary predicate on modules, not an isomorphism-invariant one, and
transporting it to the terminal object is exactly what needs `hzero` together with (1).

**Clause (4)(c) asks only for a quasi-coherent subsheaf, as the source does.** The statement attached to the tag and
the library's own restatement in `StacksFrontier/AlgebraicGeometry/HigherRank/Basic.lean` both demand
that the subsheaf `G'` inside `J·G` be coherent, which is a stronger demand on the user of the
criterion and so a weaker theorem. Coherence is not needed as a hypothesis: `G'` is a submodule
of the coherent `G` on a Noetherian scheme, so
`Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono` derives it from quasi-coherence.
`hasIrreducibleHigherRankCriterion` therefore has to weaken its input before applying the theorem
below, which is where that one line goes.

**The local `implicit_reducible` attributes are what keeps the proofs free of transparency
options.** `X.Modules` carries two category instances — its own and the one inherited from
`SheafOfModules X.ringCatSheaf` — and a stalk is written both as `TopCat.Presheaf.stalk` and as
a value of `TopCat.Presheaf.stalkFunctor`; the spellings are definitionally equal only after
unfolding `TopCat.Sheaf`, `Scheme.Modules`, its category instance, `Scheme.Modules.presheaf` and
`Scheme.Modules.pushforward`. Declaring those locally implicit-reducible makes the rewrites
match, as in [Stacks, Tag 01YH]'s file.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Opposite

universe u

namespace Stacks.AlgebraicGeometry.HigherRankIrreducibleDevissage

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor
attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules.Hom
attribute [local instance_reducible] TopCat.Sheaf

/-- The subsheaves of a sheaf of modules `M` on a scheme form a complete lattice. -/
noncomputable local instance {X : Scheme.{u}} {M : X.Modules} : CompleteLattice M.Submodule :=
  SheafOfModules.Submodule.instCompleteLattice

private lemma subsheaf_le_idealPowerMultiple {X : Scheme.{u}} {M : X.Modules}
    (I : X.IdealSheafData) (n : ℕ) (H : M.Submodule)
    (h : ∀ (U : X.affineOpens) (s : Γ(H.toSheafOfModules, U.1)),
      (Scheme.Modules.Hom.app H.ι U.1 s : Γ(M, U.1)) ∈
        I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))) :
    H ≤ Stacks.Algebraization.idealPowerMultiple I n M := by
  apply Stacks.Algebraization.submodule_le_of_affine
  intro U
  apply SetLike.le_def.mpr
  intro s hs
  have hgen : I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) ≤
      (Stacks.Algebraization.idealPowerMultiple I n M).toSubmodule.obj (op U.1) :=
    (Stacks.Algebraization.idealPowerMultiple_le_iff I n M
      (Stacks.Algebraization.idealPowerMultiple I n M)).mp le_rfl U
  exact SetLike.le_def.mp hgen (h U ⟨s, hs⟩)

private alias idealPowerMultiple_le_comap := Stacks.Coherent.idealPowerMultiple_le_comap

/-- Alias of `Stacks.AlgebraicGeometry.CoherentDevissage.supp_subset_of_mono`. -/
private alias supp_of_mono := Stacks.AlgebraicGeometry.CoherentDevissage.supp_subset_of_mono

/-- An epimorphism of sheaves of modules is locally surjective as a morphism of the underlying
sheaves of abelian groups. -/
lemma isLocallySurjective_toSheaf_of_epi
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map f).hom := by
  have : PreservesColimit (span f f) (SheafOfModules.toSheaf R) := by
    let L := PresheafOfModules.sheafification (R := R) (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)
    let Rt := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
    let K : WalkingSpan ⥤ PresheafOfModules R.obj := span f f ⋙ Rt
    have : PreservesColimit K (L ⋙ SheafOfModules.toSheaf R) :=
      preservesColimit_of_natIso K
        (PresheafOfModules.sheafificationCompToSheaf (R := R) (𝟙 R.obj)).symm
    let e : span f f ≅ K ⋙ L :=
      (Functor.rightUnitor (span f f)).symm ≪≫
        Functor.isoWhiskerLeft (span f f) (asIso adj.counit).symm ≪≫
        (Functor.associator (span f f) Rt L).symm
    have : PreservesColimit (K ⋙ L) (SheafOfModules.toSheaf R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit K))
        (isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf R) (colimit.isColimit K))
    exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) e.symm
  have := preserves_epi_of_preservesColimit (SheafOfModules.toSheaf R) f
  exact (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
    ((SheafOfModules.toSheaf R).map f)).mpr inferInstance

/-- An epimorphism of modules on a scheme is surjective on the stalk at every point. -/
lemma epi_stalk_surjective {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Epi f] (x : X) :
    Function.Surjective (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f))) := by
  have hloc : Presheaf.IsLocallySurjective (Opens.grothendieckTopology (TopCat.of X))
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom :=
    @isLocallySurjective_toSheaf_of_epi (Opens (TopCat.of X)) _
      (Opens.grothendieckTopology (TopCat.of X)) X.ringCatSheaf _ _ F G f ‹Epi f›
  exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp hloc x

private alias not_mem_supp_cokernel_of_stalk_surjective :=
  Stacks.AlgebraicGeometry.CoherentDevissage.notMem_supp_cokernel_of_stalk_surjective

private lemma stalk_surjective_of_comp {X : Scheme.{u}}
    {F G H : X.Modules} (f : F ⟶ G) (g : G ⟶ H) [Mono g] (x : X)
    (h : Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf (f ≫ g))).hom)) :
    Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f)).hom) := by
  let T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  have hm : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map g) := by
    have : (TopCat.Sheaf.forget Ab (TopCat.of X)).ReflectsMonomorphisms :=
      Functor.reflectsMonomorphisms_of_faithful _
    apply (TopCat.Sheaf.forget Ab (TopCat.of X)).mono_of_mono_map
    show Mono ((Scheme.Modules.toPresheaf X).map g)
    infer_instance
  have hg : Mono (T.map g) :=
    (TopCat.Presheaf.mono_iff_stalk_mono
      ((SheafOfModules.toSheaf X.ringCatSheaf).map g)).mp hm x
  have hinj := (AddCommGrpCat.mono_iff_injective (T.map g)).mp hg
  intro b
  obtain ⟨a, ha⟩ := h ((T.map g).hom b)
  refine ⟨a, hinj ?_⟩
  show (T.map f ≫ T.map g).hom a = (T.map g).hom b
  rwa [← T.map_comp]

/-- The target of an epimorphism is supported inside the support of its source. -/
theorem supp_of_epi {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    [Epi f] : SheafOfModules.supp G ⊆ SheafOfModules.supp F := by
  intro x hx
  have hG : Nontrivial (G.presheaf.stalk x) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk G x).mp hx
  by_contra hF
  have hFsub : Subsingleton (F.presheaf.stalk x) := not_nontrivial_iff_subsingleton.mp
    fun h => hF ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr h)
  have hsurj := epi_stalk_surjective f x
  have hGsub : Subsingleton (G.presheaf.stalk x) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨c, hc⟩ := hsurj (a - b)
    rw [hFsub.elim c 0] at hc
    have hdiff : (0 : G.presheaf.stalk x) = a - b := by simpa using hc
    exact sub_eq_zero.mp hdiff.symm
  exact (not_nontrivial_iff_subsingleton.mpr hGsub) hG

/-- The direct image of a module along a closed immersion is supported inside the image of that
immersion: off the image the stalk of the direct image vanishes. -/
theorem supp_pushforward_subset_range {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Z.Modules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj F) ⊆ Set.range i.base := by
  intro x hx
  by_contra hxrange
  have hzero : IsZero (TopCat.Presheaf.stalk
      ((closedInclusionPushforward (TopCat.of Z) (TopCat.of X) i.base).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj F)).1 x) :=
    closedInclusion_pushforward_stalk_isZero_of_not_mem_range
      (TopCat.of Z) (TopCat.of X) i.base i.isClosedEmbedding
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj F) x hxrange
  have hzero' : IsZero ((show TopCat.Presheaf Ab.{u} (TopCat.of X) from
      ((Scheme.Modules.pushforward i).obj F).val.presheaf).stalk x) := hzero
  obtain ⟨a, ha⟩ := hx
  exact ha ((AddCommGrpCat.subsingleton_of_isZero hzero').elim a 0)

/-- The middle term of a short exact sequence is supported inside the union of the supports of
the outer two. -/
alias supp_middle_subset := AlgebraicGeometry.supp_subset_union_of_shortExact

/-- **The support of the middle term of a short exact sequence is the union of the supports of
the outer two terms.** -/
theorem supp_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    SheafOfModules.supp S.X₂ =
      SheafOfModules.supp S.X₁ ∪ SheafOfModules.supp S.X₃ := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  exact (supp_middle_subset S hS).antisymm
    (Set.union_subset (fun _ hx => supp_of_mono S.f hx) fun _ hx => supp_of_epi S.g hx)

section


/-- **Coherent modules on a scheme form a weak Serre class**: they are stable under kernels,
cokernels, biproducts and extensions. -/
local instance isWeakSerreClass_isCoherent {X : Scheme.{u}} :
    ObjectProperty.IsWeakSerreClass (fun M : X.Modules => M.IsCoherent) := by
  have h : (fun M : X.Modules => M.IsCoherent) =
      fun M : X.Modules => Stacks.SheafOfModules.IsCoherent M :=
    funext fun M => propext (ProperMapping.isCoherent_iff M)
  rw [h]
  exact @Stacks.SheafOfModules.coherentModules_isWeakSerreClass
    (TopCat.of X) _ X.ringCatSheaf

/-- Alias of `Stacks.AlgebraicGeometry.ReflexiveExtensionGate.isCoherent_of_iso`. -/
private alias coherent_of_iso := Stacks.AlgebraicGeometry.ReflexiveExtensionGate.isCoherent_of_iso

/-- The cokernel of a morphism of coherent modules is coherent. -/
lemma coherent_cokernel {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (hF : F.IsCoherent) (hG : G.IsCoherent) :
    (cokernel f).IsCoherent :=
  (show ObjectProperty X.Modules from fun M => M.IsCoherent).prop_cokernel f hF hG

/-- The terminal module on a scheme is coherent, being a zero object. -/
lemma coherent_terminal (X : Scheme.{u}) : (⊤_ X.Modules).IsCoherent :=
  (show ObjectProperty X.Modules from fun M => M.IsCoherent).prop_of_isZero
    (IsTerminal.isZero terminalIsTerminal)

/-- Morphisms of modules on a scheme which agree on all sections are equal. -/
private lemma hom_ext_apply {X : Scheme.{u}} {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ U s, (f.val.app U).hom s = (g.val.app U).hom s) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext s
  exact h U s

private lemma submodule_bot_obj {X : Scheme.{u}} (F : X.Modules) (U : (Opens X)ᵒᵖ) :
    (⊥ : F.Submodule).toSubmodule.obj U = ⊥ := by
  apply le_antisymm _ bot_le
  have h := SheafOfModules.Submodule.le_iff.mp
    (show (⊥ : F.Submodule) ≤
      _root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule (𝟙 F) from bot_le)
  exact (h U).trans (by
    show LinearMap.ker (LinearMap.id) ≤ ⊥
    simp)

private lemma comp_eq_zero_of_le_idealPowerMultiple {X : Scheme.{u}}
    (J : X.IdealSheafData) (n : ℕ) {G Q : X.Modules} (q : G ⟶ Q)
    (hq : Stacks.Algebraization.idealPowerMultiple J n Q = ⊥)
    (H : G.Submodule) (hH : H ≤ Stacks.Algebraization.idealPowerMultiple J n G) :
    H.ι ≫ q = 0 := by
  have h := SheafOfModules.Submodule.le_iff.mp
    (hH.trans (idealPowerMultiple_le_comap J n q ⊥ hq.le))
  refine hom_ext_apply fun U s => ?_
  have hs := h U s.property
  change (q.val.app U).hom s.val ∈ (⊥ : Q.Submodule).toSubmodule.obj U at hs
  rwa [submodule_bot_obj] at hs

private lemma exists_submodule_iso_of_mono {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] :
    ∃ H : G.Submodule, Nonempty (F ≅ H.toSheafOfModules) := by
  let q := cokernel.π f
  let H := _root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.kernelSubmodule q
  have hw : H.ι ≫ q = 0 := hom_ext_apply fun U s => s.property
  have hH : IsLimit (KernelFork.ofι H.ι hw) := by
    apply KernelFork.IsLimit.ofι'
    intro A g hg
    let l : A ⟶ H.toSheafOfModules :=
      ⟨{ app := fun U => ModuleCat.ofHom
           ((g.val.app U).hom.codRestrict (H.toSubmodule.obj U) (fun s => by
             show (q.val.app U).hom ((g.val.app U).hom s) = 0
             exact congrArg (fun k : A ⟶ cokernel f => (k.val.app U).hom s) hg))
         naturality := by
           intro U V k
           apply ModuleCat.Hom.ext
           ext s
           apply Subtype.ext
           exact PresheafOfModules.naturality_apply g.val k s }⟩
    exact ⟨l, hom_ext_apply fun _ _ => rfl⟩
  exact ⟨H, ⟨IsLimit.conePointUniqueUpToIso
    (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel f)) hH⟩⟩

private lemma isIso_unitToPushforward_of_isIso {Z X : Scheme.{u}} (e : Z ⟶ X)
    [IsIso e] : IsIso (SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  show IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat Ab).map (e.app U))
  infer_instance

/-- A quasi-coherent ideal of the structure sheaf of a scheme of finite type over a locally
Noetherian scheme is coherent. -/
private lemma isCoherent_ideal_of_quasicoherent {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [LocallyOfFiniteType i] (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [H.toSheafOfModules.IsQuasicoherent] : H.toSheafOfModules.IsCoherent := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    CoherenceCriteria.structureSheaf_isCoherent Z
  have : Mono H.ι := SheafOfModules.Submodule.instMonoι H
  exact CoherentSubquotients.isCoherent_of_mono H.ι

private theorem coherent_pushforward_ideal {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [H.toSheafOfModules.IsQuasicoherent] :
    ((Scheme.Modules.pushforward i).obj H.toSheafOfModules).IsCoherent :=
  have := isCoherent_ideal_of_quasicoherent i H
  PushforwardCoherent.pushforward_isCoherent_of_isFinite i H.toSheafOfModules

private lemma exists_ideal_pushforward_iso_of_isIso {Z X : Scheme.{u}}
    [IsLocallyNoetherian X] (e : Z ⟶ X) [IsIso e]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [H.toSheafOfModules.IsQuasicoherent] :
    ∃ K : (SheafOfModules.unit X.ringCatSheaf).Submodule,
      K.toSheafOfModules.IsQuasicoherent ∧
        Nonempty ((Scheme.Modules.pushforward e).obj H.toSheafOfModules ≅
          K.toSheafOfModules) := by
  have hmono : Mono H.ι := SheafOfModules.Submodule.instMonoι H
  have hc := coherent_pushforward_ideal e H
  -- `X.Modules` carries two category instances, so the `IsIso` witness is supplied explicitly
  -- and the inverse is taken as the `Iso` it comes from rather than by instance search.
  let α : (Scheme.Modules.pushforward e).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    (@asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom)
      (isIso_unitToPushforward_of_isIso e)).symm
  have hαmono : Mono α.hom := mono_of_mono_fac α.hom_inv_id
  let f : (Scheme.Modules.pushforward e).obj H.toSheafOfModules ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    (Scheme.Modules.pushforward e).map H.ι ≫ α.hom
  have : Mono f := @mono_comp _ _ _ _ _ ((Scheme.Modules.pushforward e).map H.ι)
    inferInstance α.hom hαmono
  obtain ⟨K, ⟨α⟩⟩ := exists_submodule_iso_of_mono f
  have hKc := coherent_of_iso α hc
  exact ⟨K, isQuasicoherent_of_isCoherent K.toSheafOfModules, ⟨α⟩⟩

private noncomputable def submoduleInclusion {X : Scheme.{u}} {M : X.Modules}
    {H K : M.Submodule} (h : H ≤ K) : H.toSheafOfModules ⟶ K.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (SheafOfModules.Submodule.le_iff.mp h)⟩

private lemma submoduleInclusion_comp {X : Scheme.{u}} {M : X.Modules}
    {H K : M.Submodule} (h : H ≤ K) : submoduleInclusion h ≫ K.ι = H.ι := rfl

private lemma submoduleInclusion_mono {X : Scheme.{u}} {M : X.Modules}
    {H K : M.Submodule} (h : H ≤ K) : Mono (submoduleInclusion h) :=
  mono_of_mono_fac (submoduleInclusion_comp h)

private noncomputable def submoduleLift {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (H : N.Submodule)
    (h : ∀ U s, (f.val.app U).hom s ∈ H.toSubmodule.obj U) :
    M ⟶ H.toSheafOfModules :=
  ⟨{ app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict _ (h U))
     naturality := by
       intro U V k
       apply ModuleCat.Hom.ext
       ext s
       apply Subtype.ext
       exact PresheafOfModules.naturality_apply f.val k s }⟩

private lemma submoduleLift_comp {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (H : N.Submodule)
    (h : ∀ U s, (f.val.app U).hom s ∈ H.toSubmodule.obj U) :
    submoduleLift f H h ≫ H.ι = f :=
  hom_ext_apply fun _ _ => rfl

/-- **The intersection of two coherent submodules of a coherent module is coherent.** The
intersection is the pullback of the two inclusions, hence the kernel of a map out of their
biproduct, and coherent modules are closed under kernels and biproducts. -/
@[ega "0 5.3.4" "intersection clause"]
private lemma coherent_submodule_inf {X : Scheme.{u}} {M : X.Modules}
    (H K : M.Submodule) (hH : H.toSheafOfModules.IsCoherent)
    (hK : K.toSheafOfModules.IsCoherent) (hM : M.IsCoherent) :
    (H ⊓ K).toSheafOfModules.IsCoherent := by
  have : Mono H.ι := SheafOfModules.Submodule.instMonoι H
  have : Mono K.ι := SheafOfModules.Submodule.instMonoι K
  have : Mono (H ⊓ K).ι := SheafOfModules.Submodule.instMonoι (H ⊓ K)
  let a := submoduleInclusion (show H ⊓ K ≤ H from inf_le_left)
  let b := submoduleInclusion (show H ⊓ K ≤ K from inf_le_right)
  have hab : a ≫ H.ι = b ≫ K.ι := rfl
  have hcompA : a ≫ H.ι = (H ⊓ K).ι := submoduleInclusion_comp _
  have hcompB : b ≫ K.ι = (H ⊓ K).ι := submoduleInclusion_comp _
  let l := pullback.lift a b hab
  have hm : ∀ U s, ((pullback.fst H.ι K.ι ≫ H.ι).val.app U).hom s ∈
      (H ⊓ K).toSubmodule.obj U := by
    intro U s
    constructor
    · exact ((pullback.fst H.ι K.ι).val.app U s).property
    · have e := congrArg (fun f : pullback H.ι K.ι ⟶ M => (f.val.app U).hom s)
        (pullback.condition (f := H.ι) (g := K.ι))
      rw [e]
      exact ((pullback.snd H.ι K.ι).val.app U s).property
  let r := submoduleLift (pullback.fst H.ι K.ι ≫ H.ι) (H ⊓ K) hm
  have hr : r ≫ (H ⊓ K).ι = pullback.fst H.ι K.ι ≫ H.ι :=
    submoduleLift_comp _ _ _
  have hl₁ : l ≫ pullback.fst H.ι K.ι = a := pullback.lift_fst a b hab
  have hl₂ : l ≫ pullback.snd H.ι K.ι = b := pullback.lift_snd a b hab
  have hr₁ : r ≫ a = pullback.fst H.ι K.ι :=
    (cancel_mono H.ι).mp (by rw [Category.assoc, hcompA, hr])
  have hr₂ : r ≫ b = pullback.snd H.ι K.ι :=
    (cancel_mono K.ι).mp (by rw [Category.assoc, hcompB, hr, pullback.condition])
  have hlr : l ≫ r = 𝟙 (H ⊓ K).toSheafOfModules := (cancel_mono (H ⊓ K).ι).mp (by
    rw [Category.assoc, hr, ← Category.assoc, hl₁, hcompA, Category.id_comp])
  have hrl : r ≫ l = 𝟙 _ := pullback.hom_ext (f := H.ι) (g := K.ι)
    (by rw [Category.assoc, hl₁, hr₁, Category.id_comp])
    (by rw [Category.assoc, hl₂, hr₂, Category.id_comp])
  let e : (H ⊓ K).toSheafOfModules ≅ pullback H.ι K.ι :=
    { hom := l
      inv := r
      hom_inv_id := hlr
      inv_hom_id := hrl }
  let : HasBinaryBiproducts X.Modules := HasBinaryBiproducts.of_hasBinaryProducts
  let C : ObjectProperty X.Modules := fun M => M.IsCoherent
  have hpb : (pullback H.ι K.ι : X.Modules).IsCoherent :=
    C.prop_of_isLimit_kernelFork
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct H.ι K.ι)
      (C.prop_biprod hH hK) hM
  exact coherent_of_iso e.symm hpb

private lemma ideal_eq_zero_or_iso_near_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (H : (SheafOfModules.unit X.ringCatSheaf).Submodule) :
    IsZero H.toSheafOfModules ∨ ∃ U : X.Opens, genericPoint X ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map H.ι) := by
  classical
  by_cases hz : IsZero H.toSheafOfModules
  · exact Or.inl hz
  right
  have hs : ∃ (U : X.Opens) (s : Γ(H.toSheafOfModules, U)),
      (s.val : Γ(X, U)) ≠ 0 := by
    by_contra! h
    apply hz
    apply (IsZero.iff_id_eq_zero _).mpr
    refine hom_ext_apply fun U s => ?_
    apply Subtype.ext
    exact h U.unop s
  obtain ⟨U, s, hs⟩ := hs
  let t : Γ(X, U) := s.val
  let V := X.basicOpen t
  have hV : (V : Set X).Nonempty :=
    V.ne_bot_iff_nonempty.mp (fun h => hs ((basicOpen_eq_bot_iff t).mp h))
  have hξ : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  refine ⟨V, hξ, Scheme.Modules.Hom.isIso_iff_isIso_app.mpr ?_⟩
  intro W
  let W' : X.Opens := V.ι ''ᵁ W
  have hWV : W' ≤ V := by
    simpa [W'] using V.ι.image_le_opensRange W
  let k : W' ⟶ U := homOfLE (hWV.trans (X.basicOpen_le t))
  have htH : (X.presheaf.map k.op) t ∈ H.toSubmodule.obj (op W') :=
    H.toSubmodule.map k.op s.property
  have htUnit : IsUnit ((X.presheaf.map k.op) t) := by
    have := (X.toRingedSpace.isUnit_res_basicOpen t).map
      (X.presheaf.map (homOfLE hWV).op).hom
    change IsUnit ((X.presheaf.map (homOfLE hWV).op)
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op) t)) at this
    rwa [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  have htop : H.toSubmodule.obj (op W') = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨v, hv⟩ := htUnit
    let a' : Γ(X, W') := a
    have h := (H.toSubmodule.obj (op W')).smul_mem
      (a' * (↑(v⁻¹) : Γ(X, W'))) htH
    change (a' * (↑(v⁻¹) : Γ(X, W'))) * ((X.presheaf.map k.op) t) ∈ _ at h
    rw [← hv] at h
    have h' : a' ∈ H.toSubmodule.obj (op W') := by simpa [mul_assoc] using h
    exact h'
  have : Mono (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor V.ι).map H.ι) W) :=
    (AddCommGrpCat.mono_iff_injective _).mpr Subtype.val_injective
  have : Epi (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor V.ι).map H.ι) W) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr fun a => ⟨⟨a, htop.ge trivial⟩, rfl⟩
  exact isIso_of_mono_of_epi _

/-- A morphism of modules which restricts to an isomorphism over an open `U` is an isomorphism
on the stalk at every point of `U`. -/
lemma stalk_isIso_of_restrict_isIso {X : Scheme.{u}}
    {F G : X.Modules} (f : F ⟶ G) (U : X.Opens) (x : X) (hx : x ∈ U)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f)) :=
  (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hx⟩ : U)) f).mp
    (by dsimp only [Functor.comp_map]; infer_instance)

/-- The structure sheaf of an integral scheme is supported everywhere: the germ of `1` at any
point is nonzero. -/
lemma unit_mem_supp {Z : Scheme.{u}} [IsIntegral Z] (x : Z) :
    x ∈ SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf) := by
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  refine ⟨O.presheaf.germ ⊤ x (by trivial) (1 : Γ(Z, ⊤)), ?_⟩
  intro h
  have h' : O.presheaf.germ ⊤ x (by trivial) (1 : Γ(Z, ⊤)) =
      O.presheaf.germ ⊤ x (by trivial) (0 : Γ(Z, ⊤)) :=
    h.trans (map_zero _).symm
  obtain ⟨W, hxW, k, l, hW⟩ := O.presheaf.germ_eq x (by trivial) (by trivial)
    (1 : Γ(Z, ⊤)) (0 : Γ(Z, ⊤)) h'
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  change (Z.presheaf.map k.op) 1 = (Z.presheaf.map l.op) 0 at hW
  simp at hW

/-- A zero module has empty support. -/
lemma supp_eq_empty_of_isZero {X : Scheme.{u}} {F : X.Modules}
    (hF : IsZero F) : SheafOfModules.supp F = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  let T := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  have hz : IsZero (T.obj F) := T.map_isZero hF
  obtain ⟨s, hs⟩ := hx
  exact hs ((AddCommGrpCat.subsingleton_of_isZero hz).elim s 0)

/-- If a morphism is surjective on the stalk at `x` and the target is supported at `x`, then so
is the source. -/
lemma mem_supp_of_stalk_surjective {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (x : X)
    (hf : Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f)).hom))
    (hx : x ∈ SheafOfModules.supp G) : x ∈ SheafOfModules.supp F := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, ht⟩ := hf s
  refine ⟨t, fun h => hs ?_⟩
  rw [← ht, h]
  exact map_zero _

private lemma supp_ideal_eq_univ_of_not_isZero {X : Scheme.{u}} [IsIntegral X]
    (H : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (hH : H.toSheafOfModules.IsCoherent) (hne : ¬ IsZero H.toSheafOfModules) :
    SheafOfModules.supp H.toSheafOfModules = Set.univ := by
  have hft := hH.isFiniteType
  obtain ⟨U, hU, hi⟩ := (ideal_eq_zero_or_iso_near_genericPoint H).resolve_left hne
  have hst := stalk_isIso_of_restrict_isIso H.ι U (genericPoint X) hU
  have hg : genericPoint X ∈ SheafOfModules.supp H.toSheafOfModules :=
    mem_supp_of_stalk_surjective H.ι _
      ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance) (unit_mem_supp _)
  exact Set.eq_univ_of_univ_subset
    (((genericPoint_spec X).mem_closed_set_iff
      (SheafOfModules.isClosed_supp H.toSheafOfModules)).mp hg)

/-- A direct image along a closed immersion is supported at `i x` exactly when the module is
supported at `x`, the comparison map of stalks being an isomorphism. -/
lemma mem_supp_pushforward_iff {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Z.Modules) (x : Z) :
    i x ∈ SheafOfModules.supp ((Scheme.Modules.pushforward i).obj F) ↔
      x ∈ SheafOfModules.supp F := by
  let a := TopCat.Presheaf.stalkPushforward Ab.{u} i.base F.presheaf x
  have : IsIso a :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      (C := Ab.{u}) i.isClosedEmbedding.isInducing F.presheaf x
  have ha := (AddCommGrpCat.mono_iff_injective a).mp (IsIso.mono_of_iso a)
  have ha' := (AddCommGrpCat.epi_iff_surjective a).mp (IsIso.epi_of_iso a)
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨a.hom s, fun h => hs (ha (h.trans (map_zero _).symm))⟩
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := ha' s
    refine ⟨t, fun h => hs ?_⟩
    rw [← ht, h]
    exact map_zero _

private lemma supp_pushforward_ideal {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hH : H.toSheafOfModules.IsCoherent) (hne : ¬ IsZero H.toSheafOfModules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) =
      Set.range i := by
  apply (supp_pushforward_subset_range i H.toSheafOfModules).antisymm
  rintro _ ⟨x, rfl⟩
  apply (mem_supp_pushforward_iff i H.toSheafOfModules x).mpr
  rw [supp_ideal_eq_univ_of_not_isZero H hH hne]
  trivial

/-- Extension stability, applied to a monomorphism of coherent modules and its cokernel. -/
private lemma property_of_cokernel_sequence {X : Scheme.{u}} (P : X.Modules → Prop)
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    {A B : X.Modules} (a : A ⟶ B) [Mono a] (hA : A.IsCoherent) (hB : B.IsCoherent)
    (hPA : P A) (hPC : P (cokernel a)) : P B :=
  hext (ShortComplex.mk a (cokernel.π a) (cokernel.condition a))
    (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact a) inferInstance
      inferInstance) hA hB (coherent_cokernel a hA hB) hPA hPC

private theorem property_of_generic_mono {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop) (T : Set X) (ξ : X)
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hsmall : ∀ Q : X.Modules, Q.IsCoherent →
      SheafOfModules.supp Q ⊆ T → ξ ∉ SheafOfModules.supp Q → P Q)
    {G : X.Modules} (hGc : G.IsCoherent) (hGs : SheafOfModules.supp G ⊆ T)
    (hGJ : ∀ (J : X.IdealSheafData), ξ ∉ J.support →
        ∃ (G' : G.Submodule),
          G'.toSheafOfModules.IsQuasicoherent ∧
          (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
            (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
              J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
          Function.Surjective
            (((TopCat.Presheaf.stalkFunctor Ab ξ).map
              (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
          P G'.toSheafOfModules)
    {M : X.Modules} (hMc : M.IsCoherent) (f : M ⟶ G) [Mono f]
    (hf : ξ ∉ SheafOfModules.supp (cokernel f)) : P M := by
  let Q := cokernel f
  have hQc : Q.IsCoherent := coherent_cokernel f hMc hGc
  have hQft : Q.IsFiniteType := hQc.isFiniteType
  let J := Scheme.IdealSheafData.vanishingIdeal
    ⟨SheafOfModules.supp Q, SheafOfModules.isClosed_supp Q⟩
  have hJs : (J.support : Set X) = SheafOfModules.supp Q :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨n, hn⟩ :=
    (Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset Q J).2
    hJs.symm.subset
  have hJn : ξ ∉ (J ^ n).support := by
    cases n with
    | zero => exact fun h => h
    | succ n =>
      show ξ ∉ (J.support : Set X)
      rw [hJs]
      exact hf
  obtain ⟨H, hHq, hHJ, hHξ, hHP⟩ := hGJ (J ^ n) hJn
  -- Coherence of `H` is derivable from quasi-coherence, `H` being a submodule of a coherent
  -- module on a locally Noetherian scheme; the source asks only for quasi-coherence.
  have hHc : H.toSheafOfModules.IsCoherent := by
    have : G.IsCoherent := hGc
    have : H.toSheafOfModules.IsQuasicoherent := hHq
    have : Mono H.ι := SheafOfModules.Submodule.instMonoι H
    exact CoherentSubquotients.isCoherent_of_mono H.ι
  have hHle : H ≤ Stacks.Algebraization.idealPowerMultiple J n G :=
    subsheaf_le_idealPowerMultiple J n H hHJ
  have hw : H.ι ≫ cokernel.π f = 0 :=
    comp_eq_zero_of_le_idealPowerMultiple J n (cokernel.π f) hn H hHle
  let a : H.toSheafOfModules ⟶ M := Abelian.monoLift f H.ι hw
  have haf : a ≫ f = H.ι := Abelian.monoLift_comp f H.ι hw
  have ha : Mono a := mono_of_mono_fac haf
  have haξ : Function.Surjective (((TopCat.Presheaf.stalkFunctor Ab ξ).map
      (Scheme.Modules.Hom.mapPresheaf a)).hom) :=
    stalk_surjective_of_comp a f ξ (by rwa [haf])
  exact property_of_cokernel_sequence P hext a hHc hMc hHP (hsmall (cokernel a)
    (coherent_cokernel a hHc hMc)
    ((supp_of_epi (cokernel.π a)).trans ((supp_of_mono f).trans hGs))
    (not_mem_supp_cokernel_of_stalk_surjective a ξ haξ))

private lemma coherent_product {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsCoherent) (n : ℕ) : (∏ᶜ fun _ : Fin n => F).IsCoherent :=
  (show ObjectProperty X.Modules from fun M => M.IsCoherent).prop_product (fun _ => hF)

private lemma coherent_coproduct {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsCoherent) (n : ℕ) : (∐ fun _ : Fin n => F).IsCoherent := by
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  exact coherent_of_iso ((biproduct.isoProduct (fun _ : Fin n => F)).symm ≪≫
    biproduct.isoCoproduct _) (coherent_product F hF n)

private lemma isZero_coproduct {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} (F : ι → C) [HasCoproduct F] (hF : ∀ j, IsZero (F j)) :
    IsZero (∐ F) :=
  (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun j => (hF j).eq_of_src _ _)

/-- If a submodule restricts to the whole module over `U`, then every section of the module over
an open of `U` lies in it. -/
private lemma mem_of_isIso_restrict {X : Scheme.{u}} {M : X.Modules} (K : M.Submodule)
    (U : X.Opens) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map K.ι)] (W : (U : Scheme).Opens)
    (s : Γ(M, U.ι ''ᵁ W)) : s ∈ K.toSubmodule.obj (op (U.ι ''ᵁ W)) := by
  let a := Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor U.ι).map K.ι) W
  have ha : IsIso a := by dsimp [a]; infer_instance
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective a).mp inferInstance s
  change t.val = s at ht
  exact ht ▸ t.property

/-- The inclusion of a smaller submodule restricts to an isomorphism over `U` as soon as every
section of the larger one over an open of `U` lies in the smaller one. -/
private lemma restrict_submoduleInclusion_isIso {X : Scheme.{u}} {M : X.Modules}
    {A B : M.Submodule} (h : A ≤ B) (U : X.Opens)
    (hmem : ∀ (W : (U : Scheme).Opens) (s : Γ(B.toSheafOfModules, U.ι ''ᵁ W)),
      s.val ∈ A.toSubmodule.obj (op (U.ι ''ᵁ W))) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (submoduleInclusion h)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  let b := Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor U.ι).map
    (submoduleInclusion h)) W
  have : Mono b := (AddCommGrpCat.mono_iff_injective _).mpr fun s t h =>
    Subtype.ext (congrArg (fun y : Γ(B.toSheafOfModules, U.ι ''ᵁ W) => y.val) h)
  have : Epi b := (AddCommGrpCat.epi_iff_surjective _).mpr fun s => ⟨⟨s.val, hmem W s⟩, rfl⟩
  exact isIso_of_mono_of_epi b

/-- Direct image along a closed immersion carries a morphism which is an isomorphism on the
stalk at `x` to one which is an isomorphism on the stalk at `i x`. -/
private lemma stalk_pushforward_map_isIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {F G : Z.Modules} (f : F ⟶ G) (x : Z)
    [IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map
      (Scheme.Modules.Hom.mapPresheaf f))] :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (i x)).map
      (Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pushforward i).map f))) := by
  let a := TopCat.Presheaf.stalkPushforward Ab.{u} i.base F.presheaf x
  let b := TopCat.Presheaf.stalkPushforward Ab.{u} i.base G.presheaf x
  have ha : IsIso a := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    (C := Ab.{u}) i.isClosedEmbedding.isInducing F.presheaf x
  have hb : IsIso b := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    (C := Ab.{u}) i.isClosedEmbedding.isInducing G.presheaf x
  let c := (TopCat.Presheaf.stalkFunctor Ab.{u} (i x)).map
    (Scheme.Modules.Hom.mapPresheaf ((Scheme.Modules.pushforward i).map f))
  let d := (TopCat.Presheaf.stalkFunctor Ab.{u} x).map (Scheme.Modules.Hom.mapPresheaf f)
  have hd : IsIso d := inferInstance
  have h : c ≫ b = a ≫ d :=
    (TopCat.Presheaf.stalkPushforward_naturality i.base
      (Scheme.Modules.Hom.mapPresheaf f) x).symm
  have hi : IsIso (c ≫ b) := h ▸ (@IsIso.comp_isIso _ _ _ _ _ a d ha hd)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ c b hb hi

private lemma map_sigma_isIso {C D : Type*} [Category C] [Category D]
    {ι : Type*} (T : C ⥤ D) {F G : ι → C}
    [HasCoproduct F] [HasCoproduct G]
    [PreservesColimit (Discrete.functor F) T] [PreservesColimit (Discrete.functor G) T]
    (f : ∀ j, F j ⟶ G j) [∀ j, IsIso (T.map (f j))] :
    IsIso (T.map (Limits.Sigma.map f)) := by
  let e : Discrete.functor F ⋙ T ≅ Discrete.functor G ⋙ T :=
    Discrete.natIso (fun j => asIso (T.map (f j.as)))
  have h : T.map (Limits.Sigma.map f) =
      (preservesColimitIso T (Discrete.functor F)).hom ≫
        (HasColimit.isoOfNatIso e).hom ≫
          (preservesColimitIso T (Discrete.functor G)).inv := by
    apply (cancel_epi (preservesColimitIso T (Discrete.functor F)).inv).mp
    apply colimit.hom_ext
    intro j
    simp only [Iso.inv_hom_id_assoc,
      ι_preservesColimitIso_inv_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
      ι_preservesColimitIso_inv]
    show T.map (Sigma.ι F j.as) ≫ T.map (Limits.Sigma.map f) =
      T.map (f j.as) ≫ T.map (Sigma.ι G j.as)
    rw [← T.map_comp, ← T.map_comp, Sigma.ι_map]
  rw [h]
  infer_instance

end

private theorem property_of_iso {X : Scheme.{u}} (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    {F G : X.Modules} (e : F ≅ G) (hF : F.IsCoherent) (hG : G.IsCoherent)
    (hP : P F) : P G := by
  let S : ShortComplex X.Modules :=
    ShortComplex.mk e.hom (0 : G ⟶ ⊤_ X.Modules) (by simp)
  have hExact : S.Exact := (S.exact_iff_epi rfl).2
    (by dsimp [S]; infer_instance)
  let : Epi (0 : G ⟶ ⊤_ X.Modules) :=
    ⟨fun f g _ => (IsTerminal.isZero terminalIsTerminal).eq_of_src f g⟩
  have hShort : S.ShortExact := ShortComplex.ShortExact.mk' hExact
    (by dsimp [S]; infer_instance) (by dsimp [S]; infer_instance)
  exact hext S hShort hF hG (coherent_terminal X) hP hzero

/-- The direct image of a zero ideal under a closed immersion satisfies a property `P` which holds
for the zero module and is stable under isomorphisms of coherent modules. -/
private theorem property_pushforward_ideal_of_isZero {X Z : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop) (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (i : Z ⟶ X) [IsClosedImmersion i] (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [H.toSheafOfModules.IsQuasicoherent] (hHz : IsZero H.toSheafOfModules) :
    P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) :=
  property_of_iso P hzero hext ((IsTerminal.isZero terminalIsTerminal).iso
    ((Scheme.Modules.pushforward i).map_isZero hHz)) (coherent_terminal X)
    (coherent_pushforward_ideal i H) hzero

private alias vanishingIdeal_subscheme_isIntegral :=
  Stacks.AlgebraicGeometry.IrreducibleDevissage.isIntegral_subscheme_vanishingIdeal_of_isIrreducible

private theorem property_of_closed_immersion {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop) (T : Set X)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      (I.support : Set X) ⊆ T → (I.support : Set X) ≠ T →
      ∀ (H : (SheafOfModules.unit I.subscheme.ringCatSheaf).Submodule)
        [H.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward I.subschemeι).obj H.toSheafOfModules))
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (hi : Set.range i ⊆ T) (hi' : Set.range i ≠ T)
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [H.toSheafOfModules.IsQuasicoherent] :
    P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) := by
  have : IsLocallyNoetherian i.image := LocallyOfFiniteType.isLocallyNoetherian i.imageι
  have : IsIntegral i.image := IsIntegral.of_isIso i.toImage
  obtain ⟨K, hKq, ⟨e⟩⟩ := exists_ideal_pushforward_iso_of_isIso i.toImage H
  have hs : (i.ker.support : Set X) = Set.range i := by
    rw [i.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
  have hp := hideal i.ker (by rwa [hs]) (by rwa [hs]) K
  let α := (Scheme.Modules.pushforward i.imageι).mapIso e.symm ≪≫
    (Scheme.Modules.pushforwardComp i.toImage i.imageι).app H.toSheafOfModules ≪≫
      (Scheme.Modules.pushforwardCongr i.toImage_imageι).app H.toSheafOfModules
  exact property_of_iso P hzero hext α (coherent_pushforward_ideal i.imageι K)
    (coherent_pushforward_ideal i H) hp

private theorem property_of_finite_coprod {X : Scheme.{u}} (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hsum : ∀ (F : X.Modules), F.IsCoherent →
      (∃ n : ℕ, P (∏ᶜ (fun _ : Fin (n + 1) => F))) → P F)
    (F : X.Modules) (m : ℕ) (hF : F.IsCoherent)
    (hP : P (∐ fun _ : Fin (m + 1) => F)) : P F := by
  let : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let f : Fin (m + 1) → X.Modules := fun _ => F
  let e : (∐ f) ≅ ∏ᶜ f := (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f
  exact hsum F hF ⟨m, property_of_iso P hzero hext e (coherent_coproduct F hF (m + 1))
    (coherent_product F hF (m + 1)) hP⟩

private theorem property_of_ideal_of_generic_coproduct
    {X Z : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (P : X.Modules → Prop) (T : Set X) (hi : Set.range i ⊆ T)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hsum : ∀ (F : X.Modules), F.IsCoherent →
      (∃ n : ℕ, P (∏ᶜ (fun _ : Fin (n + 1) => F))) → P F)
    (hsmall : ∀ Q : X.Modules, Q.IsCoherent →
      SheafOfModules.supp Q ⊆ T → i (genericPoint Z) ∉ SheafOfModules.supp Q → P Q)
    {G : X.Modules} (hGξ : i (genericPoint Z) ∈ SheafOfModules.supp G)
    (hmono : ∀ (M : X.Modules), M.IsCoherent → ∀ (f : M ⟶ G) [Mono f],
      i (genericPoint Z) ∉ SheafOfModules.supp (cokernel f) → P M)
    (r : ℕ) (A : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hAc : A.toSheafOfModules.IsCoherent)
    (ψ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => A.toSheafOfModules) ⟶ G)
    [Mono ψ]
    [IsIso ((TopCat.Presheaf.stalkFunctor Ab (i (genericPoint Z))).map
      (Scheme.Modules.Hom.mapPresheaf ψ))]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [H.toSheafOfModules.IsQuasicoherent] :
    P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) := by
  classical
  let ξ := i (genericPoint Z)
  let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ξ
  let L := Scheme.Modules.pushforward i
  have hMξ : ξ ∈ SheafOfModules.supp (L.obj (∐ fun _ : Fin r => A.toSheafOfModules)) :=
    mem_supp_of_stalk_surjective ψ ξ
      ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance) hGξ
  have hne : ¬ ∀ _ : Fin r, IsZero A.toSheafOfModules := fun h => by
    rw [supp_eq_empty_of_isZero (L.map_isZero (isZero_coproduct _ h))] at hMξ
    exact hMξ
  have hAne : ¬ IsZero A.toSheafOfModules := fun hz => hne fun _ => hz
  have hr : r ≠ 0 := by
    rintro rfl
    exact hne Fin.elim0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have hOc := CoherenceCriteria.structureSheaf_isCoherent Z
  have hHmono : Mono H.ι := SheafOfModules.Submodule.instMonoι H
  have hHc : H.toSheafOfModules.IsCoherent :=
    CoherentSubquotients.isCoherent_of_mono H.ι
  have hLHc := coherent_pushforward_ideal i H
  by_cases hHz : IsZero H.toSheafOfModules
  · exact property_pushforward_ideal_of_isZero P hzero hext i H hHz
  obtain ⟨UA, hUA, hAiso⟩ := (ideal_eq_zero_or_iso_near_genericPoint A).resolve_left hAne
  obtain ⟨UH, hUH, hHiso⟩ := (ideal_eq_zero_or_iso_near_genericPoint H).resolve_left hHz
  let B := A ⊓ H
  have hBc : B.toSheafOfModules.IsCoherent := coherent_submodule_inf A H hAc hHc hOc
  have hBq : B.toSheafOfModules.IsQuasicoherent :=
    isQuasicoherent_of_isCoherent B.toSheafOfModules
  let a : B.toSheafOfModules ⟶ A.toSheafOfModules := submoduleInclusion inf_le_left
  let b : B.toSheafOfModules ⟶ H.toSheafOfModules := submoduleInclusion inf_le_right
  have ha : Mono a := submoduleInclusion_mono _
  have hb : Mono b := submoduleInclusion_mono _
  have haU : IsIso ((Scheme.Modules.restrictFunctor UH.ι).map a) :=
    restrict_submoduleInclusion_isIso _ UH fun W s => ⟨s.property,
      mem_of_isIso_restrict H UH W s.val⟩
  have hbU : IsIso ((Scheme.Modules.restrictFunctor UA.ι).map b) :=
    restrict_submoduleInclusion_isIso _ UA fun W s => ⟨mem_of_isIso_restrict A UA W s.val,
      s.property⟩
  have hast := stalk_isIso_of_restrict_isIso a UH (genericPoint Z) hUH
  have hbst := stalk_isIso_of_restrict_isIso b UA (genericPoint Z) hUA
  have haL := stalk_pushforward_map_isIso i a (genericPoint Z)
  have hbL := stalk_pushforward_map_isIso i b (genericPoint Z)
  let : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let : HasFiniteBiproducts (SheafOfModules.{u} Z.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : (Scheme.Modules.toPresheaf X).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : PreservesBinaryBiproducts (TopCat.Presheaf.stalkFunctor Ab.{u} ξ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (TopCat.Presheaf.stalkFunctor Ab.{u} ξ).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have hSψ : IsIso (S.map ψ) := by
    show IsIso ((TopCat.Presheaf.stalkFunctor Ab (i (genericPoint Z))).map
      (Scheme.Modules.Hom.mapPresheaf ψ))
    infer_instance
  have hSL : IsIso ((L ⋙ S).map a) := haL
  let α := Limits.Sigma.map (fun _ : Fin (n + 1) => a)
  have hα : Mono α := by dsimp [α]; infer_instance
  have hαst : IsIso (S.map (L.map α)) :=
    map_sigma_isIso (L ⋙ S) (fun _ : Fin (n + 1) => a)
  let f := L.map α ≫ ψ
  have hf : Mono f := by dsimp [f]; infer_instance
  have hfst : IsIso (S.map f) := by
    dsimp [f]
    rw [S.map_comp]
    infer_instance
  have hBcSum := coherent_coproduct B.toSheafOfModules hBc (n + 1)
  have hBqSum : (∐ fun _ : Fin (n + 1) => B.toSheafOfModules).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have hLBcSum : (L.obj (∐ fun _ : Fin (n + 1) => B.toSheafOfModules)).IsCoherent :=
    PushforwardCoherent.pushforward_isCoherent_of_isFinite i _
  have hPBsum := hmono _ hLBcSum f
    (not_mem_supp_cokernel_of_stalk_surjective f ξ
      ((AddCommGrpCat.epi_iff_surjective (S.map f)).mp inferInstance))
  have hLBc := coherent_pushforward_ideal i B
  let e := PreservesCoproduct.iso L (fun _ : Fin (n + 1) => B.toSheafOfModules)
  have hCop := coherent_coproduct (L.obj B.toSheafOfModules) hLBc (n + 1)
  have hPBcop := property_of_iso P hzero hext e hLBcSum hCop hPBsum
  have hPB := property_of_finite_coprod P hzero hext hsum (L.obj B.toSheafOfModules) n hLBc
    hPBcop
  exact property_of_cokernel_sequence P hext (L.map b) hLBc hLHc hPB (hsmall (cokernel (L.map b))
    (coherent_cokernel (L.map b) hLBc hLHc)
    ((supp_of_epi (cokernel.π (L.map b))).trans
      ((supp_pushforward_subset_range i H.toSheafOfModules).trans hi))
    (not_mem_supp_cokernel_of_stalk_surjective (L.map b) ξ
      ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)))

private theorem property_of_support_subset {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop) (T : Set X)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      H.toSheafOfModules.IsQuasicoherent →
      SheafOfModules.supp ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) ⊆ T →
      P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules)) :
    ∀ (F : X.Modules), F.IsCoherent → SheafOfModules.supp F ⊆ T → P F := by
  let Q : X.Modules → Prop := fun F => P F ∨ ¬ SheafOfModules.supp F ⊆ T
  have hQext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      Q S.X₁ → Q S.X₃ → Q S.X₂ := by
    intro S hS h1 h2 h3 hP1 hP3
    have : Mono S.f := hS.mono_f
    have : Epi S.g := hS.epi_g
    rcases hP1 with hP1 | hP1
    · rcases hP3 with hP3 | hP3
      · exact Or.inl (hext S hS h1 h2 h3 hP1 hP3)
      · exact Or.inr fun hT => hP3 ((supp_of_epi S.g).trans hT)
    · exact Or.inr fun hT => hP1 ((supp_of_mono S.f).trans hT)
  have hQideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z] (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      H.toSheafOfModules.IsQuasicoherent →
      Q ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) := by
    intro Z i hi hZ H hH
    by_cases hs : SheafOfModules.supp
        ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) ⊆ T
    · exact Or.inl (hideal i H hH hs)
    · exact Or.inr hs
  exact fun F hF hFT => (CoherentDevissage.property_of_isCoherent X Q (Or.inl hzero) hQext
    hQideal F hF).resolve_right (not_not_intro hFT)

private theorem property_of_proper_support {X : Scheme.{u}} [IsNoetherian X]
    (P : X.Modules → Prop) (T : Set X) (ξ : X) (hξ : ξ ∈ T)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      (I.support : Set X) ⊆ T → (I.support : Set X) ≠ T →
      ∀ (H : (SheafOfModules.unit I.subscheme.ringCatSheaf).Submodule)
        [H.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward I.subschemeι).obj H.toSheafOfModules))
    (F : X.Modules) (hF : F.IsCoherent) (hFT : SheafOfModules.supp F ⊆ T)
    (hFξ : ξ ∉ SheafOfModules.supp F) : P F := by
  apply property_of_support_subset P (SheafOfModules.supp F) hzero hext ?_ F hF le_rfl
  intro Z i hi hZ H hH hHF
  by_cases hz : IsZero H.toSheafOfModules
  · exact property_pushforward_ideal_of_isZero P hzero hext i H hz
  · have hs := supp_pushforward_ideal i H (isCoherent_ideal_of_quasicoherent i H) hz
    have hiF : Set.range i ⊆ SheafOfModules.supp F := by rwa [hs] at hHF
    exact property_of_closed_immersion P T hzero hext hideal i (hiF.trans hFT)
      (fun heq => hFξ (hiF (heq.symm ▸ hξ))) H

/-! ### [Stacks, Tag 01YL] -/

-- Keep the terminal-object instance used by the statement; the proof-only imports also provide
-- a definitionally equal instance through local sites.
attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape in
/-- **[Stacks, Tag 01YL], in the corrected form.** Let `X` be a Noetherian scheme, `Z₀` an
irreducible closed subset with generic point `ξ`, and `P` a property of coherent modules which
holds for the zero module, is stable under extensions of coherent modules, descends from a
nonempty finite direct sum, holds for the direct image of every quasi-coherent sheaf of ideals on
every integral closed subscheme strictly inside `Z₀`, and admits one coherent `G` of support
exactly `Z₀` whose stalk at `ξ` is annihilated by the maximal ideal there and which has, inside
every ideal multiple `J·G` with `J_ξ` the whole local ring, a quasi-coherent subsheaf agreeing
with `G` at `ξ` for which `P` holds. Then `P` holds for every coherent module whose support is
contained in `Z₀`.

The correction is the hypothesis `hzero`: the source's four conditions do not list `P` for the
zero module and do not imply it, and without it the statement is false. See this file's
implementation notes for the counterexample. -/
@[stacks 01YL]
public theorem property_irreducible_higher_rank
    (X : Scheme.{u}) [IsNoetherian X]
    (Z₀ : Set X) (hZ₀ : IsClosed Z₀)
    (ξ : X) (hξ : IsGenericPoint ξ Z₀)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      P S.X₁ → P S.X₃ → P S.X₂)
    (hsum : ∀ (F : X.Modules), F.IsCoherent →
      (∃ n : ℕ, P (∏ᶜ (fun _ : Fin (n + 1) => F))) → P F)
    (hproper : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      (I.support : Set X) ⊆ Z₀ → (I.support : Set X) ≠ Z₀ →
      ∀ (H : (SheafOfModules.unit I.subscheme.ringCatSheaf).Submodule)
        [H.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward I.subschemeι).obj H.toSheafOfModules))
    (hgeneric : ∃ (G : X.Modules), G.IsCoherent ∧
      (∀ x : X, x ∈ Z₀ ↔ Nontrivial (G.presheaf.stalk x)) ∧
      Tag01YEStalkBridge.IsMaximalIdealAnnihilated G ξ ∧
      (∀ (J : X.IdealSheafData), ξ ∉ J.support →
        ∃ (G' : G.Submodule),
          G'.toSheafOfModules.IsQuasicoherent ∧
          (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
            (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
              J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
          Function.Surjective
            (((TopCat.Presheaf.stalkFunctor Ab ξ).map
              (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
          P G'.toSheafOfModules)) :
    ∀ (F : X.Modules), F.IsCoherent →
      (∀ x : X, Nontrivial (F.presheaf.stalk x) → x ∈ Z₀) → P F := by
  classical
  rcases hgeneric with ⟨G, hGc, hGsupport, hGann, hGJ⟩
  have hGs : SheafOfModules.supp G ⊆ Z₀ := fun x hx =>
    (hGsupport x).mpr ((SheafOfModules.mem_supp_iff_nontrivial_stalk G x).mp hx)
  have hGξ : ξ ∈ SheafOfModules.supp G :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk G ξ).mpr
      ((hGsupport ξ).mp hξ.mem)
  have hsmall := property_of_proper_support P Z₀ ξ hξ.mem hzero hext hproper
  have hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      H.toSheafOfModules.IsQuasicoherent →
      SheafOfModules.supp ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) ⊆ Z₀ →
      P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) := by
    intro Z i hi hZ H hH hs
    by_cases hHz : IsZero H.toSheafOfModules
    · exact property_pushforward_ideal_of_isZero P hzero hext i H hHz
    have hHc := isCoherent_ideal_of_quasicoherent i H
    have hs' : Set.range i ⊆ Z₀ := by rwa [supp_pushforward_ideal i H hHc hHz] at hs
    by_cases heq : Set.range i = Z₀
    · have hgen : IsGenericPoint (i (genericPoint Z)) Z₀ := by
        have h := (genericPoint_spec Z).image i.continuous
        rwa [Set.image_univ, heq, hZ₀.closure_eq] at h
      have hpoint : i (genericPoint Z) = ξ := hgen.eq hξ
      have hann : Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
          (i (genericPoint Z)) := hpoint ▸ hGann
      obtain ⟨r, A, hAc, hMc, ψ, hψ, U, hU, hψU⟩ :=
        Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint
          i (genericPoint Z) (genericPoint_spec Z) G hann
      have hψst := stalk_isIso_of_restrict_isIso ψ U (i (genericPoint Z)) hU
      apply property_of_ideal_of_generic_coproduct i P Z₀ hs' hzero hext hsum
        (by simpa only [hpoint] using hsmall)
        (by simpa only [hpoint] using hGξ) ?_ r A hAc ψ H
      intro M hM f hf hfc
      apply property_of_generic_mono P Z₀ ξ hext hsmall hGc hGs hGJ hM f
      simpa only [hpoint] using hfc
    · exact property_of_closed_immersion P Z₀ hzero hext hproper i hs' heq H
  intro F hF hFs
  exact property_of_support_subset P Z₀ hzero hext hideal F hF fun x hx =>
    hFs x ((SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mp hx)

/-- **[Stacks, Tag 01YL] in the form the library consumes it.** Every Noetherian scheme satisfies
`Stacks.AlgebraicGeometry.Tag01YMHigherRank.HasIrreducibleHigherRankCriterion`, that file's
restatement of this tag over library names, which it — and the files deriving
[Stacks, Tag 01YM], [Stacks, Tag 01YQ] and the dévissage of `H¹` from it — carried as an open
hypothesis. -/
public theorem hasIrreducibleHigherRankCriterion (X : Scheme.{u}) [IsNoetherian X] :
    Tag01YMHigherRank.HasIrreducibleHigherRankCriterion X := by
  intro Z₀ hZ₀ ξ hξ P hzero hext hsum hproper hgeneric
  refine property_irreducible_higher_rank X Z₀ hZ₀ ξ hξ P hzero hext hsum hproper ?_
  obtain ⟨G, hGc, hGsupp, hGann, hGJ⟩ := hgeneric
  refine ⟨G, hGc, hGsupp, hGann, fun J hJ => ?_⟩
  obtain ⟨G', hG'c, hG'J, hG'ξ, hG'P⟩ := hGJ J hJ
  have : G'.toSheafOfModules.IsCoherent := hG'c
  exact ⟨G', isQuasicoherent_of_isCoherent G'.toSheafOfModules, hG'J, hG'ξ, hG'P⟩

end Stacks.AlgebraicGeometry.HigherRankIrreducibleDevissage

end
