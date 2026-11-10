module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.AnnihilatorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.Surjectivity
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AscendingChain
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The global-sections clause of Tag 01YB

Let `X` be a Noetherian scheme, let `I` be a quasi-coherent sheaf of ideals, let `Z = V(I)` and
let `U = X \ Z`. The global-sections half of [Stacks, Tag 01YB] asserts that the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, F) ⟶ Γ(U, F)`

of `StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/Injectivity.lean` is a bijection. Its
injectivity is the first assertion of Tag 01PQ and is proved there. Its surjectivity is, in the
source, deduced from the *second* assertion of Tag 01PQ — proved for a module without `I`-power
torsion in `StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/Surjectivity.lean` — applied not
to `F` but to the submodule `F' = Iᵐ F` for a well-chosen `m`: that submodule has the same
sections as `F` away from `Z`, and no nonzero section of it is annihilated by any power of `I`,
so for `F'` the quotients `F'/F'_N` appearing in Tag 01PQ are `F'` itself.

This file proves that `m` exists, assembles the reduction, and concludes the clause. Concretely
it supplies:

* the interface that lets the ascending chain condition of [Stacks, Tag 01Y8], which is stated
  for `CategoryTheory.Subobject`, be applied to a chain of `SheafOfModules.Submodule`s;
* the stabilisation of the chain `F_1 ⊆ F_2 ⊆ ⋯` of sections annihilated by the powers of `I`;
* the combination of that stabilisation with Artin-Rees, which is the step of the source reading
  "picking `m = n + c` we get `IᵐF ∩ H = 0`"; and
* the conclusion that `F' = Iᵐ F` has no `I`-power torsion at all, together with the comparison
  `F'|_U = F|_U`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι`: the inclusion of a subsheaf into the
  ambient sheaf, as a morphism of `AlgebraicGeometry.Scheme.Modules`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.subobjectOfSubmodule`: the subobject of `M`
  determined by a subsheaf of `M`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.subobjectOfSubmodule_injective` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.subobjectOfSubmodule_mono`: the passage from
  subsheaves to subobjects is an order embedding, so a chain of subsheaves may be fed to
  [Stacks, Tag 01Y8] and the resulting equality of subobjects read back as equality of
  subsheaves.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_idealPowerAnnihilator_eventually_constant`:
  the chain of ideal-power annihilators of a coherent module on a Noetherian scheme stabilises.
* `exists_idealPow_smul_inf_forall_idealPowerAnnihilator_eq_bot`: a single power `Iᵐ` works
  against *every* annihilator in that chain.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_noIdealTorsion_idealPowerMultiple`:
  consequently `Iᵐ F` has no `I`-power torsion.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.submoduleι_app_bijective_of_disjoint_support`:
  away from the support of `I` the inclusion `Iᵐ F ⊆ F` is bijective on sections, which is
  `F'|_U = F|_U`.
* `noIdealTorsion_iff_forall_idealPowerAnnihilator_eq_bot`: having no `I`-power torsion
  is the vanishing of every annihilator subsheaf, `F'_N = 0` for all `N`, which is how the
  source phrases it.
* `exists_isCoherent_app_eq`: a section of a quasi-coherent module over a quasi-compact open is
  the image of a section of a coherent module mapping to it. This is the reduction of Tag 01YB to
  the coherent case, through [Stacks, Tag 01PF].
* `exists_hom_idealPow_app_oneSection_eq_of_isCoherent` and
  `exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent`: **the global-sections clause of
  Tag 01YB in existence form** — every section of `F` over `U` is `φ(1)` for some `φ : Iⁿ ⟶ F`.
* `canonicalMapToSections_bijective_of_isQuasicoherent`: **the global-sections clause of
  Tag 01YB**, in the form "the canonical map is a bijection". This carries the tag.

## Implementation notes

**Reducing a quasi-coherent `F` to a coherent one.** Coherence of `F` is used only to produce
the `m`, through Artin-Rees and Tag 01Y8; the surjectivity statement it is fed to needs no
finiteness at all. The source removes the hypothesis by writing `F` as the filtered union of its
coherent submodules, [Stacks, Tag 01PG], which needs a section of `F` over `U` to lie in one of
them. That does not follow from the two forms Tag 01PG is available in:
`AlgebraicGeometry.isColimit_finiteTypeQuasicoherentSubobjectCocone` is a colimit statement in
`AlgebraicGeometry.Scheme.Modules`, and the supremum in
`AlgebraicGeometry.iSup_finiteTypeQuasicoherentSubobject_eq_top` is the sheafified one, the
`CompleteLattice` on `SheafOfModules.Submodule` being built from its `InfSet` so that only
infima are computed pointwise. So the reduction is done here through [Stacks, Tag 01PF] instead,
as `exists_isCoherent_app_eq`: `U = X \\ V(I)` is quasi-compact on a Noetherian scheme, the
section `s` generates a finite type quasi-coherent submodule of `F|_U` as the image of
`𝒪_U ⟶ F|_U`, and `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension` extends
that to a finite type quasi-coherent — hence, by Tag 01XZ, coherent — module on all of `X`
mapping to `F` and hitting `s` over `U`. Only a map to `F` is needed, not a submodule of it,
which is why `exists_isCoherent_app_eq` asks for no monomorphism.

`AlgebraicGeometry.restrictTopIso` and its naturality duplicate two `private` declarations of
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/FiniteTypeSubobjectColimit.lean`; being
private there they cannot be imported, and they are what converts between the global sections of
`F|_U` and the sections of `F` over `U`.

**The `Subobject` interface.** [Stacks, Tag 01Y8] is stated for `CategoryTheory.Subobject F`
while the annihilators are `SheafOfModules.Submodule F`, so the two must be compared.
`Mono (submoduleι N)` cannot be inherited from Mathlib's `SheafOfModules.Submodule.instMonoι`:
`AlgebraicGeometry.Scheme.Modules` is a `def` whose `Hom` is a separate `def`, so a `Mono` for
the `SheafOfModules` category instance is not found by instance search for the
`Scheme.Modules` one, and `Subobject` in the two categories are different types. The instance is
therefore rebuilt from `AlgebraicGeometry.cancel_sheafSubmodule_ι`. Going back from an equality
of subobjects to an equality of subsheaves is `le_of_subobjectOfSubmodule_le`, which reads a
section of the smaller subsheaf through the comparison morphism supplied by
`CategoryTheory.Subobject.ofMkLEMk`.

**`⊥` for subsheaves.** "No `I`-power torsion" is *stated* as a condition on sections over
affine opens, because that is the form the affine theory consumes and it needs no separatedness
argument. It is however equivalent to the vanishing of every annihilator subsheaf, and that
equivalence is `noIdealTorsion_iff_forall_idealPowerAnnihilator_eq_bot`. Getting there
needs the sections of `(⊥ : M.Submodule)`, which the `CompleteLattice` instance does not compute:
that instance is built from the `InfSet` on `SheafOfModules.Submodule`, so `⊥` is
`sInf Set.univ` and nothing says it is the zero subsheaf. So the zero subsheaf is constructed
here, as `zeroSubmodule`, its sheaf condition being separatedness of `M` in the form
`Stacks.AlgebraicGeometry.IdealPower.eq_zero_of_locally_zero`; `zeroSubmodule_eq_bot` then
identifies it with `⊥`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA) (Artin-Rees)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower SheafOfModules
open AlgebraicGeometry.SheafOfModules.Submodule
  (eq_zero_of_ιModules_app_eq_zero mem_of_ιModules_app)

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Subsheaves as subobjects -/

/-- The inclusion of a subsheaf into the ambient sheaf, as a morphism of `X.Modules`. -/
noncomputable def submoduleι {M : X.Modules} (N : M.Submodule) : subMod N ⟶ M := N.ι

/-- The inclusion of one subsheaf into a larger one, as a morphism of `X.Modules`. -/
noncomputable def submoduleHomOfLE {M : X.Modules} {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    subMod N₁ ⟶ subMod N₂ := SheafOfModules.Submodule.homOfLE h

/-- The inclusion of `N₁` into `N₂` followed by the inclusion of `N₂` into `M` is the inclusion
of `N₁` into `M`. -/
theorem submoduleHomOfLE_ι {M : X.Modules} {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    submoduleHomOfLE h ≫ submoduleι N₂ = submoduleι N₁ := rfl

/-- The inclusion of a subsheaf is a monomorphism of `X.Modules`. It is rebuilt from
`AlgebraicGeometry.cancel_sheafSubmodule_ι`; see the module documentation for why Mathlib's
instance for `SheafOfModules` does not apply. -/
instance mono_submoduleι {M : X.Modules} (N : M.Submodule) : Mono (submoduleι N) :=
  ⟨fun _ _ h => cancel_sheafSubmodule_ι N _ _ h⟩

/-- The subobject of `M` determined by a subsheaf of `M`. -/
noncomputable def subobjectOfSubmodule {M : X.Modules} (N : M.Submodule) : Subobject M :=
  Subobject.mk (submoduleι N)

/-- `subobjectOfSubmodule` is monotone. -/
theorem subobjectOfSubmodule_mono {M : X.Modules} :
    Monotone (subobjectOfSubmodule (M := M)) := fun _ _ h =>
  Subobject.mk_le_mk_of_comm (submoduleHomOfLE h) (submoduleHomOfLE_ι h)

/-- `subobjectOfSubmodule` reflects the order: if the subobject of `N₁` lies below that of `N₂`,
then `N₁ ≤ N₂`. A section of `N₁` is read in `N₂` through the comparison morphism
`CategoryTheory.Subobject.ofMkLEMk`. -/
theorem le_of_subobjectOfSubmodule_le {M : X.Modules} {N₁ N₂ : M.Submodule}
    (h : subobjectOfSubmodule N₁ ≤ subobjectOfSubmodule N₂) : N₁ ≤ N₂ := by
  have hg : Subobject.ofMkLEMk (submoduleι N₁) (submoduleι N₂) h ≫ submoduleι N₂
      = submoduleι N₁ := Subobject.ofMkLEMk_comp h
  refine SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr ?_)
  intro W s hs
  set g := Subobject.ofMkLEMk (submoduleι N₁) (submoduleι N₂) h with hgdef
  set z : N₁.toSubmodule.obj W := ⟨s, hs⟩ with hz
  have key : (((g.val.app W) z).1 : M.val.obj W) = s :=
    congrArg (fun φ : subMod N₁ ⟶ M => (φ.val.app W) z) hg
  rw [← key]
  exact ((g.val.app W) z).2

/-- Distinct subsheaves determine distinct subobjects. -/
theorem subobjectOfSubmodule_injective {M : X.Modules} :
    Function.Injective (subobjectOfSubmodule (M := M)) := fun _ _ h =>
  le_antisymm (le_of_subobjectOfSubmodule_le h.le) (le_of_subobjectOfSubmodule_le h.ge)

/-- The subobject determined by a quasi-coherent subsheaf is quasi-coherent. -/
theorem isQuasicoherent_subobjectOfSubmodule {M : X.Modules} (N : M.Submodule)
    (h : N.toSheafOfModules.IsQuasicoherent) :
    (subobjectOfSubmodule N : X.Modules).IsQuasicoherent :=
  Stacks.Descent.isQuasicoherent_of_iso (Subobject.underlyingIso (submoduleι N)).symm h

/-! ### Stabilisation of the chain of ideal-power annihilators -/

/-- **The stabilisation step of [Stacks, Tag 01YB].** On a Noetherian scheme the ascending chain
`F_1 ⊆ F_2 ⊆ ⋯` of subsheaves of sections of a coherent module annihilated by the powers of `I`
is eventually constant.

This is [Stacks, Tag 01Y8] for that chain; the quasi-coherence of its members is the instance
`Stacks.AlgebraicGeometry.IdealPowerColimit.isQuasicoherent_idealPowerAnnihilator`. -/
theorem exists_idealPowerAnnihilator_eventually_constant [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      idealPowerAnnihilator I.unitSubmodule F m
        = idealPowerAnnihilator I.unitSubmodule F n := by
  have hqc : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨n, hn⟩ := AlgebraicGeometry.exists_eventually_constant_quasicoherentSubobjects X F
    (fun k => subobjectOfSubmodule (idealPowerAnnihilator I.unitSubmodule F k))
    (fun _ => isQuasicoherent_subobjectOfSubmodule _ inferInstance)
    (fun _ _ hkl => subobjectOfSubmodule_mono
      (idealPowerAnnihilator_monotone I.unitSubmodule F hkl))
  exact ⟨n, fun m hm => subobjectOfSubmodule_injective (hn m hm)⟩

/-! ### Artin-Rees against every annihilator at once -/

/-- **The step of [Stacks, Tag 01YB] reading "picking `m = n + c` we get `IᵐF ∩ H = 0`".** For a
coherent module `F` on a Noetherian scheme there is a *single* power `Iᵐ` of `I` such that
`Iᵐ F` meets every ideal-power annihilator of `F` in zero.

The source only needs this for the stable value `H = F_n`; it then observes that the annihilators
of `F' = Iᵐ F` vanish for *all* exponents, which is what
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_noIdealTorsion_idealPowerMultiple`
records.  Both facts come from the same `m`, because every annihilator is contained in the stable
one. -/
theorem exists_idealPow_smul_inf_forall_idealPowerAnnihilator_eq_bot
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent] :
    ∃ m : ℕ, ∀ (N : ℕ) (U : X.affineOpens),
      (I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
        (idealPowerAnnihilator I.unitSubmodule F N).toSubmodule.obj (op U.1) = ⊥ := by
  obtain ⟨n, hn⟩ := exists_idealPowerAnnihilator_eventually_constant I F
  obtain ⟨m, _, hm⟩ := exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot F I n
  refine ⟨m, fun N U => le_antisymm ?_ bot_le⟩
  have hle : idealPowerAnnihilator I.unitSubmodule F N
      ≤ idealPowerAnnihilator I.unitSubmodule F n :=
    le_trans (idealPowerAnnihilator_monotone I.unitSubmodule F (le_max_left N n))
      (le_of_eq (hn _ (le_max_right N n)))
  refine le_trans (inf_le_inf_left _ ?_) (le_of_eq (hm U))
  exact (PresheafOfModules.Submodule.le_iff.mp (SheafOfModules.Submodule.le_iff.mp hle)) _

/-! ### The module `F' = Iᵐ F` -/

/-- **The module `F' = Iᵐ F` of [Stacks, Tag 01YB].** For a coherent module `F` on a Noetherian
scheme some power `Iᵐ F` has no `I`-power torsion: "the subsheaf `(F')_N` of sections annihilated
by `I^N` is zero for all `N ≥ 0`". -/
theorem exists_noIdealTorsion_idealPowerMultiple [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent] :
    ∃ m : ℕ, NoIdealTorsion I (subMod (idealPowerMultiple I m F)) := by
  have hqc : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨m, hm⟩ := exists_idealPow_smul_inf_forall_idealPowerAnnihilator_eq_bot I F
  refine ⟨m, fun N V s hs => eq_zero_of_ιModules_app_eq_zero _ _ s ?_⟩
  set t := (submoduleι (idealPowerMultiple I m F)).app V.1 s with ht
  have hval : ∀ a ∈ (I.ideal V ^ N : Ideal Γ(X, V.1)), a • t = 0 := by
    intro a ha
    rw [ht, ← Scheme.Modules.Hom.app_smul, hs a ha]
    exact map_zero (ConcreteCategory.hom
      ((submoduleι (idealPowerMultiple I m F)).app V.1))
  have hann := (mem_idealPowerAnnihilator_affineOpen I F N V t).mpr hval
  have hmul : t ∈ (I.ideal V ^ m • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1))) := by
    have h2 := mem_of_ιModules_app (idealPowerMultiple I m F) V.1 s
    rwa [idealPowerMultiple_obj_affineOpen I m F V] at h2
  have hinf : t ∈ (I.ideal V ^ m • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1))) ⊓
      (idealPowerAnnihilator I.unitSubmodule F N).toSubmodule.obj (op V.1) := ⟨hmul, hann⟩
  rw [hm N V, Submodule.mem_bot] at hinf
  exact hinf

/-! ### The zero subsheaf, and the source's phrasing `F'_N = 0` -/

/-- The zero subsheaf of a sheaf of modules. Its sheaf condition is separatedness of `M`. -/
noncomputable def zeroSubmodule (M : X.Modules) : M.Submodule where
  toSubmodule :=
    { obj := fun _ => ⊥
      map := fun _ => bot_le }
  isSheaf := by
    intro V s hs
    rw [Submodule.mem_bot]
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = V := ⟨V.unop, rfl⟩
    refine eq_zero_of_locally_zero (M := M) s fun x hx => ?_
    obtain ⟨W', f, hf, hxW'⟩ := hs x hx
    exact ⟨W', f.le, hxW', hf⟩

/-- The zero subsheaf is the bottom element `⊥` of the lattice of subsheaves. -/
theorem zeroSubmodule_eq_bot (M : X.Modules) : zeroSubmodule M = ⊥ :=
  le_antisymm (SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun _ => bot_le)) bot_le

/-- A section of `(⊥ : M.Submodule)` is zero. -/
theorem eq_zero_of_mem_submodule_bot {M : X.Modules} {V : (Opens X)ᵒᵖ} {s : M.val.obj V}
    (hs : s ∈ (⊥ : M.Submodule).toSubmodule.obj V) : s = 0 :=
  (PresheafOfModules.Submodule.le_iff.mp (SheafOfModules.Submodule.le_iff.mp
    (bot_le : (⊥ : M.Submodule) ≤ zeroSubmodule M))) V hs

/-- A subsheaf with no nonzero sections is `⊥`. -/
theorem submodule_eq_bot_of_forall_eq_zero {M : X.Modules} (N : M.Submodule)
    (h : ∀ (V : (Opens X)ᵒᵖ) (s : M.val.obj V), s ∈ N.toSubmodule.obj V → s = 0) : N = ⊥ := by
  have hle : N ≤ zeroSubmodule M :=
    SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr
      fun V s hs => (Submodule.mem_bot _).mpr (h V s hs))
  exact le_antisymm (zeroSubmodule_eq_bot M ▸ hle) bot_le

/-- **`G_N = 0` for all `N`.** Having no `I`-power torsion is exactly the vanishing of every
annihilator subsheaf, which is how [Stacks, Tag 01YB] phrases the property of `F' = Iᵐ F` that
makes [Stacks, Tag 01PQ] apply to it. -/
theorem noIdealTorsion_iff_forall_idealPowerAnnihilator_eq_bot
    (I : X.IdealSheafData) (G : X.Modules) :
    NoIdealTorsion I G ↔
      ∀ N : ℕ, idealPowerAnnihilator I.unitSubmodule G N = ⊥ := by
  constructor
  · intro h N
    refine submodule_eq_bot_of_forall_eq_zero _ fun V s hs => ?_
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = V := ⟨V.unop, rfl⟩
    refine eq_zero_of_restrict_affineOpens_eq_zero (M := G) s fun V' hV' => ?_
    exact h N V' _ ((mem_idealPowerAnnihilator_affineOpen I G N V' _).mp
      ((idealPowerAnnihilator I.unitSubmodule G N).toSubmodule.map (homOfLE hV').op hs))
  · intro h N V s hs
    exact eq_zero_of_mem_submodule_bot
      (h N ▸ (mem_idealPowerAnnihilator_affineOpen I G N V s).mpr hs)

/-! ### `F'|_U = F|_U` -/

/-- **`F'|_U = F|_U`.** Over an open disjoint from the support of `I` the inclusion
`Iᵐ F ⟶ F` is bijective on sections, since there `Iᵐ F` is all of `F`
(`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_eq_top_of_disjoint_support`). -/
theorem submoduleι_app_bijective_of_disjoint_support (I : X.IdealSheafData) (m : ℕ)
    (F : X.Modules) {W : X.Opens} (hW : Disjoint (W : Set X) (I.support : Set X)) :
    Function.Bijective (ConcreteCategory.hom
      ((submoduleι (idealPowerMultiple I m F)).app W)) := by
  have htop : (idealPowerMultiple I m F).toSubmodule.obj (op W) = ⊤ :=
    idealPowerMultiple_obj_eq_top_of_disjoint_support I m F hW le_rfl
  exact ⟨fun _ _ h => Subtype.ext h, fun x => ⟨⟨x, htop ▸ Submodule.mem_top⟩, rfl⟩⟩

/-! ### The global-sections clause of Tag 01YB -/

/-- Every ideal of a quasi-coherent sheaf of ideals on a locally Noetherian scheme is finitely
generated on each affine open. -/
theorem idealSheafData_ideal_fg [AlgebraicGeometry.IsLocallyNoetherian X] (I : X.IdealSheafData)
    (V : X.affineOpens) : (I.ideal V).FG :=
  let : IsNoetherianRing Γ(X, V.1) := AlgebraicGeometry.IsLocallyNoetherian.component_noetherian V
  IsNoetherian.noetherian _

/-! ### Reduction of a quasi-coherent module to a coherent one -/

/-- The constant compatible family of restrictions of a global section. -/
noncomputable def sectionsOfTop (M : X.Modules) (t : Γ(M, ⊤)) : M.sections :=
  M.val.sectionsMk (fun V => M.val.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op t)
    (by
      intro V W g
      change M.val.presheaf.map g
          (M.val.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op t) = _
      exact (M.val.presheaf.map_comp_apply _ g t).symm.trans
        (congrArg (fun j => M.val.presheaf.map j t) (Subsingleton.elim _ _)))

/-- The component of `sectionsOfTop M t` over `⊤` is `t` itself. -/
theorem sectionsOfTop_val_top (M : X.Modules) (t : Γ(M, ⊤)) :
    (sectionsOfTop M t).val (op ⊤) = t := by
  change M.val.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op t = t
  rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)) = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

/-- **Reduction to a coherent module, through [Stacks, Tag 01PF].** On a Noetherian scheme, every
section `s` of a quasi-coherent module `F` over a quasi-compact open `U` is the image under some
morphism `G ⟶ F` of a section over `U` of a coherent module `G`.

The section generates a finite type quasi-coherent submodule of `F|_U`, the image of
`𝒪_U ⟶ F|_U`, and `AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_extension` extends
it to a finite type quasi-coherent, hence coherent, module on `X` mapping to `F`. -/
theorem exists_isCoherent_app_eq [AlgebraicGeometry.IsNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (hU : IsCompact (U : Set X))
    (s : Γ(F, U)) :
    ∃ (G : X.Modules) (ι : G ⟶ F) (t : Γ(G, U)),
      _root_.SheafOfModules.IsCoherent G ∧ ι.app U t = s := by
  classical
  let Fw : U.toScheme.Modules := F.restrict U.ι
  have hFwqc : Fw.IsQuasicoherent := inferInstance
  let sTop : Γ(Fw, ⊤) := (AlgebraicGeometry.restrictTopIso F U).inv s
  let O : U.toScheme.Modules := SheafOfModules.unit U.toScheme.ringCatSheaf
  let _ : O.IsQuasicoherent := (unit_isQuasicoherent_and_isFiniteType (X := U.toScheme)).1
  let _ : O.IsFiniteType := (unit_isQuasicoherent_and_isFiniteType (X := U.toScheme)).2
  let f : O ⟶ Fw := Fw.unitHomEquiv.symm (sectionsOfTop Fw sTop)
  let K : Subobject Fw := imageSubobject f
  have hKqc : (K : U.toScheme.Modules).IsQuasicoherent := imageSubobject_isQuasicoherent f
  have hKft : (K : U.toScheme.Modules).IsFiniteType := imageSubobject_isFiniteType f
  obtain ⟨G', hG'qc, hG'ft, e, he⟩ :=
    exists_finiteTypeQuasicoherentSubobject_extension F U hU K
  let k : Γ((K : U.toScheme.Modules), ⊤) :=
    (factorThruImageSubobject f).app ⊤ (1 : Γ(U.toScheme, ⊤))
  have hk : K.arrow.app ⊤ k = sTop := by
    refine (congrArg (fun q : O ⟶ Fw => q.app ⊤ (1 : Γ(U.toScheme, ⊤)))
      (imageSubobject_arrow_comp f)).trans ?_
    have h2 := SheafOfModules.unitHomEquiv_apply_coe Fw f (op ⊤)
    rw [Equiv.apply_symm_apply] at h2
    exact (h2.symm).trans (sectionsOfTop_val_top Fw sTop)
  let w : Γ((G' : X.Modules).restrict U.ι, ⊤) := e.inv.app ⊤ k
  have hw : ((Scheme.Modules.restrictFunctor U.ι).map G'.arrow).app ⊤ w = sTop := by
    have h1 := congrArg
      (fun q : (G' : X.Modules).restrict U.ι ⟶ Fw => q.app ⊤ w) he
    refine h1.trans ?_
    change K.arrow.app ⊤ (e.hom.app ⊤ (e.inv.app ⊤ k)) = sTop
    exact (congrArg (fun q : (K : U.toScheme.Modules) ⟶ (K : U.toScheme.Modules) =>
      K.arrow.app ⊤ (q.app ⊤ k)) (Iso.inv_hom_id e)).trans hk
  refine ⟨(G' : X.Modules), G'.arrow,
    (AlgebraicGeometry.restrictTopIso (G' : X.Modules) U).hom w, ?_, ?_⟩
  · exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      (G' : X.Modules)
  · have h2 := ConcreteCategory.congr_hom
      (AlgebraicGeometry.restrictTopIso_naturality G'.arrow U) w
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hw] at h2
    rw [← h2]
    change (AlgebraicGeometry.restrictTopIso F U).hom
      ((AlgebraicGeometry.restrictTopIso F U).inv s) = s
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
    rfl

/-- **The global-sections clause of [Stacks, Tag 01YB], in existence form.** Let `X` be a
Noetherian scheme, `I` a quasi-coherent sheaf of ideals, `F` a coherent `𝒪_X`-module and
`U = X \\ V(I)`. Every section of `F` over `U` is `φ(1)` for some `φ : Iⁿ ⟶ F`.

This is the second display of Tag 01YB read elementwise, and it is the shape its consumers want:
with `G = 𝒪_X` the first display of the tag is `colim_n Hom(Iⁿ G, F) ≅ Hom(G|_U, F|_U)`, so this
is also the `G = 𝒪_X` case of that display.

The proof is the argument of the source: replace `F` by `F' = Iᵐ F` for the `m` of
`exists_noIdealTorsion_idealPowerMultiple`, which has the same sections over `U` by
`submoduleι_app_bijective_of_disjoint_support` and no `I`-power torsion, apply
`canonicalMapToSections_surjective` (Tag 01PQ) to `F'`, and push the resulting map forward along
`F' ⟶ F`. -/
theorem exists_hom_idealPow_app_oneSection_eq_of_isCoherent
    [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsCoherent]
    (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (n : ℕ) (φ : idealPow I n ⟶ F),
      φ.app (I.support.compl : X.Opens) (oneSection I n) = s := by
  have hqc : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨m, hm⟩ := exists_noIdealTorsion_idealPowerMultiple I F
  obtain ⟨s', hs'⟩ := (submoduleι_app_bijective_of_disjoint_support I m F
    (W := (I.support.compl : X.Opens)) disjoint_compl_left).2 s
  obtain ⟨n, ψ, hψ⟩ := exists_hom_idealPow_app_oneSection_eq I (idealSheafData_ideal_fg I)
    (subMod (idealPowerMultiple I m F)) hm s'
  refine ⟨n, ψ ≫ submoduleι (idealPowerMultiple I m F), ?_⟩
  rw [Scheme.Modules.Hom.comp_app]
  change (submoduleι (idealPowerMultiple I m F)).app _
    (ψ.app (I.support.compl : X.Opens) (oneSection I n)) = s
  rw [hψ]
  exact hs'

/-- **The global-sections clause of [Stacks, Tag 01YB], in existence form.** Let `X` be a
Noetherian scheme, `I` a quasi-coherent sheaf of ideals, `F` a quasi-coherent `𝒪_X`-module and
`U = X \\ V(I)`. Every section of `F` over `U` is `φ(1)` for some `φ : Iⁿ ⟶ F`.

This is the second display of the tag read elementwise, and it is the shape its consumers want:
with `G = 𝒪_X` the tag's first display is `colim_n Hom(Iⁿ G, F) ≅ Hom(G|_U, F|_U)`, so this is
also the `G = 𝒪_X` case of that display.

`U` is quasi-compact because `X` is Noetherian, so `exists_isCoherent_app_eq` puts `s` in the
image of a coherent module, and the coherent case applies there. -/
theorem exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (n : ℕ) (φ : idealPow I n ⟶ F),
      φ.app (I.support.compl : X.Opens) (oneSection I n) = s := by
  obtain ⟨G, ιG, t, hG, ht⟩ := exists_isCoherent_app_eq F (I.support.compl : X.Opens)
    (NoetherianSpace.isCompact _) s
  have : G.IsCoherent := hG
  obtain ⟨n, φ, hφ⟩ := exists_hom_idealPow_app_oneSection_eq_of_isCoherent I G t
  refine ⟨n, φ ≫ ιG, ?_⟩
  rw [Scheme.Modules.Hom.comp_app]
  change ιG.app (I.support.compl : X.Opens)
    (φ.app (I.support.compl : X.Opens) (oneSection I n)) = s
  rw [hφ]
  exact ht

/-- **The global-sections clause of [Stacks, Tag 01YB].** For a Noetherian scheme `X`, a
quasi-coherent sheaf of ideals `I` and a quasi-coherent `𝒪_X`-module `F`, the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, F) ⟶ Γ(X \\ V(I), F)`

is a bijection. Injectivity is `canonicalMapToSections_injective`, the first assertion of
[Stacks, Tag 01PQ]; surjectivity is
`exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent`.

**This is the second of the two displays of Tag 01YB.** The tag's *first* display,
`colim_n Hom(Iⁿ G, F) ≅ Hom(G|_U, F|_U)` for a coherent `G`, is not proved here; its `G = 𝒪_X`
case is, so the clause label records the global-sections half only. The first display is what
[Stacks, Tag 0BJZ] consumes: there `G` is the coherent module itself, never `𝒪_X`. Its arrow
is `canonicalMapToHomRestrict` and its bijectivity is
`canonicalMapToHomRestrict_bijective`, whose surjectivity half applies this clause to
`SheafHom(G, F)` and then transports the resulting morphism `Iⁿ ⟶ SheafHom(G, F)` across the
surjection `Iⁿ ⊗ G ⟶ Iⁿ G`, using the vanishing `Iⁿ ker(Iⁿ ⊗ G ⟶ Iⁿ G) = 0` and a second
Artin-Rees step. -/
@[stacks 01YB "global sections", sga "2 II Theorem6" "b)"]
theorem canonicalMapToSections_bijective_of_isQuasicoherent
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] :
    Function.Bijective (canonicalMapToSections I F) := by
  refine ⟨canonicalMapToSections_injective I (idealSheafData_ideal_fg I) F, fun s => ?_⟩
  obtain ⟨n, φ, hφ⟩ := exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent I F s
  exact ⟨Limits.colimit.ι (idealPowHomSystem I F) n φ,
    (canonicalMapToSections_ι I F n φ).trans hφ⟩

end Stacks.AlgebraicGeometry.IdealPowerColimit
