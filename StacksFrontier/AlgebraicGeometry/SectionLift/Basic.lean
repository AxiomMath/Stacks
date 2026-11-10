module

public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic
public import StacksFrontier.AlgebraicGeometry.BundleRoute.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Finitely many sections of a quasi-coherent module lie in one finite type submodule

This is the step of the source proof of [Stacks, Tag 07RM] that reads

> Choose `i` such that there exist sections `e_{j, t} ∈ ℰ_i(V_j)` mapping to `s_{j, t}` in `ℱ`
> for all `j = 1, …, m` and `t = 1, …, n_j`.

and it is the only use that proof makes of the colimit assertion of [Stacks, Tag 01PG]. The two
halves it needs — that every section over an affine open lies in *some* finite type quasi-coherent
submodule, and that finitely many such submodules have a common upper bound — are both in the
library, the first as `Stacks.AlgebraicGeometry.Tag01PGColimitClose.affineSections_of_qcqs` and the
second as
`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`. Their
composition is what the source's "choose `i`" step is.

## Main results

* `Stacks.Tag07RMSectionLift.mem_range_arrow_app_of_hom`: a section of a finite type quasi-coherent
  submodule is a section of any larger one.
* `Stacks.Tag07RMSectionLift.exists_subobject_forall_mem_range`: **the "choose `i`" step.** On a
  quasi-compact quasi-separated scheme, for any *finite* family of pairs (affine open, section of a
  quasi-coherent module over it) there is a single finite type quasi-coherent submodule all of
  whose members' sections are sections of.
* `Stacks.Tag07RMSectionLift.exists_subobject_forall_mem_range_sigma`: the same in the source's
  double-indexed shape, finitely many sections over each of finitely many affine opens.
* `Stacks.Tag07RMSectionLift.exists_hom_forall_mem_range`: the same with the submodule presented as
  an `AlgebraicGeometry.Scheme.Modules` object together with a monomorphism into `F`, which is the
  form a consumer that has to pull the module back along a morphism needs.
* `Stacks.Tag07RMSectionLift.exists_hom_forall_mem_range_pushforward`: the specialisation to
  `ℱ = f_* ℒ`, which is where [Stacks, Tag 07RM] applies it. Quasi-coherence of `f_* ℒ` is
  [Stacks, Tag 01LC], available as the instance `AlgebraicGeometry.pushforward_isQuasicoherent`, so
  it costs nothing here.

## Implementation notes

The index type is a bare `{ι : Type*}` with `Finite ι` rather than a `Finset` of anything: the
filteredness lemma `CategoryTheory.IsFiltered.sup_objs_exists` wants a
`Finset (AlgebraicGeometry.FiniteTypeQuasicoherentSubobject F)`, which is produced from the family
by `Finset.image` under `classical`, and no consumer of the source's step needs the index to be
decidable.

The transport of a section along a morphism of subobjects is a `congrArg` of an explicit motive
along `CategoryTheory.Subobject.underlying_arrow`, not a `rw`: the sections of
`AlgebraicGeometry.Scheme.Modules` objects are typed through
`CategoryTheory.ConcreteCategory.hom`, and `AlgebraicGeometry.Scheme.Modules.Hom.comp_app` is
`rfl`, so `congrArg` checks at default transparency and goes through where keyed matching does not
— the barrier recorded in `StacksFrontier/AlgebraicGeometry/ColimitClose/Basic.lean`, met here from
the other side. Zero compiler options in this file.

## Where Tag 07RM is, and why no tag is attached here

**No Stacks tag attribute is attached anywhere in this file.** Tag 07RM is proved outright as
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`
(`StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Projective.lean`), at Definition
01W8's `AlgebraicGeometry.IsProjective`, which carries the attribute. Its "choose `i`" step there
is `Stacks.QuasiProjectiveCompactification.exists_isFiniteType_hom_lift`, from the same two
halves as the results below. The other inputs of half 1 are theorems too:

* [Stacks, Tag 01VU], relative ampleness to relatively very ample powers, is
  `Stacks.VeryAmplePowersQuasiCompactBase.tfae`; the form keeping the generating sections, which
  is what half 1 uses, is
  `Stacks.QuasiProjectiveCompactification.exists_finite_affine_cover_familyImmersionTwist`;
* [Stacks, Tag 02NP] is
  `Stacks.CoordinateImmersion.hasImmersionTwistOver_of_isRelativelyVeryAmple`;
* the morphism `r_{ℒ, ψ} : X ⟶ 𝐏(ℰ)` over `S` attached to the graded map
  `Sym(ℰ) ⟶ f_*(⨁_n ℒ^{⊗ n})` — the "whence we obtain a morphism" step of the source, the
  morphism of [Stacks, Tag 01O9] — is the `globalMorphism` of
  `Stacks.QuasiProjectiveCompactification.exists_isImmersion_projectiveBundle_of_cover`.

`Stacks.Tag07RMSectionLift.card_07RM_residue` below is the statement of Tag 07RM over library
names at the bundle predicate `Stacks.Tag087SBundle.IsProjective`, with the tag's binder
list verbatim and in its order, and with `Stacks.Tag07RMBundleRoute.ImmersionIntoBundle`
written in front of it; no declaration converts between that predicate and
`AlgebraicGeometry.IsProjective`, so the argument stays.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Tag07RMSectionLift

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### Growing the submodule keeps the section -/

/-- **A section of a finite type quasi-coherent submodule of `F` is a section of any larger one.**
The inclusion of the smaller one into `F` factors through the larger one by
`CategoryTheory.Subobject.underlying_arrow`, and the witness is the image of the original one. -/
theorem mem_range_arrow_app_of_hom {G H : FiniteTypeQuasicoherentSubobject F}
    (u : G ⟶ H) (U : X.Opens) {s : Γ(F, U)}
    (hs : s ∈ Set.range (G.obj.arrow.app U)) :
    s ∈ Set.range (H.obj.arrow.app U) := by
  obtain ⟨t, ht⟩ := hs
  refine ⟨(Subobject.underlying.map u.hom).app U t, ?_⟩
  rw [← ht]
  exact congrArg (fun m : (G.obj : X.Modules) ⟶ F => m.app U t)
    (Subobject.underlying_arrow u.hom)

/-! ### The "choose `i`" step of [Stacks, Tag 07RM] -/

/-- **Finitely many sections of a quasi-coherent module, each over an affine open, all lie in one
finite type quasi-coherent submodule.**

This is the step of the source proof of [Stacks, Tag 07RM] that chooses a single index `i` of the
directed system, and it is the only use that proof makes of the colimit assertion of
[Stacks, Tag 01PG]. Each section individually lies in some finite type quasi-coherent submodule by
`Stacks.AlgebraicGeometry.Tag01PGColimitClose.affineSections_of_qcqs`; the family is finite, so
filteredness of the category of those submodules
(`AlgebraicGeometry.finiteTypeQuasicoherentSubobject_isFiltered`) provides one that receives them
all.

The hypotheses are exactly those of [Stacks, Tag 01PG]: `X` quasi-compact and quasi-separated and
`F` quasi-coherent. Nothing is assumed of the index type beyond finiteness, and the affine opens
need not cover `X` nor be distinct. -/
theorem exists_subobject_forall_mem_range (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    {ι : Type*} [Finite ι] (V : ι → X.affineOpens) (s : (k : ι) → Γ(F, (V k).1)) :
    ∃ G : FiniteTypeQuasicoherentSubobject F,
      ∀ k, s k ∈ Set.range (G.obj.arrow.app (V k).1) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose G hG using fun k =>
    Stacks.AlgebraicGeometry.Tag01PGColimitClose.affineSections_of_qcqs F (V k) (s k)
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (Finset.image G Finset.univ)
  refine ⟨S, fun k => ?_⟩
  exact mem_range_arrow_app_of_hom
    (hS (Finset.mem_image_of_mem G (Finset.mem_univ k))).some _ (hG k)

/-- **The same in the source's own double-indexed shape**: finitely many sections over each of
finitely many affine opens, as the `s_{j, t}` of [Stacks, Tag 07RM] are indexed. The index type of
`Stacks.Tag07RMSectionLift.exists_subobject_forall_mem_range` is instantiated at the sigma type, so
the number of sections may differ from one open to the next, as the `n_j` of the source do. -/
theorem exists_subobject_forall_mem_range_sigma (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    {J : Type*} [Finite J] (V : J → X.affineOpens) {n : J → Type*} [∀ j, Finite (n j)]
    (s : (j : J) → (t : n j) → Γ(F, (V j).1)) :
    ∃ G : FiniteTypeQuasicoherentSubobject F,
      ∀ (j : J) (t : n j), s j t ∈ Set.range (G.obj.arrow.app (V j).1) := by
  obtain ⟨G, hG⟩ :=
    exists_subobject_forall_mem_range F (fun p : Σ j, n j => V p.1) (fun p => s p.1 p.2)
  exact ⟨G, fun j t => hG ⟨j, t⟩⟩

/-! ### The submodule as a module with a monomorphism -/

/-- **`Stacks.Tag07RMSectionLift.exists_subobject_forall_mem_range` with the submodule presented as
a module and a monomorphism into `F`**, rather than as a `CategoryTheory.Subobject`.

This is the form needed by a consumer that has to do anything with the module itself — pull it back
along a morphism, take its symmetric algebra, form its projective bundle — since those operate on
`AlgebraicGeometry.Scheme.Modules` objects and not on subobjects. -/
theorem exists_hom_forall_mem_range (F : X.Modules)
    [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    {ι : Type*} [Finite ι] (V : ι → X.affineOpens) (s : (k : ι) → Γ(F, (V k).1)) :
    ∃ (E : X.Modules) (_ : E.IsQuasicoherent) (_ : SheafOfModules.IsFiniteType.{u, u, u} E)
      (e : E ⟶ F), Mono e ∧ ∀ k, s k ∈ Set.range (e.app (V k).1) := by
  obtain ⟨G, hG⟩ := exists_subobject_forall_mem_range F V s
  exact ⟨(G.obj : X.Modules), G.property.1, G.property.2, G.obj.arrow, inferInstance, hG⟩

/-- **The specialisation [Stacks, Tag 07RM] uses it at**: `ℱ = f_* ℒ` for a quasi-compact
quasi-separated `f` and a quasi-coherent `ℒ` on the source, over a quasi-compact quasi-separated
base.

Quasi-coherence of the direct image is [Stacks, Tag 01LC], available as the instance
`AlgebraicGeometry.pushforward_isQuasicoherent`, so it is supplied by synthesis and appears in no
hypothesis here. The affine opens are affine opens of the *base*, and the sections are sections of
`f_* ℒ` over them, which is how the source's `s_{j, t} ∈ Γ(f^{-1}(V_j), ℒ) = f_* ℒ(V_j)` are
given. -/
theorem exists_hom_forall_mem_range_pushforward {Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (L : Y.Modules) [L.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X]
    {ι : Type*} [Finite ι] (V : ι → X.affineOpens)
    (s : (k : ι) → Γ((Scheme.Modules.pushforward f).obj L, (V k).1)) :
    ∃ (E : X.Modules) (_ : E.IsQuasicoherent) (_ : SheafOfModules.IsFiniteType.{u, u, u} E)
      (e : E ⟶ (Scheme.Modules.pushforward f).obj L),
      Mono e ∧ ∀ k, s k ∈ Set.range (e.app (V k).1) :=
  exists_hom_forall_mem_range ((Scheme.Modules.pushforward f).obj L) V s

/-! ### Tag `07RM` at the bundle predicate -/

/-- **Tag `07RM` at the bundle predicate `Stacks.Tag087SBundle.IsProjective`.**

This is the statement of Tag `07RM` with its own binder list reproduced verbatim and in its own
order —
the same `{X S : Scheme}`, the same `(f : X ⟶ S)`, the same `[CompactSpace S]` and
`[QuasiSeparatedSpace S]`, the same quasi-projectivity hypothesis and the same existential
conclusion — with the statement's two folded predicates replaced by their library forms
`Stacks.HProjective.IsQuasiProjective` and `Stacks.Tag087SBundle.IsProjective` and nothing else
changed, and with **one hypothesis the tag does not carry** written in front of it:
`Stacks.Tag07RMBundleRoute.ImmersionIntoBundle`, half 1 of the source's own proof.

The tag itself is stated and proved without that argument, at Definition 01W8's
`AlgebraicGeometry.IsProjective`, as
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`, which carries
the attribute; nothing in this file does. -/
theorem card_07RM_residue (hgap : Stacks.Tag07RMBundleRoute.ImmersionIntoBundle.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion i ∧ Stacks.Tag087SBundle.IsProjective p ∧ i ≫ p = f :=
  Stacks.Tag07RMBundleRoute.exists_isOpenImmersion_isProjective hgap f hf

end Stacks.Tag07RMSectionLift

end
