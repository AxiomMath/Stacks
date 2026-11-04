module

public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Filtered
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.GabberDirected
public import StacksFrontier.AlgebraicGeometry.GabberColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Colimit

/-!
# Gabber's theorem reduced to two properties of the subsheaf cut out by a compatible family

`StacksFrontier/AlgebraicGeometry/GabberColimit/Basic.lean` carries out the closure construction
of Stacks 077N and produces, from any `κ`-bounded family of sets of sections of a quasi-coherent
`F`, a submodule sheaf `sheafSubmodule` of `F` whose sections over each affine open are the span
of the chosen ones. Its module docstring records what is then still owed: *the quasi-coherence of
`sheafSubmodule` and the bound on its local generators.*

This file makes that reduction a theorem rather than a remark. It assembles the closure
construction, the subsheaf, the directedness proved in
`StacksFrontier/AlgebraicGeometry/CardinalGeneration/Filtered.lean`, and the colimit criterion of
`StacksFrontier/AlgebraicGeometry/Properties/GabberResult/Colimit.lean` into a proof of **both** open
assertions of Stacks 077N from exactly those two properties — and from nothing else. So the
remaining obligation is now a pair of Lean propositions that can be stated, discharged and gated
independently, and the rest of the tag is mechanized.

## Main results

* `exists_cardinalGeneratedQuasicoherentSubobject_of_section`: granted the two properties, every
  section of `F` over an affine open is a section of a quasi-coherent `κ`-generated subobject of
  `F`. This is the hypothesis `hgen` of
  `Stacks.AlgebraicGeometry.CardinalGeneration.isColimit_cocone_of_exists_mem`, and is the content
  of steps 1–5 of the source's proof.
* `isColimit_cardinalGeneratedQuasicoherentSubobjectCocone_of`: **the colimit assertion of
  Stacks 077N**, granted the same two properties. Together with
  `Stacks.AlgebraicGeometry.CardinalGeneration.cardinalGeneratedQuasicoherentSubobject_isFiltered`,
  which is unconditional, this is the whole of the tag beyond its cardinal.
* `isCompatible_top` and `isCompatible_bot`: the two obligations are universally quantified over
  compatible families, and compatible families exist — the full one and the zero one. Without this
  the reduction could have been vacuous.

## The two remaining obligations

Both are about `Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule F N hN` for a compatible
family `N`, read as an object of `X.Modules` through `submoduleObj`:

* **quasi-coherence.** Over an affine open `U` the sections of the subsheaf are `N U`, and the
  compatibility condition says exactly that `N` is the base change of `N U` along every
  restriction to a smaller affine open; so the restriction of the subsheaf to `U` ought to be the
  quasi-coherent sheaf attached to the module `N U`.
* **the bound on its local generators.** When `N U` is the span of a set `T U` of at most `κ`
  sections, the subsheaf ought to be `κ`-generated, with the covering by all affine opens of `X`
  and the sections of `T U` as the generators over `U`.

Neither is proved here, and no stacks attribute is carried anywhere in this file.

## Implementation notes

`SheafOfModules.Submodule.ι` lives in the `SheafOfModules X.ringCatSheaf` spelling while
`Scheme.Modules.Hom.app` — which is how the colimit criterion states its hypothesis — needs the
`X.Modules` spelling, and `AlgebraicGeometry.Scheme.Modules.Hom` is a separate definition, so the
two are definitionally equal and not interchangeable for dot notation or for instance search.
`submoduleObj` and `submoduleHom` name the `X.Modules` reading once; `Mono` crosses the boundary
by `exact` but is not found by `inferInstanceAs`, which is why `mono_submoduleHom` spells out
Mathlib's own proof instead of citing its instance.

The family of sections fed to the closure construction is the one-element family
`{s|_V : V ≤ U}`, which is a subsingleton over every affine open and so carries the bound `1 ≤ κ`
for free.

## References

* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration

universe u

namespace Stacks.AlgebraicGeometry.GabberColimit

variable {X : Scheme.{u}} (F : X.Modules)

/-! ### Reading a submodule sheaf in the `X.Modules` spelling -/

/-- The sheaf of modules underlying a submodule of `F`, as an object of `X.Modules`. -/
public def submoduleObj (N : F.Submodule) : X.Modules := N.toSheafOfModules

/-- The inclusion of a submodule of `F` into `F`, as a morphism of `X.Modules`. -/
public def submoduleHom (N : F.Submodule) : submoduleObj F N ⟶ F := N.ι

/-- The inclusion of a submodule is a monomorphism of `𝒪_X`-modules. This is Mathlib's
`SheafOfModules.Submodule.instMonoι` crossed to the `X.Modules` spelling; the instance itself is
not found by `inferInstanceAs` there, so its proof is repeated rather than cited. -/
public instance mono_submoduleHom (N : F.Submodule) : Mono (submoduleHom F N) := by
  have h : Mono (N.ι : N.toSheafOfModules ⟶ F) :=
    (SheafOfModules.forget _).mono_of_mono_map (inferInstanceAs (Mono N.toSubmodule.ι))
  exact h

/-- The sections of `F` over `U` in the image of a submodule are exactly the elements of that
submodule. -/
public theorem mem_range_submoduleHom_app (N : F.Submodule) (U : X.Opens) (t : Γ(F, U)) :
    t ∈ Set.range ((submoduleHom F N).app U) ↔ t ∈ N.toSubmodule.obj (op U) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro ht
    exact ⟨(⟨t, ht⟩ : N.toSubmodule.obj (op U)), rfl⟩

/-- A section in the image of a monomorphism into `F` is a section of the subobject that
monomorphism defines. -/
public theorem mem_range_mk_arrow_app {M : X.Modules} (f : M ⟶ F) [Mono f] (U : X.Opens)
    (t : Γ(F, U)) (ht : t ∈ Set.range (f.app U)) :
    t ∈ Set.range ((Subobject.mk f).arrow.app U) := by
  obtain ⟨y, rfl⟩ := ht
  refine ⟨((Subobject.underlyingIso f).inv.app U) y, ?_⟩
  exact (comp_app_apply _ _ U y).symm.trans
    (congrArg (fun k : M ⟶ F => k.app U y) (Subobject.underlyingIso_arrow f))

/-! ### The one-section family fed to the closure construction -/

/-- The family of sections of `F` which over an affine open `V` consists of the restriction of a
fixed section `s` over `U`, when `V ≤ U`, and is empty otherwise. -/
public def singletonFamily {U : X.affineOpens} (s : Γ(F, U.1)) (V : X.affineOpens) :
    Set Γ(F, V.1) :=
  {y | ∃ h : V.1 ≤ U.1, F.presheaf.map (homOfLE h).op s = y}

/-- `singletonFamily` is empty or a singleton. -/
public theorem subsingleton_singletonFamily {U : X.affineOpens} (s : Γ(F, U.1))
    (V : X.affineOpens) : (singletonFamily F s V).Subsingleton := by
  rintro y ⟨h1, rfl⟩ z ⟨h2, rfl⟩
  rfl

/-- The fixed section itself belongs to `singletonFamily` over its own affine open. -/
public theorem self_mem_singletonFamily {U : X.affineOpens} (s : Γ(F, U.1)) :
    s ∈ singletonFamily F s U :=
  ⟨le_rfl, res_self F s⟩

/-! ### The predicate the two remaining obligations quantify over is inhabited -/

/-- The family of **full** submodules is compatible. Both remaining obligations are universally
quantified over compatible families, so this is what makes them non-vacuous — and it is the
non-trivial witness: at this family the subsheaf is the whole of `F`. The compatibility is the
surjectivity half of Stacks 01I9, `span_range_restrict_eq_top`. -/
public theorem isCompatible_top [F.IsQuasicoherent] :
    IsCompatible F (fun _ : X.affineOpens ↦ (⊤ : Submodule Γ(X, _) Γ(F, _))) := by
  intro U W h
  dsimp only
  refine le_antisymm ?_ le_top
  rw [← span_range_restrict_eq_top F U.2 W.2 h]
  refine Submodule.span_mono ?_
  rintro y ⟨m, rfl⟩
  exact ⟨m, trivial, rfl⟩

/-- The family of **zero** submodules is compatible; the degenerate witness, needing no
quasi-coherence. -/
public theorem isCompatible_bot :
    IsCompatible F (fun _ : X.affineOpens ↦ (⊥ : Submodule Γ(X, _) Γ(F, _))) := by
  intro U W h
  dsimp only
  refine le_antisymm bot_le ?_
  refine Submodule.span_le.mpr ?_
  rintro y ⟨m, hm, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot] at hm ⊢
  rw [hm, map_zero]

/-! ### The reduction -/

/-- **The keystone of Stacks 077N, reduced to two properties of `sheafSubmodule`.**

Let `F` be a quasi-coherent `𝒪_X`-module and `κ` an infinite cardinal bounding the number of
affine opens of `X` — both hold for `cardinalBound X`. Suppose that the subsheaf cut out by a
compatible family of submodules of the sections of `F` is always quasi-coherent, and that it is
`κ`-generated whenever the family is spanned by at most `κ` sections over each affine open. Then
every section of `F` over an affine open is a section of a quasi-coherent `κ`-generated subobject
of `F`.

This is steps 1–5 of the source's proof: the closure construction
`exists_bounded_compatible_family` enlarges the one-element family containing `s` to a compatible
one still of size at most `κ`, `sheafSubmodule` turns that into a subsheaf, and
`obj_sheafSubmodule` says `s` is a section of it over `U`. -/
public theorem exists_cardinalGeneratedQuasicoherentSubobject_of_section
    [F.IsQuasicoherent] {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (hX : Cardinal.mk X.affineOpens ≤ κ)
    (hqc : ∀ (N : ∀ V : X.affineOpens, Submodule Γ(X, V.1) Γ(F, V.1))
      (hN : IsCompatible F N), (submoduleObj F (sheafSubmodule F N hN)).IsQuasicoherent)
    (hbd : ∀ (T : ∀ V : X.affineOpens, Set Γ(F, V.1)), (∀ V, Cardinal.mk (T V) ≤ κ) →
      ∀ hN : IsCompatible F (fun V ↦ Submodule.span Γ(X, V.1) (T V)),
        IsCardinalGenerated.{u, u, u}
          (submoduleObj F (sheafSubmodule F (fun V ↦ Submodule.span Γ(X, V.1) (T V)) hN)) κ)
    (U : X.affineOpens) (s : Γ(F, U.1)) :
    ∃ G : CardinalGeneratedQuasicoherentSubobject F κ,
      s ∈ Set.range (G.obj.arrow.app U.1) := by
  classical
  -- the one-element family containing `s`, of size at most one
  have hS : ∀ V, Cardinal.mk (singletonFamily F s V) ≤ κ := fun V ↦
    (((subsingleton_singletonFamily F s V).finite.lt_aleph0.le).trans hκ)
  -- the closure construction enlarges it to a compatible family, still of size at most `κ`
  obtain ⟨T, hST, hT, hTcomp⟩ :=
    exists_bounded_compatible_family F hκ hX (singletonFamily F s) hS
  set N : ∀ V : X.affineOpens, Submodule Γ(X, V.1) Γ(F, V.1) :=
    fun V ↦ Submodule.span Γ(X, V.1) (T V) with hNdef
  have hN : IsCompatible F N := isCompatible_span F T hTcomp
  -- the subsheaf it cuts out, read in `X.Modules`
  set M : X.Modules := submoduleObj F (sheafSubmodule F N hN) with hMdef
  have hMqc : M.IsQuasicoherent := hqc N hN
  have hMgen : IsCardinalGenerated.{u, u, u} M κ := hbd T hT hN
  set f : M ⟶ F := submoduleHom F (sheafSubmodule F N hN) with hfdef
  -- the subobject of `F` it defines, with the two properties transported along the comparison
  refine ⟨⟨Subobject.mk f, ?_, ?_⟩, ?_⟩
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso f).symm hMqc
  · exact @isCardinalGenerated_of_epi _ _ _ _ _ _ _ _ _ (Subobject.underlyingIso f).inv
      (@CategoryTheory.IsIso.epi_of_iso _ _ _ _ _ (CategoryTheory.Iso.isIso_inv _)) _ hMgen
  · -- and `s` is a section of it over `U`, because it survived the closure
    refine mem_range_mk_arrow_app F f U.1 s ?_
    refine (mem_range_submoduleHom_app F (sheafSubmodule F N hN) U.1 s).mpr ?_
    have hmem : s ∈ N U := Submodule.subset_span (hST U (self_mem_singletonFamily F s))
    rw [obj_sheafSubmodule F N hN U]
    exact hmem

/-- **The colimit assertion of Stacks 077N**, granted the same two properties of `sheafSubmodule`.

The directedness of the system is unconditional
(`Stacks.AlgebraicGeometry.CardinalGeneration.cardinalGeneratedQuasicoherentSubobject_isFiltered`),
and the two hypotheses of the colimit criterion
`Stacks.AlgebraicGeometry.CardinalGeneration.isColimit_cocone_of_exists_mem` are therefore reduced
to the single statement above. -/
public def isColimit_cardinalGeneratedQuasicoherentSubobjectCocone_of [F.IsQuasicoherent]
    (hqc : ∀ (N : ∀ V : X.affineOpens, Submodule Γ(X, V.1) Γ(F, V.1))
      (hN : IsCompatible F N), (submoduleObj F (sheafSubmodule F N hN)).IsQuasicoherent)
    (hbd : ∀ (T : ∀ V : X.affineOpens, Set Γ(F, V.1)),
      (∀ V, Cardinal.mk (T V) ≤ cardinalBound X) →
      ∀ hN : IsCompatible F (fun V ↦ Submodule.span Γ(X, V.1) (T V)),
        IsCardinalGenerated.{u, u, u}
          (submoduleObj F (sheafSubmodule F (fun V ↦ Submodule.span Γ(X, V.1) (T V)) hN))
          (cardinalBound X)) :
    IsColimit (cardinalGeneratedQuasicoherentSubobjectCocone F (cardinalBound X)) :=
  isColimit_cocone_of_exists_mem F (cardinalBound X)
    (exists_cardinalGeneratedQuasicoherentSubobject_of_section F
      (aleph0_le_cardinalBound X) (mk_affineOpens_le_cardinalBound X) hqc hbd)

end Stacks.AlgebraicGeometry.GabberColimit

end
