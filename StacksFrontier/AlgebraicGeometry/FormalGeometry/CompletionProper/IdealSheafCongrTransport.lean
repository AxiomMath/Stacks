module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DirectImageComparisonGeneral
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.StalkSupportBridges
public import StacksCore.Tactic.StacksAttribute

/-!
# The last hop: `β` on the compactification carried to the Chow modification

`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_opens_of_isProjectiveMorphism`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/StalkSupportBridges.lean`)
produces the source's isomorphism `β`, with the proper support of the algebraizing module, for an
**open `V` of a scheme `Y'` H-projective over a complete base**, along the ideal sheaf
`(I 𝒪_{Y'}).comap V.ι`. The binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport`
(`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAlgebraization`)
asks for it on **a proper modification `π : Y ⟶ X`**, along `(I 𝒪_X).comap π`. This file closes
that gap.

## How the two ideal sheaves are made equal

Chow's lemma with a projective compactification
(`Stacks.Algebraization.exists_isOpenImmersion_isProjectiveMorphism_denseChowModification`)
produces a proper `π₀ : Y₀ ⟶ X`, an open immersion `j : Y₀ ⟶ Y'` and an H-projective
`p : Y' ⟶ Spec A` with `j ≫ p = π₀ ≫ f`. The modification handed to `hTransport` is **not** `Y₀`
but the open subscheme `V = j(Y₀) ⊆ Y'`, with

  `π = e⁻¹ ≫ π₀ : V ⟶ X`, `e : Y₀ ≅ V` the isomorphism onto the image
  (`AlgebraicGeometry.Scheme.Hom.isoOpensRange`).

Then `π ≫ f = V.ι ≫ p` on the nose — `e⁻¹ ≫ j = V.ι` — so

  `(I 𝒪_X).comap π = I 𝒪 (π ≫ f) = I 𝒪 (V.ι ≫ p) = (I 𝒪_{Y'}).comap V.ι`

by `Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap` alone. Choosing the modification inside
`Y'` is what reduces the transport to an equality of ideal sheaves **on one scheme**; had `Y₀`
been kept, the comparison would have had to cross the isomorphism `e` as well, transporting a
completion along an isomorphism of schemes.

## No new congruence lemma: both transports were already in the library

The two transports this file needs along an equality of ideal sheaves already exist and are
**not** duplicated here.

* `Stacks.Algebraization.idealPowerQuotientCongr`
  (`CompletionProper/DirectImageRestrictOpen.lean`) — the quotient `M / 𝒦 ᵐ M` under an equality
  of ideal sheaves, built from `Stacks.Algebraization.idealPowerQuotientMap` and so normalizing
  against the quotient projections (`…idealPowerQuotientCongrMap_π`), rather than with `eqToHom`;
  that file's implementation notes record why `eqToHom` between two such cokernels times the
  kernel out inside a composite.
* `Stacks.Algebraization.completionFunctorObjCongr`
  (`CompletionCriteria/AffineExistence.lean`) — the whole adic system `G ^∧` under an equality of
  ideal sheaves, by case analysis on the equality. This is the one consumed below, and it is the
  reason no cokernel is spelled out in any type stated here: the equality of ideal sheaves is
  discharged at the level of the *system*, where the ideal sheaf is a parameter of the functor,
  and never at the level of a term `M / 𝒦 ⁿ⁺¹ M`.

Nothing in this file states a cokernel, and nothing here proves an equation between morphisms of
`Scheme.Modules`: the conclusion of `hTransport` is `Nonempty (… ≅ …)`, so the isomorphism has
only to be produced.

## Main results

* `Stacks.Algebraization.isProperOver_of_eq` and `Stacks.Algebraization.hasProperSupport_of_eq` —
  properness of a closed subset over the base, and proper support, transported along an
  **equality of base morphisms**. Needed because `π ≫ f` and `V.ι ≫ p` are equal but not
  syntactically so, and the base morphism of `AlgebraicGeometry.IsProperOver` carries a
  `LocallyOfFiniteType` instance argument which no `rw` at the stated type can carry across.
* `Stacks.Algebraization.exists_hasProperSupport_iso_coherentAdicPullback_of_isOpenImmersion` —
  **the transport**, with the Chow data as hypotheses: for `π₀ : Y₀ ⟶ X` proper,
  `j : Y₀ ⟶ Y'` an open immersion and `p : Y' ⟶ Spec A` H-projective over `f`, every coherent
  `I 𝒪_X`-adic system on `X` with support proper over `A` pulls back to the completion of a
  coherent module with support proper over `A` on a modification of `X` isomorphic to `Y₀`.
  Unconditional.
* `Stacks.Algebraization.exists_hasProperSupport_iso_coherentAdicPullback_of_denseChowModification`
  — the same with the Chow data supplied, so with no hypothesis beyond those of `hTransport`:
  **this is `hTransport` with its join clause `∀ e, K < K ⊔ 𝒦 ᵉ⁺¹` replaced by the density of
  `U` that Chow's lemma actually delivers.** Unconditional.
* `Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_join` — the properness statement
  behind `hSupp`, from [Stacks, Tag 088B] together with the join clause **alone**: every
  geometric ingredient of `hTransport` is discharged by the previous theorem, and what is left is
  a statement about the lattice of quasi-coherent ideal sheaves with no sheaf of modules in it.

## What `hSupp` still waits on, and why the join clause is carried disjunctively

The `β` half of `hTransport` is now proved outright. The other half is **not**, and asked at every
`K` it cannot be: that form is **refutable**. Read it at `K = ⊤` and at the zero system — which is
a coherent adic system, is annihilated by `⊤` (`⊤ ᵉ⁺¹ · 0 = 0`), and has empty, hence proper,
support. The clause then demands `∀ e, ⊤ < ⊤ ⊔ 𝒦 ᵉ⁺¹`, i.e. `⊤ < ⊤`. The same reading refutes
the pre-repair form of the binder `hChow` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_chowComparison`. All three binders —
those two and `hJoin` isolated below — therefore carry the clause **disjunctively**, the repair
`Stacks.Algebraization.IsDirectImageComparison` was given on this branch: either the system
already has a proper annihilator, or the Chow data with the join clause exists.

That is the shape the source's induction has and the transplanted clause lost. The source runs
Chow's lemma not on `X` but on `V(K)`, so that the dense open it produces meets `V(K)`; the join
clause then holds because `𝒦 ᵉ⁺¹ ≤ K` would force `V(K) ⊆ X ∖ U`. At `K = ⊤` there is no `V(K)`
to run it on, and there the source has nothing to prove — which is exactly what the degenerate
disjunct records. What is left is the passage to `V(K)`, a statement about ideal sheaves with the
geometry already discharged here; it is not proved in this file, which owns no part of the
binders that carry the clause beyond threading the disjunction through `hJoin`.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### Properness over the base along an equality of base morphisms -/

/-- **Properness of a closed subset over the base transported along an equality of base
morphisms.** The two base morphisms `π ≫ f` and `V.ι ≫ p` of the transport below are equal but
not syntactically equal, and `AlgebraicGeometry.IsProperOver` carries the base morphism inside a
`LocallyOfFiniteType` instance argument, so a rewrite at that type has no well-typed motive. The
unfolded statement `IsProper ((vanishingIdeal Z).subschemeι ≫ f)` carries no instance argument,
and the rewrite is performed there. -/
public theorem isProperOver_of_eq {X S : Scheme.{u}} {f g : X ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) {Z : Closeds X}
    (hZ : IsProperOver f Z) : IsProperOver g Z := by
  have h' : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) := hZ
  rw [h] at h'
  exact h'

/-- **Proper support transported along an equality of base morphisms**, from
`Stacks.Algebraization.isProperOver_of_eq`: the support itself does not mention the base
morphism. -/
public theorem hasProperSupport_of_eq {X S : Scheme.{u}} {f g : X ⟶ S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) {F : X.Modules}
    (hF : HasProperSupport f F) : HasProperSupport g F := by
  obtain ⟨Z, hZeq, hZp⟩ := hF
  exact ⟨Z, hZeq, isProperOver_of_eq h hZp⟩

/-! ### The transport of `β` to a modification of the base -/

section Transport

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]

/-- **`β` on a Chow modification, from `β` on a projective compactification.** Let `A` be
Noetherian and complete with respect to `I`, let `f : X ⟶ Spec A` be locally of finite type and
quasi-compact, and let

  `π₀ : Y₀ ⟶ X` proper, `j : Y₀ ⟶ Y'` an open immersion, `p : Y' ⟶ Spec A` H-projective

with `j ≫ p = π₀ ≫ f` — the data Chow's lemma with a projective compactification produces. Then
every coherent `I 𝒪_X`-adic system `𝓕` on `X` whose first term has support proper over `A`
admits, on a proper modification `π : Y ⟶ X` isomorphic to `Y₀`, a coherent `𝒪_Y`-module `G` with
support proper over `A` and the source's isomorphism `β : π^*(𝓕_n) ≅ G ^∧`. The modification is
an isomorphism over any open of `X` over which `π₀` is one.

The modification produced is the **open subscheme `V = j(Y₀)` of `Y'`**, with
`π = e⁻¹ ≫ π₀` for `e : Y₀ ≅ V` the isomorphism onto the image; see the module docstring for why
that choice is what makes the two ideal sheaves equal. The isomorphism `β` is then
`Stacks.Algebraization.exists_hasProperSupport_iso_completionFunctor_opens_of_isProjectiveMorphism`
over `V`, read through `Stacks.Algebraization.completionFunctorObjCongr` at that equality; the
proper support of the first term of `π^*(𝓕_n)` is
`Stacks.Algebraization.hasProperSupport_pullback_of_isProper`, properness of `π` being what that
consumes.

Unconditional: every hypothesis is data. -/
@[ega "III 5.3.5" "partial"]
public theorem exists_hasProperSupport_iso_coherentAdicPullback_of_isOpenImmersion
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    {Y₀ Y' : Scheme.{u}} (π₀ : Y₀ ⟶ X) (j : Y₀ ⟶ Y') (p : Y' ⟶ Spec (.of A))
    (hπ₀ : IsProper π₀) (hj : IsOpenImmersion j)
    (hp : AlgebraicGeometry.IsProjectiveMorphism p) (hjp : j ≫ p = π₀ ≫ f)
    (U : X.Opens) (hiso : IsIso (π₀ ∣_ U)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : IsNoetherian X := { }
    ∀ 𝓕 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓕.obj.obj (op 0)) →
        ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y),
          IsIso (π ∣_ U) ∧
            ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
              HasProperSupport (π ≫ f) G.obj ∧
                Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                  (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  have := hπ₀
  have := hj
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p
  intro 𝓕 h𝓕
  -- the open subscheme of `Y'` cut out by the image of `j`, and the modification inside it
  set V : Y'.Opens := j.opensRange with hV
  set e : Y₀ ≅ (V : Scheme.{u}) := j.isoOpensRange with he
  set π : (V : Scheme.{u}) ⟶ X := e.inv ≫ π₀ with hπ
  have : IsProper π := by rw [hπ]; infer_instance
  let : IsLocallyNoetherian (V : Scheme.{u}) := inferInstance
  let : CompactSpace (V : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace π
  let : IsNoetherian (V : Scheme.{u}) := { }
  -- the two base morphisms agree, so the two ideal sheaves do
  have hej : e.inv ≫ j = V.ι := Scheme.Hom.isoOpensRange_inv_comp j
  have hcomp : π ≫ f = V.ι ≫ p := by
    rw [hπ, Category.assoc, ← hjp, ← Category.assoc, hej]
  have hideal : (baseIdealSheaf A I f).comap π = (baseIdealSheaf A I p).comap V.ι :=
    ((Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f π).trans
        (congrArg (baseIdealSheaf A I) hcomp)).trans
      (Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I p V.ι).symm
  -- the pullback of the system, read as a system along the ideal sheaf of `V ⊆ Y'`
  have hprop : IsCoherentAdicSystem ((baseIdealSheaf A I p).comap V.ι)
      ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕).obj := by
    rw [← hideal]
    exact ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕).property
  -- its first term has support proper over `A`, because `π` is proper
  have : _root_.SheafOfModules.IsCoherent.{u} (𝓕.obj.obj (op 0)) := 𝓕.property.isCoherent 0
  have : (𝓕.obj.obj (op 0)).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := 𝓕.obj.obj (op 0))
  obtain ⟨W, hWeq, hWp⟩ :=
    hasProperSupport_pullback_of_isProper π f (𝓕.obj.obj (op 0)) h𝓕
  -- the algebraization over `V`, by the projective case on the compactification
  obtain ⟨G, hGprop, ⟨β⟩⟩ :=
    exists_hasProperSupport_iso_completionFunctor_opens_of_isProjectiveMorphism A I p hp V
      ⟨((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕).obj, hprop⟩ W hWeq.ge
      (isProperOver_of_eq hcomp hWp)
  refine ⟨(V : Scheme.{u}), π, inferInstance, inferInstance, ?_, G,
    hasProperSupport_of_eq hcomp.symm hGprop, ⟨?_⟩⟩
  · -- the restriction of an isomorphism to an open is an isomorphism, and `π ∣_ U` is the
    -- composite of that with `π₀ ∣_ U`. The isomorphism is spelled out rather than named `e`:
    -- instance search does not see through the abbreviation.
    have h1 : IsIso (j.isoOpensRange.inv ∣_ (π₀ ⁻¹ᵁ U)) := inferInstance
    rw [hπ, morphismRestrict_comp]
    exact IsIso.comp_isIso' h1 hiso
  · exact ObjectProperty.isoMk _ (β ≪≫ completionFunctorObjCongr hideal.symm G)

/-- **The `β` half of `hTransport`, unconditionally.** Let `A` be Noetherian and complete with
respect to `I` and let `f : X ⟶ Spec A` be separated, locally of finite type and quasi-compact.
Then every coherent `I 𝒪_X`-adic system whose first term has support proper over `A` admits a
proper modification `π : Y ⟶ X` which is an isomorphism over a **dense** open `U ⊆ X`, together
with a coherent `𝒪_Y`-module `G` with support proper over `A` and the source's isomorphism
`β : π^*(𝓕_n) ≅ G ^∧`.

This is verbatim the binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` with its join clause
`∀ e, K < K ⊔ 𝒦 ᵉ⁺¹` — which no Chow datum can supply, see the module docstring — replaced by the
density of `U` that
`Stacks.Algebraization.exists_isOpenImmersion_isProjectiveMorphism_denseChowModification`
delivers, and with the annihilation hypothesis on `K` dropped, the join clause being the only place
`K` occurs. Every geometric ingredient of `hTransport` is therefore discharged. -/
public theorem exists_hasProperSupport_iso_coherentAdicPullback_of_denseChowModification
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : IsNoetherian X := { }
    ∀ 𝓕 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓕.obj.obj (op 0)) →
        ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y) (U : X.Opens),
          IsIso (π ∣_ U) ∧ Dense (U : Set X) ∧
            ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
              HasProperSupport (π ≫ f) G.obj ∧
                Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                  (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  obtain ⟨Y₀, Y', π₀, j, p, U, hπ₀, -, hj, hp, hjp, hU, hiso⟩ :=
    exists_isOpenImmersion_isProjectiveMorphism_denseChowModification f
  intro 𝓕 h𝓕
  obtain ⟨Y, π, hπ, hY, hisoU, G, hG, hβ⟩ :=
    exists_hasProperSupport_iso_coherentAdicPullback_of_isOpenImmersion A I f π₀ j p hπ₀ hj hp
      hjp U hiso 𝓕 h𝓕
  exact ⟨Y, π, hπ, hY, U, hisoU, hU, G, hG, hβ⟩

/-! ### `hSupp` from Stacks 088B and the join clause alone -/

/-- **The properness statement behind `hSupp`, from [Stacks, Tag 088B] and the join clause
alone.** The binder `hTransport` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` asks for Chow data carrying
both the source's isomorphism `β` and the clause `∀ e, K < K ⊔ 𝒦 ᵉ⁺¹` on the ideal sheaf `𝒦`
cutting out the complement of the dense open. The first is
`Stacks.Algebraization.exists_hasProperSupport_iso_coherentAdicPullback_of_denseChowModification`,
proved; so `hTransport`, and with it the properness statement behind `hSupp`, follows from the
second, which is the binder `hJoin` here: once its degenerate disjunct is discharged, a statement
about the lattice of quasi-coherent ideal sheaves of `X`, with no sheaf of modules and no morphism
of schemes in it.

**`hJoin` is disjunctive, and the disjunction is not optional.** Asking the join clause at *every*
`K` is refutable at `K = ⊤`, where `⊤ < ⊤ ⊔ 𝒦 ᵉ⁺¹` reads `⊤ < ⊤`: the zero system is a coherent
adic system annihilated by `⊤` whose support is empty, hence proper over `A`. So `hJoin` offers
the same alternative the repaired binders `hChow` and `hTransport` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ProperSupportAlgebraization.lean`
offer — *either* the system's canonical annihilator already cuts out a closed subscheme proper
over `A`, which is literally the conclusion wanted of it at that stage, *or* the join clause holds
at every dense open. The degenerate disjunct is satisfiable, and at `K = ⊤` necessary:
`Stacks.Algebraization.exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal` is the
witness. This theorem is stated to isolate the clause, not to assert it: it records that nothing
geometric is left between [Stacks, Tag 088B] and `hSupp`. See the module docstring. -/
public theorem isProper_systemAnnihilatorIdeal_of_join
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u})
    (hJoin : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      letI : IsNoetherian X := { }
      ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∀ U : X.Opens, Dense (U : Set X) → ∀ e : ℕ,
              K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
                (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  refine isProper_systemAnnihilatorIdeal_of_transport A I f h088B (fun K 𝓕 hK h𝓕 => ?_)
  rcases hJoin K 𝓕 hK h𝓕 with hdone | hjoin
  · -- the degenerate disjunct is the left disjunct of `hTransport` verbatim
    exact Or.inl hdone
  obtain ⟨Y, π, hπ, hY, U, hisoU, hU, G, hG, hβ⟩ :=
    exists_hasProperSupport_iso_coherentAdicPullback_of_denseChowModification A I f 𝓕 h𝓕
  exact Or.inr ⟨Y, π, hπ, hY, U, hisoU, hjoin U hU, G, hG, hβ⟩

end Transport

end Stacks.Algebraization

end
