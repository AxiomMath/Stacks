module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AsymmetricFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.DepthCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.InternalHomCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafFromStructureSheaf
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.SupportSeparation
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowTensorSmul
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.SchemeQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomRegularSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal hom out of `𝒪_X / 𝒥`, and the theorem on formal functions for proper support

Let `X` be a scheme, `𝒥 ⊆ 𝒪_X` a quasi-coherent ideal sheaf and `ℋ` an `𝒪_X`-module annihilated
by `𝒥`. This file proves

  `SheafHom(𝒪_X / 𝒥, ℋ) ≅ ℋ`,

and draws from it the one consequence the asymmetric comparison of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AsymmetricFormalFunctions.lean`
was waiting for: **the theorem on formal functions in degree zero for a coherent sheaf whose
support is proper over the base** ([Stacks, Tag 087U], i.e. [Stacks, Tag 02OC] in degree zero,
with properness of the support in place of properness of the morphism). That discharges the
single hypothesis `hFF` of
`Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport`, which therefore
becomes unconditional over a complete Noetherian base.

## Why this closes the chain

The full faithfulness this library carries for a non-proper base,
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`, is **symmetric**: it
asks both modules to be annihilated by the ideal sheaf of one closed subscheme proper over the
base. `Stacks.Algebraization.bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit`
says that bijectivity of completion on `Hom(𝒢, ℱ)` is *equivalent* to the formal-functions
comparison being an isomorphism for `SheafHom(𝒢, ℱ)`. Reading that equivalence **backwards** on
the pair `(𝒪_X / 𝒥, ℋ)`, where `𝒥` is the ideal sheaf of the scheme-theoretic support of `ℋ`,
therefore turns the symmetric theorem into the formal-functions comparison for
`SheafHom(𝒪_X / 𝒥, ℋ)` — and that sheaf is `ℋ`, which is the isomorphism proved here. Both
members of the pair are annihilated by `𝒥`, so the symmetric theorem does apply: `𝒪_X / 𝒥` is
killed by `𝒥` by [Stacks, Tag 01Y9]'s sectionwise computation
(`Stacks.AlgebraicGeometry.HigherDirectImageCoherent.idealPowerMultiple_cokernel_eq_bot`), and
`ℋ` is killed by `𝒥` by the choice of `𝒥`
(`Stacks.Algebraization.exists_isProper_annihilatedByKer_of_hasProperSupport`). The structure
sheaf itself is **not** admissible there — its support is all of `X`, so properness of its
support is properness of `f` — which is exactly why the quotient has to be used.

## Main definitions

* `Stacks.Algebraization.sheafHomQuotientComparison` — the comparison
  `SheafHom(𝒪_X / 𝒥, ℋ) ⟶ ℋ`: precomposition with the quotient map, followed by the
  trivialisation `SheafHom(𝒪_X, ℋ) = ℋ` of [Stacks, Tag 03EM].

## Main results

* `Stacks.Algebraization.sheafHomQuotientIso` — **`SheafHom(𝒪_X / 𝒥, ℋ) ≅ ℋ` for
  `𝒥 ℋ = 0`.**
* `Stacks.Algebraization.isIso_globalSectionsToLimit_of_hasProperSupport` — **the theorem on
  formal functions in degree zero for a coherent sheaf with support proper over the base**:
  `Γ(X, 𝒩) ≅ limₙ Γ(X, 𝒩 / 𝓘ⁿ 𝒩)`, for `A` Noetherian and `I`-adically complete,
  `f : X ⟶ Spec A` locally of finite type and `𝓘 = I · 𝒪_X`. This is the residual of
  `AsymmetricFormalFunctions.lean`.
* `Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport_complete` — **the
  asymmetric comparison, unconditionally**: for coherent `ℱ` with no condition at all and
  coherent `𝒢` with support proper over `A`, completion is bijective on `Hom(ℱ, 𝒢)`.
* `Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete` — its
  specialisation at `ℱ = 𝒪_X`, the statement the unit of
  `AlgebraicGeometry.ModuleAlgebraData` needs moved.

## Implementation notes

The isomorphism is proved through the *characterised* internal hom of [Stacks, Tag 01CO], the
structure `SheafHom`, rather than through the monoidal-closed internal hom: left exactness in the
first variable is available there as `sheafHom_leftExact_fst`, acting on the canonical
precomposition maps `SheafHom.precomp`, whereas the monoidal-closed presentation
`Stacks.SheafOfModules.InternalHom.ihomCokernelIsoKernel` is identified with the internal hom of
[Stacks, Tag 03EM] at objects only, and the identification of the two *first-variable
functorialities* is not in this library. Concretely: applying `SheafHom(-, ℋ)` to
`𝒥 𝒪_X ⟶ 𝒪_X ⟶ 𝒪_X / 𝒥 ⟶ 0` gives

  `0 ⟶ SheafHom(𝒪_X / 𝒥, ℋ) ⟶ SheafHom(𝒪_X, ℋ) ⟶ SheafHom(𝒥 𝒪_X, ℋ)`,

whose first map is the comparison; it is a monomorphism by left exactness and an epimorphism
because the second map is zero, and a monomorphism which is an epimorphism in an abelian category
is an isomorphism. That the second map vanishes is where `𝒥 ℋ = 0` is used, and it is the only
computation on sections in the file: the morphism `𝒪_X|_U ⟶ ℋ|_U` named by a section `b` of `ℋ`
sends a section `a` of the structure sheaf to `a • b`
(`Stacks.SheafOfModules.unitHomEquiv_symm_val_app_apply`), and for `a` a section of `𝒥 𝒪_X` that
vanishes. `SheafHom(𝒥 𝒪_X, ℋ)` itself is **not** zero — for `X = 𝔸¹`, `𝒥 = (t)` and `ℋ` the
residue field at the origin it is `ℋ` again — so the vanishing is of the map, not of its target.

No new name is introduced for `𝒪_X / 𝒥`: it is `Stacks.Algebraization.idealPowerQuotient J 1 𝒪_X`,
the quotient the completion functor's terms are already built from, and its coherence is the
existing instance `Stacks.Algebraization.isCoherent_idealPowerQuotient`. Likewise `𝒥 𝒪_X` is
`Stacks.Algebraization.idealPowerMultiple J 1 𝒪_X`, whose sections over an affine open are
`𝒥(U) Γ(X, U)` (`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen`), which is
how the vanishing above is reduced to one scalar multiplication.

The target of the comparison is `ℋ` on the nose rather than up to a transport:
`Stacks.SheafOfModules.unitSheafHom` is the internal hom `SheafHom(𝒪_X, ℋ)` *realised as* `ℋ`,
in the sense of the characterising structure, so `SheafHom.precomp` of the quotient map lands in
`ℋ` with no comparison inserted. For the same reason `Stacks.SheafOfModules.internalHomSheafHom`
is used for the source: its underlying module is `rfl`-equal to
`(Stacks.Algebraization.sheafHomFunctor X _).obj ℋ`, the spelling
`Stacks.Algebraization.internalHomCoherent` uses.

`Stacks.Algebraization.isIso_globalSectionsToLimit_of_iso` (in
`CompletionFullyFaithful/DepthCriterion.lean`) is the transport the backwards reading needs.

## References

* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 01CO](https://stacks.math.columbia.edu/tag/01CO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry ZeroObject

universe u

namespace Stacks.Algebraization

open Stacks.SheafOfModules.InternalHom
open Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

section Quotient

variable {X : Scheme.{u}} (J : X.IdealSheafData)

/-- A section of `𝒥 𝒪_X` annihilates every section of a module annihilated by `𝒥`. -/
public theorem smul_eq_zero_of_mem_idealPowerMultiple_unit {H : X.Modules} [H.IsQuasicoherent]
    (hH : idealPowerMultiple J 1 H = ⊥) {W : X.Opens} {x : Γ(X, W)}
    (hx : x ∈ (idealPowerMultiple J 1
      (_root_.SheafOfModules.unit X.ringCatSheaf)).obj (op W)) (m : Γ(H, W)) :
    x • m = 0 := by
  refine section_eq_zero_of_affine H _ fun V i => ?_
  refine Eq.trans (Scheme.Modules.map_smul H i x m) ?_
  refine smul_eq_zero_of_idealPowerMultiple_eq_bot J 1 H hH V ?_ _
  have h1 := (idealPowerMultiple J 1
    (_root_.SheafOfModules.unit X.ringCatSheaf)).toSubmodule.map_mem i.op hx
  have h2 : (idealPowerMultiple J 1
        (_root_.SheafOfModules.unit X.ringCatSheaf)).obj (op V.1) =
      J.ideal V ^ 1 • (⊤ : Submodule Γ(X, V.1) Γ(X, V.1)) :=
    Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen J 1
      (_root_.SheafOfModules.unit X.ringCatSheaf) V
  rw [h2] at h1
  exact Submodule.smul_le.2 (fun r hr y _ => (J.ideal V ^ 1).mul_mem_right y hr) h1

/-- Precomposition with the inclusion `𝒥 𝒪_X ⟶ 𝒪_X` is zero on `SheafHom(𝒪_X, H) = H` when `𝒥`
annihilates `H`: the morphism `𝒥 𝒪_X|_V ⟶ H|_V` attached to a section `b` of `H` over `V` sends a
section `a` of `𝒥` to `a • b`, which vanishes. -/
public theorem isPrecomp_zero_idealPowerMultiple_unit {H : X.Modules} [H.IsQuasicoherent]
    (hH : idealPowerMultiple J 1 H = ⊥) :
    SheafHom.IsPrecomp X.sheaf
      (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι
      (Stacks.SheafOfModules.unitSheafHom X.sheaf H)
      (Stacks.SheafOfModules.internalHomSheafHom X.sheaf
        (idealPowerMultiple J 1
          (_root_.SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules H) 0 := by
  intro V b
  have key : (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι.over V ≫
      (Stacks.SheafOfModules.unitSheafHom X.sheaf H).sectionsEquiv V b = 0 := by
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext y
    exact smul_eq_zero_of_mem_idealPowerMultiple_unit J hH y.2 (H.val.map W.unop.hom.op b)
  rw [key]
  exact map_zero _

/-- The presentation `𝒥 𝒪_X ⟶ 𝒪_X ⟶ 𝒪_X / 𝒥 ⟶ 0` is exact: the middle node because the quotient
map is the cokernel of the inclusion, the last because a cokernel projection is an
epimorphism. -/
public theorem exact_idealPowerQuotient_unit :
    (ComposableArrows.mk₃
      (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι
      (cokernel.π (idealPowerMultiple J 1
        (_root_.SheafOfModules.unit X.ringCatSheaf)).ι)
      (0 : idealPowerQuotient J 1
        (_root_.SheafOfModules.unit X.ringCatSheaf) ⟶ 0)).Exact := by
  refine ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ ?_ ?_)
    (ComposableArrows.exact₂_mk _ ?_ ?_)
  · exact cokernel.condition _
  · exact ShortComplex.exact_cokernel
      (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι
  · exact comp_zero
  · exact (ShortComplex.exact_iff_epi _ rfl).2 (epi_of_isColimit_cofork (colimit.isColimit _))

/-- **The comparison `SheafHom(𝒪_X / 𝒥, H) ⟶ H`**: precomposition with the quotient map
`𝒪_X ⟶ 𝒪_X / 𝒥`, read through the trivialisation `SheafHom(𝒪_X, H) = H` of [Stacks, Tag 03EM].
Its target is `H` on the nose because `Stacks.SheafOfModules.unitSheafHom` realises the internal
hom out of the structure sheaf *as* `H`. -/
public abbrev sheafHomQuotientComparison (H : X.Modules) :
    (sheafHomFunctor X
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf))).obj H ⟶ H :=
  SheafHom.precomp
    (cokernel.π (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι)
    (Stacks.SheafOfModules.internalHomSheafHom X.sheaf
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)) H)
    (Stacks.SheafOfModules.unitSheafHom X.sheaf H)

/-- **The comparison is an isomorphism when `𝒥` annihilates `H`.** Applying `SheafHom(-, H)` to
the presentation `𝒥 𝒪_X ⟶ 𝒪_X ⟶ 𝒪_X / 𝒥 ⟶ 0` gives a left-exact sequence
`0 ⟶ SheafHom(𝒪_X / 𝒥, H) ⟶ H ⟶ SheafHom(𝒥 𝒪_X, H)` ([Stacks, Tag 01CO]), whose first map is the
comparison; it is therefore a monomorphism, and it is an epimorphism because the second map is
zero (`Stacks.Algebraization.isPrecomp_zero_idealPowerMultiple_unit`). A monomorphism which is an
epimorphism in an abelian category is an isomorphism. -/
public theorem isIso_sheafHomQuotientComparison {H : X.Modules} [H.IsQuasicoherent]
    (hH : idealPowerMultiple J 1 H = ⊥) :
    IsIso (sheafHomQuotientComparison J H) := by
  have hout := sheafHom_leftExact_fst X.sheaf
    (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules
    (_root_.SheafOfModules.unit X.ringCatSheaf)
    (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)) H
    (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι
    (cokernel.π (idealPowerMultiple J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)).ι)
    (exact_idealPowerQuotient_unit J)
    (Stacks.SheafOfModules.internalHomSheafHom X.sheaf
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)) H)
    (Stacks.SheafOfModules.unitSheafHom X.sheaf H)
    (Stacks.SheafOfModules.internalHomSheafHom X.sheaf
      (idealPowerMultiple J 1
        (_root_.SheafOfModules.unit X.ringCatSheaf)).toSheafOfModules H)
    (SheafHom.precomp (cokernel.π (idealPowerMultiple J 1
      (_root_.SheafOfModules.unit X.ringCatSheaf)).ι) _ _) 0
    (SheafHom.isPrecomp_precomp _ _ _) (isPrecomp_zero_idealPowerMultiple_unit J hH)
  have hmono : Mono (sheafHomQuotientComparison J H) :=
    (ShortComplex.exact_iff_mono _ rfl).1 (hout.exact 0)
  have hepi : Epi (sheafHomQuotientComparison J H) :=
    (ShortComplex.exact_iff_epi _ rfl).1 (hout.exact 1)
  exact isIso_of_mono_of_epi _

/-- **The internal hom out of `𝒪_X / 𝒥` is the identity on modules annihilated by `𝒥`:**
`SheafHom(𝒪_X / 𝒥, H) ≅ H` as soon as `𝒥 H = 0`.

A morphism `𝒪_X / 𝒥|_V ⟶ H|_V` is a section of `H` over `V` killed by `𝒥`, and every section of
`H` is killed by `𝒥`, so evaluation at the unit section is bijective. The isomorphism is the
comparison `Stacks.Algebraization.sheafHomQuotientComparison`, i.e. precomposition with the
quotient map, and not an unspecified comparison of two objects. -/
public def sheafHomQuotientIso {H : X.Modules} [H.IsQuasicoherent]
    (hH : idealPowerMultiple J 1 H = ⊥) :
    (sheafHomFunctor X
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf))).obj H ≅ H :=
  @asIso _ _ _ _ (sheafHomQuotientComparison J H) (isIso_sheafHomQuotientComparison J hH)

end Quotient

/-! ### The theorem on formal functions in degree zero, for proper support -/

section Residual

/-- **The theorem on formal functions in degree zero for a coherent sheaf with support proper
over the base** — [Stacks, Tag 087U], i.e. [Stacks, Tag 02OC] in degree zero, with properness of
the *support* in place of properness of the morphism. Let `A` be a Noetherian ring complete with
respect to an ideal `I`, let `f : X ⟶ Spec A` be locally of finite type and put `𝓘 = I · 𝒪_X`.
Then for a coherent `𝒩` whose support is proper over `A`,

  `Γ(X, 𝒩) ≅ limₙ Γ(X, 𝒩 / 𝓘ⁿ 𝒩)`.

This discharges the one hypothesis of
`Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport`.

The proof reads the equivalence
`Stacks.Algebraization.bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit`
backwards on the pair `(𝒪_X / 𝒥, 𝒩)`, where `𝒥` is the ideal sheaf of a closed subscheme proper
over `A` annihilating `𝒩` — the scheme-theoretic support of `𝒩`, by
`Stacks.Algebraization.exists_isProper_annihilatedByKer_of_hasProperSupport`. Both members of
that pair are annihilated by `𝒥`, so completion is bijective on their morphisms by the
*symmetric* full faithfulness
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`, which is
unconditional; the equivalence turns that into the comparison for `SheafHom(𝒪_X / 𝒥, 𝒩)`, and
that sheaf is `𝒩` by `Stacks.Algebraization.sheafHomQuotientIso`. -/
@[ega "III 4.1.10" "special case", ega "III 4.1.5" "partial", ega "III 5.1.2" "Degree i = 0"]
public theorem isIso_globalSectionsToLimit_of_hasProperSupport (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hH : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      HasProperSupport f H.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    IsIso (globalSectionsToLimit (baseIdealSheaf A I f) H) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : H.obj.IsCoherent := H.property
  have : H.obj.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent H.obj
  obtain ⟨J, hJ, hHann⟩ := exists_isProper_annihilatedByKer_of_hasProperSupport f H.obj hH
  have hHbot : idealPowerMultiple J 1 H.obj = ⊥ :=
    (annihilatedByKer_subschemeι_iff_idealPowerMultiple_one J H.obj).1 hHann
  have hunit : (_root_.SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hQcoh : (idealPowerQuotient J 1
      (_root_.SheafOfModules.unit X.ringCatSheaf)).IsCoherent :=
    isCoherent_idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)
  have : (idealPowerQuotient J 1
      (_root_.SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf))
  let Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
    ⟨idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf), hQcoh⟩
  have hQann : Stacks.ClosedImmersion.AnnihilatedByKer J.subschemeι
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf)) :=
    (annihilatedByKer_subschemeι_iff_idealPowerMultiple_one J
      (idealPowerQuotient J 1 (_root_.SheafOfModules.unit X.ringCatSheaf))).2
      (Stacks.AlgebraicGeometry.HigherDirectImageCoherent.idealPowerMultiple_cokernel_eq_bot
        J 1 (_root_.SheafOfModules.unit X.ringCatSheaf))
  -- the symmetric full faithfulness at the pair `(𝒪_X / 𝒥, 𝒩)`
  have hbij := bijective_completionFunctor_map_of_annihilatedByKer A I f J hJ Q H hQann hHann
  have hhom : Function.Bijective
      (fun v : (completionFunctor X (baseIdealSheaf A I f)).obj Q ⟶
        (completionFunctor X (baseIdealSheaf A I f)).obj H => v.hom) :=
    ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  have hbij' : Function.Bijective
      ((completionFunctor X (baseIdealSheaf A I f)).map : (Q ⟶ H) → _) :=
    (hhom.of_comp_iff' _).1 (show Function.Bijective ((fun v => v.hom) ∘
      ((completionFunctor X (baseIdealSheaf A I f)).map : (Q ⟶ H) → _)) from hbij)
  -- read the equivalence backwards, and identify `SheafHom(𝒪_X / 𝒥, 𝒩)` with `𝒩`
  exact isIso_globalSectionsToLimit_of_iso _ (ObjectProperty.isoMk _
    (sheafHomQuotientIso J hHbot))
    ((bijective_completionFunctor_map_iff_isIso_globalSectionsToLimit
      (baseIdealSheaf A I f) Q H).1 hbij')

/-! ### The asymmetric comparison, unconditionally -/

/-- **The asymmetric formal-functions comparison, with no residual hypothesis.** Let `A` be a
Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be locally of finite
type and put `𝓘 = I · 𝒪_X`. For a coherent `ℱ` — with **no condition whatever** — and a coherent
`𝒢` whose support is proper over `A`, completion along `𝓘` is bijective on morphisms:

  `Hom(ℱ, 𝒢) ≅ Hom_{Coh(X, 𝓘)}(ℱ^∧, 𝒢^∧) = limₙ Hom(ℱₙ, 𝒢ₙ)`.

This is `Stacks.Algebraization.bijective_completionFunctor_map_of_hasProperSupport_adic` with its
hypothesis `hFF` discharged by
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_hasProperSupport`. Neither properness nor
separatedness of `f` is assumed; what the proof uses is completeness of `A`, through the
symmetric full faithfulness of
`Stacks.Algebraization.bijective_completionFunctor_map_of_annihilatedByKer`. -/
@[ega "III 4.5.3" "special case", ega "III 5.1.3" "special case"]
public theorem bijective_completionFunctor_map_of_hasProperSupport_complete (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      HasProperSupport f G.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Function.Bijective
      ((completionFunctor X (baseIdealSheaf A I f)).map :
        (F ⟶ G) → ((completionFunctor X (baseIdealSheaf A I f)).obj F ⟶
          (completionFunctor X (baseIdealSheaf A I f)).obj G)) :=
  bijective_completionFunctor_map_of_hasProperSupport_adic A I f
    (isIso_globalSectionsToLimit_of_hasProperSupport A I f) F G hG

/-- **The specialisation at `ℱ = 𝒪_X`, with no residual hypothesis.** For a coherent `𝒩` whose
support is proper over the complete Noetherian base,

  `Hom(𝒪_X, 𝒩) ≅ Hom_{Coh(X, 𝓘)}(𝒪_X^∧, 𝒩^∧)`,

which under `Stacks.Algebraization.globalSectionOfHom` is the theorem on formal functions in
degree zero. This is the statement the unit of `AlgebraicGeometry.ModuleAlgebraData` needs
moved, and the one the symmetric full faithfulness cannot supply, since
`Stacks.Algebraization.HasProperSupport f (SheafOfModules.unit X.ringCatSheaf)` is properness of
`f`. -/
@[ega "III 4.1.10" "special case",
  ega "III 4.5.3" "special case",
  ega "III 5.1.2" "Degree i = 0 of 5.1.2",
  ega "III 5.1.3" "special case"]
public theorem bijective_completionFunctor_map_unit_of_hasProperSupport_complete (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      HasProperSupport f G.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    Function.Bijective
      ((completionFunctor X (baseIdealSheaf A I f)).map :
        ((⟨_root_.SheafOfModules.unit X.ringCatSheaf,
              Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X⟩ :
            AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶ G) →
          ((completionFunctor X (baseIdealSheaf A I f)).obj
              ⟨_root_.SheafOfModules.unit X.ringCatSheaf,
                Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X⟩ ⟶
            (completionFunctor X (baseIdealSheaf A I f)).obj G)) :=
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  bijective_completionFunctor_map_unit_of_hasProperSupport f (baseIdealSheaf A I f)
    (isIso_globalSectionsToLimit_of_hasProperSupport A I f) G hG

end Residual

end Stacks.Algebraization

end
