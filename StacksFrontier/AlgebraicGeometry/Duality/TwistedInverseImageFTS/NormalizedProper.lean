module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOverField
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistence
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpens
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedOnOpensOfShriek

/-!
# The normalized dualizing complex upstairs is the twisted inverse image of the one downstairs

Let `S` be Noetherian with a dualizing complex `ω_S^•`, and `f : X ⟶ Y` a morphism of schemes of
finite type over `S`, separated. For the upper shriek formalism of a choice of compactifications,
let `ω_X^•` and `ω_Y^•` be the dualizing complexes normalized relative to `ω_S^•`. By
[Stacks, Tag 0AUB], `ω_X^•` is normalized relative to `ω_Y^•`; so is `f^! ω_Y^•`, `X` being
separated over `Y`; so the two are uniquely isomorphic by [Stacks, Tag 0AU7] over the base `Y`.
When `f` is proper, `f^!` is the right adjoint `a` of `Rf_*`, which gives
`a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]).

Over a field `k` with `ω_S^• = k[0]`, the normalized complex gives the dualizing module
`ω_X = H^{-dim(X)}(ω_X^•)` of [Stacks, Tag 0AWJ], and for `X` separated over `S` the normalized
complex is `(X → S)^! ω_S^•` ([Stacks, Tag 0AUE], closing remark).

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.twistedInverseImageObjIso`: **[Stacks, Tag 0AUD]** for the
  upper shriek functors of compactifications.
* `Stacks.Duality.dualizingModuleOfCompactifications`: the dualizing module of
  [Stacks, Tag 0AWJ].
* `Stacks.Duality.NormalizedOnOpens.traceOfCompactifications`,
  `Stacks.Duality.NormalizedOnOpens.homEquivOfCompactifications`: the trace map
  `Rf_* ω_X^• ⟶ ω_Y^•` of a proper morphism and `Hom_X(L, ω_X^•) = Hom_Y(Rf_* L, ω_Y^•)`
  ([Stacks, Tag 0B6X]).

## Main results

* `Stacks.Duality.NormalizedOnOpens.existsUnique_iso_upperShriek_ofCompactifications`: the
  unique isomorphism `ω_X^• ≅ f^! ω_Y^•` compatible with the normalizations relative to `ω_Y^•`.
* `Stacks.Duality.NormalizedOnOpens.existsUnique_iso_shriek_ofCompactifications`: for `X`
  separated over `S`, `ω_X^• ≅ (X → S)^! ω_S^•` canonically.
* `Stacks.Duality.existsUnique_iso_shriek_of_field`: the separated case of
  [Stacks, Tag 0AWJ].

## References

* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
* [Stacks Project, Tag 0AU7](https://stacks.math.columbia.edu/tag/0AU7)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0AWJ](https://stacks.math.columbia.edu/tag/0AWJ)
* [Stacks Project, Tag 0B6X](https://stacks.math.columbia.edu/tag/0B6X)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u w w'

namespace Stacks.Duality

namespace SeparatedCovering

/-- The covering of `X` by the intersections of the members of a covering of `X` with the preimages
of the members of a covering of `Y`, each contained in the preimage of a member of the latter. -/
def interPreimage {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) {ι : Type w} {J : Type w'}
    (𝒰 : SeparatedCovering p ι) (𝒱 : SeparatedCovering q J) :
    SeparatedCovering p (J × ι) where
  U k := f ⁻¹ᵁ 𝒱.U k.1 ⊓ 𝒰.U k.2
  finite := haveI := 𝒰.finite; haveI := 𝒱.finite; inferInstance
  covers := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((congrArg (fun U : X.Opens => x ∈ U) 𝒰.covers).mpr
      trivial)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((congrArg (fun V : Y.Opens => f x ∈ V) 𝒱.covers).mpr
      trivial)
    exact Opens.mem_iSup.mpr ⟨(j, i), hj, hi⟩
  shriekable k := hp.isShriekable_le inf_le_right (𝒰.shriekable k.2)

end SeparatedCovering

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **The normalized complex upstairs is `f^!` of the one downstairs**, for `f` separated. Let
`ω_X^•` and `ω_Y^•` be dualizing complexes normalized relative to `ω_S^•` and let `𝒰`, `𝒱` be
finite coverings of `X` and `Y` by opens separated over `S`, each `U_k` mapping into `V_{idx k}`.
There is exactly one isomorphism `ω_X^• ≅ f^! ω_Y^•` carrying the normalizations of `ω_X^•`
relative to `ω_Y^•` ([Stacks, Tag 0AUB]) to the canonical ones of `f^! ω_Y^•`. -/
theorem existsUnique_iso_upperShriek_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hf : IsShriekable f)
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    {ι : Type w} {J : Type w'} (𝒰 : SeparatedCovering p ι) (𝒱 : SeparatedCovering q J)
    (idx : ι → J) (hle : ∀ k, 𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U (idx k)) :
    ∃! e : 𝒦X.complex ≅ (UpperShriek.shriekOf c f hf).obj 𝒦Y.complex, ∀ k,
      ((UpperShriek.ofCompactifications c).shriek (𝒰.U k).ι
          ((hp.of_comp' hq hpe).isShriekable_ι _)).mapIso e ≪≫
        (normalizedUpperShriek (UpperShriek.ofCompactifications c) (hp.of_comp' hq hpe) hf
          𝒦Y.complex (𝒰.overMid 𝒱 hp hq hpe idx hle)).localIso k =
      ((𝒦X.toNormalized 𝒰).overMid hpe hp hq idx hle (𝒦Y.toNormalized 𝒱)).localIso k :=
  Normalized.existsUnique_iso_ofCompactifications c
    (𝒦Y.isDualizingComplex_ofCompactifications c hωS)
    ((𝒦X.toNormalized 𝒰).overMid hpe hp hq idx hle (𝒦Y.toNormalized 𝒱))
    (normalizedUpperShriek (UpperShriek.ofCompactifications c) (hp.of_comp' hq hpe) hf
      𝒦Y.complex (𝒰.overMid 𝒱 hp hq hpe idx hle))

/-- **The canonical isomorphism `ω_X^• ≅ f^! ω_Y^•`** for `f` separated, between the dualizing
complexes normalized relative to `ω_S^•`: the isomorphism of
`existsUnique_iso_upperShriek_ofCompactifications` for the coverings of `X` and `Y` by finitely
many affine opens and their intersections. -/
def upperShriekObjIso (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (hf : IsShriekable f) (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    𝒦X.complex ≅ (UpperShriek.shriekOf c f hf).obj 𝒦Y.complex :=
  (existsUnique_iso_upperShriek_ofCompactifications c hpe hωS hf 𝒦X 𝒦Y
    ((SeparatedCovering.exists_nonempty hp).choose_spec.some.interPreimage hp
      (SeparatedCovering.exists_nonempty hq).choose_spec.some)
    (SeparatedCovering.exists_nonempty hq).choose_spec.some Prod.fst
    (fun _ => inf_le_left)).exists.choose

/-- A proper morphism of schemes of finite type over a Noetherian base is shriekable. -/
theorem isShriekable_of_isProper (hp : IsFiniteTypeOverNoetherian p)
    (hq : IsFiniteTypeOverNoetherian q) [IsProper f] : IsShriekable f :=
  { target_noetherian := hq.source_noetherian
    separatedFiniteType := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ }

/-- **[Stacks, Tag 0AUD]** for the upper shriek functors of compactifications. In Situation 0AU4,
let `f : X ⟶ Y` be a proper morphism of schemes of finite type over `S`, let `ω_X^•` and `ω_Y^•`
be the dualizing complexes normalized relative to `ω_S^•`, and let `a` be the right adjoint of
`Rf_*` ([Stacks, Tag 0A9E]). Then there is a canonical isomorphism `a(ω_Y^•) ≅ ω_X^•`: `a` is
`f^!`, and `ω_X^• ≅ f^! ω_Y^•` is `upperShriekObjIso`. -/
def twistedInverseImageObjIso
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        𝒦Y.complex.obj ≅ 𝒦X.complex.obj :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  ((UpperShriek.shriekOfIsoOfIsProper c f (isShriekable_of_isProper hp hq)).app
      𝒦Y.complex).symm ≪≫
    (ObjectProperty.ι _).mapIso
      (upperShriekObjIso c hpe hωS (isShriekable_of_isProper hp hq) 𝒦X 𝒦Y).symm

/-- **[Stacks, Tag 0B6X], the trace map**, for the upper shriek functors of compactifications:
for a proper `f : X ⟶ Y` of schemes of finite type over `S` and the dualizing complexes
normalized relative to `ω_S^•`, the canonical arrow `Tr_f : Rf_* ω_X^• ⟶ ω_Y^•`, the trace map of
[Stacks, Section 0AWG] read through `a(ω_Y^•) ≅ ω_X^•` ([Stacks, Tag 0AUD]). -/
def traceOfCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        𝒦X.complex.obj ⟶ 𝒦Y.complex.obj :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  (quasiCoherentDerivedPushforward f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
      (twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y).inv ≫
    relativeDualizingComplexTrace f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      𝒦Y.complex.obj

/-- **[Stacks, Tag 0B6X], the duality isomorphism**, for the upper shriek functors of
compactifications: `Hom_X(L, ω_X^•) = Hom_Y(Rf_* L, ω_Y^•)` for `L` in `D_QCoh(𝒪_X)`, sending
`u` to `Tr_f ∘ Rf_* u` (`homEquivOfCompactifications_apply`). -/
def homEquivOfCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (L : quasiCoherentDerivedCategory X) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (L ⟶ 𝒦X.complex.obj) ≃
      ((quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj L ⟶ 𝒦Y.complex.obj) :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  ((Iso.refl L).homCongr (twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y).symm).trans
    (relativeDualizingComplexHomEquiv f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      𝒦Y.complex.obj L)

/-- The duality isomorphism `homEquivOfCompactifications` sends `u : L ⟶ ω_X^•` to the
composite of `Rf_* u` with the trace map `traceOfCompactifications`. -/
theorem homEquivOfCompactifications_apply
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS)
    (𝒦Y : NormalizedOnOpens (UpperShriek.ofCompactifications c) hq ωS)
    (L : quasiCoherentDerivedCategory X) (u : L ⟶ 𝒦X.complex.obj) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    homEquivOfCompactifications c hpe hωS 𝒦X 𝒦Y L u =
      (quasiCoherentDerivedPushforward f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map u ≫
        traceOfCompactifications c hpe hωS 𝒦X 𝒦Y := by
  have := hq.source_noetherian
  have := hp.source_noetherian
  show relativeDualizingComplexHomEquiv f _ 𝒦Y.complex.obj L
    (𝟙 L ≫ u ≫ (twistedInverseImageObjIso c hpe hωS 𝒦X 𝒦Y).inv) = _
  rw [relativeDualizingComplexHomEquiv_apply, Category.id_comp]
  exact (congrArg (· ≫ _) ((quasiCoherentDerivedPushforward f _).map_comp _ _)).trans
    (Category.assoc _ _ _)

end NormalizedOnOpens

namespace NormalizedOnOpens

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0AUE], the closing remark on the separated case**, for the upper shriek
functors of compactifications: if `X` is separated over `S`, the dualizing complex `ω_X^•`
normalized relative to `ω_S^•` is canonically isomorphic to `(X → S)^! ω_S^•`, by the unique
isomorphism carrying `α_W` to the canonical `((X → S)^! ω_S^•)|_W ≅ (W → S)^! ω_S^•` for every
open `W` separated over `S`. -/
theorem existsUnique_iso_shriek_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) (hps : IsShriekable p)
    (𝒦 : NormalizedOnOpens (UpperShriek.ofCompactifications c) hp ωS) :
    ∃! e : 𝒦.complex ≅ (UpperShriek.shriekOf c p hps).obj ωS,
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        ((UpperShriek.ofCompactifications c).shriek W.ι (hp.isShriekable_ι W)).mapIso e ≪≫
          upperShriekLocalIso (UpperShriek.ofCompactifications c) hp hps ωS hW =
        𝒦.localIso W hW :=
  existsUnique_iso_ofCompactifications c hωS 𝒦
    (ofShriek (UpperShriek.ofCompactifications c) hp hps ωS)

end NormalizedOnOpens

/-! ### Schemes of finite type over a field -/

section Field

variable {k : Type u} [Field k]

/-- `k[0]` is a dualizing complex on `Spec(k)`. -/
theorem isDualizingComplex_derivedStructureSheafPlus_of_field (k : Type u) [Field k] :
    haveI := isNoetherian_spec_of_field k
    IsDualizingComplex (derivedStructureSheafPlus (Spec (.of k))).obj.obj := by
  have := isNoetherian_spec_of_field k
  exact isDualizingComplex_of_iso ((ObjectProperty.ι _).mapIso
    ((twistedInverseImageIdIso (Spec (.of k))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 _))).app _))
    (isDualizingComplex_relativeDualizingComplex_of_isProper (𝟙 (Spec (.of k))))

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]

/-- **[Stacks, Tag 0AWJ], the definition**, for the upper shriek functors of compactifications:
the dualizing module `ω_X = H^{-dim(X)}(ω_X^•)` of a scheme of finite type over a field `k`,
`ω_X^•` being the dualizing complex normalized relative to `k[0]`. -/
def dualizingModuleOfCompactifications : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules
    (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj
    (normalizedDualizingComplexOfCompactifications c (isFiniteTypeOverNoetherian_of_field p)
      (derivedStructureSheafPlus (Spec (.of k)))
      (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex.obj.obj

/-- **[Stacks, Tag 0AWJ], the separated case**, for the upper shriek functors of
compactifications: if `X` is separated over `k`, the dualizing complex normalized relative to
`k[0]` is canonically `f^! 𝒪_{Spec(k)}`, `f : X ⟶ Spec(k)` the structure morphism. -/
theorem existsUnique_iso_shriek_of_field [IsSeparated p] :
    ∃! e : (normalizedDualizingComplexOfCompactifications c
        (isFiniteTypeOverNoetherian_of_field p) (derivedStructureSheafPlus (Spec (.of k)))
        (isDualizingComplex_derivedStructureSheafPlus_of_field k)).complex ≅
      (UpperShriek.shriekOf c p (isShriekable_of_field p)).obj
        (derivedStructureSheafPlus (Spec (.of k))),
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        ((UpperShriek.ofCompactifications c).shriek W.ι
            ((isFiniteTypeOverNoetherian_of_field p).isShriekable_ι W)).mapIso e ≪≫
          upperShriekLocalIso (UpperShriek.ofCompactifications c)
            (isFiniteTypeOverNoetherian_of_field p) (isShriekable_of_field p)
            (derivedStructureSheafPlus (Spec (.of k))) hW =
        (normalizedDualizingComplexOfCompactifications c (isFiniteTypeOverNoetherian_of_field p)
          (derivedStructureSheafPlus (Spec (.of k)))
          (isDualizingComplex_derivedStructureSheafPlus_of_field k)).localIso W hW :=
  NormalizedOnOpens.existsUnique_iso_shriek_ofCompactifications c
    (isDualizingComplex_derivedStructureSheafPlus_of_field k) (isShriekable_of_field p) _

end Field

end Stacks.Duality

end
