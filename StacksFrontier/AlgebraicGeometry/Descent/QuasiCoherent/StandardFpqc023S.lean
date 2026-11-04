module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcEffective023T
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.AffineSingletonEffective
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaSummands
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SingletonFullness
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StandardAffineSeparated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fpqc descent of quasi-coherent sheaves along a standard fpqc covering of an affine scheme

Stacks 023S says: let `S` be an **affine** scheme and let `{f i : X i ⟶ S}` be a standard fpqc
covering of `S` (Stacks 022F — a finite family of flat morphisms from affine schemes whose images
cover `S`).  Then every descent datum on quasi-coherent sheaves for the family is effective, and
the functor from quasi-coherent `O_S`-modules to descent data for the family is fully faithful.

This file assembles **both** halves at the generality the source states them: the two tagged
declarations below are the covering set of Stacks 023S.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc_of_isAffine`: **the
  effectivity half of Stacks 023S**, for a standard fpqc covering of an arbitrary affine scheme.
* `…QuasicoherentDescentData.nonempty_fullyFaithful_canonicalDescentFunctor_standardFpqc`: **the
  full faithfulness half of Stacks 023S**, in the same generality.
* `AlgebraicGeometry.QuasicoherentDescentData.presieve₀_mem_fpqcPrecoverage_standardFpqc`: **a
  standard fpqc covering is an fpqc covering family**, which is what converts the elementary form
  of Stacks 022F into the hypothesis that the general results consume.
* `Stacks.Descent.faithful_qcohToDescentData_standardFpqc`: the faithfulness half in the
  *pseudofunctor* vocabulary, which the general full faithfulness does not give directly.
* `Stacks.Descent.isEffective_of_essSurj_qcohToDescentData`: the direction of the dictionary
  between the two vocabularies in which this repository states quasi-coherent descent that reads
  essential surjectivity of the pseudofunctor as effectivity; see the implementation notes.
* `Stacks.Descent.affineSingletonEffective`: **`Stacks.Descent.AffineSingletonEffective` is a
  theorem**, which discharges the effectivity hypothesis of
  `Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine_of_affineSingletonEffective`.
* `Stacks.Descent.faithful_toDescentData_of_sieve_eq` and
  `Stacks.Descent.sieve_ofArrows_comp_isIso`: the two transport tools the faithfulness half
  needs, namely that faithfulness of the canonical descent functor depends only on the generated
  sieve, and that replacing the members of a family by isomorphic objects does not change that
  sieve.

## Implementation notes

**Two vocabularies.**  Quasi-coherent descent data appear here in two shapes.  The first is
`AlgebraicGeometry.QuasicoherentDescentData` — the full subcategory of the descent data of
`AlgebraicGeometry.modulePullbackPseudofunctor` on the objects whose components are
quasi-coherent — with its canonical functor `AlgebraicGeometry.canonicalDescentFunctor` and its
effectivity predicate `AlgebraicGeometry.QuasicoherentDescentData.IsEffective`.  The second is
the descent data of the *sub*-pseudofunctor `Stacks.Descent.qcohPseudofunctor` of quasi-coherent
modules, with Mathlib's `CategoryTheory.Pseudofunctor.toDescentData`.  The effectivity
statement `AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc` lives in the
first, while the base transport `Stacks.Descent.essSurj_toDescentData_of_baseIso` is proved for
an arbitrary pseudofunctor and is therefore applied in the second.

The dictionary between the two is
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/StackReduction.lean`:
`Stacks.Descent.descentDataForgetFunctor` is an equivalence from the second to the first, and
`Stacks.Descent.descentDataForgetFunctor_obj_toDescentData` says that it carries the canonical
descent datum of a quasi-coherent module to the canonical descent datum of Stacks 023D — by
`rfl`.  Essential surjectivity therefore transfers both ways, which is what the two bridge
lemmas here record.  Note that this is *not* the same as
`Stacks.Descent.essSurj_canonicalDescentFunctor_iff`, which only restates effectivity inside the
first vocabulary.

**`Spec R` versus `[IsAffine S]`.**  The statement
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc` has its base literally of
the form `Spec R`, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcEffective.lean`: the one-element affine
case fixes the base of its family as the spectrum of a ring.  Stacks 023S asks only for an affine
base, so the restriction is a genuine, if mild, weakening.  It is removed here rather than
recorded in the tag: `AlgebraicGeometry.Scheme.isoSpec` moves the base of the family from an
arbitrary affine `S` to `Spec Γ(S, ⊤)`, and essential surjectivity of the canonical descent
functor comes back along that isomorphism by `Stacks.Descent.essSurj_toDescentData_of_baseIso`.
That lemma is proved in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/BaseIsoTransport.lean` for an arbitrary
pseudofunctor, which is why the passage through the second vocabulary is needed.

**Where the full faithfulness comes from.**  Full faithfulness of the
canonical descent functor for an arbitrary fpqc covering family of an arbitrary scheme is
unconditional, as `AlgebraicGeometry.nonempty_fullyFaithful_canonicalDescentFunctor'` of
`StacksFrontier/AlgebraicGeometry/Descent/FpqcHomSheafRefinement.lean`, whose input is the
Hom-sheaf route through `AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms` and, in the affine
one-element case, `Stacks.Descent.bijective_toDescentData_map_specMap`.  The `qcohPseudofunctor`
reduction to `Stacks.Descent.StandardAffineFullness` and
`Stacks.Descent.AffineSingletonFullness` is a *parallel* route which that development bypasses;
it is still undischarged, but nothing here needs it.

Stacks 022F has no named definition in this repository; a standard fpqc covering is spelled out
as a `CategoryTheory.PreZeroHypercover` with a finite index type, affine members, flat morphisms
and jointly surjective images, exactly as in the effectivity statement.

## References

* [Stacks Project, Tag 022F](https://stacks.math.columbia.edu/tag/022F)
* [Stacks Project, Tag 023S](https://stacks.math.columbia.edu/tag/023S)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace Stacks.Descent

section Abstract

variable {C : Type u} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, u}}

/-- **Faithfulness of the canonical descent functor depends only on the sieve the family
generates.**  The counterpart of `Stacks.Descent.full_toDescentData_of_sieve_eq` and of
`Stacks.Descent.essSurj_toDescentData_of_sieve_eq`, proved the same way: Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq` read through
`CategoryTheory.Functor.Faithful.of_iso`. -/
theorem faithful_toDescentData_of_sieve_eq {ι : Type t} {T : C} {V : ι → C} (f : ∀ i, V i ⟶ T)
    {ι' : Type w} {V' : ι' → C} (f' : ∀ j, V' j ⟶ T)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') [(F.toDescentData f).Faithful] :
    (F.toDescentData f').Faithful := by
  obtain ⟨e, ⟨i⟩⟩ := Pseudofunctor.DescentData.exists_equivalence_of_sieve_eq F f f' h
  have : e.functor.Faithful := inferInstance
  exact Functor.Faithful.of_iso i

/-- **Replacing the members of a family by isomorphic objects does not change the sieve it
generates.**  This is what lets a family of morphisms out of arbitrary affine schemes be replaced
by the corresponding family out of spectra of rings, along
`AlgebraicGeometry.Scheme.isoSpec`. -/
theorem sieve_ofArrows_comp_isIso {ι : Type t} {T : C} {V V' : ι → C} (f : ∀ i, V i ⟶ T)
    (v : ∀ i, V' i ⟶ V i) [∀ i, IsIso (v i)] :
    Sieve.ofArrows V' (fun i ↦ v i ≫ f i) = Sieve.ofArrows V f := by
  refine le_antisymm (Sieve.generate_le_iff _ _ |>.2 ?_) (Sieve.generate_le_iff _ _ |>.2 ?_)
  · rintro Y p ⟨i⟩
    exact ⟨V i, v i, f i, Presieve.ofArrows.mk i, rfl⟩
  · rintro Y p ⟨i⟩
    exact ⟨V' i, inv (v i), v i ≫ f i, Presieve.ofArrows.mk i,
      by rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]⟩

end Abstract

section Dictionary

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- **From essential surjectivity to effectivity, across the two vocabularies.**  If
`CategoryTheory.Pseudofunctor.toDescentData` of `Stacks.Descent.qcohPseudofunctor` is essentially
surjective for the family `f`, then every quasi-coherent descent datum of Stacks 023B for `f` is
effective.

This is the body of `Stacks.Descent.isEffective_of_isStack` with the stack condition replaced by
the essential surjectivity it is used for. -/
theorem isEffective_of_essSurj_qcohToDescentData
    [(qcohPseudofunctor.toDescentData f).EssSurj] (D : QuasicoherentDescentData f) :
    D.IsEffective := by
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := qcohPseudofunctor.toDescentData f) (descentDataLift D)
  exact ⟨M, ⟨eqToIso (descentDataForgetFunctor_obj_toDescentData M).symm ≪≫
    descentDataForgetFunctor.mapIso e ≪≫
      eqToIso (descentDataForgetFunctor_obj_descentDataLift D)⟩⟩

end Dictionary

end Stacks.Descent

namespace AlgebraicGeometry.QuasicoherentDescentData

variable {S : Scheme.{u}} [IsAffine S]

/-- **The images of a family cover the base after the base is moved along an isomorphism.** -/
theorem iUnion_range_comp_isoSpec_hom (𝒲 : PreZeroHypercover.{0} S)
    (hsurj : ⋃ i, Set.range (𝒲.f i) = Set.univ) :
    ⋃ i, Set.range (𝒲.f i ≫ S.isoSpec.hom) = Set.univ := by
  refine Set.iUnion_eq_univ_iff.2 fun y ↦ ?_
  obtain ⟨i, z, hz⟩ := Set.iUnion_eq_univ_iff.1 hsurj (S.isoSpec.inv y)
  exact ⟨i, z, by simp [show (𝒲.f i) z = S.isoSpec.inv y from hz]⟩

/-- **A standard fpqc covering is an fpqc covering family.**  For a finite family of flat
morphisms from affine schemes to an affine scheme whose images cover it, the generated presieve
belongs to `AlgebraicGeometry.Scheme.fpqcPrecoverage`.

The family is the composite of the one-element covering by the coproduct morphism
`∐ X i ⟶ S` — which is flat, surjective and, its source and target being affine, quasi-compact —
with the Zariski covering of `∐ X i` by its summands, so
`CategoryTheory.Precoverage.comp_mem_coverings` applies.  The reindexing along the projection
`(Σ _ : PUnit, I₀) → I₀` changes nothing, by
`Stacks.Descent.presieve_ofArrows_comp_of_surjective`. -/
theorem presieve₀_mem_fpqcPrecoverage_standardFpqc (𝒲 : PreZeroHypercover.{0} S) [Finite 𝒲.I₀]
    [∀ i, IsAffine (𝒲.X i)] [∀ i, Flat (𝒲.f i)]
    (hsurj : ⋃ i, Set.range (𝒲.f i) = Set.univ) :
    𝒲.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S := by
  have hsu : Surjective (Sigma.desc 𝒲.f) := Surjective.sigmaDesc_of_union_range_eq_univ hsurj
  have hqc : QuasiCompact (Sigma.desc 𝒲.f) := quasiCompact_of_compactSpace _
  have hsingle : Presieve.ofArrows (fun _ : PUnit.{1} ↦ ∐ 𝒲.X) (fun _ ↦ Sigma.desc 𝒲.f) ∈
      Scheme.fpqcPrecoverage.{u} S := by
    rw [Presieve.ofArrows_pUnit]
    exact (Sigma.desc 𝒲.f).singleton_mem_fpqcPrecoverage
  have hzar : ∀ _ : PUnit.{1}, Presieve.ofArrows 𝒲.X (fun i ↦ Sigma.ι 𝒲.X i) ∈
      Scheme.fpqcPrecoverage.{u} (∐ 𝒲.X) := fun _ ↦ by
    refine Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ ?_
    have hc := (sigmaOpenCover 𝒲.X).mem₀
    change Presieve.ofArrows 𝒲.X (fun i ↦ (sigmaOpenCover 𝒲.X).f i) ∈ _ at hc
    simpa only [sigmaOpenCover_f] using hc
  have hcomp := Precoverage.comp_mem_coverings (J := Scheme.fpqcPrecoverage.{u})
    (fun _ : PUnit.{1} ↦ Sigma.desc 𝒲.f) hsingle (fun _ i ↦ Sigma.ι 𝒲.X i) hzar
  have hfun : (fun p : Σ _ : PUnit.{1}, 𝒲.I₀ ↦ Sigma.ι 𝒲.X p.2 ≫ Sigma.desc 𝒲.f) =
      (fun p : Σ _ : PUnit.{1}, 𝒲.I₀ ↦ 𝒲.f p.2) := funext fun p ↦ Sigma.ι_desc 𝒲.f p.2
  rw [hfun, Stacks.Descent.presieve_ofArrows_comp_of_surjective 𝒲.f
    (fun p : Σ _ : PUnit.{1}, 𝒲.I₀ ↦ p.2) (fun i ↦ ⟨⟨PUnit.unit, i⟩, rfl⟩)] at hcomp
  exact hcomp

/-- **The full faithfulness half of [Stacks, Tag 023S]**: let `S` be an affine scheme and let
`{f i : X i ⟶ S}` be a standard fpqc covering of `S` in the sense of Stacks 022F.  Then the
functor from quasi-coherent `O_S`-modules to quasi-coherent descent data for the family is fully
faithful.

The content is the unconditional
`…QuasicoherentDescentData.nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage`,
which holds for an arbitrary fpqc covering family of an arbitrary scheme; all that is done here
is to supply the covering hypothesis in the elementary form in which Stacks 022F states it, by
`AlgebraicGeometry.QuasicoherentDescentData.presieve₀_mem_fpqcPrecoverage_standardFpqc`. -/
@[stacks 023S "full faithfulness", sga "1 VIII 1.1" "standard affine case"]
theorem nonempty_fullyFaithful_canonicalDescentFunctor_standardFpqc
    (𝒲 : PreZeroHypercover.{0} S) [Finite 𝒲.I₀] [∀ i, IsAffine (𝒲.X i)] [∀ i, Flat (𝒲.f i)]
    (hsurj : ⋃ i, Set.range (𝒲.f i) = Set.univ) :
    Nonempty (canonicalDescentFunctor 𝒲.f).FullyFaithful :=
  nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage 𝒲
    (presieve₀_mem_fpqcPrecoverage_standardFpqc 𝒲 hsurj)

/-- **The effectivity half of [Stacks, Tag 023S]**: let `S` be an affine scheme and let
`{f i : X i ⟶ S}` be a standard fpqc covering of `S` in the sense of Stacks 022F — a finite
family of flat morphisms from affine schemes whose images cover `S`.  Then every quasi-coherent
descent datum for the family is effective, i.e. isomorphic to the canonical descent datum of a
quasi-coherent module on `S`.

This is `AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc`, whose base is
literally of the form `Spec R`, transported to an arbitrary affine base along
`AlgebraicGeometry.Scheme.isoSpec`.  The transport runs in the vocabulary of
`Stacks.Descent.qcohPseudofunctor`, where `Stacks.Descent.essSurj_toDescentData_of_baseIso` is
available; see the implementation notes of this file. -/
@[stacks 023S "effectivity",
  sga "1 VIII 1.1" "standard affine case",
  sga "1 VIII 1.3" "Cor. 1.3, special case"]
theorem isEffective_standardFpqc_of_isAffine (𝒲 : PreZeroHypercover.{0} S) [Finite 𝒲.I₀]
    [∀ i, IsAffine (𝒲.X i)] [∀ i, Flat (𝒲.f i)]
    (hsurj : ⋃ i, Set.range (𝒲.f i) = Set.univ)
    (D : QuasicoherentDescentData 𝒲.f) : D.IsEffective := by
  have hspec : ∀ D : QuasicoherentDescentData (fun i ↦ 𝒲.f i ≫ S.isoSpec.hom), D.IsEffective :=
    isEffective_standardFpqc (R := Γ(S, ⊤))
      ⟨𝒲.I₀, 𝒲.X, fun i ↦ 𝒲.f i ≫ S.isoSpec.hom⟩
      (iUnion_range_comp_isoSpec_hom 𝒲 hsurj)
  have := Stacks.Descent.essSurj_toDescentData_of_baseIso Stacks.Descent.qcohPseudofunctor
    S.isoSpec (f := fun i ↦ 𝒲.f i ≫ S.isoSpec.hom) (f' := 𝒲.f) (fun _ ↦ rfl)
    (Stacks.Descent.essSurj_toDescentData_of_forall_isEffective hspec)
  exact Stacks.Descent.isEffective_of_essSurj_qcohToDescentData D

end AlgebraicGeometry.QuasicoherentDescentData

namespace Stacks.Descent

section Faithfulness

variable {S : Scheme.{u}} [IsAffine S]

/-- **The faithfulness half of Stacks 023S for `Stacks.Descent.qcohPseudofunctor`**: for a
standard fpqc covering `{f i : X i ⟶ S}` of an affine scheme `S` in the sense of Stacks 022F,
`CategoryTheory.Pseudofunctor.toDescentData` of the pseudofunctor of quasi-coherent modules is
faithful.

This carries no `stacks` attribute: the full faithfulness that Stacks 023S asserts is
`…QuasicoherentDescentData.nonempty_fullyFaithful_canonicalDescentFunctor_standardFpqc`
above, which subsumes it.  What this adds is the statement in the *other* of the two vocabularies
of this file — the one in which the hypothesis
`Stacks.Descent.AffineSingletonFullness` and the reductions of
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/SingletonFullness.lean` are phrased.

The lemma `Stacks.Descent.faithful_qcohToDescentData_of_isAffine` asks for the members of the
family to be spectra of rings, so each `X i` is first replaced by `Spec Γ(X i, ⊤)` along
`AlgebraicGeometry.Scheme.isoSpec`; that changes neither the generated sieve, by
`Stacks.Descent.sieve_ofArrows_comp_isIso`, nor therefore the faithfulness of the descent
functor, by `Stacks.Descent.faithful_toDescentData_of_sieve_eq`. -/
@[sga "1 VIII 1.2" "special case"]
theorem faithful_qcohToDescentData_standardFpqc (𝒲 : PreZeroHypercover.{0} S) [Finite 𝒲.I₀]
    [∀ i, IsAffine (𝒲.X i)] [∀ i, Flat (𝒲.f i)]
    (hsurj : ⋃ i, Set.range (𝒲.f i) = Set.univ) :
    (qcohPseudofunctor.toDescentData 𝒲.f).Faithful := by
  have hs : ∀ t : S, ∃ i, t ∈ Set.range ((𝒲.X i).isoSpec.inv ≫ 𝒲.f i).base := fun t ↦ by
    obtain ⟨i, z, hz⟩ := Set.iUnion_eq_univ_iff.1 hsurj t
    exact ⟨i, (𝒲.X i).isoSpec.hom z, by simpa [Scheme.Hom.comp_apply] using hz⟩
  have := faithful_qcohToDescentData_of_isAffine (T := S) (A := fun i ↦ Γ(𝒲.X i, ⊤))
    (fun i ↦ (𝒲.X i).isoSpec.inv ≫ 𝒲.f i) hs
  exact faithful_toDescentData_of_sieve_eq _ 𝒲.f
    (sieve_ofArrows_comp_isIso 𝒲.f fun i ↦ (𝒲.X i).isoSpec.inv)

end Faithfulness

/-- **`Stacks.Descent.AffineSingletonEffective` is a theorem.**  Every descent datum of
`Stacks.Descent.qcohPseudofunctor` for a single morphism from the spectrum of a ring which is an
fpqc covering of an affine scheme is effective.

A one-element covering is a standard fpqc covering: the index type `Unit` is finite, `Spec B` is
affine, and flatness and joint surjectivity are the two components of the covering hypothesis
extracted by `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff`.  So
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc_of_isAffine` applies, and
the conclusion is read in the pseudofunctor vocabulary by
`Stacks.Descent.essSurj_toDescentData_of_forall_isEffective`.

This discharges the hypothesis `heff` of
`Stacks.Descent.isStackFor_qcohPseudofunctor_of_isAffine_of_affineSingletonEffective`. -/
theorem affineSingletonEffective : AffineSingletonEffective.{u} := by
  intro T hT B b hmem
  have := hT
  obtain ⟨hsurj, hflat⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat) _ hmem)
  have hflatb : Flat b := hflat ()
  have hsurj' : ⋃ _ : Unit, Set.range b = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun t ↦ ⟨(), by simpa using hsurj t⟩
  exact essSurj_toDescentData_of_forall_isEffective
    (AlgebraicGeometry.QuasicoherentDescentData.isEffective_standardFpqc_of_isAffine
      (S := T) ⟨Unit, fun _ ↦ Spec B, fun _ ↦ b⟩ hsurj')

end Stacks.Descent

end

end
