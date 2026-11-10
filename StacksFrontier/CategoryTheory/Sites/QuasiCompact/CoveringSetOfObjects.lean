module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0GMS case (2): a covering set of objects gives the hypothesis of Stacks 0GMR (4)

Stacks Remark 0GMS lists sufficient conditions on a site `C` for the hypotheses of part (4) of
Stacks 0GMR to hold. In cases (1) and (2) one takes a set `B ⊆ Ob(C)` of objects and puts

  `S := { finite coproducts of the sheafified representables h_U^# : U ∈ B } ⊆ Ob(Sh(C))`.

This file proves **case (2)**: under

* (2)(a) there are finitely many `U₁, …, U_m ∈ B` with `∐_j h_{U_j}^# ⟶ *` surjective,
* (2)(b) every covering of a member of `B` is refined by a *finite* covering by members of `B`,
* (2)(c) for `U, U' ∈ B` there are finitely many `V_1, …, V_m ∈ B` with morphisms to `U` and to
  `U'` for which `∐_k h_{V_k}^# ⟶ h_U^# ⨯ h_{U'}^#` is surjective,

the set `S` satisfies both clauses of Stacks 0GMR (4): every sheaf surjecting onto the final
sheaf receives a map from a member of `S` which itself surjects onto the final sheaf, and
`K ⨯ K` is a quasi-compact object of the topos (Stacks 0D07) for every `K ∈ S`. The source
asserts this without proof, so each clause is work.

## Main definitions

* `CategoryTheory.Sheaf.coveringSetOfObjects`: the set `S` above.

## Main results

* `CategoryTheory.Sheaf.exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`:
  **Stacks 0GMS case (2)** — the only tagged statement in this file.
* `CategoryTheory.Sheaf.exists_mem_coveringSetOfObjects`: clause (4)(a) of Stacks 0GMR for `S`,
  from (2)(a) and (2)(b).
* `CategoryTheory.Sheaf.isQuasiCompact_prod_self_of_mem_coveringSetOfObjects`: clause (4)(b) of
  Stacks 0GMR for `S`.
* `CategoryTheory.Sheaf.bijective_colimit_post_globalSections_of_coveringSetOfObjects`: the
  payoff — global sections commute with filtered colimits of sheaves of sets on such a site,
  i.e. Stacks 0GMR (4) with its hypothesis discharged.

Supporting results of independent interest:

* `CategoryTheory.Sheaf.exists_sigmaIota_section`: **Stacks 00WI** for sheaves of sets — a section
  of a coproduct lies, locally, in a single summand.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_prodMap`: **distributivity as
  surjectivity** — the canonical morphism `∐_{(i, i')} (A i ⨯ B i') ⟶ (∐ A) ⨯ (∐ B)` is locally
  surjective.
* `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_sigma`: a coproduct of jointly surjective
  families is jointly surjective.
* `CategoryTheory.Sheaf.isQuasiCompact_sigmaObj_of_finite`: a coproduct of a *finite* family of
  quasi-compact sheaves of sets is quasi-compact.
* `CategoryTheory.Sheaf.isQuasiCompact_prod_sigmaObj`: a product of two finite coproducts of
  sheaves whose pairwise products are quasi-compact is quasi-compact.
* `CategoryTheory.GrothendieckTopology.isQuasiCompactObject_of_exists_finite_refinement`:
  hypothesis (2)(b) makes every member of `B` a quasi-compact object of the site (Stacks 090H).

## Implementation notes

Clause (4)(b) is distributivity of products over coproducts, read as a *surjectivity* statement
rather than as an isomorphism, which is all that quasi-compactness needs: Stacks 0GMP (2)
transfers quasi-compactness along a surjection, so it is enough that
`∐_{(i, i')} (A i ⨯ B i') ⟶ (∐ A) ⨯ (∐ B)` be locally surjective and that the source be a finite
coproduct of quasi-compact sheaves.

Clause (4)(a) takes the family of (2)(a), covers each of its members by objects over which `G`
has a section — local surjectivity of `G ⟶ *` gives a covering, (2)(b) refines it to a finite one
inside `B`, and the sections restrict — and takes `K` to be the coproduct of the sheafified
representables of all of those. That `K ⟶ *` is surjective is Stacks 00WT for each member
separately, assembled by `isLocallySurjective_sigmaDesc_sigma` and composed with (2)(a).

Two notions of surjectivity are in play in the quasi-compactness literature of this repository.
`Sheaf.QuasiCompact` (`…QuasiCompact.FiniteCoproducts`) phrases Stacks 0D07 with
`CategoryTheory.Epi` and a `Finset`, and carries Stacks 0GMQ; `CategoryTheory.Sheaf.IsQuasiCompact`
(`…Sites.QuasiCompact`) phrases it with `CategoryTheory.Sheaf.IsLocallySurjective` and a finite
`Set`, and is the one Stacks 0GMR (4) is stated over. `Sheaf.quasiCompact_iff_isQuasiCompact`
identifies them, and `isQuasiCompact_sigmaObj_of_finite` is how Stacks 0GMQ is consumed here: it
is 0GMQ read through that identification and generalised from `Fin n` to an arbitrary finite index
type in `Type max u v`, which is the index universe the sectionwise criterion
`Sheaf.isLocallySurjective_sigmaDesc_iff` quantifies over. It carries no `@[stacks 0GMQ]`
attribute — that tag keeps its single site on `Sheaf.quasiCompact_coproduct_fin`.

`Sheaf.QuasiCompact`, `Sheaf.quasiCompact_coproduct_fin` and the three bridge theorems live at the
*root* level rather than in `CategoryTheory`, because the file declaring them opens
`CategoryTheory` without entering it; they are therefore written `_root_.Sheaf.…` below. That
naming is pre-existing and is deliberately not changed here.

The distributivity statement is proved sectionwise, but no description of the sections of a binary
product is needed: a section of a sheaf over `V` is a morphism out of `h_V^#`
(`CategoryTheory.Sheaf.sectionEquiv`), so the pair of local sections produced by Stacks 00WI is
assembled with `CategoryTheory.Limits.prod.lift` and the required identity of sections becomes an
identity of morphisms into a product, closed by `CategoryTheory.Limits.prod.hom_ext`.
`isLocallySurjective_sigmaDesc_sigma` needs no sieve bookkeeping at all: surjectivity of sheaves
of sets is epimorphy (`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`), and an epimorphism out
of a coproduct of coproducts is cancelled one level at a time.

## Tag placement

Stacks 0GMS is a Remark with three cases, and case (2) is a *single* assertion — that the set `S`
displayed above satisfies the hypotheses of Stacks 0GMR (4). The one declaration that states that
assertion, with `S` pinned to the displayed set rather than merely asserted to exist, is
`exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`, and it carries the single
`@[stacks 0GMS "case (2)"]` site. The two clause theorems are its halves and the definition of
`S` is a *Main definitions* entry, so neither is a second site. Cases (1) and (3) of the remark
are not proved here and no key is claimed for them.

## References

Stacks Project, tag 0GMS (`sites-remark-stronger-conditions`), case (2); its target is tag 0GMR
part (4), and it consumes tags 0D06, 0D07, 00WI, 00WT, 0GMP and 0GMQ.
-/
@[expose] public section

open CategoryTheory Limits Opposite

universe w₂ w₁ v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Sections of a coproduct of sheaves of sets -/

/-- The coprojections of a coproduct of sheaves of sets are jointly surjective: the morphism they
induce out of the coproduct is the identity. -/
theorem isLocallySurjective_sigmaDesc_sigmaIota {ι : Type max u v}
    (A : ι → Sheaf J (Type max u v)) :
    IsLocallySurjective (Sigma.desc (Sigma.ι A)) := by
  have h : Sigma.desc (Sigma.ι A) = 𝟙 (∐ A) :=
    Sigma.hom_ext _ _ fun i => by rw [Sigma.ι_comp_desc, Category.comp_id]
  rw [h]
  infer_instance

/-- **Stacks 00WI** for sheaves of sets: a section `s` of a coproduct `∐ A` over `U` lies, locally
on `U`, in a single summand. Precisely, there is a covering sieve `T` of `U` such that every
`g : V ⟶ U` in `T` restricts `s` to a section of some `A i`.

This is the sectionwise criterion `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff` applied
to the coprojections, which are jointly surjective. -/
theorem exists_sigmaIota_section {ι : Type max u v} (A : ι → Sheaf J (Type max u v)) {U : C}
    (s : (∐ A).obj.obj (op U)) :
    ∃ T ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), T.arrows g →
      ∃ (i : ι) (t : (A i).obj.obj (op V)),
        (Sigma.ι A i).hom.app (op V) t = (∐ A).obj.map g.op s :=
  (isLocallySurjective_sigmaDesc_iff (Sigma.ι A)).1
    (isLocallySurjective_sigmaDesc_sigmaIota A) s

/-! ### Distributivity of products over coproducts, as a surjectivity statement -/

/-- **Distributivity as surjectivity.** The canonical morphism
`∐_{(i, i')} (A i ⨯ B i') ⟶ (∐ A) ⨯ (∐ B)` of sheaves of sets, whose `(i, i')`-th component is
`CategoryTheory.Limits.prod.map` of the two coprojections, is locally surjective.

This is weaker than the distributivity isomorphism and is all that quasi-compactness needs, by
Stacks 0GMP (2).

*Proof.* A section of `(∐ A) ⨯ (∐ B)` over `U` has two components, sections of `∐ A` and of `∐ B`;
by Stacks 00WI each lies locally in a single summand, and the two covering sieves meet in a
covering sieve. Over a member `g : V ⟶ U` of the intersection the two local sections, read as
morphisms out of `h_V^#`, pair into a morphism `h_V^# ⟶ A i ⨯ B i'`, i.e. into a section of
`A i ⨯ B i'` over `V`, whose image is the restriction of the original section: the two morphisms
`h_V^# ⟶ (∐ A) ⨯ (∐ B)` to be compared agree on both projections. -/
theorem isLocallySurjective_sigmaDesc_prodMap {ι ι' : Type max u v}
    (A : ι → Sheaf J (Type max u v)) (B : ι' → Sheaf J (Type max u v)) :
    IsLocallySurjective
      (Sigma.desc fun p : ι × ι' => prod.map (Sigma.ι A p.1) (Sigma.ι B p.2)) := by
  refine (isLocallySurjective_sigmaDesc_iff _).2 ?_
  intro U s
  obtain ⟨T₁, hT₁, hc₁⟩ := exists_sigmaIota_section A
    ((Limits.prod.fst : (∐ A) ⨯ (∐ B) ⟶ ∐ A).hom.app (op U) s)
  obtain ⟨T₂, hT₂, hc₂⟩ := exists_sigmaIota_section B
    ((Limits.prod.snd : (∐ A) ⨯ (∐ B) ⟶ ∐ B).hom.app (op U) s)
  refine ⟨T₁ ⊓ T₂, J.intersection_covering hT₁ hT₂, ?_⟩
  intro V g hg
  obtain ⟨i, a, ha⟩ := hc₁ g hg.1
  obtain ⟨i', b, hb⟩ := hc₂ g hg.2
  refine ⟨(i, i'), sectionEquiv J
    (prod.lift ((sectionEquiv J).symm a) ((sectionEquiv J).symm b)), ?_⟩
  apply (sectionEquiv J).symm.injective
  rw [sectionEquiv_symm_comp, Equiv.symm_apply_apply, sectionEquiv_symm_map]
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, prod.map_fst, prod.lift_fst_assoc, Category.assoc,
      ← sectionEquiv_symm_comp, ha, sectionEquiv_symm_map, sectionEquiv_symm_comp]
  · rw [Category.assoc, prod.map_snd, prod.lift_snd_assoc, Category.assoc,
      ← sectionEquiv_symm_comp, hb, sectionEquiv_symm_map, sectionEquiv_symm_comp]

/-! ### Finite coproducts of quasi-compact sheaves of sets -/

/-- A coproduct over an empty index type is an initial object: a morphism out of it is given by no
data and determined by none. -/
private noncomputable def isInitialSigmaObjOfIsEmpty {ι : Type max u v} [IsEmpty ι]
    (A : ι → Sheaf J (Type max u v)) : IsInitial (∐ A) :=
  IsInitial.ofUniqueHom (fun _ => Sigma.desc fun i => isEmptyElim i)
    (fun _ _ => Sigma.hom_ext _ _ fun i => isEmptyElim i)

/-- An initial sheaf of sets is a quasi-compact object of `Sh(C)` (Stacks 0D07): the **empty**
subfamily already works, because a morphism between two initial objects is an isomorphism and
hence a surjection. -/
theorem isQuasiCompact_of_isInitial {F : Sheaf J (Type max u v)} (hF : IsInitial F) :
    IsQuasiCompact F := by
  intro I G f _
  refine ⟨∅, Set.finite_empty, ?_⟩
  have hempty : IsEmpty ((∅ : Set I) : Type max u v) := by simp only [Set.isEmpty_coe_sort]
  have : IsIso (Sigma.desc fun j : ((∅ : Set I) : Type max u v) => f j.1) :=
    ⟨⟨hF.to _, (isInitialSigmaObjOfIsEmpty (J := J) _).hom_ext _ _, hF.hom_ext _ _⟩⟩
  infer_instance

/-- A coproduct of sheaves of sets over an empty index type is quasi-compact. -/
theorem isQuasiCompact_sigmaObj_of_isEmpty {ι : Type max u v} [IsEmpty ι]
    (A : ι → Sheaf J (Type max u v)) : IsQuasiCompact (∐ A) :=
  isQuasiCompact_of_isInitial (isInitialSigmaObjOfIsEmpty A)

/-- **Stacks 0GMQ, consumed at the other spelling of Stacks 0D07 and at an arbitrary finite index
type.** A coproduct of a finite family of quasi-compact sheaves of sets is quasi-compact.

Stacks 0GMQ is formalized as `Sheaf.quasiCompact_coproduct_fin`, for a family indexed by `Fin n`
with
`1 ≤ n` and in the `CategoryTheory.Epi`-and-`Finset` spelling of Stacks 0D07. Here the index is an
arbitrary type of `Type max u v` with `Finite`, which is the index universe the sectionwise
criterion `CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_iff` quantifies over, and the
spelling is `CategoryTheory.Sheaf.IsQuasiCompact`, which is the one Stacks 0GMR (4) uses. The
reindexing is `CategoryTheory.Limits.Sigma.reindex` along an equivalence with `Fin n`, the
spellings are identified by `Sheaf.quasiCompact_iff_isQuasiCompact`, and the empty case — which
0GMQ excludes — is `isQuasiCompact_sigmaObj_of_isEmpty`.

This statement carries no `@[stacks 0GMQ]` attribute: that tag keeps its single site on
`Sheaf.quasiCompact_coproduct_fin`, of which this is a consequence. -/
@[sga "4 VI 1.4" "partial"]
theorem isQuasiCompact_sigmaObj_of_finite {ι : Type max u v} [Finite ι]
    (A : ι → Sheaf J (Type max u v)) (hA : ∀ i, IsQuasiCompact (A i)) :
    IsQuasiCompact (∐ A) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : IsEmpty ι := Function.isEmpty e
    exact isQuasiCompact_sigmaObj_of_isEmpty A
  · exact _root_.Sheaf.isQuasiCompact_of_quasiCompact
      (_root_.Sheaf.QuasiCompact.of_iso (Sigma.reindex e.symm A)
        (_root_.Sheaf.quasiCompact_coproduct_fin hn (A ∘ e.symm) fun _ =>
          _root_.Sheaf.quasiCompact_of_isQuasiCompact (hA _)))

/-- A product of two finite coproducts of sheaves of sets is quasi-compact as soon as all the
pairwise products of their summands are: the canonical morphism
`∐_{(i, i')} (A i ⨯ B i') ⟶ (∐ A) ⨯ (∐ B)` is locally surjective, its source is a finite
coproduct of quasi-compact sheaves, and Stacks 0GMP (2) carries quasi-compactness across. -/
theorem isQuasiCompact_prod_sigmaObj {ι ι' : Type max u v} [Finite ι] [Finite ι']
    (A : ι → Sheaf J (Type max u v)) (B : ι' → Sheaf J (Type max u v))
    (h : ∀ i i', IsQuasiCompact (A i ⨯ B i')) :
    IsQuasiCompact ((∐ A) ⨯ (∐ B)) :=
  isQuasiCompact_of_isLocallySurjective _ (isLocallySurjective_sigmaDesc_prodMap A B)
    (isQuasiCompact_sigmaObj_of_finite (fun p : ι × ι' => A p.1 ⨯ B p.2) fun p => h p.1 p.2)

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- **Hypothesis (2)(b) of Stacks 0GMS makes an object quasi-compact.** If every covering of `U`
can be refined by a covering of `U` indexed by a finite type, then `U` is a quasi-compact object
of the site (Stacks 090H).

The finiteness condition of Stacks 090H is on the image of the index map of the refinement, which
is finite as soon as the refinement's index type is. Note that 0GMS (2)(b) asks in addition that
the members of the refinement lie in `B`; that part of the hypothesis is not used here. -/
theorem isQuasiCompactObject_of_exists_finite_refinement {U : C}
    (h : ∀ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J U →
      ∃ (𝒱 : PreZeroHypercover.{max u v} U) (_ : 𝒱.Hom 𝒰), 𝒱.sieve₀ ∈ J U ∧ Finite 𝒱.I₀) :
    J.IsQuasiCompactObject U := by
  intro 𝒰 h𝒰
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := h 𝒰 h𝒰
  exact ⟨𝒱, φ, h𝒱, Set.finite_range _⟩

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Clause (4)(b) of Stacks 0GMR from hypotheses (2)(b) and (2)(c) -/

/-- **Hypothesis (2)(c) of Stacks 0GMS makes `h_U^# ⨯ h_{U'}^#` quasi-compact.** Given a finite
family `V : ι → C` of quasi-compact objects of the site together with a locally surjective
morphism `∐_i h_{V i}^# ⟶ h_U^# ⨯ h_{U'}^#`, the product `h_U^# ⨯ h_{U'}^#` is quasi-compact.

The source is a finite coproduct of quasi-compact sheaves by Stacks 0D06 and 0GMQ, and
Stacks 0GMP (2) carries quasi-compactness across the surjection. In Stacks 0GMS (2)(c) the
morphism is `CategoryTheory.Limits.prod.lift` of the sheafified representables of two families of
morphisms `V i ⟶ U` and `V i ⟶ U'`; the statement here only uses that some locally surjective
morphism out of such a coproduct exists. -/
theorem isQuasiCompact_prod_sheafifiedYoneda_of_isLocallySurjective {ι : Type max u v} [Finite ι]
    {U U' : C} (V : ι → C) (hV : ∀ i, J.IsQuasiCompactObject (V i))
    (φ : (∐ fun i => (sheafifiedYoneda J).obj (V i)) ⟶
      (sheafifiedYoneda J).obj U ⨯ (sheafifiedYoneda J).obj U')
    (hφ : IsLocallySurjective φ) :
    IsQuasiCompact ((sheafifiedYoneda J).obj U ⨯ (sheafifiedYoneda J).obj U') :=
  isQuasiCompact_of_isLocallySurjective φ hφ
    (isQuasiCompact_sigmaObj_of_finite _ fun i =>
      (J.isQuasiCompactObject_iff_isQuasiCompact_sheafifiedYoneda (V i)).1 (hV i))

/-- **Clause (4)(b) of Stacks 0GMR for the set `S` of Stacks 0GMS.** Let `B ⊆ Ob(C)` be such that
`h_W^# ⨯ h_{W'}^#` is quasi-compact for all `W, W' ∈ B` — which is hypothesis (1)(b) of
Stacks 0GMS, and follows from its (2)(b) and (2)(c) by
`isQuasiCompact_prod_sheafifiedYoneda_of_isLocallySurjective` and
`CategoryTheory.GrothendieckTopology.isQuasiCompactObject_of_exists_finite_refinement`. Then for
every finite family `U : ι → C` of members of `B` the product `K ⨯ K` of
`K = ∐_i h_{U i}^#` with itself is quasi-compact.

This is the second of the two clauses that Stacks 0GMS case (2) asserts for `S`; the first is
`exists_mem_coveringSetOfObjects` below. Neither carries the `@[stacks 0GMS "case (2)"]`
attribute, which sits on the one declaration asserting both at once,
`exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`. -/
theorem isQuasiCompact_prod_self_sigmaSheafifiedYoneda {B : Set C} {ι : Type max u v} [Finite ι]
    (U : ι → C) (hU : ∀ i, U i ∈ B)
    (hB : ∀ W ∈ B, ∀ W' ∈ B,
      IsQuasiCompact ((sheafifiedYoneda J).obj W ⨯ (sheafifiedYoneda J).obj W')) :
    IsQuasiCompact ((∐ fun i => (sheafifiedYoneda J).obj (U i)) ⨯
      (∐ fun i => (sheafifiedYoneda J).obj (U i))) :=
  isQuasiCompact_prod_sigmaObj _ _ fun i i' => hB _ (hU i) _ (hU i')

/-! ### Clause (4)(a) of Stacks 0GMR from hypotheses (2)(a) and (2)(b) -/

/-- A coproduct of jointly surjective families is jointly surjective: if for every `i` the family
`(ψ ⟨i, k⟩)_{k}` induces a surjection onto `Gm i`, then the whole family, composed with the
coprojections of `∐ Gm`, induces a surjection onto `∐ Gm`.

Surjectivity of a morphism of sheaves of sets is epimorphy
(`CategoryTheory.Sheaf.isLocallySurjective_iff_epi`), so no sieve bookkeeping is needed: an
epimorphism is cancelled one level of the coproduct at a time. -/
theorem isLocallySurjective_sigmaDesc_sigma {ι : Type max u v} {κ : ι → Type max u v}
    {A : (p : Σ i, κ i) → Sheaf J (Type max u v)} {Gm : ι → Sheaf J (Type max u v)}
    (ψ : ∀ p : Σ i, κ i, A p ⟶ Gm p.1)
    (hψ : ∀ i, IsLocallySurjective (Sigma.desc fun k : κ i => ψ ⟨i, k⟩)) :
    IsLocallySurjective (Sigma.desc fun p : Σ i, κ i => ψ p ≫ Sigma.ι Gm p.1) := by
  rw [isLocallySurjective_iff_epi]
  have hepi : ∀ i, Epi (Sigma.desc fun k : κ i => ψ ⟨i, k⟩) := fun i =>
    (isLocallySurjective_iff_epi _).1 (hψ i)
  refine ⟨fun {Z} a b hab => Sigma.hom_ext _ _ fun i => ?_⟩
  refine (cancel_epi (Sigma.desc fun k : κ i => ψ ⟨i, k⟩)).1 (Sigma.hom_ext _ _ fun k => ?_)
  have h := congrArg (fun m => Sigma.ι A ⟨i, k⟩ ≫ m) hab
  simp only [Sigma.ι_comp_desc_assoc, Category.assoc] at h
  simp only [Sigma.ι_comp_desc_assoc]
  exact h

/-- A sheaf of sets surjecting onto the final sheaf has sections over a covering of every object:
every object `W` carries a covering sieve each of whose members has a nonempty set of sections of
`G`.

This is local surjectivity of `G ⟶ *` read at the unique section of the final sheaf over `W`; the
condition that the section of `G` map to the restriction of that section is vacuous, because the
final sheaf has at most one section over any object. -/
theorem exists_covering_nonempty_section {G : Sheaf J (Type max u v)}
    (hG : IsLocallySurjective (terminal.from G)) (W : C) :
    ∃ T ∈ J W, ∀ ⦃V : C⦄ (g : V ⟶ W), T.arrows g → Nonempty (G.obj.obj (op V)) := by
  refine ⟨Presheaf.imageSieve (terminal.from G).hom
      (sectionEquiv J (terminal.from ((sheafifiedYoneda J).obj W))),
    Presheaf.imageSieve_mem J (terminal.from G).hom _, fun V g hg => ?_⟩
  obtain ⟨t, -⟩ := hg
  exact ⟨t⟩

/-- **The set `S` of Stacks 0GMS**, for a set `B` of objects of the site: the set of those sheaves
of sets which are a coproduct, over a finite index type, of the sheafified representables `h_U^#`
of members of `B`.

In cases (1) and (2) of Stacks 0GMS this is the set the hypotheses of Stacks 0GMR (4) are asserted
for; case (3) uses the same construction with `B` the set of quasi-compact objects of the site. -/
def coveringSetOfObjects (J : GrothendieckTopology C) (B : Set C) :
    Set (Sheaf J (Type max u v)) :=
  {K | ∃ (ι : Type max u v) (_ : Finite ι) (U : ι → C),
    (∀ i, U i ∈ B) ∧ K = ∐ fun i => (sheafifiedYoneda J).obj (U i)}

/-- **Clause (4)(a) of Stacks 0GMR for the set `S` of Stacks 0GMS**, from hypotheses (2)(a) and
(2)(b). Every sheaf of sets `G` surjecting onto the final sheaf receives a morphism from a member
of `S` which itself surjects onto the final sheaf.

*Proof.* Take the family `U₀ : ι₀ → C` of (2)(a). Local surjectivity of `G ⟶ *` covers each
`U₀ j` by objects carrying a section of `G`; hypothesis (2)(b) refines that covering to a finite
one by members of `B`, whose members still carry sections of `G` by restriction. Let `K` be the
coproduct of the sheafified representables of all those members, over the (finite) sigma type.
Then `K ∈ S`, the chosen sections give `K ⟶ G`, and `K ⟶ *` is surjective because for each `j`
the morphism `∐_b h_{V_{j,b}}^# ⟶ h_{U₀ j}^#` is surjective (Stacks 00WT), hence so is
`K ⟶ ∐_j h_{U₀ j}^#`, which composes with (2)(a). -/
theorem exists_mem_coveringSetOfObjects {B : Set C}
    (ha : ∃ (ι : Type max u v) (_ : Finite ι) (U : ι → C), (∀ i, U i ∈ B) ∧
      IsLocallySurjective (terminal.from (∐ fun i => (sheafifiedYoneda J).obj (U i))))
    (hb : ∀ U ∈ B, ∀ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J U →
      ∃ (𝒱 : PreZeroHypercover.{max u v} U) (_ : 𝒱.Hom 𝒰),
        𝒱.sieve₀ ∈ J U ∧ Finite 𝒱.I₀ ∧ ∀ i, 𝒱.X i ∈ B)
    {G : Sheaf J (Type max u v)} (hG : IsLocallySurjective (terminal.from G)) :
    ∃ K ∈ coveringSetOfObjects J B, Nonempty (K ⟶ G) ∧
      IsLocallySurjective (terminal.from K) := by
  obtain ⟨ι₀, hι₀, U₀, hU₀B, hsurj⟩ := ha
  have key : ∀ j : ι₀, ∃ 𝒱 : PreZeroHypercover.{max u v} (U₀ j),
      𝒱.sieve₀ ∈ J (U₀ j) ∧ Finite 𝒱.I₀ ∧ (∀ b, 𝒱.X b ∈ B) ∧
        ∀ b, Nonempty (G.obj.obj (op (𝒱.X b))) := by
    intro j
    obtain ⟨T, hT, hTsec⟩ := exists_covering_nonempty_section hG (U₀ j)
    obtain ⟨A, X, r, hXr⟩ := Sieve.exists_eq_ofArrows T
    obtain ⟨𝒱, φ, h𝒱, hfin, hB⟩ :=
      hb (U₀ j) (hU₀B j) { I₀ := A, X := X, f := r }
        (show Sieve.ofArrows X r ∈ J (U₀ j) from hXr ▸ hT)
    refine ⟨𝒱, h𝒱, hfin, hB, fun b => ?_⟩
    obtain ⟨t⟩ := hTsec (r (φ.s₀ b)) (by rw [hXr]; exact Sieve.ofArrows_mk X r _)
    exact ⟨G.obj.map (φ.h₀ b).op t⟩
  choose 𝒱 h𝒱cov h𝒱fin h𝒱B h𝒱sec using key
  refine ⟨∐ fun p : Σ j : ι₀, (𝒱 j).I₀ => (sheafifiedYoneda J).obj ((𝒱 p.1).X p.2),
    ⟨Σ j : ι₀, (𝒱 j).I₀, inferInstance, fun p => (𝒱 p.1).X p.2,
      fun p => h𝒱B p.1 p.2, rfl⟩,
    ⟨Sigma.desc fun p => (sectionEquiv J).symm (h𝒱sec p.1 p.2).some⟩, ?_⟩
  have : IsLocallySurjective
      (Sigma.desc fun p : Σ j : ι₀, (𝒱 j).I₀ =>
        (sheafifiedYoneda J).map ((𝒱 p.1).f p.2) ≫
          Sigma.ι (fun j : ι₀ => (sheafifiedYoneda J).obj (U₀ j)) p.1) :=
    isLocallySurjective_sigmaDesc_sigma _ fun j =>
      (Stacks.Sites.QuasiCompactCriterion.isLocallySurjective_sigmaDesc_sheafifiedYoneda_map_iff ((𝒱
        j).f)).2 (h𝒱cov j)
  have := hsurj
  rw [← terminal.comp_from (Sigma.desc fun p : Σ j : ι₀, (𝒱 j).I₀ =>
    (sheafifiedYoneda J).map ((𝒱 p.1).f p.2) ≫
      Sigma.ι (fun j : ι₀ => (sheafifiedYoneda J).obj (U₀ j)) p.1)]
  infer_instance

/-! ### Stacks 0GMS case (2) -/

/-- **Clause (4)(b) of Stacks 0GMR for the set `S` of Stacks 0GMS**, in the form the clause is
stated: if `h_W^# ⨯ h_{W'}^#` is quasi-compact for all `W, W' ∈ B`, then `K ⨯ K` is quasi-compact
for every `K ∈ S`. -/
theorem isQuasiCompact_prod_self_of_mem_coveringSetOfObjects {B : Set C}
    (hB : ∀ W ∈ B, ∀ W' ∈ B,
      IsQuasiCompact ((sheafifiedYoneda J).obj W ⨯ (sheafifiedYoneda J).obj W'))
    {K : Sheaf J (Type max u v)} (hK : K ∈ coveringSetOfObjects J B) :
    IsQuasiCompact (K ⨯ K) := by
  obtain ⟨ι, hfin, U, hUB, rfl⟩ := hK
  exact isQuasiCompact_prod_self_sigmaSheafifiedYoneda U hUB hB

/-- **Stacks 0GMS, case (2).** Let `C` be a site and `B ⊆ Ob(C)` a set of objects such that

* (a) there are finitely many `U₁, …, U_m ∈ B` with `∐_j h_{U_j}^# ⟶ *` surjective,
* (b) every covering of a member of `B` is refined by a finite covering by members of `B`,
* (c) for `U, U' ∈ B` there are finitely many `V_1, …, V_m ∈ B` with morphisms `V_k ⟶ U` and
  `V_k ⟶ U'` for which `∐_k h_{V_k}^# ⟶ h_U^# ⨯ h_{U'}^#` is surjective.

Then the hypotheses of part (4) of Stacks 0GMR are satisfied, with
`S = CategoryTheory.Sheaf.coveringSetOfObjects J B` the set of finite coproducts of the sheafified
representables of members of `B`.

The two clauses are `exists_mem_coveringSetOfObjects` and
`isQuasiCompact_prod_self_of_mem_coveringSetOfObjects`; the latter consumes (b) and (c) through
`CategoryTheory.GrothendieckTopology.isQuasiCompactObject_of_exists_finite_refinement` and
`isQuasiCompact_prod_sheafifiedYoneda_of_isLocallySurjective`. The existential over `S` is the
shape in which Stacks 0GMR (4) states its hypothesis, and `S` is pinned to the set the source
displays rather than merely asserted to exist.

Cases (1) and (3) of the remark are not proved here. -/
@[stacks 0GMS "case (2)"]
theorem exists_set_isLocallySurjective_and_isQuasiCompact_prod_self {B : Set C}
    (ha : ∃ (ι : Type max u v) (_ : Finite ι) (U : ι → C), (∀ i, U i ∈ B) ∧
      IsLocallySurjective (terminal.from (∐ fun i => (sheafifiedYoneda J).obj (U i))))
    (hb : ∀ U ∈ B, ∀ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J U →
      ∃ (𝒱 : PreZeroHypercover.{max u v} U) (_ : 𝒱.Hom 𝒰),
        𝒱.sieve₀ ∈ J U ∧ Finite 𝒱.I₀ ∧ ∀ i, 𝒱.X i ∈ B)
    (hc : ∀ U ∈ B, ∀ U' ∈ B, ∃ (ι : Type max u v) (_ : Finite ι) (V : ι → C)
      (a : ∀ i, V i ⟶ U) (b : ∀ i, V i ⟶ U'), (∀ i, V i ∈ B) ∧
        IsLocallySurjective (Sigma.desc fun i =>
          prod.lift ((sheafifiedYoneda J).map (a i)) ((sheafifiedYoneda J).map (b i)))) :
    ∃ S : Set (Sheaf J (Type max u v)),
      (∀ G : Sheaf J (Type max u v), IsLocallySurjective (terminal.from G) →
          ∃ K ∈ S, Nonempty (K ⟶ G) ∧ IsLocallySurjective (terminal.from K)) ∧
        ∀ K ∈ S, IsQuasiCompact (K ⨯ K) := by
  have hqcobj : ∀ U ∈ B, J.IsQuasiCompactObject U := fun U hU =>
    GrothendieckTopology.isQuasiCompactObject_of_exists_finite_refinement fun 𝒰 h𝒰 => by
      obtain ⟨𝒱, φ, h𝒱, hfin, -⟩ := hb U hU 𝒰 h𝒰
      exact ⟨𝒱, φ, h𝒱, hfin⟩
  have hB : ∀ W ∈ B, ∀ W' ∈ B,
      IsQuasiCompact ((sheafifiedYoneda J).obj W ⨯ (sheafifiedYoneda J).obj W') := by
    intro W hW W' hW'
    obtain ⟨ι, hfin, V, a, b, hVB, hls⟩ := hc W hW W' hW'
    exact isQuasiCompact_prod_sheafifiedYoneda_of_isLocallySurjective V
      (fun i => hqcobj _ (hVB i)) _ hls
  exact ⟨coveringSetOfObjects J B, fun _ hG => exists_mem_coveringSetOfObjects ha hb hG,
    fun _ hK => isQuasiCompact_prod_self_of_mem_coveringSetOfObjects hB hK⟩

/-- **The payoff.** On a site carrying a set `B` of objects as in Stacks 0GMS case (2), global
sections commute with filtered colimits of sheaves of sets: the canonical map
`colim_i Γ(C, F i) ⟶ Γ(C, colim_i F i)` is bijective.

This is part (4) of Stacks 0GMR with its hypothesis discharged by
`exists_set_isLocallySurjective_and_isQuasiCompact_prod_self`. It is untagged: the statement is
Stacks 0GMR (4), whose single site is
`injective_and_bijective_colimit_post_globalSections`. -/
theorem bijective_colimit_post_globalSections_of_coveringSetOfObjects {B : Set C}
    (ha : ∃ (ι : Type max u v) (_ : Finite ι) (U : ι → C), (∀ i, U i ∈ B) ∧
      IsLocallySurjective (terminal.from (∐ fun i => (sheafifiedYoneda J).obj (U i))))
    (hb : ∀ U ∈ B, ∀ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J U →
      ∃ (𝒱 : PreZeroHypercover.{max u v} U) (_ : 𝒱.Hom 𝒰),
        𝒱.sieve₀ ∈ J U ∧ Finite 𝒱.I₀ ∧ ∀ i, 𝒱.X i ∈ B)
    (hc : ∀ U ∈ B, ∀ U' ∈ B, ∃ (ι : Type max u v) (_ : Finite ι) (V : ι → C)
      (a : ∀ i, V i ⟶ U) (b : ∀ i, V i ⟶ U'), (∀ i, V i ∈ B) ∧
        IsLocallySurjective (Sigma.desc fun i =>
          prod.lift ((sheafifiedYoneda J).map (a i)) ((sheafifiedYoneda J).map (b i))))
    {I : Type w₁} [Category.{w₂} I] [IsFiltered I] [HasColimitsOfShape I (Type max u v)]
    (F : I ⥤ Sheaf J (Type max u v)) :
    Function.Bijective (colimit.post F (Γ J (Type max u v))) :=
  (injective_and_bijective_colimit_post_globalSections J F).2.2.2
    (exists_set_isLocallySurjective_and_isQuasiCompact_prod_self ha hb hc)

end CategoryTheory.Sheaf
