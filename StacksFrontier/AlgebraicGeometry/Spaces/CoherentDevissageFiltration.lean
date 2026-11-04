module

public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSupportSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverAlgClosedFieldConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealCoproductGenericIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.CategoryTheory.SubfunctorFactor

/-!
# The dévissage filtration of a coherent module on a Noetherian algebraic space

Stacks 07UR says that a coherent module `F` on a Noetherian algebraic space `X` carries a
finite filtration by coherent submodules whose successive quotients are direct images of
quasi-coherent sheaves of ideals on reduced closed subspaces with irreducible space of points.

The proof is a Noetherian induction on the support of `F`, run over the closed subsets of
`|X|`, which is a Noetherian topological space.  Three cases occur.

* The support is empty.  Then `F` is zero and the empty filtration works.
* The support is reducible, say contained in `Z ∪ Z'` with both pieces strictly smaller.  Then
  Stacks 07UP splits `F` into a short exact sequence of coherent modules supported in `Z'` and
  in `Z` respectively, the inductive hypothesis applies to both, and the two filtrations are
  spliced.
* The support `T` is irreducible.  Let `J` be the ideal of the reduced closed subspace on `T`.
  By Stacks 07UK some power `Jⁿ` kills `F`, and the filtration `F ⊇ J F ⊇ … ⊇ Jⁿ F = 0`, whose
  successive quotients are killed by `J`, reduces the problem to a module `C` killed by `J`.
  If the support of `C` is strictly smaller than `T` the inductive hypothesis applies.
  Otherwise the scheme-theoretic support of `C` is the reduced closed subspace `i : Z → X` on
  `T`, and Stacks 07UQ gives an injection `i_*(I^{⊕ r}) → C` whose cokernel is supported on a
  proper closed subset of `T`: the direct sum is filtered by its `r` summands `i_*I`, and the
  cokernel by the inductive hypothesis.

The splicing is carried out in the generality in which it is true: a filtration of a subobject
`A` of `M` concatenates with a filtration of `M / A` to a filtration of `M`, in any abelian
category.  That is the `Splice` section below; it uses only
`StacksCore.CategoryTheory.Abelian.Subobject`.

## Main definitions

* `AlgebraicGeometry.Space.IsIdealPushforward` is the property of a module of being isomorphic
  to the direct image of a quasi-coherent sheaf of ideals on an integral closed subspace, that
  is, of being a possible successive quotient of the filtration of Stacks 07UR.
* `AlgebraicGeometry.Space.HasTagFiltration` is the filtration of Stacks 07UR as a structure,
  which is the form the splicing operates on.

## Main results

* `AlgebraicGeometry.Space.Splice.Filtration.splice`, `ofShortExact` and `biproductConst`:
  splicing filtrations along a short exact sequence, in any abelian category, and the
  filtration of a direct sum of copies of an object by its summands.
* `AlgebraicGeometry.Space.le_annihilatorIdealSheaf_cokernel`: a sheaf of ideals annihilates the
  cokernel of a map whose image contains its products with the target; in particular `J`
  annihilates `F / J F` and `Jᵏ F / Jᵏ⁺¹ F`.
* `AlgebraicGeometry.Space.schemeTheoreticSupport_eq_reducedClosedSubspace`: a coherent module
  killed by the ideal of the reduced closed subspace on its support has that subspace as
  scheme-theoretic support (Morphisms of Spaces, Lemma 67.14.1).
* `AlgebraicGeometry.Space.hasTagFiltration_of_le_annihilatorIdealSheaf` and
  `AlgebraicGeometry.Space.hasTagFiltration_of_isIrreducible`: the irreducible-support case.
* `AlgebraicGeometry.Space.hasTagFiltration_of_isCoherent`: the Noetherian induction.
* `AlgebraicGeometry.Space.hasIdealDevissage_of_isCoherent` is **Stacks 07UR**.

## References

* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 07UP](https://stacks.math.columbia.edu/tag/07UP)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### Filtrations by subobjects with prescribed quotients

The abstract machinery for assembling the filtration of Stacks 07UR: a filtration of `M` whose
terms satisfy a predicate `Q` and whose successive quotients satisfy a predicate `P`, together
with the operations the proof performs on such filtrations — transport along an isomorphism,
and splicing a filtration of a subobject `A` of `M` with a filtration of `M / A`. -/

namespace Splice

open CategoryTheory.Subobject CategoryTheory.Abelian.Subobject

variable {C : Type*} [Category* C] [Abelian C]

/-- A predicate on objects that is invariant under isomorphism. -/
def IsoClosed (P : C → Prop) : Prop := ∀ {A B : C}, (A ≅ B) → P A → P B

/-- `Step P U V` says that `U ≤ V` and that the quotient of the subobject `V` by the subobject
`U` of an object `M` satisfies the predicate `P`. -/
def Step {M : C} (P : C → Prop) (U V : Subobject M) : Prop :=
  ∃ h : U ≤ V, P (cokernel (Subobject.ofLE U V h))

/-- A finite filtration of `M` by subobjects, starting at a zero subobject and ending at `M`
itself, whose terms satisfy `Q` and whose successive quotients satisfy `P`.  The index runs
over all of `ℕ`, with the length recorded separately. -/
structure Filtration (Q P : C → Prop) (M : C) where
  /-- The length of the filtration. -/
  len : ℕ
  /-- The terms of the filtration. -/
  sub : ℕ → Subobject M
  /-- The filtration is increasing. -/
  mono : Monotone sub
  /-- The filtration starts at a zero subobject. -/
  isZero : IsZero ((sub 0 : C))
  /-- The filtration ends at `M`. -/
  isIso : IsIso (sub len).arrow
  /-- Every term satisfies `Q`. -/
  term : ∀ k, Q ((sub k : C))
  /-- Every successive quotient satisfies `P`. -/
  quot : ∀ k, k < len → Step P (sub k) (sub (k + 1))

/-- The identity is a cokernel of a morphism out of a zero object. -/
def isColimitCokernelCoforkId {X Y : C} (f : X ⟶ Y) (h : IsZero X) :
    IsColimit (CokernelCofork.ofπ (f := f) (𝟙 Y) (by rw [h.eq_zero_of_src f, zero_comp])) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun {_} g' _ => g')
    (fun {_} _ _ => Category.id_comp _) (fun {_} _ _ m hm => by simpa using hm)

/-- The cokernel of a morphism out of a zero object is its target. -/
def cokernelIsoOfIsZeroSrc {X Y : C} (f : X ⟶ Y) (h : IsZero X) : cokernel f ≅ Y :=
  (cokernelIsCokernel f).coconePointUniqueUpToIso (isColimitCokernelCoforkId f h)

variable {Q P : C → Prop}

/-- A zero object has the one-term filtration. -/
def Filtration.ofIsZero (hQ : IsoClosed Q) {M : C} (h : IsZero M) (hQM : Q M) :
    Filtration Q P M where
  len := 0
  sub _ := ⊤
  mono := monotone_const
  isZero := h.of_iso (asIso (⊤ : Subobject M).arrow)
  isIso := (isIso_arrow_iff_eq_top (⊤ : Subobject M)).2 rfl
  term _ := hQ (asIso (⊤ : Subobject M).arrow).symm hQM
  quot k hk := absurd hk (Nat.not_lt_zero k)

/-- A subobject with a zero underlying object is the bottom subobject. -/
theorem eq_bot_of_isZero {M : C} (U : Subobject M) (h : IsZero ((U : C))) : U = ⊥ := by
  rw [← Subobject.mk_arrow U, Subobject.mk_eq_bot_iff_zero]
  exact h.eq_zero_of_src _

/-- Transport of a step along a monomorphism. -/
theorem step_map (hP : IsoClosed P) {M N : C} (n : N ⟶ M) [Mono n] {U V : Subobject N}
    (h : Step P U V) :
    Step P ((Subobject.map n).obj U) ((Subobject.map n).obj V) := by
  obtain ⟨hUV, hq⟩ := h
  exact ⟨(Subobject.map n).monotone hUV, hP (cokernelOfLEMapIso n hUV).symm hq⟩

/-- Transport of a step along an epimorphism. -/
theorem step_pullback (hP : IsoClosed P) {M E : C} (q : M ⟶ E) [Epi q]
    {U V : Subobject E} (h : Step P U V) :
    Step P ((Subobject.pullback q).obj U) ((Subobject.pullback q).obj V) := by
  obtain ⟨hUV, hq⟩ := h
  exact ⟨(Subobject.pullback q).monotone hUV, hP (cokernelOfLEPullbackIso q hUV).symm hq⟩

/-- Transport of a filtration along an isomorphism of the ambient object. -/
def Filtration.ofIso (hQ : IsoClosed Q) (hP : IsoClosed P) {M N : C} (e : M ≅ N)
    (F : Filtration Q P M) : Filtration Q P N where
  len := F.len
  sub k := (Subobject.map e.hom).obj (F.sub k)
  mono _ _ h := (Subobject.map e.hom).monotone (F.mono h)
  isZero := F.isZero.of_iso (mapObjIso e.hom (F.sub 0))
  isIso := by
    rw [isIso_arrow_iff_eq_top, (isIso_arrow_iff_eq_top (F.sub F.len)).1 F.isIso,
      Subobject.map_top, Subobject.mk_eq_top_of_isIso]
  term k := hQ (mapObjIso e.hom (F.sub k)).symm (F.term k)
  quot k hk := step_map hP e.hom (F.quot k hk)

/-- The preimage of a subobject along an epimorphism satisfies an extension-closed,
isomorphism-closed `Q` as soon as the kernel and the subobject do. -/
theorem q_pullback (hQ : IsoClosed Q)
    (hQext : ∀ T : ShortComplex C, T.ShortExact → Q T.X₁ → Q T.X₃ → Q T.X₂)
    {M E : C} (g : M ⟶ E) [Epi g] (hker : Q (((Subobject.pullback g).obj ⊥ : C)))
    (Y : Subobject E) (hY : Q ((Y : C))) : Q (((Subobject.pullback g).obj Y : C)) := by
  have hz : IsZero (((⊥ : Subobject E) : C)) :=
    (isZero_zero C).of_iso Subobject.botCoeIsoZero
  have hcol := isColimitPullbackπCokernelCofork g (bot_le : (⊥ : Subobject E) ≤ Y)
  refine hQext (ShortComplex.mk
    (Subobject.ofLE _ _ ((Subobject.pullback g).monotone (bot_le : (⊥ : Subobject E) ≤ Y)))
    (pullbackπ g Y ≫ cokernel.π (Subobject.ofLE (⊥ : Subobject E) Y bot_le))
    (by rw [ofLE_pullback_comp_pullbackπ_assoc g (bot_le : (⊥ : Subobject E) ≤ Y),
      cokernel.condition, comp_zero])) ?_ hker ?_
  · exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ hcol)
      inferInstance (epi_of_isColimit_cofork hcol)
  · exact hQ (cokernelIsoOfIsZeroSrc _ (hz.of_iso (Iso.refl _))).symm hY

section Concatenation

variable {M : C} (A : Subobject M) (a : ℕ) (s₁ : ℕ → Subobject ((A : C)))
  (s₂ : ℕ → Subobject (cokernel A.arrow))

/-- The concatenation of a family of subobjects of a subobject `A` of `M` with a family of
subobjects of `M / A`, as a family of subobjects of `M`. -/
def spliceSub : ℕ → Subobject M := fun k =>
  if k ≤ a then (Subobject.map A.arrow).obj (s₁ k)
  else (Subobject.pullback (cokernel.π A.arrow)).obj (s₂ (k - a))

/-- Below the cut-off the concatenation is the image of the first family. -/
theorem spliceSub_of_le (k : ℕ) (h : k ≤ a) :
    spliceSub A a s₁ s₂ k = (Subobject.map A.arrow).obj (s₁ k) := by
  simp only [spliceSub, h, ite_true]

/-- The preimage of the bottom subobject along `M ⟶ M / A` is `A`. -/
theorem pullback_cokernelπ_bot :
    (Subobject.pullback (cokernel.π A.arrow)).obj ⊥ = A := by
  rw [Subobject.pullback_bot, ← imageSubobject_eq_kernelSubobject, imageSubobject_mono,
    Subobject.mk_arrow]

/-- Above the cut-off the concatenation is the preimage of the second family; at the cut-off
itself the two descriptions agree, which is where the first family reaching `⊤` and the second
starting at `⊥` are used. -/
theorem spliceSub_of_ge (h₁ : s₁ a = ⊤) (h₂ : s₂ 0 = ⊥) (k : ℕ) (h : a ≤ k) :
    spliceSub A a s₁ s₂ k =
      (Subobject.pullback (cokernel.π A.arrow)).obj (s₂ (k - a)) := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rw [spliceSub_of_le A a s₁ s₂ a le_rfl, h₁, map_arrow_top, Nat.sub_self, h₂,
      pullback_cokernelπ_bot]
  · simp only [spliceSub, show ¬ k ≤ a by omega, ite_false]

end Concatenation

/-- Splicing a filtration of a subobject `A` of `M` with a filtration of `M / A` gives a
filtration of `M`. -/
def Filtration.splice (hQ : IsoClosed Q) (hP : IsoClosed P)
    (hQext : ∀ T : ShortComplex C, T.ShortExact → Q T.X₁ → Q T.X₃ → Q T.X₂)
    {M : C} (A : Subobject M) (F₁ : Filtration Q P ((A : C)))
    (F₂ : Filtration Q P (cokernel A.arrow)) : Filtration Q P M := by
  have h₁ : F₁.sub F₁.len = ⊤ := (isIso_arrow_iff_eq_top _).1 F₁.isIso
  have h₂ : F₂.sub 0 = ⊥ := eq_bot_of_isZero _ F₂.isZero
  have hle := spliceSub_of_le A F₁.len F₁.sub F₂.sub
  have hge := spliceSub_of_ge A F₁.len F₁.sub F₂.sub h₁ h₂
  have hA : Q ((A : C)) :=
    hQ (asIso (⊤ : Subobject ((A : C))).arrow) (h₁ ▸ F₁.term F₁.len)
  refine
    { len := F₁.len + F₂.len
      sub := spliceSub A F₁.len F₁.sub F₂.sub
      mono := monotone_nat_of_le_succ fun k => ?_
      isZero := ?_
      isIso := ?_
      term := fun k => ?_
      quot := fun k hk => ?_ }
  · by_cases hk : k + 1 ≤ F₁.len
    · rw [hle k (by omega), hle (k + 1) hk]
      exact (Subobject.map A.arrow).monotone (F₁.mono (Nat.le_succ k))
    · rw [hge k (by omega), hge (k + 1) (by omega)]
      exact (Subobject.pullback _).monotone (F₂.mono (by omega))
  · rw [hle 0 (Nat.zero_le _)]
    exact F₁.isZero.of_iso (mapObjIso A.arrow (F₁.sub 0))
  · rw [hge (F₁.len + F₂.len) (by omega), Nat.add_sub_cancel_left, isIso_arrow_iff_eq_top,
      (isIso_arrow_iff_eq_top (F₂.sub F₂.len)).1 F₂.isIso, Subobject.pullback_top]
  · by_cases hk : k ≤ F₁.len
    · rw [hle k hk]
      exact hQ (mapObjIso A.arrow (F₁.sub k)).symm (F₁.term k)
    · rw [hge k (by omega)]
      exact q_pullback hQ hQext _ (by rw [pullback_cokernelπ_bot]; exact hA) _ (F₂.term _)
  · by_cases hk' : k + 1 ≤ F₁.len
    · rw [hle k (by omega), hle (k + 1) hk']
      exact step_map hP A.arrow (F₁.quot k (by omega))
    · have hge' : F₁.len ≤ k := by omega
      rw [hge k hge', hge (k + 1) (by omega), Nat.succ_sub hge']
      exact step_pullback hP _ (F₂.quot (k - F₁.len) (by omega))

/-- Splicing a filtration of the source of a monomorphism with a filtration of its cokernel. -/
def Filtration.ofMono (hQ : IsoClosed Q) (hP : IsoClosed P)
    (hQext : ∀ T : ShortComplex C, T.ShortExact → Q T.X₁ → Q T.X₃ → Q T.X₂)
    {A M : C} (i : A ⟶ M) [Mono i] (F₁ : Filtration Q P A)
    (F₂ : Filtration Q P (cokernel i)) : Filtration Q P M :=
  Filtration.splice hQ hP hQext (Subobject.mk i)
    (F₁.ofIso hQ hP (Subobject.underlyingIso i).symm)
    (F₂.ofIso hQ hP (cokernel.mapIso i (Subobject.mk i).arrow
      (Subobject.underlyingIso i).symm (Iso.refl M) (by simp)))

/-- Splicing along a short exact sequence. -/
def Filtration.ofShortExact (hQ : IsoClosed Q) (hP : IsoClosed P)
    (hQext : ∀ T : ShortComplex C, T.ShortExact → Q T.X₁ → Q T.X₃ → Q T.X₂)
    (T : ShortComplex C) (hT : T.ShortExact) (F₁ : Filtration Q P T.X₁)
    (F₃ : Filtration Q P T.X₃) : Filtration Q P T.X₂ :=
  haveI : Mono T.f := hT.mono_f
  haveI : Epi T.g := hT.epi_g
  Filtration.ofMono hQ hP hQext T.f F₁
    (F₃.ofIso hQ hP (hT.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)))

/-- The data of a filtration, in existential shape. -/
theorem Filtration.exists_spec {M : C} (F : Filtration Q P M) :
    ∃ (n : ℕ) (G : Fin (n + 1) → Subobject M) (hG : Monotone G),
      IsZero ((G 0 : C)) ∧ IsIso (G (Fin.last n)).arrow ∧
      (∀ j : Fin (n + 1), Q ((G j : C))) ∧
      ∀ j : Fin n, ∃ (W : C) (q : ((G j.succ : C)) ⟶ W)
        (hq : Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ) ≫ q = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ q hq)) ∧ P W := by
  refine ⟨F.len, fun j => F.sub j.val, fun i j h => F.mono h, F.isZero, F.isIso,
    fun j => F.term _, fun j => ?_⟩
  obtain ⟨h, hPq⟩ := F.quot j.val j.isLt
  exact ⟨cokernel (Subobject.ofLE (F.sub j.val) (F.sub (j.val + 1)) h), cokernel.π _,
    cokernel.condition _, ⟨cokernelIsCokernel _⟩, hPq⟩

/-- The data of a filtration, with each successive quotient replaced by a chosen isomorphic
representative satisfying `R`. -/
theorem Filtration.exists_spec_of {M : C} (F : Filtration Q P M) (R : C → Prop)
    (hPR : ∀ W : C, P W → ∃ W' : C, R W' ∧ Nonempty (W ≅ W')) :
    ∃ (n : ℕ) (G : Fin (n + 1) → Subobject M) (hG : Monotone G),
      IsZero ((G 0 : C)) ∧ IsIso (G (Fin.last n)).arrow ∧
      (∀ j : Fin (n + 1), Q ((G j : C))) ∧
      ∀ j : Fin n, ∃ W : C, R W ∧ ∃ (q : ((G j.succ : C)) ⟶ W)
        (hq : Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ) ≫ q = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ q hq)) := by
  obtain ⟨n, G, hG, hzero, hiso, hterm, hstep⟩ := F.exists_spec
  refine ⟨n, G, hG, hzero, hiso, hterm, fun j => ?_⟩
  obtain ⟨W, q, hq, ⟨hcolimit⟩, hPW⟩ := hstep j
  obtain ⟨W', hR, ⟨e⟩⟩ := hPR W hPW
  refine ⟨W', hR, q ≫ e.hom, by rw [← Category.assoc, hq, zero_comp], ?_⟩
  exact ⟨IsColimit.ofIsoColimit hcolimit (Cofork.ext e rfl)⟩

/-- The filtration of length one: `0 ⊆ M`, whose only successive quotient is `M` itself. -/
def Filtration.single (hQ : IsoClosed Q) (hP : IsoClosed P) (hQ₀ : ∀ Z : C, IsZero Z → Q Z)
    {M : C} (hQM : Q M) (hPM : P M) : Filtration Q P M where
  len := 1
  sub k := if k = 0 then ⊥ else ⊤
  mono i j h := by
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact bot_le
    · have hj : j ≠ 0 := by omega
      simp only [hi, hj, if_false, le_refl]
  isZero := (isZero_zero C).of_iso (Subobject.botCoeIsoZero (B := M))
  isIso := (isIso_arrow_iff_eq_top (⊤ : Subobject M)).2 rfl
  term k := by
    split_ifs
    · exact hQ₀ _ ((isZero_zero C).of_iso Subobject.botCoeIsoZero)
    · exact hQ (asIso (⊤ : Subobject M).arrow).symm hQM
  quot k hk := by
    obtain rfl : k = 0 := by omega
    change Step P (⊥ : Subobject M) ⊤
    refine ⟨bot_le, hP ?_ hPM⟩
    exact (asIso (⊤ : Subobject M).arrow).symm ≪≫ (cokernelIsoOfIsZeroSrc _
      ((isZero_zero C).of_iso Subobject.botCoeIsoZero)).symm

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- A biproduct of `r` copies of `M` is filtered by `r` copies of the filtration of length one
of `M`: the inclusion of the last summand has the biproduct of the others as cokernel. -/
def Filtration.biproductConst (hQ : IsoClosed Q) (hP : IsoClosed P)
    (hQext : ∀ T : ShortComplex C, T.ShortExact → Q T.X₁ → Q T.X₃ → Q T.X₂)
    (hQ₀ : ∀ Z : C, IsZero Z → Q Z) {M : C} (hQM : Q M) (hPM : P M) :
    ∀ r : ℕ, Filtration Q P (⨁ fun _ : Fin r => M)
  | 0 => by
    have hz : IsZero (⨁ fun _ : Fin 0 => M) :=
      (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j => j.elim0)
    exact Filtration.ofIsZero hQ hz (hQ₀ _ hz)
  | r + 1 =>
    Filtration.ofMono hQ hP hQext (biproduct.ι (fun _ : Fin (r + 1) => M) (Fin.last r))
      (Filtration.single hQ hP hQ₀ hQM hPM)
      ((Filtration.biproductConst hQ hP hQext hQ₀ hQM hPM r).ofIso hQ hP
        (biproduct.whiskerEquiv (finSuccAboveEquiv (Fin.last r)) (fun _ => Iso.refl M) ≪≫
          (cokernelBiproductιIso (fun _ : Fin (r + 1) => M) (Fin.last r)).symm))

end Splice

/-! ### The dévissage filtration -/

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪_X`-modules with sections in the universe of the schemes form an abelian category.

This is `SheafOfModules.instAbelian`, which instance search finds; it is named here so that the
universe levels of `AlgebraicGeometry.Space.Splice.Filtration` can be pinned by it. -/
abbrev spaceModulesAbelian (X : AlgebraicSpaces B S hS) :
    Abelian (Modules.{u, u} B S hS X.1 X.2) :=
  SheafOfModules.instAbelian _

/-- The support of an `𝒪_X`-module, as a set of points of `X`. -/
abbrev moduleSupportSet (X : AlgebraicSpaces B S hS) (F : Modules.{u, m} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)

/-- The support of an `𝒪_X`-module read through the abelian sheaf of
`AlgebraicGeometry.Space.moduleAddSheaf`, which is how Stacks 07UP states it, is the same
set. -/
theorem moduleSupportSet_eq_supportOfSheaf_moduleAddSheaf (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, m} B S hS X.1 X.2) :
    moduleSupportSet B S hS X F =
      supportOfSheaf B S hS X.1 (moduleAddSheaf B S hS X.1 X.2 F) := rfl

/-- The support of a coherent module on an algebraic space is closed: a coherent module is of
finite type on the site, and the support of such a module is closed by Stacks 07TZ. -/
theorem isClosed_moduleSupportSet (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    IsClosed (moduleSupportSet B S hS X F) :=
  let := hF
  let := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F
  isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 F

/-- The direct images of quasi-coherent sheaves of ideals on integral closed subspaces: the
objects that occur as the successive quotients of the filtration of Stacks 07UR. -/
def IsIdealPushforwardTarget (X : AlgebraicSpaces B S hS)
    (W : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
    IsReducedIrreducible B S hS Z ∧
      ∃ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ),
        W = (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules

/-- The property, of a module on `X`, of being isomorphic to the direct image of a
quasi-coherent sheaf of ideals on an integral closed subspace of `X`. -/
def IsIdealPushforward (X : AlgebraicSpaces B S hS) (W : Modules.{u, u} B S hS X.1 X.2) :
    Prop :=
  ∃ W' : Modules.{u, u} B S hS X.1 X.2,
    IsIdealPushforwardTarget B S hS X W' ∧ Nonempty (W ≅ W')

/-- `AlgebraicGeometry.Space.IsIdealPushforward` is invariant under isomorphism. -/
theorem isoClosed_isIdealPushforward (X : AlgebraicSpaces B S hS) :
    Splice.IsoClosed (IsIdealPushforward B S hS X) := by
  intro W W' e hW
  obtain ⟨W'', hW'', ⟨f⟩⟩ := hW
  exact ⟨W'', hW'', ⟨e.symm.trans f⟩⟩

/-- Coherence of modules on an algebraic space is invariant under isomorphism, in the shape the
splicing machinery consumes. -/
theorem isoClosed_isCoherent (X : AlgebraicSpaces B S hS) :
    Splice.IsoClosed (isCoherent.{u, u} B S hS X.1 X.2) :=
  fun e hM => isCoherent_of_iso B S hS X.2 e hM

/-- `M` carries the filtration of Stacks 07UR: coherent terms whose successive quotients are
isomorphic to direct images of quasi-coherent sheaves of ideals on integral closed
subspaces. -/
abbrev HasTagFiltration (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  Nonempty (@Splice.Filtration.{u + 1, u + 1} (Modules.{u, u} B S hS X.1 X.2) _
    (spaceModulesAbelian B S hS X) (isCoherent.{u, u} B S hS X.1 X.2)
    (IsIdealPushforward B S hS X) M)

/-- The conclusion of Stacks 07UR follows from a filtration by coherent subobjects whose
successive quotients are isomorphic to direct images of quasi-coherent sheaves of ideals on
integral closed subspaces: the isomorphism is absorbed into the choice of the cokernel
projection. -/
theorem hasIdealDevissage_of_hasTagFiltration (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (F : HasTagFiltration B S hS X M) :
    HasIdealDevissage B S hS X M := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  obtain ⟨F⟩ := F
  obtain ⟨n, G, hG, hzero, hiso, hcoh, hstep⟩ :=
    F.exists_spec_of (IsIdealPushforwardTarget B S hS X) (fun _ h => h)
  refine ⟨n, G, hG, hzero, hiso, hcoh, fun j => ?_⟩
  obtain ⟨W, ⟨Z, hZ, hint, I, hWeq⟩, q, hq, hcolimit⟩ := hstep j
  subst hWeq
  exact ⟨Z, hZ, hint, I, q, hq, hcolimit⟩

/-! ### Supports of submodules and quotient modules -/

/-- The support of a submodule is contained in the support of the module: the forgetful functor
to abelian sheaves preserves finite limits, hence monomorphisms, and the statement for abelian
sheaves is `AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono`. -/
theorem moduleSupportSet_subset_of_mono (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) (hf : Mono f) :
    moduleSupportSet B S hS X M ⊆ moduleSupportSet B S hS X N := by
  have _ := hf
  have hmono : Mono ((SheafOfModules.toSheaf _).map f) :=
    preserves_mono_of_preservesLimit _ f
  exact @supportOfSheaf_subset_of_mono B S hS X.1 X.2 _ _
    ((SheafOfModules.toSheaf _).map f) hmono

/-- The support of a quotient module is contained in the support of the module: an epimorphism
of modules is locally surjective, and the statement for abelian sheaves is
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_isLocallySurjective`. -/
theorem moduleSupportSet_subset_of_epi (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) (hf : Epi f) :
    moduleSupportSet B S hS X N ⊆ moduleSupportSet B S hS X M := by
  have _ := hf
  have hsurj : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map f) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi f
  exact @supportOfSheaf_subset_of_isLocallySurjective B S hS X.1 X.2 _ _
    ((SheafOfModules.toSheaf _).map f) hsurj

/-! ### Modules annihilated by a sheaf of ideals -/

/-- **A sheaf of ideals annihilates the cokernel of a morphism whose image contains every
product of a section of the ideal with a section of the target.**  A section of the cokernel is
locally the image of a section `s` of the target, and the product of a section of the ideal with
`s` comes from the source, so it dies in the cokernel; the cokernel is a sheaf. -/
theorem le_annihilatorIdealSheaf_cokernel (X : AlgebraicSpaces B S hS)
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {A M : Modules.{u, u} B S hS X.1 X.2} (φ : A ⟶ M)
    (h : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (b : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj W),
      b ∈ J.obj W → ∀ s : M.val.obj W, ∃ y : A.val.obj W, φ.val.app W y = b • s) :
    J ≤ annihilatorIdealSheaf B S hS X (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ) := by
  intro U a ha W g t
  have hb := J.map_mem g ha
  obtain ⟨Sv, hSv, hcov⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ) t
  refine (Presheaf.IsSheaf.isSeparated
    (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).isSheaf) W.unop Sv hSv _ 0 ?_
  intro Y f hf
  obtain ⟨s, hs⟩ := hcov f hf
  obtain ⟨y, hy⟩ := h (op Y) _ (J.map_mem f.op hb) s
  rw [map_zero]
  refine ((cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).val.map_smul f.op _ t).trans ?_
  rw [show (cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ).val.map f.op t =
    (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ).val.app (op Y) s from hs.symm]
  refine (((cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) φ).val.app (op Y)).hom.map_smul
    _ s).symm.trans ?_
  refine (congrArg _ hy.symm).trans ?_
  exact congrArg (fun k : A ⟶ cokernel (C := Modules.{u, u} B S hS X.1 X.2) φ =>
    k.val.app (op Y) y) (cokernel.condition (C := Modules.{u, u} B S hS X.1 X.2) φ)

/-- **A sheaf of ideals `J` annihilates `F / J F`.** -/
theorem le_annihilatorIdealSheaf_cokernel_idealPowModuleι_one (X : AlgebraicSpaces B S hS)
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    J ≤ annihilatorIdealSheaf B S hS X
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (idealPowModuleι J 1 F)) := by
  refine le_annihilatorIdealSheaf_cokernel B S hS X J _ fun W b hb s => ?_
  exact ⟨⟨b • s, smul_mem_idealPowSubmodule J
    (SheafOfModules.Submodule.le_iff.1 (Stacks.Sites.idealPow_one J).ge W hb) s⟩, rfl⟩

/-- **A sheaf of ideals `J` annihilates the graded piece `Jᵏ F / Jᵏ⁺¹ F`.** -/
theorem le_annihilatorIdealSheaf_cokernel_idealPowModuleSuccHom (X : AlgebraicSpaces B S hS)
    (J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (F : Modules.{u, u} B S hS X.1 X.2) (k : ℕ) :
    J ≤ annihilatorIdealSheaf B S hS X
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) (idealPowModuleSuccHom J k F)) := by
  refine le_annihilatorIdealSheaf_cokernel B S hS X J _ fun W b hb s => ?_
  have hb1 : b ∈ (Stacks.Sites.idealPow J 1).obj W :=
    SheafOfModules.Submodule.le_iff.1 (Stacks.Sites.idealPow_one J).ge W hb
  have hmem := idealPowSmul_idealPowSubmodule_le J 1 k F W
    (Stacks.Sites.smul_mem_idealPowSmul J hb1 s.2)
  rw [add_comm] at hmem
  exact ⟨⟨b • s.1, hmem⟩, rfl⟩

/-- The support of a coherent module is the set of points of its scheme-theoretic support. -/
private theorem moduleSupportSet_eq_range_pointsMap_schemeTheoreticSupport
    (X : AlgebraicSpaces B S hS) (C : Modules.{u, u} B S hS X.1 X.2)
    (hC : IsCoherent B S hS X.1 X.2 C) :
    moduleSupportSet B S hS X C = Set.range (pointsMap B S hS
      (schemeTheoreticSupport B S hS X C).toFunctor (schemeTheoreticSupport B S hS X C).ι) :=
  let := hC
  supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X C
    hC.toIsQuasicoherentOnSite (isFiniteTypeOnSite_of_isCoherentOnSite B S hS X C)

/-- **A coherent module killed by the ideal of the reduced closed subspace on its support has
that reduced closed subspace as scheme-theoretic support** (Morphisms of Spaces, Lemma 67.14.1).
Its scheme-theoretic support is a closed subspace whose points are the support of the module, by
part (4) of Stacks 07U0; it lies in the reduced closed subspace on the support, whose defining
ideal annihilates the module, and contains it by Stacks 03JJ, the reduced closed subspace being
reduced with the same points. -/
theorem schemeTheoreticSupport_eq_reducedClosedSubspace (X : AlgebraicSpaces B S hS)
    (C : Modules.{u, u} B S hS X.1 X.2) (hC : IsCoherent B S hS X.1 X.2 C)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (hann : reducedIdealSheaf B S hS X T hT ≤ annihilatorIdealSheaf B S hS X C)
    (hsupp : moduleSupportSet B S hS X C = T) :
    schemeTheoreticSupport B S hS X C = reducedClosedSubspace B S hS X.1 X.2 T hT := by
  let := hC
  obtain ⟨hZ, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X C
    hC.toIsQuasicoherentOnSite hC.toIsCoherentOnSite.isFiniteType
  have hpts := moduleSupportSet_eq_range_pointsMap_schemeTheoreticSupport B S hS X C hC
  have hWc := isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 T hT
  refine le_antisymm (sInf_le ⟨hWc, hann⟩) ?_
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS X.2 hWc.1
    (schemeTheoreticSupport B S hS X C) hZ
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.1 X.2 T hT)
    (reducedClosedSubspace B S hS X.1 X.2 T hT).ι).2 (by
      rw [range_pointsMap_ι_reducedClosedSubspace, ← hpts]
      exact hsupp.ge)
  exact Subfunctor.le_of_comp_eq_ι g hg

/-- **A coherent module with irreducible support killed by the ideal of the reduced closed
subspace on its support has a reduced scheme-theoretic support with irreducible space of
points**: that support is the reduced closed subspace on the support of the module, by
`AlgebraicGeometry.Space.schemeTheoreticSupport_eq_reducedClosedSubspace`, and its map on points
is a topological embedding with image the support. -/
theorem isReducedIrreducible_schemeTheoreticSupport (X : AlgebraicSpaces B S hS)
    (C : Modules.{u, u} B S hS X.1 X.2) (hC : IsCoherent B S hS X.1 X.2 C)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTirr : IsIrreducible T)
    (hann : reducedIdealSheaf B S hS X T hT ≤ annihilatorIdealSheaf B S hS X C)
    (hsupp : moduleSupportSet B S hS X C = T) :
    IsReducedIrreducible B S hS (schemeTheoreticSupport B S hS X C) := by
  rw [schemeTheoreticSupport_eq_reducedClosedSubspace B S hS X C hC T hT hann hsupp]
  have hWc := isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 T hT
  have hrange := range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 T hT
  refine ⟨hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.1 X.2 T hT, ?_⟩
  have hpre := preirreducibleSpace_points_of_isPreirreducible_range_pointsMap B S hS X.2 _
    (isImmersion_of_isClosedImmersion B S hS hWc.2) (by rw [hrange]; exact hTirr.2)
  obtain ⟨x, hx⟩ := hTirr.1
  rw [← hrange] at hx
  obtain ⟨y, -⟩ := hx
  exact { toPreirreducibleSpace := hpre, toNonempty := ⟨y⟩ }

/-! ### The irreducible-support case -/

/-- A zero module on an algebraic space is coherent. -/
theorem isCoherent_of_isZero (X : AlgebraicSpaces B S hS) {Z : Modules.{u, u} B S hS X.1 X.2}
    (hZ : IsZero Z) : IsCoherent B S hS X.1 X.2 Z :=
  let := Stacks.SheafOfModules.isCoherentOnSite_zero hZ
  isCoherent_of_isCoherentOnSite B S hS X.1 X.2 Z

/-- **A summand of a coherent direct sum of copies of a module is coherent**: the summand is the
kernel of the endomorphism `𝟙 - ι₀ π₀` of the direct sum, and a kernel of a map of coherent
modules is coherent by Stacks 07UC. -/
theorem isCoherent_of_isCoherent_biproductConst (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (r : ℕ) (hr : 0 < r)
    (h : IsCoherent B S hS X.1 X.2 (⨁ fun _ : Fin r => M)) : IsCoherent B S hS X.1 X.2 M := by
  let f : Fin r → Modules.{u, u} B S hS X.1 X.2 := fun _ => M
  let j : Fin r := ⟨0, hr⟩
  let e : (⨁ f) ⟶ (⨁ f) := 𝟙 _ - biproduct.π f j ≫ biproduct.ι f j
  have hw : biproduct.ι f j ≫ e = 0 := by
    simp only [e, Preadditive.comp_sub, Category.comp_id, biproduct.ι_π_self_assoc, sub_self]
  have hlim : IsLimit (KernelFork.ofι (biproduct.ι f j) hw) :=
    KernelFork.IsLimit.ofι _ _ (fun g _ => g ≫ biproduct.π f j)
      (fun g hg => by
        have h1 : g ≫ e = 0 := hg
        simp only [e, Preadditive.comp_sub, Category.comp_id] at h1
        rw [Category.assoc]
        exact (sub_eq_zero.1 h1).symm)
      (fun g _ m hm => by rw [← hm, Category.assoc, biproduct.ι_π_self, Category.comp_id])
  exact isCoherent_of_iso B S hS X.2
    ((limit.isLimit _).conePointUniqueUpToIso hlim)
    (isCoherent_kernel B S hS X.1 X.2 h h e)

/-- The direct image of a quasi-coherent sheaf of ideals on a reduced closed subspace with
irreducible space of points is a possible successive quotient of the filtration of
Stacks 07UR. -/
theorem isIdealPushforward_modulePushforward (X : AlgebraicSpaces B S hS) {Z : Subfunctor X.1}
    (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) :
    IsIdealPushforward B S hS X
      ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) :=
  ⟨_, ⟨Z, hZ, hint, I, rfl⟩, ⟨Iso.refl _⟩⟩

/-- **Splicing along a monomorphism**, for the filtration of Stacks 07UR: a module containing a
submodule with the filtration, with quotient carrying the filtration, carries it. -/
theorem hasTagFiltration_of_mono (X : AlgebraicSpaces B S hS)
    {A M : Modules.{u, u} B S hS X.1 X.2} (i : A ⟶ M) [Mono i]
    (hA : HasTagFiltration B S hS X A) {Q : Modules.{u, u} B S hS X.1 X.2} (q : M ⟶ Q)
    (hq : i ≫ q = 0) (hcol : IsColimit (CokernelCofork.ofπ q hq))
    (hQ : HasTagFiltration B S hS X Q) : HasTagFiltration B S hS X M := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  obtain ⟨FA⟩ := hA
  obtain ⟨FQ⟩ := hQ
  exact ⟨Splice.Filtration.ofMono (isoClosed_isCoherent B S hS X)
    (isoClosed_isIdealPushforward B S hS X)
    (fun T hT h₁ h₃ => isCoherent_X₂_of_shortExact B S hS X.1 X.2 hT h₁ h₃) i FA
    (FQ.ofIso (isoClosed_isCoherent B S hS X) (isoClosed_isIdealPushforward B S hS X)
      (hcol.coconePointUniqueUpToIso (colimit.isColimit _)))⟩

/-- The filtration of Stacks 07UR is transported along an isomorphism. -/
theorem hasTagFiltration_of_iso (X : AlgebraicSpaces B S hS)
    {A M : Modules.{u, u} B S hS X.1 X.2} (e : A ≅ M) (hA : HasTagFiltration B S hS X A) :
    HasTagFiltration B S hS X M := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  obtain ⟨FA⟩ := hA
  exact ⟨FA.ofIso (isoClosed_isCoherent B S hS X) (isoClosed_isIdealPushforward B S hS X) e⟩

/-- **A direct sum of copies of the direct image of a quasi-coherent sheaf of ideals on a
reduced closed subspace with irreducible space of points carries the filtration of
Stacks 07UR**, once that direct image is coherent: one step for each copy. -/
theorem hasTagFiltration_biproductConst_modulePushforward (X : AlgebraicSpaces B S hS)
    {Z : Subfunctor X.1} (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ))
    (hI : IsCoherent B S hS X.1 X.2
      ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules))
    (r : ℕ) :
    HasTagFiltration B S hS X (⨁ fun _ : Fin r =>
      (modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  exact ⟨Splice.Filtration.biproductConst (isoClosed_isCoherent B S hS X)
    (isoClosed_isIdealPushforward B S hS X)
    (fun T hT h₁ h₃ => isCoherent_X₂_of_shortExact B S hS X.1 X.2 hT h₁ h₃)
    (fun _ hZ => isCoherent_of_isZero B S hS X hZ) hI
    (isIdealPushforward_modulePushforward B S hS X hZ hint I) r⟩

/-- **The case of a module killed by the ideal of the reduced closed subspace on an irreducible
closed set containing its support**, granted the filtration for every coherent module whose
support is strictly smaller than that set.  If the support is strictly smaller there is nothing
to do.  Otherwise the scheme-theoretic support is that reduced closed subspace `Z`, which is
reduced with `|Z|` irreducible, and Stacks 07UQ gives an injection `i_*(I^{⊕ r}) → C` whose
cokernel is supported in the image of a proper closed subset of `|Z|`: the cokernel has the
filtration, `i_*(I^{⊕ r}) = (i_*I)^{⊕ r}` has the evident one, and the two are spliced. -/
theorem hasTagFiltration_of_le_annihilatorIdealSheaf (hTop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hTop X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTirr : IsIrreducible T)
    (IH : ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G →
      moduleSupportSet B S hS X G ⊂ T → HasTagFiltration B S hS X G)
    (C : Modules.{u, u} B S hS X.1 X.2) (hC : IsCoherent B S hS X.1 X.2 C)
    (hann : reducedIdealSheaf B S hS X T hT ≤ annihilatorIdealSheaf B S hS X C)
    (hsupp : moduleSupportSet B S hS X C ⊆ T) :
    HasTagFiltration B S hS X C := by
  rcases hsupp.eq_or_ssubset with heq | hlt
  swap
  · exact IH C hC hlt
  have hint := isReducedIrreducible_schemeTheoreticSupport B S hS X C hC T hT hTirr hann heq
  obtain ⟨hZ, r, I, hIq, -, -, hsum, φ, hφ, Q, q, w, ⟨hcol⟩, T', -, hT'ne, hQsupp⟩ :=
    exists_mono_modulePushforward_idealSum_of_schemeTheoreticSupport B S hS hTop X hX C hC hint
  have hpts := moduleSupportSet_eq_range_pointsMap_schemeTheoreticSupport B S hS X C hC
  -- the support of the cokernel is strictly smaller than `T`
  have hQlt : moduleSupportSet B S hS X Q ⊂ T := by
    have hmem : ∀ z, pointsMap B S hS _ (closedSubfunctorι B S hS hZ).hom z ∈
        moduleSupportSet B S hS X C := fun z => by
      rw [hpts]
      exact ⟨z, rfl⟩
    refine hQsupp.trans_ssubset ?_
    rw [← heq]
    refine ⟨?_, fun hsub => ?_⟩
    · rintro _ ⟨z, -, rfl⟩
      exact hmem z
    · obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem T').1 hT'ne
      obtain ⟨z', hz', hzz⟩ := hsub (hmem z)
      exact hz ((pointsMap_hom_injective_of_isClosedImmersion B S hS
        (closedSubfunctorι B S hS hZ) hZ.2 hzz) ▸ hz')
  have hQcoh : IsCoherent B S hS X.1 X.2 Q :=
    isCoherent_of_iso B S hS X.2 (hcol.coconePointUniqueUpToIso (colimit.isColimit _)).symm
      (isCoherent_cokernel B S hS X.1 X.2 hsum hC φ)
  have e := modulePushforwardBiproductConstIso B S hS X (closedSubfunctorι B S hS hZ) r
    I.toSheafOfModules ≪≫ ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).mapIso
      (biproduct.isoProduct fun _ : Fin r => I.toSheafOfModules)).symm
  have _ := hφ
  exact hasTagFiltration_of_mono B S hS X φ
    (hasTagFiltration_of_iso B S hS X e (hasTagFiltration_biproductConst_modulePushforward
      B S hS X hZ hint ⟨I, hIq⟩ (isCoherent_modulePushforward_quasicoherentIdeal B S hS hX.2.2
        (closedSubfunctorι B S hS hZ) hZ.2 ⟨I, hIq⟩) r))
    q w hcol (IH Q hQcoh hQlt)

/-- **The irreducible-support case of Stacks 07UR, on a Noetherian algebraic space.**

Let `T` be the support of `F` and `J` the ideal of the reduced closed subspace on `T`.  Some
power `Jⁿ` kills `F`, by Stacks 07UK, so `F ⊇ J F ⊇ J² F ⊇ … ⊇ Jⁿ F = 0` is a finite filtration
by coherent submodules whose successive quotients are killed by `J`.  Those quotients have the
filtration of Stacks 07UR by
`AlgebraicGeometry.Space.hasTagFiltration_of_le_annihilatorIdealSheaf`, and the pieces are
spliced, from `Jⁿ F` up to `F`. -/
theorem hasTagFiltration_of_isIrreducible (hTop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hTop X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hirr : IsIrreducible (moduleSupportSet B S hS X F))
    (IH : ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G →
      moduleSupportSet B S hS X G ⊂ moduleSupportSet B S hS X F →
      HasTagFiltration B S hS X G) :
    HasTagFiltration B S hS X F := by
  have _ : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX.2.2⟩
  have hT : IsClosed (moduleSupportSet B S hS X F) := isClosed_moduleSupportSet B S hS X F hF
  set T := moduleSupportSet B S hS X F with hTdef
  set J := reducedIdealSheaf B S hS X T hT with hJdef
  have hJq : J.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_reducedIdealSheaf B S hS X T hT
  obtain ⟨n, hn⟩ := (exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus B S hS
    hTop X hX F hF J hJq).2 (idealZeroLocus_reducedIdealSheaf B S hS X T hT).ge
  have hcoh : ∀ k, IsCoherent B S hS X.1 X.2 (idealPowModule J k F) := fun k =>
    isCoherent_idealPowModule_of_isQuasicoherentOnSite B S hS X.1 X.2 J k F hF hJq
  have hsuppN : ∀ k, moduleSupportSet B S hS X (idealPowModule J k F) ⊆ T := fun k =>
    moduleSupportSet_subset_of_mono B S hS X (idealPowModuleι J k F) inferInstance
  -- splicing a coherent submodule `A` having the filtration with the quotient `M / A`, which is
  -- killed by `J` and supported in `T`
  have glue : ∀ {A M : Modules.{u, u} B S hS X.1 X.2} (i : A ⟶ M) [Mono i],
      IsCoherent B S hS X.1 X.2 A → HasTagFiltration B S hS X A →
      IsCoherent B S hS X.1 X.2 M → moduleSupportSet B S hS X M ⊆ T →
      J ≤ annihilatorIdealSheaf B S hS X (cokernel i) → HasTagFiltration B S hS X M :=
    fun i _ hA hFA hM hMT hJ =>
      hasTagFiltration_of_mono B S hS X i hFA _ (cokernel.condition _) (cokernelIsCokernel _)
        (hasTagFiltration_of_le_annihilatorIdealSheaf B S hS hTop X hX T hT hirr IH _
          (isCoherent_cokernel B S hS X.1 X.2 hA hM _) hJ
          ((moduleSupportSet_subset_of_epi B S hS X (cokernel.π i) inferInstance).trans hMT))
  -- the filtration of `Jᵏ⁺¹ F`, by descending induction on `k`
  have chain : ∀ m k : ℕ, k + m = n →
      HasTagFiltration B S hS X (idealPowModule J (k + 1) F) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
      have hbot : idealPowSubmodule J (k + 1) F = ⊥ :=
        eq_bot_iff.2 ((idealPowSubmodule_antitone J F (by omega : n ≤ k + 1)).trans hn.le)
      exact ⟨Splice.Filtration.ofIsZero (isoClosed_isCoherent B S hS X)
        (SheafOfModules.Submodule.isZero_toSheafOfModules_of_eq_bot hbot) (hcoh _)⟩
    | succ m ih =>
      intro k hk
      exact glue (idealPowModuleSuccHom J (k + 1) F) (hcoh _) (ih (k + 1) (by omega)) (hcoh _)
        (hsuppN _) (le_annihilatorIdealSheaf_cokernel_idealPowModuleSuccHom B S hS X J F (k + 1))
  exact glue (idealPowModuleι J 1 F) (hcoh _) (chain n 0 (by omega)) hF le_rfl
    (le_annihilatorIdealSheaf_cokernel_idealPowModuleι_one B S hS X J F)

/-- **The Noetherian induction of Stacks 07UR**, on the support of the module.  A module with
empty support is zero; a reducible support is split by Stacks 07UP and the two filtrations are
spliced; an irreducible support is
`AlgebraicGeometry.Space.hasTagFiltration_of_isIrreducible`. -/
theorem hasTagFiltration_of_isCoherent (hTop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hTop X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M) :
    HasTagFiltration B S hS X M := by
  let _ : Abelian (Modules.{u, u} B S hS X.1 X.2) := spaceModulesAbelian B S hS X
  have _ : TopologicalSpace.NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 hX.1 hX.2.2
  have hclosed : ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      IsClosed (moduleSupportSet B S hS X F) := fun F hF =>
    isClosed_moduleSupportSet B S hS X F hF
  have key : ∀ T : TopologicalSpace.Closeds (points B S hS X.1),
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
      moduleSupportSet B S hS X F ⊆ (T : Set (points B S hS X.1)) →
      HasTagFiltration B S hS X F := by
    intro T
    refine wellFounded_lt.induction
      (C := fun T : TopologicalSpace.Closeds (points B S hS X.1) =>
        ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
          moduleSupportSet B S hS X F ⊆ (T : Set (points B S hS X.1)) →
          HasTagFiltration B S hS X F) T ?_
    clear T
    intro T IH F hF hFT
    -- a coherent module whose support is strictly inside `T` is covered by the inductive
    -- hypothesis, applied to its own support
    have step : ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G →
        moduleSupportSet B S hS X G ⊂ (T : Set (points B S hS X.1)) →
        HasTagFiltration B S hS X G := fun G hG hGT =>
      IH ⟨moduleSupportSet B S hS X G, hclosed G hG⟩ (SetLike.coe_ssubset_coe.mp hGT) G hG
        Set.Subset.rfl
    rcases Set.eq_empty_or_nonempty (moduleSupportSet B S hS X F) with hempty | hne
    · exact ⟨Splice.Filtration.ofIsZero (isoClosed_isCoherent B S hS X)
        (isZero_of_supportOfSheaf_eq_empty B S hS X F hempty) hF⟩
    by_cases hpre : IsPreirreducible (moduleSupportSet B S hS X F)
    · exact hasTagFiltration_of_isIrreducible B S hS hTop X hX F hF ⟨hne, hpre⟩
        fun G hG hGF => step G hG (hGF.trans_le hFT)
    simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hpre
    obtain ⟨z₁, z₂, hz₁, hz₂, hcover, hn₁, hn₂⟩ := hpre
    have hunion : moduleSupportSet B S hS X F =
        moduleSupportSet B S hS X F ∩ z₁ ∪ moduleSupportSet B S hS X F ∩ z₂ := by
      rw [← Set.inter_union_distrib_left]
      exact (Set.inter_eq_left.2 hcover).symm
    have hlt₁ : moduleSupportSet B S hS X F ∩ z₁ ⊂ moduleSupportSet B S hS X F :=
      ⟨Set.inter_subset_left, fun h => hn₁ fun x hx => (h hx).2⟩
    have hlt₂ : moduleSupportSet B S hS X F ∩ z₂ ⊂ moduleSupportSet B S hS X F :=
      ⟨Set.inter_subset_left, fun h => hn₂ fun x hx => (h hx).2⟩
    obtain ⟨G', G, i, p, hip, hSE, hG', hG, hsupp', hsupp⟩ :=
      exists_shortExact_coherent_supportOfSheaf_subset B S hS X hTop hX F hF
        (moduleSupportSet B S hS X F ∩ z₁) (moduleSupportSet B S hS X F ∩ z₂)
        ((hclosed F hF).inter hz₁) ((hclosed F hF).inter hz₂) hunion
    have F₁ := step G' hG' ((hsupp'.trans_lt hlt₂).trans_le hFT)
    have F₃ := step G hG ((hsupp.trans_lt hlt₁).trans_le hFT)
    have := hSE.mono_f
    exact hasTagFiltration_of_mono B S hS X i F₁ p hip hSE.gIsCokernel F₃
  exact key ⟨moduleSupportSet B S hS X M, hclosed M hM⟩ M hM Set.Subset.rfl

/-- **Stacks Project, Tag 07UR.**  Let `X` be a Noetherian algebraic space over a scheme `S`
and let `F` be a coherent `𝒪_X`-module.  Then `F` carries a filtration

`0 = F₀ ⊆ F₁ ⊆ … ⊆ F_m = F`

by coherent submodules such that for each `j` there are a reduced closed subspace `Z_j ⊆ X`
with `|Z_j|` irreducible and a quasi-coherent sheaf of ideals `I_j ⊆ 𝒪_{Z_j}` with
`F_j / F_{j-1} ≅ (Z_j → X)_* I_j`.

The filtration is produced as a structure by
`AlgebraicGeometry.Space.hasTagFiltration_of_isCoherent` and read in this existential form by
`AlgebraicGeometry.Space.hasIdealDevissage_of_hasTagFiltration`. -/
@[stacks 07UR]
theorem hasIdealDevissage_of_isCoherent (terminal : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (noeth : IsNoetherian B S hS terminal X.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (coh : IsCoherent B S hS X.1 X.2 M) :
    HasIdealDevissage B S hS X M :=
  hasIdealDevissage_of_hasTagFiltration B S hS X M
    (hasTagFiltration_of_isCoherent B S hS terminal X noeth M coh)

end AlgebraicGeometry.Space

end
