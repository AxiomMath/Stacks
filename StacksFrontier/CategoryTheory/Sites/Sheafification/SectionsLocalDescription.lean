module

public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-!
# Local description of the sections of a sheafification

Stacks tag 00WK. Let `P` be a presheaf of sets on a site `(C, J)`, let `P♯` be its
sheafification and `θ² : P ⟶ P♯` the canonical map. Every section `s ∈ P♯(U)` admits a local
description: there is a covering `{U_i ⟶ U}` and sections `s_i ∈ P(U_i)` with
`s|_{U_i} = θ²(s_i)`, such that for all `i, j` the pullbacks of `s_i` and `s_j` agree in `P` on
some covering of `U_i ×_U U_j` (`LocallyAgreeOnOverlaps`). Conversely, any family of local
sections satisfying that overlap condition glues to a unique section of `P♯` over `U`. The
complete statement is `sheafify_local_description`.

The auxiliary condition `MatchingOnOverlaps` asks instead that the `θ²(s_i)` agree in `P♯` on
`U_i ×_U U_j`. It follows from `LocallyAgreeOnOverlaps` since `P♯` is separated
(`matchingOnOverlaps_of_locallyAgreeOnOverlaps`), and implies it since `θ²` is locally
injective (`locallyAgreeOnOverlaps_of_matchingOnOverlaps`).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C)
variable (P : Cᵒᵖ ⥤ Type (max u v))

/-- A variant of condition (2) of tag 00WK, phrased in the sheafification (Stacks
phrases (2) in `P` itself: see `LocallyAgreeOnOverlaps`, which is equivalent).
Given a covering sieve `𝒰` of `U` and a choice of section
`s_ I ∈ P(I.Y)` for each leg `I`, this says that for every pair of legs `I, I'`,
the images `θ²(s_ I)` and `θ²(s_ I')` agree on the fibre product `I.Y ×_U I'.Y`,
i.e. become equal in `P♯(I.Y ×_U I'.Y)` after restriction along the two
projections. -/
def MatchingOnOverlaps {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) : Prop :=
  ∀ I I' : 𝒰.Arrow,
    (J.sheafify P).map (pullback.fst I.f I'.f).op ((J.toSheafify P).app (op I.Y) (s_ I)) =
      (J.sheafify P).map (pullback.snd I.f I'.f).op ((J.toSheafify P).app (op I'.Y) (s_ I'))

/-- Condition (2) of tag 00WK, as Stacks states it: for every pair of legs `I, I'` of the
covering there is a covering `R` of the fibre product `I.Y ×_U I'.Y` on each leg of which the
pullbacks of `s_ I` and `s_ I'` agree in `P`. -/
def LocallyAgreeOnOverlaps {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) : Prop :=
  ∀ I I' : 𝒰.Arrow, ∃ R : J.Cover (pullback I.f I'.f), ∀ K : R.Arrow,
    P.map (K.f ≫ pullback.fst I.f I'.f).op (s_ I) =
      P.map (K.f ≫ pullback.snd I.f I'.f).op (s_ I')

/-- Condition (1) of tag 00WK: the section `s ∈ P♯(U)` restricts, on each leg
`U_i → U` of the covering, to the image `θ²(s_i)` of the local section `s_i`. -/
def IsLocalDescription {U : C} (𝒰 : J.Cover U)
    (s : (J.sheafify P).obj (op U)) (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) : Prop :=
  ∀ I : 𝒰.Arrow,
    (J.sheafify P).map I.f.op s = (J.toSheafify P).app (op I.Y) (s_ I)

omit [HasPullbacks C] in
/-- For a sheaf `F` (valued in `Type _`), a compatible family `x : Meq F S` over a
covering sieve `S` glues to a unique section `t` of `F` whose restriction along each
leg `I` equals `x I`.

Proof: for the sheaf `F` the canonical map `S.toMultiequalizer F` is an isomorphism
(`Presheaf.isSheaf_iff_multiequalizer`); composing its inverse with the bijection
`Meq.equiv F S : multiequalizer (S.index F) ≃ Meq F S` turns the matching family `x`
into a global section, and `Meq.ext` gives uniqueness. -/
private theorem sheaf_glue_meq (F : Cᵒᵖ ⥤ Type (max u v)) (hF : Presheaf.IsSheaf J F)
    {X : C} (S : J.Cover X) (x : Meq F S) :
    ∃! t : F.obj (op X), ∀ I : S.Arrow, F.map I.f.op t = x.1 I := by
  -- For a sheaf, `S.toMultiequalizer F` is an iso.
  have hiso : IsIso (S.toMultiequalizer F) :=
    (Presheaf.isSheaf_iff_multiequalizer J F).mp hF X S
  -- The family-of-restrictions of a section, read off through `Meq.equiv`.
  have hrestr : ∀ (t : F.obj (op X)) (I : S.Arrow),
      (Meq.equiv F S) (S.toMultiequalizer F t) I = F.map I.f.op t := by
    intro t I
    rw [Meq.equiv_apply, Cover.toMultiequalizer, ← ConcreteCategory.comp_apply,
      Multiequalizer.lift_ι]
    rfl
  -- Transport `x` back through the equiv, then through the inverse iso.
  set m : multiequalizer (S.index F) := (Meq.equiv F S).symm x with hm
  refine ⟨inv (S.toMultiequalizer F) m, ?_, ?_⟩
  · intro I
    rw [← hrestr, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
    simp [hm]
  · intro y hy
    -- Uniqueness: a section with the same restrictions has the same image in the multiequalizer.
    have hkey : S.toMultiequalizer F y = m := by
      apply (Meq.equiv F S).injective
      apply Meq.ext
      intro I
      rw [hrestr y I, hm, Equiv.apply_symm_apply]
      exact hy I
    rw [← hkey, ← ConcreteCategory.comp_apply]
    simp [IsIso.hom_inv_id]

/-- The `MatchingOnOverlaps` condition (agreement on the chosen pullbacks) implies
agreement on *every* relation `r : I₁.Relation I₂`, because any such relation factors
through the pullback `I₁.Y ×_U I₂.Y`. -/
private theorem matching_relation {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) (h : MatchingOnOverlaps J P 𝒰 s_)
    (I₁ I₂ : 𝒰.Arrow) (r : I₁.Relation I₂) :
    (J.sheafify P).map r.g₁.op ((J.toSheafify P).app (op I₁.Y) (s_ I₁)) =
      (J.sheafify P).map r.g₂.op ((J.toSheafify P).app (op I₂.Y) (s_ I₂)) := by
  set l : r.Z ⟶ pullback I₁.f I₂.f := pullback.lift r.g₁ r.g₂ r.w with hl
  have e1 : r.g₁ = l ≫ pullback.fst I₁.f I₂.f := by simp [hl]
  have e2 : r.g₂ = l ≫ pullback.snd I₁.f I₂.f := by simp [hl]
  rw [e1, e2, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h I₁ I₂]

/-- A weak form of the existence half of tag 00WK, with condition (2) replaced by the
variant `MatchingOnOverlaps` in `P♯`, which here follows from (1) alone; the existence half
with Stacks' condition (2) is `exists_isLocalDescription_locallyAgreeOnOverlaps`.
Every section `s` of the sheafification `P♯` over `U` admits, on some covering
`{U_i → U}` of `U`, a description by local sections `s_i ∈ P(U_i)` of the original
presheaf such that `s|_{U_i} = θ²(s_i)` (condition (1)) and the `s_i` agree on the
overlaps `U_i ×_U U_j` after applying `θ²` (condition (2)).

Proof strategy:
* The canonical map `θ² = J.toSheafify P` is *locally surjective* (Mathlib
  instance `Presheaf.isLocallySurjective_toSheafify`).  Hence the *image sieve*
  `S := Presheaf.imageSieve θ² s` of `s` is a covering of `U`
  (`Presheaf.IsLocallySurjective.imageSieve_mem`).  Take `𝒰 := ⟨S, _⟩ : J.Cover U`.
* For each leg `I : 𝒰.Arrow`, membership `I.hf : S.arrows I.f` unfolds, for the
  image sieve, to `∃ t : P(I.Y), θ².app _ t = (sheafify P).map I.f.op s`.  Use
  `choose` to pick `s_ I := t` and the witness `hs_ I`.
* Condition (1) `IsLocalDescription` is exactly `(hs_ I).symm`.
* Condition (2) `MatchingOnOverlaps` needs **no** sheaf-separatedness: rewrite
  `θ²(s_ I) = (sheafify P).map I.f.op s` and `θ²(s_ I') = (sheafify P).map I'.f.op s`
  (the `hs_` witnesses), collapse the two restrictions via functoriality
  (`Functor.map_comp_apply`, `op_comp`), and use `pullback.condition`
  (`fst ≫ I.f = snd ≫ I'.f`) to identify the two composite restrictions. -/
theorem exists_local_description {U : C} (s : (J.sheafify P).obj (op U)) :
    ∃ (𝒰 : J.Cover U) (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)),
      IsLocalDescription J P 𝒰 s s_ ∧ MatchingOnOverlaps J P 𝒰 s_ := by
  set 𝒰 : J.Cover U := ⟨Presheaf.imageSieve (J.toSheafify P) s,
    Presheaf.imageSieve_mem (J := J) (f := J.toSheafify P) (s := s)⟩
  have hleg : ∀ I : 𝒰.Arrow, ∃ t : P.obj (op I.Y),
      (J.toSheafify P).app (op I.Y) t = (J.sheafify P).map I.f.op s := fun I => I.hf
  choose s_ hs_ using hleg
  refine ⟨𝒰, s_, fun I => (hs_ I).symm, fun I I' => ?_⟩
  rw [hs_ I, hs_ I', ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    pullback.condition]

/-- The converse half of tag 00WK under the variant `MatchingOnOverlaps` of condition (2),
which is implied by Stacks' condition (2) (see
`existsUnique_isLocalDescription_of_locallyAgreeOnOverlaps`).
Given any covering `{U_i → U}` and local sections `s_i ∈ P(U_i)`
satisfying `MatchingOnOverlaps`, there is a **unique** section `s ∈ P♯(U)`
with `s|_{U_i} = θ²(s_i)` for all `i` (condition (1)).

Proof strategy:
* Build a compatible family `x : Meq F 𝒰` for `F := J.sheafify P` with
  `x I = θ².app (op I.Y) (s_ I)`; its `condition` is exactly `matching_relation`
  (the overlap condition transported to every `Relation`).
* `F` is a sheaf (`J.sheafify_isSheaf P`), so by `sheaf_glue_meq` the family `x`
  glues to a unique section `t` with `F.map I.f.op t = x I = θ²(s_ I)`, i.e.
  satisfying `IsLocalDescription`; uniqueness is the `∃!` part of `sheaf_glue_meq`. -/
theorem exists_unique_glue {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) (h : MatchingOnOverlaps J P 𝒰 s_) :
    ∃! s : (J.sheafify P).obj (op U), IsLocalDescription J P 𝒰 s s_ :=
  sheaf_glue_meq J _ (J.sheafify_isSheaf P) 𝒰
    ⟨fun I => (J.toSheafify P).app (op I.Y) (s_ I),
      fun I => matching_relation J P 𝒰 s_ h I.fst I.snd I.r⟩

/-- Condition (2) of tag 00WK in `P` implies its variant in `P♯`, because `P♯` is separated. -/
theorem matchingOnOverlaps_of_locallyAgreeOnOverlaps {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) (h : LocallyAgreeOnOverlaps J P 𝒰 s_) :
    MatchingOnOverlaps J P 𝒰 s_ := by
  intro I I'
  obtain ⟨R, hR⟩ := h I I'
  have hsh := (isSheaf_iff_isSheaf_of_type J (J.sheafify P)).mp (J.sheafify_isSheaf P)
  refine (hsh _ R.condition).isSeparatedFor.ext fun Y f hf => ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    ← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hR ⟨Y, f, hf⟩]

/-- The variant of condition (2) of tag 00WK in `P♯` implies the condition in `P`, because
`θ²` is locally injective. -/
theorem locallyAgreeOnOverlaps_of_matchingOnOverlaps {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) (h : MatchingOnOverlaps J P 𝒰 s_) :
    LocallyAgreeOnOverlaps J P 𝒰 s_ := by
  intro I I'
  have heq : (J.toSheafify P).app _ (P.map (pullback.fst I.f I'.f).op (s_ I)) =
      (J.toSheafify P).app _ (P.map (pullback.snd I.f I'.f).op (s_ I')) := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact h I I'
  refine ⟨⟨_, Presheaf.equalizerSieve_mem J (J.toSheafify P) _ _ heq⟩, fun K => ?_⟩
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact K.hf

/-- The existence half of tag 00WK: every section `s ∈ P♯(U)` has, on some covering
`{U_i → U}`, local sections `s_i ∈ P(U_i)` with `s|_{U_i} = θ²(s_i)` (condition (1)) whose
pullbacks agree in `P` on a covering of each `U_i ×_U U_j` (condition (2)). -/
theorem exists_isLocalDescription_locallyAgreeOnOverlaps {U : C}
    (s : (J.sheafify P).obj (op U)) :
    ∃ (𝒰 : J.Cover U) (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)),
      IsLocalDescription J P 𝒰 s s_ ∧ LocallyAgreeOnOverlaps J P 𝒰 s_ := by
  obtain ⟨𝒰, s_, h1, h2⟩ := exists_local_description J P s
  exact ⟨𝒰, s_, h1, locallyAgreeOnOverlaps_of_matchingOnOverlaps J P 𝒰 s_ h2⟩

/-- The converse half of tag 00WK: local sections `s_i ∈ P(U_i)` on a covering `{U_i → U}`
satisfying condition (2) come from a unique `s ∈ P♯(U)` satisfying condition (1). -/
theorem existsUnique_isLocalDescription_of_locallyAgreeOnOverlaps {U : C} (𝒰 : J.Cover U)
    (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)) (h : LocallyAgreeOnOverlaps J P 𝒰 s_) :
    ∃! s : (J.sheafify P).obj (op U), IsLocalDescription J P 𝒰 s s_ :=
  exists_unique_glue J P 𝒰 s_ (matchingOnOverlaps_of_locallyAgreeOnOverlaps J P 𝒰 s_ h)

/-- **Stacks 00WK.** Let `P` be a presheaf of sets on a site, `θ² : P → P♯` the canonical map.
Every `s ∈ P♯(U)` admits a covering `{U_i → U}` and `s_i ∈ P(U_i)` with (1)
`s|_{U_i} = θ²(s_i)` and (2) for all `i, j`, the pullbacks of `s_i` and `s_j` agree on a
covering of `U_i ×_U U_j`. Conversely, for any covering and `s_i` satisfying (2) there is a
unique `s ∈ P♯(U)` satisfying (1). Coverings are covering sieves of `J`, indexed by their
arrows; `P` takes values in `Type (max u v)`, the universe of Mathlib's `J.sheafify`. -/
@[stacks 00WK]
theorem sheafify_local_description :
    (∀ {U : C} (s : (J.sheafify P).obj (op U)),
      ∃ (𝒰 : J.Cover U) (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)),
        IsLocalDescription J P 𝒰 s s_ ∧ LocallyAgreeOnOverlaps J P 𝒰 s_) ∧
    (∀ {U : C} (𝒰 : J.Cover U) (s_ : ∀ I : 𝒰.Arrow, P.obj (op I.Y)),
      LocallyAgreeOnOverlaps J P 𝒰 s_ →
        ∃! s : (J.sheafify P).obj (op U), IsLocalDescription J P 𝒰 s s_) :=
  ⟨fun s => exists_isLocalDescription_locallyAgreeOnOverlaps J P s,
    fun 𝒰 s_ h => existsUnique_isLocalDescription_of_locallyAgreeOnOverlaps J P 𝒰 s_ h⟩
