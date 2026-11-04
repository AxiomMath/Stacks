module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CechOfCovering

/-!
# Čech hypercoverings

Let `C` be a site given by a pretopology `J`, let `C` have fibre products and let `X : C`. Let
`{U_i → X}_{i ∈ I}` be a covering family of `X`, viewed as an object `A` of
`SR(C, X) = FormalCoproduct (Over X)`, and let `K_0` be the zero-truncated simplicial object it
gives. The source forms `K = cosk₀ K_0` and shows that `K` is a hypercovering of `X`: its
degree-zero family is the covering family one started with, and all its matching morphisms
`K_{n + 1} ⟶ (cosk_n sk_n K)_{n + 1}` are isomorphisms, hence covering, by Simplicial Tag 018B.
A hypercovering of this form is a *Čech hypercovering* of `X`, and its degree-`n` term is
`{U_{i_0} ×_X ⋯ ×_X U_{i_n} → X}` indexed by `(i_0, …, i_n) ∈ I^{n + 1}`.

## Main definitions

* `IsCechHypercovering`: a simplicial object of `SR(C, X)` is a Čech hypercovering of `X` when
  its degree-zero family covers `X` and it is the zeroth coskeleton of that family, i.e. it is
  isomorphic to `cosk₀ U` for a zero-truncated simplicial object `U` (Tag 01G6).

## Main results

* `isCoveringOver_terminal_from_power`: condition (1) of Tag 01G5 for the Čech construction —
  the degree-zero term of the Čech object of a covering family covers `X`, because it is that
  family again, componentwise a product of one copy.
* `IsCechHypercovering.isHypercovering`: a Čech hypercovering is a hypercovering, the matching
  clauses holding because `cosk₀` is `n`-coskeletal for every `n` (Tag 018B).
* `isHypercovering_cech_of_isCoveringOver` and `isCechHypercovering_cech`: the Čech object of a
  covering family of `X` is a Čech hypercovering, hence a hypercovering, of `X`. This is Tag
  01G6 for an arbitrary covering family; the one-member case is
  `isHypercovering_cech` (Tag 0GMA).
* `isHypercovering_cosk_zero`: the same statement in the `cosk₀` form in which the source states
  it.
* `isLimitWidePullbackConePowerObj`: **Stacks Project, Tag 01G6**, the terms clause read in `C` —
  the component of the `α`-fold power of a family is a product in `Over X`, and its underlying
  object of `C` is the fibre product over `X` of the indexed members, so that for
  `α = Fin (n + 1)` the degree-`n` term is `{U_{i_0} ×_X ⋯ ×_X U_{i_n} → X}`.

## Implementation notes

The degree-zero covering clause is part of `IsCechHypercovering` rather than a consequence of
the remaining data. The reason is a genuine feature of `CategoryTheory.Pretopology`: its
transitivity axiom is stated for `Presieve.bind`, which refines each *arrow* of a covering
presieve, and not for an indexed family. Consequently a covering family of `X` need not stay
covering after replacing its members by isomorphic objects over `X`, because `Presieve.ofArrows`
forgets the index set entirely. A witness, using Mathlib's own `Pretopology.trivial` (coverings
are the singleton presieves of isomorphisms): the two-member family constantly `𝟙 X` has
presieve `{𝟙 X}` and so covers `X`, while an isomorphic family whose two members are distinct
isomorphisms `u₁, u₂ → X` has a two-arrow presieve and does not. Note the two arrows may even
share a domain, so this is not merely about collapsing repeated indices. In the source's indexed
formulation none of this arises, and `K_0` is *equal* to the covering family one started with,
so requiring that `K`'s own degree-zero family covers `X` is the faithful rendering of the
hypothesis of Tag 01G6.

What the `Presieve.bind` axiom does give is `mem_coverings_uniform_isIso_comp`: a covering family
stays covering after precomposing each member with an isomorphism chosen *uniformly*, as a
function of the member itself. The isomorphism `A.power α ≅ A` of `powerUniqueIso` is of this
shape — the component at `i` is the projection of a product of one copy of `A.obj (i default)` —
which is what makes `isCoveringOver_terminal_from_power` provable, and with it condition (1) of
Tag 01G5 for a Čech object with an arbitrary index set.

The covering families here are recorded as objects of `SR(C, X)`, their covering `X` being
`IsCoveringOver J (terminal.from ·)` as in `IsHypercovering`. The Čech object is Mathlib's
`FormalCoproduct.cech`, which is `0`-coskeletal (`cech_isCoskeletal`), so it is isomorphic to
`cosk₀` of its own degree-zero term and the two descriptions of a Čech hypercovering agree.

## References

* [Stacks Project, Tag 01G6](https://stacks.math.columbia.edu/tag/01G6)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

section Plumbing

/-- Two families of arrows whose objects agree and whose arrows agree up to that identification
generate the same presieve. -/
private theorem ofArrows_congr {T : C} {ι : Type*} {A B : ι → C} (gA : ∀ i, A i ⟶ T)
    (gB : ∀ i, B i ⟶ T) (e : ∀ i, A i = B i) (h : ∀ i, gA i = eqToHom (e i) ≫ gB i) :
    Presieve.ofArrows A gA = Presieve.ofArrows B gB := by
  funext W
  ext k
  constructor
  · rintro ⟨i⟩
    exact Presieve.ofArrows.mk' i (e i) (h i)
  · rintro ⟨i⟩
    refine Presieve.ofArrows.mk' i (e i).symm ?_
    rw [h i]
    simp

/-- The underlying morphism of an isomorphism of objects over `X` is an isomorphism. -/
private theorem isIso_left {X : C} {A B : Over X} (φ : A ⟶ B) [IsIso φ] : IsIso φ.left :=
  inferInstanceAs (IsIso ((Over.forget X).map φ))

/-- The underlying morphism of an `eqToHom` of objects over `X`. -/
private theorem eqToHom_left {X : C} {A B : Over X} (h : A = B) :
    (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  subst h
  simp

/-- The morphisms to a terminal object of a slice category out of two equal objects. -/
private theorem left_from_eq {X : C} {t : Over X} (hT : IsTerminal t) {Y Y' : Over X}
    (h : Y' = Y) :
    (hT.from Y').left = eqToHom (congrArg Comma.left h) ≫ (hT.from Y).left := by
  subst h
  simp

/-- An arrow to the underlying object of a terminal object of a slice category is the underlying
morphism of the terminal morphism out of the object over `X` which it defines. -/
private theorem left_from_mk {X : C} {t : Over X} (hT : IsTerminal t) {Z : C}
    (q : Z ⟶ t.left) : (hT.from (Over.mk (q ≫ t.hom))).left = q := by
  rw [hT.hom_ext (hT.from (Over.mk (q ≫ t.hom))) (Over.homMk q)]
  simp

/-- The comparison of the terminal morphism out of `G Y` with the composition of the objectwise
isomorphism `η W` with an arrow out of `W`, for `W` equal to `Y`. -/
private theorem objFun_aux {X : C} {t : Over X} (hT : IsTerminal t) (G : Over X → Over X)
    (η : ∀ Y : Over X, G Y ⟶ Y) {Y W : Over X} (hW : W = Y)
    (q : W.left ⟶ t.left) (q' : W ⟶ t) (hq : q = q'.left)
    (e : (G Y).left = (G W).left) :
    (hT.from (G Y)).left = eqToHom e ≫ (η W).left ≫ q := by
  subst hq
  subst hW
  rw [eqToHom_refl, Category.id_comp, ← Over.comp_left]
  exact congrArg Over.Hom.left (hT.hom_ext _ _)

/-- The underlying morphism of an `eqToHom` between components of a family of objects
over `X`. -/
private theorem eqToHom_left_congr {X : C} {β : Type*} (Q : β → Over X) {k l : β} (h : k = l) :
    eqToHom (congrArg (fun k ↦ (Q k).left) h) = (eqToHom (congrArg Q h) : Q k ⟶ Q l).left := by
  subst h
  simp

end Plumbing

variable [HasPullbacks C]

/-- A covering family stays covering after precomposing every member with an isomorphism chosen
uniformly, that is, by a function `η` of the member itself. This is the form in which the
transitivity axiom of a pretopology, stated for `Presieve.bind`, applies: the presieve refining
the member `f` is the one-member family `η f`. -/
theorem mem_coverings_uniform_isIso_comp (J : Pretopology C) {T : C} {ι : Type*}
    (A : ι → C) (g : ∀ i, A i ⟶ T) (hg : Presieve.ofArrows A g ∈ J T)
    (F : {Z : C} → (Z ⟶ T) → C) (η : {Z : C} → (h : Z ⟶ T) → F h ⟶ Z)
    (hη : ∀ {Z : C} (h : Z ⟶ T), IsIso (η h)) :
    Presieve.ofArrows (fun i ↦ F (g i)) (fun i ↦ η (g i) ≫ g i) ∈ J T := by
  have hbind : (Presieve.ofArrows A g).bind
      (fun ⦃_ : C⦄ (f : _ ⟶ T) (_ : Presieve.ofArrows A g f) ↦ Presieve.singleton (η f)) =
      Presieve.ofArrows (fun i ↦ F (g i)) (fun i ↦ η (g i) ≫ g i) := by
    funext W
    ext k
    constructor
    · rintro ⟨Z, g', f', H, hT, rfl⟩
      obtain ⟨i⟩ := H
      cases hT
      exact Presieve.ofArrows.mk i
    · rintro ⟨i⟩
      exact ⟨A i, η (g i), g i, Presieve.ofArrows.mk i, Presieve.singleton.mk, rfl⟩
  rw [← hbind]
  exact J.transitive _ _ hg fun _ f _ ↦ have := hη f; J.has_isos (η f)

/-- A family of objects over `X` whose structure morphisms cover the underlying object of a
terminal object `t` of `Over X` stays covering after applying a function `G` on objects over `X`
equipped with an objectwise isomorphism `η : G Y ⟶ Y`. -/
private theorem mem_coverings_overObjFun (J : Pretopology C) {X : C} {t : Over X}
    (hT : IsTerminal t) (G : Over X → Over X) (η : ∀ Y : Over X, G Y ⟶ Y)
    (hη : ∀ Y, IsIso (η Y)) {ι : Type*} (A : ι → Over X)
    (hg : Presieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (hT.from (A i)).left) ∈ J t.left) :
    Presieve.ofArrows (fun i ↦ (G (A i)).left) (fun i ↦ (hT.from (G (A i))).left) ∈
      J t.left := by
  have key := mem_coverings_uniform_isIso_comp J (fun i ↦ (A i).left)
    (fun i ↦ (hT.from (A i)).left) hg
    (F := fun {Z} (h : Z ⟶ t.left) ↦ (G (Over.mk (h ≫ t.hom))).left)
    (η := fun {Z} (h : Z ⟶ t.left) ↦ (η (Over.mk (h ≫ t.hom))).left)
    (fun {Z} h ↦ by have := hη (Over.mk (h ≫ t.hom)); exact isIso_left _)
  have hW : ∀ i, Over.mk ((hT.from (A i)).left ≫ t.hom) = A i := fun i ↦ by
    rw [Over.w]
    exact rfl
  have hpres : Presieve.ofArrows (fun i ↦ (G (A i)).left) (fun i ↦ (hT.from (G (A i))).left)
      = Presieve.ofArrows (fun i ↦ (G (Over.mk ((hT.from (A i)).left ≫ t.hom))).left)
          (fun i ↦ (η (Over.mk ((hT.from (A i)).left ≫ t.hom))).left ≫
            (hT.from (A i)).left) := by
    refine ofArrows_congr _ _ (fun i ↦ congrArg (fun Y ↦ (G Y).left) (hW i).symm) (fun i ↦ ?_)
    exact objFun_aux hT G η (hW i) _ (hT.from (Over.mk ((hT.from (A i)).left ≫ t.hom)))
      (left_from_mk hT ((hT.from (A i)).left)).symm _
  rwa [hpres]

section Terminal

variable {X : C}

/-- The terminal object of `SR(C, X)` is the one-member family of a terminal object of
`Over X`. -/
private noncomputable def inclTerminalIso :
    (FormalCoproduct.incl (Over X)).obj (⊤_ (Over X)) ≅ ⊤_ FormalCoproduct.{w} (Over X) :=
  (FormalCoproduct.isTerminalIncl (⊤_ (Over X)) terminalIsTerminal).uniqueUpToIso
    terminalIsTerminal

/-- The terminal object of `SR(C, X)` has at most one index. -/
private instance subsingleton_terminal_I :
    Subsingleton (⊤_ FormalCoproduct.{w} (Over X)).I := by
  have hP : Subsingleton ((FormalCoproduct.incl (Over X)).obj (⊤_ (Over X))).I := by
    dsimp [FormalCoproduct.incl]
    infer_instance
  refine ⟨fun i₁ i₂ ↦ ?_⟩
  calc i₁ = inclTerminalIso.hom.f ((inv inclTerminalIso.hom).f i₁) :=
        (f_inv_f inclTerminalIso.hom i₁).symm
    _ = inclTerminalIso.hom.f ((inv inclTerminalIso.hom).f i₂) :=
        congrArg _ (Subsingleton.elim _ _)
    _ = i₂ := f_inv_f inclTerminalIso.hom i₂

/-- Every component of the terminal object of `SR(C, X)` is a terminal object of `Over X`. -/
private noncomputable def isTerminalTerminalObj (j : (⊤_ FormalCoproduct.{w} (Over X)).I) :
    IsTerminal ((⊤_ FormalCoproduct.{w} (Over X)).obj j) :=
  have : IsIso (inclTerminalIso.{w} (X := X)).inv := inferInstance
  IsTerminal.ofIso terminalIsTerminal (asIso ((inclTerminalIso.{w} (X := X)).inv.φ j)).symm

omit [HasPullbacks C] in
/-- The component over `i` of the morphism to the terminal object of `SR(C, X)`, as the terminal
morphism of `Over X` out of the component. -/
private theorem left_from_eq_eqToHom (Z : FormalCoproduct.{w} (Over X))
    {j : (⊤_ FormalCoproduct.{w} (Over X)).I}
    (hT : IsTerminal ((⊤_ FormalCoproduct.{w} (Over X)).obj j))
    (i : Z.I) (h : (terminal.from Z).f i = j) :
    (hT.from (Z.obj i)).left = ((terminal.from Z).φ i).left ≫
      eqToHom (congrArg (fun k ↦ ((⊤_ FormalCoproduct.{w} (Over X)).obj k).left) h) := by
  rw [eqToHom_left_congr (fun k ↦ (⊤_ FormalCoproduct.{w} (Over X)).obj k) h, ← Over.comp_left]
  exact congrArg Over.Hom.left (hT.hom_ext _ _)

omit [HasPullbacks C] in
/-- A family of objects over `X` covers `X` exactly when the presieve of the terminal morphisms
of `Over X` out of its components is a covering presieve: the index of the terminal object of
`SR(C, X)` being unique, the covering presieve of `terminal.from Z` over it is that one. -/
private theorem ofArrows_terminal_eq (Z : FormalCoproduct.{w} (Over X))
    (j : (⊤_ FormalCoproduct.{w} (Over X)).I)
    (hT : IsTerminal ((⊤_ FormalCoproduct.{w} (Over X)).obj j)) :
    Presieve.ofArrows (fun i : Z.I ↦ (Z.obj i).left) (fun i ↦ (hT.from (Z.obj i)).left) =
      Presieve.ofArrows (fun i : {i : Z.I // (terminal.from Z).f i = j} ↦ (Z.obj i.1).left)
        (fun i ↦ ((terminal.from Z).φ i.1).left ≫
          eqToHom (congrArg (fun k ↦ ((⊤_ FormalCoproduct.{w} (Over X)).obj k).left) i.2)) := by
  have ha : Function.Surjective (fun i : Z.I ↦ (⟨i, Subsingleton.elim _ _⟩ :
      {i : Z.I // (terminal.from Z).f i = j})) := fun i ↦ ⟨i.1, Subtype.ext rfl⟩
  rw [← Presieve.ofArrows_comp_eq_of_surjective _ ha]
  refine ofArrows_congr _ _ (fun i ↦ rfl) (fun i ↦ ?_)
  rw [eqToHom_refl, Category.id_comp]
  exact left_from_eq_eqToHom Z hT i (Subsingleton.elim _ _)

end Terminal

/-- A family of objects over `X` which covers `X` stays covering after applying a function `G`
on objects over `X` equipped with an objectwise isomorphism `η : G Y ⟶ Y`, and reindexing along
a surjection. -/
theorem isCoveringOver_terminal_from_of_objFun (J : Pretopology C) {X : C}
    {Z Z' : FormalCoproduct.{w} (Over X)}
    (G : Over X → Over X) (η : ∀ Y : Over X, G Y ⟶ Y) (hη : ∀ Y, IsIso (η Y))
    (σ : Z'.I → Z.I) (hσ : Function.Surjective σ)
    (hobj : ∀ i, Z'.obj i = G (Z.obj (σ i)))
    (hZ : IsCoveringOver J (terminal.from Z)) :
    IsCoveringOver J (terminal.from Z') := by
  intro j
  have hT := isTerminalTerminalObj j
  rw [← ofArrows_terminal_eq Z' j hT]
  have h1 := hZ j
  rw [← ofArrows_terminal_eq Z j hT, ← Presieve.ofArrows_comp_eq_of_surjective _ hσ] at h1
  rw [ofArrows_congr (fun i ↦ (hT.from (Z'.obj i)).left)
    (fun i ↦ (hT.from (G (Z.obj (σ i)))).left)
    (fun i ↦ congrArg Comma.left (hobj i)) (fun i ↦ left_from_eq hT (hobj i))]
  exact mem_coverings_overObjFun J hT G η hη (fun i ↦ Z.obj (σ i)) h1

/-- **Stacks Project, Tag 01G6**, condition (1) of Definition 01G5 for the Čech construction.
If the family `U` covers `X` then so does its `α`-fold power for a one-element index type `α`,
which is the degree-zero term of the Čech object of `U`: that term is `U` again, its component
at `i` being a product of one copy of the component of `U` at `i default`. -/
@[stacks 01G6 "condition (1) of Definition 01G5, for the degree-zero term of the Čech object"]
theorem isCoveringOver_terminal_from_power (J : Pretopology C) {X : C}
    (U : FormalCoproduct.{w} (Over X)) (α : Type) [Unique α] [HasProductsOfShape α (Over X)]
    (hU : IsCoveringOver J (terminal.from U)) :
    IsCoveringOver J (terminal.from (U.power α)) := by
  refine isCoveringOver_terminal_from_of_objFun J (fun Y ↦ ∏ᶜ (fun _ : α ↦ Y))
    (fun Y ↦ Pi.π (fun _ : α ↦ Y) default) (fun Y ↦ ?_) (fun i ↦ i default)
    (fun i ↦ ⟨fun _ ↦ i, rfl⟩) (fun i ↦ congrArg (fun f ↦ ∏ᶜ f)
      (funext fun a ↦ congrArg U.obj (congrArg i (Subsingleton.elim a default)))) hU
  rw [← productUniqueIso_hom]
  infer_instance

/-- **A family of objects over `X` covers `X` as soon as the presieve of its structure morphisms
is a covering presieve of `X`.** This is the hypothesis `IsCoveringOver J (terminal.from A)` of
`isCechHypercovering_cech` and `isHypercovering_cech_of_isCoveringOver` in the form in which a
covering family of a pretopology is given: the covering clause of `IsHypercovering` is stated
over the component of the terminal object of `SR(C, X)`, whose structure morphism to `X` is an
isomorphism because that component is terminal in `Over X`, and composing a covering family with
a fixed isomorphism of the target keeps it covering (`mem_coverings_comp_isIso`). -/
theorem isCoveringOver_terminal_from_of_mem (J : Pretopology C) {X : C}
    (A : FormalCoproduct.{w} (Over X))
    (hA : Presieve.ofArrows (fun i ↦ (A.obj i).left) (fun i ↦ (A.obj i).hom) ∈ J X) :
    IsCoveringOver J (terminal.from A) := by
  intro j
  have hT := isTerminalTerminalObj.{w} (X := X) j
  rw [← ofArrows_terminal_eq A j hT]
  have he : ((Over.forget X).map (hT.uniqueUpToIso Over.mkIdTerminal).hom) =
      ((⊤_ FormalCoproduct.{w} (Over X)).obj j).hom :=
    Over.mkIdTerminal_from_left _
  have : IsIso ((Over.forget X).map (hT.uniqueUpToIso Over.mkIdTerminal).hom) := inferInstance
  rw [he] at this
  rw [ofArrows_congr (fun i ↦ (hT.from (A.obj i)).left)
    (fun i ↦ (A.obj i).hom ≫ inv ((⊤_ FormalCoproduct.{w} (Over X)).obj j).hom)
    (fun _ ↦ rfl) (fun i ↦ by
      rw [eqToHom_refl, Category.id_comp, ← Over.w (hT.from (A.obj i))]
      simp)]
  exact mem_coverings_comp_isIso J _ _ hA _

/-- **Stacks Project, Tag 01G6.** A simplicial object `K` of `SR(C, X)` is a *Čech
hypercovering* of `X` when its degree-zero family `K_0` covers `X` and `K` is the zeroth
coskeleton of `K_0`, that is, when `K` is isomorphic to `cosk₀ U` for a zero-truncated
simplicial object `U` of `SR(C, X)`. -/
@[stacks 01G6 "the definition of a Čech hypercovering"]
abbrev IsCechHypercovering (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) : Prop :=
  IsCoveringOver J (terminal.from (K.obj (op ⦋0⦌))) ∧
    ∃ U : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) 0,
      Nonempty (K ≅ (SimplicialObject.Truncated.cosk 0).obj U)

/-- **Stacks Project, Tag 01G6**, condition (2) of Definition 01G5 and the hypercovering
property. A Čech hypercovering of `X` is a hypercovering of `X`: its degree-zero family covers
`X` by definition, and each of its matching morphisms is an isomorphism, hence covering, because
`cosk₀ U` is `n`-coskeletal for every `n` (Tag 018B). -/
@[stacks 01G6 "condition (2) of Definition 01G5 by Tag 018B, hence the hypercovering property"]
theorem IsCechHypercovering.isHypercovering {J : Pretopology C} {X : C}
    {K : SimplicialObject (FormalCoproduct.{w} (Over X))} (hK : IsCechHypercovering J K) :
    IsHypercovering J K := by
  obtain ⟨h0, U, ⟨e⟩⟩ := hK
  refine ⟨h0, fun n ↦ ?_⟩
  have hcosk : IsIso ((SimplicialObject.coskAdj 0).unit.app
      ((SimplicialObject.Truncated.cosk 0).obj U)) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app (le_refl 0)).2.1 U
  have hzero : IsIso ((SimplicialObject.coskAdj 0).unit.app K) := by
    have hcomp : IsIso ((SimplicialObject.coskAdj 0).unit.app K ≫
        (SimplicialObject.truncation 0 ⋙ SimplicialObject.Truncated.cosk 0).map e.hom) := by
      rw [← (SimplicialObject.coskAdj 0).unit.naturality e.hom]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((SimplicialObject.truncation 0 ⋙
      SimplicialObject.Truncated.cosk 0).map e.hom)
  have hn : IsIso ((SimplicialObject.coskAdj n).unit.app K) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (Nat.zero_le n)).2.2 K hzero
  exact IsCoveringOver.of_isIso J _

/-- **Stacks Project, Tag 01G6.** The Čech object of a covering family of `X` is a Čech
hypercovering of `X`: its degree-zero term is the covering family again, and it is
`0`-coskeletal, hence isomorphic to the zeroth coskeleton of that term. -/
@[stacks 01G6 "the Čech object of a covering family is a Čech hypercovering"]
theorem isCechHypercovering_cech (J : Pretopology C) {X : C}
    (A : FormalCoproduct.{w} (Over X)) (hA : IsCoveringOver J (terminal.from A)) :
    let : HasTerminal (Over X) := Over.over_hasTerminal X
    let : HasBinaryProducts (Over X) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    let : HasFiniteProducts (Over X) := hasFiniteProducts_of_has_binary_and_terminal
    IsCechHypercovering J A.cech := by
  intro _ _ _
  refine ⟨isCoveringOver_terminal_from_power J A (Fin 1) hA, ?_⟩
  have hiso : IsIso ((SimplicialObject.coskAdj 0).unit.app A.cech) :=
    (SimplicialObject.isCoskeletal_iff_isIso A.cech 0).mp (cech_isCoskeletal A)
  exact ⟨(SimplicialObject.truncation 0).obj A.cech,
    ⟨asIso ((SimplicialObject.coskAdj 0).unit.app A.cech)⟩⟩

/-- **Stacks Project, Tag 01G6.** The Čech object of a covering family `{U_i → X}_{i ∈ I}` of `X`
is a hypercovering of `X`. Its degree-`n` term is the family of the `(n + 1)`-fold fibre products
`U_{i_0} ×_X ⋯ ×_X U_{i_n}` over `X`, indexed by `I^{n + 1}`; see `FormalCoproduct.cech_obj`,
`FormalCoproduct.power_I` and `FormalCoproduct.power_obj`. The one-member case is
`isHypercovering_cech`, Tag 0GMA. -/
@[stacks 01G6 "the Čech object of a covering family is a hypercovering"]
theorem isHypercovering_cech_of_isCoveringOver (J : Pretopology C) {X : C}
    (A : FormalCoproduct.{w} (Over X)) (hA : IsCoveringOver J (terminal.from A)) :
    let : HasTerminal (Over X) := Over.over_hasTerminal X
    let : HasBinaryProducts (Over X) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    let : HasFiniteProducts (Over X) := hasFiniteProducts_of_has_binary_and_terminal
    IsHypercovering J A.cech := by
  intro _ _ _
  exact (isCechHypercovering_cech J A hA).isHypercovering

/-- **Stacks Project, Tag 01G6**, in the `cosk₀` shape in which the source states it: the zeroth
coskeleton of a zero-truncated simplicial object of `SR(C, X)` is a hypercovering of `X` as soon
as its degree-zero family covers `X`. The degree-zero family of `cosk₀ U` is `U` up to the
isomorphism given by the counit of the coskeletal adjunction; the covering hypothesis is stated
for `cosk₀ U` itself because a covering family of a pretopology need not stay covering under an
arbitrary isomorphism of `SR(C, X)` — see the implementation notes.

This is a convenience restatement, not the tag's assertion, and its hypothesis placement is not
claimed to be optimal: the counit comparison at level `0` is a limit over a one-object,
one-morphism indexing category, so it is of the objectwise shape that
`isCoveringOver_terminal_from_of_objFun` transports, and stating the hypothesis on `U` itself is
expected to be reachable by that route — it would need an explicit description of the pointwise
right Kan extension at degree `0`, which is not developed here. For the covering family itself
as the hypothesis, use `isHypercovering_cech_of_isCoveringOver`, which carries the source's own
hypothesis and whose Čech object is `0`-coskeletal and therefore of this form. -/
@[stacks 01G6 "the hypercovering property in the `cosk₀` form"]
theorem isHypercovering_cosk_zero (J : Pretopology C) {X : C}
    (U : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) 0)
    (hU : IsCoveringOver J
      (terminal.from (((SimplicialObject.Truncated.cosk 0).obj U).obj (op ⦋0⦌)))) :
    IsHypercovering J ((SimplicialObject.Truncated.cosk 0).obj U) :=
  IsCechHypercovering.isHypercovering ⟨hU, U, ⟨Iso.refl _⟩⟩

/-- **Stacks Project, Tag 01G6**, the terms clause read in `C`. The component at `i : α → I` of
the `α`-fold power of the family `A = {U_i → X}` is a product taken in `Over X`; its underlying
object of `C` is the fibre product over `X` of the `U_{i a}`. Precisely, the cone in `C` with
apex that underlying object, projections the underlying morphisms of the product projections of
`Over X` and base the structure morphism to `X`, is a limit of the wide cospan of the structure
morphisms `U_{i a} → X`.

Together with `FormalCoproduct.cech_obj`, `FormalCoproduct.power_I` and
`FormalCoproduct.power_obj` this is the source's formula
`K_n = {U_{i_0} ×_X ⋯ ×_X U_{i_n} → X}` indexed by `I^{n + 1}`: take `α = Fin (n + 1)`. -/
@[stacks 01G6 "the terms in `C`: each component is the fibre product over `X` of its factors"]
noncomputable def isLimitWidePullbackConePowerObj {X : C} (A : FormalCoproduct.{w} (Over X))
    (α : Type) [Finite α] :
    let : HasTerminal (Over X) := Over.over_hasTerminal X
    let : HasBinaryProducts (Over X) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    let : HasFiniteProducts (Over X) := hasFiniteProducts_of_has_binary_and_terminal
    ∀ i : α → A.I, IsLimit (WidePullbackCone.mk (f := fun a ↦ (A.obj (i a)).hom)
      ((A.power α).obj i).hom (fun a ↦ (Pi.π (A.obj ∘ i) a).left)
      fun a ↦ Over.w (Pi.π (A.obj ∘ i) a)) := by
  intro _ _ _ i
  refine WidePullbackCone.IsLimit.mk _
    (fun t ↦ (Pi.lift fun a ↦ (Over.homMk (t.π a) (t.condition a) :
      Over.mk t.base ⟶ (A.obj ∘ i) a)).left) (fun t ↦ ?_) (fun t a ↦ ?_) (fun t m hb ha ↦ ?_)
  · exact Over.w (Pi.lift fun a ↦ (Over.homMk (t.π a) (t.condition a) :
      Over.mk t.base ⟶ (A.obj ∘ i) a))
  · exact congrArg Over.Hom.left (Pi.lift_π
      (fun a ↦ (Over.homMk (t.π a) (t.condition a) : Over.mk t.base ⟶ (A.obj ∘ i) a)) a)
  · refine congrArg Over.Hom.left (Pi.hom_ext
      (Over.homMk m hb : Over.mk t.base ⟶ ∏ᶜ (A.obj ∘ i))
      (Pi.lift fun a ↦ (Over.homMk (t.π a) (t.condition a) :
        Over.mk t.base ⟶ (A.obj ∘ i) a)) fun a ↦ ?_)
    rw [Pi.lift_π]
    exact Over.OverMorphism.ext (ha a)

add_to_stacks 01G6 "the terms: the degree-`n` term is the `(n + 1)`-fold power"
  FormalCoproduct.cech_obj
add_to_stacks 01G6 "the terms: the index set `I^{n + 1}`" FormalCoproduct.power_I
add_to_stacks 01G6 "the terms: the fibre product over `X` of the indexed components"
  FormalCoproduct.power_obj

end Stacks.CategoryTheory.Hypercovering

end
