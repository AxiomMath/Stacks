module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesCompSections
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces

/-!
# Pro-isomorphisms and the completed internal hom on an algebraic space

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale ringed site and let `M`, `N` be `𝒪_F`-modules, with `𝓗 = 𝓗om_{𝒪_F}(M, N)`.  The identity
of Stacks 08B6,

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`,

factors through the inverse limit of the global sections of the internal homs into the
ideal-power quotients of `N`, in two independent steps:

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = lim_n H⁰(F, 𝓗om(M, N / 𝓘 ^ n N))`  (the comparison step), and
`lim_n H⁰(F, 𝓗om(M, N / 𝓘 ^ n N)) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`  (the morphism step).

The morphism step is `AlgebraicGeometry.Space.bijective_smallEtaleInternalHomAdicSection`, proved
for arbitrary `𝒪_F`-modules and an arbitrary sheaf of ideals; it is registered here as that step
of Stacks 08B6.

The comparison step is where the source's Noetherian and coherence hypotheses do their work.
The comparison `AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` between the two
systems is *not* an isomorphism at any single level — its kernel and cokernel are killed by a
power of `𝓘` and no more — so the step is a **pro-isomorphism**, an Artin–Rees phenomenon, and
only the inverse limits agree.  The passage from a pro-isomorphism to the identity of inverse
limits is proved here outright and with no hypothesis on the systems, by
`AlgebraicGeometry.Space.bijective_adicSectionsMap_of_isSeqProIso`.  What is not proved here is
the Artin–Rees input which feeds *that* step, namely the global pro-isomorphism
`AlgebraicGeometry.Space.IsAdicComparisonProIso`.  The tag does not depend on it: Stacks 08B6 is
proved under the source's own hypotheses alone by the chartwise route, as
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfNoetherian`, where the Artin–Rees
content is *derived* from Noetherianness and coherence at an affine chart through Stacks 09BB.

Two forms of that input are stated here, and they are not equivalent.
`AlgebraicGeometry.Space.IsAdicComparisonProIso` asks the comparison to be a pro-isomorphism
globally, and `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfProIso` derives the whole
identity from it and from nothing else; but it is stronger than the tag requires — it asks for a
family of morphisms of sheaves, natural in the chart, at one shift uniform over the charts, none
of which the identity uses — and it is accordingly *not* an obligation of Stacks 08B6; see its
docstring.  The form the identity actually needs is the chart-local one of
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_chartInterleaving`, which is what feeds
the chartwise hypothesis `h0882` of `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv`.

What *is* proved here about the input is its decomposition: by
`AlgebraicGeometry.Space.isSeqProIso_of_proSection_of_proCancellation` a pro-isomorphism may be
assembled from two independent halves at one common shift — a pro-section of the comparison, and
cancellation of the comparison by the descent maps of the source system — which is the form in
which an Artin–Rees argument delivers pro-surjectivity and pro-injectivity separately.  The
single interleaving family of `IsSeqProIso`, which must satisfy both triangles at once, does not
have to be produced directly.  `AlgebraicGeometry.Space.isSeqProIso_of_proSection_of_proRetraction`
is the same statement with the cancellation half in split form.

## Main definitions

* `AlgebraicGeometry.Space.seqDownTo` — the descent map of an inverse sequence of
  `𝒪_F`-modules, from level `m` to a level `n ≤ m`.
* `AlgebraicGeometry.Space.IsSeqProIso` — a morphism of inverse sequences of `𝒪_F`-modules is a
  pro-isomorphism: a cofinal shift and a family of morphisms back whose two composites with it
  are the descent maps of the two systems.
* `AlgebraicGeometry.Space.IsAdicComparisonProIso` — that condition for the comparison
  `AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp`.  It is not proved, and it
  is *not* an obligation of Stacks 08B6: the tag is proved by the chartwise route without it,
  and this condition is strictly stronger than the tag requires.

## Main results

* `AlgebraicGeometry.Space.bijective_adicSectionsMap_of_isSeqProIso` — **the comparison step of
  Stacks 08B6**: pro-isomorphic inverse systems of `𝒪_F`-modules have the same inverse limit of
  global sections.  Proved outright, with no hypothesis on the systems.
* `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_chartInterleaving` — the chartwise
  bijection from chart-local data: interleaving functions on the sections over one chart, at a
  shift attached to that chart, with no naturality in the chart asked of them.  This is strictly
  weaker than a pro-isomorphism and is what the tag's chartwise hypothesis needs.
* `AlgebraicGeometry.Space.isSeqProIso_of_proSection_of_proCancellation` and
  `AlgebraicGeometry.Space.isSeqProIso_of_proSection_of_proRetraction` — pro-surjectivity and
  pro-injectivity of one morphism of inverse sequences, at a common shift, assemble into a
  pro-isomorphism.  Proved outright, for arbitrary inverse sequences.
* `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfProIso` — the identity of
  Stacks 08B6 from the pro-isomorphism input, and from no other hypothesis; untagged, see its
  docstring.

## References

* [Stacks Project, Tag 08B6](https://stacks.math.columbia.edu/tag/08B6)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.PresheafOfModules.InternalHom

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-! ### Pro-isomorphisms of inverse systems of `𝒪_F`-modules -/

section ProIso

variable (X Y : ℕ → Modules.{u, m} B S hS F hF) (trX : ∀ n, X (n + 1) ⟶ X n)
    (trY : ∀ n, Y (n + 1) ⟶ Y n)

/-- Applying a composite of morphisms of `𝒪_F`-modules to a section over a chart is applying
the two morphisms in turn.

This is `AlgebraicGeometry.Space.Modules.comp_val_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesCompSections.lean`, restated with the chart object
spelled `(smallEtaleRingedSite B S hS F hF).C` rather than `SmallEtale B S hS F`.  The two
spellings are definitionally equal but not syntactically so, and `rw` needs this one: rewriting
with the canonical form here fails with "did not find an occurrence of the pattern".
The proof is not repeated — it delegates. -/
private theorem comp_val_app_apply {M N P : Modules.{u, m} B S hS F hF} (f : M ⟶ N) (g : N ⟶ P)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (x : M.val.obj U) :
    (f ≫ g).val.app U x = g.val.app U (f.val.app U x) :=
  Modules.comp_val_app B S hS f g U x

/-- The identity acts as the identity on sections over a chart. -/
private theorem id_val_app_apply {M : Modules.{u, m} B S hS F hF}
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) (x : M.val.obj U) :
    (𝟙 M : M ⟶ M).val.app U x = x := rfl

/-- **The descent map of an inverse sequence.**  The composite of the transition maps from
level `m` down to a level `n ≤ m`.  It is taken from the functor out of `ℕᵒᵖ` assembled from the
sequence of transition maps, so that its functoriality is that of a functor. -/
def seqDownTo {n m : ℕ} (h : n ≤ m) : X m ⟶ X n :=
  (Functor.ofOpSequence trX).map (homOfLE h).op

/-- Descending no levels is the identity. -/
@[simp]
theorem seqDownTo_self (n : ℕ) : seqDownTo B S hS F hF X trX (le_refl n) = 𝟙 (X n) :=
  (Functor.ofOpSequence trX).map_id (op n)

/-- Descending a single level is one transition map. -/
theorem seqDownTo_le_succ (n : ℕ) :
    seqDownTo B S hS F hF X trX (Nat.le_succ n) = trX n :=
  Functor.ofOpSequence_map_homOfLE_succ trX n

/-- Descending from `q` to `p` and then from `p` to `n` is descending from `q` to `n`. -/
theorem seqDownTo_trans {n p q : ℕ} (h₁ : n ≤ p) (h₂ : p ≤ q) :
    seqDownTo B S hS F hF X trX h₂ ≫ seqDownTo B S hS F hF X trX h₁ =
      seqDownTo B S hS F hF X trX (h₁.trans h₂) :=
  ((Functor.ofOpSequence trX).map_comp (homOfLE h₂).op (homOfLE h₁).op).symm

/-- Peeling one transition map off the bottom of a descent map. -/
theorem seqDownTo_succ {n m : ℕ} (h : n ≤ m) :
    seqDownTo B S hS F hF X trX (h.trans (Nat.le_succ m)) =
      trX m ≫ seqDownTo B S hS F hF X trX h := by
  rw [← seqDownTo_trans B S hS F hF X trX h (Nat.le_succ m), seqDownTo_le_succ]

/-- Descending a compatible family of sections to a lower level recovers its term there. -/
theorem seqDownTo_adicSectionsAt {U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ}
    (t : adicSectionsAt B S hS F hF X trX U) {n m : ℕ} (h : n ≤ m) :
    (seqDownTo B S hS F hF X trX h).val.app U (t.1 m) = t.1 n := by
  induction m, h using Nat.le_induction with
  | base => rw [seqDownTo_self, id_val_app_apply]
  | succ k hk ih =>
      rw [seqDownTo_succ B S hS F hF X trX hk, comp_val_app_apply, t.2 k]
      exact ih

variable (β : ∀ n : ℕ, X n ⟶ Y n)

/-- A morphism of inverse sequences commutes with the descent maps. -/
theorem seqDownTo_comp_beta (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    {n m : ℕ} (h : n ≤ m) :
    seqDownTo B S hS F hF X trX h ≫ β n = β m ≫ seqDownTo B S hS F hF Y trY h := by
  induction m, h using Nat.le_induction with
  | base => rw [seqDownTo_self, seqDownTo_self, Category.id_comp, Category.comp_id]
  | succ k hk ih =>
      rw [seqDownTo_succ B S hS F hF X trX hk, seqDownTo_succ B S hS F hF Y trY hk,
        Category.assoc, ih, ← Category.assoc, hβ k, Category.assoc]

/-- **A pro-isomorphism of inverse sequences of `𝒪_F`-modules.**  The morphism `β` is a
pro-isomorphism when it is invertible in the category of pro-objects, that is when there is a
cofinal shift `φ` and a family of morphisms `γ n : Y (φ n) ⟶ X n` going back, such that both
composites with `β` are the descent maps of the two systems:

`β (φ n) ≫ γ n = X (φ n) → X n`   and   `γ n ≫ β n = Y (φ n) → Y n`.

This is *not* a level-by-level isomorphism — `β n` itself need be neither injective nor
surjective at any `n`, and the shift `φ` is what absorbs the failure.  It is the condition that
the kernel and the cokernel of `β` are pro-zero, written as the interleaving data that
witnesses it. -/
def IsSeqProIso : Prop :=
  ∃ (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n) (γ : ∀ n, Y (φ n) ⟶ X n),
    (∀ n, β (φ n) ≫ γ n = seqDownTo B S hS F hF X trX (hφ n)) ∧
      (∀ n, γ n ≫ β n = seqDownTo B S hS F hF Y trY (hφ n))

/-- **Pro-surjectivity and pro-injectivity of one morphism assemble into a pro-isomorphism.**
Suppose that, with a single shift `c`, the morphism `β` of inverse sequences admits

* a *pro-section* `σ n : Y (n + c) ⟶ X n` with `σ n ≫ β n` the descent map of `Y`, which says
  that the cokernel of `β` is pro-zero, in split form, and
* *pro-cancellation* `hker`: the descent map `X (n + c) ⟶ X n` cancels `β (n + c)` on the
  right, that is any two morphisms into `X (n + c)` which `β (n + c)` identifies are already
  identified by that descent map.  In an abelian category this says exactly that the descent
  map kills the kernel of `β (n + c)`, that is that the kernel of `β` is pro-zero.

Neither half alone makes `β` a pro-isomorphism, but
`γ n = σ (n + c) ≫ (X (n + c) → X n)` satisfies both triangles of
`AlgebraicGeometry.Space.IsSeqProIso` at the shift `φ n = n + c + c`.  The second triangle is
the pro-section property pushed through `seqDownTo_comp_beta`.  For the first, the pro-section
property makes `β (n + c + c) ≫ σ (n + c)` and the descent map `X (n + c + c) ⟶ X (n + c)`
agree after `β (n + c)`, so pro-cancellation makes them agree after the descent map to `X n`,
and the two descent maps compose to the descent map asked for.

This splits the single interleaving datum of `IsSeqProIso`, which asks one family of morphisms
to satisfy both triangles at once, into two independent halves, which is the form in which an
Artin–Rees argument produces them. -/
theorem isSeqProIso_of_proSection_of_proCancellation (c : ℕ)
    (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    (σ : ∀ n : ℕ, Y (n + c) ⟶ X n)
    (hσ : ∀ n : ℕ, σ n ≫ β n = seqDownTo B S hS F hF Y trY (Nat.le_add_right n c))
    (hker : ∀ (n : ℕ) (W : Modules.{u, m} B S hS F hF) (g g' : W ⟶ X (n + c)),
      g ≫ β (n + c) = g' ≫ β (n + c) →
      g ≫ seqDownTo B S hS F hF X trX (Nat.le_add_right n c) =
        g' ≫ seqDownTo B S hS F hF X trX (Nat.le_add_right n c)) :
    IsSeqProIso B S hS F hF X Y trX trY β := by
  have hφ : ∀ n : ℕ, n ≤ n + c + c :=
    fun n => (Nat.le_add_right n c).trans (Nat.le_add_right (n + c) c)
  have t₁ : ∀ n : ℕ,
      β (n + c + c) ≫ σ (n + c) ≫ seqDownTo B S hS F hF X trX (Nat.le_add_right n c) =
        seqDownTo B S hS F hF X trX (hφ n) := by
    intro n
    have key : (β (n + c + c) ≫ σ (n + c)) ≫ β (n + c) =
        seqDownTo B S hS F hF X trX (Nat.le_add_right (n + c) c) ≫ β (n + c) := by
      rw [Category.assoc, hσ (n + c)]
      exact (seqDownTo_comp_beta B S hS F hF X Y trX trY β hβ
        (Nat.le_add_right (n + c) c)).symm
    rw [← Category.assoc, hker n _ _ _ key, seqDownTo_trans B S hS F hF X trX]
  have t₂ : ∀ n : ℕ,
      (σ (n + c) ≫ seqDownTo B S hS F hF X trX (Nat.le_add_right n c)) ≫ β n =
        seqDownTo B S hS F hF Y trY (hφ n) := by
    intro n
    rw [Category.assoc, seqDownTo_comp_beta B S hS F hF X Y trX trY β hβ (Nat.le_add_right n c),
      ← Category.assoc, hσ (n + c), seqDownTo_trans B S hS F hF Y trY]
  exact ⟨fun n => n + c + c, hφ,
    fun n => σ (n + c) ≫ seqDownTo B S hS F hF X trX (Nat.le_add_right n c), t₁, t₂⟩

/-- **A pro-section and a pro-retraction of the same morphism assemble into a
pro-isomorphism.**  The split form of
`AlgebraicGeometry.Space.isSeqProIso_of_proSection_of_proCancellation`: a *pro-retraction*
`ρ n : Y (n + c) ⟶ X n` with `β (n + c) ≫ ρ n` the descent map of `X` gives pro-cancellation
at once, since two morphisms identified by `β (n + c)` are then identified by that descent map.
The two families `σ` and `ρ` need not agree, and neither half alone makes `β` a
pro-isomorphism. -/
theorem isSeqProIso_of_proSection_of_proRetraction (c : ℕ)
    (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    (σ : ∀ n : ℕ, Y (n + c) ⟶ X n)
    (hσ : ∀ n : ℕ, σ n ≫ β n = seqDownTo B S hS F hF Y trY (Nat.le_add_right n c))
    (ρ : ∀ n : ℕ, Y (n + c) ⟶ X n)
    (hρ : ∀ n : ℕ, β (n + c) ≫ ρ n = seqDownTo B S hS F hF X trX (Nat.le_add_right n c)) :
    IsSeqProIso B S hS F hF X Y trX trY β :=
  isSeqProIso_of_proSection_of_proCancellation B S hS F hF X Y trX trY β c hβ σ hσ
    fun n _ g g' h => by rw [← hρ n, ← Category.assoc, ← Category.assoc, h]

/-- The monotone majorant of a sequence of natural numbers: `seqMax φ n` is the largest of
`φ 0, …, φ n`. -/
def seqMax (φ : ℕ → ℕ) : ℕ → ℕ
  | 0 => φ 0
  | n + 1 => max (seqMax φ n) (φ (n + 1))

/-- The monotone majorant dominates the sequence. -/
theorem le_seqMax (φ : ℕ → ℕ) : ∀ n, φ n ≤ seqMax φ n
  | 0 => le_refl _
  | _ + 1 => le_max_right _ _

/-- The monotone majorant is monotone, one step at a time. -/
theorem seqMax_le_succ (φ : ℕ → ℕ) (n : ℕ) : seqMax φ n ≤ seqMax φ (n + 1) :=
  le_max_left _ _

/-- **Chart-local interleaving data already gives the bijection on the inverse limits of the
sections over that chart.**  The hypotheses are the two triangles of
`AlgebraicGeometry.Space.IsSeqProIso` read over a single chart `U` and applied to sections:
the family going back is an arbitrary family of *functions* `g n` on the sections over `U`, not
a morphism of `𝒪_F`-modules, and the shift `φ` is attached to this chart alone.

This is the form in which an Artin–Rees argument on a chart delivers the data, and it is
strictly weaker than `AlgebraicGeometry.Space.IsSeqProIso`: no naturality in the chart is
asked of `g`, so the chartwise functions need not assemble into a morphism of sheaves, and no
shift uniform over the charts is asked for.  Since
`AlgebraicGeometry.Space.bijective_adicSectionsMap_of_bijective_adicSectionsMapAt` globalises
the *conclusion* — bijectivity, a property — rather than the data, a chart-dependent shift and a
non-natural choice of `g` are both harmless.

Injectivity: a term of a compatible family at level `n` is the descent of its term at level
`φ n`, which the first triangle rewrites as `g n` applied to the image under `β (φ n)`, so the
family is determined by its image.  Surjectivity: the second triangle makes
`σ m = g m (t (φ m))` a `β`-preimage of `t m` at every level, and although the `σ m` need not
be compatible, their descents `σ (seqMax φ n) ↦ X n` are: two `β`-equal elements at a level
above `φ n` have the same descent to `X n`, again by the first triangle, and the monotone
majorant makes the comparison available at every step. -/
theorem bijective_adicSectionsMapAt_of_chartInterleaving
    (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ)
    (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n)
    (g : ∀ n : ℕ, (Y (φ n)).val.obj U → (X n).val.obj U)
    (hg₁ : ∀ (n : ℕ) (x : (X (φ n)).val.obj U),
      g n ((β (φ n)).val.app U x) = (seqDownTo B S hS F hF X trX (hφ n)).val.app U x)
    (hg₂ : ∀ (n : ℕ) (y : (Y (φ n)).val.obj U),
      (β n).val.app U (g n y) = (seqDownTo B S hS F hF Y trY (hφ n)).val.app U y) :
    Function.Bijective (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U) := by
  have hcomm : ∀ (n m : ℕ) (h : n ≤ m) (x : (X m).val.obj U),
      (β n).val.app U ((seqDownTo B S hS F hF X trX h).val.app U x) =
        (seqDownTo B S hS F hF Y trY h).val.app U ((β m).val.app U x) := fun n m h x => by
    rw [← comp_val_app_apply, seqDownTo_comp_beta B S hS F hF X Y trX trY β hβ h,
      comp_val_app_apply]
  have hfact : ∀ (n m : ℕ) (hm : φ n ≤ m) (x : (X m).val.obj U),
      (seqDownTo B S hS F hF X trX ((hφ n).trans hm)).val.app U x =
        g n ((seqDownTo B S hS F hF Y trY hm).val.app U ((β m).val.app U x)) := by
    intro n m hm x
    rw [← hcomm _ _ hm x, hg₁, ← comp_val_app_apply, seqDownTo_trans]
  refine ⟨fun {s s'} hss => ?_, fun t => ?_⟩
  · have key : ∀ (z : adicSectionsAt B S hS F hF X trX U) (n : ℕ),
        z.1 n = g n ((β (φ n)).val.app U (z.1 (φ n))) := by
      intro z n
      rw [hg₁ n (z.1 (φ n))]
      exact (seqDownTo_adicSectionsAt B S hS F hF X trX z (hφ n)).symm
    refine Subtype.ext (funext fun n => ?_)
    rw [key s n, key s' n]
    exact congrArg (g n) (congrArg (fun z => z.1 (φ n)) hss)
  · obtain ⟨σ, hσ⟩ : ∃ σ : ∀ m : ℕ, (X m).val.obj U,
        ∀ m, (β m).val.app U (σ m) = t.1 m := by
      refine ⟨fun m => g m (t.1 (φ m)), fun m => ?_⟩
      rw [hg₂ m (t.1 (φ m))]
      exact seqDownTo_adicSectionsAt B S hS F hF Y trY t (hφ m)
    have hstab : ∀ (n m' m : ℕ) (h₁ : φ n ≤ m') (h₂ : m' ≤ m),
        (seqDownTo B S hS F hF X trX ((hφ n).trans h₁)).val.app U (σ m') =
          (seqDownTo B S hS F hF X trX ((hφ n).trans (h₁.trans h₂))).val.app U (σ m) := by
      intro n m' m h₁ h₂
      rw [hfact n m' h₁, hfact n m (h₁.trans h₂), hσ m', hσ m,
        seqDownTo_adicSectionsAt B S hS F hF Y trY t,
        seqDownTo_adicSectionsAt B S hS F hF Y trY t]
    refine ⟨⟨fun n => (seqDownTo B S hS F hF X trX
      ((hφ n).trans (le_seqMax φ n))).val.app U (σ (seqMax φ n)), fun n => ?_⟩, ?_⟩
    · rw [← comp_val_app_apply, ← seqDownTo_le_succ B S hS F hF X trX n, seqDownTo_trans]
      exact (hstab n (seqMax φ n) (seqMax φ (n + 1)) (le_seqMax φ n)
        (seqMax_le_succ φ n)).symm
    · refine Subtype.ext (funext fun n => ?_)
      change (β n).val.app U ((seqDownTo B S hS F hF X trX
        ((hφ n).trans (le_seqMax φ n))).val.app U (σ (seqMax φ n))) = t.1 n
      rw [hcomm, hσ, seqDownTo_adicSectionsAt B S hS F hF Y trY t]

/-- **A pro-isomorphism is a bijection on the inverse limits of the sections over a chart.**
Each chart receives the interleaving data of the pro-isomorphism by taking the sections of its
morphisms over that chart, which is
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_chartInterleaving`.  Only those
sections are used, and only over the one chart, so the global naturality of the family going
back and the uniformity of the shift over the charts are both spent for nothing here; that
observation is what the chart-local form records. -/
theorem bijective_adicSectionsMapAt_of_isSeqProIso
    (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    (hpro : IsSeqProIso B S hS F hF X Y trX trY β)
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    Function.Bijective (adicSectionsMapAt B S hS F hF X Y trX trY β hβ U) := by
  obtain ⟨φ, hφ, γ, hT₁, hT₂⟩ := hpro
  exact bijective_adicSectionsMapAt_of_chartInterleaving B S hS F hF X Y trX trY β hβ U φ hφ
    (fun n => (γ n).val.app U)
    (fun n x => congrArg (fun k : X (φ n) ⟶ X n => k.val.app U x) (hT₁ n))
    (fun n y => congrArg (fun k : Y (φ n) ⟶ Y n => k.val.app U y) (hT₂ n))

/-- **A pro-isomorphism of inverse systems of `𝒪_F`-modules induces a bijection on the inverse
limits of their global sections.**  Pro-isomorphic systems therefore have the same
`lim_n H⁰(F, -)`, although they are nowhere isomorphic level by level.  The chartwise statement
is `bijective_adicSectionsMapAt_of_isSeqProIso` and the passage to global sections is the étale
descent of `bijective_adicSectionsMap_of_bijective_adicSectionsMapAt`.

This is the step by which Stacks 08B6 identifies its left-hand side
`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗)` with `lim_n H⁰(F, 𝓗om(M, N / 𝓘 ^ n N))`: the comparison
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` between those two systems is
not an isomorphism at any single level, and the source's Noetherian and coherence hypotheses
enter only to make it a pro-isomorphism.  Once that is known, this theorem turns it into the
identity of inverse limits, with no hypothesis on the systems at all. -/
@[stacks 08B6 "the pro-isomorphism step: pro-isomorphic inverse systems of `𝒪_F`-modules have
the same inverse limit of global sections, which is what identifies the tag's two limits
`lim H⁰(𝓗 / 𝓘 ^ n 𝓗)` and `lim H⁰(𝓗om(M, N / 𝓘 ^ n N))` from a pro-isomorphism of the
comparison"]
theorem bijective_adicSectionsMap_of_isSeqProIso
    (hβ : ∀ n : ℕ, trX n ≫ β n = β (n + 1) ≫ trY n)
    (hpro : IsSeqProIso B S hS F hF X Y trX trY β) :
    Function.Bijective (adicSectionsMap B S hS F hF X Y trX trY β hβ) :=
  bijective_adicSectionsMap_of_bijective_adicSectionsMapAt B S hS F hF X Y trX trY β hβ
    (bijective_adicSectionsMapAt_of_isSeqProIso B S hS F hF X Y trX trY β hβ hpro)

end ProIso

/-! ### The comparison with the internal hom of the completion as a pro-isomorphism -/

section Comparison

variable (M N : Modules.{u, u} B S hS F hF)

/-- **A sufficient but deliberately stronger input for the identity of Stacks 08B6**: that the
comparison `AlgebraicGeometry.Space.smallEtaleInternalHomAdicComparisonApp` is a
pro-isomorphism of the inverse system of ideal-power quotients of `𝓗om(M, N)` with the inverse
system of the internal homs into the ideal-power quotients of `N`.

It is not proved in this tree, and **it is not an obligation of the tag either.**  This
predicate is a convenience of this file, not a statement Stacks 08B6 makes: it asks for a
single family of morphisms of `𝒪_F`-modules going back, natural in the étale chart, at one
shift `φ` uniform over all charts.  The tag's identity needs neither of those.  The only use
made of it is `AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_isSeqProIso`, which
consumes the family one chart at a time and only through its sections over that chart; so the
genuinely required input is the chart-local, chart-dependently shifted, non-natural data of
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_of_chartInterleaving`, which this
predicate implies and which does not imply it.  The tag's own route therefore runs through the
chartwise hypothesis `h0882` of `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv`, which
that chart-local lemma feeds, and not through this predicate.

So a reader should not record this as a gap in the formalisation of Stacks 08B6.  It remains
stated because it is the shape in which a *global* Artin–Rees argument would deliver the
comparison, and because
`AlgebraicGeometry.Space.isSeqProIso_of_proSection_of_proCancellation` splits it into the two
independent halves — pro-surjectivity and pro-injectivity at one common shift — in which such
an argument produces them.  Granted it,
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfProIso` yields the whole identity. -/
abbrev IsAdicComparisonProIso : Prop :=
  IsSeqProIso B S hS F hF
    (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS F hF M N))
    (fun n => smallEtaleInternalHom B S hS F hF M
      (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
    (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
      (smallEtaleInternalHom B S hS F hF M N))
    (fun n => smallEtaleInternalHomMapRight B S hS F hF M
      (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N))
    (smallEtaleInternalHomAdicComparisonApp B S hS F hF 𝓘 M N)

add_to_stacks 08B6 "the morphism step of the identity: morphisms of the inverse systems of
ideal-power quotients are exactly the compatible families of global sections of the internal
homs into those quotients, so that `Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))` is
`lim_n H⁰(F, 𝓗om(M, N / 𝓘 ^ n N))`" bijective_smallEtaleInternalHomAdicSection

/-- **The identity of Stacks 08B6 from the pro-isomorphism input alone.**

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`

for arbitrary `𝒪_F`-modules `M`, `N` and an arbitrary sheaf of ideals, granted only
`AlgebraicGeometry.Space.IsAdicComparisonProIso`: that the comparison between the two inverse
systems is a pro-isomorphism.  Everything else — the pro-isomorphism step
(`bijective_adicSectionsMap_of_isSeqProIso`), the identification of the global sections of the
internal hom with the morphisms (`smallEtaleInternalHomSectionsEquiv`) and the morphism step
(`bijective_smallEtaleInternalHomAdicSection`) — is proved outright in this file.

This is the same conclusion as `AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquiv` from a
different input.  That one assumes the chartwise bijectivity `h0882`, which is the source's own
route (étale descent to the Noetherian scheme case) and carries in addition the source's
Noetherian and coherence hypotheses, under which `h0882` is true.  This one assumes the
pro-isomorphism instead, which needs no hypothesis on `F`, `𝓘`, `M` or `N` in the signature
because the hypotheses are what would make it true.  Of the two inputs, `h0882` **is**
discharged — by
`AlgebraicGeometry.Space.bijective_adicSectionsMapAt_smallEtaleInternalHomAdic_of_isNoetherian`,
which is why the tag's full identity under the source's hypotheses alone is
`AlgebraicGeometry.Space.smallEtaleInternalHomAdicEquivOfNoetherian` — while the
pro-isomorphism assumed here is not.  So this route is the unfinished one of the two.

**No Stacks 08B6 registration is placed on this declaration**, for the same reason as there:
`hpro` is an assumed input and not one of the source's hypotheses. -/
def smallEtaleInternalHomAdicEquivOfProIso (hpro : IsAdicComparisonProIso B S hS F hF 𝓘 M N) :
    adicSections B S hS F hF
        (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS F hF M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHom B S hS F hF M N)) ≃
      (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M ⟶
        smallEtaleAdicQuotientSystem B S hS F hF 𝓘 N) :=
  ((Equiv.ofBijective _ (bijective_adicSectionsMap_of_isSeqProIso B S hS F hF _ _ _ _ _
        (smallEtaleInternalHomAdicComparison_compat B S hS F hF 𝓘 M N) hpro)).trans
      (Equiv.ofBijective _
        (bijective_smallEtaleInternalHomAdicSection B S hS F hF 𝓘 M N)).symm).trans
    (systemHomEquiv B S hS F hF _ _ _ _).symm

end Comparison

end AlgebraicGeometry.Space

end
