module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Countable direct sums and the presentation of a colimit over `ℕ`

Let `A` be a category and give `ℕ` its poset structure `0 ⟶ 1 ⟶ 2 ⟶ ⋯`. A *system over `ℕ`* in
`A` is a functor `F : ℕ ⥤ A`, that is, objects `Aₙ = F.obj n` together with transition maps
`fₙ : Aₙ ⟶ Aₙ₊₁`; its colimit is `colim Aₙ = colimit F`, with cocone maps `ιₙ`.

Assume `A` abelian and that colimits over `ℕ` exist and are exact: every system has a colimit and
`colim : (ℕ ⥤ A) ⥤ A` preserves finite limits. (Being a left adjoint, `colim` is automatically
additive and right exact, so preservation of finite limits is precisely the missing half of
exactness.) Then countable direct sums `∐ₙ Aₙ` exist in `A` and are exact, and every system sits
in a short exact sequence
`0 ⟶ ∐ₙ Aₙ --(1 - f)--> ∐ₙ Aₙ --π--> colim Aₙ ⟶ 0`,
where `1 - f` is the morphism with `σₙ ≫ (1 - f) = σₙ - fₙ ≫ σₙ₊₁` on the `n`-th coprojection
`σₙ`, and `π` is the morphism with `σₙ ≫ π = ιₙ`.

Countable direct sums come from colimits over `ℕ` because a countable coproduct is the filtered
colimit of its finite subsums and `n ↦ {0, …, n - 1}` is a cofinal functor
`ℕ ⥤ Finset (Discrete ℕ)`.

## Main definitions

* `Stacks.CountableCoproducts.SystemOverNat`: a system over `ℕ`, i.e. a functor `ℕ ⥤ A`.
* `Stacks.CountableCoproducts.oneSubShift`: the map `1 - f` on `∐ₙ Aₙ`.
* `Stacks.CountableCoproducts.piMap`: the map `π : ∐ₙ Aₙ ⟶ colim Aₙ`.

## Main results

* `Stacks.CountableCoproducts.hasColimitsOfShape_discrete_of_hasColimitsOfShape_nat`: countable
  direct sums exist.
* `Stacks.CountableCoproducts.preservesFiniteLimits_colim_discrete_of_hasColimitsOfShape_nat`: they
  are exact.
* `Stacks.CountableCoproducts.shortExact_oneSubShift_piMap`: the short exact sequence above.
* `Stacks.CountableCoproducts.oneSubShift_comp_sigmaComparison`: an additive functor takes
  `1 - f` to `1 - f`.

## Implementation notes

`piMap`, and its being an epimorphism, are the universal property of the colimit, so they ask for
no additive structure; `oneSubShift`, and the vanishing of the composite `(1 - f) ≫ π`, need only
subtraction of morphisms, so they ask for a preadditive category. Middle exactness
(`exact_oneSubShift_piMap`) — that `π` exhibits `colim Aₙ` as the *cokernel* of `1 - f` — is again
just the two universal properties and needs no exactness hypothesis, only enough structure for
the short complex to have homology; exactness of `colim` enters only in making `1 - f` a
monomorphism.

For that, `1 - f` is exhibited as a colimit of monomorphisms of systems. The partial sums
`Pₙ = A₀ ⊕ ⋯ ⊕ Aₙ₋₁` form a system `P` with `colim P = ∐ₙ Aₙ`, but `1 - f` is not an endomorphism
of `P`: on `Pₙ` the boundary term `fₙ₋₁ ≫ σₙ` leaves `Pₙ`. It is instead a morphism of systems
`P ⟹ P ∘ succ`, with components `Pₙ ⟶ Pₙ₊₁`, where that term lands in the extra summand, so the
squares commute on the nose and each component is a split monomorphism with an explicit
telescoping retraction. As `succ : ℕ ⥤ ℕ` is final, `colim (P ∘ succ) = colim P`, and an exact
`colim` preserves the monomorphism.

## References

* [Stacks Project, Tag 093W](https://stacks.math.columbia.edu/tag/093W) (Lemma 13.33.6).
-/

@[expose] public section

-- Works around the isDefEq-transparency change in this Lean bump: numerous `rw`/`calc`/
-- `simp` steps over category composition rely on defeq (not syntactic) object matching.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CountableCoproducts

variable {A : Type*} [Category A]

/-- A *system over `ℕ`* in `A` is a functor `ℕ ⥤ A`. Its `n`-th transition map
`fₙ : Aₙ ⟶ Aₙ₊₁` is `F.map (homOfLE (Nat.le_succ n))`. -/
abbrev SystemOverNat (A : Type*) [Category A] := ℕ ⥤ A

/-! ### The two maps `π` and `1 - f` -/

/-- The map `π : ∐ₙ Aₙ ⟶ colim Aₙ` induced by the cocone maps `ιₙ`: the unique morphism with
`σₙ ≫ π = ιₙ` for every `n`. -/
noncomputable def piMap (F : SystemOverNat A) [HasCoproduct F.obj] [HasColimit F] :
    (∐ F.obj) ⟶ colimit F :=
  Sigma.desc fun n => colimit.ι F n

/-- The defining property of `piMap`: `σₙ ≫ π = ιₙ`. -/
@[simp]
theorem ι_piMap (F : SystemOverNat A) [HasCoproduct F.obj] [HasColimit F] (n : ℕ) :
    Sigma.ι F.obj n ≫ piMap F = colimit.ι F n :=
  Sigma.ι_comp_desc _ _

/-- **`π` is an epimorphism.** The cocone maps `ιₙ` are jointly epic and each of them factors as
`σₙ ≫ π` through `π`. -/
theorem epi_piMap (F : SystemOverNat A) [HasCoproduct F.obj] [HasColimit F] : Epi (piMap F) := by
  refine ⟨fun {_} g h eq => colimit.hom_ext fun n => ?_⟩
  have h := Sigma.ι F.obj n ≫= eq
  rwa [← Category.assoc, ← Category.assoc, ι_piMap] at h

section Preadditive

variable [Preadditive A]

/-- The map `1 - f : ∐ₙ Aₙ ⟶ ∐ₙ Aₙ` of a system over `ℕ`: the unique morphism with
`σₙ ≫ (1 - f) = σₙ - fₙ ≫ σₙ₊₁` for every `n`, where the `σₙ` are the coprojections of `∐ₙ Aₙ`
and `fₙ` is the `n`-th transition map. -/
noncomputable def oneSubShift (F : SystemOverNat A) [HasCoproduct F.obj] :
    (∐ F.obj) ⟶ (∐ F.obj) :=
  Sigma.desc fun n => Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)

/-- The defining property of `oneSubShift`: in degree `n` it is `σₙ - fₙ ≫ σₙ₊₁`. -/
@[simp]
theorem ι_oneSubShift (F : SystemOverNat A) [HasCoproduct F.obj] (n : ℕ) :
    Sigma.ι F.obj n ≫ oneSubShift F
      = Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1) :=
  Sigma.ι_comp_desc _ _

/-- The composite `(1 - f) ≫ π` vanishes: on the `n`-th coprojection it is `ιₙ - fₙ ≫ ιₙ₊₁`, which
is zero because the cocone maps of a colimit satisfy `fₙ ≫ ιₙ₊₁ = ιₙ`. -/
theorem comp_oneSubShift_piMap (F : SystemOverNat A) [HasCoproduct F.obj] [HasColimit F] :
    oneSubShift F ≫ piMap F = 0 := by
  refine Sigma.hom_ext _ _ fun n => ?_
  rw [← Category.assoc, ι_oneSubShift, Preadditive.sub_comp, Category.assoc, ι_piMap, ι_piMap,
    comp_zero, colimit.w F (homOfLE (Nat.le_succ n)), sub_self]

/-- An additive functor `G` takes `1 - f` to `1 - f`: the coproduct comparison map of `G`
intertwines the map `1 - G fₙ` of the image system, written over the family `n ↦ G (Aₙ)`, with
`G (1 - f)`. -/
theorem oneSubShift_comp_sigmaComparison {B : Type*} [Category B] [Preadditive B] (G : A ⥤ B)
    [G.Additive] (F : SystemOverNat A) [HasCoproduct F.obj]
    [HasCoproduct fun n => G.obj (F.obj n)] :
    (Sigma.desc fun n => Sigma.ι (fun n => G.obj (F.obj n)) n -
        G.map (F.map (homOfLE (Nat.le_succ n))) ≫ Sigma.ι (fun n => G.obj (F.obj n)) (n + 1)) ≫
          sigmaComparison G F.obj
      = sigmaComparison G F.obj ≫ G.map (oneSubShift F) := by
  rw [oneSubShift, sigmaComparison_map_desc]
  refine Sigma.hom_ext _ _ fun n => ?_
  simp [Preadditive.sub_comp, ι_comp_sigmaComparison]

end Preadditive

variable [Abelian A]

/-! ### Countable direct sums exist and are exact

A countable coproduct is the filtered colimit, over the finite subsets of the index type, of the
corresponding finite subsums, and `n ↦ {0, …, n - 1}` is a cofinal functor
`ℕ ⥤ Finset (Discrete ℕ)`; so colimits over `ℕ` produce colimits over `Finset (Discrete ℕ)` and
hence countable coproducts, exactness being carried along at each step. -/

/-- The monotone map `n ↦ {⟨0⟩, …, ⟨n - 1⟩}` from `ℕ` to `Finset (Discrete ℕ)`. -/
private def coprodFinsetFun : ℕ → Finset (Discrete ℕ) :=
  fun n => Finset.image Discrete.mk (Finset.range n)

private theorem coprodFinsetFun_mono : Monotone coprodFinsetFun :=
  fun _ _ h => Finset.image_subset_image (Finset.range_mono h)

/-- The functor `ℕ ⥤ Finset (Discrete ℕ)` given by `coprodFinsetFun`; it is cofinal, every finite
set of indices being contained in some `{0, …, n - 1}`. -/
private def coprodFinsetFunctor : ℕ ⥤ Finset (Discrete ℕ) :=
  coprodFinsetFun_mono.functor

private instance coprodFinsetFunctor_final : coprodFinsetFunctor.Final := by
  rw [coprodFinsetFunctor, Monotone.final_functor_iff]
  intro S
  refine ⟨(S.image Discrete.as).sup id + 1, fun x hx => ?_⟩
  rw [coprodFinsetFun, Finset.mem_image]
  refine ⟨x.as, ?_, rfl⟩
  rw [Finset.mem_range]
  have : x.as ≤ (S.image Discrete.as).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem Discrete.as hx)
  omega

/-- **Countable direct sums exist.** If colimits over `ℕ` exist in `A`, then every countable
family of objects has a coproduct, i.e. `A` has colimits of shape `Discrete ℕ`. -/
@[stacks 093W]
theorem hasColimitsOfShape_discrete_of_hasColimitsOfShape_nat
    [HasColimitsOfShape ℕ A] :
    HasColimitsOfShape (Discrete ℕ) A := by
  have : HasColimitsOfShape (Finset (Discrete ℕ)) A :=
    Functor.Final.hasColimitsOfShape_of_final coprodFinsetFunctor
  exact ⟨fun F => HasColimit.mk (CoproductsFromFiniteFiltered.liftToFinsetColimitCocone F)⟩

/-- **Countable direct sums are exact.** If colimits over `ℕ` exist and are exact in `A`, then the
countable-coproduct functor `colim : (Discrete ℕ ⥤ A) ⥤ A` preserves finite limits — which, for a
right-exact additive left adjoint, is exactness: it carries short exact sequences to short exact
sequences. -/
@[stacks 093W]
theorem preservesFiniteLimits_colim_discrete_of_hasColimitsOfShape_nat
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A]
    (hexact : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A)) :
    PreservesFiniteLimits (colim : (Discrete ℕ ⥤ A) ⥤ A) := by
  have : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasColimitsOfShape (Finset (Discrete ℕ)) A :=
    Functor.Final.hasColimitsOfShape_of_final coprodFinsetFunctor
  have hfin : PreservesFiniteLimits (colim : (Finset (Discrete ℕ) ⥤ A) ⥤ A) := by
    have : PreservesFiniteLimits
        ((Functor.whiskeringLeft ℕ (Finset (Discrete ℕ)) A).obj coprodFinsetFunctor ⋙ colim) :=
      comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_natIso (Functor.Final.colimIso coprodFinsetFunctor (E := A))
  have : PreservesFiniteLimits (CoproductsFromFiniteFiltered.liftToFinset A ℕ) := inferInstance
  have : PreservesFiniteLimits (CoproductsFromFiniteFiltered.liftToFinset A ℕ ⋙ colim) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (CoproductsFromFiniteFiltered.liftToFinsetColimIso (C := A) (α := ℕ))

/-! ### The presentation of the colimit

The short complex `∐ₙ Aₙ --(1 - f)--> ∐ₙ Aₙ --π--> colim Aₙ` is short exact: `1 - f` is a
monomorphism (`mono_oneSubShift`), `π` is an epimorphism (`epi_piMap`) and the image of `1 - f` is
the kernel of `π` (`exact_oneSubShift_piMap`); `shortExact_oneSubShift_piMap` assembles the three.
-/

/-! #### Partial sums

`1 - f` is a monomorphism because it is a colimit of monomorphisms. The partial sums
`Pₙ = ∐_{i < n} Aᵢ` form a system `P` (`psSystem`) whose colimit is `∐ₙ Aₙ` (`psColimIso`), and
`1 - f` is the colimit of the morphism of systems `P ⟹ P ∘ succ` whose `n`-th component
`Pₙ ⟶ Pₙ₊₁` is `σᵢ ↦ σᵢ - fᵢ ≫ σᵢ₊₁` (`psLadder`, `tMap_eq_oneSubShift`); each component is a
split monomorphism, the retraction telescoping the transition maps (`isSplitMono_psLadder`). -/

/-- The `n`-th partial sum `Pₙ = ∐_{i < n} Aᵢ` of a system over `ℕ`. -/
private noncomputable def psObj (F : SystemOverNat A) (n : ℕ) : A :=
  ∐ fun i : Fin n => F.obj i.1

/-- The canonical inclusion `Pₙ ⟶ Pₙ₊₁` of partial sums, taking the summand `i` to the summand
`i.castSucc`. -/
private noncomputable def psStep (F : SystemOverNat A) (n : ℕ) : psObj F n ⟶ psObj F (n + 1) :=
  Sigma.desc fun i : Fin n =>
    Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1, by omega⟩

@[simp]
private lemma ι_psStep (F : SystemOverNat A) {n : ℕ} (i : Fin n) :
    Sigma.ι (fun i : Fin n => F.obj i.1) i ≫ psStep F n
      = Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1, by omega⟩ :=
  Sigma.ι_comp_desc _ _

/-- The system of partial sums `P : ℕ ⥤ A`, with objects `psObj` and transition maps `psStep`;
built by `Functor.ofSequence`, so functoriality is automatic. -/
private noncomputable def psSystem (F : SystemOverNat A) : SystemOverNat A :=
  Functor.ofSequence (psStep F)

@[simp]
private lemma psSystem_map_succ (F : SystemOverNat A) (n : ℕ) :
    (psSystem F).map (homOfLE (Nat.le_succ n)) = psStep F n :=
  Functor.ofSequence_map_homOfLE_succ (psStep F) n

@[simp]
private lemma psStep_comp_ι (F : SystemOverNat A) [HasColimitsOfShape ℕ A] (n : ℕ) :
    psStep F n ≫ colimit.ι (psSystem F) (n + 1) = colimit.ι (psSystem F) n := by
  rw [← psSystem_map_succ F n, colimit.w]

/-- A summand of a partial sum reaches `colim P` through the smallest partial sum containing it:
for `k < m` the summand `k` of `Pₘ` and the top summand of `Pₖ₊₁` have the same image. -/
private lemma ι_comp_ι_psSystem (F : SystemOverNat A) [HasColimitsOfShape ℕ A] (k : ℕ) :
    ∀ (m : ℕ) (h : k < m),
      Sigma.ι (fun j : Fin m => F.obj j.1) ⟨k, h⟩ ≫ colimit.ι (psSystem F) m
        = Sigma.ι (fun j : Fin (k + 1) => F.obj j.1) ⟨k, Nat.lt_succ_self k⟩
            ≫ colimit.ι (psSystem F) (k + 1) := by
  intro m
  induction m with
  | zero => exact fun h => absurd h (Nat.not_lt_zero k)
  | succ p ih =>
    intro h
    rcases Nat.lt_or_ge k p with hlt | hge
    · calc Sigma.ι (fun j : Fin (p + 1) => F.obj j.1) ⟨k, h⟩ ≫ colimit.ι (psSystem F) (p + 1)
          = (Sigma.ι (fun j : Fin p => F.obj j.1) ⟨k, hlt⟩ ≫ psStep F p)
              ≫ colimit.ι (psSystem F) (p + 1) := by rw [ι_psStep]
        _ = Sigma.ι (fun j : Fin p => F.obj j.1) ⟨k, hlt⟩ ≫ colimit.ι (psSystem F) p := by
              rw [Category.assoc, psStep_comp_ι]
        _ = _ := ih hlt
    · obtain rfl : k = p := by omega
      rfl

/-- The cocone leg `Pₙ ⟶ ∐ₙ Aₙ`, taking the summand `i` by the coprojection `σᵢ`. -/
private noncomputable def psLeg (F : SystemOverNat A) [HasColimitsOfShape (Discrete ℕ) A]
    (n : ℕ) : psObj F n ⟶ (∐ F.obj) :=
  Sigma.desc fun i : Fin n => Sigma.ι F.obj i.1

@[simp]
private lemma ι_psLeg (F : SystemOverNat A) [HasColimitsOfShape (Discrete ℕ) A] {n : ℕ}
    (i : Fin n) : Sigma.ι (fun i : Fin n => F.obj i.1) i ≫ psLeg F n = Sigma.ι F.obj i.1 :=
  Sigma.ι_comp_desc _ _

/-- The cocone on a system over `ℕ` with legs `f n`, given compatibility of consecutive legs. -/
private noncomputable def sequenceCocone {F : SystemOverNat A} {Z : A} (f : ∀ n, F.obj n ⟶ Z)
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ f (n + 1) = f n) : Cocone F where
  pt := Z
  ι := NatTrans.ofSequence (F := F) (G := (Functor.const ℕ).obj Z) f fun n =>
    (h n).trans (Category.comp_id _).symm

/-- The cocone on the system of partial sums with apex `∐ₙ Aₙ` and legs `psLeg`. -/
private noncomputable def psCocone (F : SystemOverNat A) [HasColimitsOfShape (Discrete ℕ) A] :
    Cocone (psSystem F) :=
  sequenceCocone (psLeg F) fun n => by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [psSystem_map_succ, ← Category.assoc, ι_psStep, ι_psLeg, ι_psLeg]

@[simp]
private lemma psCocone_ι_app (F : SystemOverNat A) [HasColimitsOfShape (Discrete ℕ) A] (n : ℕ) :
    (psCocone F).ι.app n = psLeg F n := rfl

/-- The colimit of the system of partial sums is the countable direct sum, `colim P = ∐ₙ Aₙ`. The
inverse takes the coprojection `σₙ` to the top summand of `Pₙ₊₁`. -/
private noncomputable def psColimIso (F : SystemOverNat A)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A] :
    colimit (psSystem F) ≅ (∐ F.obj) where
  hom := colimit.desc (psSystem F) (psCocone F)
  inv := Sigma.desc fun n => Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨n, Nat.lt_succ_self n⟩
    ≫ colimit.ι (psSystem F) (n + 1)
  hom_inv_id := by
    refine colimit.hom_ext fun n => ?_
    rw [← Category.assoc, colimit.ι_desc, psCocone_ι_app, Category.comp_id]
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, ι_psLeg, Sigma.ι_comp_desc]
    exact (ι_comp_ι_psSystem F i.1 n i.2).symm
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, colimit.ι_desc, psCocone_ι_app,
      ι_psLeg, Category.comp_id]

@[simp]
private lemma ι_comp_psColimIso_hom (F : SystemOverNat A)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A] (n : ℕ) :
    colimit.ι (psSystem F) n ≫ (psColimIso F).hom = psLeg F n :=
  colimit.ι_desc _ _

@[simp]
private lemma ι_comp_psColimIso_inv (F : SystemOverNat A)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A] (n : ℕ) :
    Sigma.ι F.obj n ≫ (psColimIso F).inv
      = Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨n, Nat.lt_succ_self n⟩
          ≫ colimit.ι (psSystem F) (n + 1) :=
  Sigma.ι_comp_desc _ _

/-- The ladder map `Pₙ ⟶ Pₙ₊₁`, `σᵢ ↦ σᵢ - fᵢ ≫ σᵢ₊₁`. There is no boundary case: the index
`i + 1` of the released term is a legitimate summand of `Pₙ₊₁`. -/
private noncomputable def psLadder (F : SystemOverNat A) (n : ℕ) : psObj F n ⟶ psObj F (n + 1) :=
  Sigma.desc fun i : Fin n =>
    Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1, by omega⟩
      - F.map (homOfLE (Nat.le_succ i.1))
          ≫ Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1 + 1, by omega⟩

@[simp]
private lemma ι_psLadder (F : SystemOverNat A) {n : ℕ} (i : Fin n) :
    Sigma.ι (fun i : Fin n => F.obj i.1) i ≫ psLadder F n
      = Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1, by omega⟩
        - F.map (homOfLE (Nat.le_succ i.1))
            ≫ Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1 + 1, by omega⟩ :=
  Sigma.ι_comp_desc _ _

/-- The retraction `Pₙ₊₁ ⟶ Pₙ` of the ladder map: the summand `j` maps by the sum, over the
indices `k < n` with `j ≤ k`, of the transition composite `A_j ⟶ A_k` followed by `σ_k`. -/
private noncomputable def psRetraction (F : SystemOverNat A) (n : ℕ) :
    psObj F (n + 1) ⟶ psObj F n :=
  Sigma.desc fun j : Fin (n + 1) =>
    ∑ k : Fin n, if h : j.1 ≤ k.1 then
      F.map (homOfLE h) ≫ Sigma.ι (fun i : Fin n => F.obj i.1) k else 0

@[simp]
private lemma ι_psRetraction (F : SystemOverNat A) {n : ℕ} (j : Fin (n + 1)) :
    Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) j ≫ psRetraction F n
      = ∑ k : Fin n, if h : j.1 ≤ k.1 then
          F.map (homOfLE h) ≫ Sigma.ι (fun i : Fin n => F.obj i.1) k else 0 :=
  Sigma.ι_comp_desc _ _

/-- The telescoping identity that makes `psRetraction` a retraction of `psLadder`:
`ρᵢ - fᵢ ≫ ρᵢ₊₁ = σᵢ`, all the terms of the two sums cancelling in pairs except the `k = i` term
of the first, which is `σᵢ`. -/
private lemma psRetraction_telescope (F : SystemOverNat A) {n : ℕ} (i : Fin n) :
    (Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1, by omega⟩ ≫ psRetraction F n)
      - F.map (homOfLE (Nat.le_succ i.1))
          ≫ (Sigma.ι (fun j : Fin (n + 1) => F.obj j.1) ⟨i.1 + 1, by omega⟩ ≫ psRetraction F n)
      = Sigma.ι (fun i : Fin n => F.obj i.1) i := by
  rw [ι_psRetraction, ι_psRetraction, Preadditive.comp_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single i]
  · have hii : i.1 ≤ i.1 := le_refl _
    have hnii : ¬ (i.1 + 1 ≤ i.1) := by omega
    rw [dite_eq_left hii, dite_eq_right hnii, comp_zero, sub_zero,
      show F.map (homOfLE hii) = 𝟙 (F.obj i.1) by
        rw [show (homOfLE hii : i.1 ⟶ i.1) = 𝟙 i.1 from Subsingleton.elim _ _, F.map_id],
      Category.id_comp]
  · intro k _ hk
    by_cases hik : i.1 ≤ k.1
    · have hik1 : i.1 + 1 ≤ k.1 := Nat.lt_of_le_of_ne hik fun h => hk (Fin.ext h.symm)
      rw [dite_eq_left hik, dite_eq_left hik1, ← Category.assoc, ← F.map_comp,
        show (homOfLE (Nat.le_succ i.1) ≫ homOfLE hik1 : i.1 ⟶ k.1) = homOfLE hik from
          Subsingleton.elim _ _, sub_self]
    · have hik1 : ¬ (i.1 + 1 ≤ k.1) := by omega
      rw [dite_eq_right hik, dite_eq_right hik1, comp_zero, sub_zero]
  · exact fun h => absurd (Finset.mem_univ i) h

/-- Each ladder map is a split monomorphism, `psRetraction` being an explicit retraction. -/
private lemma isSplitMono_psLadder (F : SystemOverNat A) (n : ℕ) :
    IsSplitMono (psLadder F n) :=
  IsSplitMono.mk' ⟨psRetraction F n, Sigma.hom_ext _ _ fun i => by
    rw [← Category.assoc, ι_psLadder, Preadditive.sub_comp, Category.assoc,
      psRetraction_telescope]
    exact (Category.comp_id _).symm⟩

/-- The ladder square, which commutes on the nose:
`psStep F n ≫ psLadder F (n + 1) = psLadder F n ≫ psStep F (n + 1)`. -/
private lemma psStep_comp_psLadder (F : SystemOverNat A) (n : ℕ) :
    psStep F n ≫ psLadder F (n + 1) = psLadder F n ≫ psStep F (n + 1) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, ι_psStep, ι_psLadder, ← Category.assoc, ι_psLadder,
    Preadditive.sub_comp, Category.assoc, ι_psStep, ι_psStep]

/-- The cocone on the system of partial sums with apex `colim P` whose `n`-th leg is the ladder
map followed by `ιₙ₊₁`; its compatibility is the ladder square. -/
private noncomputable def psLadderCocone (F : SystemOverNat A) [HasColimitsOfShape ℕ A] :
    Cocone (psSystem F) :=
  sequenceCocone (fun n => psLadder F n ≫ colimit.ι (psSystem F) (n + 1)) fun n => by
    rw [psSystem_map_succ, ← Category.assoc, psStep_comp_psLadder, Category.assoc, psStep_comp_ι]

/-- The endomorphism of `colim P` induced by the ladder; it realizes `1 - f` under
`psColimIso` (`tMap_eq_oneSubShift`). -/
private noncomputable def tMap (F : SystemOverNat A) [HasColimitsOfShape ℕ A] :
    colimit (psSystem F) ⟶ colimit (psSystem F) :=
  colimit.desc (psSystem F) (psLadderCocone F)

@[simp]
private lemma ι_comp_tMap (F : SystemOverNat A) [HasColimitsOfShape ℕ A] (n : ℕ) :
    colimit.ι (psSystem F) n ≫ tMap F = psLadder F n ≫ colimit.ι (psSystem F) (n + 1) :=
  colimit.ι_desc _ _

/-- `tMap` is a monomorphism: it is `colim` of the ladder, a morphism of systems
`P ⟹ P ∘ succ` with split monomorphic components, followed by the isomorphism
`colim (P ∘ succ) ≅ colim P` coming from finality of `succ : ℕ ⥤ ℕ`. -/
private lemma mono_tMap [HasColimitsOfShape ℕ A]
    (hexact : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A))
    (F : SystemOverNat A) : Mono (tMap F) := by
  let succF : ℕ ⥤ ℕ := Monotone.functor (f := fun n => n + 1) fun a b h => by dsimp; omega
  have succF_final : succF.Final := (Monotone.final_functor_iff _).2 fun d => ⟨d, by omega⟩
  -- The ladder as a morphism of systems `P ⟹ P ∘ succ`: its component at `n` has the right type
  -- because `(succF ⋙ psSystem F).obj n` is `Pₙ₊₁`, and its naturality is the ladder square.
  let a : psSystem F ⟶ succF ⋙ psSystem F :=
    NatTrans.ofSequence (F := psSystem F) (G := succF ⋙ psSystem F) (fun n => psLadder F n)
      fun n => by
        have hG : (succF ⋙ psSystem F).map (homOfLE (Nat.le_succ n)) = psStep F (n + 1) := by
          change (psSystem F).map (succF.map (homOfLE (Nat.le_succ n))) = psStep F (n + 1)
          rw [show succF.map (homOfLE (Nat.le_succ n)) = homOfLE (Nat.le_succ (n + 1)) from
            Subsingleton.elim _ _, psSystem_map_succ]
          rfl
        rw [psSystem_map_succ, hG, psStep_comp_psLadder]
  have : ∀ n, Mono (a.app n) := fun n => by
    have := isSplitMono_psLadder F n
    change Mono (psLadder F n)
    infer_instance
  have : Mono a := NatTrans.mono_of_mono_app a
  have : PreservesLimitsOfShape WalkingCospan (colim : (ℕ ⥤ A) ⥤ A) :=
    hexact.preservesFiniteLimits _
  have : (colim : (ℕ ⥤ A) ⥤ A).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have key : tMap F = colim.map a ≫ colimit.pre (psSystem F) succF := by
    refine colimit.hom_ext fun n => ?_
    have hmap : colimit.ι (psSystem F) n ≫ colim.map a
        = a.app n ≫ colimit.ι (succF ⋙ psSystem F) n := by simp [colim]
    rw [ι_comp_tMap, ← Category.assoc, hmap, Category.assoc, colimit.ι_pre]
    rfl
  rw [key]
  exact mono_comp _ _

/-- Under `psColimIso`, the endomorphism `tMap` of `colim P` is the map `1 - f` of `∐ₙ Aₙ`. Both
sides are read on the `n`-th leg of `colim P` and then on each summand of `Pₙ`, where they become
the same difference of two summand inclusions, up to sliding each of them into the smallest
partial sum that contains it (`ι_comp_ι_psSystem`). -/
private lemma tMap_eq_oneSubShift (F : SystemOverNat A)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A] :
    (psColimIso F).hom ≫ oneSubShift F ≫ (psColimIso F).inv = tMap F := by
  refine colimit.hom_ext fun n => ?_
  rw [ι_comp_tMap, ← Category.assoc, ι_comp_psColimIso_hom]
  refine Sigma.hom_ext _ _ fun i => ?_
  have hR : Sigma.ι (fun i : Fin n => F.obj i.1) i
        ≫ psLadder F n ≫ colimit.ι (psSystem F) (n + 1)
      = (Sigma.ι (fun j : Fin (i.1 + 1) => F.obj j.1) ⟨i.1, Nat.lt_succ_self i.1⟩
            ≫ colimit.ι (psSystem F) (i.1 + 1))
        - F.map (homOfLE (Nat.le_succ i.1))
            ≫ (Sigma.ι (fun j : Fin (i.1 + 1 + 1) => F.obj j.1)
                  ⟨i.1 + 1, Nat.lt_succ_self (i.1 + 1)⟩
                ≫ colimit.ι (psSystem F) (i.1 + 1 + 1)) := by
    rw [← Category.assoc, ι_psLadder, Preadditive.sub_comp, Category.assoc,
      ι_comp_ι_psSystem F i.1 (n + 1) (Nat.lt_succ_of_lt i.2),
      ι_comp_ι_psSystem F (i.1 + 1) (n + 1) (Nat.succ_lt_succ i.2)]
  rw [hR, ← Category.assoc, ι_psLeg, ← Category.assoc, ι_oneSubShift, Preadditive.sub_comp,
    Category.assoc, ι_comp_psColimIso_inv, ι_comp_psColimIso_inv]

/-- **`1 - f` is a monomorphism.** It is conjugate to `tMap`, the colimit of a morphism of systems
with split monomorphic components. -/
theorem mono_oneSubShift
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A]
    (hexact : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A))
    (F : SystemOverNat A) : Mono (oneSubShift F) := by
  have : Mono (tMap F) := mono_tMap hexact F
  have hrw : oneSubShift F = (psColimIso F).inv ≫ tMap F ≫ (psColimIso F).hom := by
    rw [← tMap_eq_oneSubShift F]
    simp
  rw [hrw]
  infer_instance

/-- **The short complex `∐ₙ Aₙ --(1 - f)--> ∐ₙ Aₙ --π--> colim Aₙ` is exact in the middle**, i.e.
the image of `1 - f` is the kernel of `π`.

The source deduces this from exactness of `colim`, applied to a levelwise split short exact
sequence of systems. It is in fact the universal property of the two colimits and needs no
exactness hypothesis: `π` exhibits `colim Aₙ` as the *cokernel* of `1 - f`. Indeed a morphism
`g : ∐ₙ Aₙ ⟶ Z` kills `1 - f` exactly when its components satisfy `fₙ ≫ gₙ₊₁ = gₙ`, that is,
exactly when they form a cocone on the system, and such a cocone factors uniquely through
`colim Aₙ`. -/
theorem exact_oneSubShift_piMap (F : SystemOverNat A) [HasCoproduct F.obj] [HasColimit F] :
    (ShortComplex.mk (oneSubShift F) (piMap F) (comp_oneSubShift_piMap F)).Exact := by
  -- A morphism killing `1 - f` has components forming a cocone on the system.
  have hstep : ∀ {Z : A} (g : (∐ F.obj) ⟶ Z), oneSubShift F ≫ g = 0 →
      ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ (Sigma.ι F.obj (n + 1) ≫ g)
        = Sigma.ι F.obj n ≫ g := by
    intro Z g eq n
    have h := Sigma.ι F.obj n ≫= eq
    rw [← Category.assoc, ι_oneSubShift, Preadditive.sub_comp, Category.assoc, comp_zero] at h
    rw [← sub_eq_zero.mp h]
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ _ _ ?desc ?fac ?uniq
  · -- The factorization of such a `g` through `colim Aₙ`.
    intro Z g eq
    exact colimit.desc F (sequenceCocone (fun n => Sigma.ι F.obj n ≫ g) (hstep g eq))
  · -- It does factor `g`: check on each coprojection.
    intro Z g eq
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, ι_piMap, colimit.ι_desc]
    rfl
  · -- It is the only factorization: the cocone maps are jointly epic.
    intro Z g eq m hm
    refine colimit.hom_ext fun n => ?_
    rw [colimit.ι_desc]
    have h := Sigma.ι F.obj n ≫= hm
    rwa [← Category.assoc, ι_piMap] at h

/-- **The presentation of the colimit: Lemma 093W(2).** For every system over `ℕ` in an abelian
category with countable direct sums and colimits over `ℕ` that are exact, the sequence
`0 ⟶ ∐ₙ Aₙ --(1 - f)--> ∐ₙ Aₙ --π--> colim Aₙ ⟶ 0` is short exact. -/
@[stacks 093W]
theorem shortExact_oneSubShift_piMap
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) A]
    (hexact : PreservesFiniteLimits (colim : (ℕ ⥤ A) ⥤ A))
    (F : SystemOverNat A) :
    ∃ w : oneSubShift F ≫ piMap F = 0,
      (ShortComplex.mk (oneSubShift F) (piMap F) w).ShortExact := by
  refine ⟨comp_oneSubShift_piMap F, ?_⟩
  have := mono_oneSubShift hexact F
  have := epi_piMap F
  exact ⟨exact_oneSubShift_piMap F⟩

end Stacks.CountableCoproducts
