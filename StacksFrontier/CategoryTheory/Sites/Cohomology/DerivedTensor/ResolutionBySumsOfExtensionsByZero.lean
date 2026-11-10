module

public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroGenerators
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ShortComplexDiagramHomology
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import Mathlib.Algebra.Homology.Embedding.TruncLE
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Resolutions by direct sums of extensions by zero on a ringed site

Let `(C, J, R)` be a ringed site with `C` small. Every complex `G` of `O`-modules, where
`O = Stacks.SheafOfModules.Tensor.ringSheaf R`, carries a compatible ladder of bounded-above
resolutions of its upper truncations `τ_{≤ n} G`, whose terms and whose successive cokernels
are direct sums of extensions by zero `j_{U!}O_U` of the structure sheaves of slices, and
whose colimit is quasi-isomorphic to `G`.

The declarations below live in the namespace `Stacks.DerivedTensor.ResolutionByExtensionsByZero`.

## Main definitions

* `IsSumOfExtensionByZeroStructureSheaves`: the property of being a direct sum of modules
  `j_{U!}O_U`.
* `ResolutionByDirectSumsExtensionsByZero`: the whole compatible ladder, together with the
  comparison from its colimit.

## Main results

* `exists_resolutionByDirectSumsExtensionsByZero`: such a ladder exists for every complex.

## Implementation notes

The natural-number index `n` of the ladder corresponds to the truncation bound `n + 1` in the
source, so that the ladder starts at `τ_{≤ 1} G` as in the Stacks diagram. The ladder itself
comes from `CochainComplex.exists_sequence_quasiIso_truncLE` (Stacks 06XX), applied to the
object property `IsSumOfExtensionByZeroStructureSheaves`; its three inputs are the three
private lemmas below. Only the cover is mathematical content, and it is exactly
`SheafOfModules.exists_epi_from_coproduct_extensionByZero`, the sheaf-level half of 03EW.
Because the property is not assumed closed under isomorphism, each input is phrased with an
explicit isomorphism, which for the cover is `Iso.refl` — the epimorphism produced there is
already out of a sum in precisely this shape.

Mathlib has no transition map `τ_{≤ a} G ⟶ τ_{≤ b} G`; `truncationTransition` builds it as
`(ι_{τ_{≤ a} G})⁻¹ ≫ τ_{≤ b}(ι_{τ_{≤ a} G})`, using that `τ_{≤ a} G` is strictly `≤ b` for
`b ≥ a` so its own inclusion is invertible. It is characterised by its composite with
`ιTruncLE`, which is how both the structure field and the ladder square are stated and
proved; `eq_of_comp_ιTruncLE_of_strictlyLE` is the cancellation that makes that
characterisation an equality of maps.

The shift by one is also why the colimit comparison needs its own quasi-isomorphism lemma:
the private `quasiIso_of_isColimit_of_quasiIso_truncLE` of
`StacksFrontier/Homology/KFlat/Resolution.lean` is stated at bound `n`, and the four
colimit-preservation facts it rests on are likewise private there, so generic copies at an
arbitrary monotone unbounded family of bounds appear here.

All truncation bounds are written as a single cast of a natural number, `((n + 1 : ℕ) : ℤ)`
and `((n + 1 + 1 : ℕ) : ℤ)`, and never as `(n : ℤ) + 1` and `(n : ℤ) + 2`. This is not
cosmetic. With the latter spelling the two sides of `square` have codomains
`G.truncLE (↑(n + 1) + 1)` and `G.truncLE ((n : ℤ) + 2)`, which are definitionally equal only
after unfolding the `ℤ` numeral `2` through the structure projections of its `CommRing`
instance; `isDefEq` cannot close that by congruence on `truncLE`'s argument and unfolds
`truncLE` itself instead. That is what the store's `maxHeartbeats 2000000` on this statement
was paying for. Doing the arithmetic in `ℕ` under one cast makes both codomains the same
term, and the declaration elaborates in seconds with no option set.

The residue of the same effect is why the `square` proof is a term-mode chain of
`Category.assoc` and `congrArg` rather than `rw`/`simp`: `Functor.ofSequence` presents its
morphisms through `catToReflQuiver`, so the composite coming out of the ladder and the one
coming out of `f` carry different — definitionally equal — `CategoryStruct` instances.
`rw` builds its motive at `instances` transparency and cannot match across them, while
`exact` and `calc` unify at default transparency and can. For the same reason the one place
that does rewrite with `hmap` (`key`) does nothing afterwards but `exact`: a `rw` of a
functor's action on objects leaves the goal ill-typed at `instances` transparency, and any
later `rw` or `simp` then fails.

## References

* [Stacks Project, Tag 077J](https://stacks.math.columbia.edu/tag/077J)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.DerivedTensor.ResolutionByExtensionsByZero

section Colimit

variable {A : Type*} [Category A] [Abelian A]

/-- **A sequential colimit of quasi-isomorphisms onto a cofinal family of upper truncations
is a quasi-isomorphism.** The bounds `b n` are only required to be monotone and unbounded
above, which is what lets the ladder be indexed with a shift. -/
private lemma quasiIso_of_isColimit_of_quasiIso_truncLE
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    {b : ℕ → ℤ} (hbmono : Monotone b) (hbtop : ∀ i : ℤ, ∃ n : ℕ, i ≤ b n)
    {X : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ} {g : ∀ n : ℕ, Q n ⟶ Q (n + 1)}
    (f : ∀ n : ℕ, Q n ⟶ X.truncLE (b n)) (hf : ∀ n, QuasiIso (f n))
    {c : Cocone (Functor.ofSequence g)} (hc : IsColimit c) (α : c.pt ⟶ X)
    (hα : ∀ n : ℕ, c.ι.app n ≫ α = f n ≫ X.ιTruncLE (b n)) :
    QuasiIso α := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  set H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor (A := A) (J := ℕ)
    (ComplexShape.up ℤ) i
  have hqis : ∀ {K L : CochainComplex A ℤ} (φ : K ⟶ L), QuasiIsoAt φ i → IsIso (H.map φ) :=
    fun φ h ↦ (quasiIsoAt_iff_isIso_homologyMap φ i).1 h
  have hiso : ∀ n : ℕ, i ≤ b n → IsIso (H.map (c.ι.app n ≫ α)) := by
    intro n hn
    have h₁ := hqis _ ((quasiIso_iff _).1 (hf n) i)
    have h₂ := hqis _ (CochainComplex.quasiIsoAt_ιTruncLE X (b n) i hn)
    rw [(congrArg H.map (hα n)).trans (H.map_comp _ _)]
    exact IsIso.comp_isIso' h₁ h₂
  have w : ∀ j j' (φ : j ⟶ j'), (Functor.ofSequence g ⋙ H).map φ ≫ H.map (c.ι.app j' ≫ α)
      = H.map (c.ι.app j ≫ α) := fun j j' φ ↦ by
    rw [Functor.comp_map, ← H.map_comp, ← Category.assoc, c.w φ]
  obtain ⟨n₀, hn₀⟩ := hbtop i
  have hev : (Functor.ofSequence g ⋙ H).IsEventuallyConstantFrom n₀ := by
    intro j φ
    have := hiso j (hn₀.trans (hbmono (leOfHom φ)))
    have := hiso n₀ hn₀
    exact IsIso.of_isIso_fac_right (w _ _ φ)
  let v : Cocone (Functor.ofSequence g ⋙ H) :=
    Cocone.mk (H.obj X)
      { app := fun n ↦ H.map (c.ι.app n ≫ α)
        naturality := fun j j' φ ↦ by simp }
  have hv₀ : IsIso (v.ι.app n₀) := hiso n₀ hn₀
  have hv : IsColimit v := hev.isColimitOfIsIso v
  have hHc : IsColimit (H.mapCocone c) := isColimitOfPreserves H hc
  have heq : H.map α = (hHc.coconePointUniqueUpToIso hv).hom := by
    refine hHc.hom_ext (fun n ↦ ?_)
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (H.map_comp _ _).symm
  change IsIso (H.map α)
  rw [heq]
  infer_instance

/-- **The transition `τ_{≤ n+1} G ⟶ τ_{≤ n+2} G` between successive upper truncations.**
Mathlib has no such map; it is built from the inclusion of `τ_{≤ n+1} G`, which is invertible
because that complex is already strictly `≤ n+2`. -/
noncomputable def truncationTransition (G : CochainComplex A ℤ) (n : ℕ) :
    G.truncLE ((n + 1 : ℕ) : ℤ) ⟶ G.truncLE ((n + 1 + 1 : ℕ) : ℤ) := by
  have := CochainComplex.isStrictlyLE_of_le (K := G.truncLE ((n + 1 : ℕ) : ℤ))
    ((n + 1 : ℕ) : ℤ) ((n + 1 + 1 : ℕ) : ℤ) (by push_cast; omega)
  exact inv ((G.truncLE ((n + 1 : ℕ) : ℤ)).ιTruncLE ((n + 1 + 1 : ℕ) : ℤ)) ≫
    CochainComplex.truncLEMap (G.ιTruncLE ((n + 1 : ℕ) : ℤ)) ((n + 1 + 1 : ℕ) : ℤ)

/-- The transition `τ_{≤ n+1} G ⟶ τ_{≤ n+2} G` commutes with the inclusions into `G`. -/
@[simp]
lemma truncationTransition_ιTruncLE (G : CochainComplex A ℤ) (n : ℕ) :
    truncationTransition G n ≫ G.ιTruncLE ((n + 1 + 1 : ℕ) : ℤ)
      = G.ιTruncLE ((n + 1 : ℕ) : ℤ) := by
  dsimp only [truncationTransition]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

/-- **The whole ladder, over an abstract abelian category.** This is 06XX's conclusion
reindexed so that index `n` carries the truncation bound `n + 1`, with the transition maps
between successive truncations supplied and the colimit comparison built and shown to be a
quasi-isomorphism. Everything in 077J except the cover is here, and stating it for an
abstract `A` is what keeps the assembly over sheaves of modules a matter of naming fields:
no `Functor.ofSequence`, `NatTrans.ofSequence` or `colimit.desc` is ever elaborated against
an expected type mentioning the category of sheaves of modules. -/
private theorem exists_shiftedLadder [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hiso : ∀ X Y : A, (X ≅ Y) → P X → P Y)
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p) (G : CochainComplex A ℤ) :
    ∃ (D : ℕ ⥤ CochainComplex A ℤ)
      (F : ∀ n : ℕ, D.obj n ⟶ G.truncLE ((n + 1 : ℕ) : ℤ))
      (α : colimit D ⟶ G),
      (∀ n : ℕ, D.map (homOfLE (Nat.le_succ n)) ≫ F (n + 1)
          = F n ≫ truncationTransition G n) ∧
        (∀ n : ℕ, QuasiIso (F n)) ∧ (∀ (n : ℕ) (i : ℤ), Epi ((F n).f i)) ∧
        (∀ n : ℕ, ∃ a : ℤ, (D.obj n).IsStrictlyLE a) ∧
        (∀ (n : ℕ) (i : ℤ), P ((D.obj n).X i)) ∧
        (∀ (n : ℕ) (i : ℤ), IsSplitMono ((D.map (homOfLE (Nat.le_succ n))).f i)) ∧
        (∀ (n : ℕ) (i : ℤ), P (cokernel ((D.map (homOfLE (Nat.le_succ n))).f i))) ∧
        (∀ n : ℕ, colimit.ι D n ≫ α = F n ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ)) ∧
        QuasiIso α := by
  obtain ⟨Q, f, g, hq, hepi, hLE, hQP, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hP G
  have hmap : ∀ n : ℕ, (Functor.ofSequence (fun m : ℕ ↦ g (m + 1))).map
      (homOfLE (Nat.le_succ n)) = g (n + 1) :=
    Functor.ofSequence_map_homOfLE_succ _
  refine ⟨Functor.ofSequence (fun m : ℕ ↦ g (m + 1)), fun n ↦ f (n + 1),
    (colimit.isColimit _).desc (Cocone.mk G
      (NatTrans.ofSequence (fun n ↦ f (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ)) (fun n ↦ by
        rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        exact (hladder (n + 1)).trans (Category.comp_id _).symm))),
    ?_, fun n ↦ hq (n + 1), fun n i ↦ hepi (n + 1) i,
    fun n ↦ ⟨((n + 1 : ℕ) : ℤ), hLE (n + 1)⟩, fun n i ↦ hQP (n + 1) i, ?_, ?_,
    fun n ↦ (colimit.isColimit _).fac _ n, ?_⟩
  · intro n
    have key : (Functor.ofSequence (fun m : ℕ ↦ g (m + 1))).map (homOfLE (Nat.le_succ n)) ≫
        f (n + 1 + 1) ≫ G.ιTruncLE ((n + 1 + 1 : ℕ) : ℤ)
          = f (n + 1) ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) := by
      rw [hmap n]
      exact hladder (n + 1)
    exact (cancel_mono (G.ιTruncLE ((n + 1 + 1 : ℕ) : ℤ))).1
      ((Category.assoc _ _ _).trans (key.trans ((congrArg (fun φ ↦ f (n + 1) ≫ φ)
        (truncationTransition_ιTruncLE G n)).symm.trans (Category.assoc _ _ _).symm)))
  · intro n i
    rw [hmap n]
    obtain ⟨T, _, e, he⟩ := hsplit (n + 1) i
    refine IsSplitMono.mk' ⟨e.hom ≫ biprod.fst, ?_⟩
    change (g (n + 1)).f i ≫ e.hom ≫ biprod.fst = 𝟙 ((Q (n + 1)).X i)
    rw [← Category.assoc, he, biprod.inl_fst]
  · intro n i
    rw [hmap n]
    obtain ⟨T, hT, e, he⟩ := hsplit (n + 1) i
    exact hiso T _ (cokernel.mapIso ((g (n + 1)).f i) biprod.inl (Iso.refl _) e
      (by simpa using he) ≪≫ cokernelBiprodInlIso).symm hT
  · have hmono : Monotone (fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ)) := fun a b hab ↦ by
      push_cast
      omega
    have htop : ∀ i : ℤ, ∃ n : ℕ, i ≤ ((n + 1 : ℕ) : ℤ) := fun i ↦
      ⟨i.toNat, by
        have := Int.self_le_toNat i
        push_cast
        omega⟩
    exact quasiIso_of_isColimit_of_quasiIso_truncLE
      (b := fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ)) hmono htop
      (fun n ↦ f (n + 1)) (fun n ↦ hq (n + 1)) (colimit.isColimit _) _
      (fun n ↦ (colimit.isColimit _).fac _ n)

end Colimit

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

/-- **A direct sum of extensions by zero `j_{U!}O_U` of the structure sheaves of slices** of
the ringed site `(C, J, R)`. -/
def IsSumOfExtensionByZeroStructureSheaves
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) : Prop :=
  ∃ (ι : Type u) (U : ι → C),
    Nonempty ((∐ fun i : ι ↦
      (SheafOfModules.extensionByZero
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) (U i)).obj
        (SheafOfModules.unit
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).over (U i))) :
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ≅ M)

/-- Sheaves of modules on a ringed site form an abelian category. -/
noncomputable instance instAbelian :
    Abelian (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
  AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules _

/-- Sequential colimits of sheaves of modules on a ringed site are exact. -/
noncomputable instance instHasExactColimitsOfShapeNat :
    HasExactColimitsOfShape ℕ
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
  have : AB5OfSize.{0, 0}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :=
    AB5OfSize_of_univLE.{0, 0, u, u} _
  AB5OfSize.ofShape ℕ

/-- The zero module is the empty sum. -/
private theorem containsZero_isSum : ObjectProperty.ContainsZero
    (IsSumOfExtensionByZeroStructureSheaves R :
      ObjectProperty
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))) := by
  let U₀ : PEmpty.{u + 1} → C := fun i ↦ nomatch i
  let E : PEmpty.{u + 1} →
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) := fun i ↦
    (SheafOfModules.extensionByZero
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) (U₀ i)).obj
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).over (U₀ i)))
  exact ⟨∐ E, (Stacks.Cohomology.isInitial_coproduct_of_isEmpty E).isZero,
    PEmpty.{u + 1}, U₀, ⟨Iso.refl _⟩⟩

/-- A biproduct of two such sums is again one: concatenate the index types. -/
private theorem isSum_biprod
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
    (hM : IsSumOfExtensionByZeroStructureSheaves R M)
    (hN : IsSumOfExtensionByZeroStructureSheaves R N) :
    IsSumOfExtensionByZeroStructureSheaves R (M ⊞ N) := by
  obtain ⟨ι, U, ⟨eM⟩⟩ := hM
  obtain ⟨κ, V, ⟨eN⟩⟩ := hN
  exact ⟨ι ⊕ κ, Sum.elim U V, ⟨Stacks.Cohomology.coproductSumIso _ ≪≫ biprod.mapIso eM eN⟩⟩

/-- Being such a sum is invariant under isomorphism: compose the witnessing isomorphism. -/
private theorem isSum_of_iso
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) (e : M ≅ N)
    (hM : IsSumOfExtensionByZeroStructureSheaves R M) :
    IsSumOfExtensionByZeroStructureSheaves R N := by
  obtain ⟨ι, U, ⟨eM⟩⟩ := hM
  exact ⟨ι, U, ⟨eM ≪≫ e⟩⟩

/-- **Every sheaf of modules on the ringed site is a quotient of such a sum**, by the
sheaf-level half of 03EW. -/
private theorem exists_epi_isSum
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) :
    ∃ (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
      (_ : IsSumOfExtensionByZeroStructureSheaves R N) (p : N ⟶ M), Epi p := by
  obtain ⟨ι, U, p, hp⟩ :=
    SheafOfModules.exists_epi_from_coproduct_extensionByZero
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) M
  exact ⟨_, ⟨ι, U, ⟨Iso.refl _⟩⟩, p, hp⟩

/-- **A compatible ladder resolving the upper truncations of a complex by direct sums of
extensions by zero**, together with the comparison from its colimit. The index `n`
corresponds to the truncation bound `n + 1`. -/
structure ResolutionByDirectSumsExtensionsByZero
    (G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) where
  /-- The sequence of resolving complexes. -/
  system : ℕ ⥤ CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ
  /-- The resolution of the `(n+1)`-st upper truncation. -/
  toTruncation (n : ℕ) : system.obj n ⟶ G.truncLE ((n + 1 : ℕ) : ℤ)
  /-- The transition between successive truncations of `G`. -/
  truncationTransition (n : ℕ) :
    G.truncLE ((n + 1 : ℕ) : ℤ) ⟶ G.truncLE ((n + 1 + 1 : ℕ) : ℤ)
  /-- The transition is the one compatible with the inclusions into `G`. -/
  truncationTransition_ι (n : ℕ) :
    truncationTransition n ≫ G.ιTruncLE ((n + 1 + 1 : ℕ) : ℤ)
      = G.ιTruncLE ((n + 1 : ℕ) : ℤ)
  /-- The ladder commutes. -/
  square (n : ℕ) :
    system.map (homOfLE (Nat.le_succ n)) ≫ toTruncation (n + 1) =
      toTruncation n ≫ truncationTransition n
  /-- Each vertical arrow is a quasi-isomorphism. -/
  quasiIso (n : ℕ) : QuasiIso (toTruncation n)
  /-- Each vertical arrow is termwise surjective. -/
  epi_f (n : ℕ) (i : ℤ) : Epi ((toTruncation n).f i)
  /-- Each resolving complex is bounded above. -/
  boundedAbove (n : ℕ) : ∃ a : ℤ, (system.obj n).IsStrictlyLE a
  /-- Each term of each resolving complex is a sum of extensions by zero. -/
  term_isSum (n : ℕ) (i : ℤ) :
    IsSumOfExtensionByZeroStructureSheaves R ((system.obj n).X i)
  /-- The transitions of the ladder are termwise split injections. -/
  transition_splitMono (n : ℕ) (i : ℤ) :
    IsSplitMono ((system.map (homOfLE (Nat.le_succ n))).f i)
  /-- Their termwise cokernels are again sums of extensions by zero. -/
  transition_cokernel_isSum (n : ℕ) (i : ℤ) :
    IsSumOfExtensionByZeroStructureSheaves R
      (cokernel ((system.map (homOfLE (Nat.le_succ n))).f i))
  /-- The comparison from the colimit of the ladder. -/
  colimitComparison : colimit system ⟶ G
  /-- It is the map induced by the ladder. -/
  colimitComparison_fac (n : ℕ) :
    colimit.ι system n ≫ colimitComparison =
      toTruncation n ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ)
  /-- It is a quasi-isomorphism. -/
  colimit_quasiIso : QuasiIso colimitComparison

/-- **A complex of modules on a ringed site admits a compatible resolution by direct sums of
extensions by zero of the structure sheaves of slices, whose colimit is quasi-isomorphic to
the complex.** -/
theorem exists_resolutionByDirectSumsExtensionsByZero
    (G : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ) :
    Nonempty (ResolutionByDirectSumsExtensionsByZero R G) := by
  have := containsZero_isSum R
  obtain ⟨D, F, α, hsquare, hqis, hepi, hLE, hterm, hsplit, hcoker, hfac, hα⟩ :=
    exists_shiftedLadder (IsSumOfExtensionByZeroStructureSheaves R)
      (isSum_biprod R) (isSum_of_iso R) (exists_epi_isSum R) G
  exact ⟨{ system := D
           toTruncation := F
           truncationTransition := truncationTransition G
           truncationTransition_ι := truncationTransition_ιTruncLE G
           square := hsquare
           quasiIso := hqis
           epi_f := hepi
           boundedAbove := hLE
           term_isSum := hterm
           transition_splitMono := hsplit
           transition_cokernel_isSum := hcoker
           colimitComparison := α
           colimitComparison_fac := hfac
           colimit_quasiIso := hα }⟩

end Stacks.DerivedTensor.ResolutionByExtensionsByZero

end
