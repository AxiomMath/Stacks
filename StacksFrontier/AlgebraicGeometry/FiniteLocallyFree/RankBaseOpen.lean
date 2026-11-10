module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Divisors.RankLocalGenerators
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankPullbackFree

/-!
# The open of the base over which a finite locally free module has a given rank

Let `E` be a finite locally free module on a scheme `X`.

* If a morphism `q : T ⟶ X` maps into the locus `X_ρ` where `E` has rank `ρ`, then `q^*E` is
  finite locally free of rank `ρ`.
* If `f : X ⟶ S` is universally closed, then the points `s` of `S` all of whose preimages lie in
  `X_ρ` form an open `rankBaseOpen f E ρ` of `S`: it is the complement of the image under the
  closed map `f` of the closed complement of `X_ρ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.overIsoOfRestrictIso`: an isomorphism of the restriction of
  a sheaf of modules to an open `W` with a free module, read on the slice site over `W`.
* `AlgebraicGeometry.Scheme.Modules.rankBaseOpen`: the open of `S` over which `E` has rank `ρ`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_restrictIso`: a sheaf of
  modules which near every point is free on a type with `r` elements is finite locally free of
  rank `r`.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_range_subset`: the
  pullback of `E` along a morphism landing in `X_ρ` is finite locally free of rank `ρ`.
* `AlgebraicGeometry.Scheme.Modules.mem_rankBaseOpen_iff`: `s` lies in `rankBaseOpen f E ρ` iff
  every point over `s` lies in `X_ρ`.
* `AlgebraicGeometry.Scheme.Modules.eq_of_mem_rankBaseOpen`: the opens for distinct ranks do not
  meet in the image of `f`.
* `AlgebraicGeometry.Scheme.Modules.range_fst_subset_rankStratum` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_fst`: over a morphism
  `g : T ⟶ S` landing in `rankBaseOpen f E ρ`, the pullback of `E` to `X ×_S T` is finite locally
  free of rank `ρ`.
* `AlgebraicGeometry.Scheme.Modules.mem_rankBaseOpen_of_pullback_iso_free`: if the pullback of
  `E` to `X ×_S W` is free of rank `m` for an open `W` of `T` containing `t`, then `g t` lies in
  `rankBaseOpen f E m`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphism between the restriction of a sheaf of modules to an open `W` and a free sheaf
of modules, read on the slice site over `W`. -/
def overIsoOfRestrictIso {T : Scheme.{u}} (M : T.Modules) (W : T.Opens) (I : Type u)
    (e : (restrictFunctor W.ι).obj M ≅ SheafOfModules.free.{u} I) :
    SheafOfModules.free.{u} I ≅ M.over W :=
  haveI hdisc : PreservesColimitsOfShape (Discrete I) (overEquiv W).functor :=
    preservesColimitsOfShape_of_discrete _
  let hunit : SheafOfModules.unit (W.toScheme).ringCatSheaf ≅
      (overEquiv W).functor.obj (SheafOfModules.unit (T.ringCatSheaf.over W)) := Iso.refl _
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    (overEquiv W).functor I hdisc hunit
  ((overEquiv W).functor.preimageIso ((overFunctorEquiv W).app M ≪≫ e ≪≫ eFree)).symm

/-- A sheaf of modules on a scheme which near every point is free on a type with `r` elements
is finite locally free of rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_forall_restrictIso {T : Scheme.{u}} (M : T.Modules) (r : ℕ)
    (h : ∀ t : T, ∃ (W : T.Opens) (_ : t ∈ W) (I : Type u), Nonempty (I ≃ Fin r) ∧
      Nonempty ((restrictFunctor W.ι).obj M ≅ SheafOfModules.free.{u} I)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r := by
  choose W hW I hI e using h
  refine Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso r W ?_ fun t ↦
    (SheafOfModules.freeFunctor.mapIso ((hI t).some.trans Equiv.ulift.symm).toIso).symm ≪≫
      overIsoOfRestrictIso M (W t) (I t) (e t).some
  exact (Opens.coversTop_iff T W).2 (top_unique fun t _ ↦ Opens.mem_iSup.2 ⟨t, hW t⟩)

/-- If `q : T ⟶ X` maps into the locus `X_ρ` where `E` has rank `ρ`, then `q^*E` is finite
locally free of rank `ρ`. -/
theorem isFiniteLocallyFreeOfRank_pullback_of_range_subset {X T : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (q : T ⟶ X) (ρ : ℕ)
    (h : Set.range q ⊆ rankStratum E ρ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback q).obj E) ρ := by
  refine isFiniteLocallyFreeOfRank_of_forall_restrictIso _ ρ fun t ↦ ?_
  obtain ⟨V, hV, -, I, hI, ⟨eV⟩⟩ := exists_free_nbhd_of_mem_rankStratum E ρ (q t) (h ⟨t, rfl⟩)
  exact ⟨q ⁻¹ᵁ V, hV, I, hI,
    ⟨restrictPullbackIsoFree E q V I (restrictIsoFreeOfOverIso E V I eV)⟩⟩

section BaseOpen

variable {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The open of `S` consisting of the points all of whose preimages under the universally closed
morphism `f` lie in the locus where `E` has rank `ρ`. -/
def rankBaseOpen (ρ : ℕ) : S.Opens :=
  ⟨(f '' (rankStratum E ρ : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ (rankStratum E ρ).isOpen.isClosed_compl).isOpen_compl⟩

/-- A point lies in `rankBaseOpen f E ρ` iff every point over it lies in the rank-`ρ` locus. -/
theorem mem_rankBaseOpen_iff {ρ : ℕ} {s : S} :
    s ∈ rankBaseOpen f E ρ ↔ ∀ x : X, f x = s → x ∈ rankStratum E ρ := by
  change s ∉ f '' (rankStratum E ρ : Set X)ᶜ ↔ _
  simp only [Set.mem_image, Set.mem_compl_iff, SetLike.mem_coe, not_exists, not_and]
  exact ⟨fun h x hx ↦ by_contra fun hx' ↦ h x hx' hx, fun h x hx' hx ↦ hx' (h x hx)⟩

/-- The opens `rankBaseOpen f E ρ` for distinct ranks do not meet in the image of `f`. -/
theorem eq_of_mem_rankBaseOpen {ρ ρ' : ℕ} {s : S} (hs : s ∈ rankBaseOpen f E ρ)
    (hs' : s ∈ rankBaseOpen f E ρ') (hrange : s ∈ Set.range f) : ρ = ρ' := by
  obtain ⟨x, rfl⟩ := hrange
  have h := (mem_rankBaseOpen_iff f E).1 hs x rfl
  have h' := (mem_rankBaseOpen_iff f E).1 hs' x rfl
  rw [mem_rankStratum] at h h'
  exact h.symm.trans h'

/-- Over a morphism `g : T ⟶ S` landing in `rankBaseOpen f E ρ`, the first projection of
`X ×_S T` lands in the rank-`ρ` locus of `E`. -/
theorem range_fst_subset_rankStratum {T : Scheme.{u}} (g : T ⟶ S) {ρ : ℕ}
    (hg : Set.range g ⊆ rankBaseOpen f E ρ) :
    Set.range (pullback.fst f g) ⊆ rankStratum E ρ := by
  rintro _ ⟨z, rfl⟩
  refine (mem_rankBaseOpen_iff f E).1 (hg ⟨pullback.snd f g z, rfl⟩) _ ?_
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

/-- Over a morphism `g : T ⟶ S` landing in `rankBaseOpen f E ρ`, the pullback of `E` to
`X ×_S T` is finite locally free of rank `ρ`. -/
theorem isFiniteLocallyFreeOfRank_pullback_fst {T : Scheme.{u}} (g : T ⟶ S) {ρ : ℕ}
    (hg : Set.range g ⊆ rankBaseOpen f E ρ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (pullback.fst f g)).obj E) ρ :=
  isFiniteLocallyFreeOfRank_pullback_of_range_subset E _ ρ (range_fst_subset_rankStratum f E g hg)

/-- If the pullback of `E` to `X ×_S W` is free of rank `m` for an open `W` of `T` containing
`t`, then `g t` lies in `rankBaseOpen f E m`. -/
theorem mem_rankBaseOpen_of_pullback_iso_free {T : Scheme.{u}} (g : T ⟶ S) (t : T) (W : T.Opens)
    (ht : t ∈ W) {m : ℕ}
    (e : (Scheme.Modules.pullback (pullback.fst f (W.ι ≫ g))).obj E ≅
      SheafOfModules.free (ULift.{u} (Fin m))) :
    g t ∈ rankBaseOpen f E m := by
  refine (mem_rankBaseOpen_iff f E).2 fun x hx ↦ ?_
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := W.ι ≫ g) x
    (⟨t, ht⟩ : W) hx
  exact hz ▸ mem_rankStratum_of_pullback_iso_free E _ e z

end BaseOpen

end AlgebraicGeometry.Scheme.Modules
