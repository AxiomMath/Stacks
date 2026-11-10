module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAscendingChain
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.Homology.Injectives.Size.SubobjectDirectedInf

/-!
# A coherent submodule of a directed union lies in one member

Let `X` be a Noetherian algebraic space over a scheme `S`, let `N` be a quasi-coherent
`𝒪_X`-module and let `(N_j)` be a directed family of quasi-coherent submodules of `N`.  A coherent
submodule `K` of `N` contained in the union of the `N_j` is contained in one of them.

## Main results

* `AlgebraicGeometry.Space.exists_le_of_le_iSup_of_isCoherent`: a coherent submodule contained in
  a directed supremum of quasi-coherent submodules is contained in one member.

## Implementation notes

The proof is by the ascending chain condition of Stacks 07UJ.  Intersecting with `K` commutes with
the directed supremum, by AB5 (`Stacks.Injectives.iSup_inf_of_monotone`), so `K` is the directed
union of the `N_j ∩ K`.  If no `N_j` contains `K`, then none of the `N_j ∩ K` is all of `K`, and
directedness produces from each of them a strictly larger one; iterating gives a strictly
increasing sequence of quasi-coherent submodules of the coherent module `K`, which Stacks 07UJ
forbids.

## References

* [Stacks Project, Tag 07UJ](https://stacks.math.columbia.edu/tag/07UJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The `𝒪_X`-modules on an algebraic space form a Grothendieck abelian category, the small étale
site being essentially small.  It is a local instance in this file, so that the supremum of a
family of submodules has its universe pinned to that of the schemes. -/
theorem isGrothendieckAbelian_modules :
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

attribute [local instance] isGrothendieckAbelian_modules

/-- The intersection of a subobject `K` with a subobject `T` of a quasi-coherent module, read as a
subobject of `K`, is quasi-coherent as soon as `K` and `T` are: it is a fibre product of
quasi-coherent modules. -/
theorem isQuasicoherentOnSite_pullback_obj {N : Modules.{u, u} B S hS F hF}
    (hN : N.IsQuasicoherentOnSite) (K T : Subobject N)
    (hK : (K : Modules.{u, u} B S hS F hF).IsQuasicoherentOnSite)
    (hT : (T : Modules.{u, u} B S hS F hF).IsQuasicoherentOnSite) :
    (((Subobject.pullback K.arrow).obj T : Subobject (K : Modules.{u, u} B S hS F hF)) :
      Modules.{u, u} B S hS F hF).IsQuasicoherentOnSite := by
  rw [Subobject.pullback_obj]
  exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    (Subobject.underlyingIso (pullback.snd T.arrow K.arrow)).symm
    (isQuasicoherentOnSite_of_isPullback B S hS F hF (IsPullback.of_hasPullback T.arrow K.arrow)
      hT hK hN)

/-- **A coherent submodule of a directed union of quasi-coherent submodules lies in one member.**
Let `X` be a Noetherian algebraic space, `N` a quasi-coherent `𝒪_X`-module, `(N_j)` a family of
quasi-coherent submodules of `N` indexed by a filtered category and monotone along its
morphisms, and `K` a coherent submodule of `N` contained in the supremum of the `N_j`.  Then
`K ≤ N_j` for some `j`. -/
theorem exists_le_of_le_iSup_of_isCoherent (hZ : B.Contains (⊤_ Scheme.{u}))
    (hX : IsNoetherian B S hS hZ F) {N : Modules.{u, u} B S hS F hF}
    (hN : N.IsQuasicoherentOnSite) (K : Subobject N)
    (hK : IsCoherent B S hS F hF (K : Modules.{u, u} B S hS F hF))
    {J : Type u} [SmallCategory J] [IsFiltered J] (s : J → Subobject N)
    (hs : ∀ {i j : J}, (i ⟶ j) → s i ≤ s j)
    (hqc : ∀ j, (s j : Modules.{u, u} B S hS F hF).IsQuasicoherentOnSite)
    (hle : K ≤ ⨆ j, s j) : ∃ j, K ≤ s j := by
  classical
  by_contra hcon
  push Not at hcon
  -- `K` is the directed union of the `N_j ∩ K`
  have hdist : (⨆ j, (s j ⊓ K)) = K := by
    rw [← Stacks.Injectives.iSup_inf_of_monotone s hs K]
    exact inf_eq_right.2 hle
  -- every `N_j ∩ K` is strictly contained in a larger one
  have hstep : ∀ j, ∃ (j' : J) (_ : j ⟶ j'), s j ⊓ K < s j' ⊓ K := by
    intro j
    have hne : ¬ ∀ i, s i ⊓ K ≤ s j ⊓ K := fun hall =>
      hcon j ((hdist.symm.le.trans (iSup_le hall)).trans inf_le_left)
    obtain ⟨i, hi⟩ := not_forall.1 hne
    exact ⟨IsFiltered.max i j, IsFiltered.rightToMax i j, lt_of_le_not_ge
      (inf_le_inf_right K (hs (IsFiltered.rightToMax i j))) fun hge =>
        hi ((inf_le_inf_right K (hs (IsFiltered.leftToMax i j))).trans hge)⟩
  choose next hnext hlt using hstep
  let seq : ℕ → J := fun n => Nat.rec (IsFiltered.nonempty (C := J)).some (fun _ j => next j) n
  have hseq : ∀ n, seq (n + 1) = next (seq n) := fun _ => rfl
  let G : ℕ → Subobject (K : Modules.{u, u} B S hS F hF) :=
    fun n => (Subobject.pullback K.arrow).obj (s (seq n))
  have hGmono : Monotone G := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine leOfHom ((Subobject.pullback K.arrow).map (homOfLE ?_))
    rw [hseq]
    exact hs (hnext (seq n))
  have hGqc : ∀ n, SheafOfModules.IsQuasicoherentOnSite
      (G n : Modules.{u, u} B S hS F hF) := fun n =>
    isQuasicoherentOnSite_pullback_obj B S hS F hF hN K (s (seq n))
      hK.toIsQuasicoherentOnSite (hqc (seq n))
  obtain ⟨n, hn⟩ := exists_eventually_constant_quasicoherentSubobjects B S hS F hF hZ hX
    (K : Modules.{u, u} B S hS F hF) hK G hGqc hGmono
  have heq : K ⊓ s (seq (n + 1)) = K ⊓ s (seq n) := by
    rw [Subobject.inf_eq_map_pullback, Subobject.inf_eq_map_pullback]
    exact congrArg (Subobject.map K.arrow).obj (hn (n + 1) (Nat.le_succ n))
  have h := hlt (seq n)
  rw [← hseq, inf_comm, inf_comm (s (seq (n + 1))), heq] at h
  exact lt_irrefl _ h

end AlgebraicGeometry.Space

end
