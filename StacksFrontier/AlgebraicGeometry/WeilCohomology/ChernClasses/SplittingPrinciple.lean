module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneIff.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Situation
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback

/-!
# The splitting principle for a family of finite locally free modules

In the standing situation of Stacks Section 45.12, finitely many finite locally free modules
`ℰ_i` of ranks `r_i` on one object `X` of `𝒞` can be split *simultaneously*: there is a single
morphism `p : P ⟶ X` of `𝒞` such that `p^* : A(X) ⟶ A(P)` is injective and every `p^*ℰ_i`
carries a filtration of length `r_i` whose successive quotients are invertible.

The induction is on `∑ rᵢ`. When every rank is at most one there is nothing to do and `p` is the
identity, each `ℰ_i` being zero or invertible. Otherwise one rank exceeds one; the projective
bundle of that module splits an invertible quotient off it and lowers its rank by one, and the
inductive hypothesis is applied to the tautological kernel together with the pullbacks of the
other modules.

## Main definitions

* `Stacks.WeilCohomology.HasInvertibleFiltration`: a module admits a filtration of a given length
  whose successive quotients are invertible.

## Main results

* `Stacks.WeilCohomology.HasInvertibleFiltration.of_iso`: the property depends only on the
  isomorphism class of the module.
* `Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero`: a finite locally free module
  of rank zero is a zero object, which is the length-zero case of a filtration.
* `Stacks.WeilCohomology.ChernSetup.exists_injective_hasInvertibleFiltration`: **the splitting
  principle, Tag 0FI7.**

## Implementation notes

A filtration `0 = 𝓕₀ ⊆ 𝓕₁ ⊆ … ⊆ 𝓕_r = ℰ` with invertible successive quotients is recorded
inductively, by the short exact sequence `0 ⟶ 𝓕_{r-1} ⟶ ℰ ⟶ 𝓛_r ⟶ 0` of its top step together
with a filtration of `𝓕_{r-1}` of length `r - 1`. At length zero the empty list of quotients
forces `ℰ` itself to vanish, so that is what the base constructor asks for. Each step also
records that the module it filters is finite locally free; that is not a consequence of the other
fields — an extension of a finite locally free module by an invertible one is finite locally free
only because the sequence is locally split, which is not available here — and it is what lets the
filtration be read in the `K`-group of Tag 0FDK.

Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible`, the class carrying Tag 01CS in
which the tautological module of a projective bundle is stated. The repository's other class with
that label, `Stacks.SheafOfModules.IsInvertible`, is the one in which stability of invertibility
under pullback is available, so the two are exchanged through
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible` where that
stability is used.

Flatness of the projection of a projective bundle is used, and is not decoration: extending a
filtration of the tautological kernel to one of `p^*ℰ` requires the tautological sequence to stay
exact after the further pullback supplied by the inductive hypothesis, which is exactness of flat
pullback, Tag 02N4.

Injectivity of `p^*` is not assumed: it is `Stacks.WeilCohomology.ChernSetup.injective_pull_proj`,
deduced from the projective bundle formula, which is condition (4) of the situation.

The ranks are constant, as in the source, which writes `ℰ_i` for a locally free module "of rank
`r_i`". The source reduces an arbitrary finite locally free module to this case by condition (2);
that
condition is not part of `Stacks.WeilCohomology.ChernSetup`, so the reduction is not available and
the
constant rank is a hypothesis here.

## References

* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ZeroObject

universe u v v₁ w

namespace Stacks.WeilCohomology

/-! ### Filtrations with invertible successive quotients -/

/-- **A filtration with invertible successive quotients.** `HasInvertibleFiltration X E r` says
that `E` admits a filtration `0 = 𝓕₀ ⊆ … ⊆ 𝓕_r = E` of length `r` whose `r` successive quotients
are invertible `𝒪_X`-modules, every stage being finite locally free. At length zero the list of
quotients is empty, which forces `E` to be a zero object. -/
inductive HasInvertibleFiltration (X : Scheme.{u}) : X.Modules → ℕ → Prop
  | nil (E : X.Modules) (hE : IsZero E) : HasInvertibleFiltration X E 0
  | step {E F L : X.Modules} {r : ℕ} (f : F ⟶ E) (g : E ⟶ L) (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
      (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
      (hF : HasInvertibleFiltration X F r) : HasInvertibleFiltration X E (r + 1)

/-- Having a filtration with invertible successive quotients depends only on the isomorphism
class of the module: an isomorphism transports the top step of the filtration and leaves the
rest of it alone. -/
theorem HasInvertibleFiltration.of_iso {X : Scheme.{u}} {E F : X.Modules} {r : ℕ} (e : E ≅ F)
    (h : HasInvertibleFiltration X E r) : HasInvertibleFiltration X F r := by
  cases h with
  | nil E hE => exact .nil F (hE.of_iso e.symm)
  | step f g w hS hL hE hF =>
    exact .step (f ≫ e.hom) (e.inv ≫ g) (by simp [w])
      (ShortComplex.shortExact_of_iso
        (ShortComplex.isoMk (S₁ := ShortComplex.mk f g w) (Iso.refl _) e (Iso.refl _)
          (by simp) (by simp)) hS)
      hL (SheafOfModules.IsFiniteLocallyFree.of_iso (h := hE) e) hF

/-! ### Finite local freeness of rank zero and of rank one -/

/-- A section of a sheaf of modules which vanishes on a neighbourhood of every point of its
domain vanishes: the open sets on which it vanishes cover the domain, and a sheaf is separated
for that covering. -/
private theorem section_eq_zero_of_locally_zero {X : Scheme.{u}} (M : X.Modules) {U : Opens X}
    (s : Γ(M, U))
    (hs : ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U),
      x ∈ V ∧ M.val.restrictₛₗ (homOfLE hVU).op s = 0) : s = 0 := by
  have hsheaf : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (M.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)
  choose V hVU hxV hzero using fun x : U => hs x.1 x.2
  apply (hsheaf.isSheafFor (.ofArrows V fun x => homOfLE (hVU x)) ?_).isSeparatedFor.ext
  · rintro _ _ ⟨x⟩
    change M.val.restrictₛₗ (homOfLE (hVU x)).op s =
      M.val.restrictₛₗ (homOfLE (hVU x)).op 0
    rw [hzero, map_zero]
  · intro x hx
    exact ⟨V ⟨x, hx⟩, homOfLE (hVU _), Sieve.ofArrows_mk _ _ _, hxV _⟩

/-- **A finite locally free module of rank zero is a zero object.** On each member of a
trivialising cover the module is free on an empty basis, hence zero there, so every section
vanishes locally and therefore vanishes. -/
theorem isZero_of_isFiniteLocallyFreeOfRank_zero {X : Scheme.{u}} (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 0) : IsZero M := by
  classical
  obtain ⟨q, hq, hrank⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  have hlocal (i : q.I) : IsZero (M.over (q.X i)) := by
    have hfree : IsZero (SheafOfModules.free
        (R := X.ringCatSheaf.over (q.X i)) (q.generators i).I) := by
      have : IsEmpty (q.generators i).I := ⟨fun j => Fin.elim0 ((hrank i).some j)⟩
      have : ∀ N : SheafOfModules (X.ringCatSheaf.over (q.X i)),
          Unique (SheafOfModules.free (R := X.ringCatSheaf.over (q.X i))
            (q.generators i).I ⟶ N) := fun N => Equiv.unique N.freeHomEquiv
      exact IsInitial.isZero (IsInitial.ofUnique _)
    have : IsIso (q.generators i).π := hq.isIso i
    exact IsZero.of_iso hfree (asIso (q.generators i).π).symm
  apply (IsZero.iff_id_eq_zero M).2
  ext U s
  apply section_eq_zero_of_locally_zero M s
  intro x hx
  have hcover : (⨆ i, q.X i) = ⊤ := (Opens.coversTop_iff _ _).1 q.coversTop
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcover ▸ trivial : x ∈ ⨆ i, q.X i)
  have hVq : U ⊓ q.X i ≤ q.X i := inf_le_right
  have hzeroAt : IsZero ((PresheafOfModules.evaluation (X.ringCatSheaf.over (q.X i)).obj
      (Opposite.op (Over.mk (homOfLE hVq)))).obj ((SheafOfModules.forget
        (X.ringCatSheaf.over (q.X i))).obj (M.over (q.X i)))) :=
    Functor.map_isZero _ (Functor.map_isZero _ (hlocal i))
  have hsub : Subsingleton (Γ(M, U ⊓ q.X i)) := by
    change Subsingleton (↑(((M.over (q.X i)).val.obj
      (Opposite.op (Over.mk (homOfLE hVq))))))
    exact ModuleCat.subsingleton_of_isZero hzeroAt
  exact ⟨U ⊓ q.X i, inf_le_left, ⟨hx, hxi⟩, hsub.elim _ 0⟩

/-- A finite locally free module of rank one is invertible, so it has a filtration of length one
whose single successive quotient is the module itself. -/
private theorem hasInvertibleFiltration_one {X : Scheme.{u}} (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M 1) :
    HasInvertibleFiltration X M 1 := by
  have hS : (ShortComplex.mk (0 : (0 : X.Modules) ⟶ M) (𝟙 M) (by simp)).ShortExact :=
    ShortComplex.ShortExact.mk'
      ((ShortComplex.exact_iff_mono _ rfl).2 inferInstance)
      ⟨fun _ _ _ => (isZero_zero _).eq_of_tgt _ _⟩ inferInstance
  exact HasInvertibleFiltration.step (0 : (0 : X.Modules) ⟶ M) (𝟙 M) (by simp) hS
    (@Stacks.InvertibleRankOneIff.isInvertible_of_isFiniteLocallyFreeOfRank_one
      X.toRingedSpace M hM) hM.isFiniteLocallyFree
    (HasInvertibleFiltration.nil (0 : X.Modules) (isZero_zero _))

/-- A finite locally free module of rank at most one has a filtration of that length with
invertible successive quotients: it is zero if the rank is zero and invertible if it is one. -/
theorem hasInvertibleFiltration_of_rank_le_one {X : Scheme.{u}} (M : X.Modules) (r : ℕ)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r) (hr : r ≤ 1) :
    HasInvertibleFiltration X M r := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
  · exact HasInvertibleFiltration.nil M (isZero_of_isFiniteLocallyFreeOfRank_zero M hM)
  · exact hasInvertibleFiltration_one M hM

/-! ### Flat pullback -/

/-- **A short exact sequence of sheaves of modules stays short exact after flat pullback.** -/
theorem shortExact_map_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (s : ShortComplex Y.Modules) (hs : s.ShortExact) :
    (s.map (Scheme.Modules.pullback f)).ShortExact :=
  @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ hs (Scheme.Modules.pullback f)
    inferInstance (AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat f) inferInstance

/-- The pullback of an invertible module is invertible, at the Tag 01CS spelling in which the
filtrations above are stated. -/
theorem isInvertible_pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ f L
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mpr hL))

/-- The pullback of a finite locally free module of rank `r` is finite locally free of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    {E : Y.Modules} {r : ℕ}
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) r :=
  @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ f E r hE

/-- Lowering one entry of a family of natural numbers by one, where that entry is positive,
lowers the sum of the family. -/
private theorem sum_update_sub_one_lt {I : Type*} [Fintype I] [DecidableEq I] (r : I → ℕ) (i : I)
    (hi : 0 < r i) : ∑ j, Function.update r i (r i - 1) j < ∑ j, r j := by
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · by_cases hj : j = i
    · rw [hj, Function.update_self]
      omega
    · exact (Function.update_of_ne hj (r i - 1) r).le
  · simp only [Function.update_self]
    omega

/-- **One step of the splitting.** For a projective bundle datum of a module `ℰ` of rank `r + 1`
and a flat morphism `q` into the bundle, a filtration of `q^*𝓕` of length `r` with invertible
successive quotients, `𝓕` the tautological kernel, extends to one of `q^*p^*ℰ` of length
`r + 1`. -/
private theorem BundleDatum.hasInvertibleFiltration_pullback {C : Type w} [Category.{v₁} C]
    {S : C ⥤ Scheme.{u}} {X : C} {E : (S.obj X).Modules} {r : ℕ} (D : BundleDatum S X E r)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1))
    {Q : C} (q : Q ⟶ D.bundle) [Flat (S.map q)]
    (hF : HasInvertibleFiltration (S.obj Q) ((Scheme.Modules.pullback (S.map q)).obj D.sub) r) :
    HasInvertibleFiltration (S.obj Q)
      ((Scheme.Modules.pullback (S.map q)).obj ((Scheme.Modules.pullback (S.map D.proj)).obj E))
      (r + 1) :=
  HasInvertibleFiltration.step _ _ _ (shortExact_map_pullback (S.map q) _ D.shortExact)
    (isInvertible_pullback_obj (S.map q) D.twist D.twist_isInvertible)
    (isFiniteLocallyFreeOfRank_pullback_obj _
      (isFiniteLocallyFreeOfRank_pullback_obj _ hE)).isFiniteLocallyFree hF

/-! ### The splitting principle -/

namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The splitting principle, Stacks Tag 0FI7.** In the standing situation of Section 45.12, let
`X` be an object of `𝒞` and let `ℰ_i` be a finite collection of locally free `𝒪_X`-modules of
ranks `r_i`. There is a morphism `p : P ⟶ X` of `𝒞` such that `p^* : A(X) ⟶ A(P)` is injective
and each `p^*ℰ_i` has a filtration of length `r_i` whose successive quotients are invertible
`𝒪_P`-modules. The projection is moreover flat.

The induction is on `∑ rᵢ`. If every rank is at most one the identity of `X` already works, each
`ℰ_i` being zero or invertible. Otherwise some `rᵢ` exceeds one; the projective bundle of `ℰ_i`
gives `p : P ⟶ X` with its tautological sequence `0 ⟶ 𝓕 ⟶ p^*ℰ_i ⟶ 𝒪_P(1) ⟶ 0`, and `p^*` is
injective by the projective bundle formula. The inductive hypothesis applied to `𝓕` together
with the `p^*ℰ_{i'}` for `i' ≠ i` produces `q : Q ⟶ P`, and `q ≫ p` is the required morphism:
flatness of `S q` keeps the tautological sequence exact after pullback, so the filtration of
`q^*𝓕` extends by one step to one of `q^*p^*ℰ_i`. -/
@[stacks 0FI7 "the ranks are constant, as in the source; see the module documentation for the
clauses of the standing situation that `ChernSetup` transcribes"]
theorem exists_injective_hasInvertibleFiltration (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (I : Type*) [Finite I] (E : I → (S.obj X).Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ (P : C) (p : P ⟶ X), Flat (S.map p) ∧ Function.Injective (𝔄.pull p) ∧
      ∀ i, HasInvertibleFiltration (S.obj P)
        ((Scheme.Modules.pullback (S.map p)).obj (E i)) (r i) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  generalize hn : ∑ i, r i = n
  induction n using Nat.strong_induction_on generalizing X E r with
  | h n ih =>
    by_cases hr : ∀ i, r i ≤ 1
    · refine ⟨X, 𝟙 X, ?_, ?_, fun i => ?_⟩
      · simpa using (inferInstance : Flat (𝟙 (S.obj X)))
      · exact fun x y h => by simpa [𝔄.pull_id X] using h
      · exact hasInvertibleFiltration_of_rank_le_one _ (r i)
          (isFiniteLocallyFreeOfRank_pullback_obj _ (hE i)) (hr i)
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have hi : 1 < r i := by omega
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (r i - 1 + 1) := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ r i)] using hE i
    set D := 𝔄.bundleDatum X (E i) (r i - 1) hEi
    have hpf : Flat (S.map D.proj) := D.flat
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j => (Scheme.Modules.pullback (S.map D.proj)).obj (E j)) i D.sub j)
        (Function.update r i (r i - 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          isFiniteLocallyFreeOfRank_pullback_obj _ (hE j)
    have hlt : ∑ j, Function.update r i (r i - 1) j < n :=
      hn ▸ sum_update_sub_one_lt r i (by omega)
    obtain ⟨Q, q, hqf, hqinj, hQ⟩ := ih _ hlt D.bundle _ _ hE' rfl
    refine ⟨Q, q ≫ D.proj, ?_, ?_, fun j => ?_⟩
    · rw [S.map_comp]
      infer_instance
    · simpa only [𝔄.pull_comp q D.proj, RingHom.coe_comp] using
        hqinj.comp (𝔄.injective_pull_proj X (E i) _ hEi)
    · have comp₁ : (Scheme.Modules.pullback (S.map q)).obj
            ((Scheme.Modules.pullback (S.map D.proj)).obj (E j)) ≅
          (Scheme.Modules.pullback (S.map (q ≫ D.proj))).obj (E j) :=
        (Scheme.Modules.pullbackComp (S.map q) (S.map D.proj)).app (E j) ≪≫
          (Scheme.Modules.pullbackCongr (S.map_comp q D.proj).symm).app (E j)
      refine HasInvertibleFiltration.of_iso comp₁ ?_
      by_cases hj : j = i
      · rw [hj]
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r i)] using
          D.hasInvertibleFiltration_pullback hEi q (by simpa only [Function.update_self] using hQ i)
      · simpa only [Function.update_of_ne hj] using hQ j

end ChernSetup

end Stacks.WeilCohomology

end
