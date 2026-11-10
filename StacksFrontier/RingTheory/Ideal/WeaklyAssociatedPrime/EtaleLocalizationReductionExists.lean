module

public import StacksFrontier.RingTheory.Flat.EtaleMapMaximalIdeal
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleLocalBaseTransport
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleLocalizationReduction

/-!
# Existence of the étale-local reduction of 05IG

The reduction recorded by `Stacks.WeaklyAssociatedPrimes.Reduction` always exists.  This is the
first half of the proof of [Stacks, Tag 05IG]:  the construction of the diagram
```
  S ⟶ S_g ⟶ S' ⟶ S'_{𝔭'}
      ↑       ↑     ↑
      R   ⟶  R' ⟶ R'_{𝔭'}
```
together with its primes and its module.

Two ingredients go into it.  The element `g` to be inverted is chosen by prime avoidance:  the
primes of `S` weakly associated to the fibre module `N ⊗_R κ(𝔭)` are *finitely many*, because by
`isWeaklyAssociatedPrime_tensorResidueField_iff` each of them is the contraction of a prime of the
Noetherian fibre ring `S ⊗_R κ(𝔭)` associated to `(S ⊗_R κ(𝔭)) ⊗_S N`, and a finite module over a
Noetherian ring has finitely many associated primes.  One element of `S ∖ 𝔮` therefore lies in
every one of them that is not contained in `𝔮`;  after inverting it no prime of the upper ring
contracts outside `𝔮`, which is `Reduction.below`.  This replaces [Stacks, Tag 0CU6] and
[Stacks, Tag 0CU7]:  the source makes the choice on the fibre ring and transports it along a flat
base change, whereas the finiteness above lets the choice be made on `S` itself.

The étale square is then the ring-theoretic form of [Stacks, Tag 05ID],
`Module.exists_elementaryEtaleLocalization_projective_baseChange`, applied to `R → S_g` and `N_g`;
localizing its lower ring at `𝔭'` makes the base local without disturbing projectivity, by
`Module.projective_of_isLocalizedModule`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.nonempty_reduction`: the reduction exists.
* `Stacks.WeaklyAssociatedPrimes.nonempty_reduction_of_square`: the reduction exists once the
  element `g` and the étale square of [Stacks, Tag 05ID] are given.
* `Stacks.WeaklyAssociatedPrimes.nonempty_reduction_aux`: the fields of `Reduction` hold for the
  diagram above, presented as abstract data.

## Implementation notes

`nonempty_reduction_aux` takes the whole diagram as abstract data — `S_g`, `N_g`, the square `R'`,
`S'`, the localizations `R₁`, `S₁`, `N₁` — together with the localization and base-change
hypotheses relating them.  Separating that from the construction of the data is not cosmetic:  with
the concrete `Localization`s and `LocalizedModule`s substituted throughout, a single tactic block
exhausts the elaborator's heartbeat budget.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 05FP](https://stacks.math.columbia.edu/tag/05FP)
* [Stacks Project, Tag 0CU6](https://stacks.math.columbia.edu/tag/0CU6)
* [Stacks Project, Tag 0CU7](https://stacks.math.columbia.edu/tag/0CU7)
-/

@[expose] public section

open TensorProduct

open IsLocalRing

universe u

namespace Stacks.WeaklyAssociatedPrimes

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Projectivity depends only on the module structure, so it transports along an equality of
module structures. -/
theorem projective_of_module_eq {A M : Type u} [CommRing A] [AddCommGroup M]
    {inst₁ inst₂ : Module A M} (h : inst₁ = inst₂)
    (hp : @Module.Projective A _ M _ inst₁) : @Module.Projective A _ M _ inst₂ := by
  subst h
  exact hp

/-- An ideal of a localization is determined by its contraction to the base ring. -/
theorem eq_of_comap_eq_of_isLocalization {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (U : Submonoid A) [IsLocalization U B] {I J : Ideal B}
    (h : I.comap (algebraMap A B) = J.comap (algebraMap A B)) : I = J := by
  rw [← IsLocalization.map_under U B I, ← IsLocalization.map_under U B J]
  exact congrArg (Ideal.map (algebraMap A B)) h

/-- **The reduction of [Stacks, Tag 05IG], read off the diagram it is built from.**  Given the
element `g` of the prime-avoidance step, an étale square as produced by [Stacks, Tag 05ID], and
localizations of that square at the chosen prime — all as abstract data — the fields of
`Stacks.WeaklyAssociatedPrimes.Reduction` can be verified. -/
theorem nonempty_reduction_aux
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (g : S)
    (hgmem : ∀ J : Ideal S, IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) J →
      ¬ J ≤ q → g ∈ J)
    (Sg : Type u) [CommRing Sg] [Algebra S Sg] [Algebra R Sg] [IsScalarTower R S Sg]
    [IsLocalization (Submonoid.powers g) Sg] [Module.Flat S Sg]
    (Ng : Type u) [AddCommGroup Ng] [Module Sg Ng] [Module S Ng] [Module R Ng]
    [IsScalarTower S Sg Ng] [IsScalarTower R Sg Ng] [IsScalarTower R S Ng]
    (fg : N →ₗ[S] Ng) [IsLocalizedModule (Submonoid.powers g) fg]
    (R' S' : Type u) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra Sg S']
    [Algebra R' S'] [Algebra S S'] [Algebra R S'] [Module.Flat R R'] [Module.Flat Sg S']
    [Algebra.Etale Sg S']
    [IsScalarTower S Sg S'] [IsScalarTower R S S'] [IsScalarTower R Sg S']
    [IsScalarTower R R' S']
    (p' : Ideal R') [p'.IsPrime] (q' : Ideal S') [q'.IsPrime] [q'.LiesOver p']
    (hq' : q'.comap (algebraMap S S') = q)
    (N' : Type u) [AddCommGroup N'] [Module S' N'] [Module R' N'] [Module Sg N'] [Module S N']
    [Module R N'] [IsScalarTower R' S' N'] [IsScalarTower Sg S' N'] [IsScalarTower S S' N']
    [IsScalarTower R S' N'] [IsScalarTower S Sg N'] [IsScalarTower R Sg N']
    [Module.Projective R' N']
    [Module.FinitePresentation S' N']
    (f' : Ng →ₗ[Sg] N') (hf' : IsBaseChange S' f')
    (R₁ S₁ : Type u) [CommRing R₁] [CommRing S₁] [IsLocalRing R₁]
    [Algebra R' R₁] [Algebra S' S₁] [Module.Flat R' R₁] [Module.Flat S' S₁]
    [IsLocalization p'.primeCompl R₁] [IsLocalization (primeComplImage S' p') S₁]
    [Algebra R₁ S₁] [Algebra R R₁] [Algebra R S₁] [Algebra S S₁] [Algebra Sg S₁]
    [IsScalarTower R S' S₁] [IsScalarTower S S' S₁] [IsScalarTower Sg S' S₁]
    [IsScalarTower R R' R₁]
    [IsScalarTower R R₁ S₁] [IsScalarTower R S S₁] [IsScalarTower S Sg S₁]
    [Algebra.FormallyUnramified Sg S₁] [Algebra.EssFiniteType Sg S₁]
    (N₁ : Type u) [AddCommGroup N₁] [Module S₁ N₁] [Module S' N₁] [Module R' N₁]
    [Module R₁ N₁] [Module S N₁] [Module R N₁]
    [IsScalarTower S' S₁ N₁] [IsScalarTower R₁ S₁ N₁] [IsScalarTower R' R₁ N₁]
    [IsScalarTower S S₁ N₁] [IsScalarTower R S₁ N₁] [IsScalarTower R R₁ N₁]
    [IsScalarTower R S N₁] [IsScalarTower R' S' N₁] [IsScalarTower S S' N₁]
    [IsScalarTower R S' N₁]
    [Module.FinitePresentation S₁ N₁]
    (f₁ : N' →ₗ[S'] N₁) [IsLocalizedModule (primeComplImage S' p') f₁]
    [IsNoetherianRing (S₁ ⧸ Ideal.map (algebraMap R₁ S₁) (maximalIdeal R₁))]
    (hmax : Ideal.map (algebraMap R R₁) p = maximalIdeal R₁)
    (hfib : Ideal.map (algebraMap R₁ S₁) (maximalIdeal R₁) ≤ q'.map (algebraMap S' S₁))
    (hessFP : (algebraMap R₁ S₁).EssentiallyOfFinitePresentation)
    (hPsi : ∀ (X : Type u) [AddCommGroup X] [Module R X],
      (IsWeaklyAssociatedPrime R₁ (R₁ ⊗[R] X) (maximalIdeal R₁) ↔
        IsWeaklyAssociatedPrime R X p)) :
    Nonempty (Reduction R S N p q) := by
  classical
  -- the prime `𝔮₁` of `S₁` and its contraction to `S`
  have hdisj : Disjoint ((primeComplImage S' p' : Submonoid S') : Set S') (q' : Set S') :=
    Ideal.disjoint_primeCompl_of_liesOver q' p'
  have hq1p : (q'.map (algebraMap S' S₁)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (primeComplImage S' p') _ q' inferInstance hdisj
  have hq1c : (q'.map (algebraMap S' S₁)).comap (algebraMap S' S₁) = q' :=
    IsLocalization.under_map_of_isPrime_disjoint (primeComplImage S' p') _ inferInstance hdisj
  have hcomapq : (q'.map (algebraMap S' S₁)).comap (algebraMap S S₁) = q := by
    rw [IsScalarTower.algebraMap_eq S S' S₁, ← Ideal.comap_comap, hq1c, hq']
  -- `N₁` is projective over `R₁` and finitely presented over `S₁`
  have hlocR' : IsLocalizedModule p'.primeCompl (f₁.restrictScalars R') :=
    IsLocalizedModule.restrictScalars (A := S') p'.primeCompl _
  have hprojN1 : Module.Projective R₁ N₁ :=
    Module.projective_of_isLocalizedModule (R := R') (Rₛ := R₁) p'.primeCompl
      (f₁.restrictScalars R')
  have hbc1 : IsBaseChange S₁ f₁ :=
    (isLocalizedModule_iff_isBaseChange (primeComplImage S' p') S₁ f₁).mp inferInstance
  -- flatness of `S → S₁` and of `R → N₁`
  have : Module.Flat Sg S₁ := Module.Flat.trans Sg S' S₁
  have : Module.Flat S S₁ := Module.Flat.trans S Sg S₁
  have : Module.Flat R R₁ := Module.Flat.trans R R' R₁
  have : Module.Flat R₁ N₁ := Module.Flat.of_projective
  have : Module.Flat R N₁ := Module.Flat.trans R R₁ N₁
  -- the base-change map `N → N₁`
  have hbcg : IsBaseChange Sg fg :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) Sg fg).mp inferInstance
  have hiota : IsBaseChange S₁
      ((f₁.restrictScalars S).comp ((f'.restrictScalars S).comp fg)) :=
    (hbcg.comp hf').comp hbc1
  -- the transport of weak association along `S → S₁`
  have hcc : ∀ t : Ideal S₁,
      ((t.comap (algebraMap S' S₁)).comap (algebraMap Sg S')).comap (algebraMap S Sg)
        = t.comap (algebraMap S S₁) := by
    intro t
    ext a
    simp only [Ideal.mem_comap]
    rw [← IsScalarTower.algebraMap_apply S Sg S', ← IsScalarTower.algebraMap_apply S S' S₁]
  have hcc2 : ∀ t : Ideal S₁,
      (t.comap (algebraMap Sg S₁)).comap (algebraMap S Sg) = t.comap (algebraMap S S₁) := by
    intro t
    ext a
    simp only [Ideal.mem_comap]
    rw [← IsScalarTower.algebraMap_apply S Sg S₁]
  have htransPhi : ∀ (s : Ideal S₁), s.IsPrime →
      ∀ (X : Type u) [AddCommGroup X] [Module R X],
      (IsWeaklyAssociatedPrime S₁ (N₁ ⊗[R] X) s ↔
        IsWeaklyAssociatedPrime S (N ⊗[R] X) (s.comap (algebraMap S S₁))) := by
    intro s hs X _ _
    have h1 := isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
      (R := R) (A := S') (A' := S₁) (P := N') (P' := N₁) (X := X)
      (primeComplImage S' p') f₁ s hs
    have hbridge : IsWeaklyAssociatedPrime S' (N' ⊗[R] X) (s.comap (algebraMap S' S₁)) ↔
        IsWeaklyAssociatedPrime S' (S' ⊗[Sg] (Ng ⊗[R] X)) (s.comap (algebraMap S' S₁)) :=
      ⟨isWeaklyAssociatedPrime_of_linearEquiv'
          (isBaseChange_tensorProduct_map (R := R) (P := X) _ hf').equiv.symm,
        isWeaklyAssociatedPrime_of_linearEquiv'
          (isBaseChange_tensorProduct_map (R := R) (P := X) _ hf').equiv⟩
    have h2 := isWeaklyAssociatedPrime_tensorProduct_iff_of_etale
      (A := Sg) (B := S') (X := Ng ⊗[R] X) (s.comap (algebraMap S' S₁))
    have h3 := isWeaklyAssociatedPrime_tensor_comap_iff_of_isLocalization
      (R := R) (A := S) (A' := Sg) (P := N) (P' := Ng) (X := X)
      (Submonoid.powers g) fg
      ((s.comap (algebraMap S' S₁)).comap (algebraMap Sg S')) inferInstance
    rw [h1, hbridge, h2, h3, hcc]
  -- incomparability
  have hincomparable : ∀ s : Ideal S₁, s.IsPrime → q'.map (algebraMap S' S₁) ≤ s →
      s.comap (algebraMap S S₁) = q → s = q'.map (algebraMap S' S₁) := by
    intro s hs hle hsq
    have := hs
    refine (eq_of_le_of_under_eq_of_formallyUnramified (A := Sg) hle ?_).symm
    refine eq_of_comap_eq_of_isLocalization (Submonoid.powers g) ?_
    rw [hcc2, hcc2, hcomapq, hsq]
  -- the key observation
  have hgunit : IsUnit (algebraMap S S₁ g) := by
    rw [IsScalarTower.algebraMap_apply S Sg S₁]
    exact (IsLocalization.map_units Sg
      (⟨g, Submonoid.mem_powers g⟩ : Submonoid.powers g)).map (algebraMap Sg S₁)
  have hbelow : ∀ s : Ideal S₁, s.IsPrime →
      IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) (s.comap (algebraMap S S₁)) →
      s.comap (algebraMap S S₁) ≤ q := by
    intro s hs hwa
    by_contra hns
    exact hs.ne_top (Ideal.eq_top_of_isUnit_mem s (hgmem _ hwa hns) hgunit)
  exact ⟨{ R₁ := R₁
           S₁ := S₁
           N₁ := N₁
           ι := (f₁.restrictScalars S).comp ((f'.restrictScalars S).comp fg)
           isBaseChange_ι := hiota
           q₁ := q'.map (algebraMap S' S₁)
           map_eq_maximalIdeal := hmax
           map_maximalIdeal_le := hfib
           comap_q₁ := hcomapq
           essFP := hessFP
           transΦ := htransPhi
           transΨ := hPsi
           incomparable := hincomparable
           below := hbelow }⟩


/-- **The reduction of [Stacks, Tag 05IG] from an étale square.**  Given the element `g` of the
prime-avoidance step and an elementary étale localization of `R → S_g` at `𝔮 S_g` whose base change
of `N_g` is projective over the lower ring, localizing the square at its lower prime produces a
`Stacks.WeaklyAssociatedPrimes.Reduction`. -/
theorem nonempty_reduction_of_square
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (g : S)
    (hgmem : ∀ J : Ideal S, IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) J →
      ¬ J ≤ q → g ∈ J)
    [(q.map (algebraMap S (Localization.Away g))).IsPrime]
    (hqgc : (q.map (algebraMap S (Localization.Away g))).comap
      (algebraMap S (Localization.Away g)) = q)
    (E : Algebra.ElementaryEtaleLocalization.{u, u, u, u} R (Localization.Away g)
      ((q.map (algebraMap S (Localization.Away g))).under R)
      (q.map (algebraMap S (Localization.Away g))))
    (hproj : letI : Module E.R' (E.S' ⊗[Localization.Away g]
          LocalizedModule (Submonoid.powers g) N) := Module.compHom _ (algebraMap E.R' E.S')
      Module.Projective E.R' (E.S' ⊗[Localization.Away g]
        LocalizedModule (Submonoid.powers g) N)) :
    Nonempty (Reduction R S N p q) := by
  classical
  -- capture the localization square of the lower ring before adding any algebra structure
  have htowR'R₁S₁ : IsScalarTower E.R' (Localization.AtPrime E.p')
      (Localization (primeComplImage E.S' E.p')) := inferInstance
  -- the composites `S → S'` and `R → S'`
  let : Algebra S E.S' := ((algebraMap (Localization.Away g) E.S').comp
    (algebraMap S (Localization.Away g))).toAlgebra
  have : IsScalarTower S (Localization.Away g) E.S' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R E.S' := ((algebraMap S E.S').comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S E.S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (Localization.Away g) E.S' := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap S E.S' (algebraMap R S r) = _
    rw [IsScalarTower.algebraMap_apply S (Localization.Away g) E.S',
      ← IsScalarTower.algebraMap_apply R S (Localization.Away g)]
  have htowRR'S' : IsScalarTower R E.R' E.S' := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change algebraMap (Localization.Away g) E.S'
      (algebraMap S (Localization.Away g) (algebraMap R S r)) = _
    rw [← IsScalarTower.algebraMap_apply R S (Localization.Away g)]
    exact RingHom.congr_fun E.commutes r
  have : Algebra.FinitePresentation R E.S' :=
    Algebra.FinitePresentation.trans R (Localization.Away g) E.S'
  have : Algebra.FinitePresentation E.R' E.S' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R E.R' E.S'
  -- projectivity, read for the canonical action of `R'` on the base change
  have hprojN' : Module.Projective E.R' (E.S' ⊗[Localization.Away g]
      LocalizedModule (Submonoid.powers g) N) :=
    projective_of_module_eq (inst₁ := Module.compHom _ (algebraMap E.R' E.S'))
      (Module.ext' _ _ fun a x => IsScalarTower.algebraMap_smul E.S' a x) hproj
  -- the three ring towers through the localizations
  have htowRSS₁ : IsScalarTower R S (Localization (primeComplImage E.S' E.p')) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [IsScalarTower.algebraMap_apply R E.S' (Localization (primeComplImage E.S' E.p')),
      IsScalarTower.algebraMap_apply R S E.S',
      ← IsScalarTower.algebraMap_apply S E.S' (Localization (primeComplImage E.S' E.p'))]
  have htowSSgS₁ : IsScalarTower S (Localization.Away g)
      (Localization (primeComplImage E.S' E.p')) := by
    refine IsScalarTower.of_algebraMap_eq fun s => ?_
    rw [IsScalarTower.algebraMap_apply S E.S' (Localization (primeComplImage E.S' E.p')),
      IsScalarTower.algebraMap_apply S (Localization.Away g) E.S',
      ← IsScalarTower.algebraMap_apply (Localization.Away g) E.S'
        (Localization (primeComplImage E.S' E.p'))]
  have htowRR₁S₁ : IsScalarTower R (Localization.AtPrime E.p')
      (Localization (primeComplImage E.S' E.p')) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    have h1 : algebraMap R (Localization.AtPrime E.p') r
        = algebraMap E.R' (Localization.AtPrime E.p') (algebraMap R E.R' r) :=
      IsScalarTower.algebraMap_apply R E.R' (Localization.AtPrime E.p') r
    have h2 : algebraMap E.R' (Localization (primeComplImage E.S' E.p')) (algebraMap R E.R' r)
        = algebraMap (Localization.AtPrime E.p') (Localization (primeComplImage E.S' E.p'))
            (algebraMap E.R' (Localization.AtPrime E.p') (algebraMap R E.R' r)) :=
      IsScalarTower.algebraMap_apply E.R' (Localization.AtPrime E.p')
        (Localization (primeComplImage E.S' E.p')) _
    have h3 : algebraMap R (Localization (primeComplImage E.S' E.p')) r
        = algebraMap E.S' (Localization (primeComplImage E.S' E.p')) (algebraMap R E.S' r) :=
      IsScalarTower.algebraMap_apply R E.S' (Localization (primeComplImage E.S' E.p')) r
    have h4 : algebraMap R E.S' r = algebraMap E.R' E.S' (algebraMap R E.R' r) :=
      IsScalarTower.algebraMap_apply R E.R' E.S' r
    have h5 : algebraMap E.R' (Localization (primeComplImage E.S' E.p')) (algebraMap R E.R' r)
        = algebraMap E.S' (Localization (primeComplImage E.S' E.p'))
            (algebraMap E.R' E.S' (algebraMap R E.R' r)) :=
      IsScalarTower.algebraMap_apply E.R' E.S'
        (Localization (primeComplImage E.S' E.p')) _
    rw [h1, ← h2, h5, ← h4, ← h3]
  -- the module structure of `N₁` over the local base
  let : Module (Localization.AtPrime E.p') (LocalizedModule (primeComplImage E.S' E.p')
      (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N)) :=
    Module.compHom _ (algebraMap (Localization.AtPrime E.p')
      (Localization (primeComplImage E.S' E.p')))
  have : IsScalarTower (Localization.AtPrime E.p')
      (Localization (primeComplImage E.S' E.p'))
      (LocalizedModule (primeComplImage E.S' E.p')
        (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower E.R' (Localization.AtPrime E.p')
      (LocalizedModule (primeComplImage E.S' E.p')
        (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N)) := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    change algebraMap (Localization.AtPrime E.p') (Localization (primeComplImage E.S' E.p'))
        (algebraMap E.R' (Localization.AtPrime E.p') r) • x = r • x
    rw [← IsScalarTower.algebraMap_apply E.R' (Localization.AtPrime E.p')
        (Localization (primeComplImage E.S' E.p')),
      IsScalarTower.algebraMap_smul]
  have : IsScalarTower R (Localization.AtPrime E.p')
      (LocalizedModule (primeComplImage E.S' E.p')
        (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N)) := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    change algebraMap (Localization.AtPrime E.p') (Localization (primeComplImage E.S' E.p'))
        (algebraMap R (Localization.AtPrime E.p') r) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime E.p')
        (Localization (primeComplImage E.S' E.p')),
      IsScalarTower.algebraMap_smul]
  -- unramifiedness of `S_g → S₁`
  have : Algebra.FormallyUnramified E.S' (Localization (primeComplImage E.S' E.p')) :=
    Algebra.FormallyUnramified.of_isLocalization (primeComplImage E.S' E.p')
  have : Algebra.FormallyUnramified (Localization.Away g)
      (Localization (primeComplImage E.S' E.p')) :=
    Algebra.FormallyUnramified.comp (Localization.Away g) E.S'
      (Localization (primeComplImage E.S' E.p'))
  have : Algebra.EssFiniteType E.S' (Localization (primeComplImage E.S' E.p')) :=
    Algebra.EssFiniteType.of_isLocalization (Localization (primeComplImage E.S' E.p'))
      (primeComplImage E.S' E.p')
  have : Algebra.EssFiniteType (Localization.Away g)
      (Localization (primeComplImage E.S' E.p')) :=
    Algebra.EssFiniteType.comp (Localization.Away g) E.S'
      (Localization (primeComplImage E.S' E.p'))
  -- `𝔭'` lies over `𝔭`, and the closed fibre ring is Noetherian
  have hpunder : (q.map (algebraMap S (Localization.Away g))).under R = p := by
    rw [Ideal.under_def, IsScalarTower.algebraMap_eq R S (Localization.Away g),
      ← Ideal.comap_comap, hqgc]
    exact ((q.over_def p).symm : q.comap (algebraMap R S) = p)
  have hp'over : E.p'.LiesOver p := ⟨by rw [← hpunder]; exact E.p'_liesOver⟩
  have : Algebra.FinitePresentation E.p'.ResidueField (E.p'.Fiber E.S') :=
    Algebra.FinitePresentation.baseChange _
  have : IsNoetherianRing (E.p'.Fiber E.S') :=
    Algebra.FiniteType.isNoetherianRing E.p'.ResidueField (E.p'.Fiber E.S')
  have : IsNoetherianRing (Localization (primeComplImage E.S' E.p') ⧸
      Ideal.map (algebraMap (Localization.AtPrime E.p')
        (Localization (primeComplImage E.S' E.p')))
        (IsLocalRing.maximalIdeal (Localization.AtPrime E.p'))) :=
    isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivQuotient E.p').toRingEquiv
  -- the contraction of `𝔮'` to `S`
  have hq'S : E.q'.comap (algebraMap S E.S') = q := by
    rw [IsScalarTower.algebraMap_eq S (Localization.Away g) E.S', ← Ideal.comap_comap,
      ← E.q'_liesOver_q, hqgc]
  exact nonempty_reduction_aux R S N p q g hgmem (Localization.Away g)
    (LocalizedModule (Submonoid.powers g) N)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) E.R' E.S' E.p' E.q' hq'S
    (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N)
    (TensorProduct.mk (Localization.Away g) E.S'
      (LocalizedModule (Submonoid.powers g) N) 1)
    (TensorProduct.isBaseChange (Localization.Away g)
      (LocalizedModule (Submonoid.powers g) N) E.S')
    (Localization.AtPrime E.p') (Localization (primeComplImage E.S' E.p'))
    (LocalizedModule (primeComplImage E.S' E.p')
      (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N))
    (LocalizedModule.mkLinearMap (primeComplImage E.S' E.p')
      (E.S' ⊗[Localization.Away g] LocalizedModule (Submonoid.powers g) N))
    (Algebra.map_eq_maximalIdeal_localizationAtPrime_of_formallyUnramified p E.p')
    (fibreIdeal_le_map E.p' E.q')
    (essentiallyOfFinitePresentation_localization E.p')
    fun X _ _ => isWeaklyAssociatedPrime_tensorProduct_localization_iff_of_etale p E.p' X

/-- **The étale-local reduction of [Stacks, Tag 05IG] exists.** -/
theorem nonempty_reduction (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.FinitePresentation S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Nonempty (Reduction R S N p q) := by
  classical
  -- the primes of `S` weakly associated to the fibre module are finitely many
  have : IsNoetherianRing (S ⊗[R] p.ResidueField) := isNoetherianRing_tensorResidueField p
  have : Module.Finite (S ⊗[R] p.ResidueField) ((S ⊗[R] p.ResidueField) ⊗[S] N) :=
    Module.Finite.base_change S _ N
  have hWfin : {J : Ideal S | IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) J}.Finite := by
    refine Set.Finite.subset (Set.Finite.image
      (fun q' : Ideal (S ⊗[R] p.ResidueField) =>
        q'.comap (algebraMap S (S ⊗[R] p.ResidueField)))
      (associatedPrimes.finite (S ⊗[R] p.ResidueField)
        ((S ⊗[R] p.ResidueField) ⊗[S] N))) ?_
    intro J hJ
    obtain ⟨q', hq', hJeq⟩ := (isWeaklyAssociatedPrime_tensorResidueField_iff p J).mp hJ
    obtain ⟨hpr, m, hm⟩ := hq'
    rw [Submodule.colon_span] at hm
    exact ⟨q', ⟨hpr, m, by rw [hm]; exact hpr.radical.symm⟩, hJeq.symm⟩
  -- prime avoidance chooses the element to invert
  obtain ⟨g, hgq, hgmem⟩ := exists_notMem_and_forall_mem q
    (u := {J : Ideal S | IsWeaklyAssociatedPrime S (N ⊗[R] p.ResidueField) J ∧ ¬ J ≤ q})
    (hWfin.subset fun _ hJ => hJ.1) fun _ hJ => hJ.2
  -- invert it and apply the structure theorem
  have : Algebra.FinitePresentation S (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FinitePresentation R (Localization.Away g) :=
    Algebra.FinitePresentation.trans R S (Localization.Away g)
  have : Module.Flat R (LocalizedModule (Submonoid.powers g) N) :=
    Module.Flat.of_isLocalizedModule_tower (Submonoid.powers g)
      (LocalizedModule.mkLinearMap (Submonoid.powers g) N)
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid S) : Set S) (q : Set S) := by
    refine Set.disjoint_left.mpr ?_
    rintro a ⟨n, rfl⟩ ha
    exact hgq ((‹q.IsPrime›).mem_of_pow_mem n ha)
  have : (q.map (algebraMap S (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ q inferInstance hdisj
  have hqgc : (q.map (algebraMap S (Localization.Away g))).comap
      (algebraMap S (Localization.Away g)) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) _ inferInstance hdisj
  obtain ⟨E, hproj⟩ := Module.exists_elementaryEtaleLocalization_projective_baseChange R
    (Localization.Away g) (LocalizedModule (Submonoid.powers g) N)
    (q.map (algebraMap S (Localization.Away g)))
  exact nonempty_reduction_of_square R S N p q g
    (fun J hJ hJq => hgmem J ⟨hJ, hJq⟩) hqgc E hproj

end Stacks.WeaklyAssociatedPrimes

end
