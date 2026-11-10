module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundlePullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bridge
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
public import StacksCore.Tactic.StacksAttribute

/-!
# The splitting principle in Chow homology

Let `X` be locally of finite type over the base of a Chow situation and let `ℰ_i`, `i ∈ I`
finite, be finite locally free `𝒪_X`-modules of constant ranks `r_i`. There is a flat proper
morphism `π : P ⟶ X` of relative dimension `d = ∑_i binom(r_i, 2)` such that, for every
`f : Y ⟶ X`, flat pullback on Chow groups along the base change `π_Y : Y ×_X P ⟶ Y` is injective
in every degree, and each `π^*ℰ_i` has a filtration of length `r_i` whose successive quotients
are invertible. The morphism `π` is proper; it is not asserted to be projective. Each layer of
the tower is the projective bundle `𝐏(ℰ) ⟶ X` of a finite locally free module of constant rank,
which is a `Stacks.Chow.BundleStep`.

## Main definitions

* `Stacks.Chow.BaseChangeInjective`: in every cartesian square over `π` and an `f : Y ⟶ X`,
  flat pullback along the base change of `π` is injective in every degree.
* `Stacks.Chow.bundleTautological`: the tautological surjection `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` for the
  projective bundle of a finite locally free module.
* `Stacks.Chow.bundleStep`: a layer `Stacks.Chow.BundleStep` of a finite locally free module of
  rank `m + 1`.

## Main results

* `Stacks.Chow.exists_bundleStep_baseChangeInjective`: the projective bundle of a finite locally
  free module of rank `m + 1` is a layer whose projection satisfies
  `Stacks.Chow.BaseChangeInjective`.
* `Stacks.Chow.baseChangeInjective_bundleProj`: the projection of `𝐏(ℰ)` satisfies
  `Stacks.Chow.BaseChangeInjective`.
* `Stacks.Chow.baseChangeInjective_splittingMorphismId` and
  `Stacks.Chow.baseChangeInjective_compStep`: the same property for the identity and for a layer
  composed onto a tower.
* `Stacks.Chow.exists_splittingMorphism_unconditional`: the splitting principle over `X`.
* `Stacks.Chow.exists_splittingMorphism_basechange_uniform`: the splitting principle over `X`,
  with flat pullback injective after every base change of the one morphism `π`.
* `Stacks.Chow.exists_splittingMorphism_basechange_unconditional`: the splitting principle over
  `Y` for the modules `f^*ℰ_i`.

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow


/-! ### Injectivity of flat pullback along a composite, and along an isomorphism -/

/-- If `p = f ≫ g` with `f` flat of relative dimension `r` and `g` flat of relative dimension
`s`, `t = r + s`, and if `f^*` is injective in degree `k + s` and `g^*` is injective in degree
`k`, then `p^*` is injective in degree `k`. -/
private theorem injective_flatPullbackChow_of_comp_eq (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g] (p : X ⟶ Z)
    [LocallyOfFiniteType p] [Flat p] (hp : f ≫ g = p) (hfbase : f ≫ sY = sX)
    (hgbase : g ≫ sZ = sY) (hpbase : p ≫ sZ = sX) (r s t : ℕ) (ht : t = r + s)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s)
    (hpt : AlgebraicGeometry.RelativeDimension p t) (k : ℤ)
    (hfacf : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hfbase r hf (k + (s : ℤ)))
    (hfacg : FlatPullbackFactorsThroughRationalEquivalence C sY sZ g hgbase s hg k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sZ p hpbase t hpt k)
    (hinjf : Function.Injective (flatPullbackChow C sX sY f hfbase r hf (k + (s : ℤ)) hfacf))
    (hinjg : Function.Injective (flatPullbackChow C sY sZ g hgbase s hg k hfacg)) :
    Function.Injective (flatPullbackChow C sX sZ p hpbase t hpt k hfacp) := by
  subst hp ht
  intro α β hαβ
  exact hinjg (hinjf (eq_of_heq ((flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k
    hfacf hfacg hfacp α).trans ((heq_of_eq hαβ).trans
      (flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k hfacf hfacg hfacp β).symm))))

/-- If `p = ε ≫ q` with `ε` an isomorphism over the base and `q` flat of relative dimension `r`
with injective flat pullback in degree `k`, then `p^*` is injective in degree `k`. -/
private theorem injective_flatPullbackChow_of_iso_comp (C : ChowSituation.{u})
    {X A Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (ε : X ≅ A)
    (q : A ⟶ Y) [LocallyOfFiniteType q] [Flat q] (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p]
    (hp : ε.hom ≫ q = p) (hebase : ε.hom ≫ sA = sX) (hqbase : q ≫ sY = sA)
    (hpbase : p ≫ sY = sX) (r : ℕ) (hq : AlgebraicGeometry.RelativeDimension q r)
    (hpr : AlgebraicGeometry.RelativeDimension p r) (k : ℤ)
    (hfacq : FlatPullbackFactorsThroughRationalEquivalence C sA sY q hqbase r hq k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sY p hpbase r hpr k)
    (hinjq : Function.Injective (flatPullbackChow C sA sY q hqbase r hq k hfacq)) :
    Function.Injective (flatPullbackChow C sX sY p hpbase r hpr k hfacp) := by
  have hface := flatPullbackFactorsThroughRationalEquivalence_general C sX sA ε.hom hebase 0
    (relativeDimension_of_isIso ε.hom) (k + (r : ℤ))
  exact injective_flatPullbackChow_of_comp_eq C sX sA sY ε.hom q p hp hebase hqbase hpbase 0 r r
    (Nat.zero_add r).symm (relativeDimension_of_isIso ε.hom) hq hpr k hface hfacq hfacp
    (flatPullbackChow_bijective_of_isIso C sX sA ε.hom hebase (relativeDimension_of_isIso ε.hom)
      (k + (r : ℤ)) hface).injective hinjq

/-- If two cartesian squares over `π` and `f` have the same corner `Y`, the flat pullback along the
second vertical map `q` is injective in degree `k`, and the first vertical map `πY` is flat of the
same relative dimension, then so is flat pullback along `πY`. -/
private theorem injective_flatPullbackChow_of_isPullback_pullback (C : ChowSituation.{u})
    {X P Y PY A : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sPY : PY ⟶ C.S)
    [LocallyOfFiniteType sPY] (sA : A ⟶ C.S) [LocallyOfFiniteType sA] {π : P ⟶ X} {f : Y ⟶ X}
    {b : PY ⟶ P} {πY : PY ⟶ Y} {b' : A ⟶ P} {q : A ⟶ Y} (hsq : IsPullback b πY π f)
    (hsq2 : IsPullback b' q π f) [LocallyOfFiniteType q] [Flat q] [LocallyOfFiniteType πY]
    [Flat πY] (hsPY : πY ≫ sY = sPY) (hqbase : q ≫ sY = sA) (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r)
    (hrd : AlgebraicGeometry.RelativeDimension πY r) (k : ℤ)
    (hinjq : Function.Injective (flatPullbackChow C sA sY q hqbase r hq k
      (flatPullbackFactorsThroughRationalEquivalence_general C sA sY q hqbase r hq k))) :
    Function.Injective (flatPullbackChow C sPY sY πY hsPY r hrd k
      (flatPullbackFactorsThroughRationalEquivalence_general C sPY sY πY hsPY r hrd k)) := by
  have hi := IsPullback.isoIsPullback_hom_snd _ _ hsq hsq2
  exact injective_flatPullbackChow_of_iso_comp C sPY sA sY (IsPullback.isoIsPullback _ _ hsq hsq2)
    q πY hi (by rw [← hqbase, ← Category.assoc, hi, hsPY]) hqbase hsPY r hq hrd k _ _ hinjq

/-! ### Injectivity of `π^*` from the projective space bundle map -/

/-- Flat pullback along a flat morphism `π` of relative dimension `r` whose projective space
bundle map is injective is injective in every degree. -/
private theorem injective_flatPullbackChow_of_relationInjective (C : ChowSituation.{u})
    {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
    (r : ℕ) (hrd : AlgebraicGeometry.RelativeDimension π r)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP r hrd k)
    (twist : ChernCapOperator C sP)
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP (r + 1) hrd hfac twist) (k : ℤ) :
    Function.Injective (flatPullbackChow C sP sX π hsP r hrd k (hfac k)) := by
  classical
  have hk : k + ((r + 1 : ℕ) : ℤ) - ((r + 1 - 0 : ℕ) : ℤ) = k := by push_cast; ring
  have hcomp := (hinj (k + ((r + 1 : ℕ) : ℤ))).comp
    (Pi.single_injective (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)))
  have hterm : Function.Injective (projectiveBundleChernTerm C sX sP π hsP (r + 1) hrd hfac twist
      (k + ((r + 1 : ℕ) : ℤ)) 0 (Nat.zero_le _)) := by
    intro x y hxy
    apply hcomp
    simp only [Function.comp_apply]
    rw [Finset.sum_eq_single (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)),
      Finset.sum_eq_single (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1))]
    · simpa only [Pi.single_eq_same] using hxy
    all_goals first
      | (intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero])
      | (intro h; exact absurd (Finset.mem_univ _) h)
  simp only [projectiveBundleChernTerm, projectiveBundlePullback, AddMonoidHom.coe_comp] at hterm
  have hcongr : ∀ {a b : ℤ}, a = b →
      Function.Injective (flatPullbackChow C sP sX π hsP r hrd a (hfac a)) →
        Function.Injective (flatPullbackChow C sP sX π hsP r hrd b (hfac b)) := by
    rintro a b rfl
    exact id
  exact hcongr hk hterm.of_comp.of_comp

/-- Flat pullback along the identity is injective. -/
theorem injective_flatPullbackChow_id (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sX (𝟙 X) (Category.id_comp sX) 0
      (relativeDimension_identity X) k) :
    Function.Injective (flatPullbackChow C sX sX (𝟙 X) (Category.id_comp sX) 0
      (relativeDimension_identity X) k hfac) := by
  intro x y hxy
  have h := (flatPullbackChow_id C sX k x).symm.trans (hxy.trans (flatPullbackChow_id C sX k y))
  exact (chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp)).injective h

/-! ### Injectivity of flat pullback after every base change -/

/-- For a flat morphism `π : P ⟶ X` of relative dimension `d`: in every cartesian square

  `b : P_Y ⟶ P`, `π_Y : P_Y ⟶ Y`, `f : Y ⟶ X`, `π : P ⟶ X`,

flat pullback on Chow groups along the base change `π_Y` is injective in every degree. -/
def BaseChangeInjective (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (d : ℕ) : Prop :=
  ∀ {Y PY : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sPY : PY ⟶ C.S)
    [LocallyOfFiniteType sPY] (f : Y ⟶ X) (b : PY ⟶ P) (πY : PY ⟶ Y),
    IsPullback b πY π f → ∀ [LocallyOfFiniteType πY] [Flat πY] (hsPY : πY ≫ sY = sPY)
      (hrd : AlgebraicGeometry.RelativeDimension πY d) (k : ℤ),
      Function.Injective (flatPullbackChow C sPY sY πY hsPY d hrd k
        (flatPullbackFactorsThroughRationalEquivalence_general C sPY sY πY hsPY d hrd k))

/-! ### The layer exists: the projective bundle of a finite locally free module -/

section Layer

variable {X : Scheme.{u}} (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The tautological surjection `π^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` for the projective bundle of a finite
locally free module. -/
def bundleTautological : (Scheme.Modules.pullback (bundleProj E)).obj E ⟶ bundleTwist E :=
  Stacks.ProjectiveBundleSplitting.tautologicalMap E (bundlePieces E)

/-- **The tautological surjection is an epimorphism**: Stacks 0B3V,
`Stacks.ProjectiveBundleSplitting.epi_tautologicalMap`, whose quasi-coherence hypothesis a finite
locally free module satisfies. -/
@[ega "II 4.1.6" "(1), special case"]
instance epi_bundleTautological : Epi (bundleTautological E) :=
  haveI : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (bundlePieces E)

/-- **The tautological sequence `0 ⟶ 𝓕 ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0` is short exact**: Stacks 0B3V. The
kernel is taken as the categorical kernel, so exactness in the middle is
`CategoryTheory.ShortComplex.exact_kernel` and surjectivity on the right is
`Stacks.Chow.epi_bundleTautological`. -/
@[sga "6 VII 1.8" "partial"]
theorem shortExact_bundleTautological :
    (ShortComplex.mk (kernel.ι (bundleTautological E)) (bundleTautological E)
      (kernel.condition (bundleTautological E))).ShortExact :=
  { exact := ShortComplex.exact_kernel (bundleTautological E)
    mono_f := inferInstanceAs (Mono (kernel.ι (bundleTautological E)))
    epi_g := inferInstanceAs (Epi (bundleTautological E)) }

/-- **The tautological kernel of the bundle of a module of rank `m + 1` is finite locally free of
rank `m`**: Stacks 0B3V, by
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible` applied
to `π^*ℰ`, which has the same constant rank as `ℰ`. This includes the rank-one end `m = 0`, where
the kernel is of rank zero. -/
@[ega "IV 19.4.11"]
theorem isFiniteLocallyFreeOfRank_kernel_bundleTautological (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel (bundleTautological E)) m :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (bundleTautological E) (epi_bundleTautological E) (isInvertible_bundleTwist E) m
    (have := hm; AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ E (m + 1))

end Layer

/-- Flat pullback along the projection of the projective bundle of a module of constant rank
`m + 1` is injective in every degree. -/
private theorem injective_flatPullbackChow_bundleProj (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1))
    [LocallyOfFiniteType (bundleProj E)] [Flat (bundleProj E)]
    (hd : AlgebraicGeometry.RelativeDimension (bundleProj E) m)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E ≫ sX) sX
      (bundleProj E) rfl m hd k) (k : ℤ) :
    Function.Injective (flatPullbackChow C (bundleProj E ≫ sX) sX (bundleProj E) rfl m hd k
      (hfac k)) := by
  have := hm
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    hm.isFiniteLocallyFree
  exact injective_flatPullbackChow_of_relationInjective C sX (bundleProj E ≫ sX) (bundleProj E)
    rfl m hd hfac (invCap C (bundleProj E ≫ sX) (bundleTwist E))
    (projectiveBundleRelationInjective_of_bundleMap C sX (bundleProj E ≫ sX) (bundleProj E) rfl m
      hd hfac (invCap C (bundleProj E ≫ sX) (bundleTwist E))
      fun k ↦ (projectiveBundle_formula E m C sX k).1) k

/-- For `ℰ` finite locally free of constant rank `m + 1` on `X` and any cartesian square over
`π : 𝐏(ℰ) ⟶ X` and `f : Y ⟶ X`, flat pullback along the base-changed projection is injective in
every degree. -/
theorem baseChangeInjective_bundleProj (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1))
    [LocallyOfFiniteType (bundleProj E)] [Flat (bundleProj E)] :
    BaseChangeInjective C sX (bundleProj E) m := by
  intro Y PY sY _ sPY _ f b πY hsq _ _ hsPY hrd k
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) (m + 1) :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ f E (m + 1) hm
  have := hm'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) := hm'.isFiniteLocallyFree
  have : ((Scheme.Modules.pullback f).obj E).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  have : LocallyOfFiniteType (bundleProj ((Scheme.Modules.pullback f).obj E)) :=
    locallyOfFiniteType_bundleProj ((Scheme.Modules.pullback f).obj E) m
  have : Flat (bundleProj ((Scheme.Modules.pullback f).obj E)) :=
    flat_bundleProj ((Scheme.Modules.pullback f).obj E) m
  have hd' : AlgebraicGeometry.RelativeDimension
      (bundleProj ((Scheme.Modules.pullback f).obj E)) m :=
    relativeDimension_bundleProj ((Scheme.Modules.pullback f).obj E) m
  exact injective_flatPullbackChow_of_isPullback_pullback C sY sPY
    (bundleProj ((Scheme.Modules.pullback f).obj E) ≫ sY)
    (q := bundleProj ((Scheme.Modules.pullback f).obj E)) hsq
    (Stacks.ProjectiveBundle.isPullback_baseChangeHom f E (bundlePieces E)
      ((Scheme.Modules.pullback f).obj E)
      (bundlePieces ((Scheme.Modules.pullback f).obj E)) (Iso.refl _)).flip hsPY rfl m hd' hrd k
    (injective_flatPullbackChow_bundleProj C sY ((Scheme.Modules.pullback f).obj E) m hm' hd'
      (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
        (bundleProj ((Scheme.Modules.pullback f).obj E) ≫ sY) sY
        (bundleProj ((Scheme.Modules.pullback f).obj E)) rfl m hd' j) k)

/-- For a finite locally free module `ℰ` of rank `m + 1` there is a layer
`Stacks.Chow.BundleStep` of `ℰ`, the projective bundle of `ℰ`, whose projection satisfies
`Stacks.Chow.BaseChangeInjective`. -/
theorem exists_bundleStep_baseChangeInjective (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    ∃ D : BundleStep C sX E m, BaseChangeInjective C sX D.π m := by
  have := hm
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    hm.isFiniteLocallyFree
  have : Flat (bundleProj E) := flat_bundleProj E m
  have : LocallyOfFiniteType (bundleProj E) := locallyOfFiniteType_bundleProj E m
  have hd : AlgebraicGeometry.RelativeDimension (bundleProj E) m :=
    relativeDimension_bundleProj E m
  have hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C (bundleProj E ≫ sX) sX
      (bundleProj E) rfl m hd k := fun k ↦
    flatPullbackFactorsThroughRationalEquivalence_general C (bundleProj E ≫ sX) sX
      (bundleProj E) rfl m hd k
  exact ⟨{ P := bundle E
           sP := bundleProj E ≫ sX
           π := bundleProj E
           hsP := rfl
           relDim := hd
           hfac := hfac
           twist := invCap C (bundleProj E ≫ sX) (bundleTwist E)
           hinj := projectiveBundleRelationInjective_of_bundleMap C sX (bundleProj E ≫ sX)
             (bundleProj E) rfl m hd hfac (invCap C (bundleProj E ≫ sX) (bundleTwist E))
             fun k ↦ (projectiveBundle_formula E m C sX k).1
           twistModule := bundleTwist E
           twistModule_isInvertible := isInvertible_bundleTwist E
           sub := kernel (bundleTautological E)
           incl := kernel.ι (bundleTautological E)
           quot := bundleTautological E
           incl_comp_quot := kernel.condition (bundleTautological E)
           shortExact := shortExact_bundleTautological E
           sub_rank := isFiniteLocallyFreeOfRank_kernel_bundleTautological E m hm },
    baseChangeInjective_bundleProj C sX E m hm⟩

/-- Every finite locally free module of rank `m + 1` has a layer `Stacks.Chow.BundleStep`. -/
theorem nonempty_bundleStep (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    Nonempty (BundleStep C sX E m) :=
  ⟨(exists_bundleStep_baseChangeInjective C sX E m hm).choose⟩

/-- A layer `Stacks.Chow.BundleStep` of a finite locally free module of rank `m + 1`, chosen so
that its projection satisfies `Stacks.Chow.BaseChangeInjective`. -/
def bundleStep (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    BundleStep C sX E m :=
  (exists_bundleStep_baseChangeInjective C sX E m hm).choose

/-- In every cartesian square over the projection of `Stacks.Chow.bundleStep` and a morphism
`f : Y ⟶ X`, flat pullback along the base change of the projection is injective in every
degree. -/
theorem baseChangeInjective_bundleStep (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (m : ℕ)
    (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)) :
    BaseChangeInjective C sX (bundleStep C sX E m hm).π m :=
  (exists_bundleStep_baseChangeInjective C sX E m hm).choose_spec

/-! ### Clause (1) after a base change along the iteration -/

/-- The identity of `X` satisfies `Stacks.Chow.BaseChangeInjective` in relative dimension `0`. -/
theorem baseChangeInjective_splittingMorphismId (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] :
    BaseChangeInjective C sX (SplittingMorphism.id C sX).π 0 := by
  intro Y PY sY _ sPY _ g b πY hsq _ _ hsPY hrd k
  exact injective_flatPullbackChow_of_isPullback_pullback C sY sPY sY hsq
    (IsPullback.of_vert_isIso ⟨by simp⟩ : IsPullback g (𝟙 Y) (𝟙 X) g) hsPY
    (Category.id_comp sY) 0 (relativeDimension_identity Y) hrd k
    (injective_flatPullbackChow_id C sY k _)

/-- If the projection of the layer `D` and the tower `T` both satisfy
`Stacks.Chow.BaseChangeInjective`, so does the composite
`Stacks.Chow.SplittingMorphism.compStep D T`. -/
theorem baseChangeInjective_compStep {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {E : X.Modules} {m : ℕ} (D : BundleStep C sX E m) {n : ℕ}
    (T : SplittingMorphism C D.sP n) (hD : BaseChangeInjective C sX D.π m)
    (hT : BaseChangeInjective C D.sP T.π n) :
    BaseChangeInjective C sX (SplittingMorphism.compStep D T).π (n + m) := by
  change BaseChangeInjective C sX (T.π ≫ D.π) (n + m)
  intro Y PY sY _ sPY _ g b πY hsq _ _ hsPY hrd k
  have hQ : IsPullback (pullback.fst D.π g) (pullback.snd D.π g) D.π g :=
    IsPullback.of_hasPullback D.π g
  have : LocallyOfFiniteType (pullback.snd D.π g) :=
    MorphismProperty.of_isPullback hQ (P := @LocallyOfFiniteType) inferInstance
  have : Flat (pullback.snd D.π g) :=
    MorphismProperty.of_isPullback hQ (P := @AlgebraicGeometry.Flat) inferInstance
  have hdQ : AlgebraicGeometry.RelativeDimension (pullback.snd D.π g) m :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hQ D.relDim
  have hw : (b ≫ T.π) ≫ D.π = πY ≫ g := (Category.assoc _ _ _).trans hsq.w
  have hlift : hQ.lift (b ≫ T.π) πY hw ≫ pullback.snd D.π g = πY :=
    hQ.lift_snd (b ≫ T.π) πY hw
  have hliftf : hQ.lift (b ≫ T.π) πY hw ≫ pullback.fst D.π g = b ≫ T.π :=
    hQ.lift_fst (b ≫ T.π) πY hw
  have hbig : IsPullback b (hQ.lift (b ≫ T.π) πY hw ≫ pullback.snd D.π g)
      (T.π ≫ D.π) g := by rwa [hlift]
  have htop : IsPullback b (hQ.lift (b ≫ T.π) πY hw) T.π (pullback.fst D.π g) :=
    hbig.of_bot hliftf.symm hQ
  have : LocallyOfFiniteType (hQ.lift (b ≫ T.π) πY hw) :=
    MorphismProperty.of_isPullback htop (P := @LocallyOfFiniteType) inferInstance
  have : Flat (hQ.lift (b ≫ T.π) πY hw) :=
    MorphismProperty.of_isPullback htop (P := @AlgebraicGeometry.Flat) inferInstance
  have hdw : AlgebraicGeometry.RelativeDimension (hQ.lift (b ≫ T.π) πY hw) n :=
    AlgebraicGeometry.RelativeDimension.of_isPullback htop T.relDim
  have hwbase : hQ.lift (b ≫ T.π) πY hw ≫ (pullback.snd D.π g ≫ sY) = sPY :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun t ↦ t ≫ sY) hlift).trans hsPY)
  exact injective_flatPullbackChow_of_comp_eq C sPY (pullback.snd D.π g ≫ sY) sY
    (hQ.lift (b ≫ T.π) πY hw) (pullback.snd D.π g) πY hlift hwbase rfl hsPY n m (n + m) rfl
    hdw hdQ hrd k
    (flatPullbackFactorsThroughRationalEquivalence_general C sPY
      (pullback.snd D.π g ≫ sY) _ hwbase n hdw (k + (m : ℤ)))
    (flatPullbackFactorsThroughRationalEquivalence_general C (pullback.snd D.π g ≫ sY) sY
      (pullback.snd D.π g) rfl m hdQ k)
    (flatPullbackFactorsThroughRationalEquivalence_general C sPY sY πY hsPY (n + m) hrd k)
    (hT (pullback.snd D.π g ≫ sY) sPY (pullback.fst D.π g) b
      (hQ.lift (b ≫ T.π) πY hw) htop hwbase hdw (k + (m : ℤ)))
    (hD sY (pullback.snd D.π g ≫ sY) g (pullback.fst D.π g) (pullback.snd D.π g) hQ
      rfl hdQ k)
/-! ### The splitting principle with injectivity after every base change -/

/-- If every layer `step` satisfies `Stacks.Chow.BaseChangeInjective`, then for every finite
family of finite locally free modules of constant ranks `r_i` with `∑ binom(r_i, 2) = n` there is
a tower of relative dimension `n` satisfying `Stacks.Chow.BaseChangeInjective` that splits every
module of the family. -/
private theorem exists_splittingMorphism_baseChangeInjective_aux (C : ChowSituation.{u})
    (step : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) →
        BundleStep C sY F m)
    (hstep : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ)
      (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1)),
        BaseChangeInjective C sY (step sY F m hF).π m) :
    ∀ (n : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type)
      [Fintype I] (E : I → X.Modules) (r : I → ℕ),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) →
      ∑ i, (r i).choose 2 = n →
      ∃ T : SplittingMorphism C sX n, BaseChangeInjective C sX T.π n ∧
        ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X sX _ I _ E r hE hn
    by_cases hr : ∀ i, r i ≤ 1
    · have hn0 : n = 0 := by
        rw [← hn]
        exact Finset.sum_eq_zero fun i _ ↦ Nat.choose_eq_zero_of_lt ((hr i).trans_lt one_lt_two)
      subst hn0
      exact ⟨SplittingMorphism.id C sX, baseChangeInjective_splittingMorphismId C sX,
        fun i ↦ Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one _ (r i)
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (𝟙 X) (E i) (r i) (hE i))
          (hr i)⟩
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have hi : 1 < r i := by omega
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (r i - 1 + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ r i by omega)]
      exact hE i
    set D := step sX (E i) (r i - 1) hEi with hD
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j)
        (Function.update r i (r i - 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E j) (r j) (hE j)
    have hchoose : (r i - 1).choose 2 + (r i - 1) = (r i).choose 2 := by
      obtain ⟨m, hm⟩ : ∃ m, r i = m + 1 := ⟨r i - 1, by omega⟩
      have key : (m + 1).choose 2 = m.choose 2 + m := by
        change Nat.choose (m + 1) (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        change m + Nat.choose m 2 = Nat.choose m 2 + m
        omega
      rw [hm, Nat.add_sub_cancel, key]
    have hA : (∑ j, (Function.update r i (r i - 1) j).choose 2) =
        (r i - 1).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j ↦ (Function.update r i (r i - 1) j).choose 2) (Finset.mem_univ i),
        Function.update_self]
      exact congrArg _ (Finset.sum_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hB : (∑ j, (r j).choose 2) =
        (r i).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 :=
      (Finset.add_sum_erase Finset.univ (fun j ↦ (r j).choose 2) (Finset.mem_univ i)).symm
    have hsum : (∑ j, (Function.update r i (r i - 1) j).choose 2) + (r i - 1) = n := by
      rw [hA, ← hn, hB]; omega
    have hlt : (∑ j, (Function.update r i (r i - 1) j).choose 2) < n := by
      rw [hA, ← hn, hB]; omega
    obtain ⟨T, hTb, hT⟩ := ih _ hlt D.sP I
      (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub)
      (Function.update r i (r i - 1)) hE' rfl
    subst hsum
    refine ⟨SplittingMorphism.compStep D T,
      baseChangeInjective_compStep D T (hstep sX (E i) (r i - 1) hEi) hTb, fun j ↦ ?_⟩
    simp only [SplittingMorphism.compStep_P, SplittingMorphism.compStep_π]
    have comp₁ : (Scheme.Modules.pullback T.π).obj
          ((Scheme.Modules.pullback D.π).obj (E j)) ≅
        (Scheme.Modules.pullback (T.π ≫ D.π)).obj (E j) :=
      (Scheme.Modules.pullbackComp T.π D.π).app (E j)
    by_cases hj : j = i
    · rw [hj] at comp₁ ⊢
      have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
          (Scheme.Modules.pullback T.π)).ShortExact :=
        Stacks.WeilCohomology.shortExact_map_pullback T.π _ D.shortExact
      have hleft : Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj D.sub) (r i - 1) := by
        simpa only [Function.update_self] using hT i
      have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback T.π).obj
            ((Scheme.Modules.pullback D.π).obj (E i))) (r i - 1 + 1) :=
        @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.π _ _
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E i) _ hEi)
      refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Nat.sub_add_cancel (show 1 ≤ r i by omega)] using
        Stacks.WeilCohomology.HasInvertibleFiltration.step _ _ _ hDx
          (Stacks.WeilCohomology.isInvertible_pullback_obj T.π D.twistModule
            D.twistModule_isInvertible)
          hrank.isFiniteLocallyFree hleft
    · refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Function.update_of_ne hj] using hT j

/-! ### The splitting principle -/

/-- The splitting principle. Let `X` be locally of finite type over the base `S` of `C` and let
`ℰ_i`, `i ∈ I` finite, be finite locally free `𝒪_X`-modules of constant ranks `r_i`. There is a
flat proper morphism `π : P ⟶ X` of relative dimension `d = ∑_i binom(r_i, 2)` such that

1. the flat pullback `π^* : A_k(X) ⟶ A_{k+d}(P)` is injective in every degree, and
2. each `π^*ℰ_i` has a filtration of length `r_i` whose successive quotients are invertible
   `𝒪_P`-modules. -/
@[stacks 02UL "clauses (1) and (2) over X itself, for a finite collection of finite locally free \
modules of constant ranks r_i, with relative dimension d = sum of binom(r_i, 2), and NOTHING \
CARRIED: the only hypotheses are that each module is finite locally free of constant rank r_i.  \
The layer of the tower is the projective bundle of the module itself, Stacks.Chow.bundleStep, so \
every fact about it that the parametrised form exists_splittingMorphism takes in its step \
argument is PROVED \
here: Stacks 02TX for flatness and relative dimension m of the projection \
(Stacks.Chow.flat_bundleProj, Stacks.Chow.relativeDimension_bundleProj -- for an arbitrary \
module of constant rank, not only for a free one), Stacks 0800 for properness \
(Stacks.Chow.isProper_bundleProj), Stacks 02S1 for the descent of flat pullback to Chow groups \
(Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general, with nothing carried), \
Stacks 01O4, 02SO and 02TI for c_1(O_P(1)) cap - (Stacks.Chow.bundleTwist with \
Stacks.Chow.invCap), the injectivity half of Stacks 02TX for the projective space bundle map \
(Stacks.Chow.projectiveBundleRelationInjective_of_bundleMap at \
Stacks.Chow.projectiveBundle_formula), and Stacks 0B3V for the tautological short exact sequence \
with locally free kernel of rank m (Stacks.Chow.shortExact_bundleTautological, \
Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological, including the rank-one end m = \
0 where the kernel has rank zero).  Injectivity of pi^* itself is derived from the 02TX bundle \
map, not assumed.  WEAKENED IN ONE WORD: the source says the morphism is projective and only \
properness is delivered, because IsProjectiveMorphism of the identity of X needs the \
identification of P^0_X with X, which this repository lacks.  Clause (1) of the source quantifies \
over every f : Y -> X, and that full form is exists_splittingMorphism_basechange_uniform, which \
is about the single morphism this theorem delivers"]
theorem exists_splittingMorphism_unconditional (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I] (E : I → X.Modules)
    (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i) :=
  exists_splittingMorphism C (bundleStep C) sX I E r hE

/-- The splitting principle over `Y` for the pulled-back modules. For every `f : Y ⟶ X` with `Y`
locally of finite type over the base there is a flat proper morphism `π_Y : P_Y ⟶ Y` of relative
dimension `d = ∑_i binom(r_i, 2)` along which flat pullback on Chow groups is injective in every
degree, and such that each `π_Y^* f^* ℰ_i` has a filtration of length `r_i` with invertible
successive quotients. -/
theorem exists_splittingMorphism_basechange_unconditional (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i))
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) :
    ∃ T : SplittingMorphism C sY (∑ i, (r i).choose 2),
      ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj ((Scheme.Modules.pullback f).obj (E i))) (r i) :=
  exists_splittingMorphism_basechange C (bundleStep C) sX I E r hE sY f

/-! ### Injectivity after every base change of one morphism -/

/-- The splitting principle with injectivity after every base change. Let `X` be locally of
finite type over the base `S` of `C` and let `ℰ_i`, `i ∈ I` finite, be finite locally free
`𝒪_X`-modules of constant ranks `r_i`. There is a single flat proper morphism `π : P ⟶ X` of
relative dimension `d = ∑_i binom(r_i, 2)` such that

1. for any `f : Y ⟶ X` with `Y` locally of finite type over the base, the flat pullback
   `π_Y^* : A_k(Y) ⟶ A_{k+d}(Y ×_X P)` along the base change of `π` is injective in every
   degree, and
2. each `π^*ℰ_i` has a filtration of length `r_i` whose successive quotients are invertible
   `𝒪_P`-modules. -/
@[stacks 02UL "clauses (1) and (2) for a finite collection of finite locally free modules of \
constant ranks r_i, with relative dimension d = sum of binom(r_i, 2), and with clause (1) in the \
form the source states it: ONE morphism pi : P -> X, and for EVERY f : Y -> X injectivity in \
every degree of the flat pullback along the base change of that pi, which is \
Stacks.Chow.BaseChangeInjective quantified over every cartesian square over pi and f.  The only \
hypotheses are the source's: each module finite locally free of constant rank r_i.  Clause (1) \
is proved through the iteration -- base case the identity of X, whose base change is an \
isomorphism; inductive step the splitting of the base change of a composite by \
CategoryTheory.IsPullback.of_bot together with Stacks 02RD for a composite pullback, the \
base-changed layer being the projective bundle of the pulled-back module by \
Stacks.ProjectiveBundle.isPullback_baseChangeHom and its pullback injective by the injectivity \
half of Stacks 02TX.  The single word of the tag delivered more weakly is projective, delivered \
as proper: IsProjectiveMorphism of the identity of X needs the identification of P^0_X with X, \
which this repository lacks"]
theorem exists_splittingMorphism_basechange_uniform (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I] (E : I → X.Modules)
    (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      BaseChangeInjective C sX T.π (∑ i, (r i).choose 2) ∧
        ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj (E i)) (r i) :=
  exists_splittingMorphism_baseChangeInjective_aux C (bundleStep C)
    (fun sY _ F m hF ↦ baseChangeInjective_bundleStep C sY F m hF) _ sX I E r hE rfl

end Stacks.Chow

end
