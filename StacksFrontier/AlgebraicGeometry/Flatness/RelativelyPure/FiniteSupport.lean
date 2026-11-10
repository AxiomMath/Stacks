module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.IsolatedPointsDecomposition
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.QuasiFinitePointedBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPointsLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic

/-!
# Purity and finiteness of the scheme-theoretic support

Let `f : X ⟶ S` be a separated morphism of finite type and let `ℱ` be a finite type
quasi-coherent `𝒪_X`-module whose support meets every fibre of `f` in a finite set. Then `ℱ` is
pure relative to `S` exactly when its scheme-theoretic support is finite over `S`, and exactly
when `ℱ` is universally pure relative to `S`. Specializing to the structure sheaf: a separated
quasi-finite scheme over `S` is pure relative to `S` exactly when it is finite over `S`.

Finiteness of the scheme-theoretic support gives universal purity through the properness
criterion: a finite morphism is proper, so the support of `ℱ` is a closed subset proper over
`S`, and a module with proper support is universally pure.

The converse is Zariski's main theorem. The scheme-theoretic support `Z ⊂ X` is separated and
quasi-finite over `S`, and `ℱ` is the direct image of a finite type quasi-coherent module `𝒢` on
`Z` whose support is all of `Z`, so it suffices to show that a separated quasi-finite `g : Z ⟶ S`
carrying such a `𝒢` pure relative to `S` is finite. Being finite is being proper and
quasi-finite, and properness is local on `S`, so `S` may be taken affine; then `g` factors as a
quasi-compact open immersion `j : Z ⟶ T` followed by a finite `π : T ⟶ S`. A specialization
`j z ⤳ t` is lifted into `Z` as follows: after an elementary étale base change `U ⟶ S` the point
of `T` above `t` becomes isolated in a finite open-and-closed piece `V` of `T × _S U` having a
unique point `v` above the distinguished point of `U`, and `V ⟶ T` is étale, hence flat, hence
lifts the specialization to a point `v' ⤳ v` above `j z`. Since `𝒢` has full support and the
fibres of `g` are discrete, `v'` lies in the relative assassin of the pullback of `𝒢`, so purity
forbids the closure of `v'` from missing the fibre of `U` over its distinguished point; inside
`V` that closure can only reach `v`, which therefore lies over `Z`, so `t` lies in the image of
`j`. Thus specializations lift along `j`, so `j` is closed and hence a closed immersion, and
`g = j ≫ π` is finite.

## Main results

* `AlgebraicGeometry.isPureRelative_iff_isFinite_schemeTheoreticSupport`: conditions (1) and (2)
  of the source.
* `AlgebraicGeometry.isUniversallyPureRelative_iff_isFinite_schemeTheoreticSupport`: conditions
  (2) and (3) of the source.
* `AlgebraicGeometry.isSchemePureRelative_iff_isFinite`: the final assertion of the source, for
  a separated quasi-finite morphism.

## Implementation notes

Finiteness of `Supp(ℱ_s)` is phrased as finiteness of the support of the pullback of `ℱ` to the
scheme-theoretic fibre over `s`, and finiteness of the scheme-theoretic support over `S` as
`AlgebraicGeometry.IsFinite` for the composite of the closed immersion of
`AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport` with `f`. Finite type of a morphism is
`AlgebraicGeometry.LocallyOfFiniteType` together with `AlgebraicGeometry.QuasiCompact`, and
quasi-finiteness adds `AlgebraicGeometry.LocallyQuasiFinite`, as in [Stacks, Tag 02NG].

The three-way equivalence of the source is delivered as the two equivalences of conditions (1)
and (3) with condition (2). The implication (3) → (1), which the source calls trivial, amounts
in this presentation to discarding the two unused hypotheses of
`AlgebraicGeometry.IsPureAlong`.

Finiteness is reduced to an affine base through
`AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite` rather than directly, since
local quasi-finiteness is already available on the morphism in question and properness is local
on the target.

## References

* [Stacks Project, Tag 05K4](https://stacks.math.columbia.edu/tag/05K4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private theorem pullback_isQuasicoherent {X Y : Scheme.{u}} (p : Y ⟶ X) (G : X.Modules)
    [hG : G.IsQuasicoherent] : ((Scheme.Modules.pullback p).obj G).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ p.toLRSHom.toShHom G hG

/-- Purity along a fibre only depends on the isomorphism class of the module. -/
private theorem isPureAlong_iff_of_moduleIso {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] (F G : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent] (e : F ≅ G) (s : S) :
    IsPureAlong ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u}) ↔
      IsPureAlong ({ S := S, X := X, f := f, F := G, s := s } : PrePureSituation.{u}) := by
  have key : ∀ (A B : X.Modules) (_ : A.IsFiniteType) (_ : A.IsQuasicoherent)
      (_ : B.IsFiniteType) (_ : B.IsQuasicoherent), (A ≅ B) →
      IsPureAlong ({ S := S, X := X, f := f, F := A, s := s } : PrePureSituation.{u}) →
        IsPureAlong ({ S := S, X := X, f := f, F := B, s := s } : PrePureSituation.{u}) := by
    intro A B _ _ _ _ i h D hEt hElem hImp
    refine h { D with } hEt hElem ⟨?_, hImp.2⟩
    change D.xi ∈ Stacks.Divisors.relativeAssassin D.toT
      ((Scheme.Modules.pullback D.toX).obj A)
    rw [relativeAssassin_eq_of_moduleIso D.toT ((Scheme.Modules.pullback D.toX).mapIso i)]
    exact hImp.1
  exact ⟨key F G inferInstance inferInstance inferInstance inferInstance e,
    key G F inferInstance inferInstance inferInstance inferInstance e.symm⟩

/-- A closed subscheme whose image is the support of a finite type module is quasi-finite over
the base as soon as the support of the module on every fibre is finite: the fibre of the closed
subscheme injects into the support of the restriction of the module to the corresponding
fibre. -/
private theorem locallyQuasiFinite_of_range_eq_supp {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] (hrange : Set.range i.base = SheafOfModules.supp F)
    (hfinite : ∀ s : S,
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)).Finite) :
    LocallyQuasiFinite (i ≫ f) := by
  refine (locallyQuasiFinite_iff_finite_preimage_singleton (f := i ≫ f)).2 fun s ↦ ?_
  have hmem (z : (i ≫ f).fiber s) : i.base ((i ≫ f).fiberι s z) ∈ f ⁻¹' {s} := by
    have h : (i ≫ f).fiberι s z ∈ (i ≫ f) ⁻¹' {s} := by
      rw [← (i ≫ f).range_fiberι s]
      exact ⟨z, rfl⟩
    simpa using h
  let φ : (i ≫ f).fiber s → f.fiber s := fun z ↦
    (f.fiberHomeo s).symm ⟨i.base ((i ≫ f).fiberι s z), hmem z⟩
  have hφ (z : (i ≫ f).fiber s) : f.fiberι s (φ z) = i.base ((i ≫ f).fiberι s z) :=
    f.fiberι_fiberHomeo_symm s _
  have hφinj : Function.Injective φ := fun z z' h ↦
    ((i ≫ f).fiberι s).injective (i.isClosedEmbedding.injective
      (((hφ z).symm.trans (congrArg (f.fiberι s) h)).trans (hφ z')))
  have hφmem (z : (i ≫ f).fiber s) :
      φ z ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
    rw [Stacks.Modules.supp_pullback]
    refine Set.mem_preimage.mpr ?_
    rw [hφ z, ← hrange]
    exact ⟨(i ≫ f).fiberι s z, rfl⟩
  have hdom : (Set.univ : Set ((i ≫ f).fiber s)).Finite := by
    refine (Set.finite_image_iff hφinj.injOn).1 ((hfinite s).subset ?_)
    rintro y ⟨z, -, rfl⟩
    exact hφmem z
  simpa only [Set.image_univ, (i ≫ f).range_fiberι] using hdom.image ((i ≫ f).fiberι s)

/-- Along a locally quasi-finite morphism, a finite type quasi-coherent module whose support is
everything has every point of the source in its relative assassin: the fibres are discrete, so
every point of a fibre is minimal in the support of the restriction of the module to that fibre,
and a minimal point of the support of a quasi-coherent module on a locally Noetherian scheme is
an associated point. -/
private theorem relativeAssassin_eq_univ_of_supp_eq_univ {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (hsupp : SheafOfModules.supp F = Set.univ) :
    Stacks.Divisors.relativeAssassin f F = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hnoeth : IsLocallyNoetherian (f.fiber (f.base x)) :=
    have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (f.base x)) :=
      inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f
        (S.fromSpecResidueField (f.base x))))
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f.base x))
  have hqc : ((Scheme.Modules.pullback (f.fiberι (f.base x))).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent (f.fiberι (f.base x)) F
  have hmem : f.asFiber x ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι (f.base x))).obj F) := by
    refine mem_associatedPoints_of_mem_supp_of_specialization (f.fiber (f.base x)) _
      (f.asFiber x) ?_ fun y _ hspec ↦ ?_
    · rw [Stacks.Modules.supp_pullback, hsupp]
      trivial
    · exact (Set.mem_singleton_iff.mp (hspec.mem_closed ⟨isOpen_discrete _⟩ rfl)).symm
  simpa using (Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin f F
    (f.base x) (f.asFiber x)).mp hmem

/-- The closure of a point `xi` of the pullback, lying over the closed piece `k` of an étale
neighbourhood, misses the fibre over `y` when the only point of that piece over `y` maps to a
point `t` outside the range of `j`. -/
private theorem closure_inter_range_fiberι_eq_empty {X T W V P : Scheme.{u}} (j : X ⟶ T)
    (q : W ⟶ T) (p : W ⟶ V) (k : P ⟶ W) [hk : IsClosedImmersion k] {t : T} {y : V}
    {v v' : P} (ht : t ∉ Set.range j.base) (hkv : (k ≫ q) v = t)
    (hsingle : {w : P | (k ≫ p) w = y} = {v}) {xi : (Limits.pullback j q : Scheme.{u})}
    (hxi : (Limits.pullback.snd j q).base xi = k.base v') :
    closure {xi} ∩ Set.range ((Limits.pullback.snd j q ≫ p).fiberι y) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
  obtain ⟨hzclosure, hzrange⟩ := hz
  have hzbase : (Limits.pullback.snd j q ≫ p).base z = y := by
    have h : z ∈ (Limits.pullback.snd j q ≫ p) ⁻¹' {y} := by
      simpa only [(Limits.pullback.snd j q ≫ p).range_fiberι] using hzrange
    exact h
  have hmap : k.base v' ⤳ (Limits.pullback.snd j q).base z := by
    simpa only [hxi] using (specializes_iff_mem_closure.mpr hzclosure).map
      (Limits.pullback.snd j q).continuous
  obtain ⟨w, hwb⟩ := hmap.mem_closed hk.isClosedEmbedding.isClosed_range ⟨v', rfl⟩
  have hwmem : w ∈ {w : P | (k ≫ p) w = y} := by
    change p.base (k.base w) = y
    rw [hwb]
    exact hzbase
  have hwEq : w = v := (Set.eq_singleton_iff_unique_mem.mp hsingle).2 w hwmem
  have hji : j.base ((Limits.pullback.fst j q).base z) =
      q.base ((Limits.pullback.snd j q).base z) := by
    simpa using congrArg (fun m : Limits.pullback j q ⟶ T ↦ m.base z)
      (Limits.pullback.condition (f := j) (g := q))
  refine ht ⟨_, hji.trans ?_⟩
  rw [← hwb, hwEq]
  exact hkv

/-- In an impurity diagram for a locally quasi-finite morphism and a module with full support,
the point `xi` lies in the relative assassin of the pulled-back module. -/
private theorem xi_mem_relativeAssassin_of_supp_eq_univ {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (hsupp : SheafOfModules.supp F = Set.univ) (s : S)
    (D : ImpurityDiagram ({ S := S, X := X, f := f, F := F, s := s } : PrePureSituation.{u})) :
    D.xi ∈ Stacks.Divisors.relativeAssassin D.toT (D.pulledBack _) := by
  have _ : (D.pulledBack _).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType D.toX.toLRSHom.toShHom F
  have _ : (D.pulledBack _).IsQuasicoherent := pullback_isQuasicoherent D.toX F
  have _ : LocallyOfFiniteType D.toT :=
    MorphismProperty.of_isPullback D.isPullback ‹LocallyOfFiniteType f›
  have _ : LocallyQuasiFinite D.toT :=
    MorphismProperty.of_isPullback D.isPullback ‹LocallyQuasiFinite f›
  have hfull : SheafOfModules.supp (D.pulledBack _) = Set.univ := by
    rw [Stacks.Modules.supp_pullback, hsupp, Set.preimage_univ]
  rw [relativeAssassin_eq_univ_of_supp_eq_univ D.toT _ hfull]
  trivial

/-- If `f = j ≫ π` with `j` an open immersion and `π` finite, and the module `F` with full support
is pure relative to `f`, then `j` is specializing: a specialization `j x ⤳ t` with `t` outside
the range of `j` is lifted along an étale neighbourhood to an impurity of `F`. -/
private theorem specializingMap_of_isPureRelative_of_factorization {X T S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hsupp : SheafOfModules.supp F = Set.univ) (hPure : IsPureRelative f F) (j : X ⟶ T)
    (π : T ⟶ S) [IsOpenImmersion j] [IsFinite π] (hfac : f = j ≫ π) :
    SpecializingMap j.base := by
  intro x t hxt
  by_contra ht
  have hnot : t ∉ Set.range j.base := by
    rintro ⟨z, rfl⟩
    exact ht ⟨z, j.isOpenEmbedding.isInducing.specializes_iff.mp hxt, rfl⟩
  obtain ⟨U, hU, P, k, hkOpen, hkClosed, hkIso, v, hkFinite, hkv, hksingle, hkres, hknone⟩ :=
    Stacks.Flatness.exists_etaleNeighborhood_decomposition π (π.base t) 1 (fun _ ↦ t)
      (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _) fun _ ↦ isOpen_discrete _
  have hxt' : j.base x ⤳ (k (some 0) ≫ Limits.pullback.fst π U.toBase) (v 0) := by
    rwa [hkv 0]
  obtain ⟨v', hv'v, hv'base⟩ :=
    Flat.generalizingMap (k (some 0) ≫ Limits.pullback.fst π U.toBase) hxt'
  obtain ⟨xi, hxiX, hxiTU⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := j)
      (g := Limits.pullback.fst π U.toBase) x ((k (some 0)).base v') hv'base.symm
  have hsquare : IsPullback (Limits.pullback.fst j (Limits.pullback.fst π U.toBase))
      (Limits.pullback.snd j (Limits.pullback.fst π U.toBase) ≫
        Limits.pullback.snd π U.toBase) f U.toBase := by
    rw [hfac]
    exact (IsPullback.of_hasPullback _ _).paste_vert (IsPullback.of_hasPullback _ _)
  have hvpoint : (k (some 0) ≫ Limits.pullback.snd π U.toBase) (v 0) = U.point :=
    (Set.eq_singleton_iff_unique_mem.mp (hksingle 0)).1
  let D : ImpurityDiagram
      ({ S := S, X := X, f := f, F := F, s := π.base t } : PrePureSituation.{u}) :=
    { T := U.scheme
      g := U.toBase
      t' := (k (some 0) ≫ Limits.pullback.snd π U.toBase) v'
      t := U.point
      specializes := hvpoint ▸ hv'v.map (k (some 0) ≫ Limits.pullback.snd π U.toBase).continuous
      mapsToChosenPoint := U.map_point
      X_T := Limits.pullback j (Limits.pullback.fst π U.toBase)
      toX := Limits.pullback.fst j (Limits.pullback.fst π U.toBase)
      toT := Limits.pullback.snd j (Limits.pullback.fst π U.toBase) ≫
        Limits.pullback.snd π U.toBase
      isPullback := hsquare
      xi := xi
      xi_liesOver :=
        congrArg (Limits.pullback.snd π U.toBase).base hxiTU }
  exact hPure (π.base t) D U.etale_toBase hU
    ⟨xi_mem_relativeAssassin_of_supp_eq_univ f F hsupp _ D,
      closure_inter_range_fiberι_eq_empty j (Limits.pullback.fst π U.toBase)
        (Limits.pullback.snd π U.toBase) (k (some 0)) hnot (hkv 0) (hksingle 0) hxiTU⟩

/-- A separated quasi-finite morphism onto a quasi-compact quasi-separated base carrying a finite
type quasi-coherent module with full support which is pure relative to that base is finite.

Zariski's main theorem factors the morphism as a quasi-compact open immersion `j : X ⟶ T`
followed by a finite `π : T ⟶ S`. If a specialization `j x ⤳ t` had `t ∉ j(X)`, an elementary
étale neighbourhood of `π t` would isolate the point of the base change above `t` in a finite
open-and-closed piece, flatness of that piece over `T` would lift the specialization to a point
`v'` of it lying over `j x`, and the resulting diagram would be an impurity: `v'` lies in the
relative assassin because the module has full support, and the closure of `v'` misses the fibre
over the distinguished point because inside the piece that closure can only reach the unique
point above it, which lies over `t`. Hence specializations lift along `j`, so `j` is a closed
immersion, and a closed immersion followed by a finite morphism is finite. -/
private theorem isFinite_of_isPureRelative_of_supp_eq_univ_of_compactSpace {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [LocallyQuasiFinite f]
    [CompactSpace S] [QuasiSeparatedSpace S] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (hsupp : SheafOfModules.supp F = Set.univ)
    (hPure : IsPureRelative f F) : IsFinite f := by
  obtain ⟨T, j, π, _, _, _, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization f
  have hjclosed := (isClosedMap_iff_specializingMap j).2
    (specializingMap_of_isPureRelative_of_factorization f F hsupp hPure j π hfac)
  have _ : IsClosedImmersion j := IsClosedImmersion.of_isPreimmersion j hjclosed.isClosed_range
  rw [hfac]
  infer_instance

/-- A separated quasi-finite morphism carrying a finite type quasi-coherent module with full
support which is pure relative to the base is finite: being finite is being proper and
quasi-finite, properness is local on the target, and the morphism is finite over each affine
open of the target, where purity is inherited by the base change. -/
private theorem isFinite_of_isPureRelative_of_supp_eq_univ {X S : Scheme.{u}} (g : X ⟶ S)
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g] [LocallyQuasiFinite g]
    (G : X.Modules) [G.IsFiniteType] [G.IsQuasicoherent]
    (hsupp : SheafOfModules.supp G = Set.univ) (hPure : IsPureRelative g G) : IsFinite g := by
  rw [IsFinite.iff_isProper_and_locallyQuasiFinite]
  refine ⟨?_, inferInstance⟩
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsProper) S.affineCover]
  intro n
  have hpb : IsPullback (Limits.pullback.fst g (S.affineCover.f n))
      (Limits.pullback.snd g (S.affineCover.f n)) g (S.affineCover.f n) :=
    IsPullback.of_hasPullback _ _
  have _ : ((Scheme.Modules.pullback (Limits.pullback.fst g (S.affineCover.f n))).obj
      G).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType
      (Limits.pullback.fst g (S.affineCover.f n)).toLRSHom.toShHom G
  have _ : ((Scheme.Modules.pullback (Limits.pullback.fst g (S.affineCover.f n))).obj
      G).IsQuasicoherent :=
    pullback_isQuasicoherent (Limits.pullback.fst g (S.affineCover.f n)) G
  have hGUsupp : SheafOfModules.supp ((Scheme.Modules.pullback
      (Limits.pullback.fst g (S.affineCover.f n))).obj G) = Set.univ := by
    rw [Stacks.Modules.supp_pullback, hsupp, Set.preimage_univ]
  have hPureGU : IsPureRelative (Limits.pullback.snd g (S.affineCover.f n))
      ((Scheme.Modules.pullback (Limits.pullback.fst g (S.affineCover.f n))).obj G) := by
    intro y
    let Pb : PrePureSituation.{u} :=
      { S := S, X := X, f := g, F := G, s := (S.affineCover.f n).base y }
    let Qb : PrePureSituation.{u} :=
      { S := S.affineCover.X n
        X := Limits.pullback g (S.affineCover.f n)
        f := Limits.pullback.snd g (S.affineCover.f n)
        F := (Scheme.Modules.pullback (Limits.pullback.fst g (S.affineCover.f n))).obj G
        s := y }
    exact isPureAlong_of_quasiFiniteAt_of_isPureAlong (P := Pb) (Q := Qb)
      (S.affineCover.f n) rfl (Limits.pullback.fst g (S.affineCover.f n)) hpb (Iso.refl _)
      ((forall_quasiFiniteAt_iff (S.affineCover.f n)).2 ⟨inferInstance, inferInstance⟩ y)
      (hPure ((S.affineCover.f n).base y))
  have _ : IsFinite (S.affineCover.pullbackHom g n) :=
    isFinite_of_isPureRelative_of_supp_eq_univ_of_compactSpace
      (Limits.pullback.snd g (S.affineCover.f n)) _ hGUsupp hPureGU
  infer_instance

/-- A finite type quasi-coherent module whose scheme-theoretic support is finite over the base is
universally pure relative to that base: a finite morphism is proper, so the support of the module
is a closed subset proper over the base. -/
theorem isUniversallyPureRelative_of_isFinite_schemeTheoreticSupport {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hfin : IsFinite ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f)) :
    IsUniversallyPureRelative f F :=
  isUniversallyPureRelative_of_support_isProperOver f F
    ((Scheme.Modules.isProperOver_supp_iff_isProper_schemeTheoreticSupport f F).2 inferInstance)

/-- **Stacks Project, Tag 05K4, conditions (1) and (2).** Let `f : X ⟶ S` be separated of finite
type and let `ℱ` be a finite type quasi-coherent `𝒪_X`-module with finite support on every fibre
of `f`. Then `ℱ` is pure relative to `S` if and only if its scheme-theoretic support is finite
over `S`. -/
@[stacks 05K4 "conditions (1) and (2)"]
theorem isPureRelative_iff_isFinite_schemeTheoreticSupport {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hfinite : ∀ s : S,
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)).Finite) :
    IsPureRelative f F ↔
      IsFinite ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f) := by
  refine ⟨fun hPure ↦ ?_, fun hfin s D _ _ ↦
    isUniversallyPureRelative_of_isFinite_schemeTheoreticSupport f F hfin s D⟩
  -- descend `ℱ` to its scheme-theoretic support and apply Zariski's main theorem there
  obtain ⟨G, _, -, ⟨e⟩⟩ := Scheme.Modules.exists_module_on_schemeTheoreticSupport F
  have _ : G.IsFiniteType := Scheme.Modules.module_on_schemeTheoreticSupport_isFiniteType F G e
  have hGsupp : SheafOfModules.supp G = Set.univ :=
    Scheme.Modules.module_on_schemeTheoreticSupport_support F G e
  have hrange : Set.range (Scheme.Modules.schemeTheoreticSupport F).subschemeι.base =
      SheafOfModules.supp F :=
    (Scheme.Modules.schemeTheoreticSupport F).range_subschemeι.trans
      (Scheme.Modules.supp_eq_support_schemeTheoreticSupport F).symm
  have _ : LocallyQuasiFinite
      ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f) :=
    locallyQuasiFinite_of_range_eq_supp _ f F hrange hfinite
  have _ : ((Scheme.Modules.pushforward
      (Scheme.Modules.schemeTheoreticSupport F).subschemeι).obj G).IsFiniteType :=
    (isFiniteType_iff_pushforward_isFiniteType _ G).mp inferInstance
  -- purity of `ℱ` on `X` becomes purity of `𝒢` on the scheme-theoretic support
  have hPureG : IsPureRelative
      ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f) G := fun s ↦
    (isPureAlong_iff_pushforward _ f G s).2
      ((isPureAlong_iff_of_moduleIso f ((Scheme.Modules.pushforward
        (Scheme.Modules.schemeTheoreticSupport F).subschemeι).obj G) F e s).2 (hPure s))
  exact isFinite_of_isPureRelative_of_supp_eq_univ _ G hGsupp hPureG

/-- **Stacks Project, Tag 05K4, conditions (2) and (3).** Let `f : X ⟶ S` be separated of finite
type and let `ℱ` be a finite type quasi-coherent `𝒪_X`-module with finite support on every fibre
of `f`. Then `ℱ` is universally pure relative to `S` if and only if its scheme-theoretic support
is finite over `S`. -/
@[stacks 05K4 "conditions (2) and (3)"]
theorem isUniversallyPureRelative_iff_isFinite_schemeTheoreticSupport {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent]
    (hfinite : ∀ s : S,
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)).Finite) :
    IsUniversallyPureRelative f F ↔
      IsFinite ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f) :=
  ⟨fun hPure ↦ (isPureRelative_iff_isFinite_schemeTheoreticSupport f F hfinite).1
      fun s D _ _ ↦ hPure s D,
    isUniversallyPureRelative_of_isFinite_schemeTheoreticSupport f F⟩

/-- **Stacks Project, Tag 05K4, in particular.** A separated quasi-finite scheme over `S` is pure
relative to `S` if and only if its structure morphism is finite. -/
@[stacks 05K4 "in particular: quasi-finite separated morphisms"]
theorem isSchemePureRelative_iff_isFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [IsSeparated f] :
    IsSchemePureRelative f ↔ IsFinite f := by
  have hFT : (SheafOfModules.unit.{u} X.ringCatSheaf).IsFiniteType :=
    structureSheaf_isFiniteType X
  have hsupp : SheafOfModules.supp (SheafOfModules.unit.{u} X.ringCatSheaf) = Set.univ :=
    Set.eq_univ_of_forall (mem_supp_structureSheaf X)
  refine ⟨fun hPure ↦ isFinite_of_isPureRelative_of_supp_eq_univ f _ hsupp hPure,
    fun _ s D _ _ ↦ isSchemeUniversallyPureRelative_of_isProper f s D⟩

end AlgebraicGeometry

end
