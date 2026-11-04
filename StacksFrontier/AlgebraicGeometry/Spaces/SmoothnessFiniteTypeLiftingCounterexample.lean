module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothnessOverNoetherianBaseLifting
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.Spaces.NonSeparatedGroupSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0APP with test morphisms of finite type is false

Condition (2) of Stacks 0APP asks for lifts along small extensions `B' ⟶ B` of Artinian local
rings of every solid square whose test morphism `β : Spec B' ⟶ Y` is *of finite type*. Over a
target which is not quasi-separated that condition can be vacuous, and then it does not imply
smoothness. This file proves that, for the point `Spec ℚ ⟶ 𝔸¹_ℚ/ℤ` given by the zero section of
the affine line, in the quotient of the line by the translation action of the integers.

## Main results

* `AlgebraicGeometry.AffineLineTranslation.not_isQuasiCompact_of_comp_eq_linePoint_zero`: a
  morphism to `𝔸¹_k/ℤ` from a one-point affine object, which agrees with the zero section on a
  nonempty object mapping to it, is not quasi-compact.
* `AlgebraicGeometry.AffineLineTranslation.not_smooth_zeroSection`: the zero section of `𝔸¹_k` is
  not smooth.
* `AlgebraicGeometry.Space.exists_not_isSmooth_liftsAgainstFiniteTypeSmallExtensions`: a
  morphism of algebraic spaces, locally of finite type over a locally Noetherian target, which
  satisfies the literal condition (2) of Stacks 0APP and is not smooth.
* `AlgebraicGeometry.Space.not_forall_isSmooth_iff_liftsAgainstFiniteTypeSmallExtensions`:
  **Stacks 0APP as stated is false**. The corrected statement is
  `AlgebraicGeometry.Space.isSmooth_iff_forall_exists_lift_isSmallExtension`.

## Implementation notes

The quasi-compactness of a test morphism `β : Spec R' ⟶ 𝔸¹_k/ℤ` is tested against the chart
`𝔸¹_k ⟶ 𝔸¹_k/ℤ`. The base change of `β` along the chart has a section over `Spec R` whose
coordinate is `n` for every integer `n`, since translating by `n` does not change the class in
the quotient, by
`AlgebraicGeometry.AffineLineTranslation.yoneda_map_linePoint_add_intCast_comp_lineChart`.
A surjective étale chart `W` of the base change by a quasi-compact scheme is étale over the
one-point scheme `Spec R'`, hence finite by Mathlib's
`AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton`, but each of those sections lifts to a
point of `W`, and the images of these points in `𝔸¹_k` are pairwise distinct because their
coordinates are distinct integers in a field of characteristic zero
(`AlgebraicGeometry.Scheme.intCast_eq_of_appTop_eq_of_apply_eq`).

The zero section is not smooth because a smooth morphism is flat, while the zero section pulls
the coordinate, a nonzerodivisor of the ring of functions on the line, back to zero.

## References

* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0APP](https://stacks.math.columbia.edu/tag/0APP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AffineLineTranslation

open AffineLineInvolution Stacks.Examples.NonSeparatedGroupSpace

variable (k : Type u) [Field k] [CharZero k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
  [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- The morphism from an object `T` of the big fppf site over `Spec k` to the affine line whose
coordinate is a given global section of `T`. -/
noncomputable def linePoint (T : BigFppfOver B (Spec (.of k)) hS)
    (s : Γ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T, ⊤)) : T ⟶ lineObj k B hS :=
  (Over.post (X := B.obj hS) B.inclusion).preimage
    (((lineSectionsIso k B hS).inv.app (op T) s :
      (Over.post (X := B.obj hS) B.inclusion).obj T ⟶ AffineLineInvolution.affineLine k) :
      (Over.post (X := B.obj hS) B.inclusion).obj T ⟶
        (Over.post (X := B.obj hS) B.inclusion).obj (lineObj k B hS))

omit [CharZero k] [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The morphism `linePoint k B hS T s` pulls the coordinate of the affine line back to `s`. -/
theorem linePoint_appTop_coord (T : BigFppfOver B (Spec (.of k)) hS)
    (s : Γ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T, ⊤)) :
    ((BigFppfOver.toScheme B (Spec (.of k)) hS).map (linePoint k B hS T s)).appTop
      (AffineSpace.coord (Spec (.of k)) PUnit.unit) = s := by
  have hmap : (Over.post (X := B.obj hS) B.inclusion).map (linePoint k B hS T s) =
      (lineSectionsIso k B hS).inv.app (op T) s := Functor.map_preimage _ _
  change ((Over.post (X := B.obj hS) B.inclusion).map (linePoint k B hS T s)).left.appTop _ = s
  rw [hmap]
  exact congrArg (fun g => g s) ((lineSectionsIso k B hS).inv_hom_id_app (op T))

/-- The chart `𝔸¹_k ⟶ 𝔸¹_k/ℤ` sends a morphism `x : T ⟶ 𝔸¹_k` of the site to the class in the
quotient of the corresponding morphism of schemes over `Spec k`. -/
theorem lineChart_app (T : BigFppfOver B (Spec (.of k)) hS) (x : T ⟶ lineObj k B hS) :
    (lineChart k B hS).app (op T) x =
      (lineToTranslationQuotient k B hS).app (op T)
        ((Over.post (X := B.obj hS) B.inclusion).map x) := by
  have hn := NatTrans.naturality_apply (lineToTranslationQuotient k B hS) x.op
    (𝟙 ((Over.post (X := B.obj hS) B.inclusion).obj (lineObj k B hS)))
  refine hn.symm.trans ?_
  congr 1

/-- The morphisms to the affine line with coordinates `s + n` and `s`, for an integer `n`, have
the same image in `𝔸¹_k/ℤ`. -/
theorem yoneda_map_linePoint_add_intCast_comp_lineChart (T : BigFppfOver B (Spec (.of k)) hS)
    (s : Γ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T, ⊤)) (n : ℤ) :
    yoneda.map (linePoint k B hS T (s + n)) ≫ lineChart k B hS =
      yoneda.map (linePoint k B hS T s) ≫ lineChart k B hS := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map,
    lineChart_app, lineChart_app]
  have h1 : (Over.post (X := B.obj hS) B.inclusion).map (linePoint k B hS T (s + n)) =
      (lineSectionsIso k B hS).inv.app (op T)
        (s + (n : Γ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T, ⊤))) :=
    Functor.map_preimage _ _
  have h2 : (Over.post (X := B.obj hS) B.inclusion).map (linePoint k B hS T s) =
      (lineSectionsIso k B hS).inv.app (op T) s := Functor.map_preimage _ _
  rw [h1, h2]
  exact lineSectionsIso_inv_lineToTranslationQuotient_add_intCast k B hS (op T) s n

/-- Two morphisms of schemes pulling a global section back to two integers, and agreeing at a
point whose residue field has characteristic zero, pull it back to the same integer: the
evaluation of the section at the common image point is sent to both integers by injective
residue field maps. -/
theorem _root_.AlgebraicGeometry.Scheme.intCast_eq_of_appTop_eq_of_apply_eq {X A : Scheme.{u}}
    (g g' : X ⟶ A) (c : Γ(A, ⊤)) (n m : ℤ) (hg : g.appTop c = n) (hg' : g'.appTop c = m)
    (t : X) [CharZero (X.residueField t)] (h : g t = g' t) : n = m := by
  have e1 := Scheme.Γevaluation_naturality_apply g t c
  have e2 := Scheme.Γevaluation_naturality_apply g' t c
  rw [hg, map_intCast] at e1
  rw [hg', map_intCast] at e2
  have ha : A.Γevaluation (g t) c = n :=
    (g.residueFieldMap t).hom.injective (by rw [e1, map_intCast])
  have hb : A.Γevaluation (g' t) c = m :=
    (g'.residueFieldMap t).hom.injective (by rw [e2, map_intCast])
  have hc := Scheme.residueFieldCongr_Γevaluation_apply h c
  rw [ha, hb, map_intCast] at hc
  have hd := congrArg (g'.residueFieldMap t).hom hc
  rw [map_intCast, map_intCast] at hd
  exact_mod_cast hd

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The residue fields of a scheme of the site over `Spec k` have characteristic zero when `k`
has. -/
theorem charZero_residueField (T : BigFppfOver B (Spec (.of k)) hS)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hS).obj T) :
    CharZero (((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T).residueField t) :=
  charZero_of_injective_ringHom (((Scheme.ΓSpecIso (.of k)).inv ≫
    (B.inclusion.map T.hom).appTop ≫
      ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T).Γevaluation t).hom).injective

/-- A quasi-compact, locally quasi-finite scheme over a scheme with at most one point is
finite. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.finite_source_of_subsingleton {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyQuasiFinite f] [QuasiCompact f] [Subsingleton Y] : Finite X := by
  rcases isEmpty_or_nonempty X with _ | ⟨⟨x⟩⟩
  · infer_instance
  · rw [← Set.finite_univ_iff, show (Set.univ : Set X) = f.base ⁻¹' {f.base x} from
      (Set.eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _).symm]
    exact f.finite_preimage_singleton _

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The points of a scheme of the site over `Spec k` pulled back from a point along the morphisms
to the affine line with integer coordinates are pairwise distinct. -/
theorem injective_linePoint_intCast_apply (T : BigFppfOver B (Spec (.of k)) hS)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hS).obj T) :
    Function.Injective fun n : ℤ ↦
      ((BigFppfOver.toScheme B (Spec (.of k)) hS).map (linePoint k B hS T n)).base t := by
  intro n m hnm
  have := charZero_residueField k B hS T t
  exact Scheme.intCast_eq_of_appTop_eq_of_apply_eq _ _
    (AffineSpace.coord (Spec (.of k)) PUnit.unit) n m (linePoint_appTop_coord k B hS T _)
    (linePoint_appTop_coord k B hS T _) t hnm

/-- A morphism `β` to `𝔸¹_k/ℤ` from a one-point affine object `T'` of the site, which restricts
along a morphism from a one-point object `T` to the class of the zero section, is not
quasi-compact.

The base change of `β` along the chart `𝔸¹_k ⟶ 𝔸¹_k/ℤ` has, for every integer `n`, the section
over `T` whose coordinate is `n`, because translation by `n` does not change the class in the
quotient. A surjective étale chart of that base change by a quasi-compact scheme `W` is étale
over the one-point affine scheme `T'`, hence finite; but it has a point above each of those
sections, and the coordinates `n` of the images of these points in `𝔸¹_k` are pairwise
distinct. -/
theorem not_isQuasiCompact_of_comp_eq_linePoint_zero
    {T T' : BigFppfOver B (Spec (.of k)) hS} (i : T ⟶ T')
    (β : yoneda.obj T' ⟶ translationQuotient k B hS (contains_affineLine k B hS))
    (hβ : yoneda.map (linePoint k B hS T 0) ≫ lineChart k B hS = yoneda.map i ≫ β)
    [Nonempty ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T)]
    [Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T')]
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj T')] :
    ¬ Space.IsQuasiCompact B (Spec (.of k)) hS β := by
  intro hqc
  let F := BigFppfOver.toScheme B (Spec (.of k)) hS
  let q := lineChart k B hS
  obtain ⟨W, w, hWc, hwS, hwE⟩ := hqc (yoneda.obj (lineObj k B hS))
    (isAlgebraicSpace_yoneda B _ hS _)
    (Space.isQuasiCompact_yoneda_of_compact B _ hS _
      (by change CompactSpace (AffineSpace PUnit.{u + 1} (Spec (.of k))); infer_instance)) q
  let u : W ⟶ lineObj k B hS := Yoneda.fullyFaithful.preimage (w ≫ pullback.fst q β)
  let v : W ⟶ T' := Yoneda.fullyFaithful.preimage (w ≫ pullback.snd q β)
  have hu : yoneda.map u = w ≫ pullback.fst q β := Yoneda.fullyFaithful.map_preimage _
  have hv : yoneda.map v = w ≫ pullback.snd q β := Yoneda.fullyFaithful.map_preimage _
  have hvEt : Etale (F.map v) := by
    have hw' := hwE W (𝟙 _) (Space.presheaf_yoneda_map_id_etale B _ hS W)
    rw [Category.id_comp] at hw'
    have hsnd := (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F)
      (F := yoneda)).of_isPullback (IsPullback.of_hasPullback q β) (etale_lineChart k B hS)
    have hcomp := (MorphismProperty.relative_isStableUnderComposition
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F)
      (F := yoneda)).comp_mem _ _ hw' hsnd
    rw [← hv] at hcomp
    exact (Space.presheaf_yoneda_map_iff B _ hS inferInstance v).mp hcomp
  have hWfin : Finite (F.obj W) := by
    obtain ⟨-, hlqf⟩ := locallyQuasiFinite_of_etale (F.map v)
    have : QuasiCompact (F.map v) := (quasiCompact_iff_compactSpace (F.map v)).mpr hWc
    exact (F.map v).finite_source_of_subsingleton
  obtain ⟨t⟩ := ‹Nonempty (F.obj T)›
  have hpt : ∀ n : ℤ, ∃ y : F.obj W,
      (F.map u).base y = (F.map (linePoint k B hS T (0 + n))).base t := by
    intro n
    let σ : yoneda.obj T ⟶ pullback q β :=
      pullback.lift (yoneda.map (linePoint k B hS T (0 + n))) (yoneda.map i)
        (by rw [yoneda_map_linePoint_add_intCast_comp_lineChart, hβ])
    obtain ⟨z, hz⟩ := (hwS.property_snd σ).surj t
    let r : hwS.rep.pullback σ ⟶ W := Yoneda.fullyFaithful.preimage (hwS.rep.fst σ)
    have hr : yoneda.map r = hwS.rep.fst σ := Yoneda.fullyFaithful.map_preimage _
    have hru : r ≫ u = hwS.rep.snd σ ≫ linePoint k B hS T (0 + n) := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_comp, hr, hu, ← Category.assoc, hwS.rep.w σ,
        Category.assoc, pullback.lift_fst]
    refine ⟨(F.map r).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← F.map_comp, hru, F.map_comp, Scheme.Hom.comp_apply]
    exact congrArg _ hz
  choose y hy using hpt
  refine not_injective_infinite_finite y fun n m hnm ↦
    injective_linePoint_intCast_apply k B hS T t ?_
  have h := congrArg (F.map u).base hnm
  rwa [hy n, hy m, zero_add, zero_add] at h

/-! ### The zero section of the affine line, as a point of `𝔸¹_k/ℤ` -/

omit [CharZero k] [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- Two morphisms to the affine line with the same coordinate agree. -/
theorem linePoint_ext {T : BigFppfOver B (Spec (.of k)) hS} {x y : T ⟶ lineObj k B hS}
    (h : ((BigFppfOver.toScheme B (Spec (.of k)) hS).map x).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      ((BigFppfOver.toScheme B (Spec (.of k)) hS).map y).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit)) : x = y := by
  apply (Over.post (X := B.obj hS) B.inclusion).map_injective
  have hx := congrArg (fun g => g ((Over.post (X := B.obj hS) B.inclusion).map x))
    ((lineSectionsIso k B hS).hom_inv_id_app (op T))
  have hy := congrArg (fun g => g ((Over.post (X := B.obj hS) B.inclusion).map y))
    ((lineSectionsIso k B hS).hom_inv_id_app (op T))
  refine hx.symm.trans (Eq.trans ?_ hy)
  exact congrArg (fun s => (lineSectionsIso k B hS).inv.app (op T) s) h

/-- The base `Spec k`, as an object of the big fppf site over it. -/
noncomputable abbrev baseObj : BigFppfOver B (Spec (.of k)) hS := Over.mk (𝟙 (B.obj hS))

/-- The zero section of the affine line over `k`. -/
noncomputable abbrev zeroSection : baseObj k B hS ⟶ lineObj k B hS := linePoint k B hS _ 0

omit [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] in
/-- The zero section of the affine line over a field is not smooth: it pulls the coordinate,
a nonzerodivisor of the ring of functions on the line, back to zero, so the field is not flat
over that ring. -/
theorem not_smooth_zeroSection :
    ¬ Smooth ((BigFppfOver.toScheme B (Spec (.of k)) hS).map (zeroSection k B hS)) := by
  intro hsm
  let z : Spec (.of k) ⟶ AffineSpace PUnit.{u + 1} (Spec (.of k)) :=
    (BigFppfOver.toScheme B (Spec (.of k)) hS).map (zeroSection k B hS)
  have : Smooth z := hsm
  let A := Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤)
  let c : A := AffineSpace.coord (Spec (.of k)) PUnit.unit
  have hflat : RingHom.Flat z.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Flat) (f := z)).mp inferInstance
  let := z.appTop.hom.toAlgebra
  have : Module.Flat A Γ(Spec (.of k), ⊤) := hflat
  let e := AffineSpace.isoOfIsAffine PUnit.{u + 1} (Spec (.of k))
  let ψ : A →+* MvPolynomial PUnit.{u + 1} Γ(Spec (.of k), ⊤) :=
    (e.inv.appTop ≫ (Scheme.ΓSpecIso _).hom).hom
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have hl : ∀ x, e.hom.appTop ((Scheme.ΓSpecIso _).inv (ψ x)) = x := by
      intro x
      change (e.hom.appTop) ((Scheme.ΓSpecIso _).inv ((Scheme.ΓSpecIso _).hom
        (e.inv.appTop x))) = x
      rw [Iso.hom_inv_id_apply]
      change (e.inv.appTop ≫ e.hom.appTop) x = x
      rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
      rfl
    rw [← hl a, ← hl b, hab]
  have hψc : ψ c = MvPolynomial.X PUnit.unit := by
    change (Scheme.ΓSpecIso _).hom (e.inv.appTop (AffineSpace.coord _ PUnit.unit)) = _
    rw [AffineSpace.isoOfIsAffine_inv_appTop_coord]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso _) _
  have hc : _root_.IsRegular c := by
    have hX : _root_.IsRegular (ψ c) := hψc ▸ MvPolynomial.isRegular_X
    constructor <;> intro a b hab <;> apply hψinj
    · exact hX.1 (by simpa only [map_mul] using congrArg ψ hab)
    · exact hX.2 (by simpa only [map_mul] using congrArg ψ hab)
  have hreg := Module.Flat.isSMulRegular_of_isRegular (M := Γ(Spec (.of k), ⊤)) hc
  have hz : z.appTop c = 0 := linePoint_appTop_coord k B hS (baseObj k B hS) 0
  have h10 : (1 : Γ(Spec (.of k), ⊤)) = 0 :=
    hreg (by
      change c • (1 : Γ(Spec (.of k), ⊤)) = c • 0
      rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_one]
      exact hz)
  have := congrArg (Scheme.ΓSpecIso (.of k)).hom.hom h10
  simp only [map_one, map_zero] at this
  exact one_ne_zero this

/-- The zero section of the affine line, followed by the projection, as a point of
`𝔸¹_k/ℤ` over `Spec k`. -/
noncomputable abbrev zeroQuotientPoint :
    yoneda.obj (baseObj k B hS) ⟶ translationQuotient k B hS (contains_affineLine k B hS) :=
  yoneda.map (zeroSection k B hS) ≫ lineChart k B hS

/-- The point `Spec k ⟶ 𝔸¹_k/ℤ` given by the zero section satisfies condition (2) of Stacks 0APP
read literally, for want of any test square: the test morphism `Spec R' ⟶ 𝔸¹_k/ℤ` of a square
restricts to the class of the zero section on `Spec R`, so it is not quasi-compact by
`AlgebraicGeometry.AffineLineTranslation.not_isQuasiCompact_of_comp_eq_linePoint_zero`. -/
theorem liftsAgainstFiniteTypeSmallExtensions_zeroQuotientPoint :
    Space.LiftsAgainstFiniteTypeSmallExtensions B _ hS (zeroQuotientPoint k B hS) := by
  intro R' R φ hφ T T' i e e' _ α β hβ hcomm
  exfalso
  obtain ⟨hR'loc, hRloc, hR'art, -, -, -⟩ := hφ
  let F := BigFppfOver.toScheme B (Spec (.of k)) hS
  have : Nonempty (F.obj T) := ⟨e.inv.base (IsLocalRing.closedPoint R)⟩
  have : Subsingleton (F.obj T') := ⟨fun x y ↦ e'.hom.isOpenEmbedding.injective
    (Subsingleton.elim (α := PrimeSpectrum R') _ _)⟩
  have : IsAffine (F.obj T') := IsAffine.of_isIso e'.hom
  let a₀ : T ⟶ baseObj k B hS := Yoneda.fullyFaithful.preimage α
  have ha₀ : yoneda.map a₀ = α := Yoneda.fullyFaithful.map_preimage _
  have hcoord : a₀ ≫ zeroSection k B hS = linePoint k B hS T 0 := by
    apply linePoint_ext
    have h1 : (F.map (a₀ ≫ zeroSection k B hS)).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit) = (F.map a₀).appTop
          ((F.map (zeroSection k B hS)).appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) := by
      rw [F.map_comp, Scheme.Hom.comp_appTop]
      rfl
    rw [h1, linePoint_appTop_coord, map_zero, linePoint_appTop_coord]
  refine not_isQuasiCompact_of_comp_eq_linePoint_zero k B hS i β ?_ hβ.2
  rwa [← hcoord, Functor.map_comp, Category.assoc, ha₀]

/-- The point `Spec k ⟶ 𝔸¹_k/ℤ` given by the zero section is locally of finite type: on the
square of étale charts formed by the identity of `Spec k` and the chart `𝔸¹_k ⟶ 𝔸¹_k/ℤ` it is
the zero section, a section of the structure morphism of `𝔸¹_k`. -/
theorem isLocallyOfFiniteType_zeroQuotientPoint :
    Space.IsLocallyOfFiniteType B _ hS (zeroQuotientPoint k B hS) := by
  let F := BigFppfOver.toScheme B (Spec (.of k)) hS
  apply (Space.holdsOnEveryEtaleChart_iff_surjectiveChart B _ hS
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B _ hS _) (isAlgebraicSpace_translationQuotient k B hS)
    (zeroQuotientPoint k B hS)).mpr
  refine ⟨baseObj k B hS, lineObj k B hS, 𝟙 _, lineChart k B hS, zeroSection k B hS, ?_,
    etale_lineChart k B hS, ?_, by simp, ?_⟩
  · exact Space.presheaf_yoneda_map_id_etale B _ hS _
  · rw [← yoneda.map_id]
    exact (Space.presheaf_yoneda_map_iff B _ hS inferInstance _).mpr
      (by rw [F.map_id]; infer_instance)
  · have hsec : F.map (zeroSection k B hS) ≫ B.inclusion.map (lineObj k B hS).hom = 𝟙 _ := by
      have h := congrArg B.inclusion.map (Over.w (zeroSection k B hS))
      rw [Functor.map_comp] at h
      refine h.trans ?_
      change B.inclusion.map (𝟙 (B.obj hS)) = _
      rw [B.inclusion.map_id]
      rfl
    have : LocallyOfFiniteType
        (F.map (zeroSection k B hS) ≫ B.inclusion.map (lineObj k B hS).hom) := by
      rw [hsec]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (B.inclusion.map (lineObj k B hS).hom)

/-- The point `Spec k ⟶ 𝔸¹_k/ℤ` given by the zero section is not smooth: on the square of
étale charts formed by the identity of `Spec k` and the chart `𝔸¹_k ⟶ 𝔸¹_k/ℤ` it is the zero
section, which is not smooth. -/
theorem not_isSmooth_zeroQuotientPoint :
    ¬ Space.IsSmooth B _ hS (zeroQuotientPoint k B hS) := by
  intro hsm
  exact not_smooth_zeroSection k B hS (hsm (baseObj k B hS) (lineObj k B hS) (𝟙 _)
    (lineChart k B hS) (zeroSection k B hS) (Space.presheaf_yoneda_map_id_etale B _ hS _)
    (etale_lineChart k B hS) (by simp))

/-- `𝔸¹_k/ℤ` is locally Noetherian: the affine line is a surjective étale chart of it. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_translationQuotient :
    Space.HasEtaleLocalProperty B _ hS (translationQuotient k B hS (contains_affineLine k B hS))
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) := by
  refine ⟨lineObj k B hS, lineChart k B hS, surjective_lineChart k B hS,
    etale_lineChart k B hS, ?_⟩
  change IsLocallyNoetherian (AffineSpace PUnit.{u + 1} (Spec (.of k)))
  exact LocallyOfFiniteType.isLocallyNoetherian
    (AffineSpace PUnit.{u + 1} (Spec (.of k)) ↘ Spec (.of k))

end AlgebraicGeometry.AffineLineTranslation

namespace AlgebraicGeometry.Space

open AffineLineTranslation Stacks.Examples.NonSeparatedGroupSpace

/-- **The literal condition (2) of Stacks 0APP does not characterize smoothness.** There is a
morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, locally of finite type with `Y`
locally Noetherian, which satisfies condition (2) of Stacks 0APP with the test morphism
`Spec B' ⟶ Y` required to be of finite type, but which is not smooth.

The morphism is the point `Spec ℚ ⟶ 𝔸¹_ℚ/ℤ` given by the zero section. Over the
non-quasi-separated target `𝔸¹_ℚ/ℤ` no morphism from a one-point affine scheme agreeing with
that point on a test square is quasi-compact, so condition (2) holds for want of a test
square. -/
theorem exists_not_isSmooth_liftsAgainstFiniteTypeSmallExtensions :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
      (_ : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y),
      HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z) ∧
        IsLocallyOfFiniteType B S hS f ∧ LiftsAgainstFiniteTypeSmallExtensions B S hS f ∧
        ¬ IsSmooth B S hS f := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_contains (Spec (.of (ULift.{u} ℚ)))
  let : CharZero (ULift.{u} ℚ) := (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ).toRingHom.charZero
  let := BigFppfOver.hasSheafify_type B (Spec (.of (ULift.{u} ℚ))) hB
  exact ⟨B, _, hB, _, _, isAlgebraicSpace_yoneda B _ hB _,
    isAlgebraicSpace_translationQuotient _ B hB, zeroQuotientPoint _ B hB,
    hasEtaleLocalProperty_isLocallyNoetherian_translationQuotient _ B hB,
    isLocallyOfFiniteType_zeroQuotientPoint _ B hB,
    liftsAgainstFiniteTypeSmallExtensions_zeroQuotientPoint _ B hB,
    not_isSmooth_zeroQuotientPoint _ B hB⟩

/-- **Stacks 0APP, as stated, is false.** The equivalence of smoothness with condition (2) of
Stacks 0APP, in which the test morphism `Spec B' ⟶ Y` is required to be of finite type, fails for
some morphism of algebraic spaces locally of finite type over a locally Noetherian target: the
point `Spec ℚ ⟶ 𝔸¹_ℚ/ℤ` of `exists_not_isSmooth_liftsAgainstFiniteTypeSmallExtensions` satisfies
condition (2) and is not smooth.

The implication from smoothness does hold, and is
`AlgebraicGeometry.Space.IsSmooth.liftsAgainstFiniteTypeSmallExtensions`; the corrected
equivalence, with the test morphism required only to be locally of finite type, is
`AlgebraicGeometry.Space.isSmooth_iff_forall_exists_lift_isSmallExtension`. -/
@[stacks 0APP "the statement with the test morphism Spec B' ⟶ Y of finite type is false: the
point Spec ℚ ⟶ 𝔸¹_ℚ/ℤ of the zero section satisfies that condition (2) and is not smooth. The
corrected form, with Spec B' ⟶ Y locally of finite type, is
isSmooth_iff_forall_exists_lift_isSmallExtension"]
theorem not_forall_isSmooth_iff_liftsAgainstFiniteTypeSmallExtensions :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
      IsAlgebraicSpace B S hS Y → ∀ f : X ⟶ Y,
      HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z) →
      IsLocallyOfFiniteType B S hS f →
      (IsSmooth B S hS f ↔ LiftsAgainstFiniteTypeSmallExtensions B S hS f) := by
  intro h
  obtain ⟨B, S, hS, X, Y, hX, hY, f, hNoeth, hft, hlift, hnot⟩ :=
    exists_not_isSmooth_liftsAgainstFiniteTypeSmallExtensions.{u}
  exact hnot ((h B S hS X Y hX hY f hNoeth hft).mpr hlift)

end AlgebraicGeometry.Space

end
