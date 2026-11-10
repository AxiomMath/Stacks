module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Subcanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Monomorphy of morphisms of algebraic spaces is fpqc local on the base

Being a monomorphism — an injective map of sheaves on the big fppf site of `S`, which is Stacks
042L and, by Stacks 042M, monomorphy in the category of algebraic spaces over `S` — is local on
the base for the fpqc topology of Stacks 03YH. This is **Stacks 042D**.

The ascent half is the stability of monomorphisms under base change. For the descent half, Stacks
042Q reduces monomorphy of `f : X ⟶ Y` to monomorphy of the base change of `f` along every
morphism from an affine object of the site, and the fpqc covering condition of Stacks 03MQ refines
the given covering over such an affine object `Z` by a finite family of affine objects over `Z`
each of which factors through a member of the covering. The base changes of `f` along that finite
family are therefore base changes of base changes of `f` along members of the covering, hence
monomorphisms, and the family generates an fpqc covering sieve of `Z`, along which monomorphy
descends because the fibre product `X ×_Y h_Z` is an fpqc sheaf by Stacks 0APL.

## Main results

* `AlgebraicGeometry.Space.mono_isLocalAtTarget_fpqc`: **Stacks 042D**.
* `AlgebraicGeometry.Space.mono_isLocalAtTarget_fppf`: the same at the fppf precoverage, which is
  the form the relative properties of Stacks 03YK ask for.

## Implementation notes

The property is Mathlib's `CategoryTheory.MorphismProperty.monomorphisms`, taken in the category
of algebraic spaces over `S`, which is the reading of Stacks 042L that
`AlgebraicGeometry.Space.mono_hom_iff_mono` identifies with injectivity as a map of presheaves.

`CategoryTheory.mono_of_mono_pullback_snd_ofArrows` is the descent of monomorphy along a family of
morphisms of a site generating a covering sieve. It is the `CategoryTheory.Sieve.ofArrows` form of
the private lemma `mono_of_isLocallySurjective_sigmaDesc` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Monomorphisms.lean`, which is stated for a family
whose induced morphism out of the coproduct of its sources is locally surjective; since that
lemma is private it is restated here rather than reused, and the `ofArrows` form is what is
needed, because the coproduct form constrains the index type to `Type u` whereas the finite family
supplied by Stacks 03MQ is indexed in `Type (u + 1)`.

The two sides of Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtTarget` speak of
`CategoryTheory.Limits.pullback.snd` in the category of algebraic spaces, whereas Stacks 042Q and
the covering condition speak of the presheaf fibre product;
`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom` is the comparison, and monomorphy is carried
across the resulting isomorphism of fibre products by `CategoryTheory.mono_comp`.

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 042D](https://stacks.math.columbia.edu/tag/042D)
* [Stacks Project, Tag 042L](https://stacks.math.columbia.edu/tag/042L)
* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 042Q](https://stacks.math.columbia.edu/tag/042Q)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

/-- **Monomorphy descends along a covering family of a site.** Let `q : P ⟶ yoneda.obj Z` be a
morphism of presheaves on a site whose source is a sheaf, and let `m i : V i ⟶ Z` be a family of
morphisms generating a covering sieve of `Z`. If every base change of `q` along an `m i` is a
monomorphism, then so is `q`.

Two sections of `P` which agree under `q` agree after restriction along any morphism whose
`q`-image factors through some `m i`, because the two restrictions are morphisms into the base
change of `q` along `m i` with the same second component. That makes `q` locally injective, and
the source being a sheaf turns local injectivity into injectivity. -/
@[sga "3 IV 4.5.7" "(iv)⇒(i), special case", sga "3 IV 4.5.8" "partial", sga "4 IV 8.5.1" "partial"]
private theorem mono_of_mono_pullback_snd_ofArrows {C : Type v} [Category.{u, v} C]
    (J : GrothendieckTopology C) {P : Cᵒᵖ ⥤ Type u} {Z : C} (q : P ⟶ yoneda.obj Z)
    (hP : Presheaf.IsSheaf J P) {I : Type w} (V : I → C) (m : ∀ i, V i ⟶ Z)
    (hcover : Sieve.ofArrows V m ∈ J Z)
    (hmono : ∀ i, Mono (pullback.snd q (yoneda.map (m i)))) : Mono q := by
  have hlocinj : Presheaf.IsLocallyInjective J q := by
    refine ⟨fun {W} x y hxy ↦ ?_⟩
    refine J.superset_covering ?_ (J.pullback_stable (q.app W x) hcover)
    intro W' a ha
    rw [Sieve.pullback_apply] at ha
    obtain ⟨i, b, hb⟩ := (Sieve.mem_ofArrows_iff V m (a ≫ q.app W x)).mp ha
    have key : ∀ t : P.obj W, q.app W x = q.app W t →
        (yonedaEquiv (F := P)).symm (P.map a.op t) ≫ q = yoneda.map b ≫ yoneda.map (m i) := by
      intro t ht
      apply (yonedaEquiv (F := yoneda.obj Z)).injective
      simp only [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rw [NatTrans.naturality_apply q a.op t, ← ht]
      simp only [yonedaEquiv_yoneda_map]
      exact hb
    have hα := key x rfl
    have hβ := key y hxy
    have := hmono i
    have heq : pullback.lift _ _ hα = pullback.lift _ _ hβ :=
      (cancel_mono (pullback.snd q (yoneda.map (m i)))).1
        (by rw [pullback.lift_snd, pullback.lift_snd])
    have hαβ : (yonedaEquiv (F := P)).symm (P.map a.op x)
        = (yonedaEquiv (F := P)).symm (P.map a.op y) := by
      rw [← pullback.lift_fst _ _ hα, ← pullback.lift_fst _ _ hβ, heq]
    change P.map a.op x = P.map a.op y
    simpa using congrArg (yonedaEquiv (F := P)) hαβ
  have hsep : Presieve.IsSeparated J (P ⋙ forget (Type u)) :=
    ((isSheaf_iff_isSheaf_of_type J P).1 hP).isSeparated
  exact (NatTrans.mono_iff_mono_app q).2 fun W ↦ (mono_iff_injective (q.app W)).2 <|
    (Presheaf.isLocallyInjective_iff_injective_of_separated J q hsep).1 hlocinj W

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 042D.** Monomorphy of morphisms of algebraic spaces over `S` is local on the base for
the fpqc topology: a morphism is a monomorphism exactly when its base change to every member of
some fpqc covering of its target is a monomorphism.

Stacks 042Q reduces monomorphy to monomorphy of the base changes along the morphisms out of the
affine objects of the site, over such an object the covering is refined by a finite family of
affine objects factoring through its members, and monomorphy descends along the fpqc covering
sieve that family generates because the fibre product is an fpqc sheaf by Stacks 0APL. -/
@[stacks 042D, sga "3 IV 4.5.8" "special case", sga "4 IV 8.5.5" "more general"]
instance mono_isLocalAtTarget_fpqc :
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  refine .mk_of_iff fun X Y f R hR ↦ ⟨fun hf U g _ _ ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) hf,
    fun hlocal ↦ ?_⟩
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  change Mono f
  rw [← mono_hom_iff_mono B S hS f]
  refine ((mono_tfae B S hS X.property Y.property f.hom).out 3 1).mp fun Z g hZaff ↦ ?_
  -- The finite family of affine objects over `Z` refining the covering.
  obtain ⟨U, hfin, hmem, hfactor⟩ := hcover.2.2.2 ⟨Z, hZaff⟩ g
  have hmem' : Presieve.ofArrows
      (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (U.X j))
      (fun j ↦ (BigAffineFppf.inclusion B S hS).map (U.f j)) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).coverings Z := by
    rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hmem
    rwa [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  have hcoverZ : Sieve.ofArrows
      (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (U.X j))
      (fun j ↦ (BigAffineFppf.inclusion B S hS).map (U.f j)) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck Z :=
    Precoverage.generate_mem_toGrothendieck hmem'
  -- Over each member of that family the base change of `f` is a monomorphism.
  have hmono : ∀ j, Mono (pullback.snd (pullback.snd f.hom g)
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)))) := by
    intro j
    obtain ⟨i, a, hfac⟩ := hfactor j
    have hmi : Mono (pullback.snd f.hom (gi i).hom) := by
      have : Mono (pullback.snd f (gi i)).hom :=
        (mono_hom_iff_mono B S hS _).mpr (hlocal (gi i) (Presieve.ofArrows.mk i))
      rw [← (IsPullback.of_hasPullback f.hom (gi i).hom).isoIsPullback_hom_snd _ _
        (AlgebraicSpaces.isPullback_hom _ _ _ (IsPullback.of_hasPullback f (gi i)))]
      infer_instance
    have sq2 := (IsPullback.of_hasPullback (pullback.snd f.hom (gi i).hom) a).paste_horiz
      (IsPullback.of_hasPullback f.hom (gi i).hom)
    have sq1 := (IsPullback.of_hasPullback (pullback.snd f.hom g)
      (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)))).paste_horiz
      (IsPullback.of_hasPullback f.hom g)
    rw [← hfac] at sq1
    rw [← sq1.isoIsPullback_hom_snd _ _ sq2]
    infer_instance
  exact mono_of_mono_pullback_snd_ofArrows
    (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
    (pullback.snd f.hom g)
    (BigFppfOver.isSheaf_fpqc_pullback_yoneda_obj f.hom g X.property.isSheaf_fpqc
      Y.property.isSheaf_fpqc)
    _ _ hcoverZ hmono

/-- **Stacks 042D at the fppf precoverage:** monomorphy of morphisms of algebraic spaces over `S`
is local on the base for the fppf topology. This is the form in which Stacks 03YK's relative
properties ask for it, and it follows from the fpqc form because every fppf covering family of
algebraic spaces is an fpqc covering family. -/
@[sga "3 IV 4.5.8" "special case", sga "4 IV 8.5.5" "special case"]
instance mono_isLocalAtTarget_fppf :
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  .of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

end
