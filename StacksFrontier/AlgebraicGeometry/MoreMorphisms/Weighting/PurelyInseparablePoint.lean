module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a fibre reduced to one purely inseparable point

If the fibre of `f : X ⟶ S` over `s` consists of a single point `x` whose residue-field
extension over `κ(s)` is purely inseparable, then over any point of any base change `S' ⟶ S`
lying over `s` the fibre of `X ×_S S' ⟶ S'` again consists of a single point. This is the
geometric reason why a finite open piece of an étale base change which meets the distinguished
fibre in a single purely inseparable point stays that way after a further base change.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.spec_tensor_subsingleton_of_isPurelyInseparable` and
  `AlgebraicGeometry.Scheme.Pullback.tensor_subsingleton_of_isPurelyInseparable`: the spectrum of
  the tensor product is a subsingleton when one side is purely inseparable.
* `AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isPurelyInseparable`: two points of
  a fibre product with the same images are equal when one of the residue-field extensions is
  purely inseparable.
* `AlgebraicGeometry.Scheme.Pullback.existsUnique_of_isPurelyInseparable`: existence and
  uniqueness of the point of the fibre product over a prescribed pair of points.
* `AlgebraicGeometry.Scheme.Pullback.eq_of_snd_eq_of_isPurelyInseparable`: the fibre of the base
  change over such a point is a subsingleton.

## Implementation notes

Points of a fibre product are described by Mathlib's
`AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: a point is a triplet of points with matching
images together with a point of the spectrum of the tensor product of the three residue fields.
A purely inseparable field extension induces a homeomorphism on prime spectra after any base
change, so that spectrum is a subsingleton and the triplet determines the point.

## References

* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- The spectrum of `L ⊗[k] K` is a subsingleton when `K/k` is purely inseparable. -/
theorem spec_tensor_subsingleton_of_isPurelyInseparable
    (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [IsPurelyInseparable k K] :
    Subsingleton (Spec (CommRingCat.of (L ⊗[k] K))) :=
  (Equiv.ofBijective _
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K L).bijective).subsingleton

/-- The tensor-product spectrum attached to a triplet of points is a subsingleton when the
residue-field extension on one side is purely inseparable. -/
theorem tensor_subsingleton_of_isPurelyInseparable
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Triplet f g)
    (hpi : (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).IsPurelyInseparable) :
    Subsingleton (Spec T.tensor) := by
  let k := S.residueField T.s
  let K := X.residueField T.x
  let L := Y.residueField T.y
  let : Algebra k K := ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom.toAlgebra
  let : Algebra k L := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
  have hpure : IsPurelyInseparable k K := by
    simpa only [RingHom.IsPurelyInseparable] using hpi
  have hT : IsPushout (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (algebraMap k L)) T.tensorInl T.tensorInr := by
    dsimp [Triplet.tensorInl, Triplet.tensorInr, Triplet.tensor]
    exact IsPushout.of_hasPushout _ _
  let e := hT.isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct k K L)
  let e₁ : Spec T.tensor ≅ Spec (CommRingCat.of (K ⊗[k] L)) :=
    Scheme.Spec.mapIso e.symm.op
  let eKL : CommRingCat.of (K ⊗[k] L) ≅ CommRingCat.of (L ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).toCommRingCatIso
  let e₂ : Spec (CommRingCat.of (K ⊗[k] L)) ≅ Spec (CommRingCat.of (L ⊗[k] K)) :=
    Scheme.Spec.mapIso eKL.symm.op
  have : Subsingleton (Spec (CommRingCat.of (L ⊗[k] K))) :=
    spec_tensor_subsingleton_of_isPurelyInseparable k K L
  exact (e₁ ≪≫ e₂).hom.homeomorph.subsingleton

/-- Two points of a fibre product with the same images under both projections agree, provided
the residue-field extension of one projection at that image is purely inseparable. -/
theorem eq_of_fst_eq_of_snd_eq_of_isPurelyInseparable
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Triplet f g)
    (hpi : (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom).IsPurelyInseparable)
    {z z' : ↑(pullback f g)}
    (hzx : pullback.fst f g z = T.x) (hzy : pullback.snd f g z = T.y)
    (hz'x : pullback.fst f g z' = T.x) (hz'y : pullback.snd f g z' = T.y) : z = z' := by
  let e := carrierEquiv (f := f) (g := g)
  have key (w : ↑(pullback f g)) (hx : pullback.fst f g w = T.x)
      (hy : pullback.snd f g w = T.y) : (e w).1 = T := by
    apply Triplet.ext
    · have hh := carrierEquiv_symm_fst (e w).1 (e w).2
      change pullback.fst f g (e.symm (e w)) = (e w).1.x at hh
      rw [e.symm_apply_apply] at hh
      exact hh.symm.trans hx
    · have hh := carrierEquiv_symm_snd (e w).1 (e w).2
      change pullback.snd f g (e.symm (e w)) = (e w).1.y at hh
      rw [e.symm_apply_apply] at hh
      exact hh.symm.trans hy
  have hTz' := key z' hz'x hz'y
  refine e.injective (carrierEquiv_eq_iff.mpr ⟨(key z hzx hzy).trans hTz'.symm, ?_⟩)
  have : Subsingleton (Spec (e z').1.tensor) := by
    rw [hTz']
    exact tensor_subsingleton_of_isPurelyInseparable T hpi
  exact Subsingleton.elim _ _

/-- If the fibre of `f` over `s` is the single point `x` with purely inseparable residue-field
extension, then for every point `t` of a base change lying over `s` there is a unique point of
the fibre product above `x` and `t`. -/
@[ega "IV 6.15.3" "partial"]
theorem existsUnique_of_isPurelyInseparable
    {X S S' : Scheme.{u}} (f : X ⟶ S) (x : X) (s : S) (hxs : f x = s)
    (hfiber : f ⁻¹' {s} = {x})
    (hpi : (((S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom).IsPurelyInseparable)
    (q : S' ⟶ S) (t : S') (ht : q t = s) :
    ∃! z : ↑(pullback f q),
      pullback.fst f q z = x ∧ pullback.snd f q z = t := by
  obtain ⟨z₀, hz₀x, hz₀t⟩ := exists_preimage_pullback x t (hxs.trans ht.symm)
  refine ⟨z₀, ⟨hz₀x, hz₀t⟩, fun z hz ↦ ?_⟩
  have hbase : f (pullback.fst f q z) = q (pullback.snd f q z) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : pullback f q ⟶ S ↦ m z) (pullback.condition (f := f) (g := q))
  have hm : pullback.fst f q z ∈ f ⁻¹' {s} := by simpa [hz.2, ht] using hbase
  rw [hfiber] at hm
  exact eq_of_fst_eq_of_snd_eq_of_isPurelyInseparable ⟨x, t, s, hxs, ht⟩ hpi
    (Set.mem_singleton_iff.mp hm) hz.2 hz₀x hz₀t

/-- If the fibre of `f` over `s` is the single point `x` with purely inseparable residue-field
extension, then the fibre of the base change `X ×_S S' ⟶ S'` over any point lying over `s` is a
subsingleton. -/
@[ega "IV 6.15.3" "partial"]
theorem eq_of_snd_eq_of_isPurelyInseparable
    {X S S' : Scheme.{u}} (f : X ⟶ S) (x : X) (s : S) (hxs : f x = s)
    (hfiber : f ⁻¹' {s} = {x})
    (hpi : (((S.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom).IsPurelyInseparable)
    (q : S' ⟶ S) (t : S') (ht : q t = s)
    {z z' : ↥(pullback f q)}
    (hz : pullback.snd f q z = t) (hz' : pullback.snd f q z' = t) : z = z' := by
  obtain ⟨c, hc, huniq⟩ := existsUnique_of_isPurelyInseparable f x s hxs hfiber hpi q t ht
  have hfst (p : ↥(pullback f q)) (hp : pullback.snd f q p = t) :
      pullback.fst f q p = x := by
    have hbase : f (pullback.fst f q p) = q (pullback.snd f q p) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun m : pullback f q ⟶ S ↦ m p) (pullback.condition (f := f) (g := q))
    have hm : pullback.fst f q p ∈ f ⁻¹' {s} := by simpa [hp, ht] using hbase
    rw [hfiber] at hm
    exact Set.mem_singleton_iff.mp hm
  exact (huniq z ⟨hfst z hz, hz⟩).trans (huniq z' ⟨hfst z' hz', hz'⟩).symm

end AlgebraicGeometry.Scheme.Pullback
