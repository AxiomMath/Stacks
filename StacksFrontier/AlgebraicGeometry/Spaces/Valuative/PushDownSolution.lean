module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Injective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition

/-!
# Pushing a valuative solution down along an extension of valuation rings

Let `B` be a big fppf site containing a scheme `S` and let `f : X ⟶ Y` be a separated
morphism of algebraic spaces over `S`. A valuative square `q` for `f` consists of a
valuation ring `A` with fraction field `K`, a generic point `Spec K ⟶ X` and a bottom edge
`Spec A ⟶ Y`; a dominating extension `e` of `q` is an extension `K'/K` together with a
valuation ring `A' ⊆ K'` dominating `A`, and a lift of `e.square` is a morphism
`Spec A' ⟶ X` making the two triangles commute.

This file pushes such a lift down to the original square: the dotted arrow
`Spec A ⟶ X` exists, with no condition at all on the extension `K'/K`.

## Main results

* `AlgebraicGeometry.Space.exists_lift_of_dominatingExtension`: **a lift of a dominating
  extension of a valuative square for a separated morphism descends to a lift of the square
  itself**.
* `AlgebraicGeometry.Space.subsingleton_lift_of_dominatingExtension`: **a dotted arrow of a
  valuative square is determined by its restriction to a dominating extension**, for any
  morphism with source an algebraic space.
* `AlgebraicGeometry.Space.valuativeCriterion_existence_iff_lift_of_isSeparated`: for a
  separated morphism, the existence half of the valuative criterion holds exactly when every
  valuative square has a lift over the original valuation ring.

## Implementation notes

The argument is fpqc descent along the single morphism `Spec A' ⟶ Spec A`, which is a
covering because `A'` is torsion free over the valuation ring `A`, hence flat, and dominates
`A`, hence faithfully flat. The descent datum is the lift `Spec A' ⟶ X`, and what has to be
checked is that its two restrictions to `Spec (A' ⊗_A A')` agree. They have the same
composite to `Y`, so by separatedness of `f` they agree as soon as they agree on a subscheme
through which `A' ⊗_A A'` injects; the localization of `A' ⊗_A A'` at the images of the
nonzerodivisors of `A'` under both inclusions is such a subscheme, and over it both
restrictions factor through the generic point `Spec K ⟶ X`, where the two inclusions become
equal because every nonzero element of `A` is inverted.

The sheaf condition for that one covering is supplied by
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc`, the fpqc sheaf condition of Stacks 0APL for
an algebraic space; the rest of the argument needs only its uniqueness half, which is
`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`.

## References

* [Stacks Project, Tag 0ARH](https://stacks.math.columbia.edu/tag/0ARH)
* [Stacks Project, Tag 0A3W](https://stacks.math.columbia.edu/tag/0A3W)
* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- The homomorphism of valuation rings of a dominating extension is injective, because it
becomes the injective homomorphism of fraction fields. -/
private theorem dominatingExtension_ringMap_injective (q : ValuativeSquare f)
    (e : q.DominatingExtension) : Function.Injective e.ringMap := by
  intro a b hab
  apply (IsFractionRing.injective q.R q.K)
  apply e.fieldMap.injective
  have h := congrArg (algebraMap e.square.R e.square.K) hab
  have h' := congrArg (fun φ : q.R →+* e.square.K => φ a) e.fraction_comm
  have h'' := congrArg (fun φ : q.R →+* e.square.K => φ b) e.fraction_comm
  calc
    e.fieldMap (algebraMap q.R q.K a) =
        algebraMap e.square.R e.square.K (e.ringMap a) := h'.symm
    _ = algebraMap e.square.R e.square.K (e.ringMap b) := h
    _ = e.fieldMap (algebraMap q.R q.K b) := h''

/-- The homomorphism of valuation rings of a dominating extension is faithfully flat: the
larger ring is torsion free over the smaller, hence flat over it as it is a valuation ring,
and the homomorphism is local. -/
private theorem dominatingExtension_ringMap_faithfullyFlat (q : ValuativeSquare f)
    (e : q.DominatingExtension) : e.ringMap.FaithfullyFlat := by
  let : IsLocalHom e.ringMap := e.isLocalHom
  let : Algebra q.R e.square.R := e.ringMap.toAlgebra
  have hinj := dominatingExtension_ringMap_injective q e
  have hflat : Module.Flat q.R e.square.R := by
    have htf : Module.IsTorsionFree q.R e.square.R := by
      constructor
      intro r hr
      have hr0 : r ≠ 0 := (isRegular_iff_ne_zero.mp hr)
      have hc : e.ringMap r ≠ 0 := by
        intro h
        exact hr0 (hinj (by simpa using h))
      intro x y hxy
      apply mul_left_cancel₀ hc
      change e.ringMap r * x = e.ringMap r * y at hxy
      exact hxy
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  let : IsLocalRing q.R := ValuationRing.isLocalRing q.R
  let : IsLocalRing e.square.R := ValuationRing.isLocalRing e.square.R
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- A morphism of the site whose underlying scheme morphism is the spectrum map of a
faithfully flat ring homomorphism is a one-element fpqc covering. -/
private theorem singleton_mem_fpqc_of_faithfullyFlat {R R' : Type u} [CommRing R] [CommRing R']
    (hR : B.Contains (Spec (.of R))) (hR' : B.Contains (Spec (.of R')))
    {b : Spec (.of R) ⟶ S} {b' : Spec (.of R') ⟶ S}
    (a : siteObject B S hS hR' b' ⟶ siteObject B S hS hR b) (φ : R →+* R')
    (hφ : φ.FaithfullyFlat)
    (ha : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a =
      Spec.map (CommRingCat.ofHom φ)) :
    Presieve.singleton a ∈ Scheme.fpqcPrecoverage.comap
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS) (siteObject B S hS hR b) := by
  have hmap := (AlgebraicGeometry.flat_and_surjective_SpecMap_iff (CommRingCat.ofHom φ)).2 hφ
  have : Flat (Spec.map (CommRingCat.ofHom φ)) := hmap.1
  have : Surjective (Spec.map (CommRingCat.ofHom φ)) := hmap.2
  rw [Precoverage.mem_comap_iff, Presieve.map_singleton, ha]
  have : QuasiCompact (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  exact Scheme.Hom.singleton_mem_fpqcPrecoverage _

/-- The bottom edge of a dominating extension is a one-element fpqc covering of the site. -/
private theorem dominatingExtension_specialOver_mem_fpqc (q : ValuativeSquare f)
    (e : q.DominatingExtension) :
    Presieve.singleton e.specialOver ∈
      Scheme.fpqcPrecoverage.comap (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
        (siteObject B S hS q.ring_mem q.base) :=
  singleton_mem_fpqc_of_faithfullyFlat _ _ _ _ (dominatingExtension_ringMap_faithfullyFlat q e)
    e.specialOver_left

/-- The top edge of a dominating extension is a one-element fpqc covering of the site: an
extension of fields is faithfully flat. -/
private theorem dominatingExtension_genericOver_mem_fpqc (q : ValuativeSquare f)
    (e : q.DominatingExtension) :
    Presieve.singleton e.genericOver ∈
      Scheme.fpqcPrecoverage.comap (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
        (siteObject B S hS q.field_mem
          (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) :=
  let : Algebra q.K e.square.K := e.fieldMap.toAlgebra
  singleton_mem_fpqc_of_faithfullyFlat _ _ _ _ (by
    change Module.FaithfullyFlat q.K e.square.K
    infer_instance) e.genericOver_left

/-- The square of a dominating extension formed by the top edge, the bottom edge and the
inclusions of the generic points commutes. -/
private theorem dominatingExtension_genericOver_comp_eq (q : ValuativeSquare f)
    (e : q.DominatingExtension)
    (iKR : siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
        siteObject B S hS q.ring_mem q.base)
    (iLA : siteObject B S hS e.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base) ⟶
        siteObject B S hS e.square.ring_mem e.square.base)
    (hK : iKR.left = ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))))
    (hL : iLA.left = ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)))) :
    e.genericOver ≫ iKR = iLA ≫ e.specialOver := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change B.inclusion.map e.genericOver.left ≫ B.inclusion.map iKR.left =
    B.inclusion.map iLA.left ≫ B.inclusion.map e.specialOver.left
  rw [hK, hL, e.genericOver_left, e.specialOver_left]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact e.fraction_comm.symm

/-- A nonzerodivisor of a flat algebra stays a nonzerodivisor in the left factor of the
tensor square. -/
private theorem tensor_includeLeft_regular
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [SMulCommClass R A A]
    [Module.Flat R A] (a : A) (ha : IsRegular a) :
    IsRegular ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) a) :=
  isLeftRegular_iff_isRegular.mp (IsSMulRegular.of_flat (S := A ⊗[R] A) ha.1)

/-- A nonzerodivisor of a flat algebra stays a nonzerodivisor in the right factor of the
tensor square. -/
private theorem tensor_includeRight_regular
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [SMulCommClass R A A]
    [Module.Flat R A] (a : A) (ha : IsRegular a) :
    IsRegular ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) a) := by
  let E := Algebra.TensorProduct.comm R A A
  have h := tensor_includeLeft_regular (R := R) a ha
  apply isLeftRegular_iff_isRegular.mp
  intro x y hxy
  apply E.injective
  apply h.left
  have hs : E ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A) a) =
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A) a := rfl
  simpa only [map_mul, hs] using congrArg E hxy

/-- The spectrum of the tensor square of a ring whose own spectrum belongs to the site
belongs to the site. -/
private theorem tensor_spec_mem (B : AlgebraicGeometry.BigFppfSite.{u}) {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (hA : B.Contains (Spec (.of A))) :
    B.Contains (Spec (.of (A ⊗[R] A))) := by
  have hAcard : Cardinal.mk A < B.cutoff :=
    lt_of_le_of_lt (le_max_right _ _) (by simpa [Scheme.size_Spec] using hA)
  have hbound : max Cardinal.aleph0 (max (Cardinal.mk A) (Cardinal.mk A)) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt hAcard hAcard)
  change (Spec (.of (A ⊗[R] A))).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_tensorProduct_le.trans_lt hbound)

/-- Two morphisms from an affine object of the site to the source of a separated morphism
which have the same composite to the target, and which agree after a morphism injective on
global sections, are equal. The equalizer of the two morphisms is cut out by the relative
diagonal, hence by a closed immersion into an affine scheme, and a closed immersion through
which an injection on global sections factors is an isomorphism. -/
@[sga "3 IX 4.1" "special case"]
private theorem eq_of_agree_of_appTop_injective
    (hf : AlgebraicGeometry.Space.IsSeparated B S hS f)
    {D Dg : AlgebraicGeometry.BigFppfOver B S hS} (j : Dg ⟶ D)
    (hD : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D))
    (hj : Function.Injective
      (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j).appTop))
    (x y : yoneda.obj D ⟶ X) (hxy : x ≫ f = y ≫ f)
    (hgen : yoneda.map j ≫ x = yoneda.map j ≫ y) : x = y := by
  classical
  let w : yoneda.obj D ⟶ pullback f f := pullback.lift x y hxy
  have hdiag : yoneda.map j ≫ w = yoneda.map j ≫ x ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · calc
        yoneda.map j ≫ w ≫ pullback.fst f f = yoneda.map j ≫ x := by
          change yoneda.map j ≫ (pullback.lift x y hxy ≫ pullback.fst f f) = _
          rw [pullback.lift_fst]
        _ = yoneda.map j ≫ x ≫ pullback.diagonal f ≫ pullback.fst f f := by simp
    · calc
        yoneda.map j ≫ w ≫ pullback.snd f f = yoneda.map j ≫ y := by
          change yoneda.map j ≫ (pullback.lift x y hxy ≫ pullback.snd f f) = _
          rw [pullback.lift_snd]
        _ = yoneda.map j ≫ x ≫ pullback.diagonal f ≫ pullback.snd f f := by
          simp [hgen]
  let P : MorphismProperty ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  change P (pullback.diagonal f) at hf
  let rep := hf.rep
  let Tobj := rep.pullback w
  let sOver := rep.snd w
  let r := rep.fst w
  have sq := rep.isPullback w
  have hsClosed : AlgebraicGeometry.IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sOver) := hf.property w r sOver sq
  let T := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Tobj
  let s : T ⟶ (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sOver
  let kYon : yoneda.obj Dg ⟶ yoneda.obj Tobj :=
    sq.lift (yoneda.map j ≫ x) (yoneda.map j) hdiag.symm
  have hkS : kYon ≫ yoneda.map sOver = yoneda.map j :=
    sq.lift_snd (yoneda.map j ≫ x) (yoneda.map j) hdiag.symm
  let kOver : Dg ⟶ Tobj := yoneda.preimage kYon
  have hkOver : kOver ≫ sOver = j := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, Functor.map_preimage]
    exact hkS
  let k : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dg ⟶ T :=
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map kOver
  have hk : k ≫ s = (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j := by
    change (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map kOver ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map sOver = _
    rw [← Functor.map_comp, hkOver]
  let : AlgebraicGeometry.IsClosedImmersion s := hsClosed
  let : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj D) := hD
  have hsInjective : Function.Injective s.appTop := by
    have hcomp : Function.Injective (k ≫ s).appTop := by
      rw [hk]
      exact hj
    exact Function.Injective.of_comp hcomp
  have hsIso : IsIso s := IsClosedImmersion.isIso_of_injective_of_isAffine hsInjective
  have : IsIso sOver := by
    have hsLeft : IsIso sOver.left := by
      apply (isIso_iff_of_reflects_iso sOver.left B.inclusion).mp
      exact hsIso
    let eOver : Tobj ≅ D := Over.isoMk (asIso sOver.left) (Over.w sOver)
    have he : eOver.hom = sOver := by ext; rfl
    rw [← he]
    infer_instance
  have hw : w = yoneda.map (inv sOver) ≫ r ≫ pullback.diagonal f := by
    calc
      w = yoneda.map (inv sOver) ≫ yoneda.map sOver ≫ w := by simp
      _ = _ := by rw [← sq.w]
  have hfst : w ≫ pullback.fst f f = yoneda.map (inv sOver) ≫ r := by
    simpa [Category.assoc] using congrArg (fun z => z ≫ pullback.fst f f) hw
  have hsnd : w ≫ pullback.snd f f = yoneda.map (inv sOver) ≫ r := by
    simpa [Category.assoc] using congrArg (fun z => z ≫ pullback.snd f f) hw
  calc
    x = w ≫ pullback.fst f f := (pullback.lift_fst x y hxy).symm
    _ = yoneda.map (inv sOver) ≫ r := hfst
    _ = w ≫ pullback.snd f f := hsnd.symm
    _ = y := pullback.lift_snd x y hxy

/-- **A lift of a dominating extension of a valuative square for a separated morphism of
algebraic spaces descends to a lift of the square itself.** The extension `K'/K` of fraction
fields is arbitrary: no finiteness or separability condition is imposed on it.

The descent step needs the sheaf condition for the single faithfully flat covering
`Spec A' ⟶ Spec A`; it is supplied by the fpqc sheaf condition
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc` for `X`, which is Stacks 0APL. -/
@[stacks 0ARH]
public theorem exists_lift_of_dominatingExtension
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hf : AlgebraicGeometry.Space.IsSeparated B S hS f)
    (q : ValuativeSquare f) (e : q.DominatingExtension)
    (he : Nonempty e.square.Lift) :
    Nonempty q.Lift := by
  classical
  obtain ⟨ℓ⟩ := he
  have hff := dominatingExtension_ringMap_faithfullyFlat q e
  have hcover := dominatingExtension_specialOver_mem_fpqc q e
  let A := e.square.R
  let R := q.R
  let : Algebra R A := e.ringMap.toAlgebra
  let T := A ⊗[R] A
  let il : A →ₐ[R] T := Algebra.TensorProduct.includeLeft
  let ir : A →ₐ[R] T := Algebra.TensorProduct.includeRight
  have hTmem : B.Contains (Spec (.of T)) := tensor_spec_mem B e.square.ring_mem
  let pLs : Spec (.of T) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom il.toRingHom)
  let pRs : Spec (.of T) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom ir.toRingHom)
  let Dbase : Spec (.of T) ⟶ S := pLs ≫ e.square.base
  let Dobj := siteObject B S hS hTmem Dbase
  let Aobj := siteObject B S hS e.square.ring_mem e.square.base
  let pLleft : B.obj hTmem ⟶ B.obj e.square.ring_mem := B.inclusion.preimage pLs
  have hpLbase : pLleft ≫ Aobj.hom = Dobj.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    rfl
  let pL : Dobj ⟶ Aobj := Over.homMk pLleft hpLbase
  have hpRbaseScheme : pRs ≫ e.square.base = Dbase := by
    have hbase : pRs ≫ Spec.map (CommRingCat.ofHom e.ringMap) =
        pLs ≫ Spec.map (CommRingCat.ofHom e.ringMap) := by
      dsimp [pRs, pLs]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext r
      change ir (algebraMap R A r) = il (algebraMap R A r)
      rw [ir.commutes, il.commutes]
    calc
      pRs ≫ e.square.base =
          pRs ≫ (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base) := by rw [e.base_comm]
      _ = (pRs ≫ Spec.map (CommRingCat.ofHom e.ringMap)) ≫ q.base := by rw [Category.assoc]
      _ = (pLs ≫ Spec.map (CommRingCat.ofHom e.ringMap)) ≫ q.base := by rw [hbase]
      _ = Dbase := by simp [Dbase, e.base_comm, Category.assoc]
  let pRleft : B.obj hTmem ⟶ B.obj e.square.ring_mem := B.inclusion.preimage pRs
  have hpRbase : pRleft ≫ Aobj.hom = Dobj.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    exact hpRbaseScheme
  let pR : Dobj ⟶ Aobj := Over.homMk pRleft hpRbase
  have hsameSpecial : pL ≫ e.specialOver = pR ≫ e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (pLleft ≫ e.specialOver.left) =
      B.inclusion.map (pRleft ≫ e.specialOver.left)
    rw [B.inclusion.map_comp, B.inclusion.map_comp,
      B.inclusion.map_preimage, B.inclusion.map_preimage, e.specialOver_left]
    have hbase : pLs ≫ Spec.map (CommRingCat.ofHom e.ringMap) =
        pRs ≫ Spec.map (CommRingCat.ofHom e.ringMap) := by
      dsimp [pRs, pLs]
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext r
      change il (algebraMap R A r) = ir (algebraMap R A r)
      rw [il.commutes, ir.commutes]
    exact hbase
  let xL : yoneda.obj Dobj ⟶ X := yoneda.map pL ≫ ℓ.map
  let xR : yoneda.obj Dobj ⟶ X := yoneda.map pR ≫ ℓ.map
  have hxy : xL ≫ f = xR ≫ f := by
    calc
      xL ≫ f = yoneda.map pL ≫ (ℓ.map ≫ f) := by simp [xL, Category.assoc]
      _ = yoneda.map pL ≫ e.square.special := by rw [ℓ.special_comm]
      _ = yoneda.map pL ≫ (yoneda.map e.specialOver ≫ q.special) := by rw [e.special_comm]
      _ = (yoneda.map pR ≫ yoneda.map e.specialOver) ≫ q.special := by
        simpa [Functor.map_comp, Category.assoc] using
          congrArg (fun g => yoneda.map g ≫ q.special) hsameSpecial
      _ = yoneda.map pR ≫ e.square.special := by simp [e.special_comm, Category.assoc]
      _ = yoneda.map pR ≫ (ℓ.map ≫ f) := by rw [ℓ.special_comm.symm]
      _ = xR ≫ f := by simp [xR, Category.assoc]
  let L := e.square.K
  let : IsLocalization (nonZeroDivisors A) L := e.square.isFractionRing
  let M : Submonoid T :=
    (nonZeroDivisors A).map il.toRingHom ⊔ (nonZeroDivisors A).map ir.toRingHom
  let W := Localization M
  let : Algebra T W := inferInstance
  let : IsLocalization M W := inferInstance
  let gl : A →+* W := (algebraMap T W).comp il.toRingHom
  let gr : A →+* W := (algebraMap T W).comp ir.toRingHom
  have hgl : ∀ x : nonZeroDivisors A, IsUnit (gl x) := by
    intro x
    change IsUnit (algebraMap T W (il x))
    have hx : il x ∈ M := Submonoid.mem_sup_left (Submonoid.mem_map.mpr ⟨x.val, x.2, rfl⟩)
    exact IsLocalization.map_units (R := T) (M := M) W ⟨il x, hx⟩
  have hgr : ∀ x : nonZeroDivisors A, IsUnit (gr x) := by
    intro x
    change IsUnit (algebraMap T W (ir x))
    have hx : ir x ∈ M := Submonoid.mem_sup_right (Submonoid.mem_map.mpr ⟨x.val, x.2, rfl⟩)
    exact IsLocalization.map_units (R := T) (M := M) W ⟨ir x, hx⟩
  let ρl : L →+* W := IsLocalization.lift hgl
  let ρr : L →+* W := IsLocalization.lift hgr
  have hρl : ρl.comp (algebraMap A L) = gl := IsLocalization.lift_comp hgl
  have hρr : ρr.comp (algebraMap A L) = gr := IsLocalization.lift_comp hgr
  have hρ : ρl.comp e.fieldMap = ρr.comp e.fieldMap := by
    have hbal : il.toRingHom.comp e.ringMap = ir.toRingHom.comp e.ringMap := by
      ext r
      change il (algebraMap R A r) = ir (algebraMap R A r)
      rw [il.commutes, ir.commutes]
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    calc
      (ρl.comp e.fieldMap).comp (algebraMap R q.K) =
          ρl.comp (e.fieldMap.comp (algebraMap R q.K)) := by rw [RingHom.comp_assoc]
      _ = ρl.comp ((algebraMap A L).comp e.ringMap) := by rw [← e.fraction_comm]
      _ = (ρl.comp (algebraMap A L)).comp e.ringMap := by rw [← RingHom.comp_assoc]
      _ = gl.comp e.ringMap := by rw [hρl]
      _ = gr.comp e.ringMap := by
        change (algebraMap T W).comp (il.toRingHom.comp e.ringMap) =
          (algebraMap T W).comp (ir.toRingHom.comp e.ringMap)
        rw [hbal]
      _ = (ρr.comp (algebraMap A L)).comp e.ringMap := by rw [hρr]
      _ = ρr.comp ((algebraMap A L).comp e.ringMap) := by rw [RingHom.comp_assoc]
      _ = ρr.comp (e.fieldMap.comp (algebraMap R q.K)) := by rw [e.fraction_comm]
      _ = (ρr.comp e.fieldMap).comp (algebraMap R q.K) := by rw [RingHom.comp_assoc]
  let : Module.Flat R A := hff.toFlat
  have hleft : (nonZeroDivisors A).map il.toRingHom ≤ nonZeroDivisors T := by
    rw [Submonoid.map_le_iff_le_comap]
    intro x hx
    change il x ∈ nonZeroDivisors T
    exact isRegular_iff_mem_nonZeroDivisors.mp <| tensor_includeLeft_regular x
      (isRegular_iff_mem_nonZeroDivisors.mpr hx)
  have hright : (nonZeroDivisors A).map ir.toRingHom ≤ nonZeroDivisors T := by
    rw [Submonoid.map_le_iff_le_comap]
    intro x hx
    change ir x ∈ nonZeroDivisors T
    exact isRegular_iff_mem_nonZeroDivisors.mp <| tensor_includeRight_regular x
      (isRegular_iff_mem_nonZeroDivisors.mpr hx)
  have hM : M ≤ nonZeroDivisors T := sup_le hleft hright
  have hWinj : Function.Injective (algebraMap T W) :=
    IsLocalization.injective (R := T) (M := M) (S := W) hM
  have hWmem : B.Contains (Spec (.of W)) := by
    change (Spec (.of W)).size < B.cutoff
    exact Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit M W hTmem
  let jScheme : Spec (.of W) ⟶ Spec (.of T) := Spec.map (CommRingCat.ofHom (algebraMap T W))
  let Wobj := siteObject B S hS hWmem (jScheme ≫ Dbase)
  let jleft : B.obj hWmem ⟶ B.obj hTmem := B.inclusion.preimage jScheme
  have hjbase : jleft ≫ Dobj.hom = Wobj.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    rfl
  let j : Wobj ⟶ Dobj := Over.homMk jleft hjbase
  have hDaffine : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj Dobj) := by
    change IsAffine (Spec (.of T))
    infer_instance
  have hjmap : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j = jScheme := by
    change B.inclusion.map jleft = jScheme
    rw [B.inclusion.map_preimage]
  have hjinj : Function.Injective
      (((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map j).appTop) := by
    rw [hjmap]
    let iso := arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom (algebraMap T W))
    let Q : MorphismProperty CommRingCat :=
      RingHom.toMorphismProperty fun φ ↦ Function.Injective φ
    have hQ : Q.RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.injective_respectsIso
    change Q _
    rw [← MorphismProperty.arrow_mk_iso_iff (P := Q) iso]
    exact hWinj
  let Lobj := siteObject B S hS e.square.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ e.square.base)
  let iLScheme : Spec (.of L) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A L))
  let iLleft : B.obj e.square.field_mem ⟶ B.obj e.square.ring_mem :=
    ObjectProperty.homMk iLScheme
  let iLA : Lobj ⟶ Aobj := Over.homMk iLleft
  let gLscheme : Spec (.of W) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom ρl)
  let gRscheme : Spec (.of W) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom ρr)
  let gLleft : B.obj hWmem ⟶ B.obj e.square.field_mem := B.inclusion.preimage gLscheme
  let gRleft : B.obj hWmem ⟶ B.obj e.square.field_mem := B.inclusion.preimage gRscheme
  have hringL : CommRingCat.ofHom (algebraMap A L) ≫ CommRingCat.ofHom ρl =
      CommRingCat.ofHom il.toRingHom ≫ CommRingCat.ofHom (algebraMap T W) := by
    apply CommRingCat.hom_ext
    ext a
    change ρl (algebraMap A L a) = algebraMap T W (il a)
    exact congrArg (fun φ : A →+* W => φ a) hρl
  have hringR : CommRingCat.ofHom (algebraMap A L) ≫ CommRingCat.ofHom ρr =
      CommRingCat.ofHom ir.toRingHom ≫ CommRingCat.ofHom (algebraMap T W) := by
    apply CommRingCat.hom_ext
    ext a
    change ρr (algebraMap A L a) = algebraMap T W (ir a)
    exact congrArg (fun φ : A →+* W => φ a) hρr
  have hgLbase : gLleft ≫ Lobj.hom = Wobj.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    dsimp [Lobj, Wobj, iLScheme, gLscheme]
    dsimp [jScheme, pLs, Dbase]
    rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
    rw [hringL]
    rfl
  have hgRbase : gRleft ≫ Lobj.hom = Wobj.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    dsimp [Lobj, Wobj, iLScheme, gRscheme]
    dsimp [jScheme, pRs, Dbase]
    rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
    rw [hringR]
    rw [Spec.map_comp, Spec.map_comp]
    rw [Category.assoc, Category.assoc]
    rw [hpRbaseScheme]
  let gL : Wobj ⟶ Lobj := Over.homMk gLleft hgLbase
  let gR : Wobj ⟶ Lobj := Over.homMk gRleft hgRbase
  have hsameGeneric : gL ≫ e.genericOver = gR ≫ e.genericOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (gLleft ≫ e.genericOver.left) =
      B.inclusion.map (gRleft ≫ e.genericOver.left)
    rw [B.inclusion.map_comp, B.inclusion.map_comp,
      B.inclusion.map_preimage, B.inclusion.map_preimage, e.genericOver_left]
    dsimp [gL, gR, gLleft, gRleft, gLscheme, gRscheme]
    rw [← Spec.map_comp, ← Spec.map_comp]
    have hring : CommRingCat.ofHom e.fieldMap ≫ CommRingCat.ofHom ρl =
        CommRingCat.ofHom e.fieldMap ≫ CommRingCat.ofHom ρr := by
      apply CommRingCat.hom_ext
      ext a
      exact congrArg (fun φ : q.K →+* W => φ a) hρ
    rw [hring]
  have hcompLScheme : jScheme ≫ pLs = gLscheme ≫ iLScheme := by
    dsimp [jScheme, pLs, gLscheme, iLScheme]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rw [hringL]
    rfl
  have hcompRScheme : jScheme ≫ pRs = gRscheme ≫ iLScheme := by
    dsimp [jScheme, pRs, gRscheme, iLScheme]
    rw [← Spec.map_comp, ← Spec.map_comp]
    rw [hringR]
    rfl
  have hcompL : j ≫ pL = gL ≫ iLA := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (jleft ≫ pLleft) = B.inclusion.map (gLleft ≫ iLleft)
    rw [B.inclusion.map_comp, B.inclusion.map_comp]
    rw [B.inclusion.map_preimage, B.inclusion.map_preimage, B.inclusion.map_preimage]
    change jScheme ≫ pLs = gLscheme ≫ iLScheme
    exact hcompLScheme
  have hcompR : j ≫ pR = gR ≫ iLA := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (jleft ≫ pRleft) = B.inclusion.map (gRleft ≫ iLleft)
    rw [B.inclusion.map_comp, B.inclusion.map_comp]
    rw [B.inclusion.map_preimage, B.inclusion.map_preimage, B.inclusion.map_preimage]
    change jScheme ≫ pRs = gRscheme ≫ iLScheme
    exact hcompRScheme
  have hgen : yoneda.map j ≫ xL = yoneda.map j ≫ xR := by
    calc
      yoneda.map j ≫ xL = yoneda.map (j ≫ pL) ≫ ℓ.map := by simp [xL, Category.assoc]
      _ = yoneda.map (gL ≫ iLA) ≫ ℓ.map := by rw [hcompL]
      _ = yoneda.map gL ≫ e.square.generic := by
        simp [Category.assoc, iLA, iLleft, iLScheme, ℓ.generic_comm]
      _ = yoneda.map (gL ≫ e.genericOver) ≫ q.generic := by
        rw [e.generic_comm]
        simp [Category.assoc]
      _ = yoneda.map (gR ≫ e.genericOver) ≫ q.generic := by rw [hsameGeneric]
      _ = yoneda.map gR ≫ e.square.generic := by
        rw [e.generic_comm]
        simp [Category.assoc]
      _ = yoneda.map (gR ≫ iLA) ≫ ℓ.map := by
        simp [Category.assoc, iLA, iLleft, iLScheme, ℓ.generic_comm]
      _ = yoneda.map j ≫ xR := by rw [← hcompR]; simp [xR, Category.assoc]
  have hsame : xL = xR :=
    eq_of_agree_of_appTop_injective hf j hDaffine hjinj xL xR hxy hgen
  let toSch := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let rScheme : Spec (.of A) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom e.ringMap)
  have hspecialMap : toSch.map e.specialOver = rScheme := by
    change B.inclusion.map e.specialOver.left = rScheme
    exact e.specialOver_left
  have hsingle : Presieve.IsSheafFor X (Presieve.singleton e.specialOver) :=
    ((isSheaf_iff_isSheaf_of_type _ X).mp hX.isSheaf_fpqc).isSheafFor_of_mem_precoverage hcover
  rw [Presieve.isSheafFor_singleton] at hsingle
  have hmatch : ∀ {Z : AlgebraicGeometry.BigFppfOver B S hS} (u v : Z ⟶ Aobj),
      u ≫ e.specialOver = v ≫ e.specialOver →
      X.map u.op (yonedaEquiv ℓ.map) = X.map v.op (yonedaEquiv ℓ.map) := by
    intro Z u v huv
    let uScheme := toSch.map u
    let vScheme := toSch.map v
    have hcompat : uScheme ≫ rScheme = vScheme ≫ rScheme := by
      have h := congrArg toSch.map huv
      simpa [Functor.map_comp, hspecialMap] using h
    let pbIso := pullbackSpecIso R A A
    let tPB : toSch.obj Z ⟶ pullback rScheme rScheme := pullback.lift uScheme vScheme hcompat
    let tScheme : toSch.obj Z ⟶ Spec (.of T) := tPB ≫ pbIso.hom
    have htL : tScheme ≫ pLs = uScheme := by
      dsimp [tScheme, tPB, pbIso, pLs]
      rw [Category.assoc]
      change pullback.lift uScheme vScheme hcompat ≫
        (pullbackSpecIso R A A).hom ≫
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = uScheme
      rw [pullbackSpecIso_hom_fst]
      exact pullback.lift_fst _ _ _
    have htR : tScheme ≫ pRs = vScheme := by
      dsimp [tScheme, tPB, pbIso]
      calc
        pullback.lift uScheme vScheme hcompat ≫ ((pullbackSpecIso R A A).hom ≫ pRs) =
          pullback.lift uScheme vScheme hcompat ≫ pullback.snd rScheme rScheme := by
            congr 1
            change (pullbackSpecIso R A A).hom ≫
              Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) =
              pullback.snd rScheme rScheme
            exact pullbackSpecIso_hom_snd R A A
        _ = vScheme := pullback.lift_snd _ _ _
    have huBase : uScheme ≫ e.square.base = B.inclusion.map Z.hom := by
      change B.inclusion.map (Over.Hom.left u) ≫ e.square.base = B.inclusion.map Z.hom
      have h := congrArg B.inclusion.map (Over.w u)
      simpa [Aobj] using h
    let tLeft : Z.left ⟶ Dobj.left := B.inclusion.preimage tScheme
    have htbase : tLeft ≫ Dobj.hom = Z.hom := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, B.inclusion.map_preimage]
      change tScheme ≫ Dbase = B.inclusion.map Z.hom
      calc
        tScheme ≫ Dbase = tScheme ≫ pLs ≫ e.square.base := by rfl
        _ = uScheme ≫ e.square.base := by rw [← Category.assoc, htL]
        _ = B.inclusion.map Z.hom := huBase
    let tOver : Z ⟶ Dobj := Over.homMk tLeft htbase
    have htu : tOver ≫ pL = u := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change B.inclusion.map (tLeft ≫ pLleft) = B.inclusion.map u.left
      rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
      exact htL
    have htv : tOver ≫ pR = v := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change B.inclusion.map (tLeft ≫ pRleft) = B.inclusion.map v.left
      rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
      exact htR
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    apply congrArg yonedaEquiv
    calc
      yoneda.map u ≫ ℓ.map = yoneda.map tOver ≫ xL := by
        rw [← htu]
        simp [xL, Category.assoc]
      _ = yoneda.map tOver ≫ xR := by rw [hsame]
      _ = yoneda.map v ≫ ℓ.map := by
        rw [← htv]
        simp [xR, Category.assoc]
  obtain ⟨z, hz, -⟩ := hsingle (yonedaEquiv ℓ.map) hmatch
  let Robj := siteObject B S hS q.ring_mem q.base
  let m : yoneda.obj Robj ⟶ X := yonedaEquiv.symm z
  have hdescended : yoneda.map e.specialOver ≫ m = ℓ.map := by
    apply (yonedaEquiv : (yoneda.obj Aobj ⟶ X) ≃ X.obj (Opposite.op Aobj)).injective
    simpa [m, ← yonedaEquiv_naturality] using hz
  have hYinj := (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY.isSeparatedFor_fpqc hcover)
  have hspecial : m ≫ f = q.special := by
    apply yonedaEquiv.injective
    apply hYinj
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    apply congrArg yonedaEquiv
    calc
      yoneda.map e.specialOver ≫ (m ≫ f) = ℓ.map ≫ f := by
        rw [← Category.assoc, hdescended]
      _ = e.square.special := ℓ.special_comm
      _ = yoneda.map e.specialOver ≫ q.special := e.special_comm
  let Kobj := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  let iKR : Kobj ⟶ Robj := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem)
  have hcommOver : e.genericOver ≫ iKR = iLA ≫ e.specialOver :=
    dominatingExtension_genericOver_comp_eq q e _ _ rfl rfl
  have hXinj := (Presieve.isSeparatedFor_singleton (P := X)).mp
    (hX.isSeparatedFor_fpqc (dominatingExtension_genericOver_mem_fpqc q e))
  have hgeneric : yoneda.map iKR ≫ m = q.generic := by
    apply yonedaEquiv.injective
    apply hXinj
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    apply congrArg yonedaEquiv
    calc
      yoneda.map e.genericOver ≫ (yoneda.map iKR ≫ m) =
          yoneda.map iLA ≫ (yoneda.map e.specialOver ≫ m) := by
        simp only [← Functor.map_comp_assoc, hcommOver]
      _ = yoneda.map iLA ≫ ℓ.map := by rw [hdescended]
      _ = e.square.generic := ℓ.generic_comm
      _ = yoneda.map e.genericOver ≫ q.generic := e.generic_comm
  exact ⟨⟨m, hgeneric, hspecial⟩⟩

/-- **A dotted arrow of a valuative square is determined by its restriction to a dominating
extension.** If the valuative square of a dominating extension `e` of `q` has at most one dotted
arrow, then so does `q`; no hypothesis on the morphism is needed.

Two dotted arrows of `q`, restricted along the bottom edge `Spec A' ⟶ Spec A` of `e`, are dotted
arrows of `e.square`, hence agree there; that bottom edge is a one-element fpqc covering, so the
two arrows agree by the uniqueness half of the fpqc sheaf condition for `X`, Stacks 0APL. -/
public theorem subsingleton_lift_of_dominatingExtension
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (q : ValuativeSquare f) (e : q.DominatingExtension)
    (he : Subsingleton e.square.Lift) :
    Subsingleton q.Lift := by
  let Robj := siteObject B S hS q.ring_mem q.base
  let Kobj := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  let iKR : Kobj ⟶ Robj := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
      B.obj q.field_mem ⟶ B.obj q.ring_mem)
  let iLA : siteObject B S hS e.square.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K)) ≫ e.square.base) ⟶
      siteObject B S hS e.square.ring_mem e.square.base :=
    Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (algebraMap e.square.R e.square.K))) :
        B.obj e.square.field_mem ⟶ B.obj e.square.ring_mem)
  have hcommOver : e.genericOver ≫ iKR = iLA ≫ e.specialOver :=
    dominatingExtension_genericOver_comp_eq q e _ _ rfl rfl
  let restrict (l : q.Lift) : e.square.Lift :=
    { map := yoneda.map e.specialOver ≫ l.map
      generic_comm := by
        change yoneda.map iLA ≫ yoneda.map e.specialOver ≫ l.map = e.square.generic
        rw [← Category.assoc, ← Functor.map_comp, ← hcommOver, Functor.map_comp,
          Category.assoc]
        change yoneda.map e.genericOver ≫ yoneda.map iKR ≫ l.map = e.square.generic
        rw [e.generic_comm]
        exact congrArg (fun t => yoneda.map e.genericOver ≫ t) l.generic_comm
      special_comm := by
        rw [Category.assoc, l.special_comm, e.special_comm] }
  have hXinj := (Presieve.isSeparatedFor_singleton (P := X)).mp
    (hX.isSeparatedFor_fpqc (dominatingExtension_specialOver_mem_fpqc q e))
  refine ⟨fun l₁ l₂ => ?_⟩
  have hres : yoneda.map e.specialOver ≫ l₁.map = yoneda.map e.specialOver ≫ l₂.map :=
    congrArg ValuativeSquare.Lift.map (he.elim (restrict l₁) (restrict l₂))
  have hmap : l₁.map = l₂.map := by
    apply yonedaEquiv.injective
    apply hXinj
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv hres
  cases l₁
  cases l₂
  cases hmap
  rfl

/-- **For a separated morphism of algebraic spaces, allowing a dominating extension of the
valuation ring does not change the existence half of the valuative criterion**: the criterion
holds exactly when every valuative square already has a lift over the original valuation ring. -/
@[stacks 0A3W]
public theorem valuativeCriterion_existence_iff_lift_of_isSeparated
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hf : AlgebraicGeometry.Space.IsSeparated B S hS f) :
    ValuativeCriterion.Existence f ↔ ∀ q : ValuativeSquare f, Nonempty q.Lift where
  mp h q := by
    obtain ⟨e, he⟩ := h q
    exact exists_lift_of_dominatingExtension hX hY hf q e he
  mpr := valuativeCriterionExistence_of_forall_nonempty_lift f

end AlgebraicGeometry.Space

end
