module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSquareLocality
import all StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# Cartesianness of the image of a square from cartesianness over a covering of every base change

Let `F` be a presheaf on the big h site over `S` which is a Zariski sheaf, and consider a square
such that, for every base change of it, there is some Zariski covering of the new base over whose
members the image under `F` of the restricted square is cartesian. Then the image of the square
itself is cartesian. This is the passage from an affine base to an arbitrary one in the proof of
the sufficiency direction of Stacks 0EVF and in the proof of Stacks 0EVI.

## Main definitions

* `AlgebraicGeometry.BigHOver.IsLocallyCartesianSquare`: the hypothesis above.

## Main results

* `AlgebraicGeometry.BigHOver.isSeparatedSquare_of_isLocallyCartesianSquare`: every base change
  of such a square has jointly injective restriction maps.
* `AlgebraicGeometry.BigHOver.isPullback_of_isLocallyCartesianSquare`: the image of such a square
  is cartesian.

## Implementation notes

The restricted squares in `AlgebraicGeometry.BigHOver.IsLocallyCartesianSquare` are data —
arbitrary objects and morphisms whose squares over the members of the covering are cartesian —
rather than chosen fibre products.

## References

* [Stacks Project, Tag 0EVF](https://stacks.math.columbia.edu/tag/0EVF)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v)

/-- Restriction along an isomorphism of the site is injective on sections. -/
public theorem injective_map_op_of_isIso {A C : BigHOver B S hS} (g : A ⟶ C) [IsIso g] :
    Function.Injective (F.map g.op) :=
  ((isIso_iff_bijective (F.map g.op)).mp inferInstance).1

/-- Restricting along a composite is restricting twice. -/
public theorem map_op_comp_apply {A₁ A₂ A₃ : BigHOver B S hS} (g : A₁ ⟶ A₂) (h : A₂ ⟶ A₃)
    (x : F.obj (op A₃)) : F.map g.op (F.map h.op x) = F.map (g ≫ h).op x :=
  (F.map_comp_apply h.op g.op x).symm

/-- **The image of every base change of the square is cartesian over the members of some Zariski
covering of its base.** The restricted squares are given as data: objects and morphisms whose
squares over the members of the covering are cartesian over the square itself.

This is the hypothesis shared by the second step of the proof of Stacks 0EVI and by Interlude B
of the proof of the sufficiency direction of Stacks 0EVF. -/
public def IsLocallyCartesianSquare {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X)
    (d : E ⟶ X') (e : E ⟶ Z) : Prop :=
  ∀ (W : BigHOver B S hS) (w : W ⟶ X),
    ∃ C : PreZeroHypercover.{u + 1} W,
      ((C.map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj W)) ∧
      ∀ i, ∃ (X'i Zi Ei : BigHOver B S hS) (bi : X'i ⟶ C.X i) (zi : Zi ⟶ C.X i)
        (di : Ei ⟶ X'i) (ei : Ei ⟶ Zi) (qb : X'i ⟶ X') (qz : Zi ⟶ Z) (qe : Ei ⟶ E),
        IsPullback qb bi b (C.f i ≫ w) ∧ IsPullback qz zi z (C.f i ≫ w) ∧
          di ≫ qb = qe ≫ d ∧ ei ≫ qz = qe ≫ e ∧
          IsPullback (F.map zi.op) (F.map bi.op) (F.map ei.op) (F.map di.op)

/-- Equality of restrictions to one base change of a morphism gives it for any other. -/
private theorem map_op_eq_of_isPullback {A P P' W X' : BigHOver B S hS} (f : A ⟶ X') (w : W ⟶ X')
    {q : P ⟶ A} {a : P ⟶ W} {q' : P' ⟶ A} {a' : P' ⟶ W}
    (h1 : IsPullback q a f w) (h2 : IsPullback q' a' f w) {s t : F.obj (op W)}
    (h : F.map a.op s = F.map a.op t) : F.map a'.op s = F.map a'.op t := by
  refine injective_map_op_of_isIso B S hS F (h1.isoIsPullback _ _ h2).hom ?_
  rwa [map_op_comp_apply, map_op_comp_apply, h1.isoIsPullback_hom_snd _ _ h2]

/-- **Joint injectivity transports between two base changes of the same square**: if two squares
over `W` are both base changes of the square along `w : W ⟶ X`, and the restriction maps of one
are jointly injective, then so are those of the other. -/
public theorem isSeparatedSquare_of_isPullback_of_isSeparatedSquare
    {X X' Z W W' Wz V' Vz : BigHOver B S hS} {b : X' ⟶ X} {z : Z ⟶ X} {w : W ⟶ X}
    {bw : W' ⟶ W} {zw : Wz ⟶ W} {qbw : W' ⟶ X'} {qzw : Wz ⟶ Z}
    {bv : V' ⟶ W} {zv : Vz ⟶ W} {qbv : V' ⟶ X'} {qzv : Vz ⟶ Z}
    (hw1 : IsPullback qbw bw b w) (hw2 : IsPullback qzw zw z w)
    (hv1 : IsPullback qbv bv b w) (hv2 : IsPullback qzv zv z w)
    (h : IsSeparatedSquare B S hS F bv zv) :
    IsSeparatedSquare B S hS F bw zw := by
  intro s t hb hz
  exact h s t (map_op_eq_of_isPullback B S hS F b w hw1 hv1 hb)
    (map_op_eq_of_isPullback B S hS F z w hw2 hv2 hz)

/-- **Every base change of a locally cartesian square has jointly injective restriction maps**, for
a Zariski sheaf `F`: the restriction maps of the base change of the square along an arbitrary
morphism of the site are jointly injective. -/
public theorem isSeparatedSquare_of_isLocallyCartesianSquare
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    {X X' Z E : BigHOver B S hS} {b : X' ⟶ X} {z : Z ⟶ X} {d : E ⟶ X'} {e : E ⟶ Z}
    (hloc : IsLocallyCartesianSquare B S hS F b z d e)
    (W W' Wz : BigHOver B S hS) (w : W ⟶ X) (bw : W' ⟶ W) (zw : Wz ⟶ W)
    (qbw : W' ⟶ X') (qzw : Wz ⟶ Z) (hb : IsPullback qbw bw b w) (hz : IsPullback qzw zw z w) :
    IsSeparatedSquare B S hS F bw zw := by
  obtain ⟨C, hC, hdata⟩ := hloc W w
  choose X'i Zi Ei bi zi di ei qb qz qe hqb hqz hqd hqe hcart using hdata
  have hbfac (i : C.I₀) : qb i ≫ b = (bi i ≫ C.f i) ≫ w :=
    (hqb i).w.trans (Category.assoc _ _ _).symm
  have hzfac (i : C.I₀) : qz i ≫ z = (zi i ≫ C.f i) ≫ w :=
    (hqz i).w.trans (Category.assoc _ _ _).symm
  exact isSeparatedSquare_of_zariskiCover B S hS F hzar bw zw C hC X'i Zi bi zi
    (fun i => hb.lift (qb i) (bi i ≫ C.f i) (hbfac i))
    (fun i => hz.lift (qz i) (zi i ≫ C.f i) (hzfac i))
    (fun i => (hb.lift_snd _ _ (hbfac i)).symm) (fun i => (hz.lift_snd _ _ (hzfac i)).symm)
    fun i s t hs ht => ((Limits.Types.isPullback_iff _ _ _ _).1 (hcart i)).2.1 s t ⟨ht, hs⟩

/-- **The image of a locally cartesian square is cartesian.** If a presheaf on the big h category
over `S` is a sheaf for the Zariski topology and the image of every base change of a square is
cartesian over the members of some Zariski covering of its base, then the image of the square
itself is cartesian.

This is the second step of the proof of Stacks 0EVI and Interlude B of the proof of the
sufficiency direction of Stacks 0EVF, in the one form both need. -/
public theorem isPullback_of_isLocallyCartesianSquare
    (hzar : BigHOver.IsZariskiSheaf B S hS F)
    {X X' Z E : BigHOver B S hS} (b : X' ⟶ X) (z : Z ⟶ X) (d : E ⟶ X') (e : E ⟶ Z)
    (hw : e ≫ z = d ≫ b) (hloc : IsLocallyCartesianSquare B S hS F b z d e) :
    IsPullback (F.map z.op) (F.map b.op) (F.map e.op) (F.map d.op) := by
  have : HasPullbacks B.Schemes := inferInstance
  let _ := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  let _ : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
    inferInstance
  obtain ⟨C, hC, hdata⟩ := hloc X (𝟙 X)
  choose X'i Zi Ei bi zi di ei qb qz qe hqb hqz hqd hqe hcart using hdata
  simp only [Category.comp_id] at hqb hqz
  have hcov {Y : BigHOver B S hS} (g : Y ⟶ X) (Yi : C.I₀ → BigHOver B S hS)
      (gi : ∀ i, Yi i ⟶ C.X i) (qg : ∀ i, Yi i ⟶ Y)
      (hqg : ∀ i, IsPullback (qg i) (gi i) g (C.f i)) :
      ((PreZeroHypercover.mk C.I₀ Yi qg).map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Y) := by
    refine PreZeroHypercover.presieve₀_mem_of_iso
      (PreZeroHypercover.isoMk (Equiv.refl C.I₀)
        (fun i => ((BigHOver.toScheme B S hS).mapIso
          ((hqg i).isoIsPullback _ _ (IsPullback.of_hasPullback (C.f i) g).flip)).symm)
        fun i => congrArg (BigHOver.toScheme B S hS).map
          ((hqg i).isoIsPullback_inv_fst _ _ (IsPullback.of_hasPullback (C.f i) g).flip))
      (zariskiPrecoverage_pullback₂ C hC g)
  exact isPullback_of_zariskiCover B S hS F hzar b z d e hw
    (fun W W' Wz w bw zw qbw qzw h1 h2 =>
      isSeparatedSquare_of_isLocallyCartesianSquare B S hS F hzar hloc W W' Wz w bw zw qbw qzw
        h1 h2)
    C hC X'i Zi Ei bi zi di ei qb qz qe hqb hqz hqd hqe
    (hcov b X'i bi qb hqb) (hcov z Zi zi qz hqz) hcart

end BigHOver

end AlgebraicGeometry

end
