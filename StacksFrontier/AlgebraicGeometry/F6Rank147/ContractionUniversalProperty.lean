module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Topology.Maps.SubmersiveClosed
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction

/-!
# Factoring a morphism through a contraction

Let `b : X ⟶ X'` be a morphism of schemes which is an isomorphism over the complement of a
closed point `x` of `X'`, and let `φ : X ⟶ Y` be a morphism which is constant on the fibre of
`b` over `x`. Then `φ` factors uniquely through `b`. This is the universal property of the
contraction of an exceptional curve of the first kind, and it is proved here in the generality
in which the argument runs: the only facts used about the pair `(b, x)` are that `b` restricts
to an isomorphism away from `x`, that `b` is a closed map, that `x` is in the image of `b`, and
that the comparison map `b.c` of structure sheaves is an isomorphism.

The proof separates into three independent steps. First, `φ` factors through `b` *as a function*:
away from the fibre over `x` the morphism `b` is injective, and on that fibre `φ` is constant by
hypothesis. Second, a closed surjection is a quotient map, so the factorisation is continuous.
Third, the factorisation is upgraded to a morphism of schemes: the sheaf component of the
candidate is forced by `φ.c` and the inverse of `b.c`, locality of the stalk maps is inherited
from `φ`, and uniqueness holds because `b.c` is a monomorphism.

## Main results

* `AlgebraicGeometry.existsUnique_comp_eq_of_isQuotientMap_of_isIso_c` — a morphism that is a
  topological quotient map and an isomorphism on structure sheaves is initial among morphisms
  that factor through it setwise.
* `AlgebraicGeometry.existsUnique_comp_eq_of_isIso_morphismRestrict_compl` — the universal
  property above, for a closed map which is an isomorphism away from a closed point.
* `AlgebraicGeometry.isIso_c_of_isIso_morphismRestrict` — `b.c` is an isomorphism as soon as `b`
  is an isomorphism over an open `U` whose inclusion has an invertible comparison map and whose
  inverse image has a monomorphic one.
* `AlgebraicGeometry.Scheme.IdealSheafData.isFiniteType_vanishingIdeal` — on a Noetherian scheme
  every vanishing ideal sheaf of a closed set is of finite type.
* `AlgebraicGeometry.exists_const_on_fibre_of_const_on_subscheme`,
  `AlgebraicGeometry.factorsThrough_of_isIso_morphismRestrict_compl` and
  `AlgebraicGeometry.surjective_of_isClosedMap_of_isIso_morphismRestrict_compl` — the three
  inputs of the universal property: being constant on the exceptional subscheme is being
  constant on the fibre over the centre, such a morphism factors setwise, and a closed morphism
  which is an isomorphism off a non-maximal closed point is surjective.

## References

* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Finite type of a vanishing ideal -/

/-- On a Noetherian scheme the vanishing ideal sheaf of a closed subset is of finite type: its
ideal on an affine open is an ideal of a Noetherian ring. -/
public theorem Scheme.IdealSheafData.isFiniteType_vanishingIdeal {Z : Scheme.{u}}
    [IsNoetherian Z] (T : Closeds Z) :
    Scheme.IdealSheafData.IsFiniteType (Scheme.IdealSheafData.vanishingIdeal T) := by
  intro U
  let _ := IsLocallyNoetherian.component_noetherian U
  exact Ideal.fg_of_isNoetherianRing _

/-! ### Recognising an isomorphism of structure sheaves -/

/-- If `b` is an isomorphism over an open `U` of the target, the comparison map of the inclusion
of `U` is an isomorphism and that of the inclusion of `b ⁻¹ᵁ U` is a monomorphism, then the
comparison map of `b` is an isomorphism. -/
public theorem isIso_c_of_isIso_morphismRestrict
    {X Z : Scheme.{u}} (b : X ⟶ Z) (U : Z.Opens)
    [IsIso (b ∣_ U)] [IsIso U.ι.c] [Mono (b ⁻¹ᵁ U).ι.c] : IsIso b.c := by
  let j := (b ⁻¹ᵁ U).ι
  have hcomp : IsIso (j ≫ b).c := by
    rw [← morphismRestrict_ι b U]
    change IsIso (U.ι.c ≫
      (TopCat.Presheaf.pushforward CommRingCat U.ι.base).map (b ∣_ U).c)
    infer_instance
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun V => ?_
  let f := b.c.app V
  let g := j.c.app (Opposite.op ((Opens.map b.base).obj V.unop))
  have : IsIso (f ≫ g) := NatIso.isIso_app_of_isIso (j ≫ b).c V
  have : Mono g := (NatTrans.mono_iff_mono_app j.c).mp inferInstance _
  have : IsSplitEpi g := ⟨⟨⟨inv (f ≫ g) ≫ f, by simp [Category.assoc]⟩⟩⟩
  have : IsIso g := isIso_of_mono_of_isSplitEpi g
  exact IsIso.of_isIso_comp_right f g

/-! ### Factoring as a function -/

/-- A morphism which is constant on the closed subscheme cut out by an ideal sheaf takes the
same value at every point of the support of that ideal sheaf. -/
public theorem eq_of_mem_support_of_const_on_subscheme
    {X Y : Scheme.{u}} (D : X.IdealSheafData) (φ : X ⟶ Y)
    (hφ : ∃ y : Y, ∀ z : D.subscheme, φ (D.subschemeι z) = y)
    {x : X} (hx : x ∈ D.support) : φ x = Classical.choose hφ := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range D.subschemeι := by
    rw [D.range_subschemeι]; exact hx
  exact Classical.choose_spec hφ z

/-- For a morphism whose contracted ideal sheaf is the inverse image of the vanishing ideal of a
closed point `x`, being constant on the associated closed subscheme is the same as being constant
on the fibre over `x`. -/
public theorem exists_const_on_fibre_of_const_on_subscheme
    {X X' Y : Scheme.{u}} (D : X.IdealSheafData) (b : X ⟶ X') (φ : X ⟶ Y)
    (x : X') (hx : IsClosed ({x} : Set X'))
    (hD : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X')).comap b)
    (hφ : ∃ y : Y, ∀ z : D.subscheme, φ (D.subschemeι z) = y) :
    ∃ y : Y, ∀ z : X, b z = x → φ z = y := by
  classical
  refine ⟨Classical.choose hφ, fun z hz => eq_of_mem_support_of_const_on_subscheme D φ hφ ?_⟩
  change z ∈ (D.support : Set X)
  rw [hD, Scheme.IdealSheafData.support_comap]
  change b z ∈
    ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X')).support : Set X')
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hz

/-- A morphism constant on the fibre over a closed point factors through a morphism that is an
isomorphism over the complement of that point. -/
public theorem factorsThrough_of_isIso_morphismRestrict_compl
    {X Z Y : Scheme.{u}} (b : X ⟶ Z) (φ : X ⟶ Y) (x : Z) (hx : IsClosed ({x} : Set Z))
    (hIso : IsIso (b ∣_ (⟨({x} : Set Z)ᶜ, hx.isOpen_compl⟩ : Z.Opens)))
    (hφ : ∃ y : Y, ∀ z : X, b z = x → φ z = y) :
    Function.FactorsThrough φ b := by
  obtain ⟨y, hy⟩ := hφ
  intro z w hzw
  by_cases hz : b z = x
  · exact (hy z hz).trans (hy w (hzw.symm.trans hz)).symm
  · let U : Z.Opens := ⟨({x} : Set Z)ᶜ, hx.isOpen_compl⟩
    have hzU : z ∈ b ⁻¹ᵁ U := hz
    have hwU : w ∈ b ⁻¹ᵁ U := fun hw => hz (hzw.trans hw)
    let f := b ∣_ U
    have hf : Function.Injective f.base := by
      let _ : IsIso f := hIso
      exact (TopCat.mono_iff_injective f.base).mp inferInstance
    have hfg : f.base ⟨z, hzU⟩ = f.base ⟨w, hwU⟩ :=
      Subtype.ext ((morphismRestrict_base_coe b U ⟨z, hzU⟩).trans
        (hzw.trans (morphismRestrict_base_coe b U ⟨w, hwU⟩).symm))
    exact congrArg φ (congrArg Subtype.val (hf hfg))

/-! ### Surjectivity -/

/-- A closed morphism which is an isomorphism over the complement of a closed point `x` is
surjective as soon as `x` is not a maximal point of the target, for instance when the local ring
at `x` has positive Krull dimension. -/
public theorem surjective_of_isClosedMap_of_isIso_morphismRestrict_compl
    {X Z : Scheme.{u}} (b : X ⟶ Z) (hclosed : IsClosedMap b.base)
    (x : Z) (hx : IsClosed ({x} : Set Z)) (hdim : ringKrullDim (Z.presheaf.stalk x) ≠ 0)
    (hoff : IsIso (b ∣_ (⟨({x} : Set Z)ᶜ, hx.isOpen_compl⟩ : Z.Opens))) :
    Surjective b := by
  classical
  let U : Z.Opens := ⟨({x} : Set Z)ᶜ, hx.isOpen_compl⟩
  have := hoff
  have hoffRange (y : Z) (hy : y ≠ x) : y ∈ Set.range b := by
    obtain ⟨xU, hxU⟩ := (b ∣_ U).surjective (⟨y, hy⟩ : U.toScheme)
    refine ⟨(b ⁻¹ᵁ U).ι xU, ?_⟩
    have hw := congrArg (fun f => f xU) (morphismRestrict_ι b U)
    change U.ι ((b ∣_ U) xU) = b ((b ⁻¹ᵁ U).ι xU) at hw
    simpa [hxU] using hw.symm
  have hxRange : x ∈ Set.range b := by
    by_contra hnot
    have hcompl : (Set.range b)ᶜ = {x} := by
      ext y
      refine ⟨fun hy => by by_contra hyx; exact hy (hoffRange y hyx), ?_⟩
      rintro rfl; exact hnot
    have hopen : IsOpen ({x} : Set Z) := by
      rw [← hcompl]; exact hclosed.isClosed_range.isOpen_compl
    have hmax : IsMax x := fun y hxy => by
      have hy : y = x := (hxy : y ⤳ x).mem_open hopen rfl
      simp [hy]
    refine hdim ?_
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr hmax]
    rfl
  exact (surjective_iff b).mpr fun y => if hy : y = x then hy ▸ hxRange else hoffRange y hy

/-! ### The factorisation -/

/-- A continuous map factors uniquely through a topological quotient map through which it
factors setwise. -/
private theorem existsUnique_continuous_comp_eq
    {X X' Y : Scheme.{u}} (b : X ⟶ X') (φ : X ⟶ Y)
    (hb : Topology.IsQuotientMap b.base)
    (hφ : Function.FactorsThrough φ b) :
    ∃! ψ : TopCat.of X' ⟶ TopCat.of Y,
      TopCat.ofHom ⟨b.base, Scheme.Hom.continuous b⟩ ≫ ψ =
        TopCat.ofHom ⟨φ.base, Scheme.Hom.continuous φ⟩ := by
  let fφ : C(X, Y) := ⟨fun x => φ x, Scheme.Hom.continuous φ⟩
  let hFib : ∀ x x' : X, b x = b x' → fφ x = fφ x' := fun x x' hxx' => @hφ x x' hxx'
  let ψ : X' → Y := hb.lift fφ hFib
  have hcomp : (fun x : X => ψ (b x)) = (fun x => fφ x) :=
    congrArg (fun f : C(X, Y) => (f : X → Y)) (hb.lift_comp fφ hFib)
  have hψ : Continuous ψ := by
    apply hb.continuous_iff.mpr
    change Continuous (fun x : X => ψ (b x))
    rw [hcomp]
    exact fφ.continuous
  refine ⟨TopCat.ofHom ⟨ψ, hψ⟩, TopCat.ext (congrFun hcomp), fun ψ' hψ' => TopCat.ext fun x => ?_⟩
  obtain ⟨x, rfl⟩ := hb.surjective x
  exact (congrArg (fun f : TopCat.of X ⟶ TopCat.of Y => f x) hψ').trans (congrFun hcomp x).symm

/-- A morphism of presheafed spaces whose sheaf comparison map is an isomorphism is initial, at
the level of presheafed spaces, among the morphisms out of its source that factor through it on
the underlying spaces: the sheaf component of the factorisation is forced. -/
private theorem exists_presheafedSpace_hom_comp_eq
    {A B C : PresheafedSpace.{u} CommRingCat.{u}} (b : A ⟶ B) [IsIso b.c]
    (f : A ⟶ C) (t : (B : TopCat) ⟶ (C : TopCat)) (ht : b.base ≫ t = f.base) :
    ∃ g : B ⟶ C, g.base = t ∧ b ≫ g = f := by
  have key : ∀ m : C.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat t).obj
        ((TopCat.Presheaf.pushforward CommRingCat b.base).obj A.presheaf),
      (m ≫ (TopCat.Presheaf.pushforward CommRingCat t).map (inv b.c)) ≫
        (TopCat.Presheaf.pushforward CommRingCat t).map b.c = m := fun m => by
    rw [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  obtain ⟨fb, fc⟩ := f
  dsimp only at ht
  subst ht
  refine ⟨⟨t, fc ≫ (TopCat.Presheaf.pushforward CommRingCat t).map (inv b.c)⟩, rfl, ?_⟩
  exact PresheafedSpace.hext _ _ rfl (heq_of_eq (key fc))

/-- Two morphisms of presheafed spaces out of the target of a morphism whose sheaf comparison
map is an isomorphism agree as soon as they agree on the base and after composing with that
morphism. -/
private theorem presheafedSpace_hom_ext_of_comp_eq
    {A B C : PresheafedSpace.{u} CommRingCat.{u}}
    (b : A ⟶ B) [IsIso b.c] (f g : B ⟶ C)
    (hbase : f.base = g.base) (hcomp : b ≫ f = b ≫ g) : f = g := by
  obtain ⟨fb, fc⟩ := f
  obtain ⟨gb, gc⟩ := g
  dsimp only at hbase
  subst hbase
  refine PresheafedSpace.hext _ _ rfl (heq_of_eq ?_)
  have h : fc ≫ (TopCat.Presheaf.pushforward CommRingCat fb).map b.c =
      gc ≫ (TopCat.Presheaf.pushforward CommRingCat fb).map b.c := by
    injection hcomp
  exact (cancel_mono _).mp h

/-- **The universal property of a topological quotient which is an isomorphism on structure
sheaves.** If `b : X ⟶ X'` is a quotient map on points and its comparison map of structure
sheaves is an isomorphism, then every morphism `φ : X ⟶ Y` that factors through `b` setwise
factors through `b` uniquely as a morphism of schemes. -/
public theorem existsUnique_comp_eq_of_isQuotientMap_of_isIso_c
    {X X' Y : Scheme.{u}} (b : X ⟶ X') (φ : X ⟶ Y)
    (hQuot : Topology.IsQuotientMap b.base)
    (hFactor : Function.FactorsThrough φ b)
    (hO : IsIso b.c) :
    ∃! ψ : X' ⟶ Y, b ≫ ψ = φ := by
  obtain ⟨ψTop, hψTop, hψTopUnique⟩ := existsUnique_continuous_comp_eq b φ hQuot hFactor
  obtain ⟨ψP, hψPbase, hψP⟩ :=
    exists_presheafedSpace_hom_comp_eq b.toPshHom φ.toPshHom ψTop hψTop
  have hlocal : ∀ x' : X', IsLocalHom (ψP.stalkMap x').hom := by
    intro x'
    obtain ⟨x, rfl⟩ := hQuot.surjective x'
    have hφlocal : IsLocalHom ((φ.toPshHom).stalkMap x).hom := φ.toLRSHom.prop x
    rw [← hψP, PresheafedSpace.stalkMap.comp] at hφlocal
    let _ : IsLocalHom (((b.toPshHom).stalkMap x).hom.comp (ψP.stalkMap (b x)).hom) := hφlocal
    exact isLocalHom_of_comp (ψP.stalkMap (b x)).hom ((b.toPshHom).stalkMap x).hom
  refine ⟨⟨⟨ψP, hlocal⟩⟩, ?_, ?_⟩
  · exact Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' hψP)
  · intro ψ' hψ'
    have htop : ψ'.toPshHom.base = ψP.base := by
      rw [hψPbase]
      exact hψTopUnique _ (congrArg (fun f : X ⟶ Y => f.toPshHom.base) hψ')
    apply Scheme.Hom.ext'
    apply LocallyRingedSpace.Hom.ext'
    refine presheafedSpace_hom_ext_of_comp_eq b.toPshHom _ _ htop ?_
    rw [hψP]
    exact congrArg (fun f : X ⟶ Y => f.toPshHom) hψ'

/-- **The universal property of a contraction.** A closed morphism `b : X ⟶ X'` which is an
isomorphism over the complement of a closed point `x` whose local ring has positive Krull
dimension, and whose comparison map of structure sheaves is an isomorphism, is initial among
morphisms out of `X` that are constant on the fibre of `b` over `x`. -/
public theorem existsUnique_comp_eq_of_isIso_morphismRestrict_compl
    {X X' Y : Scheme.{u}} (b : X ⟶ X') (φ : X ⟶ Y)
    (hclosed : IsClosedMap b.base) (x : X') (hx : IsClosed ({x} : Set X'))
    (hdim : ringKrullDim (X'.presheaf.stalk x) ≠ 0)
    (hoff : IsIso (b ∣_ (⟨({x} : Set X')ᶜ, hx.isOpen_compl⟩ : X'.Opens)))
    (hO : IsIso b.c)
    (hφ : ∃ y : Y, ∀ z : X, b z = x → φ z = y) :
    ∃! ψ : X' ⟶ Y, b ≫ ψ = φ := by
  exact existsUnique_comp_eq_of_isQuotientMap_of_isIso_c b φ
    (hclosed.isQuotientMap (Scheme.Hom.continuous b) ((surjective_iff b).mp
      (surjective_of_isClosedMap_of_isIso_morphismRestrict_compl b hclosed x hx hdim hoff)))
    (factorsThrough_of_isIso_morphismRestrict_compl b φ x hx hoff hφ) hO

end AlgebraicGeometry

end
