module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference

/-!
# The obstruction to mapping extensions across a first order thickening

For two extensions of modules over a first order thickening of ringed topoi, compatible maps on
their quotient and kernel modules admit a lift to the middle terms precisely when an obstruction
class in the first Ext group over the quotient structure sheaf vanishes.

The obstruction extension is the cokernel of
`Deformation.ToposThickening.differenceRelation`, descended along the structure map: a section
of the square-zero ideal annihilates that cokernel, because multiplying a section of the twisted
pullback by such a section lands in the image of the kernel of the first extension. The
obstruction class is the negative of the Ext class of the descended extension, and it vanishes
exactly when the extension splits, which by
`Deformation.ToposThickening.difference_retraction_iff` is exactly the existence of a lift.

## Main definitions

* `Deformation.ToposThickening.ObstructionExtension` and
  `Deformation.ToposThickening.obstructionExtension`: the extension of the first quotient by the
  second kernel, over the quotient structure sheaf, whose retractions are the lifts.
* `Deformation.ToposThickening.obstructionClass`: the obstruction class in the first Ext group.

## Main results

* `Deformation.ToposThickening.obstructionClass_eq_zero_iff`: the lifting criterion.

## Implementation notes

`ObstructionExtension` bundles the descended extension with the correspondence between its
retractions and the lifts, so that `obstructionClass` depends on no further choice than the
one made by `obstructionExtension`.

## References

* [Stacks Project, Tag 08MD](https://stacks.math.columbia.edu/tag/08MD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

/-- The class of `a ⊗ y` in the sheafified tensor product of the square-zero ideal with `M`. -/
private noncomputable def idealTensorUnit (D : TwoExtensions i)
    (M : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (V : Y.Cᵒᵖ) (a : D.thickening.I.val.obj V) (y : M.val.obj V) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj
      X.O)).obj)).unit.app
    (PresheafOfModules.tensorObj D.thickening.I.val M.val)).app V
    (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj V] y)

/-- Equal morphisms of sheaves of modules agree on sections. -/
private lemma sheafModule_hom_app_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w'}} {M N : SheafOfModules.{w'} R} {u v : M ⟶ N} (h : u = v)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    u.val.app V x = v.val.app V x := by
  subst h
  rfl

/-- The local section of the kernel of the first extension produced by multiplying a lift of a
section of the first quotient by a section of the square-zero ideal. -/
private noncomputable def differenceIdealLift (D : TwoExtensions i) (V : Y.Cᵒᵖ)
    (a : D.thickening.I.val.obj V) (y : D.F.val.obj V) : D.K.val.obj V :=
  D.firstActionMap.1.val.app V (idealTensorUnit D D.F V a y)

/-- Multiplying a section of the twisted pullback by a section of the square-zero ideal lands in
the image of the kernel of the first extension. -/
private lemma difference_smul_eq_relation
    (D : TwoExtensions i) (h : CompatibleActions D)
    (V : Y.Cᵒᵖ) (a : D.thickening.I.val.obj V)
    (x : (pullback (differenceCospanFst D) D.secondExtension.g).val.obj V) :
    (show ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).obj Y.O).obj.obj V from
        D.thickening.incl.val.app V a) • x =
      (differenceRelation D).val.app V
        (differenceIdealLift D V a (D.firstExtension.g.val.app V
          ((pullback.fst (differenceCospanFst D) D.secondExtension.g).val.app V x))) := by
  let ρ := (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let R := SheafOfModules.restrictScalars ρ
  let f := differenceCospanFst D
  let g := D.secondExtension.g
  let p := pullback.fst f g
  let s := pullback.snd f g
  let j := differenceRelation D
  have hjp : j ≫ p = D.firstExtension.f := pullback.lift_fst _ _ _
  have hjs : j ≫ s = R.map D.kernelMap ≫ D.secondExtension.f := pullback.lift_snd _ _ _
  have hps : p ≫ f = s ≫ g := pullback.condition
  let k := differenceIdealLift D V a (D.firstExtension.g.val.app V (p.val.app V x))
  apply pullback_sections_ext f g V
  · rw [(p.val.app V).hom.map_smul]
    have hp : p.val.app V (j.val.app V k) = D.firstExtension.f.val.app V k :=
      sheafModule_hom_app_congr hjp V k
    exact ((D.firstActionMap.2 V a (p.val.app V x)).symm).trans hp.symm
  · rw [(s.val.app V).hom.map_smul]
    have hs : s.val.app V (j.val.app V k) =
        D.secondExtension.f.val.app V (D.kernelMap.val.app V k) :=
      sheafModule_hom_app_congr hjs V k
    rw [hs]
    have he : D.quotientMap.val.app V (D.firstExtension.g.val.app V (p.val.app V x)) =
        D.secondExtension.g.val.app V (s.val.app V x) :=
      sheafModule_hom_app_congr hps V x
    have hc := (h V a (D.firstExtension.g.val.app V (p.val.app V x))).trans
        (congrArg (fun z => D.secondActionMap.1.val.app V (idealTensorUnit D D.G V a z)) he)
    exact ((D.secondActionMap.2 V a (s.val.app V x)).symm).trans
      (congrArg (fun z => D.secondExtension.f.val.app V z) hc.symm)

/-- Multiplication by a section of the square-zero ideal kills the image in the difference
cokernel of a section of the twisted pullback. The ideal section is given through an arbitrary
section of the structure sheaf equal to its image, so that the statement applies without a
rewrite at a use site that produced the scalar in another form. -/
lemma difference_cokernel_smul_image
    (D : TwoExtensions i) (h : CompatibleActions D)
    (V : Y.Cᵒᵖ) (c : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V)
    (a : D.thickening.I.val.obj V)
    (hc : (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V from
      D.thickening.incl.val.app V a) = c)
    (x : (pullback (differenceCospanFst D) D.secondExtension.g).val.obj V) :
    (show ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).obj Y.O).obj.obj V from c) •
      (cokernel.π (differenceRelation D)).val.app V x = 0 := by
  subst hc
  refine ((((cokernel.π (differenceRelation D)).val.app V).hom.map_smul _ x).symm).trans ?_
  refine (congrArg ((cokernel.π (differenceRelation D)).val.app V)
    (difference_smul_eq_relation D h V a x)).trans ?_
  exact sheafModule_hom_app_congr (cokernel.condition (differenceRelation D)) V _

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] in
/-- A section of the structure sheaf in the kernel of the structure map stays in that kernel
after restriction. -/
private lemma fSharp_app_restrict_eq_zero
    (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (hr : i.fSharp.hom.app U r = 0) (V : Y.C) (t : V ⟶ U.unop) :
    i.fSharp.hom.app (Opposite.op V)
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map t.op r) = 0 := by
  have he := ConcreteCategory.congr_hom (i.fSharp.hom.naturality t.op) r
  change i.fSharp.hom.app (Opposite.op V) (Y.O.obj.map t.op r) = 0
  exact he.trans ((congrArg
    (fun x => ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.map t.op x)
      hr).trans (map_zero _))

private lemma difference_cokernel_smul_restrict
    (D : TwoExtensions i) (h : CompatibleActions D)
    (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (hr : i.fSharp.hom.app U r = 0) (V : Y.C) (t : V ⟶ U.unop)
    (x : (pullback (differenceCospanFst D) D.secondExtension.g).val.obj (Opposite.op V)) :
    (show ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).obj Y.O).obj.obj (Opposite.op V) from
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map t.op r) •
      (cokernel.π (differenceRelation D)).val.app (Opposite.op V) x = 0 := by
  have hex := D.thickening.exists_ideal_section (Opposite.op V)
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map t.op r)
    (fSharp_app_restrict_eq_zero U r hr V t)
  obtain ⟨a, ha⟩ := hex
  exact difference_cokernel_smul_image D h (Opposite.op V) _ a ha x

/-- Every section of the structure sheaf in the kernel of the structure map kills the
difference cokernel. -/
lemma difference_cokernel_annihilated
    (D : TwoExtensions i) (h : CompatibleActions D)
    (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (hr : i.fSharp.hom.app U r = 0)
    (z : (cokernel (differenceRelation D)).val.obj U) :
    (show ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).obj Y.O).obj.obj U from r) •
      z = 0 := by
  have := sheafModule_epi_locallySurjective (cokernel.π (differenceRelation D))
  exact smul_eq_zero_of_locallySurjective (cokernel.π (differenceRelation D)) U r z
    (difference_cokernel_smul_restrict D h U r hr)

/-- The obstruction extension of two extensions over a first order thickening: an extension of
the first quotient by the second kernel, over the quotient structure sheaf, whose splittings are
exactly the lifts of the prescribed maps on the end terms. -/
structure ObstructionExtension (D : TwoExtensions i) where
  /-- The middle term of the obstruction extension. -/
  middle : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- The injection of the second kernel. -/
  ι : D.L ⟶ middle
  /-- The projection onto the first quotient. -/
  π : middle ⟶ D.F
  /-- The two maps compose to zero. -/
  zero : ι ≫ π = 0
  /-- The resulting short complex is short exact. -/
  shortExact : (ShortComplex.mk ι π zero).ShortExact
  /-- Retractions of the injection correspond to lifts of the prescribed end maps. -/
  retraction_iff : (∃ r : middle ⟶ D.L, ι ≫ r = 𝟙 _) ↔
    ∃ t : D.firstExtension.Z.left ⟶ D.secondExtension.Z.left, IsExtensionLift D t

/-- Construction of the obstruction extension from the difference cokernel: it is annihilated
by the square-zero ideal, hence descends along the structure map. -/
noncomputable def obstructionExtension
    (D : TwoExtensions i) (h : CompatibleActions D) :
    ObstructionExtension D := by
  apply Classical.choice
  let ρ := (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let R := SheafOfModules.restrictScalars ρ
  let S₁ := ShortComplex.mk D.firstExtension.f D.firstExtension.g
    (yonedaExtension_comp_zero D.firstExtension)
  let S₂ := ShortComplex.mk D.secondExtension.f D.secondExtension.g
    (yonedaExtension_comp_zero D.secondExtension)
  have h₂ : S₂.ShortExact := yonedaExtension_shortExact D.secondExtension
  let φ := R.map D.quotientMap
  let p := pullback.fst (S₁.g ≫ φ) S₂.g
  let l := pullback.lift (f := S₁.g ≫ φ) (g := S₂.g) (0 : S₂.X₁ ⟶ S₁.X₂)
    S₂.f (by simp)
  let j := differenceRelation D
  let q := cokernel.π j
  have hjp : j ≫ p = S₁.f := pullback.lift_fst _ _ _
  have hlp : l ≫ p = 0 := pullback.lift_fst _ _ _
  have hP : (ShortComplex.mk l p hlp).ShortExact :=
    differencePullback_shortExact (S₁ := S₁) h₂ φ
  let a := l ≫ q
  let b := cokernel.desc j (p ≫ S₁.g) (by rw [← Category.assoc, hjp, S₁.zero])
  have hab : a ≫ b = 0 := by
    dsimp only [a, b, q]
    rw [Category.assoc, cokernel.π_desc, ← Category.assoc, hlp, zero_comp]
  have hH : (ShortComplex.mk a b hab).ShortExact :=
    quotient_shortExact (yonedaExtension_shortExact D.firstExtension) hP j hjp
  have : Presheaf.IsLocallySurjective Y.J ρ.hom := structureMap_locallySurjective D
  obtain ⟨N, eN⟩ := descendModule ρ (cokernel j) (fun U r hr z =>
    difference_cokernel_annihilated D h U r hr z)
  let ff : R.FullyFaithful := {
    preimage := fun t => moduleHomEquivOfLocallySurjective ρ this t
    map_preimage := fun t => (moduleHomEquivOfLocallySurjective ρ this).symm_apply_apply t
    preimage_map := fun t => (moduleHomEquivOfLocallySurjective ρ this).apply_symm_apply t }
  obtain ⟨a', b', hz, hshort, hret⟩ := descend_shortExact R ff a b hab hH eN
  refine ⟨{
    middle := N
    ι := a'
    π := b'
    zero := hz
    shortExact := hshort
    retraction_iff := ?_ }⟩
  refine hret.trans ?_
  have H := difference_retraction_iff (S₁ := S₁) h₂ (R.map D.kernelMap) φ
  change (∃ r : cokernel j ⟶ R.obj D.L, a ≫ r = 𝟙 _) ↔ _ at H
  constructor
  · intro hr
    obtain ⟨t, ht₁, ht₂⟩ := H.mp hr
    exact ⟨t, ht₁.symm, ht₂⟩
  · rintro ⟨t, ht₁, ht₂⟩
    exact H.mpr ⟨t, ht₁.symm, ht₂⟩

/-- The obstruction class in the first Ext group over the quotient structure sheaf. Its
vanishing characterizes lifts of the prescribed end maps. -/
@[stacks 08MD "obstruction class"]
noncomputable def obstructionClass
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    (D : TwoExtensions i) (h : CompatibleActions D) :
    Abelian.Ext D.F D.L 1 :=
  -(obstructionExtension D h).shortExact.extClass

/-- The obstruction vanishes exactly when the end maps extend to a map of the two
extensions. -/
@[stacks 08MD "vanishing criterion"]
theorem obstructionClass_eq_zero_iff
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
    (D : TwoExtensions i) (h : CompatibleActions D) :
    obstructionClass D h = 0 ↔
      ∃ φ' : D.firstExtension.Z.left ⟶ D.secondExtension.Z.left,
        IsExtensionLift D φ' := by
  rw [obstructionClass, neg_eq_zero]
  have H := extClass_comp_mk₀_eq_zero_iff (obstructionExtension D h).shortExact (𝟙 D.L)
  rw [Abelian.Ext.comp_mk₀_id] at H
  exact H.trans (obstructionExtension D h).retraction_iff

end Deformation.ToposThickening

end
