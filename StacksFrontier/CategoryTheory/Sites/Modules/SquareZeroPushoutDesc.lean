module

public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafRecognition
public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout

/-!
# Homomorphisms out of a square-zero pushout

Let `π : R ⟶ ℬ` be a locally surjective morphism of sheaves of commutative rings on a small
site, `𝒢` a sheaf of `R`-modules and `ψ : Ker π ⟶ 𝒢` the datum of
`Stacks.Sites.SqZeroPushout.PushoutData`, so that the square-zero pushout `(R ⋉ 𝒢)/J` is
defined. This file records its universal property: a homomorphism of sheaves of rings
`q : R ⟶ 𝒯` together with a section-wise additive map `ι : 𝒢 ⟶ 𝒯`, natural, `R`-linear through
`q`, with square-zero image, defines a homomorphism `R ⋉ 𝒢 ⟶ 𝒯`, `(r, n) ↦ q r + ι n`; and when
`q` agrees with `ι ∘ ψ` on `Ker π` it descends to `(R ⋉ 𝒢)/J ⟶ 𝒯`. Two homomorphisms out of the
pushout agreeing after the quotient map are equal.

## Main definitions

* `Stacks.Sites.SqZeroPushout.SqZeroDescData`: the data `(q, ι)` of a homomorphism out of
  `R ⋉ 𝒢`.
* `Stacks.Sites.SqZeroPushout.SqZeroDescData.toHom`: that homomorphism.
* `Stacks.Sites.SqZeroPushout.pushoutDesc`: the induced homomorphism out of the pushout.

## Main results

* `Stacks.Sites.SqZeroPushout.pushoutMk_comp_pushoutDesc`: the induced homomorphism restricts
  to `(q, ι)` along the quotient map.
* `Stacks.Sites.SqZeroPushout.pushoutDesc_pushoutInr`: it is `ι` on `𝒢`.
* `Stacks.Sites.SqZeroPushout.pushout_hom_ext`: homomorphisms out of the pushout are determined
  by their restriction along the quotient map.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public section

open CategoryTheory PresheafOfModules Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf sqZeroExtSheaf)
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace Stacks.Sites.SqZeroPushout

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R B : Sheaf K CommRingCat.{u}}
  (N : SheafOfModules.{u} (underlyingRingSheaf R))

/-- **The data of a homomorphism out of `R ⋉ 𝒢`** into a sheaf of commutative rings `𝒯`: a
homomorphism `q : R ⟶ 𝒯` and a natural section-wise additive map `ι : 𝒢 ⟶ 𝒯` which is
`R`-linear through `q` and has square-zero image. -/
structure SqZeroDescData (T : Sheaf K CommRingCat.{u}) where
  /-- The homomorphism on the ring component. -/
  ringMap : R ⟶ T
  /-- The map on the module component, on sections. -/
  inr (X : Cᵒᵖ) : ↥((modules N).obj X) →+ ↥(T.obj.obj X)
  /-- The map on the module component is `R`-linear through `q`. -/
  inr_smul (X : Cᵒᵖ) (r : ↥(R.obj.obj X)) (n : ↥((modules N).obj X)) :
    inr X (r • n) = ringMap.hom.app X r * inr X n
  /-- The image of the module component has square zero. -/
  inr_mul_inr (X : Cᵒᵖ) (n m : ↥((modules N).obj X)) : inr X n * inr X m = 0
  /-- The map on the module component commutes with the restriction maps. -/
  inr_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ↥((modules N).obj X)) :
    inr Y ((modules N).map f n) = (T.obj.map f).hom (inr X n)

namespace SqZeroDescData

variable {N} {T : Sheaf K CommRingCat.{u}} (d : SqZeroDescData N T)

/-- The homomorphism `(r, n) ↦ q r + ι n` on the sections over one object. -/
noncomputable def app (X : Cᵒᵖ) : ↥((sqZeroExtSheaf R N).obj.obj X) →+* ↥(T.obj.obj X) where
  toFun w := d.ringMap.hom.app X (sqZeroExtFst (M := modules N) w) +
    d.inr X (sqZeroExtSnd (M := modules N) w)
  map_one' := by
    change d.ringMap.hom.app X 1 + d.inr X 0 = 1
    rw [map_one, map_zero, add_zero]
  map_mul' w w' := by
    change d.ringMap.hom.app X
          (sqZeroExtFst (M := modules N) w * sqZeroExtFst (M := modules N) w') +
        d.inr X (sqZeroExtFst (M := modules N) w • sqZeroExtSnd (M := modules N) w' +
          sqZeroExtFst (M := modules N) w' • sqZeroExtSnd (M := modules N) w) = _
    rw [map_mul, map_add, d.inr_smul, d.inr_smul]
    linear_combination (-1 : ↥(T.obj.obj X)) *
      d.inr_mul_inr X (sqZeroExtSnd (M := modules N) w) (sqZeroExtSnd (M := modules N) w')
  map_zero' := by
    change d.ringMap.hom.app X 0 + d.inr X 0 = 0
    rw [map_zero, map_zero, add_zero]
  map_add' w w' := by
    change d.ringMap.hom.app X
          (sqZeroExtFst (M := modules N) w + sqZeroExtFst (M := modules N) w') +
        d.inr X (sqZeroExtSnd (M := modules N) w + sqZeroExtSnd (M := modules N) w') = _
    rw [map_add, map_add]
    abel

/-- The homomorphism `SqZeroDescData.app` sends a section `w` to `q (w.fst) + ι (w.snd)`. -/
theorem app_apply (X : Cᵒᵖ) (w : ↥((sqZeroExtSheaf R N).obj.obj X)) :
    d.app X w = d.ringMap.hom.app X (sqZeroExtFst (M := modules N) w) +
      d.inr X (sqZeroExtSnd (M := modules N) w) :=
  rfl

/-- **The homomorphism `R ⋉ 𝒢 ⟶ 𝒯`**, `(r, n) ↦ q r + ι n`. -/
noncomputable def toHom : sqZeroExtSheaf R N ⟶ T :=
  ObjectProperty.homMk
    { app := fun X => CommRingCat.ofHom (R := ↥((sqZeroExtSheaf R N).obj.obj X))
        (S := ↥(T.obj.obj X)) (d.app X)
      naturality := fun {X Y} f => CommRingCat.hom_ext (RingHom.ext fun w => by
        change d.ringMap.hom.app Y ((R.obj.map f).hom (sqZeroExtFst (M := modules N) w)) +
            d.inr Y ((modules N).map f (sqZeroExtSnd (M := modules N) w)) =
          (T.obj.map f).hom (d.ringMap.hom.app X (sqZeroExtFst (M := modules N) w) +
            d.inr X (sqZeroExtSnd (M := modules N) w))
        rw [map_add, d.inr_map]
        exact congrArg (· + _) (NatTrans.naturality_apply d.ringMap.hom f (sqZeroExtFst w))) }

/-- The homomorphism `SqZeroDescData.toHom` sends a section `w` to `q (w.fst) + ι (w.snd)`. -/
theorem toHom_app_apply (X : Cᵒᵖ) (w : ↥((sqZeroExtSheaf R N).obj.obj X)) :
    d.toHom.hom.app X w = d.ringMap.hom.app X (sqZeroExtFst (M := modules N) w) +
      d.inr X (sqZeroExtSnd (M := modules N) w) :=
  rfl

end SqZeroDescData

variable (π : R ⟶ B) (ψ : PushoutData π N) {T : Sheaf K CommRingCat.{u}}
  (d : SqZeroDescData N T)
  (hd : ∀ (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)),
    d.ringMap.hom.app X (g : ↥(R.obj.obj X)) = d.inr X (ψ.app X g))

include hd in
/-- The homomorphism `R ⋉ 𝒢 ⟶ 𝒯` kills the graph ideal of `ψ` as soon as `q = ι ∘ ψ` on
`Ker π`. -/
theorem graphIdeal_le_ker (X : Cᵒᵖ) :
    Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) X ≤
      RingHom.ker (d.toHom.hom.app X).hom := by
  rintro _ ⟨g, rfl⟩
  change d.ringMap.hom.app X (g : ↥(R.obj.obj X)) + d.inr X (-(ψ.app X g)) = 0
  rw [map_neg, hd, add_neg_cancel]

variable [HasWeakSheafify K CommRingCat.{u}]

/-- **The homomorphism out of the square-zero pushout** induced by `(q, ι)` when `q = ι ∘ ψ` on
`Ker π`. -/
noncomputable def pushoutDesc : pushoutSheaf π N ψ ⟶ T :=
  Stacks.Sites.quotientRingSheafDesc d.toHom (graphIdealSubsheaf π N ψ)
    (graphIdeal_le_ker N π ψ d hd)

/-- The induced homomorphism out of the pushout restricts to `SqZeroDescData.toHom` along the
quotient map. -/
@[reassoc (attr := simp)]
theorem pushoutMk_comp_pushoutDesc : pushoutMk π N ψ ≫ pushoutDesc N π ψ d hd = d.toHom :=
  Stacks.Sites.toQuotientRingSheaf_comp_quotientRingSheafDesc _ _ _

/-- The induced homomorphism sends the class of a section `w` of `R ⋉ 𝒢` to
`q (w.fst) + ι (w.snd)`. -/
theorem pushoutDesc_pushoutMk_apply (X : Cᵒᵖ) (w : ↥((sqZeroExtSheaf R N).obj.obj X)) :
    (pushoutDesc N π ψ d hd).hom.app X ((pushoutMk π N ψ).hom.app X w) =
      d.ringMap.hom.app X (sqZeroExtFst (M := modules N) w) +
        d.inr X (sqZeroExtSnd (M := modules N) w) :=
  Stacks.Sites.quotientRingSheafDesc_app_apply _ _ _ X w

/-- The induced homomorphism is `ι` on `𝒢`. -/
theorem pushoutDesc_pushoutInr (X : Cᵒᵖ) (n : ↥((modules N).obj X)) :
    (pushoutDesc N π ψ d hd).hom.app X (pushoutInr π N ψ X n) = d.inr X n := by
  refine (pushoutDesc_pushoutMk_apply N π ψ d hd X (inrSection N X n)).trans ?_
  rw [inrSection_fst, inrSection_snd, map_zero, zero_add]

/-- The induced homomorphism is `q` on the image of `R`. -/
theorem pushoutDesc_pushoutMk_inl (X : Cᵒᵖ) (r : ↥(R.obj.obj X)) :
    (pushoutDesc N π ψ d hd).hom.app X
        ((pushoutMk π N ψ).hom.app X (sqZeroExtMk (M := modules N) r 0)) =
      d.ringMap.hom.app X r := by
  refine (pushoutDesc_pushoutMk_apply N π ψ d hd X _).trans ?_
  rw [sqZeroExtFst_mk, sqZeroExtSnd_mk, map_zero, add_zero]

/-- **Homomorphisms out of the square-zero pushout are determined by their restriction along
the quotient map.** -/
theorem pushout_hom_ext {f g : pushoutSheaf π N ψ ⟶ T}
    (h : pushoutMk π N ψ ≫ f = pushoutMk π N ψ ≫ g) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext K f.hom g.hom T.property ?_
  ext X x
  obtain ⟨w, rfl⟩ := Stacks.Sites.toQuotientPresheaf_app_surjective
    (graphIdealSubsheaf π N ψ) X x
  exact congrArg (fun k : sqZeroExtSheaf R N ⟶ T => k.hom.app X w) h

end Stacks.Sites.SqZeroPushout

end
