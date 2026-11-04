module

public import StacksFrontier.Deformation.AlgebraExtension.Pushout

/-!
# Morphisms of extensions from maps of a presentation (Step 3 of Stacks 08UG)

Let `P` be an extension of `𝒜`-algebras of `𝒪` by `ℳ`, and let `ℓ : R ⟶ 𝒪'_P` be a
homomorphism of `𝒜`-algebras out of a sheaf of rings `R` such that `R ⟶ 𝒪'_P ⟶ 𝒪` is locally
surjective — for instance the map `𝒜[ℰ] ⟶ 𝒪'_P` classifying a lift `ℰ ⟶ 𝒪'_P` of a family of
generators of `𝒪`. Then `P` is the square-zero pushout of `R` along the restriction of `ℓ` to
the kernel `ℐ` of `R ⟶ 𝒪`: the canonical morphism from the pushout to `P` is an isomorphism.

Consequently a morphism of extensions out of `P` is produced from a homomorphism out of `R`:
given an extension `Q` by `𝒩`, a map `φ : ℳ ⟶ 𝒩`, and a homomorphism `q : R ⟶ 𝒪'_Q` of
`𝒜`-algebras over `𝒪` whose restriction to `ℐ` is `φ` of that of `ℓ`, there is a morphism of
extensions `P ⟶ Q` along `φ`. This is Step 3 of the proof of [Stacks Project, Tag 08UG]
("a calculation shows that `b + θ ∘ d` annihilates `ℐ'` and hence defines a map `𝒪'₁ ⟶ 𝒪'₂`"),
in the form in which the twisting by `θ` has already been absorbed into `q`.

## Main definitions

* `Deformation.AlgebraExtension.kernelPreimage`: the inverse, on sections, of the
  identification of `ℳ` with the kernel of the reduction.
* `Deformation.AlgebraExtension.ofLift`: the pushout data of a presentation of `P`.
* `Deformation.AlgebraExtension.mapAlongOfLift`: the morphism `P ⟶ Q` along `φ` built from `q`.

## Main results

* `Deformation.AlgebraExtension.isIso_ofLiftComparison`: `P` is the pushout of any of its
  presentations.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal IdealRestriction presentationScalar)
open Stacks.Sites.SqZeroPushout

universe u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}

/-! ### The inverse of the kernel identification -/

section KernelPreimage

variable (P : AlgebraExtension a M)

/-- The section of `ℳ` corresponding to a section of the kernel of the reduction. -/
noncomputable def kernelPreimage {U : Cᵒᵖ} (x : kernelIdeal P.reduction.hom U) : M.val.obj U :=
  (P.exists_incl (x : P.extension.obj.obj U) x.2).choose

/-- The inclusion `ℳ ⟶ 𝒪'_P` sends `kernelPreimage x` to `x`. -/
theorem incl_kernelPreimage {U : Cᵒᵖ} (x : kernelIdeal P.reduction.hom U) :
    P.incl (P.kernelPreimage x) = (x : P.extension.obj.obj U) :=
  (P.exists_incl (x : P.extension.obj.obj U) x.2).choose_spec

/-- `kernelPreimage x` is the unique section of `ℳ` whose image in `𝒪'_P` is `x`. -/
theorem kernelPreimage_eq {U : Cᵒᵖ} (x : kernelIdeal P.reduction.hom U) (m : M.val.obj U)
    (h : P.incl m = (x : P.extension.obj.obj U)) : P.kernelPreimage x = m :=
  P.incl_injective ((P.incl_kernelPreimage x).trans h.symm)

end KernelPreimage

/-! ### An extension is the pushout of any of its presentations -/

/-- A morphism of extensions along the identity has an invertible middle term. -/
private theorem isIso_hom_of_mapAlong_id [J.HasSheafCompose (forget CommRingCat.{u})]
    [(forget CommRingCat.{u}).ReflectsIsomorphisms] {X Y : AlgebraExtension a M}
    (f : MapAlong (𝟙 M) X Y) : IsIso f.hom :=
  (Sheaf.isLocallyBijective_iff_isIso _).1
    ⟨(Sheaf.isLocallyInjective_iff_injective _).2
      (MapAlong.injective_app f fun _ => Function.injective_id),
      MapAlong.isLocallySurjective f fun _ => Function.surjective_id⟩

section OfLift

variable (P : AlgebraExtension a M) {R : Sheaf J CommRingCat.{u}} (ℓ : R ⟶ P.extension)
  (base : A ⟶ R) (hbase : base ≫ ℓ = P.algebraMap)
  [hℓ : Presheaf.IsLocallySurjective J (ℓ ≫ P.reduction).hom]

/-- A local relation of the presentation `R ⟶ 𝒪` is carried by `ℓ` into the square-zero ideal. -/
theorem lift_mem_kernelIdeal (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U) :
    ((ℓ.hom.app U).hom (g : R.obj.obj U)) ∈ kernelIdeal P.reduction.hom U :=
  g.2

/-- The restriction `ℓ|_ℐ : ℐ ⟶ ℳ` of a presentation of `P` to the kernel of `R ⟶ 𝒪`. -/
noncomputable def liftKernel (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U) :
    M.val.obj U :=
  P.kernelPreimage ⟨(ℓ.hom.app U).hom (g : R.obj.obj U), P.lift_mem_kernelIdeal ℓ U g⟩

/-- The inclusion `ℳ ⟶ 𝒪'_P` sends `ℓ|_ℐ g` to `ℓ g`. -/
theorem incl_liftKernel (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U) :
    P.incl (P.liftKernel ℓ U g) = ℓ.hom.app U (g : R.obj.obj U) :=
  P.incl_kernelPreimage _

include hbase in
/-- **The pushout data of a presentation of `P`**: `R ⟶ 𝒪` with the restriction `ℓ|_ℐ`. -/
noncomputable def ofLift : PresentationPushout a M where
  presentation := R
  proj := ℓ ≫ P.reduction
  locallySurjective := hℓ
  base := base
  base_proj := by rw [← Category.assoc, hbase, P.algebraMap_reduction]
  psi :=
    { app := fun U => AddMonoidHom.mk' (P.liftKernel ℓ U) fun g h => P.kernelPreimage_eq _ _
        ((P.incl_add _ _).trans ((congrArg₂ (· + ·) (P.incl_liftKernel ℓ U g)
          (P.incl_liftKernel ℓ U h)).trans (map_add (ℓ.hom.app U).hom _ _).symm))
      app_smul := fun U r g => P.kernelPreimage_eq _ _
        ((P.mul_incl (ℓ.hom.app U r) (P.liftKernel ℓ U g)).symm.trans
          ((congrArg (ℓ.hom.app U r * ·) (P.incl_liftKernel ℓ U g)).trans
            (map_mul (ℓ.hom.app U).hom r (g : R.obj.obj U)).symm))
      app_map := fun {U V} f g => P.kernelPreimage_eq _ _
        ((P.incl_naturality f (P.liftKernel ℓ U g)).trans
          ((congrArg (P.extension.obj.map f).hom (P.incl_liftKernel ℓ U g)).trans
            (NatTrans.naturality_apply ℓ.hom f (g : R.obj.obj U)).symm))
      smul_eq_zero := fun U g m => by
        have h : (show (underlyingRingSheaf O).obj.obj U from
            (ℓ ≫ P.reduction).hom.app U (g : R.obj.obj U)) = 0 := RingHom.mem_ker.1 g.2
        have h2 : (show (underlyingRingSheaf O).obj.obj U from
              (ℓ ≫ P.reduction).hom.app U (g : R.obj.obj U)) •
            (show M.val.obj U from m) = 0 := by
          rw [h, zero_smul]
        exact h2 }

/-- The projection of the pushout data `ofLift` is the composite `R ⟶ 𝒪'_P ⟶ 𝒪`. -/
theorem ofLift_proj : (P.ofLift ℓ base hbase).proj = ℓ ≫ P.reduction :=
  rfl

/-- The map `ℐ ⟶ ℳ` of the pushout data `ofLift` is the restriction `ℓ|_ℐ`. -/
theorem ofLift_psi_app (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U) :
    (P.ofLift ℓ base hbase).psi.app U g = P.liftKernel ℓ U g :=
  rfl

variable [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}]

/-- The canonical morphism from the pushout of a presentation of `P` to `P`. -/
noncomputable def ofLiftComparison :
    MapAlong (𝟙 M) (P.ofLift ℓ base hbase).extension P :=
  (P.ofLift ℓ base hbase).desc (𝟙 M) ℓ rfl hbase
    (fun U g => (P.incl_liftKernel ℓ U g).symm :
      ∀ (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U),
        ℓ.hom.app U (g : R.obj.obj U) =
          P.incl (((𝟙 M : M ⟶ M).val.app U (P.liftKernel ℓ U g)) : M.val.obj U))

variable [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- **An extension is the square-zero pushout of any of its presentations**: the canonical
morphism is an isomorphism. -/
theorem isIso_ofLiftComparison : IsIso (P.ofLiftComparison ℓ base hbase).hom :=
  isIso_hom_of_mapAlong_id _

/-- **Step 3 of the proof of [Stacks Project, Tag 08UG].** Let `ℓ : R ⟶ 𝒪'_P` be a presentation
of `P`, let `Q` be an extension by `𝒩` and `φ : ℳ ⟶ 𝒩`. A homomorphism `q : R ⟶ 𝒪'_Q` of
`𝒜`-algebras over `𝒪` which is `φ ∘ ℓ|_ℐ` on the kernel `ℐ` of `R ⟶ 𝒪` defines a morphism of
extensions `P ⟶ Q` along `φ`. -/
noncomputable def mapAlongOfLift {Q : AlgebraExtension a N} (φ : M ⟶ N)
    (q : R ⟶ Q.extension) (hq : q ≫ Q.reduction = ℓ ≫ P.reduction)
    (hqb : base ≫ q = Q.algebraMap)
    (hψ : ∀ (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U),
      q.hom.app U (g : R.obj.obj U) = Q.incl ((φ.val.app U (P.liftKernel ℓ U g)) : N.val.obj U)) :
    MapAlong φ P Q :=
  haveI := P.isIso_ofLiftComparison ℓ base hbase
  let c := P.ofLiftComparison ℓ base hbase
  let k := (P.ofLift ℓ base hbase).desc φ q hq hqb hψ
  { hom := inv c.hom ≫ k.hom
    reduction_comm := by
      rw [Category.assoc, k.reduction_comm, IsIso.inv_comp_eq, c.reduction_comm]
    algebraMap_comm := by
      rw [← c.algebraMap_comm, Category.assoc, IsIso.hom_inv_id_assoc, k.algebraMap_comm]
    kernel_comm := fun U m => by
      have hc : (inv c.hom).hom.app U (P.incl m) = (P.ofLift ℓ base hbase).extension.incl m := by
        refine (congrArg ((inv c.hom).hom.app U).hom (c.kernel_comm U m).symm).trans ?_
        change (c.hom ≫ inv c.hom).hom.app U _ = _
        rw [IsIso.hom_inv_id]
        rfl
      change k.hom.hom.app U ((inv c.hom).hom.app U (P.incl m)) = _
      rw [hc, k.kernel_comm] }

/-- The morphism of extensions built from `q` restricts to `q` along `ℓ`. -/
theorem lift_mapAlongOfLift_hom {Q : AlgebraExtension a N} (φ : M ⟶ N)
    (q : R ⟶ Q.extension) (hq : q ≫ Q.reduction = ℓ ≫ P.reduction)
    (hqb : base ≫ q = Q.algebraMap)
    (hψ : ∀ (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U),
      q.hom.app U (g : R.obj.obj U) = Q.incl ((φ.val.app U (P.liftKernel ℓ U g)) : N.val.obj U)) :
    ℓ ≫ (P.mapAlongOfLift ℓ base hbase φ q hq hqb hψ).hom = q := by
  have := P.isIso_ofLiftComparison ℓ base hbase
  have hc : (P.ofLift ℓ base hbase).lift ≫ (P.ofLiftComparison ℓ base hbase).hom = ℓ :=
    (P.ofLift ℓ base hbase).lift_desc (𝟙 M) ℓ rfl hbase _
  show ℓ ≫ inv (P.ofLiftComparison ℓ base hbase).hom ≫
    ((P.ofLift ℓ base hbase).desc φ q hq hqb hψ).hom = q
  refine (congrArg (· ≫ inv (P.ofLiftComparison ℓ base hbase).hom ≫
    ((P.ofLift ℓ base hbase).desc φ q hq hqb hψ).hom) hc.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((P.ofLift ℓ base hbase).lift ≫ ·) (IsIso.hom_inv_id_assoc _ _)).trans ?_
  exact (P.ofLift ℓ base hbase).lift_desc φ q hq hqb hψ

include hbase in
/-- A homomorphism `q : R ⟶ 𝒪'_Q` of `𝒜`-algebras over `𝒪` which is `φ ∘ ℓ|_ℐ` on the kernel
`ℐ` of `R ⟶ 𝒪` yields a morphism of extensions `P ⟶ Q` along `φ`. -/
theorem nonempty_mapAlong_of_lift {Q : AlgebraExtension a N} (φ : M ⟶ N)
    (q : R ⟶ Q.extension) (hq : q ≫ Q.reduction = ℓ ≫ P.reduction)
    (hqb : base ≫ q = Q.algebraMap)
    (hψ : ∀ (U : Cᵒᵖ) (g : kernelIdeal (ℓ ≫ P.reduction).hom U),
      q.hom.app U (g : R.obj.obj U) = Q.incl ((φ.val.app U (P.liftKernel ℓ U g)) : N.val.obj U)) :
    Nonempty (MapAlong φ P Q) :=
  ⟨P.mapAlongOfLift ℓ base hbase φ q hq hqb hψ⟩

end OfLift

/-! ### Morphisms of extensions by the same module are isomorphisms -/

section IsIso

variable [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- **A morphism of extensions by the same module is an isomorphism of middle terms**. -/
theorem MapAlong.isIso_hom {P Q : AlgebraExtension a M} (f : P ⟶ Q) : IsIso f.hom :=
  isIso_hom_of_mapAlong_id f

/-- The inverse of a morphism of extensions by the same module. -/
noncomputable def MapAlong.inv {P Q : AlgebraExtension a M} (f : P ⟶ Q) : Q ⟶ P :=
  haveI := MapAlong.isIso_hom f
  { hom := CategoryTheory.inv f.hom
    reduction_comm := by rw [IsIso.inv_comp_eq, MapAlong.reduction_comm]
    algebraMap_comm := by rw [IsIso.comp_inv_eq, MapAlong.algebraMap_comm]
    kernel_comm := fun U m => by
      refine Eq.trans (congrArg (fun x => (CategoryTheory.inv f.hom).hom.app U x)
        (f.kernel_comm U m).symm) ?_
      change (f.hom ≫ CategoryTheory.inv f.hom).hom.app U (P.incl m) = _
      rw [IsIso.hom_inv_id]
      rfl }

/-- **The category of extensions by `ℳ` is a groupoid**: every morphism is an isomorphism. -/
instance isIso_of_algebraExtension {P Q : AlgebraExtension a M} (f : P ⟶ Q) : IsIso f :=
  ⟨MapAlong.inv f, MapAlong.ext (by
    have := MapAlong.isIso_hom f
    exact IsIso.hom_inv_id f.hom), MapAlong.ext (by
    have := MapAlong.isIso_hom f
    exact IsIso.inv_hom_id f.hom)⟩

end IsIso

end Deformation.AlgebraExtension

end
