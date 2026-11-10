module

public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageThickening
public import StacksFrontier.Deformation.RingedSpaceThickening.InverseImageExtensionComparison
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleThickeningMorphism
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtensionClassification
import StacksCore.Tactic.StacksAttribute

/-!
# The two extensions of `g⁻¹𝒪_X` by `𝒢` of Stacks 0GQ2, and the diagram chase

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, `ℱ`
an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module, `c : ℱ ⟶ g_*𝒢` a `g`-map, `0 ⟶ ℱ ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` an
extension of `f⁻¹𝒪_S`-algebras and `0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` an extension of
`g⁻¹f⁻¹𝒪_S`-algebras, both with ideals of square zero, as in **Stacks 0GQ1**. **Stacks 0GQ2**
constructs two extensions of `g⁻¹𝒪_X` by `𝒢` as `g⁻¹f⁻¹𝒪_S`-algebras:

* `𝒪'₁`, the pushout of `0 ⟶ g⁻¹ℱ ⟶ g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X ⟶ 0` along `c : g⁻¹ℱ ⟶ 𝒢`
  (`inverseImagePushout`), and
* `𝒪'₂ = 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X`, the pullback along `g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`
  (`inverseImagePullback`),

and shows by a diagram chase that an `S`-morphism `Y' ⟶ X'` compatible with `g` and `c` exists
exactly when `𝒪'₁ ≅ 𝒪'₂` (`nonempty_compatibleMorphism_iff_nonempty_iso`).

Both extensions are objects of the category of **Stacks 0GPZ** for the ringed space `(Y, g⁻¹𝒪_X)`
(`inverseImageRingedSpace g`) over `S` (`inverseImageSpaceHom f g`), with `𝒢` read as a
`g⁻¹𝒪_X`-module along `g^♯` (`restrictedModule g G`); so their classes are the images under the
bijection `SquareZeroAlgebraExtension.isomorphismClassesEquivExt` of that ringed space.

## Main definitions

* `pushoutOfIdealRestriction`, `pullbackOfExtension`: the pushout of an extension along a map
  out of its ideal and the pullback of an extension along a map of sheaves of rings, as square-zero
  extensions of the category of **Stacks 0GPZ**.
* `inverseImagePushout`, `inverseImagePullback`: `𝒪'₁` and `𝒪'₂`.
* `inverseImageData`: the setup, as a term of `Stacks.Deformation.InverseImageExtension.Data`.

## Main results

* `inverseImagePushoutMap_comp_reduction`, `inverseImagePushoutMap_app_kernel`: the first
  displayed diagram of the source commutes.
* `nonempty_compatibleMorphism_iff_nonempty_iso`: **the diagram chase of Stacks 0GQ2**.

## Implementation notes

The map `c : g⁻¹ℱ ⟶ 𝒢` on the kernel `g⁻¹ℱ` of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` is `idealMap`, built from
the stalks of the inverse image, so the exactness of `g⁻¹` is proved rather than assumed. The
diagram chase goes through `Stacks.Deformation.InverseImageExtension.Data`: its two conditions on
`𝒢` are discharged by the square-zero extension `𝒪_{Y'}`, and its type of compatible morphisms
`g⁻¹𝒪_{X'} ⟶ 𝒪_{Y'}` is identified, through the inverse-image adjunction, with
`CompatibleMorphism`, the comorphisms `𝒪_{X'} ⟶ g_*𝒪_{Y'}` of the source.

## References

* [Stacks Project, Tag 0GQ2](https://stacks.math.columbia.edu/tag/0GQ2)
* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SheafOfModules (ringedSpaceStructureMap)
open Stacks.Sites.Conormal (kernelIdeal IdealRestriction)
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.SqZeroPullback

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### The pushout of an extension along a map out of its ideal -/

section PushoutOfIdealRestriction

variable {T S : RingedSpace.{u, u}} (k : T ⟶ S)
  {R : Sheaf (Opens.grothendieckTopology T.carrier) CommRingCat.{u}} (π : R ⟶ T.sheaf)
  (b : inverseImageBaseRing k ⟶ R) (hb : b ≫ π = structureRingMap k)
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology T.carrier) T.sheaf)}
  (ρ : IdealRestriction.{u, u, u, u} π G)

/-- `𝒢`, read over `R` through `π`. -/
abbrev pushoutModuleOf :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.underlyingRingSheaf.{u} R) :=
  (SheafOfModules.restrictScalars ((sheafCompose (Opens.grothendieckTopology T.carrier)
    (forget₂ CommRingCat.{u} RingCat.{u})).map π)).obj G

local notation "M" => pushoutModuleOf

/-- The pushout datum of a restriction datum `ρ : Ker π ⟶ 𝒢`. -/
abbrev pushoutDatumOf : PushoutData.{u} π (pushoutModuleOf π (G := G)) :=
  IdealRestriction.toPushoutData.{u} π ρ

/-- The pushout `(R ⋉ 𝒢)/{(x, -ρ x)}`. -/
abbrev pushoutRingOf : Sheaf (Opens.grothendieckTopology T.carrier) CommRingCat.{u} :=
  pushoutSheaf.{u} π (M π (G := G)) (pushoutDatumOf π ρ)

/-- The inclusion of `𝒢` into the pushout, on sections, as a map into the kernel of the
projection. -/
def pushoutIdealHomOf (U : (Opens T.carrier)ᵒᵖ) :
    G.val.obj U →+ kernelIdeal (pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ)).hom U where
  toFun n := ⟨pushoutInr.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U n,
    pushoutProj_pushoutInr.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U n⟩
  map_zero' := Subtype.ext (pushoutInr_zero.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U)
  map_add' n m :=
    Subtype.ext (pushoutInr_add.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U n m)

/-- The inclusion of `𝒢` into the pushout, on sections, onto the kernel of the projection. -/
def pushoutIdealEquivOf (U : (Opens T.carrier)ᵒᵖ) :
    G.val.obj U ≃+ kernelIdeal (pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ)).hom U :=
  AddEquiv.ofBijective (pushoutIdealHomOf π ρ U)
    ⟨fun n m h ↦ pushoutInr_injective.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U
        (congrArg Subtype.val h),
      fun s ↦ by
        obtain ⟨n, hn⟩ :=
          (pushoutProj_app_eq_zero_iff.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U s.1).1 s.2
        exact ⟨n, Subtype.ext hn⟩⟩

/-- The equivalence `pushoutIdealEquivOf` sends a section `n` of `𝒢` to its image `[(0, n)]` in
the pushout. -/
theorem pushoutIdealEquivOf_apply (U : (Opens T.carrier)ᵒᵖ) (n : G.val.obj U) :
    (pushoutIdealEquivOf π ρ U n).1 =
      pushoutInr.{u} π (M π (G := G)) (pushoutDatumOf π ρ) U n :=
  rfl

/-- The inverse of `pushoutIdealEquivOf` commutes with restriction of sections. -/
theorem pushoutIdealEquivOf_symm_map {U V : (Opens T.carrier)ᵒᵖ} (i : U ⟶ V)
    (s : kernelIdeal (pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ)).hom U) :
    (pushoutIdealEquivOf π ρ V).symm ⟨((pushoutRingOf π ρ).obj.map i).hom s.1,
      Stacks.Sites.Conormal.map_kernel _ i s.2⟩ =
      G.val.map i ((pushoutIdealEquivOf π ρ U).symm s) := by
  obtain ⟨n, rfl⟩ := (pushoutIdealEquivOf π ρ U).surjective s
  rw [AddEquiv.symm_apply_apply]
  exact (AddEquiv.symm_apply_eq _).2
    (Subtype.ext (pushoutInr_map.{u} π (M π (G := G)) (pushoutDatumOf π ρ) i n))

/-- `R ⟶ (R ⋉ 𝒢)/{(x, -ρ x)}`, `x ↦ [(x, 0)]`. -/
abbrev pushoutMapOf : R ⟶ pushoutRingOf π ρ :=
  Stacks.Sheaves.Differentials.sqZeroExtSheafInl _ (M π (G := G)) ≫
    pushoutMk.{u} π (M π (G := G)) (pushoutDatumOf π ρ)

/-- The composite `R ⟶ (R ⋉ 𝒢)/{(x, -ρ x)} ⟶ 𝒪_T` is `π`. -/
theorem pushoutMapOf_comp_pushoutProj :
    pushoutMapOf π ρ ≫ pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ) = π :=
  (Category.assoc _ _ _).trans ((congrArg
    (Stacks.Sheaves.Differentials.sqZeroExtSheafInl _ (M π (G := G)) ≫ ·)
    (pushoutMk_comp_pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π)
        (Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj.{u} _ _)).trans
          (Category.id_comp _))))

/-- **The pushout of the extension `0 ⟶ Ker π ⟶ R ⟶ 𝒪_T ⟶ 0` along `ρ : Ker π ⟶ 𝒢`**, an
extension `0 ⟶ 𝒢 ⟶ (R ⋉ 𝒢)/{(x, -ρ x)} ⟶ 𝒪_T ⟶ 0` of `k⁻¹𝒪_S`-algebras. -/
def pushoutOfIdealRestriction
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T.carrier) π.hom] :
    SquareZeroAlgebraExtension k G where
  sheaf := pushoutRingOf π ρ
  base := b ≫ pushoutMapOf π ρ
  reduction := pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ)
  base_comp_reduction := (Category.assoc _ _ _).trans
    ((congrArg (b ≫ ·) (pushoutMapOf_comp_pushoutProj π ρ)).trans hb)
  reduction_surjective := isLocallySurjective_pushoutProj.{u} π (M π (G := G)) (pushoutDatumOf π ρ)
  ideal :=
    { app U := (pushoutIdealEquivOf π ρ U).symm.toAddMonoidHom
      app_smul U r s := by
        change (pushoutIdealEquivOf π ρ U).symm (r • s) =
          _ • (pushoutIdealEquivOf π ρ U).symm s
        obtain ⟨n, rfl⟩ := (pushoutIdealEquivOf π ρ U).surjective s
        rw [AddEquiv.symm_apply_apply]
        exact (AddEquiv.symm_apply_eq _).2
          (Subtype.ext (mul_pushoutInr.{u} π (pushoutDatumOf π ρ) U r n))
      app_map := pushoutIdealEquivOf_symm_map π ρ }
  ideal_bijective U := (pushoutIdealEquivOf π ρ U).symm.bijective

end PushoutOfIdealRestriction

/-! ### The pullback of an extension along a map of sheaves of rings -/

section PullbackOfExtension

variable {T S : RingedSpace.{u, u}} (k : T ⟶ S)
  {B B' : Sheaf (Opens.grothendieckTopology T.carrier) CommRingCat.{u}} (p : B' ⟶ B)
  (q : T.sheaf ⟶ B) (b' : inverseImageBaseRing k ⟶ B') (hb : b' ≫ p = structureRingMap k ≫ q)
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology T.carrier) T.sheaf)}
  (ι : FibreInrData p G.val.presheaf)

/-- The inclusion of `𝒢` into the fibre product, as a map into the kernel of the second
projection. -/
def pullbackIdealHomOf (U : (Opens T.carrier)ᵒᵖ) :
    G.val.obj U →+ kernelIdeal (fibreSnd p q).hom U where
  toFun n := ⟨fibreInr p q ι U n, fibreSnd_fibreInr p q ι U n⟩
  map_zero' := Subtype.ext (fibreInr_zero p q ι U)
  map_add' n m := Subtype.ext (fibreInr_add p q ι U n m)

/-- The inclusion of `𝒢` into the fibre product, onto the kernel of the second projection. -/
def pullbackIdealEquivOf (U : (Opens T.carrier)ᵒᵖ) :
    G.val.obj U ≃+ kernelIdeal (fibreSnd p q).hom U :=
  AddEquiv.ofBijective (pullbackIdealHomOf p q ι U)
    ⟨fun n m h => fibreInr_injective p q ι U (congrArg Subtype.val h),
      fun z => by
        obtain ⟨n, hn⟩ := (fibreSnd_app_eq_zero_iff_exists_fibreInr p q ι U z.1).1 z.2
        exact ⟨n, Subtype.ext hn⟩⟩

/-- The equivalence `pullbackIdealEquivOf` sends a section `n` of `𝒢` to its image in the fibre
product. -/
theorem pullbackIdealEquivOf_apply (U : (Opens T.carrier)ᵒᵖ) (n : G.val.obj U) :
    (pullbackIdealEquivOf p q ι U n).1 = fibreInr p q ι U n := rfl

/-- The inverse of `pullbackIdealEquivOf` commutes with restriction of sections. -/
theorem pullbackIdealEquivOf_symm_map {U V : (Opens T.carrier)ᵒᵖ} (i : U ⟶ V)
    (z : kernelIdeal (fibreSnd p q).hom U) :
    (pullbackIdealEquivOf p q ι V).symm ⟨((fibreSheaf p q).obj.map i).hom z.1,
      Stacks.Sites.Conormal.map_kernel _ i z.2⟩ =
      G.val.map i ((pullbackIdealEquivOf p q ι U).symm z) := by
  obtain ⟨n, rfl⟩ := (pullbackIdealEquivOf p q ι U).surjective z
  rw [AddEquiv.symm_apply_apply]
  exact (AddEquiv.symm_apply_eq _).2 (Subtype.ext (fibreInr_map p q ι i n))

/-- **The pullback of an extension `0 ⟶ 𝒢 ⟶ ℬ' ⟶ ℬ ⟶ 0` along `q : 𝒪_T ⟶ ℬ`**, the extension
`0 ⟶ 𝒢 ⟶ ℬ' ×_ℬ 𝒪_T ⟶ 𝒪_T ⟶ 0` of `k⁻¹𝒪_S`-algebras, `𝒢` read over `𝒪_T` through `q`
(`hsmul`) and with square zero in `ℬ'` (`hsq`). -/
def pullbackOfExtension [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T.carrier) p.hom]
    (hsmul : ∀ (U : (Opens T.carrier)ᵒᵖ) (x : B'.obj.obj U) (a : T.sheaf.obj.obj U)
      (n : G.val.obj U), p.hom.app U x = q.hom.app U a →
        x * ι.app U n = ι.app U ((show (Stacks.SheafOfModules.Tensor.ringSheaf
          (J := Opens.grothendieckTopology T.carrier) T.sheaf).obj.obj U from a) • n)) :
    SquareZeroAlgebraExtension k G where
  sheaf := fibreSheaf p q
  base := fibreLift p q b' (structureRingMap k) hb
  reduction := fibreSnd p q
  base_comp_reduction := fibreLift_comp_snd _ _ _ _ _
  reduction_surjective := isLocallySurjective_fibreSnd p q
  ideal :=
    { app U := (pullbackIdealEquivOf p q ι U).symm.toAddMonoidHom
      app_smul U r z := by
        change (pullbackIdealEquivOf p q ι U).symm (r • z) =
          _ • (pullbackIdealEquivOf p q ι U).symm z
        obtain ⟨n, rfl⟩ := (pullbackIdealEquivOf p q ι U).surjective z
        rw [AddEquiv.symm_apply_apply]
        refine (AddEquiv.symm_apply_eq _).2 (Subtype.ext ?_)
        exact (fibreMk_mul_fibreInr p q ι U r n _
          (hsmul U _ _ n (fibreVal_mem p q U r)))
      app_map := pullbackIdealEquivOf_symm_map p q ι }
  ideal_bijective U := (pullbackIdealEquivOf p q ι U).symm.bijective

end PullbackOfExtension

/-! ### The two extensions `𝒪'₁` and `𝒪'₂` of `g⁻¹𝒪_X` by `𝒢` -/

section Extensions

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} {g : Y ⟶ X}
  {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {G : SheafOfModules.{u} (structureSheafRing Y)}
  (P : SquareZeroAlgebraExtension f F) (c : F ⟶ (modulePushforward g).obj G)

/-- The inverse image `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` of the reduction is locally surjective. -/
instance isLocallySurjective_inverseImageReduction_site :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (inverseImageRingedSpace g).carrier)
      (inverseImageReduction (Y := Y) (g := g) P).hom :=
  isLocallySurjective_inverseImageReduction P

variable (G) in
/-- **The extension `𝒪'₁` of Stacks 0GQ2**: the pushout of
`0 ⟶ g⁻¹ℱ ⟶ g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X ⟶ 0` along `c : g⁻¹ℱ ⟶ 𝒢`, an extension
`0 ⟶ 𝒢 ⟶ 𝒪'₁ ⟶ g⁻¹𝒪_X ⟶ 0` of `g⁻¹f⁻¹𝒪_S`-algebras, that is, a square-zero extension over the
ringed space `(Y, g⁻¹𝒪_X)` and its morphism to `S`. Here `g⁻¹ℱ` is the kernel of the inverse
image `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` of the reduction, and `c` on it is `idealMap`. -/
@[stacks 0GQ2]
def inverseImagePushout :
    SquareZeroAlgebraExtension (inverseImageSpaceHom f g) (restrictedModule g G) :=
  @pushoutOfIdealRestriction (inverseImageRingedSpace g) S (inverseImageSpaceHom f g)
    (inverseImageRing (Y := Y) (g := g) P) (inverseImageReduction (Y := Y) (g := g) P)
    (inverseImageBase P) (inverseImageBase_comp_inverseImageReduction P) (restrictedModule g G)
    (idealMap P G c) (isLocallySurjective_inverseImageReduction P)

/-- The comparison `g⁻¹𝒪_{X'} ⟶ 𝒪'₁` of the first displayed diagram of Stacks 0GQ2, over
`g⁻¹𝒪_X`. -/
abbrev inverseImagePushoutMap :
    inverseImageRing (Y := Y) (g := g) P ⟶ (inverseImagePushout G P c).sheaf :=
  pushoutMapOf (T := inverseImageRingedSpace g) (inverseImageReduction (Y := Y) (g := g) P)
    (idealMap P G c)

/-- The first displayed diagram commutes on the right: `g⁻¹𝒪_{X'} ⟶ 𝒪'₁ ⟶ g⁻¹𝒪_X` is the
inverse image of the reduction. -/
theorem inverseImagePushoutMap_comp_reduction :
    inverseImagePushoutMap P c ≫ (inverseImagePushout G P c).reduction =
      inverseImageReduction (Y := Y) (g := g) P :=
  pushoutMapOf_comp_pushoutProj (T := inverseImageRingedSpace g) _ _

/-- The first displayed diagram commutes on the left: on `g⁻¹ℱ` the comparison
`g⁻¹𝒪_{X'} ⟶ 𝒪'₁` is `c : g⁻¹ℱ ⟶ 𝒢` followed by the inclusion of `𝒢`. -/
theorem inverseImagePushoutMap_app_kernel (V : Opens Y.carrier)
    (s : kernelIdeal (inverseImageReduction (Y := Y) (g := g) P).hom (op V)) :
    ((inverseImagePushoutMap P c).hom.app (op V)).hom s.1 =
      (inverseImagePushout G P c).incl (op V) ((idealMap P G c).app (op V) s) := by
  refine (pushoutMk_inl.{u} _ _ _ (op V) s).trans ?_
  let E := pushoutIdealEquivOf (T := inverseImageRingedSpace g) _ (idealMap P G c) (op V)
  let n := (idealMap P G c).app (op V) s
  exact ((congrArg ((inverseImagePushout G P c).incl (op V)) (E.symm_apply_apply n)).symm.trans
    ((inverseImagePushout G P c).incl_ideal (op V) (E n))).symm

variable (Q : SquareZeroAlgebraExtension (g ≫ f) G)

/-- `σ = g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
abbrev inverseImageComorphism :
    (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf ⟶ Y.sheaf :=
  ringedSpaceStructureMap g

/-- The inclusion of the ideal `𝒢` of `𝒪_{Y'}`, in the form the fibre product consumes. -/
def idealInclusion : FibreInrData Q.reduction G.val.presheaf where
  app U :=
    { toFun := Q.incl U
      map_zero' := Q.incl_zero U
      map_add' := Q.incl_add U }
  app_map f n := (Q.incl_map _ f n).symm
  app_injective U := Q.incl_injective U
  range U a := ⟨fun h => ⟨Q.ideal.app U ⟨a, h⟩, Q.incl_ideal U ⟨a, h⟩⟩,
    fun ⟨n, hn⟩ => hn ▸ Q.reduction_incl U n⟩

/-- The structure maps of `𝒪_{Y'}` and of `(Y, g⁻¹𝒪_X)` agree in `𝒪_Y`. -/
theorem base_comp_reduction_eq :
    Q.base ≫ Q.reduction = baseToMid f g ≫ inverseImageComorphism (Y := Y) (g := g) :=
  Q.base_comp_reduction.trans (ringedSpaceStructureMap_comp_eq f g)

/-- **The extension `𝒪'₂` of Stacks 0GQ2**: the pullback of `0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0` along
`g^♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`, the extension `0 ⟶ 𝒢 ⟶ 𝒪_{Y'} ×_{𝒪_Y} g⁻¹𝒪_X ⟶ g⁻¹𝒪_X ⟶ 0` of
`g⁻¹f⁻¹𝒪_S`-algebras; its two projections are the second displayed diagram. -/
@[stacks 0GQ2]
def inverseImagePullback :
    SquareZeroAlgebraExtension (inverseImageSpaceHom f g) (restrictedModule g G) :=
  @pullbackOfExtension (inverseImageRingedSpace g) S (inverseImageSpaceHom f g) Y.sheaf Q.sheaf
    Q.reduction (inverseImageComorphism (Y := Y) (g := g)) Q.base (base_comp_reduction_eq Q)
    (restrictedModule g G) (idealInclusion Q) Q.reduction_surjective
    (fun U x _a n h => (Q.incl_smul U x n).symm.trans
      (congrArg (fun z => Q.incl U ((z : (structureSheafRing Y).obj.obj U) •
        (show G.val.obj U from n))) h))

/-! ### The criterion -/

/-- The setup of Stacks 0GQ1 read on `Y`, as a term of
`Stacks.Deformation.InverseImageExtension.Data`. -/
def inverseImageData : Stacks.Deformation.InverseImageExtension.Data.{u}
    (K := Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f))
    ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf)
    (inverseImageRing (Y := Y) (g := g) P) Y.sheaf Q.sheaf where
  π := inverseImageReduction (Y := Y) (g := g) P
  locallySurjective_π := isLocallySurjective_inverseImageReduction P
  N := pushoutModuleOf (T := inverseImageRingedSpace g) (inverseImageReduction (Y := Y) (g := g) P)
    (G := restrictedModule g G)
  c := pushoutDatumOf (T := inverseImageRingedSpace g) _ (idealMap P G c)
  q := inverseImageComorphism (Y := Y) (g := g)
  p := Q.reduction
  locallySurjective_p := Q.reduction_surjective
  ι := idealInclusion Q
  inr_mul_inr U n m := Q.incl_mul_incl U n m
  smul_inr U b a n hb := (Q.incl_smul U b n).symm.trans
    (congrArg (fun z => Q.incl U ((z : (structureSheafRing Y).obj.obj U) •
      (show G.val.obj U from n))) hb)
  u := inverseImageBase P
  v := Q.base
  base_comm := by
    rw [inverseImageBase_comp_inverseImageReduction]
    exact base_comp_reduction_eq Q

/-- The adjoint transpose `𝒪_{X'} ⟶ g_*𝒪_{Y'}` of `h : g⁻¹𝒪_{X'} ⟶ 𝒪_{Y'}`, on sections. -/
theorem homEquiv_app (h : inverseImageRing (Y := Y) (g := g) P ⟶ Q.sheaf) (U : Opens X.carrier)
    (x : P.sheaf.obj.obj (op U)) :
    ((((adjP g.hom.base).homEquiv _ _ h).hom.app (op U)).hom x) =
      (h.hom.app (op ((Opens.map g.hom.base).obj U))).hom (unitSec g P.sheaf U x) :=
  congrArg (fun t : P.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Q.sheaf =>
    (t.hom.app (op U)).hom x) (Adjunction.homEquiv_unit _ _ _ h)

/-- **Compatibility with the structure maps, on the two sides of the adjunction.** -/
theorem inverseImageBase_comp_eq_iff (h : inverseImageRing (Y := Y) (g := g) P ⟶ Q.sheaf) :
    inverseImageBase P ≫ h = Q.base ↔
      (adjP f.hom.base).homEquiv _ _ P.base ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
            ((adjP g.hom.base).homEquiv _ _ h) =
        (adjP (g ≫ f).hom.base).homEquiv _ _ Q.base := by
  have e : (adjP (g ≫ f).hom.base).homEquiv _ _ (inverseImageBase P ≫ h) =
      (adjP f.hom.base).homEquiv _ _ P.base ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
            ((adjP g.hom.base).homEquiv _ _ h) := by
    refine ((adjP (g ≫ f).hom.base).homEquiv_naturality_right _ _).trans ?_
    refine (congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
      (g ≫ f).hom.base).map h) (homEquiv_inverseImageBase P)).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    change (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
        ((adjP g.hom.base).unit.app P.sheaf) ≫ (TopCat.Sheaf.pushforward CommRingCat.{u}
          f.hom.base).map ((TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map h) = _
    refine ((TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map_comp _ _).symm.trans ?_
    exact congrArg _ (Adjunction.homEquiv_unit _ _ _ h).symm
  rw [← e]
  exact (Equiv.apply_eq_iff_eq _).symm

/-- **Compatibility with the reductions, on the two sides of the adjunction.** -/
theorem comp_reduction_eq_iff (h : inverseImageRing (Y := Y) (g := g) P ⟶ Q.sheaf) :
    h ≫ Q.reduction = inverseImageReduction (Y := Y) (g := g) P ≫
        inverseImageComorphism (Y := Y) (g := g) ↔
      (adjP g.hom.base).homEquiv _ _ h ≫
          (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map Q.reduction =
        P.reduction ≫ (ObjectProperty.homMk g.hom.c : X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Y.sheaf) := by
  have e : (adjP g.hom.base).homEquiv _ _ (inverseImageReduction (Y := Y) (g := g) P ≫
      inverseImageComorphism (Y := Y) (g := g)) =
      P.reduction ≫ (ObjectProperty.homMk g.hom.c : X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Y.sheaf) := by
    have h1 : (adjP g.hom.base).homEquiv _ _ (inverseImageReduction (Y := Y) (g := g) P) =
        P.reduction ≫ (adjP g.hom.base).unit.app X.sheaf :=
      (Adjunction.homEquiv_unit _ _ _ _).trans ((adjP g.hom.base).unit.naturality P.reduction).symm
    refine ((adjP g.hom.base).homEquiv_naturality_right _ _).trans ?_
    refine (congrArg (· ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      (inverseImageComorphism (Y := Y) (g := g))) h1).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (P.reduction ≫ ·) ?_)
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (homEquiv_ringedSpaceStructureMap g)
  rw [← (adjP g.hom.base).homEquiv_naturality_right h Q.reduction, ← e]
  exact (Equiv.apply_eq_iff_eq _).symm

/-- A section of a sheaf of rings on a space is determined by its restrictions to a
neighbourhood of each point. -/
theorem ringSection_ext {T : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} T) {V : Opens T}
    (t t' : R.obj.obj (op V))
    (h : ∀ y ∈ V, ∃ (W : Opens T) (_ : y ∈ W) (i : W ⟶ V),
      (R.obj.map i.op).hom t = (R.obj.map i.op).hom t') : t = t' := by
  choose W hW i hi using fun y : V => h y.1 y.2
  exact R.eq_of_locally_eq' W V i (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hW ⟨y, hy⟩⟩) t t' hi

/-- The image in `g⁻¹𝒪_{X'}` of a section of the ideal of `𝒪_{X'}` lies in the kernel of
`g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X`. -/
theorem unitSec_mem_kernelIdeal (U : Opens X.carrier) (a : kernelIdeal P.reduction.hom (op U)) :
    unitSec g P.sheaf U a.1 ∈
      kernelIdeal (inverseImageReduction (Y := Y) (g := g) P).hom
        (op ((Opens.map g.hom.base).obj U)) := by
  change ((inverseImageReduction (Y := Y) (g := g) P).hom.app _).hom (unitSec g P.sheaf U a.1) = 0
  rw [← unitSec_naturality g P.reduction U a.1, show (P.reduction.hom.app (op U)).hom a.1 = 0
    from a.2, map_zero]

/-- **Compatibility with `c`, on the two sides of the adjunction**: `h : g⁻¹𝒪_{X'} ⟶ 𝒪_{Y'}` is
`c` on the kernel `g⁻¹ℱ` of `g⁻¹𝒪_{X'} ⟶ g⁻¹𝒪_X` exactly when its transpose
`𝒪_{X'} ⟶ g_*𝒪_{Y'}` is `c` on `ℱ`. -/
theorem kernel_comm_iff_homEquiv (h : inverseImageRing (Y := Y) (g := g) P ⟶ Q.sheaf) :
    (∀ (V : Opens Y.carrier) (k : kernelIdeal (inverseImageReduction (Y := Y) (g := g) P).hom
        (op V)), (h.hom.app (op V)).hom k.1 = Q.incl (op V) ((idealMap P G c).app (op V) k)) ↔
      ∀ (U : Opens X.carrier) (s : F.val.obj (op U)),
        ((((adjP g.hom.base).homEquiv _ _ h).hom.app (op U)).hom (P.incl (op U) s)) =
          Q.incl (op ((Opens.map g.hom.base).obj U)) (c.val.app (op U) s) := by
  refine ⟨fun H U s => ?_, fun H V k => ?_⟩
  · let a : kernelIdeal P.reduction.hom (op U) := ⟨P.incl (op U) s, P.incl_mem (op U) s⟩
    refine (homEquiv_app P Q h U _).trans ?_
    refine (H _ ⟨_, unitSec_mem_kernelIdeal P U a⟩).trans ?_
    refine congrArg (Q.incl _) ((idealMap_app_unitSec (G := G) (c := c) U a _).trans ?_)
    exact congrArg (c.val.app (op U)) (P.ideal_incl (op U) s)
  · refine ringSection_ext Q.sheaf _ _ fun y hy => ?_
    obtain ⟨r, hr⟩ := exists_localRep (P := P) V k.1 k.2 y hy
    refine ⟨r.W, hr, homOfLE r.le_V, ?_⟩
    have e1 := NatTrans.naturality_apply h.hom (homOfLE r.le_V).op k.1
    have e2 := NatTrans.naturality_apply h.hom (homOfLE r.le_U).op (unitSec g P.sheaf r.U r.a.1)
    have e3 := homEquiv_app P Q h r.U r.a.1
    have e4 := H r.U (P.ideal.app (op r.U) r.a)
    rw [P.incl_ideal] at e4
    have e5 := Q.incl_map (op ((Opens.map g.hom.base).obj r.U)) (homOfLE r.le_U).op
      (c.val.app (op r.U) (P.ideal.app (op r.U) r.a))
    have e6 := Q.incl_map (op V) (homOfLE r.le_V).op ((idealMap P G c).app (op V) k)
    have e7 := idealMapValue_spec (G := G) (c := c) V k.1 k.2 r
    refine e1.symm.trans ?_
    refine (congrArg (h.hom.app (op r.W)).hom r.eq).trans ?_
    refine e2.trans ?_
    refine (congrArg (Q.sheaf.obj.map (homOfLE r.le_U).op).hom (e3.symm.trans e4)).trans ?_
    refine e5.trans ?_
    refine Eq.trans ?_ e6.symm
    exact congrArg (Q.incl (op r.W)) e7.symm

/-! ### The diagram chase -/

/-- The structure map of `𝒪'₂` is the lift the site-level comparison uses. -/
theorem inverseImagePullback_base :
    (inverseImagePullback Q).base = (inverseImageData P c Q).pullbackExtension.fromBase := by
  refine fibre_hom_ext Q.reduction _ ?_ ?_
  · exact (fibreLift_comp_fst _ _ _ _ (base_comp_reduction_eq Q)).trans
      (fibreLift_comp_fst _ _ _ _ (inverseImageData P c Q).base_comm).symm
  · refine (fibreLift_comp_snd _ _ _ _ (base_comp_reduction_eq Q)).trans
      ((fibreLift_comp_snd _ _ _ _ (inverseImageData P c Q).base_comm).trans ?_).symm
    exact inverseImageBase_comp_inverseImageReduction P

/-- A morphism of extensions `𝒪'₁ ⟶ 𝒪'₂`, read at the level of the site-level comparison. -/
def toAlgebraExtensionHom (φ : inverseImagePushout G P c ⟶ inverseImagePullback Q) :
    Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom (inverseImageData P c Q).pushoutExtension
      (inverseImageData P c Q).pullbackExtension where
  hom := φ.hom
  base_comm := φ.base_hom.trans (inverseImagePullback_base P c Q)
  proj_comm := φ.hom_reduction
  inr_comm U n := by
    let E := pushoutIdealEquivOf (T := inverseImageRingedSpace g) _ (idealMap P G c) U
    let E' := pullbackIdealEquivOf (T := inverseImageRingedSpace g) (G := restrictedModule g G)
      Q.reduction (inverseImageComorphism (Y := Y) (g := g)) (idealInclusion Q) U
    have h := (φ.ideal_hom U (E n)).trans (E.symm_apply_apply n)
    exact ((inverseImagePullback Q).incl_ideal U _).symm.trans
      ((congrArg ((inverseImagePullback Q).incl U) h).trans
        ((congrArg ((inverseImagePullback Q).incl U) (E'.symm_apply_apply n)).symm.trans
          ((inverseImagePullback Q).incl_ideal U (E' n))))

/-- A morphism of extensions `𝒪'₁ ⟶ 𝒪'₂` of the site-level comparison, as a morphism of
square-zero extensions over `(Y, g⁻¹𝒪_X)`. -/
def ofAlgebraExtensionHom
    (e : Stacks.Sites.SqZeroExtension.AlgebraExtension.Hom (inverseImageData P c Q).pushoutExtension
      (inverseImageData P c Q).pullbackExtension) :
    SquareZeroAlgebraExtension.Hom (inverseImagePushout G P c) (inverseImagePullback Q) where
  hom := e.hom
  hom_reduction := e.proj_comm
  base_hom := e.base_comm.trans (inverseImagePullback_base P c Q).symm
  ideal_hom U y := by
    let E := pushoutIdealEquivOf (T := inverseImageRingedSpace g) _ (idealMap P G c) U
    let E' := pullbackIdealEquivOf (T := inverseImageRingedSpace g) (G := restrictedModule g G)
      Q.reduction (inverseImageComorphism (Y := Y) (g := g)) (idealInclusion Q) U
    obtain ⟨n, rfl⟩ := E.surjective y
    have hn : (e.hom.hom.app U).hom (E n).1 = (E' n).1 := e.inr_comm U n
    exact (congrArg E'.symm (Subtype.ext hn)).trans
      ((E'.symm_apply_apply n).trans (E.symm_apply_apply n).symm)

/-- The morphism `g⁻¹𝒪_{X'} ⟶ 𝒪_{Y'}` of the site-level comparison attached to a compatible
`S`-morphism `Y' ⟶ X'`: the adjoint transpose of its comorphism. -/
def compatibleHomOf (m : CompatibleMorphism P Q c) : (inverseImageData P c Q).CompatibleHom where
  hom := ((adjP g.hom.base).homEquiv _ _).symm m.hom
  base_comm := (inverseImageBase_comp_eq_iff P Q _).2
    ((congrArg (fun t => (adjP f.hom.base).homEquiv _ _ P.base ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map t)
        (((adjP g.hom.base).homEquiv _ _).apply_symm_apply m.hom)).trans m.base_comm)
  proj_comm := (comp_reduction_eq_iff P Q _).2
    ((congrArg (fun t => t ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
      Q.reduction) (((adjP g.hom.base).homEquiv _ _).apply_symm_apply m.hom)).trans
        m.reduction_comm)
  kernel_comm U k := (kernel_comm_iff_homEquiv P c Q _).2 (fun U' s =>
    (congrArg (fun t : P.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj Q.sheaf =>
      (t.hom.app (op U')).hom (P.incl (op U') s))
        (((adjP g.hom.base).homEquiv _ _).apply_symm_apply m.hom)).trans (m.ideal_comm U' s))
    U.unop k

/-- The compatible `S`-morphism `Y' ⟶ X'` attached to a morphism `g⁻¹𝒪_{X'} ⟶ 𝒪_{Y'}` of the
site-level comparison: its comorphism is the adjoint transpose. -/
def compatibleMorphismOf (h : (inverseImageData P c Q).CompatibleHom) :
    CompatibleMorphism P Q c where
  hom := (adjP g.hom.base).homEquiv _ _ h.hom
  reduction_comm := (comp_reduction_eq_iff P Q h.hom).1 h.proj_comm
  base_comm := (inverseImageBase_comp_eq_iff P Q h.hom).1 h.base_comm
  ideal_comm := (kernel_comm_iff_homEquiv P c Q h.hom).1 fun V k => h.kernel_comm (op V) k

/-- **Stacks 0GQ2, the diagram chase.** An `S`-morphism `Y' ⟶ X'` compatible with `g` and `c`
exists if and only if `𝒪'₁` and `𝒪'₂` are isomorphic as `g⁻¹f⁻¹𝒪_S`-algebra extensions of
`g⁻¹𝒪_X` by `𝒢`. -/
@[stacks 0GQ2]
theorem nonempty_compatibleMorphism_iff_nonempty_iso :
    Nonempty (CompatibleMorphism P Q c) ↔
      Nonempty (inverseImagePushout G P c ≅ inverseImagePullback Q) :=
  ⟨fun ⟨m⟩ => ⟨SquareZeroAlgebraExtension.isoOfHom (ofAlgebraExtensionHom P c Q
      ((inverseImageData P c Q).comparisonExtensionHom (compatibleHomOf P c Q m)))⟩,
    fun ⟨e⟩ => ⟨compatibleMorphismOf P c Q ((inverseImageData P c Q).compatibleHomOfExtensionHom
      (toAlgebraExtensionHom P c Q e.hom))⟩⟩

end Extensions







end AlgebraicGeometry.RingedSpaceThickening

