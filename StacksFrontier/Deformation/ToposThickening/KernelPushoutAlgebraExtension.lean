module

public import StacksFrontier.Deformation.AlgebraExtension.SiteRestriction
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutFaithful

/-!
# Solutions of an extension problem as extensions of algebras, and pushout

Let `S` be a square-zero extension problem of ringed topoi — the problem (91.13.0.1) of
[Stacks Project, Tag 08UF] — over a morphism `f : X ⟶ B` and a first order thickening
`𝒪_{B'} ⟶ 𝒪_B` of the base, with ideal `𝒥`, prescribed module `ℱ` and prescribed map
`c : f⁻¹𝒥 ⟶ ℱ`. A solution is in particular an extension `0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of
`f⁻¹𝒪_{B'}`-algebras, and it is a solution exactly when the map `c_{𝒪'} : f⁻¹𝒥 ⟶ ℱ` it
induces is `c`. This file makes that precise and deduces, following the source's proof of
[Stacks Project, Tag 0D3Q], that pushout `FT` of solutions along `φ : ℱ ⟶ 𝒢` is an equivalence
as soon as pushout `F` of all extensions of `f⁻¹𝒪_{B'}`-algebras along `φ` is one and
post-composition with `φ` is injective on `Hom(f⁻¹𝒥, ℱ)`.

The base ring of the extensions is any sheaf of rings `𝒜` identified with `f⁻¹𝒪_{B'}` by an
isomorphism `θ` over `𝒪_X`, so that the extensions may be taken over the base ring of
[Stacks Project, Tag 0D3P] for the composite `X ⟶ B'` itself.

## Main definitions

* `...RingedToposExtensionProblem.toAlgebraExtensionFunctor`: a solution as an extension of
  `𝒜`-algebras; it is fully faithful.
* `...RingedToposExtensionProblem.ofAlgebraExtension`: an extension of `𝒜`-algebras inducing `c`
  on the base ideal, as a solution.
* `...RingedToposExtensionProblem.idealMap`: the map `c_{𝒪'} : f⁻¹𝒥 ⟶ ℱ` induced by an extension
  `𝒪'` of `𝒜`-algebras, as a morphism of sheaves of `f⁻¹𝒪_B`-modules.

## Main results

* `...RingedToposExtensionProblem.idealMap_comp`: `c_{𝒪''} = φ ∘ c_{𝒪'}` for a morphism of
  extensions `𝒪' ⟶ 𝒪''` along `φ`.
* `...RingedToposExtensionProblem.isEquivalence_of_isPushoutFunctor`: pushout of solutions is an
  equivalence once pushout of extensions is, and `Hom(f⁻¹𝒥, ℱ) ⟶ Hom(f⁻¹𝒥, 𝒢)` is injective.

## References

* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open CompatibleFirstOrderThickening AlgebraExtension

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)
  {A : Sheaf X.J CommRingCat.{w}} {a : A ⟶ X.O}
  (θ : A ≅ (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
  (hθ : θ.hom ≫ (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
      S.f.fSharpInverseImage = a)

/-! ### Solutions as extensions of algebras -/

/-- **A solution, read as an extension of `𝒜`-algebras** of `𝒪_X` by the prescribed module, the
`𝒜`-algebra structure being the map from the thickened base read through `θ`. -/
abbrev toAlgebraExtension (P : S.CompatibleFirstOrderThickening) : AlgebraExtension a S.G where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  algebraMap := θ.hom ≫ P.baseMap
  algebraMap_reduction := by rw [Category.assoc, P.baseMap_reduction, hθ]
  kernelInclusion := P.kernelInclusion
  kernelZero := P.kernelZero
  kernelUniversal := P.kernelUniversal

/-- The image in an extension `𝒪'` of `𝒜`-algebras of a section of the base ideal `f⁻¹𝒥`. -/
def idealImage {M : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (Q : AlgebraExtension a M) {U : X.Cᵒᵖ} (x : S.I.val.obj U) : Q.extension.obj.obj U :=
  Q.algebraMap.hom.app U (θ.inv.hom.app U
    (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
      S.idealInclusion.val.app U x))

/-- **An extension of `𝒜`-algebras induces the prescribed map on the base ideal**: the image of
a section of `f⁻¹𝒥` is the image of its value under `c`. This is the condition cutting the
solutions out of all extensions. -/
def IsCompatible {M : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (c : S.I ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
        S.f.fSharpInverseImage)).obj M)
    (Q : AlgebraExtension a M) : Prop :=
  ∀ (U : X.Cᵒᵖ) (x : S.I.val.obj U),
    S.idealImage θ Q x = Q.incl (show M.val.obj U from c.val.app U x)

/-- The isomorphism `θ` and its inverse cancel on sections. -/
private theorem hom_app_inv_app (U : X.Cᵒᵖ)
    (y : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    θ.hom.hom.app U (θ.inv.hom.app U y) = y :=
  congrArg (fun k : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶
    (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension => k.hom.app U y)
    θ.inv_hom_id

/-- The reduction carries the image of a section of `f⁻¹𝒪_{B'}` to its image in `𝒪_X`. -/
private theorem reduction_algebraMap_inv {M : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    (hθ : θ.hom ≫ (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
      S.f.fSharpInverseImage = a) (Q : AlgebraExtension a M) (U : X.Cᵒᵖ)
    (r : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    Q.reduction.hom.app U (Q.algebraMap.hom.app U (θ.inv.hom.app U r)) =
      S.f.fSharpInverseImage.hom.app U
        (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U r) := by
  rw [Q.reduction_algebraMap, ← hθ]
  change S.f.fSharpInverseImage.hom.app U
    (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
      (θ.hom.hom.app U (θ.inv.hom.app U r))) = _
  rw [hom_app_inv_app]

/-- A solution, read as an extension of `𝒜`-algebras, induces `c`. -/
theorem isCompatible_toAlgebraExtension (P : S.CompatibleFirstOrderThickening) :
    S.IsCompatible θ S.c (S.toAlgebraExtension θ hθ P) := fun U x => by
  change P.baseMap.hom.app U (θ.hom.hom.app U (θ.inv.hom.app U _)) = _
  rw [hom_app_inv_app]
  exact P.baseMap_ideal U x

/-- **An extension of `𝒜`-algebras inducing `c` on the base ideal, as a solution.** -/
abbrev ofAlgebraExtension (Q : AlgebraExtension a S.G) (hQ : S.IsCompatible θ S.c Q) :
    S.CompatibleFirstOrderThickening where
  extension := Q.extension
  reduction := Q.reduction
  locallySurjective := Q.locallySurjective
  squareZero := Q.squareZero
  baseMap := θ.inv ≫ Q.algebraMap
  baseMap_reduction := by rw [Category.assoc, Q.algebraMap_reduction, ← hθ, Iso.inv_hom_id_assoc]
  kernelInclusion := Q.kernelInclusion
  kernelZero := Q.kernelZero
  kernelUniversal := Q.kernelUniversal
  baseMap_ideal := hQ

/-- **Solutions as extensions of `𝒜`-algebras, as a functor.** -/
abbrev toAlgebraExtensionFunctor :
    S.CompatibleFirstOrderThickening ⥤ AlgebraExtension a S.G where
  obj := S.toAlgebraExtension θ hθ
  map e :=
    { hom := e.hom.hom
      reduction_comm := e.reduction_comm
      algebraMap_comm := (Category.assoc _ _ _).trans (congrArg (θ.hom ≫ ·) e.baseMap_comm)
      kernel_comm := e.kernel_comm }
  map_id _ := MapAlong.ext rfl
  map_comp _ _ := MapAlong.ext rfl

/-- Reading solutions as extensions does not change the map of middle terms of a morphism. -/
@[simp]
theorem toAlgebraExtensionFunctor_map_hom {P Q : S.CompatibleFirstOrderThickening} (e : P ⟶ Q) :
    ((S.toAlgebraExtensionFunctor θ hθ).map e).hom = e.hom.hom :=
  rfl

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]

omit [X.J.HasSheafCompose (forget RingCat.{w})] in
/-- **Every morphism of extensions by a fixed module is an isomorphism**: its map of middle terms
is injective on sections and locally surjective, by the short five lemma on the ideal rows. -/
theorem isIso_mapAlong {M : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
    {P Q : AlgebraExtension a M} (g : P ⟶ Q) : IsIso g :=
  have : IsIso g.hom := (Sheaf.isLocallyBijective_iff_isIso g.hom).1
    ⟨(Sheaf.isLocallyInjective_iff_injective g.hom).2
      (g.injective_app fun _ => Function.injective_id),
      g.isLocallySurjective fun _ => Function.surjective_id⟩
  isIso_of_isIso_hom g

/-- **Reading solutions as extensions of `𝒜`-algebras is fully faithful.** -/
noncomputable def toAlgebraExtensionFullyFaithful :
    (S.toAlgebraExtensionFunctor θ hθ).FullyFaithful where
  preimage g := Hom.toIso
    { hom := g.hom
      reduction_comm := g.reduction_comm
      baseMap_comm := (cancel_epi θ.hom).1 ((Category.assoc _ _ _).symm.trans g.algebraMap_comm)
      kernel_comm := g.kernel_comm }
  map_preimage _ := MapAlong.ext rfl
  preimage_map _ := CompatibleFirstOrderThickening.Iso.ext (CategoryTheory.Iso.ext rfl)

/-- The solution attached to a compatible extension reads back as that extension, up to the
identity of its middle term. -/
noncomputable def toAlgebraExtensionOfAlgebraExtensionIso (Q : AlgebraExtension a S.G)
    (hQ : S.IsCompatible θ S.c Q) :
    (S.toAlgebraExtensionFunctor θ hθ).obj (S.ofAlgebraExtension θ hθ Q hQ) ≅ Q :=
  let g : (S.toAlgebraExtensionFunctor θ hθ).obj (S.ofAlgebraExtension θ hθ Q hQ) ⟶ Q :=
    { hom := 𝟙 _
      reduction_comm := Category.id_comp _
      algebraMap_comm := (Category.comp_id _).trans (Iso.hom_inv_id_assoc θ Q.algebraMap)
      kernel_comm := fun _ _ => rfl }
  haveI := isIso_mapAlong g
  asIso g

/-! ### Morphisms over a change of the ideal module -/

variable {N : SheafOfModules.{w}
  ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)} (φ : S.G ⟶ N)

/-- A morphism of solutions over the change of ideal module `φ`, read as a morphism of extensions
of `𝒜`-algebras along `φ`. -/
def toMapAlong {P : S.CompatibleFirstOrderThickening}
    {R : (changeKernel S φ).CompatibleFirstOrderThickening} (h : KernelChangeHom φ P R) :
    MapAlong φ (S.toAlgebraExtension θ hθ P) ((changeKernel S φ).toAlgebraExtension θ hθ R) where
  hom := h.hom
  reduction_comm := h.reduction_comm
  algebraMap_comm := (Category.assoc _ _ _).trans (congrArg (θ.hom ≫ ·) h.baseMap_comm)
  kernel_comm := h.kernel_comm

/-- A morphism of extensions of `𝒜`-algebras along `φ` between solutions, read as a morphism of
solutions over the change of ideal module. -/
def ofMapAlong {P : S.CompatibleFirstOrderThickening}
    {R : (changeKernel S φ).CompatibleFirstOrderThickening}
    (g : MapAlong φ (S.toAlgebraExtension θ hθ P)
      ((changeKernel S φ).toAlgebraExtension θ hθ R)) : KernelChangeHom φ P R where
  hom := g.hom
  reduction_comm := g.reduction_comm
  baseMap_comm := (cancel_epi θ.hom).1 ((Category.assoc _ _ _).symm.trans g.algebraMap_comm)
  kernel_comm := g.kernel_comm

/-! ### The map induced on the base ideal -/

section IdealMap

variable {M : SheafOfModules.{w}
  ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hθ in
/-- The reduction kills the image of a section of the base ideal. -/
theorem reduction_idealImage (Q : AlgebraExtension a M) {U : X.Cᵒᵖ} (x : S.I.val.obj U) :
    Q.reduction.hom.app U (S.idealImage θ Q x) = 0 := by
  rw [idealImage, S.reduction_algebraMap_inv θ hθ Q U _, S.idealZero U x, map_zero]

include hθ in
/-- The section of the module by which an extension carries a section of the base ideal. -/
def idealMapApp (Q : AlgebraExtension a M) (U : X.Cᵒᵖ) (x : S.I.val.obj U) : M.val.obj U :=
  (Q.exists_incl (S.idealImage θ Q x) (S.reduction_idealImage θ hθ Q x)).choose

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hθ in
/-- `idealMapApp` is the preimage in `ℳ` of the image of a section of the base ideal. -/
theorem incl_idealMapApp (Q : AlgebraExtension a M) (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    Q.incl (S.idealMapApp θ hθ Q U x) = S.idealImage θ Q x :=
  (Q.exists_incl (S.idealImage θ Q x) (S.reduction_idealImage θ hθ Q x)).choose_spec

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The image of a section of the base ideal is additive. -/
theorem idealImage_add (Q : AlgebraExtension a M) {U : X.Cᵒᵖ} (x y : S.I.val.obj U) :
    S.idealImage θ Q (x + y) = S.idealImage θ Q x + S.idealImage θ Q y := by
  unfold idealImage
  rw [← map_add, ← map_add]
  congr 2
  exact map_add (S.idealInclusion.val.app U).hom x y

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The image of a section of the base ideal is natural in the open. -/
theorem idealImage_naturality (Q : AlgebraExtension a M) {U V : X.Cᵒᵖ} (g : U ⟶ V)
    (x : S.I.val.obj U) :
    S.idealImage θ Q (show S.I.val.obj V from S.I.val.map g x) =
      Q.extension.obj.map g (S.idealImage θ Q x) := by
  rw [idealImage, idealImage, ← NatTrans.naturality_apply Q.algebraMap.hom g,
    ← NatTrans.naturality_apply θ.inv.hom g]
  congr 2
  exact PresheafOfModules.naturality_apply S.idealInclusion.val g x

/-- The ring map `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B` along which the base ideal is a module, as a morphism of
presheaves of rings. -/
abbrev baseReductionInverseImagePresheafHom :=
  ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)).hom

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hθ in
/-- `idealMapApp` is additive. -/
theorem idealMapApp_add (Q : AlgebraExtension a M) (U : X.Cᵒᵖ) (x y : S.I.val.obj U) :
    S.idealMapApp θ hθ Q U (x + y) = S.idealMapApp θ hθ Q U x + S.idealMapApp θ hθ Q U y := by
  refine Q.incl_injective ?_
  rw [Q.incl_add, S.incl_idealMapApp, S.incl_idealMapApp, S.incl_idealMapApp, S.idealImage_add]

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hθ in
/-- `idealMapApp` is natural in the open. -/
theorem idealMapApp_naturality (Q : AlgebraExtension a M) {U V : X.Cᵒᵖ} (g : U ⟶ V)
    (x : S.I.val.obj U) :
    S.idealMapApp θ hθ Q V (show S.I.val.obj V from S.I.val.map g x) =
      (show M.val.obj V from M.val.map g (S.idealMapApp θ hθ Q U x)) :=
  Q.incl_injective ((S.incl_idealMapApp θ hθ Q V _).trans ((S.idealImage_naturality θ Q g x).trans
    ((congrArg (Q.extension.obj.map g) (S.incl_idealMapApp θ hθ Q U x)).symm.trans
      (Q.incl_naturality g _).symm)))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hθ in
/-- `c_{𝒪'}` is linear over `f⁻¹𝒪_{B'}`, acting on `𝒥` through `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B` and on `ℳ`
through `f⁻¹𝒪_{B'} ⟶ 𝒪_X`. -/
theorem idealMapApp_smul (Q : AlgebraExtension a M) (U : X.Cᵒᵖ)
    (r : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (x : S.I.val.obj U) :
    S.idealMapApp θ hθ Q U
        (show S.I.val.obj U from
          (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
              ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj.obj U from
            ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U r) • x) =
      (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O).obj.obj U from
          S.f.fSharpInverseImage.hom.app U
            (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U r)) •
        S.idealMapApp θ hθ Q U x := by
  have hs := (S.idealInclusion.val.app U).hom.map_smul
    (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)).obj.obj U from r)
    (show ((SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction))).obj S.I).val.obj U
      from x)
  have hs' : (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U
      from S.idealInclusion.val.app U (show S.I.val.obj U from
        (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
            ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj.obj U from
          ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U r) • x)) =
      r * (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U
        from S.idealInclusion.val.app U x) := hs
  refine Q.incl_injective ?_
  rw [S.incl_idealMapApp, ← S.reduction_algebraMap_inv θ hθ Q U _, ← Q.mul_incl,
    S.incl_idealMapApp, idealImage, idealImage, hs',
    map_mul, map_mul]

variable [Presheaf.IsLocallySurjective X.J S.baseReductionInverseImagePresheafHom]

include hθ in
/-- **The map `c_{𝒪'} : f⁻¹𝒥 ⟶ ℳ` induced by an extension `𝒪'` of `𝒜`-algebras**: a section of
the base ideal is carried by the structure map into the ideal `ℳ` of `𝒪'`. It is linear over
`f⁻¹𝒪_B`, since `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B` is locally surjective. -/
def idealMap (Q : AlgebraExtension a M) :
    S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M :=
  ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective S.baseReductionInverseImagePresheafHom
      ((SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M).isSheaf).symm
    (PresheafOfModules.homMk
      { app := fun U => AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (S.idealMapApp θ hθ Q U) (S.idealMapApp_add θ hθ Q U))
        naturality := fun {U V} g => by
          ext x
          exact S.idealMapApp_naturality θ hθ Q g x }
      fun U r x => S.idealMapApp_smul θ hθ Q U r x)⟩

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- On sections, `c_{𝒪'}` is `idealMapApp`. -/
theorem idealMap_val_app (Q : AlgebraExtension a M) (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    (S.idealMap θ hθ Q).val.app U x = S.idealMapApp θ hθ Q U x :=
  rfl

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The inclusion `ℳ ⟶ 𝒪'` carries `c_{𝒪'}(x)` to the image of `x` in `𝒪'`. -/
theorem incl_idealMap (Q : AlgebraExtension a M) (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    Q.incl (show M.val.obj U from (S.idealMap θ hθ Q).val.app U x) = S.idealImage θ Q x :=
  S.incl_idealMapApp θ hθ Q U x

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Presheaf.IsLocallySurjective X.J S.baseReductionInverseImagePresheafHom] in
/-- Two morphisms out of the base ideal agree when they agree on sections. -/
theorem idealHom_ext {d₁ d₂ : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M}
    (h : ∀ (U : X.Cᵒᵖ) (x : S.I.val.obj U), d₁.val.app U x = d₂.val.app U x) : d₁ = d₂ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => h U x))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **An extension induces `c` exactly when its map on the base ideal is `c`.** -/
theorem idealMap_eq_iff (Q : AlgebraExtension a M)
    (c : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M) :
    S.idealMap θ hθ Q = c ↔ S.IsCompatible θ c Q := by
  constructor
  · rintro rfl U x
    exact (S.incl_idealMap θ hθ Q U x).symm
  · intro hc
    exact S.idealHom_ext fun U x => Q.incl_injective ((S.incl_idealMap θ hθ Q U x).trans (hc U x))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- **`c_{𝒪''} = φ ∘ c_{𝒪'}`** for a morphism of extensions `𝒪' ⟶ 𝒪''` along `φ`. -/
theorem idealMap_comp {M' : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)} {ψ : M ⟶ M'}
    {Q : AlgebraExtension a M} {Q' : AlgebraExtension a M'} (h : MapAlong ψ Q Q') :
    S.idealMap θ hθ Q ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map ψ =
      S.idealMap θ hθ Q' := by
  refine S.idealHom_ext fun U x => Q'.incl_injective ?_
  refine ((h.kernel_comm U _).symm.trans ?_).trans (S.incl_idealMap θ hθ Q' U x).symm
  refine (congrArg (h.hom.hom.app U) (S.incl_idealMapApp θ hθ Q U x)).trans ?_
  rw [idealImage, idealImage, h.algebraMap_apply]

end IdealMap

/-! ### Maps out of the base ideal, read on a module covering it -/

section IdealTransfer

variable {A' : Sheaf X.J CommRingCat.{w}}
  (θ' : A' ⟶ (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)
  {K : SheafOfModules.{w} ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj A')}
  (ι : K ⟶ SheafOfModules.unit ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj A'))
  (hι : ∀ (U : X.Cᵒᵖ) (m : K.val.obj U),
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
      (θ'.hom.app U (show A'.obj.obj U from ι.val.app U m)) = 0)

/-- The section of the base ideal a section of `K` is carried to: the unique one with the same
image in `f⁻¹𝒪_{B'}`. -/
def idealTransferApp (U : X.Cᵒᵖ) (m : K.val.obj U) : S.I.val.obj U :=
  (S.idealUniversal U _ (hι U m)).exists.choose

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The section of the base ideal attached to `m` has the same image in `f⁻¹𝒪_{B'}` as `m`. -/
theorem idealInclusion_idealTransferApp (U : X.Cᵒᵖ) (m : K.val.obj U) :
    (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
      S.idealInclusion.val.app U (S.idealTransferApp θ' ι hι U m)) =
      θ'.hom.app U (show A'.obj.obj U from ι.val.app U m) :=
  (S.idealUniversal U _ (hι U m)).exists.choose_spec

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The inclusion of the base ideal into `f⁻¹𝒪_{B'}` is injective on sections. -/
theorem idealInclusion_injective_app (U : X.Cᵒᵖ) {x y : S.I.val.obj U}
    (h : (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U x) =
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U y)) : x = y := by
  have hy := S.idealZero U y
  obtain ⟨z, -, hz⟩ := S.idealUniversal U _ hy
  exact (hz x h).trans (hz y rfl).symm

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- `idealTransferApp` is additive. -/
theorem idealTransferApp_add (U : X.Cᵒᵖ) (m m' : K.val.obj U) :
    S.idealTransferApp θ' ι hι U (m + m') =
      S.idealTransferApp θ' ι hι U m + S.idealTransferApp θ' ι hι U m' := by
  refine S.idealInclusion_injective_app U ?_
  have h1 := map_add (S.idealInclusion.val.app U).hom (S.idealTransferApp θ' ι hι U m)
    (S.idealTransferApp θ' ι hι U m')
  have h2 := map_add (ι.val.app U).hom m m'
  refine (S.idealInclusion_idealTransferApp θ' ι hι U _).trans ?_
  refine Eq.trans ?_ h1.symm
  refine (congrArg (θ'.hom.app U) h2).trans ((map_add _ _ _).trans ?_)
  exact congrArg₂ (· + ·) (S.idealInclusion_idealTransferApp θ' ι hι U m).symm
    (S.idealInclusion_idealTransferApp θ' ι hι U m').symm

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- `idealTransferApp` is natural in the open. -/
theorem idealTransferApp_naturality {U V : X.Cᵒᵖ} (g : U ⟶ V) (m : K.val.obj U) :
    S.idealTransferApp θ' ι hι V (show K.val.obj V from K.val.map g m) =
      (show S.I.val.obj V from S.I.val.map g (S.idealTransferApp θ' ι hι U m)) := by
  refine S.idealInclusion_injective_app V ?_
  refine (S.idealInclusion_idealTransferApp θ' ι hι V _).trans ?_
  have h1 := PresheafOfModules.naturality_apply S.idealInclusion.val g
    (S.idealTransferApp θ' ι hι U m)
  have h2 := PresheafOfModules.naturality_apply ι.val g m
  refine Eq.trans ?_ h1.symm
  refine (congrArg (θ'.hom.app V) h2).trans ?_
  refine (NatTrans.naturality_apply θ'.hom g _).trans ?_
  exact congrArg (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.map g)
    (S.idealInclusion_idealTransferApp θ' ι hι U m).symm

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- `idealTransferApp` is linear, a section `r` of `𝒜'` acting on the base ideal through `θ'`
and `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B`. -/
theorem idealTransferApp_smul (U : X.Cᵒᵖ)
    (r : ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj A').obj.obj U)
    (m : K.val.obj U) :
    S.idealTransferApp θ' ι hι U (r • m) =
      (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj.obj U from
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
          (θ'.hom.app U (show A'.obj.obj U from r))) • S.idealTransferApp θ' ι hι U m := by
  refine S.idealInclusion_injective_app U ?_
  refine (S.idealInclusion_idealTransferApp θ' ι hι U _).trans ?_
  have h1 := (S.idealInclusion.val.app U).hom.map_smul
    (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension)).obj.obj U from
        θ'.hom.app U (show A'.obj.obj U from r))
    (show ((SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map
        ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction))).obj S.I).val.obj U
      from S.idealTransferApp θ' ι hι U m)
  have h2 := (ι.val.app U).hom.map_smul r m
  refine Eq.trans ?_ h1.symm
  refine (congrArg (θ'.hom.app U) h2).trans ?_
  refine (map_mul (θ'.hom.app U).hom _ _).trans ?_
  exact congrArg (θ'.hom.app U (show A'.obj.obj U from r) * ·)
    (S.idealInclusion_idealTransferApp θ' ι hι U m).symm

variable {M : SheafOfModules.{w}
  ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)}
  (ρ : (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj A' ⟶
    (sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)
  (hρ : ∀ (U : X.Cᵒᵖ)
    (r : ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj A').obj.obj U),
    ρ.hom.app U r = S.f.fSharpInverseImage.hom.app U
      (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
        (θ'.hom.app U (show A'.obj.obj U from r))))

include hρ in
/-- **A map `d : f⁻¹𝒥 ⟶ ℳ`, read on `K`**: `m ↦ d(m̄)`, with `m̄` the section of the base ideal
with the same image in `f⁻¹𝒪_{B'}`. -/
def idealTransfer (d : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M) :
    K ⟶ (SheafOfModules.restrictScalars ρ).obj M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun m => d.val.app U (S.idealTransferApp θ' ι hι U m)) fun m m' => by
          rw [S.idealTransferApp_add]
          exact map_add (d.val.app U).hom _ _)
      naturality := fun {U V} g => by
        ext m
        exact (congrArg (d.val.app V) (S.idealTransferApp_naturality θ' ι hι g m)).trans
          (PresheafOfModules.naturality_apply d.val g _) }
    fun U r m => by
      change d.val.app U (S.idealTransferApp θ' ι hι U (r • m)) =
        (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O).obj.obj U from
          ρ.hom.app U r) • (show M.val.obj U from d.val.app U (S.idealTransferApp θ' ι hι U m))
      rw [hρ U r]
      exact (congrArg (d.val.app U) (S.idealTransferApp_smul θ' ι hι U r m)).trans
        ((d.val.app U).hom.map_smul _ _)⟩

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hρ in
/-- On sections, `idealTransfer d` is `d` applied to `idealTransferApp`. -/
theorem idealTransfer_app (d : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M)
    (U : X.Cᵒᵖ) (m : K.val.obj U) :
    (S.idealTransfer θ' ι hι ρ hρ d).val.app U m = d.val.app U (S.idealTransferApp θ' ι hι U m) :=
  rfl

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hρ in
/-- Reading on `K` commutes with postcomposition with a map of modules `ℳ ⟶ ℳ'`. -/
theorem idealTransfer_comp {M' : SheafOfModules.{w}
      ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O)} (ψ : M ⟶ M')
    (d : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M) :
    S.idealTransfer θ' ι hι ρ hρ (d ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map ψ) =
      S.idealTransfer θ' ι hι ρ hρ d ≫ (SheafOfModules.restrictScalars ρ).map ψ :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] in
include hρ in
/-- **Reading on `K` is injective** when every section of the base ideal is carried from `K`. -/
theorem idealTransfer_injective
    (hsurj : ∀ (U : X.Cᵒᵖ)
      (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U),
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U a = 0 →
        ∃ m : K.val.obj U, θ'.hom.app U (show A'.obj.obj U from ι.val.app U m) = a)
    {d₁ d₂ : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
      (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj M}
    (h : S.idealTransfer θ' ι hι ρ hρ d₁ = S.idealTransfer θ' ι hι ρ hρ d₂) : d₁ = d₂ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  obtain ⟨m, hm⟩ := hsurj U _ (S.idealZero U x)
  have hx : S.idealTransferApp θ' ι hι U m = x :=
    S.idealInclusion_injective_app U ((S.idealInclusion_idealTransferApp θ' ι hι U m).trans hm)
  have := congrArg (fun k => k.val.app U m) h
  rw [S.idealTransfer_app, S.idealTransfer_app, hx] at this
  exact this

end IdealTransfer

/-! ### Pushout of solutions -/

section Pushout

variable [Presheaf.IsLocallySurjective X.J S.baseReductionInverseImagePresheafHom]
  {F : AlgebraExtension a S.G ⥤ AlgebraExtension a N} (hF : IsPushoutFunctor φ F)
  {FT : S.CompatibleFirstOrderThickening ⥤ (changeKernel S φ).CompatibleFirstOrderThickening}
  (j : ∀ P, KernelChangeHom φ P (FT.obj P))
  (hj : ∀ {P Q : S.CompatibleFirstOrderThickening} (k : P ⟶ Q),
      (j P).hom ≫ (FT.map k).hom.hom = k.hom.hom ≫ (j Q).hom)

/-- The comparison `F(𝒪') ⟶ FT(𝒪')` of the two pushouts of a solution, the factorisation of the
comparison `𝒪' ⟶ FT(𝒪')` through the pushout `F(𝒪')` of all extensions. -/
noncomputable def pushoutComparison (P : S.CompatibleFirstOrderThickening) :
    F.obj ((S.toAlgebraExtensionFunctor θ hθ).obj P) ⟶
      ((changeKernel S φ).toAlgebraExtensionFunctor θ hθ).obj (FT.obj P) :=
  (hF.desc_unique _ _ (S.toMapAlong θ hθ φ (j P))).choose

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Presheaf.IsLocallySurjective X.J S.baseReductionInverseImagePresheafHom] in
/-- `pushoutComparison` is a factorisation of `j P` through the pushout `ι`. -/
theorem pushoutComparison_spec (P : S.CompatibleFirstOrderThickening) :
    (hF.ι _).hom ≫ (S.pushoutComparison θ hθ φ hF j P).hom = (j P).hom :=
  (hF.desc_unique _ _ (S.toMapAlong θ hθ φ (j P))).choose_spec.1

include hj in
/-- **The two pushouts of a solution agree**: `FT` followed by reading solutions as extensions is
reading solutions as extensions followed by `F`. -/
noncomputable def pushoutComparisonIso :
    S.toAlgebraExtensionFunctor θ hθ ⋙ F ≅
      FT ⋙ (changeKernel S φ).toAlgebraExtensionFunctor θ hθ :=
  NatIso.ofComponents
    (fun P => haveI := isIso_mapAlong (S.pushoutComparison θ hθ φ hF j P)
      asIso (S.pushoutComparison θ hθ φ hF j P))
    fun {P P'} m => by
      let h : MapAlong φ ((S.toAlgebraExtensionFunctor θ hθ).obj P)
          (((changeKernel S φ).toAlgebraExtensionFunctor θ hθ).obj (FT.obj P')) :=
        MapAlong.comp ((S.toAlgebraExtensionFunctor θ hθ).map m) (S.toMapAlong θ hθ φ (j P'))
          (Category.id_comp φ)
      obtain ⟨k, -, hk⟩ := hF.desc_unique _ _ h
      refine (hk _ ?_).trans (hk _ ?_).symm
      · change (hF.ι _).hom ≫ (F.map _).hom ≫ (S.pushoutComparison θ hθ φ hF j P').hom = _
        rw [← Category.assoc, hF.naturality, Category.assoc, pushoutComparison_spec]
        rfl
      · change (hF.ι _).hom ≫ (S.pushoutComparison θ hθ φ hF j P).hom ≫ (FT.map m).hom.hom = _
        rw [← Category.assoc, pushoutComparison_spec, hj]
        rfl

variable [F.IsEquivalence]

include θ hθ hF hj in
/-- **[Stacks Project, Tag 0D3Q], the reduction to [Stacks Project, Tag 0D3P].** Pushout `FT` of
solutions along `φ : ℱ ⟶ 𝒢` is an equivalence once pushout `F` of all extensions of
`𝒜`-algebras along `φ` is one and post-composition with `φ` is injective on the maps
`f⁻¹𝒥 ⟶ ℱ` of `f⁻¹𝒪_B`-modules. The solutions are the full subcategory of the extensions on which
`c_{𝒪'} = c`; `F` carries it into the one on which `c_{𝒪''} = φ ∘ c`, and the injectivity says that
an extension whose pushout lies there lies in the first one. -/
theorem isEquivalence_of_isPushoutFunctor
    (hinj : ∀ d₁ d₂ : S.I ⟶ (SheafOfModules.restrictScalars ((sheafCompose X.J
        (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).obj S.G,
      d₁ ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map φ =
        d₂ ≫ (SheafOfModules.restrictScalars ((sheafCompose X.J
          (forget₂ CommRingCat.{w} RingCat.{w})).map S.f.fSharpInverseImage)).map φ →
        d₁ = d₂) :
    FT.IsEquivalence := by
  let ιG := (changeKernel S φ).toAlgebraExtensionFunctor θ hθ
  have hιG := (changeKernel S φ).toAlgebraExtensionFullyFaithful θ hθ
  have := (S.toAlgebraExtensionFullyFaithful θ hθ).full
  have := (S.toAlgebraExtensionFullyFaithful θ hθ).faithful
  have := hιG.full
  have := hιG.faithful
  let e := S.pushoutComparisonIso θ hθ φ hF j hj
  have : (FT ⋙ ιG).Full := Functor.Full.of_iso e
  have : (FT ⋙ ιG).Faithful := Functor.Faithful.of_iso e
  have : FT.Faithful := Functor.Faithful.of_comp FT ιG
  have : FT.Full := Functor.Full.of_comp_faithful FT ιG
  have : FT.EssSurj := ⟨fun R => by
    let P₀ := F.objPreimage (ιG.obj R)
    let u : F.obj P₀ ≅ ιG.obj R := F.objObjPreimageIso (ιG.obj R)
    let h : MapAlong φ P₀ (ιG.obj R) := MapAlong.comp (hF.ι P₀) u.hom (Category.comp_id φ)
    have hc : S.idealMap θ hθ P₀ = S.c :=
      hinj _ _ ((S.idealMap_comp θ hθ h).trans
        (((changeKernel S φ).idealMap_eq_iff θ hθ _ _).2
          ((changeKernel S φ).isCompatible_toAlgebraExtension θ hθ R)))
    have hP₀ : S.IsCompatible θ S.c P₀ := (S.idealMap_eq_iff θ hθ P₀ S.c).1 hc
    let P := S.ofAlgebraExtension θ hθ P₀ hP₀
    refine ⟨P, ⟨hιG.preimageIso ?_⟩⟩
    exact e.symm.app P ≪≫ F.mapIso (S.toAlgebraExtensionOfAlgebraExtensionIso θ hθ P₀ hP₀) ≪≫ u⟩
  exact { }

end Pushout

end Deformation.ToposThickening.RingedToposExtensionProblem

end
