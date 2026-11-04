module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorsInclusion
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorSupport
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InversePairing
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiOver

/-!
# The denominator ideal acting on a coherent module

Let `X` be a locally Noetherian scheme, `L` an invertible `𝒪_X`-module and `s` a regular
meromorphic section of `L`, with ideal of denominators `I` (Tag 02P0). Let `F` be coherent,
with full support and no embedded associated points. This file constructs the product `I F`
together with the two canonical injections of
[Stacks, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
`1 : I F ⟶ F` and `s : I F ⟶ F ⊗ L`,
and bounds both their cokernels by the union of the two cokernel supports of Tag 02P0.

## Main definitions

* `AlgebraicGeometry.denominatorIdealAction`: the action `I ⊗ F ⟶ F`.
* `AlgebraicGeometry.denominatorIdealTimesModule`: the product `I F`, as the image of that
  action.
* `AlgebraicGeometry.denominatorIdealTimesModuleι`: the first canonical map `I F ⟶ F`.
* `AlgebraicGeometry.denominatorIdealSectionTensor`: multiplication by `s` before taking that
  image, as a map `I ⊗ F ⟶ F ⊗ L`.
* `AlgebraicGeometry.denominatorIdealTimesModuleMul`: the second canonical map
  `I F ⟶ F ⊗ L`, characterised by its composite with the epimorphism onto the image.
* `AlgebraicGeometry.denominatorBadLocus`: the union of the supports of the two Tag 02P0
  cokernels.

## Main results

* `AlgebraicGeometry.denominatorIdealTimesModuleι_mono` and
  `AlgebraicGeometry.denominatorIdealTimesModuleMul_mono`: both maps are injective.
* `AlgebraicGeometry.denominatorBadLocus_isClosed` and
  `AlgebraicGeometry.denominatorBadLocus_isNowhereDense`: the exceptional subset is closed and
  nowhere dense.
* `AlgebraicGeometry.denominatorIdealTimesModuleι_cokernel_support` and
  `AlgebraicGeometry.denominatorIdealTimesModuleMul_cokernel_supp`: both cokernels are
  supported on it.

## Implementation notes

The product `I F` is the image of the canonical action map out of the tensor product, so the
first map is the image inclusion and is a monomorphism by construction. The second map is not
a choice of embedding: it is pinned down by requiring that its composite with
`CategoryTheory.Abelian.factorThruImage` be multiplication by `s` on `I ⊗ F`, which is why
`AlgebraicGeometry.denominatorIdealTimesModuleMul` returns a subtype rather than a bare
morphism. Its existence is the one place where the hypotheses on `F` are used: the two kernels
`ker(I ⊗ F ⟶ F)` and `ker(I ⊗ F ⟶ F ⊗ L)` have to die under the other map, and
that is checked stalkwise at the associated points of `F`, which by the absence of embedded
points are the generic points of the irreducible components of `X` and therefore avoid the
nowhere dense exceptional set.

## References

* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.Invertible

universe u

namespace AlgebraicGeometry


variable (X : Scheme.{u})

/-- Sheafification of presheaves of abelian groups on the opens of `X` exists. -/
local instance : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- A morphism of presheaves of abelian groups on `X` becomes an isomorphism after
sheafification if and only if it is locally bijective. -/
local instance : (Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The category of sheaves of `𝒪_X`-modules is abelian. -/
local instance : Abelian (_root_.SheafOfModules.{u} X.ringCatSheaf) := inferInstance

open Scheme.Modules in
/-- The kernel of a morphism of quasi-coherent modules is quasi-coherent. This is
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, restated as an ordinary lemma
because that instance's binders are typed `X.Modules`, which is a `def`, so instance search does
not match a module spelled `_root_.SheafOfModules X.ringCatSheaf` against it, while an explicit
application does. -/
private lemma isQuasicoherent_kernel {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel f

/-- The cokernel of a morphism of quasi-coherent modules is quasi-coherent. This is
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`; see
`isQuasicoherent_kernel` for why it is restated rather than inferred. -/
private lemma isQuasicoherent_cokernel {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel f


private theorem stalk_surjective_of_not_mem_cokernel_support
    {F G : SheafOfModules.{u} X.ringCatSheaf} (f : G ⟶ F) (x : X)
    (hx : x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel f)).supp) :
    Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      G.val F.val f.val x) := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hx' : x ∉ SheafOfModules.supp (cokernel f) := by
    intro hs
    apply hx
    have hmem : x ∈
        (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
          (cokernel f)).supp := by
      rw [SheafOfModules.supp_eq_moduleSheaf_supp]
      exact hs
    exact hmem
  have hzeroStalk : ∀ a : T.obj (cokernel f), a = 0 := by
    intro a
    by_contra ha
    exact hx' ⟨a, ha⟩
  have hzero : IsZero (T.obj (cokernel f)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun a b => ?_⟩
    have ha := hzeroStalk (a - b)
    exact sub_eq_zero.mp ha
  have hzeroCok : IsZero (cokernel (T.map f)) :=
    IsZero.of_iso hzero (PreservesCokernel.iso T f).symm
  have hπ : cokernel.π (T.map f) = 0 := hzeroCok.eq_of_tgt _ _
  have hepi : Epi (T.map f) := Abelian.epi_of_cokernel_π_eq_zero _ hπ
  exact (ModuleCat.epi_iff_surjective (T.map f)).mp hepi

private theorem stalk_tensorMap_surjective_of_stalk_surjective
    {A B G : SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B) (x : X)
    (hf : Function.Surjective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val B.val f.val x))
        :
    Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G)).val
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G)).val
      ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))).map
        (X := (A, G)) (Y := (B, G)) (f, 𝟙 G)).val) x) := by
  let idG : G ⟶ G := 𝟙 G
  let : Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace A.val x) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace A.val x
  let : Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace B.val x) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace B.val x
  let : Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x
  let : Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val x) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val x
  let : Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val x) :=
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val x
  show Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          ((f, idG) : (A, G) ⟶ (B, G)))).val x)
  let Q := Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x
  let e₁ := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x A G
  let e₂ := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x B G
  have hs := LinearMap.rTensor_surjective Q hf
  intro y
  obtain ⟨z, hz⟩ := hs (e₂ y)
  refine ⟨e₁.symm z, ?_⟩
  have hnat := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural X.toRingedSpace x
    A G B G f idG
  have hid : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace G.val G.val
    idG.val x =
      LinearMap.id := by
    ext z
    exact congrArg (fun k => k z)
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map_id G)
  have he := LinearMap.congr_fun hnat (e₁.symm z)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hid] at he
  rw [← LinearMap.rTensor_def] at he
  apply e₂.injective
  calc
    e₂ (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          ((f, idG) : (A, G) ⟶ (B, G)))).val x
        (e₁.symm z)) =
        LinearMap.rTensor Q
          (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val B.val f.val
            x)
          (e₁ (e₁.symm z)) := he.symm
    _ = LinearMap.rTensor Q
          (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val B.val f.val
            x) z := by
      rw [e₁.apply_symm_apply]
    _ = e₂ y := hz

private theorem not_mem_cokernel_support_of_stalk_surjective
    {F G : SheafOfModules.{u} X.ringCatSheaf} (f : F ⟶ G) (x : X)
    (hsurj : Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL
      X.toRingedSpace F.val G.val f.val x)) :
    x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel f)).supp := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hepi : Epi (T.map f) := (ModuleCat.epi_iff_surjective (T.map f)).2 hsurj
  have hzeroCok : IsZero (cokernel (T.map f)) := isZero_cokernel_of_epi (T.map f)
  have hzero : IsZero (T.obj (cokernel f)) :=
    IsZero.of_iso hzeroCok (PreservesCokernel.iso T f)
  have hx' : x ∉ SheafOfModules.supp (cokernel f) := by
    intro hx
    change ∃ a : T.obj (cokernel f), a ≠ 0 at hx
    rcases hx with ⟨a, ha⟩
    have hsub : Subsingleton (T.obj (cokernel f)) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    exact ha (hsub.elim a 0)
  intro hx
  change x ∈
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (cokernel f)).supp at hx
  rw [SheafOfModules.supp_eq_moduleSheaf_supp] at hx
  exact hx' hx

private theorem stalk_surjective_of_iso
    {F G : SheafOfModules.{u} X.ringCatSheaf} (f : F ⟶ G) (x : X) [IsIso f] :
    Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      F.val G.val f.val x) := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have : IsIso (T.map f) := Functor.map_isIso T f
  exact (ModuleCat.epi_iff_surjective (T.map f)).mp inferInstance

private theorem stalk_surjective_comp
    {F G H : SheafOfModules.{u} X.ringCatSheaf} (f : F ⟶ G) (g : G ⟶ H) (x : X)
    (hf : Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL
      X.toRingedSpace
      F.val G.val f.val x))
    (hg : Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL
      X.toRingedSpace
      G.val H.val g.val x)) :
    Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      F.val H.val (f ≫ g).val x) := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hEpiF : Epi (T.map f) := (ModuleCat.epi_iff_surjective (T.map f)).2 hf
  have hEpiG : Epi (T.map g) := (ModuleCat.epi_iff_surjective (T.map g)).2 hg
  have hEpi : Epi (T.map (f ≫ g)) := by
    rw [T.map_comp]
    infer_instance
  exact (ModuleCat.epi_iff_surjective (T.map (f ≫ g))).mp hEpi

/-- Tensoring a stalkwise surjective map with `G` and composing with an isomorphism is stalkwise
surjective. -/
private theorem stalk_surjective_tensorMap_comp_iso
    {A B G C : SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B)
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G) ≅ C) (x : X)
    (hf : Function.Surjective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val B.val
        f.val x)) :
    Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G)).val C.val
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (X := (A, G)) (Y := (B, G)) (f, 𝟙 G) ≫ e.hom).val) x) :=
  have : IsIso (C := _root_.SheafOfModules.{u} X.ringCatSheaf) e.hom := Iso.isIso_hom e
  stalk_surjective_comp X _ _ x (stalk_tensorMap_surjective_of_stalk_surjective X f x hf)
    (stalk_surjective_of_iso X e.hom x)

universe v w

private def imageDesc {C : Type v} [Category.{w} C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : A ⟶ D)
    (h : kernel.ι a ≫ b = 0) : Abelian.image a ⟶ D :=
  (Abelian.coimageIsoImage a).inv ≫ cokernel.desc (kernel.ι a) b h

private theorem factorThruImage_imageDesc {C : Type v} [Category.{w} C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : A ⟶ D)
    (h : kernel.ι a ≫ b = 0) :
    Abelian.factorThruImage a ≫ imageDesc a b h = b := by
  have he : cokernel.π (kernel.ι a) ≫ (Abelian.coimageIsoImage a).hom =
      Abelian.factorThruImage a := by
    simp [Abelian.coimageIsoImage, Abelian.coimageImageComparison]
  rw [← he]
  simp [imageDesc]

private theorem mono_imageDesc {C : Type v} [Category.{w} C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : A ⟶ D)
    (hab : kernel.ι a ≫ b = 0) (hba' : kernel.ι b ≫ Abelian.factorThruImage a = 0) :
    Mono (imageDesc a b hab) := by
  have hab' : kernel.ι a ≫ Abelian.factorThruImage b = 0 := by
    apply (cancel_mono (Abelian.image.ι b)).1
    simpa using hab
  let f := imageDesc a (Abelian.factorThruImage b) hab'
  let g := imageDesc b (Abelian.factorThruImage a) hba'
  have hfg : f ≫ g = 𝟙 _ := by
    apply (cancel_epi (Abelian.factorThruImage a)).1
    simp only [← Category.assoc, f, factorThruImage_imageDesc, g, Category.comp_id]
  have : Mono f := mono_of_mono_fac hfg
  have he : f ≫ Abelian.image.ι b = imageDesc a b hab := by
    apply (cancel_epi (Abelian.factorThruImage a)).1
    simp only [← Category.assoc, f, factorThruImage_imageDesc, Abelian.image.fac]
  rw [← he]
  infer_instance

private theorem epi_right_factor {C : Type v} [Category.{w} C]
    {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (h : Epi (f ≫ g)) : Epi g := by
  constructor
  intro Z a b hab
  let : Epi (f ≫ g) := h
  apply (cancel_epi (f ≫ g)).mp
  simpa only [Category.assoc] using congrArg (fun k => f ≫ k) hab

/-- If `a ≫ m = c` and `c` is stalkwise surjective at `x`, then `x` is not in the support of the
cokernel of `m`. -/
private theorem not_mem_cokernel_support_of_factor
    {A B C : SheafOfModules.{u} X.ringCatSheaf} (a : A ⟶ B) (m : B ⟶ C) (c : A ⟶ C)
    (hc : a ≫ m = c) (x : X)
    (h : Function.Surjective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val C.val
        c.val x)) :
    x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel m)).supp := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hsplit : T.map a ≫ T.map m = T.map c := (T.map_comp _ _).symm.trans (congrArg T.map hc)
  have hEpi : Epi (T.map a ≫ T.map m) := by
    rw [hsplit]
    exact (ModuleCat.epi_iff_surjective (T.map c)).2 h
  exact not_mem_cokernel_support_of_stalk_surjective X m x
    ((ModuleCat.epi_iff_surjective (T.map m)).1 (epi_right_factor _ _ hEpi))

/-- A functor sends a composite whose two images are monomorphisms to a monomorphism. Stated
for a bare pair of categories on purpose: at the geometry the same `rw [T.map_comp]` cannot form
its motive, because the stalk functor's type mentions `X.ringCatSheaf.obj`, which is not
type-correct at the `implicit` transparency level that motive type-checking uses. Here there is
nothing to unfold, so the rewrite goes through and the consumer applies this as a term. -/
private theorem mono_functor_map_comp {C D : Type v} [Category.{w} C] [Category.{w} D]
    (T : C ⥤ D) {A B E : C} (a : A ⟶ B) (b : B ⟶ E)
    (ha : Mono (T.map a)) (hb : Mono (T.map b)) : Mono (T.map (a ≫ b)) := by
  rw [T.map_comp]
  exact @mono_comp _ _ _ _ _ _ ha _ hb

/-- A functor sends an isomorphism to a monomorphism. -/
private theorem mono_functor_map_of_isIso {C D : Type v} [Category.{w} C] [Category.{w} D]
    (T : C ⥤ D) {A B : C} (e : A ≅ B) : Mono (T.map e.hom) :=
  have : IsIso (T.map e.hom) := (T.mapIso e).isIso_hom
  mono_of_mono_fac (IsIso.hom_inv_id _)

/-- The canonical action of the denominator ideal on a module. -/
noncomputable def denominatorIdealAction
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (denominatorIdeal X L s)).obj F) ⟶
        F :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))).map
      (X := (denominatorIdeal X L s, F))
      (Y := (SheafOfModules.unit X.ringCatSheaf, F))
      (denominatorIdealι X L s, 𝟙 F) ≫
    (tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property F).hom

/-- The product `I F`, as a subobject of `F`. -/
@[stacks 02P2 "the product of the denominator ideal and the module"]
noncomputable def denominatorIdealTimesModule
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    SheafOfModules.{u} X.ringCatSheaf :=
  Abelian.image (denominatorIdealAction X L F s)

/-- The inclusion `I F ⟶ F`. -/
@[stacks 02P2 "the first canonical map"]
noncomputable def denominatorIdealTimesModuleι
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    denominatorIdealTimesModule X L F s ⟶ F :=
  Abelian.image.ι (denominatorIdealAction X L F s)

/-- Multiplication by the section before taking the image defining `I F`. -/
noncomputable def denominatorIdealSectionTensor
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (denominatorIdeal X L s)).obj F) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj L) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))).map
      (X := (denominatorIdeal X L s, F)) (Y := (L, F))
      (denominatorIdealMul X L s, 𝟙 F) ≫
      (tensorProductBraiding X.sheaf.obj X.ringCatSheaf.property L F).hom

/-- The action `I ⊗ F ⟶ F`, equal to `denominatorIdealAction X L F s`. -/
private noncomputable abbrev actionMod
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (denominatorIdeal X L s)).obj F) ⟶
        F :=
  denominatorIdealAction X L F s

/-- Multiplication by `s` as a map `I ⊗ F ⟶ F ⊗ L`, equal to
`denominatorIdealSectionTensor X L F s`. -/
private noncomputable abbrev sectionTensorMod
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (denominatorIdeal X L s)).obj F) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj L) :=
  denominatorIdealSectionTensor X L F s

/-- The union of the supports of the cokernels of `denominatorIdealι X L s` and
`denominatorIdealMul X L s`. -/
noncomputable def denominatorBadLocus
    (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) : Set X :=
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (cokernel (denominatorIdealι X L s))).supp ∪
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (cokernel (denominatorIdealMul X L s))).supp

/-- If `L` is invertible and `s` is a regular meromorphic section of `L` on a locally Noetherian
scheme, then `denominatorBadLocus X L s` is closed. -/
@[stacks 02P2 "the exceptional subset is closed"]
theorem denominatorBadLocus_isClosed
    (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    IsClosed (denominatorBadLocus X L s) := by
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  let : L.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  let : (SheafOfModules.unit X.ringCatSheaf).IsFiniteType :=
    SheafOfModules.IsCoherent.isFiniteType
  let : L.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have key : ∀ {M N : SheafOfModules.{u} X.ringCatSheaf} [N.IsFiniteType] (f : M ⟶ N),
      IsClosed (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel f)).supp := by
    intro M N _ f
    have : (cokernel f).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_of_epi.{u, u, u} (cokernel.π f) inferInstance
    show IsClosed ((AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel f)).supp)
    rw [SheafOfModules.supp_eq_moduleSheaf_supp]
    exact SheafOfModules.isClosed_supp _
  show IsClosed
    ((AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        (cokernel (denominatorIdealι X L s))).supp ∪
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        (cokernel (denominatorIdealMul X L s))).supp)
  exact (key _).union (key _)

/-- If `L` is invertible and `s` is a regular meromorphic section of `L` on a locally Noetherian
scheme, then `denominatorBadLocus X L s` is nowhere dense. -/
@[stacks 02P2 "the exceptional subset is nowhere dense"]
theorem denominatorBadLocus_isNowhereDense
    (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    IsNowhereDense (denominatorBadLocus X L s) := by
  obtain ⟨T₁, hT₁closed, hT₁nd, h₁⟩ :=
    denominatorIdeal_inclusion_support X L s hL
  obtain ⟨T₂, hT₂closed, hT₂nd, h₂⟩ :=
    denominatorIdeal_section_support X L s hL hs
  exact IsNowhereDense.mono (Set.union_subset_union h₁ h₂) (hT₁nd.union hT₂nd)

/-- The stalk functor at `x` on sheaves of `𝒪_X`-modules preserves zero morphisms. -/
local instance stalkFunctor_preservesZeroMorphisms (x : X) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).PreservesZeroMorphisms where
  map_zero A B := by
    ext z
    obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq A.val.presheaf z
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (0 : A ⟶ B).val)).hom
        (TopCat.Presheaf.germ A.val.presheaf U x hxU a) = 0
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (0 : A ⟶ B).val) a).trans
        (by
          change (TopCat.Presheaf.germ B.val.presheaf U x hxU).hom 0 = 0
          exact map_zero _)

private theorem stalk_mono {A B : _root_.SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B)
    [Mono f] (x : X) :
    Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) := by
  apply (ModuleCat.mono_iff_injective _).2
  have : Mono f.val := (SheafOfModules.forget X.ringCatSheaf).map_mono f
  have : Mono ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val) :=
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map_mono f.val
  show Function.Injective (ConcreteCategory.hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val)))
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
  intro U
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
    ((NatTrans.mono_iff_mono_app _).1 inferInstance (Opposite.op U))

private theorem eq_zero_of_stalk_eq_zero_at_associated
    [IsLocallyNoetherian X] {A F : _root_.SheafOfModules.{u} X.ringCatSheaf}
    [A.IsQuasicoherent] [F.IsQuasicoherent] (f : A ⟶ F)
    (hf : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f = 0) : f = 0 := by
  let : (cokernel f).IsQuasicoherent := isQuasicoherent_cokernel f
  have : Mono (cokernel.π f) := by
    apply Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
    intro x
    by_cases hx : x ∈ Stacks.Divisors.associatedPoints F
    · left
      let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
      have he : T.map (cokernel.π f) ≫ (PreservesCokernel.iso T f).hom =
          cokernel.π (T.map f) := PreservesCokernel.π_iso_hom T f
      have : IsIso (cokernel.π (T.map f)) := cokernel.π_of_zero (hf x hx)
      have : Mono (T.map (cokernel.π f)) := mono_of_mono_fac he
      exact (ModuleCat.mono_iff_injective _).1 this
    · exact Or.inr hx
  exact (cancel_mono (cokernel.π f)).1 (by simp)

private theorem stalk_tensorRight_map_eq_zero
    {A B : _root_.SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B)
    (G : _root_.SheafOfModules.{u} X.ringCatSheaf) (x : X)
    (hf : (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f = 0) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj G)).map f) = 0 := by
  have nativeMap : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj G).map f =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map ((f, 𝟙 G) : (A, G) ⟶ (B, G)) :=
    (Category.comp_id (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map f).app G)).symm.trans
      (congrArg (fun morphism => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).map f).app G ≫ morphism)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).map_id G).symm)
  refine (congrArg (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
    nativeMap).trans ?_
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace A.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace B.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val x
  have hf' : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val B.val
    f.val x = 0 := by
    ext z
    exact congrArg (fun k => k z) hf
  have hnat := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural X.toRingedSpace x
    A G B G f (𝟙 G)
  rw [hf', TensorProduct.map_zero_left, LinearMap.zero_comp] at hnat
  ext z
  show Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        ((f, (𝟙 G)) : (A, G) ⟶ (B, G)))).val x z =
      0
  apply (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x B
    G).injective
  convert (LinearMap.congr_fun hnat z).symm using 1 <;> first | rfl | exact map_zero _

private theorem stalk_tensorRight_map_mono
    {A B : _root_.SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B)
    (G : _root_.SheafOfModules.{u} X.ringCatSheaf) (x : X)
    [IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f)] :
    Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map ((f, 𝟙 G) : (A, G) ⟶ (B, G)))) := by
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace A.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace B.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace G.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val x
  let e := LinearEquiv.ofBijective
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace A.val B.val f.val x)
    (ConcreteCategory.bijective_of_isIso
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f))
  let idG : G ⟶ G := 𝟙 G
  have hnat := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural X.toRingedSpace x
    A G B G f idG
  have hid : Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace G.val G.val
    idG.val x =
      LinearMap.id := by
    ext z
    exact congrArg (fun k => k z)
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map_id G)
  rw [hid] at hnat
  apply (ModuleCat.mono_iff_injective _).2
  show Function.Injective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G).val
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        ((f, idG) : (A, G) ⟶ (B, G)))).val x)
  intro z w hzw
  apply (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x A
    G).injective
  apply (TensorProduct.congr e (LinearEquiv.refl _ _)).injective
  have hz := LinearMap.congr_fun hnat z
  have hw := LinearMap.congr_fun hnat w
  exact hz.trans ((congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso
    X.toRingedSpace x B G) hzw).trans
    hw.symm)

private theorem stalk_tensorMap_comp_iso_mono
    {A B C : _root_.SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B)
    (G : _root_.SheafOfModules.{u} X.ringCatSheaf)
    (e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj B).obj G) ≅ C) (x : X)
    [IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f)] :
    Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := (A, G)) (Y := (B, G)) (f, 𝟙 G) ≫ e.hom)) :=
  mono_functor_map_comp _ _ _ (stalk_tensorRight_map_mono X f G x)
    (mono_functor_map_of_isIso _ e)

/-- If a morphism is a monomorphism on the stalk at `x`, composing it with any morphism that is
zero on that stalk after precomposing with its kernel inclusion gives zero. -/
private theorem stalk_map_kernel_ι_comp_eq_zero
    {M N P : _root_.SheafOfModules.{u} X.ringCatSheaf} (f : M ⟶ N) (g : M ⟶ P) (x : X)
    [Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f)] :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map (kernel.ι f ≫ g) = 0 := by
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have : T.PreservesZeroMorphisms := stalkFunctor_preservesZeroMorphisms X x
  have hk : T.map (kernel.ι f) = 0 :=
    (cancel_mono (T.map f)).1 ((T.map_comp _ _).symm.trans
      ((congrArg T.map (kernel.condition f)).trans ((T.map_zero _ _).trans zero_comp.symm)))
  exact (T.map_comp _ _).trans ((congrArg (· ≫ T.map _) hk).trans zero_comp)

private theorem eq_zero_of_stalk_eq_zero_at_associated_tensor
    [IsLocallyNoetherian X] {F L : _root_.SheafOfModules.{u} X.ringCatSheaf}
    {A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)}
    [A.IsQuasicoherent] [F.IsQuasicoherent]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (f : A ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj L))
    (hf : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f = 0) : f = 0 := by
  let := hL
  let W : _root_.SheafOfModules.{u} X.ringCatSheaf :=
    (Stacks.SheafOfModules.Invertible.tensorPower X.sheaf.obj X.ringCatSheaf.property L (-1))
  let Q : _root_.SheafOfModules.{u} X.ringCatSheaf ⥤ _root_.SheafOfModules.{u} X.ringCatSheaf :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).flip.obj W)
  have hWinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property W :=
    tensorPower_isInvertible X.sheaf.obj X.ringCatSheaf.property L (-1)
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ W).mpr hWinv
  have : W.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X W
  have : W.IsQuasicoherent :=
      (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X W).out 1 2 rfl
        rfl).mp inferInstance).1
  have hWq : W.IsQuasicoherent := inferInstance
  have hAq : A.IsQuasicoherent := inferInstance
  have : (Q.obj A).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace A W hAq hWq
  have : Q.IsEquivalence :=
    tensorRightFunctor_isEquivalence X.sheaf.obj X.ringCatSheaf.property W
  let eLW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj W) ≅
        SheafOfModules.unit X.ringCatSheaf :=
    tensorProductIso X.sheaf.obj X.ringCatSheaf.property
      (tensorPowerOneIso X.sheaf.obj X.ringCatSheaf.property L).symm (Iso.refl W) ≪≫
      tensorPowerMulIsoNegOne X.sheaf.obj X.ringCatSheaf.property L
  let e : Q.obj ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj L)) ≅ F :=
    tensorProductAssociator X.sheaf.obj X.ringCatSheaf.property F L W ≪≫
      tensorProductIso X.sheaf.obj X.ringCatSheaf.property (Iso.refl F) eLW ≪≫
      tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property F
  have hz : Q.map f ≫ e.hom = 0 := by
    apply eq_zero_of_stalk_eq_zero_at_associated X
    intro x hx
    rw [Functor.map_comp, stalk_tensorRight_map_eq_zero X f W x (hf x hx), zero_comp]
  have hq : Q.map f = 0 := (cancel_mono e.hom).1 (by simpa using hz)
  exact Q.map_injective (hq.trans (Q.map_zero _ _).symm)

/-- The generic point of an irreducible component of a locally Noetherian scheme does not lie in a
closed nowhere dense subset. -/
theorem genericPoint_not_mem_closed_nowhereDense
    [IsLocallyNoetherian X] {Z T : Set X} {x : X}
    (hZ : Z ∈ irreducibleComponents X) (hx : IsGenericPoint x Z)
    (hT : IsClosed T) (hT' : IsNowhereDense T) : x ∉ T := by
  intro hxT
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
  have : IsAffine U.toScheme := hU
  have : IsLocallyNoetherian U.toScheme := inferInstance
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  have hZU : Subtype.val ⁻¹' Z ∈ irreducibleComponents U :=
    preimage_mem_irreducibleComponents hZ U.isOpenEmbedding
      ⟨x, hx.mem, ⟨⟨x, hxU⟩, rfl⟩⟩
  obtain ⟨V, hV, hVne, hVZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hZU
  have hVT : Subtype.val '' V ⊆ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hx.mem_closed_set_iff hT).1 hxT (hVZ hy)
  have hVo : IsOpen (Subtype.val '' V : Set X) := U.isOpenEmbedding.isOpenMap _ hV
  have hVi : Subtype.val '' V ⊆ interior T := interior_maximal hVT hVo
  rw [hT.isNowhereDense_iff.mp hT'] at hVi
  exact (hVne.image Subtype.val).ne_empty (Set.eq_empty_of_subset_empty hVi)

private theorem associated_not_mem_denominatorBadLocus
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (x : X) (hx : x ∈ Stacks.Divisors.associatedPoints F) : x ∉ denominatorBadLocus X L s := by
  have hfull : SheafOfModules.supp F = Set.univ := by
    rw [← SheafOfModules.supp_eq_moduleSheaf_supp]
    exact hSupp
  have hg : ∃ Z ∈ irreducibleComponents (↥(SheafOfModules.supp F)),
      IsGenericPoint x (Subtype.val '' Z) := by
    by_contra h
    exact hF x ((isEmbeddedAssociatedPoint_iff_not_genericPoint X F x).2 ⟨hx, h⟩)
  rw [hfull] at hg
  obtain ⟨Z, hZ, hxZ⟩ := hg
  have hZ' : Subtype.val '' Z ∈ irreducibleComponents X := by
    let e := Homeomorph.Set.univ X
    exact image_mem_irreducibleComponents_of_isPreirreducible_fiber e
      e.continuous e.isOpenMap (fun y => Set.Subsingleton.isPreirreducible
        (fun a ha b hb => e.injective (ha.trans hb.symm))) e.surjective hZ
  exact genericPoint_not_mem_closed_nowhereDense X hZ' hxZ
    (denominatorBadLocus_isClosed X L s hL hs) (denominatorBadLocus_isNowhereDense X L s hL hs)


private theorem stalk_isIso_of_not_mem_cokernel_support
    {A B : _root_.SheafOfModules.{u} X.ringCatSheaf} (f : A ⟶ B) [Mono f] (x : X)
    (hx : x ∉ (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (cokernel f)).supp) :
    IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) := by
  have := stalk_mono X f x
  have : Epi ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) :=
    (ModuleCat.epi_iff_surjective _).2
      (stalk_surjective_of_not_mem_cokernel_support X f x hx)
  exact isIso_of_mono_of_epi _

private theorem kernel_compositions_eq_zero
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
    kernel.ι (actionMod X L F s) ≫ sectionTensorMod X L F s = 0 ∧
      kernel.ι (sectionTensorMod X L F s) ≫ Abelian.factorThruImage (actionMod X L F s) = 0 := by
  let := hL
  have : F.IsQuasicoherent :=
      (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X F).out 1 2 rfl
        rfl).mp inferInstance).1
  let : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).mpr hL
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have : L.IsQuasicoherent :=
      (((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X L).out 1 2 rfl
        rfl).mp inferInstance).1
  have : (denominatorIdeal X L s).IsQuasicoherent :=
    denominatorIdeal_isQuasicoherent X L s hL
  have hIq : (denominatorIdeal X L s).IsQuasicoherent := inferInstance
  have hFq : F.IsQuasicoherent := inferInstance
  have hLq : L.IsQuasicoherent := inferInstance
  have hIFq : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (denominatorIdeal X L s)).obj
        F)).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hIq hFq
  have hFLq : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj L)).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace _ _ hFq hLq
  have : (kernel (actionMod X L F s)).IsQuasicoherent :=
    @isQuasicoherent_kernel X _ _ hIFq hFq (actionMod X L F s)
  have hKq : (kernel (sectionTensorMod X L F s)).IsQuasicoherent :=
    @isQuasicoherent_kernel X _ _ hIFq hFLq (sectionTensorMod X L F s)
  have hmono : ∀ x ∈ Stacks.Divisors.associatedPoints F,
        Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
          (actionMod X L F s)) ∧
        Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map
          (sectionTensorMod X L F s)) := by
    intro x hx
    let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
    have hx' := associated_not_mem_denominatorBadLocus X L F s hL hs hF hSupp x hx
    have := denominatorIdeal_inclusion_mono X L s hL
    have := denominatorIdeal_section_mono X L s hL hs
    have : IsIso (T.map (denominatorIdealι X L s)) :=
      stalk_isIso_of_not_mem_cokernel_support X _ x (fun h => hx' (Or.inl h))
    have : IsIso (T.map (denominatorIdealMul X L s)) :=
      stalk_isIso_of_not_mem_cokernel_support X _ x (fun h => hx' (Or.inr h))
    exact ⟨stalk_tensorMap_comp_iso_mono X (denominatorIdealι X L s) F
        (tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property F) x,
      stalk_tensorMap_comp_iso_mono X (denominatorIdealMul X L s) F
        (tensorProductBraiding X.sheaf.obj X.ringCatSheaf.property L F) x⟩
  constructor
  · apply eq_zero_of_stalk_eq_zero_at_associated_tensor X hL
    intro x hx
    have := (hmono x hx).1
    exact stalk_map_kernel_ι_comp_eq_zero X _ _ x
  · have hz := @eq_zero_of_stalk_eq_zero_at_associated X _ _ _ hKq hFq
      (kernel.ι (sectionTensorMod X L F s) ≫ actionMod X L F s) (by
        intro x hx
        have := (hmono x hx).2
        exact stalk_map_kernel_ι_comp_eq_zero X _ _ x)
    exact (Abelian.imageStrongEpiMonoFactorisation (actionMod X L F s)).m_mono.right_cancellation
      _ _ ((Category.assoc _ _ _).trans
      ((congrArg (kernel.ι (sectionTensorMod X L F s) ≫ ·)
        (Abelian.image.fac (actionMod X L F s))).trans (hz.trans zero_comp.symm)))


/-- The canonical section action, specified by its value on local products. -/
@[stacks 02P2 "the second canonical map"]
noncomputable def denominatorIdealTimesModuleMul
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent]
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
      { f : denominatorIdealTimesModule X L F s ⟶
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj L) //
        Abelian.factorThruImage (denominatorIdealAction X L F s) ≫ f =
          denominatorIdealSectionTensor X L F s } := by
    exact ⟨(Abelian.coimageIsoImage (denominatorIdealAction X L F s)).inv ≫
        cokernel.desc (kernel.ι (denominatorIdealAction X L F s))
          (denominatorIdealSectionTensor X L F s)
        (by exact (kernel_compositions_eq_zero X L F s hL hs hF hSupp).1),
      by exact factorThruImage_imageDesc _ _ _⟩

/-- The inclusion `I F ⟶ F` is a monomorphism, because `I F` is by definition the image of the
action of `I` on `F`. -/
@[stacks 02P2 "injectivity of the first map"]
theorem denominatorIdealTimesModuleι_mono
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    Mono (denominatorIdealTimesModuleι X L F s) :=
  (Abelian.imageStrongEpiMonoFactorisation (denominatorIdealAction X L F s)).m_mono

/-- Under the hypotheses of `denominatorIdealTimesModuleMul`, the second canonical map
`I F ⟶ F ⊗ L` is a monomorphism. -/
@[stacks 02P2 "injectivity of the second map"]
theorem denominatorIdealTimesModuleMul_mono
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent]
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
    Mono (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val :=
  mono_imageDesc _ _
    (kernel_compositions_eq_zero X L F s hL hs hF hSupp).1
    (kernel_compositions_eq_zero X L F s hL hs hF hSupp).2

/-- The cokernel of the inclusion `I F ⟶ F` is supported on `denominatorBadLocus X L s`. -/
@[stacks 02P2 "support of the first cokernel"]
theorem denominatorIdealTimesModuleι_cokernel_support
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        (cokernel (denominatorIdealTimesModuleι X L F s))).supp ⊆
      denominatorBadLocus X L s := by
  intro x hx
  by_contra hnot
  have hι := stalk_surjective_of_not_mem_cokernel_support X (denominatorIdealι X L s) x
    (fun h => hnot (Or.inl h))
  exact not_mem_cokernel_support_of_factor X (Abelian.factorThruImage _)
    (denominatorIdealTimesModuleι X L F s) (denominatorIdealAction X L F s)
    (Abelian.image.fac _) x
    (stalk_surjective_tensorMap_comp_iso X (denominatorIdealι X L s)
      (tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property F) x hι) hx

/-- Under the hypotheses of `denominatorIdealTimesModuleMul`, the cokernel of the second
canonical map `I F ⟶ F ⊗ L` is supported on `denominatorBadLocus X L s`. -/
@[stacks 02P2 "support of the second cokernel"]
theorem denominatorIdealTimesModuleMul_cokernel_supp
    (L F : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent]
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
      (cokernel (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).val)).supp ⊆
      denominatorBadLocus X L s := by
      intro x hx
      by_contra hnot
      have hμ := stalk_surjective_of_not_mem_cokernel_support X (denominatorIdealMul X L s) x
        (fun h => hnot (Or.inr h))
      exact not_mem_cokernel_support_of_factor X (Abelian.factorThruImage _) _ _
        (denominatorIdealTimesModuleMul X L F s hL hs hF hSupp).property x
        (stalk_surjective_tensorMap_comp_iso X (denominatorIdealMul X L s)
          (tensorProductBraiding X.sheaf.obj X.ringCatSheaf.property L F) x hμ) hx


end AlgebraicGeometry

end
