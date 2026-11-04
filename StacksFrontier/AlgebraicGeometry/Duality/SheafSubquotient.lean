module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleOpen

/-!
# Subquotients of a module on a scheme

For submodules `N ≤ M` of an `𝒪_X`-module `L`, the quotient `M / N` is a module on `X`, and an
inclusion of pairs `(N, M) ⊆ (N', M')` induces a map `M / N ⟶ M' / N'`. These subquotients compute
homology: the homology of a three term complex `L₁ ⟶ L₂ ⟶ L₃` is the subquotient of `L₂` cut out by
the sectionwise image of the first map inside the sectionwise kernel of the second. A monomorphism
`j : M ⟶ L` carries the submodule lattice of `M` into that of `L` and identifies the subquotients,
so a subquotient of a submodule of `L` is again a subquotient of `L`.

## Main definitions

* `AlgebraicGeometry.subι` — the inclusion of a submodule, typed at `X.Modules`.
* `AlgebraicGeometry.subq` — the subquotient `M / N`, and `AlgebraicGeometry.subqMap` the map it
  induces from an inclusion of pairs.
* `AlgebraicGeometry.toImageSubmodule` — the corestriction of a morphism to its image submodule,
  and `AlgebraicGeometry.imageSubmoduleIso` a monomorphism as the inclusion of its image.

## Main results

* `AlgebraicGeometry.homologyIsoSubq` — the homology of a short complex is the subquotient of its
  middle term cut out by the image of the first map inside the kernel of the second.
* `AlgebraicGeometry.subqPushIso` — a monomorphism identifies a subquotient of its source with the
  corresponding subquotient of its target.
* `AlgebraicGeometry.imageSubmodule_subι_comp_imageSubmodule` and
  `AlgebraicGeometry.imageSubmodule_subι_comp_kernelSubmodule` — the image along the inclusion of a
  submodule of a sectionwise image and of a sectionwise kernel.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` carrying its own
`Category` instance, so `N.ι` and a morphism of `X.Modules` compose at two different instances and
class synthesis does not transfer between them. `AlgebraicGeometry.subι` is the inclusion typed at
`X.Modules`, and every composite below is formed from it. For the same reason a goal mentioning the
module underlying a submodule is not type-correct at the transparency `rw` and `simp` use, so
identities between composites are proved as explicit chains of `CategoryTheory.Category.assoc` and
`congrArg` steps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Inclusions of submodules -/

/-- The inclusion of a submodule of a module on a scheme, typed at `X.Modules`. -/
def subι {L : X.Modules} (N : L.Submodule) : (N.toSheafOfModules : X.Modules) ⟶ L := N.ι

/-- A morphism into a submodule is determined by its composite with the inclusion. -/
lemma cancel_subι {L : X.Modules} (N : L.Submodule) {A : X.Modules}
    (f g : A ⟶ (N.toSheafOfModules : X.Modules)) (h : f ≫ subι N = g ≫ subι N) : f = g :=
  AlgebraicGeometry.cancel_sheafSubmodule_ι N f g h

/-- The inclusion of a submodule is a monomorphism. -/
instance mono_subι {L : X.Modules} (N : L.Submodule) : Mono (subι N) :=
  ⟨fun _ _ h => cancel_subι N _ _ h⟩

/-- The inclusion between two comparable submodules, typed at `X.Modules`. -/
def subHom {L : X.Modules} {N₁ N₂ : L.Submodule} (h : N₁ ≤ N₂) :
    (N₁.toSheafOfModules : X.Modules) ⟶ (N₂.toSheafOfModules : X.Modules) :=
  SheafOfModules.Submodule.homOfLE h

/-- The inclusion between comparable submodules composes to the inclusion into the ambient
module. -/
lemma homOfLE_comp_subι {L : X.Modules} {N₁ N₂ : L.Submodule} (h : N₁ ≤ N₂) :
    subHom h ≫ subι N₂ = subι N₁ :=
  SheafOfModules.Submodule.homOfLE_ι h

/-- The inclusions between comparable submodules compose. -/
lemma subHom_comp {L : X.Modules} {N₁ N₂ N₃ : L.Submodule} (h₁ : N₁ ≤ N₂)
    (h₂ : N₂ ≤ N₃) :
    subHom h₁ ≫ subHom h₂ = subHom (h₁.trans h₂) :=
  cancel_subι N₃ _ _
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => subHom h₁ ≫ t) (homOfLE_comp_subι h₂)).trans
        ((homOfLE_comp_subι h₁).trans (homOfLE_comp_subι (h₁.trans h₂)).symm)))

/-- An isomorphism of modules on a scheme is an epimorphism. -/
lemma epi_of_isIso_modules {M N : X.Modules} (f : M ⟶ N) (hf : IsIso f) : Epi f :=
  have := hf
  ⟨fun a b hab =>
    (Category.id_comp a).symm.trans
      ((congrArg (fun t => t ≫ a) (IsIso.inv_hom_id f).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => inv f ≫ t) hab).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun t => t ≫ b) (IsIso.inv_hom_id f)).trans
                (Category.id_comp b))))))⟩

/-- The inclusion of a submodule into itself is the identity. -/
lemma subHom_rfl {L : X.Modules} (N : L.Submodule) :
    subHom (le_refl N) = 𝟙 (N.toSheafOfModules : X.Modules) :=
  cancel_subι N _ _ ((homOfLE_comp_subι (le_refl N)).trans (Category.id_comp (subι N)).symm)

/-- The inclusion of a submodule is injective on sections. -/
lemma injective_subι_app {L : X.Modules} (N : L.Submodule)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) : Function.Injective (((subι N).val.app U).hom) :=
  fun _ _ hab => Subtype.ext hab

/-- A composite of morphisms injective on sections is injective on sections. -/
lemma injective_app_comp {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P)
    {U : (TopologicalSpace.Opens X)ᵒᵖ} (ha : Function.Injective ((a.val.app U).hom))
    (hb : Function.Injective ((b.val.app U).hom)) :
    Function.Injective (((a ≫ b).val.app U).hom) :=
  fun _ _ hxy => ha (hb hxy)

/-! ### Sectionwise kernels and images -/

/-- Enlarging a morphism by a further composite enlarges its sectionwise kernel. -/
lemma kernelSubmodule_le_comp {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) :
    Stacks.Algebraization.kernelSubmodule a ≤ Stacks.Algebraization.kernelSubmodule (a ≫ b) := by
  refine SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U s hs => ?_)
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker] at hs
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker]
  have h : ((a ≫ b).val.app U).hom s = (b.val.app U).hom ((a.val.app U).hom s) := rfl
  rw [h, hs, map_zero]

/-- A morphism which is injective on sections may be cancelled from a sectionwise kernel. -/
lemma kernelSubmodule_comp_eq {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (hb : ∀ U : (TopologicalSpace.Opens X)ᵒᵖ, Function.Injective ((b.val.app U).hom)) :
    Stacks.Algebraization.kernelSubmodule (a ≫ b) = Stacks.Algebraization.kernelSubmodule a := by
  refine le_antisymm ?_ (kernelSubmodule_le_comp a b)
  refine SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U s hs => ?_)
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker] at hs
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker]
  refine hb U ?_
  rw [map_zero]
  exact hs

/-- A morphism whose composite with `g` vanishes has its sectionwise image inside the sectionwise
kernel of `g`. -/
lemma imageSubmodule_le_kernelSubmodule {M N P : X.Modules} (p : M ⟶ N) (g : N ⟶ P)
    (hpg : p ≫ g = 0) :
    imageSubmodule p ≤ Stacks.Algebraization.kernelSubmodule g := by
  have h := kernelSubmodule_le_comp (cokernel.π (C := X.Modules) p)
    (cokernel.desc (C := X.Modules) p g hpg)
  rwa [cokernel.π_desc] at h

/-- The sectionwise image of a composite is contained in that of its second factor. -/
lemma imageSubmodule_comp_le {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) :
    imageSubmodule (a ≫ b) ≤ imageSubmodule b :=
  imageSubmodule_le_kernelSubmodule _ _
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => a ≫ t) (cokernel.condition (C := X.Modules) b)).trans comp_zero))

/-- Precomposition with an epimorphism does not change the sectionwise image. -/
lemma imageSubmodule_epi_comp {M N P : X.Modules} (e : M ⟶ N) [Epi e] (b : N ⟶ P) :
    imageSubmodule (e ≫ b) = imageSubmodule b :=
  le_antisymm (imageSubmodule_comp_le e b)
    (imageSubmodule_le_kernelSubmodule b (cokernel.π (C := X.Modules) (e ≫ b))
      ((cancel_epi e).1 ((Category.assoc _ _ _).symm.trans
        ((cokernel.condition (C := X.Modules) (e ≫ b)).trans comp_zero.symm))))

/-- The corestriction of the categorical kernel into the sectionwise kernel is an epimorphism. -/
instance epi_kernelSubmoduleCorestrict {M N : X.Modules} (f : M ⟶ N) :
    Epi (Stacks.Algebraization.kernelSubmoduleCorestrict f) :=
  epi_of_isIso_modules _ (Stacks.Algebraization.kernelSubmoduleIso f).isIso_inv

/-- The corestriction of the categorical kernel into the sectionwise kernel, composed with the
inclusion, is the kernel inclusion. -/
lemma kernelSubmoduleCorestrict_comp_subι {M N : X.Modules} (f : M ⟶ N) :
    Stacks.Algebraization.kernelSubmoduleCorestrict f ≫
      subι (Stacks.Algebraization.kernelSubmodule f) = kernel.ι (C := X.Modules) f :=
  Stacks.Algebraization.kernelSubmoduleCorestrict_comp_ι f

/-- The corestriction of a morphism to its sectionwise image. -/
def toImageSubmodule {M N : X.Modules} (p : M ⟶ N) :
    M ⟶ ((imageSubmodule p).toSheafOfModules : X.Modules) :=
  Abelian.factorThruImage p ≫
    Stacks.Algebraization.kernelSubmoduleCorestrict (cokernel.π (C := X.Modules) p)

/-- The corestriction to the image, followed by the inclusion of the image, is the morphism. -/
lemma toImageSubmodule_comp_subι {M N : X.Modules} (p : M ⟶ N) :
    toImageSubmodule p ≫ subι (imageSubmodule p) = p :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => Abelian.factorThruImage p ≫ t)
        (kernelSubmoduleCorestrict_comp_subι (cokernel.π (C := X.Modules) p))).trans
      (Abelian.image.fac p))

/-- The corestriction of a morphism to its sectionwise image is an epimorphism. -/
instance epi_toImageSubmodule {M N : X.Modules} (p : M ⟶ N) : Epi (toImageSubmodule p) :=
  epi_comp (Abelian.factorThruImage p)
    (Stacks.Algebraization.kernelSubmoduleCorestrict (cokernel.π (C := X.Modules) p))

/-- A monomorphism is isomorphic to the inclusion of its sectionwise image. -/
def imageSubmoduleIso {M N : X.Modules} (p : M ⟶ N) (hp : Mono p) :
    M ≅ ((imageSubmodule p).toSheafOfModules : X.Modules) :=
  haveI : Mono (toImageSubmodule p) :=
    haveI := hp
    mono_of_mono_fac (toImageSubmodule_comp_subι p)
  haveI : IsIso (toImageSubmodule p) := isIso_of_mono_of_epi _
  asIso (toImageSubmodule p)

/-- The isomorphism of a monomorphism with its sectionwise image, followed by the inclusion of
the image, is the monomorphism. -/
lemma imageSubmoduleIso_hom_comp_subι {M N : X.Modules} (p : M ⟶ N) (hp : Mono p) :
    (imageSubmoduleIso p hp).hom ≫ subι (imageSubmodule p) = p :=
  toImageSubmodule_comp_subι p

/-! ### The image of a submodule along a morphism -/

/-- Taking the image along a morphism is monotone in the submodule. -/
lemma imageSubmodule_subι_comp_mono {M L : X.Modules} (j : M ⟶ L) {K K' : M.Submodule}
    (h : K ≤ K') : imageSubmodule (subι K ≫ j) ≤ imageSubmodule (subι K' ≫ j) :=
  have hfac : subι K ≫ j = subHom h ≫ (subι K' ≫ j) :=
    (congrArg (fun t => t ≫ j) (homOfLE_comp_subι h)).symm.trans (Category.assoc _ _ _)
  le_of_eq (congrArg (fun t : (K.toSheafOfModules : X.Modules) ⟶ L => imageSubmodule t) hfac)
    |>.trans (imageSubmodule_comp_le (subHom h) (subι K' ≫ j))

/-- The inclusion of a submodule composed with a monomorphism is a monomorphism. -/
lemma mono_subι_comp {M L : X.Modules} (j : M ⟶ L) (hj : Mono j) (K : M.Submodule) :
    Mono (subι K ≫ j) :=
  ⟨fun a b hab => cancel_subι K a b
    (hj.right_cancellation _ _
      ((Category.assoc a (subι K) j).trans (hab.trans (Category.assoc b (subι K) j).symm)))⟩

/-- The sections of the image of a submodule along a monomorphism are the image of its sections. -/
lemma imageSubmodule_subι_comp_obj {M L : X.Modules} (j : M ⟶ L) (hj : Mono j) (K : M.Submodule)
    (U : X.Opens) :
    (imageSubmodule (subι K ≫ j)).toSubmodule.obj (op U) =
      LinearMap.range (((subι K ≫ j).val.app (op U)).hom) :=
  imageSubmodule_obj (subι K ≫ j) (mono_subι_comp j hj K) U

/-! ### Subquotients -/

variable {L : X.Modules}

/-- The subquotient `M / N` of `L` determined by submodules `N ≤ M` of `L`. -/
def subq (N M : L.Submodule) (h : N ≤ M) : X.Modules :=
  cokernel (C := X.Modules) (subHom h)

/-- The projection of `M` onto the subquotient `M / N`. -/
def subqπ (N M : L.Submodule) (h : N ≤ M) : (M.toSheafOfModules : X.Modules) ⟶ subq N M h :=
  cokernel.π (C := X.Modules) (subHom h)

/-- The projection of `M` onto the subquotient `M / N` is an epimorphism. -/
instance epi_subqπ (N M : L.Submodule) (h : N ≤ M) : Epi (subqπ N M h) :=
  coequalizer.π_epi

/-- The map `M / N ⟶ M' / N'` induced by an inclusion of pairs of submodules. -/
def subqMap {N M N' M' : L.Submodule} (h : N ≤ M) (h' : N' ≤ M') (hM : M ≤ M') (hN : N ≤ N') :
    subq N M h ⟶ subq N' M' h' :=
  cokernel.desc (C := X.Modules) (subHom h) (subHom hM ≫ subqπ N' M' h')
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t : (N.toSheafOfModules : X.Modules) ⟶ (M'.toSheafOfModules : X.Modules) =>
            t ≫ subqπ N' M' h')
          ((subHom_comp h hM).trans (subHom_comp hN h').symm)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => subHom hN ≫ t)
              (cokernel.condition (C := X.Modules) (subHom h'))).trans comp_zero))))

/-- The induced map on subquotients is compatible with the projections and the inclusion
`M ⟶ M'`. -/
lemma subqπ_comp_subqMap {N M N' M' : L.Submodule} (h : N ≤ M) (h' : N' ≤ M') (hM : M ≤ M')
    (hN : N ≤ N') :
    subqπ N M h ≫ subqMap h h' hM hN = subHom hM ≫ subqπ N' M' h' :=
  cokernel.π_desc (C := X.Modules) _ _ _

/-- The map of subquotients induced by the identity inclusion is the identity. -/
lemma subqMap_id {N M : L.Submodule} (h : N ≤ M) :
    subqMap h h (le_refl M) (le_refl N) = 𝟙 (subq N M h) :=
  (cancel_epi (subqπ N M h)).1
    ((subqπ_comp_subqMap h h (le_refl M) (le_refl N)).trans
      (((congrArg (fun t => t ≫ subqπ N M h) (subHom_rfl M)).trans
        (Category.id_comp _)).trans (Category.comp_id _).symm))

/-- The maps of subquotients induced by composable inclusions of pairs compose. -/
lemma subqMap_comp {N M N' M' N'' M'' : L.Submodule} (h : N ≤ M) (h' : N' ≤ M') (h'' : N'' ≤ M'')
    (hM : M ≤ M') (hN : N ≤ N') (hM' : M' ≤ M'') (hN' : N' ≤ N'') :
    subqMap h h' hM hN ≫ subqMap h' h'' hM' hN' =
      subqMap h h'' (hM.trans hM') (hN.trans hN') :=
  (cancel_epi (subqπ N M h)).1
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ subqMap h' h'' hM' hN')
          (subqπ_comp_subqMap h h' hM hN)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => subHom hM ≫ t)
              (subqπ_comp_subqMap h' h'' hM' hN')).trans
            ((Category.assoc _ _ _).symm.trans
              (subqπ_comp_subqMap h h'' (hM.trans hM') (hN.trans hN')).symm)))))

/-! ### Homology as a subquotient -/

/-- The canonical map from `S.X₁` to the sectionwise kernel of `S.g`, followed by the inclusion,
is `S.f`. -/
lemma kernelLift_corestrict_comp_subι (S : ShortComplex X.Modules) :
    (kernel.lift (C := X.Modules) S.g S.f S.zero ≫
      Stacks.Algebraization.kernelSubmoduleCorestrict S.g) ≫
      subι (Stacks.Algebraization.kernelSubmodule S.g) = S.f :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t => kernel.lift (C := X.Modules) S.g S.f S.zero ≫ t)
        (kernelSubmoduleCorestrict_comp_subι S.g)).trans
      (kernel.lift_ι (C := X.Modules) S.g S.f S.zero))

/-- That canonical map factors through the sectionwise image of `S.f`. -/
lemma kernelLift_corestrict_fac (S : ShortComplex X.Modules) :
    kernel.lift (C := X.Modules) S.g S.f S.zero ≫
      Stacks.Algebraization.kernelSubmoduleCorestrict S.g =
      toImageSubmodule S.f ≫ subHom (imageSubmodule_le_kernelSubmodule S.f S.g S.zero) :=
  cancel_subι _ _ _
    ((kernelLift_corestrict_comp_subι S).trans
      ((toImageSubmodule_comp_subι S.f).symm.trans
        ((congrArg (fun t => toImageSubmodule S.f ≫ t)
            (homOfLE_comp_subι (imageSubmodule_le_kernelSubmodule S.f S.g S.zero))).symm.trans
          (Category.assoc _ _ _).symm)))

/-- The cycles of a short complex of modules on a scheme, identified with the sectionwise kernel
of its second map. -/
def cycIso (S : ShortComplex X.Modules) :
    S.cycles ≅ ((Stacks.Algebraization.kernelSubmodule S.g).toSheafOfModules : X.Modules) :=
  (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S).cyclesIso ≪≫
    (Stacks.Algebraization.kernelSubmoduleIso S.g).symm

/-- The identification of the cycles with the sectionwise kernel, followed by the inclusion, is
the inclusion of the cycles. -/
lemma cycIso_hom_comp_subι (S : ShortComplex X.Modules) :
    (cycIso S).hom ≫ subι (Stacks.Algebraization.kernelSubmodule S.g) = S.iCycles :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun t =>
          (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S).cyclesIso.hom ≫ t)
        (kernelSubmoduleCorestrict_comp_subι S.g)).trans
      (ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i
        (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S)))

/-- The homology of a short complex is the cokernel of the canonical map into the kernel. -/
def homologyIsoCokLift (S : ShortComplex X.Modules) :
    S.homology ≅ cokernel (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero) :=
  (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S).homologyIso

/-- Replacing the categorical kernel of `S.g` by the sectionwise one. -/
def cokLiftIso₁ (S : ShortComplex X.Modules) :
    cokernel (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero) ≅
      cokernel (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero ≫
        Stacks.Algebraization.kernelSubmoduleCorestrict S.g) :=
  cokernel.mapIso (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero)
    (kernel.lift (C := X.Modules) S.g S.f S.zero ≫
      Stacks.Algebraization.kernelSubmoduleCorestrict S.g)
    (Iso.refl S.X₁) (Stacks.Algebraization.kernelSubmoduleIso S.g).symm
    (Category.id_comp _).symm

/-- Factoring that map through the sectionwise image of `S.f`. -/
def cokLiftIso₂ (S : ShortComplex X.Modules) :
    cokernel (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero ≫
        Stacks.Algebraization.kernelSubmoduleCorestrict S.g) ≅
      cokernel (C := X.Modules) (toImageSubmodule S.f ≫
        subHom (imageSubmodule_le_kernelSubmodule S.f S.g S.zero)) :=
  cokernelIsoOfEq (C := X.Modules) (kernelLift_corestrict_fac S)

/-- Cancelling the epimorphism onto the sectionwise image. -/
def cokLiftIso₃ (S : ShortComplex X.Modules) :
    cokernel (C := X.Modules) (toImageSubmodule S.f ≫
        subHom (imageSubmodule_le_kernelSubmodule S.f S.g S.zero)) ≅
      subq (imageSubmodule S.f) (Stacks.Algebraization.kernelSubmodule S.g)
        (imageSubmodule_le_kernelSubmodule S.f S.g S.zero) :=
  cokernelEpiComp (C := X.Modules) (toImageSubmodule S.f)
    (subHom (imageSubmodule_le_kernelSubmodule S.f S.g S.zero))

/-- The homology of a short complex of modules on a scheme is the subquotient of its middle term
cut out by the sectionwise image of the first map inside the sectionwise kernel of the second. -/
def homologyIsoSubq (S : ShortComplex X.Modules) :
    S.homology ≅ subq (imageSubmodule S.f) (Stacks.Algebraization.kernelSubmodule S.g)
      (imageSubmodule_le_kernelSubmodule S.f S.g S.zero) :=
  homologyIsoCokLift S ≪≫ cokLiftIso₁ S ≪≫ cokLiftIso₂ S ≪≫ cokLiftIso₃ S

/-- The cokernel projection of the corestricted canonical map, followed by `cokLiftIso₂` and
`cokLiftIso₃`, is the projection onto the subquotient. -/
lemma π_comp_cokLiftIso₂₃ (S : ShortComplex X.Modules) :
    cokernel.π (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero ≫
        Stacks.Algebraization.kernelSubmoduleCorestrict S.g) ≫
      ((cokLiftIso₂ S).hom ≫ (cokLiftIso₃ S).hom) =
      subqπ (imageSubmodule S.f) (Stacks.Algebraization.kernelSubmodule S.g)
        (imageSubmodule_le_kernelSubmodule S.f S.g S.zero) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (cokLiftIso₃ S).hom)
        (π_comp_cokernelIsoOfEq_hom (C := X.Modules) (kernelLift_corestrict_fac S))).trans
      (cokernel.π_desc (C := X.Modules) _ _ _))

/-- The cokernel projection of the canonical map into the kernel, followed by `cokLiftIso₁`,
`cokLiftIso₂` and `cokLiftIso₃`, is the corestriction to the sectionwise kernel followed by the
projection onto the subquotient. -/
lemma π_comp_cokLiftIso₁₂₃ (S : ShortComplex X.Modules) :
    cokernel.π (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero) ≫
      ((cokLiftIso₁ S).hom ≫ ((cokLiftIso₂ S).hom ≫ (cokLiftIso₃ S).hom)) =
      Stacks.Algebraization.kernelSubmoduleCorestrict S.g ≫
        subqπ (imageSubmodule S.f) (Stacks.Algebraization.kernelSubmodule S.g)
          (imageSubmodule_le_kernelSubmodule S.f S.g S.zero) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ ((cokLiftIso₂ S).hom ≫ (cokLiftIso₃ S).hom))
        (cokernel.π_desc (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero)
          (Stacks.Algebraization.kernelSubmoduleCorestrict S.g ≫
            cokernel.π (C := X.Modules) (kernel.lift (C := X.Modules) S.g S.f S.zero ≫
              Stacks.Algebraization.kernelSubmoduleCorestrict S.g)) _)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => Stacks.Algebraization.kernelSubmoduleCorestrict S.g ≫ t)
          (π_comp_cokLiftIso₂₃ S))))

/-- The projection onto homology, read in the subquotient model, is the projection of the
sectionwise kernel onto its quotient by the sectionwise image. -/
lemma homologyπ_comp_homologyIsoSubq_hom (S : ShortComplex X.Modules) :
    S.homologyπ ≫ (homologyIsoSubq S).hom =
      (cycIso S).hom ≫ subqπ (imageSubmodule S.f)
        (Stacks.Algebraization.kernelSubmodule S.g)
        (imageSubmodule_le_kernelSubmodule S.f S.g S.zero) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t =>
          t ≫ ((cokLiftIso₁ S).hom ≫ ((cokLiftIso₂ S).hom ≫ (cokLiftIso₃ S).hom)))
        (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom S
          (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t =>
              (ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S).cyclesIso.hom ≫ t)
            (π_comp_cokLiftIso₁₂₃ S)).trans
          (Category.assoc _ _ _).symm)))

/-! ### Subquotients along a monomorphism -/

/-- A monomorphism `j : M ⟶ L` identifies the subquotient `M' / N` of `M` with the corresponding
subquotient of `L`. -/
def subqPushIso {M : X.Modules} (j : M ⟶ L) (hj : Mono j) (N M' : M.Submodule) (h : N ≤ M') :
    subq N M' h ≅ subq (imageSubmodule (subι N ≫ j)) (imageSubmodule (subι M' ≫ j))
      (imageSubmodule_subι_comp_mono j h) :=
  cokernel.mapIso (C := X.Modules) (subHom h)
    (subHom (imageSubmodule_subι_comp_mono j h))
    (imageSubmoduleIso (subι N ≫ j) (mono_subι_comp j hj N))
    (imageSubmoduleIso (subι M' ≫ j) (mono_subι_comp j hj M'))
    (cancel_subι (imageSubmodule (subι M' ≫ j)) _ _
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => subHom h ≫ t)
            (imageSubmoduleIso_hom_comp_subι (subι M' ≫ j) (mono_subι_comp j hj M'))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ j) (homOfLE_comp_subι h)).trans
              (((imageSubmoduleIso_hom_comp_subι (subι N ≫ j)
                    (mono_subι_comp j hj N)).symm.trans
                (congrArg (fun t =>
                    (imageSubmoduleIso (subι N ≫ j) (mono_subι_comp j hj N)).hom ≫ t)
                  (homOfLE_comp_subι (imageSubmodule_subι_comp_mono j h)).symm)).trans
                (Category.assoc _ _ _).symm))))))

/-! ### Images along the inclusion of a submodule -/

/-- The image along a morphism of the sectionwise image of a morphism is the sectionwise image of
the composite. -/
lemma imageSubmodule_subι_comp_imageSubmodule {A M : X.Modules} (q : A ⟶ M) (j : M ⟶ L) :
    imageSubmodule (subι (imageSubmodule q) ≫ j) = imageSubmodule (q ≫ j) :=
  have h : q ≫ j = toImageSubmodule q ≫ (subι (imageSubmodule q) ≫ j) :=
    (congrArg (fun t => t ≫ j) (toImageSubmodule_comp_subι q)).symm.trans (Category.assoc _ _ _)
  (imageSubmodule_epi_comp (toImageSubmodule q) (subι (imageSubmodule q) ≫ j)).symm.trans
    (congrArg (fun t : A ⟶ L => imageSubmodule t) h).symm

/-- The image along the inclusion of a submodule `Q` of the sectionwise kernel of the restriction
of `k` to `Q` is the intersection of `Q` with the sectionwise kernel of `k`. -/
lemma imageSubmodule_subι_comp_kernelSubmodule_subι {C₂ : X.Modules} (Q : L.Submodule)
    (k : L ⟶ C₂) :
    imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule (subι Q ≫ k)) ≫ subι Q) =
      Q ⊓ Stacks.Algebraization.kernelSubmodule k := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W => ?_)
  obtain ⟨W, rfl⟩ : ∃ W₀ : X.Opens, op W₀ = W := ⟨W.unop, rfl⟩
  rw [imageSubmodule_subι_comp_obj (subι Q) (mono_subι Q)]
  refine le_antisymm (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨t, rfl⟩ := hs
    have ht := (mem_kernelSubmodule_iff (subι Q ≫ k) W t.1).1 t.2
    exact ⟨t.1.2, (mem_kernelSubmodule_iff k W _).2 ht⟩
  · obtain ⟨hsQ, hsk⟩ := hs
    refine ⟨⟨⟨s, hsQ⟩, (mem_kernelSubmodule_iff (subι Q ≫ k) W _).2 ?_⟩, rfl⟩
    exact (mem_kernelSubmodule_iff k W s).1 hsk

/-- The image along the inclusion of a submodule `Q` of the sectionwise kernel of a morphism `g`
out of `Q` which lifts `k` along a morphism injective on sections is `Q ⊓ ker k`. -/
lemma imageSubmodule_subι_comp_kernelSubmodule {C₁ C₂ : X.Modules} {Q : L.Submodule}
    (g : (Q.toSheafOfModules : X.Modules) ⟶ C₁) (k : L ⟶ C₂) (jm : C₁ ⟶ C₂)
    (hjm : ∀ U : (TopologicalSpace.Opens X)ᵒᵖ, Function.Injective ((jm.val.app U).hom))
    (hsq : subι Q ≫ k = g ≫ jm) :
    imageSubmodule (subι (Stacks.Algebraization.kernelSubmodule g) ≫ subι Q) =
      Q ⊓ Stacks.Algebraization.kernelSubmodule k :=
  have h1 : Stacks.Algebraization.kernelSubmodule (subι Q ≫ k) =
      Stacks.Algebraization.kernelSubmodule g :=
    (congrArg (fun t : (Q.toSheafOfModules : X.Modules) ⟶ C₂ =>
        Stacks.Algebraization.kernelSubmodule t) hsq).trans
      (kernelSubmodule_comp_eq g jm hjm)
  (congrArg (fun K : (Q.toSheafOfModules : X.Modules).Submodule =>
      imageSubmodule (subι K ≫ subι Q)) h1).symm.trans
    (imageSubmodule_subι_comp_kernelSubmodule_subι Q k)


/-! ### Subquotients along a morphism, and the functoriality of homology -/

/-- The inclusion of a submodule, read through the induced morphism between submodules. -/
lemma sheafSubmoduleMap_comp_subι {L₁ L₂ : X.Modules} (f : L₁ ⟶ L₂) (P : L₁.Submodule)
    (Q : L₂.Submodule) (h : P ≤ AlgebraicGeometry.sheafSubmoduleComap f Q) :
    AlgebraicGeometry.sheafSubmoduleMap f P Q h ≫ subι Q = subι P ≫ f :=
  AlgebraicGeometry.sheafSubmoduleMap_comp_ι f P Q h

/-- The morphisms induced on submodules by `f` are compatible with the inclusions. -/
lemma subHom_comp_sheafSubmoduleMap {L₁ L₂ : X.Modules} (f : L₁ ⟶ L₂) {N₁ M₁ : L₁.Submodule}
    {N₂ M₂ : L₂.Submodule} (h₁ : N₁ ≤ M₁) (h₂ : N₂ ≤ M₂)
    (hM : M₁ ≤ AlgebraicGeometry.sheafSubmoduleComap f M₂)
    (hN : N₁ ≤ AlgebraicGeometry.sheafSubmoduleComap f N₂) :
    subHom h₁ ≫ AlgebraicGeometry.sheafSubmoduleMap f M₁ M₂ hM =
      AlgebraicGeometry.sheafSubmoduleMap f N₁ N₂ hN ≫ subHom h₂ :=
  cancel_subι M₂ _ _
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => subHom h₁ ≫ t) (sheafSubmoduleMap_comp_subι f M₁ M₂ hM)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ f) (homOfLE_comp_subι h₁)).trans
            (((sheafSubmoduleMap_comp_subι f N₁ N₂ hN).symm.trans
                (congrArg (fun t => AlgebraicGeometry.sheafSubmoduleMap f N₁ N₂ hN ≫ t)
                  (homOfLE_comp_subι h₂).symm)).trans
              (Category.assoc _ _ _).symm)))))

/-- The map `M₁ / N₁ ⟶ M₂ / N₂` induced by a morphism `f : L₁ ⟶ L₂` carrying `M₁` into `M₂` and
`N₁` into `N₂`. -/
def subqMapAlong {L₁ L₂ : X.Modules} (f : L₁ ⟶ L₂) {N₁ M₁ : L₁.Submodule} {N₂ M₂ : L₂.Submodule}
    (h₁ : N₁ ≤ M₁) (h₂ : N₂ ≤ M₂) (hM : M₁ ≤ AlgebraicGeometry.sheafSubmoduleComap f M₂)
    (hN : N₁ ≤ AlgebraicGeometry.sheafSubmoduleComap f N₂) :
    subq N₁ M₁ h₁ ⟶ subq N₂ M₂ h₂ :=
  cokernel.desc (C := X.Modules) (subHom h₁)
    (AlgebraicGeometry.sheafSubmoduleMap f M₁ M₂ hM ≫ subqπ N₂ M₂ h₂)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t : (N₁.toSheafOfModules : X.Modules) ⟶ (M₂.toSheafOfModules : X.Modules) =>
            t ≫ subqπ N₂ M₂ h₂)
          (subHom_comp_sheafSubmoduleMap f h₁ h₂ hM hN)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => AlgebraicGeometry.sheafSubmoduleMap f N₁ N₂ hN ≫ t)
              (cokernel.condition (C := X.Modules) (subHom h₂))).trans comp_zero))))

/-- The map of subquotients induced by `f` is compatible with the projections and the
restriction of `f` to `M₁ ⟶ M₂`. -/
lemma subqπ_comp_subqMapAlong {L₁ L₂ : X.Modules} (f : L₁ ⟶ L₂) {N₁ M₁ : L₁.Submodule}
    {N₂ M₂ : L₂.Submodule} (h₁ : N₁ ≤ M₁) (h₂ : N₂ ≤ M₂)
    (hM : M₁ ≤ AlgebraicGeometry.sheafSubmoduleComap f M₂)
    (hN : N₁ ≤ AlgebraicGeometry.sheafSubmoduleComap f N₂) :
    subqπ N₁ M₁ h₁ ≫ subqMapAlong f h₁ h₂ hM hN =
      AlgebraicGeometry.sheafSubmoduleMap f M₁ M₂ hM ≫ subqπ N₂ M₂ h₂ :=
  cokernel.π_desc (C := X.Modules) _ _ _

/-- A commuting square carries the sectionwise kernel into the sectionwise kernel. -/
lemma kernelSubmodule_le_comap {L₁ L₂ C₁ C₂ : X.Modules} (g₁ : L₁ ⟶ C₁) (g₂ : L₂ ⟶ C₂)
    (t : L₁ ⟶ L₂) (t' : C₁ ⟶ C₂) (hsq : t ≫ g₂ = g₁ ≫ t') :
    Stacks.Algebraization.kernelSubmodule g₁ ≤
      AlgebraicGeometry.sheafSubmoduleComap t (Stacks.Algebraization.kernelSubmodule g₂) := by
  refine SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U s hs => ?_)
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker] at hs
  show ((t.val.app U).hom s) ∈ (Stacks.Algebraization.kernelSubmodule g₂).toSubmodule.obj U
  rw [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker]
  have h1 : ((t ≫ g₂).val.app U).hom s = (g₂.val.app U).hom ((t.val.app U).hom s) := rfl
  have h2 : ((g₁ ≫ t').val.app U).hom s = (t'.val.app U).hom ((g₁.val.app U).hom s) := rfl
  have h3 := congrArg (fun k : L₁ ⟶ C₂ => (k.val.app U).hom s) hsq
  rw [h1, h2, hs, map_zero] at h3
  exact h3

/-- A commuting square carries the sectionwise image into the sectionwise image. -/
lemma imageSubmodule_le_comap {A₁ A₂ L₁ L₂ : X.Modules} (a₁ : A₁ ⟶ L₁) (a₂ : A₂ ⟶ L₂)
    (t₁ : A₁ ⟶ A₂) (t : L₁ ⟶ L₂) (hsq : a₁ ≫ t = t₁ ≫ a₂) :
    imageSubmodule a₁ ≤ AlgebraicGeometry.sheafSubmoduleComap t (imageSubmodule a₂) := by
  have hz : a₁ ≫ (t ≫ cokernel.π (C := X.Modules) a₂) = 0 :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k : A₁ ⟶ L₂ => k ≫ cokernel.π (C := X.Modules) a₂) hsq).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => t₁ ≫ k) (cokernel.condition (C := X.Modules) a₂)).trans
            comp_zero)))
  have hd := cokernel.π_desc (C := X.Modules) a₁ (t ≫ cokernel.π (C := X.Modules) a₂) hz
  refine SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U s hs => ?_)
  rw [imageSubmodule, Stacks.Algebraization.kernelSubmodule_toSubmodule_obj,
    LinearMap.mem_ker] at hs
  show ((t.val.app U).hom s) ∈ (imageSubmodule a₂).toSubmodule.obj U
  rw [imageSubmodule, Stacks.Algebraization.kernelSubmodule_toSubmodule_obj, LinearMap.mem_ker]
  have h1 : ((t ≫ cokernel.π (C := X.Modules) a₂).val.app U).hom s =
      ((cokernel.π (C := X.Modules) a₂).val.app U).hom ((t.val.app U).hom s) := rfl
  have h2 : ((cokernel.π (C := X.Modules) a₁ ≫
        cokernel.desc (C := X.Modules) a₁ (t ≫ cokernel.π (C := X.Modules) a₂) hz).val.app
          U).hom s =
      ((cokernel.desc (C := X.Modules) a₁ (t ≫ cokernel.π (C := X.Modules) a₂)
        hz).val.app U).hom (((cokernel.π (C := X.Modules) a₁).val.app U).hom s) := rfl
  have h3 := congrArg (fun k : L₁ ⟶ cokernel (C := X.Modules) a₂ => (k.val.app U).hom s) hd
  rw [h2, hs, map_zero, h1] at h3
  exact h3.symm

/-- The cycles of a morphism of short complexes, read in the sectionwise kernels. -/
lemma cyclesMap_comp_cycIso {S₁ S₂ : ShortComplex X.Modules} (φ : S₁ ⟶ S₂)
    (hk : Stacks.Algebraization.kernelSubmodule S₁.g ≤
      AlgebraicGeometry.sheafSubmoduleComap φ.τ₂ (Stacks.Algebraization.kernelSubmodule S₂.g)) :
    ShortComplex.cyclesMap φ ≫ (cycIso S₂).hom =
      (cycIso S₁).hom ≫ AlgebraicGeometry.sheafSubmoduleMap φ.τ₂
        (Stacks.Algebraization.kernelSubmodule S₁.g)
        (Stacks.Algebraization.kernelSubmodule S₂.g) hk :=
  cancel_subι _ _ _
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => ShortComplex.cyclesMap φ ≫ t) (cycIso_hom_comp_subι S₂)).trans
        ((ShortComplex.cyclesMap_i φ).trans
          (((congrArg (fun t => t ≫ φ.τ₂) (cycIso_hom_comp_subι S₁)).symm.trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun t => (cycIso S₁).hom ≫ t)
                  (sheafSubmoduleMap_comp_subι φ.τ₂ _ _ hk).symm))).trans
            (Category.assoc _ _ _).symm))))

/-- **The homology of a morphism of short complexes, read in the subquotient model.** The map
`homologyMap φ` is the map of subquotients induced by `φ.τ₂`. -/
lemma homologyMap_comp_homologyIsoSubq_hom {S₁ S₂ : ShortComplex X.Modules} (φ : S₁ ⟶ S₂)
    (hk : Stacks.Algebraization.kernelSubmodule S₁.g ≤
      AlgebraicGeometry.sheafSubmoduleComap φ.τ₂ (Stacks.Algebraization.kernelSubmodule S₂.g))
    (hi : imageSubmodule S₁.f ≤
      AlgebraicGeometry.sheafSubmoduleComap φ.τ₂ (imageSubmodule S₂.f)) :
    ShortComplex.homologyMap φ ≫ (homologyIsoSubq S₂).hom =
      (homologyIsoSubq S₁).hom ≫ subqMapAlong φ.τ₂
        (imageSubmodule_le_kernelSubmodule S₁.f S₁.g S₁.zero)
        (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero) hk hi := by
  refine (cancel_epi S₁.homologyπ).1 ?_
  calc S₁.homologyπ ≫ (ShortComplex.homologyMap φ ≫ (homologyIsoSubq S₂).hom)
      = (S₁.homologyπ ≫ ShortComplex.homologyMap φ) ≫ (homologyIsoSubq S₂).hom :=
        (Category.assoc _ _ _).symm
    _ = (ShortComplex.cyclesMap φ ≫ S₂.homologyπ) ≫ (homologyIsoSubq S₂).hom :=
        congrArg (fun t => t ≫ (homologyIsoSubq S₂).hom) (ShortComplex.homologyπ_naturality φ)
    _ = ShortComplex.cyclesMap φ ≫ (S₂.homologyπ ≫ (homologyIsoSubq S₂).hom) :=
        Category.assoc _ _ _
    _ = ShortComplex.cyclesMap φ ≫ ((cycIso S₂).hom ≫ subqπ (imageSubmodule S₂.f)
          (Stacks.Algebraization.kernelSubmodule S₂.g)
          (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero)) :=
        congrArg (fun t => ShortComplex.cyclesMap φ ≫ t)
          (homologyπ_comp_homologyIsoSubq_hom S₂)
    _ = (ShortComplex.cyclesMap φ ≫ (cycIso S₂).hom) ≫ subqπ (imageSubmodule S₂.f)
          (Stacks.Algebraization.kernelSubmodule S₂.g)
          (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero) :=
        (Category.assoc _ _ _).symm
    _ = ((cycIso S₁).hom ≫ AlgebraicGeometry.sheafSubmoduleMap φ.τ₂ _ _ hk) ≫
          subqπ (imageSubmodule S₂.f) (Stacks.Algebraization.kernelSubmodule S₂.g)
            (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero) :=
        congrArg (fun t => t ≫ _) (cyclesMap_comp_cycIso φ hk)
    _ = (cycIso S₁).hom ≫ (AlgebraicGeometry.sheafSubmoduleMap φ.τ₂ _ _ hk ≫
          subqπ (imageSubmodule S₂.f) (Stacks.Algebraization.kernelSubmodule S₂.g)
            (imageSubmodule_le_kernelSubmodule S₂.f S₂.g S₂.zero)) := Category.assoc _ _ _
    _ = (cycIso S₁).hom ≫ (subqπ (imageSubmodule S₁.f)
          (Stacks.Algebraization.kernelSubmodule S₁.g)
          (imageSubmodule_le_kernelSubmodule S₁.f S₁.g S₁.zero) ≫
            subqMapAlong φ.τ₂ _ _ hk hi) :=
        congrArg (fun t => (cycIso S₁).hom ≫ t)
          (subqπ_comp_subqMapAlong φ.τ₂ _ _ hk hi).symm
    _ = ((cycIso S₁).hom ≫ subqπ (imageSubmodule S₁.f)
          (Stacks.Algebraization.kernelSubmodule S₁.g)
          (imageSubmodule_le_kernelSubmodule S₁.f S₁.g S₁.zero)) ≫
            subqMapAlong φ.τ₂ _ _ hk hi := (Category.assoc _ _ _).symm
    _ = (S₁.homologyπ ≫ (homologyIsoSubq S₁).hom) ≫ subqMapAlong φ.τ₂ _ _ hk hi :=
        congrArg (fun t => t ≫ subqMapAlong φ.τ₂ _ _ hk hi)
          (homologyπ_comp_homologyIsoSubq_hom S₁).symm
    _ = S₁.homologyπ ≫ ((homologyIsoSubq S₁).hom ≫ subqMapAlong φ.τ₂ _ _ hk hi) :=
        Category.assoc _ _ _

/-- A monomorphism identifies a subquotient of its source with the corresponding subquotient of
its target: the isomorphism is the induced map of subquotients. -/
lemma subqPushIso_hom_eq {M : X.Modules} (j : M ⟶ L) (hj : Mono j) (N M' : M.Submodule)
    (h : N ≤ M') (hM : M' ≤ AlgebraicGeometry.sheafSubmoduleComap j (imageSubmodule (subι M' ≫ j)))
    (hN : N ≤ AlgebraicGeometry.sheafSubmoduleComap j (imageSubmodule (subι N ≫ j))) :
    (subqPushIso j hj N M' h).hom =
      subqMapAlong j h (imageSubmodule_subι_comp_mono j h) hM hN :=
  (cancel_epi (subqπ N M' h)).1
    (((cokernel.π_desc (C := X.Modules) _ _ _).trans
      (congrArg (fun t => t ≫ subqπ (imageSubmodule (subι N ≫ j))
          (imageSubmodule (subι M' ≫ j)) (imageSubmodule_subι_comp_mono j h))
        (cancel_subι (imageSubmodule (subι M' ≫ j)) _ _
          ((imageSubmoduleIso_hom_comp_subι (subι M' ≫ j)
              (mono_subι_comp j hj M')).trans
            (sheafSubmoduleMap_comp_subι j M' _ hM).symm)))).trans
      (subqπ_comp_subqMapAlong j h (imageSubmodule_subι_comp_mono j h) hM hN).symm)

end AlgebraicGeometry

end
