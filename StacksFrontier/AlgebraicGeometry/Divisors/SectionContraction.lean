module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# The sheaf of ideals cut out by a regular section of an invertible module

Let `(C, J)` be a site with a sheaf of commutative rings `𝒪`, and let `L` be an invertible
`𝒪`-module with a global section `s`.  Contracting with `s` turns the inverse `L^{⊗ -1}` into a
sheaf of ideals: the composite

`L^{⊗ -1} ≅ L^{⊗ -1} ⊗ 𝒪 ⟶ L^{⊗ -1} ⊗ L ≅ 𝒪`,

whose middle arrow is multiplication by `s`, is a morphism `L^{⊗ -1} ⟶ 𝒪`.  Tensoring by an
invertible module is an equivalence, so this morphism is a monomorphism exactly when
multiplication by `s` is one, that is exactly when `s` is a regular section.  Its image is then
a sheaf of ideals of `𝒪` isomorphic to `L^{⊗ -1}`, and in particular invertible.

## Main definitions

* `Stacks.SheafOfModules.Invertible.isoOfTensorUnit`: two modules which are both inverse to the
  same module, for the tensor product, are isomorphic.
* `Stacks.SheafOfModules.Invertible.inverseSheaf` is `L^{⊗ -1}`, with
  `Stacks.SheafOfModules.Invertible.inverseSheafEvaluation` the pairing `L^{⊗ -1} ⊗ L ≅ 𝒪`.
* `Stacks.SheafOfModules.Invertible.sectionContraction` is the contraction
  `L^{⊗ -1} ⟶ 𝒪` with a global section of `L`.
* `Stacks.SheafOfModules.Invertible.sectionIdealSubmodule` is its image, a sheaf of ideals
  of `𝒪`.

## Main results

* `Stacks.SheafOfModules.Invertible.mono_sectionContraction`: the contraction with a regular
  section is a monomorphism.
* `Stacks.SheafOfModules.Invertible.inverseSheafIsoSectionIdeal`: for a regular section the
  contraction identifies `L^{⊗ -1}` with that sheaf of ideals, and
* `Stacks.SheafOfModules.Invertible.isInvertible_sectionIdealSubmodule`: the sheaf of ideals is
  therefore invertible.

## Implementation notes

The inverse of an invertible module is its `-1`st tensor power, and the pairing
`L^{⊗ -1} ⊗ L ≅ 𝒪` is the instance `n = -1` of the successor isomorphism
`L^{⊗ n} ⊗ L ≅ L^{⊗ (n+1)}`, since the zeroth power is the structure sheaf by definition.

Monicity comes from the equivalence `- ⊗ L^{⊗ -1}`, not from any local trivialisation of `L`:
the contraction is, up to the unit and braiding constraints, the image of multiplication by `s`
under that equivalence.  The image is formed with
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule`, whose sections are those of `𝒪` lying
locally in the range; for a monomorphism the local condition collapses, which is what makes the
image isomorphic to `L^{⊗ -1}`.

`Stacks.SheafOfModules.Invertible.isoOfTensorUnit` is the general form of the comparison by
which `𝒪_X(-D)` is identified with the defining ideal sheaf of `D`: given pairings
`M ⊗ G ≅ 𝒪` and `N ⊗ M ≅ 𝒪`, the chain
`N ≅ N ⊗ 𝒪 ≅ N ⊗ (M ⊗ G) ≅ (N ⊗ M) ⊗ G ≅ 𝒪 ⊗ G ≅ G` is an isomorphism `N ≅ G`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite Limits
open Stacks.SheafOfModules.TensorSheafification (structureSheaf)

universe w v u

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

noncomputable section

/-- **Two inverses of the same module are isomorphic.**  Given pairings `M ⊗ G ≅ 𝒪` and
`N ⊗ M ≅ 𝒪`, cancelling `M` identifies `N` with `G`. -/
def isoOfTensorUnit {G M N : SheafOfModules.{w} (structureSheaf O hO)}
    (eM : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (M)).obj (G)) ≅ SheafOfModules.unit (structureSheaf O hO))
    (eN : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (N)).obj (M)) ≅ SheafOfModules.unit (structureSheaf O hO)) : N ≅ G :=
  (tensorProductRightUnitor O hO N).symm ≪≫
    tensorProductIso O hO (Iso.refl N) eM.symm ≪≫
    (tensorProductAssociator O hO N M G).symm ≪≫
    tensorProductIso O hO eN (Iso.refl G) ≪≫
    tensorProductLeftUnitor O hO G

variable (L : SheafOfModules.{w} (structureSheaf O hO))
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]

/-- Tensoring by an invertible module preserves monomorphisms, being an equivalence. -/
theorem mono_tensorRightFunctor_map (G : SheafOfModules.{w} (structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO G]
    {M N : SheafOfModules.{w} (structureSheaf O hO)} (f : M ⟶ N)
    (hf : Mono f) : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (G)).map f) := by
  have := tensorRightFunctor_isEquivalence O hO G
  exact @Functor.map_mono _ _ _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj G) _ _ _
    f hf

/-- The inverse `L^{⊗ -1}` of an invertible module. -/
def inverseSheaf : SheafOfModules.{w} (structureSheaf O hO) := tensorPower O hO L (-1)

/-- The inverse of an invertible module is invertible. -/
instance inverseSheaf_isInvertible :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO (inverseSheaf O hO L) :=
  tensorPower_isInvertible O hO L (-1)

/-- The evaluation pairing `L^{⊗ -1} ⊗ L ≅ 𝒪`. -/
def inverseSheafEvaluation :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((inverseSheaf O hO L))).obj (L)) ≅ SheafOfModules.unit (structureSheaf O hO) :=
  tensorPowerSuccIso O hO L (-1)

/-- The unit constraint `L^{⊗ -1} ⊗ 𝒪 ≅ L^{⊗ -1}`, in the shape produced by tensoring on the
right by `L^{⊗ -1}`. -/
def inverseSheafUnitIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        ((inverseSheaf O hO L))).obj (SheafOfModules.unit (structureSheaf O hO))
      ≅ inverseSheaf O hO L :=
  tensorProductLeftUnitor O hO (inverseSheaf O hO L)

/-- The braiding `L ⊗ L^{⊗ -1} ≅ L^{⊗ -1} ⊗ L`, in the shape produced by tensoring on the right
by `L^{⊗ -1}`. -/
def inverseSheafSwapIso : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        ((inverseSheaf O hO L))).obj L ≅
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((inverseSheaf O hO L))).obj (L)) :=
  tensorProductBraiding O hO L (inverseSheaf O hO L)

/-- **Contraction with a global section.**  The morphism `L^{⊗ -1} ⟶ 𝒪` obtained by tensoring
multiplication by `s` with `L^{⊗ -1}` and evaluating. -/
def sectionContraction (s : L.sections) :
    inverseSheaf O hO L ⟶ SheafOfModules.unit (structureSheaf O hO) :=
  (inverseSheafUnitIso O hO L).inv ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        ((inverseSheaf O hO L))).map (L.unitHomEquiv.symm s) ≫
    (inverseSheafSwapIso O hO L).hom ≫ (inverseSheafEvaluation O hO L).hom

/-- **Contraction with a regular section is a monomorphism.**  Multiplication by a regular
section is a monomorphism, and tensoring by the invertible module `L^{⊗ -1}` preserves
monomorphisms. -/
theorem mono_sectionContraction (s : L.sections)
    (hs : Mono (L.unitHomEquiv.symm s)) : Mono (sectionContraction O hO L s) := by
  have key : ∀ {X Y : SheafOfModules.{w} (structureSheaf O hO)} (e : X ≅ Y), Mono e.hom :=
    fun e => @IsIso.mono_of_iso _ _ _ _ e.hom (Iso.isIso_hom e)
  exact mono_comp' (key (inverseSheafUnitIso O hO L).symm)
    (mono_comp' (mono_tensorRightFunctor_map O hO _ _ hs)
      (mono_comp' (key (inverseSheafSwapIso O hO L)) (key (inverseSheafEvaluation O hO L))))

/-- **The sheaf of ideals cut out by a global section of an invertible module**: the image of
contraction with the section. -/
def sectionIdealSubmodule (s : L.sections) :
    (SheafOfModules.unit (structureSheaf O hO)).Submodule :=
  Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (sectionContraction O hO L s)

/-- For a regular section, contraction identifies `L^{⊗ -1}` with the sheaf of ideals it cuts
out. -/
def inverseSheafIsoSectionIdeal (s : L.sections) (hs : Mono (L.unitHomEquiv.symm s)) :
    inverseSheaf O hO L ≅ (sectionIdealSubmodule O hO L s).toSheafOfModules :=
  haveI := mono_sectionContraction O hO L s hs
  Stacks.SheafOfModules.ImageSubsheaf.imageIso (sectionContraction O hO L s)

/-- The sheaf of ideals cut out by a regular section of an invertible module is invertible. -/
theorem isInvertible_sectionIdealSubmodule (s : L.sections) (hs : Mono (L.unitHomEquiv.symm s)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible O hO
      (sectionIdealSubmodule O hO L s).toSheafOfModules :=
  isInvertible_of_iso O hO (inverseSheafIsoSectionIdeal O hO L s hs)

end

end Stacks.SheafOfModules.Invertible

end
