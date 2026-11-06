module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected

/-!
# Images as finite type quasi-coherent submodules

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`. The image of a
morphism from a quasi-coherent `𝒪_F`-module of finite type to a quasi-coherent `𝒪_F`-module `G`
is a quasi-coherent submodule of `G` of finite type, and in an abelian category the images of the
legs of a colimit cocone, indexed by a category of any size, cover its point. These are the two
facts the colimit assertion of Stacks 0829 is assembled from.

## Main results

* `AlgebraicGeometry.Space.iSup_imageSubobject_eq_top_of_isColimit_of_category`: the images of the
  legs of a colimit cocone have supremum the whole of its point.
* `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobjectProperty_imageSubobject`: the image of
  a morphism out of a finite type quasi-coherent module into a quasi-coherent module `G` is a
  finite type quasi-coherent submodule of `G`.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

section Subobjects

variable {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{u} C]

/-- The images of the legs of a colimit cocone have supremum the whole of its point: the
inclusion of that supremum is an epimorphism because every leg factors through it, and it is a
monomorphism because it is a subobject arrow. -/
lemma iSup_imageSubobject_eq_top_of_isColimit_of_category {I : Type*} [Category* I]
    {D : I ⥤ C} {F : C} (φ : D ⟶ (Functor.const I).obj F)
    (hc : IsColimit (Cocone.mk F φ)) :
    (⨆ i, imageSubobject (φ.app i)) = ⊤ := by
  classical
  let T : Subobject F := ⨆ i, imageSubobject (φ.app i)
  let q : (T : C) ⟶ F := T.arrow
  have hq : Epi q := by
    refine ⟨fun {Z} g h hh => ?_⟩
    apply hc.hom_ext
    intro i
    let G : Subobject F := imageSubobject (φ.app i)
    have hfac : φ.app i = factorThruImageSubobject (φ.app i) ≫ G.arrow :=
      (imageSubobject_arrow_comp (φ.app i)).symm
    have hle : G ≤ T := le_iSup (fun j => imageSubobject (φ.app j)) i
    let k : (G : C) ⟶ (T : C) := Subobject.ofLE G T hle
    have hk : G.arrow = k ≫ q := (Subobject.ofLE_arrow _).symm
    let l : D.obj i ⟶ (T : C) := factorThruImageSubobject (φ.app i) ≫ k
    have hφ : φ.app i = l ≫ q := by simpa only [l, Category.assoc, ← hk] using hfac
    simp only [hφ, Category.assoc, hh]
  have : Epi q := hq
  have : Mono q := by dsimp [q]; infer_instance
  have : IsIso q := isIso_of_mono_of_epi q
  simpa only [T, q, Subobject.mk_arrow] using Subobject.mk_eq_top_of_isIso q

end Subobjects

section Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

set_option synthInstance.maxHeartbeats 200000 in
/-- **The image of a morphism out of a finite type quasi-coherent module is a finite type
quasi-coherent submodule of the target**, when the target is quasi-coherent: it is quasi-coherent
because quasi-coherence is closed under kernels and cokernels, and of finite type because it is a
quotient of the source. -/
theorem finiteTypeQuasicoherentSubobjectProperty_imageSubobject
    {M G : Modules.{u, u} B S hS F hF} (f : M ⟶ G) (hM : M.IsQuasicoherentOnSite)
    (hG : G.IsQuasicoherentOnSite) (hfin : M.IsFiniteType) :
    finiteTypeQuasicoherentSubobjectProperty B S hS F hF G (imageSubobject f) := by
  refine ⟨isQuasicoherentOnSite_image B S hS F hF
    (isClosedUnderKernels_quasicoherentSheaves B S hS F hF
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF))
    (isClosedUnderCokernels_quasicoherentSheaves B S hS F hF) f hM hG, ?_⟩
  have : Epi (factorThruImageSubobject f) := by
    dsimp [factorThruImageSubobject]
    apply epi_comp
  exact Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (factorThruImageSubobject f) hfin

end Space

end AlgebraicGeometry.Space

end
