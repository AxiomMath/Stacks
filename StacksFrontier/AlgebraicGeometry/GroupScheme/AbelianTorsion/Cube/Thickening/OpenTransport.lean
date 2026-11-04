module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CubeRelation

/-!
# Transporting triviality over an open of a chart to an open of the base

Let `c : P ⟶ Z` be a morphism of schemes, `φ : T ⟶ Z` an open immersion and `U'` an open of `T`.
If the pullback of a sheaf of modules `N` on `P` to `(P ×_Z T) ×_T U'` is trivial, then so is its
pullback to `P ×_Z φ(U')`: the two schemes are isomorphic over `P`, because `U' ⟶ T ⟶ Z` is the
isomorphism `U' ≅ φ(U')` followed by the inclusion of `φ(U')`.

## Main results

* `Stacks.CubeOpenAtUnit.isTrivial_of_iso_over`: triviality of a pullback is invariant under
  isomorphism of the sources over the target.
* `Stacks.CubeOpenAtUnit.isTrivial_pullback_fst_image`: the transport described above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.CubeOpenAtUnit

/-- **Triviality of a pullback depends only on the source up to isomorphism over the target.**
If `e : Y ≅ Y'` satisfies `e.hom ≫ a' = a` and the pullback of `N` along `a'` is trivial, so is
its pullback along `a`. -/
theorem isTrivial_of_iso_over {P Y Y' : Scheme.{u}}
    (N : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (a : Y ⟶ P) (a' : Y' ⟶ P) (e : Y ≅ Y') (he : e.hom ≫ a' = a)
    (h : Stacks.SheafOfModules.IsTrivial Y'.presheaf Y'.ringCatIsSheaf
      ((modulePullback a'.toLRSHom.toShHom).obj N)) :
    Stacks.SheafOfModules.IsTrivial Y.presheaf Y.ringCatIsSheaf
      ((modulePullback a.toLRSHom.toShHom).obj N) := by
  obtain ⟨t⟩ := h
  subst he
  exact ⟨(modulePullbackComp e.hom.toLRSHom.toShHom a'.toLRSHom.toShHom).app N ≪≫
    (modulePullback e.hom.toLRSHom.toShHom).mapIso t ≪≫
    modulePullbackObjUnitIso e.hom.toLRSHom.toShHom⟩

/-- `P ×_Z φ(U')` is isomorphic over `P` to `(P ×_Z T) ×_T U'`, for an open immersion
`φ : T ⟶ Z` and an open `U'` of `T`. -/
def pullbackImageIso {P Z T : Scheme.{u}} (c : P ⟶ Z) (φ : T ⟶ Z) [IsOpenImmersion φ]
    (U' : T.Opens) :
    pullback c (φ ''ᵁ U').ι ≅ pullback (pullback.snd c φ) U'.ι := by
  have H : IsPullback (pullback.fst (pullback.snd c φ) U'.ι ≫ pullback.fst c φ)
      (pullback.snd (pullback.snd c φ) U'.ι) c (U'.ι ≫ φ) :=
    (IsPullback.of_hasPullback (pullback.snd c φ) U'.ι).paste_horiz
      (IsPullback.of_hasPullback c φ)
  have H' : IsPullback (pullback.fst (pullback.snd c φ) U'.ι ≫ pullback.fst c φ)
      (pullback.snd (pullback.snd c φ) U'.ι ≫ (φ.isoImage U').hom) c (φ ''ᵁ U').ι :=
    H.of_iso (Iso.refl _) (Iso.refl _) (φ.isoImage U') (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  exact (IsPullback.of_hasPullback c (φ ''ᵁ U').ι).isoIsPullback _ _ H'

/-- The isomorphism `pullbackImageIso c φ U'` commutes with the projections to `P`. -/
theorem pullbackImageIso_hom_fst {P Z T : Scheme.{u}} (c : P ⟶ Z) (φ : T ⟶ Z)
    [IsOpenImmersion φ] (U' : T.Opens) :
    (pullbackImageIso c φ U').hom ≫
        (pullback.fst (pullback.snd c φ) U'.ι ≫ pullback.fst c φ) =
      pullback.fst c (φ ''ᵁ U').ι :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **Triviality over an open of a chart gives triviality over its image.** For `c : P ⟶ Z`,
an open immersion `φ : T ⟶ Z` and an open `U'` of `T`, if the pullback of `N` to
`(P ×_Z T) ×_T U'` is trivial, so is its pullback to `P ×_Z φ(U')`. -/
theorem isTrivial_pullback_fst_image {P Z T : Scheme.{u}} (c : P ⟶ Z) (φ : T ⟶ Z)
    [IsOpenImmersion φ] (N : SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
    (U' : T.Opens)
    (h : Stacks.SheafOfModules.IsTrivial (pullback (pullback.snd c φ) U'.ι).presheaf
      (pullback (pullback.snd c φ) U'.ι).ringCatIsSheaf
      ((modulePullback (pullback.fst (pullback.snd c φ) U'.ι ≫
        pullback.fst c φ).toLRSHom.toShHom).obj N)) :
    Stacks.SheafOfModules.IsTrivial (pullback c (φ ''ᵁ U').ι).presheaf
      (pullback c (φ ''ᵁ U').ι).ringCatIsSheaf
      ((modulePullback (pullback.fst c (φ ''ᵁ U').ι).toLRSHom.toShHom).obj N) :=
  isTrivial_of_iso_over N _ _ (pullbackImageIso c φ U') (pullbackImageIso_hom_fst c φ U') h

end Stacks.CubeOpenAtUnit

end
