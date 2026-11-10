module

public import StacksFrontier.AlgebraicGeometry.Descent.FreeHomMatrixPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport

/-!
# Endomorphisms of a free module along a morphism inducing a bijection on global functions

Let `e : E ⟶ Z` be a morphism of schemes inducing a bijection `Γ(Z, 𝒪_Z) ⟶ Γ(E, 𝒪_E)` on global
functions — for instance the structure morphism of a projective line `𝐏¹_Z ⟶ Z` over an affine
scheme.  Then inverse image along `e` is a bijection on the endomorphisms of a finite free module:
an endomorphism of `𝒪_Z^{⊕I}` is a matrix of global functions on `Z`
(`Stacks.SheafOfModules.freeHomMatrixEquiv`), inverse image acts on it entrywise by `e`
(`Stacks.SheafOfModules.freeHomMatrixEquiv_pullbackFreeHom`), and `e` is bijective on the entries.

Consequently every automorphism of the inverse image of a module isomorphic to a finite free one
is the inverse image of an automorphism.  This is the rigidity that lets a pair of isomorphisms
`z^*N ≅ ℰ`, `b^*N ≅ 𝒢` over an almost blowup square be corrected to one compatible with a given
isomorphism over the exceptional line, in the proof of [Stacks, Tag 0EXD].

## Main results

* `AlgebraicGeometry.Scheme.Modules.bijective_pullback_map_free`: inverse image along `e` is a
  bijection on the morphisms between two finite free modules.
* `AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_eq_of_iso_free`: every automorphism
  of the inverse image of a module isomorphic to a finite free module is the inverse image of an
  automorphism.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

/-- **An automorphism of `P.obj M` is `P` of an automorphism of `M`**, as soon as `M` is
isomorphic to an object on whose endomorphisms `P` is bijective.  Stated in an arbitrary
category, so that it applies where the objects are sheaves of modules on schemes, at which the
simplifier does not rewrite. -/
theorem CategoryTheory.Functor.exists_iso_map_eq_of_bijective_of_iso {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] (P : 𝒞 ⥤ 𝒟) {M F : 𝒞} (ε : M ≅ F)
    (hb : Function.Bijective (fun g : F ⟶ F => P.map g)) (δ : P.obj M ≅ P.obj M) :
    ∃ β : M ≅ M, P.map β.hom = δ.hom := by
  obtain ⟨g, hg⟩ := hb.2 (P.map ε.inv ≫ δ.hom ≫ P.map ε.hom)
  obtain ⟨g', hg'⟩ := hb.2 (P.map ε.inv ≫ δ.inv ≫ P.map ε.hom)
  simp only at hg hg'
  obtain ⟨h1, h2⟩ : g ≫ g' = 𝟙 _ ∧ g' ≫ g = 𝟙 _ := by
    constructor <;> refine hb.1 ?_ <;>
      simp only [Functor.map_comp, Functor.map_id, hg, hg', Category.assoc] <;>
      simp [← Functor.map_comp_assoc]
  refine ⟨ε ≪≫ ⟨g, g', h1, h2⟩ ≪≫ ε.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, hg, Category.assoc]
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

namespace AlgebraicGeometry.Scheme.Modules

variable {E Z : Scheme.{u}} (e : E ⟶ Z)

/-- Conjugating by two isomorphisms and back is the identity, in an arbitrary category.  Stated
abstractly so that it applies where the objects are free sheaves of modules on schemes, at which
the simplifier does not rewrite. -/
private theorem conj_conj_eq {𝒞 : Type*} [Category 𝒞] {X X' Y Y' : 𝒞} (a : X ≅ X') (b : Y ≅ Y')
    (f : X ⟶ Y) : a.symm.inv ≫ (a.inv ≫ f ≫ b.hom) ≫ b.symm.hom = f := by
  simp

/-- The inverse image of a morphism of free modules, conjugated by the free identifications, is
`Stacks.SheafOfModules.pullbackFreeHom` of the morphism of sheaves of rings of `e`. -/
theorem pullbackFreeIso_inv_comp_map_comp_hom (I L : Type u)
    (g : SheafOfModules.free (R := Z.ringCatSheaf) I ⟶
      SheafOfModules.free (R := Z.ringCatSheaf) L) :
    haveI : (SheafOfModules.pushforward e.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs ((Scheme.Modules.pushforward e).IsRightAdjoint)
    haveI : (Opens.map e.base).Final := final_of_representablyFlat _
    (pullbackFreeIso e I).inv ≫ (Scheme.Modules.pullback e).map g ≫ (pullbackFreeIso e L).hom =
      Stacks.SheafOfModules.pullbackFreeHom e.toRingCatSheafHom I L g :=
  rfl

/-- **Inverse image along a morphism bijective on global functions is a bijection on morphisms
of finite free modules.** -/
theorem bijective_pullback_map_free (he : Function.Bijective e.appTop) (I L : Type u)
    [Finite L] :
    Function.Bijective (fun g : SheafOfModules.free (R := Z.ringCatSheaf) I ⟶
        SheafOfModules.free (R := Z.ringCatSheaf) L => (Scheme.Modules.pullback e).map g) := by
  have := Fintype.ofFinite L
  classical
  have : (SheafOfModules.pushforward e.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward e).IsRightAdjoint)
  have : (Opens.map e.base).Final := final_of_representablyFlat _
  -- the matrix of the conjugated inverse image is the matrix with `e` applied entrywise
  have hmat : ∀ g, Stacks.SheafOfModules.freeHomMatrixEquiv (R := E.ringCatSheaf)
      (isTerminalTop (α := E.Opens)) I L
        (Stacks.SheafOfModules.pullbackFreeHom e.toRingCatSheafHom I L g) =
      fun i k => e.appTop (Stacks.SheafOfModules.freeHomMatrixEquiv (R := Z.ringCatSheaf)
        (isTerminalTop (α := Z.Opens)) I L g i k) := fun g => by
    funext i k
    exact Stacks.SheafOfModules.freeHomMatrixEquiv_pullbackFreeHom e.toRingCatSheafHom
      (isTerminalTop (α := Z.Opens)) (isTerminalTop (α := E.Opens)) I L g i k
  -- the conjugated inverse image is bijective
  have hb : Function.Bijective (Stacks.SheafOfModules.pullbackFreeHom e.toRingCatSheafHom I L) := by
    have hentry : Function.Bijective (fun m : I → L → ToType (Z.ringCatSheaf.obj.obj (op ⊤)) =>
        fun i k => e.appTop (m i k)) :=
      ⟨fun m m' h => funext fun i => funext fun k => he.1 (congrFun (congrFun h i) k),
        fun m => ⟨fun i k => (he.2 (m i k)).choose, funext fun i => funext fun k =>
          (he.2 (m i k)).choose_spec⟩⟩
    refine (Function.Bijective.of_comp_iff' (Equiv.bijective
      (Stacks.SheafOfModules.freeHomMatrixEquiv (R := E.ringCatSheaf)
        (isTerminalTop (α := E.Opens)) I L)) _).mp ?_
    convert hentry.comp (Equiv.bijective (Stacks.SheafOfModules.freeHomMatrixEquiv
      (R := Z.ringCatSheaf) (isTerminalTop (α := Z.Opens)) I L)) using 1
    · rfl
    · exact heq_of_eq (funext hmat)
  -- conjugating back by the free identifications
  have heq : (fun g : SheafOfModules.free (R := Z.ringCatSheaf) I ⟶
        SheafOfModules.free (R := Z.ringCatSheaf) L => (Scheme.Modules.pullback e).map g) =
      (Iso.homCongr (pullbackFreeIso e I).symm (pullbackFreeIso e L).symm) ∘
        Stacks.SheafOfModules.pullbackFreeHom e.toRingCatSheafHom I L := by
    funext g
    exact (conj_conj_eq (pullbackFreeIso e I) (pullbackFreeIso e L)
      ((Scheme.Modules.pullback e).map g)).symm.trans
        (congrArg (fun x => (pullbackFreeIso e I).symm.inv ≫ x ≫ (pullbackFreeIso e L).symm.hom)
          (pullbackFreeIso_inv_comp_map_comp_hom e I L g))
  rw [heq]
  exact (Equiv.bijective _).comp hb

/-- **Every automorphism of the inverse image of a module isomorphic to a finite free module is
the inverse image of an automorphism**, along a morphism bijective on global functions. -/
theorem exists_iso_pullback_map_eq_of_iso_free (he : Function.Bijective e.appTop) {M : Z.Modules}
    {I : Type u} [Finite I] (ε : M ≅ SheafOfModules.free (R := Z.ringCatSheaf) I)
    (δ : (Scheme.Modules.pullback e).obj M ≅ (Scheme.Modules.pullback e).obj M) :
    ∃ β : M ≅ M, (Scheme.Modules.pullback e).map β.hom = δ.hom :=
  CategoryTheory.Functor.exists_iso_map_eq_of_bijective_of_iso _ ε
    (bijective_pullback_map_free e he I I) δ

end AlgebraicGeometry.Scheme.Modules

end
