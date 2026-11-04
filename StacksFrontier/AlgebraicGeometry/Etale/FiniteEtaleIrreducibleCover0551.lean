module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ComponentsOverFiniteSeparableExtension

/-!
# Geometrically irreducible generic-fibre components after a finite étale base change

Let `f : X ⟶ Y` be a quasi-compact morphism, locally of finite type, onto an irreducible
scheme `Y`. [Stacks, Tag 0551] asserts that after restricting `Y` to a nonempty open `V` there is a
surjective finite étale cover `g : Y' ⟶ V` by an irreducible affine scheme such that every
irreducible component of the generic fibre of the base change `f' : Y' ×_Y X ⟶ Y'` is
geometrically irreducible.

The statement is proved here under the hypothesis
`AlgebraicGeometry.SpreadsOutFiniteSeparableResidueExtension Y`, which says that a finite separable
extension of the residue field at the generic point of `Y` is realised by a surjective finite étale
cover of a nonempty open of `Y` by an irreducible affine scheme; it mentions neither `X` nor `f`.

## Main definitions

* `AlgebraicGeometry.GeometricallyIrreducibleComponents`: every irreducible component of the
  source of a morphism, with its reduced induced closed subscheme structure, is geometrically
  irreducible over the target.
* `AlgebraicGeometry.SpreadsOutFiniteSeparableResidueExtension`: the hypothesis described above.

## Main results

* `AlgebraicGeometry.GeometricallyIrreducibleComponents.of_iso`: the property transports along an
  isomorphism of the source compatible with an isomorphism of the target.
* `AlgebraicGeometry.geometricallyIrreducibleComponents_fiber_pullback_fst`: the fibre of a base
  change is the base change of a fibre, so the property for the latter gives it for the former.
* `exists_finiteEtale_cover_geometricallyIrreducible_genericFiber_components_of_spreadsOut`:
  [Stacks, Tag 0551] under the hypothesis above.

## References

* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
* [Stacks Project, Tag 054R](https://stacks.math.columbia.edu/tag/054R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry

open CommRingCat Scheme.IdealSheafData

/-- Geometric irreducibility respects isomorphisms. -/
instance : MorphismProperty.RespectsIso (@GeometricallyIrreducible.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @GeometricallyIrreducible.{u})

/-- The image of a closed set under an isomorphism of schemes is closed. -/
theorem isClosed_image_of_iso {A B : Scheme.{u}} (e : A ≅ B) {Z : Set A} (hZ : IsClosed Z) :
    IsClosed (⇑e.hom '' Z) :=
  (Homeomorph.isClosed_image (Scheme.homeoOfIso e)).mpr hZ

/-- Pushing the vanishing ideal of a closed set forward along an isomorphism gives the vanishing
ideal of the image. -/
theorem Scheme.IdealSheafData.map_vanishingIdeal_of_iso {A B : Scheme.{u}} (e : A ≅ B)
    (Z : Closeds A) :
    (vanishingIdeal Z).map e.hom = vanishingIdeal ⟨⇑e.hom '' Z, isClosed_image_of_iso e Z.2⟩ := by
  rw [map_vanishingIdeal]
  congr 1
  exact Closeds.ext (isClosed_image_of_iso e Z.2).closure_eq

/-- The inverse of an isomorphism of schemes undoes it on subsets. -/
theorem image_image_inv_of_iso {A B : Scheme.{u}} (e : A ≅ B) (Z : Set A) :
    ⇑e.inv '' (⇑e.hom '' Z) = Z := by
  rw [Set.image_image]
  simp [Scheme.hom_inv_apply e]

/-- An isomorphism of schemes identifies the reduced induced closed subscheme structure on a
closed set with the one on its image. -/
def Scheme.IdealSheafData.subschemeIsoOfIso {A B : Scheme.{u}} (e : A ≅ B) (Z : Closeds A) :
    (vanishingIdeal Z).subscheme ≅
      (vanishingIdeal (⟨⇑e.hom '' Z, isClosed_image_of_iso e Z.2⟩ : Closeds B)).subscheme where
  hom := subschemeMap _ _ e.hom (le_of_eq (map_vanishingIdeal_of_iso e Z).symm)
  inv := subschemeMap _ _ e.inv (le_of_eq (by
    rw [show e.inv = e.symm.hom from rfl,
      map_vanishingIdeal_of_iso e.symm ⟨⇑e.hom '' Z, isClosed_image_of_iso e Z.2⟩]
    congr 1
    exact Closeds.ext (image_image_inv_of_iso e Z).symm))
  hom_inv_id := by
    rw [← cancel_mono (vanishingIdeal Z).subschemeι]
    simp [Category.assoc]
  inv_hom_id := by
    rw [← cancel_mono
      (vanishingIdeal (⟨⇑e.hom '' Z, isClosed_image_of_iso e Z.2⟩ : Closeds B)).subschemeι]
    simp [Category.assoc]

/-- `GeometricallyIrreducibleComponents a` says that every irreducible component of the source of
`a`, equipped with its reduced induced closed subscheme structure, is geometrically irreducible
over the target of `a`. -/
def GeometricallyIrreducibleComponents {A S : Scheme.{u}} (a : A ⟶ S) : Prop :=
  ∀ Z : irreducibleComponents A,
    GeometricallyIrreducible
      ((vanishingIdeal (X := A)
        ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫ a)

/-- If isomorphisms of the sources and of the targets identify `a` with `b`, and the image of the
closed set `Zc`, with its reduced induced closed subscheme structure, is geometrically irreducible
over the target of `b`, then `Zc` is geometrically irreducible over the target of `a`. -/
theorem geometricallyIrreducible_subschemeι_of_iso {A B S T : Scheme.{u}} {a : A ⟶ S} {b : B ⟶ T}
    (eA : A ≅ B) (eS : S ≅ T) (w : a ≫ eS.hom = eA.hom ≫ b) (Zc : Closeds A)
    (key : GeometricallyIrreducible
      ((vanishingIdeal
        (⟨⇑eA.hom '' Zc, isClosed_image_of_iso eA Zc.2⟩ : Closeds B)).subschemeι ≫ b)) :
    GeometricallyIrreducible ((vanishingIdeal Zc).subschemeι ≫ a) := by
  have ha : a = eA.hom ≫ b ≫ eS.inv := by rw [← Category.assoc, ← w]; simp
  have h1 : (subschemeIsoOfIso eA Zc).hom ≫
      (vanishingIdeal (⟨⇑eA.hom '' Zc, isClosed_image_of_iso eA Zc.2⟩ : Closeds B)).subschemeι =
      (vanishingIdeal Zc).subschemeι ≫ eA.hom :=
    subschemeMap_subschemeι _ _ eA.hom (le_of_eq (map_vanishingIdeal_of_iso eA Zc).symm)
  have hcomp : (vanishingIdeal Zc).subschemeι ≫ a =
      (subschemeIsoOfIso eA Zc).hom ≫
        ((vanishingIdeal
          (⟨⇑eA.hom '' Zc, isClosed_image_of_iso eA Zc.2⟩ : Closeds B)).subschemeι ≫ b)
          ≫ eS.inv := by
    simp only [ha, Category.assoc, reassoc_of% h1]
  rw [hcomp, MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible.{u}),
    MorphismProperty.cancel_right_of_respectsIso (P := @GeometricallyIrreducible.{u})]
  exact key

/-- If the sources and the targets of `a` and `b` are
identified by isomorphisms making the square commute, then the components of the source of `b`
being geometrically irreducible forces the same for `a`. -/
theorem GeometricallyIrreducibleComponents.of_iso {A B S T : Scheme.{u}} {a : A ⟶ S} {b : B ⟶ T}
    (eA : A ≅ B) (eS : S ≅ T) (w : a ≫ eS.hom = eA.hom ≫ b)
    (hB : GeometricallyIrreducibleComponents b) : GeometricallyIrreducibleComponents a := fun Z =>
  geometricallyIrreducible_subschemeι_of_iso eA eS w
    ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩
    (hB ⟨⇑eA.hom '' Z.1, image_mem_irreducibleComponents_of_iso eA Z.2⟩)

/-- If `φ : k ⟶ K₁` and `ψ : k ⟶ K₂` differ by an isomorphism `ε : K₁ ≅ K₂`, and the base change
of `F` along `Spec.map ψ` has geometrically irreducible components, so does its base change along
`Spec.map φ`. -/
theorem geometricallyIrreducibleComponents_pullback_congr {D : Scheme.{u}}
    {k K₁ K₂ : CommRingCat.{u}} (F : D ⟶ Spec k) (φ : k ⟶ K₁) (ψ : k ⟶ K₂) (ε : K₁ ≅ K₂)
    (hε : φ ≫ ε.hom = ψ)
    (hB : GeometricallyIrreducibleComponents (pullback.snd F (Spec.map ψ))) :
    GeometricallyIrreducibleComponents (pullback.snd F (Spec.map φ)) := by
  have eq₂ : Spec.map φ ≫ 𝟙 (Spec k) = Spec.map ε.inv ≫ Spec.map ψ := by
    rw [Category.comp_id, ← Spec.map_comp, show ψ ≫ ε.inv = φ by
      rw [← hε, Category.assoc, ε.hom_inv_id, Category.comp_id]]
  refine .of_iso (asIso (pullback.map F (Spec.map φ) F (Spec.map ψ) (𝟙 D)
    (Spec.map ε.inv) (𝟙 (Spec k)) (by simp) eq₂)) (asIso (Spec.map ε.inv)) ?_ hB
  rw [asIso_hom, asIso_hom, pullback.lift_snd]

/-- For `g₀ : Y' ⟶ Y` and a point `η'` of `Y'`, if the base change of the fibre of `f` at `g₀ η'`
along the induced map of residue fields has geometrically irreducible components, so does the
fibre of `pullback.fst g₀ f` at `η'`. -/
theorem geometricallyIrreducibleComponents_fiber_pullback_fst {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g₀ : Y' ⟶ Y) (η' : Y')
    (hB : GeometricallyIrreducibleComponents (pullback.snd
      (f.fiberToSpecResidueField (g₀ η')) (Spec.map (g₀.residueFieldMap η')))) :
    GeometricallyIrreducibleComponents ((pullback.fst g₀ f).fiberToSpecResidueField η') := by
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback g₀ f).flip η'
  refine .of_iso (hsq.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)) (Iso.refl _) ?_ hB
  rw [Iso.refl_hom, Category.comp_id]
  exact (IsPullback.isoIsPullback_hom_snd _ _ hsq (IsPullback.of_hasPullback _ _)).symm

/-- `AlgebraicGeometry.geometricallyIrreducibleComponents_fiber_pullback_fst`, with the image
`g₀ η' = η` of the point named. -/
theorem geometricallyIrreducibleComponents_fiber_pullback_fst' {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g₀ : Y' ⟶ Y) (η' : Y') (η : Y) (hη : g₀ η' = η)
    (hB : GeometricallyIrreducibleComponents (pullback.snd (f.fiberToSpecResidueField η)
      (Spec.map ((Y.residueFieldCongr hη).inv ≫ g₀.residueFieldMap η')))) :
    GeometricallyIrreducibleComponents ((pullback.fst g₀ f).fiberToSpecResidueField η') := by
  subst hη
  refine geometricallyIrreducibleComponents_fiber_pullback_fst f g₀ η' ?_
  rwa [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp] at hB

/-- For an irreducible scheme `Y`: every finite separable extension `K` of the residue field at the
generic point of `Y` is realised by a surjective finite étale cover `g : Y' ⟶ V` of a nonempty
open `V` of `Y` with `Y'` irreducible and affine, in the strong sense that the generic point `η'`
of `Y'` lies over the generic point of `Y` and has residue field `K` as an extension of it. -/
def SpreadsOutFiniteSeparableResidueExtension (Y : Scheme.{u}) [IrreducibleSpace Y] : Prop :=
  ∀ (K : Type u) (_ : Field K)
    (_ : Algebra (Y.residueField (genericPoint Y)) K)
    (_ : Module.Finite (Y.residueField (genericPoint Y)) K)
    (_ : Algebra.IsSeparable (Y.residueField (genericPoint Y)) K),
    ∃ (V : Y.Opens) (_ : V.1.Nonempty) (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme)
      (_ : Surjective g) (_ : IsFinite g) (_ : Etale g) (_ : IrreducibleSpace Y')
      (_ : IsAffine Y') (η' : Y') (_ : IsGenericPoint η' Set.univ)
      (hη' : (g ≫ V.ι) η' = genericPoint Y)
      (ε : Y'.residueField η' ≅ CommRingCat.of K),
      (Y.residueFieldCongr hη').inv ≫ (g ≫ V.ι).residueFieldMap η' ≫ ε.hom =
        CommRingCat.ofHom (algebraMap (Y.residueField (genericPoint Y)) K)

/-- Under the hypothesis `SpreadsOutFiniteSeparableResidueExtension Y`, after passing to a nonempty
open of an irreducible base, a quasi-compact morphism locally of finite type admits a finite étale
surjective base change from an irreducible affine scheme whose generic fibre has geometrically
irreducible irreducible components. -/
theorem exists_finiteEtale_cover_geometricallyIrreducible_genericFiber_components_of_spreadsOut
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : SpreadsOutFiniteSeparableResidueExtension Y) :
    ∃ (V : Y.Opens) (_ : V.1.Nonempty)
      (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme)
      (_ : Surjective g) (_ : IsFinite g) (_ : Etale g)
      (_ : IrreducibleSpace Y') (_ : IsAffine Y'),
      let X_V := pullback V.ι f
      let fV : X_V ⟶ V.toScheme := pullback.fst V.ι f
      let X' := pullback (g ≫ V.ι) f
      let f' : X' ⟶ Y' := pullback.fst (g ≫ V.ι) f
      let g' : X' ⟶ X_V := pullback.lift
        (pullback.fst (g ≫ V.ι) f ≫ g)
        (pullback.snd (g ≫ V.ι) f) (by
          rw [Category.assoc]
          exact pullback.condition)
      IsPullback g' f' fV g ∧
        Surjective g' ∧ IsFinite g' ∧ Etale g' ∧
        ∀ (η : Y'), IsGenericPoint η Set.univ →
          ∀ Z : irreducibleComponents (f'.fiber η),
            GeometricallyIrreducible
              ((Scheme.IdealSheafData.vanishingIdeal (X := f'.fiber η)
                  ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩).subschemeι ≫
                f'.fiberToSpecResidueField η) := by
  classical
  have hlft : LocallyOfFiniteType (f.fiberToSpecResidueField (genericPoint Y)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField (genericPoint Y))) inferInstance
  obtain ⟨K, hKfield, hKalg, hKfin, hKsep, hK⟩ :=
    exists_finite_separable_extension_geometricallyIrreducible_components
      (Y.residueField (genericPoint Y)) (f.fiber (genericPoint Y))
      (f.fiberToSpecResidueField (genericPoint Y))
      (finite_irreducibleComponents_fiber f (genericPoint Y))
  obtain ⟨V, hV, Y', g, hgsurj, hgfin, hget, hirr, haff, η', hη'gen, hη'over, ε, hε⟩ :=
    hY K hKfield hKalg hKfin hKsep
  have hsq : IsPullback
      (pullback.lift (pullback.fst (g ≫ V.ι) f ≫ g) (pullback.snd (g ≫ V.ι) f)
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.fst (g ≫ V.ι) f) (pullback.fst V.ι f) g := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback V.ι f).flip
    rw [pullback.lift_snd]
    exact (IsPullback.of_hasPullback (g ≫ V.ι) f).flip
  refine ⟨V, hV, Y', g, hgsurj, hgfin, hget, hirr, haff, hsq,
    MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hgsurj,
    MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hgfin,
    MorphismProperty.of_isPullback (P := @Etale) hsq.flip hget, ?_⟩
  · intro η hη
    have hηη' : η = η' := hη.eq hη'gen
    subst hηη'
    refine geometricallyIrreducibleComponents_fiber_pullback_fst' f (g ≫ V.ι) η
      (genericPoint Y) hη'over ?_
    refine geometricallyIrreducibleComponents_pullback_congr _ _
      (CommRingCat.ofHom (algebraMap (Y.residueField (genericPoint Y)) K)) ε ?_ hK
    rw [Category.assoc]
    exact hε

end AlgebraicGeometry

end

end
