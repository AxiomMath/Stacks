module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineOverChartSectionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineOpenImmersionChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# A quasi-affine morphism of finite type is closed in one of finite presentation, via algebras

Let `f : Y ⟶ X` be a quasi-affine morphism of algebraic spaces which is locally of finite type,
with `X` quasi-compact and quasi-separated.  This file proves that there are an affine
surjective étale chart `U` of `X` and finitely many sections `s` of `f_* 𝒪_Y` over `U` such that
every quasi-coherent `𝒪_X`-algebra `𝒞` of finite presentation with a morphism of algebras
`φ : 𝒞 ⟶ f_* 𝒪_Y` whose image over `U` contains `s` produces the factorization of Stacks 0871:
an algebraic space `X'` of finite presentation over `X` and a closed immersion `Y ⟶ X'` over
`X`.

## Main results

* `AlgebraicGeometry.Space.exists_finset_forall_algebraHom_exists_isClosedImmersion`: finitely
  many sections over an affine étale chart such that every finitely presented quasi-coherent
  algebra mapping onto them gives a closed immersion of `Y` into an algebraic space of finite
  presentation over `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `f : Y ⟶ X` be quasi-affine and locally of finite type with `X` quasi-compact and
quasi-separated.  There are an affine étale chart `U` of `X` and finitely many sections `s` of
`f_* 𝒪_Y` over `U` such that every morphism of `𝒪_X`-algebras `φ : 𝒞 ⟶ f_* 𝒪_Y` out of a
quasi-coherent algebra of finite presentation (with fewer than `B.cutoff` sections on every
chart) whose image over `U` contains `s` gives a closed immersion of `Y` into an algebraic space
of finite presentation over `X`. -/
theorem exists_finset_forall_algebraHom_exists_isClosedImmersion
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqa : IsQuasiAffineHom B S hS f.hom) (hft : IsLocallyOfFiniteType B S hS f.hom)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ (U : SmallEtale B S hS X.1), IsAffine (chartScheme U) ∧
      ∃ (s : Finset ((pushforwardAlgebra B S hS (Over.mk f)).right.obj.obj (op U))),
      ∀ (C : QuasicoherentAlgebra B S hS X) (hC : AlgebraSheaf.SectionsBelowCutoff B S hS C.obj),
        C.obj.IsFinitePresentation →
        ∀ φ : C.obj ⟶ pushforwardAlgebra B S hS (Over.mk f),
          (s : Set _) ⊆ Set.range (φ.right.hom.app (op U)) →
          ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ X.1) (i : Y.1 ⟶ X'),
            IsAlgebraicSpace B S hS X' ∧ IsFinitePresentation B S hS f' ∧
              IsClosedImmersion B S hS i ∧ i ≫ f' = f.hom := by
  obtain ⟨U, hUaff, s, hs⟩ :=
    exists_finset_isImmersion_of_pushforwardRingMap_app B S hS f hfqa hft hXqc
  refine ⟨U, hUaff, s, fun C hC hCfp φ hsφ => ?_⟩
  let P := boundedRelativeSpec B S hS C hC
  let e := pushforwardAlgebraBoundedRelativeSpecIso B S hS C hC
  let g : Over.mk f ⟶ P.obj :=
    (overHomEquivPushforwardAlgebraHom B S hS (Over.mk f) P).symm (e.hom ≫ φ)
  have hgalg : pushforwardAlgebraMap B S hS g = e.hom ≫ φ :=
    pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm B S hS (Over.mk f) P _
  have hinvhom : ∀ {A A' : AlgebraSheaf.{u, u} B S hS X.1 X.2} (k : A ≅ A')
      (W : (SmallEtale B S hS X.1)ᵒᵖ) (c : A'.right.obj.obj W),
      (k.hom.right.hom.app W) ((k.inv.right.hom.app W) c) = c := fun k W c =>
    congrArg (fun m => (m.right.hom.app W) c) k.inv_hom_id
  have hrange : (s : Set _) ⊆ Set.range ((pushforwardRingMap B S hS g).hom.app (op U)) := by
    intro t ht
    obtain ⟨c, hc⟩ := hsφ ht
    refine ⟨(e.inv.right.hom.app (op U)) c, ?_⟩
    rw [← pushforwardAlgebraMap_right, hgalg]
    show (φ.right.hom.app (op U)) ((e.hom.right.hom.app (op U))
      ((e.inv.right.hom.app (op U)) c)) = t
    rwa [hinvhom e]
  have himm : IsImmersion B S hS g.left.hom := hs P g hrange
  have hfpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f.hom :=
    ((isQuasiAffineHom_tfae_of_isAlgebraicSpace Y.2 X.2 f.hom).out 2 1).mp hfqa
  have hfqc : IsQuasiCompact B S hS f.hom :=
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      (MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _
        (fun X' Y' k (hk : @_root_.AlgebraicGeometry.IsQuasiAffineHom X' Y' k) => by
          have := hk; exact (inferInstance : QuasiCompact k))) _ hfpre)
  have hYqc : IsQuasiCompactSpace B S hS Y.1 :=
    (hfqc X.1 X.2 hXqc (𝟙 X.1)).of_iso B S hS (asIso (pullback.snd (𝟙 X.1) f.hom))
  obtain ⟨V, h, hV, hVqc, hcl, hhV⟩ :=
    exists_isQuasiCompactSpace_isClosedImmersion_of_isImmersion B S hS P.obj.left.2 Y.2 hYqc
      g.left.hom himm
  have hPfp : IsFinitePresentation B S hS P.obj.hom.hom := by
    refine isFinitePresentation_of_isFinitePresentation_pushforwardAlgebra B S hS hXqc P ?_
    intro W hW
    have hbij : Function.Bijective (e.inv.right.hom.app (op W)).hom :=
      Function.bijective_iff_has_inverse.2 ⟨e.hom.right.hom.app (op W),
        hinvhom e (op W), hinvhom e.symm (op W)⟩
    have h2 : RingHom.FinitePresentation (e.inv.right.hom.app (op W)).hom := by
      refine RingHom.FinitePresentation.of_surjective _ hbij.2 ?_
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hbij.1]
      exact Submodule.fg_bot
    rw [← AlgebraSheaf.comp_algebraMap e.inv (op W)]
    exact h2.comp (hCfp W hW)
  have hfac : g.left.hom ≫ P.obj.hom.hom = f.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Y ⟶ X => m.hom) (Over.w g)
  refine ⟨V.toFunctor, V.ι ≫ P.obj.hom.hom, h, hV.1, ⟨?_, ?_, ?_⟩, hcl, ?_⟩
  · exact isLocallyOfFinitePresentation_comp B S hS hV.1 P.obj.left.2 X.2 _ _
      (isLocallyOfFinitePresentation_of_isOpenImmersion B S hS hV.2) hPfp.1
  · exact isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs hVqc _
  · exact isQuasiSeparated_comp B S hS hV.1 P.obj.left.2 _ _
      (isQuasiSeparated_of_mono B S hS V.ι inferInstance) hPfp.2.2
  · rw [← Category.assoc, hhV, hfac]

end AlgebraicGeometry.Space

end
