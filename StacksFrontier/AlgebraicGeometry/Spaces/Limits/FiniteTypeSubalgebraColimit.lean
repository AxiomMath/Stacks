module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubalgebras
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasicoherentAlgebraFinitePresentationColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SubalgebraJoinFiniteType

/-!
# A quasi-coherent algebra as the colimit of its finite type quasi-coherent subalgebras

Let `𝒜` be a quasi-coherent algebra on an algebraic space `Y`, and let `φ` present the underlying
module of `𝒜` as a filtered colimit of modules `F_k` of finite presentation. Then `𝒜` is the
colimit of its finite type quasi-coherent subalgebras, among which are the images of the
morphisms of algebras `Sym(F_k) ⟶ 𝒜` extending the legs `F_k ⟶ 𝒜`. If `𝒜` is moreover integral,
it is the directed colimit of its finite quasi-coherent subalgebras.

## Main results

* `Space.nonempty_isColimit_finiteTypeSubalgebraCocone_of_presentation`: `𝒜` is the colimit of
  the cocone of its finite type quasi-coherent subalgebras, given such a presentation.
* `Space.isFiltered_and_nonempty_isColimit_finiteSubalgebraCocone_of_presentation`: for integral
  `𝒜`, the finite quasi-coherent subalgebras form a filtered category whose cocone is a colimit,
  given such a presentation.

## References

* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-coherent algebra sheaf whose underlying module is a filtered colimit of modules of
finite presentation is the colimit of the cocone of its finite type quasi-coherent
subalgebras. -/
theorem nonempty_isColimit_finiteTypeSubalgebraCocone_of_presentation
    (Y : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (hA : A.IsQuasicoherent) {K : Type u} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (φ : D ⟶ (Functor.const K).obj (AlgebraSheaf.underlyingModule A))
    (hfp : ∀ k, (D.obj k).IsFinitePresentation) (hc : IsColimit (Cocone.mk _ φ)) :
    Nonempty (IsColimit (finiteTypeSubalgebraCocone B S hS Y.1 Y.2 A)) := by
  have := isFiltered_finiteTypeSubalgebra Y A hA
  refine AlgebraSheaf.nonempty_isColimit_of_affineChartSections_of_injective _
    (fun U _ C => AlgebraSheaf.injective_subobject_arrow_app C.obj (.op U)) fun U hU x => ?_
  have hD : ∀ k, (D.obj k).IsQuasicoherentOnSite := fun k =>
    have := hfp k
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentation (D.obj k)
  obtain ⟨k, y, hy⟩ := exists_eq_of_isColimit_of_isQuasicoherentOnSite φ hc hD hA hU x
  let ψ := SymSections.lift (φ.app k)
  have hSq : (SymSections.algebra (D.obj k)).IsQuasicoherent :=
    SymSections.isQuasicoherent_algebra _ (hD k)
  have hSft : (SymSections.algebra (D.obj k)).IsFiniteType :=
    (SymSections.isFinitePresentation_algebra _ (hD k)
      (SheafOfModules.isFinitePresentationOnSite_of_isFinitePresentation (D.obj k)
        (h := hfp k))).isFiniteType
  refine ⟨⟨imageSubobject ψ,
      AlgebraSheaf.IsQuasicoherent.of_iso (imageSubobjectIso ψ).symm
        (AlgebraSheaf.isQuasicoherent_image ψ hSq hA),
      AlgebraSheaf.IsFiniteType.of_iso (imageSubobjectIso ψ).symm
        (AlgebraSheaf.isFiniteType_image ψ hSq hA hSft)⟩,
    (factorThruImageSubobject ψ).right.hom.app (op U)
      (SymSections.genApp (D.obj k) (op U) y), ?_⟩
  have h := ConcreteCategory.congr_hom
    (congrArg (fun g => g.right.hom.app (op U)) (imageSubobject_arrow_comp ψ))
    (SymSections.genApp (D.obj k) (op U) y)
  exact h.trans ((SymSections.gen_lift_apply (φ.app k) (op U) y).trans hy)

/-- An integral quasi-coherent algebra sheaf whose underlying module is a filtered colimit of
modules of finite presentation is the directed colimit of its finite quasi-coherent subalgebras:
these form a filtered category, and their cocone is a colimit. -/
theorem isFiltered_and_nonempty_isColimit_finiteSubalgebraCocone_of_presentation
    (Y : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (hA : A.IsQuasicoherent) (hint : A.IsIntegral) {K : Type u} [SmallCategory K]
    [IsFiltered K] {D : K ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (φ : D ⟶ (Functor.const K).obj (AlgebraSheaf.underlyingModule A))
    (hfp : ∀ k, (D.obj k).IsFinitePresentation) (hc : IsColimit (Cocone.mk _ φ)) :
    IsFiltered (FiniteSubalgebra B S hS Y.1 Y.2 A) ∧
      Nonempty (IsColimit (finiteSubalgebraCocone B S hS Y.1 Y.2 A)) :=
  ⟨isFiltered_finiteSubalgebra_of_isFiltered_finiteTypeSubalgebra' B S hS Y.1 Y.2 A hint
      (isFiltered_finiteTypeSubalgebra Y A hA),
    isColimit_finiteSubalgebraCocone_of_isColimit_finiteTypeSubalgebraCocone' B S hS Y.1 Y.2 A
      hint (nonempty_isColimit_finiteTypeSubalgebraCocone_of_presentation B S hS Y A hA φ hfp hc)⟩

end AlgebraicGeometry.Space

end
