module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeSubalgebraColimit

/-!
# Finitely many sections of an integral algebra lie in a finite subalgebra

Let `Y` be a quasi-compact and quasi-separated algebraic space and `𝒜` a quasi-coherent
`𝒪_Y`-algebra. Every section of `𝒜` over an affine étale chart lies in a quasi-coherent
subalgebra of finite type: the underlying module of `𝒜` is a filtered colimit of modules of
finite presentation by Stacks 07V9, a section over an affine chart comes from one member `ℱ`, and
it is then a section of the image of `Sym(ℱ) ⟶ 𝒜`. Since these subalgebras are directed, finitely
many sections lie in one of them, and if `𝒜` is integral that subalgebra is finite.

## Main results

* `AlgebraicGeometry.Space.exists_finiteTypeSubalgebra_mem_of_presentation`: a section over an
  affine chart lies in a finite type quasi-coherent subalgebra, given a filtered presentation of
  the underlying module by modules of finite presentation.
* `AlgebraicGeometry.Space.exists_finiteSubalgebra_forall_mem`: on a quasi-compact quasi-separated
  space, finitely many sections over an affine chart of an integral quasi-coherent algebra lie in
  one finite quasi-coherent subalgebra.

## References

* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 082C](https://stacks.math.columbia.edu/tag/082C)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section of a quasi-coherent algebra over an affine chart lies in a finite type
quasi-coherent subalgebra, given a filtered presentation `φ` of its underlying module by modules
of finite presentation. -/
theorem exists_finiteTypeSubalgebra_mem_of_presentation
    (Y : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (hA : A.IsQuasicoherent) {K : Type (u + 1)} [Category.{u} K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS Y.1 Y.2}
    (φ : D ⟶ (Functor.const K).obj (AlgebraSheaf.underlyingModule A))
    (hfp : ∀ k, (D.obj k).IsFinitePresentation) (hc : IsColimit (Cocone.mk _ φ))
    {U : SmallEtale B S hS Y.1}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj U)))
    (x : A.right.obj.obj (op U)) :
    ∃ C : FiniteTypeSubalgebra B S hS Y.1 Y.2 A,
      x ∈ Set.range (C.obj.arrow.right.hom.app (op U)) := by
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

/-- The sections of a subalgebra over a chart grow with the subalgebra. -/
theorem range_arrow_app_subset_of_le {Y : AlgebraicSpaces B S hS}
    {A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} {C C' : Subobject A} (h : C ≤ C')
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Set.range (C.arrow.right.hom.app U) ⊆ Set.range (C'.arrow.right.hom.app U) := by
  rintro _ ⟨z, rfl⟩
  refine ⟨(Subobject.ofLE C C' h).right.hom.app U z, ?_⟩
  have key : (Subobject.ofLE C C' h ≫ C'.arrow).right.hom.app U = C.arrow.right.hom.app U := by
    rw [Subobject.ofLE_arrow]
  rw [← key]
  rfl

/-- On a quasi-compact quasi-separated algebraic space, finitely many sections of an integral
quasi-coherent algebra over an affine chart lie in a finite quasi-coherent subalgebra. -/
theorem exists_finiteSubalgebra_forall_mem (Y : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (hA : A.IsQuasicoherent) (hint : A.IsIntegral)
    {U : SmallEtale B S hS Y.1}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj U)))
    (G : Finset (A.right.obj.obj (op U))) :
    ∃ C : FiniteSubalgebra B S hS Y.1 Y.2 A,
      ∀ x ∈ G, x ∈ Set.range (C.obj.arrow.right.hom.app (op U)) := by
  classical
  obtain ⟨K, inst, hK, D, φ, hfp, ⟨hc⟩⟩ :=
    exists_isFilteredColimit_isFinitePresentation B S hS B.contains_terminal Y.2 hqc hqs
      (AlgebraSheaf.underlyingModule A) hA
  let _ := inst
  choose Cx hCx using fun x : A.right.obj.obj (op U) =>
    exists_finiteTypeSubalgebra_mem_of_presentation B S hS Y A hA φ hfp hc hU x
  have hfilt := isFiltered_finiteTypeSubalgebra Y A hA
  obtain ⟨C, hC⟩ := IsFiltered.sup_objs_exists (G.image Cx)
  have hC' : ∀ x ∈ G, x ∈ Set.range (C.obj.arrow.right.hom.app (op U)) := fun x hx =>
    range_arrow_app_subset_of_le B S hS (leOfHom (hC (Finset.mem_image_of_mem Cx hx)).some.hom)
      (op U) (hCx x)
  exact ⟨⟨C.obj, C.property.1,
    (isFinite_subobject_iff_isFiniteType' B S hS Y.1 Y.2 A hint C.obj).2 C.property.2⟩, hC'⟩

end AlgebraicGeometry.Space

end
