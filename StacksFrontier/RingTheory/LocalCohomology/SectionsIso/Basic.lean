module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Cech
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Kernel

/-!
# The degree-zero sections comparison of the localization triangle

Let `R` be a commutative ring, `I = (f₁, …, f_r)` a finitely generated ideal, `U = Spec R \ V(I)`
and `M` an `R`-module whose universe is independent of the ring's. The degree-zero cohomology of
the third term of the localization triangle is the kernel of the first Čech differential
(`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer`). This file identifies that kernel
with the sections of the associated sheaf on `U`:

`ker (Cech.cechD f M 1) ≅ Γ(U, M̃|U)`.

The two sides are joined through the chain
`ker d¹ ≅ { Čech compatible families } ≅ Γ(U, M̃) ≅ Γ(⊤, M̃|U)`, whose first link is
`Stacks.LocalCohomology.kerCechDOneEquivCechCompatible`, whose second is the sheaf axiom in the
form `Stacks.LocalCohomology.moduleSectionsComplementEquivCechCompatible`, and whose third is the
transport along `ι ''ᵁ ⊤ = U` of `AlgebraicGeometry.Scheme.Opens.ι_image_top`.

The last link needs one remark. Restricting the associated sheaf along the open immersion
`ι : U ⟶ Spec R` and taking global sections produces the same *set* of locally fractional sections
as evaluating at `ι ''ᵁ ⊤`, but carries the `R`-action obtained by restricting scalars along
`R ⟶ Γ(U, 𝒪_U) ⟶ Γ(Spec R, ι ''ᵁ ⊤)` rather than the evident one. The two agree: that composite is
the structure map `R ⟶ Γ(Spec R, ι ''ᵁ ⊤)` of the structure sheaf
(`AlgebraicGeometry.Scheme.toOpen_eq`, the comparison of
`Stacks.LocalCohomology.appIsoScalars_eq_id` being the identity), which acts on a locally
fractional section by multiplying its value at every prime by `a / 1`.

## Main definitions

* `Stacks.LocalCohomology.complementGlobalSectionsEquiv` — the two `R`-module structures on the
  locally fractional sections over `ι ''ᵁ ⊤` agree.
* `Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections` — **`ker d¹ ≅ Γ(U, M̃|U)`**.
* `Stacks.LocalCohomology.cechSectionsIso` — the composite with the degree-zero cohomology of the
  Čech cone: the comparison the field `sectionsIso` of
  `Stacks.LocalCohomology.LocalizationTriangleData` asks for.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R]

section Free

variable (I : Ideal R) (M : ModuleCat.{v} R)

/-- The locally fractional sections of `M` on `ι ''ᵁ ⊤`, as a module over the sections of the
structure sheaf there. Restricting the associated sheaf along the open immersion of
`U = Spec R \ V(I)` and evaluating at `⊤` gives exactly this module, with scalars restricted along
the comparison `Γ(U, 𝒪_U) ⟶ Γ(Spec R, ι ''ᵁ ⊤)`. -/
abbrev imageTopSections : ModuleCat.{max u v}
    ((Spec (CommRingCat.of R)).ringCatSheaf.obj.obj
      (op ((complementZeroLocus R I).ι ''ᵁ ⊤))) :=
  (associatedSheaf R M).val.obj (op ((complementZeroLocus R I).ι ''ᵁ ⊤))

/-- The structure map `R ⟶ Γ(Spec R, ι ''ᵁ ⊤)` through which the sections of a restricted sheaf of
modules become an `R`-module is the one of the structure sheaf: at every prime of `ι ''ᵁ ⊤` it is
`a ↦ a / 1`. -/
theorem imageTopScalars_apply_coe (a : R) (x : ↥((complementZeroLocus R I).ι ''ᵁ ⊤)) :
    (imageTopScalars I a :
        StructureSheaf.sectionsSubalgebra R ((complementZeroLocus R I).ι ''ᵁ ⊤)).1 x =
      algebraMap R (StructureSheaf.Localizations R x.1) a := by
  rw [imageTopScalars_eq]
  rfl

/-- **The two `R`-module structures on the sections over `ι ''ᵁ ⊤` agree.** The `R`-action on the
global sections on `U = Spec R \ V(I)` of the restriction of `M̃` is obtained by restricting
scalars along `R ⟶ Γ(U, 𝒪_U) ⟶ Γ(Spec R, ι ''ᵁ ⊤)`, which is the structure map of the structure
sheaf; it therefore multiplies the value of a section at every prime by `a / 1`, which is the
evident action. -/
theorem complementGlobalSections_smul (a : R)
    (s : moduleSections M ((complementZeroLocus R I).ι ''ᵁ ⊤)) :
    (show complementGlobalSections R I (complementTilde R I M) from a • s) =
      a • (show complementGlobalSections R I (complementTilde R I M) from s) := by
  have h1 : (a • (show complementGlobalSections R I (complementTilde R I M) from s)) =
      (show ↑((Spec (CommRingCat.of R)).ringCatSheaf.obj.obj
          (op ((complementZeroLocus R I).ι ''ᵁ ⊤))) from imageTopScalars I a) •
        (show imageTopSections I M from s) := rfl
  refine Subtype.ext (funext fun x => ?_)
  refine Eq.symm ((congrFun (congrArg Subtype.val h1) x).trans ?_)
  exact (congrArg (fun c : StructureSheaf.Localizations R x.1 => c • s.1 x)
    (imageTopScalars_apply_coe I a x)).trans (algebraMap_smul _ a (s.1 x))

/-- **The sections over `ι ''ᵁ ⊤` are the global sections on `U` of the restricted sheaf**, as
`R`-modules: the underlying sets are the same and the two `R`-actions agree by
`Stacks.LocalCohomology.complementGlobalSections_smul`. -/
def complementGlobalSectionsEquiv :
    moduleSections M ((complementZeroLocus R I).ι ''ᵁ ⊤) ≃ₗ[R]
      complementGlobalSections R I (complementTilde R I M) where
  toFun s := s
  map_add' _ _ := rfl
  map_smul' a s := complementGlobalSections_smul I M a s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl

variable {r : ℕ} (f : Fin r → R)

/-- **`ker d¹ ≅ Γ(U, M̃|U)`.** The kernel of the first differential of the extended alternating
Čech complex is the module of global sections on `U = Spec R \ V(I)` of the restriction of the
quasi-coherent module generated by `M`: a cocycle is a compatible family of fractions, and a
compatible family of fractions is a section. -/
def kerCechDOneEquivComplementGlobalSections (hIf : Ideal.span (Set.range f) = I) :
    LinearMap.ker (Cech.cechD f (M : Type _) 1) ≃ₗ[R]
      complementGlobalSections R I (complementTilde R I M) :=
  (((kerCechDOneEquivCechCompatible f M).trans
      (moduleSectionsComplementEquivCechCompatible f M I hIf).symm).trans
    (moduleSectionsCongr M (Scheme.Opens.ι_image_top (complementZeroLocus R I)).symm)).trans
      (complementGlobalSectionsEquiv I M)

end Free

/-! ### The comparison for the pinned Čech complex

`Stacks.LocalCohomology.cechComplementFunctor` is an endofunctor of `ModuleCat.{max u v} R`
rather than of `ModuleCat.{v} R`, because `Stacks.LocalCohomology.extendedCechComplex` is a
complex of `ModuleCat.{max u v} R`. The two declarations below therefore need the module
universe above the ring universe, while everything above holds with the two independent. -/

section Pinned

variable (I : Ideal R) (M : ModuleCat.{max u v} R) {r : ℕ} (f : Fin r → R)

/-- **The degree-zero sections comparison of the localization triangle.** The degree-zero
cohomology of derived sections on `U = Spec R \ V(I)` is the module of sections of `M̃` on `U`:
by `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer` that cohomology is the kernel of
the first Čech differential, and by
`Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections` that kernel is the sections. -/
def cechSectionsIso (hIf : Ideal.span (Set.range f) = I) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
        ((cechComplementFunctor.{v} f).obj M) ≃ₗ[R]
      complementGlobalSections R I (complementTilde R I M) :=
  (cechComplementHomologyZeroEquivKer.{v} f M).trans
    (kerCechDOneEquivComplementGlobalSections I M f hIf)

/-- The comparison `Stacks.LocalCohomology.cechSectionsIso` sends a degree-zero cohomology class
to the section attached to its image in the kernel of the first Čech differential. -/
@[simp]
theorem cechSectionsIso_apply (hIf : Ideal.span (Set.range f) = I)
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
      ((cechComplementFunctor.{v} f).obj M)) :
    cechSectionsIso I M f hIf z =
      kerCechDOneEquivComplementGlobalSections I M f hIf
        (cechComplementHomologyZeroEquivKer.{v} f M z) :=
  rfl

end Pinned

end Stacks.LocalCohomology

end
