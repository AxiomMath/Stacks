module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderFunctionsLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafExtensionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.StructureSheafSquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UnitsShortExactSequence

/-!
# A square-zero extension of the structure sheaf is a short exact sequence of abelian sheaves

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y` in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`. This file
assembles it into a `CategoryTheory.ShortComplex` of sheaves of abelian groups on the small étale
site of `X`, proves it short exact, and deduces that `𝒜(U) ⟶ 𝒪_X(U)` is surjective over every
object `U` of the small étale site with affine underlying scheme.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.extensionAddSheaf`: the extension sheaf `𝒜`, read
  as a sheaf of abelian groups.
* `AlgebraicGeometry.Space.SquareZeroExtension.idealToExtension` and
  `AlgebraicGeometry.Space.SquareZeroExtension.extensionToStructure`: the two maps of the
  sequence, as morphisms of sheaves of abelian groups.
* `AlgebraicGeometry.Space.SquareZeroExtension.shortComplex`: the sequence
  `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` itself.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.shortComplex_shortExact`: the sequence
  `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of a square-zero extension of the structure sheaf is short exact.
* `AlgebraicGeometry.Space.SquareZeroExtension.surjective_π_app_of_isAffine`: over an object of
  the small étale site with affine underlying scheme the reduction `𝒜 ⟶ 𝒪_X` is surjective on
  sections.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03F8](https://stacks.math.columbia.edu/tag/03F8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-! ### The three terms of the sequence -/

/-- The extension sheaf `𝒜` of a square-zero extension of the structure sheaf, with
commutativity of its rings of sections forgotten. -/
abbrev SquareZeroExtension.extensionRingSheaf :
    Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  letI := Stacks.hasSheafCompose_forget₂_commRingCat.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj E.A

/-- The extension sheaf `𝒜` of a square-zero extension of the structure sheaf, read as a sheaf
of abelian groups on the small étale site of `X`: the sheaf of rings `𝒜` regarded as a module
over itself. -/
abbrev SquareZeroExtension.extensionAddSheaf :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (SquareZeroExtension.extensionRingSheaf B S hS E)).obj
    (SheafOfModules.unit (SquareZeroExtension.extensionRingSheaf B S hS E))

/-! ### The two maps of the sequence -/

/-- The inclusion `ℐ ⟶ 𝒜` of a square-zero extension of the structure sheaf, as a morphism of
sheaves of abelian groups. -/
def SquareZeroExtension.idealToExtension :
    (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj E.I ⟶
      SquareZeroExtension.extensionAddSheaf B S hS E :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (E.ι U)
      naturality := fun U V m ↦ by
        ext x
        exact E.naturality m x }

/-- On sections the inclusion `ℐ ⟶ 𝒜` is the field `ι`. -/
theorem SquareZeroExtension.idealToExtension_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : E.I.val.obj U) :
    (SquareZeroExtension.idealToExtension B S hS E).hom.app U x = E.ι U x := rfl

/-- The reduction `𝒜 ⟶ 𝒪_X` of a square-zero extension of the structure sheaf, as a morphism of
sheaves of abelian groups. -/
def SquareZeroExtension.extensionToStructure :
    SquareZeroExtension.extensionAddSheaf B S hS E ⟶ structureAddSheaf B S hS X :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom (E.π.hom.app U).hom.toAddMonoidHom
      naturality := fun U V m ↦ by
        ext a
        exact congrArg (fun k : E.A.obj.obj U ⟶ _ ↦ k.hom a) (E.π.hom.naturality m) }

/-- On sections the reduction `𝒜 ⟶ 𝒪_X` is the field `π`. -/
theorem SquareZeroExtension.extensionToStructure_app (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : E.A.obj.obj U) :
    (SquareZeroExtension.extensionToStructure B S hS E).hom.app U a =
      (E.π.hom.app U).hom a := rfl

/-- The reduction `𝒜 ⟶ 𝒪_X`, read as a map of sheaves of abelian groups, is locally
surjective. -/
theorem SquareZeroExtension.locallySurjective_extensionToStructure :
    Sheaf.IsLocallySurjective (SquareZeroExtension.extensionToStructure B S hS E) :=
  let := E.locallySurjective_π
  ⟨fun s ↦ Presheaf.imageSieve_mem (SmallEtale.topology B S hS X.1) E.π.hom s⟩

/-- The inclusion of the square-zero ideal is injective on the sections over every object of the
small étale site. -/
theorem SquareZeroExtension.injective_ι (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Injective (E.ι U) := by
  intro x y hxy
  obtain ⟨z, -, hz⟩ := E.exact_kernel U (E.ι U y) (E.mem_kernel U y)
  exact (hz x hxy).trans (hz y rfl).symm

/-! ### The sequence and its exactness -/

/-- The sequence `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of a square-zero extension of the structure sheaf, as
a short complex of sheaves of abelian groups on the small étale site of `X`. -/
def SquareZeroExtension.shortComplex :
    ShortComplex (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  ShortComplex.mk (SquareZeroExtension.idealToExtension B S hS E)
    (SquareZeroExtension.extensionToStructure B S hS E) <| by
    refine ObjectProperty.hom_ext _ ?_
    ext U x
    exact E.mem_kernel U x

/-- The inclusion `ℐ ⟶ 𝒜` of a square-zero extension is a monomorphism. -/
theorem SquareZeroExtension.mono_idealToExtension :
    Mono (SquareZeroExtension.idealToExtension B S hS E) :=
  Sheaf.mono_of_injective _ fun U ↦ SquareZeroExtension.injective_ι B S hS E U

/-- Equal morphisms of sheaves of abelian groups agree on every section. -/
private theorem congr_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u}} {k l : F ⟶ G} (h : k = l) (U : Cᵒᵖ) (x : F.obj.obj U) :
    k.hom.app U x = l.hom.app U x := by
  rw [h]

/-- The canonical map from `ℐ` to the categorical kernel of `𝒜 ⟶ 𝒪_X` is surjective on the
sections over every object of the small étale site. -/
theorem SquareZeroExtension.surjective_kernelLift_shortComplex_app
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Surjective ((kernel.lift (SquareZeroExtension.shortComplex B S hS E).g
      (SquareZeroExtension.shortComplex B S hS E).f
      (SquareZeroExtension.shortComplex B S hS E).zero).hom.app U) := by
  intro w
  have hzero : (SquareZeroExtension.extensionToStructure B S hS E).hom.app U
      ((kernel.ι (SquareZeroExtension.shortComplex B S hS E).g).hom.app U w) = 0 :=
    congr_hom_app_apply (kernel.condition (SquareZeroExtension.shortComplex B S hS E).g) U w
  obtain ⟨x, hx, -⟩ := E.exact_kernel U
    ((kernel.ι (SquareZeroExtension.shortComplex B S hS E).g).hom.app U w) hzero
  refine ⟨x, injective_kernel_ι_app B S hS _ U ?_⟩
  exact (congr_hom_app_apply (kernel.lift_ι (SquareZeroExtension.shortComplex B S hS E).g
    (SquareZeroExtension.shortComplex B S hS E).f
    (SquareZeroExtension.shortComplex B S hS E).zero) U x).trans hx

/-- The sequence `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` of a square-zero extension of the structure sheaf of an
algebraic space is short exact. -/
theorem SquareZeroExtension.shortComplex_shortExact :
    (SquareZeroExtension.shortComplex B S hS E).ShortExact := by
  have : Mono (SquareZeroExtension.shortComplex B S hS E).f :=
    SquareZeroExtension.mono_idealToExtension B S hS E
  have : Sheaf.IsLocallySurjective (SquareZeroExtension.shortComplex B S hS E).g :=
    SquareZeroExtension.locallySurjective_extensionToStructure B S hS E
  have : Epi (SquareZeroExtension.shortComplex B S hS E).g :=
    Sheaf.epi_of_isLocallySurjective _
  refine { exact := ?_ }
  refine (SquareZeroExtension.shortComplex B S hS E).exact_iff_epi_kernel_lift.mpr ?_
  have : Sheaf.IsLocallySurjective (kernel.lift (SquareZeroExtension.shortComplex B S hS E).g
      (SquareZeroExtension.shortComplex B S hS E).f
      (SquareZeroExtension.shortComplex B S hS E).zero) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (SquareZeroExtension.surjective_kernelLift_shortComplex_app B S hS E)
  exact Sheaf.epi_of_isLocallySurjective _

/-! ### Surjectivity of the reduction on an affine chart -/

/-- Over an object of the small étale site with affine underlying scheme, the reduction
`𝒜 ⟶ 𝒪_X` of a square-zero extension of the structure sheaf is surjective on sections. -/
theorem SquareZeroExtension.surjective_π_app_of_isAffine (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (E.π.hom.app (op W)).hom :=
  surjective_app_of_shortExact_of_isQuasicoherentOnSite (hF := X.2) E.quasicoherent
    (SquareZeroExtension.shortComplex B S hS E)
    (SquareZeroExtension.shortComplex_shortExact B S hS E) rfl W hW

end AlgebraicGeometry.Space

end
